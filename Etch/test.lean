import Mathlib.Tactic

namespace SAM

inductive Token (ι : Type)
| stop (n : Nat)
| val (x : ι)
| done
| empty
deriving Repr

def Token.comp : Token ℕ → Token ℕ → Ordering
  | Token.empty, _ => Ordering.eq
  | _, Token.empty => Ordering.eq
  | Token.done, Token.done => Ordering.eq
  | _, Token.done => Ordering.lt
  | Token.done, _ => Ordering.gt
  | Token.stop n1, Token.stop n2 => Ord.compare n1 n2
  | _, Token.stop _ => Ordering.lt
  | Token.stop _, _ => Ordering.gt
  | Token.val v1, Token.val v2 => Ord.compare v1 v2

instance : Ord (Token ℕ) where
  compare := Token.comp

variable {ι : Type} [Zero ι]

abbrev Stream (ι : Type) := List (Token ι)

abbrev Ident := String

-- todo: `tree-like' structure
inductive Format
inductive Expr
| root
| read (name : Ident) (level : Nat) (input : Expr)

example : Expr := .read "m" 1 (.read "m" 0 .root)
-- example : Expr := .intersect (.read "m1" 0 .root) (.read "m2" 0 .root)
-- example : Expr := .read "m" 1 (.intersect (.read "m1" 0 .root) (.read "m2" 0 .root))

def vec : Expr := .read "v" 0 .root

-- ?: Need to store dimensions?
/-
Example matrix (Sparse): 6x6
i: [0 3]
   [0 3 5]
j: [0 2 4 5]
   [1 4 0 1 5]
val: [1 5 2 3 9]

Example matrix (Dense) 6x6
i: [6] j: [6]
-/


structure Ctxt (ι : Type) where
 -- name -> level -> index -> (ref, crd) for list of children
  data : Ident → Nat → ι → Prod (List ι) (List ι)

#check List.bind

def a : Option ℕ := some 3

partial def binaryIntersectHelper (xr: Stream ℕ) (xc: Stream ℕ) (yr: Stream ℕ)(yc: Stream ℕ) (res_c: Stream ℕ) (res_rx: Stream ℕ) (res_ry: Stream ℕ): Stream ℕ × Stream ℕ × Stream ℕ :=
match xr, xc, yr, yc with
| r_x::xs_r, c_x::xs_c, r_y::ys_r, c_y::ys_c =>
  match Ord.compare c_x c_y with
  | .eq =>
    have : sizeOf xs_r < sizeOf (r_x :: xs_r) := by decreasing_tactic
    binaryIntersectHelper xs_r xs_c ys_r ys_c (c_x::res_c) (r_x::res_rx) (r_y::res_ry)
  | .lt =>
    have : sizeOf xs_r < sizeOf (r_x :: xs_r) := by decreasing_tactic
    binaryIntersectHelper xs_r xs_c yr yc res_c res_rx res_ry
  | .gt =>
    have : sizeOf ys_r < sizeOf (r_y :: ys_r) := by decreasing_tactic
    binaryIntersectHelper xr xc ys_r ys_c res_c res_rx res_ry
|  _, _, _, _ => (res_c, res_rx, res_ry)

def BinaryIntersect  (r1: Stream ℕ) (c1: Stream ℕ) (r2: Stream ℕ)(c2: Stream ℕ) : Stream ℕ × Stream ℕ × Stream ℕ :=
  (λ(z1, z2, z3) => (List.reverse z1, List.reverse z2, List.reverse z3)) (binaryIntersectHelper r1 c1 r2 c2 [] [] [])

-- todo
def MultiIntersect (l: List (Stream ℕ × Stream ℕ)): Stream ℕ × (List (Stream ℕ)) := sorry

--todo: remove this partial def
partial def binaryUnionHelper (xr: Stream ℕ) (xc: Stream ℕ) (yr: Stream ℕ)(yc: Stream ℕ) (res_c: Stream ℕ) (res_rx: Stream ℕ) (res_ry: Stream ℕ): Stream ℕ × Stream ℕ × Stream ℕ :=
match xr, xc, yr, yc with
| r_x::xs_r, c_x::xs_c, r_y::ys_r, c_y::ys_c =>
  match Ord.compare c_x c_y with
  | .eq =>
    have : sizeOf xs_r < sizeOf (r_x :: xs_r) := by decreasing_tactic
    binaryUnionHelper xs_r xs_c ys_r ys_c (c_x::res_c) (r_x::res_rx) (r_y::res_ry)
  | .lt => -- current x crd does not appear in y stream
    have : sizeOf xs_r < sizeOf (r_x :: xs_r) := by decreasing_tactic
    binaryUnionHelper xs_r xs_c yr yc (c_x::res_c) (r_x::res_rx) (Token.empty::res_ry)
  | .gt => -- current y crd does not appear in x stream
    have : sizeOf ys_r < sizeOf (r_y :: ys_r) := by decreasing_tactic
    binaryUnionHelper xr xc ys_r ys_c (c_y::res_c) (Token.empty::res_rx) (r_y::res_ry)
|  _, _, _, _ => (res_c, res_rx, res_ry)

def BinaryUnion (r1: Stream ℕ) (c1: Stream ℕ) (r2: Stream ℕ)(c2: Stream ℕ) : Stream ℕ × Stream ℕ × Stream ℕ :=
  (λ(z1, z2, z3) => (List.reverse z1, List.reverse z2, List.reverse z3)) (binaryUnionHelper r1 c1 r2 c2 [] [] [])

-- todo
def MultiUnion (l: List (Stream ℕ × Stream ℕ)): Stream ℕ × (List (Stream ℕ)) := sorry

def xr : Stream ℕ := [Token.val 0, Token.val 1, Token.stop 0]
def xc : Stream ℕ := [Token.val 3, Token.val 4, Token.stop 0]
def yr : Stream ℕ := [Token.val 1, Token.val 2, Token.stop 0]
def yc : Stream ℕ := [Token.val 4, Token.val 5, Token.stop 0]
#eval BinaryIntersect xr xc yr yc
#eval BinaryUnion xr xc yr yc

def Expr.eval (ctxt : Ctxt ι) (e : Expr) : List (Stream ι) :=
match e with
| root => [[.val 0, .done]]
| .read name level input =>
  if h:(input.eval ctxt).length > 0
    then let is := (input.eval ctxt)[0]'h
    -- Examples (Compressed m1):
    -- is  = [0, done]
    -- out = [0, 1, 2, s0, done] & [0, 3, 5, s0, done]

    -- is = [0, 2, s0, done]
    -- out = [0, 1, s0, 4, s1, done] & [1, 4, s0, 5, s1, done]

    -- Examples (dense 3x4):
    -- is = [0, 2, s0, done]
    -- out = [0, 1, 2, 3, s0, 8, 9, 10, 11, s1, done] & [0, 1, 2, 3, 4, s0, 0, 1, 2, 3, 4, s1, done]

    -- store previous token
    let ref : List (Stream ι) := is.map fun token =>
      match token with
      | .val i => ((ctxt.data name level i).fst |>.map .val) ++ [Token.stop 0] -- ?: Don't add this to the last one?
      | .stop n => [.stop (n+1)]
      | .done => [.done]
      | .empty => []
    let crd : List (Stream ι) := is.map fun token =>
      match token with
      | .val i => ((ctxt.data name level i).snd |>.map .val) ++ [Token.stop 0] -- ?: Don't add this to the last one?
      | .stop n => [.stop (n+1)]
      | .done => [.done]
      | .empty => []
    [ref.join, crd.join]
  else []
-- | .intersect is js =>


inductive Level
| dense (n: Nat) (size: Nat)
| compressed (n: Nat) (v1: List Nat) (v2: List Nat)
deriving Repr

#check Level.dense 0 3
#check Level.compressed 1 [0, 3] [0, 3, 5]

def emptyContext : Ctxt ι where
  data := fun _ _ _  => ([], [])

def range (a b: ℕ) := List.range (b-a) |>.map (.+a)

def contextFromData (ident: Ident) (levels: List Level) : Ctxt (ι := Nat) where
  -- data : Ident → ι → List ι
  -- ?: Write this function in a better way
  data := fun name =>
    if name = ident -- Check if name is valid
      then (fun n =>
        if h : n < levels.length -- Check if level number is valid
          then fun i =>
            match levels[n]'h with
            | Level.dense _ size => (range (size*i) (size*i+size), range 0 size) -- ??
            | Level.compressed _ v1 v2 =>
              if h: (i+1) < v1.length
                then
                  have h': i < v1.length := by {
                    exact Nat.lt_of_succ_lt h
                  }
                  if h2: v1[i+1] <= v2.length ∧ v1[i]'h' < v2.length
                  then (range v1[i] v1[i+1], v2.toArray[v1[i]:v1[i+1]].toArray.toList)
                  else ([], [])
                else ([], [])
          else fun _ => ([], []))
      else fun _ _ => ([], [])

def root : Expr := .root
def mat1_level0 : Expr := .read "m" 0 .root
def mat1_level1 : Expr := .read "m" 1 (.read "m" 0 .root)


def l_i := Level.compressed 0 [0, 3] [0, 3, 5]
def l_j := Level.compressed 1 [0, 2, 4, 5] [1, 4, 0, 1, 5]
def c := contextFromData "m" [l_i, l_j]

#eval root.eval (emptyContext (ι := Nat))
#eval root.eval c
#eval mat1_level0.eval c
#eval mat1_level1.eval c

/-
Example 2 (sparse) 6x6:
i: [0 5]
   [1 2 3 4 5]
j: [0 2 3 4 5 7]
   [3 4 2 1 4 0 5]
val: [1 2 3 4 5 6 7]
-/
def l2_i := Level.compressed 0 [0, 5] [1, 2, 3, 4, 5]
def l2_j := Level.compressed 1 [0, 2, 3, 4, 5, 7] [3, 4, 2, 1, 4, 0, 5]
def c2 := contextFromData "n" [l2_i, l2_j]

def l3_i := Level.dense 0 6
def l3_j := Level.dense 1 6
def c3 := contextFromData "m3" [l3_i, l3_j]

def mat2_level0 : Expr := .read "n" 0 .root
def mat2_level1 : Expr := .read "n" 1 (.read "n" 0 .root)
#eval mat2_level1.eval c2


def mat3_level0 : Expr := .read "m3" 0 .root
def mat3_level1 : Expr := .read "m3" 1 (.read "m3" 0 .root)
#eval mat3_level1.eval c3

end SAM

/-
inductive StopCont
| stop
| cont
deriving Repr

partial def binaryIntersectHelper (xr: Stream ℕ) (xc: Stream ℕ) (a1: StopCont) (yr: Stream ℕ)(yc: Stream ℕ) (a2: StopCont) (res_c: Stream ℕ) (res_rx: Stream ℕ) (res_ry: Stream ℕ): Stream ℕ × Stream ℕ × Stream ℕ  :=
match xr, xc, a1, yr, yc, a2 with
| [], _, _, _, _, _
| _, [], _, _, _, _
| _, _, _, [], _, _
| _, _, _, _, [], _
| Token.done::_, _, _, _, _, _ => (res_c, res_rx, res_ry)
| _, Token.done::_, _, _, _, _ => (res_c, res_rx, res_ry)
| _, _, _, Token.done::_, _, _ => (res_c, res_rx, res_ry)
| _, _, _, _, Token.done::_, _ => (res_c, res_rx, res_ry)
| xs_r, xs_c, .stop, y::ys_r, Token.val v ::ys_c, .cont
    => binaryIntersectHelper xs_r xs_c .stop ys_r ys_c .cont res_c res_rx res_ry
| x::xs_r, Token.val v ::xs_c, .cont, ys_r, ys_c, .stop
    => binaryIntersectHelper xs_r xs_c .cont ys_r ys_c .stop res_c res_rx res_ry
| r_x::xs_r, Token.val v_x::xs_c, .cont, r_y::ys_r, Token.val v_y::ys_c, .cont
    => if v_x < v_y
      then binaryIntersectHelper xs_r xs_c .cont yr yc .cont res_c res_rx res_ry
      else if v_x > v_y
        then binaryIntersectHelper xr xc .cont ys_r ys_c .cont res_c res_rx res_ry
        else binaryIntersectHelper xs_r xs_c .cont ys_r ys_c .cont (Token.val v_x::res_c) (r_x::res_rx) (r_y::res_ry)
--| xs, Token.stop n_x::xs_c, .cont, ys,
| _, _, _, _, _, _ => ([], [], [])
-/
