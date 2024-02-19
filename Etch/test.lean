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

-- Treat empty tokens as zeros
def Token.add: Token ℕ → Token ℕ → Token ℕ
  | Token.val v1, Token.val v2 => Token.val (v1 + v2)
  | Token.empty, Token.val v => Token.val v
  | Token.val v, Token.empty => Token.val v
  | Token.stop n, Token.stop _ => Token.stop n
  | Token.done, Token.done => Token.done
  | _, _ => Token.empty --invalid

def Token.mul: Token ℕ → Token ℕ → Token ℕ
  | Token.val v1, Token.val v2 => Token.val (v1 * v2)
  | Token.empty, Token.val _ => Token.val 0
  | Token.val _, Token.empty => Token.val 0
  | Token.stop n, Token.stop _ => Token.stop n
  | Token.done, Token.done => Token.done
  | _, _ => Token.empty --invalid

instance: Add (Token ℕ) where
  add := Token.add

instance: Mul (Token ℕ) where
  mul := Token.mul

variable {ι : Type} [Zero ι]

abbrev Stream (ι : Type) := List (Token ι)

abbrev Ident := String

-- todo: `tree-like' structure
inductive Format
inductive Expr
| root
| scan (name : Ident) (level : Nat) (input : Expr)
| add (input1: Expr) (input2: Expr)
| mul (input1: Expr) (input2: Expr)
| array_load (name : Ident) (input: Expr)
| select (i: Nat) (input : Expr) -- output of Expr is currently list of streams, select ith stream
| intersect (input1: Expr) (input2: Expr) -- input1 and input2 are both (ref, crd) pairs; currently only binary intersect
| union (input1: Expr) (input2: Expr) -- input1 and input2 are both (ref, crd) pairs; currently only binary union
| repeater (inputc: Expr) (inputr: Expr) -- inputc is one crd stream, inputr is one ref stream

structure Ctxt (ι : Type) where
 -- name -> level -> index -> (ref, crd) for list of children
  level_data : Ident → Nat → ι → Prod (List ι) (List ι)
 -- name -> index -> val
  val_data : Ident → ι → ι

partial def binaryIntersectHelper [Ord (Token ι)] (xr: Stream ι) (xc: Stream ι) (yr: Stream ι)(yc: Stream ι) (res_c: Stream ι) (res_rx: Stream ι) (res_ry: Stream ι): Stream ι × Stream ι × Stream ι :=
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
    binaryIntersectHelper (r_x::xs_r) (c_x::xs_c) ys_r ys_c res_c res_rx res_ry
|  _, _, _, _ => (res_c, res_rx, res_ry)

def BinaryIntersect [Ord (Token ι)] (r1: Stream ι) (c1: Stream ι) (r2: Stream ι)(c2: Stream ι) : Stream ι × Stream ι × Stream ι :=
  (λ(z1, z2, z3) => (List.reverse z1, List.reverse z2, List.reverse z3)) (binaryIntersectHelper r1 c1 r2 c2 [] [] [])

-- todo
def MultiIntersect (l: List (Stream ι × Stream ι)): Stream ι × (List (Stream ι)) := sorry

--todo: remove this partial def
def binaryUnionHelper [Ord (Token ι)] (xr: Stream ι) (xc: Stream ι) (yr: Stream ι)(yc: Stream ι) (res_c: Stream ι) (res_rx: Stream ι) (res_ry: Stream ι): Stream ι × Stream ι × Stream ι :=
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
    binaryUnionHelper (r_x::xs_r) (c_x::xs_c) ys_r ys_c (c_y::res_c) (Token.empty::res_rx) (r_y::res_ry)
|  _, _, _, _ => (res_c, res_rx, res_ry)

def BinaryUnion [Ord (Token ι)] (r1: Stream ι) (c1: Stream ι) (r2: Stream ι)(c2: Stream ι) : Stream ι × Stream ι × Stream ι :=
  (λ(z1, z2, z3) => (List.reverse z1, List.reverse z2, List.reverse z3)) (binaryUnionHelper r1 c1 r2 c2 [] [] [])

-- todo
def MultiUnion (l: List (Stream ℕ × Stream ℕ)): Stream ℕ × (List (Stream ℕ)) := sorry

def xr : Stream ℕ := [Token.val 0, Token.val 1, Token.stop 0, Token.done]
def xc : Stream ℕ := [Token.val 3, Token.val 4, Token.stop 0, Token.done]
def yr : Stream ℕ := [Token.val 1, Token.val 2, Token.stop 0, Token.done]
def yc : Stream ℕ := [Token.val 4, Token.val 5, Token.stop 0, Token.done]
#eval BinaryIntersect xr xc yr yc
#eval BinaryUnion xr xc yr yc

def repeaterHelper (crd: Stream ι) (ref: Stream ι) (m: ℕ): Stream ι :=
match crd with
| [] => [] -- This case should never happen since every stream has a done token
| Token.val _::crds => repeaterHelper crds ref (m+1)
| Token.empty::crds => repeaterHelper crds ref m     -- Ignore empty tokens
| _::_ => let val : List (Stream ι) := ref.map fun token => match token with
        | .val i => List.range m |>.map (fun _ => .val i)
        | c => [c]
      val.join

-- Repeat each non-control token in ref m times, where m is number of non-control tokens in crd seen before a stop token is seen
def Repeat (crd: Stream ι) (ref: Stream ι): Stream ι :=
  repeaterHelper crd ref 0

#eval Repeat xc xr -- should be [0, 0, 1, 1, s0, done]

def Expr.eval [Ord (Token ι)] [Mul (Token ι)] [Add (Token ι)] (ctxt : Ctxt ι) (e : Expr) : List (Stream ι) :=
match e with
| root => [[.val 0, .done]]
| .scan name level input =>
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
      | .val i => ((ctxt.level_data name level i).fst |>.map .val) ++ [Token.stop 0] -- ?: Don't add this to the last one?
      | .stop n => [.stop (n+1)]
      | .done => [.done]
      | .empty => [.stop 0] -- ?
    let crd : List (Stream ι) := is.map fun token =>
      match token with
      | .val i => ((ctxt.level_data name level i).snd |>.map .val) ++ [Token.stop 0] -- ?: Don't add this to the last one?
      | .stop n => [.stop (n+1)]
      | .done => [.done]
      | .empty => [.stop 0] -- ?
    [ref.join, crd.join]
  else []
| .add input1 input2 =>
  if h:(input1.eval ctxt).length > 0 ∧ (input2.eval ctxt).length > 0
  then let is := (input1.eval ctxt)[0]'h.left
       let js := (input2.eval ctxt)[0]'h.right
       if h: is.length = js.length
       then [List.range is.length |>.map (λ i => if h_i:i < is.length then
          have h_j: i < js.length := by { rw [← h]; exact h_i }
          is[i]'h_i + js[i]'h_j else Token.empty)]
       else []
  else []
| .mul input1 input2 =>
  if h:(input1.eval ctxt).length > 0 ∧ (input2.eval ctxt).length > 0
  then let is := (input1.eval ctxt)[0]'h.left
       let js := (input2.eval ctxt)[0]'h.right
       if h: is.length = js.length
       then [List.range is.length |>.map (λ i => if h_i:i < is.length then
          have h_j: i < js.length := by { rw [← h]; exact h_i }
          is[i]'h_i * js[i]'h_j else Token.empty)]
       else []
  else []
| .array_load name input =>
  if h:(input.eval ctxt).length > 0
    then let is := (input.eval ctxt)[0]'h
      let val : List (Stream ι) := is.map fun token =>
        match token with
        | .val i => [Token.val (ctxt.val_data name i)] -- ?: Don't add this to the last one?
        | c => [c]
      [val.join]
    else []
| select i input =>
  if h:i < (input.eval ctxt).length
    then [(input.eval ctxt)[i]'h]
    else []
| .intersect input1 input2 =>
  if h: (input1.eval ctxt).length > 1 ∧ (input2.eval ctxt).length > 1
  then have h1: (input1.eval ctxt).length > 0 := by linarith --{exact Nat.lt_of_succ_lt h.left}
       have h2: (input2.eval ctxt).length > 0 := by {exact Nat.lt_of_succ_lt h.right}
       let r1 := (input1.eval ctxt)[0]'h1
       let c1 := (input1.eval ctxt)[1]'h.left
       let r2 := (input2.eval ctxt)[0]
       let c2 := (input2.eval ctxt)[1]'h.right
       let p := BinaryIntersect r1 c1 r2 c2
       [p.fst, p.snd.fst, p.snd.snd]
  else []
| .union input1 input2 =>
  if h: (input1.eval ctxt).length > 1 ∧ (input2.eval ctxt).length > 1
  then have h1: (input1.eval ctxt).length > 0 := by {exact Nat.lt_of_succ_lt h.left}
       have h2: (input2.eval ctxt).length > 0 := by {exact Nat.lt_of_succ_lt h.right}
       let r1 := (input1.eval ctxt)[0]'h1
       let c1 := (input1.eval ctxt)[1]'h.left
       let r2 := (input2.eval ctxt)[0]'h2
       let c2 := (input2.eval ctxt)[1]'h.right
       let p := BinaryUnion r1 c1 r2 c2
       [p.fst, p.snd.fst, p.snd.snd]
  else []
|.repeater inputc inputr =>
  if h:(inputc.eval ctxt).length > 0 ∧ (inputr.eval ctxt).length > 0
  then let crd := (inputc.eval ctxt)[0]'h.left
       let ref := (inputr.eval ctxt)[0]'h.right
    [Repeat crd ref]
  else []

inductive Level
| dense (n: Nat) (size: Nat)
| compressed (n: Nat) (v1: List Nat) (v2: List Nat)
deriving Repr

#check Level.dense 0 3
#check Level.compressed 1 [0, 3] [0, 3, 5]

def emptyContext : Ctxt ι where
  level_data := fun _ _ _  => ([], [])
  val_data := fun _ _ => 0

def range (a b: ℕ) := List.range (b-a) |>.map (.+a)

def contextFromData (ident: Ident) (levels: List Level) (vals: List Nat): Ctxt (ι := Nat) where
  -- level_data : Ident → ι → List ι
  -- ?: Write this function in a better way
  level_data := fun name =>
    if name = ident -- Check if name is valid
      then (fun n =>
        if h : n < levels.length -- Check if level number is valid
          then fun i =>
            match levels[n]'h with
            | Level.dense _ size => (range (size*i) (size*i+size), range 0 size)
            | Level.compressed _ v1 v2 =>
              if h: (i+1) < v1.length
                then have h': i < v1.length := by { exact Nat.lt_of_succ_lt h }
                  if h2: v1[i+1] <= v2.length ∧ v1[i]'h' < v2.length
                  then (range v1[i] v1[i+1], v2.toArray[v1[i]:v1[i+1]].toArray.toList)
                  else ([], [])
                else ([], [])
          else fun _ => ([], []))
      else fun _ _ => ([], [])
  val_data := fun name  =>
    if name = ident
      then (fun i =>
        if h: i < vals.length
          then vals[i]
          else 0
      )
    else 0

def joinContexts (ident1: Ident) (c1: Ctxt (ι := Nat)) (ident2: Ident) (c2: Ctxt (ι := Nat)): Ctxt (ι:=Nat) where
  level_data := fun name =>
    if name = ident1 then c1.level_data name
    else if name = ident2 then c2.level_data name
    else fun _ _ => ([], [])
  val_data := fun name =>
    if name = ident1 then c1.val_data name
    else if name = ident2 then c2.val_data name
    else 0

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
