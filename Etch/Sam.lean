import Mathlib.Tactic

/- todo
- Multi intersect/union
- Ref/Crd/Val distinction
- think about changing expr data structure
- fix level scanner
- Fix types to be different for values
- Generalize vector reducer (type and dimension)
- remove partial def on extendlist method
- get rid of level number in level constructor
-/

namespace SAM

inductive Token (ι : Type)
| stop (n : Nat)
| val (x : ι)
| done
| empty
deriving Repr

instance : OfNat (Token Nat) n where
  ofNat := Token.val n

def Token.comp [Ord ι]: Token ι → Token ι → Ordering
  | Token.empty, _ => Ordering.eq
  | _, Token.empty => Ordering.eq
  | Token.done, Token.done => Ordering.eq
  | _, Token.done => Ordering.lt
  | Token.done, _ => Ordering.gt
  | Token.stop n1, Token.stop n2 => Ord.compare n1 n2
  | _, Token.stop _ => Ordering.lt
  | Token.stop _, _ => Ordering.gt
  | Token.val v1, Token.val v2 => Ord.compare v1 v2

instance [Ord ι]: Ord (Token ι) where
  compare := Token.comp

-- Treat empty tokens as zeros
def Token.add [Add α]: Token α → Token α → Token α
  | Token.val v1, Token.val v2 => Token.val (v1 + v2)
  | Token.empty, Token.val v => Token.val v
  | Token.val v, Token.empty => Token.val v
  | Token.stop n, Token.stop _ => Token.stop n
  | Token.done, Token.done => Token.done
  | _, _ => Token.empty --invalid

def Token.mul [OfNat α 0] [Mul α]: Token α → Token α → Token α
  | Token.val v1, Token.val v2 => Token.val (v1 * v2)
  | Token.empty, Token.val _ => Token.val 0
  | Token.val _, Token.empty => Token.val 0
  | Token.stop n, Token.stop _ => Token.stop n
  | Token.done, Token.done => Token.done
  | _, _ => Token.empty --invalid

instance [Add α]: Add (Token α) where
  add := Token.add

instance [OfNat α 0] [Mul α]: Mul (Token α) where
  mul := Token.mul

instance [OfNat α 0]: OfNat (Token α) 0 where
  ofNat := Token.val 0

variable {ι : Type} [Zero ι]

abbrev Stream (ι : Type) := List (Token ι)


inductive SAMStream (ι: Type) (α: Type)
| ref (r: Stream ι)
| crd (c: Stream ι)
| val (v: Stream α)
deriving Repr

abbrev Ident := String

inductive Level
| null
| dense (n: Nat) (size: Nat)
| compressed (n: Nat) (v1: List Nat) (v2: List Nat)
deriving Repr

structure Ctxt (α: Type) (ι : Type) where
levels: Ident → (List Level)
val: Ident → (List α)

#check Level.dense 0 3
#check Level.compressed 1 [0, 3] [0, 3, 5]

def emptyContext : Ctxt α ι where
levels := fun _ => []
val := fun _ => []

def range (a b: ℕ) := List.range (b-a) |>.map (.+a)

def getLevel (n: ℕ) (ident: Ident) (c: Ctxt α ι) : Level :=
  if h: n < (c.levels ident).length then (c.levels ident)[n]'h else Level.null

def getChildren (level: Level) (i: Nat): List ℕ × List ℕ :=
match level with
| Level.dense _ size => (range (size*i) (size*i+size), range 0 size)
| Level.compressed _ v1 v2 => if h: (i+1) < v1.length
                then have h': i < v1.length := by { exact Nat.lt_of_succ_lt h }
                  if h2: v1[i+1] <= v2.length ∧ v1[i]'h' < v2.length
                  then (range v1[i] v1[i+1], v2.toArray[v1[i]:v1[i+1]].toArray.toList)
                  else ([], [])
                else ([], [])
| Level.null => ([], [])

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
--| vecreducer (input_c: Expr) (input_v: Expr) -- input/output 1 coordinate streams and one value stream

def binaryIntersectHelper [Ord (Token ι)] (xr: Stream ι) (xc: Stream ι) (yr: Stream ι)(yc: Stream ι) (res_c: Stream ι) (res_rx: Stream ι) (res_ry: Stream ι): Stream ι × Stream ι × Stream ι :=
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

def nonControlTokensHelper (s: Stream ι) (res: List ι) : List ι :=
  match s with
  | [] => res
  | Token.val v::rest => nonControlTokensHelper rest (res ++ [v])
  | _::rest => nonControlTokensHelper rest res

def nonControlTokens (s: Stream ι) : List ι := nonControlTokensHelper s []

def repeaterHelper (crd: Stream ι) (ref: List ι) (res: Stream ι) (i: ℕ): Stream ι :=
match crd with
| [] => [] -- Input error, no done token
| Token.val _::rest => if h:i < ref.length then
  repeaterHelper rest ref (res ++ [Token.val ref[i]]) i
  else [] -- Input error
| Token.empty::rest => repeaterHelper rest ref res i
| Token.stop n::rest => match rest with
   | Token.val _::_ => repeaterHelper rest ref (res ++ [Token.stop n]) (i+1)
   | _ => repeaterHelper rest ref (res ++ [Token.stop n]) i
| Token.done::_ => (res ++ [Token.done])

-- Repeat each non-control token in ref m times, where m is number of non-control tokens in crd seen before a stop token is seen
-- number of non-control tokens in ref stream is equal to number of control tokens in crd stream
-- Output ref stream has same shape as input crd stream
def Repeat (crd: Stream ι) (ref: Stream ι): Stream ι :=
  repeaterHelper crd (nonControlTokens ref) [] 0

#eval Repeat ([3, Token.stop 0, 4, 5, Token.stop 1, Token.done] : Stream Nat) ([0, 1, Token.stop 0, Token.done] : Stream Nat)

--#eval vecReduceHelper [.val 1, .val 2, .stop 0, .val 2, .done] [.val 3, .val 4, .stop 0, .val 3, .done] []

def VecReduce [OfNat α 0] [Add α] (crds: Stream ℕ) (vals: Stream α) : Stream ℕ × Stream α := sorry

--#eval VecReduce [.val 1, .val 2, .stop 0, .val 2, .done] [.val 3, .val 4, .stop 0, .val 3, .done]
--#eval VecReduce ([3, 4, .stop 0, 4, .stop 1, 3, 4, .stop 1, 0, 5, .stop 2, .done]: Stream Nat) ([1, 2, .stop 0, 25, .stop 1, 3, 6, .stop 1, 54, 63, .stop 2, .done]: Stream Nat)

def levelScanHelper (level: Level) (inputref: Stream ℕ) (res_r: Stream ℕ) (res_c: Stream ℕ): List (Stream ℕ) :=
  match inputref with
  | Token.done::_ => [res_r ++ [Token.done], res_c ++ [Token.done]]
  | Token.val i::rest => match rest with -- If next token is a stop token, don't emit a stop 0
      | Token.stop _::_ => levelScanHelper level rest
            (res_r ++ ((getChildren level i).fst |>.map .val))
            (res_c ++ ((getChildren level i).snd |>.map .val))
      | _ => levelScanHelper level rest
            (res_r ++ ((getChildren level i).fst |>.map .val) ++ [Token.stop 0])
            (res_c ++ ((getChildren level i).snd |>.map .val) ++ [Token.stop 0])
  | Token.stop n::rest => levelScanHelper level rest (res_r ++ [Token.stop (n+1)]) (res_c ++ [Token.stop (n+1)])
  | Token.empty::rest => levelScanHelper level rest (res_r ++ [Token.stop 0]) (res_c ++ [Token.stop 0])
  | [] => [] -- Invalid input

def LevelScan (ctxt: Ctxt α ℕ) (name: Ident) (l: ℕ) (inputref: Stream ℕ) : List (Stream ℕ) :=
  let level := getLevel l name ctxt
  levelScanHelper level inputref [] []

--def Expr.eval [OfNat ι 0] [Ord ι] [Mul ι] [Add ι] (ctxt : Ctxt α ι) (e : Expr) : List (Stream ι) :=
def Expr.eval (ctxt: Ctxt ℕ ℕ) (e: Expr) : List (Stream ℕ) :=
match e with
| root => [[.val 0, .done]]
| .scan name level input =>
  if h:(input.eval ctxt).length > 0
    then let is := (input.eval ctxt)[0]'h
    LevelScan ctxt name level is
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
      let val : List (Stream ℕ) := is.map fun token =>
        match token with
        | .val i => if h: i < (ctxt.val name).length then [Token.val (ctxt.val name)[i] ]
          else []
        | ctrl => [ctrl]
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
/-|.vecreducer inputc inputv =>
  if h:(inputc.eval ctxt).length > 0 ∧ (inputv.eval ctxt).length > 0
  then let crd := (inputc.eval ctxt)[0]'h.left
       let val := (inputv.eval ctxt)[0]'h.right
       let result := VecReduce crd val
      [result.fst, result.snd]
  else []-/

def contextFromData (ident: Ident) (inputlevels: List Level) (inputvals: List Nat): Ctxt ℕ ℕ where
  levels := fun name => if name = ident then inputlevels
      else []
  val := fun name  =>
    if name = ident then inputvals
    else []

def joinContexts (ident1: Ident) (c1: Ctxt α ι) (ident2: Ident) (c2: Ctxt α ι): Ctxt α ι where
levels := fun name =>
    if name = ident1 then c1.levels ident1
    else if name = ident2 then c2.levels ident2
    else []
val := fun name =>
    if name = ident1 then c1.val ident1
    else if name = ident2 then c2.val ident2
    else []
end SAM
