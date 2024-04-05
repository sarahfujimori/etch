import Etch.Sam

namespace SAM
------------------------------------------------------------------
-- Vector Examples
------------------------------------------------------------------
/-
v1: compressed [0 3] [0 3 5] vals: [1 4 6] i.e. [1, 0, 0, 4, 0, 6]
v2: dense [6] vals: [1, .. 6] i.e. [1, 2, 3, 4, 5, 6]
-/
def c_v1 : Ctxt ℕ ℕ := contextFromData "v1" [(Level.compressed [0, 3] [0, 3, 5])] [1, 4, 6]
def c_v2 : Ctxt ℕ ℕ := contextFromData "v2" [(Level.dense 6)] [1, 2, 3, 4, 5, 6]
def c_v := joinContexts "v1" c_v1 "v2" c_v2

def crd_cap : Expr := .intersect (.scan "v1" 0 .root) (.scan "v2" 0 .root)
def cap_vals1 : Expr := .array_load "v1" (.select 1 crd_cap)
def cap_vals2 : Expr := .array_load "v2" (.select 2 crd_cap)
def res_vals_cap : Expr := .mul cap_vals1 cap_vals2
--#eval res_vals_cap.eval c_v

def crd_cup : Expr := .union (.scan "v1" 0 .root) (.scan "v2" 0 .root)
def cup_vals1 : Expr := .array_load "v1" (.select 1 crd_cup)
def cup_vals2 : Expr := .array_load "v2" (.select 2 crd_cup)
def res_vals_cup : Expr := .add cup_vals1 cup_vals2
--#eval crd_cup.eval c_v

------------------------------------------------------------------
-- Matrix Examples
------------------------------------------------------------------
/- Example m1 sparse 6x6
i: [0 3]
   [0 3 5]
j: [0 2 4 5]
   [1 4 0 1 5]
val: [1 5 2 3 9]

Example m2 sparse 6x6:
i: [0 5]
   [1 2 3 4 5]
j: [0 2 3 4 5 7]
   [3 4 2 1 4 0 5]
val: [1 2 3 4 5 6 7]

Example matrix (Dense) 6x6
i: [6] j: [6], vals: [0, ..., 35] -/

def root : Expr := .root
#eval root.eval (emptyContext (ι := Nat))

def mat1_level0 : Expr := .scan "m1" 0 .root
def mat1_level1 : Expr := .scan "m1" 1 (.scan "m1" 0 .root)
def mat1_val : Expr := .array_load "m1" (.select 0 mat1_level1)

def l1_i := Level.compressed [0, 3] [0, 3, 5]
def l1_j := Level.compressed [0, 2, 4, 5] [1, 4, 0, 1, 5]
def l1_v := [1, 5, 2, 3, 9]
def c1 := contextFromData "m1" [l1_i, l1_j] l1_v

#eval mat1_level0.eval c1
#eval mat1_level1.eval c1
#eval mat1_val.eval c1


def l2_i := Level.compressed [0, 5] [1, 2, 3, 4, 5]
def l2_j := Level.compressed [0, 2, 3, 4, 5, 7] [3, 4, 2, 1, 4, 0, 5]
def l2_v := [1, 2, 3, 4, 5, 6, 7]
def c2 := contextFromData "m2" [l2_i, l2_j] l2_v

def l3_i := Level.dense 6
def l3_j := Level.dense 6
def l3_v := range 0 36
def c3 := contextFromData "m3" [l3_i, l3_j] l3_v

def mat2_level0 : Expr := .scan "m2" 0 .root
def mat2_level1 : Expr := .scan "m2" 1 (.scan "m2" 0 .root)
#eval mat2_level1.eval c2


def mat3_level0 : Expr := .scan "m3" 0 .root
def mat3_level1 : Expr := .scan "m3" 1 (.scan "m3" 0 .root)
#eval mat3_level1.eval c3

/-
def m1_cup_m3_level0 : Expr := .union mat1_level0 mat3_level0
def add_m1_level1 : Expr := .scan "m1" 1 (.select 1 m1_cup_m3_level0)
def add_m3_level1 : Expr := .scan "m3" 1 (.select 2 m1_cup_m3_level0)
def cup_level1 : Expr := .union add_m1_level1 add_m3_level1
def cup_m1_vals : Expr := .array_load "m1" (.select 1 cup_level1)
def cup_m3_vals : Expr := .array_load "m3" (.select 2 cup_level1)
def add_vals : Expr := .add cup_m1_vals cup_m3_vals
def result := add_vals.eval c
#eval result
-/
def c12 := joinContexts "m1" c1 "m2" c2
def m1_cup_m2_level0 : Expr := .union mat1_level0 mat2_level0
def add_m1_level1 : Expr := .scan "m1" 1 (.select 1 m1_cup_m2_level0)
def add_m2_level1 : Expr := .scan "m2" 1 (.select 2 m1_cup_m2_level0)
def cup_level1 : Expr := .union add_m1_level1 add_m2_level1
def cup_m1_vals : Expr := .array_load "m1" (.select 1 cup_level1)
def cup_m2_vals : Expr := .array_load "m2" (.select 2 cup_level1)
def add_vals : Expr := .add cup_m1_vals cup_m2_vals
def result := add_vals.eval c12
#eval result
#eval (Expr.select 0 cup_level1).eval c12

------------------------------------------------------------------
-- Matrix Mul
/- Example m1 sparse 6x6        [0, 1, 0, 0, 5, 0]
i: [0 3]                        [0, 0, 0, 0, 0, 0]
   [0 3 5]                      [0, 0, 0, 0, 0, 0]
k: [0 2 4 5]                    [2, 3, 0, 0, 0, 0]
   [1 4 0 1 5]                  [0, 0, 0, 0, 0, 0]
val: [1 5 2 3 9]                [0, 0, 0, 0, 0, 9]

Example m2 sparse 6x6:          [0, 0, 0, 0, 0, 0]
k: [0 5]                        [0, 0, 0, 1, 2, 0]
   [1 2 3 4 5]                  [0, 0, 3, 0, 0, 0]
j: [0 2 3 4 5 7]                [0, 4, 0, 0, 0, 0]
   [3 4 2 1 4 0 5]              [0, 0, 0, 0, 5, 0]
val: [1 2 3 4 5 6 7]            [6, 0, 0, 0, 0, 7]

m1*m2:                          [ 0, 0, 0, 1, 27,  0]
                                [ 0, 0, 0, 0,  0,  0]
                                [ 0, 0, 0, 0,  0,  0]
                                [ 0, 0, 0, 3,  6,  0]
                                [ 0, 0, 0, 0,  0,  0]
                                [54, 0, 0, 0,  0, 63]
i: [0 3]
   [0 3 5]
j: [0 2 4 6]
   [3 4 3 4 0 5]
val: [1 27 3 6 54 63]
-/
------------------------------------------------------------------

def m1_i := mat1_level0 -- [ref, crd]
def repeater1 : Expr := .repeater (.select 1 m1_i) .root
def m2_k : Expr := .scan "m2" 0 repeater1 -- [ref, crd]
def m1_k : Expr := .scan "m1" 1 (.select 0 m1_i) -- [ref, crd]
def m1_cap_m2_k : Expr := .intersect m1_k m2_k -- [crd, ref1, ref2]
def m2_j : Expr := .scan "m2" 1 (.select 2 m1_cap_m2_k) -- [crd, ref]
def repeater2 : Expr := .repeater (.select 1 m2_j) (.select 1 m1_cap_m2_k)
def array1 : Expr := .array_load "m1" repeater2
def array2 : Expr := .array_load "m2" (.select 0 m2_j)
def mul_values : Expr := .mul array1 array2
#eval array1.eval c12 -- [1, 1, 5, 5, s0, 3, 3, s0, 9, 9, s0, d]
#eval array2.eval c12 -- [1, 2, s0, 5, s0, s1, 1, 2, s0, s1, 6, 7, s0, s1, d]

def mul_values_eval : List (Stream ℕ) := mul_values.eval c12
#eval mul_values_eval
