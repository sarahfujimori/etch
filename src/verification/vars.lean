import tactic.derive_fintype
import logic.function.basic
import data.set.function

section vars
@[derive decidable_eq, derive fintype, derive inhabited]
inductive Vars
| i | j | k | w | x | y | z | ind₀ | ind₁ | ind₂ | break | output

open Vars
instance : has_to_string Vars :=
⟨λ v, match v with 
-- S.split(" | ").map(s => s + ' := "' + s + '"')
| i := "i" | j := "j" | k := "k" | w := "w" | x := "x" | y := "y" | z := "z" | ind₀ := "ind₀" | ind₁ := "ind₁" | ind₂ := "ind₂" | break := "break" | output := "output"
end⟩
end vars

section NameSpace
@[derive decidable_eq, derive inhabited, derive has_to_string, reducible]
def NameSpace := ℕ

def NameSpace.reserved : NameSpace := 0

def fresh (S : finset NameSpace) : NameSpace :=
S.max.iget + 1

theorem not_fresh_mem (S : finset NameSpace) : fresh S ∉ S :=
begin
  simp only [fresh],
  cases hn : S.max,
  { rw [finset.max_eq_none] at hn, subst hn, exact finset.not_mem_empty _, },
  intro h, simpa using finset.le_max_of_mem h hn,
end

theorem not_fresh_reserved (S : finset NameSpace) : fresh S ≠ NameSpace.reserved :=
by simp [fresh, NameSpace.reserved]

attribute [irreducible] NameSpace
end NameSpace

@[derive decidable_eq, derive fintype, derive inhabited]
inductive Types
| nn | rr

section Ident

@[derive decidable_eq]
structure Ident (b : Types) :=
(ns : NameSpace)
(name : Vars)

instance {b : Types} : has_to_string (Ident b) :=
⟨λ i, "n" ++ (to_string i.ns) ++ "_" ++ (to_string i.name)⟩

lemma Ident_ns_surjective {b : Types} : function.surjective (@Ident.ns b) :=
by { intro x, use ⟨x, default⟩, }

@[simp] lemma Ident_ns_range {b : Types} : set.range (@Ident.ns b) = set.univ :=
by simpa [set.surjective_iff_surj_on_univ, set.surj_on, set.univ_subset_iff] using Ident_ns_surjective

local infix `∷`:9000 := Ident.mk

end Ident

section frames
-- TODO Fix
variables {α γ : Type*} {β : α → Type*} (f : (Π x, β x) → γ) (g : (Π x, β x) → (Π x, β x))

def function.has_dframe (S : set α) : Prop :=
∀ ⦃c₁ c₂ : Π x, β x⦄, (∀ x ∈ S, c₁ x = c₂ x) → f c₁ = f c₂

structure function.has_dheap (S : set α) : Prop :=
(local_frame : ∀ (c₁ c₂ : Π x, β x), (∀ x ∈ S, c₁ x = c₂ x) → ∀ {y}, y ∈ S → g c₁ y = g c₂ y)
(global_id : ∀ (c y), y ∉ S → g c y = c y)

variables {f g}
theorem function.has_dframe.res {S} (h : function.has_dframe f S) (S') (hS' : S ⊆ S') :
  function.has_dframe f S' :=
λ c₁ c₂ h', h (λ x hx, h' _ (hS' hx))

theorem function.has_dheap.res {S} (h : function.has_dheap g S) (S') (hS' : S ⊆ S') :
  function.has_dheap g S' :=
{ local_frame := λ c₁ c₂ c_eq y hy, 
begin
  by_cases H : y ∈ S,
  { exact h.local_frame c₁ c₂ (λ x hx, c_eq _ (hS' hx)) H, },
  { rw [h.global_id c₁ _ H, h.global_id c₂ _ H],  exact c_eq _ hy, },
end,
  global_id := λ c y hy, h.global_id c y (λ H, hy (hS' H)), }

theorem function.has_dframe.const (x : γ) (S : set α) : function.has_dframe (λ _ : Π x, β x, x) S :=
λ _ _ _, rfl

theorem function.has_dheap.id (S : set α) : function.has_dheap (@id (Π x, β x)) S :=
{ local_frame := λ c₁ c₂ h y hy, h y hy,
  global_id := λ _ _ _, rfl }

example {S : set α} {x₀ : α} {y₀ : β x₀} [∀ x, decidable_eq (β x)] (f : (Π x, β x) → (Π x, β x)) (g : (Π x, β x) → γ)
  (hf : function.has_dframe g S) (hg : function.has_dheap f (insert x₀ S)) :
  function.has_dframe (λ ctx, if ctx x₀ = y₀ then g (f ctx) else g ctx) (insert x₀ S) :=
begin
  intros c₁ c₂ c_eq, dsimp only,
  have := (hf.res _ _) c_eq,
  all_goals { sorry, },
end

end frames

section iterate

def iterate_while {α : Type*} (f : α → α) (cond : α → Prop) [decidable_pred cond] : ℕ → α → α := sorry
end iterate
