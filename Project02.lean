import Mathlib.Tactic
open Function

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
section
-- As a final project, these tasks are not simply
-- asking you to give proofs: you have to come up
-- with what to prove!
--
-- Define a function f of _your choice_ from A to B.
def A : Type := ℕ
def B : Type := ℕ
def f : A → B := fun x => Nat.succ x

-- Show that your function f is injective...
lemma inj : Injective f := by
  unfold Injective
  intro a b h
  unfold f at h
  have h1 : Nat.succ a - Nat.succ b = 0 := tsub_eq_of_eq_add_rev h
  have h2 : Nat.succ a - Nat.succ b = Nat.rawCast a - Nat.rawCast b := Nat.succ_sub_succ a b
  rw [h2] at h1
  have h3 : Nat.rawCast a - Nat.rawCast b + Nat.rawCast b = 0 + Nat.rawCast b := congrFun (congrArg HAdd.hAdd h1) (Nat.rawCast b)
  
  
-- But that your function f is not surjective.
lemma not_surj : ¬ Surjective f := by
  unfold Surjective
  push_neg
  sorry

end section

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
section

-- Given a function f : A → B...
variable {A B : Type*}
variable (f : A → B)
-- and subsets A' ⊆ A and B' ⊆ B...
variable (A' : Set A)
variable (B' : Set B)

-- prove that f(A') ∩ B' = f(f⁻¹(B') ∩ A').
lemma projection_formula : (f '' A') ∩ B' = f '' (f ⁻¹' B' ∩ A') := by
  have h1 : f '' A' = B' := by
    refine Iff.mpr Set.Subset.antisymm_iff ?_
    constructor
    intro y h
    simp only [Set.mem_image] at h
    rcases h with ⟨x, h⟩
    
    
  have h2 : f ⁻¹' B' = A' := by
    sorry
  rw [h1, h2]
  simp only [Set.inter_self]
  rw [h1]

end section
