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
def f : A → B := fun x => Nat.pow x 2

-- Show that your function f is injective...
lemma inj : Injective f := by
  unfold Injective
  unfold f
  intro (a : ℕ) (b : ℕ) h
  simp only [Nat.pow_eq] at h
  have h1 : Nat.sqrt (a^2) = Nat.sqrt (b^2) := by exact congrArg Nat.sqrt h
  have h2 : Nat.sqrt (a^2) = a := by exact Nat.sqrt_eq' a
  have h3 : Nat.sqrt (b^2) = b := by exact Nat.sqrt_eq' b
  rwa [h2, h3] at h1

-- But that your function f is not surjective.
lemma not_surj : ¬ Surjective f := by
  unfold Surjective
  push_neg
  use (5 : ℕ)
  unfold f
  intro (a : ℕ) h
  simp only [Nat.pow_eq] at h
  have h1 : Nat.sqrt (a^2) = Nat.sqrt (5) := by exact congrArg Nat.sqrt h
  have h2 : Nat.sqrt (a^2) = a := by exact Nat.sqrt_eq' a
  rw [h2] at h1
  ring_nf at h1
  rw [h1] at h
  ring_nf at h
  have h3 : 4 ≠ 5 := by exact Nat.ne_of_beq_eq_false rfl
  exact h3 h

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
  ext y
  constructor
  intro h
  simp only [Set.mem_inter_iff, Set.mem_image] at h
  rcases h with ⟨⟨x, ⟨h1, h⟩⟩, h'⟩
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
  use x
  constructor
  constructor
  rwa [h]
  tauto
  tauto

  intro h
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage] at h
  rcases h with ⟨x, ⟨⟨h, h1⟩, h'⟩⟩
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  use x
  rwa [h'] at h

end section
