import Mathlib

lemma finite_test (k:Nat) : Set.Finite {n : Nat | n ≤ k } := by
  exact Set.finite_le_nat k

#check Set.Finite.subset

lemma finite_of_bounded_of_Nat (s: Set ℕ) :
  ∃ k : ℕ, ∀ x ∈ s, x ≤ k → s.Finite := by
  sorry

section

variable (e f : ℕ+)
variable (i : ℕ)

def setI : Set ℕ :=
  {n : ℕ |
  n % e ≠ e - 1
  ∧ n % f ≠ f - 1
  ∧ n / e + n / f = i }

def setII : Set ℕ :=
  {n : ℕ |
  n % e = e - 1
  ∧ n % f = f - 1
  ∧ n / e + n / f + 1 = i }

lemma setI_finite : Set.Finite (setI e f i) := by
  have setI_bdd : (setI e f i) ⊆ {n : ℕ | n ≤ e * i + e} := by
    rw [Set.subset_def]
    intro x
    intro h
    simp [setI] at h
    have h1 : x / ↑e + x / ↑f = i := h.right.right
    simp
    have h2 : x / ↑e ≤ i := by sorry
    sorry

lemma setII_finite : Set.Finite (setII e f i) := by
  sorry

noncomputable def finsetI : Finset ℕ := Set.Finite.toFinset (setI_finite e f i)

noncomputable def finsetII : Finset ℕ := Set.Finite.toFinset (setII_finite e f i)

noncomputable def cardI : ℕ := (finsetI e f i).card

noncomputable def cardII : ℕ := (finsetII e f i).card

noncomputable def h : ℕ := (cardI e f i) + (cardII e f i)

end

section

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
end
