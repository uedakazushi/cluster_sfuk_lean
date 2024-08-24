import Mathlib
import ClusterSfukLean.FunctionPhi

section main_def

variable (e f: ℕ+)
variable (i : ℕ)
variable (e_ge_2 : (e:Nat) ≥ 2)
variable (f_ge_2 : (f:Nat) ≥ 2)

def setI (e f i : ℕ) : Set ℕ :=
  {b : ℕ |
  b % e ≠ e - 1
  ∧ b % f ≠ f - 1
  ∧ b / e + b / f = i }

lemma I_as_a_subset_of_preimage_φ : setI e f i = { n ∈ (φ e f) ⁻¹' { m : ℕ | m = i } | n % e ≠ e - 1 ∧ n % f ≠ f - 1} := by
  apply Set.eq_of_subset_of_subset
  { intro x
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    apply And.intro
    { apply h3 }
    { apply And.intro
      { apply h1 }
      { apply h2 }
    }
  }
  { intro x
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    apply And.intro
    { assumption }
    { apply And.intro
      { assumption }
      { assumption }
    }
  }

def setII : Set ℕ :=
  {n : ℕ |
  n % e = e - 1
  ∧ n % f = f - 1
  ∧ n / e + n / f + 1 = i }

def setIII : Set ℂ :=
  {ξ : ℂ |
  ξ ≠ 1
  ∧ ξ^(e:ℕ) = 1
  ∧ ξ^(f:ℕ) = 1 }

lemma Nat_le_add_right (a b : ℕ) : a ≤ a + b := by
  linarith

lemma setI_finite : (setI e f i).Finite := by
  have setI_bdd : ∃ k : ℕ, ∀ n ∈ setI e f i, n ≤ k := by
    exists e*i+e
    intro n
    dsimp [setI]
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    have h4 : n/e ≤ i := by
      have h5 : n / e ≤ n/e+n/f := by
        apply Nat_le_add_right
      linarith
    have h6 := nat_div_pnat_le n i e
    exact h6 h4
  apply finite_of_bounded_of_Nat
  assumption

lemma setII_finite : (setII e f i).Finite := by
  sorry

lemma setIII_finite : (setIII e f).Finite := by
  sorry

noncomputable def finsetI : Finset ℕ :=
  (setI_finite e f i).toFinset

noncomputable def finsetII : Finset ℕ :=
  (setII_finite e f i).toFinset

noncomputable def finsetIII : Finset ℂ :=
  (setIII_finite e f).toFinset

noncomputable def cardI : ℕ := (finsetI e f i).card

noncomputable def cardII : ℕ := (finsetII e f i).card

noncomputable def cardIII : ℕ := (finsetIII e f).card

noncomputable def h : ℕ := (cardI e f i + (cardII e f i) * (cardIII e f))

end main_def
