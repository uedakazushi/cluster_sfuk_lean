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

def setIII : Set ℂˣ :=
  {ξ : ℂˣ |
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

lemma setII_zero : setII e f 0 = ∅ := by
  dsimp [setII]
  by_contra h
  push_neg at h
  match h with
  | ⟨ n, _, _, h3 ⟩ =>
    have h4 (a : Nat) : a + 1 = 0 → False := by
      intro h5
      linarith
    have h5 := h4 (n/e+n/f)
    exact h5 h3

lemma setII_sub_φinv : setII e f (i+1) ⊆ φinv e f i := by
  intro n
  intro h
  simp [φinv]
  simp [setII] at h
  simp [φ]
  exact h.2.2

lemma setII_finite : (setII e f i).Finite := by
  cases i with
  |zero =>
    rw [setII_zero]
    aesop
  |succ i =>
    have h1 := φinv_finite e f i
    apply Set.Finite.subset h1
    apply setII_sub_φinv

lemma setIII_finite : (setIII e f).Finite := by
  have setIII_sub_rootsOfUnity
  : setIII e f ⊆ {ξ : ℂˣ | ξ^(e:ℕ) = 1}
  := by
    intro ξ
    intro h
    simp [setIII] at h
    exact h.2.1
  have rootsOfUnity_finite : {ξ : ℂˣ | ξ^(e:ℕ) = 1}.Finite := by
    have h1 := rootsOfUnity.fintype ℂ e
    have : (rootsOfUnity e ℂ) = {ξ : ℂˣ | ξ^(e:ℕ) = 1} := by
      apply Set.eq_of_subset_of_subset
      { intro x
        intro h3
        have h4 := mem_rootsOfUnity e x
        have h5 := h4.mp h3
        exact h5
      }
      { intro x
        intro h3
        simp [rootsOfUnity] at h3
        exact h3
      }
    set f : (rootsOfUnity e ℂ) → {ξ : ℂˣ | ξ^(e:ℕ) = 1} :=
      fun x => x
    set g : {ξ : ℂˣ | ξ^(e:ℕ) = 1} → (rootsOfUnity e ℂ) :=
      fun x => x with def_g
    -- have f_inj : Function.Injective f := by
    --   intro x y h3
    --   rw [def_f] at h3
    --   simp at h3
    --   exact h3
    have left_inv : Function.LeftInverse g f := by
      intro x
      simp [def_g]
    have right_inv : Function.RightInverse g f := by
      intro x
      simp [def_g]
    have f_equiv : Equiv (rootsOfUnity e ℂ) {ξ : ℂˣ | ξ^(e:ℕ) = 1} := by
      constructor
      { exact left_inv }
      { exact right_inv }
    have h3 := Fintype.ofEquiv (rootsOfUnity e ℂ) f_equiv
    have h4 := @Finite.of_fintype (@Set.Elem ℂˣ {ξ | ξ ^ e.1 = 1}) h3
    exact h4
  apply Set.Finite.subset rootsOfUnity_finite
  assumption

noncomputable def finsetI : Finset ℕ :=
  (setI_finite e f i).toFinset

noncomputable def finsetII : Finset ℕ :=
  (setII_finite e f i).toFinset

noncomputable def cardI : ℕ := (finsetI e f i).card

noncomputable def cardII : ℕ := (finsetII e f i).card

noncomputable def cardIII : ℕ := (setIII_finite e f).toFinset.card

noncomputable def h : ℕ := (cardI e f i + (cardII e f i) * (cardIII e f))

end main_def
