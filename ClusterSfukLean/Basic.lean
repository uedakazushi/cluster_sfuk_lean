import Mathlib
import ClusterSfukLean.NatInterval
import ClusterSfukLean.QuotRem
set_option linter.unusedVariables false

lemma Nat_div_monotone (d : ℕ) : Monotone (fun n ↦ n / d) := by
  intro n m h
  apply Nat.div_le_div_right
  assumption

lemma Nat_add_div_monotone (e f : ℕ)
 : Monotone (fun n ↦ n / e + n / f) := by
  intro n m h
  apply Nat.add_le_add
  apply Nat.div_le_div_right
  assumption
  apply Nat.div_le_div_right
  assumption

def φ (e f : ℕ) : ℕ → ℕ :=
  λ n ↦ n / e + n / f

def φinv (e f i : ℕ) : Set ℕ :=
  { n : ℕ | φ e f n = i }

lemma φinv_is_preim_φ (e f i : ℕ) : φinv e f i = (φ e f) ⁻¹' (Set.singleton i) := by
  apply Set.eq_of_subset_of_subset
  { intro x
    intro h
    simp [φinv] at h
    simp [φ, Set.singleton]
    apply h
  }
  { intro x
    intro h
    simp [φinv]
    simp [φ, Set.singleton] at h
    apply h
  }

lemma φ_monotone (e f : ℕ) : Monotone (φ e f) := by
  intro n m h
  apply Nat_add_div_monotone
  assumption

lemma φ_mul (e f : ℕ+) (n : ℕ) (l : ℕ+) : φ (e * l) (f * l) (n * l) = φ e f n := by
  simp [φ]
  have h1 : (n * l) / (e * l) = n / e := by
    rw [Nat.mul_div_mul_right]
    exact l.2
  have h2 := Nat.mul_div_mul_right n f l.2
  aesop

lemma nat_succ_div_le (n d : ℕ) : (n+1) / d ≤ (n / d)+1 := by
  rw [Nat.succ_div]
  -- aesop
  by_cases h : d ∣ n + 1
  {
    rw [if_pos h]
  }
  { rw [if_neg h]
    linarith
  }

lemma φ_n_add_one_le_φ_n_add_two (e f : ℕ+) (n : ℕ) : φ e f (n+1) ≤ (φ e f n) + 2 := by
  dsimp [φ]
  have h3 := nat_succ_div_le n e
  have h4 := nat_succ_div_le n f
  linarith

#check Nat.decidable_dvd 3 2
#eval Nat.decidable_dvd 3 2
#eval 3 ∣ 2

open Classical
noncomputable instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match Classical.em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

lemma not_dvd_mod_eq
  (e n: ℕ)
  (n_ne_zero : n ≠ 0)
  (h : ¬ e ∣ n)
  :
  n / e = (n-1)/e := by
  set n' := n - 1 with h2
  have h4 := Nat.sub_one_add_one n_ne_zero
  rw [←h2] at h4
  have h5 := Nat.succ_div n' e
  rw [h4] at h5
  rw [if_neg h] at h5
  exact h5

lemma dvd_mod_ne
  (e n: ℕ)
  (n_ne_zero : n ≠ 0)
  (h : e ∣ n)
  :
  (n-1) / e + 1 = n/e := by
  set n' := n - 1 with h2
  have h4 := Nat.sub_one_add_one n_ne_zero
  rw [←h2] at h4
  have h5 := Nat.succ_div n' e
  rw [h4] at h5
  rw [if_pos h] at h5
  exact Eq.symm h5

lemma φ_n_minus_one_eq_φ_n
  (e f n : ℕ)
  (n_ne_zero : n ≠ 0)
  (e_not_dvd_n : ¬ e ∣ n)
  (f_not_dvd_n : ¬ f ∣ n)
  :
  φ e f (n-1) = φ e f n
  := by
  simp [φ]
  have h1 := not_dvd_mod_eq e n n_ne_zero e_not_dvd_n
  have h2 := not_dvd_mod_eq f n n_ne_zero f_not_dvd_n
  rw [h1]
  rw [h2]

lemma φ_n_minus_one_ne_φ_n
  (e f n : ℕ)
  (n_ne_zero : n ≠ 0)
  (e_dvd_n : e ∣ n)
  :
  φ e f (n-1) + 1 ≤ φ e f n
  := by
  simp [φ]
  set n' := n - 1 with h1
  have h2 := dvd_mod_ne e n n_ne_zero e_dvd_n
  have h3 : n' ≤ n' + 1 := by
    linarith
  have h4 := @Nat.div_le_div_right n' (n'+1) f h3
  rw [h1]
  rw [h1] at h4
  have h5 : n - 1 + 1 = n := Nat.succ_pred n_ne_zero
  rw [h5] at h4
  linarith

lemma pnat_ne_zero (n : ℕ+) : n.1 ≠ 0 := by
  intro h
  have h1 := n.2
  rw [h] at h1
  linarith

lemma preimage_φ_isInterval (e f : ℕ+) (i : ℕ) : IsInterval ((φ e f) ⁻¹' { n : ℕ | n = i }) := by
  apply preimage_of_monotone_isInterval
  apply φ_monotone

lemma nat_div_pnat_le (n q : ℕ) (d : ℕ+) : n / d ≤ q → n ≤ d * q + d := by
  intro h1
  have h2 : n = d * (n / d) + n % d := Eq.symm (Nat.div_add_mod n d)
  have h3 := Nat.mod_lt n d.2
  have h4 : n % d ≤ d := Nat.le_of_lt h3
  have h5 : d * (n/d) ≤ d * q := by
    apply mul_le_mul
    apply le_refl
    assumption
    apply Nat.zero_le
    apply Nat.zero_le
  linarith

lemma finset_min_eq (s : Finset ℕ) (m : ℕ) (m_in_s : m ∈ s) (minimality : ∀ x ∈ s, x ≥ m) : s.min = m := by
  have h1 := s.min_eq_inf_withTop
  simp [Finset.inf] at h1
  have h2 : s.min ≤ m := by
    apply Finset.min_le
    assumption
  have h3 : m ≤ s.min := by
    simp
    apply minimality
  exact le_antisymm h2 h3

lemma finset_min_min' (s : Finset ℕ) (h : s.Nonempty) : s.min = s.min' h := by
  apply finset_min_eq
  apply Finset.min'_mem
  intro x
  intro h1
  apply Finset.min'_le
  assumption

section main_def

variable (e f: ℕ+)
variable (i : ℕ)
variable (e_ge_2 : (e:Nat) ≥ 2)
variable (f_ge_2 : (f:Nat) ≥ 2)

def setI : Set ℕ :=
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

lemma ge_2_1_le (n : ℕ) : n ≥ 2 → 1 ≤ n := by
  intro h
  linarith

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

section main_lemma

variable (e f l: ℕ+)
variable (i : ℕ)

lemma Imin_l (non_emp : (finsetI (e * l) (f * l) i).Nonempty) :
(finsetI (e * l) (f * l) i).min = (finsetI e f i).min * l := by
  have h1 := Classical.em (finsetI e f i).Nonempty
  cases h1 with
  |inl h =>
    let b_min := (finsetI e f i).min' h
    have h2 : b_min ∈ (finsetI e f i) := by
      apply Finset.min'_mem
    have h3 : ¬ (b_min % e = 0 ∨ b_min % f = 0) → False := by
      have h4 : ∃ b ∈ (finsetI e f i), b < b_min := by
        sorry
      -- match h4 with
      -- |⟨ i, h5, h6 ⟩ =>
      let ⟨ b, h5, h6 ⟩ := h4
      exfalso
      have h7 := Finset.min'_le (finsetI e f i) b h5
      have h8 := not_le_of_lt h6
      linarith
    have h3' : b_min % e = 0 ∨ b_min % f = 0 := by
      have h10 := Classical.em (b_min % e = 0 ∨ b_min % f = 0)
      cases h10 with
      |inl h11 =>
        exact h11
      |inr h12 =>
        exfalso
        exact h3 h12
    have h13 : b_min * l ∈ (finsetI (e * l) (f * l) i) := by
      sorry
    have h14 : ∀ x ∈ (finsetI (e * l) (f * l) i), b_min * l ≤ x := by
      sorry
    have h15 := finset_min_eq (finsetI (e * l) (f * l) i) (b_min * l) h13 h14
    rw [h15]
    have h16 := finset_min_min' (finsetI e f i) h
    rw [h16]
    rfl
  |inr h =>
    have h2 : (finsetI e f i).min = 0 := by
      sorry
    have h3 : (finsetI (e * l) (f * l) i).min = 0 := by
      sorry
    rw [h2]
    rw [h3]
    sorry

section main_theorem

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
end main_theorem
