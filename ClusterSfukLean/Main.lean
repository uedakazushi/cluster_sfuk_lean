import Mathlib
import ClusterSfukLean.NatInterval
import ClusterSfukLean.QuotRem
import ClusterSfukLean.FunctionPhi
-- set_option linter.unusedVariables false

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

lemma φinv_i_empty_i_mod_e_add_f
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (h : φinv (e*l) (f*l) i = ∅)
  :
  i % (e+f) = e+f-1 := by
  set s := φinv (e*l) (f*l) (i+1) with s_eq_φinv
  have nonemp_s : s ≠ ∅ := by
    sorry
  have nonempty_s : s.Nonempty := by
    by_contra h3
    let h4 := Set.not_nonempty_iff_eq_empty.mp h3
    exact nonemp_s h4
  clear nonemp_s
  set n := WellFounded.min Nat.lt.isWellOrder.3.wf s nonempty_s with def_n
  have minimality_n : ∀ m ∈ s, n ≤ m := by
    intro m
    intro mem
    have wfnlm := WellFounded.not_lt_min Nat.lt.isWellOrder.3.wf s nonempty_s mem
    linarith
  have n_in_s := WellFounded.min_mem Nat.lt.isWellOrder.3.wf s nonempty_s
  rw [←def_n] at n_in_s
  clear def_n
  -- have h6 : e*l ∣ n ∨ f*l ∣ n := by
  --   exact min_φinv_dvd (e*l) (f*l) (i+1) n h5 h4
  -- #check min_φinv_dvd
  have el_dvd_n : e*l ∣ n := by
    sorry
  have fl_dvd_n : f*l ∣ n := by
    sorry
  have h8 := Nat.lcm_dvd el_dvd_n fl_dvd_n
  clear el_dvd_n fl_dvd_n
  have h9 := Nat.gcd_mul_right e l f
  rw [coprime] at h9
  simp at h9
  have h10 : (e*l:Nat).lcm (f*l) = e*f*l := by
    rw [Nat.lcm]
    rw [h9]
    have h11 : e * l * (f * l) = (e * l * f) * l := by
      ring
    rw [h11]
    have h12 := Nat.mul_div_cancel (e * l * f) l_pos
    have h13 : e * l * f = e * f * l := by
      ring
    aesop
  rw [h10] at h8
  match h8 with
  | ⟨ k, hk ⟩ =>
  have h11 : φ (e*l) (f*l) n = (e+f)*k := by
    rw [φ]
    rw [hk]
    have h12 : e * f * l * k = f * k * (e * l) := by ring
    have h13 : f * k * (e * l) = e * k * (f * l) := by ring
    have el_pos : 0 < e * l := by
      apply mul_pos
      linarith
      exact l_pos
    have fl_pos : 0 < f * l := by
      apply mul_pos
      linarith
      exact l_pos
    have h14 := Nat.mul_div_cancel (f * k) el_pos
    have h15 := Nat.mul_div_cancel (e * k) fl_pos
    rw [h12, h14, h13, h15]
    ring
  have h12 : φ (e*l) (f*l) n = i+1 := by
    rw [φinv] at s_eq_φinv
    rw [s_eq_φinv] at n_in_s
    exact n_in_s
  rw [h11] at h12
  have h13 : k > 0 := by
    by_contra h13
    have h14 : k = 0 := by
      linarith
    rw [h14] at h12
    have h15 : i+1 = 0 := by
      linarith
    have h16 : i+1 ≠ 0 := by
      linarith
    contradiction
  cases k with
  | zero =>
  contradiction
  | succ k' =>
  rw [Nat.mul_comm] at h12
  rw [Nat.add_mul] at h12
  have h14 : 1 ≤ e + f := by
    linarith
  have h15 := Nat.sub_add_cancel h14
  have h16 : k' * (e+f) + 1*(e+f) = k' * (e+f) + e+f := by
    ring
  rw [h16] at h12
  set e_add_f := e + f with eaddf
  have h18 : k' * e_add_f + e + f = ((e+f-1)+1)+k'*e_add_f := by
    rw [eaddf] at h15
    rw [h15]
    ring
  rw [h18] at h12
  have h19 : e + f - 1 + 1 + k' * e_add_f = e + f - 1 + k' * e_add_f + 1 := by
    ring
  rw [h19] at h12
  rw [Nat.succ_inj] at h12
  rw [eaddf]
  rw [eaddf] at h12
  have h20 := Nat.add_mul_mod_self_right (e+f-1) k' (e+f)
  rw [h12] at h20
  rw [h20]
  rw [Nat.mod_eq_of_lt]
  linarith

section main_theorem

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
end main_theorem
