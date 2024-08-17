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

lemma φ_n_add_one_le_φ_n_add_two (e f n : ℕ) : φ e f (n+1) ≤ (φ e f n) + 2 := by
  dsimp [φ]
  have h3 := nat_succ_div_le n e
  have h4 := nat_succ_div_le n f
  linarith

lemma φinv_i_empty_implies_φinv_i_add_one_nonempty
  (e f i : ℕ)
  (h : φinv e f i = ∅)
  :
  φinv e f (i+1) ≠ ∅ := by
    sorry

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

lemma φ_n_minus_one_ne_φ_n_e
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

lemma φ_n_minus_one_ne_φ_n_f
  (e f n : ℕ)
  (n_ne_zero : n ≠ 0)
  (f_dvd_n : f ∣ n)
  :
  φ e f (n-1) + 1 ≤ φ e f n
  := by
  simp [φ]
  set n' := n - 1 with h1
  have h2 := dvd_mod_ne f n n_ne_zero f_dvd_n
  have h3 : n' ≤ n' + 1 := by
    linarith
  have h4 := @Nat.div_le_div_right n' (n'+1) e h3
  rw [h1]
  rw [h1] at h4
  have h5 : n - 1 + 1 = n := Nat.succ_pred n_ne_zero
  rw [h5] at h4
  linarith

lemma φ_n_minus_one_ne_φ_n
  (e f n : ℕ)
  (n_ne_zero : n ≠ 0)
  (ef_dvd_n : e ∣ n ∨ f ∣ n)
  :
  φ e f (n-1) + 1 ≤ φ e f n
  := by
  cases ef_dvd_n with
  | inl e_dvd_n =>
    exact φ_n_minus_one_ne_φ_n_e e f n n_ne_zero e_dvd_n
  | inr f_dvd_n =>
    exact φ_n_minus_one_ne_φ_n_f e f n n_ne_zero f_dvd_n

lemma min_φinv_dvd
  (e f i n: ℕ)
  (mem : n ∈ φinv e f i)
  (min : ∀ m ∈ φinv e f i, n ≤ m)
  :
  e ∣ n ∨ f ∣ n := by
  by_cases n_ne_zero : n ≠ 0

  case pos =>
    simp [φinv, φ] at mem
    simp [φinv, φ] at min
    by_contra h
    push_neg at h
    have h1 : (n - 1) / e = n / e := by
      apply Eq.symm
      apply not_dvd_mod_eq
      exact n_ne_zero
      exact h.1
    have h2 : (n - 1) / f = n / f := by
      apply Eq.symm
      apply not_dvd_mod_eq
      exact n_ne_zero
      exact h.2
    have h3 : (n - 1) / e + (n - 1) / f = i := by
      rw [h1]
      rw [h2]
      exact mem
    have h4 := min (n-1) h3
    cases n with
    | zero =>
      contradiction
    | succ n' =>
      have h5 : n' + 1 - 1 = n' := by
        aesop
      rw [h5] at h4
      linarith

  case neg =>
    aesop

lemma dvd_min_φinv
  (e f i n : ℕ)
  (dvd : e ∣ n ∨ f ∣ n)
  (mem : φ e f n = i)
  :
  ∀ m < n, φ e f m < i := by
  intro m
  intro h
  have n_ne_zero : n ≠ 0 := by
    linarith
  have h1 := φ_n_minus_one_ne_φ_n e f n n_ne_zero dvd
  rw [mem] at h1
  have h2 : φ e f (n-1) < i := by
    linarith
  have succ_pred_n : n - 1 + 1 = n := Nat.succ_pred n_ne_zero
  set n' := n - 1 with h3
  have h4 : m ≤ n' := by
    linarith
  have h5 : φ e f m ≤ φ e f n' := by
    apply φ_monotone
    linarith
  linarith

lemma nat_mul_dvd {a b c : ℕ} : a * b ∣ c → b ∣ c := by
  intro h
  dsimp [Nat.instDvd] at h
  match h with
  | ⟨ d, h1 ⟩ =>
    exists a * d
    have h2 : a * b * d = b * (a * d) := by ring
    rw [←h2]
    exact h1

lemma gcd_div_min_φinv
  (e f i l n : ℕ)
  (mem : n ∈ φinv (e*l) (f*l) i)
  (min : ∀ m ∈ φinv (e*l) (f*l) i, n ≤ m)
  :
  l ∣ n := by
  have h1 := min_φinv_dvd (e*l) (f*l) i n mem min
  cases h1 with
  | inl h2 => apply nat_mul_dvd h2
  | inr h3 => apply nat_mul_dvd h3

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
  have h2 : s ≠ ∅ := by
    sorry
  have nonempty_s : s.Nonempty := by
    by_contra h3
    let h4 := Set.not_nonempty_iff_eq_empty.mp h3
    exact h2 h4
  clear h2
  set n := WellFounded.min Nat.lt.isWellOrder.3.wf s nonempty_s with h3
  have h4 : ∀ m ∈ s, n ≤ m := by
    intro m
    intro mem
    have h4 := WellFounded.not_lt_min Nat.lt.isWellOrder.3.wf s nonempty_s mem
    linarith
  have h5 := WellFounded.min_mem Nat.lt.isWellOrder.3.wf s nonempty_s
  rw [←h3] at h5
  -- have h6 : e*l ∣ n ∨ f*l ∣ n := by
  --   exact min_φinv_dvd (e*l) (f*l) (i+1) n h5 h4
  have h6 : e*l ∣ n := by
    sorry
  have h7 : f*l ∣ n := by
    sorry
  have h8 := Nat.lcm_dvd h6 h7
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
    rw [s_eq_φinv] at h5
    exact h5
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
