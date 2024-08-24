import Mathlib
import ClusterSfukLean.QuotRem
import ClusterSfukLean.Lipschitz
import ClusterSfukLean.NatDvd

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
  set n' := n - 1 -- with h3
  -- have h4 : m ≤ n' := by
  --   linarith
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
