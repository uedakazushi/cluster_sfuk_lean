import Mathlib
import ClusterSfukLean.MainDef
import ClusterSfukLean.Lipschitz
-- set_option linter.unusedVariables false

def ex (e f: ℕ) : Set ℕ :=
  { n : ℕ | n % e = e - 1 ∨ n % f = f - 1 }

lemma I_eq_φinv_diff_ex (e f i : ℕ) :
  setI e f i = φinv e f i \ ex e f := by
  apply Set.eq_of_subset_of_subset
  { intro x
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    apply And.intro
    { apply h3 }
    { rw [ex]
      intro h4
      cases h4 with
      | inl h4 =>
        exact h1 h4
      | inr h4 =>
        exact h2 h4 }
  }
  { rw [φinv,setI,ex]
    intro x
    intro h
    have h1 := h.1
    have h2 := h.2
    aesop
  }

lemma φinv_i_empty_i_mod_e_add_f
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (h : φinv (e*l) (f*l) i = ∅)
  :
  i % (e+f) = e+f-1 := by
  have el_pos : e*l > 0 := by
    apply mul_pos
    linarith
    exact l_pos
  -- have h1 := skip (φ (e*l) (f*l)) mtl (iuf el_pos) φ_zero i h
  set s := φinv (e*l) (f*l) (i+1) with def_s
  have s_ne_empty : s ≠ ∅ :=
    skip (φ (e*l) (f*l)) mtl (iuf el_pos) φ_zero i h
  have s_nonempty := Set.nonempty_iff_ne_empty.mpr s_ne_empty
  set n := WellFounded.min Nat.lt.isWellOrder.3.wf s s_nonempty with def_n
  have minimality_n : ∀ m ∈ s, n ≤ m := by
    intro m
    intro mem
    have wfnlm := WellFounded.not_lt_min Nat.lt.isWellOrder.3.wf s s_nonempty mem
    linarith
  have n_in_s := WellFounded.min_mem Nat.lt.isWellOrder.3.wf s s_nonempty
  rw [←def_n] at n_in_s
  clear def_n
  have h6 :=
    min_φinv_dvd (e*l) (f*l) (i+1) n n_in_s minimality_n
  have i_pos : i > 0 := by
    by_contra h1
    have h2 : i = 0 := by
      linarith
    rw [h2] at h
    have h3 : φ (e*l) (f*l) 0 = 0 := by
      rw [φ_zero]
    rw [φinv] at h
    contrapose h
    push_neg
    exact ⟨ 0, h3 ⟩
  have n_pos : n > 0 := by
    by_contra h1
    have h2 : n = 0 := by
      linarith
    rw [h2] at n_in_s
    have h3 : φ (e*l) (f*l) 0 = i + 1 := by
      rw [def_s] at n_in_s
      exact n_in_s
    have h4 : φ (e*l) (f*l) 0 = 0 := by
      rw [φ_zero]
    rw [h4] at h3
    linarith
  have n_ne_zero : n ≠ 0 := by
    linarith
  set n' := n - 1 with def_n'
  have succ_n' : n - 1 + 1 = n := by
    exact Nat.succ_pred n_ne_zero
  rw [← def_n'] at succ_n'
  have φ_n'_ne_i : φ (e*l) (f*l) n' ≠ i := by
    by_contra h3
    have h4 : n' ∈ φinv (e*l) (f*l) i := by
      exact h3
    rw [h] at h4
    contradiction
  have i_ne_zero : i ≠ 0 := by
    linarith
  set i' := i - 1 with def_i'
  have succ_i' : i - 1 + 1 = i := by
    exact Nat.succ_pred i_ne_zero
  rw [← def_i'] at succ_i'
  have φ_n' : φ (e*l) (f*l) n' = i' := by
    have h1 := (@mtl (e*l) (f*l)).2 n'
    have h2 : φ (e * l) (f * l) (n' + 1) = i+1 := by
      rw [def_s] at n_in_s
      rw [succ_n']
      exact n_in_s
    rw [h2] at h1
    rw [← succ_i'] at h1
    have h3 := Nat.le_of_succ_le_succ h1
    have i'_le_φ_n' := Nat.le_of_succ_le_succ h3
    clear h1 h2 h3
    rw [← succ_i'] at φ_n'_ne_i
    have h1 := (@mtl (e*l) (f*l)).1 (Nat.le_succ n')
    have n_in_s2 : φ (e*l) (f*l) n = i + 1 := by
      exact n_in_s
    have h2 : n'.succ = n := by
      exact succ_n'
    rw [h2] at h1
    rw [n_in_s2] at h1
    rw [← succ_i'] at h1
    have φ_n'_le_succ_succ_i' : φ (e*l) (f*l) n' ≤ i' + 2 := by
      exact h1
    clear h1
    have φ_n'_ne_succ_succ_i' : φ (e * l) (f * l) n' ≠ i' + 2 := by
      by_contra h1
      have succ_succ_i' : i' + 2 = i + 1 := by
        rw [← succ_i']
      rw [succ_succ_i'] at h1
      have h2 : n' ∈ s := by
        rw [def_s]
        exact h1
      have h3 := minimality_n n' h2
      linarith
    have le_of_le_succ_and_ne_succ : ∀ a b : ℕ, a ≤ b + 1 → a ≠ b + 1 → a ≤ b := by
      intro a
      intro b
      intro h1
      intro h2
      by_contra h3
      have h4 : a = b + 1 := by
        linarith
      contradiction
    have h3 (a : Nat) (ineq1 : a ≠ i' + 1) (ineq2 : i' ≤ a) (ineq3 : a ≤ i' + 2) (ineq4 : a ≠ i' + 2) : a = i' := by
      have h7 := le_of_le_succ_and_ne_succ a (i'+1) ineq3 ineq4
      have h5 := le_of_le_succ_and_ne_succ a i' h7 ineq1
      linarith
    exact h3 (φ (e*l) (f*l) n') φ_n'_ne_i i'_le_φ_n' φ_n'_le_succ_succ_i' φ_n'_ne_succ_succ_i'
  clear φ_n'_ne_i
  have φ_succ_n' : φ (e*l) (f*l) (n' + 1) = i + 1 := by
    rw [def_s] at n_in_s
    rw [succ_n']
    exact n_in_s
  rw [← succ_i'] at φ_succ_n'
  have succ_succ_i' : i' + 1 + 1 = i' + 2 := by
    ring
  rw [succ_succ_i'] at φ_succ_n'
  clear succ_succ_i'
  have el_fl_dvd_n := φ_skip2 (e*l) (f*l) n' i' φ_n' φ_succ_n'
  rw [succ_n'] at el_fl_dvd_n
  have el_dvd_n : e*l ∣ n := el_fl_dvd_n.1
  have fl_dvd_n : f*l ∣ n := el_fl_dvd_n.2
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
    -- have h12 := Nat.mul_div_cancel (e * l * f) l_pos
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
    dsimp [nat_div]
    rw [h12, h14, h13, h15]
    ring
  have h12 : φ (e*l) (f*l) n = i+1 := by
    rw [φinv] at def_s
    rw [def_s] at n_in_s
    exact n_in_s
  rw [h11] at h12
  have h13 : k > 0 := by
    by_contra h13
    have h14 : k = 0 := by
      linarith
    rw [h14] at h12
    -- have h15 : i+1 = 0 := by
    --   linarith
    -- have h16 : i+1 ≠ 0 := by
    --   linarith
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

lemma i_mod_e_add_f_φinv_i_empty
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (i_mod : i % (e+f) = e+f-1)
  :
  φinv (e*l) (f*l) i = ∅
  := by
  sorry

section main

namespace main_lemma

variable
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (non_empty : i % (e+f) ≠ e+f-1)

lemma non_emp_l : φinv (e*l) (f*l) i ≠ ∅ := by
  by_contra h
  have h1 := φinv_i_empty_i_mod_e_add_f e f i l e_ge_2 f_ge_2 coprime l_pos h
  contradiction

lemma non_emp_1 : φinv e f i ≠ ∅ := by
  by_contra h
  have h1 := φinv_i_empty_i_mod_e_add_f e f i 1 e_ge_2 f_ge_2 coprime (by linarith)
  rw [Nat.mul_one] at h1
  rw [Nat.mul_one] at h1
  have h2 := h1 h
  contradiction

def nat_min {s : Set ℕ} := { n : ℕ | IsMinIn n s }

noncomputable def nat_min_in (s : Set ℕ) (h : s.Nonempty) : (@nat_min s) := by
  rw [nat_min]
  set m := WellFounded.min Nat.lt.isWellOrder.3.wf s h with def_m
  have isminin : IsMinIn m s := by
    rw [IsMinIn]
    apply And.intro
    {
      rw [def_m]
      exact WellFounded.min_mem Nat.lt.isWellOrder.3.wf s h
    }
    {
      intro n
      intro h1
      have h2 := WellFounded.not_lt_min Nat.lt.isWellOrder.3.wf s h h1
      rw [def_m]
      linarith
    }
  exact ⟨ m, isminin ⟩

noncomputable def n_min_l := nat_min_in (φinv (e*l) (f*l) i) (Set.nonempty_iff_ne_empty.mpr (non_emp_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty))

noncomputable def n_min_1 := nat_min_in (φinv e f i) (Set.nonempty_iff_ne_empty.mpr (non_emp_1 e f i e_ge_2 f_ge_2 coprime non_empty))

lemma min_l_eq_l_mul_min_1 : (n_min_l e f i l e_ge_2 f_ge_2 coprime l_pos non_emptry).1 = l * (n_min_1 e f i e_ge_2 f_ge_2 coprime non_empty).1 := by
  set m_1 := n_min_1 e f i e_ge_2 f_ge_2 coprime non_empty with def_m_1
  set m_l := n_min_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty with def_m_l
  have mem_1 : ↑m_1 ∈ φinv e f i := by
    rw [def_m_1]
    exact (nat_min_in (φinv e f i) (Set.nonempty_iff_ne_empty.mpr (non_emp_1 e f i e_ge_2 f_ge_2 coprime non_empty))).2.1
  have min_1 : ∀ m ∈ φinv e f i, ↑m_1 ≤ m := by
    rw [def_m_1]
    exact (nat_min_in (φinv e f i) (Set.nonempty_iff_ne_empty.mpr (non_emp_1 e f i e_ge_2 f_ge_2 coprime non_empty))).2.2
  -- have min_l : ∀ m ∈ φinv (e*l) (f*l) i, ↑m_l ≤ m := by
  --   rw [def_m_l]
  --   exact (nat_min_in (φinv (e*l) (f*l) i) (Set.nonempty_iff_ne_empty.mpr (non_emp_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty))).2.2
  have dvd_1 := min_φinv_dvd e f i m_1.1 mem_1 min_1
  have dvd_l : (e*l) ∣ (l * ↑ m_1) ∨ (f*l) ∣ (l * ↑ m_1) := by
    cases dvd_1 with
    | inl dvd_1 =>
      left
      rw [Nat.mul_comm]
      exact Nat.mul_dvd_mul_left l dvd_1
    | inr dvd_1 =>
      right
      rw [Nat.mul_comm]
      exact Nat.mul_dvd_mul_left l dvd_1
  set e' : PNat := ⟨ e, by linarith ⟩ with def_e'
  set f' : PNat := ⟨ f, by linarith ⟩ with def_f'
  set l' : PNat := ⟨ l, by linarith ⟩
  have mem_l : φ (e * l) (f * l) (l * ↑m_1) = i := by
    have h1 : l * ↑m_1 = ↑m_1 * l := by
      ring
    rw [h1]
    have h2 := φ_mul e' f' (↑m_1) l'
    have h3 : φ e f m_1 = i := by
      rw [def_m_1]
      exact (nat_min_in (φinv e f i) (Set.nonempty_iff_ne_empty.mpr (non_emp_1 e f i e_ge_2 f_ge_2 coprime non_empty))).2.1
    have h4 : φ ↑e' ↑f' ↑m_1 = i := by
      simp [def_e', def_f']
      exact h3
    rw [h4] at h2
    exact h2
  have min_l' := dvd_min_φinv (e*l) (f*l) i (l * ↑ m_1) dvd_l mem_l
  have inv_mem : ∀ (m:Nat), m ∈ φinv (e*l) (f*l) i ↔ φ (e*l) (f*l) m = i := by
    intro m
    apply Iff.intro
    { intro h
      rw [φinv] at h
      exact h }
    { intro h
      rw [φinv]
      exact h }
  have min_l_rw : ∀ (m:Nat), φ (e*l) (f*l) m = i → ↑m_l ≤ m := by
    intro m
    intro h
    rw [def_m_l]
    exact (nat_min_in (φinv (e*l) (f*l) i) (Set.nonempty_iff_ne_empty.mpr (non_emp_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty))).2.2 m h
  have ineq1 := min_l_rw (l * ↑ m_1) mem_l
  have ineq2 : ↑ m_l ≥ l * ↑ m_1 := by
    by_contra h
    rw [not_le] at h
    have h1 := min_l' ↑ m_l h
    have h2 := m_l.2.1
    have h3 : φ (e * l) (f * l) ↑m_l = i := by
      aesop
    linarith
  linarith

lemma case_a (h : (i+1) % (e+f) ≠ e+f-1) : (n_min_l e f (i+1) l e_ge_2 f_ge_2 coprime l_pos h).1 - 1 ∈ (φinv (e*l) (f*l) i) ∧ (n_min_l e f (i+1) l e_ge_2 f_ge_2 coprime l_pos h).1 ∉ (φinv (e*l) (f*l) i):= by
  set nmin' := n_min_l e f (i+1) l e_ge_2 f_ge_2 coprime l_pos h with def_nmin'
  set nmin := n_min_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty with def_nmin
  have h1 : φ (e*l) (f*l) (nmin'.1-1) ≤ φ (e*l) (f*l) nmin'.1 := by
    apply φ_monotone
    apply Nat.sub_le
  have h2 : φ (e*l) (f*l) (nmin'.1-1) ≠ φ (e*l) (f*l) nmin'.1 := by
    -- have h3 := nmin'.2.1
    have h4 := nmin'.2.2
    by_contra h5
    have h6 : (↑nmin':Nat) - 1 ∈ φinv (e*l) (f*l) (i+1) := by
      have h7 : φ (e * l) (f * l) (↑nmin' - 1) = i + 1 := by
        rw [h5]
        rw [def_nmin']
        exact nmin'.2.1
      exact h7
    have h8 := h4 (nmin'.1 - 1) h6
    have h9 (a : Nat) (ineq : a ≤ a - 1) : a = 0 := by
      cases a with
      | zero =>
        linarith
      | succ a =>
        have h10 : a + 1 - 1 = a := Nat.pred_succ a
        rw [h10] at ineq
        simp
        simp at ineq
    have h10 := h9 (nmin'.1) h8
    clear h8 h9
    have h11 : nmin'.1 - 1 = 0 := by
      rw [h10]
    rw [h11] at h6
    have h12 : i + 1 = 0 := by
      rw [φinv] at h6
      simp at h6
      simp [φ] at h6
      dsimp [nat_div] at h6
      rw [Nat.zero_div] at h6
      rw [Nat.zero_div] at h6
      simp at h6
    simp at h12
  have h3 : φ (e*l) (f*l) (nmin'.1) = i + 1:=
    nmin'.2.1
  have h4 : φ (e*l) (f*l) (nmin) = i :=
    nmin.2.1
  rw [h3] at h1
  rw [h3] at h2
  have h5 : φ (e*l) (f*l) (nmin'.1-1) = i := by
    by_contra h5
    have h6 (a : Nat) (ineq1 : a ≤ i + 1) (ineq2 : a ≠ i+1) : a ≤ i := by
      by_contra ineq3
      have h7 : a = i + 1 := by
        linarith
      contradiction
    have h7 (a : Nat) (ineq1 : a ≤ i + 1) (ineq2 : a ≠ i+1) (ineq3 : a ≠ i) : a ≤ i-1 := by
      have h7 : a ≤ i := by
        exact h6 a ineq1 ineq2
      by_contra h8
      rw [not_le] at h8
      cases i with
      | zero =>
        linarith
      | succ i =>
        simp at h8
        have h9 : a = i + 1 := by
          linarith
        contradiction
    have h8 := h7 (φ (e * l) (f * l) (↑nmin' - 1)) h1 h2 h5
    have h9 : nmin.1 ≤ nmin'.1 := by
      by_contra h9
      rw [not_le] at h9
      have h10 : nmin'.1 ≤ nmin.1 := by
        linarith
      have h11 := φ_monotone (e*l) (f*l) h10
      rw [h3,h4] at h11
      linarith
    have h10 : nmin.1 ≠ nmin'.1 := by
      by_contra h10
      have h11 : φ (e * l) (f * l) nmin.1 = i + 1 := by
        rw [h10]
        exact h3
      rw [h4] at h11
      linarith
    have h11 : nmin.1 ≤ nmin'.1 - 1 := by
      have h12 (a b: Nat) (ineq1 : a ≤ b) (ineq2 : a ≠ b) : a ≤ b-1 := by
        cases b with
        | zero =>
          linarith
        | succ b =>
          simp
          by_contra h12
          rw [not_le] at h12
          have h13 : b+1 ≤ a := by
            linarith
          have h14 := LE.le.ge_iff_eq h13
          have h15 := h14.mp ineq1
          exact ineq2 (Eq.symm h15)
      exact h12 nmin.1 nmin'.1 h9 h10
    have h12 := φ_monotone (e*l) (f*l) h11
    rw [h4] at h12
    have h13 := le_trans h12 h8
    have h14 : i = 0 := by
      cases i with
      | zero =>
        rfl
      | succ i =>
        simp at h13
    simp [h14] at h1
    simp [h14] at h2
    simp [h14] at h5
    have h15 (a : Nat) (ineq1 : a ≤ 1) (ineq2 : a ≠ 1) : a = 0 := by
      cases a with
      | zero =>
        rfl
      | succ a =>
        cases a with
        | zero =>
          simp at ineq2
        | succ a =>
          linarith
    have h16 := h15 _ h1 h2
    exact h5 h16
  apply And.intro
  { exact h5 }
  { by_contra h6
    have h7 : φ (e * l) (f * l) ↑nmin' ≠ i := by
      have h8 : i + 1 ≠ i := by
        linarith
      rw [← h3] at h8
      exact h8
    exact h7 h6 }

lemma mod_ne_succ (n d : ℕ) (d_ge_2 : d ≥ 2) : n % d ≠ (n+1) % d := by
  by_contra h
  have h1: n ≤ n*d := by
    have h2 : 1 ≤ d := by
      linarith
    have h3 : n*1 ≤ n*d := by
      exact Nat.mul_le_mul_left n h2
    rw [Nat.mul_one] at h3
    exact h3
  have h2 : n*d - n + n = n*d := by
    exact Nat.sub_add_cancel h1
  have h3 : ((n*d-n) % d + n % d) % d = 0 := by
    have h4 := Nat.add_mod (n*d-n) n d
    rw [h2] at h4
    have h5 : n * d % d = 0 := by
      simp
    rw [h5] at h4
    exact Eq.symm h4
  have h4 : ((n*d-n) % d + (n+1) % d) % d = 1 := by
    have h5 := Nat.add_mod (n*d-n) (n+1) d
    have h6 : (n * d - n + (n + 1)) % d = 1 := by
      have h7 : n * d - n + (n + 1) = n * d - n + n + 1 := by
        ring
      rw [h7] at h5
      rw [h2] at h5
      have h8 : (n * d + 1) % d = 1 := by
        rw [Nat.add_mod]
        simp
        have h9 := Nat.mod_eq 1 d
        have d_pos : 0 < d := by
          linarith
        have one_lt_d : 1 < d := by
          linarith
        have h10 : ¬ (0 < d ∧ d ≤ 1) := by
          push_neg
          exact fun x => one_lt_d
        rw [if_neg h10] at h9
        rw [Nat.mod_eq]
        simp
        intro h11
        intro h12
        linarith
      rw [h8] at h5
      rw [← h] at h5
      rw [h3] at h5
      contradiction
    have h7 := Nat.add_mod (n*d-n) (n+1) d
    rw [h7] at h6
    exact h6
  have h5 : ((n*d-n) % d + (n+1) % d) % d = 0 := by
    have h6 : (n * d - n) % d + (n + 1) % d = (n * d - n) % d + n % d := by
      rw [h]
    rw [h6]
    exact h3
  rw [h4] at h5
  contradiction

lemma mod_eq_succ_ne (n d : ℕ) (d_ge_2 : d ≥ 2) (h1 : n % d = d - 1) : (n+1) % d ≠ d - 1 := by
  have h2 := mod_ne_succ n d d_ge_2
  rw [h1] at h2
  simp at h2
  intro h3
  exact h2 (Eq.symm h3)

lemma add_ge {e f : ℕ} (e_ge_2 : e ≥ 2) (f_ge_2 : f ≥ 2) : e + f ≥ 2 := by
  linarith

lemma case_b
  (non_empty : (i+1) % (e+f) = e+f-1)
  :
  (n_min_l e f (i+2) l e_ge_2 f_ge_2 coprime l_pos (mod_eq_succ_ne (i+1) (e+f) (add_ge e_ge_2 f_ge_2) h1)).1 - 2 ∈ (φinv (e*l) (f*l) i)
  ∧
  (n_min_l e f (i+2) l e_ge_2 f_ge_2 coprime l_pos (mod_eq_succ_ne (i+1) (e+f) (add_ge e_ge_2 f_ge_2) h1)).1 ∉ (φinv (e*l) (f*l) i)
  := by
  sorry

end main_lemma

end main

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
