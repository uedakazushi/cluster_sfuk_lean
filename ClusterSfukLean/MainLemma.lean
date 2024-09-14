import Mathlib
import ClusterSfukLean.MainDef
import ClusterSfukLean.Lipschitz
set_option linter.unusedVariables false

def ex (e f i: ℕ) : Set ℕ :=
  { n : ℕ | φ e f n = i ∧ (n % e = e - 1 ∨ n % f = f - 1) }

theorem I_eq_φinv_diff_ex (e f i : ℕ) :
  setI e f i = φinv e f i \ ex e f i := by
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
      cases h4.2 with
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
    apply And.intro
    { contrapose h2
      push_neg
      push_neg at h2
      apply And.intro
      { exact h1 }
      { apply Or.inl h2 }
    }
    {
      apply And.intro
      {
        contrapose h2
        push_neg at h2
        push_neg
        apply And.intro
        { exact h1 }
        { apply Or.inr h2 }
      }
      {
        contrapose h2
        rw [φ] at h1
        dsimp [nat_div] at h1
        contradiction
      }
    }
  }

theorem φinv_i_empty_i_mod_e_add_f
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

theorem i_mod_e_add_f_φinv_i_empty
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (i_mod : i % (e+f) = e+f-1)
  :
  φinv (e*l) (f*l) i = ∅
  := by
  set k := (i+1) / (e+f) with def_k
  set n := e*f*l*k with def_n
  have succ_i_mod : (i+1) % (e+f) = 0 := by
    rw [Nat.add_mod]
    rw [i_mod]
    simp
    have ne : e + f ≠ 0 := by
      linarith
    have succ_pred : e+f-1+1=e+f := Nat.succ_pred ne
    rw [succ_pred]
    rw [Nat.mod_self]
  have dvd : (e+f) ∣ (i+1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact succ_i_mod
  have dmc := Nat.div_mul_cancel dvd
  rw [← def_k] at dmc
  rw [mul_comm] at dmc
  have h1 : φ (e*l) (f*l) n = i + 1 := by
    rw [φ]
    rw [def_n]
    dsimp [nat_div]
    have h2 : e * f * l * k = f * k * (e * l) := by
      ring
    rw [h2]
    rw [Nat.mul_div_cancel]
    clear h2
    have h2 : f * k * (e * l) = e * k * (f * l) := by
      ring
    rw [h2]
    rw [Nat.mul_div_cancel]
    clear h2
    have h2 : f * k + e * k = (e + f) * k := by
      ring
    rw [h2]
    exact dmc
    apply mul_pos
    linarith
    exact l_pos
    apply mul_pos
    linarith
    exact l_pos
  have n_pos : n ≠ 0 := by
    rw [def_n]
    repeat apply mul_ne_zero
    repeat linarith
    by_contra k_zero
    rw [k_zero] at dmc
    simp at dmc
  set n' := n - 1 with def_n'
  have succ_n' : n - 1 + 1 = n := by
    exact Nat.succ_pred n_pos
  rw [← def_n'] at succ_n'
  have i_pos : i ≠ 0 := by
    by_contra i_zero
    rw [i_zero] at i_mod
    simp at i_mod
    have ef_ge_4 : e + f ≥ 4 := by
      linarith
    have h2 (a : Nat) (eq : 0 = a - 1) : a = 0 ∨ a = 1 := by
      cases a with
      | zero =>
        exact Or.inl rfl
      | succ a =>
        cases a with
        | zero =>
          exact Or.inr rfl
        | succ a =>
          have pred_succ : a+1+1-1 = a+1 := Nat.pred_succ (a+1)
          rw [pred_succ] at eq
          contradiction
    have h3 := h2 (e+f) i_mod
    cases h3 with
    | inl h3 =>
      rw [h3] at i_mod
      linarith
    | inr h3 =>
      rw [h3] at i_mod
      linarith
  set i' := i - 1 with def_i'
  have succ_i' : i - 1 + 1 = i := by
    exact Nat.succ_pred i_pos
  rw [← def_i'] at succ_i'
  have h2 : φ (e*l) (f*l) n' = i' := by
    rw [φ]
    dsimp [nat_div]
    rw [def_n']
    rw [def_n]
    have el_pos : e*l > 0 := by
      apply mul_pos
      linarith
      exact l_pos
    have h2 := mul_pred_div (f*k) (e*l) el_pos
    have fl_pos : f*l > 0 := by
      apply mul_pos
      linarith
      exact l_pos
    have h3 : e * f * l * k = f * k * (e * l) := by
      ring
    rw [h3]
    rw [h2]
    have h4 := mul_pred_div (e*k) (f*l) fl_pos
    have h5 : f * k * (e * l) = e * k * (f * l) := by
      ring
    rw [h5]
    rw [h4]
    rw [← succ_i'] at dmc
    have k_pos : k > 0 := by
      by_contra k_zero'
      have k_zero : k = 0 := by
        linarith
      rw [k_zero] at dmc
      simp at dmc
    have fk_pos : f*k > 0 := by
      apply mul_pos
      linarith
      exact k_pos
    have ek_pos : e*k > 0 := by
      apply mul_pos
      linarith
      exact k_pos
    have ek_pos' : 1 ≤ e*k := by
      linarith
    have h6 := Nat.add_sub_assoc ek_pos (f * k - 1)
    rw [← h6]
    simp
    have h7 : (f * k - 1) + e * k = e * k + (f * k - 1) := Nat.add_comm (f * k - 1) (e * k)
    rw [h7]
    have fk_pos : f*k > 0 := by
      apply mul_pos
      linarith
      exact k_pos
    have fk_pos' : 1 ≤ f*k := by
      linarith
    have h8 := Nat.add_sub_assoc fk_pos' (e*k)
    rw [← h8]
    have h9 : e * k + f * k = (e+f) * k := by
      ring
    rw [h9]
    rw [dmc]
    simp
  by_contra h3
  rw [φinv] at h3
  push_neg at h3
  match h3 with
  | ⟨ m, h4 ⟩ =>
  have le_or_ge : m ≤ n' ∨ n ≤ m := by
    have h5 := le_or_lt m n'
    match h5 with
    | Or.inl h5 =>
      left
      exact h5
    | Or.inr h5 =>
      right
      rw [← succ_n']
      linarith
  cases le_or_ge with
  | inl le =>
    have h6 := φ_monotone (e*l) (f*l) le
    rw [h2] at h6
    rw [h4] at h6
    rw [← succ_i'] at h6
    linarith
  | inr ge =>
    have h6 := φ_monotone (e*l) (f*l) ge
    rw [h4] at h6
    rw [h1] at h6
    linarith

namespace main_lemma

variable
  (e f i l: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (l_pos : l > 0)
  (non_empty : i % (e+f) ≠ e+f-1)

theorem non_emp_l : φinv (e*l) (f*l) i ≠ ∅ := by
  by_contra h
  have h1 := φinv_i_empty_i_mod_e_add_f e f i l e_ge_2 f_ge_2 coprime l_pos h
  contradiction

theorem non_emp_1 : φinv e f i ≠ ∅ := by
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

theorem min_l_eq_l_mul_min_1 : (n_min_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty).1 = l * (n_min_1 e f i e_ge_2 f_ge_2 coprime non_empty).1 := by
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

theorem case_a (h : (i+1) % (e+f) ≠ e+f-1) : (n_min_l e f (i+1) l e_ge_2 f_ge_2 coprime l_pos h).1 - 1 ∈ (φinv (e*l) (f*l) i) ∧ (n_min_l e f (i+1) l e_ge_2 f_ge_2 coprime l_pos h).1 ∉ (φinv (e*l) (f*l) i):= by
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

theorem mod_ne_succ (n d : ℕ) (d_ge_2 : d ≥ 2) : n % d ≠ (n+1) % d := by
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

theorem mod_eq_succ_ne (n d : ℕ) (d_ge_2 : d ≥ 2) (h1 : n % d = d - 1) : (n+1) % d ≠ d - 1 := by
  have h2 := mod_ne_succ n d d_ge_2
  rw [h1] at h2
  simp at h2
  intro h3
  exact h2 (Eq.symm h3)

theorem add_ge {e f : ℕ} (e_ge_2 : e ≥ 2) (f_ge_2 : f ≥ 2) : e + f ≥ 2 := by
  linarith

theorem le_of_le_succ_and_ne (a b : ℕ) (ineq1 : a ≤ b + 1) (ineq2 : a ≠ b + 1) : a ≤ b := by
  rw [Nat.le_iff_lt_or_eq] at ineq1
  cases ineq1 with
  | inl ineq1 =>
    linarith
  | inr ineq1 =>
    contradiction

theorem zero_of_le_pred_self {a : ℕ} (ineq : a ≤ a - 1) : a = 0 := by
  cases a with
  | zero =>
    rfl
  | succ a =>
    have pred_suc : a + 1 - 1 = a := by
      exact Nat.pred_succ a
    rw [pred_suc] at ineq
    linarith

theorem case_b
  (empty' : (i+1) % (e+f) = e+f-1)
  :
  (n_min_l e f (i+2) l e_ge_2 f_ge_2 coprime l_pos (mod_eq_succ_ne (i+1) (e+f) (add_ge e_ge_2 f_ge_2) empty')).1 - 1 ∈ (φinv (e*l) (f*l) i)
  ∧
  (n_min_l e f (i+2) l e_ge_2 f_ge_2 coprime l_pos (mod_eq_succ_ne (i+1) (e+f) (add_ge e_ge_2 f_ge_2) empty')).1 ∉ (φinv (e*l) (f*l) i)
  := by
  have non_empty'' : (i+2) % (e+f) ≠ e+f-1 :=
  mod_eq_succ_ne _ _ (add_ge e_ge_2 f_ge_2) empty'
  set nmin := n_min_l e f i l e_ge_2 f_ge_2 coprime l_pos non_empty with def_nmin
  have φinv_empty' := i_mod_e_add_f_φinv_i_empty e f (i+1) l e_ge_2 f_ge_2 coprime l_pos empty'
  set nmin'' := n_min_l e f (i+2) l e_ge_2 f_ge_2 coprime l_pos non_empty'' with def_nmin''
  have mem : nmin''.1-1 ∈ φinv (e*l) (f*l) i := by
    have φ_pred_nmin''_eq_i : φ (e*l) (f*l) (nmin''.1-1) = i := by
      have φ_pred_nmin''_le_succ_succ_i : φ (e*l) (f*l) (nmin''.1-1) ≤ i + 2 := by
        have h1 := φ_monotone (e*l) (f*l) (Nat.pred_le nmin''.1)
        rw [nmin''.2.1] at h1
        exact h1
      have φ_pred_nmin''_ne_succ_succ_i : φ (e*l) (f*l) (nmin''.1-1) ≠ i + 2 := by
        have minimality := nmin''.2.2
        by_contra h2
        have h3 : nmin''.1-1 ∈ φinv (e*l) (f*l) (i+2) := by
          exact h2
        have h4 := minimality (nmin''.1-1) h3
        have h5 := zero_of_le_pred_self h4
        rw [h5] at h2
        simp at h2
        rw [φ_zero] at h2
        linarith
      have φ_pred_nmin''_ne_succ_i : φ (e*l) (f*l) (nmin''.1-1) ≠ i + 1 := by
        have h1 := mod_ne_succ (i+1) (e+f) (add_ge e_ge_2 f_ge_2)
        rw [empty'] at h1
        simp at h1
        intro h2
        have φinv_non_empty' : φinv (e*l) (f*l) (i+1) ≠ ∅ := by
          apply Set.nonempty_iff_ne_empty.mp
          rw [Set.nonempty_def]
          exists nmin''.1-1
        exact φinv_non_empty' φinv_empty'
      have i_le_φ_pred_nmin'' : i ≤ φ (e*l) (f*l) (nmin''.1-1) := by
        have h1 := nmin''.2.2
        have h2 := nmin''.2.1
        have h3 := (@mtl (e*l) (f*l)).2 (nmin''.1-1)
        have nmin''_ne_zero : nmin''.1 ≠ 0 := by
          by_contra nmin''_eq_zero
          have h5 : φ (e*l) (f*l) (nmin''.1) = i+2 := by
            exact h2
          rw [nmin''_eq_zero] at h5
          rw [φ_zero] at h5
          linarith
        have h4 : nmin''.1 - 1 + 1 = nmin''.1 := Nat.succ_pred nmin''_ne_zero
        rw [h4] at h3
        have h5 : φ (e*l) (f*l) (nmin''.1) = i + 2 := by
          exact h2
        rw [h5] at h3
        repeat apply Nat.le_of_succ_le_succ at h3
        exact h3
      have h1 := le_of_le_succ_and_ne (φ (e*l) (f*l) (nmin''.1-1)) (i+1) φ_pred_nmin''_le_succ_succ_i φ_pred_nmin''_ne_succ_succ_i
      have h2 := le_of_le_succ_and_ne (φ (e*l) (f*l) (nmin''.1-1)) i h1 φ_pred_nmin''_ne_succ_i
      linarith
    exact φ_pred_nmin''_eq_i
  apply And.intro
  {
    exact mem
  }
  {
    have h1 := nmin''.2.1
    dsimp [φinv]
    dsimp [φinv] at h1
    by_contra h
    rw [h1] at h
    linarith
  }

end main_lemma
