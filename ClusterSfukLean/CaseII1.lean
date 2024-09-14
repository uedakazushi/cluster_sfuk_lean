import ClusterSfukLean.caseI
import Mathlib.Tactic.ClearExcept
set_option maxHeartbeats 500000

theorem setII_empty_if_not_dvd
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  (not_dvd : ¬ (e.1 + f.1) ∣ (i + 1) )
  : setII (e*l) (f*l) i = ∅
  := by
  by_contra h
  apply not_dvd
  push_neg at h
  match h with
  | ⟨n, h1, h2, h3⟩ =>
  have h1' : n % (e.1 * l.1) = e.1 * l.1 - 1 := by
    exact h1
  simp at h2
  have h2' : n % (f.1 * l.1) = f.1 * l.1 - 1 := by
    exact h2
  simp at h3
  have : n / (e.1 * l.1) + n / (f.1 * l.1) + 1 = i := by
    exact h3
  have h5 : (n+1) % (e.1*l.1) = 0 := by
    have h7 := Nat.add_mod n 1 (e.1*l.1)
    have h10 : e.1 * l.1 - 1 + 1 = e.1 * l.1 := by
      have h11 : 1 ≤ e.1 * l.1 := by
        have h12 := Nat.mul_le_mul e_ge_2 l.2
        simp at h12
        have h13 : 2 ≤ e.1*l.1 := by exact h12
        linarith
      have h12 := Nat.sub_add_cancel h11
      exact h12
    rw [h1'] at h7
    simp at h7
    rw [h10] at h7
    simp at h7
    exact h7
  have h6 : (n+1) % (f.1*l.1) = 0 := by
    have h7 := Nat.add_mod n 1 (f.1*l.1)
    have h10 : f.1 * l.1 - 1 + 1 = f.1 * l.1 := by
      have h11 : 1 ≤ f.1 * l.1 := by
        have h12 := Nat.mul_le_mul f_ge_2 l.2
        simp at h12
        have h13 : 2 ≤ f.1*l.1 := by exact h12
        linarith
      have h12 := Nat.sub_add_cancel h11
      exact h12
    rw [h2'] at h7
    simp at h7
    rw [h10] at h7
    simp at h7
    exact h7
  have h5' : (e.1*l.1) ∣ (n+1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact h5
  have h6' : (f.1*l.1) ∣ (n+1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact h6
  have h7 := Nat.lcm_dvd h5' h6'
  have h8 : Nat.gcd (e.1*l.1) (f.1*l.1) = l.1 := by
    have h9 := Nat.gcd_mul_right e.1 l.1 f.1
    have h10 : Nat.gcd e.1 f.1 = 1 := by
      exact coprime
    rw [h10] at h9
    simp at h9
    exact h9
  have h9 : Nat.lcm (e.1*l.1) (f.1*l.1) = (e.1*f.1*l.1) := by
    simp [Nat.lcm]
    rw [h8]
    have h10 : e.1 * l.1 * (f.1 * l.1) = (e.1*l.1 * f.1) * l.1 := by
      ring
    rw [h10]
    have h11 := Nat.mul_div_cancel (e.1*l.1*f.1) l.2
    rw [h11]
    ring
  rw [h9] at h7
  set k := (n+1)/(e.1*f.1*l.1) with def_k
  have h10 := Nat.div_mul_cancel h7
  rw [← def_k] at h10
  have h11 : i = φ (e.1*l.1) (f.1*l.1) n + 1 := by
    simp [φ]
    exact h3.symm
  have k_ne_zero : k ≠ 0 := by
    by_contra k_zero
    rw [k_zero] at h10
    simp at h10
  have : n ≠ 0 := by
    by_contra n_zero
    rw [n_zero] at h10
    simp at h10
    have := h10.2.1.1
    have h12 : e.1 ≥ 2 := by exact e_ge_2
    linarith
  have h12 : (φ (e.1*l.1) (f.1*l.1) n + 1) + 1 = (e.1+f.1)*k := by
    rw [φ]
    dsimp [nat_div]
    have h13 := dvd_mod_ne (e.1*l.1) (n+1) (by linarith) h5'
    have h14 := dvd_mod_ne (f.1*l.1) (n+1) (by linarith) h6'
    simp at h13
    simp at h14
    have h15 : n / (e.1 * l.1) + n / (f.1 * l.1) + 1 + 1 = (n / (e.1 * l.1) + 1) + (n / (f.1 * l.1) + 1) := by
      ring
    rw [h15, h13, h14]
    have h16 : (n+1)/(e.1*l.1) = k*f.1 := by
      rw [← h10]
      have h17 : k * (e.1 * f.1 * l.1) = k*f.1*(e.1*l.1) := by ring
      rw [h17]
      rw [Nat.mul_div_left]
      simp
      have l_pos : 0 < l.1 := by
        exact l.2
      have e_pos : 0 < e.1 := by
        exact e.2
      have el_pos := And.intro e_pos l_pos
      exact el_pos
    have h17 : (n+1)/(f.1*l.1) = k*e.1 := by
      rw [← h10]
      have h18 : k * (e.1 * f.1 * l.1) = k*e.1*(f.1*l.1) := by ring
      rw [h18]
      rw [Nat.mul_div_left]
      simp
      have l_pos : 0 < l.1 := by
        exact l.2
      have f_pos : 0 < f.1 := by
        exact f.2
      have fl_pos := And.intro f_pos l_pos
      exact fl_pos
    rw [h16, h17]
    ring
  rw [← h11] at h12
  dsimp [Nat.instDvd]
  exists k

theorem setII_singleton
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  -- (coprime : Nat.Coprime e f)
  (dvd : (e.1 + f.1) ∣ (i + 1))
  : setII (e*l) (f*l) i = Set.singleton (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1:ℕ)
  := by
  set k := (i+1)/(e.1+f.1) with def_k
  set n := e.1*f.1*l.1*k-1 with def_n
  have def_k' := Nat.div_mul_cancel dvd
  rw [← def_k] at def_k'
  have k_ne_zero : k ≠ 0 := by
    by_contra k_zero
    rw [k_zero] at def_k'
    simp at def_k'
  have k_pos : 0 < k := by
    exact Nat.pos_iff_ne_zero.mpr k_ne_zero
    -- match k with
    -- | 0 => contradiction
    -- | Nat.succ k' => linarith
  have e_ge_2' : e.1 ≥ 2 := by
    exact e_ge_2
  have f_ge_2' : f.1 ≥ 2 := by
    exact f_ge_2
  have ef_ge := Nat.mul_le_mul e_ge_2' f_ge_2'
  simp at ef_ge
  have efl_ge := Nat.mul_le_mul ef_ge l.2
  simp at efl_ge
  have eflk_ge := Nat.mul_le_mul efl_ge k_pos
  simp at eflk_ge
  have eflk_ne_zero : e.1*f.1*l.1*k ≠ 0 := by
    linarith
  have eflk : e.1*f.1*l.1*k = n + 1 := by
    rw [def_n]
    have h5 := Nat.sub_one_add_one eflk_ne_zero
    exact h5.symm
  rw [eflk] at eflk_ge
  have : n ≠ 0 := by
    linarith
  have def_n' : n + 1 = e.1*f.1*l.1*k := by
    have h6 := Nat.sub_one_add_one eflk_ne_zero
    rw [← def_n] at h6
    exact h6
  have dvd1 : e.1*l.1 ∣ (n+1) := by
    rw [def_n]
    rw [def_n']
    exists f.1*k
    ring
  have h1 := dvd_mod_ne (e.1*l.1) (n+1) (by linarith) dvd1
  simp at h1
  rw [def_n'] at h1
  have h1_1 : e.1 * f.1 * l.1 * k / (e.1 * l.1) = f.1*k := by
    have el_pos : 0 < e.1*l.1 := by
      nlinarith
    have h3 := Nat.mul_div_cancel (f.1*k) el_pos
    rw [← h3]
    ring_nf
  rw [h1_1] at h1
  clear h1_1
  have dvd2 : f.1*l.1 ∣ (n+1) := by
    rw [def_n]
    rw [def_n']
    exists e.1*k
    ring
  have h2 := dvd_mod_ne (f.1*l.1) (n+1) (by linarith) dvd2
  simp at h2
  rw [def_n'] at h2
  have h2_1 : e.1 * f.1 * l.1 * k / (f.1 * l.1) = e.1*k := by
    have fl_pos : 0 < f.1*l.1 := by
      nlinarith
    have h3 := Nat.mul_div_cancel (e.1*k) fl_pos
    rw [← h3]
    ring_nf
  rw [h2_1] at h2
  clear h2_1
  have h3 : φ (e*l) (f*l) n + 1 + 1 = i + 1 := by
    rw [φ]
    dsimp [nat_div]
    have h4 : n / (e * l) + n / (f * l) + 1 + 1 = (n / (e.1 * l.1) + 1) + (n / (f.1 * l.1) + 1) := by
      have h5 : n / (e.1 * l.1) + n / (f.1 * l.1) + 1 + 1 = (n / (e.1 * l.1) + 1) + (n / (f.1 * l.1) + 1) := by
        ring
      exact h5
    rw [h4]
    rw [h1]
    rw [h2]
    rw [← def_k']
    ring
  simp at h3
  have n_in_setII : n ∈ setII (e*l) (f*l) i := by
    simp [setII]
    apply And.intro
    { have n_mod_el : n % (e.1 * l.1) = e.1 * l.1 - 1 := by
        have h4 := mul_pred_mod (f.1*k) (e.1*l.1) (by nlinarith) (by nlinarith)
        have h5 : f.1*k*(e.1*l.1)-1 = n := by
          rw [def_n]
          have h6 : f.1*k*(e.1*l.1) = e.1 * f.1 * l.1 * k := by
            ring
          rw [h6]
        rw [h5] at h4
        exact h4
      exact n_mod_el
    }
    { apply And.intro
      {
        have n_mod_fl : n % (f.1 * l.1) = f.1 * l.1 - 1 := by
          have ek_pos : 0 < e.1*k := by
            apply Nat.mul_pos
            exact e.2
            exact k_pos
          have fl_pos : 0 < f.1*l.1 := by
            apply Nat.mul_pos
            exact f.2
            exact l.2
          have h4 := mul_pred_mod (e.1*k) (f.1*l.1) ek_pos fl_pos
          have h5 : e.1*k*(f.1*l.1)-1 = n := by
            rw [def_n]
            have h6 : e.1*k*(f.1*l.1) = e.1 * f.1 * l.1 * k := by
              ring
            rw [h6]
          rw [h5] at h4
          exact h4
        exact n_mod_fl
      }
      {
        exact h3
      }
    }
  apply Set.ext
  intro x
  apply Iff.intro
  {
    intro h
    have h' := h
    rw [Set.singleton]
    simp
    rw [setII] at h
    simp at h
    by_contra x_ne_n
    have rhs_eq_n : e.1*f.1*l.1*(i+1)/(e.1+f.1)-1 = n := by
      rw [← def_k']
      have h1 : e.1 * f.1 * l.1 * (k * (e.1 + f.1)) = (e.1 * f.1 * l.1 * k) * (e.1 + f.1) := by
        ring
      rw [h1]
      rw [eflk]
      rw [Nat.mul_div_cancel]
      rw [Nat.add_sub_cancel]
      linarith
    rw [rhs_eq_n] at x_ne_n
    have x_lt_or_gt_n : x < n ∨ n < x := by
      have h1 := Nat.lt_trichotomy x n
      cases h1 with
      | inl h1 => exact Or.inl h1
      | inr h1 =>
        cases h1 with
        | inl h1 => contradiction
        | inr h1 => exact Or.inr h1
    cases x_lt_or_gt_n with
    | inl x_lt_n =>
      have x_eq_n_mod_el : x % (e.1*l.1) = n % (e.1*l.1) := by
        have h1 := h.1
        have el_pos : 0 < e.1*l.1 := by
          apply Nat.mul_pos
          linarith
          exact l.2
        have h2 := mod_of_dvd_succ n (e.1*l.1) el_pos dvd1
        have h1' : x % (e.1*l.1) = e.1*l.1 - 1 := by
          exact h1
        rw [h1']
        rw [h2]
      have div_lt := div_lt_of_lt_and_mod_eq x n (e.1*l.1) x_eq_n_mod_el x_lt_n
      have x_le_n : x ≤ n := by
        exact Nat.le_of_lt x_lt_n
      have div_le := nat_div_monotone (f.1*l.1) x_le_n
      have φx_lt_φn : φ (e.1*l.1) (f.1*l.1) x < φ (e.1*l.1) (f.1*l.1) n := by
        rw [φ]
        dsimp [nat_div]
        dsimp [nat_div] at div_le
        linarith
      have φx : φ (e.1*l.1) (f.1*l.1) x + 1 = i := by
        rw [setII] at h'
        exact h'.2.2
      have φx_lt_φn' : φ (e.1*l.1) (f.1*l.1) x + 1 < φ (e.1*l.1) (f.1*l.1) n + 1 := by
        linarith
      rw [φx] at φx_lt_φn'
      have h3' : φ (e.1*l.1) (f.1*l.1) n + 1 = i := by
        exact h3
      rw [h3'] at φx_lt_φn'
      clear * - φx_lt_φn'
      linarith
    | inr n_lt_x =>
      have x_eq_n_mod_el : x % (e.1*l.1) = n % (e.1*l.1) := by
        have h1 := h.1
        have el_pos : 0 < e.1*l.1 := by
          apply Nat.mul_pos
          linarith
          exact l.2
        have h2 := mod_of_dvd_succ n (e.1*l.1) el_pos dvd1
        have h1' : x % (e.1*l.1) = e.1*l.1 - 1 := by
          exact h1
        rw [h1']
        rw [h2]
      have div_lt := div_lt_of_lt_and_mod_eq n x (e.1*l.1) x_eq_n_mod_el.symm n_lt_x
      have n_le_x : n ≤ x := by
        exact Nat.le_of_lt n_lt_x
      have div_le := nat_div_monotone (f.1*l.1) n_le_x
      have φn_lt_φx : φ (e.1*l.1) (f.1*l.1) n < φ (e.1*l.1) (f.1*l.1) x := by
        rw [φ]
        dsimp [nat_div]
        dsimp [nat_div] at div_le
        linarith
      have φx : φ (e.1*l.1) (f.1*l.1) x + 1 = i := by
        rw [setII] at h'
        exact h'.2.2
      have φn_lt_φx' : φ (e.1*l.1) (f.1*l.1) n + 1 < φ (e.1*l.1) (f.1*l.1) x + 1 := by
        linarith
      rw [φx] at φn_lt_φx'
      have h3' : φ (e.1*l.1) (f.1*l.1) n + 1 = i := by
        exact h3
      rw [h3'] at φn_lt_φx'
      clear * - φn_lt_φx'
      linarith
  }
  { intro h
    simp at h
    rw [Set.singleton] at h
    simp at h
    simp [setII] at n_in_setII
    have n_eq_x : n = x := by
      rw [← def_k'] at h
      have h1 : e.1 * f.1 * l.1 * (k * (e.1 + f.1)) = (e.1 * f.1 * l.1 * k) * (e.1 + f.1) := by
        ring
      rw [h1] at h
      rw [eflk] at h
      rw [Nat.mul_div_cancel] at h
      rw [Nat.add_sub_cancel] at h
      rw [h]
      linarith
    rw [n_eq_x] at n_in_setII
    exact n_in_setII
  }
