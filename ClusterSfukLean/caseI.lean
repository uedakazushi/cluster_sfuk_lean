import ClusterSfukLean.MainLemma

noncomputable def finsetφinv (e f : ℕ+) (i : ℕ) : Finset ℕ := (φinv_finite e f i).toFinset

-- noncomputable def cardφinv (e f : ℕ+) (i : ℕ) : ℕ := (finsetφinv e f i).card

theorem φinv_sub_ex (e f i : ℕ) : ex e f i ⊆ φinv e f i := by
  intro m
  intro h
  simp [ex] at h
  simp [φinv]
  exact h.1

def ex_finite (e f : ℕ+) (i : ℕ) : Set.Finite (ex e f i) := by
  have h1 := φinv_finite e f i
  apply Set.Finite.subset h1
  apply φinv_sub_ex

noncomputable def finsetex (e f : ℕ+) (i : ℕ) : Finset ℕ := (ex_finite e f i).toFinset

theorem finsetφinv_sub_finsetex (e f : ℕ+) (i : ℕ) : finsetex e f i ⊆ finsetφinv e f i := by
  intro m
  intro h
  simp [finsetex] at h
  simp [finsetφinv]
  simp [ex] at h
  simp [φinv]
  exact h.1

theorem finsetI_eq_finsetφinv_sub_finsetex (e f : ℕ+) (i : ℕ) :
  finsetI e f i = finsetφinv e f i \ finsetex e f i := by
  have := φinv e f i
  apply Finset.ext
  intro x
  apply Iff.intro
  {
    intro h
    simp [finsetI] at h
    simp [finsetφinv, finsetex]
    simp [setI] at h
    simp [φinv]
    simp [ex]
    simp [φ]
    simp [nat_div]
    apply And.intro
    {
      exact h.2.2
    }
    {
      intro
      apply And.intro
      {
        exact h.1
      }
      {
        exact h.2.1
      }
    }
  }
  {
    intro h
    simp [finsetI]
    simp [setI]
    simp [finsetφinv] at h
    simp [finsetex] at h
    simp [φinv] at h
    simp [ex] at h
    simp [φ] at h
    simp [nat_div] at h
    have h1 := h.1
    have h2 := h.2
    have h3 := h2 h1
    clear h2
    apply And.intro
    {
      exact h3.1
    }
    {
      apply And.intro
      {
        exact h3.2
      }
      {
        exact h1
      }
    }
  }

theorem cardI_eq_cardφinv_sub_cardex (e f : ℕ+) (i : ℕ) :
  cardI e f i = (finsetφinv e f i).card - (finsetex e f i).card := by
  have h1 := finsetI_eq_finsetφinv_sub_finsetex e f i
  have h2 := finsetφinv_sub_finsetex e f i
  have h3 := Finset.card_sdiff h2
  rw [← h1] at h3
  rw [cardI]
  exact h3

def φ_inv_nonempty
  (e f i l : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : e.Coprime f)
  (l_pos : l > 0)
  (non_empty : ¬e + f ∣ i + 1)
  : φinv (e * l) (f * l) i ≠ ∅
  := by
  have h1 := Nat.dvd_iff_mod_eq_zero (e + f) (i + 1)
  have h2 : i % (↑e + ↑f) ≠ ↑e + ↑f - 1 := by
    by_contra h2
    have h3 := Nat.add_mod i 1 (e + f)
    rw [h2] at h3
    have ef : 1 ≤ e + f := by linarith
    have h4 := Nat.sub_add_cancel ef
    simp at h3
    rw [h4] at h3
    simp at h3
    have h5 := h1.2 h3
    exact non_empty h5
  exact main_lemma.non_emp_l e f i l e_ge_2 f_ge_2 coprime l_pos h2

def finsetφinv_nonempty
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  : (finsetφinv (e * l) (f * l) i).Nonempty := by
  have h1 := φ_inv_nonempty e f i l e_ge_2 f_ge_2 coprime l.2 non_empty
  have h2 : finsetφinv (e * l) (f * l) i ≠ ∅ := by
    rw [finsetφinv]
    simp
    exact h1
  exact Finset.nonempty_iff_ne_empty.2 h2

noncomputable def min_φinv
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  : ℕ :=
  (finsetφinv (e * l) (f * l) i).min' (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)

noncomputable def min_φinv_mem
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  :
  min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty ∈ finsetφinv (e * l) (f * l) i
  :=
  Finset.min'_mem (finsetφinv (e * l) (f * l) i) (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)

noncomputable def max_φinv
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  : ℕ :=
  (finsetφinv (e * l) (f * l) i).max' (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)

theorem finsetφinv_is_interval
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  :
  finsetφinv (e * l) (f * l) i = nat_interval (min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) (max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty)
  := by
  apply Finset.ext
  intro a
  set min := min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty with def_min
  set max := max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty with def_max
  have min_mem := Finset.min'_mem (finsetφinv (e * l) (f * l) i) (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)
  rw [min_φinv] at def_min
  rw [← def_min] at min_mem
  have max_mem := Finset.max'_mem (finsetφinv (e * l) (f * l) i) (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)
  rw [max_φinv] at def_max
  rw [← def_max] at max_mem
  apply Iff.intro
  {
  intro h1
  have min_le := Finset.min'_le (finsetφinv (e * l) (f * l) i) a h1
  rw [← def_min] at min_le
  have le_max := Finset.le_max' (finsetφinv (e * l) (f * l) i) a h1
  rw [← def_max] at le_max
  simp [finsetφinv] at h1
  have h2 := preimage_φ_isInterval (e * l) (f * l) i
  rw [IsInterval] at h2
  simp [nat_interval]
  apply And.intro
  {
    linarith
  }
  {
    exact min_le
  }
  }
  {
  intro h1
  simp [nat_interval] at h1
  have h2 := preimage_φ_isInterval (e * l) (f * l) i
  rw [IsInterval] at h2
  have min_mem' : min ∈ φ ↑(e * l) ↑(f * l) ⁻¹' {n | n = i} := by
    rw [finsetφinv] at min_mem
    simp at min_mem
    exact min_mem
  have max_mem' : max ∈ φ ↑(e * l) ↑(f * l) ⁻¹' {n | n = i} := by
    rw [finsetφinv] at max_mem
    simp at max_mem
    exact max_mem
  have h2' := h2 min a max min_mem' max_mem' (by linarith) (by linarith)
  simp at h2'
  rw [finsetφinv]
  simp
  exact h2'
  }

theorem cardφinv_eq_max_sub_min
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  : (finsetφinv (e * l) (f * l) i).card = (max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) + 1 - (min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) := by
  have h1 := finsetφinv_is_interval e f l i e_ge_2 f_ge_2 coprime non_empty
  rw [h1]
  rw [nat_interval_card]

-- theorem max_φinv_eq1
--   (e f l : ℕ+)
--   (i : ℕ)
--   (e_ge_2 : e ≥ 2)
--   (f_ge_2 : f ≥ 2)
--   (coprime : (e.1).Coprime f.1)
--   (non_empty : ¬e.1 + f.1 ∣ i + 1)
--   (succ_non_empty : ¬e.1 + f.1 ∣ i + 2)
--   :
--   (max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) = (min_φinv e f l (i+1) e_ge_2 f_ge_2 coprime succ_non_empty) - 1 := by
--   sorry

theorem dvd_succ_not_dvd
  (k : ℕ)
  (n : ℕ+)
  (n_ge_2 : n ≥ 2)
  (dvd : n.1 ∣ k)
  : ¬n.1 ∣ k + 1 := by
  intro h
  have h1 : k ≤ k+1 := by linarith
  have h2 := Nat.dvd_sub h1 h dvd
  simp at h2
  have : n.1 ≥ 2 := by exact n_ge_2
  linarith

lemma ge_2_ge_2_add {a b : ℕ+} (a_ge_2 : a ≥ 2) (b_ge_2 : b ≥ 2) : a + b ≥ 2 := by
  have : a.1 ≥ 2 := by exact a_ge_2
  have : b.1 ≥ 2 := by exact b_ge_2
  have : a.1 + b.1 ≥ 2 := by linarith
  exact this

-- theorem max_φinv_eq2
--   (e f l : ℕ+)
--   (i : ℕ)
--   (e_ge_2 : e ≥ 2)
--   (f_ge_2 : f ≥ 2)
--   (coprime : (e.1).Coprime f.1)
--   (non_empty : ¬e.1 + f.1 ∣ i + 1)
--   (succ_empty : e.1 + f.1 ∣ i + 2)
--   :
--   (max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) = (min_φinv e f l (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_empty)) - 2 := by
--   sorry

lemma non_emp_conv
  {e f : ℕ+}
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  :
  i % (e.1 + f.1) ≠ e.1 + f.1 - 1
  := by
  by_contra h
  contrapose non_empty
  push_neg
  clear non_empty
  have h1 := Nat.add_mod i 1 (e.1 + f.1)
  rw [h] at h1
  simp at h1
  have ef_pos : e.1 + f.1 > 0 := (e+f).2
  have ef_pos' : 1 ≤ e.1 + f.1 := by linarith
  have h2 := Nat.sub_add_cancel ef_pos'
  rw [h2] at h1
  simp at h1
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h1

theorem min_φinv_mul_l
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  :
  min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty = l.1 * min_φinv e f 1 i e_ge_2 f_ge_2 coprime non_empty := by
  set min1 := min_φinv e f 1 i e_ge_2 f_ge_2 coprime non_empty with def_min1
  set minl := min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty with def_minl
  have min1_mem : min1 ∈ φinv e f i := by
    have mem := min_φinv_mem e f 1 i e_ge_2 f_ge_2 coprime non_empty
    rw [← def_min1] at mem
    rw [finsetφinv] at mem
    simp at mem
    exact mem
  have minl_mem : minl ∈ φinv (e * l) (f * l) i := by
    have mem := min_φinv_mem e f l i e_ge_2 f_ge_2 coprime non_empty
    rw [← def_minl] at mem
    rw [finsetφinv] at mem
    simp at mem
    exact mem
  have minimality1 : ∀ m ∈ φinv e f i, min1 ≤ m := by
    intro m
    intro h
    have h1 : m ∈ finsetφinv e f i := by
      rw [finsetφinv]
      simp
      exact h
    have min1_le := Finset.min'_le (finsetφinv e f i) m h1
    rw [min_φinv] at def_min1
    simp at def_min1
    simp
    rw [← def_min1] at min1_le
    exact min1_le
  have dvd_1 := min_φinv_dvd e f i min1 min1_mem minimality1
  have dvd_l : (e.1*l.1) ∣ (l.1 * min1) ∨ (f.1*l.1) ∣ (l.1 * min1) := by
    cases dvd_1 with
    | inl dvd_1 =>
      left
      rw [Nat.mul_comm]
      exact Nat.mul_dvd_mul_left l dvd_1
    | inr dvd_1 =>
      right
      rw [Nat.mul_comm]
      exact Nat.mul_dvd_mul_left l dvd_1
  have mem_l : φ (e * l) (f * l) (l * min1) = i := by
    have h1 : l * min1 = min1 * l := by
      ring
    rw [h1]
    have h2 := φ_mul e f min1 l
    have h3 : φ e f min1 = i := by
      have h3 := min_φinv_mem e f 1 i e_ge_2 f_ge_2 coprime non_empty
      rw [← def_min1] at h3
      simp at h3
      rw [finsetφinv] at h3
      simp at h3
      exact h3
    rw [h3] at h2
    exact h2
  have min_l' := dvd_min_φinv (e*l) (f*l) i (l * min1) dvd_l mem_l
  have inv_mem : ∀ (m:Nat), m ∈ φinv (e*l) (f*l) i ↔ φ (e*l) (f*l) m = i := by
    intro m
    apply Iff.intro
    { intro h
      rw [φinv] at h
      exact h }
    { intro h
      rw [φinv]
      exact h }
  have min_l_rw : ∀ (m:Nat), φ (e*l) (f*l) m = i → minl ≤ m := by
    intro m
    intro h
    rw [def_minl]
    have minimalityl : ∀ m ∈ φinv (e * l) (f * l) i, minl ≤ m := by
      intro m
      intro h
      have h1 : m ∈ finsetφinv (e * l) (f * l) i := by
        rw [finsetφinv]
        simp
        exact h
      have minl_le := Finset.min'_le (finsetφinv (e * l) (f * l) i) m h1
      rw [min_φinv] at def_minl
      simp
      rw [← def_minl] at minl_le
      exact minl_le
    simp
    rw [← def_minl]
    have h1 : m ∈ φinv (e.1 * l.1) (f.1 * l.1) i := by
      exact h
    exact minimalityl m h1
  have ineq1 := min_l_rw (l * min1) mem_l
  have ineq2 : minl ≥ l.1 * min1 := by
    by_contra h
    rw [not_le] at h
    have h1 := min_l' minl h
    have h2 : φ (e * l) (f * l) minl = i := by
      exact minl_mem
    have h3 : φ (e * l) (f * l) minl ≠ i := by
      exact Nat.ne_of_lt h1
    contradiction
  simp at ineq1
  simp at ineq2
  exact le_antisymm ineq1 ineq2

theorem div_succ_of_mod_eq_sub_one
  (n : ℕ)
  (d : ℕ)
  (d_ge_2 : d ≥ 2)
  (h : n % d = d - 1)
  :
  (n + 1) / d = n / d + 1 := by
  rw [Nat.add_div (by linarith)]
  rw [h]
  have h1 : 1 % d = 1 := by
    rw [Nat.mod_eq]
    split
    case isTrue h1 =>
      linarith
    case isFalse h1 =>
      rfl
  have h2 : 1 / d = 0 := by
    rw [Nat.div_eq]
    split
    case isTrue h2 =>
      linarith
    case isFalse h2 =>
      rfl
  split
  case isTrue h3 =>
    rw [h1] at h3
    rw [h2]
  case isFalse h3 =>
    rw [h1] at h3
    have h4 : 1 ≤ d := by linarith
    rw [Nat.sub_add_cancel h4] at h3
    linarith

theorem succ_ex
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  :
  n ∈ (finsetex (e * l) (f * l) i)
  →
  φ (e * l) (f * l) (n+1) > i
  := by
  intro h
  simp [finsetex] at h
  simp [ex] at h
  simp [φ]
  simp [nat_div]
  simp [φ] at h
  simp [nat_div] at h
  have h1 := h.1
  have h2 := h.2
  have l_pos := l.2
  have : l.1 ≥ 1 := by
    linarith
  have el_ge_2 : e.1 * l.1 ≥ 2 := by
    have h3 := Nat.mul_le_mul l.2 e_ge_2
    simp at h3
    simp
    rw [mul_comm] at h3
    exact h3
  have fl_ge_2 : f.1 * l.1 ≥ 2 := by
    have h3 := Nat.mul_le_mul l.2 f_ge_2
    simp at h3
    simp
    rw [mul_comm] at h3
    exact h3
  clear h
  cases h2
  case inl h2 =>
    have h3 := div_succ_of_mod_eq_sub_one n (e.1 * l.1) (by nlinarith) h2
    simp
    simp at h3
    have el_eq_el : ↑e * ↑l = e.1 * l.1 := by
      rfl
    rw [el_eq_el]
    rw [h3]
    have h5 := @Nat.div_le_div_right n (n+1) (f.1*l.1) (by linarith)
    have h6 : n / (↑e * ↑l) + 1 + (n + 1) / (↑f * ↑l) ≥ n / (e.1 * l.1) + n / (f.1 * l.1) + 1 := by
      have h7 : n / (e.1 * l.1) + n / (f.1 * l.1) + 1 = n / (e.1 * l.1) + 1 + n / (f.1 * l.1) := by
        linarith
      rw [h7]
      simp
      have h6 := Nat.add_le_add_left h5 (n / (e.1 * l.1) + 1)
      exact h6
    simp at h6
    have h7 : n / (↑e * ↑l) + n / (↑f * ↑l) + 1 = n / (e.1 * l.1) + n / (f.1 * l.1) + 1 := by
      rfl
    simp at h7
    rw [← h7] at h6
    have h8 : n / (↑e * ↑l) + n / (↑f * ↑l) + 1 = i + 1 := by
      rw [h1]
    rw [h8] at h6
    have h9 := Nat.lt_of_succ_le h6
    exact h9
  case inr h2 =>
    have h3 := div_succ_of_mod_eq_sub_one n (f.1 * l.1) (by nlinarith) h2
    simp
    simp at h3
    have fl_eq_fl : ↑f * ↑l = f.1 * l.1 := by
      rfl
    rw [fl_eq_fl]
    rw [h3]
    have h5 := @Nat.div_le_div_right n (n+1) (e.1*l.1) (by linarith)
    have h6 : (n + 1) / (↑e * ↑l) + n / (↑f * ↑l) + 1 ≥ n / (e.1 * l.1) + (n / (f.1 * l.1) + 1) := by
      have h7 : n / (e.1 * l.1) + (n / (f.1 * l.1) + 1) = n / (e.1 * l.1) + 1 + n / (f.1 * l.1) := by
        linarith
      rw [h7]
      simp
      have h8 : n / (e.1 * l.1) + 1 + n / (f.1 * l.1) = n / (e.1 * l.1) + n / (f.1 * l.1) + 1 := by
        linarith
      rw [h8]
      simp
      have h6 := Nat.add_le_add_right h5 (n / (f.1 * l.1))
      exact h6
    simp at h6
    have h7 : n / (↑e * ↑l) + (n / (↑f * ↑l) + 1) = n / (e.1 * l.1) + (n / (f.1 * l.1) + 1) := by
      rfl
    simp at h7
    rw [← h7] at h6
    have h8 : n / (↑e * ↑l) + (n / (↑f * ↑l) + 1) = i + 1 := by
      have h9 : n / (↑e * ↑l) + (n / (↑f * ↑l) + 1) = n / (↑e * ↑l) + n / (↑f * ↑l) + 1 := by
        rfl
      rw [h9]
      rw [h1]
    rw [h8] at h6
    have h9 := Nat.lt_of_succ_le h6
    exact h9

theorem suc_div_eq_div
  (n : ℕ)
  (d : ℕ)
  (d_ge_2 : d ≥ 2)
  (h : ¬ n % d = d - 1)
  :
  (n + 1) / d = n / d
  := by
  by_contra h2
  have h3 := nat_succ_div_le n d
  have h4 : n ≤ n + 1 := by linarith
  have h5 := nat_div_monotone d h4
  simp [nat_div] at h5
  have h6 : ¬n / d = (n + 1) / d := by
    aesop
  have h7 := Nat.lt_of_le_of_ne h5 h6
  have h8 := Nat.succ_le_of_lt h7
  have := Nat.le_antisymm h3 h8
  have h10 : nat_div d n < nat_div d (n + 1) := by
    rw [nat_div,nat_div]
    exact h7
  have h11 := nat_div_lt_dvd d (n+1) (by linarith) h10
  have h12 := Nat.mod_eq_zero_of_dvd h11
  have h13 := Nat.add_mod n 1 d
  rw [h12] at h13
  have h14 := @Nat.mod_lt n d (by linarith)
  have h15 := Nat.le_pred_of_lt h14
  simp at h15
  have h16 := Nat.lt_of_le_of_ne h15 h
  have h17 := Nat.le_pred_of_lt h16
  simp at h17
  have h18 : 1 % d = 1 := by
    rw [Nat.mod_eq]
    split
    case isTrue h18 =>
      linarith
    case isFalse h18 =>
      rfl
  rw [h18] at h13
  have h19 := Nat.add_le_add_right h17 1
  have h20 := Nat.sub_le_sub_right d_ge_2 1
  have h21 := Nat.sub_add_cancel h20
  simp at h21
  rw [h21] at h19
  have h22 : (n % d + 1) % d = (n % d + 1) := by
    rw [Nat.mod_eq]
    split
    case isTrue h22 =>
      have := h22.2
      have h24 := Nat.add_le_add_right h19 1
      have h25 : 1 ≤ d := by linarith
      have h26 := Nat.sub_add_cancel h25
      rw [h26] at h24
      linarith
    case isFalse h22 =>
      rfl
  rw [h22] at h13
  contradiction

theorem cardex
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  :
  (finsetex (e * l) (f * l) i).card = 1 := by
  set m := max_φinv e f l i e_ge_2 f_ge_2 coprime non_empty with def_m
  have m_mem' := Finset.max'_mem (finsetφinv (e * l) (f * l) i) (finsetφinv_nonempty e f l i e_ge_2 f_ge_2 coprime non_empty)
  have m_mem : m ∈ finsetφinv (e * l) (f * l) i := by
    rw [max_φinv] at def_m
    rw [← def_m] at m_mem'
    exact m_mem'
  have m_max : ∀ x ∈ finsetφinv (e*l) (f*l) i, x ≤ m := by
    intro x
    intro x_mem
    have le_max := Finset.le_max' (finsetφinv (e*l) (f*l) i) x x_mem
    rw [max_φinv] at def_m
    rw [← def_m] at le_max
    exact le_max
  have m_in_ex : m ∈ finsetex (e * l) (f * l) i := by
    by_contra nin
    rw [finsetex] at nin
    simp at nin
    rw [ex] at nin
    simp at nin
    have m_mem'' : φ (e * l) (f * l) m = i := by
      rw [finsetφinv] at m_mem
      simp at m_mem
      exact m_mem
    have nin1 := (nin m_mem'').1
    have nin2 := (nin m_mem'').2
    sorry
  have m_in_finsetex : m ∈ finsetex e f i := by
    rw [finsetex]
    simp
    simp [finsetφinv] at m_mem
    sorry
  sorry

theorem cardI1
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  (succ_non_empty : ¬e.1 + f.1 ∣ i + 2)
  :
  cardI (e * l) (f * l) i = (min_φinv e f l (i+1) e_ge_2 f_ge_2 coprime succ_non_empty) - 1 - (min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) := by
  sorry

theorem cardI2
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  (succ_empty : e.1 + f.1 ∣ i + 2)
  :
  cardI (e * l) (f * l) i = (min_φinv e f l (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_empty)) - 1 - (min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty) := by
  sorry

lemma one_le_of_succ_le
  {a b : ℕ}
  (h : a.succ ≤ b)
  :
  1 ≤ b - a
  := by
  have h1 := Nat.sub_le_sub_right h a
  simp at h1
  exact h1

theorem caseI_main
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : (e.1).Coprime f.1)
  (non_empty : ¬e.1 + f.1 ∣ i + 1)
  : cardI (e * l) (f * l) i = l.1 * cardI e f i + l.1 - 1
  := by
  by_cases succ_emp : e.1 + f.1 ∣ i + 2
  case pos =>
    -- have h1 := max_φinv_eq2 e f l i e_ge_2 f_ge_2 coprime non_empty succ_emp
    rw [cardI2]
    have h2 := min_φinv_mul_l e f l i e_ge_2 f_ge_2 coprime non_empty
    rw [h2]
    have h3 := min_φinv_mul_l e f l (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_emp)
    rw [h3]
    -- have h4 := max_φinv_eq2 e f 1 i e_ge_2 f_ge_2 coprime non_empty succ_emp
    -- simp at h4
    have h5 := cardI2 e f 1 i e_ge_2 f_ge_2 coprime non_empty succ_emp
    simp at h5
    rw [h5]
    set min1 := min_φinv e f 1 i e_ge_2 f_ge_2 coprime non_empty with def_min1
    set min1' := min_φinv e f 1 (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_emp) with def_min1'
    set minl := min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty
    set minl' := min_φinv e f l (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_emp)
    rw [Nat.mul_sub]
    rw [Nat.mul_sub]
    simp
    rw [Nat.sub_right_comm]
    have h6 : l.1 * min1' - l.1 - l.1 * min1 = l.1 * min1' - l.1 * min1 - l.1 := by
      rw [Nat.sub_right_comm]
    rw [h6]
    have h7 : min1 < min1' := by
      by_contra h7
      push_neg at h7
      have min1_mem : min1 ∈ φinv e f i := by
        have h8 := min_φinv_mem e f 1 i e_ge_2 f_ge_2 coprime non_empty
        rw [← def_min1] at h8
        rw [finsetφinv] at h8
        simp at h8
        exact h8
      have min1'_mem : min1' ∈ φinv e f (i+2) := by
        have h8 := min_φinv_mem e f 1 (i+2) e_ge_2 f_ge_2 coprime (dvd_succ_not_dvd (i+2) (e+f) (ge_2_ge_2_add e_ge_2 f_ge_2) succ_emp)
        rw [← def_min1'] at h8
        rw [finsetφinv] at h8
        simp at h8
        exact h8
      have monot := φ_monotone e f h7
      rw [min1_mem] at monot
      rw [min1'_mem] at monot
      linarith
    have h8 : l.1 ≤ l.1 * min1' - l.1 * min1 := by
      have := Nat.succ_le_of_lt h7
      have h10 : 1 ≤ min1' - min1 :=
        one_le_of_succ_le h7
      have h11 := Nat.mul_le_mul_left l.1 h10
      rw [Nat.mul_sub] at h11
      simp at h11
      exact h11
    rw [Nat.sub_add_cancel h8]
    exact succ_emp
  case neg =>
    -- have := max_φinv_eq1 e f l i e_ge_2 f_ge_2 coprime non_empty
    rw [cardI1]
    have h2 := min_φinv_mul_l e f l i e_ge_2 f_ge_2 coprime non_empty
    rw [h2]
    have h3 := min_φinv_mul_l e f l (i+1) e_ge_2 f_ge_2 coprime succ_emp
    rw [h3]
    -- have h4 := max_φinv_eq1 e f 1 i e_ge_2 f_ge_2 coprime non_empty
    -- simp at h4
    have h5 := cardI1 e f 1 i e_ge_2 f_ge_2 coprime non_empty
    simp at h5
    rw [h5]
    set min1 := min_φinv e f 1 i e_ge_2 f_ge_2 coprime non_empty with def_min1
    set min1' := min_φinv e f 1 (i+1) e_ge_2 f_ge_2 coprime succ_emp with def_min1'
    set minl := min_φinv e f l i e_ge_2 f_ge_2 coprime non_empty
    set minl' := min_φinv e f l (i+1) e_ge_2 f_ge_2 coprime succ_emp
    rw [Nat.mul_sub]
    rw [Nat.mul_sub]
    simp
    rw [Nat.sub_right_comm]
    have h6 : l.1 * min1' - l.1 - l.1 * min1 = l.1 * min1' - l.1 * min1 - l.1 := by
      rw [Nat.sub_right_comm]
    rw [h6]
    have h7 : min1 < min1' := by
      by_contra h7
      push_neg at h7
      have min1_mem : min1 ∈ φinv e f i := by
        have h8 := min_φinv_mem e f 1 i e_ge_2 f_ge_2 coprime non_empty
        rw [← def_min1] at h8
        rw [finsetφinv] at h8
        simp at h8
        exact h8
      have min1'_mem : min1' ∈ φinv e f (i+1) := by
        have h8 := min_φinv_mem e f 1 (i+1) e_ge_2 f_ge_2 coprime succ_emp
        rw [← def_min1'] at h8
        rw [finsetφinv] at h8
        simp at h8
        exact h8
      have monot := φ_monotone e f h7
      rw [min1_mem] at monot
      rw [min1'_mem] at monot
      linarith
    have h8 : l.1 ≤ l.1 * min1' - l.1 * min1 := by
      have := Nat.succ_le_of_lt h7
      have h10 : 1 ≤ min1' - min1 :=
        one_le_of_succ_le h7
      have h11 := Nat.mul_le_mul_left l.1 h10
      rw [Nat.mul_sub] at h11
      simp at h11
      exact h11
    rw [Nat.sub_add_cancel h8]
