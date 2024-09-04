import ClusterSfukLean.MainLemma

section CaseII

lemma setII_empty_if_not_dvd
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

lemma setII_singleton
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
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
  have n_ne_zero : n ≠ 0 := by
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
    rw [Set.singleton]
    simp
    sorry
  }
  { intro h
    simp at h
    rw [Set.singleton] at h
    simp at h
    have n_eq_x : n = x := by
      rw [← def_k'] at h
      have h1 : e.1 * f.1 * l.1 * (k * (e.1 + f.1)) = (e.1 * f.1 * l.1 * k) * (e.1 + f.1) := by
        ring
      rw [h1] at h
      rw [eflk] at h
      sorry
    rw [n_eq_x] at n_in_setII
    exact n_in_setII
  }

lemma setII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : (setII (e*l) (f*l) i) =
    (
    ite ((e.1+f.1) ∣ (e.1+f.1-1))
    (Set.singleton (e*f*l*(i+1)/(e+f) : ℕ))
    ∅
    )
  := by
  sorry

example : Nat.card (Set.singleton 1) = 1 := by
  simp

lemma cardII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : cardII (e*l) (f*l) i = ite ((e.1+f.1) ∣ (e.1+f.1-1)) 1 0
  := by
  dsimp [cardII]
  dsimp [finsetII]
  sorry

def equiv_rootsOfUnity (n : PNat) :
  {x : ℂ | x ^ n.1 = 1} ≃ {x : ℂˣ | x ^ n.1 = 1} := by
  set tofun : {x : ℂ | x ^ n.1 = 1} → {x : ℂˣ | x ^ n.1 = 1} := by
    intro x
    set val := x.1 with def_val
    set inv : ℂ := x^(n.1-1)
    have val_inv : val * inv = 1 := by
      have h1 := pow_add val 1 (n.1-1)
      have h2 : 1 + (n.1 - 1) = n.1 := by
        rw [add_comm]
        exact Nat.succ_pred n.ne_zero
      simp at h1
      simp [val,inv]
      rw [def_val] at h1
      rw [h2] at h1
      have h3 := x.2
      rw [h3] at h1
      exact h1.symm
    have inv_val : inv * val = 1 := by
      rw [mul_comm]
      exact val_inv
    set x' : ℂˣ := ⟨val, inv, val_inv, inv_val⟩ with def_x'
    have h1 : x' ^ n.1 = 1 := by
      rw [def_x']
      simp [Units.ext_iff]
      exact x.2
    exact ⟨⟨val, inv, val_inv, inv_val⟩,h1⟩
  set invfun : {x : ℂˣ | x ^ n.1 = 1} → {x : ℂ | x ^ n.1 = 1} := by
    intro x''
    set x' := x''.1 with def_x'
    have p' : x' ^ n.1 = 1 := by
      rw [def_x']
      exact x''.2
    set x := x'.1
    have p : x ^ n.1 = 1 := by
      simp [Units.ext_iff] at p'
      exact p'
    exact ⟨x, p⟩
  have left_inv : Function.LeftInverse invfun tofun := by
    simp [Function.LeftInverse]
  have right_inv : Function.RightInverse invfun tofun := by
    simp [Function.RightInverse]
    simp [Function.LeftInverse]
    intro x'
    intro h
    simp [invfun]
    simp [tofun]
  exact ⟨ tofun, invfun, left_inv, right_inv ⟩

def lexNat := Prod.Lex Nat.lt Nat.lt

lemma lexNat_wf : WellFounded (lexNat) :=
  WellFoundedRelation.wf

def mygcd_ind_step (x : ℕ × ℕ) (ih : (y : ℕ × ℕ) → (lexNat y x) → ℕ) : ℕ := by
  cases x with
  |mk x1 x2 =>
    cases x1 with
    | zero =>
      exact x2
    | succ x1' =>
      by_cases h : (Nat.succ x1') ≤ x2
      case pos =>
        have h1 : lexNat (Nat.succ x1', x2 - (Nat.succ x1')) (Nat.succ x1', x2) := by
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          linarith
        exact ih (Nat.succ x1', x2 - (Nat.succ x1')) h1
      case neg =>
        have h1 : lexNat (x2, Nat.succ x1') (Nat.succ x1', x2) := by
          push_neg at h
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          aesop
        exact ih (x2, Nat.succ x1') h1

def mygcd := WellFounded.fix lexNat_wf mygcd_ind_step

def mygcd_eq_ind (x : ℕ × ℕ) (ih : (y : ℕ × ℕ) → (lexNat y x) → mygcd y = Nat.gcd y.1 y.2 ) :  mygcd x = gcd x.1 x.2 := by
  have fix_eq := WellFounded.fix_eq lexNat_wf mygcd_ind_step x
  rw [← mygcd] at fix_eq
  cases x with
  | mk x1 x2 =>
    cases x1 with
    | zero =>
      rw [fix_eq]
      simp
      unfold mygcd_ind_step
      simp
    | succ x1' =>
      by_cases h : (Nat.succ x1') ≤ x2
      case pos =>
        have h2 : lexNat (x1' + 1, x2 - (x1' + 1)) (x1' + 1, x2) := by
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          linarith
        have h3 := ih (x1' + 1, x2 - (x1' + 1)) h2
        have : (y : ℕ × ℕ) → lexNat y (x1' + 1, x2) → ℕ := fun y _ ↦ mygcd y
        set h4 := mygcd_ind_step (x1' + 1, x2) fun y _ ↦ mygcd y with def_h4
        rw [mygcd_ind_step] at def_h4
        simp [Nat.casesAuxOn] at def_h4
        split at def_h4
        · rw [fix_eq]
          rw [def_h4]
          rw [h3]
          simp
          aesop
        · contradiction
      case neg =>
        have h2 : lexNat (x2, Nat.succ x1') (Nat.succ x1', x2) := by
          push_neg at h
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          aesop
        have h3 := ih (x2, Nat.succ x1') h2
        have : (y : ℕ × ℕ) → lexNat y (x1' + 1, x2) → ℕ := fun y _ ↦ mygcd y
        set h4 := mygcd_ind_step (x1' + 1, x2) fun y _ ↦ mygcd y with def_h4
        simp [mygcd_ind_step] at def_h4
        simp [Nat.casesAuxOn] at def_h4
        split at def_h4
        · contradiction
        · simp
          rw [fix_eq]
          rw [def_h4]
          rw [h3]
          simp
          apply Nat.gcd_comm

theorem mygcd_eq_gcd : ∀ x : ℕ × ℕ, mygcd x = Nat.gcd x.1 x.2 :=
  WellFounded.fix lexNat_wf mygcd_eq_ind

def condIII_gcd (e : ℕ × ℕ) : Prop :=
  ∀ (x : ℂˣ), (x ^ e.1 = 1 ∧ x ^ e.2 = 1 ↔ x ^ (Nat.gcd e.1 e.2) = 1)

lemma III_gcd_ind
  (e : ℕ × ℕ)
  (ih : (f : ℕ × ℕ) → (lexNat f e) → condIII_gcd f)
  :
  condIII_gcd e := by
  intro x
  cases e with
  | mk e1 e2 =>
    cases e1 with
    | zero =>
      simp
    | succ e1' =>
      by_cases h : (Nat.succ e1') ≤ e2
      case pos =>
        have h1 : lexNat (Nat.succ e1', e2 - (Nat.succ e1')) (Nat.succ e1', e2) := by
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          linarith
        have h2 := ih (Nat.succ e1', e2 - (Nat.succ e1')) h1
        rw [condIII_gcd] at h2
        simp
        have h2 := h2 x
        simp at h2
        have h3 : (x ^ (e1' + 1) = 1 ∧ x ^ (e2 - (e1'+1)) = 1) ↔ (x ^ (e1' + 1) = 1 ∧ x ^ e2 = 1) := by
          apply Iff.intro
          {
            intro h3
            apply And.intro
            { exact h3.1 }
            {
              have h4 := pow_add x (e1' + 1) (e2 - (e1'+1))
              rw [h3.1,h3.2] at h4
              simp at h4
              have h5 : e2 = e1' + 1 + (e2 - (e1' + 1)) := by
                rw [add_comm]
                rw [Nat.sub_add_cancel h]
              rw [← h5] at h4
              exact h4
            }
          }
          {
            intro h3
            apply And.intro
            { exact h3.1 }
            {
              have h5 : e2 = e1' + 1 + (e2 - (e1' + 1)) := by
                rw [add_comm]
                rw [Nat.sub_add_cancel h]
              have h4 := pow_add x (e1' + 1) (e2 - (e1' + 1))
              rw [← h5] at h4
              rw [h3.1,h3.2] at h4
              simp at h4
              rw [h4]
            }
          }
        rw [h3] at h2
        have h4 : (e1' + 1).gcd (e2 - (e1' + 1)) = (e1' + 1).gcd e2 := by
          -- have h5 : (e1' + 1).gcd (e2 - (e1' + 1)) = (e2 - (e1' + 1)).gcd (e1' + 1) := by
          --   apply Nat.gcd_comm
          -- have h6 : (e1'+1).gcd e2 = e2.gcd (e1'+1) := by
          --   apply Nat.gcd_comm
          -- rw [h5,h6]
          set e3 := e2 - (e1'+1) with def_e3
          have h9 := Nat.sub_add_cancel h
          rw [←def_e3] at h9
          rw [← h9]
          have h7 := Nat.gcd_rec (e1'+1) e3
          have h8 := Nat.gcd_rec (e1'+1) (e3+e1'.succ)
          rw [h7,h8]
          have h9 : e3 % (e1' + 1) = (e3 + e1'.succ) % (e1' + 1) := by
            have h10 := Nat.add_mod_right e3 e1'.succ
            rw [h10]
          rw [h9]
        rw [h4] at h2
        exact h2
      case neg =>
        have h1 : lexNat (e2, Nat.succ e1') (Nat.succ e1', e2) := by
          push_neg at h
          simp [lexNat]
          rw [Prod.lex_def]
          simp
          aesop
        have h2 := ih (e2, Nat.succ e1') h1
        rw [condIII_gcd] at h2
        set h2 := h2 x
        simp
        simp at h2
        have h3 : (x ^ e2 = 1 ∧ x ^ (e1' + 1) = 1) ↔ (x ^ (e1' + 1) = 1 ∧ x ^ e2 = 1) := by
          apply And.comm
        rw [h3] at h2
        have h4 : e2.gcd (e1' + 1) = (e1' + 1).gcd e2 := by
          apply Nat.gcd_comm
        rw [h4] at h2
        exact h2

theorem III_gcd :
  ∀ e : ℕ × ℕ,
  condIII_gcd e
  :=
  WellFounded.fix lexNat_wf III_gcd_ind

def setIII' (e : ℕ+) : Set ℂˣ := {ξ : ℂˣ | ξ ≠ 1 ∧ ξ^e.1 = 1}

lemma setIII_eq_setIII' (e f : ℕ+) : setIII e f = setIII' (PNat.gcd e f) := by
  simp [setIII]
  simp [setIII']
  have h1 := III_gcd (e,f)
  rw [condIII_gcd] at h1
  apply Set.ext
  intro x
  apply Iff.intro
  {
    intro h2
    apply And.intro
    { exact h2.1 }
    {
      have h1 := h1 x
      have h1 := h1.1
      have h2 := h2.2
      exact h1 h2
    }
  }
  {
    intro h2
    apply And.intro
    { exact h2.1 }
    {
      have h3 := h1 x
      have h3 := h3.2
      exact h3 h2.2
    }
  }

lemma PNat_gcd_self (e : ℕ+) : PNat.gcd e e = e := by
  rw [← PNat.coe_inj]
  rw [PNat.gcd_coe]
  simp

lemma setIII'_finite (e : ℕ+) : (setIII' e).Finite := by
  have h1 := setIII_finite e e
  have h2 := setIII_eq_setIII' e e
  rw [PNat_gcd_self] at h2
  rw [h2] at h1
  exact h1

lemma finite_eq (e f : ℕ+): cardIII e f = Nat.card (setIII' (PNat.gcd e f)) := by
  have h1 := setIII_eq_setIII' e f
  have h2 : Nat.card (setIII e f) = Nat.card (setIII' (PNat.gcd e f)) := by
    rw [h1]
  have h3 := Nat.card_eq_card_finite_toFinset (setIII_finite e f)
  rw [h3] at h2
  exact h2

noncomputable def finsetIII' (e : ℕ+):= (setIII'_finite e).toFinset

lemma setIII'_sub_rootsOfUnity (e : ℕ+) : setIII' e ⊆ {ξ : ℂˣ | ξ^(e:ℕ) = 1} := by
  intro x
  intro h
  simp [setIII'] at h
  exact h.2

lemma setIII'_compl (e : ℕ+) : { ξ : ℂˣ | ξ^(e:ℕ) = 1} \ (setIII' e) = {1} := by
  apply Set.eq_of_subset_of_subset
  { intro x
    intro h
    simp at h
    rw [setIII'] at h
    simp at h
    have h2 := h.2
    push_neg at h2
    by_cases h3 : x = 1
    { exact h3 }
    { have h4 := h2 h3
      have h1 := h.1
      contradiction
    }
  }
  { intro x
    intro h
    simp
    apply And.intro
    {
      have h1 : x = 1 := by exact h
      rw [h1]
      simp
    }
    {
      intro h1
      rw [setIII'] at h1
      simp at h1
      aesop
    }
  }



-- lemma pow_and_pow
--   (e f : ℕ)
--   (e_le_f : e ≤ f)
--   (x : ℂˣ)
--   : x^e = 1 ∧ x^f = 1 → x^(f-e) = 1
--   := by
--   intro h
--   have h1 : f = e + (f - e) := by
--     rw [add_comm]
--     rw [Nat.sub_add_cancel]
--     exact e_le_f
--   set h3 := pow_add x e (f-e)
--   rw [h.1] at h3
--   simp at h3
--   rw [← h1] at h3
--   rw [h.2] at h3
--   exact h3.symm

end CaseII
