import ClusterSfukLean.CaseII1

lemma setII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : (setII (e*l) (f*l) i) =
    (
    ite ((e.1+f.1) ∣ (i+1))
    (Set.singleton (e*f*l*(i+1)/(e+f) - 1 : ℕ))
    ∅
    )
  := by
  by_cases dvd: ((e.1+f.1) ∣ (i+1))
  case pos =>
    apply Eq.symm
    rw [ite_eq_iff]
    apply Or.inl
    apply And.intro
    { exact dvd }
    {
      have h1 := setII_singleton e f l i e_ge_2 f_ge_2 dvd
      exact h1.symm
    }
  case neg =>
    apply Eq.symm
    rw [ite_eq_iff]
    have h1 := setII_empty_if_not_dvd e f l i e_ge_2 f_ge_2 coprime dvd
    apply Or.inr
    apply And.intro
    exact dvd
    exact h1.symm

example : Nat.card (Set.singleton 1) = 1 := by
  simp

lemma singleton_card (n : ℕ) : (Set.singleton n).toFinset.card = 1 := by
  have := Set.card_singleton n
  have := Set.toFinset_card (Set.singleton n)
  aesop

lemma cardII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : cardII (e*l) (f*l) i = ite ((e.1+f.1) ∣ (i+1)) 1 0
  := by
  by_cases dvd: ((e.1+f.1) ∣ (i+1))
  case pos =>
    apply Eq.symm
    rw [ite_eq_iff]
    apply Or.inl
    apply And.intro
    exact dvd
    rw [cardII]
    rw [finsetII]
    have h1 := setII_finite (e*l) (f*l) i
    have h2 := Set.Finite.fintype h1
    have := Set.Finite.toFinset_eq_toFinset h1
    rw [Set.Finite.toFinset_eq_toFinset]
    have h4 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    have h5 : setII (e*l) (f*l) i = Set.singleton (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1) := by
      conv =>
      lhs
      rw [h4]
      split
      {
        case isTrue h5; rfl
      }
      {
        case isFalse; rfl
      }
    have h6 : Set.toFinset (setII (e * l) (f * l) i) = Set.toFinset (Set.singleton (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1)) := by
      conv =>
      lhs
      congr
      aesop
    rw [h6]
    have h7 := singleton_card (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1)
    rw [h7]
  case neg =>
    split
    case isTrue h
    have := dvd h
    contradiction
    case isFalse h
    have h3 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    have := Eq.symm h3
    rw [cardII]
    rw [finsetII]
    have h4 := setII_finite (e*l) (f*l) i
    have h5 := Set.Finite.fintype h4
    have := Set.Finite.toFinset_eq_toFinset h4
    rw [Set.Finite.toFinset_eq_toFinset]
    have h7 : setII (e*l) (f*l) i = ∅ := by
      conv =>
      lhs
      rw [h3]
      split
      {
        case isTrue h5; contradiction
      }
      {
        case isFalse h5; rfl
      }
    have h8 : Set.toFinset (setII (e * l) (f * l) i) = Set.toFinset ∅ := by
      conv =>
      lhs
      congr
      aesop
    rw [h8]
    simp

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
