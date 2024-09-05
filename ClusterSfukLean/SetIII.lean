import ClusterSfukLean.CaseII2

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

def setOfComplexRootsOfUnity (e : ℕ+) : Set ℂˣ := {ξ : ℂˣ | ξ^(e.1) = 1}

def setOfComplexRootsOfUnity_eq (e : ℕ+):(setOfComplexRootsOfUnity e) = (rootsOfUnity e ℂ) := by
  apply Set.eq_of_subset_of_subset
  { intro x
    intro h1
    have h2 := mem_rootsOfUnity e x
    exact h2.mp h1
  }
  { intro x
    intro h1
    simp [rootsOfUnity] at h1
    exact h1
  }

def setOfComplexRootsOfUnity_finite (e : ℕ+) : (setOfComplexRootsOfUnity e).Finite := by
  rw [setOfComplexRootsOfUnity_eq e]
  apply Finite.of_fintype

noncomputable def finsetOfComplexRootsOfUnity (e : ℕ+) : Finset ℂˣ := (setOfComplexRootsOfUnity_finite e).toFinset

lemma finsetIII'_sub_rootsOfUnity (e : ℕ+) : finsetIII' e ⊆ finsetOfComplexRootsOfUnity e := by
  intro x
  intro h
  simp [finsetIII'] at h
  simp [setIII'] at h
  simp [finsetOfComplexRootsOfUnity]
  simp [setOfComplexRootsOfUnity]
  exact h.2

lemma setIII'_compl (e : ℕ+) : (finsetOfComplexRootsOfUnity e) \ (finsetIII' e) = {1} := by
  simp [finsetOfComplexRootsOfUnity]
  simp [setOfComplexRootsOfUnity]
  simp [finsetIII']
  simp [setIII']
  apply Finset.ext
  intro x
  simp
  apply Iff.intro
  {
    intro h
    by_contra x_ne_one
    have h1 := h.1
    have h2 := h.2 x_ne_one
    contradiction
  }
  {
    intro h
    apply And.intro
    { rw [h]
      simp
    }
    {
      intro h1
      contradiction
    }
  }

def equiv_rootsOfUnity2 (e : ℕ+) : { x : ℂˣ // x ∈ rootsOfUnity e ℂ } ≃ (setOfComplexRootsOfUnity e) := by
  simp [setOfComplexRootsOfUnity]
  set tofun : {x : ℂˣ // x ^ e.1 = 1} → {ξ : ℂˣ // ξ ^ e.1 = 1} := by
    intro x
    exact x
  set invfun : {ξ : ℂˣ // ξ ^ e.1 = 1} → {x : ℂˣ | x ^ e.1 = 1} := by
    intro ξ
    exact ξ
  have left_inv : Function.LeftInverse invfun tofun := by
    simp [Function.LeftInverse]
  have right_inv : Function.RightInverse invfun tofun := by
    simp [Function.RightInverse]
    simp [Function.LeftInverse]
  exact ⟨ tofun, invfun, left_inv, right_inv ⟩

def finsetOfComplexRootsOfUnity_card (e : ℕ+) : (finsetOfComplexRootsOfUnity e).card = e.1 := by
  have card1 : Fintype.card { x : ℂˣ // x ∈ rootsOfUnity e ℂ } = e.1 := Complex.card_rootsOfUnity e
  have eq1 : { x : ℂˣ // x ∈ rootsOfUnity e ℂ } ≃ (setOfComplexRootsOfUnity e) := by
    simp [setOfComplexRootsOfUnity]
    have h2 := equiv_rootsOfUnity2 e
    exact h2
  set set1 := setOfComplexRootsOfUnity e
  have set1_finite: Set.Finite set1 := setOfComplexRootsOfUnity_finite e
  have set1_fintype : Fintype set1 := Set.Finite.fintype set1_finite
  have h2 := Set.toFinset_card set1
  have h3 : set1.toFinset = finsetOfComplexRootsOfUnity e := by
    simp [set1]
    simp [finsetOfComplexRootsOfUnity]
  rw [h3] at h2
  have eq1' := Nonempty.intro eq1
  have eq1'' := Fintype.card_eq.mpr eq1'
  rw [eq1''] at card1
  rw [← h2] at card1
  exact card1

lemma cardIII'_card (e : ℕ+): Nat.card (setIII' e) = e - 1 := by
  have := setIII'_compl e
  have h2 := setIII'_finite e
  have h3 := Nat.card_eq_card_finite_toFinset h2
  have h4 : Nat.card (setIII' e) = (finsetIII' e).card := by
    exact h3
  have h5 := finsetIII'_sub_rootsOfUnity e
  have h6 := setIII'_compl e
  have h7 :=Finset.card_sdiff_add_card_eq_card h5
  rw [h6] at h7
  simp at h7
  have h8 := finsetOfComplexRootsOfUnity_card e
  rw [h8] at h7
  rw [h4]
  rw [add_comm] at h7
  have h9 : (finsetIII' e).card + 1 - 1 = e.1 - 1 := by
    conv => rhs
    rw [← h7]
  rw [Nat.add_one_sub_one] at h9
  exact h9

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
