import ClusterSfukLean.MainLemma

section CaseII

lemma setII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : (setII (e*l) (f*l) i) =
    (
    ite ((e+f) ∣ (e+f-1))
    (Set.singleton (e*f*l*(i+1)/(e+f) : ℕ))
    ∅
    )
  := by
  sorry

lemma cardII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : cardII (e*l) (f*l) i = ite ((e+f) ∣ (e+f-1)) 1 0
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

def ind_step (x : ℕ × ℕ) (ih : (y : ℕ × ℕ) → (lexNat y x) → ℕ) : ℕ := by
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

def mygcd := WellFounded.fix lexNat_wf ind_step

def eq_ind (x : ℕ × ℕ) (ih : (y : ℕ × ℕ) → (lexNat y x) → mygcd y = Nat.gcd y.1 y.2 ) :  mygcd x = gcd x.1 x.2 := by
  have fix_eq := WellFounded.fix_eq lexNat_wf ind_step x
  rw [← mygcd] at fix_eq
  cases x with
  | mk x1 x2 =>
    cases x1 with
    | zero =>
      rw [fix_eq]
      simp
      unfold ind_step
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
        set h4 := ind_step (x1' + 1, x2) fun y _ ↦ mygcd y with def_h4
        rw [ind_step] at def_h4
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
        set h4 := ind_step (x1' + 1, x2) fun y _ ↦ mygcd y with def_h4
        simp [ind_step] at def_h4
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
  WellFounded.fix lexNat_wf eq_ind

end CaseII
