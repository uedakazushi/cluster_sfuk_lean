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
    set inv : ℂ := x^(n.1-1) with def_inv
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
    with def_tofun
  set invfun : {x : ℂˣ | x ^ n.1 = 1} → {x : ℂ | x ^ n.1 = 1} := by
    intro x''
    set x' := x''.1 with def_x'
    have p' : x' ^ n.1 = 1 := by
      rw [def_x']
      exact x''.2
    set x := x'.1 with def_x
    have p : x ^ n.1 = 1 := by
      simp [Units.ext_iff] at p'
      exact p'
    exact ⟨x, p⟩
    with def_invfun
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

end CaseII
