import Mathlib
-- set_option linter.unusedVariables false

lemma quot_rem : ∀ q n r: ℕ, ∀ d : ℕ+, (n = q * d + r ∧ 0 ≤ r ∧ r < d)
 → (q = n / d ∧ r = n % d) := by
  intro q
  induction q with
  |zero =>
    intro n r d h
    simp at h
    apply And.intro
    · rw [h.1]
      have h2 : (¬ ↑d ≤ r) := by
        intro h'
        -- have h'' := le_antisymm h'
        -- have h''' : r ≤ ↑d := by
        --   linarith
        linarith
      have h3 := Nat.div_eq r d
      simp [h2] at h3
      simp [h3]
    · rw [h.1]
      have h3 := Nat.mod_eq r d
      have h2 : (¬ ↑d ≤ r) := by
        intro h'
        -- have h'' := le_antisymm h'
        -- have h''' : r ≤ ↑d := by
        --   linarith
        linarith
      have d_pos : d > (0:Nat) := d.2
      simp [d_pos] at h3
      simp [h2] at h3
      exact Eq.symm h3
  |succ q ih =>
    intro n r d h
    apply And.intro
    · have h1 := h.1
      -- have h2 := (h.2).1
      have h3 := (h.2).2
      have h4 := Nat.div_eq n d
      have d_pos : d > (0:Nat) := d.2
      have h5 : ↑ d ≤ n := by
        -- have h1' : n = d + q * d + r := by
        --   simp [h1]
        --   rw [Nat.add_mul]
        --   rw [add_comm]
        --   simp
        -- have h1'' : n ≥ d + q * d := by
        --   linarith
        have h1''' : d + q * d ≥ d := by
          have h1'''' : q * d ≥ 0 := by
            apply mul_nonneg
            linarith
            linarith
          linarith
        linarith
      simp [d_pos] at h4
      simp [h5] at h4
      have ih1 := ih (n-d) r d
      simp [h1] at ih1
      have h1' : (q + 1) * ↑d + r - ↑d = q * ↑d + r := by
        ring_nf
        nth_rw 1 [←add_comm]
        nth_rw 1 [←add_assoc]
        simp
        rw [add_comm]
      have h6 := Nat.div_eq n d
      simp [d_pos] at h6
      simp [h5] at h6
      have ih1' := ih1 h1'
      have ih1'' := (ih1' h3).1
      rw [h6]
      have h1' : (q + 1) * ↑d + r - ↑d = n - ↑ d := by
        rw [h1]
      rw [h1'] at ih1''
      rw [ih1'']
    · have h1 := h.1
      -- have h2 := (h.2).1
      have h3 := (h.2).2
      have h4 := Nat.mod_eq n d
      have d_pos : d > (0:Nat) := d.2
      have h5 : ↑ d ≤ n := by
        -- have h1' : n = d + q * d + r := by
        --   simp [h1]
        --   rw [Nat.add_mul]
        --   rw [add_comm]
        --   simp
        -- have h1'' : n ≥ d + q * d := by
        --   linarith
        have h1''' : d + q * d ≥ d := by
          have h1'''' : q * d ≥ 0 := by
            apply mul_nonneg
            linarith
            linarith
          linarith
        linarith
      simp [d_pos] at h4
      simp [h5] at h4
      have ih1 := ih (n-d) r d
      simp [h1] at ih1
      have h1' : (q + 1) * ↑d + r - ↑d = q * ↑d + r := by
        ring_nf
        nth_rw 1 [←add_comm]
        nth_rw 1 [←add_assoc]
        simp
        rw [add_comm]
      have h6 := Nat.mod_eq n d
      simp [d_pos] at h6
      simp [h5] at h6
      have ih1' := ih1 h1'
      have ih1'' := (ih1' h3).2
      rw [h6]
      have h1' : (q + 1) * ↑d + r - ↑d = n - ↑ d := by
        rw [h1]
      rw [h1'] at ih1''
      rw [ih1'']
