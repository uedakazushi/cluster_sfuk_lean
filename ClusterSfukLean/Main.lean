import ClusterSfukLean.SetIII



theorem main
  (e f l : ℕ+)
  (i : ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  by_cases h1 : e.1 + f.1 ∣ i + 1
  case pos =>
    have h2 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    split at h2
    case isTrue h3 =>
      have ef_ge_4 : e.1 + f.1 ≥ 4 := Nat.add_le_add e_ge_2 f_ge_2
      have i_pos : i > 0 := by
        by_contra i_zero
        push_neg at i_zero
        simp at i_zero
        rw [i_zero] at h1
        simp at h1
        linarith
      have i_mod_ef := mod_of_dvd_succ i (e.1+f.1) (by linarith) h1
      have h4 := i_mod_e_add_f_φinv_i_empty e f i l e_ge_2 f_ge_2 coprime l.2 i_mod_ef
      rw [h]
      rw [cardI]
      have h5 : (finsetI (e*l) (f*l) i) = ∅ := by
        rw [finsetI]
        apply Finset.ext
        simp
        rw [setI]
        simp
        by_contra h7
        push_neg at h7
        match h7 with
        | ⟨ n, _, _, h8 ⟩ =>
          rw [φinv] at h4
          rw [φ] at h4
          dsimp [nat_div] at h4
          have h9 : n ∈ {n | n / (↑e * ↑l) + n / (↑f * ↑l) = i} := by
            exact h8
          rw [h4] at h9
          exact h9
      have h6 : (finsetI (e * l) (f * l) i).card = 0 := by
        rw [h5]
        simp
      rw [h6]
      simp
      sorry
    case isFalse h3 =>
      contradiction
  case neg =>
    have h2 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    split at h2
    case isTrue h3 =>
      contradiction
    case isFalse h3 =>
      sorry
