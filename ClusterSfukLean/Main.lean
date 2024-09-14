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
      rw [h]
      rw [cardI]
      have h7 : (finsetI e f i) = ∅ := by
        rw [finsetI]
        apply Finset.ext
        simp
        rw [setI]
        simp
        by_contra h8
        push_neg at h8
        match h8 with
        | ⟨ n, _, _, h9 ⟩ =>
          have h4 := i_mod_e_add_f_φinv_i_empty e f i 1 e_ge_2 f_ge_2 coprime (by linarith) i_mod_ef
          rw [φinv] at h4
          rw [φ] at h4
          dsimp [nat_div] at h4
          have h10 : n ∈ {n | n / (↑e) + n / (↑f) = i} := by
            exact h9
          simp at h4
          rw [h4] at h10
          exact h10
      have h8 : (finsetI e f i).card = 0 := by
        rw [h7]
        simp
      rw [h8]
      simp
      have h9 := cardII_dichotomy e f l i e_ge_2 f_ge_2 coprime
      split at h9
      case isTrue h10 =>
        rw [h9]
        simp
        have h11 := cardII_dichotomy e f 1 i e_ge_2 f_ge_2 coprime
        simp at h11
        split at h11
        case isTrue h12 =>
          rw [h11]
          simp
          have h13 := cardIII_gcd e f
          have h14 := cardIII_gcd (e*l) (f*l)
          have gcd1 : e.1.gcd f.1 = 1 := by
            exact coprime
          have gcd2 : (e*l).1.gcd (f*l).1 = l := by
            have h15 := Nat.gcd_mul_right e.1 l.1 f.1
            simp at h15
            have el : e.1 * l.1 = (e*l).1 := by
              aesop
            rw [el.symm]
            have fl : (f*l).1 = f.1 * l.1 := by
              aesop
            rw [fl]
            rw [h15]
            rw [gcd1]
            simp
            rfl
          rw [h13]
          rw [h14]
          rw [gcd2]
          rw [gcd1]
          simp
        case isFalse h12 =>
          contradiction
      case isFalse h10 =>
        contradiction
    case isFalse h3 =>
      contradiction
  case neg =>
    rw [h,h]
    have cardII1 := cardII_dichotomy e f 1 i e_ge_2 f_ge_2 coprime
    simp at cardII1
    have cardIIl := cardII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    split at cardII1
    case isTrue => contradiction
    case isFalse =>
    split at cardIIl
    case isTrue => contradiction
    case isFalse =>
    rw [cardII1,cardIIl]
    simp
    clear cardII1 cardIIl
    exact caseI_main e f l i e_ge_2 f_ge_2 coprime h1
