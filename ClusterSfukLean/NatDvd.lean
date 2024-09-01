import Mathlib
-- import ClusterSfukLean.QuotRem
set_option linter.unusedVariables false

open Classical
noncomputable instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match Classical.em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

def nat_div (d n : ℕ) : ℕ := n / d

lemma nat_ne_zero_iff_pos (n:Nat) : n ≠ 0 ↔ n > 0 := by
  apply Iff.intro
  { intro h
    have h1 := Nat.pos_of_ne_zero h
    exact h1
  }
  { intro h
    have h1 := Nat.ne_of_gt h
    exact h1
  }

lemma nat_div_monotone (d : ℕ) : Monotone (nat_div d) := by
  intro n m h
  apply Nat.div_le_div_right
  assumption

lemma nat_succ_div_le (n d : ℕ) : (n+1) / d ≤ (n / d)+1 := by
  rw [Nat.succ_div]
  -- aesop
  by_cases h : d ∣ n + 1
  {
    rw [if_pos h]
  }
  { rw [if_neg h]
    linarith
  }

lemma nat_add_div_monotone (e f : ℕ)
 : Monotone (fun n ↦ n / e + n / f) := by
  intro n m h
  apply Nat.add_le_add
  apply Nat.div_le_div_right
  assumption
  apply Nat.div_le_div_right
  assumption

lemma not_dvd_mod_eq
  (e n: ℕ)
  (n_ne_zero : n ≠ 0)
  (h : ¬ e ∣ n)
  :
  n / e = (n-1)/e := by
  set n' := n - 1 with h2
  have h4 := Nat.sub_one_add_one n_ne_zero
  rw [←h2] at h4
  have h5 := Nat.succ_div n' e
  rw [h4] at h5
  rw [if_neg h] at h5
  exact h5

lemma dvd_mod_ne
  (e n: ℕ)
  (n_ne_zero : n ≠ 0)
  (h : e ∣ n)
  :
  (n-1) / e + 1 = n/e := by
  set n' := n - 1 with h2
  have h4 := Nat.sub_one_add_one n_ne_zero
  rw [←h2] at h4
  have h5 := Nat.succ_div n' e
  rw [h4] at h5
  rw [if_pos h] at h5
  exact Eq.symm h5

lemma mul_pred_div (k d: ℕ) (d_pos : d > 0) : (k * d - 1) / d = k - 1 := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    induction k with
    | zero =>
      simp
      induction d with
      | zero =>
        simp
      | succ d ih =>
        simp
        rw [Nat.div_eq]
        simp
    | succ k ih' =>
      simp
      have h1 : (k+1+1) * d - 1 = (k+1) * d - 1 + d := by
        have h2 := Nat.add_mul (k+1) 1 d
        rw [h2]
        simp
        have h2 (a b : Nat)  (pos_a : a > 0) : a + b - 1= a - 1 + b := by
          induction b with
          | zero =>
            simp
          | succ b ih =>
            simp
            have h3 : a - 1 + (b+1) = a - 1 + 1 + b := by
              ring
            rw [h3]
            have h4 : 1 ≤ a := by
              linarith
            rw [Nat.sub_add_cancel h4]
        rw [h2]
        have h3 : k+1 > 0 := by
          linarith
        aesop
      rw [h1]
      have h2 := Nat.add_div_right ((k + 1) * d - 1) d_pos
      rw [h2]
      rw [ih]
      simp
