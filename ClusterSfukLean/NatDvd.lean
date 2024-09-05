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

lemma mul_pred_mod
  (k d: ℕ) (k_pos : k > 0) (d_pos : d > 0)
  :
  (k * d - 1) % d = d - 1 := by
  have h1 := mul_pred_div k d d_pos
  have h2 := Nat.div_add_mod (k * d - 1) d
  rw [h1] at h2
  rw [Nat.add_comm] at h2
  have h3 := Nat.add_sub_cancel ((k * d - 1) % d) (d * (k - 1))
  rw [h2] at h3
  have h4 : k * d - 1 - d * (k - 1) = d - 1 := by
    have h5 : k * d - 1 - d * (k - 1) = k * d - d * (k-1) - 1 := by
      rw [Nat.sub_sub]
      rw [Nat.add_comm]
      rw [Nat.sub_sub]
    rw [h5]
    have h6 : k * d - d * (k-1) = d := by
      have h7 : k * d = d * k := by
        ring
      rw [h7]
      have h8 := Nat.mul_sub d k (k-1)
      have h9 : k - (k-1) = 1 := by
        set k' := k - 1 with def_k'
        have succ_k' : k = k' + 1 := by
          rw [def_k']
          have k_ne_zero : k ≠ 0 := by linarith
          exact (Nat.sub_one_add_one k_ne_zero).symm
        rw [succ_k']
        have h10 : k' ≤ k' := by
          linarith
        have h11 := Nat.succ_sub h10
        rw [h11]
        simp
      rw [h9] at h8
      rw [← h8]
      simp
    rw [h6]
  rw [h4] at h3
  exact h3.symm

lemma div_lt_of_lt_and_mod_eq
  (a b d: ℕ)
  (mod_eq : a % d = b % d)
  (a_lt_b : a < b)
  :
  a / d < b / d := by
  have ha := Nat.div_add_mod a d
  set r := a % d with r1
  have hb := Nat.div_add_mod b d
  have r2 : r = b % d := by
    rw [r1] at mod_eq
    exact mod_eq
  rw [← r2] at hb
  by_contra h
  push_neg at h
  have h1 := Nat.mul_le_mul_left d h
  have h2 := Nat.add_le_add_right h1 r
  rw [ha, hb] at h2
  linarith

lemma mod_of_dvd_succ
  (n d : ℕ)
  (d_pos : d > 0)
  (dvd : d ∣ n + 1)
  :
  n % d = d - 1
  := by
  match dvd with
  | ⟨ c, hc ⟩ =>
  have h := Nat.add_one_sub_one n
  rw [hc] at h
  have hd := Nat.sub_add_cancel d_pos
  simp at hd
  set d' := d - 1 with def_d'
  have c_pos : c > 0 := by
    by_contra c_zero
    push_neg at c_zero
    simp at c_zero
    rw [c_zero] at hc
    simp at hc
  set c' := c - 1 with def_c'
  have hc' : c = c' + 1 := by
    have h1 := Nat.sub_add_cancel c_pos
    rw [def_c']
    rw [h1]
  rw [hc'] at h
  rw [Nat.mul_add] at h
  rw [Nat.add_sub_assoc] at h
  simp at h
  rw [← def_d'] at h
  rw [← h]
  rw [Nat.add_mod]
  simp
  rw [← hd]
  simp
  simp
  linarith
