import Mathlib
import ClusterSfukLean.NatInterval
import ClusterSfukLean.QuotRem

open Classical
noncomputable instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match Classical.em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

lemma Nat_div_monotone (d : ℕ) : Monotone (fun n ↦ n / d) := by
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

lemma Nat_add_div_monotone (e f : ℕ)
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
