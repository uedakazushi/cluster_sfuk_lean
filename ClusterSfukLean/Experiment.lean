import Mathlib

lemma add_one_div_le_div_add_one (n : ℕ) (d : ℕ+) : (n+1) / d ≤ (n / d) + 1 := by
  have h1 : n + 1 ≤ n + d := by
    have h1' : 1 ≤ (d:Nat) := by
      exact d.2
    linarith
  have h2 := @Nat.div_le_div_right (n+1) (n+d) d h1
  have h3 := Nat.add_div_right n d.2
  aesop
