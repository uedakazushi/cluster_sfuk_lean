import Mathlib.Init.Set
import Mathlib.Data.Set.Finite

#eval 7/3
#eval 8%3

set_option diagnostics true

def set1 : Set Nat := {n : Nat | n < 10}

#check set1

#check Set.finite_le_nat

example (k:Nat) : Set.Finite {n : Nat | n ≤ k } := by
  exact Set.finite_le_nat k

def I (e f i : Nat) : Set Nat :=
  {n : Nat |
  n % e ≠ e - 1
  ∧ n % f ≠ f - 1
  ∧ n / e + n / f = i }

example (e f n i: Nat) :
  n / e + n / f = i → n ≤ e * i + e := by
  intro h
  have h1 : n / e ≤ i := Nat.le.intro h
  have h2 := Nat.mul_le_mul_left e h1
  have h3 : e * (n / e) + n % e = n := by
    rw [Nat.div_add_mod]
  have h4 := Nat.le.intro h3
