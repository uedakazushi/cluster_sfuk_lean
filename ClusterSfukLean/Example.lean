import ClusterSfukLean.Main
set_option linter.unusedVariables false

example : PNat.mod 3 3 = 3 := rfl

example : (3:ℕ) % (3:ℕ+) = 0 := rfl

example : (1:PNat) - (1:PNat) = 1 := rfl

#print setI

#check {m : ℕ // m ≤ 3}
example : (0 : Nat) = 0 := rfl
example : Nat := 0
example : {m : ℕ // m ≤ 3} := ⟨0, by linarith⟩
example : Fin 3 := ⟨ 0, by linarith ⟩
example : Fin 3 := by
  apply Fin.mk
  have h : 0 < 3 := by linarith
  exact h
#print Fin
example : {m : ℕ // m = 0} := ⟨0, rfl⟩
#check Set.Mem (0:Nat) {m : ℕ | m = 0}
#check Set.singleton 0 = {m : ℕ // m = 0}
example : Set.singleton 0 = {m : ℕ // m = 0} := rfl
#check {m : ℕ // m ≤ 3}
#check {m : ℕ | m ≤ 3}
#check (↑{m : ℕ | m ≤ 3} : Type)
#check Fin 3
#check Fin 3 = {m : ℕ // m < 3}
example : {m : ℕ // m < 3} := ⟨ 0, by linarith ⟩

#check { 0 } = Set.singleton 0
#check (0:Nat) ∈ { (0:Nat) }
#check 0 ∈ { 0 }
#check { 0 } = { 0 }
#check 0 = 0
#check Finite (Fin 3)
#check Finite {m : ℕ // m < 3}
#check {m : ℕ | m < 3}
#check Finite {m : ℕ | m < 3}
example : Finite {m : ℕ | m < 3} := by
  apply finite_of_bounded_of_Nat
  rw [IsBounded]
  exists 4
  intro x
  intro h
  have h := Membership.mem.out h
  linarith

#check Set.instMembership.1
