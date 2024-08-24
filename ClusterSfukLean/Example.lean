import ClusterSfukLean.Main
set_option linter.unusedVariables false

#print Monotone

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

example : Finset ℕ := {m : ℕ | m ≤ 10}.toFinset

namespace temp

example : Finset ℕ := Set.toFinset {m : ℕ | m ≤ 10}

def s1 := {m : ℕ | m ≤ 10}
-- def s2 := Set.toFinset s1 -- fails

#check Fintype s1
#check @Set.Elem {m : ℕ | m ≤ 10}
#check {m | m ≤ 10}
#check ℕ

example : 1 = 1 := by
 set s1 := {m : ℕ | m ≤ 10} with h1
 set s2 := Set.toFinset s1
 have s3 := {m : ℕ | m ≤ 10}
--  set s4 := Set.toFinset s3 -- fails
 let s5 := {m : ℕ | m ≤ 10}
 let s6 := Set.toFinset s5
 rfl

end temp

#check {m : ℕ | m < 4}

example (n : ℕ) : {m : ℕ | m ≤ n} = (⋃ i ∈ {m : ℕ | m < n + 1}, Set.singleton i) := by
  apply Set.ext
  intro x
  apply Iff.intro
  { intro h
    simp
    simp at h
    exists x
    apply And.intro
    linarith
    exact Set.mem_singleton x
  }
  { intro h
    simp
    simp at h
    cases h with
    | intro a h1 =>
      simp at h1
      have h2 := h1.1
      have h3 := h1.2
      have h4 : x = a := by
        exact h3
      linarith
  }
