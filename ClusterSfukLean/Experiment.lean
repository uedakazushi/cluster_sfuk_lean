import Mathlib

section

#check WellFounded.min
def h1 := Nat.lt.isWellOrder
#check h1.3

def nat_lt_iswellfounded := Nat.lt.isWellOrder.3.wf

#check WellFounded.min Nat.lt.isWellOrder.3.wf

end

#check quot_rem


        #check add_sub

        simp [d_pos] at h3
      have h3 := Nat.div_eq r d
      have d_pos : d > (0:Nat) := d.2
      simp [d_pos] at h3
      simp [h2] at h3
have h4 : ¬ ((0:Nat) < ↑d ∧ ↑d ≤ r) := by
        push_neg
        intro h'
        assumption
      apply Eq.symm
      have h5 : (if (0:Nat) < ↑d ∧ ↑d ≤ r then (r - (d:Nat)) % (d:Nat) else r) = 0 := by
        simp [h2]

rw [h4] at h3
    · rw [h.1]
    ·
have h1 : n = 0 := by
      simp at h

lemma h6 : ∀ m: Nat, ∀ e : ℕ+ , m % e ≠ 0 → m / e = (m - 1) / e := by
  intro m e h
  sorry


variable (e f l : ℕ+)
variable (e_coprime_f : Nat.Coprime e f)
variable (n i : ℕ)




def s: Set Nat := {n : Nat | n ≥ 1 ∧ n ≤ 3}

def t: Set Nat := {1,2,3}

#check s
#print s
#check t
#print t

example : s = t := by
  apply Set.ext
  intro n
  simp [s, t]
  apply Iff.intro
  · intro h
    cases n with
    | zero => linarith
    | succ n' =>
      cases n' with
      | zero => simp
      | succ n'' =>
        cases n'' with
        | zero => simp
        | succ n''' =>
          simp
          have h' := h.2
          linarith
  · intro h
    cases h with
    | inl h1 =>
      apply And.intro
      · linarith
      · linarith
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        apply And.intro
        · linarith
        · linarith
      | inr h4 =>
        apply And.intro
        · linarith
        · linarith

def u : Finset Nat := {1,2,3}

#print s

def finite_t : Set.Finite s := by
  apply Set.Finite.subset (Set.finite_le_nat 3)
  intro n
  intro h
  exact h.2

noncomputable def finset_s := Set.Finite.toFinset (finite_t)

#check finset_s.card

#check u.card

#eval u.card

variable (a b : Nat)

def setI : Set Nat :=
  {n : Nat |
  a ≤ n
  ∧ n ≤ b }

def setI_finite : Set.Finite (setI a b) := by
  apply Set.Finite.subset (Set.finite_le_nat b)
  intro n
  intro h
  exact h.2

noncomputable def finsetI : Finset Nat := Set.Finite.toFinset (setI_finite a b)

noncomputable def cardI : Nat := (finsetI a b).card

#eval ({1} : Finset Nat) ∪ {0}

#eval ({1} : Finset Nat) ∪ {0} = {1,0}

def s2 : Finset Nat := {1,2,0}

#check s2

def s3 := s2 \ {1}

#eval s3

def s4 := { x ∈ s3 | x ≠ 1 }

#check s4

-- #eval s4 -- fails

example : ∀ n : ℕ, Fintype.card (Fin n) = n := Fintype.card_fin
example : ∀ n : ℕ, Finset.card (Finset.range n) = n := Finset.card_range

#check Finset.range 3

#eval Finset.range 3

#check Fin 3

#eval Finset.range 3 \ {0}

def type02 := { a : Fin 3 // a ≠ 1 }

#check type02

#print type02

example : Fin 3 := 2

#print Fin

#print cardI

def finsetminus (s : Finset Nat) (t : Finset Nat) : Finset Nat := s \ t

#check finsetminus ({1,2,3} : Finset Nat) ({1} : Finset Nat)

#eval finsetminus ({1,2,3} : Finset Nat) ({1} : Finset Nat)

#check ({1,2,3} : Finset Nat) \ ({1,2} : Finset Nat)

#check (Finset.range 3) \ (Finset.range 1)
#eval (Finset.range 3) \ (Finset.range 1)

#eval ((Finset.range 3) \ (Finset.range 1)).card

#eval ((Finset.range 10) \ (Finset.range 7)).min

#eval (Finset.range 3).max

theorem main : ((Finset.range (a+1)) \ (Finset.range b)).card = a - b + 1 := by
  sorry
