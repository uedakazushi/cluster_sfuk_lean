import Mathlib

lemma finite_of_bounded_of_Nat (s: Set ℕ) :
  (∃ k : ℕ, ∀ x ∈ s, x ≤ k) → s.Finite := by
  intro h
  cases h with
  | intro k h =>
      have h1 : s ⊆ {n : ℕ | n ≤ k} := by
        rw [Set.subset_def]
        intro x
        intro h2
        exact h x h2
      apply Set.Finite.subset (Set.finite_le_nat k)
      assumption

lemma nat_mod_pnat_le (n : ℕ) (m : ℕ+) : n % m ≤ m := by
  cases n with
  | zero => simp
  | succ n' =>
      let n : PNat := ⟨ Nat.succ n', Nat.succ_pos n' ⟩
      have nn' : n'+1 = n := rfl
      have h1 := (PNat.mod_le n m).2
      have h2 := PNat.mod_coe n m
      rw [nn']
      cases (n.1) % m with
      | zero =>
          split_ifs at h2
          · linarith
          · rw [←h2]
            simp
            exact h1
      | succ k =>
          split_ifs at h2
          · linarith
          · rw [←h2]
            simp
            exact h1

lemma nat_div_pnat_le (n q : ℕ) (d : ℕ+) : n / d ≤ q → n ≤ d * q + d := by
  intro h1
  have h2 : n = d * (n / d) + n % d := Eq.symm (Nat.div_add_mod n d)
  have h3 := nat_mod_pnat_le n d
  have h5 : d * (n/d) ≤ d * q := by
    apply mul_le_mul
    apply le_refl
    assumption
    apply Nat.zero_le
    apply Nat.zero_le
  linarith

section

variable (e f : ℕ+)
variable (i : ℕ)

def setI : Set ℕ :=
  {n : ℕ |
  n % e ≠ e - 1
  ∧ n % f ≠ f - 1
  ∧ n / e + n / f = i }

def setII : Set ℕ :=
  {n : ℕ |
  n % e = e - 1
  ∧ n % f = f - 1
  ∧ n / e + n / f + 1 = i }

lemma Nat_le_add_right (a b : ℕ) : a ≤ a + b := by
  linarith

lemma setI_finite : Set.Finite (setI e f i) := by
  have setI_bdd : ∃ k : ℕ, ∀ n ∈ setI e f i, n ≤ k := by
    exists e*i+e
    intro n
    dsimp [setI]
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    have h4 : n/e ≤ i := by
      have h5 : n / e ≤ n/e+n/f := by
        apply Nat_le_add_right
      linarith
    have h6 := nat_div_pnat_le n i e
    exact h6 h4
  apply finite_of_bounded_of_Nat
  assumption

noncomputable def finsetI : Finset ℕ := Set.Finite.toFinset (setI_finite e f i)

noncomputable def cardI : ℕ := (finsetI e f i).card

noncomputable def h : ℕ := (cardI e f i)

end

section

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
end
