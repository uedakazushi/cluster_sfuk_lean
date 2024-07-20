import Mathlib

lemma finite_test (k:Nat) : Set.Finite {n : Nat | n ≤ k } := by
  exact Set.finite_le_nat k

#check Set.Finite.subset

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

-- example (m: ℕ) (n d : ℕ+) : n / d ≤ m → n ≤ d * m + d := by
--   intro h1
--   #check (↑d : Nat)
--   have h2 : n = d * ((n:Nat) / d) + n % d := Eq.symm (Nat.div_add_mod n d)
--   have h3 := Nat.mul_le_mul_left d h1
--   have h4 := Nat.add_le_add_right h3 (n % d)
--   have h5 : n ≤ d * m + ↑n % d := by linarith
--   have h6 := (PNat.mod_le n d).2
--   have h7 : n ≤ d -> (n:Nat) ≤ (d:Nat) := by
--     intro h
--     exact h
--   have h8 : (n: Nat) % d = (n.mod d : Nat) := by
--     induction n
--     ·

--   have h8 : (n: Nat) % (↑d) ≤ d :=



--     _ ≤ d * m + d := by
--       apply Nat.add_le_add_left
--       exact PNat.mod_le n d


    -- ... ≤ i * m + m : by
    --   intro h
    --   have h1 : x / m * m ≤ i * m := Nat.mul_le_mul_left m h
    --   have h2 : x % m ≤ m := Nat.mod_le x m
    --   linarith


-- lemma setI_finite : Set.Finite (setI e f i) := by
--   have setI_bdd : (setI e f i) ⊆ {n : ℕ | n ≤ e * i + e} := by
--     rw [Set.subset_def]
--     intro x
--     intro h
--     simp [setI] at h
--     have h1 : x / ↑e + x / ↑f = i := h.right.right
--     simp
--     have h2 : x / ↑e ≤ i := by
--       have h3 := Nat_le_add_right (x / ↑e) (x / ↑f)
--       rw [h1] at h3
--       assumption

-- lemma setII_finite : Set.Finite (setII e f i) := by
--   sorry

-- noncomputable def finsetI : Finset ℕ := Set.Finite.toFinset (setI_finite e f i)

-- noncomputable def finsetII : Finset ℕ := Set.Finite.toFinset (setII_finite e f i)

-- noncomputable def cardI : ℕ := (finsetI e f i).card

-- noncomputable def cardII : ℕ := (finsetII e f i).card

-- noncomputable def h : ℕ := (cardI e f i) + (cardII e f i)

end

section

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

-- theorem main :
--   h (e * l) (f * l) i = l * (h e f i) + l - 1
--   := by
--   sorry
-- end
