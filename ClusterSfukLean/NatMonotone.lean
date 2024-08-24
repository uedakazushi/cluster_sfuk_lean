import Mathlib
-- set_option linter.unusedVariables false

noncomputable def nat_min'
  (s : Set ℕ)
  (h : s.Nonempty)
  :
  ℕ
  :=
  WellFounded.min Nat.lt.isWellOrder.3.wf s h

def nat_interval (a b : ℕ) : Finset ℕ :=
  Finset.range (b + 1) \ Finset.range a

theorem nat_interval_card : (nat_interval a b).card =
  b + 1 - a := by
  cases Decidable.em (b ≥ a) with
  |inl h =>
    simp [nat_interval]
    rw [Finset.card_sdiff]
    rw [Finset.card_range]
    rw [Finset.card_range]
    simp
    linarith
  | inr h =>
    simp [nat_interval]
    have h1 : b + 1 ≤ a := by
      linarith
    -- have h2 : Finset.range (b+1) ⊆ Finset.range a := by
    --   rw [Finset.subset_iff]
    --   intro x
    --   intro h3
    --   rw [Finset.mem_range] at h3
    --   rw [Finset.mem_range]
    --   linarith
    -- have h4 : Finset.range (b+1) \ Finset.range a = ∅ := by
    --   rw [Finset.sdiff_eq_empty_iff_subset]
    --   exact h2
    aesop

lemma nat_interval_mem (a b c : ℕ) : b ∈ nat_interval a c ↔ a ≤ b ∧ b ≤ c := by
  rw [nat_interval]
  by_cases h : a ≤ c
  {
    rw [Finset.mem_sdiff]
    rw [Finset.mem_range]
    apply Iff.intro
    { intro h1
      -- have h11 := h1.1
      have h12 := h1.2
      rw [Finset.mem_range] at h12
      have h12' := Nat.le_of_not_gt h12
      apply And.intro
      { exact h12' }
      { linarith }
    }
    { intro h1
      -- have h11 := h1.1
      -- have h12 := h1.2
      apply And.intro
      { linarith }
      { rw [Finset.mem_range]
        apply Nat.not_lt_of_ge
        linarith }
    }
  }
  {
    -- have h' := Nat.gt_of_not_le h
    apply Iff.intro
    { intro h1
      exfalso
      simp at h1
      linarith
    }
    { intro h1
      -- have h11 := h1.1
      -- have h12 := h1.2
      exfalso
      linarith
    }
  }

def IsInterval (S : Set ℕ) : Prop := ∀ a b c : ℕ, a ∈ S → c ∈ S → a ≤ b → b ≤ c → b ∈ S

lemma nonempty_interval_range (S : Finset ℕ) (nonempty : S.Nonempty) (h : IsInterval S) : S = nat_interval (S.min' nonempty) (S.max' nonempty) := by
  apply Finset.ext
  intro a
  apply Iff.intro
  { intro a_in_S
    -- have h1 : (S.min' nonempty) ∈ S := by
    --   apply Finset.min'_mem
    -- have h2 : (S.max' nonempty) ∈ S := by
    --   apply Finset.max'_mem
    have h3 : (S.min' nonempty) ≤ a := by
      apply Finset.min'_le
      assumption
    have h4 : a ≤ (S.max' nonempty) := by
      apply Finset.le_max'
      assumption
    rw [nat_interval_mem]
    apply And.intro
    { exact h3 }
    { exact h4 }
  }
  { intro a_in_interval
    rw [nat_interval_mem] at a_in_interval
    have h1 := a_in_interval.1
    have h2 := a_in_interval.2
    rw [IsInterval] at h
    have h3 := h (S.min' nonempty) a (S.max' nonempty) (Finset.min'_mem S nonempty) (Finset.max'_mem S nonempty) h1 h2
    exact h3
  }

lemma preimage_of_monotone_isInterval (f : ℕ → ℕ) (h : Monotone f) (i : ℕ) : IsInterval ((f : ℕ → ℕ) ⁻¹' (Set.singleton i)) := by
  intro a b c a_in_f_inv c_in_f_inv a_le_b b_le_c
  have f_a_i : f a = i := by
    exact a_in_f_inv
  have f_c_i : f c = i := by
    exact c_in_f_inv
  have f_a_le_f_b : f a ≤ f b := by
    apply h
    assumption
  have f_b_le_f_c : f b ≤ f c := by
    apply h
    assumption
  have f_b_i : f b = i := by
    apply Nat.le_antisymm
    linarith
    linarith
  exact f_b_i

def IsBounded (s : Set ℕ) := ∃ k : ℕ, ∀ x ∈ s, x ≤ k

def IsBoundedFun (f : ℕ → ℕ) := ∃ k : ℕ, ∀ x : ℕ, f x ≤ k

def IsUnboundedFun (f : ℕ → ℕ) := ∀ k : ℕ, ∃ x : ℕ, k < f x

lemma not_bounded_unbounded (f : ℕ → ℕ) : IsBoundedFun f → ¬ IsUnboundedFun f := by
  intro h1
  rw [IsBoundedFun] at h1
  rw [IsUnboundedFun]
  push_neg
  assumption

lemma finite_of_bounded_of_Nat (s: Set ℕ) :
  IsBounded s → s.Finite := by
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

lemma fib_monotone_ubd_fun_bdd
  (f : ℕ → ℕ)
  (monotone : Monotone f)
  (ubd : IsUnboundedFun f)
  :
  ∀ j : ℕ, IsBounded (f ⁻¹' { j }) := by
    intro j
    rw [IsBounded]
    cases ubd (j+1) with
    | intro k hk =>
      exists k
      intro x
      intro h1
      simp at h1
      rw [←h1] at hk
      rw [Monotone] at monotone
      by_contra h3
      have h4 := le_of_not_ge h3
      have h5 := monotone h4
      linarith

lemma monotone_add
  (f g : ℕ → ℕ)
  (monotone_f : Monotone f)
  (monotone_g : Monotone g)
  :
  Monotone (f + g) := by
    intro a b h
    simp
    apply Nat.add_le_add
    apply monotone_f
    assumption
    apply monotone_g
    assumption

lemma unbounded_fun_add
  (f g : ℕ → ℕ)
  (ubd_f_or_g : IsUnboundedFun f ∨ IsUnboundedFun g)
  :
  IsUnboundedFun (f + g) := by
    intro k
    cases ubd_f_or_g with
    | inl ubd_f =>
      rw [IsUnboundedFun] at ubd_f
      have h := ubd_f k
      simp
      match h with
      | ⟨ x, h1 ⟩ =>
        exists x
        linarith
    | inr ubd_g =>
      rw [IsUnboundedFun] at ubd_g
      have h := ubd_g k
      simp
      match h with
      | ⟨ x, h1 ⟩ =>
        exists x
        linarith

def IsMinIn (m : ℕ) (s : Set ℕ) := m ∈ s ∧ ∀ x ∈ s, m ≤ x
