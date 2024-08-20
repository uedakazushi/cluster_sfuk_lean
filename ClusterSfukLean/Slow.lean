import Mathlib
import ClusterSfukLean.NatMonotone

def IsSlow (f : ℕ → ℕ) := ∀ n : ℕ, f (n + 1) ≤ (f n) + 1

lemma slow_sublemma (a b c d : ℕ) (b_le_succ_a : b ≤ a + 1) (d_le_succ_c : d ≤ c + 1) (eq : b + d = a + c + 2) : b = a + 1 ∧ d = c + 1 := by
  apply And.intro
  { linarith }
  { linarith }

lemma slow_lemma
  (f g : ℕ → ℕ)
  (f_slow : IsSlow f)
  (g_slow : IsSlow g)
  (n : ℕ)
  (h : (f+g) (n+1) = ((f+g) n) + 2)
  :
  (f (n+1) = (f n) + 1)
  ∧
  (g (n+1) = (g n) + 1)
  := by
    have h1 := f_slow n
    have h2 := g_slow n
    exact slow_sublemma (f n) (f (n+1)) (g n) (g (n+1)) h1 h2 h

lemma skip
  (f g : ℕ → ℕ)
  (f_slow : IsSlow f)
  (g_slow : IsSlow g)
  (f_monotone : Monotone f)
  (g_monotone : Monotone g)
  (i : ℕ)
  (i_pos : i > 0)
  (f_zero : f 0 = 0)
  (g_zero : g 0 = 0)
  (ubd : IsUnboundedFun (f+g) )
  (fg_inv_i_empty : (f+g) ⁻¹' (Set.singleton i) = ∅)
  :
  ( (f+g) ⁻¹' (Set.singleton (i-1)) ≠ ∅ )
  ∧
  ( (f+g) ⁻¹' (Set.singleton (i+1)) ≠ ∅ )
  := by
  have fg_inv_le_i_nonempty : (f+g) ⁻¹' {m : ℕ | m ≤ i} ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty]
    rw [Set.Nonempty]
    apply Exists.intro 0
    simp
    rw [f_zero]
    rw [g_zero]
    linarith
  have fg_inv_i_finite : Set.Finite ((f+g) ⁻¹' (Set.singleton i )) := by
    have h1 := monotone_unboundedFun_bounded (f+g) (Monotone.add f_monotone g_monotone) ubd i
    apply finite_of_bounded_of_Nat
    assumption
  set ff : {m : ℕ | m ≤ i} → Set ℕ := fun n => (f+g) ⁻¹' (Set.singleton n) with def_ff
  have inv_le_i_union :
  (f+g) ⁻¹' {m : ℕ | m ≤ i} = Set.iUnion ff := by
    rw [def_ff]
    rw [Set.iUnion]
    simp [Set.preimage]
    apply Set.ext
    intro x
    apply Iff.intro
    { intro h
      simp
      simp at h
      exists f x + g x
    }
    { intro h
      simp
      simp at h
      cases h with
      | intro a h1 =>
        simp at h1
        have h2 := h1.1
        have h3 := h1.2
        have h4 : f x + g x = a := by
          exact h3
        linarith
    }
  have le_i_finite : Finite {m : ℕ | m ≤ i} := by
    apply Set.finite_le_nat
  have inv_finite : ∀ (i : ↑{m | m ≤ i}), Finite ↑(ff i) := by
    intro n
    apply finite_of_bounded_of_Nat
    apply monotone_bounded
    apply Monotone.add
    apply f_monotone
    apply g_monotone
    rw [IsUnboundedFun] at ubd
    intro n'
    have ubd2 := ubd n'
    match ubd2 with
    | ⟨ k, hk ⟩ =>
      exists k
      linarith
  have hh := @Finite.Set.finite_iUnion ℕ {m : ℕ | m ≤ i} le_i_finite ff inv_finite
  set aux := Set.Finite.toFinset hh with def_m
  have m := aux.max'
  have fg_inv_le_i_finite : Set.Finite ((f+g) ⁻¹' {m : ℕ | m ≤ i}) := by
    sorry
  sorry
