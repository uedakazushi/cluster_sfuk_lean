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
  have fg_inv_i_bounded : IsBounded ((f+g) ⁻¹' { m : ℕ | m ≤ i } ) := by
    have h1 := monotone_unboundedFun_bounded (f+g) (Monotone.add f_monotone g_monotone) ubd i
    sorry
  sorry
