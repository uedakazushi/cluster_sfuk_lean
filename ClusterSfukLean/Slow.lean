import Mathlib

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
