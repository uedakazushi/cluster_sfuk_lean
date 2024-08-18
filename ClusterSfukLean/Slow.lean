import Mathlib

def IsSlow (f : ℕ → ℕ) := ∀ k : ℕ, f (k + 1) ≤ (f k) + 1

lemma slow_sublemma (a b c d : ℕ) (b_le_succ_a : b ≤ a + 1) (d_le_succ_c : d ≤ c + 1) (eq : b + d = a + c + 2) : b = a + 1 ∧ d = c + 1 := by
  apply And.intro
  { linarith }
  { linarith }

lemma slow_lemma
  (f g : ℕ → ℕ)
  (f_slow : IsSlow f)
  (g_slow : IsSlow g)
  (x : ℕ)
  (h : (f+g) (x+1) = ((f+g) x) + 2)
  :
  (f (x+1) = (f x) + 1)
  ∧
  (g (x+1) = (g x) + 1)
  := by
    have h1 := f_slow x
    have h2 := g_slow x
    exact slow_sublemma (f x) (f (x+1)) (g x) (g (x+1)) h1 h2 h
