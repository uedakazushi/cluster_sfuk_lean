import Mathlib
import ClusterSfukLean.NatMonotone

def MonotoneOneLipschitz (f : ℕ → ℕ) := Monotone f ∧ ∀ n : ℕ, f (n + 1) ≤ (f n) + 1

def MonotoneTwoLipschitz (f : ℕ → ℕ) := Monotone f ∧ ∀ n : ℕ, f (n + 1) ≤ (f n) + 2

theorem skip
  (f : ℕ → ℕ)
  (mtl : MonotoneTwoLipschitz f)
  (ubd : IsUnboundedFun f)
  (f_zero : f 0 = 0)
  (i : ℕ)
  (emp1 : f ⁻¹' { i } = ∅)
  (emp2 : f ⁻¹' { i+1 } = ∅)
  : False
  := by
  induction i with
  | zero =>
    have h1 : 0 ∈ f ⁻¹' {0} := by
      simp
      exact f_zero
    rw [emp1] at h1
    simp at h1
  | succ i ih =>
    have h1 := Classical.em (f ⁻¹' {i} = ∅)
    cases h1 with
    | inl h1 =>
      have h2 := ih h1
      exact h2 emp1
    | inr h1 =>
      set s := f ⁻¹' {i} with def_s
      have nonemp_s : s.Nonempty := by
        push_neg at h1
        exact h1
      have bdd_s :=
        fib_monotone_ubd_fun_bdd f mtl.1 ubd i
      rw [← def_s] at bdd_s
      have s_finite := finite_of_bounded_of_Nat s bdd_s
      set finset_s := s_finite.toFinset with def_finset_s
      have finsets_nonemp : finset_s.Nonempty := by
        aesop
      set s_max' := finset_s.max' finsets_nonemp with def_s_max'
      have s_max'_mem := Finset.max'_mem _ finsets_nonemp
      have s_le_max' := Finset.le_max' finset_s
      rw [← def_s_max'] at s_max'_mem
      have h2 : ∀ x ∈ finset_s, f x = i := by
        intro x
        intro h3
        rw [def_finset_s] at h3
        rw [Set.Finite.toFinset] at h3
        simp at h3
        rw [def_s] at h3
        simp at h3
        exact h3
      have h3 := h2 s_max' s_max'_mem
      have h4 := mtl.2 s_max'
      rw [h3] at h4
      have h5 : s_max' ≤ s_max'+1 := by
        linarith
      have h6 := mtl.1 h5
      rw [h3] at h6
      have h7 : f (s_max'+1) ≠ i := by
        intro h7
        have h8 : s_max' + 1 ∈ s := by
          rw [def_s]
          simp
          exact h7
        have h9 : s_max' + 1 ∈ finset_s := by
          rw [def_finset_s]
          simp
          exact h8
        have h10 := s_le_max' (s_max'+1) h9
        linarith
      have h8 : f (s_max'+1) ≠ i+1 := by
        intro h8
        have h9 : s_max' + 1 ∈ f ⁻¹' {i+1} := by
          exact h8
        rw [emp1] at h9
        simp at h9
      have h9 : f (s_max'+1) = i+2 := by
        set y := f (s_max'+1)
        by_contra h10
        have h11 := Nat.le_iff_lt_or_eq.mp h6
        cases h11 with
        | inl h11 =>
          have h12 := Nat.le_iff_lt_or_eq.mp h11
          cases h12 with
          | inl h12 =>
            have h13 : y = i + 2 := by
              linarith
            contradiction
          | inr h12 =>
            simp at h12
            simp at h8
            apply h8
            rw [h12]
        | inr h11 =>
          apply h7
          rw [h11]
      rw [Set.preimage] at emp2
      simp at emp2
      have h10 : {x | f x = i + 2} ≠ ∅ := by
        simp
        push_neg
        exists s_max' + 1
      contradiction

theorem le_add_one_le_add_one_le_add_two (a b c d : ℕ) (b_le_succ_a : b ≤ a + 1) (d_le_succ_c : d ≤ c + 1) (eq : b + d = a + c + 2) : b = a + 1 ∧ d = c + 1 := by
  apply And.intro
  { linarith }
  { linarith }

theorem OneLipschitz_add
  (f g : ℕ → ℕ)
  (f_lip : MonotoneOneLipschitz f)
  (g_lip : MonotoneOneLipschitz g)
  (n : ℕ)
  (h : (f+g) (n+1) = ((f+g) n) + 2)
  :
  (f (n+1) = (f n) + 1)
  ∧
  (g (n+1) = (g n) + 1)
  := by
    have h1 := f_lip.2 n
    have h2 := g_lip.2 n
    exact le_add_one_le_add_one_le_add_two (f n) (f (n+1)) (g n) (g (n+1)) h1 h2 h
