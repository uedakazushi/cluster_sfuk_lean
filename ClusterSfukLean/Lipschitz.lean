import Mathlib
import ClusterSfukLean.NatMonotone

def MonotoneOneLipschitz (f : ℕ → ℕ) := Monotone f ∧ ∀ n : ℕ, f (n + 1) ≤ (f n) + 1

def MonotoneTwoLipschitz (f : ℕ → ℕ) := Monotone f ∧ ∀ n : ℕ, f (n + 1) ≤ (f n) + 2

lemma skip
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








lemma le_add_one_le_add_one_le_add_two (a b c d : ℕ) (b_le_succ_a : b ≤ a + 1) (d_le_succ_c : d ≤ c + 1) (eq : b + d = a + c + 2) : b = a + 1 ∧ d = c + 1 := by
  apply And.intro
  { linarith }
  { linarith }

lemma OneLipschitz_add
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

-- lemma skip2
--   (f g : ℕ → ℕ)
--   (f_lip : MonotoneOneLipschitz f)
--   (g_lip : MonotoneOneLipschitz g)
--   (f_monotone : Monotone f)
--   (g_monotone : Monotone g)
--   (i : ℕ)
--   (i_pos : i > 0)
--   (f_zero : f 0 = 0)
--   (g_zero : g 0 = 0)
--   (ubd : IsUnboundedFun (f+g) )
--   (fg_inv_i_empty : (f+g) ⁻¹' (Set.singleton i) = ∅)
--   :
--   ( (f+g) ⁻¹' (Set.singleton (i-1)) ≠ ∅ )
--   ∧
--   ( (f+g) ⁻¹' (Set.singleton (i+1)) ≠ ∅ )
--   := by
--   set fg : ℕ → ℕ := f + g with def_fg
--   set fg_inv_le_i := fg ⁻¹' {m : ℕ | m ≤ i} with def_fg_inv_le_i
--   have fg_inv_le_i_nonempty : fg_inv_le_i ≠ ∅ := by
--     rw [← Set.nonempty_iff_ne_empty]
--     rw [Set.Nonempty]
--     apply Exists.intro 0
--     rw [def_fg_inv_le_i]
--     simp
--     rw [def_fg]
--     simp
--     rw [f_zero]
--     rw [g_zero]
--     linarith
--   have fg_inv_i_finite : Set.Finite (fg ⁻¹' (Set.singleton i )) := by
--     have h1 := monotone_unboundedFun_bounded fg (Monotone.add f_monotone g_monotone) ubd i
--     apply finite_of_bounded_of_Nat
--     assumption
--   set ff : {m : ℕ | m ≤ i} → Set ℕ := fun n => fg ⁻¹' (Set.singleton n) with def_ff
--   have inv_le_i_union :
--   fg_inv_le_i = Set.iUnion ff := by
--     rw [def_ff]
--     rw [Set.iUnion]
--     simp [Set.preimage]
--     apply Set.ext
--     intro x
--     apply Iff.intro
--     { intro h
--       simp
--       simp at h
--       exists f x + g x
--     }
--     { intro h
--       rw [def_fg_inv_le_i]
--       simp
--       simp at h
--       cases h with
--       | intro a h1 =>
--         simp at h1
--         have h2 := h1.1
--         have h3 := h1.2
--         have h4 : f x + g x = a := by
--           exact h3
--         rw [def_fg]
--         simp
--         linarith
--     }
--   have le_i_finite : Finite {m : ℕ | m ≤ i} := by
--     apply Set.finite_le_nat
--   have inv_finite : ∀ (i : ↑{m | m ≤ i}), Finite ↑(ff i) := by
--     intro n
--     apply finite_of_bounded_of_Nat
--     apply monotone_unboundedFun_bounded
--     apply Monotone.add
--     apply f_monotone
--     apply g_monotone
--     rw [IsUnboundedFun] at ubd
--     intro n'
--     have ubd2 := ubd n'
--     match ubd2 with
--     | ⟨ k, hk ⟩ =>
--       exists k

--   have hh := @Finite.Set.finite_iUnion ℕ {m : ℕ | m ≤ i} le_i_finite ff inv_finite
--   set aux := Set.Finite.toFinset hh with def_m
--   have m := aux.max'
--   have fg_inv_le_i_finite : Set.Finite fg_inv_le_i := by
--     rw [inv_le_i_union]
--     exact hh
--   set fg_inv_le_i_finset := Set.Finite.toFinset fg_inv_le_i_finite with def_fg_inv_le_i_finset
--   have fg_inv_le_i_nonempty : fg_inv_le_i_finset.Nonempty := by
--     have h1 := @Set.toFinset_nonempty _ _ fg_inv_le_i_finite.fintype
--     rw [def_fg_inv_le_i_finset]
--     simp
--     dsimp [fg_inv_le_i]
--     dsimp [Set.Nonempty]
--     exists 0
--     rw [def_fg]
--     simp
--     rw [f_zero,g_zero]
--     linarith
--   have fg_inv_le_i_max'_mem := Finset.max'_mem _ fg_inv_le_i_nonempty
--   have fg_inv_le_i_le_max' := Finset.le_max' fg_inv_le_i_finset
--   set fg_inv_le_i_max := fg_inv_le_i_finset.max' fg_inv_le_i_nonempty with def_fg_inv_le_i_max
--   have fg_ne_i : fg (fg_inv_le_i_max) = i-1 := by sorry
--   sorry
