import Mathlib

section preliminaries

def nat_interval (a b : ℕ) : Finset ℕ :=
  if b ≥ a then Finset.range (b + 1) \ Finset.range a else ∅

theorem nat_interval_card : (nat_interval a b).card =
  if b ≥ a then b + 1 - a else 0 := by
  cases Decidable.em (b ≥ a) with
  |inl h =>
    simp [nat_interval]
    rw [if_pos h]
    rw [Finset.card_sdiff]
    rw [Finset.card_range]
    rw [Finset.card_range]
    rw [if_pos h]
    simp
    linarith
  | inr h =>
    simp [nat_interval]
    rw [if_neg h]
    rw [Finset.card_empty]
    rw [if_neg h]

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

lemma nat_div_pnat_le (n q : ℕ) (d : ℕ+) : n / d ≤ q → n ≤ d * q + d := by
  intro h1
  have h2 : n = d * (n / d) + n % d := Eq.symm (Nat.div_add_mod n d)
  have h3 := Nat.mod_lt n d.2
  have h4 : n % d ≤ d := Nat.le_of_lt h3
  have h5 : d * (n/d) ≤ d * q := by
    apply mul_le_mul
    apply le_refl
    assumption
    apply Nat.zero_le
    apply Nat.zero_le
  linarith

lemma finset_min_eq (s : Finset ℕ) (m : ℕ) (m_in_s : m ∈ s) (minimality : ∀ x ∈ s, x ≥ m) : s.min = m := by
  have h1 := s.min_eq_inf_withTop
  simp [Finset.inf] at h1
  have h2 : s.min ≤ m := by
    apply Finset.min_le
    assumption
  have h3 : m ≤ s.min := by
    simp
    apply minimality
  exact le_antisymm h2 h3

lemma finset_min_min' (s : Finset ℕ) (h : s.Nonempty) : s.min = s.min' h := by
  apply finset_min_eq
  apply Finset.min'_mem
  intro x
  intro h1
  apply Finset.min'_le
  assumption

end preliminaries

section quotient_and_remainder

lemma quot_rem : ∀ q n r: ℕ, ∀ d : ℕ+, (n = q * d + r ∧ 0 ≤ r ∧ r < d)
 → (q = n / d ∧ r = n % d) := by
  intro q
  induction q with
  |zero =>
    intro n r d h
    simp at h
    apply And.intro
    · rw [h.1]
      have h2 : (¬ ↑d ≤ r) := by
        intro h'
        have h'' := le_antisymm h'
        have h''' : r ≤ ↑d := by
          linarith
        linarith
      have h3 := Nat.div_eq r d
      simp [h2] at h3
      simp [h3]
    · rw [h.1]
      have h3 := Nat.mod_eq r d
      have h2 : (¬ ↑d ≤ r) := by
        intro h'
        have h'' := le_antisymm h'
        have h''' : r ≤ ↑d := by
          linarith
        linarith
      have d_pos : d > (0:Nat) := d.2
      simp [d_pos] at h3
      simp [h2] at h3
      exact Eq.symm h3
  |succ q ih =>
    intro n r d h
    apply And.intro
    · have h1 := h.1
      have h2 := (h.2).1
      have h3 := (h.2).2
      have h4 := Nat.div_eq n d
      have d_pos : d > (0:Nat) := d.2
      have h5 : ↑ d ≤ n := by
        have h1' : n = d + q * d + r := by
          simp [h1]
          rw [Nat.add_mul]
          rw [add_comm]
          simp
        have h1'' : n ≥ d + q * d := by
          linarith
        have h1''' : d + q * d ≥ d := by
          have h1'''' : q * d ≥ 0 := by
            apply mul_nonneg
            linarith
            linarith
          linarith
        linarith
      simp [d_pos] at h4
      simp [h5] at h4
      have ih1 := ih (n-d) r d
      simp [h1] at ih1
      have h1' : (q + 1) * ↑d + r - ↑d = q * ↑d + r := by
        ring_nf
        nth_rw 1 [←add_comm]
        nth_rw 1 [←add_assoc]
        simp
        rw [add_comm]
      have h6 := Nat.div_eq n d
      simp [d_pos] at h6
      simp [h5] at h6
      have ih1' := ih1 h1'
      have ih1'' := (ih1' h3).1
      rw [h6]
      have h1' : (q + 1) * ↑d + r - ↑d = n - ↑ d := by
        rw [h1]
      rw [h1'] at ih1''
      rw [ih1'']
    · have h1 := h.1
      have h2 := (h.2).1
      have h3 := (h.2).2
      have h4 := Nat.mod_eq n d
      have d_pos : d > (0:Nat) := d.2
      have h5 : ↑ d ≤ n := by
        have h1' : n = d + q * d + r := by
          simp [h1]
          rw [Nat.add_mul]
          rw [add_comm]
          simp
        have h1'' : n ≥ d + q * d := by
          linarith
        have h1''' : d + q * d ≥ d := by
          have h1'''' : q * d ≥ 0 := by
            apply mul_nonneg
            linarith
            linarith
          linarith
        linarith
      simp [d_pos] at h4
      simp [h5] at h4
      have ih1 := ih (n-d) r d
      simp [h1] at ih1
      have h1' : (q + 1) * ↑d + r - ↑d = q * ↑d + r := by
        ring_nf
        nth_rw 1 [←add_comm]
        nth_rw 1 [←add_assoc]
        simp
        rw [add_comm]
      have h6 := Nat.mod_eq n d
      simp [d_pos] at h6
      simp [h5] at h6
      have ih1' := ih1 h1'
      have ih1'' := (ih1' h3).2
      rw [h6]
      have h1' : (q + 1) * ↑d + r - ↑d = n - ↑ d := by
        rw [h1]
      rw [h1'] at ih1''
      rw [ih1'']

end quotient_and_remainder

section main_def

variable (e f: ℕ+)
variable (i : ℕ)
variable (e_ge_2 : (e:Nat) ≥ 2)
variable (f_ge_2 : (f:Nat) ≥ 2)

def setI : Set ℕ :=
  {b : ℕ |
  b % e ≠ e - 1
  ∧ b % f ≠ f - 1
  ∧ b / e + b / f = i }

def setI' : Set ℕ :=
  {b : ℕ |
  b % e ≠ e - 1
  ∧ b % f ≠ f - 1
  ∧ b / e + b / f ≥ i }

lemma setI'_non_empty : (setI' e f i).Nonempty := by
  exists e*f*i
  simp [setI']
  apply And.intro
  rw [Nat.mul_assoc]
  rw [Nat.mul_mod_right]
  intro h
  have e_le_1 := e.one_le
  have h1 := @Nat.sub_eq_iff_eq_add 1 e 0 e_le_1
  simp at h1
  have h2 := Eq.symm h
  have h3 := h1.1 h2
  have h5 : (e:Nat) = 1 := by
    exact congr_arg (PNat.val : ℕ+ → ℕ) h3
  linarith
  apply And.intro
  rw [Nat.mul_assoc]
  rw [Nat.mul_comm]
  rw [Nat.mul_assoc]
  rw [Nat.mul_mod_right]
  intro h
  have f_le_1 := f.one_le
  have h1 := @Nat.sub_eq_iff_eq_add 1 f 0 f_le_1
  simp at h1
  have h2 := Eq.symm h
  have h3 := h1.1 h2
  have h5 : (f:Nat) = 1 := by
    exact congr_arg (PNat.val : ℕ+ → ℕ) h3
  linarith
  rw [Nat.mul_assoc]
  rw [Nat.mul_div_right]
  have h1 : i ≤ (f:Nat) * i := by
    apply Nat.le_mul_of_pos_left
    exact f.2
  have h2 : ↑f * i ≤ ↑f * i + ↑e * (↑f * i) / ↑f :=
    Nat.le_add_right (↑f * i) (↑e * (↑f * i) / ↑f)
  exact le_trans h1 h2
  exact e.property

noncomputable def min_setI' : ℕ :=
  WellFounded.min
    Nat.lt.isWellOrder.3.wf
    (setI' e f i)
    (setI'_non_empty e f i e_ge_2 f_ge_2)

def setI'' : Set ℕ :=
  {b : ℕ |
  b % e ≠ e - 1
  ∧ b % f ≠ f - 1
  ∧ b / e + b / f ≤ i }

lemma ge_2_1_le (n : ℕ) : n ≥ 2 → 1 ≤ n := by
  intro h
  linarith

def setII : Set ℕ :=
  {n : ℕ |
  n % e = e - 1
  ∧ n % f = f - 1
  ∧ n / e + n / f + 1 = i }

def setIII : Set ℂ :=
  {ξ : ℂ |
  ξ ≠ 1
  ∧ ξ^(e:ℕ) = 1
  ∧ ξ^(f:ℕ) = 1 }

lemma Nat_le_add_right (a b : ℕ) : a ≤ a + b := by
  linarith

lemma setI_finite : (setI e f i).Finite := by
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

lemma setI''_finite : (setI'' e f i).Finite := by
  have setII'_bdd : ∃ k : ℕ, ∀ n ∈ setI'' e f i, n ≤ k := by
    exists e*f*i+e
    intro n
    dsimp [setI'']
    intro h
    cases h with
    | intro h1 h2 => cases h2 with
    | intro h2 h3 =>
    have h4 : n/e ≤ i := by
      have h5 : n / e ≤ n/e+n/f := by
        apply Nat_le_add_right
      linarith
    have h6 := nat_div_pnat_le n i e
    have h7 := h6 h4
    have h8 : e * i ≤ e * f * i := by
      have h9 : e * f * i = f * e * i := by
        simp
        apply Or.inl
        apply Nat.mul_comm e f
      rw [h9]
      rw [Nat.mul_assoc]
      apply Nat.le_mul_of_pos_left
      exact f.2
    linarith
  apply finite_of_bounded_of_Nat
  assumption

lemma setII_finite : (setII e f i).Finite := by
  sorry

lemma setIII_finite : (setIII e f).Finite := by
  sorry

noncomputable def finsetI : Finset ℕ :=
  (setI_finite e f i).toFinset

noncomputable def finsetI'' : Finset ℕ :=
  (setI''_finite e f i).toFinset

noncomputable def finsetII : Finset ℕ :=
  (setII_finite e f i).toFinset

noncomputable def finsetIII : Finset ℂ :=
  (setIII_finite e f).toFinset

noncomputable def cardI : ℕ := (finsetI e f i).card

noncomputable def cardII : ℕ := (finsetII e f i).card

noncomputable def cardIII : ℕ := (finsetIII e f).card

noncomputable def h : ℕ := (cardI e f i + (cardII e f i) * (cardIII e f))

lemma setI''_non_empty : (setI'' e f i).Nonempty := by
  exists 0
  simp [setI'']
  apply And.intro
  intro h
  have h1 := Iff.mp (Nat.sub_eq_iff_eq_add (ge_2_1_le (e:ℕ) e_ge_2)) (Eq.symm h)
  simp at h1
  rw [h1] at e_ge_2
  linarith
  intro h
  have h1 := Iff.mp (Nat.sub_eq_iff_eq_add (ge_2_1_le (f:ℕ) f_ge_2)) (Eq.symm h)
  simp at h1
  rw [h1] at f_ge_2
  linarith

lemma finsetI''_non_empty : (finsetI'' e f i).Nonempty := by
  exists 0
  simp [finsetI'']
  apply And.intro
  intro h
  have h1 := Iff.mp (Nat.sub_eq_iff_eq_add (ge_2_1_le (e:ℕ) e_ge_2)) (Eq.symm h)
  simp at h1
  rw [h1] at e_ge_2
  linarith
  apply And.intro
  intro h
  have h1 := Iff.mp (Nat.sub_eq_iff_eq_add (ge_2_1_le (f:ℕ) f_ge_2)) (Eq.symm h)
  simp at h1
  rw [h1] at f_ge_2
  linarith
  have h2 : 0 / (e:Nat) = 0 := by
    simp
  rw [h2]
  have h3 : 0 / (f:Nat) = 0 := by
    simp
  rw [h3]
  linarith

noncomputable def b_max : ℕ := (finsetI'' e f i).max' (finsetI''_non_empty e f i e_ge_2 f_ge_2)

end main_def

section main_lemma

variable (e f l: ℕ+)
variable (i : ℕ)

lemma Imin_l (non_emp : (finsetI (e * l) (f * l) i).Nonempty) :
(finsetI (e * l) (f * l) i).min = (finsetI e f i).min * l := by
  have h1 := Classical.em (finsetI e f i).Nonempty
  cases h1 with
  |inl h =>
    let b_min := (finsetI e f i).min' h
    have h2 : b_min ∈ (finsetI e f i) := by
      apply Finset.min'_mem
    have h3 : ¬ (b_min % e = 0 ∨ b_min % f = 0) → False := by
      #check finsetI
      have h4 : ∃ b ∈ (finsetI e f i), b < b_min := by
        sorry
      -- match h4 with
      -- |⟨ i, h5, h6 ⟩ =>
      let ⟨ b, h5, h6 ⟩ := h4
      exfalso
      have h7 := Finset.min'_le (finsetI e f i) b h5
      have h8 := not_le_of_lt h6
      linarith
    have h3' : b_min % e = 0 ∨ b_min % f = 0 := by
      have h10 := em (b_min % e = 0 ∨ b_min % f = 0)
      cases h10 with
      |inl h11 =>
        exact h11
      |inr h12 =>
        exfalso
        exact h3 h12
    have h13 : b_min * l ∈ (finsetI (e * l) (f * l) i) := by
      sorry
    have h14 : ∀ x ∈ (finsetI (e * l) (f * l) i), b_min * l ≤ x := by
      sorry
    have h15 := finset_min_eq (finsetI (e * l) (f * l) i) (b_min * l) h13 h14
    rw [h15]
    have h16 := finset_min_min' (finsetI e f i) h
    rw [h16]
    rfl
  |inr h =>
    have h2 : (finsetI e f i).min = 0 := by
      sorry
    have h3 : (finsetI (e * l) (f * l) i).min = 0 := by
      sorry
    rw [h2]
    rw [h3]
    sorry

section main_theorem

variable (e f l: ℕ+)
variable (i : ℕ)
variable (e_coprime_f : Nat.Coprime e f)

theorem main :
  h (e * l) (f * l) i = l * (h e f i) + l - 1
  := by
  sorry
end main_theorem
