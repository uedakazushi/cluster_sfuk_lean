import ClusterSfukLean.CaseII1

lemma setII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : (setII (e*l) (f*l) i) =
    (
    ite ((e.1+f.1) ∣ (i+1))
    (Set.singleton (e*f*l*(i+1)/(e+f) - 1 : ℕ))
    ∅
    )
  := by
  by_cases dvd: ((e.1+f.1) ∣ (i+1))
  case pos =>
    apply Eq.symm
    rw [ite_eq_iff]
    apply Or.inl
    apply And.intro
    { exact dvd }
    {
      have h1 := setII_singleton e f l i e_ge_2 f_ge_2 dvd
      exact h1.symm
    }
  case neg =>
    apply Eq.symm
    rw [ite_eq_iff]
    have h1 := setII_empty_if_not_dvd e f l i e_ge_2 f_ge_2 coprime dvd
    apply Or.inr
    apply And.intro
    exact dvd
    exact h1.symm

example : Nat.card (Set.singleton 1) = 1 := by
  simp

lemma singleton_card (n : ℕ) : (Set.singleton n).toFinset.card = 1 := by
  have := Set.card_singleton n
  have := Set.toFinset_card (Set.singleton n)
  aesop

lemma cardII_dichotomy
  (e f l: ℕ+)
  (i: ℕ)
  (e_ge_2 : e ≥ 2)
  (f_ge_2 : f ≥ 2)
  (coprime : Nat.Coprime e f)
  : cardII (e*l) (f*l) i = ite ((e.1+f.1) ∣ (i+1)) 1 0
  := by
  by_cases dvd: ((e.1+f.1) ∣ (i+1))
  case pos =>
    apply Eq.symm
    rw [ite_eq_iff]
    apply Or.inl
    apply And.intro
    exact dvd
    rw [cardII]
    rw [finsetII]
    have h1 := setII_finite (e*l) (f*l) i
    have h2 := Set.Finite.fintype h1
    have := Set.Finite.toFinset_eq_toFinset h1
    rw [Set.Finite.toFinset_eq_toFinset]
    have h4 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    have h5 : setII (e*l) (f*l) i = Set.singleton (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1) := by
      conv =>
      lhs
      rw [h4]
      split
      {
        case isTrue h5; rfl
      }
      {
        case isFalse; rfl
      }
    have h6 : Set.toFinset (setII (e * l) (f * l) i) = Set.toFinset (Set.singleton (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1)) := by
      conv =>
      lhs
      congr
      aesop
    rw [h6]
    have h7 := singleton_card (e.1*f.1*l.1*(i+1)/(e.1+f.1) - 1)
    rw [h7]
  case neg =>
    split
    case isTrue h
    have := dvd h
    contradiction
    case isFalse h
    have h3 := setII_dichotomy e f l i e_ge_2 f_ge_2 coprime
    have := Eq.symm h3
    rw [cardII]
    rw [finsetII]
    have h4 := setII_finite (e*l) (f*l) i
    have h5 := Set.Finite.fintype h4
    have := Set.Finite.toFinset_eq_toFinset h4
    rw [Set.Finite.toFinset_eq_toFinset]
    have h7 : setII (e*l) (f*l) i = ∅ := by
      conv =>
      lhs
      rw [h3]
      split
      {
        case isTrue h5; contradiction
      }
      {
        case isFalse h5; rfl
      }
    have h8 : Set.toFinset (setII (e * l) (f * l) i) = Set.toFinset ∅ := by
      conv =>
      lhs
      congr
      aesop
    rw [h8]
    simp
