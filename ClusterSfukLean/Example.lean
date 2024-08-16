import ClusterSfukLean.Basic
set_option linter.unusedVariables false

example : PNat.mod 3 3 = 3 := rfl

example : (3:ℕ) % (3:ℕ+) = 0 := rfl

example : (1:PNat) - (1:PNat) = 1 := rfl
