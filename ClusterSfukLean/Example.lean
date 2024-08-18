import ClusterSfukLean.Main
set_option linter.unusedVariables false

example : PNat.mod 3 3 = 3 := rfl

example : (3:ℕ) % (3:ℕ+) = 0 := rfl

example : (1:PNat) - (1:PNat) = 1 := rfl

#print setI

variable (f g : ℕ → ℕ)
variable (a : ℕ)

#check f+g
#check (f+g) a
