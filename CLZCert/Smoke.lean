import Mathlib

-- smoke: the toolchain resolves, Mathlib oleans are shared, decide over Rat works
example : (36 : Nat) * 10^36 < 4 * 10^37 := by decide
example : (221 : ℚ) / 10^6 < 3 / 10000 := by norm_num
