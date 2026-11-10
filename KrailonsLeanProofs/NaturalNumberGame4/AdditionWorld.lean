module

import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Nat.Notation

namespace NaturalNumberGame4

open Nat

theorem add_zero (a : ℕ) : a + 0 = a := by
  rfl

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  rw [add_zero]
  rw [add_succ, hd]

end NaturalNumberGame4
