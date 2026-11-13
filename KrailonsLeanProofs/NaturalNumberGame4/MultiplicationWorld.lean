module

import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Nat.Notation
import KrailonsLeanProofs.NaturalNumberGame4.TutorialWorld
import KrailonsLeanProofs.NaturalNumberGame4.AdditionWorld

namespace NaturalNumberGame4

open Nat

theorem mul_zero (a : ℕ) : a * 0 = 0 := by
  rfl

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]    

end NaturalNumberGame4
