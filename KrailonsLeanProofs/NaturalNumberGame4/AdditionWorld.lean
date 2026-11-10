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

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with d hd
  rw [add_zero, add_zero]
  nth_rewrite 2 [add_succ]
  rw [add_succ]
  rw [hd]

end NaturalNumberGame4
