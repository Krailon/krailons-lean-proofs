module

import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Nat.Notation

namespace NaturalNumberGame4

open Nat

public theorem example1 (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

public theorem example2 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

public theorem one_eq_succ_zero : (1 : ℕ) = succ 0 := by
  rfl

public theorem two_eq_succ_one : (2 : ℕ) = succ 1 := by
  rfl

public theorem example3 : 2 = succ (succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

public theorem example4 : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

public theorem add_zero (a : ℕ) : a + 0 = a := by
  rfl

public theorem example5 (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero, add_zero]

public theorem example6 (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c, add_zero b]

public theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]

public theorem three_eq_succ_two : 3 = succ 2 := by
  rfl

public theorem four_eq_succ_three : 4 = succ 3 := by
  rfl

public theorem two_plus_two_eq_four : (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ, ← succ_eq_add_one, ← three_eq_succ_two, ← four_eq_succ_three]

end NaturalNumberGame4
