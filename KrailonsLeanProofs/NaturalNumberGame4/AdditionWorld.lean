module

import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Nat.Notation
import KrailonsLeanProofs.NaturalNumberGame4.TutorialWorld

namespace NaturalNumberGame4

open Nat

public theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    rw [add_zero]
  | succ d hd =>
    rw [add_succ, hd]

public theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
    rw [add_zero, add_zero]
  | succ d hd =>
    rw [add_succ, add_succ]
    rw [hd]

public theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero =>
    rw [add_zero, zero_add]
  | succ d hd =>
    rw [add_succ, succ_add, hd]

public theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_add, zero_add]
  | succ d hd =>
    rw [succ_add, succ_add, succ_add, hd]

public theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_assoc, add_comm b c]

end NaturalNumberGame4
