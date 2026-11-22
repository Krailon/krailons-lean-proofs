module

import Mathlib.Data.Nat.Notation
import KrailonsLeanProofs.NaturalNumberGame4.TutorialWorld
import KrailonsLeanProofs.NaturalNumberGame4.AdditionWorld

namespace NaturalNumberGame4

open Nat

public theorem mul_zero (a : ℕ) : a * 0 = 0 := by
  rfl

public theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]    

public theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [mul_zero]
  | succ d hd =>
    rw [mul_succ, add_zero, hd]

public theorem mul_succ (a b : ℕ) : a * succ b = a * b + a := by
  rfl

public theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero, add_zero]
  | succ d hd =>
    rw [add_succ]
    rw [mul_succ a d]
    rw [mul_succ]
    rw [hd]
    rw [add_succ]
    rw [add_assoc]
    rw [add_zero]
    rw [add_succ]
    rw [add_assoc]
    rw [add_comm a d]

public theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction a with
  | zero =>
    rw [zero_mul, zero_mul, zero_mul, zero_add]
  | succ d hd =>
    rw [succ_mul, succ_mul, succ_mul, hd]
    rw [add_comm (d * b) b]
    rw [add_right_comm b (d * b) (d * c + c)]
    rw [add_comm b (d * c + c)]
    rw [add_right_comm (d * c + c) b (d * b)]
    rw [add_right_comm (d * c) c (d * b)]
    rw [add_comm (d * c) (d * b)]
    rw [add_comm (d * b + d * c) c]
    rw [add_right_comm c (d * b + d * c) b]
    rw [add_comm c b]
    rw [add_comm (b + c) (d * b + d * c)]

end NaturalNumberGame4
