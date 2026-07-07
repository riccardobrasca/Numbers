import Batteries.CodeAction

/-!

In this file we define our copy `MyNat` of the natural numbers. To check that we don't cheat
using results already proved in mathlib we don't import anything. (Note that even if `MyNat` is
defined here, the simple fact of, say, providing the `Semiring` instance allows to use a lot of
results in mathlib.)

-/

/-- Our copy of the natural numbers.-/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

#check MyNat.zero
namespace MyNat

#check zero

#check succ

#check succ zero

#check succ (succ zero)

variable (a b c : MyNat)

/-- The following is to activate the notation `(0 : MyNat)`.
Beware: if you just write `0`, sometimes Lean thinks you mean the "usual" natural number `0`. -/
instance : Zero MyNat := ⟨zero⟩

#check 0

#check (0 : MyNat)

theorem zero_def : zero = 0 := by
  sorry

def one : MyNat := succ 0

instance : One MyNat := ⟨one⟩

theorem one_def : one = 1 := by
  sorry

theorem one_eq_succ_zero : 1 = succ 0 := by
  sorry

/-- This is basically an axiom added by Lean when defining natural numbers (feel free to ask more
details if you want!) -/
theorem succ_ne_zero : succ a ≠ 0 := by
  sorry

theorem one_ne_zero : (1 : MyNat) ≠ 0 := by
  sorry

theorem zero_ne_one : (0 : MyNat) ≠ 1 := by
  sorry

/-- Addition on `MyNat`. -/
def add : MyNat → MyNat → MyNat
| a, 0 => a
| a, (succ b) => succ (add a b)

instance : Add MyNat where
  add := add

theorem add_zero : a + 0 = a := by
  sorry

theorem add_succ : a + succ b = succ (a + b):= by
  sorry

@[grind =] --Ignore all tags like this one, same for `@[simp]`
theorem succ_eq_add_one : succ a = a + 1 := by
  sorry

@[simp]
theorem add_one_ne_zero : a + 1 ≠ 0 := by
  sorry

theorem zero_add : 0 + a = a := by
  sorry

theorem succ_add : (succ a) + b = succ (a + b) := by
  sorry

theorem add_assoc : a + b + c = a + (b + c) := by
  sorry

theorem add_comm : a + b = b + a := by
  sorry

variable {a b} in
theorem eq_zero_of_add_eq_zero (h : a + b = 0) : a = 0 := by
  sorry

/-- Multiplication on `MyNat`. -/
def mul : MyNat → MyNat → MyNat
| _, 0 => 0
| a, (succ b) => mul a b + a

instance : Mul MyNat where
  mul := mul

theorem mul_zero : a * 0 = 0 := by
  sorry

theorem mul_succ : a * b.succ = a * b + a := by
  sorry

@[grind =]
theorem succ_mul : a.succ * b = a * b + b := by
  sorry

theorem zero_mul : 0 * a = 0 := by
  sorry

theorem left_distrib : a * (b + c) = a * b + a * c := by
  sorry

theorem mul_one : a * 1 = a := by
  sorry

theorem mul_comm : a * b = b * a := by
  sorry

theorem right_distrib : (a + b) * c = a * c + b * c := by
  sorry

theorem one_mul : 1 * a = a := by
  sorry

theorem mul_assoc : a * b * c = a * (b * c) := by
  sorry

variable {a b c} in
theorem add_left_cancel (h : a + b = a + c) : b = c := by
  sorry

theorem mul_ne_zero : ∀ {a b : MyNat}, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  sorry

/-- The predecessor function, with `pred 0 = 0`. -/
def pred : MyNat → MyNat
| zero => 0
| succ a => a

@[simp]
theorem pred_zero : pred 0 = 0 := by
  sorry

theorem pred_succ : pred (succ a) = a := by
  sorry

@[simp]
theorem add_one_pred : pred (a + 1) = a := by
  sorry

variable {a} in
theorem succ_pred (ha : a ≠ 0) : succ (pred a) = a := by
  sorry

variable {a} in
@[simp]
theorem pred_add_one (ha : a ≠ 0) : (pred a) + 1 = a := by
  sorry

/-- The order relation on `MyNat`. -/
def le : Prop := ∃ x, b = a + x

instance : LE MyNat where
  le := le

@[simp]
theorem zero_le : 0 ≤ a := by
  sorry

theorem le_succ : a ≤ a.succ := by
  sorry

theorem le_refl : a ≤ a := by
  sorry

variable {a b c} in
theorem le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  sorry

variable {a b} in
theorem le_antisymm (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  sorry

theorem le_total : a ≤ b ∨ b ≤ a := by
  sorry

theorem le_self_add : a ≤ a + b := by
  sorry

theorem le_add_self : a ≤ b + a := by
  sorry

@[simp]
theorem le_succ_iff_eq_succ_or_le : a ≤ b.succ ↔ a = b.succ ∨ a ≤ b := by
  sorry

/-- The obvious `<` relation. -/
def lt : Prop := a ≤ b ∧ ¬b ≤ a

instance : LT MyNat where
  lt := lt

variable {a b} in
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b := by
  sorry

theorem ne_zero_iff_pos : a ≠ 0 ↔ 0 < a := by
  sorry

theorem lt_iff_ex_ne_zero : a < b ↔ ∃ x ≠ 0, b = a + x := by
  sorry

variable {a b c}

theorem add_le_add_left (hab : a ≤ b) : a + c ≤ b + c := by
  sorry

theorem mul_lt_mul_of_pos_left (hc : 0 < c) (hab : a < b) : c * a < c * b := by
  sorry

theorem mul_lt_mul_of_pos_right (hc : 0 < c) (hab : a < b) : a * c < b * c := by
  sorry

theorem le_of_add_le_add_left (h : a + b ≤ a + c) : b ≤ c := by
  sorry

theorem mul_left_cancel_of_ne_zero (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

theorem mul_right_cancel_of_ne_zero (ha : a ≠ 0) (h : b * a = c * a) : b = c := by
  sorry

end MyNat
