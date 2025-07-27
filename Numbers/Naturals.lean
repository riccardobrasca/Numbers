/-!

In this file we define our copy `MyNat` of the natural numbers. To check that we dont cheat
using results already proved in mathlib we don't import anything. (Note that even if `MyNat` is
defined here, the simple fact of, say, providing the `Semiring` instance allows to use a lot of
results in mathlib.)

-/

/-- Our copy of the natural numbers.-/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

variable (a b c : MyNat)

instance : Zero MyNat := ⟨zero⟩

theorem zero_def : zero = 0 := rfl

instance : One MyNat := ⟨succ 0⟩

theorem one_eq_succ_zero : 1 = succ 0 := rfl

theorem succ_ne_zero : succ a ≠ 0 := by simp

theorem zero_ne_one : (0 : MyNat) ≠ 1 := by simp

/-- Addition on `MyNat`. -/
def add : MyNat → MyNat → MyNat
| a, 0 => a
| a, (succ b) => succ (add a b)

instance : Add MyNat where
  add := add

theorem add_zero : a + 0 = a := rfl

theorem add_succ : a + succ b = succ (a + b):= rfl

@[grind =]
theorem succ_eq_add_one : succ a = a + 1 := rfl

@[simp] theorem add_one_ne_zero : a + 1 ≠ 0 := by simp [← succ_eq_add_one]

theorem zero_add : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ n hn =>
      rw [add_succ, hn]

theorem succ_add : (succ a) + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ n hn =>
      rw [add_succ, hn, add_succ]

theorem add_assoc : a + b + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ n hn =>
    rw [add_succ, hn, add_succ, add_succ]

theorem add_comm : a + b = b + a := by
  induction a with
  | zero =>
      rw [zero_def, zero_add, add_zero]
  | succ n hn =>
      rw [add_succ, succ_add, hn]

variable {a b} in
theorem eq_zero_of_add_eq_zero (h : a + b = 0) : a = 0 := by
  induction b with
  | zero =>
      rwa [zero_def, add_zero] at h
  | succ n hn =>
      exfalso
      rw [add_succ] at h
      exact succ_ne_zero _ h

/-- Multiplication on `MyNat`. -/
def mul : MyNat → MyNat → MyNat
| _, 0 => 0
| a, (succ b) => mul a b + a

instance : Mul MyNat where
  mul := mul

theorem mul_zero : a * 0 = 0 := by
  rw [← zero_def]
  rfl

theorem mul_succ : a * b.succ = a * b + a := rfl

@[grind =] theorem succ_mul : a.succ * b = a * b + b := by
  induction b with
  | zero =>
      rw [zero_def, mul_zero, mul_zero, zero_add]
  | succ n hn =>
      rw [mul_succ, hn, mul_succ, add_succ, add_succ, add_assoc, add_comm n, ← add_assoc]

theorem zero_mul : 0 * a = 0 := by
  induction a with
  | zero => rfl
  | succ n hn =>
      rw [mul_succ, hn, add_zero]

theorem left_distrib : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
      rw [zero_def, add_zero, mul_zero, add_zero]
  | succ n hn =>
      rw [add_succ, mul_succ, hn, mul_succ, add_assoc]

theorem mul_one : a * 1 = a := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem mul_comm : a * b = b * a := by
  induction b with
  | zero =>
      rw [zero_def, mul_zero, zero_mul]
  | succ n hn =>
      rw [mul_succ, succ_mul, hn]

theorem right_distrib : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem one_mul : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem mul_assoc : a * b * c = a * (b * c) := by
  induction c with
  | zero =>
      rw [zero_def, mul_zero, mul_zero, mul_zero]
  | succ n hn =>
      rw [mul_succ, hn, mul_succ, left_distrib]

variable {a b c} in
theorem add_left_cancel (h : a + b = a + c) : b = c := by
  induction a with
  | zero =>
      rwa [zero_def, zero_add, zero_add] at h
  | succ n hn =>
      rw [succ_add, succ_add] at h
      exact hn (succ.inj h)

theorem mul_ne_zero : ∀ {a b : MyNat}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
| 0, b => by simp
| a, 0 => by simp
| a + 1, b + 1 => by
  intro _ _
  calc (a + 1) * (b + 1) = (a * b + a + b) + 1 := by
        rw [left_distrib, mul_one, right_distrib, one_mul, add_assoc, ← add_assoc b,
          add_assoc (a * b), add_comm a, ← add_assoc]
    _ ≠ 0 := by simp

/-- The predecessor function, with `pred 0 = 0`. -/
def pred : MyNat → MyNat
| zero => 0
| succ a => a

@[simp] theorem pred_zero : pred 0 = 0 := rfl

theorem pred_succ : pred (succ a) = a := rfl

@[simp] theorem add_one_pred : pred (a + 1) = a := rfl

variable {a} in
theorem succ_pred (ha : a ≠ 0) : succ (pred a) = a :=
match a with
| succ _ => pred_succ _

variable {a} in
@[simp] theorem pred_add_one (ha : a ≠ 0) : (pred a) + 1 = a := succ_pred ha

/-- The order relation on `MyNat`. -/
def le : Prop := ∃ x, b = a + x

instance : LE MyNat where
  le := le

@[simp] theorem zero_le : 0 ≤ a := by
  exact ⟨a, by rw [zero_add]⟩

theorem le_succ : a ≤ a.succ := by
  exact ⟨1, by rw [succ_eq_add_one]⟩

theorem le_refl : a ≤ a := by
  exact ⟨0, by rw [add_zero]⟩

variable {a b c} in
theorem le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with ⟨x, rfl⟩
  rcases hbc with ⟨y, rfl⟩
  exact ⟨x + y, by rw [add_assoc]⟩

variable {a b} in
theorem le_antisymm (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with ⟨x, rfl⟩
  rcases hba with ⟨y, hy⟩
  replace hy : a + 0 = a + (x + y) := by
    rwa [add_zero, ← add_assoc]
  rw [eq_zero_of_add_eq_zero (add_left_cancel hy.symm), add_zero]

theorem le_total : a ≤ b ∨ b ≤ a := by
  induction a with
  | zero =>
      left
      exact zero_le b
  | succ n hn =>
      rcases hn with hn | hn
      · by_cases h : b = n
        · right
          rw [h]
          exact le_succ _
        · left
          rcases hn with ⟨x, rfl⟩
          cases x with
          | zero => simp [zero_def, add_zero] at h
          | succ x =>
              exact ⟨x, by rw [add_succ, succ_add]⟩
      · right
        exact le_trans hn (le_succ _)

theorem le_self_add : a ≤ a + b :=
  ⟨b, rfl⟩

@[simp] theorem le_succ_iff_eq_succ_or_le : a ≤ b.succ ↔ a = b.succ ∨ a ≤ b := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦  ?_⟩
  · cases x with
    | zero =>
        rw [zero_def, add_zero] at hx
        left
        exact hx.symm
    | succ x =>
        right
        refine ⟨x, ?_⟩
        rw [add_succ] at hx
        exact succ.inj hx
  · rcases h with h | h
    · rw [h]
      exact le_refl _
    · exact le_trans h (le_succ _)

/-- The obvious `<` relation. -/
def lt : Prop := a ≤ b ∧ ¬b ≤ a

instance : LT MyNat where
  lt := lt

variable {a b} in
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h ↦ ⟨h.1, fun hab ↦ h.2 <| hab ▸ le_refl b⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, fun hab ↦ h2 <| le_antisymm h1 hab⟩⟩

theorem ne_zero_iff_pos : a ≠ 0 ↔ 0 < a :=
  ⟨fun h ↦ lt_iff_le_and_ne.mpr ⟨zero_le _, h.symm⟩, fun h ↦ Ne.symm (lt_iff_le_and_ne.1 h).2⟩

theorem lt_iff_ex_ne_zero : a < b ↔ ∃ x ≠ 0, b = a + x := by
  rw [lt_iff_le_and_ne]
  refine ⟨fun ⟨⟨x, hx⟩, h⟩ ↦ ⟨x, fun h0 ↦ h ?_, hx⟩, fun ⟨x, hx, h⟩ ↦ ⟨⟨x, h⟩, fun h0 ↦ hx ?_⟩⟩
  · rw [h0, add_zero] at hx
    exact hx.symm
  · replace h : a + 0 = a + x := by
      rwa [add_zero, ← h]
    exact (add_left_cancel h).symm

variable {a b c}

theorem add_le_add_left (hab : a ≤ b) : c + a ≤ c + b := by
  rcases hab with ⟨x, rfl⟩
  exact ⟨x, by rw [add_assoc]⟩

theorem mul_lt_mul_of_pos_left (hab : a < b) (hc : 0 < c) : c * a < c * b := by
  rw [lt_iff_ex_ne_zero] at *
  rcases hab with ⟨x, hx, rfl⟩
  rcases hc with ⟨y, hy, rfl⟩
  refine ⟨x * y, ?_⟩
  constructor
  · exact mul_ne_zero hx hy
  · rw [zero_add, left_distrib, mul_comm x]

theorem mul_lt_mul_of_pos_right (hab : a < b) (hc : 0 < c) : a * c < b * c := by
  rw [mul_comm, mul_comm b]
  exact mul_lt_mul_of_pos_left hab hc

theorem le_of_add_le_add_left (h : a + b ≤ a + c) : b ≤ c := by
  rcases h with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [add_assoc] at hx
  exact add_left_cancel hx

theorem mul_left_cancel_of_ne_zero (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  rcases le_total b c with H | H
  · by_cases hbc : b = c
    · assumption
    exfalso
    rw [ne_zero_iff_pos] at ha
    exact (lt_iff_le_and_ne.1 (mul_lt_mul_of_pos_left (lt_iff_le_and_ne.mpr ⟨H, hbc⟩) ha)).2 h
  · by_cases hbc : b = c
    · assumption
    exfalso
    rw [ne_zero_iff_pos] at ha
    exact (lt_iff_le_and_ne.1 (mul_lt_mul_of_pos_left (lt_iff_le_and_ne.mpr
        ⟨H, Ne.symm hbc⟩) ha)).2 h.symm

theorem mul_right_cancel_of_ne_zero (ha : a ≠ 0) (h : b * a = c * a) : b = c := by
  rw [mul_comm, mul_comm c] at h
  exact mul_left_cancel_of_ne_zero ha h

end MyNat
