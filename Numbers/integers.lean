import Mathlib.Tactic

/-!

All the original work is by Kevin Buzzard.

# The integers

In this file we assume all standard facts about the naturals, and then build
the integers from scratch.

The strategy is to observe that every integer can be written as `a - b`
for `a` and `b` naturals, so we define the "pre-integers" to be `ℕ × ℕ`, the pairs
`(a, b)` of naturals. We define an equivalence relation `≈` on `ℕ × ℕ`, with the
idea being that `(a, b) ≈ (c, d)` if and only if `a - b = c - d`. This doesn't
make sense yet, but the equivalent equation `a + d = b + c` does. We prove
that this is an equivalence relation, and define the integers to be the quotient.

## The ring structure on the integers

We extend addition and multiplication from the naturals to the integers,
and also define negation `-x` and subtraction `x - y`.
We then prove that the integers are a commutative ring. The proofs are all of
the form "reduce to a question about naturals, and then solve it using tactics
which prove theorems about naturals".

## The ordering on the integers

We prove that the integers are a total order, and also that the ordering
plays well with the ring structure.

-/

/-!

## The pre-integers

-/

-- A term of type `MyPreint` is just a pair of natural numbers.
abbrev MyPreint := ℕ × ℕ

namespace MyPreint

/-!

## The equivalence relation on the pre-integers

-/

/-- The equivalence relation on pre-integers, which we'll quotient out
by to get integers. -/
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

/-- Useful lemma that is mathematically trivial. -/
lemma R_def (a b c d : ℕ) : R (a,b) (c,d) ↔ a + d = b + c := by
  sorry

lemma R_refl : ∀ x, R x x := by
  sorry

lemma R_symm : ∀ {x y}, R x y → R y x := by
  sorry

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  sorry

/-- Enable `≈` notation for `R` and ability to quotient by it -/
-- you can ignore this
instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = b + c := by
  sorry

-- Teach the definition of `Setoid.r` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def' (a b c d : ℕ) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by
  sorry

/-!

## The algebraic structure on the pre-integers

-/

/-- Negation on pre-integers. -/
def neg (x : MyPreint) : MyPreint := (x.2, x.1)

-- teach it to the simplifier
@[simp] lemma neg_def (a b : ℕ) : neg (a, b) = (b, a) := by
  sorry

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  sorry

/-- Addition on pre-integers. -/
@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

-- teach it to the simplifier
@[simp] lemma add_def (a b c d : ℕ) : add (a, b) (c, d) = (a + c, b + d) := by
  sorry

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  sorry

/-- Multiplication on pre-integers. -/
@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

-- teach it to the simplifier
@[simp] lemma mul_def (a b c d : ℕ) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := by
  sorry

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  sorry

end MyPreint

open MyPreint

/-!

## The integers: definition and algebraic structure -/

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

-- Now one can use the notation `⟦(a,b)⟧` to denote the class of `(a,b)`.

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : ℕ) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  sorry

-- `0` notation (the equiv class of (0,0))
instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := by
  sorry

-- `1` notation (the equiv class of (1,0))
instance one : One MyInt where one := ⟦(1, 0)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := by
  sorry

/-- Negation on integers. -/
def neg : MyInt → MyInt := Quotient.map MyPreint.neg neg_quotient

-- unary `-` notation
instance : Neg MyInt where neg := neg

/-- Addition on integers. -/
def add : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.add add_quotient

-- `+` notation
instance : Add MyInt where add := add

/-- Multiplication on integers. -/
def mul : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.mul mul_quotient

-- `*` notation
instance : Mul MyInt where mul := mul

lemma mul_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ := by
  sorry

lemma add_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
  rfl

lemma add_assoc : ∀ (x y z : MyInt), (x + y) + z = x + (y + z) := by
  sorry

--The same will happen for almost everything else we want to prove!

/-!

## Tactic hackery

Every single proof of every single ring axiom for the integers is:
"replace all integers with pairs of naturals, turn the question into a question
about naturals, and then get the `ring` tactic to prove it"

One slight problem is that we need three different tactics depending on whether the
axiom mentions 1, 2 or 3 variables. So we write three tactics and then one tactic
which does all three cases.

-/

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients. -/
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyInt where
  add := (· + ·)
  add_assoc := sorry
  zero := 0
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  mul := (· * ·)
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one := 1
  one_mul := by sorry
  mul_one := by sorry
  neg := (- ·)
  mul_comm := by sorry
  neg_add_cancel := by sorry
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  sorry

lemma aux_mul_lemma (a b c d : ℕ) (h : a * d + b * c = a * c + b * d) : a = b ∨ c = d := by
  induction a generalizing b with
  | zero =>
    simp_all
    tauto
  | succ e he =>
    cases b with
    | zero =>
      simp_all
    | succ f =>
      specialize he f
      simp
      apply he
      simp [Nat.succ_mul] at h
      linarith

lemma mul_ne_zero (x y : MyInt) : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  sorry

lemma eq_of_mul_eq_mul_right {x y z : MyInt} (hx : x ≠ 0) (h : y * x = z * x) : y = z := by
  sorry

/-!

## The map from the naturals to the integers

-/

/-- The natural map from the naturals to the integers. -/
def i (n : ℕ) : MyInt := ⟦(n, 0)⟧

-- The natural map preserves 0
lemma i_zero : i 0 = 0 := by
  sorry

-- The natural map preserves 1
lemma i_one : i 1 = 1 := by
  sorry

-- The natural map preserves addition
lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  sorry

-- The natural map preserves multiplication
lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  sorry

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  sorry

/-!

## Linear order structure on the integers

-/

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + a` -/
def le (x y : MyInt) : Prop := ∃ a : ℕ, y = x + i a

-- Notation `≤` for `le`
instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  sorry

lemma le_trans (x y z : MyInt) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry

lemma le_antisymm (x y : MyInt) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  sorry

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _ --ignore this

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  sorry

/-- The natural map from the naturals to the integers preserves and reflects `≤`. -/
lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  sorry

/-

## Interaction between ordering and algebraic structure

-/

lemma add_le_add_left (x y : MyInt) (h : x ≤ y) (z : MyInt) : x + z ≤ y + z := by
  sorry

lemma mul_pos (x y : MyInt) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  sorry

instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma archimedean (x : MyInt) : ∃ (n : ℕ), x ≤ i n := by
  sorry

end MyInt
