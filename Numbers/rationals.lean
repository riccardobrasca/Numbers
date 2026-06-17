import Mathlib.Tactic
import Numbers.integers

/-!

All the original work is by Kevin Buzzard.

# The rationals

In this file we build the rationals from scratch.

The strategy is to observe that every rationals can be written as `a / b`
for `a` and `b` integers witb `b ≠ 0`, so we define the "pre-rationals" to
be `MyInt × (MyInt - {0})`, the pairs `(a, b)` of integers. We define an equivalence
relation `≈` on `MyInt × (MyInt - {0})`, with the idea being that `(a, b) ≈ (c, d)`
if and only if `a / b = c / d`. This doesn't make sense yet, but the equivalent
equation `a * d = b * c` does. We prove that this is an equivalence relation,
and define the integers to be the quotient.

## The field structure on the rationals

We extend addition, subtraction and multiplication to the rationals, and also
define division. We then prove that the rationals are a field. The proofs are all of
the form "reduce to a question about integers, and then solve it using tactics
which prove theorems about integers".

## The ordering on the integers

In the file `RationalGameOrder.lean` we define an ordering on the rationals,
prove that it is total, and that it plays well with the ring structure
defined in this file.
-/

/-!

## The pre-rationals

### Denominator API

-/
instance : Mul {x : MyInt // x ≠ 0} where
  mul a b := ⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩

@[simp, norm_cast] lemma Int.ne_zero_coe_mul (a b : {x : MyInt // x ≠ 0}) :
    ((a * b : {x : MyInt // x ≠ 0}) : MyInt) = a * b := by
  sorry

/-!

### Definition of `MyPrerat`, the pre-rationals

-/

/-- A "pre-rational" is just a pair of integers, the second one non-zero. -/
abbrev MyPrerat := MyInt × {x : MyInt // x ≠ 0}

namespace MyPrerat

/-!

## The equivalence relation on `MyPrerat`

-/

/-- The equivalence relation on pre-rationals, which we'll quotient out
by to get rationals. -/
def R (x y : MyPrerat) : Prop := x.1 * y.2 = x.2 * y.1

-- Lemma saying what definition of `R` is on ordered pairs
@[grind =] lemma R_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    R (a,b) (c,d) ↔ a * d = b * c := by
  sorry

lemma R_refl : ∀ x, R x x := by
  sorry

lemma R_symm : ∀ {x y}, R x y → R y x := by
  sorry

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  sorry

/-- Enable `≈` notation for `R` and ability to quotient by it. -/
instance R_equiv : Setoid MyPrerat where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier
@[simp, grind =]
lemma equiv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (a, b) ≈ (c, d) ↔ a * d = b * c := by
  sorry

-- Teach the definition of `Setoid.r` to the simplifier
@[simp, grind =]
lemma equiv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    Setoid.r (a, b) (c, d) ↔ a * d = b * c := by
  sorry

/-!

## The algebraic structure on the pre-rationals

-/

/-!

# Negation

-/

/-- Negation on pre-rationals. -/
def neg (x : MyPrerat) : MyPrerat := (-x.1, x.2)

-- teach it to the simplifier
@[simp, grind =] lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) : neg (a, b) = (-a, b) := by
  sorry

lemma neg_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  sorry

/-

## Addition

-/

/-- Addition on pre-rationals. -/
def add (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.2 + ab.2 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    add (a, b) (c, d) = (a * d + b * c, b * d) := by
  sorry

lemma add_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  sorry

/-

## Multiplication

-/

/-- Multiplication on pre-rationals. -/
def mul (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    mul (a, b) (c, d) = (a * c, b * d) := by
  sorry

lemma mul_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  sorry

/-

## Reciprocal

-/

/-- Reciprocal, or inverse, on pre-rationals. -/
noncomputable
def inv (x : MyPrerat) : MyPrerat := if ha : x.1 ≠ 0 then ⟨x.2, x.1, ha⟩ else ⟨0, 1, by simp⟩

-- teach it to the simplifier
@[simp] lemma inv_def {a : MyInt} (b : {x : MyInt // x ≠ 0}) (ha : a ≠ 0) :
    inv (a, b) = (b.1, ⟨a, ha⟩) := by
  sorry

lemma inv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    inv (a, b) = if ha : a ≠ 0 then ⟨b, a, ha⟩ else ⟨0, 1, by simp⟩ := by
  sorry

lemma inv_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  sorry

end MyPrerat

open MyPrerat

/-!

## The rationals: definition and algebraic structure

-/

/-- Make the rationals as a quotient of prerationals. -/
abbrev MyRat := Quotient R_equiv

namespace MyRat

@[simp] lemma Quot_eq_Quotient (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  sorry

-- `0` notation (the equiv class of (0,1))
instance zero : Zero MyRat where zero := ⟦(0, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyRat) = ⟦(0, ⟨1, one_ne_zero⟩)⟧ := by
  sorry

-- `1` notation (the equiv class of (1,1))
instance one : One MyRat where one := ⟦(1, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyRat) = ⟦(1, ⟨1, one_ne_zero⟩)⟧ := by
  sorry

/-- Negation on rationals. -/
def neg : MyRat → MyRat := Quotient.map MyPrerat.neg neg_quotient

-- unary `-` notation
instance : Neg MyRat where neg := neg

lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    -(⟦(a, b)⟧ : MyRat) = ⟦(-a, b)⟧ := by
  sorry

/-- Addition on integers. -/
def add : MyRat → MyRat → MyRat := Quotient.map₂ MyPrerat.add add_quotient

-- `+` notation
instance : Add MyRat where add := add

lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) + ⟦(c, d)⟧ = ⟦(a * d + b * c, b * d)⟧ :=
  sorry

/-- Multiplication on integers. -/
def mul : MyRat → MyRat → MyRat  := Quotient.map₂ MyPrerat.mul mul_quotient

-- `*` notation
instance : Mul MyRat where mul := mul

lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) * ⟦(c, d)⟧ = ⟦(a * c, b * d)⟧ :=
  sorry

/-

## Inverse

-/
/-- reciprocal on nonzero rationals. -/
noncomputable
def inv : MyRat → MyRat := Quotient.map MyPrerat.inv inv_quotient

noncomputable
instance : Inv MyRat := ⟨inv⟩

lemma inv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat)⁻¹ = ⟦MyPrerat.inv (a, b)⟧ := by
  sorry

/-!

## Tactic hackery

Every single proof of every single ring axiom for the rationals is:
"replace all rationals with pairs of integers, turn the question into a question
about integers, and then get the `ring` tactic to prove it"

The problem is that we need three slightly different tactics depending on whether the
axiom mentions 1, 2 or 3 variables.

-/

section tactic_hackery

-- This section contains everything Kevin knows about tactic writing:
-- you can write a tactic which just does other tactics in some order.

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients.

It will work if there are between 1 and 3 variables, and it
uses the universal property of quotients to reduce the equality
to an equality of polynomials with coefficients in the *integers*,
and then attempts to use the `ring` tactic to solve it. -/

-- note that we have to go through all this: we can't use `ring`
-- on MyRat directly yet and we're using this tool to prove
-- that it's a commutative ring, after which we will be able to use `ring`.
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃
  )

end tactic_hackery

instance commRing : CommRing MyRat where
  add := (· + ·)
  add_assoc := by sorry
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
  nsmul := nsmulRec --ignore
  zsmul := zsmulRec --ignore

@[grind =]
lemma sub_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) - ⟦(c, d)⟧ = ⟦(a * d - b * c, b * d)⟧ := by
  sorry

-- To make the rationals into a field we need to think a little more.

lemma zero_ne_one : (0 : MyRat) ≠ 1 := by
  sorry

lemma mul_inv_cancel (x : MyRat) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

noncomputable
instance field : Field MyRat where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by sorry
  qsmul := _ --ignore
  nnqsmul := _ --ignore

/-!

## The natural map from the naturals to the rationals

-/

/-- The natural map from the naturals to the rationals. -/
def i (n : ℕ) : MyRat := ⟦(MyInt.i n, ⟨1, by simp⟩)⟧

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

## The natural map from the integers to the rationals

-/

/-- The natural map from the integers to the rationals. -/
def j (n : MyInt) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma j_zero : j 0 = 0 := by
  sorry

-- The natural map preserves 1
lemma j_one : j 1 = 1 := by
  sorry

-- The natural map preserves addition
lemma j_add (a b : MyInt) : j (a + b) = j a + j b := by
  sorry

-- The natural map preserves multiplication
lemma j_mul (a b : MyInt) : j (a * b) = j a * j b := by
  sorry

-- The natural map is injective
lemma j_injective (a b : MyInt) : j a = j b ↔ a = b := by
  sorry

-- All the proofs were exactly the same as the natural number case.

lemma j_comp_eq_i (n : ℕ) : j (MyInt.i n) = i n := by
  sorry

-- We can now give a formula for `⟦(a, b)⟧` using `j a` and `j b`.

theorem Quotient.mk_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    ⟦(a, b)⟧ = j a * (j b)⁻¹ := by
  sorry

-- Now given a prerational, we never have to unfold it again,
-- because we have got the theorem giving the formula for
-- a general prerational, so we can just rewrite that instead.

end MyRat

/-!

Want more of this nonsense? See how the concept of order is developed
on the rational numbers in `RationalGameOrder.lean`. It's more
subtle than what we had to do here, which was only equational reasoning.

-/
