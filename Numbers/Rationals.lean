import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Setoid.Basic
import Numbers.Integers

instance : Mul {x : MyInt // x ≠ 0} where
  mul a b := ⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩

@[simp, norm_cast] lemma Int.ne_zero_coe_mul (a b : {x : MyInt // x ≠ 0}) :
    ((a * b : {x : MyInt // x ≠ 0}) : MyInt) = a * b := by
  rfl

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
  rfl

lemma R_refl : ∀ x, R x x := by
  grind

lemma R_symm : ∀ {x y}, R x y → R y x := by
  grind

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ h1 h2
  apply MyInt.eq_of_mul_eq_mul_right hd
  grind

/-- Enable `≈` notation for `R` and ability to quotient by it. -/
instance R_equiv : Setoid MyPrerat where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier
@[simp, grind =] lemma equiv_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (a, b) ≈ (c, d) ↔ a * d = b * c := by
  rfl

-- Teach the definition of `Setoid.r` to the simplifier
@[simp] lemma equiv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    Setoid.r (a, b) (c, d) ↔ a * d = b * c := by
  rfl

/-!

## The algebraic structure on the pre-rationals

-/

/-!

# Negation

-/

/-- Negation on pre-rationals. -/
def neg (ab : MyPrerat) : MyPrerat := (-ab.1, ab.2)

-- teach it to the simplifier
@[simp, grind =] lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) : neg (a, b) = (-a, b) := by
  rfl

lemma neg_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  grind

/-

## Addition

-/

/-- Addition on pre-rationals. -/
def add (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.2 + ab.2 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    add (a, b) (c, d) = (a * d + b * c, b * d) := by
  rfl

lemma add_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  rcases x with ⟨a, b, hb⟩
  rcases x' with ⟨a', b', hb'⟩
  rcases y with ⟨c, d, hd⟩
  rcases y' with ⟨c', d', hd'⟩
  simp [MyPrerat.add] at *
  -- it's just some random puzzle about polynomials in algebra
  grind

/-

## Multiplication

-/

/-- Multiplication on pre-rationals. -/
def mul (ab cd : MyPrerat) : MyPrerat := (ab.1 * cd.1, ab.2 * cd.2)

-- teach it to the simplifier
@[simp] lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    mul (a, b) (c, d) = (a * c, b * d) := by
  rfl

lemma mul_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') ⦃y y' : MyPrerat⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  rcases x with ⟨a, b, hb⟩
  rcases x' with ⟨a', b', hb'⟩
  rcases y with ⟨c, d, hd⟩
  rcases y' with ⟨c', d', hd'⟩
  simp [MyPrerat.mul] at *
  grind

/-

## Reciprocal

-/

/-- Reciprocal, or inverse, on pre-rationals. -/
noncomputable
def inv (ab : MyPrerat) : MyPrerat := if ha : ab.1 ≠ 0 then ⟨ab.2, ab.1, ha⟩ else ⟨0, 1, by simp⟩

-- teach it to the simplifier
@[simp] lemma inv_def {a : MyInt} (b : {x : MyInt // x ≠ 0}) (ha : a ≠ 0) :
    inv (a, b) = (b.1, ⟨a, ha⟩) := by
  -- Proof: obvious by definition of `inv`
  dsimp [inv]
  split <;> simp

lemma inv_def' (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    inv (a, b) = if ha : a ≠ 0 then ⟨b, a, ha⟩ else ⟨0, 1, by simp⟩ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrerat⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨a', b'⟩
  simp [MyPrerat.inv] at *
  aesop

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
  rfl

-- `0` notation (the equiv class of (0,1))
instance zero : Zero MyRat where zero := ⟦(0, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyRat) = ⟦(0, ⟨1, one_ne_zero⟩)⟧ := by
  rfl

-- `1` notation (the equiv class of (1,1))
instance one : One MyRat where one := ⟦(1, ⟨1, one_ne_zero⟩)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyRat) = ⟦(1, ⟨1, one_ne_zero⟩)⟧ := by
  rfl

/-- Negation on rationals. -/
def neg : MyRat → MyRat := Quotient.map MyPrerat.neg neg_quotient

-- unary `-` notation
instance : Neg MyRat where neg := neg

lemma neg_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    -(⟦(a, b)⟧ : MyRat) = ⟦(-a, b)⟧ := by
  rfl

/-- Addition on integers. -/
def add : MyRat → MyRat → MyRat := Quotient.map₂ MyPrerat.add add_quotient

-- `+` notation
instance : Add MyRat where add := add

lemma add_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) + ⟦(c, d)⟧ = ⟦(a * d + b * c, b * d)⟧ :=
  rfl

/-- Multiplication on integers. -/
def mul : MyRat → MyRat → MyRat  := Quotient.map₂ MyPrerat.mul mul_quotient

-- `*` notation
instance : Mul MyRat where mul := mul

lemma mul_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) * ⟦(c, d)⟧ = ⟦(a * c, b * d)⟧ :=
  rfl

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
  rfl

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
    try grind)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp
    try grind)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp
    try grind)

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
  add_assoc := by quot_proof
  zero := 0
  zero_add := by quot_proof
  add_zero := by quot_proof
  add_comm := by quot_proof
  mul := (· * ·)
  left_distrib := by quot_proof
  right_distrib := by quot_proof
  zero_mul := by quot_proof
  mul_zero := by quot_proof
  mul_assoc := by quot_proof
  one := 1
  one_mul := by quot_proof
  mul_one := by quot_proof
  neg := (- ·)
  mul_comm := by quot_proof
  neg_add_cancel := by quot_proof
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma sub_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) (c : MyInt) (d : {x : MyInt // x ≠ 0}) :
    (⟦(a, b)⟧ : MyRat) - ⟦(c, d)⟧ = ⟦(a * d - b * c, b * d)⟧ := by
  rw [sub_eq_add_neg, neg_def, add_def, mul_neg, ← sub_eq_add_neg]

-- To make the rationals into a field we need to think a little more.

lemma zero_ne_one : (0 : MyRat) ≠ 1 := by
  simp [zero_def, one_def]

lemma mul_inv_cancel (x : MyRat) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rcases x with ⟨a, b, hb⟩
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    apply Quotient.eq.2
    simp
  simp
  rw [inv_def, one_def]
  apply Quotient.eq.2
  simp [MyPrerat.mul]
  rw [MyPrerat.inv_def _ ha]
  simp [mul_comm]

noncomputable
instance field : Field MyRat where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    apply Quot.sound
    simp [MyPrerat.inv]
  qsmul := _
  nnqsmul := _

/-!

## The natural map from the naturals to the rationals

-/

/-- The natural map from the naturals to the rationals. -/
def i (n : MyNat) : MyRat := ⟦(MyInt.i n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma i_zero : i 0 = 0 := by
  rfl

-- The natural map preserves 1
lemma i_one : i 1 = 1 := by
  rfl

-- The natural map preserves addition
lemma i_add (a b : MyNat) : i (a + b) = i a + i b := by
  apply Quot.sound
  simp [MyInt.i]

-- The natural map preserves multiplication
lemma i_mul (a b : MyNat) : i (a * b) = i a * i b := by
  apply Quot.sound
  simp [MyInt.i]

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  intro a b h
  simp [i, MyInt.i] at h
  assumption

/-!

## The natural map from the integers to the rationals

-/

/-- The natural map from the integers to the rationals. -/
def j (n : MyInt) : MyRat := ⟦(n, ⟨1, by simp⟩)⟧

-- The natural map preserves 0
lemma j_zero : j 0 = 0 := by
  rfl

-- The natural map preserves 1
lemma j_one : j 1 = 1 := by
  rfl

-- The natural map preserves addition
lemma j_add (a b : MyInt) : j (a + b) = j a + j b := by
  apply Quot.sound
  simp

-- The natural map preserves multiplication
lemma j_mul (a b : MyInt) : j (a * b) = j a * j b := by
  apply Quot.sound
  simp

-- The natural map is injective
lemma j_injective (a b : MyInt) : j a = j b ↔ a = b := by
  constructor
  · intro h
    simp [j] at h
    assumption
  · rintro rfl
    rfl

lemma j_comp_eq_i (n : MyNat) : j (MyInt.i n) = i n := by
  simp [i, j, MyInt.i]

-- We can now give a formula for `⟦(a, b)⟧` using `j a` and `j b`.

theorem Quotient.mk_def (a : MyInt) (b : {x : MyInt // x ≠ 0}) :
    ⟦(a, b)⟧ = j a * (j b)⁻¹ := by
  calc
  ⟦(a, b)⟧ = ⟦((a, ⟨1, by simp⟩) : MyPrerat)⟧ * ⟦(1, b)⟧ := by
    apply Quotient.sound
    simp only [ne_eq, MyPrerat.mul_def, mul_one, equiv_def, Int.ne_zero_coe_mul, mul_comm]
  _        = j a * (⟦((b, ⟨1, by simp⟩) : MyPrerat)⟧)⁻¹ := by
    apply Quotient.sound
    rw [MyPrerat.inv_def _ b.2]

end MyRat
