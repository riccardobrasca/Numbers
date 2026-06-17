import Mathlib.Tactic

/-!

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
  rfl

lemma R_refl : ∀ x, R x x := by
  dsimp [R] --Let's unfold the definitions
  intro x
  rw [add_comm] --We alreado know that addition is commutative on natural numbers!

lemma R_symm : ∀ {x y}, R x y → R y x := by
  dsimp [R]
  intro x y hxy
  rw [add_comm y.1, add_comm y.2, hxy]

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z h1 h2
  rcases x with ⟨a, b⟩
  -- the line above introduces natural numbers `a` and `b` such that `x` is the equivalence class
  -- of the pair `(a,b)`: they exist by definition
  rcases y with ⟨c, d⟩
  rcases z with ⟨e, f⟩ --one can do directly `intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩`
  dsimp [R] at *
  linarith -- `linarith` can do easy computation automatically, see also `ring`

/-- Enable `≈` notation for `R` and ability to quotient by it -/
-- you can ignore this
instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = b + c := by
  exact R_def a b c d

-- Teach the definition of `Setoid.r` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def' (a b c d : ℕ) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by
  exact equiv_def a b c d

/-!

## The algebraic structure on the pre-integers

-/

/-- Negation on pre-integers. -/
def neg (x : MyPreint) : MyPreint := (x.2, x.1)

-- teach it to the simplifier
@[simp] lemma neg_def (a b : ℕ) : neg (a, b) = (b, a) := by
  rfl

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨c, d⟩
  simp at *
  grind



/-- Addition on pre-integers. -/
@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

-- teach it to the simplifier
@[simp] lemma add_def (a b c d : ℕ) : add (a, b) (c, d) = (a + c, b + d) := by
  rfl

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases x' with ⟨a', b'⟩
  rcases y' with ⟨c', d'⟩
  simp at *
  linarith

/-- Multiplication on pre-integers. -/
@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

-- teach it to the simplifier
@[simp] lemma mul_def (a b c d : ℕ) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := by
  rfl

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases x' with ⟨a', b'⟩
  rcases y' with ⟨c', d'⟩
  simp at *
  -- `nlinarith`, a more powerful version of `linarith` works, but let's do it by hand
  --linear_combination (↑r - ↑s) * h1 + (↑a - ↑b) * h2 -- found using `polyrith`
  --`H1` is `h * c'`
  have H1 : a * c' + b' * c' = b * c' + a' * c' := by
    rw [← add_mul, ← add_mul, h]
  --`H2` is `h * d'`
  have H2 : b * d' + a' * d' = a * d' + b' * d' := by
    rw [← add_mul, ← add_mul, h]
  --`H3` is `a * h'`
  have H3 : a * c + a * d' = a * d + a * c' := by
    rw [← mul_add, ← mul_add, h']
  --`H4` is `b * h'`
  have H4 : b * d + b * c' = b * c + b * d' := by
    rw [← mul_add, ← mul_add, h']
  -- `H5` is `H1+H4`
  have H5 : a * c' + b' * c' + b * d + b * c' = b * c' + a' * c' + b * c + b * d' := by
    linarith
  -- `H6` is `H3+H2`
  have H6 : a * c + a * d' + b * d' + a' * d' = a * d + a * c' + a * d' + b' * d' := by
    linarith
  -- `H` is `H5+H6`
  have H7 : a * c' + b' * c' + b * d + b * c' + a * c + a * d' + b * d' + a' * d' =
      b * c' + a' * c' + b * c + b * d' + a * d + a * c' + a * d' + b' * d' := by
    linarith
  -- let's now simplify `H`
  have H : b' * c' + b * d + a * c + a' * d' =
      a' * c' + b * c + a * d + b' * d' := by
    linarith
  linarith

end MyPreint

open MyPreint

/-!

## The integers: definition and algebraic structure -/

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

-- Now one can use the notation `⟦(a,b)⟧` to denote the class of `(a,b)`.

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : ℕ) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

-- `0` notation (the equiv class of (0,0))
instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := by
  rfl

-- `1` notation (the equiv class of (1,0))
instance one : One MyInt where one := ⟦(1, 0)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := by
  rfl

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

lemma mul_def (a b c d : ℕ) :
  (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ :=
  rfl

lemma add_def (a b c d : ℕ) : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
  rfl

lemma add_assoc : ∀ (x y z : MyInt), (x + y) + z = x + (y + z) := by
  intro x y z
  refine Quot.induction_on₃ x y z ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  apply Quot.sound --this just goes from "equal in the quotient" to "in relation"
  simp [Setoid.r, R]
  ring

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
  add_assoc := add_assoc
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
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  simp [zero_def, one_def, Quotient.eq]

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
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2
  simp_all [zero_def, mul_def, Quotient.eq]
  intro h
  cases aux_mul_lemma _ _ _ _ h <;> tauto

lemma eq_of_mul_eq_mul_right {x y z : MyInt} (hx : x ≠ 0) (h : y * x = z * x) : y = z := by
  have : (y - z) * x = 0 := by rwa [sub_mul, sub_eq_zero]
  rw [← sub_eq_zero]
  by_contra! h
  apply mul_ne_zero _ _ h hx
  assumption


/-!

## The map from the naturals to the integers

-/

/-- The natural map from the naturals to the integers. -/
def i (n : ℕ) : MyInt := ⟦(n, 0)⟧

-- The natural map preserves 0
lemma i_zero : i 0 = 0 := by
  rfl

-- The natural map preserves 1
lemma i_one : i 1 = 1 := by
  rfl

-- The natural map preserves addition
lemma i_add (a b : ℕ) : i (a + b) = i a + i b := by
  dsimp [i]
  rfl

-- The natural map preserves multiplication
lemma i_mul (a b : ℕ) : i (a * b) = i a * i b := by
  dsimp [i]
  apply Quot.sound
  simp

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  intro a b h
  simpa [i, Quotient.eq] using h

/-!

## Linear order structure on the integers

-/

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + a` -/
def le (x y : MyInt) : Prop := ∃ a : ℕ, y = x + i a

-- Notation `≤` for `le`
instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0 -- the idea in this proof
  revert x
  quot_proof₁

lemma le_trans (x y z : MyInt) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rcases h1 with ⟨p, rfl⟩
  rcases h2 with ⟨q, rfl⟩
  use p + q -- the idea in this proof
  revert x
  quot_proof₁

lemma le_antisymm (x y : MyInt) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases hxy with ⟨p, rfl⟩
  rcases hyx with ⟨q, hq⟩
  rw [add_assoc, left_eq_add, ← i_add, ← i_zero] at hq -- lots of ideas
  replace hq := Nat.eq_zero_of_add_eq_zero_right (i_injective hq)
  subst hq
  simp [i_zero]

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases Nat.le_total (a + d) (b + c) with (h | h) -- idea
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    left
    use e
    apply Quot.sound
    simp
    linarith
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    right
    use e
    apply Quot.sound
    simp
    linarith

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  rw [i_one]
  ring

/-- The natural map from the naturals to the integers preserves and reflects `≤`. -/
lemma i_le_iff (a b : ℕ) : i a ≤ i b ↔ a ≤ b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    rw [← i_add] at hn
    rw [i_injective hn]
    simp
  · intro h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    use k
    rw [← i_add, ← hk]

/-

## Interaction between ordering and algebraic structure

-/

lemma add_le_add_left (x y : MyInt) (h : x ≤ y) (z : MyInt) : x + z ≤ y + z := by
  rcases h with ⟨n, rfl⟩
  use n
  ring

lemma mul_pos (x y : MyInt) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  refine Ne.lt_of_le  ?_ ?_
  · exact (mul_ne_zero x y hx.ne.symm hy.ne.symm).symm
  · rcases hx.le with ⟨n, rfl⟩
    rcases hy.le with ⟨m, rfl⟩
    simp
    use n * m
    rw [i_mul]
    ring

instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma archimedean (x : MyInt) : ∃ (n : ℕ), x ≤ i n := by
  refine Quot.induction_on x ?_
  intro ⟨a, b⟩
  refine ⟨a, b, ?_⟩
  simp [i, add_def, Quotient.eq]

end MyInt
