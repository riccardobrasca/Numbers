import Numbers.NaturalsInstances

-- A term of type `MyPreint` is just a pair of natural numbers.
abbrev MyPreint := MyNat × MyNat
namespace MyPreint

/-- The equivalence relation on pre-integers, which we'll quotient out by to get integers. -/
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

@[simp] lemma R_def (a b c d : MyNat) : R (a,b) (c,d) ↔ a + d = b + c := by rfl

lemma R_refl : ∀ x, R x x := by
  grind [R_def]

lemma R_symm : ∀ {x y}, R x y → R y x := by
  grind [R_def]

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  grind [R_def]

instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (a b c d : MyNat) : (a, b) ≈ (c, d) ↔ a + d = b + c := by rfl

@[simp] lemma equiv_def' (a b c d : MyNat) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by rfl

/-- Negation on pre-integers. -/
def neg (x : MyPreint) : MyPreint := (x.2, x.1)

@[simp] lemma neg_def (a b : MyNat) : neg (a, b) = (b, a) := rfl

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨c, d⟩
  grind [equiv_def, neg_def]

/-- Addition on pre-integers. -/
@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

@[simp] lemma add_def (a b c d : MyNat) : add (a, b) (c, d) = (a + c, b + d) := rfl

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases x' with ⟨a', b'⟩
  rcases y' with ⟨c', d'⟩
  grind [equiv_def, add]

/-- Multiplication on pre-integers. -/
@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp] lemma mul_def (a b c d : MyNat) : mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := rfl

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases x' with ⟨a', b'⟩
  rcases y' with ⟨c', d'⟩
  grind [equiv_def, mul]

end MyPreint

open MyPreint

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

variable {x y z : MyInt} (a b c d : MyNat)

namespace MyInt

@[simp] lemma Quot_eq_Quotient : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := rfl

instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := rfl

instance one : One MyInt where one := ⟦(1, 0)⟧

lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := rfl

/-- Negation on integers. -/
def neg : MyInt → MyInt := Quotient.map MyPreint.neg neg_quotient

instance : Neg MyInt where neg := neg

/-- Addition on integers. -/
def add : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.add add_quotient

instance : Add MyInt where add := add

@[simp] lemma add_def : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ := rfl

/-- Multiplication on integers. -/
def mul : MyInt → MyInt → MyInt  := Quotient.map₂ MyPreint.mul mul_quotient

instance : Mul MyInt where mul := mul

@[simp] lemma mul_def : (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ := rfl

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

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyInt where
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

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  simp [zero_def, one_def]

lemma mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2 h
  simp only [Quot_eq_Quotient, mul_def, zero_def, ne_eq, Quotient.eq, equiv_def', add_zero] at *
  cases MyNat.eq_or_eq_of_add_mul_eq_add_mul h <;> tauto

lemma eq_of_mul_eq_mul_right (hx : x ≠ 0) (h : y * x = z * x) : y = z := by
  have : (y - z) * x = 0 := by rwa [sub_mul, sub_eq_zero]
  rw [← sub_eq_zero]
  by_contra! h
  exact mul_ne_zero h hx this

/-- The natural map from the naturals to the integers. -/
def i : MyInt := ⟦(a, 0)⟧

@[simp] lemma i_zero : i 0 = 0 := rfl

@[simp] lemma i_one : i 1 = 1 := rfl

lemma i_add : i (a + b) = i a + i b := rfl

lemma i_mul : i (a * b) = i a * i b := by
  apply Quot.sound
  simp

lemma i_injective : Function.Injective i := by
  intro a b h
  simpa [i] using h

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + a` -/
def le (x y : MyInt) : Prop := ∃ a : MyNat, y = x + i a

instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0
  simp

lemma le_trans (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rcases h1 with ⟨p, rfl⟩
  rcases h2 with ⟨q, rfl⟩
  use p + q
  grind [i_add]

lemma le_antisymm (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  rcases hxy with ⟨p, rfl⟩
  rcases hyx with ⟨q, hq⟩
  rw [add_assoc, left_eq_add, ← i_add, ← i_zero] at hq
  simp [MyNat.eq_zero_of_add_eq_zero (i_injective hq)]

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases MyNat.le_total (a + d) (b + c) with (h | h)
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    left
    use e
    apply Quot.sound
    simp only [MyPreint.add, add_zero, equiv_def']
    grind
  · rw [le_iff_exists_add] at h
    rcases h with ⟨e, he⟩
    right
    use e
    apply Quot.sound
    simp only [MyPreint.add, add_zero, equiv_def']
    grind

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  simp

lemma i_le_iff : i a ≤ i b ↔ a ≤ b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    rw [← i_add] at hn
    rw [i_injective hn]
    simp
  · intro ⟨k, hk⟩
    use k
    rw [← i_add, ← hk]

lemma add_le_add_left (h : x ≤ y) (z : MyInt) : z + x ≤ z + y := by
  rcases h with ⟨n, rfl⟩
  use n
  grind

lemma mul_pos (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  refine Ne.lt_of_le  ?_ ?_
  · exact (mul_ne_zero hx.ne.symm hy.ne.symm).symm
  · rcases hx.le with ⟨n, rfl⟩
    rcases hy.le with ⟨m, rfl⟩
    simp only [zero_add]
    use n * m
    grind [i_mul]

instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left _ _ := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos (fun _ _ ↦ mul_pos)

lemma archimedean (x : MyInt) : ∃ (n : MyNat), x ≤ i n := by
  refine Quot.induction_on x ?_
  intro ⟨a, b⟩
  refine ⟨a, b, ?_⟩
  simp [i, add_def]

end MyInt
