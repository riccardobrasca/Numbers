import Numbers.rationals_order

-- Lean already knows the absolute value (since there is an order on `MyRat`: `|x|` is defined as
-- `max (x, -x)`.
--See the files `Mathlib.Algebra.Order.*.Abs` for various properties
abbrev IsCauchy (x : ℕ → MyRat) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε

open Finset in
lemma IsCauchy.bounded {x : ℕ → MyRat} (hx : IsCauchy x) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B := by
  sorry

abbrev MyPrereal := {x // IsCauchy x}

namespace MyPrereal

open MyPrereal

--ignore the following
instance funLike : FunLike MyPrereal ℕ MyRat where
  coe := Subtype.val
  coe_injective _ _ := Subtype.ext

lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε :=
  x.2

@[simp] lemma coe_apply {x : ℕ → MyRat} (hx : IsCauchy x) (n : ℕ) :
    (⟨x, hx⟩ : MyPrereal) n = x n := by
  rfl

lemma bounded (x : MyPrereal) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
  x.2.bounded

def R (x y : MyPrereal) : Prop := ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε

lemma R_def (x y : MyPrereal) : R x y ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  sorry

lemma R_refl : ∀ x, R x x := by
  sorry

lemma R_symm : ∀ {x y}, R x y → R y x := by
  sorry

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  sorry

instance R_equiv : Setoid MyPrereal where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (x y : MyPrereal) : x ≈ y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  sorry

@[simp] lemma equiv_def' (x y : MyPrereal) : Setoid.r x y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  sorry

lemma IsCauchy.const (x : MyRat) : IsCauchy (fun _ ↦ x) := by
  sorry

instance zero : Zero MyPrereal where
  zero := ⟨0, IsCauchy.const 0⟩

@[simp] lemma zero_def (n : ℕ) : (0 : MyPrereal) n = 0 := by
  sorry

instance one : One MyPrereal where
  one := ⟨1, IsCauchy.const 1⟩

@[simp] lemma one_def (n : ℕ) : (1 : MyPrereal) n = 1 := by
  sorry

lemma IsCauchy.neg {x : ℕ → MyRat} (hx : IsCauchy x) : IsCauchy (-x) := by
  sorry

instance : Neg MyPrereal where
  neg x := ⟨-x, x.2.neg⟩

@[simp] lemma neg_def (x : MyPrereal) (n : ℕ) : (-x) n = -x n := by
  sorry

lemma neg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : -x ≈ -x' := by
  sorry

lemma IsCauchy.add {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x + y) := by
  sorry

instance : Add MyPrereal where
  add x y := ⟨x + y, x.2.add y.2⟩

instance : Sub MyPrereal where
  sub x y := x + -y

@[simp] lemma add_def (x y : MyPrereal) (n : ℕ) : (x + y) n = x n + y n := by
  sorry

@[simp] lemma sub_def (x y : MyPrereal) (n : ℕ) : (x - y) n = x n - y n := by
  sorry

lemma add_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x + y ≈ x' + y' := by
  sorry

lemma IsCauchy.mul {x y : ℕ → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x * y) := by
  sorry

instance : Mul MyPrereal where
  mul x y := ⟨x * y, x.2.mul y.2⟩

@[simp] lemma mul_def (x y : MyPrereal) (n : ℕ) : (x * y) n = x n * y n := by
  sorry

lemma mul_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x * y ≈ x' * y' := by
  sorry

lemma pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < |x n| := by
  sorry

lemma IsCauchy.inv {x : MyPrereal} (H : ¬(x ≈ 0)) : IsCauchy (x⁻¹) := by
  sorry

open Classical in
noncomputable def inv (x : MyPrereal) : MyPrereal := if H : ¬(x ≈ 0) then ⟨_, IsCauchy.inv H⟩ else 0

@[simp] lemma inv_def {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    inv x n = (x n)⁻¹ := by
  sorry

@[simp] lemma inv_def' {x : MyPrereal} (H : ¬(x ≈ 0)) (n : ℕ) :
    (⟨x⁻¹, IsCauchy.inv H⟩ : MyPrereal) n = (x n)⁻¹ := by
  sorry

lemma inv_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  sorry

end MyPrereal

open MyPrereal

abbrev MyReal := Quotient R_equiv

namespace MyReal

@[simp] lemma Quot_eq_Quotient (x : MyPrereal) : Quot.mk Setoid.r x = ⟦x⟧ := by
  sorry

instance zero : Zero MyReal where
  zero := ⟦0⟧

lemma zero_def : (0 : MyReal) = ⟦0⟧ := by
  sorry

instance one : One MyReal where
  one := ⟦1⟧

lemma one_def : (1 : MyReal) = ⟦1⟧ := by
  sorry

def neg : MyReal → MyReal := Quotient.map _ neg_quotient

instance : Neg MyReal where
  neg := neg

lemma neg_def (x : MyPrereal) : -(⟦x⟧ : MyReal) = ⟦-x⟧ := by
  sorry

def add : MyReal → MyReal → MyReal  := Quotient.map₂ _ add_quotient

instance : Add MyReal
  where add := add

lemma add_def (x y : MyPrereal) : (⟦x⟧ : MyReal) + (⟦y⟧ : MyReal) = ⟦x + y⟧ := by
  sorry

def mul : MyReal → MyReal → MyReal  := Quotient.map₂ _ mul_quotient

instance : Mul MyReal where
  mul := mul

lemma mul_def (x y : MyPrereal) : (⟦x⟧ : MyReal) * (⟦y⟧ : MyReal) = ⟦x * y⟧ := by
  sorry

noncomputable
def inv : MyReal → MyReal := Quotient.map _ inv_quotient

noncomputable
instance : Inv MyReal := ⟨inv⟩

lemma inv_def (x : MyPrereal) :
    (⟦x⟧ : MyReal)⁻¹ = ⟦MyPrereal.inv x⟧ := by
  sorry

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    intro a
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    intro a b
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try {ring_nf; simp [hε.le]})

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    intro a b c
    apply Quot.sound
    simp
    intro ε hε
    use 0
    intro n hn
    try { ring_nf; simp [hε.le] })

macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyReal where
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
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma sub_def (x y : MyPrereal) : (⟦x⟧ : MyReal) - (⟦y⟧ : MyReal) = ⟦x - y⟧ := by
  sorry

lemma zero_ne_one : (0 : MyReal) ≠ 1 := by
  sorry

lemma mul_inv_cancel (x : MyReal) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

noncomputable
instance field : Field MyReal where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    apply Quot.sound
    simp [MyPrereal.inv]
  qsmul := _
  nnqsmul := _

def k (x : MyRat) : MyReal := ⟦⟨_, IsCauchy.const x⟩⟧

@[simp] lemma k_zero : k 0 = 0 := by
  sorry

@[simp] lemma k_one : k 1 = 1 := by
  sorry

@[simp] lemma k_neg (x : MyRat) : k (-x) = -(k x) := by
  sorry

lemma k_add (x y : MyRat) : k (x + y) = k x + k y := by
  sorry

lemma k_sub (x y : MyRat) : k (x - y) = k x - k y := by
  sorry

lemma k_mul (x y : MyRat) : k (x * y) = k x * k y := by
  sorry

lemma k_injective : Function.Injective k := by
  sorry

lemma k_inv (x : MyRat) : k x⁻¹ = (k x)⁻¹ := by
  sorry

@[simp] lemma k_inj {x y : MyRat} : k x = k y ↔ x = y :=
  k_injective.eq_iff

end MyReal

namespace MyPrereal

def IsPos (x : MyPrereal) : Prop :=
  ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ x n

lemma pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
    ∃ N, ∀ n, N ≤ n → 0 < x n := by
  sorry

@[simp] lemma one_pos : IsPos 1 := by
  sorry

lemma not_isPos_zero {x : MyPrereal} (hx : x ≈ 0) : ¬ IsPos x := by
  sorry

lemma not_isPos_zero' {x : MyPrereal} (hx : (⟦x⟧ : MyReal) = 0) : ¬ IsPos x :=
  sorry

lemma not_equiv_zero_of_isPos {x : MyPrereal} (hx : IsPos x) : ¬(x ≈ 0) :=
  sorry

lemma not_equiv_zero_of_isPos' {x : MyPrereal} (hx : IsPos x) : (⟦x⟧ : MyReal) ≠ 0 :=
  sorry

lemma isPos_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsPos x) : IsPos x' := by
  sorry

lemma IsPos.add {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  sorry

lemma IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  sorry

def IsNonneg (x : MyPrereal) : Prop :=
  IsPos x ∨ x ≈ 0

lemma IsNonneg_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : IsNonneg x := by
  sorry

lemma IsNonneg_of_nonneg {x : MyPrereal} (N : ℕ) (hx : ∀ n, N ≤ n → 0 ≤ x n) : IsNonneg x := by
  sorry

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  sorry

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  sorry

lemma isNonneg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsNonneg x) : IsNonneg x' := by
  sorry

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyPrereal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x ≈ 0 := by
  sorry

lemma isNonneg_neg_of_not_isNonneg {x : MyPrereal} (hx : ¬ IsNonneg x) : IsNonneg (-x) := by
  sorry

end MyPrereal

namespace MyReal

def IsNonneg : MyReal →  Prop := Quotient.lift (MyPrereal.IsNonneg) <| fun _ _ h ↦
  propext ⟨fun hx ↦ isNonneg_quotient h hx, fun hy ↦ isNonneg_quotient (symm h) hy⟩

lemma isNonneg_def {x : MyPrereal} : IsNonneg ⟦x⟧ ↔ x.IsNonneg := by
  sorry

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  sorry

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyReal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  sorry

lemma IsNonneg.add {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  sorry

lemma IsNonneg.mul {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x * y) := by
  sorry

def le (x y : MyReal) : Prop := IsNonneg (y - x)

instance : LE MyReal where
  le := le

lemma le_def (x y : MyReal) : x ≤ y ↔ IsNonneg (y - x) := by
  sorry

lemma zero_le_iff_isNonneg (x : MyReal) : 0 ≤ x ↔ IsNonneg x := by
  sorry

lemma zero_le_one : (0 : MyReal) ≤ 1 := by
  sorry

lemma le_refl (x : MyReal) : x ≤ x := by
  sorry

lemma le_trans (x y z : MyReal) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry

lemma le_antisymm (x y : MyReal) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry

instance : PartialOrder MyReal where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyReal := ⟨zero_le_one⟩

lemma pos_def {x : MyPrereal} : IsPos x ↔ 0 < (⟦x⟧ : MyReal) := by
  sorry

lemma add_le_add_left (x y : MyReal) (h : x ≤ y) (t : MyReal) : x + t ≤ y + t := by
  sorry

lemma mul_nonneg (x y : MyReal) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  sorry

instance : IsOrderedAddMonoid MyReal where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyReal :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

lemma k_le_iff (x y : MyRat) : k x ≤ k y ↔ x ≤ y := by
  sorry

lemma k_lt_iff (x y : MyRat) : k x < k y ↔ x < y := by
  simp [lt_iff_le_and_ne, k_le_iff, k_injective.ne_iff]

lemma le_total (x y : MyReal) : x ≤ y ∨ y ≤ x := by
  sorry

noncomputable instance linearOrder : LinearOrder MyReal where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  sorry

noncomputable instance : IsStrictOrderedRing MyReal :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma myRat_dense_rat' (x : MyReal) {ε : MyRat} (hε : 0 < ε) : ∃ r, |x - k r| < k ε := by
  sorry

lemma myRat_dense_of_pos {x : MyReal} (hx : 0 < x) : ∃ r, 0 < r ∧ k r < x := by
  sorry

lemma myRat_dense_rat (x : MyReal) {ε : MyReal} (hε : 0 < ε) : ∃ r, |x - k r| < ε := by
  sorry

abbrev TendsTo (f : ℕ → MyReal) (x : MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ ε

lemma tendsTo_of_myRat_tendsTo {f : ℕ → MyReal} {x : MyReal}
    (h : ∀ (ε : MyRat), 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ k ε) : TendsTo f x := by
  sorry

abbrev IsConvergent (f : ℕ → MyReal) : Prop :=
  ∃ x, TendsTo f x

abbrev IsCauchy (f : ℕ → MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |f p - f q| ≤ ε

lemma tendsTo_myRat (x : MyPrereal) : TendsTo (fun n ↦ k (x n)) ⟦x⟧ := by
  sorry

section completeness

lemma ex_approx_punctual (x : MyReal) (n : ℕ) :
    ∃ (r : MyRat), |x - k r| < k ((MyRat.i (n+1))⁻¹) := by
  sorry

lemma ex_approx (f : ℕ → MyReal) :
    ∃ (g : ℕ → MyRat), ∀ n, |f n - k (g n)| < k ((MyRat.i (n+1))⁻¹) := by
  sorry

noncomputable def approx (f : ℕ → MyReal) : ℕ → MyRat := (ex_approx f).choose

lemma approx_spec (f : ℕ → MyReal) : ∀ n, |f n - k ((approx f) n)| < k ((MyRat.i (n+1))⁻¹) :=
  (ex_approx f).choose_spec

lemma archimedean (x : MyReal) : ∃ (n : ℕ), x ≤ k (MyRat.i (n + 1)) := by
  sorry

lemma archimedean0 {x : MyReal} (hx : 0 < x) : ∃ (n : ℕ), k (MyRat.i (n + 1))⁻¹ ≤ x := by
  sorry

lemma approx_cauchy {f : ℕ → MyReal} (hf : IsCauchy f) : _root_.IsCauchy (approx f) := by
  sorry

noncomputable
def IsCauchy.approx {f : ℕ → MyReal} (hf : IsCauchy f) : MyPrereal := ⟨_, approx_cauchy hf⟩

nonrec lemma IsCauchy.approx_spec {f : ℕ → MyReal} (hf : IsCauchy f) :
    ∀ n, |f n - k (hf.approx n)| < k ((MyRat.i (n+1))⁻¹) :=
  approx_spec f

theorem complete {f : ℕ → MyReal} (hf : IsCauchy f) : IsConvergent f := by
  sorry

end completeness

end MyReal
