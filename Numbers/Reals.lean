import Numbers.RationalsOrder

-- Lean already knows the absolute value (since there is an order on `MyRat`: `|x|` is defined as
-- `max (x, -x)`.
--See the files `Mathlib.Algebra.Order.*.Abs` for various properties
abbrev IsCauchy (x : MyNat → MyRat) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε

open Finset in
lemma IsCauchy.bounded {x : MyNat → MyRat} (hx : IsCauchy x) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B := by
  rcases hx 1 (by simp) with ⟨A, hA⟩
  let S' := (Finset.Icc 0 A).image (fun n ↦ |x n|)
  have hEmpty' : S'.Nonempty := image_nonempty.2 (by simp)
  let M := max' _ hEmpty'
  use M + 1
  constructor
  · suffices 0 ≤ M by linarith
    refine le_trans (abs_nonneg (x 0)) ?_
    apply le_max'
    simp [S']
    refine ⟨0, by simp, rfl⟩
  intro n
  rcases le_total n A with H | H
  · calc |x n| ≤ M := by
          apply le_max'
          simp [S']
          refine ⟨n, H, rfl⟩
         _ ≤ M + 1 := by linarith
  · calc |x n| = |x A + (x n - x A)| := by ring_nf
         _ ≤ |x A| + |x n - x A| := abs_add _ _
         _ ≤ M + 1 := by
                      gcongr
                      · apply le_max'
                        simp [S']
                        exact ⟨A, by simp, rfl⟩
                      · exact hA _ _ H rfl.le

-- When adding grind attributes to external lemmas, best to use "local".
-- These are not great `grind` attributes, but we will need better built-in support for inequalities
-- before you can do without them here.
attribute [local grind] le_of_max_le_left
attribute [local grind] le_of_max_le_right
attribute [local grind] le_trans

abbrev MyPrereal := {x // IsCauchy x}

namespace MyPrereal

open MyPrereal

--ignore the following
instance funLike : FunLike MyPrereal MyNat MyRat where
  coe := Subtype.val
  coe_injective' _ _ := Subtype.ext

lemma prop (x : MyPrereal) : ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |x p - x q| ≤ ε :=
  x.2

@[simp] lemma coe_apply {x : MyNat → MyRat} (hx : IsCauchy x) (n : MyNat) :
    (⟨x, hx⟩ : MyPrereal) n = x n := by
  rfl

lemma bounded (x : MyPrereal) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
  x.2.bounded

def R (x y : MyPrereal) : Prop := ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε

lemma R_def (x y : MyPrereal) : R x y ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma R_refl : ∀ x, R x x := by
  intro x ε hε
  use 0
  intro n _
  simpa using hε.le

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y H ε hε
  rcases H ε hε with ⟨N, HN⟩
  use N
  intro n hn
  rw [abs_sub_comm]
  exact HN n hn

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z hxy hyz ε hε
  rcases hxy (ε/2) (by linarith) with ⟨N, HN⟩
  rcases hyz (ε/2) (by linarith) with ⟨M, HM⟩
  use max N M
  intro n hn
  calc |x n - z n| = |(x n - y n) + (y n - z n)| := by ring_nf
       _ ≤ |x n - y n| + |(y n - z n)| := abs_add_le _ _
       _ ≤ (ε/2) + (ε/2) := by grw [HN n (by grind), HM n (by grind)]
       _ ≤ ε := by simp

instance R_equiv : Setoid MyPrereal where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

@[simp] lemma equiv_def (x y : MyPrereal) : x ≈ y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

@[simp] lemma equiv_def' (x y : MyPrereal) : Setoid.r x y ↔
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - y n| ≤ ε := by
  rfl

lemma IsCauchy.const (x : MyRat) : IsCauchy (fun _ ↦ x) := by
  intro ε hε
  use 0
  intro p q hp hq
  simp [hε.le]

instance zero : Zero MyPrereal where
  zero := ⟨0, IsCauchy.const 0⟩

@[simp] lemma zero_def (n : MyNat) : (0 : MyPrereal) n = 0 := by
  rfl

instance one : One MyPrereal where
  one := ⟨1, IsCauchy.const 1⟩

@[simp] lemma one_def (n : MyNat) : (1 : MyPrereal) n = 1 := by
  rfl

lemma IsCauchy.neg {x : MyNat → MyRat} (hx : IsCauchy x) : IsCauchy (-x) := by
  intro ε hε
  rcases hx ε hε with ⟨N, HN⟩
  use N
  intro p q hp hq
  calc |(-x) p - (-x) q| = |x q - x p| := by simp; ring_nf
       _ = |x p - x q| := abs_sub_comm _ _
       _ ≤ ε := HN p q hp hq

instance : Neg MyPrereal where
  neg x := ⟨-x, x.2.neg⟩

@[simp] lemma neg_def (x : MyPrereal) (n : MyNat) : (-x) n = -x n := by
  rfl

lemma neg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : -x ≈ -x' := by
  intro ε hε
  rcases h ε hε with ⟨N, HN⟩
  use N
  intro n hn
  simpa [← sub_eq_neg_add, abs_sub_comm] using HN n hn

lemma IsCauchy.add {x y : MyNat → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x + y) := by
  intro ε hε
  rcases hx (ε/2) (by linarith) with ⟨N, HN⟩
  rcases hy (ε/2) (by linarith) with ⟨M, HM⟩
  use max N M
  intro p q hp hq
  calc |(x + y) p - (x + y) q| = |(x p - x q) - (y q - y p)| := by simp; ring_nf
       _ ≤ |x p - x q| + |y p - y q| := by grw [abs_sub, abs_sub_comm (y p)]
       _ ≤ ε/2 + ε/2 := by grw [HN p q (by grind) (by grind), HM p q (by grind) (by grind)]
       _ = ε := by simp

instance : Add MyPrereal where
  add x y := ⟨x + y, x.2.add y.2⟩

instance : Sub MyPrereal where
  sub x y := x + -y

@[simp] lemma add_def (x y : MyPrereal) (n : MyNat) : (x + y) n = x n + y n := by
  rfl

@[simp] lemma sub_def (x y : MyPrereal) (n : MyNat) : (x - y) n = x n - y n := by
  rfl

lemma add_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x + y ≈ x' + y' := by
  intro ε hε
  rcases h (ε/2) (by linarith) with ⟨N, HN⟩
  rcases h' (ε/2) (by linarith) with ⟨N', HN'⟩
  use max N N'
  intro n hn
  calc |(x + y) n - (x' + y') n| = |(x n - x' n) - (y' n - y n)| := by simp; ring_nf
       _ ≤ |x n - x' n| + |y n - y' n| := by grw [abs_sub, abs_sub_comm (y n)]
       _ ≤ ε/2 + ε/2 := by grw [HN n (by grind), HN' n (by grind)]
       _ = ε := by simp

lemma IsCauchy.mul {x y : MyNat → MyRat} (hx : IsCauchy x) (hy : IsCauchy y) : IsCauchy (x * y) := by
  rcases hx.bounded with ⟨A, hApos, hA⟩
  rcases hy.bounded with ⟨B, hBpos, hB⟩
  intro ε hε
  rcases hx (ε/(2*B)) (div_pos hε (by linarith)) with ⟨N, HN⟩
  rcases hy (ε/(2*A)) (div_pos hε (by linarith)) with ⟨M, HM⟩
  use max N M
  intro p q hp hq
  calc |(x * y) p - (x * y) q| = |x p * y p - x q * y q| := by simp
       _ = |x p * (y p - y q) + y q * (x p - x q)| := by ring_nf
       _ ≤ |x p * (y p - y q)| + |y q * (x p - x q)| := abs_add _ _
       _ = |x p| * |(y p - y q)| + |y q| * |(x p - x q)| := by simp only [abs_mul]
       _ ≤ A * (ε/(2*A)) + B * (ε/(2*B)) := by grw [hA, hB, HN p q (by grind) (by grind),
                                              HM p q (by grind) (by grind)]
       _ = ε := by field_simp; ring

instance : Mul MyPrereal where
  mul x y := ⟨x * y, x.2.mul y.2⟩

@[simp] lemma mul_def (x y : MyPrereal) (n : MyNat) : (x * y) n = x n * y n := by
  rfl

lemma mul_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') ⦃y y' : MyPrereal⦄ (h' : y ≈ y') :
    x * y ≈ x' * y' := by
  intro ε hε
  rcases x.bounded with ⟨A, hApos, hA⟩
  rcases y'.bounded with ⟨B, hBpos, hB⟩
  rcases h (ε/(2*B)) (div_pos hε (by linarith)) with ⟨N, HN⟩
  rcases h' (ε/(2*A)) (div_pos hε (by linarith)) with ⟨N', HN'⟩
  use max N N'
  intro n hn
  calc |(x * y) n - (x' * y') n| = |x n * y n - x' n * y' n| := by simp
       _ = |x n * (y n - y' n) + y' n * (x n - x' n)| := by ring_nf
       _ ≤ |x n| * |(y n - y' n)| + |y' n| * |(x n - x' n)| := by grw [abs_add, abs_mul, abs_mul]
       _ ≤ A * (ε/(2*A)) + B * (ε/(2*B)) := by grw [hA, hB, HN' n (by grind), HN n (by grind)]
       _ = ε := by field_simp; ring

lemma pos_of_not_equiv_zero {x : MyPrereal} (H : ¬(x ≈ 0)) :
    ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ < |x n| := by
  simp only [equiv_def, zero_def, sub_zero, not_forall, not_exists, not_le] at H
  rcases H with ⟨δ, hδpos, h⟩
  rcases x.prop (δ/2) (by linarith) with ⟨N, HN⟩
  rcases h N with ⟨M, HNM, HM⟩
  refine ⟨δ/2, by linarith, M, fun n hn ↦ ?_⟩
  calc |x n| = |x M - (x M - x n)| := by ring_nf
      _ ≥ |x M| - |x M - x n| := abs_sub_abs_le_abs_sub _ _
      _ > δ - |x M - x n| := by gcongr
      _ ≥ δ - (δ/2) := by grw [HN M n HNM (by grind)]
      _ = δ/2 := by ring

lemma IsCauchy.inv {x : MyPrereal} (H : ¬(x ≈ 0)) : IsCauchy (x⁻¹) := by
  intro ε hε
  rcases pos_of_not_equiv_zero H with ⟨A, hApos, N, HN⟩
  rcases x.prop (ε*A*A) (by positivity) with ⟨M, hM⟩
  refine ⟨max N M, fun p q hp hq ↦ ?_⟩
  simp only [Pi.inv_apply]
  calc |(x p)⁻¹ - (x q)⁻¹| = |(x q - x p)/(x p * x q)| := by rw [inv_sub_inv
      (abs_ne_zero.1 (ne_of_gt (lt_trans hApos (HN _ (by grind)))))
      (abs_ne_zero.1 (ne_of_gt (lt_trans hApos (HN _ (by grind)))))]
      _ = |(x q - x p)|/(|x p| * |x q|) := by rw [abs_div, abs_mul]
      _ ≤ |(x q - x p)|/(A * A) := by gcongr
                                      · exact (HN p (by grind)).le
                                      · exact (HN q (by grind)).le
      _ ≤ (ε*A*A) / (A * A) := by grw [hM q p (by grind) (by grind)]
      _ = ε := by field_simp; ring

open Classical in
noncomputable def inv (x : MyPrereal) : MyPrereal := if H : ¬(x ≈ 0) then ⟨_, IsCauchy.inv H⟩ else 0

@[simp] lemma inv_def {x : MyPrereal} (H : ¬(x ≈ 0)) (n : MyNat) :
    inv x n = (x n)⁻¹ := by
  simp [inv, H]

@[simp] lemma inv_def' {x : MyPrereal} (H : ¬(x ≈ 0)) (n : MyNat) :
    (⟨x⁻¹, IsCauchy.inv H⟩ : MyPrereal) n = (x n)⁻¹ := by
  rfl

lemma inv_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') : inv x ≈ inv x' := by
  by_cases H : x ≈ 0
  · suffices H' : x' ≈ 0 by
      · simp [inv, H, H']
    exact _root_.trans (symm h) H
  have H' : ¬(x' ≈ 0) := fun H' ↦ H <| _root_.trans h H'
  simp only [inv, H, not_false_eq_true, reduceDIte, H', equiv_def]
  intro ε hε
  rcases pos_of_not_equiv_zero H with ⟨A, hApos, N, HN⟩
  rcases pos_of_not_equiv_zero H' with ⟨A', hA'pos, N', HN'⟩
  rcases (symm h) (ε*A*A') (by positivity) with ⟨M, hM⟩
  refine ⟨max M (max N N'), fun n hn ↦ ?_⟩
  simp only [coe_apply, Pi.inv_apply]
  calc |(x n)⁻¹ - (x' n)⁻¹| = |(x' n - x n)/(x n * x' n)| := by rw [inv_sub_inv
    (abs_ne_zero.1 <| ne_of_gt <| lt_trans hApos <| HN n (by grind))
    (abs_ne_zero.1 <| ne_of_gt <| lt_trans hA'pos <| HN' n (by grind))]
       _ = |x' n - x n|/(|x n| * |x' n|) := by rw [abs_div, abs_mul]
       _ ≤ |x' n - x n| / (A * A') := by gcongr
                                         · exact (HN n (by grind)).le
                                         · exact (HN' n (by grind)).le
       _ ≤ (ε*A*A') / (A * A') := by gcongr
                                     exact hM n (by grind)
       _ = ε := by field_simp; ring

end MyPrereal

open MyPrereal

abbrev MyReal := Quotient R_equiv

namespace MyReal

@[simp] lemma Quot_eq_Quotient (x : MyPrereal) : Quot.mk Setoid.r x = ⟦x⟧ := by
  rfl

instance zero : Zero MyReal where
  zero := ⟦0⟧

lemma zero_def : (0 : MyReal) = ⟦0⟧ := by
  rfl

instance one : One MyReal where
  one := ⟦1⟧

lemma one_def : (1 : MyReal) = ⟦1⟧ := by
  rfl

def neg : MyReal → MyReal := Quotient.map _ neg_quotient

instance : Neg MyReal where
  neg := neg

lemma neg_def (x : MyPrereal) : -(⟦x⟧ : MyReal) = ⟦-x⟧ := by
  rfl

def add : MyReal → MyReal → MyReal  := Quotient.map₂ _ add_quotient

instance : Add MyReal
  where add := add

lemma add_def (x y : MyPrereal) : (⟦x⟧ : MyReal) + (⟦y⟧ : MyReal) = ⟦x + y⟧ := by
  rfl

def mul : MyReal → MyReal → MyReal  := Quotient.map₂ _ mul_quotient

instance : Mul MyReal where
  mul := mul

lemma mul_def (x y : MyPrereal) : (⟦x⟧ : MyReal) * (⟦y⟧ : MyReal) = ⟦x * y⟧ := by
  rfl

noncomputable
def inv : MyReal → MyReal := Quotient.map _ inv_quotient

noncomputable
instance : Inv MyReal := ⟨inv⟩

lemma inv_def (x : MyPrereal) :
    (⟦x⟧ : MyReal)⁻¹ = ⟦MyPrereal.inv x⟧ := by
  rfl

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

lemma sub_def (x y : MyPrereal) : (⟦x⟧ : MyReal) - (⟦y⟧ : MyReal) = ⟦x - y⟧ := by
  rfl

lemma zero_ne_one : (0 : MyReal) ≠ 1 := by
  simp only [zero_def, one_def, ne_eq, Quotient.eq, equiv_def', MyPrereal.zero_def,
    MyPrereal.one_def, zero_sub, abs_neg, abs_one, not_forall, not_exists, not_le]
  exact ⟨1/2, by simp, fun n ↦ ⟨n, le_rfl, by linarith⟩⟩

lemma mul_inv_cancel (x : MyReal) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  revert hx
  refine Quot.induction_on x ?_
  intro x hx
  replace hx : ¬(x ≈ 0) := fun h ↦ hx <| by simpa [← Quotient.eq_iff_equiv, zero_def] using h
  rcases pos_of_not_equiv_zero hx with ⟨δ, hδpos, N, HN⟩
  apply Quot.sound
  simp only [equiv_def', MyPrereal.mul_def, MyPrereal.one_def]
  intro ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  convert hε.le
  simp only [hx, not_false_eq_true, MyPrereal.inv_def, abs_eq_zero]
  suffices x n ≠ 0 by field_simp
  exact abs_ne_zero.1 <| ne_of_gt <| lt_trans hδpos <| HN n hn

noncomputable
instance field : Field MyReal where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_inv_cancel := mul_inv_cancel
  inv_zero := by
    apply Quot.sound
    simp only [MyPrereal.inv, Setoid.refl, not_true_eq_false, reduceDIte, equiv_def',
      MyPrereal.zero_def, sub_self, abs_zero]
    intro ε hε
    exact ⟨0, fun _ _ ↦ hε.le⟩
  qsmul := _
  nnqsmul := _

def k (x : MyRat) : MyReal := ⟦⟨_, IsCauchy.const x⟩⟧

@[simp] lemma k_zero : k 0 = 0 := by
  rfl

@[simp] lemma k_one : k 1 = 1 := by
  rfl

@[simp] lemma k_neg (x : MyRat) : k (-x) = -(k x) := by
  rfl

lemma k_add (x y : MyRat) : k (x + y) = k x + k y := by
  apply Quot.sound
  apply R_refl

lemma k_sub (x y : MyRat) : k (x - y) = k x - k y := by
  apply Quot.sound
  apply R_refl

lemma k_mul (x y : MyRat) : k (x * y) = k x * k y := by
  apply Quot.sound
  apply R_refl

lemma k_injective : Function.Injective k := by
  intro x y h
  rw [← sub_eq_zero]
  by_contra! habs
  simp only [k, Quotient.eq, equiv_def'] at h
  have := lt_of_le_of_ne (by simp) (abs_ne_zero.2 habs).symm
  rcases h (|x - y|/2) (by linarith) with ⟨N, HN⟩
  specialize HN N le_rfl
  simp only [coe_apply] at HN
  linarith

lemma k_inv (x : MyRat) : k x⁻¹ = (k x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← mul_eq_one_iff_eq_inv₀ (k_injective.ne hx), ← k_mul]
  field_simp

@[simp] lemma k_inj {x y : MyRat} : k x = k y ↔ x = y :=
  k_injective.eq_iff

end MyReal

namespace MyPrereal

def IsPos (x : MyPrereal) : Prop :=
  ∃ δ, 0 < δ ∧ ∃ N, ∀ n, N ≤ n → δ ≤ x n

lemma pos_of_isPos {x : MyPrereal} (hx : IsPos x) :
    ∃ N, ∀ n, N ≤ n → 0 < x n := by
  rcases hx with ⟨δ, hδpos, N, HN⟩
  exact ⟨N, fun n hn ↦ lt_of_lt_of_le hδpos (HN n hn)⟩

@[simp] lemma one_pos : IsPos 1 :=
  ⟨1, by simp, 0, fun _ _ ↦ by simp⟩

lemma not_isPos_zero {x : MyPrereal} (hx : x ≈ 0) : ¬ IsPos x := by
  intro ⟨δ, hδpos, N, HN⟩
  rcases hx (δ/2) (by linarith) with ⟨M, HM⟩
  specialize HN (max N M) (by simp)
  specialize HM (max N M) (by simp)
  simp only [zero_def, sub_zero, abs_le] at HM
  linarith

lemma not_isPos_zero' {x : MyPrereal} (hx : (⟦x⟧ : MyReal) = 0) : ¬ IsPos x :=
  not_isPos_zero (Quotient.eq_iff_equiv.1 hx)

lemma not_equiv_zero_of_isPos {x : MyPrereal} (hx : IsPos x) : ¬(x ≈ 0) :=
  fun h ↦ not_isPos_zero h hx

lemma not_equiv_zero_of_isPos' {x : MyPrereal} (hx : IsPos x) : (⟦x⟧ : MyReal) ≠ 0 :=
  fun h ↦ not_isPos_zero' h hx

lemma isPos_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsPos x) : IsPos x' := by
  rcases hx with ⟨δ, hδpos, N, HN⟩
  rcases h (δ/2) (by linarith) with ⟨M, HM⟩
  refine ⟨δ/2, by linarith, max N M, fun n hn ↦ ?_⟩
  calc x' n = x n - (x n - x' n) := by ring
       _ ≥ δ - (x n - x' n) := by grw [HN n (by grind)]
       _ ≥ δ - δ/2 := by grw [(abs_le.1 (HM n (by grind))).2]
       _ = δ/2 := by ring

lemma IsPos.add {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  rcases hx with ⟨A, hApos, N, HN⟩
  rcases hy with ⟨B, hBpos, M, HM⟩
  refine ⟨A + B, by linarith, max N M, fun n hn ↦ ?_⟩
  grw [add_def, HN n (by grind), HM n (by grind)]

lemma IsPos.mul {x y : MyPrereal} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  rcases hx with ⟨A, hApos, N, HN⟩
  rcases hy with ⟨B, hBpos, M, HM⟩
  refine ⟨A * B, mul_pos hApos hBpos, max N M, fun n hn ↦ ?_⟩
  grw [mul_def, HN n (by grind), HM n (by grind)]
  linarith [HN n (by grind)]

def IsNonneg (x : MyPrereal) : Prop :=
  IsPos x ∨ x ≈ 0

lemma IsNonneg_of_equiv_zero {x : MyPrereal} (hx : x ≈ 0) : IsNonneg x := by
  simp [IsNonneg, hx]

lemma IsNonneg_of_nonneg {x : MyPrereal} (N : MyNat) (hx : ∀ n, N ≤ n → 0 ≤ x n) : IsNonneg x := by
  by_cases h : x ≈ 0
  · exact IsNonneg_of_equiv_zero h
  rcases pos_of_not_equiv_zero h with ⟨δ, hδpos, M, HM⟩
  left
  refine ⟨δ, hδpos, max N M, fun n hn ↦ ?_⟩
  rcases lt_abs.1 (HM n (by grind)) with H | H
  · linarith
  · linarith [hx n (by grind)]

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  simp [IsNonneg]

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  simp [IsNonneg]

lemma isNonneg_quotient ⦃x x' : MyPrereal⦄ (h : x ≈ x') (hx : IsNonneg x) : IsNonneg x' := by
  by_cases h0 : x ≈ 0
  · exact IsNonneg_of_equiv_zero (_root_.trans (symm h) h0)
  suffices ¬(x' ≈ 0) by
    · simp only [IsNonneg, h0, or_false] at hx
      simpa [IsNonneg, this] using isPos_quotient h hx
  exact fun h0' ↦ h0 <| _root_.trans h h0'

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyPrereal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x ≈ 0 := by
  by_contra H
  have H' : ¬(-x ≈ 0) := fun h0 ↦ H <| by simpa [neg_quotient] using h0
  simp only [IsNonneg, H, or_false, H'] at h h'
  rcases h with ⟨δ, hδpos, N, HN⟩
  rcases h' with ⟨δ', hδ'pos, N', HN'⟩
  specialize HN (max N N') (by exact le_max_left N N')
  specialize HN' (max N N') (by exact le_max_right N N')
  simp only [neg_def] at HN'
  linarith

lemma isNonneg_neg_of_not_isNonneg {x : MyPrereal} (hx : ¬ IsNonneg x) : IsNonneg (-x) := by
  simp only [IsNonneg, not_or] at hx
  rcases hx with ⟨hx1, hx2⟩
  simp only [IsPos, not_exists, not_and, not_forall, not_le] at hx1
  rcases pos_of_not_equiv_zero hx2 with ⟨δ, hδpos, N, HN⟩
  rcases x.prop (δ/2) (by linarith) with ⟨M, HM⟩
  rcases hx1 δ (by linarith) (max N M) with ⟨R, HRMN, HR⟩
  replace HR : -x R > δ := by
    have := lt_abs.1 (HN R (by grind))
    simp only [not_lt_of_ge HR.le, false_or] at this
    linarith
  left
  refine ⟨δ/2, by linarith, max R (max N M), fun n hn ↦ ?_⟩
  calc -x n = x R - x n + -x R := by ring
       _ ≥ -(δ / 2) + δ := by grw [(abs_le.1 (HM R n (by grind) (by grind))).1, HR]
       _ = δ / 2 := by ring

end MyPrereal

namespace MyReal

def IsNonneg : MyReal →  Prop := Quotient.lift (MyPrereal.IsNonneg) <| fun _ _ h ↦
  propext ⟨fun hx ↦ isNonneg_quotient h hx, fun hy ↦ isNonneg_quotient (symm h) hy⟩

lemma isNonneg_def {x : MyPrereal} : IsNonneg ⟦x⟧ ↔ x.IsNonneg := by
  rfl

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  simp [zero_def, isNonneg_def]

lemma eq_zero_of_isNonneg_of_isNonneg_neg {x : MyReal} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  revert h h'
  refine Quot.induction_on x ?_
  intro a h h'
  rw [zero_def, Quot_eq_Quotient, Quotient.eq_iff_equiv]
  exact MyPrereal.eq_zero_of_isNonneg_of_isNonneg_neg (by simpa) (by simpa)

lemma IsNonneg.add {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  by_cases hx0 : x = 0
  · simpa [hx0]
  by_cases hy0 : y = 0
  · simpa [hy0]
  revert hx hy hx0 hy0
  refine Quot.induction_on₂ x y ?_
  intro a b ha hb ha0 hb0
  replace ha0 : ¬(a ≈ 0) := fun h ↦ ha0 <| Quotient.eq_iff_equiv.2 h
  replace hb0 : ¬(b ≈ 0) := fun h ↦ hb0 <| Quotient.eq_iff_equiv.2 h
  simp only [Quot_eq_Quotient, add_def, isNonneg_def]
  left
  simp only [Quot_eq_Quotient, isNonneg_def, MyPrereal.IsNonneg, ha0, or_false] at ha
  simp only [Quot_eq_Quotient, isNonneg_def, MyPrereal.IsNonneg, hb0, or_false] at hb
  exact IsPos.add ha hb

lemma IsNonneg.mul {x y : MyReal} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  revert hx hy hx0 hy0
  refine Quot.induction_on₂ x y ?_
  intro a b ha hb ha0 hb0
  replace ha0 : ¬(a ≈ 0) := fun h ↦ ha0 <| Quotient.eq_iff_equiv.2 h
  replace hb0 : ¬(b ≈ 0) := fun h ↦ hb0 <| Quotient.eq_iff_equiv.2 h
  simp only [Quot_eq_Quotient, mul_def, isNonneg_def]
  left
  simp only [Quot_eq_Quotient, isNonneg_def, MyPrereal.IsNonneg, ha0, or_false] at ha
  simp only [Quot_eq_Quotient, isNonneg_def, MyPrereal.IsNonneg, hb0, or_false] at hb
  exact IsPos.mul ha hb

def le (x y : MyReal) : Prop := IsNonneg (y - x)

instance : LE MyReal where
  le := le

lemma le_def (x y : MyReal) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_isNonneg (x : MyReal) : 0 ≤ x ↔ IsNonneg x := by
  simp [le_def]

lemma zero_le_one : (0 : MyReal) ≤ 1 := by
  simp [le_def, one_def, isNonneg_def]

lemma le_refl (x : MyReal) : x ≤ x := by
  simp [le_def]

lemma le_trans (x y z : MyReal) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp only [le_def] at *
  convert h1.add h2 using 1
  ring

lemma le_antisymm (x y : MyReal) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp only [le_def] at *
  refine (sub_eq_zero.1 (eq_zero_of_isNonneg_of_isNonneg_neg hxy ?_)).symm
  convert hyx using 1
  ring

instance : PartialOrder MyReal where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyReal := ⟨zero_le_one⟩

lemma pos_def {x : MyPrereal} : IsPos x ↔ 0 < (⟦x⟧ : MyReal) := by
  rw [lt_iff_le_and_ne, zero_le_iff_isNonneg, isNonneg_def, MyPrereal.IsNonneg, ne_comm]
  refine ⟨fun h ↦ ⟨by left; assumption, not_equiv_zero_of_isPos' h⟩, fun ⟨h1, h2⟩ ↦ ?_⟩
  simpa [← Quotient.eq_iff_equiv, ← zero_def, h2] using h1

lemma add_le_add_left (x y : MyReal) (h : x ≤ y) (t : MyReal) : t + x ≤ t + y := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyReal) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp only [le_def, sub_zero] at *
  exact IsNonneg.mul hx hy

instance : IsOrderedAddMonoid MyReal where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyReal :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

lemma k_le_iff (x y : MyRat) : k x ≤ k y ↔ x ≤ y := by
  by_cases H : x = y
  · simp [H]
  refine ⟨fun h ↦ ?_, fun h ↦  ?_⟩
  · simp only [k, le_def, sub_def, isNonneg_def] at h
    have : ¬((⟨_, IsCauchy.const y⟩ : MyPrereal) - ⟨_, IsCauchy.const x⟩ ≈ 0) := fun h0 ↦ by
      apply (k_injective.ne H).symm
      rwa [← Quotient.eq_iff_equiv, ← sub_def, ← zero_def, sub_eq_zero] at h0
    simp only [MyPrereal.IsNonneg, this, or_false] at h
    rcases pos_of_isPos h with ⟨N, HN⟩
    refine le_of_lt (by simpa using HN N le_rfl)
  · simp only [le_def, k, sub_def, isNonneg_def]
    left
    exact ⟨y - x, sub_pos_of_lt (lt_of_le_of_ne h H), 0, fun n _ ↦ by simp⟩

lemma k_lt_iff (x y : MyRat) : k x < k y ↔ x < y := by
  simp [lt_iff_le_and_ne, k_le_iff, k_injective.ne_iff]

lemma le_total (x y : MyReal) : x ≤ y ∨ y ≤ x := by
  by_cases h1 : IsNonneg (y - x)
  · left
    exact h1
  · right
    by_cases h2 : IsNonneg (x - y)
    · exact h2
    · exfalso
      revert h1 h2
      refine Quot.induction_on₂ x y ?_
      intro a b ha hb
      simp only [Quot_eq_Quotient,sub_def, isNonneg_def] at ha
      simp only [Quot_eq_Quotient] at hb
      apply hb
      rw [(show (⟦a⟧ : MyReal) - ⟦b⟧ = -(⟦b⟧ - ⟦a⟧) by ring), sub_def, neg_def, isNonneg_def]
      exact isNonneg_neg_of_not_isNonneg ha

noncomputable instance linearOrder : LinearOrder MyReal where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyReal) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at ha hb ⊢
  rcases ha with ⟨ha, ha'⟩
  rcases hb with ⟨hb, hb'⟩
  refine ⟨?_, by aesop⟩
  rw [zero_le_iff_isNonneg] at ha hb ⊢
  exact IsNonneg.mul ha hb

noncomputable instance : IsStrictOrderedRing MyReal :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma myRat_dense_rat' (x : MyReal) {ε : MyRat} (hε : 0 < ε) : ∃ r, |x - k r| < k ε := by
  refine Quot.induction_on x ?_
  intro a
  rcases a.prop (ε/2) (by linarith) with ⟨N, HN⟩
  refine ⟨a N, ?_⟩
  rw [Quot_eq_Quotient, abs_lt, neg_lt_sub_iff_lt_add]
  constructor
  · rw [← sub_pos, k, k, add_def, sub_def, ← pos_def]
    refine ⟨ε/2, by linarith, N, fun n hn ↦ ?_⟩
    simp only [MyPrereal.sub_def, MyPrereal.add_def, coe_apply]
    linarith [abs_le.1 (HN n N hn le_rfl)]
  · rw [← sub_pos, k, k, sub_def, sub_def, ← pos_def]
    refine ⟨ε/2, by linarith, N, fun n hn ↦ ?_⟩
    simp only [MyPrereal.sub_def, coe_apply]
    linarith [abs_le.1 (HN n N hn le_rfl)]

lemma myRat_dense_of_pos {x : MyReal} (hx : 0 < x) : ∃ r, 0 < r ∧ k r < x := by
  revert hx
  refine Quot.induction_on x ?_
  intro a ha
  simp only [Quot_eq_Quotient, ← pos_def] at ha
  rcases ha with ⟨δ, hδpos, N, HN⟩
  refine ⟨δ/2, by linarith, ?_⟩
  rw [Quot_eq_Quotient, ← sub_pos, k, sub_def, ← pos_def]
  refine ⟨δ/2, by linarith, N, fun n hn ↦ ?_⟩
  simp only [MyPrereal.sub_def, coe_apply]
  linarith [HN n hn]

lemma myRat_dense_rat (x : MyReal) {ε : MyReal} (hε : 0 < ε) : ∃ r, |x - k r| < ε := by
  rcases myRat_dense_of_pos hε with ⟨δ, hδpos, hδ⟩
  rcases myRat_dense_rat' x hδpos with ⟨r, hr⟩
  refine ⟨r, by linarith⟩

abbrev TendsTo (f : MyNat → MyReal) (x : MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ ε

lemma tendsTo_of_myRat_tendsTo {f : MyNat → MyReal} {x : MyReal}
    (h : ∀ (ε : MyRat), 0 < ε → ∃ N, ∀ n, N ≤ n → |f n - x| ≤ k ε) : TendsTo f x := by
  intro ε hε
  rcases myRat_dense_of_pos hε with ⟨δ, hδpos, hδ⟩
  rcases h δ hδpos with ⟨N, HN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  linarith [HN n hn]

abbrev IsConvergent (f : MyNat → MyReal) : Prop :=
  ∃ x, TendsTo f x

abbrev IsCauchy (f : MyNat → MyReal) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ p q, N ≤ p → N ≤ q → |f p - f q| ≤ ε

lemma tendsTo_myRat (x : MyPrereal) : TendsTo (fun n ↦ k (x n)) ⟦x⟧ := by
  apply tendsTo_of_myRat_tendsTo
  intro ε hε
  rcases x.prop ε hε with ⟨N, HN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [k, k, sub_def, abs_le]
  constructor
  · rw [← sub_nonneg, sub_neg_eq_add, add_def, zero_le_iff_isNonneg, isNonneg_def]
    refine IsNonneg_of_nonneg N (fun m hm ↦ ?_)
    simp only [MyPrereal.add_def, MyPrereal.sub_def, coe_apply]
    linarith [abs_le.1 (HN n m hn hm)]
  · rw [← sub_nonneg, sub_def, zero_le_iff_isNonneg, isNonneg_def]
    refine IsNonneg_of_nonneg N (fun m hm ↦ ?_)
    simp only [MyPrereal.sub_def, coe_apply]
    linarith [abs_le.1 (HN n m hn hm)]

section completeness

lemma ex_approx_punctual (x : MyReal) (n : MyNat) :
    ∃ (r : MyRat), |x - k r| < k ((MyRat.i (n+1))⁻¹) := by
  refine myRat_dense_rat' x ?_
  rw [inv_pos, ← MyRat.i_zero, MyRat.i_lt_iff]
  simp

lemma ex_approx (f : MyNat → MyReal) :
    ∃ (g : MyNat → MyRat), ∀ n, |f n - k (g n)| < k ((MyRat.i (n+1))⁻¹) := by
  choose g h using (fun n ↦ ex_approx_punctual (f n) n)
  refine ⟨g, h⟩

noncomputable def approx (f : MyNat → MyReal) : MyNat → MyRat := (ex_approx f).choose

lemma approx_spec (f : MyNat → MyReal) : ∀ n, |f n - k ((approx f) n)| < k ((MyRat.i (n+1))⁻¹) :=
  (ex_approx f).choose_spec

lemma archimedean (x : MyReal) : ∃ (n : MyNat), x ≤ k (MyRat.i (n + 1)) := by
  refine Quot.induction_on x ?_
  intro x
  rcases x.bounded with ⟨r, hrpos, hr⟩
  rcases MyRat.archimedean r with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simp only [Quot_eq_Quotient, k, le_def, sub_def]
  refine IsNonneg_of_nonneg 0 (fun m _ ↦ ?_)
  simp only [MyPrereal.sub_def, coe_apply, sub_nonneg]
  refine _root_.le_trans (abs_le.1 (hr m)).2 (_root_.le_trans hn ?_)
  rw [MyRat.i_le_iff]
  simp

lemma archimedean0 {x : MyReal} (hx : 0 < x) : ∃ (n : MyNat), k (MyRat.i (n + 1))⁻¹ ≤ x := by
  rcases archimedean |x⁻¹| with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rwa [abs_inv, inv_le_comm₀ (abs_pos_of_pos hx), ← k_inv, abs_of_pos hx] at hn
  rw [← k_zero, k_lt_iff, ← MyRat.i_zero, MyRat.i_lt_iff]
  simp

lemma approx_cauchy {f : MyNat → MyReal} (hf : IsCauchy f) : _root_.IsCauchy (approx f) := by
  intro ε hε
  have : 0 < k ε := by simpa [← k_lt_iff] using hε
  rcases hf ((k ε)/3) (by linarith) with ⟨N, HN⟩
  rcases archimedean0 (x := (k ε)/3) (by linarith) with ⟨M, HM⟩
  refine ⟨max M N, fun p q hp hq ↦ ?_⟩
  rw [abs_le, ← k_le_iff, ← k_le_iff, k_neg, ← abs_le]
  have HP : k (MyRat.i (p + 1))⁻¹ ≤ k (MyRat.i (M + 1))⁻¹ := by
    refine (k_le_iff _ _).2 (inv_anti₀ ?_ ?_)
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      simp
    · rw [MyRat.i_le_iff]
      simp only [add_le_add_iff_right]
      grind
  have HQ : k (MyRat.i (q + 1))⁻¹ ≤ k (MyRat.i (M + 1))⁻¹ := by
    refine (k_le_iff _ _).2 (inv_anti₀ ?_ ?_)
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      simp
    · rw [MyRat.i_le_iff]
      simp only [add_le_add_iff_right]
      grind
  calc |k (approx f p - approx f q)| = |k (approx f p) - k (approx f q)| := by rw [k_sub]
       _ = |-(f p - k (approx f p)) + (f p - f q) + (f q - k (approx f q))| := by ring_nf
       _ ≤ |f p - k (approx f p)| + |f p - f q| + |f q - k (approx f q)| := by
        grw [abs_add, abs_add, abs_neg]
       _ ≤ |f p - k (approx f p)| + ((k ε)/3) + |f q - k (approx f q)| := by
        grw [HN p q (by grind) (by grind)]
       _ ≤ (k ε)/3 + (k ε)/3 + (k ε)/3 := by
        grw [_root_.le_trans (_root_.le_trans (approx_spec f p).le HP) HM,
          _root_.le_trans (_root_.le_trans (approx_spec f q).le HQ) HM]
       _ = k ε := by ring

noncomputable
def IsCauchy.approx {f : MyNat → MyReal} (hf : IsCauchy f) : MyPrereal := ⟨_, approx_cauchy hf⟩

nonrec lemma IsCauchy.approx_spec {f : MyNat → MyReal} (hf : IsCauchy f) :
    ∀ n, |f n - k (hf.approx n)| < k ((MyRat.i (n+1))⁻¹) :=
  approx_spec f

theorem complete {f : MyNat → MyReal} (hf : IsCauchy f) : IsConvergent f := by
  let x := hf.approx
  refine ⟨⟦x⟧, ?_⟩
  intro ε hε
  rcases tendsTo_myRat x (ε/2) (by linarith) with ⟨N, HN⟩
  rcases archimedean0 (x := ε/2) (by linarith) with ⟨M, HM⟩
  refine ⟨max N M, fun n hn ↦ ?_⟩
  have H : k (MyRat.i (n + 1))⁻¹ ≤ k (MyRat.i (M + 1))⁻¹ := by
    refine (k_le_iff _ _).2 (inv_anti₀ ?_ ?_)
    · rw [← MyRat.i_zero, MyRat.i_lt_iff]
      simp
    · rw [MyRat.i_le_iff]
      simp only [add_le_add_iff_right]
      grind
  calc |f n - ⟦x⟧| = |f n - k (x n) + (k (x n) - ⟦x⟧)| := by ring_nf
       _ ≤ |f n - k (x n)| + |k (x n) - ⟦x⟧| := by grw [abs_add]
       _ ≤ ε/2 + ε/2 := by grw [HN n (by grind),
        _root_.le_trans (_root_.le_trans (hf.approx_spec n).le H) HM]
       _ = ε := by ring

end completeness

end MyReal
