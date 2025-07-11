import Numbers.Solutions.rationals_no_sorry

/-!

# The order on the rationals

We prove that the rationals are a total order, and also that the ordering
plays well with the ring structure.

-/

namespace MyRat

/-

## Nonnegativitiy on the rationals

-/
-- this definition is somehow bad as it asks for proofs of b≠0 and b>0
def IsNonneg (x : MyRat) : Prop :=
  ∃ (a b : MyInt) (_ : 0 ≤ a) (hb : 0 < b), x = ⟦(a, ⟨b, hb.ne'⟩)⟧

/-

### Relationship with 0 and 1

-/

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  use 0, 1
  simp [zero_def]

@[simp]
lemma one_nonneg : IsNonneg 1 := by
  use 1, 1
  simp [one_def]

/-

## Relationship with neg

-/

lemma nonneg_neg {x : MyRat} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  -- manually reduce it to a question about integers
  rcases h with ⟨a, b, ha, hb, rfl⟩
  rcases h' with ⟨c, d, hc, hd, h⟩
  -- currently a question about equalities of equivalence classes following from other equalities
  -- Turn all these hypotheses and conclusions into concrete statements about integers
  apply Quotient.eq.2
  apply Quotient.eq.1 at h
  -- They're unreadable so let the simplifier tidy them up
  simp_all
  nlinarith

-- this one is also useful
lemma nonneg_neg_of_not_nonneg {x : MyRat} : ¬ IsNonneg x → IsNonneg (-x) := by
  refine Quot.induction_on x ?_
  clear x
  rintro ⟨a, ⟨b, hb⟩⟩ h
  simp [IsNonneg] at *
  -- This is as you can imagine a big case bash depending on the signs of a and b.
  -- The question is to build a nonnegative prerational that maps onto -(a/b)
  -- given that a/b is not nonnegative. We argue by cases on whether a is nonnegative.
  by_cases ha : 0 ≤ a
  -- In  a>=0 then the prerational we're going to use is a/(-b).
  · use a, ha, -b
    -- We know x is not nonnegative. So if a>=0 then b had better be <0
    have foo : 0 < -b := by
      -- because if b>=0 then x=a/b is a nonnegative prerational, a contradiction.
      by_contra!
      exact h a b (lt_of_le_of_ne (neg_nonpos.1 this) hb.symm) ha <| mul_comm _ _
    clear h -- don't need hypothesis that x is not nonnegative any more.
    -- A machine can do the rest.
    use foo
    apply Quotient.eq.2 -- remaining goal of the form ⟦(p,q)⟧=⟦(r,s)⟧ so turn it into a question
                        -- about integers being equivalent
    simp [mul_comm] -- the simplifier reduces this random question to `mul_comm` on `MyInt`
  · push_neg at ha
    use -a, (neg_nonneg.2 ha.le)
    have foo : ¬ 0 < -b := by
      -- foo true because other wise you can use h to get a contradiction
      intro hb
      exact h (-a) (-b) hb (neg_nonneg.2 ha.le) (by ring)
    use b, (pos_of_neg_neg (lt_of_le_of_ne (by linarith) (by grind)))
    apply Quotient.eq.2
    simp [mul_comm]
/-

## Relationship with addition

-/

lemma isNonneg_add_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  rcases hx with ⟨a, b, ha, hb, rfl⟩
  rcases hy with ⟨c, d, hc, hd, rfl⟩
  use a * d + b * c, b * d, (by nlinarith), (by nlinarith)
  apply Quotient.eq.2
  simp
  ring

/-

## Relationship with multiplication

-/

-- github copilot wrote the first proof I had of this
lemma isNonneg_mul_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  rcases hx with ⟨a, b, ha, hb, rfl⟩
  rcases hy with ⟨c, d, hc, hd, rfl⟩
  use a * c, b * d, by nlinarith, by nlinarith
  apply Quotient.eq.2
  simp
  ring

/-

## Relationship with inverse

-/

lemma isNonneg_inv_isNonneg {x : MyRat} (hx : IsNonneg x) :
    IsNonneg x⁻¹ := by
  rcases hx with ⟨a, b, (ha : 0 ≤ a), (hb2 : 0 < b), rfl⟩
  rcases eq_or_ne a 0 with (rfl | ha2)
  · use 0, 1, by simp
    simp
    apply Quot.sound
    simp [MyPrerat.inv]
  · use b, a, by linarith, lt_of_le_of_ne ha ha2.symm
    apply Quotient.eq.2
    simp [MyPrerat.inv, ha2, mul_comm]

/-!

## The linear order on the rationals

I think that's it for non-negativity on the rationals. Let's see
if we can use those theorems about nonnegativity to prove that
the raionals are a linear order.

-/

/-- Our definition of x ≤ y on the rationals. -/
def le (x y : MyRat) : Prop := IsNonneg (y - x)

instance : LE MyRat where
  le := le

lemma le_def (x y : MyRat) : x ≤ y ↔ IsNonneg (y - x) := by
  rfl

lemma zero_le_iff_IsNonneg (x : MyRat) : 0 ≤ x ↔ IsNonneg x := by
  simp [le_def]
/-!

We now develop some basic theory of `≤` on the rationals.
Let's warm up with 0 ≤ 1.

-/

lemma zero_le_one : (0 : MyRat) ≤ 1 := by
  simp [le_def]

/-!

There's no point proving 0 ≤ 0 and 1 ≤ 1, we may as well prove reflexivity
in general.

-/

lemma le_refl (x : MyRat) : x ≤ x := by
  simp [le_def]

/-!

Next is transitivitiy

-/

lemma le_trans (x y z : MyRat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  simp [le_def] at *
  convert isNonneg_add_isNonneg h1 h2 using 1
  ring

/-!

Next is antisymmetry

-/

lemma le_antisymm (x y : MyRat) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  simp [le_def] at *
  have foo : IsNonneg (-(y - x)) := by
    convert hyx using 1
    ring
  have := nonneg_neg hxy foo
  linear_combination -(1 * this)

instance : PartialOrder MyRat where
  le := (. ≤ .)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

instance : ZeroLEOneClass MyRat := ⟨zero_le_one⟩

lemma add_le_add_left (x y : MyRat) (h : x ≤ y) (t : MyRat) : t + x ≤ t + y := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyRat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  simp_all [le_def]
  convert isNonneg_mul_isNonneg hx hy using 1

instance : IsOrderedAddMonoid MyRat where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyRat :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

/-!

The interplay between the ordering and the natural maps from
the naturals and integers to the rationals.

-/

-- let's do `j` first, then we can use it for `i`

/-- The natural map from the integers to the rationals
preserves and reflects `≤`. -/
lemma j_le_iff (p q : MyInt) : j p ≤ j q ↔ p ≤ q := by
  change IsNonneg _ ↔ _
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, (ha : 0 ≤ a), (hb : 0 < b), h⟩
    apply Quotient.eq.1 at h
    simp at h
    nlinarith
  · intro h
    use q - p, 1, by linarith, by linarith
    apply Quotient.eq.2
    simp
    ring

/-- The natural map from the naturals to the rationals preserves and reflects `≤`. -/
lemma i_le_iff (a b : MyNat) : i a ≤ i b ↔ a ≤ b := by
  constructor
  · intro h
    rwa [← MyInt.i_le_iff, ← j_le_iff, j_comp_eq_i, j_comp_eq_i]
  · intro h
    rwa [← MyInt.i_le_iff, ← j_le_iff, j_comp_eq_i, j_comp_eq_i] at h

lemma i_lt_iff (a b : MyNat) : i a < i b ↔ a < b := by
  simp [lt_iff_le_and_ne, i_le_iff, i_injective.ne_iff]

/-!

## Linear order structure on the rationals

-/

def le_total (a b : MyRat) : a ≤ b ∨ b ≤ a := by
  by_cases h : IsNonneg (b - a)
  · left
    exact h
  · right
    by_cases h2 : IsNonneg (a - b)
    · exact h2
    · exfalso
      apply h
      clear h
      rw [(show b - a = -(a - b) by ring)]
      apply nonneg_neg_of_not_nonneg h2

noncomputable instance linearOrder : LinearOrder MyRat where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyRat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_ne] at ha hb ⊢
  rcases ha with ⟨ha, ha'⟩
  rcases hb with ⟨hb, hb'⟩
  refine ⟨?_, by aesop⟩
  rw [zero_le_iff_IsNonneg] at  ha hb ⊢
  apply isNonneg_mul_isNonneg ha hb

noncomputable instance : IsStrictOrderedRing MyRat :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma archimedean (x : MyRat) : ∃ (n : MyNat), x ≤ i n := by
  by_cases hx : 0 ≤ x
  swap
  · refine ⟨0, ?_⟩
    rw [i_zero]
    linarith
  revert hx
  refine Quot.induction_on x (fun ⟨a, b⟩ h ↦ ?_)
  simp only [ne_eq, Quot_eq_Quotient, zero_le_iff_IsNonneg] at h
  rcases h with ⟨c, d, hc, hd, h⟩
  rcases MyInt.archimedean c with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simp only [ne_eq, i, le_def]
  refine ⟨(MyInt.i n) * d - c, d, ?_, hd, ?_⟩
  · rw [sub_nonneg]
    refine _root_.le_trans hn ?_
    suffices 1 ≤ d by
      · rcases this with ⟨m, rfl⟩
        rw [mul_add, mul_one, ← MyInt.i_mul, ← MyInt.i_add, MyInt.i_le_iff]
        exact ⟨n * m, rfl⟩
    rcases lt_iff_le_and_ne.1 hd with ⟨⟨m, rfl⟩, h2⟩
    have hm : m ≠ 0 := fun hm ↦ by simp [hm, MyInt.i_zero] at h2
    refine ⟨m.pred, ?_⟩
    rw [zero_add, add_comm 1, ← MyInt.i_one, ← MyInt.i_add, ← MyNat.succ_eq_add_one,
      MyNat.succ_pred hm]
  · simp only [ne_eq, Quot_eq_Quotient, sub_def, one_mul, Quotient.eq, MyPrerat.equiv_def', ne_eq,
      Int.ne_zero_coe_mul, MyInt.i]
    simp only [ne_eq, Quotient.eq, MyPrerat.equiv_def'] at h
    grind

end MyRat

/-

Both of these now work

#synth LinearOrder MyRat
#synth IsStrictOrderedRing MyRat

-/
