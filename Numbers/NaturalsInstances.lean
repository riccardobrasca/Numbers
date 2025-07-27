import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.Ring.Regular
import Mathlib.Order.Interval.Finset.Defs
import Numbers.Naturals

/-!

In this file we provide various instances about `MyNat` that depend on mathlib

-/

namespace MyNat

instance : CommSemiring MyNat where
  add := (· + · )
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  add_comm := add_comm
  mul := (· * ·)
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

instance : AddCancelCommMonoid MyNat where
  __ := (inferInstance : AddCommMonoid MyNat)
  add_left_cancel _ _ _ := add_left_cancel

noncomputable instance linearOrder : LinearOrder MyNat where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _

instance : IsStrictOrderedRing MyNat where
  add_le_add_left _ _ h _ := add_le_add_left h
  zero_le_one := by simp
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_lt_mul_of_pos_left _ _ _ := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right _ _ _ := mul_lt_mul_of_pos_right

instance : CanonicallyOrderedAdd MyNat where
  exists_add_of_le := id
  le_self_add := le_self_add

instance : IsDomain MyNat := inferInstance

theorem Icc_zero_succ (a : MyNat) : (Set.Icc 0 a.succ) = insert a.succ (Set.Icc 0 a) :=
  Set.ext fun x ↦ ⟨fun hx ↦ by simp_all, fun hx ↦ by simp_all⟩

theorem Icc_succ {a b : MyNat} (hab : a ≤ b.succ) :
    (Set.Icc a b.succ) = insert b.succ (Set.Icc a b) := by
  refine Set.ext fun x ↦ ⟨fun hx ↦ by simp_all, fun hx ↦ ⟨?_, ?_⟩⟩
  · simp only [Set.mem_insert_iff, Set.mem_Icc] at hx
    rcases hx with hx | hx
    · rw [hx]
      refine le_trans hab (le_refl _)
    · exact hx.1
  · simp only [Set.mem_insert_iff, Set.mem_Icc] at hx
    rcases hx with hx | hx
    · rw [hx]
    · exact le_trans hx.2 (le_succ _)

theorem Icc_zero_left_finite (a : MyNat) : (Set.Icc 0 a).Finite := by
  induction a with
  | zero => simp [zero_def]
  | succ n hn =>
      rw [Icc_zero_succ]
      exact Set.Finite.insert n.succ hn

@[simp] theorem Icc_succ_zero (a : MyNat) : Set.Icc a.succ 0 = ∅ := by simp

theorem Icc_zero_right_finite (a : MyNat) : (Set.Icc a 0).Finite := by
  cases a with
  | zero => simp [zero_def]
  | succ a => simp

theorem Icc_finite (a b : MyNat) : (Set.Icc a b).Finite := by
  by_cases hab : a ≤ b
  swap; simp [hab]
  induction b with
  | zero =>
      rw [zero_def]
      exact Icc_zero_right_finite a
  | succ n hm =>
      rw [Icc_succ hab]
      refine Set.Finite.insert n.succ ?_
      by_cases H : a ≤ n
      · exact hm H
      simp [H]

noncomputable
instance : LocallyFiniteOrder MyNat :=
  LocallyFiniteOrder.ofFiniteIcc Icc_finite

lemma eq_or_eq_of_add_mul_eq_add_mul {a b c d : MyNat} (h : a * d + b * c = a * c + b * d) :
    a = b ∨ c = d := by
  induction a generalizing b with
  | zero =>
    simp only [zero_def, zero_mul, zero_add, mul_eq_mul_left_iff] at h
    tauto
  | succ e he =>
    cases b with
    | zero =>
      simp_all [zero_def]
    | succ f =>
      simp only [succ.injEq]
      grind

end MyNat
