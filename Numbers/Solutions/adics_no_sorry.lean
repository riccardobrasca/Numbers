import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# `n`-adic numbers as compatible sequences

For a base `n : ℕ`, the ring of `n`-adic integers is the inverse limit of the tower of reductions
$$
\cdots \longrightarrow \mathrm{ZMod}\,(n^{k+1}) \longrightarrow \mathrm{ZMod}\,(n^{k})
\longrightarrow \cdots \longrightarrow \mathrm{ZMod}\,(n^{0}),
$$
where each map is the canonical ring homomorphism `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`.

Concretely we describe this inverse limit as the set of *compatible sequences*: sequences `x` with
`x k : ZMod (n ^ k)` such that each term `x k` is the reduction of the next term `x (k + 1)`.

Since the reduction maps are ring homomorphisms, the compatible sequences form a subring of the
product ring `∀ k, ZMod (n ^ k)`, so the `n`-adic numbers are a commutative ring.

For `n` a prime number this recovers the usual ring `ℤ_n` of `n`-adic integers; in particular, for
`p` prime `Adic p` is an integral domain. We prove the latter by identifying `Adic p` with a subring
of Mathlib's `ℤ_[p]` (`PadicInt`): the projections `Adic.proj p k` are compatible with the
reductions, so by the universal property `PadicInt.lift` they assemble into a ring homomorphism
`Adic p →+* ℤ_[p]`, which is injective; since `ℤ_[p]` is a domain, so is `Adic p`.

## Main definitions

* `Adic.reduction n k` : the reduction `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`.
* `Adic.IsCompatible n x` : the predicate that the sequence `x` is compatible.
* `Adic.subring n` : the compatible sequences as a subring of `∀ k, ZMod (n ^ k)`.
* `Adic n` : the `n`-adic numbers, i.e. the set of compatible sequences, a `CommRing`.
* `Adic.proj n k` : the `k`-th component, as a ring hom `Adic n →+* ZMod (n ^ k)`.
* `Adic.isDomain` : for `p` prime, `Adic p` is an integral domain.
-/

/-- The natural reduction ring homomorphism `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`, induced by the
divisibility `n ^ k ∣ n ^ (k + 1)`. -/
def Adic.reduction (n k : ℕ) : ZMod (n ^ (k + 1)) →+* ZMod (n ^ k) :=
  ZMod.castHom (pow_dvd_pow n (Nat.le_succ k)) (ZMod (n ^ k))

/-- A sequence `x`, with `x k : ZMod (n ^ k)` for every `k`, is *compatible* when each term is the
reduction of the next one, i.e. `Adic.reduction n k (x (k + 1)) = x k` for all `k`. -/
def Adic.IsCompatible (n : ℕ) (x : (k : ℕ) → ZMod (n ^ k)) : Prop :=
  ∀ k, Adic.reduction n k (x (k + 1)) = x k

/-- The compatible sequences form a subring of the product ring `∀ k, ZMod (n ^ k)`: the reductions
are ring homomorphisms, so compatibility is preserved by `0`, `1`, `+`, `*` and negation. -/
def Adic.subring (n : ℕ) : Subring (∀ k, ZMod (n ^ k)) where
  carrier := {x | Adic.IsCompatible n x}
  zero_mem' := fun k => by simp
  one_mem' := fun k => by simp
  add_mem' := fun ha hb k => by simp [map_add, ha k, hb k]
  mul_mem' := fun ha hb k => by simp [map_mul, ha k, hb k]
  neg_mem' := fun ha k => by simp [map_neg, ha k]

/-- The `n`-adic numbers, defined as the set of compatible sequences, i.e. the inverse limit
`lim_k ZMod (n ^ k)` of the tower of reductions `Adic.reduction`.

It is a commutative ring (see the `CommRing` instance below), being a subring of the product ring
`∀ k, ZMod (n ^ k)`. For `n` prime this is the usual ring of `n`-adic integers `ℤ_n`. -/
def Adic (n : ℕ) := ↥(Adic.subring n)

instance (n : ℕ) : CommRing (Adic n) :=
  inferInstanceAs (CommRing ↥(Adic.subring n))

namespace Adic

/-- The `k`-th component of an `n`-adic number, as a ring homomorphism `Adic n →+* ZMod (n ^ k)`. -/
def proj (n k : ℕ) : Adic n →+* ZMod (n ^ k) :=
  (Pi.evalRingHom (fun k => ZMod (n ^ k)) k).comp (Adic.subring n).subtype

@[simp] lemma proj_apply (n k : ℕ) (x : Adic n) : proj n k x = x.1 k := rfl

/-- Reducing the `k₂`-th component of a compatible sequence all the way down to `ZMod (n ^ k₁)`
recovers the `k₁`-th component. -/
lemma castHom_proj {n : ℕ} (x : Adic n) {k1 k2 : ℕ} (hk : k1 ≤ k2) :
    ZMod.castHom (pow_dvd_pow n hk) (ZMod (n ^ k1)) (x.1 k2) = x.1 k1 := by
  induction k2, hk using Nat.le_induction with
  | base => simp
  | succ k2 hk ih =>
    have hx : IsCompatible n x.1 := x.2
    rw [← ZMod.castHom_comp (pow_dvd_pow n hk) (pow_dvd_pow n (Nat.le_succ k2)),
      RingHom.comp_apply]
    have hred : ZMod.castHom (pow_dvd_pow n (Nat.le_succ k2)) (ZMod (n ^ k2)) (x.1 (k2 + 1))
        = x.1 k2 := hx k2
    rw [hred]
    exact ih

/-- For a prime `p`, the ring `Adic p` of `p`-adic numbers is an integral domain.

The projections `proj p k` are compatible with the reductions, so by the universal property
`PadicInt.lift` they assemble into a ring homomorphism `Adic p →+* ℤ_[p]`. This homomorphism is
injective (a compatible sequence is determined by its components), and `ℤ_[p]` is a domain, hence so
is `Adic p`. -/
instance isDomain (p : ℕ) [Fact p.Prime] : IsDomain (Adic p) := by
  have f_compat : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k1))).comp (proj p k2) = proj p k1 := by
    intro k1 k2 hk
    ext x
    rw [RingHom.comp_apply, proj_apply, proj_apply]
    exact castHom_proj x hk
  refine Function.Injective.isDomain (PadicInt.lift f_compat) ?_
  intro x y hxy
  apply Subtype.ext
  funext k
  have hspec := PadicInt.lift_spec f_compat k
  have hx : proj p k x = (PadicInt.toZModPow k) (PadicInt.lift f_compat x) := by
    rw [← hspec]; rfl
  have hy : proj p k y = (PadicInt.toZModPow k) (PadicInt.lift f_compat y) := by
    rw [← hspec]; rfl
  have hxy' : proj p k x = proj p k y := by rw [hx, hy, hxy]
  simpa using hxy'

end Adic
