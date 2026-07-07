import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Nat.Factorization.Basic

/-!
# `n`-adic numbers as compatible sequences

For a base `n : ℕ`, the ring of `n`-adic integers is the inverse limit of the tower of reductions

    ... → ZMod (n ^ (k + 1)) → ZMod (n ^ k) → ... → ZMod (n ^ 0),

where each map is the canonical ring homomorphism `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`.

Here `ZMod m` is Mathlib's type of integers modulo `m`: for `m > 0` it is the finite ring
`{0, 1, ..., m - 1}` with arithmetic taken mod `m` (and `ZMod 0` is `ℤ`). It is a commutative ring,
and whenever `m ∣ m'` there is a canonical reduction ring homomorphism `ZMod m' →+* ZMod m` obtained
by `ZMod.cast`; these reductions are the maps in the tower above (with `m = n ^ k`, `m' = n ^ (k + 1)`).

Concretely we describe this inverse limit as the set of *compatible sequences*: sequences `x` with
`x k : ZMod (n ^ k)` such that each term `x k` is the reduction of the next term `x (k + 1)`.

Since the reduction maps are ring homomorphisms, the compatible sequences form a subring of the
product ring `∀ k, ZMod (n ^ k)`, so the `n`-adic numbers are a commutative ring.

For `n` a prime number this recovers the usual ring of `n`-adic integers; in particular, for
`p` prime `Adic p` is an integral domain. We prove this directly, from the digits alone: a nonzero
compatible sequence has a least index with a nonzero digit, which pins down a `p`-adic valuation on
all of its later digits (computed as `Nat.factorization _ p`). Valuations add under multiplication,
and at a suitable index the valuation of a product still lies below the modulus exponent, so the
product keeps a nonzero digit and is itself nonzero.

## Main definitions

* `Adic.reduction n k` : the reduction `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`.
* `Adic.IsCompatible n x` : the predicate that the sequence `x` is compatible.
* `Adic.subring n` : the compatible sequences as a subring of `∀ k, ZMod (n ^ k)`.
* `Adic n` : the `n`-adic numbers, i.e. the set of compatible sequences, a `CommRing`.
* `Adic.proj n k` : the `k`-th component, as a ring hom `Adic n →+* ZMod (n ^ k)`.
* `Adic.isDomain` : for `p` prime, `Adic p` is an integral domain.
-/

namespace Adic

/-- The underlying reduction function `ZMod (n ^ (k + 1)) → ZMod (n ^ k)`, casting an element to the
smaller quotient.

Use `ZMod.cast : ZMod n → R`, the canonical map out of `ZMod n` (here with target `R = ZMod (n ^ k)`).
As a bare function it needs no hypotheses; it is only a ring hom when the target characteristic divides `n`, which is why its ring-hom properties are recorded separately below. -/
def reductionFun (n k : ℕ) : ZMod (n ^ (k + 1)) → ZMod (n ^ k) :=
  ZMod.cast

/-- `reductionFun` sends `0` to `0`.

Use `ZMod.cast_zero : ZMod.cast (0 : ZMod n) = (0 : R)`, which needs only `[AddGroupWithOne R]` (no
divisibility hypothesis). -/
lemma reductionFun_zero (n k : ℕ) : reductionFun n k 0 = 0 :=
  ZMod.cast_zero

/-- `reductionFun` sends `1` to `1`.

Use `ZMod.cast_one : m ∣ n → ZMod.cast (1 : ZMod n) = (1 : R)` (with `[Ring R] [CharP R m]`). The
divisibility `n ^ k ∣ n ^ (k + 1)` is `pow_dvd_pow (a) (h : m ≤ n) : a ^ m ∣ a ^ n` applied to
`Nat.le_succ k : k ≤ k + 1`. -/
lemma reductionFun_one (n k : ℕ) : reductionFun n k 1 = 1 := by
  apply ZMod.cast_one
  exact (pow_dvd_pow n (Nat.le_succ k))

/-- `reductionFun` commutes with addition.

Use `ZMod.cast_add : m ∣ n → ∀ (a b : ZMod n), (a + b).cast = a.cast + b.cast`, the divisibility
again coming from `pow_dvd_pow n (Nat.le_succ k)`. -/
lemma reductionFun_add (n k : ℕ) (a b : ZMod (n ^ (k + 1))) :
    reductionFun n k (a + b) = reductionFun n k a + reductionFun n k b :=
  ZMod.cast_add (pow_dvd_pow n (Nat.le_succ k)) a b

/-- `reductionFun` commutes with multiplication.

Use `ZMod.cast_mul : m ∣ n → ∀ (a b : ZMod n), (a * b).cast = a.cast * b.cast` via
`pow_dvd_pow n (Nat.le_succ k)`. -/
lemma reductionFun_mul (n k : ℕ) (a b : ZMod (n ^ (k + 1))) :
    reductionFun n k (a * b) = reductionFun n k a * reductionFun n k b :=
  ZMod.cast_mul (pow_dvd_pow n (Nat.le_succ k)) a b

/-- The reduction ring homomorphism `ZMod (n ^ (k + 1)) →+* ZMod (n ^ k)`, induced by the
divisibility `n ^ k ∣ n ^ (k + 1)`.

Build the `RingHom` with the anonymous-structure syntax `where`: the data field `toFun` is
`reductionFun n k`, and the four proof fields `map_one'`, `map_mul'`, `map_zero'`, `map_add'` are the
`reductionFun_*` lemmas above. -/
def reduction (n k : ℕ) : ZMod (n ^ (k + 1)) →+* ZMod (n ^ k) where
  toFun := reductionFun n k
  map_one' := reductionFun_one n k
  map_mul' := reductionFun_mul n k
  map_zero' := reductionFun_zero n k
  map_add' := reductionFun_add n k

/-- A sequence `x`, with `x k : ZMod (n ^ k)` for every `k`, is *compatible* when each term is the
reduction of the next one, i.e. `Adic.reduction n k (x (k + 1)) = x k` for all `k`. -/
def IsCompatible (n : ℕ) (x : (k : ℕ) → ZMod (n ^ k)) : Prop :=
  ∀ k, reduction n k (x (k + 1)) = x k

/-- The constant sequence `0` is compatible. -/
lemma isCompatible_zero (n : ℕ) : IsCompatible n 0 := fun k => by simp

/-- The constant sequence `1` is compatible. -/
lemma isCompatible_one (n : ℕ) : IsCompatible n 1 := fun k => by simp

/-- Compatibility is preserved by addition.

`simp [map_add, ha k, hb k]`: `map_add : f (a + b) = f a + f b` pushes `reduction n k` through the
sum, then the compatibility hypotheses `ha k`, `hb k` rewrite each summand. -/
lemma IsCompatible.add {n : ℕ} {a b : ∀ k, ZMod (n ^ k)} (ha : IsCompatible n a)
    (hb : IsCompatible n b) : IsCompatible n (a + b) :=
  fun k => by simp [map_add, ha k, hb k]

/-- Compatibility is preserved by multiplication.

`simp [map_mul, ha k, hb k]`, with `map_mul : f (a * b) = f a * f b`. -/
lemma IsCompatible.mul {n : ℕ} {a b : ∀ k, ZMod (n ^ k)} (ha : IsCompatible n a)
    (hb : IsCompatible n b) : IsCompatible n (a * b) :=
  fun k => by simp [map_mul, ha k, hb k]

/-- Compatibility is preserved by negation.

`simp [map_neg, ha k]`, with `map_neg : f (-a) = -f a`. -/
lemma IsCompatible.neg {n : ℕ} {a : ∀ k, ZMod (n ^ k)} (ha : IsCompatible n a) :
    IsCompatible n (-a) :=
  fun k => by simp [map_neg, ha k]

/-- The compatible sequences as a `Subring` of the product ring `∀ k, ZMod (n ^ k)`.

The `Subring` structure is given by a `carrier : Set _` together with the closure proofs
`zero_mem'`, `one_mem'`, `add_mem'`, `mul_mem'`, `neg_mem'`. Since membership in
`{x | IsCompatible n x}` unfolds definitionally to `IsCompatible n x`, those five fields are exactly
the `isCompatible_*` / `IsCompatible.*` lemmas above. -/
def subring (n : ℕ) : Subring (∀ k, ZMod (n ^ k)) where
  carrier := {x | IsCompatible n x}
  zero_mem' := isCompatible_zero n
  one_mem' := isCompatible_one n
  add_mem' := IsCompatible.add
  mul_mem' := IsCompatible.mul
  neg_mem' := IsCompatible.neg

end Adic

/-- The `n`-adic numbers, defined as the set of compatible sequences, i.e. the inverse limit
`lim_k ZMod (n ^ k)` of the tower of reductions `Adic.reduction`.

`(Adic.subring n)` is the subtype `{x // x ∈ Adic.subring n}` attached to the subring by its
`SetLike` instance. It is a commutative ring (see the `CommRing` instance below), being a subring of
the product ring `∀ k, ZMod (n ^ k)`. For `n` prime this is the usual ring of `n`-adic integers. -/
def Adic (n : ℕ) := (Adic.subring n)

/-- `Adic n` is a commutative ring, inherited from the subring. -/
instance (n : ℕ) : CommRing (Adic n) :=
  inferInstanceAs (CommRing (Adic.subring n))

namespace Adic

/-- The underlying `k`-th component function `Adic n → ZMod (n ^ k)`, evaluating the compatible
sequence at `k`. Here `x.1` is `Subtype.val`, the underlying sequence `∀ k, ZMod (n ^ k)`. -/
def projFun (n k : ℕ) (x : Adic n) : ZMod (n ^ k) := x.1 k

/-- `projFun` sends `0` to `0`; `rfl`, since the subring's `0` is the componentwise `0` (its
`val` is `(0 : ∀ k, ZMod (n ^ k))`, so evaluation at `k` is `0`). -/
lemma projFun_zero (n k : ℕ) : projFun n k 0 = 0 := rfl

/-- `projFun` sends `1` to `1`; `rfl`, as the subring's `1` is componentwise. -/
lemma projFun_one (n k : ℕ) : projFun n k 1 = 1 := rfl

/-- `projFun` commutes with addition; `rfl`, as the subring's `+` is componentwise. -/
lemma projFun_add (n k : ℕ) (x y : Adic n) :
    projFun n k (x + y) = projFun n k x + projFun n k y := rfl

/-- `projFun` commutes with multiplication; `rfl`, as the subring's `*` is componentwise. -/
lemma projFun_mul (n k : ℕ) (x y : Adic n) :
    projFun n k (x * y) = projFun n k x * projFun n k y := rfl

/-- The `k`-th component of an `n`-adic number, as a ring homomorphism `Adic n →+* ZMod (n ^ k)`.

Bundle `projFun n k` into a `RingHom` with the `where` syntax, supplying the proof fields
`map_one'`, `map_mul'`, `map_zero'`, `map_add'` from the `projFun_*` lemmas. -/
def proj (n k : ℕ) : Adic n →+* ZMod (n ^ k) where
  toFun := projFun n k
  map_one' := projFun_one n k
  map_mul' := projFun_mul n k
  map_zero' := projFun_zero n k
  map_add' := projFun_add n k

@[simp] lemma proj_apply (n k : ℕ) (x : Adic n) : proj n k x = x.1 k := rfl

/-- Casting an element of `ZMod c` down to `ZMod a` factors through any intermediate quotient
`ZMod b` (for `a ∣ b ∣ c`); the plain-function analogue of composing reductions.-/
lemma cast_cast {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : ZMod c) :
    (ZMod.cast (ZMod.cast x : ZMod b) : ZMod a) = ZMod.cast x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [ZMod.cast_intCast hbc, ZMod.cast_intCast hab, ZMod.cast_intCast (hab.trans hbc)]

/-- Reducing the `k₂`-th component of a compatible sequence all the way down to `ZMod (n ^ k₁)`
recovers the `k₁`-th component (`k₁ ≤ k₂`). -/
lemma cast_proj {n : ℕ} (x : Adic n) {k1 k2 : ℕ} (hk : k1 ≤ k2) :
    (ZMod.cast (x.1 k2) : ZMod (n ^ k1)) = x.1 k1 := by
  induction k2, hk using Nat.le_induction with
  | base => exact ZMod.cast_id _ _
  | succ k2 hk ih =>
    have hx : IsCompatible n x.1 := x.2
    rw [← ih, ← hx k2]
    exact (cast_cast (pow_dvd_pow n hk) (pow_dvd_pow n (Nat.le_succ k2)) (x.1 (k2 + 1))).symm

/-- The `0`-th digit of any `n`-adic number vanishes, since `ZMod (n ^ 0) = ZMod 1` is trivial.

`pow_zero : a ^ 0 = 1` rewrites the modulus to `1`; `ZMod 1` has a `Subsingleton` instance, so
`Subsingleton.elim : ∀ (a b : α), a = b` equates `x.1 0` with `0`. -/
lemma digit_zero {n : ℕ} (x : Adic n) : x.1 0 = 0 := by
  have : Subsingleton (ZMod (n ^ 0)) := by rw [pow_zero]; infer_instance
  exact Subsingleton.elim _ _

/-- If some digit of `x` is nonzero, then so is every later digit.

Contrapositive: a vanishing later digit `x.1 j` reduces to a vanishing earlier one via
`cast_proj` and `ZMod.cast_zero`. -/
lemma digit_ne_zero_of_le {n : ℕ} (x : Adic n) {k j : ℕ} (hkj : k ≤ j) (h : x.1 k ≠ 0) :
    x.1 j ≠ 0 := by
  intro hj
  apply h
  rw [← cast_proj x hkj, hj]
  exact ZMod.cast_zero

/-- A nonzero `n`-adic number has a nonzero digit. Prove it by contradiction. -/
lemma exists_digit_ne_zero {n : ℕ} {x : Adic n} (hx : x ≠ 0) : ∃ k, x.1 k ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hx (Subtype.ext (funext h))

/-- If a digit is nonzero, its canonical natural representative `ZMod.val` is nonzero. -/
lemma digit_val_ne_zero {p j : ℕ} [Fact p.Prime] {x : Adic p} (h : x.1 j ≠ 0) :
    (x.1 j).val ≠ 0 := by
  intro hv
  apply h
  rw [← ZMod.natCast_rightInverse (x.1 j), hv, Nat.cast_zero]

/-- A digit `x.1 k` vanishes exactly when `p ^ k` divides the representative of any later digit
`x.1 j` (`k ≤ j`).

`cast_proj` rewrites `x.1 k` as `ZMod.cast (x.1 j)`; then `ZMod.natCast_rightInverse` and
`ZMod.cast_natCast : m ∣ n → ∀ (k : ℕ), (↑k : ZMod n).cast = (↑k : R)` turn it into the natural cast
`((x.1 j).val : ZMod (p ^ k))`, which is `0` iff `p ^ k ∣ (x.1 j).val` by
`CharP.cast_eq_zero_iff (R) (p) [CharP R p] (x : ℕ) : (↑x : R) = 0 ↔ p ∣ x`. -/
lemma digit_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : Adic p) {k j : ℕ} (hkj : k ≤ j) :
    x.1 k = 0 ↔ p ^ k ∣ (x.1 j).val := by
  rw [← cast_proj x hkj]
  conv_lhs => rw [← ZMod.natCast_rightInverse (x.1 j), ZMod.cast_natCast (pow_dvd_pow p hkj)]
  exact CharP.cast_eq_zero_iff (ZMod (p ^ k)) (p ^ k) _

/-- The valuation of a nonzero digit stabilises: if `x.1 (m - 1) = 0` and `x.1 m ≠ 0` (with
`1 ≤ m`), then every later digit `x.1 j` has `p`-adic valuation exactly `m - 1`, computed as
`Nat.factorization _ p`.

`Fact.out : p.Prime` extracts primality from the instance. `digit_eq_zero_iff` converts the two
hypotheses into `p ^ (m - 1) ∣ (x.1 j).val` and `¬ p ^ m ∣ (x.1 j).val`; then
`Nat.Prime.pow_dvd_iff_le_factorization : p.Prime → n ≠ 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)`
turns both into bounds on the factorization, and `omega` pins the value to `m - 1`. -/
lemma factorization_digit_val {p : ℕ} [Fact p.Prime] (x : Adic p) {m j : ℕ}
    (hm : 1 ≤ m) (hm1 : x.1 (m - 1) = 0) (hm2 : x.1 m ≠ 0) (hmj : m ≤ j) :
    (x.1 j).val.factorization p = m - 1 := by
  have hp : p.Prime := Fact.out
  have hA : (x.1 j).val ≠ 0 := digit_val_ne_zero (digit_ne_zero_of_le x hmj hm2)
  have hdvd : p ^ (m - 1) ∣ (x.1 j).val := (digit_eq_zero_iff x (by omega)).1 hm1
  have hndvd : ¬ p ^ m ∣ (x.1 j).val := by rw [← digit_eq_zero_iff x hmj]; exact hm2
  rw [hp.pow_dvd_iff_le_factorization hA] at hdvd
  rw [hp.pow_dvd_iff_le_factorization hA] at hndvd
  omega

/-- `Adic p` has no zero divisors. If `a * b = 0` with `a, b ≠ 0`, let `mₐ`, `m_b` be their least
nonzero digit indices. At `n = mₐ + m_b - 1` the representatives of `a.1 n` and `b.1 n` have `p`-adic
valuations `mₐ - 1` and `m_b - 1` (`factorization_digit_val`), so their product has valuation
`n - 1 < n`; but `a.1 n * b.1 n = 0` would force `p ^ n` to divide it — a contradiction.

The least indices come from `Nat.find` on `exists_digit_ne_zero`: `Nat.find_spec : p (Nat.find H)`
gives the nonzero digit, and `Nat.find_min : m < Nat.find H → ¬ p m` gives that earlier digits
vanish (with `Nat.sub_lt : 0 < n → 0 < m → n - m < n` supplying `mₐ - 1 < mₐ`, and
`Nat.one_le_iff_ne_zero` / `digit_zero` giving `1 ≤ mₐ`). `a.1 n * b.1 n = 0` is `congrArg` applied
to `hab`; `CharP.cast_eq_zero_iff`, `Nat.cast_mul` and `ZMod.natCast_rightInverse` rephrase it as
`p ^ n ∣ (a.1 n).val * (b.1 n).val`. Finally `Nat.factorization_mul : a ≠ 0 → b ≠ 0 →
(a * b).factorization = a.factorization + b.factorization` with `Finsupp.add_apply : (g₁ + g₂) a =
g₁ a + g₂ a` adds the two valuations, and `Nat.Prime.pow_dvd_iff_le_factorization` + `omega` close
the contradiction. -/
lemma eq_zero_or_eq_zero_of_mul_eq_zero {p : ℕ} [Fact p.Prime] {a b : Adic p} (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  have hp : p.Prime := Fact.out
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hpa := exists_digit_ne_zero ha
  have hpb := exists_digit_ne_zero hb
  set ma := Nat.find hpa
  set mb := Nat.find hpb
  have ha_ne : a.1 ma ≠ 0 := Nat.find_spec hpa
  have hb_ne : b.1 mb ≠ 0 := Nat.find_spec hpb
  have hma1 : 1 ≤ ma :=
    Nat.one_le_iff_ne_zero.2 (fun h0 => by rw [h0] at ha_ne; exact ha_ne (digit_zero a))
  have hmb1 : 1 ≤ mb :=
    Nat.one_le_iff_ne_zero.2 (fun h0 => by rw [h0] at hb_ne; exact hb_ne (digit_zero b))
  have hma_lt : a.1 (ma - 1) = 0 := not_not.1 (Nat.find_min hpa (Nat.sub_lt hma1 Nat.one_pos))
  have hmb_lt : b.1 (mb - 1) = 0 := not_not.1 (Nat.find_min hpb (Nat.sub_lt hmb1 Nat.one_pos))
  set n := ma + mb - 1 with hn_def
  have hman : ma ≤ n := by omega
  have hmbn : mb ≤ n := by omega
  have fA : (a.1 n).val.factorization p = ma - 1 :=
    factorization_digit_val a hma1 hma_lt ha_ne hman
  have fB : (b.1 n).val.factorization p = mb - 1 :=
    factorization_digit_val b hmb1 hmb_lt hb_ne hmbn
  have hA_ne : (a.1 n).val ≠ 0 := digit_val_ne_zero (digit_ne_zero_of_le a hman ha_ne)
  have hB_ne : (b.1 n).val ≠ 0 := digit_val_ne_zero (digit_ne_zero_of_le b hmbn hb_ne)
  have hzero : a.1 n * b.1 n = 0 := congrArg (fun z : Adic p => z.1 n) hab
  have hdvd : p ^ n ∣ (a.1 n).val * (b.1 n).val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ n)) (p ^ n), Nat.cast_mul,
      ZMod.natCast_rightInverse (a.1 n), ZMod.natCast_rightInverse (b.1 n)]
    exact hzero
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hA_ne hB_ne),
    Nat.factorization_mul hA_ne hB_ne, Finsupp.add_apply, fA, fB] at hdvd
  omega

/-- For `p` prime, `0 ≠ 1` in `Adic p`: the digit `proj p 1` separates them, landing in the
nontrivial ring `ZMod p`.

Apply `proj p 1` to a hypothetical `0 = 1`; `map_zero`, `map_one` and `pow_one : a ^ 1 = a` reduce
it to `(0 : ZMod p) = 1`, refuted by `_root_.zero_ne_one : (0 : α) ≠ 1`. Its `Nontrivial (ZMod p)`
requirement is discharged by `Fact p.Prime` (which makes `ZMod p` a field). The `_root_.` prefix is
needed so the name resolves to the mathlib lemma rather than to this one. -/
lemma zero_ne_one (p : ℕ) [Fact p.Prime] : (0 : Adic p) ≠ 1 := by
  intro h
  have h1 : proj p 1 (0 : Adic p) = proj p 1 (1 : Adic p) := by rw [h]
  rw [map_zero, map_one, pow_one] at h1
  exact _root_.zero_ne_one h1

/-- For `p` prime, `Adic p` is nontrivial. The `Nontrivial` anonymous constructor `⟨x, y, h⟩`
packages a witness `∃ x y, x ≠ y`; here `⟨0, 1, zero_ne_one p⟩`. -/
instance nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (Adic p) := ⟨0, 1, zero_ne_one p⟩

/-- For a prime `p`, the ring `Adic p` of `p`-adic numbers is an integral domain.

`NoZeroDivisors.to_isDomain : (α) → [Ring α] → [Nontrivial α] → [NoZeroDivisors α] → IsDomain α`
combines the `Nontrivial` instance (`Adic.nontrivial`) with a `NoZeroDivisors` instance, whose single
field is `eq_zero_or_eq_zero_of_mul_eq_zero`. -/
instance isDomain (p : ℕ) [Fact p.Prime] : IsDomain (Adic p) := by
  haveI : NoZeroDivisors (Adic p) := ⟨eq_zero_or_eq_zero_of_mul_eq_zero⟩
  exact NoZeroDivisors.to_isDomain (Adic p)

end Adic
