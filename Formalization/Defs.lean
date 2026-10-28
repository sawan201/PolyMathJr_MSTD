module

public import Mathlib

/-!
# Gaps in the most frequent sizes of integer sumsets — basic definitions

This file contains the definitions from the *Introduction*, *Background* and
*Preliminary Lemmas* sections of the paper.

* `Sumsets.kSubsets q k` is `\binom{[q]}{k}`, the `k`-element subsets of `[q] = {1, …, q}`
  (as finsets of integers).
* The `h`-fold sumset `hA` of a finset `A` is Mathlib's pointwise `h • A`.
* `Sumsets.sumVectors h k` is `𝒳_{h,k}`, the nonnegative integer vectors of length `k`
  with coordinate sum `h`.
* `Sumsets.M h k = \binom{h+k-1}{k-1}` and `Sumsets.Mpred ℓ k = M_{ℓ-1,k}` (with `M_{-1,k} = 0`).
* `Sumsets.P h k ℓ = M_{h,k} - M_{ℓ-1,k}`.
* `Sumsets.sumsOf h v = {x · v : x ∈ 𝒳_{h,k}}`.
* `Sumsets.weight`, `Sumsets.LeadingPos`, and `Sumsets.coeffVectors h k = ℛ_{h,k}`.
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset

/-- `\binom{[q]}{k}`: the `k`-element subsets of `[q] = {1, …, q}`, as finsets of integers. -/
def kSubsets (q k : ℕ) : Finset (Finset ℤ) := (Finset.Icc (1 : ℤ) q).powersetCard k

/-- The set vector `vec A = (a_1, …, a_k)` of a `k`-element set `A = {a_1 < ⋯ < a_k}` (it is
defined to be `0` if `|A| ≠ k`). -/
def setVec (k : ℕ) (A : Finset ℤ) : Fin k → ℤ :=
  fun i => if hA : A.card = k then A.orderEmbOfFin hA i else 0

/-- The set `𝒳_{h,k}` of *sum vectors*: vectors in `ℤ_{≥0}^k` whose coordinates sum to `h`. -/
def sumVectors (h k : ℕ) : Finset (Fin k → ℕ) := Finset.Nat.antidiagonalTuple k h

/-- `M_{h,k} = \binom{h+k-1}{k-1}`, the maximal possible size of `hA` for `|A| = k`. -/
def M (h k : ℕ) : ℕ := (h + k - 1).choose (k - 1)

/-- `M_{ℓ-1,k}`, with the convention `M_{-1,k} = 0`. -/
def Mpred (ℓ k : ℕ) : ℕ := if ℓ = 0 then 0 else M (ℓ - 1) k

/-- `P_ℓ = M_{h,k} - M_{ℓ-1,k}`. -/
def P (h k ℓ : ℕ) : ℕ := M h k - Mpred ℓ k

/-- The dot product `x · v` of an integer vector with an integer vector. -/
def dot {k : ℕ} (x v : Fin k → ℤ) : ℤ := ∑ i, x i * v i

/-- The dot product `x · v` of a sum vector (a vector of naturals) with an integer vector. -/
def dotN {k : ℕ} (x : Fin k → ℕ) (v : Fin k → ℤ) : ℤ := ∑ i, (x i : ℤ) * v i

/-- `{x · v : x ∈ 𝒳_{h,k}}`.  For `v` an enumeration of `A`, this is `hA`
(see `Sumsets.nsmul_image_eq_sumsOf`). -/
def sumsOf (h : ℕ) {k : ℕ} (v : Fin k → ℤ) : Finset ℤ := (sumVectors h k).image (fun x => dotN x v)

/-- The weight `w(d) = ∑ᵢ max(dᵢ, 0)` of an integer vector. -/
def weight {k : ℕ} (d : Fin k → ℤ) : ℕ := ∑ i, (d i).toNat

/-- The positive part `d⁺` of an integer vector, as a vector of naturals. -/
def posVec {k : ℕ} (d : Fin k → ℤ) : Fin k → ℕ := fun i => (d i).toNat

/-- The negative part `d⁻` of an integer vector, as a vector of naturals. -/
def negVec {k : ℕ} (d : Fin k → ℤ) : Fin k → ℕ := fun i => (-d i).toNat

/-- The sign convention `d_{j(d)} > 0`: the first nonzero coordinate of `d` is positive. -/
def LeadingPos {k : ℕ} (d : Fin k → ℤ) : Prop := ∃ i, 0 < d i ∧ ∀ j < i, d j = 0

instance {k : ℕ} (d : Fin k → ℤ) : Decidable (LeadingPos d) := by
  unfold LeadingPos; infer_instance

/-- The predicate defining the coefficient vectors `ℛ_{h,k}`: nonzero, coordinate sum zero,
weight at most `h`, primitive (gcd of the coordinates is `1`) and with positive first nonzero
coordinate. -/
def IsCoeffVector (h : ℕ) {k : ℕ} (d : Fin k → ℤ) : Prop :=
  d ≠ 0 ∧ ∑ i, d i = 0 ∧ weight d ≤ h ∧ Finset.univ.gcd d = 1 ∧ LeadingPos d

instance (h : ℕ) {k : ℕ} (d : Fin k → ℤ) : Decidable (IsCoeffVector h d) := by
  unfold IsCoeffVector; infer_instance

/-- The finite set `ℛ_{h,k}` of coefficient vectors of weight at most `h`.  (Every such vector
has entries in `[-h, h]`, see `Sumsets.mem_coeffVectors`.) -/
def coeffVectors (h k : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc (-(h : ℤ)) h).filter (IsCoeffVector h)

/-- `A` is a `B_h`-set if `|hA| = M_{h,|A|}`. -/
def IsBhSet (h : ℕ) (A : Finset ℤ) : Prop := (h • A).card = M h A.card

/-- The number of `A ∈ \binom{[q]}{k}` with `|hA| = v`. -/
def sizeCount (h k q v : ℕ) : ℕ := ((kSubsets q k).filter (fun A => (h • A).card = v)).card

end Sumsets
