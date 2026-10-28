import RequestProject.MainTheorem

/-!
# The computation in Remark `rem:explicit`

For `(h, k) = (3, 4)` the conclusion of Corollary `cor:gap-pattern` holds for every `q` with
`16 ≤ q ≤ 50`.  This is checked by `native_decide`.  (This file is not a `module`, so that the compiled code
of the imported definitions is available to `native_decide`.)
-/

open scoped Pointwise

namespace Sumsets

open Finset

/-- The multiset of the sizes `|hA|`, `A ∈ \binom{[q]}{k}`. -/
def sizesMS (h k q : ℕ) : Multiset ℕ := (kSubsets q k).val.map (fun A => (h • A).card)

theorem sizeCount_eq_count (h k q v : ℕ) : sizeCount h k q v = (sizesMS h k q).count v := by
  rw [sizesMS, Multiset.count_map, sizeCount, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun A _ => eq_comm

theorem sizeCount_eq_zero_of_gt {h k q v : ℕ} (hk : 1 ≤ k) (hv : M h k < v) :
    sizeCount h k q v = 0 := by
  rw [sizeCount, card_eq_zero, filter_eq_empty_iff]
  intro A hA hAv
  have hAk := (mem_powersetCard.mp hA).2
  have := card_sumsOf_le h hk (setVec k A)
  rw [← nsmul_eq_sumsOf_setVec h hAk, hAv] at this
  omega

/-- The Boolean check for one value of `q`, `(h, k) = (3, 4)`. -/
def gapPatternCheck34 (q : ℕ) : Bool :=
  let L := sizesMS 3 4 q
  (List.range 3).all fun ℓ => (List.range 21).all fun v =>
    decide (v ∈ (range 3).image (P 3 4)) || decide (L.count v < L.count (P 3 4 ℓ))

theorem gapPatternCheck34_spec {q : ℕ} (hq : gapPatternCheck34 q = true) :
    ∀ ℓ < 3, ∀ v ∉ (range 3).image (P 3 4), sizeCount 3 4 q v < sizeCount 3 4 q (P 3 4 ℓ) := by
  intro ℓ hℓ v hv
  simp only [gapPatternCheck34, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at hq
  have key : ∀ w < 21, w ∉ (range 3).image (P 3 4) →
      sizeCount 3 4 q w < sizeCount 3 4 q (P 3 4 ℓ) := by
    intro w hw hw'
    rw [sizeCount_eq_count, sizeCount_eq_count]
    exact (hq ℓ hℓ w hw).resolve_left hw'
  by_cases hv21 : v < 21
  · exact key v hv21 hv
  · have hM : M 3 4 = 20 := by decide
    rw [sizeCount_eq_zero_of_gt (by norm_num) (by omega)]
    exact lt_of_le_of_lt (Nat.zero_le _) (key 17 (by norm_num) (by decide))

theorem gapPatternCheck34_all : (List.range' 16 35).all gapPatternCheck34 = true := by
  native_decide

/-- **Remark `rem:explicit`, computation.**  For `(h, k) = (3, 4)` and every `q` with
`16 ≤ q ≤ 50`, each of `P_0, P_1, P_2` is strictly more frequent as a value of `|3A|`,
`A ∈ \binom{[q]}{4}`, than every other value. -/
theorem gap_pattern_3_4_small (q : ℕ) (hq1 : 16 ≤ q) (hq2 : q ≤ 50) :
    ∀ ℓ < 3, ∀ v ∉ (range 3).image (P 3 4), sizeCount 3 4 q v < sizeCount 3 4 q (P 3 4 ℓ) := by
  have := gapPatternCheck34_all
  rw [List.all_eq_true] at this
  exact gapPatternCheck34_spec (this q (List.mem_range'_1.mpr ⟨hq1, by omega⟩))

end Sumsets
