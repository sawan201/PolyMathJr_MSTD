module

public import RequestProject.Additional.Bstar

/-!
# Proposition `prop:T-dichotomy`

For distinct sum vectors `x, y ∈ 𝒳_{h+1,k}` with disjoint support, put `d = x - y`,
`D_j = d_j + ⋯ + d_k` and
`T_{x,y} = #{A ∈ ℬ*_{h,k}(q) : x · vec A = y · vec A}`.

Indices are `0`-based in Lean: the paper's `D_j` (`2 ≤ j ≤ k`) is `suffixSum d (j - 1)`, so the
relevant indices are `1 ≤ j ≤ k - 1`.
-/

@[expose] public section

open scoped Pointwise Nat

namespace Sumsets

open Finset

variable {h k : ℕ}

/-- `d = x - y`, as an integer vector. -/
def diffVec (x y : Fin k → ℕ) : Fin k → ℤ := fun i => (x i : ℤ) - y i

/-- The suffix sum `D_j = ∑_{i ≥ j} d_i` (`0`-based index `j`). -/
def suffixSum (d : Fin k → ℤ) (j : ℕ) : ℤ := ∑ i : Fin k, if j ≤ (i : ℕ) then d i else 0

/-- `T_{x,y} = #{A ∈ ℬ*_{h,k}(q) : x · vec A = y · vec A}`. -/
def Tcount (h k q : ℕ) (x y : Fin k → ℕ) : ℕ :=
  ((BhStarSets h k q).filter (fun A => dotN x (setVec k A) = dotN y (setVec k A))).card

/-- Extension of a vector `Fin k → ℤ` by zero to `ℕ → ℤ`. -/
def extV (v : Fin k → ℤ) (i : ℕ) : ℤ := if hi : i < k then v ⟨i, hi⟩ else 0

theorem extV_coe (v : Fin k → ℤ) (i : Fin k) : extV v i = v i := by simp [extV]

theorem dotN_sub_dotN (x y : Fin k → ℕ) (v : Fin k → ℤ) :
    dotN x v - dotN y v = dot (diffVec x y) v := by
  simp only [dotN, dot, diffVec, ← sum_sub_distrib, sub_mul]

theorem sum_diffVec {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k)
    (hy : y ∈ sumVectors (h + 1) k) : ∑ i, diffVec x y i = 0 := by
  rw [mem_sumVectors] at hx hy
  have hx' : ∑ i, (x i : ℤ) = h + 1 := by exact_mod_cast hx
  have hy' : ∑ i, (y i : ℤ) = h + 1 := by exact_mod_cast hy
  simp only [diffVec, sum_sub_distrib, hx', hy', sub_self]

theorem diffVec_ne_zero {x y : Fin k → ℕ} (hxy : x ≠ y) : diffVec x y ≠ 0 := by
  intro h0; apply hxy; funext i; have := congrFun h0 i; simp [diffVec] at this; omega

theorem weight_diffVec_le {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k) :
    weight (diffVec x y) ≤ h + 1 := by
  rw [mem_sumVectors] at hx
  rw [← hx, weight]
  exact sum_le_sum fun i _ => by simp only [diffVec]; omega

theorem weight_diffVec_eq {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k)
    (hdisj : ∀ i, x i = 0 ∨ y i = 0) : weight (diffVec x y) = h + 1 := by
  rw [mem_sumVectors] at hx
  rw [← hx, weight]
  exact sum_congr rfl fun i _ => by simp only [diffVec]; rcases hdisj i with h0 | h0 <;> simp [h0]

theorem sum_range_extV (v : Fin k → ℤ) : ∑ i ∈ range k, extV v i = ∑ i, v i := by
  rw [← Fin.sum_univ_eq_sum_range]; simp only [extV_coe]

theorem prefix_add_suffixSum (d : Fin k → ℤ) {m : ℕ} (hm : m ≤ k) :
    ∑ j ∈ range m, extV d j + suffixSum d m = ∑ i, d i := by
  have h1 : suffixSum d m = ∑ i ∈ range k, if m ≤ i then extV d i else 0 := by
    rw [suffixSum, ← Fin.sum_univ_eq_sum_range (fun i => if m ≤ i then extV d i else 0)]
    simp only [extV_coe]
  have h2 : ∑ j ∈ range m, extV d j = ∑ i ∈ range k, if i < m then extV d i else 0 := by
    rw [← sum_filter]
    congr 1
    ext i; simp only [mem_range, mem_filter]; omega
  rw [h1, h2, ← sum_add_distrib, ← sum_range_extV]
  refine sum_congr rfl fun i _ => ?_
  by_cases him : i < m
  · simp [him, show ¬ m ≤ i by omega]
  · simp [him, show m ≤ i by omega]

/-- Summation by parts (`eq:suffix-sums`): if `∑ dᵢ = 0` then
`d · v = ∑_{j=1}^{k-1} (v_j - v_{j-1}) D_j`. -/
theorem dot_eq_sum_gaps (d v : Fin k → ℤ) (hd : ∑ i, d i = 0) :
    dot d v = ∑ j ∈ range (k - 1), (extV v (j + 1) - extV v j) * suffixSum d (j + 1) := by
  have h0 : dot d v = ∑ i ∈ range k, extV v i • extV d i := by
    rw [dot, ← Fin.sum_univ_eq_sum_range (fun i => extV v i • extV d i)]
    simp only [extV_coe, smul_eq_mul, mul_comm]
  rw [h0, sum_range_by_parts, sum_range_extV, hd, smul_zero, zero_sub, ← sum_neg_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have := prefix_add_suffixSum d (m := j + 1) (by omega)
  rw [hd] at this
  rw [smul_eq_mul, show ∑ i ∈ range (j + 1), extV d i = -suffixSum d (j + 1) by linarith]
  ring

/-- The sets `A ∈ \binom{[q]}{k}` with `d · vec A = 0` number at most `q^{k-1}`. -/
theorem card_kSubsets_dot_eq_zero_le (q : ℕ) {d : Fin k → ℤ} (hd : d ≠ 0) :
    ((kSubsets q k).filter (fun A => dot d (setVec k A) = 0)).card ≤ q ^ (k - 1) := by
  refine le_trans ?_ (card_tuples_dot_eq_zero_le q d hd)
  refine card_le_card_of_injOn (setVec k) ?_ ?_
  · intro A hA
    rw [coe_filter] at hA ⊢
    exact ⟨setVec_mem_tuples hA.1, hA.2⟩
  · intro A hA B hB hAB
    rw [coe_filter] at hA hB
    have hA' := (mem_powersetCard.mp hA.1).2
    have hB' := (mem_powersetCard.mp hB.1).2
    rw [← image_setVec hA', ← image_setVec hB']
    rw [hAB]

theorem Tcount_le_filter (q : ℕ) (x y : Fin k → ℕ) :
    Tcount h k q x y ≤
      ((kSubsets q k).filter (fun A => dot (diffVec x y) (setVec k A) = 0)).card := by
  refine card_le_card fun A hA => ?_
  simp only [BhStarSets, mem_filter] at hA ⊢
  exact ⟨hA.1.1, by rw [← dotN_sub_dotN, hA.2, sub_self]⟩

/-- **Proposition `prop:T-dichotomy` (upper bound).**  `T_{x,y} ≤ q^{k-1}` for every `q`. -/
theorem Tcount_le (q : ℕ) {x y : Fin k → ℕ} (hxy : x ≠ y) : Tcount h k q x y ≤ q ^ (k - 1) :=
  (Tcount_le_filter q x y).trans (card_kSubsets_dot_eq_zero_le q (diffVec_ne_zero hxy))

/-- A `B_h`-set is not killed by any vector `d'` with `∑ d' = 0`, `0 < w(d') ≤ h`. -/
theorem dot_ne_zero_of_Bh {q : ℕ} {A : Finset ℤ} (hA : A ∈ kSubsets q k)
    (hBh : (h • A).card = M h k) {d' : Fin k → ℤ} (hd0 : d' ≠ 0) (hsum : ∑ i, d' i = 0)
    (hw : weight d' ≤ h) : dot d' (setVec k A) ≠ 0 := by
  intro hdot
  have hAk := (mem_powersetCard.mp hA).2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hd0 (funext fun i => i.elim0)
  obtain ⟨e, he, c, hc, rfl⟩ := exists_coeffVector_of hd0 hsum hw
  rw [dot_smul] at hdot
  have hedot : dot e (setVec k A) = 0 := by
    rcases mul_eq_zero.mp hdot with h0 | h0
    · exact absurd h0 hc
    · exact h0
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    (equal_sum_criterion (h := h) (setVec k A)).mpr ⟨e, mem_coeffVectors.mpr he, hedot⟩
  rw [nsmul_eq_sumsOf_setVec h hAk, card_sumsOf_eq_iff h hk] at hBh
  exact hxy (hBh hx hy heq)

/-- **Proposition `prop:T-dichotomy`(1), non-primitive case.** -/
theorem Tcount_eq_zero_of_not_primitive (q : ℕ) {x y : Fin k → ℕ}
    (hx : x ∈ sumVectors (h + 1) k) (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y)
    (hdisj : ∀ i, x i = 0 ∨ y i = 0) (hprim : univ.gcd (diffVec x y) ≠ 1) :
    Tcount h k q x y = 0 := by
  rw [Tcount, card_eq_zero, filter_eq_empty_iff]
  intro A hA heq
  rw [BhStarSets, mem_filter] at hA
  obtain ⟨d, hd⟩ : ∃ d, d = diffVec x y := ⟨_, rfl⟩
  have hdot : dot d (setVec k A) = 0 := by rw [hd, ← dotN_sub_dotN, heq, sub_self]
  obtain ⟨g, hgdef⟩ : ∃ g, g = univ.gcd d := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := by
    intro h0; rw [hgdef, Finset.gcd_eq_zero_iff] at h0
    exact diffVec_ne_zero hxy (hd ▸ funext fun i => h0 i (mem_univ i))
  have hgnn : 0 ≤ g := hgdef ▸ Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  obtain ⟨n, hn⟩ : ∃ n : ℕ, g = n := ⟨g.toNat, (Int.toNat_of_nonneg hgnn).symm⟩
  have hn2 : 2 ≤ n := by
    have : g ≠ 1 := by rw [hgdef, hd]; exact hprim
    omega
  have hdd' : d = (n : ℤ) • (fun i => d i / g) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hn]
    exact (Int.mul_ediv_cancel' (hgdef ▸ Finset.gcd_dvd (mem_univ i))).symm
  set d' : Fin k → ℤ := fun i => d i / g
  have hw := weight_diffVec_eq hx hdisj
  rw [← hd, hdd', weight_smul_nat] at hw
  have hd'0 : d' ≠ 0 := by
    intro h0; rw [h0, smul_zero] at hdd'; exact diffVec_ne_zero hxy (hd ▸ hdd')
  have hsum : ∑ i, d' i = 0 := by
    have := sum_diffVec hx hy
    rw [← hd, hdd'] at this
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum] at this
    exact (mul_eq_zero.mp this).resolve_left (by omega)
  have hw' : weight d' ≤ h := by nlinarith
  have hdot' : dot d' (setVec k A) = 0 := by
    rw [hdd', dot_smul] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left (by omega)
  exact dot_ne_zero_of_Bh hA.1 hA.2.1 hd'0 hsum hw' hdot'

theorem suffixSum_sub_succ (d : Fin k → ℤ) (i : Fin k) :
    suffixSum d i - suffixSum d (i + 1) = d i := by
  rw [suffixSum, suffixSum, ← sum_sub_distrib]
  rw [sum_eq_single i]
  · simp
  · intro b _ hb
    have : (i : ℕ) ≠ b := fun h => hb (Fin.ext h).symm
    by_cases h1 : (i : ℕ) ≤ b
    · simp [h1, show (i : ℕ) + 1 ≤ b by omega]
    · simp [h1, show ¬ (i : ℕ) + 1 ≤ b by omega]
  · simp

theorem eq_zero_of_suffixSum_eq_zero {d : Fin k → ℤ} (hd : ∑ i, d i = 0)
    (hD : ∀ j, 1 ≤ j → j < k → suffixSum d j = 0) : d = 0 := by
  have hall : ∀ j, suffixSum d j = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa [suffixSum] using hd
    by_cases hjk : j < k
    · exact hD j hj hjk
    · exact sum_eq_zero fun i _ => by simp [show ¬ j ≤ (i : ℕ) by omega]
  funext i
  rw [← suffixSum_sub_succ d i, hall, hall]; rfl

theorem gap_pos {v : Fin k → ℤ} (hv : StrictMono v) {j : ℕ} (hj : j + 1 < k) :
    0 < extV v (j + 1) - extV v j := by
  simp only [extV, dif_pos hj, dif_pos (show j < k by omega), sub_pos]
  exact hv (Fin.mk_lt_mk.mpr (by omega))

theorem dot_pos_of_suffixSum_nonneg {d v : Fin k → ℤ} (hv : StrictMono v) (hd0 : d ≠ 0)
    (hd : ∑ i, d i = 0) (hD : ∀ j, 1 ≤ j → j < k → 0 ≤ suffixSum d j) : 0 < dot d v := by
  rw [dot_eq_sum_gaps d v hd]
  have hex : ∃ j, 1 ≤ j ∧ j < k ∧ suffixSum d j ≠ 0 := by
    by_contra hcon; push_neg at hcon
    exact hd0 (eq_zero_of_suffixSum_eq_zero hd hcon)
  obtain ⟨j, hj1, hjk, hjne⟩ := hex
  refine sum_pos' (fun i hi => ?_) ⟨j - 1, mem_range.mpr (by omega), ?_⟩
  · rw [mem_range] at hi
    exact mul_nonneg (gap_pos hv (by omega)).le (hD _ (by omega) (by omega))
  · have h1 := gap_pos hv (j := j - 1) (by omega)
    have h2 := hD j hj1 hjk
    rw [show j - 1 + 1 = j by omega] at h1 ⊢
    exact mul_pos h1 (lt_of_le_of_ne h2 (Ne.symm hjne))

theorem suffixSum_neg (d : Fin k → ℤ) (j : ℕ) : suffixSum (-d) j = -suffixSum d j := by
  simp only [suffixSum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- **Proposition `prop:T-dichotomy`(1), sign case.** If all `D_j` (`1 ≤ j ≤ k - 1`) are
nonnegative, or all are nonpositive, then `T_{x,y} = 0`. -/
theorem Tcount_eq_zero_of_sign (q : ℕ) {x y : Fin k → ℕ}
    (hx : x ∈ sumVectors (h + 1) k) (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y)
    (hsign : (∀ j, 1 ≤ j → j < k → 0 ≤ suffixSum (diffVec x y) j) ∨
      (∀ j, 1 ≤ j → j < k → suffixSum (diffVec x y) j ≤ 0)) :
    Tcount h k q x y = 0 := by
  rw [Tcount, card_eq_zero, filter_eq_empty_iff]
  intro A hA heq
  rw [BhStarSets, mem_filter] at hA
  have hAk := (mem_powersetCard.mp hA.1).2
  have hv := setVec_strictMono hAk
  have hdot : dot (diffVec x y) (setVec k A) = 0 := by rw [← dotN_sub_dotN, heq, sub_self]
  have hsum := sum_diffVec hx hy
  have hd0 := diffVec_ne_zero hxy
  rcases hsign with hD | hD
  · exact (dot_pos_of_suffixSum_nonneg hv hd0 hsum hD).ne' hdot
  · have := dot_pos_of_suffixSum_nonneg (d := -diffVec x y) hv (neg_ne_zero.mpr hd0)
      (by simp [hsum]) (fun j hj hjk => by rw [suffixSum_neg]; linarith [hD j hj hjk])
    have h2 : dot (-diffVec x y) (setVec k A) = -dot (diffVec x y) (setVec k A) := by
      simp [dot, sum_neg_distrib]
    rw [h2, hdot] at this
    simp at this

end Sumsets
