module

public import RequestProject.MainTheorem

/-!
# Additional results: `B_h`-sets that are not `B_{h+1}`-sets

* `Sumsets.BhSets h k q = ℬ_{h,k}(q)` and `Sumsets.BhStarSets h k q = ℬ*_{h,k}(q)`.
* `Sumsets.disjoint_support` (Lemma `lem:disjoint-support`).
* `Sumsets.Bstar_count_1`, `Sumsets.Bstar_count_2`, `Sumsets.Bstar_count_3`,
  `Sumsets.Bstar_count_theta` (Lemma `lem:Bstar-count`).
-/

@[expose] public section

open scoped Pointwise Nat

namespace Sumsets

open Finset

/-- `ℬ_{h,k}(q)`: the `B_h`-sets in `\binom{[q]}{k}`. -/
def BhSets (h k q : ℕ) : Finset (Finset ℤ) :=
  (kSubsets q k).filter (fun A => (h • A).card = M h k)

/-- `ℬ*_{h,k}(q)`: the sets in `\binom{[q]}{k}` that are `B_h`-sets but not `B_{h+1}`-sets. -/
def BhStarSets (h k q : ℕ) : Finset (Finset ℤ) :=
  (kSubsets q k).filter (fun A => (h • A).card = M h k ∧ ((h + 1) • A).card ≠ M (h + 1) k)

theorem coeffVectors_mono {h h' k : ℕ} (hh : h ≤ h') : coeffVectors h k ⊆ coeffVectors h' k := by
  intro d hd
  rw [mem_coeffVectors] at hd ⊢
  exact ⟨hd.1, hd.2.1, le_trans hd.2.2.1 hh, hd.2.2.2⟩

theorem disjoint_support_of_injOn {h k : ℕ} {v : Fin k → ℤ}
    (hv : Set.InjOn (fun x => dotN x v) (sumVectors h k)) {x y : Fin k → ℕ}
    (hx : x ∈ sumVectors (h + 1) k) (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y)
    (heq : dotN x v = dotN y v) : ∀ i, x i = 0 ∨ y i = 0 := by
  intro i
  by_contra hc
  push_neg at hc
  set x' := Function.update x i (x i - 1)
  set y' := Function.update y i (y i - 1)
  have hx' : x = x' + Pi.single i 1 := by
    ext j; by_cases hj : j = i
    · subst hj; simp [x']; omega
    · simp [x', hj]
  have hy' : y = y' + Pi.single i 1 := by
    ext j; by_cases hj : j = i
    · subst hj; simp [y']; omega
    · simp [y', hj]
  have hx'm : x' ∈ sumVectors h k := by
    rw [mem_sumVectors] at hx ⊢; rw [hx', sum_add_single] at hx; omega
  have hy'm : y' ∈ sumVectors h k := by
    rw [mem_sumVectors] at hy ⊢; rw [hy', sum_add_single] at hy; omega
  have : x' = y' := hv hx'm hy'm (by
    simp only
    rw [hx', hy', dotN_add_single, dotN_add_single] at heq
    linarith)
  exact hxy (by rw [hx', hy', this])

/-- **Lemma `lem:disjoint-support`.** For a `B_h`-set `A`, distinct sum vectors
`x, y ∈ 𝒳_{h+1,k}` with `x · vec A = y · vec A` have disjoint supports, hence are orthogonal. -/
theorem disjoint_support {h k q : ℕ} {A : Finset ℤ} (hA : A ∈ BhSets h k q) {x y : Fin k → ℕ}
    (hx : x ∈ sumVectors (h + 1) k) (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y)
    (heq : dotN x (setVec k A) = dotN y (setVec k A)) :
    (∀ i, x i = 0 ∨ y i = 0) ∧ ∑ i, x i * y i = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun i => i.elim0, by simp⟩
  rw [BhSets, Finset.mem_filter] at hA
  have hAk : A.card = k := (Finset.mem_powersetCard.mp hA.1).2
  have hinj : Set.InjOn (fun x => dotN x (setVec k A)) (sumVectors h k) := by
    rw [← card_sumsOf_eq_iff h hk, ← nsmul_eq_sumsOf_setVec h hAk]
    exact hA.2
  have hdisj := disjoint_support_of_injOn hinj hx hy hxy heq
  refine ⟨hdisj, Finset.sum_eq_zero fun i _ => ?_⟩
  rcases hdisj i with h0 | h0 <;> simp [h0]

/-! ### Lemma `lem:Bstar-count` -/

theorem card_BhStarSets_le (h k q : ℕ) (hk : 1 ≤ k) :
    (BhStarSets h k q).card ≤ (2 * h + 3) ^ (k - 1) * q ^ (k - 1) := by
  refine le_trans (Finset.card_le_card ?_) (card_not_Bh_le (h + 1) k q hk)
  intro A hA
  rw [BhStarSets, Finset.mem_filter] at hA
  exact Finset.mem_filter.mpr ⟨hA.1, hA.2.2⟩

/-- **Lemma `lem:Bstar-count`(1).** `|ℬ*_{h,k}(q)| = O(h^{k-1} q^{k-1})`. -/
theorem Bstar_count_1 (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      ((BhStarSets h k q).card : ℝ) ≤ C * (h : ℝ) ^ (k - 1) * (q : ℝ) ^ (k - 1) := by
  refine ⟨4 ^ (k - 1), by positivity, 0, fun q _ => ?_⟩
  have h1 := card_BhStarSets_le h k q (by omega)
  have h2 : (2 * h + 3) ^ (k - 1) ≤ 4 ^ (k - 1) * h ^ (k - 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  exact_mod_cast le_trans h1 (Nat.mul_le_mul_right _ h2)

/-- Explicit lower bound for `|ℬ*_{h,k}(q)|`: for `q ≥ 32 (h+1) (2h+3)^{k-1}`, at least
`q^{k-1} / (32 (h+1) k!)` sets are `B_h`-sets but not `B_{h+1}`-sets. -/
theorem card_BhStarSets_lower (h k q : ℕ) (hk : 3 ≤ k) (hh : 1 ≤ h)
    (hq : 32 * (h + 1) * (2 * h + 3) ^ (k - 1) ≤ q) :
    q ^ (k - 1) ≤ 32 * (h + 1) * k ! * (BhStarSets h k q).card := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega] at hq ⊢
  have hc := card_unique_tuples_ge (m := m) (h + 1) q (h + 1) (by omega) le_rfl
  set U := (tuples q (m + 3)).filter (fun v => Function.Injective v ∧
    ∀ e ∈ coeffVectors (h + 1) (m + 3), dot e v = 0 ↔ e = dZero ((h + 1 : ℕ) : ℤ))
  have hU : U.card ≤ (m + 3) ! * (BhStarSets h (m + 3) q).card := by
    refine le_trans ?_ (card_tuples_filter_le q (m + 3)
      (fun A => (h • A).card = M h (m + 3) ∧ ((h + 1) • A).card ≠ M (h + 1) (m + 3)))
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    obtain ⟨hvq, hvinj, hvu⟩ := hv
    have hd0 := dZero_mem (m := m) (h + 1) (s := h + 1) (by omega) le_rfl
    refine ⟨hvq, hvinj, ?_, ?_⟩
    · rw [card_nsmul_image]
      by_contra hne
      obtain ⟨e, he, hev⟩ := exists_orth_of_card_ne (by omega) hne
      have h1 := (hvu e (coeffVectors_mono (by omega) he)).mp hev
      have h2 := (mem_coeffVectors.mp he).2.2.1
      rw [h1, weight_dZero (by omega)] at h2
      omega
    · rw [card_nsmul_image, ne_eq, card_sumsOf_eq_iff _ (by omega)]
      intro hinj
      obtain ⟨x, hx, y, hy, hxy, hxyv⟩ :=
        (equal_sum_criterion v).mpr ⟨_, hd0, (hvu _ hd0).mpr rfl⟩
      exact hxy (hinj hx hy hxyv)
  have hq' : 32 * (h + 1) * (2 * (h + 1) + 1) ^ (m + 2) ≤ q := by
    rw [show 2 * (h + 1) + 1 = 2 * h + 3 by ring]; exact hq
  have h2 := arith_lower (by omega) hq' (Nat.one_le_pow _ _ (by omega)) hc
  calc q ^ (m + 2) ≤ 32 * (h + 1) * U.card := h2
    _ ≤ 32 * (h + 1) * ((m + 3) ! * (BhStarSets h (m + 3) q).card) :=
        Nat.mul_le_mul_left _ hU
    _ = _ := by ring

/-- **Lemma `lem:Bstar-count`(2).** `|ℬ*_{h,k}(q)| = Ω(q^{k-1})`. -/
theorem Bstar_count_2 (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ (k - 1) ≤ ((BhStarSets h k q).card : ℝ) := by
  refine ⟨1 / (32 * (h + 1) * k ! : ℕ), by positivity, 32 * (h + 1) * (2 * h + 3) ^ (k - 1),
    fun q hq => ?_⟩
  have h1 := card_BhStarSets_lower h k q hk (by omega) hq
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have : ((q ^ (k - 1) : ℕ) : ℝ) ≤ ((32 * (h + 1) * k ! * (BhStarSets h k q).card : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at this ⊢
  linarith

/-- Explicit form of **Lemma `lem:Bstar-count`(3)**: at most `(2h+3)^{2k-2} q^{k-2}` sets of
`ℬ*_{h,k}(q)` have `|(h+1)A| ≤ M_{h+1,k} - 2`. -/
theorem card_Bstar_small_le (h k q : ℕ) (hk : 2 ≤ k) :
    ((BhStarSets h k q).filter (fun A => ((h + 1) • A).card ≤ M (h + 1) k - 2)).card ≤
      (2 * h + 3) ^ (2 * k - 2) * q ^ (k - 2) := by
  classical
  have hrw : (BhStarSets h k q).filter (fun A => ((h + 1) • A).card ≤ M (h + 1) k - 2) =
      (kSubsets q k).filter (fun A => ((h • A).card = M h k ∧ ((h + 1) • A).card ≠ M (h + 1) k)
        ∧ ((h + 1) • A).card ≤ M (h + 1) k - 2) := by
    rw [BhStarSets, Finset.filter_filter]
  rw [hrw]
  have h2 := card_tuples_two_relations_le (h + 1) k q hk
  rw [show 2 * (h + 1) + 1 = 2 * h + 3 by ring] at h2
  refine (card_kSubsets_filter_le q k _).trans (le_trans (Finset.card_le_card ?_) h2)
  intro v hv
  rw [Finset.mem_filter, card_nsmul_image, card_nsmul_image] at hv
  obtain ⟨hvq, hvinj, ⟨hBh, hnBh1⟩, hsmall⟩ := hv
  rw [Finset.mem_filter]
  refine ⟨hvq, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨d, hd, hdv⟩ := exists_orth_of_card_ne (by omega) hnBh1
  have huniq : ∀ e ∈ coeffVectors (h + 1) k, dot e v = 0 → e = d :=
    fun e he hev => by_contra fun hne => hcon e he d hd hne hev hdv
  have hw : weight d = h + 1 := by
    have hwle := (mem_coeffVectors.mp hd).2.2.1
    by_contra hne
    have hdh : d ∈ coeffVectors h k := by
      rw [mem_coeffVectors] at hd ⊢
      exact ⟨hd.1, hd.2.1, by omega, hd.2.2.2⟩
    rw [card_sumsOf_eq_iff _ (by omega)] at hBh
    obtain ⟨x, hx, y, hy, hxy, hxyv⟩ := (equal_sum_criterion v).mpr ⟨d, hdh, hdv⟩
    exact hxy (hBh hx hy hxyv)
  have hgap := gap_size_lemma (by omega) v hd hdv huniq
  rw [hw, Nat.sub_self] at hgap
  have hM0 : M 0 k = 1 := by simp [M]
  have hM : M 0 k < M (h + 1) k := M_strictMono k hk (by omega)
  omega

/-- **Lemma `lem:Bstar-count`(3).** The number of `A ∈ ℬ*_{h,k}(q)` with
`|(h+1)A| ≤ M_{h+1,k} - 2` is `O(h^{2k-2} q^{k-2})`. -/
theorem Bstar_count_3 (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      (((BhStarSets h k q).filter (fun A => ((h + 1) • A).card ≤ M (h + 1) k - 2)).card : ℝ) ≤
        C * (h : ℝ) ^ (2 * k - 2) * (q : ℝ) ^ (k - 2) := by
  refine ⟨4 ^ (2 * k - 2), by positivity, 0, fun q _ => ?_⟩
  have h1 := card_Bstar_small_le h k q (by omega)
  have h2 : (2 * h + 3) ^ (2 * k - 2) ≤ 4 ^ (2 * k - 2) * h ^ (2 * k - 2) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  exact_mod_cast le_trans h1 (Nat.mul_le_mul_right _ h2)

/-- **Lemma `lem:Bstar-count`, "in particular".** Both `|ℬ*_{h,k}(q)|` and the number of
`A ∈ ℬ*_{h,k}(q)` with `|(h+1)A| = M_{h+1,k} - 1` are `Θ(q^{k-1})`. -/
theorem Bstar_count_theta (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ (k - 1) ≤ ((BhStarSets h k q).card : ℝ) ∧
      ((BhStarSets h k q).card : ℝ) ≤ C * (q : ℝ) ^ (k - 1)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ (k - 1) ≤
        (((BhStarSets h k q).filter (fun A => ((h + 1) • A).card = M (h + 1) k - 1)).card : ℝ) ∧
      (((BhStarSets h k q).filter (fun A => ((h + 1) • A).card = M (h + 1) k - 1)).card : ℝ) ≤
        C * (q : ℝ) ^ (k - 1)) := by
  classical
  have hsplit : ∀ q, (BhStarSets h k q).card ≤
      ((BhStarSets h k q).filter (fun A => ((h + 1) • A).card = M (h + 1) k - 1)).card +
      ((BhStarSets h k q).filter (fun A => ((h + 1) • A).card ≤ M (h + 1) k - 2)).card := by
    intro q
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro A hA
    have hA' := hA
    rw [BhStarSets, Finset.mem_filter] at hA'
    have hAk : A.card = k := (Finset.mem_powersetCard.mp hA'.1).2
    have hle : ((h + 1) • A).card ≤ M (h + 1) k := by
      rw [nsmul_eq_sumsOf_setVec (h + 1) hAk]; exact card_sumsOf_le _ (by omega) _
    have hne := hA'.2.2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases heq : ((h + 1) • A).card = M (h + 1) k - 1
    · exact Or.inl ⟨hA, heq⟩
    · exact Or.inr ⟨hA, by omega⟩
  refine ⟨⟨1 / (32 * (h + 1) * k ! : ℕ), (2 * h + 3) ^ (k - 1), by positivity, by positivity,
    32 * (h + 1) * (2 * h + 3) ^ (k - 1), fun q hq => ⟨?_, ?_⟩⟩,
    ⟨1 / (64 * (h + 1) * k ! : ℕ), (2 * h + 3) ^ (k - 1), by positivity, by positivity,
    32 * (h + 1) * (2 * h + 3) ^ (k - 1) + 64 * (h + 1) * k ! * (2 * h + 3) ^ (2 * k - 2) + 1,
    fun q hq => ⟨?_, ?_⟩⟩⟩
  · have h1 := card_BhStarSets_lower h k q hk (by omega) hq
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have : ((q ^ (k - 1) : ℕ) : ℝ) ≤
        ((32 * (h + 1) * k ! * (BhStarSets h k q).card : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢
    linarith
  · exact_mod_cast card_BhStarSets_le h k q (by omega)
  · have h1 := card_BhStarSets_lower h k q hk (by omega) (by omega)
    have h2 := card_Bstar_small_le h k q (by omega)
    have h3 := hsplit q
    set S1 := ((BhStarSets h k q).filter (fun A => ((h + 1) • A).card = M (h + 1) k - 1)).card
    set S2 := ((BhStarSets h k q).filter (fun A => ((h + 1) • A).card ≤ M (h + 1) k - 2)).card
    set c := 64 * (h + 1) * k.factorial
    have hqk1 : q ^ (k - 1) = q * q ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    have h4 : c * ((2 * h + 3) ^ (2 * k - 2) * q ^ (k - 2)) ≤ q ^ (k - 1) := by
      rw [hqk1, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have h5 : q ^ (k - 1) ≤ c * S1 := by
      have : 2 * (32 * (h + 1) * k ! * (BhStarSets h k q).card) ≤ c * S1 + c * S2 := by
        rw [← Nat.mul_add]
        calc 2 * (32 * (h + 1) * k ! * (BhStarSets h k q).card)
            = c * (BhStarSets h k q).card := by simp only [c]; ring
          _ ≤ c * (S1 + S2) := Nat.mul_le_mul_left _ h3
      have : c * S2 ≤ q ^ (k - 1) := le_trans (Nat.mul_le_mul_left _ h2) h4
      omega
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have h6 : q ^ (k - 1) ≤ S1 * (64 * (h + 1) * k !) := by rw [mul_comm]; exact h5
    exact_mod_cast h6
  · have h1 := card_BhStarSets_le h k q (by omega)
    have h2 : ((BhStarSets h k q).filter
        (fun A => ((h + 1) • A).card = M (h + 1) k - 1)).card ≤ (BhStarSets h k q).card :=
      Finset.card_filter_le _ _
    exact_mod_cast le_trans h2 h1

end Sumsets
