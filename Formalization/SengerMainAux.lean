import RequestProject.SengerConstruction

/-!
# Two lemmas that did not fit anywhere else

 An injective tuple only ever satisfies relations of
weight `≥ 2`, and uniqueness inside `R h k` gives uniqueness up to sign among all
primitive relevant relations.
-/

open scoped BigOperators
open Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option autoImplicit false

namespace Senger

noncomputable section
open Classical

/-- If `A` is injective, every relevant relation it satisfies has weight at least
two: weight one would say `A i = A j` for two different indices. -/
theorem satisfied_relevant_weight_ge_two {h k : ℕ} {A d : Fin k → ℤ}
    (hA : Function.Injective A) (hd : Relevant h d) (hsat : Satisfies A d) :
    2 ≤ weight d := by
  by_contra hw
  push_neg at hw
  have hw_le : weight d ≤ 1 := Nat.lt_succ_iff.mp hw
  cases hw0 : weight d with
  | zero =>
    -- Weight zero: every positive part vanishes, and balance drags the rest to zero.
    have hsum : ∑ j, (d j).toNat = 0 := by rw [weight] at hw0; exact hw0
    have hd0 : d = 0 := by
      have hle : ∀ i, d i ≤ 0 := by
        intro i
        have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity) |>.mp hsum
        have hi := this i (Finset.mem_univ i)
        simp only [Int.toNat_eq_zero] at hi
        exact hi
      have hbal := hd.2.1
      rw [Balanced] at hbal
      have : ∀ i, d i = 0 := by
        intro i
        by_contra hne
        have := hle i
        have hlt : d i < 0 := lt_of_le_of_ne this hne
        have hsum_neg : ∑ j, d j < 0 := by
          have : (∑ j, d j : ℤ) < ∑ j : Fin k, (0 : ℤ) := by
            apply Finset.sum_lt_sum
            · intro j _; exact hle j
            · exact ⟨i, Finset.mem_univ i, hlt⟩
          simpa using this
        omega
      exact funext this
    exact hd.1 hd0
  | succ n =>
    have hn : n = 0 := by omega
    have hwt1 : weight d = 1 := by simp [hw0, hn]
    -- Weight one: some `i₀` has `d i₀ = 1`, and balance makes the negative parts
    -- sum to 1 as well.
    have hbal := hd.2.1
    have hwt_eq := sum_negPart_eq_weight hbal
    have hpos_ex : ∃ i, posPart d i > 0 := by
      by_contra h
      push_neg at h
      have hsum0 : ∑ i, posPart d i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact Nat.eq_zero_of_le_zero (h i)
      simp [weight] at hwt1
      omega
    obtain ⟨i₀, hi₀_pos⟩ := hpos_ex
    have hi₀_eq : posPart d i₀ = 1 := by
      have hle : posPart d i₀ ≤ weight d := by
        simp [weight]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (posPart d j)) (Finset.mem_univ i₀)
      omega
    have hother : ∀ j, j ≠ i₀ → posPart d j = 0 := by
      intro j hj
      have hsum : weight d = posPart d i₀ + ∑ k ∈ Finset.univ.erase i₀, posPart d k := by
        simp [weight]
        conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      rw [hwt1, hi₀_eq] at hsum
      have hge0 : ∑ k ∈ Finset.univ.erase i₀, posPart d k = 0 := by omega
      have := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hge0
      exact this j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    have hdi₀ : d i₀ = 1 := by
      simp [posPart] at hi₀_eq
      omega
    have hnegi₀ : negPart d i₀ = 0 := by
      simp [negPart]
      linarith
    -- Splitting `Satisfies` by sign leaves `A i₀ = ∑_{j ≠ i₀} negPart d j * A j`.
    have hsplit : ∑ j, (posPart d j : ℤ) * A j = ∑ j, (negPart d j : ℤ) * A j := by
      have hsatsimp : ∑ j, d j * A j = 0 := hsat
      have hdiff : ∀ j, d j = (posPart d j : ℤ) - (negPart d j : ℤ) := fun j => by
        simp [posPart, negPart]
      have hsplit_sum : ∑ j, d j * A j = ∑ j, ((posPart d j : ℤ) - (negPart d j : ℤ)) * A j := by
        congr; ext j; exact (hdiff j).symm ▸ rfl
      rw [hsplit_sum] at hsatsimp
      simp [sub_mul] at hsatsimp
      linarith
    have hlhs : ∑ j, (posPart d j : ℤ) * A j = A i₀ := by
      have heq : ∑ j, (posPart d j : ℤ) * A j = (posPart d i₀ : ℤ) * A i₀ + ∑ j ∈ Finset.univ.erase i₀, (posPart d j : ℤ) * A j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      rw [heq, hi₀_eq]
      have hzero : ∑ j ∈ Finset.univ.erase i₀, (posPart d j : ℤ) * A j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [hother j (Finset.mem_erase.mp hj |>.1)]
      rw [hzero]
      simp
    have hrhs : ∑ j, (negPart d j : ℤ) * A j = ∑ j ∈ Finset.univ.erase i₀, (negPart d j : ℤ) * A j := by
      conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      simp [hnegi₀]
    rw [hlhs, hrhs] at hsplit
    have hnegsum : ∑ j ∈ Finset.univ.erase i₀, negPart d j = 1 := by
      have : ∑ j, negPart d j = negPart d i₀ + ∑ j ∈ Finset.univ.erase i₀, negPart d j := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      rw [hnegi₀, zero_add] at this
      linarith [this.symm ▸ hwt_eq, hwt1]
    have hneg_ex : ∃ j ∈ Finset.univ.erase i₀, negPart d j > 0 := by
      by_contra h
      push_neg at h
      have : ∑ j ∈ Finset.univ.erase i₀, negPart d j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact Nat.eq_zero_of_le_zero (h j hj)
      omega
    obtain ⟨j, hj_mem, hj_pos⟩ := hneg_ex
    have hj_ne : j ≠ i₀ := (Finset.mem_erase.mp hj_mem).1
    have hdj_neg : d j < 0 := by
      simp [negPart] at hj_pos
      omega
    by_cases hunique_neg : ∀ k ∈ Finset.univ.erase i₀, negPart d k > 0 → k = j
    · -- Only `j` is negative, so `A i₀ = A j`, which injectivity forbids.
      have hnegj : negPart d j = 1 := by
        have hsum_eq : ∑ k ∈ Finset.univ.erase i₀, negPart d k = negPart d j := by
          apply Finset.sum_eq_single j
          · intro k hk hk_ne_j
            by_contra hpos
            have hpos' : negPart d k > 0 := Nat.pos_of_ne_zero hpos
            have := hunique_neg k hk hpos'
            exact hk_ne_j this
          · simp [hj_ne]
        rw [hsum_eq] at hnegsum
        exact hnegsum
      have hai_eq_aj : A i₀ = A j := by
        rw [hsplit]
        have hsum_eq : ∑ k ∈ Finset.univ.erase i₀, (negPart d k : ℤ) * A k = (negPart d j : ℤ) * A j := by
          apply Finset.sum_eq_single j
          · intro k hk hk_ne_j
            by_contra hpos
            have hpos' : negPart d k > 0 := Nat.pos_of_ne_zero (fun h => hpos <| by simp [h])
            have := hunique_neg k hk hpos'
            exact hk_ne_j this
          · simp [hj_ne]
        rw [hsum_eq, hnegj]
        simp
      exact hj_ne (hA hai_eq_aj.symm)
    · -- Two negative indices already push the sum to 2.
      push_neg at hunique_neg
      obtain ⟨k, hk_mem, hk_pos, hk_ne_j⟩ := hunique_neg
      have hk_ne_i₀ : k ≠ i₀ := (Finset.mem_erase.mp hk_mem).1
      have hj1 : 1 ≤ negPart d j := hj_pos
      have hk1 : 1 ≤ negPart d k := hk_pos
      have hsum_ge : 2 ≤ ∑ m ∈ Finset.univ.erase i₀, negPart d m := by
        rw [← Finset.add_sum_erase _ _ hj_mem]
        have h2 : negPart d k ≤ ∑ m ∈ (Finset.univ.erase i₀).erase j, negPart d m := by
          apply Finset.single_le_sum (fun m _ => Nat.zero_le (negPart d m))
          simp [hk_mem, hk_ne_j]
        omega
      omega

/-- Uniqueness inside `R h k` is all we need: one of `e`, `-e` is canonical, hence
lands in `R h k`, so `e = ±d`. -/
theorem unique_R_implies_exactlyOne {h k : ℕ} {A d : Fin k → ℤ}
    (hd : d ∈ R h k) (hsat : Satisfies A d)
    (hunique : ∀ e ∈ R h k, Satisfies A e → e = d) :
    ExactlyOnePrimitiveRelation h A d := by
  rw [mem_R_iff] at hd
  obtain ⟨hd_prim, hd_bal, hd_wt, hd_sign⟩ := hd
  -- `Primitive` rules out `d = 0`: take `m = 2`.
  have hd_ne : d ≠ 0 := by
    intro hd0
    have := hd_prim 2 (fun _ => hd0.symm ▸ dvd_zero 2)
    simp at this
  refine ⟨hd_prim, ⟨hd_ne, hd_bal, hd_wt⟩, hsat, ?_⟩
  intro e he_prim he_rel he_sat
  -- Exactly one of `e`, `-e` carries the canonical sign.
  rcases canonicalSign_exactly_one he_rel.1 with ⟨he_sign, _⟩ | ⟨hneg_sign, _⟩
  · -- `e` is the canonical one.
    have he_in_R : e ∈ R h k := by
      rw [mem_R_iff]
      exact ⟨he_prim, he_rel.2.1, he_rel.2.2, he_sign⟩
    exact Or.inl (hunique e he_in_R he_sat)
  · -- otherwise `-e` is, and `-e = d` gives `e = -d`.
    have hneg_in_R : -e ∈ R h k := by
      rw [mem_R_iff]
      refine ⟨?_, ?_, ?_, hneg_sign⟩
      · -- primitive
        intro m hm
        have : ∀ i, m ∣ e i := fun i => by simpa using hm i
        exact he_prim m this
      · -- balanced
        simp only [Balanced, Pi.neg_apply]
        rw [Finset.sum_neg_distrib, he_rel.2.1]
        simp
      · -- weight: for balanced `e` the two parts swap
        have hwe : weight (-e) = weight e := by
          simp only [weight, posPart]
          exact sum_negPart_eq_weight he_rel.2.1
        rw [hwe]
        exact he_rel.2.2
    have hneqd : -e = d := hunique (-e) hneg_in_R (by simpa [Satisfies] using he_sat)
    exact Or.inr (neg_eq_iff_eq_neg.mp hneqd)

end
end Senger
