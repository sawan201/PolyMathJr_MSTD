module

public import RequestProject.Counting

/-!
# Lemma `lem:rank-lemma` (general `r`)

If `d⁽¹⁾, …, d⁽ʳ⁾ ∈ ℤ^k` are linearly independent, then at most `q^{k-r}` vectors
`v ∈ [q]^k` satisfy `d⁽¹⁾ · v = ⋯ = d⁽ʳ⁾ · v = 0`.  (The cases `r = 1, 2` used in the main proofs
are `Sumsets.card_tuples_dot_eq_zero_le` and `Sumsets.card_tuples_two_dot_eq_zero_le`.)
-/

@[expose] public section

namespace Sumsets

open Finset

/-- From `r` linearly independent rows one can choose `r` coordinates whose columns are
linearly independent. -/
theorem exists_independent_columns {r k : ℕ} (d : Fin r → Fin k → ℚ)
    (hd : LinearIndependent ℚ d) :
    ∃ S : Finset (Fin k), S.card = r ∧
      LinearIndependent ℚ (fun j : S => fun i : Fin r => d i (j : Fin k)) := by
  classical
  set A : Matrix (Fin r) (Fin k) ℚ := Matrix.of d
  have hrank : A.rank = r := by
    rw [Matrix.rank_eq_finrank_span_row]
    have := finrank_span_eq_card hd
    rw [Fintype.card_fin] at this
    exact this
  have hcols : Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ A.col
  haveI : Finite κ := hli.finite
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hspan, hcols]
  refine ⟨univ.map ⟨a, ha⟩, by rw [card_map, card_univ, hcard], ?_⟩
  let e : (univ.map ⟨a, ha⟩ : Finset (Fin k)) ≃ κ :=
    { toFun := fun j => (mem_map.mp j.2).choose
      invFun := fun t => ⟨a t, mem_map.mpr ⟨t, mem_univ t, rfl⟩⟩
      left_inv := fun j => Subtype.ext (mem_map.mp j.2).choose_spec.2
      right_inv := fun t => ha (mem_map.mp (mem_map.mpr ⟨t, mem_univ t, rfl⟩ :
        a t ∈ univ.map ⟨a, ha⟩)).choose_spec.2 }
  have : (fun j : (univ.map ⟨a, ha⟩ : Finset (Fin k)) => fun i : Fin r => d i (j : Fin k)) =
      (A.col ∘ a) ∘ e := by
    funext j i
    simp only [Function.comp_apply, Matrix.col_apply, A, Matrix.of_apply]
    congr 1
    exact ((mem_map.mp j.2).choose_spec.2).symm
  rw [this]
  exact hli.comp e e.injective

/-- **Lemma `lem:rank-lemma`.**  If `d⁽¹⁾, …, d⁽ʳ⁾ ∈ ℤ^k` are linearly independent (over `ℚ`,
equivalently over `ℤ`), then at most `q^{k-r}` vectors `v ∈ [q]^k` satisfy `d⁽ⁱ⁾ · v = 0` for
all `i`. -/
theorem card_tuples_rank_le (q : ℕ) {r k : ℕ} (d : Fin r → Fin k → ℤ)
    (hd : LinearIndependent ℚ (fun i j => (d i j : ℚ))) :
    ((tuples q k).filter (fun v => ∀ i, dot (d i) v = 0)).card ≤ q ^ (k - r) := by
  classical
  obtain ⟨S, hS, hli⟩ := exists_independent_columns _ hd
  set T : Fin k → Finset ℤ := fun j => if j ∈ S then {0} else Icc 1 (q : ℤ)
  have hT : (Fintype.piFinset T).card = q ^ (k - r) := by
    rw [Fintype.card_piFinset, ← prod_mul_prod_compl S]
    have h1 : ∏ j ∈ S, (T j).card = 1 := prod_eq_one fun j hj => by simp [T, hj]
    have h2 : ∏ j ∈ Sᶜ, (T j).card = q ^ (k - r) := by
      rw [prod_congr rfl (g := fun _ => q), prod_const, card_compl, Fintype.card_fin, hS]
      intro j hj
      rw [mem_compl] at hj
      simp only [T, if_neg hj]
      exact card_Icc_one q
    rw [h1, h2, one_mul]
  rw [← hT]
  refine card_le_card_of_injOn (fun v j => if j ∈ S then 0 else v j) ?_ ?_
  · intro v hv
    rw [coe_filter, tuples, Set.mem_setOf_eq, Fintype.mem_piFinset] at hv
    rw [mem_coe, Fintype.mem_piFinset]
    intro j
    by_cases hj : j ∈ S
    · simp [T, hj]
    · simp only [T, if_neg hj]; exact hv.1 j
  · intro v hv w hw hvw
    rw [coe_filter, Set.mem_setOf_eq] at hv hw
    have hoff : ∀ j, j ∉ S → v j = w j := by
      intro j hj
      have := congrFun hvw j
      simp only [if_neg hj] at this
      exact this
    have hrel : ∑ j : S, ((v j - w j : ℤ) : ℚ) • (fun i : Fin r => (d i (j : Fin k) : ℚ)) = 0 := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have h1 : dot (d i) v - dot (d i) w = 0 := by rw [hv.2 i, hw.2 i, sub_zero]
      have h2 : ∑ j, d i j * (v j - w j) = 0 := by
        rw [← h1, dot, dot, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by ring
      have h3 : ∑ j ∈ S, d i j * (v j - w j) = 0 := by
        rw [← h2]
        refine (sum_subset (subset_univ S) fun j _ hj => ?_)
        rw [hoff j hj, sub_self, mul_zero]
      have h4 : ∑ j : S, ((v j - w j : ℤ) : ℚ) * (d i (j : Fin k) : ℚ) =
          ((∑ j ∈ S, d i j * (v j - w j) : ℤ) : ℚ) := by
        push_cast
        rw [← sum_coe_sort S]
        exact sum_congr rfl fun j _ => by ring
      rw [h4, h3, Int.cast_zero]
    have hzero := Fintype.linearIndependent_iff.mp hli _ hrel
    funext j
    by_cases hj : j ∈ S
    · have := hzero ⟨j, hj⟩
      simp only [Int.cast_eq_zero] at this
      linarith
    · exact hoff j hj

end Sumsets
