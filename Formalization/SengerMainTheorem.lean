import RequestProject.SengerMainAux

/-!
# The central theorem

Parts (i)-(iii) and the corollaries. The triangular numbers when `k = 4`.
-/

open scoped BigOperators
open Filter Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option autoImplicit false

namespace Senger

noncomputable section
open Classical

/-- The listed sizes `P_ell = M h k - M (ell-1) k`, with the convention `M(-1,k)=0`. -/
def P (h k ell : ℕ) : ℕ :=
  M h k - if ell = 0 then 0 else M (ell - 1) k

/-- The `k`-subsets of `[q]` whose `h`-fold sumset has exactly `n` elements. -/
noncomputable def sumsetSizeClass (h q k n : ℕ) : Finset (Finset ℕ) :=
  (qSubsets q k).filter fun A ↦
    ∃ v ∈ increasingTuples q k,
      tupleSet v = A ∧ #(hSumset h (fun i ↦ v i)) = n

/-- The first lemma in the paper: one collision at level `h+1` propagates upward
and forces the stated deficit at every later level. -/
theorem bhStar_propagation {h ell k : ℕ} {A : Fin k → ℤ}
    (hk : 0 < k) (hell : 1 ≤ ell) (hBh : IsBh h A)
    (hnot : ¬ IsBh (h + 1) A) :
    #(hSumset (h + ell) A) ≤ M (h + ell) k - M (ell - 1) k := by
  -- Since A is not B_{h+1}, there's a collision at level h+1
  have hcoll : HasCollision (h + 1) A := by
    rw [not_isBh_iff_collision] at hnot
    exact hnot
  -- This gives us a relevant relation d
  obtain ⟨d, hd_rel, hd_sat⟩ := collision_gives_relation hcoll
  have hd0 : d ≠ 0 := hd_rel.1
  have hbal : Balanced d := hd_rel.2.1
  have hwt_le : weight d ≤ h + 1 := hd_rel.2.2
  have hs_le : weight d ≤ h + ell := by omega
  have h_upper := card_hSumset_relation_upper hk hd0 hbal rfl hs_le hd_sat
  -- `weight d ≤ h+1` gives `h + ell - weight d ≥ ell - 1`, and `M` is monotone.
  have h_bound : h + ell - weight d ≥ ell - 1 := by omega
  have hM_mono : M (h + ell - weight d) k ≥ M (ell - 1) k := by
    unfold M
    apply Nat.choose_le_choose
    omega
  exact le_trans h_upper (Nat.sub_le_sub_left hM_mono _)

/-- Part (i): explicit eventual inequalities, so the count really is `Θ(q^k)`.
The constants may depend on `h, k`, never on `q`. -/
theorem central_part_i (h k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) :
    ∃ Q : ℕ, ∀ q ≥ Q,
      (1 / (2 * k.factorial : ℝ)) * q ^ k ≤
        #(sumsetSizeClass h q k (M h k)) ∧
      (#(sumsetSizeClass h q k (M h k)) : ℝ) ≤ q ^ k := by
  -- First establish equality with bhSubsets
  have sumsetSizeClass_eq : ∀ q, sumsetSizeClass h q k (M h k) = bhSubsets h q k := by
    intro q
    ext A
    simp only [sumsetSizeClass, bhSubsets, Finset.mem_filter]
    apply Iff.intro
    · rintro ⟨hA_qsub, v, hv_tup, hv_set, hv_card⟩
      refine ⟨hA_qsub, v, hv_tup, hv_set, ?_⟩
      have := isBh_iff_card h k (by omega : 0 < k) (fun i => (v i : ℤ))
      rw [← hv_card] at this
      exact this.mpr rfl
    · rintro ⟨hA_qsub, v, hv_tup, hv_set, hv_Bh⟩
      refine ⟨hA_qsub, v, hv_tup, hv_set, ?_⟩
      exact (isBh_iff_card h k (by omega : 0 < k) (fun i => (v i : ℤ))).mp hv_Bh
  have hk_pos : 0 < k := by omega
  -- Upper bound: filter is a subset of qSubsets
  have upper_le : ∀ q, #(sumsetSizeClass h q k (M h k)) ≤ Nat.choose q k := by
    intro q
    rw [sumsetSizeClass_eq]
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_qSubsets q k).le
  -- Nat.choose q k ≤ q^k for all q
  have choose_le_pow : ∀ q, Nat.choose q k ≤ q ^ k := by
    intro q
    exact Nat.choose_le_pow q k
  -- Upper bound in ℝ
  have upper_bound : ∀ q, (#(sumsetSizeClass h q k (M h k)) : ℝ) ≤ q ^ k := by
    intro q
    have h1 : (#(sumsetSizeClass h q k (M h k)) : ℝ) ≤ Nat.choose q k := Nat.cast_le.mpr (upper_le q)
    have h2 : (Nat.choose q k : ℝ) ≤ (q ^ k : ℝ) := by exact_mod_cast choose_le_pow q
    linarith
  -- Lower bound using nonBh_count_bound
  have lower_bound : ∀ q, #(sumsetSizeClass h q k (M h k)) ≥ Nat.choose q k - Nat.choose (M h k) 2 * q ^ (k - 1) := by
    intro q
    rw [sumsetSizeClass_eq]
    have h := nonBh_count_bound h q k hk_pos
    rw [card_qSubsets] at h
    omega
  -- Plan: `C(q,k) ≥ (q^k - D q^(k-1))/k!` with `D = k(k-1)/2`, while the non-`B_h`
  -- sets cost at most `C q^(k-1)`.  Both error terms are beaten by `q^k/(2k!)`
  -- once `q ≥ k(k-1) + 2*C*k!`.
  let C := Nat.choose (M h k) 2
  let D := k * (k - 1) / 2
  let Q' := k * (k - 1) + 2 * C * k.factorial
  use Q' + 1
  intro q hq
  constructor
  · -- Lower bound
    have hq_bound : q ≥ Q' + 1 := hq
    -- First, get a lower bound on Nat.choose q k
    have q_large : q ≥ k := by
      simp only [Q'] at hq_bound
      have h1 : k * (k - 1) ≥ k := Nat.le_mul_of_pos_right k (Nat.sub_pos_of_lt (by omega : 1 < k))
      omega
    have hlb : #(sumsetSizeClass h q k (M h k)) ≥ Nat.choose q k - Nat.choose (M h k) 2 * q ^ (k - 1) := lower_bound q
    -- First establish: k! * Nat.choose q k = Nat.descFactorial q k
    have h_descFact : k.factorial * Nat.choose q k = Nat.descFactorial q k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose q k]
    -- `descFactorial q k ≥ q^k - D q^(k-1)`, since `∏(1 - i/q) ≥ 1 - ∑ i/q`.
    have h_prod_bound : Nat.descFactorial q k ≥ q ^ k - D * q ^ (k - 1) := by
      -- Induction on the number of factors.
      have helper : ∀ m q : ℕ, m ≤ q → Nat.descFactorial q m ≥ q ^ m - (m * (m - 1) / 2) * q ^ (m - 1) := by
        intro m
        induction m with
        | zero => simp [Nat.descFactorial]
        | succ m' ihm =>
          intro q hmq
          rw [Nat.descFactorial_succ]
          by_cases hq1 : q = 0
          · simp [hq1]
          · have hqpos : 0 < q := Nat.pos_of_ne_zero hq1
            have hq_ge_m'1 : q - 1 ≥ m' := by omega
            have hqm' : m' ≤ q := by omega
            have ih_applied := ihm q hqm'
            -- If the right-hand side underflows to `0` there is nothing to prove.
            set Am' := m' * (m' - 1) / 2
            have h_half : (m' + 1) * m' / 2 = m' + Am' := by
              have h_id : (m' + 1) * m' = 2 * m' + m' * (m' - 1) := by
                rcases m' with _ | m'
                · simp
                · simp; ring
              omega
            by_cases hunder : Am' * q ^ (m' - 1) > q ^ m'
            · -- RHS of ih underflows to 0
              have ih' : q.descFactorial m' ≥ 0 := Nat.zero_le _
              have hAm'_gt_q : Am' > q := by
                have hm'pos : 0 < m' := by
                  by_contra hm'neg
                  push_neg at hm'neg
                  have hm'_eq : m' = 0 := by omega
                  have Am'_eq : Am' = 0 := by show m' * (m' - 1) / 2 = 0; simp [hm'_eq]
                  rw [hm'_eq, Am'_eq] at hunder
                  norm_num at hunder
                have hsub_eq : m' - 1 + 1 = m' := Nat.sub_add_cancel hm'pos
                have hqeq : q * q ^ (m' - 1) = q ^ m' := by rw [← pow_succ', hsub_eq]
                rw [← hqeq] at hunder
                have hq_pow_pos : q ^ (m' - 1) > 0 := pow_pos hqpos _
                nlinarith
              have goal_zero : q ^ (m' + 1) - (m' + 1) * m' / 2 * q ^ m' = 0 := by
                have hqpow : q ^ (m' + 1) = q ^ m' * q := pow_succ q m'
                have : (m' + 1) * m' / 2 * q ^ m' ≥ q ^ (m' + 1) := by
                  rw [h_half, hqpow, mul_comm]
                  have hma_ge_q : m' + Am' ≥ q := by omega
                  have hqm'pos : q ^ m' > 0 := pow_pos hqpos _
                  exact Nat.mul_le_mul_left _ hma_ge_q
                exact Nat.sub_eq_zero_of_le ‹_›
              simp [goal_zero]
            · -- Normal case: q^m' ≥ A*q^(m'-1)
              push_neg at hunder
              have hm'leq : m' ≤ q := by omega
              have hqm_pos : 0 < q - m' := by omega
              -- Step: `(q - m') * descFactorial q m' ≥ q^(m'+1) - (m'+1)m'/2 * q^m'`.
              have h1 : (q - m') * q.descFactorial m' ≥ (q - m') * (q ^ m' - Am' * q ^ (m' - 1)) := by
                exact Nat.mul_le_mul_left _ ih_applied
              by_cases hm'0 : m' = 0
              · -- m' = 0 case
                simp [hm'0]
              · -- m' > 0 case
                have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'0
                have hqmm' : q ^ m' = q * q ^ (m' - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm'pos]
                have ham'q : q * (Am' * q ^ (m' - 1)) = Am' * q ^ m' := by rw [hqmm']; ring
                have hsq : q * q ^ m' = q ^ (m' + 1) := by ring
                -- Cast-related helpers
                have hm1 : ((q - m' : ℕ) : ℤ) = (q : ℤ) - (m' : ℤ) := Nat.cast_sub hm'leq
                have hqm'_eq : (q : ℤ) ^ m' = (q : ℤ) * (q : ℤ) ^ (m' - 1) := by
                  rw [← pow_succ', Nat.sub_add_cancel hm'pos]
                have ham'_eq : ((Am' * q ^ (m' - 1) : ℕ) : ℤ) = (Am' : ℤ) * (q : ℤ) ^ (m' - 1) := by norm_cast
                have hqm'_nat : ((q ^ m' : ℕ) : ℤ) = (q : ℤ) ^ m' := by norm_cast
                have hsub_eq : ((q ^ m' - Am' * q ^ (m' - 1) : ℕ) : ℤ) = (q : ℤ) ^ m' - (Am' : ℤ) * (q : ℤ) ^ (m' - 1) := by
                  rw [Nat.cast_sub hunder]
                  simp [ham'_eq, hqm'_nat]
                have ham'q_int : (q : ℤ) * ((q : ℤ) ^ (m' - 1)) = (q : ℤ) ^ m' := by rw [← hqm'_eq]
                have hcalc_step : (q - m') * (q ^ m' - Am' * q ^ (m' - 1)) + (m' + Am') * q ^ m' + m' * Am' * q ^ (m' - 1) =
                                  q ^ (m' + 1) + 2 * m' * Am' * q ^ (m' - 1) := by
                  -- Prove by casting to ℤ and using ring
                  have key : ((q - m') * (q ^ m' - Am' * q ^ (m' - 1)) + (m' + Am') * q ^ m' + m' * Am' * q ^ (m' - 1) : ℤ) =
                             ((q ^ (m' + 1) + 2 * m' * Am' * q ^ (m' - 1) : ℕ) : ℤ) := by
                    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
                    ring_nf
                    linarith
                  exact_mod_cast key
                -- Simplify the goal
                have hsimpl2 : (m' + 1 : ℕ) - 1 = m' := Nat.add_sub_cancel_right m' 1
                have hgoal_simp : q ^ (m' + 1) - (m' + 1) * m' / 2 * q ^ m' =
                                  q ^ (m' + 1) - (m' + Am') * q ^ m' := by
                  congr 1
                  rw [h_half]
                have hgoal_simp2 : q ^ (m' + 1) - (m' + 1) * (m' + 1 - 1) / 2 * q ^ (m' + 1 - 1) =
                                   q ^ (m' + 1) - (m' + 1) * m' / 2 * q ^ m' := by
                  congr 1 <;> rw [hsimpl2]
                rw [hgoal_simp2, hgoal_simp]
                -- Cast to integers to avoid natural number subtraction issues
                have hgoal_int : ((q - m') * (q ^ m' - Am' * q ^ (m' - 1)) : ℤ) ≥
                                 (q ^ (m' + 1) - (m' + 1) * m' / 2 * q ^ m' : ℤ) := by
                  have expand : ((q - m') * (q ^ m' - Am' * q ^ (m' - 1)) : ℤ) =
                                (q : ℤ) * (q ^ m' : ℤ) - (q : ℤ) * (Am' * q ^ (m' - 1) : ℤ) -
                                (m' : ℤ) * (q ^ m' : ℤ) + (m' : ℤ) * (Am' * q ^ (m' - 1) : ℤ) := by ring
                  have hsq_int : (q : ℤ) * (q ^ m' : ℤ) = (q ^ (m' + 1) : ℤ) := by ring
                  have ham'q_int2 : (q : ℤ) * (Am' * q ^ (m' - 1) : ℤ) = (Am' * q ^ m' : ℤ) := by
                    have : (q : ℤ) ^ m' = (q : ℤ) * (q : ℤ) ^ (m' - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm'pos]
                    simp [mul_comm, mul_assoc, this]
                  have h_half_int : ((m' + 1) * m' / 2 : ℤ) = (m' : ℤ) + (Am' : ℤ) := by
                    have h_div : 2 ∣ (m' + 1) * m' := by
                      have := Nat.even_mul_succ_self m'
                      simpa [mul_comm] using this.two_dvd
                    norm_cast
                  rw [expand, hsq_int, ham'q_int2]
                  rw [h_half_int]
                  ring_nf
                  have hge : (m' : ℤ) * (Am' : ℤ) * (q : ℤ) ^ (m' - 1) ≥ 0 := by positivity
                  linarith
                have hcast : ((q - m') * q.descFactorial m' : ℤ) ≥
                             ((q - m') * (q ^ m' - Am' * q ^ (m' - 1)) : ℤ) := by
                  exact_mod_cast h1
                have h_half_cast : ((m' + 1) * m' / 2 : ℕ) = (m' + Am') := h_half
                have hgoal_int' : ((q - m') * (q ^ m' - Am' * q ^ (m' - 1)) : ℤ) ≥
                                  ((q ^ (m' + 1) - (m' + Am') * q ^ m' : ℕ) : ℤ) := by
                  by_cases hge : q ^ (m' + 1) ≥ (m' + Am') * q ^ m'
                  · -- Case: subtraction doesn't underflow
                    have key : ((q ^ (m' + 1) - (m' + Am') * q ^ m' : ℕ) : ℤ) =
                               (q : ℤ) ^ (m' + 1) - ((m' + Am') : ℕ) * (q ^ m' : ℕ) := by
                      rw [Nat.cast_sub hge]
                      simp
                    rw [key]
                    have heq : ((m' + Am') : ℕ) = ((m' + 1) * m' / 2 : ℕ) := by rw [h_half]
                    rw [heq]
                    exact hgoal_int
                  · -- Case: subtraction underflows, RHS = 0
                    have hzero : q ^ (m' + 1) - (m' + Am') * q ^ m' = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hge)
                    simp [hzero]
                    have hgoal_int_nonneg : (↑q - ↑m') * (↑q ^ m' - ↑Am' * ↑q ^ (m' - 1)) ≥ 0 := by positivity
                    linarith
                linarith [hcast, hgoal_int']
      exact helper k q q_large
    have hkey : (q ^ k + 2 * k.factorial * C * q ^ (k - 1) : ℝ) ≤
                2 * k.factorial * (Nat.choose q k : ℝ) := by
      have h_descFact_real : (k.factorial : ℝ) * (Nat.choose q k : ℝ) = (Nat.descFactorial q k : ℝ) := by
        exact_mod_cast h_descFact
      have h_prod_bound_real : (Nat.descFactorial q k : ℝ) ≥ (q : ℝ) ^ k - (D : ℝ) * (q : ℝ) ^ (k - 1) := by
        have h_cast : (q ^ k : ℕ) ≤ q.descFactorial k + D * q ^ (k - 1) := by omega
        have h_cast' : ((q ^ k : ℕ) : ℝ) ≤ (q.descFactorial k : ℝ) + (D * q ^ (k - 1) : ℕ) := by
          exact_mod_cast h_cast
        simp at h_cast'
        linarith
      have h2 : (2 : ℝ) * k.factorial * (Nat.choose q k : ℝ) = 2 * (Nat.descFactorial q k : ℝ) := by
        linarith
      have h_ineq : (2 : ℝ) * (k.factorial * C + D) * q ^ (k - 1) ≤ q ^ k := by
        -- `k*(k-1)` is even, so `Q' = 2*(k!*C + D)` on the nose
        have h_even : 2 ∣ k * (k - 1) := by
          have : Even (k * (k - 1)) := Nat.even_mul_pred_self k
          exact even_iff_two_dvd.mp this
        have hD_eq : D = k * (k - 1) / 2 := rfl
        have h_even' : k * (k - 1) = 2 * D := by
          rw [hD_eq]
          have := Nat.div_mul_cancel h_even
          linarith
        have h_bound : (2 : ℝ) * (k.factorial * C + D) ≤ q := by
          have hQ' : Q' = 2 * D + 2 * C * k.factorial := by
            simp only [Q', D]
            omega
          have hQ'' : Q' = 2 * (k.factorial * C + D) := by linarith
          have hq_ge : q ≥ Q' + 1 := hq_bound
          have hQ'_cast : (Q' : ℝ) = 2 * ((k.factorial : ℝ) * C + D) := by
            exact_mod_cast hQ''
          have hcast : (Q' : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq_ge
          linarith
        have hq_pos : (0 : ℝ) < q := by
          have hqk : (q : ℝ) ≥ (k : ℝ) := by exact_mod_cast q_large
          have hk3 : (k : ℝ) ≥ 3 := by exact_mod_cast hk
          linarith
        have hq_pow_pos : (0 : ℝ) < q ^ (k - 1) := pow_pos hq_pos _
        calc (2 : ℝ) * (k.factorial * C + D) * q ^ (k - 1)
            ≤ (q : ℝ) * q ^ (k - 1) := by nlinarith
          _ = q ^ k := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
      linarith
    -- From hkey, we can derive C * q^(k-1) ≤ Nat.choose q k
    have hC_le : C * q ^ (k - 1) ≤ Nat.choose q k := by
      have hk_factorial_pos : (0 : ℝ) < k.factorial := by positivity
      have h2k_factorial_pos : (0 : ℝ) < 2 * k.factorial := by positivity
      have hqk_nonneg : (0 : ℝ) ≤ q ^ k := by positivity
      have h := hkey
      rw [← @Nat.cast_le ℝ]
      have h1 : (2 : ℝ) * k.factorial * (C * q ^ (k - 1)) ≤
                (2 : ℝ) * k.factorial * (Nat.choose q k : ℝ) := by linarith
      have h2 : (C * q ^ (k - 1) : ℝ) ≤ (Nat.choose q k : ℝ) := by
        have : (2 : ℝ) * k.factorial * (C * q ^ (k - 1)) =
               2 * k.factorial * C * q ^ (k - 1) := by ring
        rw [this] at h1
        nlinarith
      exact_mod_cast h2
    -- Now prove the lower bound
    have hlb : #(sumsetSizeClass h q k (M h k)) ≥ Nat.choose q k - Nat.choose (M h k) 2 * q ^ (k - 1) := lower_bound q
    have hlb' : (Nat.choose q k : ℝ) - ↑C * ↑q ^ (k - 1) ≤ (#(sumsetSizeClass h q k (M h k)) : ℝ) := by
      have hcast : (#(sumsetSizeClass h q k (M h k)) : ℝ) ≥ (Nat.choose q k - C * q ^ (k - 1) : ℕ) := by
        exact_mod_cast hlb
      have heq : ((Nat.choose q k - C * q ^ (k - 1) : ℕ) : ℝ) = (Nat.choose q k : ℝ) - ↑C * ↑q ^ (k - 1) := by
        rw [Nat.cast_sub hC_le]
        simp
      linarith
    suffices key : (1 / (2 * k.factorial : ℝ)) * q ^ k ≤ (#(sumsetSizeClass h q k (M h k)) : ℝ) by
      exact key
    have h1 : (1 / (2 * k.factorial : ℝ)) * q ^ k ≤ (Nat.choose q k : ℝ) - ↑C * ↑q ^ (k - 1) := by
      have h2k_factorial_pos : (0 : ℝ) < 2 * k.factorial := by positivity
      rw [div_mul_eq_mul_div, mul_comm, div_le_iff₀ h2k_factorial_pos]
      linarith
    linarith
  · -- Upper bound
    exact upper_bound q

/-- A tuple with exactly one canonical relevant relation lands on one of the listed
sizes. -/
theorem unique_canonical_relation_gives_listed (h q k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k)
    {v : Fin k → ℕ} (hv : v ∈ increasingTuples q k)
    {d : Fin k → ℤ} (hd : d ∈ R h k)
    (hsat : Satisfies (fun i ↦ (v i : ℤ)) d)
    (hunique : ∀ e ∈ R h k,
      Satisfies (fun i ↦ (v i : ℤ)) e → e = d) :
    ∃ ell < h, #(hSumset h (fun i ↦ (v i : ℤ))) = P h k ell := by
  have hd_mem : d ∈ R h k := hd
  rw [mem_R_iff] at hd
  obtain ⟨hd_prim, hd_bal, hd_wt, hd_canon⟩ := hd
  -- v is strictly increasing, hence injective
  have hv_inc : IncreasingTuple q v := Finset.mem_filter.mp hv |>.2
  have hv_inj : Function.Injective v := hv_inc.2.injective
  -- Weight at least two, since `v` is injective.
  have hv_inj_cast : Function.Injective (fun i => (v i : ℤ)) := by simpa [Function.Injective] using hv_inj
  have hd_ne : d ≠ 0 := by
    intro hd0
    have := hd_prim 2 (fun _ => by simp [hd0])
    simp at this
  have hrel : Relevant h d := ⟨hd_ne, hd_bal, hd_wt⟩
  have hwt_ge_2 : 2 ≤ weight d := satisfied_relevant_weight_ge_two hv_inj_cast hrel (by simpa using hsat)
  have hexactlyOne := unique_R_implies_exactlyOne hd_mem hsat hunique
  have hudur := exactlyOne_implies_uniqueDirection hexactlyOne
  have hcard := card_hSumset_unique_relation (by omega : 0 < k) hd_ne hd_bal rfl hd_wt hsat hd_prim hudur
  -- Take `ell = h - weight d + 1`; `2 ≤ weight d ≤ h` puts it in `[1, h)`.
  let ell := h - weight d + 1
  use ell
  constructor
  · -- ell < h
    omega
  · -- #(hSumset h ...) = P h k ell
    rw [hcard]
    unfold P
    simp only [ell]
    have hell_ne_0 : h - weight d + 1 ≠ 0 := by omega
    simp [hell_ne_0]

/-- An exceptional set has two distinct canonical relevant relations. -/
theorem exceptional_has_two_relations (h q k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) {A : Finset ℕ}
    (hA : A ∈ (qSubsets q k).filter fun A ↦
      ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)) :
    ∃ v ∈ increasingTuples q k, tupleSet v = A ∧
      ∃ d ∈ R h k, ∃ e ∈ R h k, d ≠ e ∧
        Satisfies (fun i ↦ (v i : ℤ)) d ∧ Satisfies (fun i ↦ (v i : ℤ)) e := by
  simp only [Finset.mem_filter] at hA
  obtain ⟨hA_qsub, hA_excep⟩ := hA
  -- Get v from tupleSet_bijective
  have hbij := tupleSet_bijective q k
  have hA_in_range := hbij.2.2 hA_qsub
  obtain ⟨v, hv_mem, hv_eq⟩ := hA_in_range
  use v, hv_mem, hv_eq
  -- If `v` were `B_h` the size would be `M h k = P h k 0`, which is listed.
  have hv_not_Bh : ¬ IsBh h (fun i => (v i : ℤ)) := by
    intro hv_Bh
    have hcard : #(hSumset h (fun i => (v i : ℤ))) = M h k :=
      (@isBh_iff_card h k (by omega) (fun i => (v i : ℤ)) |>.symm.mpr hv_Bh)
    have hP0 : P h k 0 = M h k := by simp [P]
    have hA_in_class : A ∈ sumsetSizeClass h q k (P h k 0) := by
      simp only [sumsetSizeClass, Finset.mem_filter]
      refine ⟨hA_qsub, v, hv_mem, ?_, ?_⟩
      · rw [← hv_eq]
      · simp [hP0, hcard]
    exact hA_excep 0 (by omega) hA_in_class
  have hcoll : HasCollision h (fun i => (v i : ℤ)) := by
    rwa [← not_isBh_iff_collision]
  -- Get d from collision_iff_exists_mem_R
  rw [collision_iff_exists_mem_R] at hcoll
  obtain ⟨d, hd_R, hd_sat⟩ := hcoll
  -- A single relation would put `A` in a listed class by the previous lemma, so
  -- there has to be a second one.
  by_contra h_unique
  have h_unique' : ∀ e ∈ R h k, Satisfies (fun i => (v i : ℤ)) e → e = d := by
    intro e he_R he_sat
    by_contra hneq
    exact h_unique ⟨d, hd_R, e, he_R, Ne.symm hneq, hd_sat, he_sat⟩
  -- Apply unique_canonical_relation_gives_listed
  obtain ⟨ell, hell_lt, hcard_eq⟩ := unique_canonical_relation_gives_listed h q k hh hk hv_mem hd_R hd_sat h_unique'
  have hA_in_class : A ∈ sumsetSizeClass h q k (P h k ell) := by
    rw [sumsetSizeClass]
    simp only [Finset.mem_filter]
    exact ⟨hA_qsub, v, hv_mem, hv_eq, hcard_eq⟩
  exact hA_excep ell hell_lt hA_in_class

/-- Union bound for increasing tuples satisfying two distinct canonical relations. -/
theorem two_relation_tuple_count_bound (h q k : ℕ) (hk : 3 ≤ k) :
    #((increasingTuples q k).filter fun v ↦
      ∃ d ∈ R h k, ∃ e ∈ R h k, d ≠ e ∧
        Satisfies (fun i ↦ (v i : ℤ)) d ∧ Satisfies (fun i ↦ (v i : ℤ)) e) ≤
      #(R h k) ^ 2 * q ^ (k - 2) := by
  -- Define the set of ordered pairs (d, e) with d ≠ e in R h k
  let pairs : Finset ((Fin k → ℤ) × (Fin k → ℤ)) := (R h k).offDiag
  -- The set we count is covered by the union over pairs
  have hsub : (increasingTuples q k).filter (fun v ↦ ∃ d ∈ R h k, ∃ e ∈ R h k, d ≠ e ∧
      Satisfies (fun i ↦ (v i : ℤ)) d ∧ Satisfies (fun i ↦ (v i : ℤ)) e) ⊆
      pairs.biUnion fun p => (increasingTuples q k).filter fun v =>
        Satisfies (fun i ↦ (v i : ℤ)) p.1 ∧ Satisfies (fun i ↦ (v i : ℤ)) p.2 := by
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    obtain ⟨hv_mem, d, hd, e, he, hne, hsat_d, hsat_e⟩ := hv
    rw [Finset.mem_biUnion]
    use ⟨d, e⟩
    refine ⟨?_, Finset.mem_filter.mpr ⟨hv_mem, hsat_d, hsat_e⟩⟩
    rw [Finset.mem_offDiag]
    exact ⟨hd, he, hne⟩
  have hle := Finset.card_le_card hsub
  -- Each term in the sum is bounded by q^(k-2)
  let term : ((Fin k → ℤ) × (Fin k → ℤ)) → Finset (Fin k → ℕ) := fun p =>
    (increasingTuples q k).filter fun (v : Fin k → ℕ) =>
      Satisfies (fun i ↦ (v i : ℤ)) p.1 ∧ Satisfies (fun i ↦ (v i : ℤ)) p.2
  have hpair_bound : ∀ p ∈ pairs, #(term p) ≤ q ^ (k - 2) := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hd, he, hne⟩ := hp
    -- Push the tuples into `qVectors` and apply `rank_counting_two`.
    let d := p.1
    let e := p.2
    have hd_mem : d ∈ R h k := hd
    have he_mem : e ∈ R h k := he
    -- Distinct elements of R are linearly independent
    have hli : LinearIndependent ℚ ![(fun i ↦ (d i : ℚ)), (fun i ↦ (e i : ℚ))] :=
      pair_linearIndependent_of_mem_R hd_mem he_mem hne
    -- The set of solutions in qVectors is bounded by q^(k-2)
    have hqvec_bound := rank_counting_two d e (q := q) (by omega : 2 ≤ k) hli
    -- The coercion `ℕ → ℤ` is injective, so the count transfers.
    let coerce : (Fin k → ℕ) → (Fin k → ℤ) := fun v i => (v i : ℤ)
    have hcoerce_inj : Function.Injective coerce := by
      intro v v' hv
      funext i
      have := congrFun hv i
      simp at this
      exact Nat.cast_injective this
    -- term p maps into the filter of qVectors satisfying both
    have himage : (term p).image coerce ⊆ (qVectors q k).filter (fun A => Satisfies A d ∧ Satisfies A e) := by
      intro A hA
      simp only [Finset.mem_image] at hA
      obtain ⟨v, hv_term, rfl⟩ := hA
      simp only [term, Finset.mem_filter] at hv_term
      refine Finset.mem_filter.mpr ⟨?_, hv_term.2.1, hv_term.2.2⟩
      rw [qVectors, Finset.mem_image]
      obtain ⟨hv_mem, _, _⟩ := hv_term
      simp only [increasingTuples, Finset.mem_filter] at hv_mem
      obtain ⟨_, hv_inc⟩ := hv_mem
      refine ⟨fun i => ⟨v i - 1, by
        have := hv_inc.1 i
        omega⟩, Finset.mem_univ _, ?_⟩
      funext i
      simp [coerce]
      have := hv_inc.1 i
      omega
    have himage_card : #(term p) = #((term p).image coerce) := by
      rw [Finset.card_image_of_injective _ hcoerce_inj]
    exact himage_card.le.trans (Finset.card_le_card himage |>.trans hqvec_bound)
  -- Sum bound
  have hsum_bound : ∑ p ∈ pairs, #(term p) ≤ #pairs * q ^ (k - 2) := by
    exact Finset.sum_le_card_nsmul _ _ _ hpair_bound
  -- Pair cardinality bound
  have hpairs_card : #pairs ≤ #(R h k) ^ 2 := by
    have h1 : pairs.card ≤ (R h k ×ˢ R h k).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_offDiag] at hp
      exact Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩
    rw [Finset.card_product] at h1
    exact le_trans h1 (by ring_nf; norm_num)
  have hbiUnion : #(pairs.biUnion fun p => term p) ≤ ∑ p ∈ pairs, #(term p) := Finset.card_biUnion_le
  have h3 := Nat.mul_le_mul_right (q ^ (k - 2)) hpairs_card
  exact le_trans hle (le_trans hbiUnion (le_trans hsum_bound h3))

/-- Part (ii): the exceptional-set estimate, with a constant that does not depend
on `q`. -/
theorem central_part_ii (h k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) :
    ∃ Q : ℕ, ∀ q ≥ Q,
      (#((qSubsets q k).filter fun A ↦
        ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)) : ℝ) ≤
      3 ^ (2 * k - 2) * h ^ (2 * k - 2) * q ^ (k - 2) := by
  use 0
  intro q _
  -- Define the set of exceptional tuples
  let exceptionalTuples := (increasingTuples q k).filter (fun ω ↦ ∃ d ∈ R h k, ∃ e ∈ R h k, d ≠ e ∧
        Satisfies (fun i ↦ (ω i : ℤ)) d ∧ Satisfies (fun i ↦ (ω i : ℤ)) e)
  -- The exceptional sets are bounded by the exceptional tuples
  have h_card_le : #((qSubsets q k).filter (fun A ↦ ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell))) ≤
      #exceptionalTuples := by
    have h_sub : (qSubsets q k).filter (fun A ↦ ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)) ⊆
        exceptionalTuples.image tupleSet := by
      intro A hA
      simp only [Finset.mem_image]
      have hbij := tupleSet_bijective q k
      have hA_subset : A ∈ qSubsets q k := Finset.mem_filter.mp hA |>.1
      obtain ⟨v, hv_mem, hv_eq⟩ := hbij.2.2 hA_subset
      -- Get the two relations for A from exceptional_has_two_relations
      have hA_excep : ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell) := Finset.mem_filter.mp hA |>.2
      obtain ⟨v', hv'_mem, hv'_eq, d, hd_mem, e, he_mem, hde, hd_sat, he_sat⟩ := exceptional_has_two_relations h q k hh hk hA
      -- Since tupleSet is injective on increasingTuples, v' = v
      have hv_eq_v' : v = v' := hbij.2.1 hv_mem hv'_mem (by rw [hv_eq, hv'_eq])
      refine ⟨v', ?_, hv'_eq⟩
      simp only [exceptionalTuples, Finset.mem_filter]
      exact ⟨hv'_mem, d, hd_mem, e, he_mem, hde, hd_sat, he_sat⟩
    exact Finset.card_le_card h_sub |> le_trans <| Finset.card_image_le
  -- Apply the tuple count bound
  have h_tuple_bound := two_relation_tuple_count_bound h q k hk
  -- Now bound #(R h k)^2
  have hR_bound := card_R_le_explicit_bigO h k (by omega : 0 < k) (by omega : 1 ≤ h)
  have hR_sq : #(R h k) ^ 2 ≤ (3 ^ (k - 1) * h ^ (k - 1)) ^ 2 := Nat.pow_le_pow_left hR_bound 2
  have h_final : #((qSubsets q k).filter (fun A ↦ ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell))) ≤
      (3 ^ (k - 1) * h ^ (k - 1)) ^ 2 * q ^ (k - 2) := by
    calc #((qSubsets q k).filter (fun A ↦ ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)))
        ≤ #exceptionalTuples := h_card_le
      _ ≤ #(R h k) ^ 2 * q ^ (k - 2) := h_tuple_bound
      _ ≤ (3 ^ (k - 1) * h ^ (k - 1)) ^ 2 * q ^ (k - 2) := Nat.mul_le_mul_right _ hR_sq
  have h_simp : (3 ^ (k - 1) * h ^ (k - 1)) ^ 2 = 3 ^ (2 * k - 2) * h ^ (2 * k - 2) := by
    have hk1 : k ≥ 1 := by omega
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 1 <;> { rw [mul_comm] ; congr 1; omega }
  rw [h_simp] at h_final
  exact_mod_cast h_final

/-- Constructed sets realize the listed cardinality indexed by a positive `ell`. -/
theorem constructedSets_subset_sizeClass (h q k ell : ℕ) (hk : 3 ≤ k)
    (hell0 : 0 < ell) (hell : ell < h) :
    constructedSets h (h - ell + 1) q k ⊆ sumsetSizeClass h q k (P h k ell) := by
  intro A hA
  -- Unfold constructedSets to get a witness tuple v
  unfold constructedSets at hA
  simp only [Finset.mem_filter] at hA
  obtain ⟨hv_subset, v, hv_tuples, hv_eq⟩ := hA
  unfold sumsetSizeClass
  simp only [Finset.mem_filter]
  refine ⟨hv_subset, ?_⟩
  -- Get the increasing tuple from the bijection
  have hbij := tupleSet_bijective q k
  have hsurj := hbij.2.2
  have hA_mem : (A : Finset ℕ) ∈ (qSubsets q k : Set (Finset ℕ)) := hv_subset
  obtain ⟨v', hv'_mem, hv'_eq⟩ := hsurj hA_mem
  use v'
  refine ⟨hv'_mem, hv'_eq, ?_⟩
  -- v satisfies ExactlyOnePrimitiveRelation, so we can use card_hSumset_exactly_one
  unfold constructedTuples at hv_tuples
  simp only [Finset.mem_filter] at hv_tuples
  obtain ⟨hv_qvec, hv_isconstructed⟩ := hv_tuples
  obtain ⟨hv_bounds, hv_inj, a, r, ha, hr, haq, i0, i1, i2, hi0, hi1, hi2, hvi0, hvi1, hvi2, hprim⟩ := hv_isconstructed
  -- The relation d used in IsConstructedTuple
  have hd_prim := hprim
  -- The weight of d is h - ell + 1
  have hweight : weight (fun (i : Fin k) => if (i : ℕ) = 0 then ↑(h - ell + 1) - 1 else
      if (i : ℕ) = 1 then -↑(h - ell + 1) else if (i : ℕ) = 2 then 1 else 0) = h - ell + 1 := by
    unfold weight posPart
    rw [show k = 3 + (k - 3) by omega]
    rw [Fin.sum_univ_add]
    simp [Fin.sum_univ_succ]
    have htail : ∀ x : Fin (k - 3), ((if 3 + (x : ℕ) = 1 then -1 + -(h - ell : ℤ) else
        if 3 + (x : ℕ) = 2 then 1 else 0).toNat) = 0 := by
      intro x
      simp [show (3 : ℕ) + (x : ℕ) ≠ 1 ∧ (3 : ℕ) + (x : ℕ) ≠ 2 by omega]
    have hzero : ∑ x : Fin (k - 3), ((if 3 + (x : ℕ) = 1 then -1 + -(h - ell : ℤ) else
        if 3 + (x : ℕ) = 2 then 1 else 0).toNat) = 0 := by
      simp_rw [htail, Finset.sum_const_zero]
    have heq : ∀ x : Fin (k - 3), ((if 3 + (x : ℕ) = 1 then -1 + -(h - ell : ℤ) else
        if 3 + (x : ℕ) = 2 then 1 else 0).toNat) =
        ((if 3 + (x : ℕ) = 1 then -1 + -((h - ell : ℕ) : ℤ) else
        if 3 + (x : ℕ) = 2 then 1 else 0).toNat) := by
      intro x
      congr 1
      omega
    simp_rw [heq] at hzero
    rw [hzero]
    simp
  -- Apply card_hSumset_exactly_one to v
  have hv_card := card_hSumset_exactly_one (by omega : 0 < k) hprim
  -- P h k ell = M h k - M (ell - 1) k
  rw [P, if_neg (by omega : ell ≠ 0)]
  -- `v'` is a reordering of `v`, so the two sumsets agree.
  have hev_eq : hSumset h (fun i => ↑(v' i)) = hSumset h v := by
    have hv_bounds : ∀ i, 1 ≤ v i ∧ v i ≤ q := by
      rw [qVectors] at hv_qvec
      rw [Finset.mem_image] at hv_qvec
      obtain ⟨A, _, hv_eq_A⟩ := hv_qvec
      intro i
      rw [← hv_eq_A]
      constructor <;> simp <;> omega
    -- v i = Int.toNat (v i) since v i ≥ 1
    have hv_nat : ∀ i, v i = Int.toNat (v i) := by
      intro i
      have := hv_bounds i
      omega
    -- v' is strictly increasing
    have hv'_inc : StrictMono v' := by
      unfold increasingTuples at hv'_mem
      simp at hv'_mem
      exact hv'_mem.2.2
    have hexists : ∀ i, ∃ j, v' j = Int.toNat (v i) := by
      intro i
      have hmem : Int.toNat (v i) ∈ tupleSet (fun i => Int.toNat (v i)) := by
        simp [tupleSet]
      rw [hv_eq] at hmem
      rw [hv'_eq.symm] at hmem
      simp [tupleSet] at hmem
      exact hmem
    choose σ hσ using hexists
    -- σ is a permutation of Fin k
    have hσ_inj : Function.Injective σ := by
      intro i j hij
      have hi : v i = v' (σ i) := by rw [hσ i]; exact hv_nat i
      have hj : v j = v' (σ j) := by rw [hσ j]; exact hv_nat j
      have heq : v i = v j := by rw [hi, hj, hij]
      exact hv_inj heq
    have hσ_bij : Function.Bijective σ := ⟨hσ_inj, Finite.injective_iff_surjective.mp hσ_inj⟩
    let σ_perm : Equiv.Perm (Fin k) := Equiv.ofBijective σ hσ_bij
    -- v = (fun i => ↑(v' i)) ∘ σ_perm
    have hv_eq_perm : v = (fun i => ↑(v' i)) ∘ σ_perm := by
      funext i
      simp only [Function.comp_apply]
      have : σ_perm i = σ i := rfl
      rw [this, hσ i]
      exact hv_nat i
    rw [hv_eq_perm]
    exact (hSumset_invariant_under_reordering h _ σ_perm).symm
  rw [hev_eq, hv_card]
  simp only [hweight]
  congr 1
  have h_ell : h - (h - ell + 1) = ell - 1 := by omega
  rw [h_ell]

/-- Turning the integral construction bound into an eventual real one. -/
theorem constructedSets_eventual_real_lower (h k ell : ℕ) (hk : 3 ≤ k)
    (hell0 : 0 < ell) (hell : ell < h) :
    ∃ c : ℝ, 0 < c ∧ ∃ Q : ℕ, ∀ q ≥ Q,
      c * q ^ (k - 1) / (h - ell + 1) ≤
        #(constructedSets h (h - ell + 1) q k) := by
  -- We use constructedSets_lower_bound with s = h - ell + 1
  have hs_pos : 2 ≤ h - ell + 1 := by omega
  have hs_le : h - ell + 1 ≤ h := by omega
  set s := h - ell + 1 with hs_def
  let Q := 2 * ((2 * h + 1) ^ (k + 1) + k + 2 * s)
  -- With `c = 1/(4^(k-1) * k!)`: the floors `q/2` and `q/(2s)` each lose at most a
  -- factor of two, so the product is at least `q^(k-1) / (4^(k-1) * s)`.
  use 1 / (4 ^ (k - 1) * k.factorial : ℝ)
  constructor
  · positivity
  use Q
  intro q hq
  have hbound := constructedSets_lower_bound h s q k hk hs_pos hs_le hq
  -- Rewrite s in the goal
  rw [hs_def]
  -- Convert hbound to reals
  have hq_pos : 0 < q := by
    have : Q > 0 := by positivity
    omega
  have hs_pos_real : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega : 0 < s)
  have hkfact_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  -- Key inequality: 2^(k-1) ≤ 6 * 3^(k-1)
  have hexp : (2 : ℝ) ^ (k - 1) ≤ 6 * 3 ^ (k - 1) := by
    calc (2 : ℝ) ^ (k - 1) ≤ 3 ^ (k - 1) := by gcongr; norm_num
      _ ≤ 6 * 3 ^ (k - 1) := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (k - 1)]
  have hQ_ge : Q ≥ 4 * s := by
    simp only [Q]
    have : (2 * h + 1) ^ (k + 1) ≥ 1 := Nat.one_le_pow _ _ (by omega)
    linarith
  have hq_ge_4s : q ≥ 4 * s := by omega
  have hs_pos2 : 0 < s := by omega
  have hq_ge_8 : q ≥ 8 := by omega
  have hq2 : q / 2 ≥ 1 := Nat.div_pos (by omega : q ≥ 2) (by omega : 2 > 0)
  have hqs : q / (2 * s) ≥ 1 := Nat.div_pos (by omega : q ≥ 2 * s) (by omega : 2 * s > 0)
  have hprod_pos : 0 < (q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3) := by positivity
  have hcard_pos : 0 < #(constructedSets h s q k) := by nlinarith
  have hq_Q_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr (by positivity)
  -- Relate (↑h - ↑ell + 1) to s
  have hs_real : (↑h : ℝ) - ↑ell + 1 = ↑s := by
    have h_le : ell ≤ h := Nat.le_of_lt hell
    simp only [hs_def]
    rw [Nat.cast_add, Nat.cast_sub h_le]
    ring
  rw [hs_real]
  -- Unify constructedSets
  have h_constructedSets : constructedSets h (h - ell + 1) q k = constructedSets h s q k := by
    simp [hs_def]
  rw [h_constructedSets]
  have hcard_lower : ( #(constructedSets h s q k) : ℝ) * (k.factorial : ℝ) ≥
      ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ) := by
    have hprod_nat : ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ) =
        ((((q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3)) : ℕ) : ℝ) := by
      push_cast; ring
    rw [hprod_nat]
    have hcard_nat : ((#(constructedSets h s q k) : ℕ) : ℝ) * (k.factorial : ℝ) =
        (((#(constructedSets h s q k) : ℕ) * k.factorial) : ℝ) := by push_cast; ring
    rw [hcard_nat]
    have hbound' := hbound
    rw [mul_comm k.factorial] at hbound'
    exact_mod_cast hbound'
  -- Key floor bounds for q ≥ 8, s ≥ 2, q ≥ 4s:
  have h_floor_q2 : ((q / 2 : ℕ) : ℝ) ≥ q / 4 := by
    have hq2_nat : (q / 2 : ℕ) ≥ q / 4 := by omega
    have hcast1 : ((q / 2 : ℕ) : ℝ) ≥ ((q / 4 : ℕ) : ℝ) := by exact_mod_cast hq2_nat
    have hq_ge_4 : q / 4 ≥ 2 := by omega
    have hq2_ge : q / 2 ≥ q / 4 + 1 := by omega
    have hcast2 : ((q / 2 : ℕ) : ℝ) ≥ ((q / 4 : ℕ) : ℝ) + 1 := by exact_mod_cast hq2_ge
    have hmod4 : (q : ℝ) = 4 * (q / 4 : ℕ) + (q % 4 : ℕ) := by
      have heq := Nat.div_add_mod q 4; push_cast at *; exact_mod_cast heq.symm
    have hmod4_lt : (q % 4 : ℕ) < 4 := Nat.mod_lt q (by norm_num)
    have hmod4_real : (q % 4 : ℕ) < (4 : ℝ) := by exact_mod_cast hmod4_lt
    linarith
  have h_floor_qs : ((q / (2 * s) : ℕ) : ℝ) ≥ q / (4 * s) := by
    have hqs1 : (q / (2 * s) : ℕ) ≥ 1 := hqs
    have hs2 : (0 : ℝ) < 2 * s := by positivity
    have hq_real_ge : (q : ℝ) ≥ 4 * s := by exact_mod_cast hq_ge_4s
    have hqs3 : (q : ℝ) / (2 * s) ≥ 2 := by rw [ge_iff_le]; rw [le_div_iff₀ hs2]; linarith
    have hdivmod : (q : ℕ) = (2 * s) * (q / (2 * s)) + q % (2 * s) := (Nat.div_add_mod q (2 * s)).symm
    have hdivmod_real : (q : ℝ) = (2 * s) * (q / (2 * s) : ℕ) + (q % (2 * s) : ℕ) := by
      push_cast; exact_mod_cast hdivmod
    have hmod_bound : (q % (2 * s) : ℕ) < 2 * s := Nat.mod_lt q (by positivity)
    have hmod_bound' : ((q % (2 * s) : ℕ) : ℝ) < 2 * s := by
      have h1 : (q % (2 * s) : ℕ) < 2 * s := hmod_bound
      have h2 : ((q % (2 * s) : ℕ) : ℝ) < (2 * s : ℕ) := by exact_mod_cast h1
      simp only [Nat.cast_mul, Nat.cast_ofNat] at h2
      exact h2
    have : (q : ℝ) / (4 * s) = (q : ℝ) / (2 * s) / 2 := by ring
    rw [this]
    have heq : (q : ℝ) / (2 * s) = (q / (2 * s) : ℕ) + ((q % (2 * s) : ℕ) : ℝ) / (2 * s) := by
      rw [hdivmod_real]; field_simp
    rw [heq]
    have hmod_frac_lt : ((q % (2 * s) : ℕ) : ℝ) / (2 * s) < 1 := by
      rw [div_lt_one hs2]; exact hmod_bound'
    linarith
  have h_floor_q2_pow : (((q / 2) ^ (k - 3) : ℕ) : ℝ) ≥ (q / 4) ^ (k - 3) := by
    have h1 : (((q / 2) ^ (k - 3) : ℕ) : ℝ) = ((q / 2 : ℕ) : ℝ) ^ (k - 3) := by
      rw [Nat.cast_pow]
    rw [h1]
    exact pow_le_pow_left₀ (by positivity) h_floor_q2 _
  -- Product bound: floor_prod ≥ q^(k-1) / (4^(k-1) * s)
  have h_floor_prod : ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ) ≥
      q ^ (k - 1) / (4 ^ (k - 1) * s) := by
    have h4s_pos : (0 : ℝ) < 4 * s := by positivity
    have hpow_pos : (0 : ℝ) < 4 ^ (k - 1) := by positivity
    have h4s_prod : (4 : ℝ) * (4 * s) * 4 ^ (k - 3) = 4 ^ (k - 1) * s := by
      have : k - 1 = (k - 3) + 2 := by omega
      rw [this, pow_add, pow_two]
      ring
    have h4pos : (0 : ℝ) < 4 := by positivity
    have hpow_pos' : (0 : ℝ) < 4 ^ (k - 3) := pow_pos h4pos _
    have hq_pos' : (0 : ℝ) < q := by exact_mod_cast hq_pos
    have hpow_cancel : ((q : ℝ) / 4) ^ (k - 3) * 4 ^ (k - 3) = q ^ (k - 3) := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ h4pos.ne')]
    have hexp : (k - 3) + 2 = k - 1 := by omega
    calc ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ)
        ≥ (q / 4) * (q / (4 * s)) * (q / 4) ^ (k - 3) := by gcongr
      _ = q ^ 2 * (q / 4) ^ (k - 3) / (16 * s) := by field_simp; ring
      _ = q ^ 2 * (q ^ (k - 3) / 4 ^ (k - 3)) / (16 * s) := by rw [div_pow]
      _ = q ^ (k - 1) / (4 ^ (k - 1) * s) := by
          have h2_add : 2 + (k - 3) = k - 1 := by omega
          have h4k : (4 : ℝ) ^ (k - 1) = 4 ^ (k - 3) * 4 ^ 2 := by rw [← pow_add]; congr 1; omega
          field_simp
          rw [← pow_add, h2_add]
          rw [h4k]
          ring
  -- Now: #(constructedSets) ≥ floor_prod / k! ≥ q^(k-1) / (4^(k-1) * k! * s)
  have hcard_final : ( #(constructedSets h s q k) : ℝ) ≥ q ^ (k - 1) / (4 ^ (k - 1) * k.factorial * s) := by
    have hfactorial_pos : (0 : ℝ) < k.factorial := hkfact_pos
    have hdenom_pos : (0 : ℝ) < 4 ^ (k - 1) * s := by positivity
    have hdenom_pos2 : (0 : ℝ) < 4 ^ (k - 1) * k.factorial * s := by positivity
    have hcard_lower' : ( #(constructedSets h s q k) : ℝ) ≥ ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ) / k.factorial := by
      rw [ge_iff_le, div_le_iff₀ hfactorial_pos]
      exact hcard_lower
    have hdiv : ((q / 2 : ℕ) : ℝ) * ((q / (2 * s) : ℕ) : ℝ) * (((q / 2) ^ (k - 3) : ℕ) : ℝ) / k.factorial ≥
        (q ^ (k - 1) / (4 ^ (k - 1) * s)) / k.factorial := by
      apply div_le_div_of_nonneg_right h_floor_prod (le_of_lt hfactorial_pos)
    have hsimp : ((q : ℝ) ^ (k - 1) / (4 ^ (k - 1) * s)) / k.factorial = (q : ℝ) ^ (k - 1) / (4 ^ (k - 1) * k.factorial * s) := by
      rw [div_div]
      ring
    linarith [hcard_lower', hdiv, hsimp]
  -- Goal: (1/(4^(k-1)*k!)) * q^(k-1) / s ≤ #(constructedSets)
  convert hcard_final.le using 1
  field_simp [hkfact_pos.ne', hs_pos_real.ne']

/-- Part (iii), keeping the factor `h-ell+1` in view instead of hiding it inside
the constant. -/
theorem central_part_iii (h k ell : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k)
    (hell : ell < h) :
    ∃ c : ℝ, 0 < c ∧ ∃ Q : ℕ, ∀ q ≥ Q,
      c * q ^ (k - 1) / (h - ell + 1) ≤
        #(sumsetSizeClass h q k (P h k ell)) := by
  by_cases hell0 : 0 < ell
  · -- Case ell > 0: use constructedSets bound
    obtain ⟨c, hc_pos, Q, hQ⟩ := constructedSets_eventual_real_lower h k ell hk hell0 hell
    use c, hc_pos, Q
    intro q hq
    have h1 := hQ q hq
    have h2 := constructedSets_subset_sizeClass h q k ell hk hell0 hell
    exact h1.trans (by exact Nat.cast_le.mpr (Finset.card_le_card h2))
  · -- Case ell = 0: use central_part_i since P h k 0 = M h k
    have hell_eq : ell = 0 := Nat.eq_zero_of_not_pos hell0
    subst hell_eq
    simp only [P, if_true, Nat.sub_zero]
    obtain ⟨Q_i, hQ_i⟩ := central_part_i h k hh hk
    -- Use Q = max Q_i 1 to ensure positive constant
    let Q := max Q_i 1
    have hQ_ge_Qi : Q ≥ Q_i := le_max_left _ _
    have hQ_ge_1 : Q ≥ 1 := le_max_right _ _
    have hQ_pos : (0 : ℝ) < Q := by positivity
    -- `q^k ≥ Q * q^(k-1)`, so `c = (h+1) * Q / (2 * k!)` works.
    refine ⟨(h + 1 : ℝ) * (1 / (2 * k.factorial : ℝ)) * Q, ?_, Q, ?_⟩
    · positivity
    · intro q hq
      have hq_i : q ≥ Q_i := hq.trans' hQ_ge_Qi
      have h1 := (hQ_i q hq_i).1
      simp only [Nat.cast_zero, sub_zero]
      calc ((h + 1 : ℝ) * (1 / (2 * k.factorial : ℝ)) * Q) * q ^ (k - 1) / (h + 1 : ℝ)
          = (1 / (2 * k.factorial : ℝ)) * Q * q ^ (k - 1) := by field_simp
        _ ≤ (1 / (2 * k.factorial : ℝ)) * q * q ^ (k - 1) := by gcongr
        _ = (1 / (2 * k.factorial : ℝ)) * q ^ k := by
            have hqk : (q : ℝ) * q ^ (k - 1) = q ^ k := by
              rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
            rw [mul_assoc, hqk]
        _ ≤ #(sumsetSizeClass h q k (M h k)) := h1

/-- Combined formal version of all three parts of the Central Theorem. -/
theorem central_theorem (h k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) :
    (∃ Q : ℕ, ∀ q ≥ Q,
      (1 / (2 * k.factorial : ℝ)) * q ^ k ≤
        #(sumsetSizeClass h q k (M h k)) ∧
      (#(sumsetSizeClass h q k (M h k)) : ℝ) ≤ q ^ k) ∧
    (∃ Q : ℕ, ∀ q ≥ Q,
      (#((qSubsets q k).filter fun A ↦
        ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)) : ℝ) ≤
      3 ^ (2 * k - 2) * h ^ (2 * k - 2) * q ^ (k - 2)) ∧
    (∀ ell < h, ∃ c : ℝ, 0 < c ∧ ∃ Q : ℕ, ∀ q ≥ Q,
      c * q ^ (k - 1) / (h - ell + 1) ≤
        #(sumsetSizeClass h q k (P h k ell))) := by
  exact ⟨central_part_i h k hh hk, central_part_ii h k hh hk, fun ell hell => central_part_iii h k ell hh hk hell⟩

/-- Every listed size eventually beats every unlisted one, compared size by
size. -/
theorem listed_more_frequent_than_unlisted (h k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) :
    ∃ Q : ℕ, ∀ q ≥ Q, ∀ ell < h, ∀ n : ℕ,
      (∀ j < h, n ≠ P h k j) →
      #(sumsetSizeClass h q k n) < #(sumsetSizeClass h q k (P h k ell)) := by
  -- Get the upper bound on unlisted sets from central_part_ii
  obtain ⟨Q_unlisted, hunified⟩ := central_part_ii h k hh hk
  -- For unlisted n, sumsetSizeClass h q k n ⊆ filter, so its size is bounded by hunified
  have unlisted_le : ∀ q n, q ≥ Q_unlisted → (∀ j < h, n ≠ P h k j) →
      #(sumsetSizeClass h q k n) ≤ 3 ^ (2 * k - 2) * h ^ (2 * k - 2) * q ^ (k - 2) := by
    intro q n hq hn
    -- First show sumsetSizeClass h q k n ⊆ filter
    have sub : sumsetSizeClass h q k n ⊆ (qSubsets q k).filter (fun A => ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell)) := by
      intro A hA
      simp only [sumsetSizeClass] at hA ⊢
      simp only [Finset.mem_filter] at hA ⊢
      obtain ⟨hA_qsub, v, hv_tup, hv_set, hv_card⟩ := hA
      refine ⟨hA_qsub, fun ell hellit ⟨hA'_qsub, w, hw_tup, hw_set, hw_card⟩ => ?_⟩
      -- `tupleSet` is injective on increasing tuples, so `v = w`.
      have hbij := tupleSet_bijective q k
      have hv_in : v ∈ (increasingTuples q k : Finset (Fin k → ℕ)) := hv_tup
      have hw_in : w ∈ (increasingTuples q k : Finset (Fin k → ℕ)) := hw_tup
      have hvsets : tupleSet v = tupleSet w := hv_set.trans hw_set.symm
      have hvw : v = w := hbij.2.1 hv_in hw_in hvsets
      subst hvw
      exact hn ell hellit (hv_card.symm.trans hw_card)
    have := Finset.card_le_card sub
    have h' := hunified q hq
    have hc : ((sumsetSizeClass h q k n).card : ℝ) ≤ ((qSubsets q k).filter (fun A => ∀ ell < h, A ∉ sumsetSizeClass h q k (P h k ell))).card := by exact_mod_cast this
    exact_mod_cast le_trans hc h'
  -- Use central_part_iii for each ell < h to get lower bounds
  choose! c hc_pos Q_ell hQ_ell using fun ell hell => central_part_iii h k ell hh hk hell
  let Q_max_ell := Finset.sup (Finset.range h) Q_ell
  -- Define the threshold Q
  let C := (3 : ℝ) ^ (2 * k - 2) * h ^ (2 * k - 2)
  have h_pos : (0 : ℝ) < 1 := by norm_num
  -- `c ell * q^(k-1)/(h-ell+1) = (c ell * q/(h-ell+1)) * q^(k-2)`, so it is enough
  -- to take `q > C * (h-ell+1) / c ell`.
  let R := fun ell => Nat.ceil ((C * (h - ell + 1) / c ell) + 1)
  let Q := max Q_unlisted (max Q_max_ell (Finset.sup (Finset.range h) R))
  use Q
  intro q hq ell hell n hn
  -- Get the bounds from hq : q ≥ Q
  have hq_ul : q ≥ Q_unlisted := le_trans (le_max_left _ _) hq
  have hq_max_ell : q ≥ Q_max_ell := le_trans (le_max_right _ _ |> le_trans (le_max_left _ _)) hq
  have hle : R ell ≤ Finset.sup (Finset.range h) R := Finset.le_sup (Finset.mem_range.mpr hell)
  have hq_R_ell : q ≥ R ell := le_trans hle (le_trans (le_max_right _ _ |> le_trans (le_max_right _ _)) hq)
  have hle2 : Q_ell ell ≤ Finset.sup (Finset.range h) Q_ell := Finset.le_sup (Finset.mem_range.mpr hell)
  have hq_ell : q ≥ Q_ell ell := le_trans hle2 (le_trans (le_max_right _ _ |> le_trans (le_max_left _ _)) hq)
  -- Bound the unlisted class from above and the listed one from below.
  have unlisted_bound := unlisted_le q n hq_ul hn
  have listed_bound := hQ_ell ell hell q hq_ell
  have hq_R_def : q ≥ Nat.ceil (C * (h - ell + 1) / c ell + 1) := hq_R_ell
  have hq_gt : (q : ℝ) > C * (h - ell + 1) / c ell := by
    have hq_nat : q ≥ R ell := hq_R_ell
    have hR_def : R ell = Nat.ceil (C * (h - ell + 1) / c ell + 1) := rfl
    rw [hR_def] at hq_nat
    have h1 : C * (h - ell + 1) / c ell + 1 ≤ q := Nat.ceil_le.mp hq_nat
    linarith
  -- From hq_gt: c ell * q > C * (h - ell + 1)
  have hcq : c ell * q > C * (h - ell + 1) := by
    have hc := hc_pos ell hell
    have step1 : c ell * (C * (h - ell + 1) / c ell) = C * (h - ell + 1) := by field_simp
    have step2 : c ell * (C * (h - ell + 1) / c ell) < c ell * q := mul_lt_mul_of_pos_left hq_gt hc
    linarith
  -- Same comparison in the other branch.
  have unlisted_bound := unlisted_le q n hq_ul hn
  have listed_bound := hQ_ell ell hell q hq_ell
  -- `q ≥ 1`, since `q ≥ R ell ≥ 1`.
  have hC_pos : C > 0 := by positivity
  have hc_pos_ell : c ell > 0 := hc_pos ell hell
  have hdenom_pos : (h : ℝ) - ell + 1 > 0 := by
    have : (h : ℝ) ≥ ell + 1 := by
      simp only [ge_iff_le, Nat.cast_add, Nat.cast_one]
      exact_mod_cast hell
    linarith
  have hterm_pos : C * (h - ell + 1) / c ell > 0 := div_pos (mul_pos hC_pos hdenom_pos) hc_pos_ell
  have hR_pos : R ell ≥ 1 := Nat.ceil_pos.mpr (by linarith : 0 < C * (h - ell + 1) / c ell + 1)
  have hR_ell_eq : R ell = Nat.ceil (C * (h - ell + 1) / c ell + 1) := rfl
  have hR_ell_ge1 : R ell ≥ 1 := hR_pos
  have hq1 : q ≥ 1 := Nat.le_trans hR_ell_ge1 hq_R_ell
  have hq1R : (q : ℝ) ≥ 1 := by exact Nat.one_le_cast.mpr hq1
  -- Rewrite q^(k-1) = q * q^(k-2)
  have hexp : k - 1 = 1 + (k - 2) := by omega
  have hq_pow : (q : ℝ) ^ (k - 1) = q * q ^ (k - 2) := by
    rw [hexp, pow_add, pow_one]
  -- Therefore c ell * q^(k-1) / (h - ell + 1) = (c ell * q / (h - ell + 1)) * q^(k-2)
  have hlisted_simp : c ell * q ^ (k - 1) / ((h : ℝ) - ell + 1) = (c ell * q / ((h : ℝ) - ell + 1)) * q ^ (k - 2) := by
    rw [hq_pow]
    ring
  -- Since c ell * q > C * (h - ell + 1), we have c ell * q / (h - ell + 1) > C
  have hC_lt : C < c ell * q / ((h : ℝ) - ell + 1) := by
    have hh_denom : (h : ℝ) - ell + 1 > 0 := hdenom_pos
    rw [lt_div_iff₀ hh_denom]
    exact hcq
  have hlisted_gt : c ell * q ^ (k - 1) / ((h : ℝ) - ell + 1) > C * q ^ (k - 2) := by
    rw [hlisted_simp]
    exact mul_lt_mul_of_pos_right hC_lt (pow_pos (by linarith : (q : ℝ) > 0) _)
  -- Convert unlisted_bound to ℝ
  have unlisted_bound_R : ((sumsetSizeClass h q k n).card : ℝ) ≤ C * q ^ (k - 2) := by
    have := unlisted_bound
    simp only [C] at *
    exact_mod_cast this
  -- Combine
  have : ((sumsetSizeClass h q k n).card : ℝ) < ((sumsetSizeClass h q k (P h k ell)).card : ℝ) := by
    calc ((sumsetSizeClass h q k n).card : ℝ) ≤ C * q ^ (k - 2) := unlisted_bound_R
      _ < c ell * q ^ (k - 1) / ((h : ℝ) - ell + 1) := hlisted_gt
      _ ≤ ((sumsetSizeClass h q k (P h k ell)).card : ℝ) := listed_bound
  exact_mod_cast this

/-- The full corollary: the frequency comparison together with the gap formula. -/
theorem frequency_and_gap_corollary (h k : ℕ) (hh : 2 ≤ h) (hk : 3 ≤ k) :
    (∃ Q : ℕ, ∀ q ≥ Q, ∀ ell < h, ∀ n : ℕ,
      (∀ j < h, n ≠ P h k j) →
      #(sumsetSizeClass h q k n) < #(sumsetSizeClass h q k (P h k ell))) ∧
    (∀ ell, ell + 1 < h →
      P h k ell - P h k (ell + 1) = Nat.choose (ell + k - 2) (k - 2)) := by
  constructor
  · exact listed_more_frequent_than_unlisted h k hh hk
  · intro ell hell
    simp only [P]
    have : ell + 1 - 1 = ell := by omega
    simp [this]
    rcases ell with _ | ell
    · -- ell = 0 case
      simp [M]
      have h1 : (k - 2).choose (k - 2) = 1 := Nat.choose_self (k - 2)
      have h2 : (h + k - 1).choose (k - 1) ≥ 1 := Nat.choose_pos (by omega : k - 1 ≤ h + k - 1)
      omega
    · -- ell = n + 1 case
      simp [M]
      -- `A - B - (A - C) = C - B`, and then Pascal.
      have hk2 : k - 2 + 1 = k - 1 := by omega
      have pell : ell + k = Nat.succ (ell + k - 1) := by omega
      have pk : k - 1 = Nat.succ (k - 2) := by omega
      have pascal : (ell + k).choose (k - 1) = (ell + k - 1).choose (k - 1) + (ell + k - 1).choose (k - 2) := by
        rw [pell, pk]
        rw [Nat.choose_succ_succ]
        have : (ell + k - 1).succ - 1 = ell + k - 1 := by omega
        simp [this]
        apply add_comm
      -- RHS simplifies: ell + 1 + k - 2 = ell + k - 1
      have hrhs : ell + 1 + k - 2 = ell + k - 1 := by omega
      rw [hrhs]
      set A := (h + k - 1).choose (k - 1) with hA
      set B := (ell + k - 1).choose (k - 1) with hB
      set C := (ell + k).choose (k - 1) with hC
      -- A ≥ C since h + k - 1 ≥ ell + k (because h > ell + 1)
      have hA_ge_C : A ≥ C := by
        unfold A C
        apply Nat.choose_le_choose
        omega
      -- C ≥ B by Pascal (or choose monotonicity)
      have hC_ge_B : C ≥ B := by
        unfold C B
        apply Nat.choose_le_choose
        omega
      -- First show C - B = (ell + k - 1).choose (k - 2)
      have hCB : C - B = (ell + k - 1).choose (k - 2) := by
        rw [pascal]
        exact Nat.add_sub_cancel_left B _
      -- Now show A - B - (A - C) = C - B
      rw [← hCB]
      omega

end
end Senger
