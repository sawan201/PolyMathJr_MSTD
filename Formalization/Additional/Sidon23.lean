module

public import RequestProject.Additional.Proportion

/-!
# Corollary `cor:proportion` for `(h, k) = (2, 3)`

A set `{a₁ < a₂ < a₃}` fails to be a Sidon (`B_2`) set exactly when `a₁ + a₃ = 2a₂`; counting
three-term progressions in `[q]` gives
`lim_{q→∞} q (1 - |ℬ_{2,3}(q)| / \binom{q}{3}) = 3/2` (`Sumsets.cor_proportion_23`).
-/

@[expose] public section

open scoped Pointwise Nat
open Filter Topology

namespace Sumsets

open Finset

theorem coeffVectors_2_3 : coeffVectors 2 3 =
    {![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1], ![1, 1, -2]} := by
  decide

theorem image_fin3 (v : Fin 3 → ℤ) : univ.image v = {v 0, v 1, v 2} := by
  ext x; simp [Fin.exists_fin_succ]; tauto

theorem not_B2_of_AP (v : Fin 3 → ℤ) (hv : v 0 + v 2 = 2 * v 1) :
    (sumsOf 2 v).card ≠ M 2 3 := by
  rw [ne_eq, card_sumsOf_eq_iff 2 (by norm_num)]
  intro hinj
  have hd : (![1, -2, 1] : Fin 3 → ℤ) ∈ coeffVectors 2 3 := by rw [coeffVectors_2_3]; simp
  have hdv : dot ![1, -2, 1] v = 0 := by simp [dot, Fin.sum_univ_three]; linarith
  obtain ⟨x, hx, y, hy, hxy, hxyv⟩ := (equal_sum_criterion v).mpr ⟨_, hd, hdv⟩
  exact hxy (hinj hx hy hxyv)

theorem AP_of_not_B2 (v : Fin 3 → ℤ) (hv : StrictMono v) (hne : (sumsOf 2 v).card ≠ M 2 3) :
    v 0 + v 2 = 2 * v 1 := by
  obtain ⟨d, hd, hdv⟩ := exists_orth_of_card_ne (by norm_num) hne
  have h01 : v 0 < v 1 := hv (by decide)
  have h12 : v 1 < v 2 := hv (by decide)
  rw [coeffVectors_2_3] at hd
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [dot, Fin.sum_univ_three] at hdv <;> linarith

/-- A set `A = {a₁ < a₂ < a₃}` is not a `B_2`-set iff `a₁ + a₃ = 2 a₂`. -/
theorem not_B2_iff {q : ℕ} {A : Finset ℤ} (hA : A ∈ kSubsets q 3) :
    (2 • A).card ≠ M 2 3 ↔ setVec 3 A 0 + setVec 3 A 2 = 2 * setVec 3 A 1 := by
  have hAk : A.card = 3 := (Finset.mem_powersetCard.mp hA).2
  rw [nsmul_eq_sumsOf_setVec 2 hAk]
  exact ⟨AP_of_not_B2 _ (setVec_strictMono hAk), not_B2_of_AP _⟩

/-- Pairs `(a, r)` with `a, r ≥ 1` and `a + 2r ≤ q`. -/
def apPairs (q : ℕ) : Finset (ℕ × ℕ) := (Icc 1 q).biUnion (fun r => Icc 1 (q - 2 * r) ×ˢ {r})

theorem mem_apPairs {q : ℕ} {p : ℕ × ℕ} :
    p ∈ apPairs q ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 + 2 * p.2 ≤ q := by
  obtain ⟨a, r⟩ := p
  simp only [apPairs, mem_biUnion, mem_Icc, mem_product, mem_singleton]
  constructor
  · rintro ⟨r', ⟨h1, h2⟩, ⟨h3, h4⟩, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨r, ⟨h2, by omega⟩, ⟨h1, by omega⟩, rfl⟩

theorem card_apPairs (q : ℕ) : (apPairs q).card = ∑ r ∈ Icc 1 q, (q - 2 * r) := by
  rw [apPairs, card_biUnion]
  · refine sum_congr rfl fun r _ => ?_
    simp
  · intro r _ r' _ hrr'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [mem_product, mem_singleton] at hp hp'
    exact hrr' (hp.2.symm.trans hp'.2)

theorem sum_ap_succ (q : ℕ) :
    ∑ r ∈ Icc 1 (q + 1), (q + 1 - 2 * r) = ∑ r ∈ Icc 1 q, (q - 2 * r) + q / 2 := by
  rw [Finset.sum_Icc_succ_top (by omega), show q + 1 - 2 * (q + 1) = 0 by omega, add_zero]
  have : ∀ r ∈ Icc 1 q, q + 1 - 2 * r = (q - 2 * r) + (if 2 * r ≤ q then 1 else 0) := by
    intro r _; split_ifs <;> omega
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_boole]
  congr 1
  have : (Icc 1 q).filter (fun r => 2 * r ≤ q) = Icc 1 (q / 2) := by
    ext r; simp only [mem_filter, mem_Icc]; omega
  simp [this]

theorem sum_ap_eq (q : ℕ) :
    4 * ∑ r ∈ Icc 1 q, (q - 2 * r) + (if q % 2 = 0 ∧ q ≠ 0 then 1 else 0) = (q - 1) ^ 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_ap_succ]
    rcases Nat.even_or_odd' q with ⟨t, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · have h1 : (2 * t) % 2 = 0 := by omega
        have h2 : (2 * t + 1) % 2 = 1 := by omega
        simp only [h1, h2, ne_eq] at ih ⊢
        simp only [show ¬ (2 * t = 0) by omega, not_false_eq_true, and_self, if_true] at ih
        simp only [show ¬ (1 = 0) by omega, false_and, if_false, add_zero]
        rw [show 2 * t / 2 = t by omega, show 2 * t + 1 - 1 = 2 * t by omega]
        have : (2 * t - 1) ^ 2 + 4 * t = (2 * t) ^ 2 + 1 := by
          obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
          rw [show 2 * (u + 1) - 1 = 2 * u + 1 by omega]; ring
        nlinarith
    · have h1 : (2 * t + 1) % 2 = 1 := by omega
      have h2 : (2 * t + 1 + 1) % 2 = 0 := by omega
      simp only [h1, h2, ne_eq] at ih ⊢
      simp only [show ¬ (1 = 0) by omega, false_and, if_false, add_zero] at ih
      simp only [show ¬ (2 * t + 1 + 1 = 0) by omega, not_false_eq_true, and_self, if_true]
      rw [show (2 * t + 1) / 2 = t by omega, show 2 * t + 1 + 1 - 1 = 2 * t + 1 by omega]
      rw [show 2 * t + 1 - 1 = 2 * t by omega] at ih
      nlinarith

/-- The three-term progression `(a, a + r, a + 2r)`. -/
def apVec (p : ℕ × ℕ) : Fin 3 → ℤ := ![(p.1 : ℤ), p.1 + p.2, p.1 + 2 * p.2]

/-- The non-Sidon sets in `\binom{[q]}{3}` are exactly the progressions `{a, a+r, a+2r}`. -/
theorem nonB2_eq_image (q : ℕ) :
    (kSubsets q 3).filter (fun A => (2 • A).card ≠ M 2 3) =
      (apPairs q).image (fun p => univ.image (apVec p)) := by
  ext A
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hA, hne⟩
    have hAk : A.card = 3 := (Finset.mem_powersetCard.mp hA).2
    have hap := (not_B2_iff hA).mp hne
    have hvq := setVec_mem_tuples hA
    rw [tuples, Fintype.mem_piFinset] at hvq
    have h0 := hvq 0
    have h2 := hvq 2
    rw [mem_Icc] at h0 h2
    have h01 : setVec 3 A 0 < setVec 3 A 1 := setVec_strictMono hAk (by decide)
    refine ⟨((setVec 3 A 0).toNat, (setVec 3 A 1 - setVec 3 A 0).toNat), ?_, ?_⟩
    · rw [mem_apPairs]; simp only; omega
    · conv_rhs => rw [← image_setVec hAk]
      rw [image_fin3, image_fin3]
      simp only [apVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      congr 2
      · ring
      · congr 1; linarith
  · rintro ⟨p, hp, rfl⟩
    rw [mem_apPairs] at hp
    have hinj : Function.Injective (apVec p) := by
      apply StrictMono.injective
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [apVec] <;> omega
    refine ⟨?_, ?_⟩
    · rw [kSubsets, mem_powersetCard]
      refine ⟨?_, card_image_of_injective' hinj⟩
      intro x hx
      rw [image_fin3] at hx
      simp only [apVec, mem_insert, mem_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hx
      rw [mem_Icc]
      rcases hx with rfl | rfl | rfl <;> constructor <;> omega
    · rw [card_nsmul_image]
      exact not_B2_of_AP _ (by simp [apVec]; ring)

theorem card_nonB2 (q : ℕ) :
    ((kSubsets q 3).filter (fun A => (2 • A).card ≠ M 2 3)).card = (apPairs q).card := by
  rw [nonB2_eq_image, card_image_of_injOn]
  rintro ⟨a, r⟩ hp ⟨a', r'⟩ hp' heq
  simp only [mem_coe, mem_apPairs] at hp hp'
  have heq' : ({(a : ℤ), (a : ℤ) + (r : ℤ), (a : ℤ) + 2 * (r : ℤ)} : Finset ℤ) =
      {(a' : ℤ), (a' : ℤ) + (r' : ℤ), (a' : ℤ) + 2 * (r' : ℤ)} := by
    have := heq
    simp only [image_fin3, apVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    exact this
  have m1 : (a : ℤ) ∈ ({(a' : ℤ), (a' : ℤ) + (r' : ℤ), (a' : ℤ) + 2 * (r' : ℤ)} : Finset ℤ) := by
    rw [← heq']; simp
  have m2 : (a' : ℤ) ∈ ({(a : ℤ), (a : ℤ) + (r : ℤ), (a : ℤ) + 2 * (r : ℤ)} : Finset ℤ) := by
    rw [heq']; simp
  have m3 : (a : ℤ) + 2 * (r : ℤ) ∈
      ({(a' : ℤ), (a' : ℤ) + (r' : ℤ), (a' : ℤ) + 2 * (r' : ℤ)} : Finset ℤ) := by
    rw [← heq']; simp
  have m4 : (a' : ℤ) + 2 * (r' : ℤ) ∈
      ({(a : ℤ), (a : ℤ) + (r : ℤ), (a : ℤ) + 2 * (r : ℤ)} : Finset ℤ) := by
    rw [heq']; simp
  simp only [mem_insert, mem_singleton] at m1 m2 m3 m4
  have e1 : a = a' := by omega
  have e2 : r = r' := by omega
  rw [e1, e2]

/-- `4 (\binom{q}{3} - |ℬ_{2,3}(q)|)` is `(q-1)^2` or `(q-1)^2 - 1`. -/
theorem four_mul_card_nonB2 (q : ℕ) :
    4 * ((kSubsets q 3).filter (fun A => (2 • A).card ≠ M 2 3)).card +
      (if q % 2 = 0 ∧ q ≠ 0 then 1 else 0) = (q - 1) ^ 2 := by
  rw [card_nonB2, card_apPairs, sum_ap_eq]

/-- **Corollary `cor:proportion`, case `(h, k) = (2, 3)`.**
`lim_{q→∞} q (1 - |ℬ_{2,3}(q)| / \binom{q}{3}) = 3/2`. -/
theorem cor_proportion_23 :
    Tendsto (fun q : ℕ => (q : ℝ) * (1 - ((BhSets 2 3 q).card : ℝ) / (q.choose 3)))
      atTop (𝓝 (3 / 2)) := by
  have hbounds : ∀ q : ℕ, 3 ≤ q →
      (3 / 2 : ℝ) * ((q : ℝ) / ((q : ℝ) - 1)) ≤ (q : ℝ) * (1 - ((BhSets 2 3 q).card : ℝ) / (q.choose 3)) ∧
      (q : ℝ) * (1 - ((BhSets 2 3 q).card : ℝ) / (q.choose 3)) ≤ (3 / 2 : ℝ) * (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
    intro q hq
    set N := ((kSubsets q 3).filter (fun A => (2 • A).card ≠ M 2 3)).card
    have hsum := sizeCount_add 2 3 q
    have h4 := four_mul_card_nonB2 q
    have hch : q.choose 3 * 6 = q * (q - 1) * (q - 2) := by
      have := Nat.descFactorial_eq_factorial_mul_choose q 3
      simp [Nat.descFactorial, Nat.factorial] at this
      rw [mul_comm, ← this]; ring
    set x : ℝ := (q : ℝ) with hxdef
    have hx3 : (3 : ℝ) ≤ x := by simp only [x]; exact_mod_cast hq
    have hchR : (q.choose 3 : ℝ) = x * (x - 1) * (x - 2) / 6 := by
      have : ((q.choose 3 * 6 : ℕ) : ℝ) = ((q * (q - 1) * (q - 2) : ℕ) : ℝ) := by
        exact_mod_cast hch
      push_cast [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_sub (show 2 ≤ q by omega)] at this
      simp only [x]; linarith
    have hNB : ((BhSets 2 3 q).card : ℝ) + N = q.choose 3 := by
      rw [card_BhSets]; exact_mod_cast hsum
    have hε : (x - 1) ^ 2 - 1 ≤ 4 * (N : ℝ) ∧ 4 * (N : ℝ) ≤ (x - 1) ^ 2 := by
      have : ((4 * N + (if q % 2 = 0 ∧ q ≠ 0 then 1 else 0) : ℕ) : ℝ) = (((q - 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h4
      push_cast [Nat.cast_sub (show 1 ≤ q by omega)] at this
      split_ifs at this <;> simp only [x] <;> constructor <;> linarith
    have hcpos : (0 : ℝ) < q.choose 3 := by rw [hchR]; apply div_pos _ (by norm_num); nlinarith
    have hf : (q : ℝ) * (1 - ((BhSets 2 3 q).card : ℝ) / (q.choose 3)) =
        6 * N / ((x - 1) * (x - 2)) := by
      have h1 : 1 - ((BhSets 2 3 q).card : ℝ) / (q.choose 3) = N / q.choose 3 := by
        field_simp; linarith
      rw [h1, hchR]
      have : x ≠ 0 := by linarith
      have : x - 1 ≠ 0 := by intro h; linarith
      have : x - 2 ≠ 0 := by intro h; linarith
      field_simp
      rw [hxdef]; ring
    rw [hf]
    have hd1 : (0 : ℝ) < x - 1 := by linarith
    have hd2 : (0 : ℝ) < x - 2 := by linarith
    constructor
    · rw [mul_div_assoc', div_le_div_iff₀ hd1 (by positivity)]
      nlinarith [hε.1]
    · rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hd2]
      nlinarith [hε.2]
  have hl1 : Tendsto (fun q : ℕ => (3 / 2 : ℝ) * ((q : ℝ) / (q - 1))) atTop (𝓝 (3 / 2)) := by
    have : Tendsto (fun q : ℕ => (q : ℝ) / (q - 1)) atTop (𝓝 1) := by
      have h : Tendsto (fun q : ℕ => 1 + 1 / ((q : ℝ) - 1)) atTop (𝓝 (1 + 0)) := by
        refine tendsto_const_nhds.add (tendsto_const_nhds.div_atTop ?_)
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with q hq
      have : (q : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ q := by exact_mod_cast hq
        intro h; linarith
      field_simp; ring
    simpa using this.const_mul (3 / 2 : ℝ)
  have hl2 : Tendsto (fun q : ℕ => (3 / 2 : ℝ) * (((q : ℝ) - 1) / (q - 2))) atTop (𝓝 (3 / 2)) := by
    have : Tendsto (fun q : ℕ => ((q : ℝ) - 1) / (q - 2)) atTop (𝓝 1) := by
      have h : Tendsto (fun q : ℕ => 1 + 1 / ((q : ℝ) - 2)) atTop (𝓝 (1 + 0)) := by
        refine tendsto_const_nhds.add (tendsto_const_nhds.div_atTop ?_)
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 3] with q hq
      have : (q : ℝ) - 2 ≠ 0 := by
        have : (3 : ℝ) ≤ q := by exact_mod_cast hq
        intro h; linarith
      field_simp; ring
    simpa using this.const_mul (3 / 2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl1 hl2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with q hq using (hbounds q hq).1
  · filter_upwards [eventually_ge_atTop 3] with q hq using (hbounds q hq).2

end Sumsets
