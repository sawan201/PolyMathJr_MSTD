module

public import RequestProject.Additional.Bstar

/-!
# Corollary `cor:proportion`: almost every set is a `B_h`-set

* `Sumsets.cor_proportion`: `1 - |ℬ_{h,k}(q)| / \binom{q}{k} = Θ(q^{-1})`.
* `Sumsets.cor_proportion_tendsto`: `|ℬ_{h,k}(q)| / \binom{q}{k} → 1`.
-/

@[expose] public section

open scoped Pointwise Nat
open Filter Topology

namespace Sumsets

open Finset

theorem card_BhSets (h k q : ℕ) : (BhSets h k q).card = sizeCount h k q (M h k) := rfl

theorem choose_lower (k q : ℕ) (hq : 2 * k ≤ q) : q ^ k ≤ 2 ^ k * k ! * q.choose k := by
  have h3 : (q + 1 - k) ^ k ≤ k ! * q.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.pow_sub_le_descFactorial q k
  have h4 : q ^ k ≤ 2 ^ k * (q + 1 - k) ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc q ^ k ≤ 2 ^ k * (k ! * q.choose k) := h4.trans (Nat.mul_le_mul_left _ h3)
    _ = _ := by ring

/-- **Corollary `cor:proportion`.** For fixed `k ≥ 3` and `h ≥ 2`,
`1 - |ℬ_{h,k}(q)| / \binom{q}{k} = Θ(q^{-1})`. -/
theorem cor_proportion (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c / q ≤ 1 - ((BhSets h k q).card : ℝ) / (q.choose k) ∧
      1 - ((BhSets h k q).card : ℝ) / (q.choose k) ≤ C / q := by
  set c : ℝ := 1 / (32 * h * k ! : ℕ)
  set C : ℝ := ((2 ^ k * k ! * (2 * h + 1) ^ (k - 1) : ℕ) : ℝ)
  refine ⟨c, C, by positivity, by positivity, 2 * k + 32 * h * (2 * h + 1) ^ (k - 1) + 1,
    fun q hq => ?_⟩
  have hsum := sizeCount_add h k q
  set N := ((kSubsets q k).filter (fun A => (h • A).card ≠ M h k)).card
  have hNup : N ≤ (2 * h + 1) ^ (k - 1) * q ^ (k - 1) := card_not_Bh_le h k q (by omega)
  have hP1 : P h k 1 = M h k - 1 := by simp [P, Mpred, M]
  have hM1 : 1 ≤ M h k := Nat.choose_pos (by omega)
  have hNlow : sizeCount h k q (P h k 1) ≤ N := by
    apply Finset.card_le_card
    intro A hA
    rw [Finset.mem_filter] at hA ⊢
    exact ⟨hA.1, by rw [hA.2, hP1]; omega⟩
  have hlow := sizeCount_P_lower h k 1 q hk le_rfl (by omega) (by omega)
  rw [show h - 1 + 1 = h by omega] at hlow
  have hch := choose_lower k q (by omega)
  have hchup := Nat.choose_le_pow q k
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hchpos : (0 : ℝ) < q.choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have hratio : 1 - ((BhSets h k q).card : ℝ) / (q.choose k) = (N : ℝ) / (q.choose k) := by
    rw [card_BhSets, eq_div_iff hchpos.ne', sub_mul, div_mul_cancel₀ _ hchpos.ne', one_mul]
    have : ((sizeCount h k q (M h k) : ℕ) : ℝ) + (N : ℝ) = (q.choose k : ℕ) := by
      exact_mod_cast hsum
    linarith
  rw [hratio]
  have hqk : (q : ℝ) ^ k = q * (q : ℝ) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  constructor
  · rw [div_le_div_iff₀ hq0 hchpos]
    have h1 : ((q ^ (k - 1) : ℕ) : ℝ) ≤ ((32 * h * k ! * sizeCount h k q (P h k 1) : ℕ) : ℝ) := by
      exact_mod_cast hlow
    have h2 : ((sizeCount h k q (P h k 1) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNlow
    have h3 : ((q.choose k : ℕ) : ℝ) ≤ ((q ^ k : ℕ) : ℝ) := by exact_mod_cast hchup
    push_cast at h1 h3
    have hc : c * (32 * h * k !) = 1 := by
      simp only [c]; push_cast; field_simp
    have hcpos : 0 ≤ c := by positivity
    calc c * (q.choose k : ℝ) ≤ c * (q : ℝ) ^ k := by gcongr
      _ = c * (q * (q : ℝ) ^ (k - 1)) := by rw [hqk]
      _ ≤ c * (q * (32 * h * k ! * (sizeCount h k q (P h k 1) : ℝ))) := by gcongr
      _ = q * (sizeCount h k q (P h k 1) : ℝ) * (c * (32 * h * k !)) := by ring
      _ = q * (sizeCount h k q (P h k 1) : ℝ) := by rw [hc, mul_one]
      _ ≤ (N : ℝ) * q := by rw [mul_comm]; gcongr
  · rw [div_le_div_iff₀ hchpos hq0]
    have h1 : (N : ℝ) ≤ (((2 * h + 1) ^ (k - 1) * q ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hNup
    have h2 : ((q ^ k : ℕ) : ℝ) ≤ ((2 ^ k * k ! * q.choose k : ℕ) : ℝ) := by exact_mod_cast hch
    push_cast at h1 h2
    simp only [C]
    push_cast
    calc (N : ℝ) * q ≤ ((2 * h + 1 : ℝ) ^ (k - 1) * (q : ℝ) ^ (k - 1)) * q := by gcongr
      _ = (2 * h + 1 : ℝ) ^ (k - 1) * (q : ℝ) ^ k := by rw [hqk]; ring
      _ ≤ (2 * h + 1 : ℝ) ^ (k - 1) * (2 ^ k * k ! * q.choose k) := by gcongr
      _ = _ := by ring

/-- **Corollary `cor:proportion`, "in particular".** `|ℬ_{h,k}(q)| / \binom{q}{k} → 1`. -/
theorem cor_proportion_tendsto (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    Tendsto (fun q : ℕ => ((BhSets h k q).card : ℝ) / (q.choose k)) atTop (𝓝 1) := by
  obtain ⟨c, C, hc, hC, q₀, hq₀⟩ := cor_proportion h k hk hh
  have hlim : Tendsto (fun q : ℕ => 1 - C / (q : ℝ)) atTop (𝓝 1) := by
    have : Tendsto (fun q : ℕ => C / (q : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop q₀] with q hq
    have := (hq₀ q hq).2
    linarith
  · filter_upwards [eventually_ge_atTop q₀] with q hq
    have := (hq₀ q hq).1
    have : (0 : ℝ) ≤ c / q := by positivity
    linarith

end Sumsets
