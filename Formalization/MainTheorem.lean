module

public import RequestProject.Construction

/-!
# The main theorem (Theorem `thm:main`) and Corollary `cor:gap-pattern`
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset
open scoped Nat

theorem card_nsmul_image (h : ℕ) {k : ℕ} (v : Fin k → ℤ) :
    (h • univ.image v).card = (sumsOf h v).card := by rw [nsmul_image_eq_sumsOf]

/-- A coefficient vector orthogonal to an injective vector has weight at least `2`. -/
theorem two_le_weight {h k : ℕ} {v d : Fin k → ℤ} (hv : Function.Injective v)
    (hd : d ∈ coeffVectors h k) (hdv : dot d v = 0) : 2 ≤ weight d := by
  classical
  obtain ⟨hd0, hdsum, hdw, -, ⟨i0, hi0, -⟩⟩ := mem_coeffVectors.mp hd
  have h1 := le_weight d i0
  by_contra hlt
  push_neg at hlt
  have hw1 : weight d = 1 := by omega
  have hdi0 : d i0 = 1 := by
    have : (weight d : ℤ) = 1 := by exact_mod_cast hw1
    omega
  have hpos : ∀ l, l ≠ i0 → d l ≤ 0 := by
    intro l hl
    have hsum : ∑ m, (d m).toNat = 1 := hw1
    rw [← Finset.add_sum_erase _ _ (mem_univ i0), hdi0] at hsum
    simp only [Int.toNat_one, add_eq_left] at hsum
    have := (Finset.sum_eq_zero_iff.mp hsum) l (mem_erase.mpr ⟨hl, mem_univ l⟩)
    omega
  obtain ⟨j, hj⟩ : ∃ j, d j < 0 := by
    by_contra hcon
    push_neg at hcon
    apply hd0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcon i)).mp hdsum
    funext i; exact this i (mem_univ i)
  have hdj : d j = -1 := by
    have := neg_le_weight hdsum j
    have : (weight d : ℤ) = 1 := by exact_mod_cast hw1
    omega
  have hneg : ∀ l, l ≠ j → 0 ≤ d l := by
    intro l hl
    have hsum : ∑ m, negVec d m = 1 := by rw [sum_negVec hdsum, hw1]
    rw [← Finset.add_sum_erase _ _ (mem_univ j)] at hsum
    simp only [negVec, hdj, neg_neg, Int.toNat_one, add_eq_left] at hsum
    have := (Finset.sum_eq_zero_iff.mp hsum) l (mem_erase.mpr ⟨hl, mem_univ l⟩)
    omega
  have hij : i0 ≠ j := by intro h; rw [h] at hdi0; omega
  rw [dot_split _ _ i0 j hij] at hdv
  have hrest : ∑ l ∈ (univ.erase i0).erase j, d l * v l = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have := hpos l (ne_of_mem_erase (mem_of_mem_erase hl))
    have := hneg l (ne_of_mem_erase hl)
    have : d l = 0 := by omega
    simp [this]
  rw [hrest, hdi0, hdj] at hdv
  exact hij (hv (by linarith))

theorem exists_orth_of_card_ne {h k : ℕ} (hk : 1 ≤ k) {v : Fin k → ℤ}
    (hne : (sumsOf h v).card ≠ M h k) : ∃ d ∈ coeffVectors h k, dot d v = 0 := by
  rw [← equal_sum_criterion]
  rw [ne_eq, card_sumsOf_eq_iff h hk] at hne
  by_contra hcon
  apply hne
  intro x hx y hy hxy
  by_contra hne'
  exact hcon ⟨x, hx, y, hy, hne', hxy⟩

theorem P_eq_of_weight (h k w : ℕ) : P h k (h - w + 1) = M h k - M (h - w) k := by
  simp [P, Mpred]

/-- If at most one coefficient vector is orthogonal to the injective vector `v`, then
`|{x · v}|` is one of `P_0, …, P_{h-1}`. -/
theorem card_sumsOf_mem_P {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {v : Fin k → ℤ}
    (hv : Function.Injective v)
    (hno : ∀ d ∈ coeffVectors h k, ∀ e ∈ coeffVectors h k, dot d v = 0 → dot e v = 0 → d = e) :
    (sumsOf h v).card ∈ (range h).image (P h k) := by
  rw [Finset.mem_image]
  by_cases hex : ∃ d ∈ coeffVectors h k, dot d v = 0
  · obtain ⟨d, hd, hdv⟩ := hex
    have hw2 := two_le_weight hv hd hdv
    have hwh := (mem_coeffVectors.mp hd).2.2.1
    refine ⟨h - weight d + 1, by simp; omega, ?_⟩
    rw [P_eq_of_weight,
      gap_size_lemma hk v hd hdv (fun e he hev => hno e he d hd hev hdv)]
  · refine ⟨0, by simp; omega, ?_⟩
    simp only [P, Mpred]
    by_contra hne
    exact hex (exists_orth_of_card_ne hk (Ne.symm (by simpa using hne)))

/-- Bound `(eq:not-Bh-count)`: at most `(2h+1)^{k-1} q^{k-1}` sets `A ∈ \binom{[q]}{k}` have
`|hA| < M_{h,k}`. -/
theorem card_not_Bh_le (h k q : ℕ) (hk : 1 ≤ k) :
    ((kSubsets q k).filter (fun A => (h • A).card ≠ M h k)).card ≤
      (2 * h + 1) ^ (k - 1) * q ^ (k - 1) := by
  classical
  refine (card_kSubsets_filter_le q k _).trans ?_
  calc _ ≤ ((coeffVectors h k).biUnion
        (fun d => (tuples q k).filter (fun p => dot d p = 0))).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter, card_nsmul_image] at hv
        obtain ⟨d, hd, hdv⟩ := exists_orth_of_card_ne hk hv.2.2
        exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hv.1, hdv⟩⟩
    _ ≤ ∑ d ∈ coeffVectors h k, ((tuples q k).filter (fun p => dot d p = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ coeffVectors h k, q ^ (k - 1) := by
        apply Finset.sum_le_sum
        intro d hd
        exact card_tuples_dot_eq_zero_le q d (mem_coeffVectors.mp hd).1
    _ = (coeffVectors h k).card * q ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_coeffVectors_le h k hk)

/-- At most `(2h+1)^{2k-2} q^{k-2}` tuples `v ∈ [q]^k` are orthogonal to two distinct coefficient
vectors of `ℛ_{h,k}`. -/
theorem card_tuples_two_relations_le (h k q : ℕ) (hk : 2 ≤ k) :
    ((tuples q k).filter (fun v => ∃ d ∈ coeffVectors h k, ∃ e ∈ coeffVectors h k,
      d ≠ e ∧ dot d v = 0 ∧ dot e v = 0)).card ≤ (2 * h + 1) ^ (2 * k - 2) * q ^ (k - 2) := by
  classical
  set R := coeffVectors h k
  calc _ ≤ (((R ×ˢ R).filter (fun de => de.1 ≠ de.2)).biUnion
        (fun de => (tuples q k).filter (fun p => dot de.1 p = 0 ∧ dot de.2 p = 0))).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨d, hd, e, he, hde, hdv, hev⟩ := hv.2
        exact Finset.mem_biUnion.mpr ⟨(d, e), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hd, he⟩, hde⟩, Finset.mem_filter.mpr ⟨hv.1, hdv, hev⟩⟩
    _ ≤ ∑ de ∈ (R ×ˢ R).filter (fun de => de.1 ≠ de.2),
          ((tuples q k).filter (fun p => dot de.1 p = 0 ∧ dot de.2 p = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ de ∈ (R ×ˢ R).filter (fun de => de.1 ≠ de.2), q ^ (k - 2) := by
        apply Finset.sum_le_sum
        intro de hde
        rw [Finset.mem_filter, Finset.mem_product] at hde
        exact card_tuples_two_dot_eq_zero_le q hde.1.1 hde.1.2 hde.2
    _ ≤ (R ×ˢ R).card * q ^ (k - 2) := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ _ := by
        rw [Finset.card_product]
        apply Nat.mul_le_mul_right
        have := card_coeffVectors_le h k (by omega)
        calc R.card * R.card ≤ (2 * h + 1) ^ (k - 1) * (2 * h + 1) ^ (k - 1) :=
              Nat.mul_le_mul this this
          _ = _ := by rw [← pow_add]; congr 1; omega

/-- Explicit form of Theorem `thm:main`(2): for every `q`, at most `(2h+1)^{2k-2} q^{k-2}` sets
`A ∈ \binom{[q]}{k}` have `|hA| ∉ {P_0, …, P_{h-1}}`. -/
theorem card_exceptional_le (h k q : ℕ) (hh : 1 ≤ h) (hk : 2 ≤ k) :
    ((kSubsets q k).filter (fun A => (h • A).card ∉ (range h).image (P h k))).card ≤
      (2 * h + 1) ^ (2 * k - 2) * q ^ (k - 2) := by
  classical
  refine (card_kSubsets_filter_le q k _).trans (le_trans (Finset.card_le_card ?_)
    (card_tuples_two_relations_le h k q hk))
  intro v hv
  rw [Finset.mem_filter, card_nsmul_image] at hv
  rw [Finset.mem_filter]
  refine ⟨hv.1, ?_⟩
  have : ¬ ∀ d ∈ coeffVectors h k, ∀ e ∈ coeffVectors h k, dot d v = 0 → dot e v = 0 → d = e :=
    fun hno => hv.2.2 (card_sumsOf_mem_P hh (by omega) hv.2.1 hno)
  push_neg at this
  obtain ⟨d, hd, e, he, hdv, hev, hde⟩ := this
  exact ⟨d, hd, e, he, hde, hdv, hev⟩

/-- The arithmetic step of the lower bound in Theorem `thm:main`(3). -/
theorem arith_lower {m q s c E : ℕ} (hs : 2 ≤ s) (hq : 32 * s * E ≤ q) (hE : 1 ≤ E)
    (hc : (q / 2) * (q / (2 * s)) * q ^ m ≤ c + E * q ^ (m + 1)) :
    q ^ (m + 2) ≤ 32 * s * c := by
  have hA' : q < 2 * (q / 2 + 1) := Nat.lt_mul_div_succ q (show 0 < 2 by norm_num)
  have hB' : q < 2 * s * (q / (2 * s) + 1) := Nat.lt_mul_div_succ q (show 0 < 2 * s by omega)
  set A := q / 2
  set B := q / (2 * s)
  have h64 : 64 * E ≤ 32 * s * E := Nat.mul_le_mul_right _ (by omega)
  have hqA : q ≤ 4 * A := by omega
  have hqB : q ≤ 4 * s * B := by
    have : 4 * s ≤ q := by nlinarith
    nlinarith
  have hAB : q * q ≤ 16 * s * (A * B) := by
    calc q * q ≤ (4 * A) * (4 * s * B) := Nat.mul_le_mul hqA hqB
      _ = 16 * s * (A * B) := by ring
  have hmain : 2 * q ^ (m + 2) ≤ 32 * s * (A * B * q ^ m) := by
    calc 2 * q ^ (m + 2) = 2 * (q * q) * q ^ m := by ring
      _ ≤ 2 * (16 * s * (A * B)) * q ^ m := by gcongr
      _ = _ := by ring
  have hbadb : 32 * s * (E * q ^ (m + 1)) ≤ q ^ (m + 2) := by
    calc 32 * s * (E * q ^ (m + 1)) = (32 * s * E) * q ^ (m + 1) := by ring
      _ ≤ q * q ^ (m + 1) := Nat.mul_le_mul_right _ hq
      _ = q ^ (m + 2) := by ring
  have h1 : 32 * s * (A * B * q ^ m) ≤ 32 * s * c + 32 * s * (E * q ^ (m + 1)) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hc
  omega

/-- Explicit form of Theorem `thm:main`(3) for `1 ≤ ℓ < h`: for
`q ≥ 32 h (2h+1)^{k-1}`, at least `q^{k-1} / (32 (h-ℓ+1) k!)` sets `A ∈ \binom{[q]}{k}` have
`|hA| = P_ℓ`. -/
theorem sizeCount_P_lower (h k ℓ q : ℕ) (hk : 3 ≤ k) (hℓ : 1 ≤ ℓ) (hℓh : ℓ < h)
    (hq : 32 * h * (2 * h + 1) ^ (k - 1) ≤ q) :
    q ^ (k - 1) ≤ 32 * (h - ℓ + 1) * k ! * sizeCount h k q (P h k ℓ) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega] at hq ⊢
  set s := h - ℓ + 1 with hsdef
  have hs : 2 ≤ s := by omega
  have hsh : s ≤ h := by omega
  have hP : P h (m + 3) ℓ = M h (m + 3) - M (h - s) (m + 3) := by
    simp only [P, Mpred, if_neg (show ℓ ≠ 0 by omega)]
    congr 2; omega
  have hc := card_good_tuples_ge (m := m) h q s hs hsh
  set T := (tuples q (m + 3)).filter (fun v => Function.Injective v ∧
          (sumsOf h v).card = M h (m + 3) - M (h - s) (m + 3))
  have hTk : T.card ≤ (m + 3) ! * sizeCount h (m + 3) q (P h (m + 3) ℓ) := by
    refine le_trans ?_ (card_tuples_filter_le q (m + 3) (fun A => (h • A).card = P h (m + 3) ℓ))
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, hv.2.1, by rw [card_nsmul_image, hv.2.2, hP]⟩
  have hq' : 32 * s * (2 * h + 1) ^ (m + 2) ≤ q :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsh)) hq
  have h2 : q ^ (m + 2) ≤ 32 * s * T.card :=
    arith_lower hs hq' (Nat.one_le_pow _ _ (by omega)) hc
  calc q ^ (m + 2) ≤ 32 * s * T.card := h2
    _ ≤ 32 * s * ((m + 3) ! * sizeCount h (m + 3) q (P h (m + 3) ℓ)) :=
        Nat.mul_le_mul_left _ hTk
    _ = _ := by ring

theorem sizeCount_add (h k q : ℕ) :
    sizeCount h k q (M h k) + ((kSubsets q k).filter (fun A => (h • A).card ≠ M h k)).card =
      q.choose k := by
  rw [sizeCount, Finset.card_filter_add_card_filter_not, kSubsets, Finset.card_powersetCard,
    card_Icc_one]

theorem sizeCount_M_le (h k q : ℕ) : sizeCount h k q (M h k) ≤ q ^ k := by
  have := sizeCount_add h k q
  have := Nat.choose_le_pow q k
  omega

/-- Explicit form of Theorem `thm:main`(1), lower bound: for `q ≥ 2k` and
`q ≥ 2^{k+1} k! (2h+1)^{k-1}`, at least `q^k / (2^{k+1} k!)` sets are `B_h`-sets. -/
theorem sizeCount_M_lower (h k q : ℕ) (hk : 1 ≤ k) (hq : 2 * k ≤ q)
    (hq' : 2 * (2 ^ k * k !) * (2 * h + 1) ^ (k - 1) ≤ q) :
    q ^ k ≤ 2 * (2 ^ k * k !) * sizeCount h k q (M h k) := by
  have h1 := sizeCount_add h k q
  have h2 := card_not_Bh_le h k q hk
  have h3 : (q + 1 - k) ^ k ≤ k ! * q.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.pow_sub_le_descFactorial q k
  have h4 : q ^ k ≤ 2 ^ k * (q + 1 - k) ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  set a := 2 ^ k * k.factorial
  set B := (2 * h + 1) ^ (k - 1)
  set c := sizeCount h k q (M h k)
  have h5 : q ^ k ≤ a * c + a * (B * q ^ (k - 1)) := by
    calc q ^ k ≤ 2 ^ k * (k ! * q.choose k) := h4.trans (Nat.mul_le_mul_left _ h3)
      _ ≤ 2 ^ k * (k ! * (c + B * q ^ (k - 1))) := by gcongr; omega
      _ = _ := by simp only [a]; ring
  have h6 : 2 * (a * (B * q ^ (k - 1))) ≤ q ^ k := by
    calc 2 * (a * (B * q ^ (k - 1))) = (2 * a * B) * q ^ (k - 1) := by ring
      _ ≤ q * q ^ (k - 1) := Nat.mul_le_mul_right _ hq'
      _ = q ^ k := by rw [← pow_succ']; congr 1; omega
  calc q ^ k ≤ 2 * (a * c) := by omega
    _ = 2 * a * c := by ring

/-- **Theorem `thm:main`(1).** The number of `A ∈ \binom{[q]}{k}` with `|hA| = M_{h,k}` is
`Θ(q^k)`.  (The paper's standing assumption `h ≥ 2` is not needed for this part.) -/
theorem main_theorem_1 (h k : ℕ) (hk : 3 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ k ≤ (sizeCount h k q (M h k) : ℝ) ∧
      (sizeCount h k q (M h k) : ℝ) ≤ C * (q : ℝ) ^ k := by
  refine ⟨1 / (2 * (2 ^ k * k ! : ℕ)), 1, by positivity, one_pos,
    2 * k + 2 * (2 ^ k * k !) * (2 * h + 1) ^ (k - 1), fun q hq => ⟨?_, ?_⟩⟩
  · have := sizeCount_M_lower h k q (by omega) (by omega) (by omega)
    have hpos : (0 : ℝ) < 2 * (2 ^ k * k ! : ℕ) := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    exact_mod_cast (by linarith : q ^ k ≤ sizeCount h k q (M h k) * (2 * (2 ^ k * k !)))
  · rw [one_mul]; exact_mod_cast sizeCount_M_le h k q

/-- **Theorem `thm:main`(2).** The number of `A ∈ \binom{[q]}{k}` with
`|hA| ∉ {P_0, …, P_{h-1}}` is `O(h^{2k-2} q^{k-2})`. -/
theorem main_theorem_2 (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      (((kSubsets q k).filter (fun A => (h • A).card ∉ (range h).image (P h k))).card : ℝ) ≤
        C * (h : ℝ) ^ (2 * k - 2) * (q : ℝ) ^ (k - 2) := by
  refine ⟨3 ^ (2 * k - 2), by positivity, 0, fun q _ => ?_⟩
  have h1 := card_exceptional_le h k q (by omega) (by omega)
  have h2 : (2 * h + 1) ^ (2 * k - 2) ≤ 3 ^ (2 * k - 2) * h ^ (2 * k - 2) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h3 := le_trans h1 (Nat.mul_le_mul_right (q ^ (k - 2)) h2)
  exact_mod_cast h3

/-- **Theorem `thm:main`(3).** For `0 ≤ ℓ < h`, the number of `A ∈ \binom{[q]}{k}` with
`|hA| = P_ℓ` is `Ω(q^{k-1} / (h - ℓ + 1))`. -/
theorem main_theorem_3 (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) (ℓ : ℕ) (hℓ : ℓ < h) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ (k - 1) / ((h : ℝ) - ℓ + 1) ≤ (sizeCount h k q (P h k ℓ) : ℝ) := by
  have hden : ((h : ℝ) - ℓ + 1) = ((h - ℓ + 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hℓ.le]; ring
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · refine ⟨1 / (2 * (2 ^ k * k ! : ℕ)), by positivity,
      2 * k + 2 * (2 ^ k * k !) * (2 * h + 1) ^ (k - 1) + 1, fun q hq => ?_⟩
    have h1 := sizeCount_M_lower h k q (by omega) (by omega) (by omega)
    have hP0 : P h k 0 = M h k := by simp [P, Mpred]
    rw [hP0]
    have hpos : (0 : ℝ) < 2 * (2 ^ k * k ! : ℕ) := by positivity
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hpow : (q : ℝ) ^ (k - 1) ≤ (q : ℝ) ^ k := pow_le_pow_right₀ hq1 (by omega)
    simp only [Nat.cast_zero, sub_zero]
    have hdiv : 1 / (2 * (2 ^ k * k ! : ℕ) : ℝ) * (q : ℝ) ^ (k - 1) / ((h : ℝ) + 1) ≤
        1 / (2 * (2 ^ k * k ! : ℕ) : ℝ) * (q : ℝ) ^ (k - 1) := by
      apply div_le_self (by positivity)
      have : (0 : ℝ) ≤ h := by positivity
      linarith
    refine hdiv.trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    have : ((q ^ k : ℕ) : ℝ) ≤ ((sizeCount h k q (M h k) * (2 * (2 ^ k * k !)) : ℕ) : ℝ) := by
      exact_mod_cast (by linarith : q ^ k ≤ sizeCount h k q (M h k) * (2 * (2 ^ k * k !)))
    push_cast at this ⊢
    linarith
  · refine ⟨1 / (32 * (k ! : ℝ)), by positivity, 32 * h * (2 * h + 1) ^ (k - 1),
      fun q hq => ?_⟩
    have h1 := sizeCount_P_lower h k ℓ q hk hℓ0 hℓ hq
    rw [hden]
    have hpos : (0 : ℝ) < ((h - ℓ + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have : ((q ^ (k - 1) : ℕ) : ℝ) ≤ ((32 * (h - ℓ + 1) * k ! * sizeCount h k q (P h k ℓ) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at this
    have hk' : (0 : ℝ) < k ! := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith

theorem sizeCount_le_exceptional (h k q v : ℕ) (hv : v ∉ (range h).image (P h k)) :
    sizeCount h k q v ≤
      ((kSubsets q k).filter (fun A => (h • A).card ∉ (range h).image (P h k))).card := by
  apply Finset.card_le_card
  intro A hA
  rw [Finset.mem_filter] at hA ⊢
  exact ⟨hA.1, hA.2 ▸ hv⟩

/-- Explicit form of Corollary `cor:gap-pattern`, first part, with the threshold coming out of
the proof. -/
theorem gap_pattern_of_le (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) (q : ℕ)
    (hq : 2 * k + 2 * (2 ^ k * k !) * (2 * h + 1) ^ (k - 1) + 32 * h * (2 * h + 1) ^ (k - 1) +
      2 * (2 ^ k * k !) * (2 * h + 1) ^ (2 * k - 2) +
      32 * h * k ! * (2 * h + 1) ^ (2 * k - 2) + 1 ≤ q) :
    ∀ ℓ < h, ∀ v ∉ (range h).image (P h k), sizeCount h k q v < sizeCount h k q (P h k ℓ) := by
  set a := 2 ^ k * k ! with ha
  set B := (2 * h + 1) ^ (k - 1) with hB
  set E := (2 * h + 1) ^ (2 * k - 2) with hE
  intro ℓ hℓ v hv
  have hvE : sizeCount h k q v ≤ E * q ^ (k - 2) :=
    (sizeCount_le_exceptional h k q v hv).trans (card_exceptional_le h k q (by omega) (by omega))
  have hqk : q ^ k = q * q * q ^ (k - 2) := by
    rw [← pow_two, ← pow_add]; congr 1; omega
  have hqk1 : q ^ (k - 1) = q * q ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hq2 : 0 < q ^ (k - 2) := pow_pos (by omega) _
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · have h1 := sizeCount_M_lower h k q (by omega) (by omega) (by rw [← ha, ← hB]; omega)
    have hP0 : P h k 0 = M h k := by simp [P, Mpred]
    rw [hP0]
    rw [← ha] at h1
    have h2 : 2 * a * E * q ^ (k - 2) < q * q * q ^ (k - 2) := by
      apply Nat.mul_lt_mul_of_pos_right _ hq2
      calc 2 * a * E < q := by omega
        _ ≤ q * q := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 2 * a * sizeCount h k q v < 2 * a * sizeCount h k q (M h k) := by
      calc 2 * a * sizeCount h k q v ≤ 2 * a * (E * q ^ (k - 2)) := Nat.mul_le_mul_left _ hvE
        _ = 2 * a * E * q ^ (k - 2) := by ring
        _ < q ^ k := by rw [hqk]; exact h2
        _ ≤ _ := h1
    exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
  · have h1 := sizeCount_P_lower h k ℓ q hk hℓ0 hℓ (by rw [← hB]; omega)
    have hs : h - ℓ + 1 ≤ h := by omega
    have h2 : 32 * h * k ! * E * q ^ (k - 2) < q * q ^ (k - 2) :=
      Nat.mul_lt_mul_of_pos_right (by omega) hq2
    have h3 : 32 * h * k ! * sizeCount h k q v < 32 * h * k ! * sizeCount h k q (P h k ℓ) := by
      calc 32 * h * k ! * sizeCount h k q v ≤ 32 * h * k ! * (E * q ^ (k - 2)) :=
            Nat.mul_le_mul_left _ hvE
        _ = 32 * h * k ! * E * q ^ (k - 2) := by ring
        _ < q ^ (k - 1) := by rw [hqk1]; exact h2
        _ ≤ 32 * (h - ℓ + 1) * k ! * sizeCount h k q (P h k ℓ) := h1
        _ ≤ 32 * h * k ! * sizeCount h k q (P h k ℓ) := by gcongr
    exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)

/-- **Remark `rem:explicit` (explicit threshold, with a worse constant).**  The conclusion of
Corollary `cor:gap-pattern` holds as soon as `q > 70 · 2^k · k! · h · (2h+1)^{2k-2}`.  (The paper
states the threshold `2^k k! h (2h+1)^{2k-2}`; our bounds lose the factor `70`.) -/
theorem gap_pattern_explicit (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) (q : ℕ)
    (hq : 70 * (2 ^ k * k !) * h * (2 * h + 1) ^ (2 * k - 2) < q) :
    ∀ ℓ < h, ∀ v ∉ (range h).image (P h k), sizeCount h k q v < sizeCount h k q (P h k ℓ) := by
  refine gap_pattern_of_le h k hk hh q ?_
  set a := 2 ^ k * k ! with ha
  set B := (2 * h + 1) ^ (k - 1) with hB
  set E := (2 * h + 1) ^ (2 * k - 2) with hE
  have hBE : B ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
  have hkf : k ! ≤ a := Nat.le_mul_of_pos_left _ (by positivity)
  have ha1 : 1 ≤ a := le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)) hkf
  have hka : k ≤ a := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    calc k ≤ 2 ^ k := this.le
      _ ≤ a := Nat.le_mul_of_pos_right _ (Nat.factorial_pos k)
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hhE : E ≤ h * E := Nat.le_mul_of_pos_left _ (by omega)
  have hX : a ≤ a * h * E :=
    calc a ≤ a * (h * E) := Nat.le_mul_of_pos_right _ (by positivity)
      _ = a * h * E := by ring
  have f2 : a * B ≤ a * h * E :=
    calc a * B ≤ a * (h * E) := Nat.mul_le_mul_left _ (hBE.trans hhE)
      _ = a * h * E := by ring
  have f3 : h * B ≤ a * h * E := by
    calc h * B ≤ h * E := Nat.mul_le_mul_left _ hBE
      _ ≤ a * (h * E) := Nat.le_mul_of_pos_left _ (by omega)
      _ = a * h * E := by ring
  have f4 : a * E ≤ a * h * E :=
    calc a * E ≤ a * (h * E) := Nat.mul_le_mul_left _ hhE
      _ = a * h * E := by ring
  have f5 : h * k ! * E ≤ a * h * E := by
    calc h * k ! * E = k ! * (h * E) := by ring
      _ ≤ a * (h * E) := Nat.mul_le_mul_right _ hkf
      _ = a * h * E := by ring
  nlinarith

/-- **Corollary `cor:gap-pattern`, first part.** For all sufficiently large `q`, each of the
values `P_0, …, P_{h-1}` of `|hA|` is strictly more frequent than every other value. -/
theorem gap_pattern_most_frequent (h k : ℕ) (hk : 3 ≤ k) (hh : 2 ≤ h) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ ℓ < h, ∀ v ∉ (range h).image (P h k),
      sizeCount h k q v < sizeCount h k q (P h k ℓ) :=
  ⟨70 * (2 ^ k * k !) * h * (2 * h + 1) ^ (2 * k - 2) + 1,
    fun q hq => gap_pattern_explicit h k hk hh q (by omega)⟩

theorem M_succ (n k : ℕ) (hk : 2 ≤ k) : M (n + 1) k = M n k + (n + k - 1).choose (k - 2) := by
  unfold M
  rw [show n + 1 + k - 1 = (n + k - 1) + 1 by omega, show k - 1 = (k - 2) + 1 by omega,
    Nat.choose_succ_succ, add_comm]

theorem M_strictMono (k : ℕ) (hk : 2 ≤ k) {a b : ℕ} (hab : a < b) : M a k < M b k := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [M_succ b k hk]
    have hpos : 0 < (b + k - 1).choose (k - 2) := Nat.choose_pos (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · have := ih h; omega
    · subst h; omega

theorem Mpred_le (h k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : ℓ ≤ h + 1) : Mpred ℓ k ≤ M h k := by
  unfold Mpred
  split_ifs with h0
  · omega
  · rcases Nat.lt_or_ge (ℓ - 1) h with h1 | h1
    · exact (M_strictMono k hk h1).le
    · rw [show ℓ - 1 = h by omega]

theorem Mpred_strictMono (k : ℕ) (hk : 2 ≤ k) {a b : ℕ} (hab : a < b) :
    Mpred a k < Mpred b k := by
  unfold Mpred
  rw [if_neg (show b ≠ 0 by omega)]
  split_ifs with ha
  · unfold M; exact Nat.choose_pos (by omega)
  · exact M_strictMono k hk (by omega)

/-- The values `P_0 > P_1 > ⋯ > P_h` are strictly decreasing; in particular `P_0, …, P_{h-1}`
are `h` distinct values. -/
theorem P_strictAnti (h k : ℕ) (hk : 2 ≤ k) {ℓ ℓ' : ℕ} (hℓ : ℓ < ℓ') (hℓ' : ℓ' < h + 1) :
    P h k ℓ' < P h k ℓ := by
  unfold P
  have := Mpred_strictMono k hk hℓ
  have := Mpred_le h k ℓ' hk (by omega)
  omega

/-- **Corollary `cor:gap-pattern`, second part.** `P_ℓ - P_{ℓ+1} = \binom{ℓ+k-2}{k-2}`. -/
theorem gap_pattern_differences (h k : ℕ) (hk : 2 ≤ k) (ℓ : ℕ) (hℓ : ℓ + 1 < h) :
    P h k ℓ - P h k (ℓ + 1) = (ℓ + k - 2).choose (k - 2) := by
  unfold P
  have h1 := Mpred_strictMono k hk (Nat.lt_succ_self ℓ)
  have h2 := Mpred_le h k (ℓ + 1) hk (by omega)
  have h3 : Mpred (ℓ + 1) k = Mpred ℓ k + (ℓ + k - 2).choose (k - 2) := by
    unfold Mpred
    rw [if_neg (by omega), Nat.add_sub_cancel]
    split_ifs with h0
    · subst h0; simp [M, show k - 2 = k - 1 - 1 by omega]
    · obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
      rw [M_succ n k hk, Nat.add_sub_cancel]
      congr 2; omega
  omega

/-- For `k = 4` the gaps are the triangular numbers `(ℓ+1)(ℓ+2)/2`. -/
theorem gap_pattern_triangular (h ℓ : ℕ) (hℓ : ℓ + 1 < h) :
    P h 4 ℓ - P h 4 (ℓ + 1) = (ℓ + 1) * (ℓ + 2) / 2 := by
  rw [gap_pattern_differences h 4 (by norm_num) ℓ hℓ, show ℓ + 4 - 2 = ℓ + 2 by omega,
    Nat.choose_two_right]
  congr 1
  rw [show ℓ + 2 - 1 = ℓ + 1 by omega]; ring

end Sumsets
