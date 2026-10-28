module

public import RequestProject.Counting

/-!
# The construction in the proof of Theorem `thm:main`(3)

For `2 ≤ s ≤ h` we consider the tuples `(a, a + r, a + s r, t₄, …, t_k)` with
`1 ≤ a ≤ ⌊q/2⌋`, `1 ≤ r ≤ ⌊q/(2s)⌋` and `t_j ∈ [q]`.  All of them are orthogonal to
`d₀ = (s-1, -s, 1, 0, …, 0)`, and all but `O(q^{k-2})` of them are orthogonal to no other
coefficient vector; for those, `|hA| = M_{h,k} - M_{h-s,k}` by the gap-size lemma.
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset

variable {m : ℕ}

/-- The coefficient vector `d₀ = (s-1, -s, 1, 0, …, 0)`. -/
def dZero (s : ℤ) : Fin (m + 3) → ℤ :=
  fun i => if i = 0 then s - 1 else if i = 1 then -s else if i = 2 then 1 else 0

/-- The parametrization `p ↦ (p₀, p₀ + p₁, p₀ + s p₁, p₃, …)`. -/
def paramMap (s : ℤ) (p : Fin (m + 3) → ℤ) : Fin (m + 3) → ℤ :=
  fun i => if i = 0 then p 0 else if i = 1 then p 0 + p 1 else if i = 2 then p 0 + s * p 1 else p i

/-- The coefficient vector `e` seen in parameter space: `e · paramMap s p = paramCoeff s e · p`. -/
def paramCoeff (s : ℤ) (e : Fin (m + 3) → ℤ) : Fin (m + 3) → ℤ :=
  fun i => if i = 0 then e 0 + e 1 + e 2 else if i = 1 then e 1 + s * e 2 else if i = 2 then 0
    else e i

/-- The parameter box. -/
def paramBox (q s : ℕ) : Fin (m + 3) → Finset ℤ :=
  fun i => if i = 0 then Icc 1 ((q / 2 : ℕ) : ℤ) else if i = 1 then Icc 1 ((q / (2 * s) : ℕ) : ℤ)
    else if i = 2 then {1} else Icc 1 (q : ℤ)

theorem fin3_ne : (0 : Fin (m + 3)) ≠ 1 ∧ (0 : Fin (m + 3)) ≠ 2 ∧ (1 : Fin (m + 3)) ≠ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]

theorem sum_split3 (f : Fin (m + 3) → ℤ) :
    ∑ i, f i = f 0 + f 1 + f 2 + ∑ i ∈ ((univ.erase 0).erase 1).erase 2, f i := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  rw [← Finset.add_sum_erase _ _ (mem_univ 0),
    ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨h01.symm, mem_univ 1⟩),
    ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨h12.symm, mem_erase.mpr ⟨h02.symm, mem_univ 2⟩⟩)]
  ring

theorem mem_rest {i : Fin (m + 3)} (hi : i ∈ ((univ.erase 0).erase 1).erase 2) :
    i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 :=
  ⟨ne_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase hi)),
    ne_of_mem_erase (mem_of_mem_erase hi), ne_of_mem_erase hi⟩

theorem dot_paramMap (s : ℤ) (e p : Fin (m + 3) → ℤ) :
    dot e (paramMap s p) = dot (paramCoeff s e) p := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  unfold dot
  rw [sum_split3, sum_split3]
  have hrest : ∑ i ∈ ((univ.erase 0).erase 1).erase 2, e i * paramMap s p i =
      ∑ i ∈ ((univ.erase 0).erase 1).erase 2, paramCoeff s e i * p i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi0, hi1, hi2⟩ := mem_rest hi
    simp [paramMap, paramCoeff, hi0, hi1, hi2]
  rw [hrest]
  simp only [paramMap, paramCoeff, if_true, if_neg h01.symm, if_neg h02.symm,
    if_neg h12.symm]
  ring

theorem paramCoeff_dZero (s : ℤ) : paramCoeff s (dZero (m := m) s) = 0 := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  funext i
  by_cases hi0 : i = 0
  · subst hi0; simp [paramCoeff, dZero, h01.symm, h02.symm, h12.symm]; ring
  by_cases hi1 : i = 1
  · subst hi1; simp [paramCoeff, dZero, h01.symm, h02.symm, h12.symm]
  by_cases hi2 : i = 2
  · subst hi2; simp [paramCoeff, h02.symm, h12.symm]
  simp [paramCoeff, dZero, hi0, hi1, hi2]

theorem gcd_eq_one_of_entry {k : ℕ} {d : Fin k → ℤ} {i : Fin k} (hi : d i = 1) :
    univ.gcd d = 1 := by
  have h1 : univ.gcd d ∣ 1 := hi ▸ Finset.gcd_dvd (mem_univ i)
  have h2 : 0 ≤ univ.gcd d := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  exact Int.eq_one_of_dvd_one h2 h1

theorem weight_dZero {s : ℕ} (hs : 2 ≤ s) : weight (dZero (m := m) (s : ℤ)) = s := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  have : (weight (dZero (m := m) (s : ℤ)) : ℤ) = s := by
    rw [weight_cast, sum_split3]
    have hrest : ∑ i ∈ ((univ.erase 0).erase 1).erase 2,
        (((dZero (m := m) (s : ℤ)) i).toNat : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨hi0, hi1, hi2⟩ := mem_rest hi
      simp [dZero, hi0, hi1, hi2]
    rw [hrest]
    simp only [dZero, if_true, if_neg h01.symm, if_neg h02.symm, if_neg h12.symm]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonpos (by omega)]
    simp
  exact_mod_cast this

theorem sum_dZero (s : ℤ) : ∑ i, dZero (m := m) s i = 0 := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  rw [sum_split3]
  have hrest : ∑ i ∈ ((univ.erase 0).erase 1).erase 2, (dZero (m := m) s) i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨hi0, hi1, hi2⟩ := mem_rest hi
    simp [dZero, hi0, hi1, hi2]
  rw [hrest]
  simp only [dZero, if_true, if_neg h01.symm, if_neg h02.symm, if_neg h12.symm]
  ring

theorem dZero_mem (h : ℕ) {s : ℕ} (hs : 2 ≤ s) (hsh : s ≤ h) :
    dZero (m := m) (s : ℤ) ∈ coeffVectors h (m + 3) := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  have h2 : dZero (m := m) (s : ℤ) 2 = 1 := by simp [dZero, h02.symm, h12.symm]
  rw [mem_coeffVectors]
  refine ⟨fun h0 => by simpa [h2] using congrFun h0 2, sum_dZero _, by rw [weight_dZero hs]; exact hsh,
    gcd_eq_one_of_entry h2, ⟨0, by simp [dZero]; omega, fun j hj => absurd hj (Fin.not_lt_zero j)⟩⟩

theorem eq_dZero_of_paramCoeff_eq_zero {h s : ℕ} (hs : 2 ≤ s) (hsh : s ≤ h)
    {e : Fin (m + 3) → ℤ} (he : e ∈ coeffVectors h (m + 3)) (hce : paramCoeff (s : ℤ) e = 0) :
    e = dZero (s : ℤ) := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  have e0 := congrFun hce 0
  have e1 := congrFun hce 1
  simp only [paramCoeff, if_true, if_neg h01.symm, Pi.zero_apply] at e0 e1
  refine eq_of_smul_eq_smul (mem_coeffVectors.mp he) (mem_coeffVectors.mp (dZero_mem h hs hsh))
    one_ne_zero (b := e 2) ?_
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hi0 : i = 0
  · subst hi0; simp only [dZero, if_true]; linear_combination e0 - e1
  by_cases hi1 : i = 1
  · subst hi1; simp only [dZero, if_neg h01.symm, if_true]; linear_combination e1
  by_cases hi2 : i = 2
  · subst hi2; simp [dZero, h02.symm, h12.symm]
  have := congrFun hce i
  simp only [paramCoeff, if_neg hi0, if_neg hi1, if_neg hi2, Pi.zero_apply] at this
  simp [dZero, hi0, hi1, hi2, this]

theorem dot_single_sub_single {k : ℕ} (i j : Fin k) (v : Fin k → ℤ) :
    dot (Pi.single i 1 - Pi.single j 1 : Fin k → ℤ) v = v i - v j := by
  simp [dot, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

/-- The vector `e_i - e_j` (for `i < j`) is a coefficient vector of weight `1`. -/
theorem single_sub_single_mem {k : ℕ} (h : ℕ) (hh : 1 ≤ h) {i j : Fin k} (hij : i < j) :
    (Pi.single i 1 - Pi.single j 1 : Fin k → ℤ) ∈ coeffVectors h k ∧
      weight (Pi.single i 1 - Pi.single j 1 : Fin k → ℤ) = 1 := by
  have hne : i ≠ j := ne_of_lt hij
  set e : Fin k → ℤ := Pi.single i 1 - Pi.single j 1
  have hei : e i = 1 := by simp [e, hne]
  have hw : weight e = 1 := by
    unfold weight
    rw [Finset.sum_eq_single i]
    · rw [hei]; rfl
    · intro l _ hl
      by_cases hlj : l = j
      · subst hlj; simp [e, hne.symm]
      · simp [e, hl, hlj]
    · simp
  refine ⟨mem_coeffVectors.mpr ⟨fun h0 => by simpa [hei] using congrFun h0 i, ?_, by omega,
    gcd_eq_one_of_entry hei, ⟨i, by rw [hei]; norm_num, fun l hl => ?_⟩⟩, hw⟩
  · simp [e, Finset.sum_sub_distrib]
  · have h1 : l ≠ i := ne_of_lt hl
    have h2 : l ≠ j := ne_of_lt (hl.trans hij)
    simp [e, h1, h2]

theorem prod_split3 (f : Fin (m + 3) → ℕ) :
    ∏ i, f i = f 0 * f 1 * f 2 * ∏ i ∈ ((univ.erase 0).erase 1).erase 2, f i := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  rw [← Finset.mul_prod_erase _ _ (mem_univ 0),
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨h01.symm, mem_univ 1⟩),
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨h12.symm, mem_erase.mpr ⟨h02.symm, mem_univ 2⟩⟩)]
  ring

theorem card_rest : (((univ.erase (0 : Fin (m + 3))).erase 1).erase 2).card = m := by
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  rw [Finset.card_erase_of_mem (mem_erase.mpr ⟨h12.symm, mem_erase.mpr ⟨h02.symm, mem_univ 2⟩⟩),
    Finset.card_erase_of_mem (mem_erase.mpr ⟨h01.symm, mem_univ 1⟩),
    Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

theorem card_paramBox_le {q s : ℕ} {j : Fin (m + 3)} (hj : j ≠ 2) :
    (paramBox (m := m) q s j).card ≤ q := by
  unfold paramBox
  split_ifs
  · rw [card_Icc_one]; exact Nat.div_le_self _ _
  · rw [card_Icc_one]; exact Nat.div_le_self _ _
  · rw [card_Icc_one]

/-- The good parameters inject (via `paramMap`) into the injective tuples `v` for which `d₀` is
the only coefficient vector orthogonal to `v`. -/
theorem card_goodParams_le (h q s : ℕ) (hs : 2 ≤ s) (hsh : s ≤ h) :
    ((Fintype.piFinset (paramBox (m := m) q s)).filter (fun p => ∀ e ∈ coeffVectors h (m + 3),
        e ≠ dZero (s : ℤ) → dot (paramCoeff s e) p ≠ 0)).card ≤
      ((tuples q (m + 3)).filter (fun v => Function.Injective v ∧
          ∀ e ∈ coeffVectors h (m + 3), dot e v = 0 ↔ e = dZero (s : ℤ))).card := by
  classical
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  refine Finset.card_le_card_of_injOn (paramMap (s : ℤ)) ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hp
    obtain ⟨hpD, hpg⟩ := hp
    have hb0 := hpD 0; have hb1 := hpD 1
    simp only [paramBox, if_true, if_neg h01.symm, mem_Icc] at hb0 hb1
    set v := paramMap (s : ℤ) p with hv
    have huniq : ∀ e ∈ coeffVectors h (m + 3), dot e v = 0 → e = dZero (s : ℤ) := by
      intro e he hev; by_contra hne; exact hpg e he hne (by rw [← dot_paramMap]; exact hev)
    have hd0v : dot (dZero (m := m) (s : ℤ)) v = 0 := by
      rw [dot_paramMap, paramCoeff_dZero]; simp [dot]
    have hinj : Function.Injective v := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · obtain ⟨he, hw⟩ := single_sub_single_mem h (by omega) hlt
        have h1 := huniq _ he (by rw [dot_single_sub_single, hij, sub_self])
        rw [h1, weight_dZero hs] at hw; omega
      · obtain ⟨he, hw⟩ := single_sub_single_mem h (by omega) hlt
        have h1 := huniq _ he (by rw [dot_single_sub_single, hij, sub_self])
        rw [h1, weight_dZero hs] at hw; omega
    simp only [mem_coe, mem_filter]
    refine ⟨?_, hinj, ?_⟩
    · rw [tuples, Fintype.mem_piFinset]
      intro l
      have hA : 2 * ((q / 2 : ℕ) : ℤ) ≤ q := by exact_mod_cast Nat.mul_div_le q 2
      have hB : (2 * s : ℤ) * ((q / (2 * s) : ℕ) : ℤ) ≤ q := by
        exact_mod_cast Nat.mul_div_le q (2 * s)
      have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
      have hsp : (s : ℤ) * p 1 ≤ s * ((q / (2 * s) : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hb1.2 (by omega)
      have hBnn : (0 : ℤ) ≤ ((q / (2 * s) : ℕ) : ℤ) := by positivity
      rw [mem_Icc]
      by_cases hl0 : l = 0
      · subst hl0; simp only [v, paramMap, if_true]; constructor <;> linarith
      by_cases hl1 : l = 1
      · subst hl1; simp only [v, paramMap, if_neg h01.symm, if_true]
        constructor <;> nlinarith
      by_cases hl2 : l = 2
      · subst hl2; simp only [v, paramMap, if_neg h02.symm, if_neg h12.symm, if_true]
        constructor <;> nlinarith
      · have := hpD l
        simp only [paramBox, if_neg hl0, if_neg hl1, if_neg hl2, mem_Icc] at this
        simp only [v, paramMap, if_neg hl0, if_neg hl1, if_neg hl2]
        exact this
    · intro e he
      exact ⟨huniq e he, fun hed => hed ▸ hd0v⟩
  · intro p hp p' hp' heq
    simp only [coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hp hp'
    have e0 := congrFun heq 0
    have e1 := congrFun heq 1
    simp only [paramMap, if_true, if_neg h01.symm] at e0 e1
    funext l
    by_cases hl0 : l = 0
    · subst hl0; exact e0
    by_cases hl1 : l = 1
    · subst hl1; linarith
    by_cases hl2 : l = 2
    · subst hl2
      have a := hp.1 2; have b := hp'.1 2
      simp only [paramBox, if_neg h02.symm, if_neg h12.symm, if_true, mem_singleton] at a b
      rw [a, b]
    · have := congrFun heq l
      simpa [paramMap, hl0, hl1, hl2] using this

/-- Main counting statement for the construction: at least
`⌊q/2⌋ ⌊q/(2s)⌋ q^{k-3} - (2h+1)^{k-1} q^{k-2}` injective tuples `v ∈ [q]^k` (here `k = m + 3`)
are orthogonal to `d₀` and to no other coefficient vector of `ℛ_{h,k}`. -/
theorem card_unique_tuples_ge (h q s : ℕ) (hs : 2 ≤ s) (hsh : s ≤ h) :
    (q / 2) * (q / (2 * s)) * q ^ m ≤
      ((tuples q (m + 3)).filter (fun v => Function.Injective v ∧
          ∀ e ∈ coeffVectors h (m + 3), dot e v = 0 ↔ e = dZero (s : ℤ))).card +
        (2 * h + 1) ^ (m + 2) * q ^ (m + 1) := by
  classical
  obtain ⟨h01, h02, h12⟩ := (fin3_ne (m := m))
  set D := Fintype.piFinset (paramBox (m := m) q s)
  set R := coeffVectors h (m + 3)
  set d0 := dZero (m := m) (s : ℤ)
  set good : (Fin (m + 3) → ℤ) → Prop := fun p => ∀ e ∈ R, e ≠ d0 → dot (paramCoeff s e) p ≠ 0
  have hD : D.card = (q / 2) * (q / (2 * s)) * q ^ m := by
    rw [Fintype.card_piFinset, prod_split3]
    have hrest : ∏ i ∈ ((univ.erase 0).erase 1).erase 2, (paramBox (m := m) q s i).card =
        q ^ m := by
      rw [Finset.prod_congr rfl (g := fun _ => q), Finset.prod_const, card_rest]
      intro i hi
      obtain ⟨hi0, hi1, hi2⟩ := mem_rest hi
      simp [paramBox, hi0, hi1, hi2]
    have b0 : (paramBox (m := m) q s 0).card = q / 2 := by
      simp only [paramBox, if_true]; exact card_Icc_one _
    have b1 : (paramBox (m := m) q s 1).card = q / (2 * s) := by
      simp only [paramBox, if_true, if_neg h01.symm]; exact card_Icc_one _
    have b2 : (paramBox (m := m) q s 2).card = 1 := by
      simp only [paramBox, if_true, if_neg h02.symm, if_neg h12.symm]; rfl
    rw [hrest, b0, b1, b2, mul_one]
  have hbad : (D.filter (fun p => ¬ good p)).card ≤ (2 * h + 1) ^ (m + 2) * q ^ (m + 1) := by
    calc (D.filter (fun p => ¬ good p)).card
        ≤ ((R.filter (· ≠ d0)).biUnion
            (fun e => D.filter (fun p => dot (paramCoeff s e) p = 0))).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          simp only [good, not_forall, not_not] at hp
          obtain ⟨e, he, hne, hdot⟩ := hp.2
          exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hne⟩,
            Finset.mem_filter.mpr ⟨hp.1, hdot⟩⟩
      _ ≤ ∑ e ∈ R.filter (· ≠ d0), (D.filter (fun p => dot (paramCoeff s e) p = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ e ∈ R.filter (· ≠ d0), q ^ (m + 1) := by
          apply Finset.sum_le_sum
          intro e he
          rw [Finset.mem_filter] at he
          have hce : paramCoeff (s : ℤ) e ≠ 0 := fun h0 =>
            he.2 (eq_dZero_of_paramCoeff_eq_zero hs hsh he.1 h0)
          obtain ⟨i, hi⟩ : ∃ i, paramCoeff (s : ℤ) e i ≠ 0 := by
            by_contra hcon; push_neg at hcon; exact hce (funext hcon)
          have hi2 : i ≠ 2 := by
            rintro rfl; apply hi; simp [paramCoeff, h02.symm, h12.symm]
          refine (card_filter_dot_eq_zero_le _ i hi _).trans ?_
          have h2mem : (2 : Fin (m + 3)) ∈ univ.erase i :=
            mem_erase.mpr ⟨Ne.symm hi2, mem_univ _⟩
          rw [← Finset.mul_prod_erase _ _ h2mem]
          have : (paramBox (m := m) q s 2).card = 1 := by
            simp [paramBox, h02.symm, h12.symm]
          rw [this, one_mul]
          have hcard : ((univ.erase i).erase 2).card = m + 1 := by
            rw [Finset.card_erase_of_mem h2mem, Finset.card_erase_of_mem (mem_univ _),
              Finset.card_univ, Fintype.card_fin]
            omega
          rw [← hcard]
          exact Finset.prod_le_pow_card _ _ _ fun j hj => card_paramBox_le (ne_of_mem_erase hj)
      _ ≤ R.card * q ^ (m + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (card_coeffVectors_le h (m + 3) (by omega))
  have hGT := card_goodParams_le (m := m) h q s hs hsh
  have := Finset.card_filter_add_card_filter_not (s := D) (p := good)
  change (D.filter good).card ≤ ((tuples q (m + 3)).filter (fun v => Function.Injective v ∧
    ∀ e ∈ R, dot e v = 0 ↔ e = d0)).card at hGT
  omega

/-- The construction gives at least `⌊q/2⌋ ⌊q/(2s)⌋ q^{k-3} - (2h+1)^{k-1} q^{k-2}` injective
tuples `v ∈ [q]^k` (here `k = m + 3`) with `|{x · v : x ∈ 𝒳_{h,k}}| = M_{h,k} - M_{h-s,k}`. -/
theorem card_good_tuples_ge (h q s : ℕ) (hs : 2 ≤ s) (hsh : s ≤ h) :
    (q / 2) * (q / (2 * s)) * q ^ m ≤
      ((tuples q (m + 3)).filter (fun v => Function.Injective v ∧
          (sumsOf h v).card = M h (m + 3) - M (h - s) (m + 3))).card +
        (2 * h + 1) ^ (m + 2) * q ^ (m + 1) := by
  refine (card_unique_tuples_ge h q s hs hsh).trans (Nat.add_le_add_right ?_ _)
  apply Finset.card_le_card
  intro v hv
  rw [Finset.mem_filter] at hv ⊢
  refine ⟨hv.1, hv.2.1, ?_⟩
  rw [gap_size_lemma (by omega) v (dZero_mem h hs hsh) ((hv.2.2 _ (dZero_mem h hs hsh)).mpr rfl)
    (fun e he hev => (hv.2.2 e he).mp hev), weight_dZero hs]

end Sumsets
