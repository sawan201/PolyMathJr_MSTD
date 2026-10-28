module

public import RequestProject.Additional.TDichotomy

/-!
# Proposition `prop:T-dichotomy`(2)

If `d = x - y` is primitive and the suffix sums `D_j` take both signs, then
`T_{x,y} = Θ(q^{k-1})`.

Instead of the lattice-basis argument of the paper we use the explicit `k - 1` linearly
independent integer vectors `d_p e_i - d_i e_p` (`i ≠ p`, where `d_p ≠ 0`) in the kernel of `d`,
which is enough for the lower bound.
-/

@[expose] public section

open scoped Pointwise Nat

namespace Sumsets

open Finset

variable {h k : ℕ}

/-- A strictly increasing positive integer vector `u` with `d · u = 0`, built from the
gaps `τ̃_j` of the paper. -/
theorem exists_base_point {d : Fin k → ℤ} (hd : ∑ i, d i = 0)
    (hpos : ∃ j, 1 ≤ j ∧ j < k ∧ 0 < suffixSum d j)
    (hneg : ∃ j, 1 ≤ j ∧ j < k ∧ suffixSum d j < 0) :
    ∃ u : Fin k → ℤ, StrictMono u ∧ (∀ i, 1 ≤ u i) ∧ dot d u = 0 := by
  obtain ⟨Lp, hLpdef⟩ : ∃ L : ℤ, L = ∑ j ∈ range (k - 1), max (suffixSum d (j + 1)) 0 :=
    ⟨_, rfl⟩
  obtain ⟨Lm, hLmdef⟩ : ∃ L : ℤ, L = ∑ j ∈ range (k - 1), max (-suffixSum d (j + 1)) 0 :=
    ⟨_, rfl⟩
  have hLp : 0 < Lp := by
    obtain ⟨j, hj1, hjk, hj⟩ := hpos
    rw [hLpdef]
    refine sum_pos' (fun i _ => le_max_right _ _) ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    rw [show j - 1 + 1 = j by omega]
    exact lt_max_of_lt_left hj
  have hLm : 0 < Lm := by
    obtain ⟨j, hj1, hjk, hj⟩ := hneg
    rw [hLmdef]
    refine sum_pos' (fun i _ => le_max_right _ _) ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    rw [show j - 1 + 1 = j by omega]
    exact lt_max_of_lt_left (by linarith)
  set τ : ℕ → ℤ := fun j => if j = 0 then 1 else if 0 < suffixSum d j then Lm
    else if suffixSum d j < 0 then Lp else 1 with hτdef
  have hτ : ∀ j, 1 ≤ τ j := by
    intro j; simp only [hτdef]; split_ifs <;> omega
  set u : Fin k → ℤ := fun i => ∑ j ∈ range (i + 1), τ j with hudef
  have hτnn : ∀ j, 0 ≤ τ j := fun j => by linarith [hτ j]
  refine ⟨u, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [hudef]
    have hab' : (a : ℕ) < b := hab
    refine sum_lt_sum_of_subset (f := τ) (s := range ((a : ℕ) + 1)) (t := range ((b : ℕ) + 1))
      (i := (b : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_range] at hx ⊢; omega
    · simp
    · simp only [mem_range]; omega
    · linarith [hτ (b : ℕ)]
    · exact fun j _ _ => hτnn j
  · intro i
    calc (1 : ℤ) = τ 0 := by simp [hτdef]
      _ ≤ u i := single_le_sum (fun j _ => hτnn j) (mem_range.mpr (by omega))
  · rw [dot_eq_sum_gaps d u hd]
    have hterm : ∀ j ∈ range (k - 1), (extV u (j + 1) - extV u j) * suffixSum d (j + 1) =
        Lm * max (suffixSum d (j + 1)) 0 - Lp * max (-suffixSum d (j + 1)) 0 := by
      intro j hj
      rw [mem_range] at hj
      have hgap : extV u (j + 1) - extV u j = τ (j + 1) := by
        simp only [extV, dif_pos (show j + 1 < k by omega), dif_pos (show j < k by omega),
          hudef]
        rw [sum_range_succ]; ring
      rw [hgap]
      simp only [hτdef, if_neg (Nat.succ_ne_zero j)]
      rcases lt_trichotomy (suffixSum d (j + 1)) 0 with hD | hD | hD
      · rw [if_neg (by omega), if_pos hD, max_eq_right hD.le, max_eq_left (by omega)]; ring
      · rw [hD]; simp
      · rw [if_pos hD, max_eq_left hD.le, max_eq_right (by omega)]; ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hLpdef, ← hLmdef]
    ring

theorem setVec_image_of_strictMono {v : Fin k → ℤ} (hv : StrictMono v) :
    setVec k (univ.image v) = v := by
  have hA : (univ.image v).card = k := card_image_of_injective' hv.injective
  have key := Finset.orderEmbOfFin_unique hA (f := v) (fun x => mem_image_of_mem v (mem_univ x)) hv
  funext i
  rw [setVec_eq hA, ← key]

/-- The perturbation `w(z) = ∑_{i ≠ p} z_i (d_p e_i - d_i e_p)` (written for `z_p = 0`). -/
def pertVec (d : Fin k → ℤ) (p : Fin k) (z : Fin k → ℤ) : Fin k → ℤ :=
  fun i => z i * d p - if i = p then ∑ j, z j * d j else 0

theorem dot_pertVec (d : Fin k → ℤ) (p : Fin k) (z : Fin k → ℤ) : dot d (pertVec d p z) = 0 := by
  simp only [dot, pertVec, mul_sub, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    if_true]
  rw [mul_sum]
  rw [sub_eq_zero]
  refine sum_congr rfl fun i _ => by ring

theorem abs_pertVec_le {d : Fin k → ℤ} {p : Fin k} {z : Fin k → ℤ} {m : ℕ} {K : ℤ}
    (hK : ∑ i, |d i| ≤ K) (hz : ∀ i, |z i| ≤ m) (i : Fin k) :
    |pertVec d p z i| ≤ 2 * m * K := by
  have hdp : |d p| ≤ K := (single_le_sum (fun j _ => abs_nonneg (d j)) (mem_univ p)).trans hK
  have h1 : |z i * d p| ≤ m * K := by
    rw [abs_mul]; exact mul_le_mul (hz i) hdp (abs_nonneg _) (Nat.cast_nonneg _)
  have h2 : |∑ j, z j * d j| ≤ m * K := by
    calc |∑ j, z j * d j| ≤ ∑ j, |z j * d j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (m : ℤ) * |d j| := sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hz j) (abs_nonneg _)
      _ = m * ∑ j, |d j| := by rw [mul_sum]
      _ ≤ m * K := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)
  have h3 : |(if i = p then ∑ j, z j * d j else 0)| ≤ m * K := by
    split_ifs
    · exact h2
    · simp only [abs_zero]; exact (abs_nonneg _).trans h1
  calc |pertVec d p z i| ≤ |z i * d p| + |(if i = p then ∑ j, z j * d j else 0)| :=
        abs_sub _ _
    _ ≤ m * K + m * K := add_le_add h1 h3
    _ = 2 * m * K := by ring

/-- The parameter box `{z : |z_i| ≤ m, z_p = 0}`. -/
def zBox (k : ℕ) (p : Fin k) (m : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun i => if i = p then ({0} : Finset ℤ) else Icc (-(m : ℤ)) m

theorem card_zBox (k : ℕ) (p : Fin k) (m : ℕ) : (zBox k p m).card = (2 * m + 1) ^ (k - 1) := by
  rw [zBox, Fintype.card_piFinset, ← mul_prod_erase _ _ (mem_univ p)]
  have : ∀ i ∈ univ.erase p,
      (if i = p then ({0} : Finset ℤ) else Icc (-(m : ℤ)) m).card = 2 * m + 1 := by
    intro i hi; rw [if_neg (ne_of_mem_erase hi), Int.card_Icc]; omega
  rw [prod_congr rfl this]
  simp

/-- The lattice family: at least `(2m+1)^{k-1}` strictly increasing `v ∈ [q]^k` with
`d · v = 0`. -/
theorem card_family_le {d u : Fin k → ℤ} {p : Fin k} (hp : d p ≠ 0) (hu : StrictMono u)
    (hu1 : ∀ i, 1 ≤ u i) (hdu : dot d u = 0) {K U : ℤ} (hK : ∑ i, |d i| ≤ K)
    (hU : ∀ i, u i ≤ U) {m q : ℕ} (hq : (4 * m * K + 1) * U + 2 * m * K ≤ q) :
    (2 * m + 1) ^ (k - 1) ≤
      ((tuples q k).filter (fun v => StrictMono v ∧ dot d v = 0)).card := by
  have hK0 : 0 ≤ K := (sum_nonneg fun i _ => abs_nonneg (d i)).trans hK
  set N : ℤ := 4 * m * K + 1 with hN
  have hN0 : 0 ≤ N := by positivity
  rw [← card_zBox k p m]
  refine card_le_card_of_injOn (fun z => N • u + pertVec d p z) ?_ ?_
  · intro z hz
    rw [mem_coe, zBox, Fintype.mem_piFinset] at hz
    have hzb : ∀ i, |z i| ≤ m := by
      intro i
      have := hz i
      split_ifs at this with hi
      · rw [mem_singleton] at this; rw [this]; simp
      · rw [mem_Icc] at this; exact abs_le.mpr this
    have hw := fun i => abs_le.mp (abs_pertVec_le (p := p) hK hzb i)
    rw [coe_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [tuples, Fintype.mem_piFinset]
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc]
      have := hw i
      have := hu1 i
      have := hU i
      constructor <;> nlinarith
    · intro a b hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : u a + 1 ≤ u b := hu hab
      have := hw a
      have := hw b
      nlinarith
    · simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
      have h1 := dot_pertVec d p z
      have h2 : ∑ i, d i * (N * u i) = N * dot d u := by
        rw [dot, mul_sum]; exact sum_congr rfl fun i _ => by ring
      rw [dot] at h1
      rw [h1, h2, hdu]; ring
  · intro z1 hz1 z2 hz2 heq
    rw [mem_coe, zBox, Fintype.mem_piFinset] at hz1 hz2
    funext i
    by_cases hi : i = p
    · subst hi
      have a1 := hz1 i; have a2 := hz2 i
      simp only [if_true, mem_singleton] at a1 a2
      rw [a1, a2]
    · have := congrFun heq i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pertVec, if_neg hi, sub_zero,
        add_right_inj] at this
      exact mul_right_cancel₀ hp this

/-- A primitive `d = x - y` (with disjoint support) is `c • d'` with `c ≠ 0` and `d'` a
coefficient vector of weight exactly `h + 1`. -/
theorem exists_coeffVector_diffVec {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k)
    (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y) (hdisj : ∀ i, x i = 0 ∨ y i = 0)
    (hprim : univ.gcd (diffVec x y) = 1) :
    ∃ d', d' ∈ coeffVectors (h + 1) k ∧ weight d' = h + 1 ∧
      ∃ c : ℤ, c ≠ 0 ∧ diffVec x y = c • d' := by
  obtain ⟨d', hd', c, hc, hdc⟩ := exists_coeffVector_of (diffVec_ne_zero hxy) (sum_diffVec hx hy)
    (weight_diffVec_le (y := y) hx)
  refine ⟨d', mem_coeffVectors.mpr hd', ?_, c, hc, hdc⟩
  have hg : normalize c = 1 := by
    have h1 : (univ.gcd fun i => c * d' i) = normalize c * univ.gcd d' := Finset.gcd_mul_left
    rw [hd'.2.2.2.1, mul_one] at h1
    rw [← h1, ← hprim, hdc]; rfl
  have hc1 : c = 1 ∨ c = -1 := by
    have := Int.abs_eq_normalize c
    rw [hg] at this
    rcases abs_eq (zero_le_one) |>.mp this with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hw := weight_diffVec_eq hx hdisj
  rw [hdc] at hw
  rcases hc1 with rfl | rfl
  · rwa [one_smul] at hw
  · rwa [neg_one_smul, weight_neg_eq hd'.2.1] at hw

/-- Lower bound for `T_{x,y}` in terms of the lattice family. -/
theorem card_family_le_Tcount (q : ℕ) {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k)
    (hy : y ∈ sumVectors (h + 1) k) (hxy : x ≠ y) (hdisj : ∀ i, x i = 0 ∨ y i = 0)
    (hprim : univ.gcd (diffVec x y) = 1) :
    ((tuples q k).filter (fun v => StrictMono v ∧ dot (diffVec x y) v = 0)).card ≤
      Tcount h k q x y + (coeffVectors h k).card * q ^ (k - 2) := by
  classical
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd (funext fun i => i.elim0) hxy
    · exact hk
  obtain ⟨d', hd', hwd', c, hc, hdc⟩ := exists_coeffVector_diffVec hx hy hxy hdisj hprim
  have hdot : ∀ v, dot (diffVec x y) v = 0 ↔ dot d' v = 0 := by
    intro v; rw [hdc, dot_smul]
    exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hc, fun h0 => by rw [h0, mul_zero]⟩
  set S := (tuples q k).filter (fun v => StrictMono v ∧ dot (diffVec x y) v = 0)
  set Q : (Fin k → ℤ) → Prop := fun v => ∃ e ∈ coeffVectors h k, dot e v = 0
  rw [← card_filter_add_card_filter_not (s := S) Q, add_comm]
  refine add_le_add ?_ ?_
  · refine card_le_card_of_injOn (fun v => univ.image v) ?_ ?_
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, S, mem_filter] at hv
      obtain ⟨⟨hvt, hvm, hvd⟩, hvQ⟩ := hv
      have hA := image_mem_kSubsets hvt hvm.injective
      have hAk : (univ.image v).card = k := card_image_of_injective' hvm.injective
      have hsv := setVec_image_of_strictMono hvm
      have heq : dotN x v = dotN y v := by
        have := dotN_sub_dotN x y v; rw [hvd] at this; linarith
      rw [coe_filter]
      refine ⟨?_, by rw [hsv]; exact heq⟩
      rw [BhStarSets, mem_filter]
      refine ⟨hA, ?_, ?_⟩
      · by_contra hne
        rw [nsmul_eq_sumsOf_setVec h hAk, hsv] at hne
        exact hvQ (exists_orth_of_card_ne hk hne)
      · rw [nsmul_eq_sumsOf_setVec (h + 1) hAk, hsv, ne_eq, card_sumsOf_eq_iff (h + 1) hk]
        intro hinj
        exact hxy (hinj hx hy heq)
    · intro v1 hv1 v2 hv2 h12
      simp only [coe_filter, Set.mem_setOf_eq, S, mem_filter] at hv1 hv2
      rw [← setVec_image_of_strictMono hv1.1.2.1, ← setVec_image_of_strictMono hv2.1.2.1]
      simp only at h12
      rw [h12]
  · calc (S.filter Q).card
        ≤ ((coeffVectors h k).biUnion
            (fun e => (tuples q k).filter (fun v => dot d' v = 0 ∧ dot e v = 0))).card := by
          refine card_le_card fun v hv => ?_
          simp only [S, Q, mem_filter] at hv
          obtain ⟨⟨hvt, -, hvd⟩, e, he, hev⟩ := hv
          rw [mem_biUnion]
          exact ⟨e, he, mem_filter.mpr ⟨hvt, (hdot v).mp hvd, hev⟩⟩
      _ ≤ ∑ e ∈ coeffVectors h k,
            ((tuples q k).filter (fun v => dot d' v = 0 ∧ dot e v = 0)).card := card_biUnion_le
      _ ≤ ∑ _e ∈ coeffVectors h k, q ^ (k - 2) := by
          refine sum_le_sum fun e he => ?_
          refine card_tuples_two_dot_eq_zero_le (h := h + 1) q hd'
            (coeffVectors_mono (Nat.le_succ h) he) ?_
          intro hde
          have := (mem_coeffVectors.mp he).2.2.1
          rw [← hde, hwd'] at this
          omega
      _ = (coeffVectors h k).card * q ^ (k - 2) := by rw [sum_const, smul_eq_mul]

/-- **Proposition `prop:T-dichotomy`(2).**  If `d = x - y` is primitive and the suffix sums
`D_j` (`1 ≤ j ≤ k - 1`) take both signs, then `T_{x,y} ≥ c q^{k-1}` for all large `q`; together
with `Sumsets.Tcount_le` this gives `T_{x,y} = Θ(q^{k-1})`. -/
theorem Tcount_lower {x y : Fin k → ℕ} (hx : x ∈ sumVectors (h + 1) k)
    (hy : y ∈ sumVectors (h + 1) k) (hdisj : ∀ i, x i = 0 ∨ y i = 0)
    (hprim : univ.gcd (diffVec x y) = 1)
    (hpos : ∃ j, 1 ≤ j ∧ j < k ∧ 0 < suffixSum (diffVec x y) j)
    (hneg : ∃ j, 1 ≤ j ∧ j < k ∧ suffixSum (diffVec x y) j < 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀, c * (q : ℝ) ^ (k - 1) ≤ (Tcount h k q x y : ℝ) := by
  have hk2 : 2 ≤ k := by obtain ⟨j, hj1, hjk, -⟩ := hpos; omega
  have hxy : x ≠ y := by
    rintro rfl
    obtain ⟨j, -, -, hj⟩ := hpos
    have : diffVec x x = 0 := funext fun i => by simp [diffVec]
    rw [this] at hj
    simp [suffixSum] at hj
  set d := diffVec x y with hd
  have hsum := sum_diffVec hx hy
  obtain ⟨u, hu, hu1, hdu⟩ := exists_base_point hsum hpos hneg
  obtain ⟨p, hp⟩ : ∃ p, d p ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact diffVec_ne_zero hxy (funext hcon)
  set Kn : ℕ := (∑ i, |d i|).toNat
  set Un : ℕ := (∑ i, u i).toNat
  have hK : ∑ i, |d i| ≤ (Kn : ℤ) := Int.self_le_toNat _
  have hU : ∀ i, u i ≤ (Un : ℤ) := by
    intro i
    calc u i ≤ ∑ j, u j := single_le_sum (fun j _ => by linarith [hu1 j]) (mem_univ i)
      _ ≤ _ := Int.self_le_toNat _
  set C : ℕ := 4 * Kn * (2 * Un + 1) + 1 with hC
  have hCpos : 0 < C := by omega
  set R := (coeffVectors h k).card
  refine ⟨1 / (2 * (C : ℝ) ^ (k - 1)), by positivity, 2 * Un + 2 * C ^ (k - 1) * R,
    fun q hq => ?_⟩
  set m := q / C with hm
  have hmC : m * C ≤ q := Nat.div_mul_le_self q C
  have hqC : q < C * (m + 1) := Nat.lt_mul_div_succ q hCpos
  have hcond : (4 * (m : ℤ) * Kn + 1) * Un + 2 * m * Kn ≤ q := by
    have h1 : ((m * C : ℕ) : ℤ) ≤ q := by exact_mod_cast hmC
    have h2 : (2 * Un : ℤ) ≤ q := by exact_mod_cast (show 2 * Un ≤ q by omega)
    push_cast [hC] at h1
    nlinarith [Nat.cast_nonneg (α := ℤ) m, Nat.cast_nonneg (α := ℤ) Kn,
      Nat.cast_nonneg (α := ℤ) Un]
  have hfam := card_family_le hp hu hu1 hdu hK hU hcond
  have hT := card_family_le_Tcount (h := h) q hx hy hxy hdisj hprim
  rw [← hd] at hT
  have hq1 : q ≤ C * (2 * m + 1) := by nlinarith
  have hpow : q ^ (k - 1) ≤ C ^ (k - 1) * (2 * m + 1) ^ (k - 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hq1 _
  have hsplit : q ^ (k - 1) = q * q ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hbig : 2 * (C ^ (k - 1) * R * q ^ (k - 2)) ≤ q ^ (k - 1) := by
    rw [hsplit, ← mul_assoc, ← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  have hmain : q ^ (k - 1) ≤ 2 * C ^ (k - 1) * Tcount h k q x y := by
    have h3 : q ^ (k - 1) ≤ C ^ (k - 1) * (Tcount h k q x y + R * q ^ (k - 2)) :=
      hpow.trans (Nat.mul_le_mul_left _ (hfam.trans hT))
    rw [mul_add] at h3
    have h4 : C ^ (k - 1) * (R * q ^ (k - 2)) = C ^ (k - 1) * R * q ^ (k - 2) := by ring
    rw [h4] at h3
    have h5 : 2 * C ^ (k - 1) * Tcount h k q x y = 2 * (C ^ (k - 1) * Tcount h k q x y) := by
      ring
    rw [h5]
    generalize C ^ (k - 1) * Tcount h k q x y = a at h3 ⊢
    generalize C ^ (k - 1) * R * q ^ (k - 2) = b at h3 hbig
    generalize q ^ (k - 1) = t at h3 hbig ⊢
    omega
  have hmainR : ((q ^ (k - 1) : ℕ) : ℝ) ≤ ((2 * C ^ (k - 1) * Tcount h k q x y : ℕ) : ℝ) := by
    exact_mod_cast hmain
  push_cast at hmainR
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-! ### Example `ex:T` (with `k = m + 3`) -/

/-- `x = (h, 0, 1, 0, …, 0)`. -/
def exTx (h m : ℕ) : Fin (m + 3) → ℕ := Fin.cons h (Fin.cons 0 (Fin.cons 1 (fun _ => 0)))

/-- `y = (0, h + 1, 0, …, 0)`. -/
def exTy (h m : ℕ) : Fin (m + 3) → ℕ := Fin.cons 0 (Fin.cons (h + 1) (fun _ => 0))

/-- `x' = (0, h, 1, 0, …, 0)`. -/
def exTx' (h m : ℕ) : Fin (m + 3) → ℕ := Fin.cons 0 (Fin.cons h (Fin.cons 1 (fun _ => 0)))

/-- `y' = (h + 1, 0, …, 0)`. -/
def exTy' (h m : ℕ) : Fin (m + 3) → ℕ := Fin.cons (h + 1) (fun _ => 0)

/-- **Example `ex:T`, first part.**  For `x = (h,0,1,0,…,0)` and `y = (0,h+1,0,…,0)`,
`T_{x,y} = Θ(q^{k-1})`. -/
theorem exT_theta (h m : ℕ) (hh : 1 ≤ h) :
    (∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q ≥ q₀,
      c * (q : ℝ) ^ (m + 2) ≤ (Tcount h (m + 3) q (exTx h m) (exTy h m) : ℝ)) ∧
    ∀ q, Tcount h (m + 3) q (exTx h m) (exTy h m) ≤ q ^ (m + 2) := by
  have hx : exTx h m ∈ sumVectors (h + 1) (m + 3) := by
    simp [mem_sumVectors, exTx, Fin.sum_univ_succ]
  have hy : exTy h m ∈ sumVectors (h + 1) (m + 3) := by
    simp [mem_sumVectors, exTy, Fin.sum_univ_succ]
  have hdisj : ∀ i, exTx h m i = 0 ∨ exTy h m i = 0 := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [exTx, exTy]
  have hprim : univ.gcd (diffVec (exTx h m) (exTy h m)) = 1 :=
    gcd_eq_one_of_entry (i := 2) (by simp [diffVec, exTx, exTy]; rfl)
  have hD1 : suffixSum (diffVec (exTx h m) (exTy h m)) 1 = -h := by
    simp [suffixSum, diffVec, exTx, exTy, Fin.sum_univ_succ]
  have hD2 : suffixSum (diffVec (exTx h m) (exTy h m)) 2 = 1 := by
    simp [suffixSum, diffVec, exTx, exTy, Fin.sum_univ_succ]
  have hxy : exTx h m ≠ exTy h m := by
    intro he; have := congrFun he 0; simp [exTx, exTy] at this; omega
  refine ⟨?_, fun q => Tcount_le q hxy⟩
  have := Tcount_lower hx hy hdisj hprim ⟨2, by omega, by omega, by rw [hD2]; norm_num⟩
    ⟨1, le_rfl, by omega, by rw [hD1]; omega⟩
  simpa using this

/-- **Example `ex:T`, second part.**  For `x' = (0,h,1,0,…,0)` and `y' = (h+1,0,…,0)`, all
`D_j ≥ 0`, so `T_{x',y'} = 0` for every `q`. -/
theorem exT_zero (h m q : ℕ) : Tcount h (m + 3) q (exTx' h m) (exTy' h m) = 0 := by
  have hx : exTx' h m ∈ sumVectors (h + 1) (m + 3) := by
    simp [mem_sumVectors, exTx', Fin.sum_univ_succ]
  have hy : exTy' h m ∈ sumVectors (h + 1) (m + 3) := by
    simp [mem_sumVectors, exTy', Fin.sum_univ_succ]
  have hxy : exTx' h m ≠ exTy' h m := by
    intro he; have := congrFun he 0; simp [exTx', exTy'] at this
  refine Tcount_eq_zero_of_sign q hx hy hxy (Or.inl fun j hj _ => ?_)
  refine sum_nonneg fun i _ => ?_
  split_ifs with hji
  · have hi : i ≠ 0 := by intro h0; rw [h0] at hji; simp at hji; omega
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    simp [diffVec, exTy']
  · exact le_rfl

end Sumsets
