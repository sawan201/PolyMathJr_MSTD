module

public import RequestProject.Defs

/-!
# Preliminary lemmas

* `Sumsets.card_sumVectors`: `|𝒳_{h,k}| = M_{h,k}`.
* `Sumsets.nsmul_image_eq_sumsOf`: `hA = {x · v : x ∈ 𝒳_{h,k}}` when `v` enumerates `A`.
* `Sumsets.equal_sum_criterion` (Lemma `lem:equal-sum-criterion`).
* `Sumsets.card_coeffVectors_le`, `Sumsets.coeffVectors_linearIndependent`
  (Proposition `prop:coefficient-vectors-lemma`).
* `Sumsets.gap_size_lemma` (Lemma `lem:gap-size-lemma`).
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset

variable {h k : ℕ}

theorem mem_sumVectors {x : Fin k → ℕ} : x ∈ sumVectors h k ↔ ∑ i, x i = h :=
  Finset.Nat.mem_antidiagonalTuple

/-! ### Elementary facts about weights -/

theorem weight_cast (d : Fin k → ℤ) : (weight d : ℤ) = ∑ i, ((d i).toNat : ℤ) := by
  simp [weight]

theorem weight_neg_eq {d : Fin k → ℤ} (hd : ∑ i, d i = 0) : weight (-d) = weight d := by
  have h1 : ∑ i, (((d i).toNat : ℤ) - ((-d i).toNat : ℤ)) = 0 := by
    simpa [Int.toNat_sub_toNat_neg] using hd
  rw [Finset.sum_sub_distrib, sub_eq_zero] at h1
  have : (weight (-d) : ℤ) = weight d := by
    rw [weight_cast, weight_cast]; simpa using h1.symm
  exact_mod_cast this

theorem weight_smul_nat (n : ℕ) (d : Fin k → ℤ) : weight ((n : ℤ) • d) = n * weight d := by
  have : (weight ((n : ℤ) • d) : ℤ) = n * weight d := by
    rw [weight_cast, weight_cast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases le_or_gt 0 (d i) with h | h
    · rw [Int.toNat_of_nonneg (by positivity), Int.toNat_of_nonneg h]
    · rw [Int.toNat_of_nonpos (by nlinarith), Int.toNat_of_nonpos h.le]; simp
  exact_mod_cast this

theorem neg_le_weight {d : Fin k → ℤ} (hd : ∑ i, d i = 0) (i : Fin k) :
    -d i ≤ weight d := by
  rw [← weight_neg_eq hd, weight_cast]
  calc -d i ≤ ((-d) i).toNat := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => (((-d) i).toNat : ℤ))
        (fun _ _ => by positivity) (Finset.mem_univ i)

theorem le_weight (d : Fin k → ℤ) (i : Fin k) : d i ≤ weight d := by
  rw [weight_cast]
  calc d i ≤ (d i).toNat := Int.self_le_toNat _
    _ ≤ _ := Finset.single_le_sum (f := fun i => ((d i).toNat : ℤ))
        (fun _ _ => by positivity) (Finset.mem_univ i)

/-- Normalization of a collision vector (the first half of the proof of the equal-sum
criterion): a nonzero vector `z` with coordinate sum `0` and weight `≤ h` is a nonzero multiple
of a coefficient vector in `ℛ_{h,k}`. -/
theorem exists_coeffVector_of {z : Fin k → ℤ} (hz : z ≠ 0) (hsum : ∑ i, z i = 0)
    (hw : weight z ≤ h) : ∃ d, IsCoeffVector h d ∧ ∃ c : ℤ, c ≠ 0 ∧ z = c • d := by
  classical
  have hne : (univ.filter fun i => z i ≠ 0).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hc
    apply hz
    funext i
    have := hc (mem_univ i)
    simp only [ne_eq, not_not] at this
    simp [this]
  set i0 := (univ.filter fun i => z i ≠ 0).min' hne
  have hi0 : z i0 ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  have hlt : ∀ j < i0, z j = 0 := by
    intro j hj
    by_contra hc
    have := Finset.min'_le (univ.filter fun i => z i ≠ 0) j
      (Finset.mem_filter.mpr ⟨mem_univ _, hc⟩)
    exact absurd hj (not_lt.mpr this)
  set g := univ.gcd z with hgdef
  have hg0 : g ≠ 0 := by
    intro h0
    rw [Finset.gcd_eq_zero_iff] at h0
    exact hi0 (h0 i0 (mem_univ _))
  have hgnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hgpos : 0 < g := lt_of_le_of_ne hgnn (Ne.symm hg0)
  have hdvd : ∀ i, g ∣ z i := fun i => Finset.gcd_dvd (mem_univ i)
  set ε : ℤ := if 0 < z i0 then 1 else -1 with hεdef
  have hε : ε * ε = 1 := by simp only [ε]; split_ifs <;> norm_num
  have hε' : ε = 1 ∨ ε = -1 := by simp only [ε]; split_ifs <;> simp
  have hεne : ε ≠ 0 := by rcases hε' with h' | h' <;> rw [h'] <;> norm_num
  set m : Fin k → ℤ := fun i => z i / g with hmdef
  have hzm : ∀ i, z i = g * m i := fun i => (Int.mul_ediv_cancel' (hdvd i)).symm
  have hmsum : ∑ i, m i = 0 := by
    have : g * ∑ i, m i = 0 := by rw [Finset.mul_sum]; simp_rw [← hzm]; exact hsum
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hg0
    · exact h
  have hwm : weight m ≤ h := by
    have hzeq : z = ((g.toNat : ℕ) : ℤ) • m := by
      funext i; simp [Int.toNat_of_nonneg hgnn, hzm i]
    have : weight z = g.toNat * weight m := by rw [hzeq, weight_smul_nat]
    have hg1 : 1 ≤ g.toNat := by omega
    calc weight m ≤ g.toNat * weight m := Nat.le_mul_of_pos_left _ hg1
      _ ≤ h := this ▸ hw
  refine ⟨ε • m, ⟨?_, ?_, ?_, ?_, ?_⟩, ε * g, mul_ne_zero hεne hg0, ?_⟩
  · intro h0
    have := congrFun h0 i0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hεne h
    · exact hi0 (by rw [hzm i0, h, mul_zero])
  · simp [Pi.smul_apply, ← Finset.mul_sum, hmsum]
  · rcases hε' with h' | h'
    · rw [h', one_smul]; exact hwm
    · rw [h', neg_one_smul, weight_neg_eq hmsum]; exact hwm
  · have h1 : (univ.gcd fun i => ε * m i) = normalize ε * univ.gcd m := Finset.gcd_mul_left
    have h2 : normalize ε = 1 := by
      rcases hε' with h' | h'
      · rw [h']; simp
      · rw [h', Int.normalize_of_nonpos (by norm_num)]; norm_num
    have h3 : univ.gcd m = 1 := Finset.gcd_div_eq_one (mem_univ i0) hi0
    change (univ.gcd fun i => ε * m i) = 1
    rw [h1, h2, h3, one_mul]
  · refine ⟨i0, ?_, fun j hj => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      have := hzm i0
      by_cases hp : 0 < z i0
      · have : ε = 1 := by simp [ε, hp]
        rw [this, one_mul]
        by_contra hc; push_neg at hc; nlinarith
      · have : ε = -1 := by simp [ε, hp]
        rw [this]
        have hneg : z i0 < 0 := lt_of_le_of_ne (not_lt.mp hp) hi0
        by_contra hc; push_neg at hc; nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul]
      have := hzm j
      rw [hlt j hj] at this
      have : m j = 0 := by
        rcases mul_eq_zero.mp this.symm with h | h
        · exact absurd h hg0
        · exact h
      rw [this, mul_zero]
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hzm i]
    calc g * m i = (ε * ε) * g * m i := by rw [hε]; ring
      _ = _ := by ring

/-- `|𝒳_{h,k}| = M_{h,k}`. -/
theorem card_sumVectors (h k : ℕ) (hk : 1 ≤ k) : (sumVectors h k).card = M h k := by
  classical
  have e : (sumVectors h k) ≃ Sym (Fin k) h :=
    (Equiv.subtypeEquivRight (fun x => Finset.Nat.mem_antidiagonalTuple)).trans
      (Sym.equivNatSumOfFintype (Fin k) h).symm
  rw [← Fintype.card_coe, Fintype.card_congr e, Sym.card_sym_eq_choose, Fintype.card_fin, M,
    show k + h - 1 = h + k - 1 by omega]
  exact (Nat.choose_symm_of_eq_add (by omega)).symm

/-- The `h`-fold sumset of the image of `v` is `{x · v : x ∈ 𝒳_{h,k}}`. -/
theorem sum_add_single (x : Fin k → ℕ) (i : Fin k) :
    ∑ j, (x + Pi.single i 1 : Fin k → ℕ) j = ∑ j, x j + 1 := by
  simp [Finset.sum_add_distrib]

theorem dotN_add_single (x : Fin k → ℕ) (i : Fin k) (v : Fin k → ℤ) :
    dotN (x + Pi.single i 1 : Fin k → ℕ) v = dotN x v + v i := by
  simp [dotN, add_mul, Finset.sum_add_distrib, Pi.single_apply]

theorem nsmul_image_eq_sumsOf (h : ℕ) (v : Fin k → ℤ) :
    h • (Finset.univ.image v) = sumsOf h v := by
  classical
  induction h with
  | zero =>
    simp [sumsOf, sumVectors, Finset.Nat.antidiagonalTuple_zero_right, dotN]
    rfl
  | succ h ih =>
    rw [succ_nsmul, ih]
    ext n
    simp only [sumsOf, sumVectors, Finset.mem_add, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.Nat.mem_antidiagonalTuple]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
      exact ⟨y + Pi.single i 1, by rw [sum_add_single, hy], dotN_add_single y i v⟩
    · rintro ⟨x, hx, rfl⟩
      have : ∃ i, x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        simp [hc] at hx
      obtain ⟨i, hi⟩ := this
      set y : Fin k → ℕ := Function.update x i (x i - 1)
      have hxy : x = y + Pi.single i 1 := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [y]; omega
        · simp [y, hj]
      refine ⟨_, ⟨y, ?_, rfl⟩, _, ⟨i, rfl⟩, ?_⟩
      · rw [hxy, sum_add_single] at hx; omega
      · rw [hxy, dotN_add_single]

theorem card_sumsOf_le (h : ℕ) (hk : 1 ≤ k) (v : Fin k → ℤ) : (sumsOf h v).card ≤ M h k := by
  rw [← card_sumVectors h k hk]; exact Finset.card_image_le

theorem card_sumsOf_eq_iff (h : ℕ) (hk : 1 ≤ k) (v : Fin k → ℤ) :
    (sumsOf h v).card = M h k ↔ Set.InjOn (fun x => dotN x v) (sumVectors h k) := by
  rw [← card_sumVectors h k hk]; exact Finset.card_image_iff

/-- The paper's description of `ℛ_{h,k}` (without the a priori bound on the entries). -/
theorem mem_coeffVectors {d : Fin k → ℤ} : d ∈ coeffVectors h k ↔ IsCoeffVector h d := by
  unfold coeffVectors
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun hd => hd.2, fun hd => ⟨fun i => Finset.mem_Icc.mpr ⟨?_, ?_⟩, hd⟩⟩
  · have h1 := neg_le_weight hd.2.1 i
    have h2 : (weight d : ℤ) ≤ h := by exact_mod_cast hd.2.2.1
    omega
  · have h1 := le_weight d i
    have h2 : (weight d : ℤ) ≤ h := by exact_mod_cast hd.2.2.1
    omega

/-! ### Dot products -/

theorem dotN_add (a b : Fin k → ℕ) (v : Fin k → ℤ) : dotN (a + b) v = dotN a v + dotN b v := by
  simp [dotN, add_mul, Finset.sum_add_distrib]

theorem dotN_posVec_sub_negVec (d v : Fin k → ℤ) :
    dotN (posVec d) v - dotN (negVec d) v = dot d v := by
  simp only [dotN, dot, posVec, negVec, ← Finset.sum_sub_distrib, ← sub_mul]
  simp

theorem dot_smul (c : ℤ) (d v : Fin k → ℤ) : dot (c • d) v = c * dot d v := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem sum_negVec {d : Fin k → ℤ} (hd : ∑ i, d i = 0) : ∑ i, negVec d i = weight d := by
  rw [← weight_neg_eq hd]; rfl

theorem posVec_eq_negVec_iff {d : Fin k → ℤ} : posVec d = negVec d ↔ d = 0 := by
  constructor
  · intro h; funext i; have := congrFun h i; simp only [posVec, negVec] at this
    have h2 := Int.toNat_sub_toNat_neg (d i); rw [this] at h2; simp at h2; simp [h2]
  · rintro rfl; rfl

/-- A collision `x · v = y · v` between distinct sum vectors comes from a coefficient vector:
`x - y` is a nonzero multiple of some `d ∈ ℛ_{h,k}` with `d · v = 0`. -/
theorem collision_vector (v : Fin k → ℤ) {x y : Fin k → ℕ} (hx : x ∈ sumVectors h k)
    (hy : y ∈ sumVectors h k) (hxy : x ≠ y) (heq : dotN x v = dotN y v) :
    ∃ d ∈ coeffVectors h k, dot d v = 0 ∧ ∃ c : ℤ, c ≠ 0 ∧ ∀ i, (x i : ℤ) - y i = c * d i := by
  rw [mem_sumVectors] at hx hy
  set z : Fin k → ℤ := fun i => (x i : ℤ) - y i
  have hz : z ≠ 0 := by
    intro h0; apply hxy; funext i; have := congrFun h0 i; simp [z] at this; omega
  have hsum : ∑ i, z i = 0 := by
    simp only [z, Finset.sum_sub_distrib]; rw [← Nat.cast_sum, ← Nat.cast_sum, hx, hy]; simp
  have hw : weight z ≤ h := by
    rw [← hx]; exact Finset.sum_le_sum fun i _ => by simp [z]
  obtain ⟨d, hd, c, hc, hzc⟩ := exists_coeffVector_of hz hsum hw
  refine ⟨d, mem_coeffVectors.mpr hd, ?_, c, hc, fun i => by
    have := congrFun hzc i; simpa [z] using this⟩
  have : dot z v = 0 := by
    simp only [dot, z, sub_mul, Finset.sum_sub_distrib]; simp only [dotN] at heq; rw [heq]; simp
  rw [hzc, dot_smul] at this
  exact (mul_eq_zero.mp this).resolve_left hc

/-- **Lemma (equal-sum criterion).** There are distinct `x, y ∈ 𝒳_{h,k}` with `x · v = y · v`
iff some `d ∈ ℛ_{h,k}` satisfies `d · v = 0`. -/
theorem equal_sum_criterion (v : Fin k → ℤ) :
    (∃ x ∈ sumVectors h k, ∃ y ∈ sumVectors h k, x ≠ y ∧ dotN x v = dotN y v) ↔
      ∃ d ∈ coeffVectors h k, dot d v = 0 := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, heq⟩
    obtain ⟨d, hd, hdv, -⟩ := collision_vector v hx hy hxy heq
    exact ⟨d, hd, hdv⟩
  · rintro ⟨d, hd, hdv⟩
    have hd' := mem_coeffVectors.mp hd
    obtain ⟨hd0, hdsum, hdw, -, ⟨i0, -, -⟩⟩ := hd'
    set t : Fin k → ℕ := (h - weight d) • Pi.single i0 1
    have ht : ∑ i, t i = h - weight d := by simp [t, Pi.single_apply]
    refine ⟨posVec d + t, ?_, negVec d + t, ?_, ?_, ?_⟩
    · rw [mem_sumVectors]; simp only [Pi.add_apply, Finset.sum_add_distrib, ht]
      change weight d + _ = h; omega
    · rw [mem_sumVectors]; simp only [Pi.add_apply, Finset.sum_add_distrib, ht]
      rw [sum_negVec hdsum]; omega
    · intro h0; apply hd0; rw [← posVec_eq_negVec_iff]; exact add_right_cancel h0
    · rw [dotN_add, dotN_add]; have := dotN_posVec_sub_negVec d v; linarith

/-! ### Rank lemma for one and two equations -/

/-- Rank lemma, one equation: if `c i ≠ 0`, the solutions of `c · p = 0` in a box `∏ S j`
number at most `∏_{j ≠ i} |S j|`. -/
theorem card_filter_dot_eq_zero_le (c : Fin k → ℤ) (i : Fin k) (hci : c i ≠ 0)
    (S : Fin k → Finset ℤ) :
    ((Fintype.piFinset S).filter (fun p => dot c p = 0)).card ≤
      ∏ j ∈ univ.erase i, (S j).card := by
  classical
  set S' : Fin k → Finset ℤ := Function.update S i {0}
  have hcard : (Fintype.piFinset S').card = ∏ j ∈ univ.erase i, (S j).card := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [S', Function.update_self, card_singleton, one_mul]
    exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => Function.update p i 0) ?_ ?_
  · intro p hp
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hp
    simp only [mem_coe, Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj; simp [S']
    · simp [S', hj, hp.1 j]
  · intro p hp p' hp' heq
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hp hp'
    have hoff : ∀ j, j ≠ i → p j = p' j := fun j hj => by
      have := congrFun heq j; simpa [hj] using this
    have key : c i * p i = c i * p' i := by
      have h1 := hp.2; have h2 := hp'.2
      unfold dot at h1 h2
      rw [← Finset.add_sum_erase _ _ (mem_univ i)] at h1 h2
      have : ∑ j ∈ univ.erase i, c j * p j = ∑ j ∈ univ.erase i, c j * p' j :=
        sum_congr rfl (fun j hj => by rw [hoff j (ne_of_mem_erase hj)])
      linarith
    funext j
    by_cases hj : j = i
    · subst hj; exact mul_left_cancel₀ hci key
    · exact hoff j hj

theorem dot_split (c p : Fin k → ℤ) (i j : Fin k) (hij : i ≠ j) :
    dot c p = c i * p i + c j * p j + ∑ l ∈ (univ.erase i).erase j, c l * p l := by
  unfold dot
  rw [← Finset.add_sum_erase _ _ (mem_univ i),
    ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨hij.symm, mem_univ j⟩)]
  ring

/-- Rank lemma, two equations: if the `2 × 2` minor in columns `i ≠ j` is nonzero, the common
solutions of `d · p = 0` and `e · p = 0` in a box number at most `∏_{l ≠ i, j} |S l|`. -/
theorem card_filter_two_dot_eq_zero_le (d e : Fin k → ℤ) (i j : Fin k) (hij : i ≠ j)
    (hdet : d i * e j - d j * e i ≠ 0) (S : Fin k → Finset ℤ) :
    ((Fintype.piFinset S).filter (fun p => dot d p = 0 ∧ dot e p = 0)).card ≤
      ∏ l ∈ (univ.erase i).erase j, (S l).card := by
  classical
  set S' : Fin k → Finset ℤ := Function.update (Function.update S i {0}) j {0}
  have hj' : j ∈ univ.erase i := mem_erase.mpr ⟨hij.symm, mem_univ j⟩
  have hcard : (Fintype.piFinset S').card = ∏ l ∈ (univ.erase i).erase j, (S l).card := by
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (mem_univ i),
      ← Finset.mul_prod_erase _ _ hj']
    simp only [S', Function.update_self, card_singleton, one_mul, Function.update_of_ne hij]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h1 := ne_of_mem_erase hl
    have h2 := ne_of_mem_erase (mem_of_mem_erase hl)
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun p => Function.update (Function.update p i 0) j 0) ?_ ?_
  · intro p hp
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hp
    simp only [mem_coe, Fintype.mem_piFinset]
    intro l
    by_cases hl : l = j
    · subst hl; simp [S']
    · by_cases hl' : l = i
      · subst hl'; simp [S', hl]
      · simp [S', hl, hl', hp.1 l]
  · intro p hp p' hp' heq
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_setOf_eq] at hp hp'
    have hoff : ∀ l, l ≠ i → l ≠ j → p l = p' l := fun l hl hl' => by
      have := congrFun heq l; simpa [hl, hl'] using this
    have hrest : ∀ c : Fin k → ℤ, ∑ l ∈ (univ.erase i).erase j, c l * p l =
        ∑ l ∈ (univ.erase i).erase j, c l * p' l := fun c =>
      sum_congr rfl (fun l hl => by
        rw [hoff l (ne_of_mem_erase (mem_of_mem_erase hl)) (ne_of_mem_erase hl)])
    have e1 := hp.2.1; have e2 := hp.2.2; have e3 := hp'.2.1; have e4 := hp'.2.2
    rw [dot_split _ _ i j hij] at e1 e2 e3 e4
    rw [hrest] at e1 e2
    have ki : (d i * e j - d j * e i) * (p i - p' i) = 0 := by
      linear_combination e j * e1 - d j * e2 - e j * e3 + d j * e4
    have kj : (d i * e j - d j * e i) * (p j - p' j) = 0 := by
      linear_combination d i * e2 - e i * e1 - d i * e4 + e i * e3
    funext l
    by_cases hl : l = i
    · subst hl; have := (mul_eq_zero.mp ki).resolve_left hdet; linarith
    · by_cases hl' : l = j
      · subst hl'; have := (mul_eq_zero.mp kj).resolve_left hdet; linarith
      · exact hoff l hl hl'

/-! ### The coefficient vectors -/

/-- **Proposition (coefficient vectors), counting part.** `|ℛ_{h,k}| ≤ (2h+1)^{k-1}`. -/
theorem card_coeffVectors_le (h k : ℕ) (hk : 1 ≤ k) :
    (coeffVectors h k).card ≤ (2 * h + 1) ^ (k - 1) := by
  classical
  set i : Fin k := ⟨0, hk⟩
  calc (coeffVectors h k).card
      ≤ ((Fintype.piFinset fun _ : Fin k => Finset.Icc (-(h : ℤ)) h).filter
          (fun p => dot (fun _ => 1) p = 0)).card := by
        apply Finset.card_le_card
        intro d hd
        have hd' := mem_coeffVectors.mp hd
        unfold coeffVectors at hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, by simpa [dot] using hd'.2.1⟩
    _ ≤ ∏ j ∈ univ.erase i, (Finset.Icc (-(h : ℤ)) h).card :=
        card_filter_dot_eq_zero_le _ i one_ne_zero _
    _ = (2 * h + 1) ^ (k - 1) := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
          Fintype.card_fin, Int.card_Icc]
        congr 1
        omega

theorem not_leadingPos_neg {d : Fin k → ℤ} (hd : LeadingPos d) (hd' : LeadingPos (-d)) : False := by
  obtain ⟨i, hi, hlt⟩ := hd
  obtain ⟨i', hi', hlt'⟩ := hd'
  rcases lt_trichotomy i i' with h | h | h
  · have := hlt' i h; simp at this; omega
  · subst h; simp at hi'; omega
  · have := hlt i' h; simp [this] at hi'

/-- Two coefficient vectors which are proportional are equal. -/
theorem eq_of_smul_eq_smul {d e : Fin k → ℤ} (hd : IsCoeffVector h d) (he : IsCoeffVector h e)
    {a b : ℤ} (ha : a ≠ 0) (hab : a • d = b • e) : d = e := by
  have hgd : (univ.gcd fun i => a * d i) = normalize a := by
    rw [Finset.gcd_mul_left, hd.2.2.2.1, mul_one]
  have hge : (univ.gcd fun i => b * e i) = normalize b := by
    rw [Finset.gcd_mul_left, he.2.2.2.1, mul_one]
  have hfun : (fun i => a * d i) = fun i => b * e i := by
    funext i; have := congrFun hab i; simpa using this
  rw [hfun, hge] at hgd
  rcases (normalize_eq_normalize_iff.mp hgd.symm) with ⟨h1, h2⟩
  have hab' : a = b ∨ a = -b := by
    rcases Int.natAbs_eq_natAbs_iff.mp (Int.natAbs_eq_of_dvd_dvd h1 h2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hab' with rfl | rfl
  · funext i; have := congrFun hfun i; exact mul_left_cancel₀ ha this
  · exfalso
    have hb : b ≠ 0 := by intro h0; simp [h0] at ha
    have hde : d = -e := by
      funext i; have := congrFun hfun i
      have : b * (d i + e i) = 0 := by simp at this; linarith
      simp only [Pi.neg_apply]
      have := (mul_eq_zero.mp this).resolve_left hb; linarith
    have := he.2.2.2.2
    have hd4 := hd.2.2.2.2
    rw [hde] at hd4
    exact not_leadingPos_neg this hd4

/-- **Proposition (coefficient vectors), independence part.** Two distinct vectors of `ℛ_{h,k}`
are linearly independent. -/
theorem coeffVectors_linearIndependent {d e : Fin k → ℤ} (hd : d ∈ coeffVectors h k)
    (he : e ∈ coeffVectors h k) (hde : d ≠ e) : LinearIndependent ℤ ![d, e] := by
  rw [mem_coeffVectors] at hd he
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right he.1⟩
  · exfalso
    apply hde
    refine eq_of_smul_eq_smul hd he hs (b := -t) ?_
    rw [neg_smul, eq_neg_iff_add_eq_zero, hst]

/-- Two distinct coefficient vectors have a nonzero `2 × 2` minor. -/
theorem exists_minor_ne_zero {d e : Fin k → ℤ} (hd : d ∈ coeffVectors h k)
    (he : e ∈ coeffVectors h k) (hde : d ≠ e) :
    ∃ i j, i ≠ j ∧ d i * e j - d j * e i ≠ 0 := by
  rw [mem_coeffVectors] at hd he
  by_contra hcon
  push_neg at hcon
  have hall : ∀ i j, d i * e j - d j * e i = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; ring
    · exact hcon i j hij
  obtain ⟨i0, hi0, -⟩ := hd.2.2.2.2
  apply hde
  refine (eq_of_smul_eq_smul he hd (ne_of_gt hi0) (b := e i0) ?_).symm
  funext j
  have := hall i0 j
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-! ### The gap-size lemma -/

/-- **Lemma (gap size).** If exactly one `d ∈ ℛ_{h,k}` satisfies `d · v = 0`, then
`|{x · v : x ∈ 𝒳_{h,k}}| = M_{h,k} - M_{h - w(d),k}`. -/
theorem gap_size_lemma (hk : 1 ≤ k) (v : Fin k → ℤ) {d : Fin k → ℤ} (hd : d ∈ coeffVectors h k)
    (hdv : dot d v = 0) (huniq : ∀ e ∈ coeffVectors h k, dot e v = 0 → e = d) :
    (sumsOf h v).card = M h k - M (h - weight d) k := by
  classical
  obtain ⟨hd0, hdsum, hdw, -, ⟨i1, hi1pos, -⟩⟩ := mem_coeffVectors.mp hd
  -- collisions are multiples of `d`
  have coll : ∀ x ∈ sumVectors h k, ∀ y ∈ sumVectors h k, dotN x v = dotN y v →
      ∃ m : ℤ, ∀ i, (x i : ℤ) - y i = m * d i := by
    intro x hx y hy hxy
    by_cases hxy' : x = y
    · exact ⟨0, fun i => by simp [hxy']⟩
    obtain ⟨d', hd', hd'v, c, -, hc⟩ := collision_vector v hx hy hxy' hxy
    obtain rfl := huniq d' hd' hd'v
    exact ⟨c, hc⟩
  set p := posVec d
  set S := (sumVectors h k).filter (fun x => ¬ ∀ i, p i ≤ x i)
  -- cardinality of `S`
  have hT : ((sumVectors h k).filter (fun x => ∀ i, p i ≤ x i)).card =
      (sumVectors (h - weight d) k).card := by
    symm
    refine Finset.card_nbij' (fun t => t + p) (fun x => x - p) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [mem_coe, mem_sumVectors, mem_filter] at ht ⊢
      refine ⟨?_, fun i => by simp⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, ht]
      change h - weight d + weight d = h
      omega
    · intro x hx
      simp only [mem_coe, mem_sumVectors, mem_filter] at hx ⊢
      have := Finset.sum_tsub_distrib (s := univ) (f := x) (g := p) (fun i _ => hx.2 i)
      simp only [Pi.sub_apply, this, hx.1]
      rfl
    · intro t _; funext i; simp
    · intro x hx
      simp only [mem_coe, mem_filter] at hx
      funext i; simp [Nat.sub_add_cancel (hx.2 i)]
  have hScard : S.card = M h k - M (h - weight d) k := by
    have := Finset.card_filter_add_card_filter_not (s := sumVectors h k)
      (p := fun x => ∀ i, p i ≤ x i)
    rw [hT, card_sumVectors h k hk, card_sumVectors (h - weight d) k hk] at this
    change _ + S.card = _ at this
    omega
  -- every value is attained on `S`
  have hreach : ∀ n, ∀ x ∈ sumVectors h k, x i1 = n → ∃ x' ∈ S, dotN x' v = dotN x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      by_cases hxS : ∀ i, p i ≤ x i
      · set x' : Fin k → ℕ := fun i => x i - p i + negVec d i
        have hx'mem : x' ∈ sumVectors h k := by
          rw [mem_sumVectors] at hx ⊢
          simp only [x', Finset.sum_add_distrib]
          rw [Finset.sum_tsub_distrib _ (fun i _ => hxS i), sum_negVec hdsum, hx]
          change h - weight d + weight d = h
          omega
        have hx'cast : ∀ i, (x' i : ℤ) = x i - d i := by
          intro i
          simp only [x', p, posVec, negVec]
          have := hxS i
          simp only [p, posVec] at this
          push_cast [this]
          have := Int.toNat_sub_toNat_neg (d i)
          linarith
        have hx'dot : dotN x' v = dotN x v := by
          have : dotN x' v = dotN x v - dot d v := by
            simp only [dotN, dot, hx'cast, sub_mul, Finset.sum_sub_distrib]
          rw [this, hdv, sub_zero]
        have hlt : x' i1 < n := by
          have := hx'cast i1
          omega
        obtain ⟨x'', hx''S, hx''⟩ := ih _ hlt x' hx'mem rfl
        exact ⟨x'', hx''S, hx''.trans hx'dot⟩
      · exact ⟨x, mem_filter.mpr ⟨hx, hxS⟩, rfl⟩
  have himage : sumsOf h v = S.image (fun x => dotN x v) := by
    apply le_antisymm
    · intro n hn
      simp only [sumsOf, mem_image] at hn ⊢
      obtain ⟨x, hx, rfl⟩ := hn
      exact hreach _ x hx rfl
    · exact Finset.image_subset_image (Finset.filter_subset _ _)
  -- injectivity on `S`
  have hinj : Set.InjOn (fun x => dotN x v) S := by
    intro x hx y hy hxy
    simp only [mem_coe, S, mem_filter] at hx hy
    obtain ⟨m, hm⟩ := coll x hx.1 y hy.1 hxy
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · exfalso; apply hy.2; intro i
      simp only [p, posVec]
      rcases le_or_gt (d i) 0 with hdi | hdi
      · simp [Int.toNat_of_nonpos hdi]
      · have := hm i; have : (d i).toNat = d i := Int.toNat_of_nonneg hdi.le
        have : (1 : ℤ) * d i ≤ -m * d i := by
          apply mul_le_mul_of_nonneg_right _ hdi.le; omega
        rw [neg_mul] at this
        omega
    · funext i; have := hm i; rw [hm0] at this; simp at this; omega
    · exfalso; apply hx.2; intro i
      simp only [p, posVec]
      rcases le_or_gt (d i) 0 with hdi | hdi
      · simp [Int.toNat_of_nonpos hdi]
      · have := hm i; have : (d i).toNat = d i := Int.toNat_of_nonneg hdi.le
        have : (1 : ℤ) * d i ≤ m * d i := by
          apply mul_le_mul_of_nonneg_right _ hdi.le; omega
        omega
  rw [himage, Finset.card_image_of_injOn hinj, hScard]

end Sumsets
