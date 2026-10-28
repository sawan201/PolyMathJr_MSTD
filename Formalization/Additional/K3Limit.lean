module

public import RequestProject.Additional.TDichotomyLower
public import RequestProject.Additional.Proportion

/-!
# Remark `rem:k3-limit`

For `k = 3` and every `h ≥ 2`,
`lim_{q→∞} q (1 - |ℬ_{h,3}(q)| / \binom{q}{3}) = 3 ∑_{w=2}^{h} φ(w)/w`.

A set `{a₁ < a₂ < a₃}` with `(a₂ - a₁)/(a₃ - a₁) = u/w` in lowest terms is a `B_h`-set iff `w > h`.
The sets that are not `B_h`-sets are therefore parametrized by `(w, u, t, a)` with
`2 ≤ w ≤ h`, `1 ≤ u < w`, `gcd(u, w) = 1`, `t, a ≥ 1`, `a + wt ≤ q`, via
`A = {a, a + ut, a + wt}`.
-/

@[expose] public section

open scoped Pointwise Nat
open Filter Topology

namespace Sumsets

open Finset

/-- The admissible pairs `(w, u)`: `2 ≤ w ≤ h`, `1 ≤ u < w`, `gcd(u, w) = 1`. -/
def k3Pairs (h : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 2 h) ×ˢ (Icc 1 h)).filter (fun wu => wu.2 < wu.1 ∧ Nat.Coprime wu.2 wu.1)

/-- The pairs `(t, a)` with `t, a ≥ 1` and `a + wt ≤ q`. -/
def k3Shifts (q w : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 q) ×ˢ (Icc 1 q)).filter (fun ta => ta.2 + w * ta.1 ≤ q)

/-- The parameter set. -/
def k3Params (h q : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (k3Pairs h).sigma (fun wu => k3Shifts q wu.1)

/-- The vector `(a, a + ut, a + wt)`. -/
def k3Vec (p : Σ _ : ℕ × ℕ, ℕ × ℕ) : Fin 3 → ℤ :=
  ![(p.2.2 : ℤ), p.2.2 + p.1.2 * p.2.1, p.2.2 + p.1.1 * p.2.1]

theorem mem_k3Params {h q w u t a : ℕ} :
    (⟨(w, u), (t, a)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ k3Params h q ↔
      ((2 ≤ w ∧ w ≤ h) ∧ (1 ≤ u ∧ u ≤ h) ∧ u < w ∧ Nat.Coprime u w) ∧
        ((1 ≤ t ∧ t ≤ q) ∧ (1 ≤ a ∧ a ≤ q) ∧ a + w * t ≤ q) := by
  simp only [k3Params, k3Pairs, k3Shifts, mem_sigma, mem_filter, mem_product, mem_Icc]
  tauto

theorem k3Vec_strictMono {h q w u t a : ℕ}
    (hp : (⟨(w, u), (t, a)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ k3Params h q) :
    StrictMono (k3Vec ⟨(w, u), (t, a)⟩) := by
  rw [mem_k3Params] at hp
  obtain ⟨⟨-, ⟨hu1, -⟩, huw, -⟩, ⟨ht1, -⟩, -⟩ := hp
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have h1 : (1 : ℤ) ≤ u := by exact_mod_cast hu1
  have h2 : (u : ℤ) < w := by exact_mod_cast huw
  have h3 : (1 : ℤ) ≤ t := by exact_mod_cast ht1
  fin_cases i <;> simp [k3Vec] <;> nlinarith

theorem k3Vec_mem_tuples {h q w u t a : ℕ}
    (hp : (⟨(w, u), (t, a)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ k3Params h q) :
    k3Vec ⟨(w, u), (t, a)⟩ ∈ tuples q 3 := by
  rw [mem_k3Params] at hp
  obtain ⟨⟨-, -, huw, -⟩, -, ⟨ha1, -⟩, hawt⟩ := hp
  have h1 : u * t ≤ w * t := Nat.mul_le_mul_right _ huw.le
  rw [tuples, Fintype.mem_piFinset]
  intro i
  fin_cases i <;> simp only [k3Vec, mem_Icc] <;> simp <;> constructor <;> omega

/-- `(w - u, -w, u)` is a coefficient vector of weight `w`. -/
theorem k3_coeffVector_mem {h w u : ℕ} (hw : w ≤ h) (hu1 : 1 ≤ u) (huw : u < w)
    (hcop : Nat.Coprime u w) : ![(w : ℤ) - u, -w, u] ∈ coeffVectors h 3 := by
  rw [mem_coeffVectors]
  refine ⟨?_, ?_, ?_, ?_, ⟨0, by simp; omega, fun j hj => absurd hj (Fin.not_lt_zero j)⟩⟩
  · intro h0; have := congrFun h0 1; simp at this; omega
  · simp [Fin.sum_univ_three]; ring
  · simp only [weight, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  · obtain ⟨α, β, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : univ.gcd ![(w : ℤ) - u, -w, u] ∣ (u : ℤ) := by
      have := Finset.gcd_dvd (s := univ) (f := ![(w : ℤ) - u, -w, u]) (mem_univ 2)
      simpa using this
    have h2 : univ.gcd ![(w : ℤ) - u, -w, u] ∣ (w : ℤ) := by
      have := Finset.gcd_dvd (s := univ) (f := ![(w : ℤ) - u, -w, u]) (mem_univ 1)
      simpa using this
    have h3 : univ.gcd ![(w : ℤ) - u, -w, u] ∣ 1 := by
      rw [← hab]; exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
    exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) h3

theorem k3_not_Bh_of_params {h q w u t a : ℕ}
    (hp : (⟨(w, u), (t, a)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ k3Params h q) :
    (h • univ.image (k3Vec ⟨(w, u), (t, a)⟩)).card ≠ M h 3 := by
  have hmono := k3Vec_strictMono hp
  have hAk : (univ.image (k3Vec ⟨(w, u), (t, a)⟩)).card = 3 :=
    card_image_of_injective' hmono.injective
  rw [mem_k3Params] at hp
  obtain ⟨⟨⟨-, hwh⟩, ⟨hu1, -⟩, huw, hcop⟩, -⟩ := hp
  rw [nsmul_eq_sumsOf_setVec h hAk, setVec_image_of_strictMono hmono, ne_eq,
    card_sumsOf_eq_iff h (by norm_num)]
  intro hinj
  have hdot : dot ![(w : ℤ) - u, -w, u] (k3Vec ⟨(w, u), (t, a)⟩) = 0 := by
    simp [dot, Fin.sum_univ_three, k3Vec]; ring
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    (equal_sum_criterion (h := h) _).mpr ⟨_, k3_coeffVector_mem hwh hu1 huw hcop, hdot⟩
  exact hxy (hinj hx hy heq)

theorem exists_params_of_not_Bh {h q : ℕ} {A : Finset ℤ} (hA : A ∈ kSubsets q 3)
    (hne : (h • A).card ≠ M h 3) :
    ∃ p ∈ k3Params h q, k3Vec p = setVec 3 A := by
  have hAk := (mem_powersetCard.mp hA).2
  have hv := setVec_strictMono hAk
  have hvt := setVec_mem_tuples hA
  rw [tuples, Fintype.mem_piFinset] at hvt
  rw [nsmul_eq_sumsOf_setVec h hAk] at hne
  generalize setVec 3 A = v at hv hvt hne ⊢
  obtain ⟨e, he, hdot⟩ := exists_orth_of_card_ne (by norm_num) hne
  have h01 : v 0 < v 1 := hv (by decide)
  have h12 : v 1 < v 2 := hv (by decide)
  have hv0 := mem_Icc.mp (hvt 0)
  have hv2 := mem_Icc.mp (hvt 2)
  set x := (v 1 - v 0).toNat with hxdef
  set y := (v 2 - v 0).toNat with hydef
  have hx : (x : ℤ) = v 1 - v 0 := Int.toNat_of_nonneg (by omega)
  have hy : (y : ℤ) = v 2 - v 0 := Int.toNat_of_nonneg (by omega)
  have hx1 : 1 ≤ x := by omega
  have hxy : x < y := by omega
  set g := Nat.gcd x y with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  set u := x / g with hudef
  set w := y / g with hwdef
  have hxu : x = u * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left x y)).symm
  have hyw : y = w * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right x y)).symm
  have hcop : Nat.Coprime u w := Nat.coprime_div_gcd_div_gcd hg
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, zero_mul] at hxu; omega
    · exact h0
  have huw : u < w := by
    rw [hxu, hyw] at hxy; exact Nat.lt_of_mul_lt_mul_right hxy
  -- the key inequality `w ≤ h`
  obtain ⟨he0, hsum, hw, -, -⟩ := mem_coeffVectors.mp he
  simp only [Fin.sum_univ_three] at hsum
  simp only [dot, Fin.sum_univ_three] at hdot
  have hrel : e 1 * u + e 2 * w = 0 := by
    have h1 : e 1 * x + e 2 * y = 0 := by
      rw [hx, hy]; have : e 0 = -e 1 - e 2 := by linarith
      rw [this] at hdot; linarith
    rw [hxu, hyw] at h1; push_cast at h1
    have : (g : ℤ) * (e 1 * u + e 2 * w) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hg.ne')
  have hdvd : (w : ℤ) ∣ e 1 := by
    have hc : IsCoprime (w : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
    exact hc.dvd_of_dvd_mul_right ⟨-e 2, by linarith⟩
  have he1 : e 1 ≠ 0 := by
    intro h0
    have hw0 : (0 : ℤ) < w := by exact_mod_cast (show 0 < w by omega)
    rw [h0, zero_mul, zero_add] at hrel
    have h2 : e 2 = 0 := (mul_eq_zero.mp hrel).resolve_right hw0.ne'
    apply he0; funext i; fin_cases i
    · simp; linarith
    · exact h0
    · exact h2
  have hwle : (w : ℤ) ≤ |e 1| := Int.le_of_dvd (abs_pos.mpr he1) ((dvd_abs _ _).mpr hdvd)
  have hwh : w ≤ h := by
    have hsum' : ∑ i, e i = 0 := by simp only [Fin.sum_univ_three]; exact hsum
    have a1 := le_weight e 1
    have a2 := neg_le_weight hsum' 1
    have a3 : (weight e : ℤ) ≤ h := by exact_mod_cast hw
    have : |e 1| ≤ weight e := abs_le.mpr ⟨by linarith, a1⟩
    have : (w : ℤ) ≤ h := by linarith
    exact_mod_cast this
  refine ⟨⟨(w, u), (g, (v 0).toNat)⟩, ?_, ?_⟩
  · rw [mem_k3Params]
    have hgx : g ≤ x := Nat.gcd_le_left _ (by omega)
    refine ⟨⟨⟨by omega, hwh⟩, ⟨hu1, by omega⟩, huw, hcop⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, ?_⟩
    rw [← hyw]; omega
  · have ha : ((v 0).toNat : ℤ) = v 0 := Int.toNat_of_nonneg (by omega)
    funext i
    fin_cases i
    · simp [k3Vec, ha]
    · simp only [k3Vec]; simp
      rw [max_eq_left (by omega)]; push_cast [hxu] at hx; linarith
    · simp only [k3Vec]; simp
      rw [max_eq_left (by omega)]; push_cast [hyw] at hy; linarith

/-- The non-`B_h`-sets in `\binom{[q]}{3}` are exactly the sets `{a, a + ut, a + wt}`. -/
theorem image_k3Params (h q : ℕ) :
    (k3Params h q).image (fun p => univ.image (k3Vec p)) =
      (kSubsets q 3).filter (fun A => (h • A).card ≠ M h 3) := by
  ext A
  rw [mem_image, mem_filter]
  constructor
  · rintro ⟨⟨⟨w, u⟩, ⟨t, a⟩⟩, hp, rfl⟩
    exact ⟨image_mem_kSubsets (k3Vec_mem_tuples hp) (k3Vec_strictMono hp).injective,
      k3_not_Bh_of_params hp⟩
  · rintro ⟨hA, hne⟩
    obtain ⟨p, hp, hpv⟩ := exists_params_of_not_Bh hA hne
    refine ⟨p, hp, ?_⟩
    rw [hpv, image_setVec (mem_powersetCard.mp hA).2]

theorem injOn_k3Params (h q : ℕ) :
    Set.InjOn (fun p => univ.image (k3Vec p)) (k3Params h q) := by
  rintro ⟨⟨w, u⟩, ⟨t, a⟩⟩ hp ⟨⟨w', u'⟩, ⟨t', a'⟩⟩ hp' heq
  have hv := congrArg (setVec 3) heq
  simp only at hv
  rw [setVec_image_of_strictMono (k3Vec_strictMono hp),
    setVec_image_of_strictMono (k3Vec_strictMono hp')] at hv
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  have e2 := congrFun hv 2
  simp only [k3Vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have ha : a = a' := by exact_mod_cast e0
  subst ha
  have hut : u * t = u' * t' := by
    have : (u : ℤ) * t = u' * t' := by linarith
    exact_mod_cast this
  have hwt : w * t = w' * t' := by
    have : (w : ℤ) * t = w' * t' := by linarith
    exact_mod_cast this
  rw [mem_coe, mem_k3Params] at hp hp'
  have hcop := hp.1.2.2.2
  have hcop' := hp'.1.2.2.2
  have htt : t = t' := by
    have g1 := Nat.gcd_mul_right u t w
    have g2 := Nat.gcd_mul_right u' t' w'
    rw [hcop.gcd_eq_one, one_mul] at g1
    rw [hcop'.gcd_eq_one, one_mul] at g2
    rw [← g1, ← g2, hut, hwt]
  subst htt
  have ht0 : 0 < t := hp.2.1.1
  have hu : u = u' := Nat.eq_of_mul_eq_mul_right ht0 hut
  have hw : w = w' := Nat.eq_of_mul_eq_mul_right ht0 hwt
  subst hu hw
  rfl

theorem card_k3Pairs_filter (h w : ℕ) (hw : w ∈ Icc 2 h) :
    ((k3Pairs h).filter (fun wu => wu.1 = w)).card = φ w := by
  rw [mem_Icc] at hw
  have : (k3Pairs h).filter (fun wu => wu.1 = w) =
      ((range w).filter (Nat.Coprime w)).image (fun u => (w, u)) := by
    ext ⟨a, b⟩
    simp only [k3Pairs, mem_filter, mem_product, mem_Icc, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, hba, hcop⟩, rfl⟩
      exact ⟨b, ⟨hba, hcop.symm⟩, rfl, rfl⟩
    · rintro ⟨u, ⟨hu, hcop⟩, rfl, rfl⟩
      have hu0 : u ≠ 0 := by
        rintro rfl; rw [Nat.coprime_zero_right] at hcop; omega
      exact ⟨⟨⟨hw, by omega, by omega⟩, hu, hcop.symm⟩, rfl⟩
  rw [this, card_image_of_injective _ (fun u v huv => (Prod.mk.inj huv).2),
    Nat.totient_eq_card_coprime]

/-- `|\binom{[q]}{3} \ ℬ_{h,3}(q)| = ∑_{w=2}^{h} φ(w) · #{(t, a)}`. -/
theorem card_nonBh_three (h q : ℕ) :
    ((kSubsets q 3).filter (fun A => (h • A).card ≠ M h 3)).card =
      ∑ w ∈ Icc 2 h, φ w * (k3Shifts q w).card := by
  rw [← image_k3Params, card_image_of_injOn (injOn_k3Params h q), k3Params, card_sigma,
    ← sum_fiberwise_of_maps_to (t := Icc 2 h) (g := fun wu : ℕ × ℕ => wu.1)]
  · refine sum_congr rfl fun w hw => ?_
    rw [← card_k3Pairs_filter h w hw, card_eq_sum_ones, sum_mul, one_mul]
    exact sum_congr rfl fun wu hwu => by rw [(mem_filter.mp hwu).2]
  · intro wu hwu
    simp only [k3Pairs, mem_filter, mem_product] at hwu
    exact hwu.1.1

theorem card_filter_add_le (q c : ℕ) :
    ((Icc 1 q).filter (fun a => a + c ≤ q)).card = q - c := by
  have : (Icc 1 q).filter (fun a => a + c ≤ q) = Icc 1 (q - c) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

theorem card_k3Shifts_eq (q w : ℕ) :
    (k3Shifts q w).card = ∑ t ∈ Icc 1 q, (q - w * t) := by
  rw [k3Shifts, card_filter, sum_product]
  refine sum_congr rfl fun t _ => ?_
  rw [← card_filter_add_le q (w * t), card_filter]

theorem two_mul_sum_gauss (q w m : ℕ) :
    2 * ∑ t ∈ Icc 1 m, ((q : ℤ) - w * t) = 2 * m * q - w * m * (m + 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast; ring

/-- `q² - w² - wq ≤ 2w · #{(t, a)} ≤ q²`. -/
theorem card_k3Shifts_bounds (q w : ℕ) (hw : 1 ≤ w) :
    (q : ℤ) ^ 2 - w ^ 2 - w * q ≤ 2 * w * (k3Shifts q w).card ∧
      2 * w * ((k3Shifts q w).card : ℤ) ≤ q ^ 2 := by
  set m := q / w with hm
  have hmq : w * m ≤ q := Nat.mul_div_le q w
  have hqm : q < w * (m + 1) := Nat.lt_mul_div_succ q (by omega)
  have hmle : m ≤ q := by nlinarith
  have hS : (k3Shifts q w).card = ∑ t ∈ Icc 1 m, (q - w * t) := by
    rw [card_k3Shifts_eq]
    symm
    refine sum_subset (Icc_subset_Icc le_rfl hmle) fun t ht htm => ?_
    simp only [mem_Icc, not_and, not_le] at ht htm
    have : m + 1 ≤ t := htm ht.1
    have : w * (m + 1) ≤ w * t := Nat.mul_le_mul_left _ this
    omega
  have hSZ : ((k3Shifts q w).card : ℤ) = ∑ t ∈ Icc 1 m, ((q : ℤ) - w * t) := by
    rw [hS]; push_cast
    refine sum_congr rfl fun t ht => ?_
    rw [mem_Icc] at ht
    have : w * t ≤ w * m := Nat.mul_le_mul_left _ ht.2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hG := two_mul_sum_gauss q w m
  rw [← hSZ] at hG
  have hmqZ : (w : ℤ) * m ≤ q := by exact_mod_cast hmq
  have hqmZ : (q : ℤ) < w * (m + 1) := by exact_mod_cast hqm
  have hw0 : (0 : ℤ) < w := by exact_mod_cast hw
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  have key : (q : ℤ) ^ 2 - 2 * w * (k3Shifts q w).card = (q - w * m) ^ 2 + w ^ 2 * m := by
    have : 2 * w * ((k3Shifts q w).card : ℤ) = w * (2 * ((k3Shifts q w).card : ℤ)) := by ring
    rw [this, hG]; ring
  constructor
  · have h1 : ((q : ℤ) - w * m) ^ 2 ≤ w ^ 2 := by
      have : (q : ℤ) - w * m < w := by linarith
      have : 0 ≤ (q : ℤ) - w * m := by linarith
      nlinarith
    have h2 : (w : ℤ) ^ 2 * m ≤ w * q := by nlinarith
    linarith
  · nlinarith

theorem tendsto_quad_ratio (α β : ℝ) :
    Tendsto (fun q : ℕ => ((q : ℝ) ^ 2 + α * q + β) / (((q : ℝ) - 1) * ((q : ℝ) - 2)))
      atTop (𝓝 1) := by
  have h0 : Tendsto (fun q : ℕ => (1 : ℝ) / q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hnum : Tendsto (fun q : ℕ => 1 + α * (1 / (q : ℝ)) + β * (1 / (q : ℝ)) ^ 2) atTop
      (𝓝 (1 + α * 0 + β * 0 ^ 2)) :=
    (tendsto_const_nhds.add (h0.const_mul α)).add ((h0.pow 2).const_mul β)
  have hden : Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) * (1 - 2 * (1 / (q : ℝ)))) atTop
      (𝓝 ((1 - 0) * (1 - 2 * 0))) :=
    (tendsto_const_nhds.sub h0).mul (tendsto_const_nhds.sub (h0.const_mul 2))
  have := hnum.div hden (by norm_num)
  simp only [mul_zero, add_zero, sub_zero, zero_pow two_ne_zero] at this
  norm_num at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have : (q : ℝ) ≠ 0 := by intro h0; linarith
  have : (q : ℝ) - 1 ≠ 0 := by intro h0; linarith
  have : (q : ℝ) - 2 ≠ 0 := by intro h0; linarith
  simp only [Pi.div_apply]
  field_simp

theorem tendsto_card_k3Shifts (w : ℕ) (hw : 1 ≤ w) :
    Tendsto (fun q : ℕ => 6 * ((k3Shifts q w).card : ℝ) / (((q : ℝ) - 1) * ((q : ℝ) - 2)))
      atTop (𝓝 (3 / w)) := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hlo := (tendsto_quad_ratio (-(w : ℝ)) (-(w : ℝ) ^ 2)).const_mul (3 / (w : ℝ))
  have hhi := (tendsto_quad_ratio 0 0).const_mul (3 / (w : ℝ))
  rw [mul_one] at hlo hhi
  have key : ∀ᶠ q : ℕ in atTop, 0 < ((q : ℝ) - 1) * ((q : ℝ) - 2) ∧
      (q : ℝ) ^ 2 - (w : ℝ) ^ 2 - w * q ≤ 2 * w * (k3Shifts q w).card ∧
      2 * (w : ℝ) * (k3Shifts q w).card ≤ (q : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with q hq
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    obtain ⟨b1, b2⟩ := card_k3Shifts_bounds q w hw
    exact ⟨by nlinarith, by exact_mod_cast b1, by exact_mod_cast b2⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [key] with q ⟨hd, b1, b2⟩
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) hd]
    nlinarith
  · filter_upwards [key] with q ⟨hd, b1, b2⟩
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_div, div_le_div_iff₀ hd (by positivity)]
    nlinarith

/-- **Remark `rem:k3-limit`.**  For `k = 3`,
`lim_{q→∞} q (1 - |ℬ_{h,3}(q)| / \binom{q}{3}) = 3 ∑_{w=2}^{h} φ(w)/w`. -/
theorem k3_limit (h : ℕ) :
    Tendsto (fun q : ℕ => (q : ℝ) * (1 - ((BhSets h 3 q).card : ℝ) / (q.choose 3)))
      atTop (𝓝 (3 * ∑ w ∈ Icc 2 h, (φ w : ℝ) / w)) := by
  have hlim : Tendsto (fun q : ℕ => ∑ w ∈ Icc 2 h, (φ w : ℝ) *
      (6 * ((k3Shifts q w).card : ℝ) / (((q : ℝ) - 1) * ((q : ℝ) - 2))))
      atTop (𝓝 (∑ w ∈ Icc 2 h, (φ w : ℝ) * (3 / w))) := by
    refine tendsto_finset_sum _ fun w hw => ?_
    rw [mem_Icc] at hw
    exact (tendsto_card_k3Shifts w (by omega)).const_mul _
  have hval : ∑ w ∈ Icc 2 h, (φ w : ℝ) * (3 / w) = 3 * ∑ w ∈ Icc 2 h, (φ w : ℝ) / w := by
    rw [mul_sum]; exact sum_congr rfl fun w _ => by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hsum := sizeCount_add h 3 q
  have hN := card_nonBh_three h q
  have hch : q.choose 3 * 6 = q * (q - 1) * (q - 2) := by
    have := Nat.descFactorial_eq_factorial_mul_choose q 3
    simp [Nat.descFactorial, Nat.factorial] at this
    rw [mul_comm, ← this]; ring
  have hchR : (q.choose 3 : ℝ) = (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) - 2) / 6 := by
    have : ((q.choose 3 * 6 : ℕ) : ℝ) = ((q * (q - 1) * (q - 2) : ℕ) : ℝ) := by
      exact_mod_cast hch
    push_cast [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_sub (show 2 ≤ q by omega)] at this
    linarith
  have hNB : ((BhSets h 3 q).card : ℝ) +
      ∑ w ∈ Icc 2 h, (φ w : ℝ) * ((k3Shifts q w).card : ℝ) = q.choose 3 := by
    rw [card_BhSets]
    have : ((sizeCount h 3 q (M h 3) + ∑ w ∈ Icc 2 h, φ w * (k3Shifts q w).card : ℕ) : ℝ) =
        (q.choose 3 : ℝ) := by rw [← hN]; exact_mod_cast hsum
    push_cast at this; exact this
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) - 1 ≠ 0 := by intro h0; linarith
  have h2 : (q : ℝ) - 2 ≠ 0 := by intro h0; linarith
  have hq0 : (q : ℝ) ≠ 0 := by intro h0; linarith
  have hc0 : (q.choose 3 : ℝ) ≠ 0 := by rw [hchR]; positivity
  have hB : ((BhSets h 3 q).card : ℝ) = (q.choose 3 : ℝ) -
      ∑ w ∈ Icc 2 h, (φ w : ℝ) * ((k3Shifts q w).card : ℝ) := by linarith
  have : ∑ w ∈ Icc 2 h, (φ w : ℝ) * (6 * ((k3Shifts q w).card : ℝ) / (((q : ℝ) - 1) *
      ((q : ℝ) - 2))) = 6 * (∑ w ∈ Icc 2 h, (φ w : ℝ) * ((k3Shifts q w).card : ℝ)) /
      (((q : ℝ) - 1) * ((q : ℝ) - 2)) := by
    rw [mul_sum, sum_div]; exact sum_congr rfl fun w _ => by ring
  rw [hB, hchR]
  rw [this]
  field_simp
  ring

end Sumsets
