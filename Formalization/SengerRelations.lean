import RequestProject.Main

/-!
# The relation set `R h k`

primitive, balanced, weight `≤ h`, first nonzero coordinate positive, all inside `[-h,h]^k`.
Two facts get used later — `#(R h k) ≤ (2h+1)^(k-1)`, and any two distinct members
are ℚ-linearly independent.
-/

open scoped BigOperators
open Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option autoImplicit false

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Senger

noncomputable section
open Classical

/-- No common factor beyond `±1`.  The `m = 0` escape is harmless: `0 ∣ d i`
already forces `d i = 0`. -/
def Primitive {k : ℕ} (d : Fin k → ℤ) : Prop :=
  ∀ m : ℤ, (∀ i, m ∣ d i) → m.natAbs = 1 ∨ m = 0

/-- Pins the sign down: first nonzero coordinate positive.  This is how we choose
one of `{d, -d}`. -/
def CanonicalSign {k : ℕ} (d : Fin k → ℤ) : Prop :=
  ∃ i, 0 < d i ∧ ∀ j, j.val < i.val → d j = 0

/-- The box `[-h,h]^k`, which is where all the relevant relations live. -/
def relationBox (h k : ℕ) : Finset (Fin k → ℤ) :=
  Finset.univ.image (fun f : Fin k → Fin (2 * h + 1) ↦
    fun i ↦ (f i : ℤ) - h)

/-- The relation set from the paper, with signs pinned so that each pair `{d,-d}`
shows up once. -/
noncomputable def R (h k : ℕ) : Finset (Fin k → ℤ) :=
  (relationBox h k).filter fun d ↦
    Primitive d ∧ Balanced d ∧ weight d ≤ h ∧ CanonicalSign d

/-- Unfolding the box: membership is just `|d i| ≤ h` coordinatewise. -/
theorem mem_relationBox_iff {h k : ℕ} {d : Fin k → ℤ} :
    d ∈ relationBox h k ↔ ∀ i, |d i| ≤ h := by
  simp only [relationBox, Finset.mem_image]
  constructor
  · rintro ⟨f, _, rfl⟩ i
    simp only [abs_le]
    have hlt : (f i : ℕ) < 2 * h + 1 := Fin.is_lt (f i)
    constructor <;> omega
  · intro hd
    have h1 : ∀ i, 0 ≤ d i + ↑h := fun i => by linarith [hd i, abs_le.mp (hd i)]
    have h2 : ∀ i, d i + ↑h < 2 * ↑h + 1 := fun i => by linarith [hd i, abs_le.mp (hd i)]
    refine ⟨fun i => ⟨(d i + ↑h).toNat, ?_⟩, ?_⟩
    · have h3 : ((d i + ↑h).toNat : ℤ) = d i + ↑h := Int.toNat_of_nonneg (h1 i)
      have h4 : ((d i + ↑h).toNat : ℤ) < 2 * ↑h + 1 := by linarith [h2 i]
      exact_mod_cast h4
    · simp only [Finset.mem_univ, true_and]
      ext i
      simp [Int.toNat_of_nonneg (h1 i)]

/-- Balanced plus weight `≤ h` traps every coordinate in `[-h,h]`.  This is what
makes `R h k` a finite set. -/
theorem relevant_coordinate_bound {h k : ℕ} {d : Fin k → ℤ}
    (hbal : Balanced d) (hwt : weight d ≤ h) :
    ∀ i, |d i| ≤ h := by
  intro i
  have hpos : posPart d i ≤ weight d := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (posPart d j)) (Finset.mem_univ i)
  have hneg : negPart d i ≤ weight d := by
    rw [← sum_negPart_eq_weight hbal]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (negPart d j)) (Finset.mem_univ i)
  have hdiff : d i = posPart d i - negPart d i := by
    simp [posPart, negPart]
  rw [abs_le]
  constructor <;> omega

theorem mem_R_iff {h k : ℕ} {d : Fin k → ℤ} :
    d ∈ R h k ↔
      Primitive d ∧ Balanced d ∧ weight d ≤ h ∧ CanonicalSign d := by
  unfold R
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, prim, bal, wt, sign⟩
    exact ⟨prim, bal, wt, sign⟩
  · intro ⟨prim, bal, wt, sign⟩
    refine ⟨?_, prim, bal, wt, sign⟩
    rw [mem_relationBox_iff]
    exact relevant_coordinate_bound bal wt

/-- Exactly one of `d`, `-d` is canonical. -/
theorem canonicalSign_exactly_one {k : ℕ} {d : Fin k → ℤ} (hd : d ≠ 0) :
    (CanonicalSign d ∧ ¬ CanonicalSign (-d)) ∨
      (CanonicalSign (-d) ∧ ¬ CanonicalSign d) := by
  -- `i₀` = the first nonzero coordinate.
  have hne : ∃ i, d i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hd (funext hc)
  have hne' : (Finset.univ.filter fun i => d i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i₀ : Fin k := Finset.min' (Finset.univ.filter fun i => d i ≠ 0) hne'
  have hi₀_in : i₀ ∈ Finset.univ.filter fun i => d i ≠ 0 := Finset.min'_mem _ hne'
  have hi₀_nonzero : d i₀ ≠ 0 := Finset.mem_filter.mp hi₀_in |>.2
  have hi₀_min : ∀ j : Fin k, j < i₀ → d j = 0 := by
    intro j hj
    by_contra hc
    have hj_in : j ∈ Finset.univ.filter fun i => d i ≠ 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    have := Finset.min'_le _ _ hj_in
    exact hj.not_ge this
  rcases Int.lt_trichotomy (d i₀) 0 with hlt | heq | hgt
  · -- `d i₀ < 0`, so `-d` is the canonical one.
    right
    constructor
    · use i₀
      constructor
      · simp only [Pi.neg_apply]
        linarith
      · intro j hj
        simp only [Pi.neg_apply, hi₀_min j hj, neg_zero]
    · intro ⟨j, hpos, hprev⟩
      by_cases hj : j < i₀
      · have := hi₀_min j hj
        linarith
      · push_neg at hj
        -- `j > i₀` would force `d i₀ = 0`.
        have heqji : i₀ = j := le_antisymm hj (by
          by_contra hi₀_gt_j
          push_neg at hi₀_gt_j
          have hij : i₀ < j := hi₀_gt_j
          have := hprev i₀ hij
          linarith)
        rw [← heqji] at hpos
        linarith
  · exact absurd heq hi₀_nonzero
  · -- `d i₀ > 0`, so `d` itself is canonical.
    left
    constructor
    · use i₀
      exact ⟨hgt, hi₀_min⟩
    · intro ⟨j, hpos, hprev⟩
      simp only [Pi.neg_apply] at hpos hprev
      by_cases hj : j < i₀
      · have := hi₀_min j hj
        linarith
      · push_neg at hj
        -- same argument with the signs flipped
        have heqji : i₀ = j := le_antisymm hj (by
          by_contra hi₀_gt_j
          push_neg at hi₀_gt_j
          have hij : i₀ < j := hi₀_gt_j
          have := hprev i₀ hij
          linarith)
        rw [← heqji] at hpos
        linarith

/-- Canonical representative of the pair `{d,-d}`. -/
def canonicalRepresentative {k : ℕ} (d : Fin k → ℤ) : Fin k → ℤ :=
  if CanonicalSign d then d else -d

theorem canonicalRepresentative_eq_or_neg {k : ℕ} (d : Fin k → ℤ) :
    canonicalRepresentative d = d ∨ canonicalRepresentative d = -d := by
  by_cases h : CanonicalSign d <;> simp [canonicalRepresentative, h]

/-- Divide out the gcd: every nonzero `e` is an integer multiple of a primitive
vector pointing the same way. -/
theorem exists_primitive_generator {k : ℕ} {e : Fin k → ℤ} (he : e ≠ 0) :
    ∃ d : Fin k → ℤ, Primitive d ∧ ∃ m : ℤ, m ≠ 0 ∧ ∀ i, e i = m * d i := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, e i ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (funext h)
  -- `g` = gcd of the coordinates, nonzero since some `e i₀` is.
  let g := (Finset.univ : Finset (Fin k)).gcd e
  have hg_div : ∀ i, g ∣ e i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hg_ne : g ≠ 0 := by
    by_contra hg0
    rw [hg0] at hg_div
    have := hg_div i₀
    simp at this
    exact hi₀ this
  let d := fun i => e i / g
  have he_eq : ∀ i, e i = g * d i := fun i => (Int.mul_ediv_cancel' (hg_div i)).symm
  have hd_prim : Primitive d := by
    intro m hm
    -- `m ∣ d i` for every `i` gives `m * g ∣ e i`, so `m * g ∣ g`, so `m ∣ 1`.
    have hm_g_div : ∀ i, m * g ∣ e i := fun i => by
      rw [he_eq i]
      exact (mul_comm m g ▸ mul_dvd_mul_left g (hm i))
    have hm_g_div_g : m * g ∣ g := Finset.dvd_gcd (fun i _ => hm_g_div i)
    have hm_div_one : m ∣ 1 := by
      obtain ⟨k, hk⟩ := hm_g_div_g
      use k
      exact mul_left_injective₀ hg_ne (by linarith)
    have : m = 1 ∨ m = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hm_div_one)
    rcases this with rfl | rfl <;> simp
  exact ⟨d, hd_prim, g, hg_ne, he_eq⟩

/-- Collisions are exactly detected by `R h k`. -/
theorem collision_iff_exists_mem_R {h k : ℕ} {A : Fin k → ℤ} :
    HasCollision h A ↔ ∃ d ∈ R h k, Satisfies A d := by
  rw [collision_iff_relation]
  constructor
  · -- Forward: pass to the primitive generator, then fix the sign.
    intro ⟨d₀, hr, hs⟩
    have hd₀_ne : d₀ ≠ 0 := hr.1
    obtain ⟨d, hd_prim, m, hm_ne, hd_eq⟩ := exists_primitive_generator hd₀_ne
    have hd_satisfies : Satisfies A d := by
      simp [Satisfies] at hs ⊢
      have : ∑ i, d₀ i * A i = m * ∑ i, d i * A i := by
        simp only [hd_eq]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this] at hs
      exact mul_eq_zero.mp hs |>.resolve_left hm_ne
    have hd_bal : Balanced d := by
      have hsum_d₀ : Balanced d₀ := hr.2.1
      rw [Balanced] at hsum_d₀ ⊢
      have hsum_d₀_eq : ∑ i, d₀ i = m * ∑ i, d i := by
        simp only [hd_eq, mul_comm m, Finset.sum_mul]
      rw [hsum_d₀_eq] at hsum_d₀
      exact mul_eq_zero.mp hsum_d₀ |>.resolve_left hm_ne
    have hd_wt_eq_neg : weight d = weight (-d) := by
      have : ∀ i, posPart (-d) i = negPart d i := fun i => by simp [posPart, negPart]
      simp [weight, this]
      exact (sum_negPart_eq_weight hd_bal).symm
    -- The weight bound survives the division: for balanced vectors
    have hd_wt_or_neg : weight d ≤ h ∨ weight (-d) ≤ h := by
      have hd₀_wt : weight d₀ ≤ h := hr.2.2
      left
      -- `weight d₀ = |m| * weight d`, and `|m| ≥ 1`.
      have hm_abs : |m| ≥ 1 := Int.one_le_abs hm_ne
      have h_wt_rel : weight d₀ ≥ weight d := by
        have h_sum_parts : ∀ x : ℤ, (x.toNat : ℤ) + ((-x).toNat : ℤ) = |x| := by
          intro x
          by_cases hx : x ≥ 0
          · simp [abs_of_nonneg hx, Int.toNat_of_nonneg hx, Int.toNat_of_nonpos (neg_nonpos_of_nonneg hx)]
          · have hx' : x < 0 := lt_of_not_ge hx
            simp [abs_of_neg hx', Int.toNat_of_nonpos (le_of_lt hx'), Int.toNat_of_nonneg (by linarith : -x ≥ 0)]
        have h_scale_parts : ∀ i, (posPart d₀ i : ℤ) + (posPart (-d₀) i : ℤ) =
            |m| * ((posPart d i : ℤ) + (negPart d i : ℤ)) := by
          intro i
          unfold posPart negPart
          show (d₀ i).toNat + ((-d₀ i).toNat : ℤ) = |m| * ((d i).toNat + ((-d i).toNat : ℤ))
          have h1 : (d₀ i).toNat + ((-d₀ i).toNat : ℤ) = |d₀ i| := h_sum_parts (d₀ i)
          have h2 : (d i).toNat + ((-d i).toNat : ℤ) = |d i| := h_sum_parts (d i)
          rw [h1, h2, hd_eq i, abs_mul]
        have h_scale_weight : (weight d₀ : ℤ) + (weight (-d₀) : ℤ) =
            |m| * ((weight d : ℤ) + (weight (-d) : ℤ)) := by
          simp only [weight]
          have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_scale_parts i)
          simp only [Finset.sum_add_distrib] at h
          push_cast
          rw [h, ← Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          simp_rw [negPart, posPart]; rfl
        have hd₀_bal : Balanced d₀ := by
          simp [Balanced] at hd_bal ⊢
          have : ∑ i, d₀ i = m * ∑ i, d i := by
            simp only [hd_eq]
            rw [Finset.mul_sum]
          rw [this, hd_bal, mul_zero]
        have hd₀_wt_eq_neg' : weight d₀ = weight (-d₀) := by
          have h1 : ∑ i, negPart d₀ i = weight d₀ := sum_negPart_eq_weight hd₀_bal
          have h3 : ∀ i, negPart d₀ i = posPart (-d₀) i := fun i => by simp [negPart, posPart]
          rw [← h1, Finset.sum_congr rfl fun i _ => h3 i]
          rfl
        have h_wt_d₀ : weight d₀ = |m|.toNat * weight d := by
          have h_eq_d : (weight d : ℤ) = weight (-d) := by exact_mod_cast hd_wt_eq_neg
          have h_eq_d₀ : (weight d₀ : ℤ) = weight (-d₀) := by exact_mod_cast hd₀_wt_eq_neg'
          have h2' : (weight d₀ : ℤ) + (weight d₀ : ℤ) = |m| * ((weight d : ℤ) + (weight d : ℤ)) := by
            have h2 := h_scale_weight
            nlinarith [h_eq_d, h_eq_d₀]
          have h4 : (weight d₀ : ℤ) = (|m| * weight d : ℤ) := by linarith
          have hm_nat : (|m|.toNat : ℤ) = |m| := Int.toNat_of_nonneg (abs_nonneg m)
          rw [← hm_nat] at h4
          exact_mod_cast h4
        have hm_nat_abs : (1 : ℕ) ≤ |m|.toNat := by
          have h1 : m.natAbs > 0 := Int.natAbs_pos.mpr hm_ne
          omega
        rw [h_wt_d₀]
        rw [ge_iff_le]
        show weight d ≤ |m|.toNat * weight d
        conv_lhs => rw [← Nat.mul_one (weight d)]
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right (weight d) hm_nat_abs
      exact @le_trans ℕ _ (weight d) (weight d₀) h h_wt_rel hd₀_wt
    have hd_ne : d ≠ 0 := by
      intro hd0
      apply hd₀_ne
      ext i
      simp [hd_eq, hd0]
    -- Take whichever of `d`, `-d` is canonical.
    rcases canonicalSign_exactly_one hd_ne with ⟨hd_canon, _⟩ | ⟨hneg_canon, _⟩
    · -- `d` is
      use d
      have hd_wt : weight d ≤ h := by
        rcases hd_wt_or_neg with h' | h'
        · exact h'
        · rw [← hd_wt_eq_neg] at h'; exact h'
      exact ⟨by rw [mem_R_iff]; exact ⟨hd_prim, hd_bal, hd_wt, hd_canon⟩, hd_satisfies⟩
    · -- `-d` is
      use -d
      have hneg_wt : weight (-d) ≤ h := by
        rcases hd_wt_or_neg with h' | h'
        · rw [hd_wt_eq_neg] at h'; exact h'
        · exact h'
      have hprim_neg : Primitive (-d) := fun m hm => hd_prim m fun i => by simpa using hm i
      have hbal_neg : Balanced (-d) := by simp [Balanced] at hd_bal ⊢; linarith
      have hsat_neg : Satisfies A (-d) := by
        unfold Satisfies
        have hd_satisfies' : ∑ i, d i * A i = 0 := hd_satisfies
        convert neg_zero
        simp [neg_mul, Finset.sum_neg_distrib]
        exact hd_satisfies'
      exact ⟨by rw [mem_R_iff]; exact ⟨hprim_neg, hbal_neg, hneg_wt, hneg_canon⟩, hsat_neg⟩
  · -- Backward: membership in `R h k` gives more than `Relevant` asks for.
    intro ⟨d, hdR, hs⟩
    rw [mem_R_iff] at hdR
    obtain ⟨hd_prim, hd_bal, hd_wt, hd_canon⟩ := hdR
    have hd_ne : d ≠ 0 := by
      intro hd0
      rw [hd0] at hd_canon
      simp [CanonicalSign] at hd_canon
    exact ⟨d, ⟨hd_ne, hd_bal, hd_wt⟩, hs⟩

/-- Balance determines the last coordinate, so we lose an exponent in the count. -/
theorem relationBox_balanced_card_bound (h k : ℕ) (hk : 0 < k) :
    #((relationBox h k).filter Balanced) ≤ (2 * h + 1) ^ (k - 1) := by
  -- Inject into `Fin (k-1) → Fin (2h+1)` by forgetting the last coordinate.
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  let ksub : k - 1 ≤ k := Nat.sub_le k 1
  let inject : {d : Fin k → ℤ | d ∈ relationBox h k ∧ Balanced d} → Fin (k - 1) → Fin (2 * h + 1) :=
    fun ⟨d, hd_mem, hd_bal⟩ i =>
      ⟨((d (Fin.castLE ksub i) + h).toNat), by
        have hb := Finset.mem_filter.mp (Finset.mem_filter.mpr ⟨hd_mem, hd_bal⟩) |>.1
        rw [mem_relationBox_iff] at hb
        have := hb (Fin.castLE ksub i)
        simp only [abs_le] at this
        omega⟩
  -- Injective: agreeing on the first `k-1` coordinates forces the last to agree.
  have hinj : Function.Injective inject := by
    intro ⟨d, hd_mem, hd_bal⟩ ⟨d', hd'_mem, hd'_bal⟩ heq
    simp only [Subtype.mk.injEq]
    funext i
    by_cases hi : i.val < k - 1
    · -- inside the first `k-1` coordinates
      let j : Fin (k - 1) := ⟨i.val, hi⟩
      have : inject ⟨d, hd_mem, hd_bal⟩ j = inject ⟨d', hd'_mem, hd'_bal⟩ j := by
        rw [heq]
      simp only [inject] at this
      have hcast : Fin.castLE ksub j = i := by
        apply Fin.ext
        simp [j]
      have := congr_arg Fin.val this
      simp at this
      rw [hcast] at this
      have h1 : 0 ≤ d i + h := by
        have := Finset.mem_filter.mp (Finset.mem_filter.mpr ⟨hd_mem, hd_bal⟩) |>.1
        rw [mem_relationBox_iff] at this
        have := this i
        simp only [abs_le] at this
        linarith
      have h2 : 0 ≤ d' i + h := by
        have := Finset.mem_filter.mp (Finset.mem_filter.mpr ⟨hd'_mem, hd'_bal⟩) |>.1
        rw [mem_relationBox_iff] at this
        have := this i
        simp only [abs_le] at this
        linarith
      linarith [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    · -- the last coordinate, recovered from the others by balance
      have hi_eq : i.val = k - 1 := by omega
      have hi_last : i = ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩ := by
        apply Fin.ext; exact hi_eq
      have agreem : ∀ j : Fin (k-1), d (Fin.castLE ksub j) = d' (Fin.castLE ksub j) := by
        intro j
        have := congr_fun heq j
        simp only [inject] at this
        have := Fin.ext_iff.mp this
        have h1 : 0 ≤ d (Fin.castLE ksub j) + h := by
          have := Finset.mem_filter.mp (Finset.mem_filter.mpr ⟨hd_mem, hd_bal⟩) |>.1
          rw [mem_relationBox_iff] at this
          have := this (Fin.castLE ksub j)
          simp only [abs_le] at this
          linarith
        have h2 : 0 ≤ d' (Fin.castLE ksub j) + h := by
          have := Finset.mem_filter.mp (Finset.mem_filter.mpr ⟨hd'_mem, hd'_bal⟩) |>.1
          rw [mem_relationBox_iff] at this
          have := this (Fin.castLE ksub j)
          simp only [abs_le] at this
          linarith
        linarith [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
      rw [hi_last]
      have hd_bal' : ∑ j : Fin k, d j = 0 := hd_bal
      have hd'_bal' : ∑ j : Fin k, d' j = 0 := hd'_bal
      let lastEl : Fin k := ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩
      have sums_eq : ∑ j : Fin (k-1), d (Fin.castLE ksub j) = ∑ j : Fin (k-1), d' (Fin.castLE ksub j) :=
        Finset.sum_congr rfl fun _ _ => agreem _
      -- Peel `lastEl` off both sums and compare what is left.
      have split_d : ∑ j : Fin k, d j = ∑ j ∈ Finset.univ \ {lastEl}, d j + d lastEl := by
        rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ lastEl)]
      have split_d' : ∑ j : Fin k, d' j = ∑ j ∈ Finset.univ \ {lastEl}, d' j + d' lastEl := by
        rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ lastEl)]
      have bij : Finset.univ \ {lastEl} = Finset.image (Fin.castLE ksub) Finset.univ := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
          Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · intro hj
          use ⟨j.val, by omega⟩
          rfl
        · rintro ⟨i, rfl⟩
          show Fin.castLE ksub i ≠ ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩
          apply ne_of_apply_ne Fin.val
          simp only [Fin.val_castLE]
          exact Nat.ne_of_lt i.isLt
      rw [split_d] at hd_bal'
      rw [split_d'] at hd'_bal'
      rw [bij] at hd_bal' hd'_bal'
      rw [Finset.sum_image] at hd_bal' hd'_bal'
      · linarith
      · intro i _ j _ h; exact Fin.castLE_injective ksub h
      · intro i _ j _ h; exact Fin.castLE_injective ksub h
  let S : Set (Fin k → ℤ) := {d | d ∈ relationBox h k ∧ Balanced d}
  have hmem : ∀ x, x ∈ (relationBox h k).filter Balanced ↔ x ∈ S := by intro x; simp [S]
  haveI : Fintype S := Fintype.ofFinset ((relationBox h k).filter Balanced) hmem
  have hcard : Fintype.card S ≤ Fintype.card (Fin (k - 1) → Fin (2 * h + 1)) :=
    Fintype.card_le_of_injective inject hinj
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  rw [← Fintype.card_ofFinset ((relationBox h k).filter Balanced) hmem]
  convert hcard

/-- The bound behind the `O(h^(k-1))` claim in the paper. -/
theorem card_R_le (h k : ℕ) (hk : 0 < k) :
    #(R h k) ≤ (2 * h + 1) ^ (k - 1) := by
  have hsub : R h k ⊆ (relationBox h k).filter Balanced := by
    show (Finset.filter (fun d => Primitive d ∧ Balanced d ∧ weight d ≤ h ∧ CanonicalSign d) (relationBox h k)) ⊆ (relationBox h k).filter Balanced
    intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mp hd |>.1, Finset.mem_filter.mp hd |>.2.2.1⟩
  exact le_trans (Finset.card_le_card hsub) (relationBox_balanced_card_bound h k hk)

/-- The same bound with the constants spelled out: `2h+1 ≤ 3h` once `h ≥ 1`. -/
theorem card_R_le_explicit_bigO (h k : ℕ) (hk : 0 < k) (hh : 1 ≤ h) :
    #(R h k) ≤ 3 ^ (k - 1) * h ^ (k - 1) := by
  have h1 : #(R h k) ≤ (2 * h + 1) ^ (k - 1) := card_R_le h k hk
  have h2 : 2 * h + 1 ≤ 3 * h := by omega
  calc #(R h k) ≤ (2 * h + 1) ^ (k - 1) := h1
    _ ≤ (3 * h) ^ (k - 1) := Nat.pow_le_pow_left h2 _
    _ = 3 ^ (k - 1) * h ^ (k - 1) := mul_pow _ _ _

/-- Two different members of `R h k` are ℚ-linearly independent: both are primitive
and canonically signed, so neither can be a multiple of the other. -/
theorem pair_linearIndependent_of_mem_R {h k : ℕ} {d e : Fin k → ℤ}
    (hd : d ∈ R h k) (he : e ∈ R h k) (hne : d ≠ e) :
    LinearIndependent ℚ ![(fun i ↦ (d i : ℚ)), (fun i ↦ (e i : ℚ))] := by
  rw [mem_R_iff] at hd he
  have hd_prim := hd.1
  have hd_canon := hd.2.2.2
  have he_prim := he.1
  have he_canon := he.2.2.2
  have he_ne : e ≠ 0 := fun h => by
    rw [h] at he_canon
    simp [CanonicalSign] at he_canon
  have hd_ne : d ≠ 0 := fun h => by
    rw [h] at hd_canon
    simp [CanonicalSign] at hd_canon
  -- The whole content is that `d` is not a rational multiple of `e`.
  have h_not_mult : ∀ q : ℚ, (fun i => (d i : ℚ)) ≠ fun i => q * (e i : ℚ) := by
    intro q hq
    have h_eq : ∀ i, (d i : ℚ) = q * (e i : ℚ) := by
      intro i; exact congr_fun hq i
    obtain ⟨i₀, hi₀⟩ : ∃ i, e i ≠ 0 := by
      by_contra hc; push_neg at hc; exact he_ne (funext hc)
    -- Cross-multiply to clear the denominator: `e i₀ * d i = e i * d i₀`.
    have h_cross : ∀ i, e i₀ * d i = e i * d i₀ := by
      intro i
      have heq := h_eq i
      have heq₀ := h_eq i₀
      have : (e i : ℚ) * (d i₀ : ℚ) = (e i₀ : ℚ) * (d i : ℚ) := by
        rw [heq, heq₀]; ring
      exact_mod_cast this.symm
    have hq_eq' : q = q.num / q.den := by exact q.num_div_den.symm
    have hb_d_ae : (q.den : ℤ) * d i₀ = q.num * e i₀ := by
      have h1 := h_eq i₀
      have h2 : (q.den : ℚ) * (d i₀ : ℚ) = (q.num : ℚ) * (e i₀ : ℚ) := by
        rw [show q = q.num / q.den from q.num_div_den.symm] at h1
        field_simp at h1 ⊢
        linarith
      exact_mod_cast h2
    have hab_gcd : Int.gcd q.num (q.den : ℤ) = 1 := q.reduced
    -- `q.den` then divides every `e i`, and `e` is primitive, so `q.den = 1`.
    have hb_div_ei₀ : (q.den : ℤ) ∣ e i₀ := by
      have hdiv : (q.den : ℤ) ∣ q.num * e i₀ := ⟨d i₀, by linarith⟩
      exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv (by rwa [Int.gcd_comm] at hab_gcd)
    have hb_d_ae_all : ∀ i, (q.den : ℤ) * d i = q.num * e i := by
      intro i
      have h1 := h_cross i
      have h2 := hb_d_ae
      have h3 : (q.den : ℤ) * (e i₀) * (d i) = (q.den : ℤ) * (e i) * (d i₀) := by
        have := h1
        nlinarith
      have h4 : (q.den : ℤ) * e i * d i₀ = e i * (q.den * d i₀) := by ring
      have h5 : e i * (q.den * d i₀) = e i * (q.num * e i₀) := by rw [hb_d_ae]
      have h6 : (q.den : ℤ) * e i₀ * d i = q.num * e i * e i₀ := by linarith
      have h7 : e i₀ * ((q.den : ℤ) * d i) = e i₀ * (q.num * e i) := by linarith
      exact Int.eq_of_mul_eq_mul_left hi₀ h7
    have hb_div_ei_all : ∀ i, (q.den : ℤ) ∣ e i := by
      intro i
      have hdiv : (q.den : ℤ) ∣ q.num * e i := ⟨d i, (hb_d_ae_all i).symm⟩
      exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv (by rwa [Int.gcd_comm] at hab_gcd)
    have hb_eq_one : q.den = 1 := by
      have := he_prim (q.den : ℤ) (hb_div_ei_all)
      rcases this with habs | hzero
      · simp [Int.natAbs_natCast] at habs; exact habs
      · exact absurd hzero (by norm_cast; exact q.den_pos.ne')
    have hd_eq_qnum_e : ∀ i, d i = q.num * e i := by
      intro i; simpa [hb_eq_one] using hb_d_ae_all i
    -- Primitivity of `d` now forces `q.num = ±1`.
    have hqnum_abs : q.num.natAbs = 1 := by
      have hdiv : ∀ i, q.num ∣ d i := fun i => ⟨e i, hd_eq_qnum_e i⟩
      have := hd_prim q.num hdiv
      rcases this with h | hzero
      · exact h
      · -- `q = 0` would make `d = 0`
        exfalso
        apply hd_ne
        funext i
        rw [hd_eq_qnum_e, hzero]
        simp
    have hqnum_eq : q.num = 1 ∨ q.num = -1 := Int.natAbs_eq_iff.mp hqnum_abs
    -- `+1` contradicts `d ≠ e`, and `-1` contradicts both being canonically signed.
    rcases hqnum_eq with hq1 | hqm1
    · -- `q.num = 1`, i.e. `d = e`
      apply hne
      ext i
      simp [hd_eq_qnum_e, hq1]
    · -- `q.num = -1`, i.e. `d = -e`
      obtain ⟨j, hj_pos, hj_prev⟩ := hd_canon
      obtain ⟨i₀, hi₀_pos, hi₀_prev⟩ := he_canon
      have hdj : d j = -e j := by rw [hd_eq_qnum_e, hqm1]; ring
      by_cases hj_lt_i₀ : j < i₀
      · have := hi₀_prev j hj_lt_i₀
        rw [this] at hdj
        linarith
      · -- `j ≥ i₀`
        push_neg at hj_lt_i₀
        -- `j > i₀` forces `d i₀ = 0`, but `d i₀ = -e i₀ < 0`.
        by_cases hj_gt_i₀ : j > i₀
        · have hd_i₀_zero := hj_prev i₀ hj_gt_i₀
          have hd_i₀ : d i₀ = -e i₀ := by rw [hd_eq_qnum_e, hqm1]; ring
          linarith
        · -- `j = i₀`
          have heqji : j = i₀ := le_antisymm (le_of_not_gt hj_gt_i₀) hj_lt_i₀
          rw [heqji] at hdj hj_pos
          linarith
  -- Two nonzero vectors, neither a multiple of the other.
  rw [linearIndependent_fin2]
  constructor
  · -- `e ≠ 0`
    intro h
    apply he_ne
    funext i
    have : (e i : ℚ) = 0 := by simpa using congr_fun h i
    exact_mod_cast this
  · -- no scalar sends `e` to `d`
    intro a ha
    apply h_not_mult a
    ext i
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
    have := congr_fun ha i
    simp at this
    linarith

end
end Senger
