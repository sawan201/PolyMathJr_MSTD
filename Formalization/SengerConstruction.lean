import RequestProject.SengerCounting

/-!
# The construction

Where the lower bounds come from.  Start with the triple `(a, a+r, a+s*r)`, whose
only primitive relation is `(s-1, -s, 1)`, and append coordinates one at a time,
skipping any value that would create a second relation.  At most
`(2h+1)^(j+1) + j` values are forbidden at each stage, so at least `q/2` survive
once `q` is large enough.  That gives `(q/2)^(k-3)` tuples over each starting
triple; dividing by `k!` turns labelled tuples into sets.
-/

open scoped BigOperators
open Filter Finset

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

/-- "Exactly one primitive relevant relation up to sign", spelled out: existence
and uniqueness in a single package. -/
def ExactlyOnePrimitiveRelation {k : ℕ} (h : ℕ) (A d : Fin k → ℤ) : Prop :=
  Primitive d ∧ Relevant h d ∧ Satisfies A d ∧
    ∀ e, Primitive e → Relevant h e → Satisfies A e → e = d ∨ e = -d

/-- The paper's hypothesis gives the `UniqueDirection` form that the counting
lemmas in `Main` actually consume. -/
theorem exactlyOne_implies_uniqueDirection {h k : ℕ} {A d : Fin k → ℤ}
    (hu : ExactlyOnePrimitiveRelation h A d) : UniqueDirection h A d := by
  intro x hx y hy heq
  -- d' = x - y as integers
  let d' : Fin k → ℤ := fun i => (x i : ℤ) - (y i : ℤ)
  -- d' satisfies A
  have hd'_satisfies : Satisfies A d' := by
    simp [Satisfies, d']
    have heq' : ∑ i, (x i : ℤ) * A i = ∑ i, (y i : ℤ) * A i := by
      simp [eval] at heq
      exact heq
    have : ∑ i, ((x i : ℤ) - (y i : ℤ)) * A i = ∑ i, (x i : ℤ) * A i - ∑ i, (y i : ℤ) * A i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, heq']
    ring
  -- d' is balanced
  have hd'_bal : Balanced d' := by
    simp [Balanced, d']
    simp [X] at hx hy
    have h1 : (∑ i, (x i : ℤ)) = h := by exact_mod_cast hx.2
    have h2 : (∑ i, (y i : ℤ)) = h := by exact_mod_cast hy.2
    rw [← Finset.sum_sub_distrib]
    simp [h1, h2]
  -- d' has weight ≤ h
  have hd'_wt : weight d' ≤ h := by
    simp only [weight, posPart]
    simp [X] at hx
    have hxsum := hx.2
    rw [← hxsum]
    apply Finset.sum_le_sum
    intro i _
    simp only [d']
    by_cases hxy : x i ≥ y i
    · have heq : (x i : ℤ) - (y i : ℤ) = (x i - y i : ℕ) := by omega
      rw [heq, Int.toNat_natCast]
      exact Nat.sub_le _ _
    · have hle : (x i : ℤ) - (y i : ℤ) ≤ 0 := by linarith
      rw [Int.toNat_of_nonpos hle]
      exact Nat.zero_le _
  by_cases hd'_zero : d' = 0
  · -- `d' = 0`: then `x = y` and any `m` does.
    use 0
    intro i
    simp [d'] at hd'_zero
    have := congr_fun hd'_zero i
    simp at this
    linarith
  · -- Otherwise pass to a primitive generator `d''` of `d'`.
    obtain ⟨d'', hd'_prim, m, hm_ne, hd'_eq⟩ := exists_primitive_generator hd'_zero
    -- d'' satisfies A (since m ≠ 0)
    have hd''_satisfies : Satisfies A d'' := by
      simp [Satisfies] at hd'_satisfies ⊢
      have h1 : ∑ i, d' i * A i = m * ∑ i, d'' i * A i := by
        simp only [hd'_eq]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1] at hd'_satisfies
      exact mul_eq_zero.mp hd'_satisfies |>.resolve_left hm_ne
    -- d'' is balanced
    have hd''_bal : Balanced d'' := by
      have hsum_d' : Balanced d' := hd'_bal
      rw [Balanced] at hsum_d' ⊢
      have hsum_eq : ∑ i, d' i = m * ∑ i, d'' i := by
        simp only [hd'_eq, mul_comm m, Finset.sum_mul]
      rw [hsum_eq] at hsum_d'
      exact mul_eq_zero.mp hsum_d' |>.resolve_left hm_ne
    -- Weight: `weight d' = |m| * weight d''` for balanced `d''`, and `|m| ≥ 1`.
    have hd''_wt : weight d'' ≤ h := by
      let c := Int.natAbs m
      have hc : c > 0 := Int.natAbs_pos.mpr hm_ne
      have h_abs_m : c ≥ 1 := by omega
      have h_posPart_mul_pos : ∀ x : ℤ, ∀ c : ℕ, c > 0 → ((c : ℤ) * x).toNat = c * x.toNat := by
        intro x c hc
        by_cases hx : x ≥ 0
        · have h1 : (c : ℤ) * x ≥ 0 := by positivity
          have : (c : ℤ) * x = ((c * x.toNat : ℕ) : ℤ) := by simp [Int.toNat_of_nonneg hx]
          rw [this, Int.toNat_natCast]
        · have hx' : x < 0 := lt_of_not_ge hx
          have h1 : (c : ℤ) * x < 0 := by nlinarith
          simp [Int.toNat_of_nonpos (le_of_lt h1), Int.toNat_of_nonpos (le_of_lt hx')]
      have h_posPart_mul_neg : ∀ x : ℤ, ∀ c : ℕ, c > 0 → ((-((c : ℤ))) * x).toNat = c * (-x).toNat := by
        intro x c hc
        by_cases hx : x ≥ 0
        · have h1 : (-((c : ℤ))) * x ≤ 0 := by nlinarith
          have h2 : -x ≤ 0 := by linarith
          rw [Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h2]; ring
        · have hx' : x < 0 := lt_of_not_ge hx
          have h1 : (-((c : ℤ))) * x = (c : ℤ) * (-x) := by ring
          have h2 : (c : ℤ) * (-x) ≥ 0 := by nlinarith
          have h3 : (c : ℤ) * (-x) = ((c * (-x).toNat : ℕ) : ℤ) := by simp [Int.toNat_of_nonneg (by linarith : -x ≥ 0)]
          rw [h1, h3, Int.toNat_natCast]
      have hweight_neg : weight (-d'') = weight d'' := by
        simp only [weight]
        have h1 : ∀ i, posPart (-d'') i = negPart d'' i := fun i => rfl
        simp_rw [h1]
        exact sum_negPart_eq_weight hd''_bal
      have h_weight_eq : weight d' = c * weight d'' := by
        simp only [weight]
        have hm_cases : m = c ∨ m = -c := by
          by_cases hm : 0 ≤ m
          · left; exact (Int.natAbs_of_nonneg hm).symm
          · right
            have hm' : m < 0 := lt_of_not_ge hm
            have : (-m) = (c : ℤ) := by
              have h1 : Int.natAbs (-m) = c := by rw [Int.natAbs_neg]
              exact (Int.ofNat_natAbs_of_nonneg (by linarith : -m ≥ 0)).symm.trans (h1.symm ▸ rfl)
            linarith
        rcases hm_cases with hm_pos | hm_neg
        · -- `m > 0`: positive parts scale
          have hd'_eq' : d' = c • d'' := by
            ext i
            simp only [d']
            rw [hm_pos] at hd'_eq
            exact hd'_eq i
          rw [hd'_eq']
          simp only [posPart, Pi.smul_apply]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact h_posPart_mul_pos (d'' i) c hc
        · -- `m < 0`: positive and negative parts swap
          have hd'_eq' : d' = c • (-d'') := by
            ext i
            simp only [d']
            rw [hm_neg] at hd'_eq
            simp at hd'_eq ⊢
            linarith [hd'_eq i]
          rw [hd'_eq']
          simp only [posPart, Pi.smul_apply]
          have hnegPart : ∀ i, ((c : ℤ) * -d'' i).toNat = c * negPart d'' i := by
            intro i
            simp [negPart]
            have h2 : (c : ℤ) * -d'' i = -((c : ℤ) * d'' i) := by ring
            rw [← h2]
            have h3 : -(c : ℤ) * d'' i = (c : ℤ) * -d'' i := by ring
            rw [h3.symm]
            exact h_posPart_mul_neg (d'' i) c hc
          show ∑ x, ((c : ℤ) * -d'' x).toNat = c * ∑ x, (d'' x).toNat
          simp_rw [hnegPart]
          rw [← Finset.mul_sum, sum_negPart_eq_weight hd''_bal]
          rfl
      have h1 : weight d'' ≤ c * weight d'' := Nat.le_mul_of_pos_left _ hc
      calc weight d'' ≤ c * weight d'' := h1
        _ = weight d' := h_weight_eq.symm
        _ ≤ h := hd'_wt
    -- `d''` is relevant, so uniqueness applies to it.
    have hd''_ne : d'' ≠ 0 := by
      intro h
      subst h
      have : (2 : ℤ).natAbs = 1 ∨ (2 : ℤ) = 0 := hd'_prim 2 (fun _ => dvd_zero 2)
      simp at this
    have hd''_rel : Relevant h d'' := ⟨hd''_ne, hd''_bal, hd''_wt⟩
    have huniq := hu.2.2.2 d'' hd'_prim hd''_rel hd''_satisfies
    rcases huniq with hd''_eq_d | hd''_eq_neg
    · -- d'' = d
      use m
      intro i
      simp only [d'] at hd'_eq
      rw [hd'_eq i, hd''_eq_d]
    · -- d'' = -d
      use -m
      intro i
      simp only [d'] at hd'_eq
      rw [hd'_eq i, hd''_eq_neg]
      simp

/-- The paper's lemma as stated, with `UniqueDirection` no longer an input. -/
theorem card_hSumset_exactly_one {h k : ℕ} {A d : Fin k → ℤ}
    (hk : 0 < k) (hu : ExactlyOnePrimitiveRelation h A d) :
    #(hSumset h A) = M h k - M (h - weight d) k := by
  have hudir := exactlyOne_implies_uniqueDirection hu
  obtain ⟨hd_prim, hd_rel, hd_sat, _⟩ := hu
  obtain ⟨hd0, hbal, hwt_le⟩ := hd_rel
  apply card_hSumset_unique_relation hk hd0 hbal rfl hwt_le hd_sat hd_prim hudir

/-- The initial triple `(a,a+r,a+s*r)`. -/
def initialTriple (a r s : ℕ) : Fin 3 → ℤ :=
  fun i ↦ ![(a : ℤ), (a + r : ℤ), (a + s * r : ℤ)] i

/-- Its distinguished relation `(s-1,-s,1)`. -/
def initialRelation (s : ℕ) : Fin 3 → ℤ :=
  fun i ↦ ![((s : ℤ) - 1), -(s : ℤ), 1] i

theorem initialRelation_primitive (s : ℕ) : Primitive (initialRelation s) := by
  intro m hm
  -- The relation at index 2 is 1
  have h_m_div_one : m ∣ 1 := by
    have := hm 2
    simp [initialRelation] at this
    exact this
  have : m = 1 ∨ m = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one h_m_div_one)
  rcases this with rfl | rfl <;> simp

theorem initialRelation_balanced (s : ℕ) : Balanced (initialRelation s) := by
  simp [Balanced, initialRelation]
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem initialRelation_weight (s : ℕ) (hs : 1 ≤ s) :
    weight (initialRelation s) = s := by
  simp [weight, initialRelation, posPart]
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  omega

theorem initialTriple_satisfies (a r s : ℕ) :
    Satisfies (initialTriple a r s) (initialRelation s) := by
  simp [Satisfies, initialTriple, initialRelation]
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- For `r > 0` and `s ≥ 2` this really is the only primitive balanced relation the
triple satisfies, up to sign. -/
theorem initialTriple_unique (a r s : ℕ) (hr : 0 < r) (hs : 2 ≤ s) :
    ExactlyOnePrimitiveRelation s (initialTriple a r s) (initialRelation s) := by
  refine ⟨initialRelation_primitive s, ?_, initialTriple_satisfies a r s, ?_⟩
  · -- Relevant s (initialRelation s)
    refine ⟨?_, initialRelation_balanced s, ?_⟩
    · -- initialRelation s ≠ 0
      intro heq
      have h := congr_fun heq 2
      simp [initialRelation] at h
    · -- weight (initialRelation s) ≤ s
      rw [initialRelation_weight s (by omega : 1 ≤ s)]
  · -- Uniqueness
    intro e he_prim he_rel he_satisf
    -- Balance and `Satisfies` together force `e 1 = -s * e 2`, `e 0 = (s-1) * e 2`.
    have hsatisf : e 0 * a + e 1 * (a + r) + e 2 * (a + s * r) = 0 := by
      simp [Satisfies, initialTriple] at he_satisf
      convert he_satisf using 1
      rw [Fin.sum_univ_three]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hbal : e 0 + e 1 + e 2 = 0 := by
      have := he_rel.2.1
      simp only [Balanced, Fin.sum_univ_three] at this
      exact this
    have he1s : e 1 + s * e 2 = 0 := by
      have h1 : r * (e 1 + s * e 2) = 0 := by
        have : e 0 * a + e 1 * (a + r) + e 2 * (a + s * r) =
               (e 0 + e 1 + e 2) * a + (e 1 + s * e 2) * r := by ring
        rw [hbal] at this
        linarith
      exact (mul_eq_zero.mp h1).resolve_left (by omega)
    have he1 : e 1 = -(s : ℤ) * e 2 := by linarith
    have he0 : e 0 = ((s : ℤ) - 1) * e 2 := by linarith
    -- So e = e 2 • initialRelation s
    have he_eq_mult : e = (e 2) • initialRelation s := by
      ext i
      simp only [initialRelation, Pi.smul_apply, smul_eq_mul]
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    -- From primitivity, e 2 must be ±1
    have he2_unit : e 2 = 1 ∨ e 2 = -1 := by
      have hdiv : ∀ i : Fin 3, e 2 ∣ e i := by
        intro i
        fin_cases i <;> simp [he0, he1]
      have := he_prim (e 2) hdiv
      rcases this with habs | he2zero
      · rw [Int.natAbs_eq_iff] at habs
        exact habs
      · -- e 2 = 0 would mean e = 0, contradicting he_rel
        have : e = 0 := by
          rw [he_eq_mult, he2zero, zero_smul]
        exact absurd this he_rel.1
    rcases he2_unit with he2pos | he2neg
    · left
      rw [he_eq_mult, he2pos]
      simp
    · right
      rw [he_eq_mult, he2neg]
      simp

/-- And it stays the unique one at every level `h ≥ s`. -/
theorem initialTriple_unique_at (h a r s : ℕ) (hr : 0 < r) (hs : 2 ≤ s)
    (hsh : s ≤ h) :
    ExactlyOnePrimitiveRelation h (initialTriple a r s) (initialRelation s) := by
  refine ⟨initialRelation_primitive s, ?_, initialTriple_satisfies a r s, ?_⟩
  · -- Relevant h (initialRelation s)
    refine ⟨?_, initialRelation_balanced s, ?_⟩
    · -- initialRelation s ≠ 0
      intro heq
      have h := congr_fun heq 2
      simp [initialRelation] at h
    · -- weight (initialRelation s) ≤ h
      rw [initialRelation_weight s (by omega : 1 ≤ s)]
      exact hsh
  · -- Uniqueness
    intro e he_prim he_rel he_satisf
    -- Same computation as above.
    have hsatisf : e 0 * a + e 1 * (a + r) + e 2 * (a + s * r) = 0 := by
      simp [Satisfies, initialTriple] at he_satisf
      convert he_satisf using 1
      rw [Fin.sum_univ_three]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hbal : e 0 + e 1 + e 2 = 0 := by
      have := he_rel.2.1
      simp only [Balanced, Fin.sum_univ_three] at this
      exact this
    have he1s : e 1 + s * e 2 = 0 := by
      have h1 : r * (e 1 + s * e 2) = 0 := by
        have : e 0 * a + e 1 * (a + r) + e 2 * (a + s * r) =
               (e 0 + e 1 + e 2) * a + (e 1 + s * e 2) * r := by ring
        rw [hbal] at this
        linarith
      exact (mul_eq_zero.mp h1).resolve_left (by omega)
    have he1 : e 1 = -(s : ℤ) * e 2 := by linarith
    have he0 : e 0 = ((s : ℤ) - 1) * e 2 := by linarith
    -- So e = e 2 • initialRelation s
    have he_eq_mult : e = (e 2) • initialRelation s := by
      ext i
      simp only [initialRelation, Pi.smul_apply, smul_eq_mul]
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    -- From primitivity, e 2 must be ±1
    have he2_unit : e 2 = 1 ∨ e 2 = -1 := by
      have hdiv : ∀ i : Fin 3, e 2 ∣ e i := by
        intro i
        fin_cases i <;> simp [he0, he1]
      have := he_prim (e 2) hdiv
      rcases this with habs | he2zero
      · rw [Int.natAbs_eq_iff] at habs
        exact habs
      · -- e 2 = 0 would mean e = 0, contradicting he_rel
        have : e = 0 := by
          rw [he_eq_mult, he2zero, zero_smul]
        exact absurd this he_rel.1
    rcases he2_unit with he2pos | he2neg
    · left
      rw [he_eq_mult, he2pos]
      simp
    · right
      rw [he_eq_mult, he2neg]
      simp

/-- Extending a tuple by one coordinate. -/
def appendValue {j : ℕ} (A : Fin j → ℤ) (a : ℤ) : Fin (j + 1) → ℤ :=
  Fin.lastCases a A

/-- Extend a relation by a zero coefficient in the new last coordinate. -/
def appendRelation {j : ℕ} (d : Fin j → ℤ) : Fin (j + 1) → ℤ :=
  Fin.lastCases 0 d

/-- A value is forbidden if it repeats an old coordinate, or creates a new
primitive relevant relation that actually uses the new coordinate. -/
def ForbiddenExtension {j : ℕ} (h q : ℕ) (A : Fin j → ℤ) (a : ℤ) : Prop :=
  a < 1 ∨ q < a ∨ (∃ i, a = A i) ∨
    ∃ e : Fin (j + 1) → ℤ, Primitive e ∧ Relevant h e ∧
      Satisfies (appendValue A a) e ∧ e (Fin.last j) ≠ 0

/-- Each coefficient vector forbids at most one value, so a stage rules out at most
`(2h+1)^(j+1) + j` of them — the source's explicit bound. -/
theorem forbidden_extension_count {j h q : ℕ} (A : Fin j → ℤ) :
    #((Finset.Icc (1 : ℤ) q).filter (ForbiddenExtension h q A)) ≤
      (2 * h + 1) ^ (j + 1) + j := by
  let box := relationBox h (j + 1)
  have hbox_card : #box = (2 * h + 1) ^ (j + 1) := by
    show #(relationBox h (j + 1)) = (2 * h + 1) ^ (j + 1)
    simp only [relationBox]
    rw [Finset.card_image_of_injective]
    · simp [Fintype.card_pi]
    · intro f₁ f₂ heq
      funext i
      have := congrFun heq i
      simp at this
      exact Fin.ext (by simp_all)
  -- The forbidden set is covered by the old values (at most `j` of them) together
  -- with one value for each coefficient vector in the box.
  have hsubset : (Finset.Icc (1 : ℤ) q).filter (ForbiddenExtension h q A) ⊆
      Finset.image A Finset.univ ∪
      (box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)).biUnion
        (fun e => Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    simp only [ForbiddenExtension] at *
    rcases ha.2 with h1 | h2 | h3 | ⟨e, he_prim, he_rel, he_satisf, he_last⟩
    · -- a < 1 contradicts ha.1.1
      linarith
    · -- q < a contradicts ha.1.2
      linarith
    · -- ∃ i, a = A i
      simp only [Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨h3.choose, Finset.mem_univ _, h3.choose_spec.symm⟩
    · -- ∃ e ... Satisfies ... e (last j) ≠ 0
      simp only [Finset.mem_union]
      right
      have he_in_box : e ∈ box := by
        have := relevant_coordinate_bound he_rel.2.1 he_rel.2.2
        exact mem_relationBox_iff.mpr (this)
      have he_in_badRel : e ∈ box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0) :=
        Finset.mem_filter.mpr ⟨he_in_box, he_prim, he_rel, he_last⟩
      have : a ∈ Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ha.1, he_satisf⟩
      exact Finset.mem_biUnion.mpr ⟨e, he_in_badRel, this⟩
  calc #(Finset.filter (ForbiddenExtension h q A) (Finset.Icc (1 : ℤ) q))
      ≤ #(Finset.image A Finset.univ ∪
          (box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)).biUnion
            (fun e => Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q))) :=
        Finset.card_mono hsubset
    _ ≤ #(Finset.image A Finset.univ) +
          #((box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)).biUnion
            (fun e => Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q))) :=
        Finset.card_union_le _ _
    _ ≤ j + (2 * h + 1) ^ (j + 1) := by
        -- #(image A univ) ≤ j
        have hcard_A : #(Finset.image A Finset.univ) ≤ j := Finset.card_image_le.trans (by simp)
        -- biUnion size ≤ #badRel ≤ box size
        -- each equation pins `a` down, so at most one value apiece
        have hcard_each : ∀ e ∈ box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0),
            #(Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q)) ≤ 1 := by
          intro e he
          -- `e (last j) ≠ 0`, so `a` is determined
          have he_last_ne : e (Fin.last j) ≠ 0 := Finset.mem_filter.mp he |>.2.2.2
          -- The filter is contained in a singleton
          have hsingleton : Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q) ⊆
              {-(∑ i : Fin j, e (Fin.castSucc i) * A i) / e (Fin.last j)} := by
            intro a ha
            simp only [Finset.mem_filter] at ha
            simp only [Finset.mem_singleton]
            have hsatisf : Satisfies (appendValue A a) e := ha.2
            -- Expand the Satisfies equation
            simp only [Satisfies, appendValue, Fin.sum_univ_castSucc, Fin.lastCases_last,
              Fin.lastCases_castSucc] at hsatisf
            have heq : e (Fin.last j) * a = -(∑ i : Fin j, e (Fin.castSucc i) * A i) := by linarith
            exact (Int.ediv_eq_of_eq_mul_right he_last_ne heq.symm).symm
          exact Finset.card_le_one.mpr (fun x hx y hy => Finset.mem_singleton.mp (hsingleton hx) ▸
            Finset.mem_singleton.mp (hsingleton hy) ▸ rfl)
        have hcard_biUnion : #(
            (box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)).biUnion
              (fun e => Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q))) ≤
          #(box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)) := by
            calc #(
                (box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)).biUnion
                  (fun e => Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q)))
              ≤ ∑ e ∈ box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0),
                  #(Finset.filter (fun a => Satisfies (appendValue A a) e) (Finset.Icc (1 : ℤ) q)) :=
                Finset.card_biUnion_le
            _ ≤ ∑ e ∈ box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0), 1 := by
                apply Finset.sum_le_sum
                exact hcard_each
            _ = #(box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)) := by simp
        have hcard_badRel_le : #(box.filter (fun e => Primitive e ∧ Relevant h e ∧ e (Fin.last j) ≠ 0)) ≤
            #(box) := Finset.card_filter_le _ _
        have hbox_bound : #(box) = (2 * h + 1) ^ (j + 1) := hbox_card
        linarith [hcard_A, hcard_biUnion, hcard_badRel_le, hbox_bound]
    _ = (2 * h + 1) ^ (j + 1) + j := by ring

/-- A permissible extension keeps the unique relation, now with a zero in the new
coordinate. -/
theorem appendValue_preserves_exactlyOne {j h q : ℕ} {A d : Fin j → ℤ} {a : ℤ}
    (hu : ExactlyOnePrimitiveRelation h A d)
    (ha : ¬ ForbiddenExtension h q A a) :
    ExactlyOnePrimitiveRelation h (appendValue A a) (appendRelation d) := by
  obtain ⟨hd_prim, hd_rel, hd_sat, hd_uniq⟩ := hu
  obtain ⟨hd_ne, hd_bal, hd_wt⟩ := hd_rel
  -- What `¬ ForbiddenExtension` buys us: every primitive relevant `e` satisfied by
  -- the extended tuple has `e (last j) = 0`.
  have hNoBadRel : ∀ e : Fin (j + 1) → ℤ, Primitive e → Relevant h e → Satisfies (appendValue A a) e → e (Fin.last j) = 0 := by
    intro e he_prim he_rel he_satisf
    by_contra he_last_ne
    have := ha
    simp only [ForbiddenExtension] at this
    exact this (Or.inr (Or.inr (Or.inr ⟨e, he_prim, he_rel, he_satisf, he_last_ne⟩)))
  refine ⟨?_, ?_, ?_, ?_⟩
  -- 1. primitive
  · intro m hm
    apply hd_prim m
    intro i
    have := hm (Fin.castSucc i)
    simp [appendRelation] at this
    exact this
  -- 2. relevant
  · refine ⟨?_, ?_, ?_⟩
    -- appendRelation d ≠ 0
    · intro h
      apply hd_ne
      ext i
      have := congr_fun h (Fin.castSucc i)
      simp [appendRelation] at this
      exact this
    -- Balanced
    · simp only [Balanced] at hd_bal ⊢
      simp [appendRelation]
      rw [Fin.sum_univ_castSucc]
      simp
      exact hd_bal
    -- weight ≤ h
    · unfold weight at hd_wt ⊢
      rw [Fin.sum_univ_castSucc]
      simp [appendRelation, posPart]
      exact hd_wt
  -- 3. satisfied
  · simp [Satisfies, appendValue, appendRelation]
    rw [Fin.sum_univ_castSucc]
    simp
    exact hd_sat
  -- 4. unique
  · intro e he_prim he_rel he_satisf
    -- `e (last j) = 0`, so `e` is `appendRelation` applied to its restriction.
    have he_last : e (Fin.last j) = 0 := hNoBadRel e he_prim he_rel he_satisf
    let d' : Fin j → ℤ := fun i => e (Fin.castSucc i)
    have he_eq : e = appendRelation d' := by
      ext i
      change e i = (appendRelation d') i
      cases i using Fin.lastCases with
      | last => simp [appendRelation, he_last]
      | cast => simp [appendRelation, d']
    -- `d'` is primitive
    have hd'_prim : Primitive d' := by
      intro m hm
      apply he_prim m
      intro k
      cases k using Fin.lastCases with
      | last => simp [he_last]
      | cast => exact hm _
    have hd'_ne : d' ≠ 0 := by
      intro h
      -- If d' = 0 and e (last j) = 0, then e = 0
      have he_zero : e = 0 := by
        ext i
        cases i using Fin.lastCases with
        | last => simp [he_last]
        | cast => simp [d'] at h; exact congr_fun h _
      have := he_prim 2 (fun _ => he_zero ▸ dvd_zero 2)
      simp at this
    have hd'_bal : Balanced d' := by
      have hsum := he_rel.2.1
      unfold Balanced at hsum ⊢
      rw [Fin.sum_univ_castSucc] at hsum
      simp [he_last] at hsum
      exact hsum
    have hd'_wt : weight d' ≤ h := by
      have hsum := he_rel.2.2
      unfold weight at hsum ⊢
      rw [Fin.sum_univ_castSucc] at hsum
      simp only [he_last, posPart, Int.toNat_zero] at hsum
      exact hsum
    -- and it satisfies `A`
    have hd'_sat : Satisfies A d' := by
      unfold Satisfies at he_satisf ⊢
      rw [Fin.sum_univ_castSucc] at he_satisf
      simp [appendValue] at he_satisf
      simp [he_last] at he_satisf
      exact he_satisf
    -- Use uniqueness of d
    rcases hd_uniq d' hd'_prim ⟨hd'_ne, hd'_bal, hd'_wt⟩ hd'_sat with hd'_eq | hd'_eq
    · left
      rw [he_eq, hd'_eq]
    · right
      rw [he_eq, hd'_eq]
      ext i
      cases i using Fin.lastCases with
      | last => simp [appendRelation]
      | cast => simp [appendRelation]

/-- So at least `q/2` values survive at each stage, once `q` clears the threshold. -/
theorem many_permissible_extensions {j h q : ℕ} (A : Fin j → ℤ)
    (hq : 2 * ((2 * h + 1) ^ (j + 1) + j) ≤ q) :
    q / 2 ≤ #((Finset.Icc (1 : ℤ) q).filter
      (fun a ↦ ¬ ForbiddenExtension h q A a)) := by
  have htotal : #(Finset.Icc (1 : ℤ) q) = q := by
    rw [Int.card_Icc]
    simp
  have hforbid_sub : (Finset.Icc (1 : ℤ) q).filter (ForbiddenExtension h q A) ⊆ Finset.Icc (1 : ℤ) q :=
    Finset.filter_subset _ _
  have hperm : Finset.filter (fun a ↦ ¬ ForbiddenExtension h q A a) (Finset.Icc (1 : ℤ) q) =
      Finset.Icc (1 : ℤ) q \ Finset.filter (ForbiddenExtension h q A) (Finset.Icc (1 : ℤ) q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor <;> intro h <;> tauto
  rw [hperm]
  have hcard_compl : #(Finset.Icc (1 : ℤ) q \ Finset.filter (ForbiddenExtension h q A) (Finset.Icc (1 : ℤ) q)) =
      q - #(Finset.filter (ForbiddenExtension h q A) (Finset.Icc (1 : ℤ) q)) := by
    rw [Finset.card_sdiff]
    simp [htotal, Finset.inter_eq_left.mpr hforbid_sub]
  rw [hcard_compl]
  -- Use forbidden_extension_count
  have hforbid_bound : #(Finset.filter (ForbiddenExtension h q A) (Finset.Icc (1 : ℤ) q)) ≤
      (2 * h + 1) ^ (j + 1) + j := forbidden_extension_count A
  -- `q/2` already dominates the forbidden count, so at least `q/2` values remain.
  omega

/-- Ordered labeled constructions produced by the inductive procedure. -/
def IsConstructedTuple (h s q : ℕ) {k : ℕ} (A : Fin k → ℤ) : Prop :=
  (∀ i, 1 ≤ A i ∧ A i ≤ q) ∧ Function.Injective A ∧
  ∃ a r : ℕ, 1 ≤ a ∧ 1 ≤ r ∧ a + s * r ≤ q ∧
    ∃ i0 i1 i2 : Fin k, i0.val = 0 ∧ i1.val = 1 ∧ i2.val = 2 ∧
    A i0 = a ∧ A i1 = a + r ∧ A i2 = a + s * r ∧
    ExactlyOnePrimitiveRelation h A
      (fun i ↦ if i.val = 0 then (s : ℤ) - 1 else
        if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0)

noncomputable def constructedTuples (h s q k : ℕ) : Finset (Fin k → ℤ) :=
  (qVectors q k).filter (IsConstructedTuple h s q)

/-- Tuples obtained by repeatedly appending permissible coordinates to a fixed
initial triple. -/
noncomputable def extensionChains (h q : ℕ) (A : Fin 3 → ℤ) :
    (n : ℕ) → Finset (Fin (3 + n) → ℤ)
  | 0 => {A}
  | n + 1 =>
      (extensionChains h q A n).biUnion fun B =>
        ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)).image
          (appendValue B)

/-- Distinct one-step extensions have distinct prefixes and last coordinates, so
the chain count multiplies. -/
theorem extensionChains_card_lower (h q n : ℕ) (A : Fin 3 → ℤ)
    (hq : ∀ j, 3 ≤ j → j ≤ 3 + n →
      2 * ((2 * h + 1) ^ (j + 1) + j) ≤ q) :
    (q / 2) ^ n ≤ #(extensionChains h q A n) := by
  induction n with
  | zero =>
    simp [extensionChains]
  | succ n ih =>
    have hq' : ∀ j, 3 ≤ j → j ≤ 3 + n → 2 * ((2 * h + 1) ^ (j + 1) + j) ≤ q := by
      intro j hj1 hj2
      exact hq j hj1 (by omega)
    have ih' := ih hq'
    rw [extensionChains]
    -- At least `q/2` permissible extensions of each `B`.
    have h_card_each : ∀ B ∈ extensionChains h q A n,
        q / 2 ≤ #((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)) := by
      intro B hB
      apply many_permissible_extensions
      exact hq (3 + n) (by omega) (by omega)
    -- appendValue is injective when restricted to a fixed prefix
    have h_append_inj : ∀ B : Fin (3 + n) → ℤ, Function.Injective (appendValue B) := by
      intro B a₁ a₂ heq
      have := congrFun heq (Fin.last _)
      simp only [appendValue, Fin.lastCases_last] at this
      exact this
    -- The images are disjoint: the prefix can be read back off the extended tuple.
    have h_disjoint : ∀ B B' : Fin (3 + n) → ℤ, B ∈ extensionChains h q A n → B' ∈ extensionChains h q A n →
        B ≠ B' → Disjoint (Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)))
          (Finset.image (appendValue B') ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B' a))) := by
      intro B B' hB hB' hne
      rw [Finset.disjoint_left]
      intro x hxmem hxmem'
      rw [Finset.mem_image] at hxmem hxmem'
      obtain ⟨a, ha, hxa⟩ := hxmem
      obtain ⟨a', ha', hxa'⟩ := hxmem'
      have heq : appendValue B a = appendValue B' a' := hxa.trans hxa'.symm
      have hBB' : B = B' := by
        ext i
        have := congrFun heq (Fin.castSucc i)
        simp [appendValue] at this
        exact this
      exact hne hBB'
    -- Image cardinality equals filter cardinality (by injectivity)
    have h_image_card : ∀ B ∈ extensionChains h q A n,
        #(Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))) =
        #((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)) := by
      intro B hB
      exact Finset.card_image_of_injective _ (h_append_inj B)
    -- Lower bound on biUnion cardinality
    have h_biUnion_lower : #((extensionChains h q A n).biUnion
        (fun B => Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)))) ≥
        (extensionChains h q A n).card * (q / 2) := by
        -- every term of the sum is at least `q/2`
        have h_each_ge : ∀ B ∈ extensionChains h q A n,
            (q / 2) ≤ #(Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))) := by
          intro B hB
          rw [h_image_card B hB]
          exact h_card_each B hB
        -- Images are pairwise disjoint
        have h_pwidj : Set.PairwiseDisjoint (extensionChains h q A n : Set (Fin (3 + n) → ℤ))
            (fun B => Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))) := by
          intro B hB B' hB' hne
          exact h_disjoint B B' hB hB' hne
        -- biUnion cardinality = sum (when disjoint)
        have hcard_eq : #((extensionChains h q A n).biUnion
            (fun B => Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)))) =
            ∑ B ∈ extensionChains h q A n, #(Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))) := by
          exact Finset.card_biUnion h_pwidj
        calc #((extensionChains h q A n).biUnion
            (fun B => Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))))
            = ∑ B ∈ extensionChains h q A n, #(Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a))) := hcard_eq
          _ ≥ ∑ _B ∈ extensionChains h q A n, (q / 2) := Finset.sum_le_sum h_each_ge
          _ = (extensionChains h q A n).card * (q / 2) := by simp
    -- Final bound: (q/2)^(n+1) = (q/2)^n * (q/2) ≤ #(extensionChains) * (q/2) ≤ biUnion
    have h_exp : (q / 2) ^ (n + 1) = (q / 2) ^ n * (q / 2) := by ring
    rw [h_exp]
    calc (q / 2) ^ n * (q / 2) ≤ #(extensionChains h q A n) * (q / 2) := by
          apply Nat.mul_le_mul_right
          exact ih'
      _ ≤ #((extensionChains h q A n).biUnion
          (fun B => Finset.image (appendValue B) ((Finset.Icc (1 : ℤ) q).filter (fun a ↦ ¬ ForbiddenExtension h q B a)))) := h_biUnion_lower

/-- The coordinate formula agrees with the three-term initial relation. -/
theorem initialRelation_eq_coordinate_formula (s : ℕ) :
    initialRelation s = fun i : Fin 3 ↦
      if i.val = 0 then (s : ℤ) - 1 else
        if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0 := by
  ext i
  show ![((s : ℤ) - 1), -(s : ℤ), 1] i = _
  rcases i with ⟨_ | _ | _ | n, hn⟩
  · rfl
  · rfl
  · rfl
  · omega

/-- Appending a zero coefficient leaves the coordinate formula unchanged. -/
theorem appendRelation_coordinate_formula (s j : ℕ) (hj : 3 ≤ j) :
    appendRelation (fun i : Fin j ↦
      if i.val = 0 then (s : ℤ) - 1 else
        if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) =
      (fun i : Fin (j + 1) ↦
        if i.val = 0 then (s : ℤ) - 1 else
          if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) := by
  ext i
  by_cases hi : i = Fin.last j
  · subst hi
    simp [appendRelation]
    omega
  · obtain ⟨i', hi'⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [← hi']
    simp [appendRelation]

/-- One permissible step preserves every invariant the construction needs. -/
theorem appendValue_preserves_construction_spec {j h s q : ℕ}
    (hj : 3 ≤ j) {A : Fin j → ℤ}
    (hb : ∀ i, 1 ≤ A i ∧ A i ≤ q) (hinj : Function.Injective A)
    (hu : ExactlyOnePrimitiveRelation h A
      (fun i ↦ if i.val = 0 then (s : ℤ) - 1 else
        if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0))
    {a : ℤ} (ha : a ∈ (Finset.Icc (1 : ℤ) q).filter
      (fun x ↦ ¬ ForbiddenExtension h q A x)) :
    (∀ i, 1 ≤ appendValue A a i ∧ appendValue A a i ≤ q) ∧
      Function.Injective (appendValue A a) ∧
      ExactlyOnePrimitiveRelation h (appendValue A a)
        (fun i ↦ if i.val = 0 then (s : ℤ) - 1 else
          if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) := by
  -- Extract a's bounds from membership in the filter
  have ha_mem := ha
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha_mem
  have ha_lb : 1 ≤ a := ha_mem.1.1
  have ha_ub : a ≤ q := ha_mem.1.2
  -- 1. bounds
  have hbounds : ∀ i, 1 ≤ appendValue A a i ∧ appendValue A a i ≤ q := by
    intro i
    cases i using Fin.lastCases with
    | last => simp [appendValue]; exact ⟨ha_lb, ha_ub⟩
    | cast => simp [appendValue]; exact hb _
  -- 2. injectivity
  have ha_not_in_range : ∀ i : Fin j, a ≠ A i := by
    intro i hi
    have : ForbiddenExtension h q A a := Or.inr (Or.inr (Or.inl ⟨i, hi⟩))
    exact ha_mem.2 this
  have hinj' : Function.Injective (appendValue A a) := by
    intro i₁ i₂ heq
    have heq' : (appendValue A a) i₁ = (appendValue A a) i₂ := heq
    cases i₁ using Fin.lastCases with
    | last =>
      cases i₂ using Fin.lastCases with
      | last => rfl
      | cast =>
        exfalso
        simp [appendValue] at heq'
        exact ha_not_in_range _ heq'
    | cast =>
      cases i₂ using Fin.lastCases with
      | last =>
        exfalso
        simp [appendValue] at heq'
        exact ha_not_in_range _ heq'.symm
      | cast =>
        simp [appendValue] at heq'
        have := hinj heq'
        simp_all [Fin.ext_iff]
  -- 3. the unique relation
  -- First, show ¬ ForbiddenExtension h q A a
  have ha_not_forbidden : ¬ ForbiddenExtension h q A a := ha_mem.2
  have h_exact := appendValue_preserves_exactlyOne hu ha_not_forbidden
  -- Now convert appendRelation d to coordinate formula
  rw [appendRelation_coordinate_formula s j hj] at h_exact
  exact ⟨hbounds, hinj', h_exact⟩

/-- Everything the chain needs, carried from the initial triple all the way along
the construction. -/
theorem extensionChains_spec (h s q a r n : ℕ)
    (hs : 2 ≤ s) (hsh : s ≤ h) (ha : 1 ≤ a) (hr : 1 ≤ r)
    (haq : a + s * r ≤ q) :
    ∀ B ∈ extensionChains h q (initialTriple a r s) n,
      (∀ i, 1 ≤ B i ∧ B i ≤ q) ∧ Function.Injective B ∧
      ExactlyOnePrimitiveRelation h B
        (fun i ↦ if i.val = 0 then (s : ℤ) - 1 else
          if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) := by
  induction n with
  | zero =>
    intro B hB
    simp [extensionChains] at hB
    rw [hB]
    have heq : (fun i : Fin 3 ↦ if i.val = 0 then (s : ℤ) - 1 else if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) = initialRelation s := by
      ext i
      simp [initialRelation]
      fin_cases i <;> simp <;> omega
    have hr_pos : (1 : ℤ) ≤ r := by exact_mod_cast hr
    have hs_pos : (1 : ℤ) ≤ s := by linarith [hs]
    have hsr_pos : (1 : ℤ) ≤ s * r := by nlinarith
    have hr_ne_srs : (r : ℤ) ≠ s * r := by nlinarith
    refine ⟨?_, ?_, by rw [heq]; exact initialTriple_unique_at h a r s (by omega : 0 < r) hs hsh⟩
    · -- Bounds: use that a ≤ q and a + s*r ≤ q
      have hr_le_srs : (r : ℤ) ≤ s * r := by nlinarith
      have ha_le_q : (a : ℤ) ≤ q := by linarith [haq]
      have haq' : (a : ℤ) + s * r ≤ q := by exact_mod_cast haq
      intro i
      fin_cases i <;> simp [initialTriple] <;> [constructor <;> linarith; constructor <;> [linarith; linarith]; constructor <;> linarith]
    · -- Injectivity
      have hne1 : (a : ℤ) ≠ (a : ℤ) + r := by linarith
      have hne2 : (a : ℤ) ≠ (a : ℤ) + s * r := by linarith [hsr_pos]
      have hne3 : (a : ℤ) + r ≠ (a : ℤ) + s * r := by intro h; exact hr_ne_srs (by linarith : (r : ℤ) = s * r)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [initialTriple] <;> linarith
  | succ n ih =>
    intro B hB
    rw [extensionChains] at hB
    rw [Finset.mem_biUnion] at hB
    obtain ⟨B', hB', hBmem⟩ := hB
    rw [Finset.mem_image] at hBmem
    obtain ⟨a, ha, rfl⟩ := hBmem
    exact appendValue_preserves_construction_spec (by omega : 3 ≤ 3 + n)
      (ih B' hB').1 (ih B' hB').2.1 (ih B' hB').2.2 ha

/-- A bounded positive tuple lives in the finite box `qVectors q k`. -/
theorem mem_qVectors_of_bounds {q k : ℕ} {A : Fin k → ℤ}
    (hb : ∀ i, 1 ≤ A i ∧ A i ≤ q) : A ∈ qVectors q k := by
  rw [qVectors]
  refine Finset.mem_image.mpr ⟨fun i => ⟨(A i).toNat - 1, by
    have := hb i
    omega⟩, Finset.mem_univ _, ?_⟩
  funext i
  have h := hb i
  have h1 : 1 ≤ (A i).toNat := by
    have := Int.toNat_of_nonneg (by linarith : 0 ≤ A i)
    linarith
  have h2 : (A i).toNat = A i := Int.toNat_of_nonneg (by linarith : 0 ≤ A i)
  simp only
  have heq : ((A i).toNat - 1 + 1 : ℕ) = (A i).toNat := Nat.sub_add_cancel h1
  have := congrArg (↑· : ℕ → ℤ) heq
  simp at this
  rw [this]
  simp [show 0 ≤ A i by linarith]

/-- Recasting a chain at its final arity gives a constructed tuple with the
prescribed first three coordinates. -/
theorem extensionChain_cast_isConstructed (h s q k a r : ℕ)
    (hk : 3 ≤ k) (hs : 2 ≤ s) (hsh : s ≤ h) (ha : 1 ≤ a) (hr : 1 ≤ r)
    (haq : a + s * r ≤ q)
    {B : Fin (3 + (k - 3)) → ℤ}
    (hB : B ∈ extensionChains h q (initialTriple a r s) (k - 3)) :
    IsConstructedTuple h s q (fun i : Fin k ↦ B ⟨i.val, by omega⟩) ∧
      (fun i : Fin k ↦ B ⟨i.val, by omega⟩) ⟨0, by omega⟩ = (a : ℤ) ∧
      (fun i : Fin k ↦ B ⟨i.val, by omega⟩) ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ) ∧
      (fun i : Fin k ↦ B ⟨i.val, by omega⟩) ⟨2, by omega⟩ = ((a + s * r : ℕ) : ℤ) := by
  have hspec := extensionChains_spec h s q a r (k - 3) hs hsh ha hr haq B hB
  -- B agrees with initialTriple on the first 3 coordinates
  have hB_prefix : ∀ i : Fin 3, B ⟨i.val, by omega⟩ = initialTriple a r s i := by
    -- Induction following the structure of extensionChains
    have aux : ∀ n : ℕ, ∀ B' ∈ extensionChains h q (initialTriple a r s) n,
        ∀ i : Fin 3, B' ⟨i.val, by omega⟩ = initialTriple a r s i := by
      intro n
      induction n with
      | zero =>
        intro B' hB' i
        simp [extensionChains] at hB'
        rw [hB']
      | succ n ih =>
        intro B' hB' i
        rw [extensionChains] at hB'
        rw [Finset.mem_biUnion] at hB'
        obtain ⟨B'', hB'', hB'mem⟩ := hB'
        rw [Finset.mem_image] at hB'mem
        obtain ⟨a', ha', rfl⟩ := hB'mem
        simp only [appendValue]
        have hi_lt : (i : ℕ) < 3 + n + 1 := by omega
        have h1 : (i : ℕ) < 3 + n := by omega
        have heq : ⟨i.val, hi_lt⟩ = Fin.castSucc ⟨i.val, h1⟩ := by
          ext; simp
        rw [heq, Fin.lastCases_castSucc]
        exact ih B'' hB'' i
    exact aux (k - 3) B hB
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Goal 1: IsConstructedTuple h s q (fun i ↦ B ⟨i.val, by omega⟩)
  · refine ⟨?_, ?_, a, r, ha, hr, haq,
            ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
    · intro i
      exact hspec.1 ⟨i.val, by omega⟩
    · intro x y hxy
      have heq := hspec.2.1 hxy
      apply Fin.ext
      simp at heq
      exact heq
    · simp only
      rw [hB_prefix ⟨0, by omega⟩]
      simp [initialTriple]
    · simp only
      rw [hB_prefix ⟨1, by omega⟩]
      simp [initialTriple]
    · simp only
      rw [hB_prefix ⟨2, by omega⟩]
      simp [initialTriple]
    · -- by induction along the chain
      have hcard : 3 + (k - 3) = k := by omega
      have aux : ∀ n : ℕ, ∀ B' ∈ extensionChains h q (initialTriple a r s) n,
          ExactlyOnePrimitiveRelation h (fun i : Fin (3 + n) => B' i)
            (fun i : Fin (3 + n) => if i.val = 0 then (s : ℤ) - 1 else
              if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) := by
        intro n
        induction n with
        | zero =>
          intro B' hB'
          simp [extensionChains] at hB'
          rw [hB']
          have heq : (fun i : Fin 3 ↦ if i.val = 0 then (s : ℤ) - 1 else if i.val = 1 then -(s : ℤ) else if i.val = 2 then 1 else 0) = initialRelation s := by
            ext i
            simp [initialRelation]
            fin_cases i <;> simp <;> omega
          rw [heq]
          exact initialTriple_unique_at h a r s (by omega : 0 < r) hs hsh
        | succ n ih =>
          intro B' hB'
          rw [extensionChains] at hB'
          rw [Finset.mem_biUnion] at hB'
          obtain ⟨B'', hB'', hB'mem⟩ := hB'
          rw [Finset.mem_image] at hB'mem
          obtain ⟨a', ha', rfl⟩ := hB'mem
          have hind := ih B'' hB''
          rw [Finset.mem_filter] at ha'
          have h_exact := appendValue_preserves_exactlyOne hind ha'.2
          rw [appendRelation_coordinate_formula s (3 + n) (by omega : 3 ≤ 3 + n)] at h_exact
          exact h_exact
      -- Apply aux to get the result for Fin (k), since 3 + (k - 3) = k
      have hresult := aux (k - 3) B hB
      let e : Fin k → Fin (3 + (k - 3)) := fun i => ⟨i.val, by omega⟩
      have he_inj : Function.Injective e := by
        intro i j h
        show i = j
        have : (e i).val = (e j).val := congr_arg Fin.val h
        simp only [e] at this
        exact Fin.ext this
      -- Transfer ExactlyOnePrimitiveRelation via e
      have hcard : k = 3 + (k - 3) := by omega
      let equiv : Fin k ≃ Fin (3 + (k - 3)) := Equiv.ofBijective (fun i => ⟨i.val, by omega⟩) ⟨he_inj, by
        intro j
        use ⟨j.val, by omega⟩⟩
      have hequiv_symm : ∀ j : Fin (3 + (k - 3)), (equiv.symm j).val = j.val := by
        intro j
        have := equiv.apply_symm_apply j
        exact congr_arg Fin.val this
      have hequiv_val : ∀ i : Fin k, (equiv i).val = i.val := by
        intro i
        rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- primitive
        intro m hm
        have he_surj : Function.Surjective e := by
          intro j
          use ⟨j.val, by omega⟩
        have hm' : ∀ j : Fin (3 + (k - 3)), m ∣ (fun i : Fin (3 + (k - 3)) => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) j := by
          intro j
          obtain ⟨i, hi⟩ := he_surj j
          have := hm i
          simp only at this ⊢
          rw [← hi]
          exact this
        exact hresult.1 m hm'
      · -- relevant
        -- d ∘ e ≠ 0
        have hne : (fun i : Fin k => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) ≠ 0 := by
          intro hz
          have := congr_fun hz ⟨0, by omega⟩
          simp at this
          linarith
        -- Balanced
        have hbal : Balanced (fun i : Fin k => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) := by
          have h := hresult.2.1.2.1
          rw [Balanced] at h ⊢
          have heq : ∑ i : Fin k, (fun i : Fin k => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) i =
                     ∑ i : Fin (3 + (k - 3)), (fun i : Fin (3 + (k - 3)) => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) i := by
            rw [← Equiv.sum_comp equiv]
            simp [equiv]
          linarith
        -- weight ≤ h
        have hwt : weight (fun i : Fin k => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) ≤ h := by
          have h := hresult.2.1.2.2
          unfold weight at h ⊢
          simp only [posPart] at h ⊢
          rw [← Equiv.sum_comp equiv.symm]
          convert h using 2
          simp [hequiv_symm]
        exact ⟨hne, hbal, hwt⟩
      · -- satisfied
        have h := hresult.2.2.1
        simp only [Satisfies] at h ⊢
        have : ∑ i : Fin k, (fun i => if (i : ℕ) = 0 then (s : ℤ) - 1 else if (i : ℕ) = 1 then -(s : ℤ) else if (i : ℕ) = 2 then 1 else 0) i * B ⟨i.val, by omega⟩ =
               ∑ j : Fin (3 + (k - 3)), (fun j => if (j : ℕ) = 0 then (s : ℤ) - 1 else if (j : ℕ) = 1 then -(s : ℤ) else if (j : ℕ) = 2 then 1 else 0) j * B j := by
          symm
          rw [← Equiv.sum_comp equiv.symm]
          congr 1
          ext i
          simp [hequiv_symm]
        linarith
      · -- unique
        intro e' he'_prim he'_rel he'_sat
        -- Transport e' to Fin (3 + (k - 3)) via equiv.symm
        let e'' : Fin (3 + (k - 3)) → ℤ := fun j => e' (equiv.symm j)
        have he'_equiv : ∀ i : Fin k, e' i = e'' (equiv i) := by
          intro i
          simp [e'']
        have he''_prim : Primitive e'' := by
          intro m hm
          exact he'_prim m (by
            intro i
            rw [he'_equiv i]
            exact hm (equiv i))
        have he''_rel : Relevant h e'' := by
          rw [Relevant] at he'_rel ⊢
          refine ⟨?_, ?_, ?_⟩
          · intro hz
            apply he'_rel.1
            ext i
            rw [he'_equiv]
            have := congr_fun hz (equiv i)
            exact this
          · have := he'_rel.2.1
            rw [Balanced] at this ⊢
            rw [← Equiv.sum_comp equiv]
            convert this using 2
            simp [e'']
          · have := he'_rel.2.2
            unfold weight at this ⊢
            simp only [posPart] at this ⊢
            rw [← Equiv.sum_comp equiv]
            convert this using 2
            simp [e'']
        have he''_sat : Satisfies (fun i => B i) e'' := by
          simp only [Satisfies] at he'_sat ⊢
          rw [← Equiv.sum_comp equiv]
          have heq : ∀ j : Fin k, e'' (equiv j) * B (equiv j) = e' j * B ⟨j.val, by omega⟩ := by
            intro j
            simp only [e'']
            have h1 : equiv.symm (equiv j) = j := equiv.symm_apply_apply j
            rw [h1]
            rfl
          simp_rw [heq]
          exact he'_sat
        cases hresult.2.2.2 e'' he''_prim he''_rel he''_sat with
        | inl h =>
          left
          ext i
          rw [he'_equiv]
          have := congr_fun h (equiv i)
          simp [hequiv_val] at this
          exact this
        | inr h =>
          right
          ext i
          rw [he'_equiv]
          have := congr_fun h (equiv i)
          simp [hequiv_val] at this
          convert this using 2
          simp [Pi.neg_apply]
          congr 1 <;> simp [hequiv_val, Fin.ext_iff]
  -- Goal 2: B ⟨0, _⟩ = a
  · simp only
    rw [hB_prefix ⟨0, by omega⟩]
    simp [initialTriple]
  -- Goal 3: B ⟨1, _⟩ = a + r
  · simp only
    rw [hB_prefix ⟨1, by omega⟩]
    simp [initialTriple]
  -- Goal 4: B ⟨2, _⟩ = a + s * r
  · simp only
    rw [hB_prefix ⟨2, by omega⟩]
    simp [initialTriple]

/-- Every chain lands in the right initial-coordinate fibre of `constructedTuples`. -/
theorem extensionChains_subset_initial_fiber (h s q k a r : ℕ)
    (hk : 3 ≤ k) (hs : 2 ≤ s) (hsh : s ≤ h) (ha : 1 ≤ a) (hr : 1 ≤ r)
    (haq : a + s * r ≤ q) :
    (extensionChains h q (initialTriple a r s) (k - 3)).image
        (fun B i ↦ B ⟨i.val, by omega⟩) ⊆
      (constructedTuples h s q k).filter fun A ↦
        A ⟨0, by omega⟩ = (a : ℤ) ∧ A ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ) ∧
          A ⟨2, by omega⟩ = ((a + s * r : ℕ) : ℤ) := by
  intro A hA
  rw [Finset.mem_image] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  obtain ⟨hconst, h0, h1, h2⟩ := extensionChain_cast_isConstructed h s q k a r hk hs hsh ha hr haq hB
  rw [constructedTuples]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_qVectors_of_bounds hconst.1, hconst⟩, h0, h1, h2⟩

/-- For each admissible `(a,r)` the construction still has `q/2` choices at every
remaining coordinate. -/
theorem constructedTuples_initial_fiber_lower_bound (h s q k a r : ℕ)
    (hk : 3 ≤ k) (hs : 2 ≤ s) (hsh : s ≤ h)
    (ha : 1 ≤ a ∧ a ≤ q / 2) (hr : 1 ≤ r ∧ r ≤ q / (2 * s))
    (hq : 2 * ((2 * h + 1) ^ (k + 1) + k + 2 * s) ≤ q) :
    (q / 2) ^ (k - 3) ≤
      #((constructedTuples h s q k).filter fun A ↦
        A ⟨0, by omega⟩ = (a : ℤ) ∧ A ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ) ∧
          A ⟨2, by omega⟩ = ((a + s * r : ℕ) : ℤ)) := by
  -- First prove a + s * r ≤ q from the bounds on a and r
  have has : a + s * r ≤ q := by
    have hr' : s * r ≤ s * (q / (2 * s)) := Nat.mul_le_mul_left s hr.2
    have hsdiv : s * (q / (2 * s)) ≤ q / 2 := by
      have h2s_pos : 0 < 2 * s := by omega
      have : s * (q / (2 * s)) * 2 ≤ q := by
        calc s * (q / (2 * s)) * 2 = s * 2 * (q / (2 * s)) := by ring
          _ = (2 * s) * (q / (2 * s)) := by ring
          _ ≤ q := Nat.mul_div_le q (2 * s)
      omega
    omega
  -- The fiber contains the image of extensionChains
  have hsubset : (extensionChains h q (initialTriple a r s) (k - 3)).image
      (fun B (i : Fin k) ↦ B ⟨i.val, by omega⟩) ⊆
    (constructedTuples h s q k).filter fun A ↦
      A ⟨0, by omega⟩ = (a : ℤ) ∧ A ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ) ∧
        A ⟨2, by omega⟩ = ((a + s * r : ℕ) : ℤ) :=
    extensionChains_subset_initial_fiber h s q k a r hk hs hsh ha.1 hr.1 has
  have hcard_le :
    Finset.card ((extensionChains h q (initialTriple a r s) (k - 3)).image
      (fun B (i : Fin k) ↦ B ⟨i.val, by omega⟩)) ≤
    Finset.card ((constructedTuples h s q k).filter (fun A ↦
      A ⟨0, by omega⟩ = (a : ℤ) ∧ A ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ) ∧
        A ⟨2, by omega⟩ = ((a + s * r : ℕ) : ℤ))) :=
    Finset.card_le_card hsubset
  -- The image has the same cardinality as extensionChains (by injectivity of cast)
  have himage_card :
    Finset.card ((extensionChains h q (initialTriple a r s) (k - 3)).image
      (fun B (i : Fin k) ↦ B ⟨i.val, by omega⟩)) =
    Finset.card (extensionChains h q (initialTriple a r s) (k - 3)) := by
    apply Finset.card_image_of_injective
    intro B B' h_eq
    have hlen : 3 + (k - 3) = k := by omega
    ext i
    have hi : i.val < k := by omega
    have := congr_fun h_eq ⟨i.val, hi⟩
    simp at this
    exact this
  have hcard_lower : (q / 2) ^ (k - 3) ≤
      Finset.card (extensionChains h q (initialTriple a r s) (k - 3)) := by
    apply extensionChains_card_lower h q (k - 3) (initialTriple a r s)
    intro j hj1 hj2
    have hjk : j ≤ k := by omega
    have h1 : (2 * h + 1) ^ (j + 1) ≤ (2 * h + 1) ^ (k + 1) := by
      apply pow_le_pow_right₀ (by omega : 1 ≤ 2 * h + 1)
      omega
    omega
  exact hcard_lower.trans (himage_card.symm ▸ hcard_le)

/-- Fibers corresponding to distinct initial parameter pairs are disjoint. -/
theorem constructedTuples_initial_fibers_disjoint (h s q k : ℕ) (hk : 3 ≤ k)
    {a r a' r' : ℕ} (hne : (a, r) ≠ (a', r')) :
    Disjoint
      ((constructedTuples h s q k).filter fun A ↦
        A ⟨0, by omega⟩ = (a : ℤ) ∧ A ⟨1, by omega⟩ = ((a + r : ℕ) : ℤ))
      ((constructedTuples h s q k).filter fun A ↦
        A ⟨0, by omega⟩ = (a' : ℤ) ∧ A ⟨1, by omega⟩ = ((a' + r' : ℕ) : ℤ)) := by
  rw [Finset.disjoint_left]
  intro A hAin1 hAin2
  simp only [Finset.mem_filter, constructedTuples] at hAin1 hAin2
  have hA1 := hAin1.2
  have hA2 := hAin2.2
  -- From hA1 and hA2, we get a = a' and a + r = a' + r'
  have ha : (a : ℤ) = a' := by rw [← hA1.1, hA2.1]
  have hr : (a + r : ℤ) = a' + r' := by
    have := hA1.2.symm.trans hA2.2
    simp at this
    exact this
  have ha' : a = a' := by omega
  have hr' : r = r' := by omega
  exact hne (Prod.ext ha' hr')

/-- Explicit ordered-construction lower bound. -/
theorem constructedTuples_lower_bound (h s q k : ℕ)
    (hk : 3 ≤ k) (hs : 2 ≤ s) (hsh : s ≤ h)
    (hq : 2 * ((2 * h + 1) ^ (k + 1) + k + 2 * s) ≤ q) :
    (q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3) ≤
      #(constructedTuples h s q k) := by
  let choices := Finset.Icc 1 (q / 2) ×ˢ Finset.Icc 1 (q / (2 * s))
  -- Each fiber (fixing positions 0, 1, 2)
  let fiber := fun (p : ℕ × ℕ) => (constructedTuples h s q k).filter (fun A =>
    A ⟨0, by omega⟩ = (p.1 : ℤ) ∧ A ⟨1, by omega⟩ = ((p.1 + p.2 : ℕ) : ℤ) ∧
    A ⟨2, by omega⟩ = ((p.1 + s * p.2 : ℕ) : ℤ))
  have h_fiber_card : ∀ p ∈ choices, (q / 2) ^ (k - 3) ≤ #(fiber p) := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have ha : 1 ≤ p.1 ∧ p.1 ≤ q / 2 := Finset.mem_Icc.mp hp'.1
    have hr : 1 ≤ p.2 ∧ p.2 ≤ q / (2 * s) := Finset.mem_Icc.mp hp'.2
    exact constructedTuples_initial_fiber_lower_bound h s q k p.1 p.2 hk hs hsh ha hr hq
  -- Fibers are pairwise disjoint (via subset)
  have h_fiber_subset : ∀ p ∈ choices, fiber p ⊆
      (constructedTuples h s q k).filter (fun A => A ⟨0, by omega⟩ = (p.1 : ℤ) ∧ A ⟨1, by omega⟩ = ((p.1 + p.2 : ℕ) : ℤ)) := by
    intro p _ A hA
    simp only [fiber, Finset.mem_filter] at hA ⊢
    exact ⟨hA.1, hA.2.1, hA.2.2.1⟩
  have h_fiber_disjoint : Set.PairwiseDisjoint (choices : Set (ℕ × ℕ)) (fun p => fiber p) := by
    intro p hp q' hq' hpq'
    simp only [Function.onFun]
    exact Disjoint.mono (h_fiber_subset p hp) (h_fiber_subset q' hq')
      (constructedTuples_initial_fibers_disjoint h s q k hk hpq')
  -- The union of fibers is contained in constructedTuples
  have h_union_subset : choices.biUnion fiber ⊆ constructedTuples h s q k := by
    intro A hA
    rw [Finset.mem_biUnion] at hA
    obtain ⟨p, hp, hAp⟩ := hA
    exact Finset.mem_filter.mp hAp |>.1
  -- Lower bound via sum of fiber cardinalities
  have h_card_biUnion : #(choices.biUnion fiber) = ∑ p ∈ choices, #(fiber p) := by
    exact Finset.card_biUnion h_fiber_disjoint
  have h_sum_bound : ∑ p ∈ choices, #(fiber p) ≥ choices.card * (q / 2) ^ (k - 3) := by
    have h1 : ∑ p ∈ choices, (q / 2) ^ (k - 3) ≤ ∑ p ∈ choices, #(fiber p) :=
      Finset.sum_le_sum h_fiber_card
    simp at h1
    exact h1
  have h_subset_bound : #(choices.biUnion fiber) ≤ #(constructedTuples h s q k) :=
    Finset.card_le_card h_union_subset
  have h_choices_card : choices.card = (q / 2) * (q / (2 * s)) := by
    simp [choices, Finset.card_product, Nat.card_Icc]
  rw [← h_choices_card]
  linarith

/-- Forgetting labels has multiplicity at most `k!`. -/
theorem tupleSet_fiber_card_le_factorial {q k : ℕ} (A : Finset ℕ) :
    #((qVectors q k).filter fun v ↦
      tupleSet (fun i ↦ Int.toNat (v i)) = A ∧ Function.Injective v) ≤ k.factorial := by
  by_cases hA : A.card = k
  · -- Define an injection from the fiber to Equiv.Perm (Fin k)
    have hA' : Fintype A := Fintype.ofFinset A (by simp)
    have hcard : Fintype.card A = k := Fintype.card_coe A ▸ hA
    -- Reference equivalence Fin k ≃ A
    let φ : Fin k ≃ A := Fintype.equivOfCardEq (by simp [hcard.symm])
    have hcard_perm : Fintype.card (Equiv.Perm (Fin k)) = k.factorial := by simp [Fintype.card_perm]
    -- For `v` in the fibre, `i ↦ (v i).toNat` is a bijection onto `A`; composing
    -- with a fixed reference bijection turns it into a permutation of `Fin k`.
    have hv_toNat_inj : ∀ v : Fin k → ℤ, v ∈ qVectors q k →
        (tupleSet fun i => (v i).toNat) = A → Function.Injective v →
        ∀ x y, (v x).toNat = (v y).toNat → x = y := by
      intro v hv_mem hv_image hv_inj x y hxy
      have hv_pos : ∀ i, 0 ≤ v i := by
        intro i
        rw [qVectors] at hv_mem
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv_mem
        obtain ⟨a, rfl⟩ := hv_mem
        exact le_add_of_nonneg_left (Int.ofNat_zero_le _)
      have hvxy : v x = v y := by
        have hx := Int.toNat_of_nonneg (hv_pos x)
        have hy := Int.toNat_of_nonneg (hv_pos y)
        rw [hxy] at hx
        linarith
      exact hv_inj hvxy
    let S : Finset (Fin k → ℤ) := (qVectors q k).filter fun v =>
      tupleSet (fun i => (v i).toNat) = A ∧ Function.Injective v
    let g : S → Equiv.Perm (Fin k) := fun ⟨v, hv⟩ =>
      let hv' := Finset.mem_filter.mp hv
      let memproof : ∀ i, (v i).toNat ∈ A := fun i => by
        rw [← hv'.2.1]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      (Equiv.ofBijective (fun i => ⟨(v i).toNat, memproof i⟩) ⟨fun x y hxy => hv_toNat_inj v (hv'.1) hv'.2.1 hv'.2.2 x y (Subtype.mk.inj hxy), by
        intro ⟨a, ha⟩
        have := hv'.2.1
        rw [tupleSet] at this
        have := Finset.mem_image.mp (this ▸ ha)
        obtain ⟨a_1, _, ha_eq⟩ := this
        use a_1
        exact Subtype.ext ha_eq
      ⟩).trans φ.symm
    -- `g` is injective on `S`
    have hg_inj : ∀ x y : S, g x = g y → x = y := by
      intro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      have hv' := Finset.mem_filter.mp hv
      have hw' := Finset.mem_filter.mp hw
      have heq : ∀ i, (v i).toNat = (w i).toNat := by
        intro i
        have h1 := congrArg (fun σ : Equiv.Perm (Fin k) => σ i) hvw
        have h2 := φ.symm.injective h1
        simp at h2
        exact h2
      -- Since v and w are injective with same toNat values, v = w
      ext i
      have hi := heq i
      have hv_qvec : v ∈ qVectors q k := hv'.1
      have hw_qvec : w ∈ qVectors q k := hw'.1
      have hv_pos : ∀ j, 0 ≤ v j := by
        rw [qVectors] at hv_qvec
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv_qvec
        obtain ⟨a, rfl⟩ := hv_qvec
        intro j
        simp only
        exact le_add_of_nonneg_left (Int.ofNat_zero_le _)
      have hw_pos : ∀ j, 0 ≤ w j := by
        rw [qVectors] at hw_qvec
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw_qvec
        obtain ⟨a, rfl⟩ := hw_qvec
        intro j
        simp only
        exact le_add_of_nonneg_left (Int.ofNat_zero_le _)
      exact (by
        have := Int.toNat_of_nonneg (hv_pos i)
        have := Int.toNat_of_nonneg (hw_pos i)
        linarith)
    have hcard_le : S.card ≤ Fintype.card (Equiv.Perm (Fin k)) := by
      have hinj : Set.InjOn g Set.univ := by
        intro x _ y _ hxy
        exact hg_inj x y hxy
      rw [← Fintype.card_coe]
      exact Fintype.card_le_of_injective g (fun x y hxy => hg_inj x y hxy)
    exact le_trans hcard_le (hcard_perm.le)
  · have hempty : {v ∈ qVectors q k | tupleSet (fun i => (v i).toNat) = A ∧ Function.Injective v} = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv_mem hv_pair
      obtain ⟨hv_image, hv_inj⟩ := hv_pair
      have hcard : A.card = k := by
        rw [← hv_image, tupleSet, Finset.card_image_of_injective]
        · simp
        · have hv_pos : ∀ i, 0 ≤ v i := by
            intro i
            rw [qVectors] at hv_mem
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv_mem
            obtain ⟨a, rfl⟩ := hv_mem
            exact le_add_of_nonneg_left (Int.ofNat_zero_le _)
          exact fun x y h => hv_inj (by
            have hx := hv_pos x
            have hy := hv_pos y
            have := Int.toNat_of_nonneg hx
            have := Int.toNat_of_nonneg hy
            linarith)
      exact hA hcard
    rw [hempty]
    simp

/-- Distinct constructed `k`-sets satisfying the required exact relation. -/
noncomputable def constructedSets (h s q k : ℕ) : Finset (Finset ℕ) :=
  (qSubsets q k).filter fun A ↦
    ∃ v ∈ constructedTuples h s q k,
      tupleSet (fun i ↦ Int.toNat (v i)) = A

/-- Converting the labelled bound into one about genuinely distinct sets. -/
theorem constructedSets_lower_bound (h s q k : ℕ)
    (hk : 3 ≤ k) (hs : 2 ≤ s) (hsh : s ≤ h)
    (hq : 2 * ((2 * h + 1) ^ (k + 1) + k + 2 * s) ≤ q) :
    (q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3) ≤
      k.factorial * #(constructedSets h s q k) := by
  -- First get the lower bound on constructedTuples
  have htuples : (q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3) ≤ #(constructedTuples h s q k) :=
    constructedTuples_lower_bound h s q k hk hs hsh hq
  calc (q / 2) * (q / (2 * s)) * (q / 2) ^ (k - 3)
      ≤ #(constructedTuples h s q k) := htuples
    _ ≤ k.factorial * #(constructedSets h s q k) := by
        -- each set has at most `k!` labelled preimages
        have hbound : ∀ A ∈ constructedSets h s q k,
            #((constructedTuples h s q k).filter (fun v => tupleSet (fun i => Int.toNat (v i)) = A)) ≤ k.factorial := by
          intro A hA
          unfold constructedSets at hA
          simp at hA
          obtain ⟨v, hv_tuples, hv_eq⟩ := hA
          have hsub : (constructedTuples h s q k).filter (fun v => tupleSet (fun i => Int.toNat (v i)) = A) ⊆
            (qVectors q k).filter fun v => tupleSet (fun i => Int.toNat (v i)) = A ∧ Function.Injective v := by
            intro v' hv'
            simp only [constructedTuples, Finset.mem_filter] at hv' ⊢
            obtain ⟨⟨hv'_qvec, hv'_ict⟩, hv'_eq⟩ := hv'
            exact ⟨hv'_qvec, hv'_eq, hv'_ict.2.1⟩
          exact le_trans (Finset.card_le_card hsub) (tupleSet_fiber_card_le_factorial A)
        -- constructedTuples is the union of fibers over constructedSets
        have hunion : constructedTuples h s q k =
          (constructedSets h s q k).biUnion (fun A => (constructedTuples h s q k).filter
            (fun v => tupleSet (fun i => Int.toNat (v i)) = A)) := by
          ext v
          rw [Finset.mem_biUnion]
          simp only [constructedSets, Finset.mem_filter]
          constructor
          · intro hv
            simp [qSubsets, Finset.mem_powersetCard, constructedTuples] at hv ⊢
            use v
            refine ⟨⟨⟨?_, ?_⟩, hv⟩, hv, rfl⟩
            · -- subset
              intro x hx
              rw [tupleSet] at hx
              simp at hx
              obtain ⟨i, rfl⟩ := hx
              have := hv.2.1 i
              rw [Finset.mem_Icc]
              omega
            · -- cardinality
              rw [tupleSet, Finset.card_image_of_injective]
              · simp
              · have := hv.2.2.1
                intro i j hij
                exact this (by
                  have hi := Int.toNat_of_nonneg (by have := hv.2.1 i; linarith : 0 ≤ v i)
                  have hj := Int.toNat_of_nonneg (by have := hv.2.1 j; linarith : 0 ≤ v j)
                  linarith)
          · intro ⟨a, _, hv, _⟩
            exact hv
        have hcard_le : #(constructedTuples h s q k) ≤
            ∑ A ∈ constructedSets h s q k, #((constructedTuples h s q k).filter (fun v => tupleSet (fun i => Int.toNat (v i)) = A)) := by
          conv_lhs => rw [hunion]
          apply Finset.card_biUnion_le
        calc #(constructedTuples h s q k)
            ≤ ∑ A ∈ constructedSets h s q k, #((constructedTuples h s q k).filter (fun v => tupleSet (fun i => Int.toNat (v i)) = A)) := hcard_le
          _ ≤ ∑ _ ∈ constructedSets h s q k, k.factorial := Finset.sum_le_sum hbound
          _ = k.factorial * #(constructedSets h s q k) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end
end Senger
