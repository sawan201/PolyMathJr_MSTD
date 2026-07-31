import RequestProject.SengerRelations

/-!
# Tuples versus sets, and the rank count

First, increasing tuples and `k`-subsets of `[q]` are in bijection, so
nothing is lost by computing with tuples.  Second, `rank_counting`: `r`
independent relations leave at most `q^(k-r)` tuples.  Together they give the
statement that almost every `k`-subset is a `B_h` set.
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

/-- The `k`-element subsets of `[q] = {1,…,q}`. -/
def qSubsets (q k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 q).powersetCard k

/-- Labelled representatives: strictly increasing tuples in `[q]`.  Tuples are far
more convenient to compute with; the next lemma says nothing is lost. -/
def IncreasingTuple (q : ℕ) {k : ℕ} (A : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ A i ∧ A i ≤ q) ∧ StrictMono A

noncomputable def increasingTuples (q k : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.univ.image fun A : Fin k → Fin q ↦ fun i ↦ (A i : ℕ) + 1).filter
    (IncreasingTuple q)

noncomputable def tupleSet {k : ℕ} (A : Fin k → ℕ) : Finset ℕ :=
  Finset.univ.image A

theorem mem_qSubsets_iff {q k : ℕ} {A : Finset ℕ} :
    A ∈ qSubsets q k ↔ A.card = k ∧ ∀ a ∈ A, 1 ≤ a ∧ a ≤ q := by
  simp [qSubsets, Finset.mem_powersetCard, Finset.subset_iff, Finset.mem_Icc]
  tauto

theorem card_qSubsets (q k : ℕ) : #(qSubsets q k) = Nat.choose q k := by
  unfold qSubsets
  rw [Finset.card_powersetCard]
  simp

/-- The bijection.  Worth spelling out — I did not want tuples quietly standing in
for unordered sets. -/
theorem tupleSet_bijective (q k : ℕ) :
    Set.BijOn tupleSet (↑(increasingTuples q k) : Set (Fin k → ℕ))
      (↑(qSubsets q k) : Set (Finset ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  -- 1. lands in `qSubsets`
  · intro A hA
    rw [Finset.mem_coe, mem_qSubsets_iff]
    have hAt : IncreasingTuple q A := by
      unfold increasingTuples at hA
      rw [Finset.mem_coe] at hA
      rw [Finset.mem_filter] at hA
      exact hA.2
    constructor
    · -- card = k
      rw [tupleSet]
      rw [Finset.card_image_of_injective _ hAt.2.injective]
      simp
    · -- all elements in [1, q]
      intro a ha
      rw [tupleSet, Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact hAt.1 i
  -- 2. injective
  · intro A hA B hB hAB
    rw [increasingTuples] at hA hB
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hA hB
    obtain ⟨⟨A'', _, rfl⟩, hAtA⟩ := hA
    obtain ⟨⟨B'', _, rfl⟩, hAtB⟩ := hB
    ext i
    -- Both tuples are strictly monotone with the same image, so the induced index
    -- map `f` is monotone, hence the identity.
    -- For each i, A i is in tupleSet B, so exists j with A i = B j
    have hA_inj := hAtA.2.injective
    have hB_inj := hAtB.2.injective
    simp only [tupleSet] at hAB
    have hAim : ∀ i, (fun i => (A'' i : ℕ) + 1) i ∈ Finset.univ.image (fun i => (B'' i : ℕ) + 1) := by
      intro i
      have : (fun i => (A'' i : ℕ) + 1) i ∈ Finset.univ.image (fun i => (A'' i : ℕ) + 1) := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [hAB] at this
      exact this
    have hcorresp : ∀ i, ∃ j, A'' i = B'' j := by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hAim i)
      refine ⟨j, ?_⟩
      simp at hj
      exact Fin.ext hj.symm
    -- `f i` = the index with `A'' i = B'' (f i)`.
    choose f hf using hcorresp
    have hf_mono : StrictMono f := by
      intro i j hij
      by_contra h
      push_neg at h
      have hle : f j ≤ f i := h
      have hAB' : (fun i => (A'' i : ℕ) + 1) i = (fun i => (B'' i : ℕ) + 1) (f i) := by simp [hf]
      have hAB'' : (fun i => (A'' i : ℕ) + 1) j = (fun i => (B'' i : ℕ) + 1) (f j) := by simp [hf]
      have hAiAj : (fun i => (A'' i : ℕ) + 1) i < (fun i => (A'' i : ℕ) + 1) j := hAtA.2 hij
      have hBfj_fi : (fun i => (B'' i : ℕ) + 1) (f j) ≤ (fun i => (B'' i : ℕ) + 1) (f i) := hAtB.2.monotone hle
      linarith
    have hf_ge : ∀ i : Fin k, (f i).val ≥ i.val := by
      have aux : ∀ (n : ℕ) (hn : n ≤ k) (m : ℕ) (hm : m < n), (f ⟨m, lt_of_lt_of_le hm hn⟩ : Fin k).val ≥ m := by
        intro n hn m hm
        induction n generalizing m with
        | zero => cases hm
        | succ n ih =>
          by_cases hm0 : m = 0
          · simp [hm0]
          · have hmpos : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm0
            have hm' : m - 1 < n := by omega
            have hm'lt : m - 1 < k := by omega
            have hn' : n ≤ k := Nat.le_of_succ_le hn
            have ih' := ih hn' (m - 1) hm'
            have hj : (⟨m - 1, hm'lt⟩ : Fin k) < (⟨m, lt_of_lt_of_le hm hn⟩ : Fin k) := by
              simp [Fin.lt_iff_val_lt_val]
              omega
            have hmono := hf_mono hj
            omega
      exact fun i => aux k (le_refl k) i.val i.is_lt
    have hf_id : f = id := by
      have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_mono.injective
      -- A strictly monotone self-map of `Fin k` cannot skip anything: `f i > i`
      -- would leave `i` out of the range.
      have hnot_in_range : ∀ i j, (f i).val > i.val → f j = i → False := by
        intro i j hi_gt hj
        have hfi_gt : f i > i := Fin.lt_iff_val_lt_val.mpr hi_gt
        by_cases hj_eq : j = i
        · rw [hj_eq] at hj; exact hfi_gt.ne hj.symm
        · have hji : j ≠ i := hj_eq
          by_cases hj_lt : j < i
          · -- j < i, f j = i, f i > i
            -- sum argument: `∑ (f k).val` would exceed `∑ k.val`
            have hsum_eq : ∑ k : Fin k, (f k).val = ∑ k : Fin k, k.val :=
              Equiv.sum_comp (Equiv.ofBijective f ⟨hf_mono.injective, hsurj⟩) (fun x => x.val)
            have hsum_lt : ∑ k : Fin k, (f k).val > ∑ k : Fin k, k.val := by
              apply Finset.sum_lt_sum
              · intro x _; exact hf_ge x
              · exact ⟨i, Finset.mem_univ _, hi_gt⟩
            linarith
          · -- j ≥ i, so j > i (since j ≠ i)
            push_neg at hj_lt
            have hj_gt : j > i := lt_of_le_of_ne hj_lt hji.symm
            have hmono := hf_mono hj_gt
            rw [hj] at hmono
            -- `j > i`, yet `j ≤ (f j).val = i`
            have h2 := hf_ge j
            rw [hj] at h2
            exact not_lt.mpr h2 hj_gt
      -- and `f` is surjective, so nothing may be skipped
      funext i
      by_contra hc
      have hfi_gt : (f i).val > i.val := lt_of_le_of_ne (hf_ge i) (fun heq => hc (Fin.ext heq.symm))
      obtain ⟨j, hj⟩ := hsurj i
      exact hnot_in_range i j hfi_gt hj
    -- Therefore A'' i = B'' (f i) = B'' i
    simp [hf, hf_id]
  -- 3. surjective
  · intro A hA
    rw [Finset.mem_coe, mem_qSubsets_iff] at hA
    obtain ⟨hk, hmem⟩ := hA
    -- Sort `A`: `sorted i` is its `i`-th smallest element.
    let hemb : Fin k ↪o ℕ := Finset.orderEmbOfFin A hk
    let sorted : Fin k → ℕ := fun i => hemb i
    have hsorted_mono : StrictMono sorted := by
      intro i j hij
      exact hemb.lt_iff_lt.mpr hij
    have hsorted_range : ∀ i, sorted i ∈ A := by
      intro i
      exact (Finset.orderEmbOfFin_mem A hk i)
    have hsorted_bound : ∀ i, 1 ≤ sorted i ∧ sorted i ≤ q := by
      intro i
      exact hmem _ (hsorted_range i)
    have hsorted_mem : sorted ∈ increasingTuples q k := by
      unfold increasingTuples
      rw [Finset.mem_filter]
      constructor
      · -- `sorted` is in the image
        rw [Finset.mem_image]
        refine ⟨fun i => ⟨sorted i - 1, by have := hsorted_bound i; omega⟩, ?_, ?_⟩
        · simp
        · funext i
          simp only
          have h := hsorted_bound i
          omega
      · -- and it is increasing
        exact ⟨hsorted_bound, hsorted_mono⟩
    use sorted
    constructor
    · exact hsorted_mem
    · -- tupleSet sorted = A
      rw [tupleSet]
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.image_subset_iff.mpr (fun x _ => hsorted_range x)
      · rw [Finset.card_image_of_injective _ hsorted_mono.injective]
        simp [hk]

theorem card_increasingTuples (q k : ℕ) :
    #(increasingTuples q k) = Nat.choose q k := by
  rw [← card_qSubsets q k]
  let bij := tupleSet_bijective q k
  have hmaps := bij.1
  have hsurj := bij.2.2
  let e : increasingTuples q k ≃ qSubsets q k := {
    toFun := fun x => ⟨tupleSet x.val, hmaps x.prop⟩
    invFun := fun x => by
      have hx : (x : Finset ℕ) ∈ (qSubsets q k : Set (Finset ℕ)) := x.2
      have hmem : (x : Finset ℕ) ∈ tupleSet '' ((increasingTuples q k) : Set (Fin k → ℕ)) := hsurj hx
      exact ⟨hmem.choose, hmem.choose_spec.1⟩
    left_inv := fun x => by
      have hmem : tupleSet ↑x ∈ tupleSet '' ((increasingTuples q k) : Set (Fin k → ℕ)) :=
        hsurj (hmaps x.2)
      rw [Set.mem_image] at hmem
      have hspec := hmem.choose_spec
      have hinj := bij.2.1
      have heq : hmem.choose = ↑x := hinj hmem.choose_spec.1 x.2 hspec.2
      simp [heq]
    right_inv := fun x => by
      have hmem : (x : Finset ℕ) ∈ tupleSet '' ((increasingTuples q k) : Set (Fin k → ℕ)) := hsurj x.2
      rw [Set.mem_image] at hmem
      have hspec := hmem.choose_spec
      simp [hspec.2]
  }
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr e

/-- Reordering a labeled tuple does not change its `h`-fold sumset. -/
theorem hSumset_invariant_under_reordering {k : ℕ} (h : ℕ)
    (A : Fin k → ℤ) (σ : Equiv.Perm (Fin k)) :
    hSumset h (A ∘ σ) = hSumset h A := by
  simp only [hSumset, eval]
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x ∘ σ.symm, ?_, ?_⟩
    · rw [X] at hx ⊢
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [Fintype.mem_piFinset] at hx1 ⊢; exact fun i => hx1 (σ.symm i)
      · simp only [Function.comp_apply]
        rw [← hx2, Equiv.sum_comp σ.symm]
    · simp only [eval]
      conv_rhs => rw [← Equiv.sum_comp σ.symm]
      simp [Function.comp]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x ∘ σ, ?_, ?_⟩
    · rw [X] at hx ⊢
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [Fintype.mem_piFinset] at hx1 ⊢; exact fun i => hx1 (σ i)
      · simp only [Function.comp_apply]
        rw [← hx2, Equiv.sum_comp σ]
    · simp only [eval, Function.comp]
      show ∑ i, (x (σ i) : ℤ) * A (σ i) = ∑ i, (x i : ℤ) * A i
      rw [Equiv.sum_comp σ (fun j => (x j : ℤ) * A j)]

/-- All labeled vectors in `[q]^k`. -/
noncomputable def qVectors (q k : ℕ) : Finset (Fin k → ℤ) :=
  Finset.univ.image fun A : Fin k → Fin q ↦ fun i ↦ (A i : ℤ) + 1

/-- Simultaneous homogeneous solutions to a family of integral equations. -/
noncomputable def relationSolutions {r k : ℕ} (q : ℕ) (D : Fin r → Fin k → ℤ) :
    Finset (Fin k → ℤ) :=
  (qVectors q k).filter fun A ↦ ∀ j, Satisfies A (D j)

/-- The rank-counting lemma: `r` independent relations cut the count down to
`q^(k-r)`.  Independence is taken over `ℚ`, after embedding the integer vectors. -/
theorem rank_counting {r k q : ℕ} (D : Fin r → Fin k → ℤ)
    (hrk : r ≤ k)
    (hli : LinearIndependent ℚ (fun j i ↦ (D j i : ℚ))) :
    #(relationSolutions q D) ≤ q ^ (k - r) := by
  -- Induction on `r`.
  induction r generalizing k with
  | zero =>
    -- `r = 0`: every vector is a solution.
    simp [relationSolutions]
    unfold qVectors
    rw [Finset.card_image_of_injective]
    · simp
    · intro A B h
      funext i
      have := congrFun h i
      have h' : (A i : ℤ) = (B i : ℤ) := by linarith
      exact Fin.ext (Int.ofNat.inj h')
  | succ r' ih =>
    have hD0_ne : D 0 ≠ 0 := by
      have := hli.ne_zero ⟨0, Nat.succ_pos r'⟩
      intro hD0_eq
      apply this
      ext i
      simp [hD0_eq]
    -- Independence gives some `j` with `D 0 j ≠ 0`.  Solve the first equation for
    -- coordinate `j` and eliminate it.
    have hD0_ne' : (fun i => (D 0 i : ℚ)) ≠ 0 := by
      intro h
      apply hD0_ne
      exact funext (fun i => by simpa using congrFun h i)
    obtain ⟨j, hj⟩ : ∃ j, (D 0 j : ℚ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hD0_ne' (funext h)
    have hj' : D 0 j ≠ 0 := by
      intro heq
      simp [heq] at hj
    have hrk' : r' ≤ k - 1 := by omega
    -- `enc` enumerates the coordinates other than `j`.
    rcases k with _ | k
    · exact absurd hrk (Nat.not_succ_le_zero _)
    · simp
      -- `D'` is what is left after the elimination: the usual
      -- `D(i+1)(p) * D 0 j - D(i+1) j * D 0 (p)` combination.
      let enc : Fin k → Fin (k + 1) := fun i =>
        if i.val < j.val then Fin.castLT i (by omega) else Fin.succAbove j i
      have enc_surj : ∀ i : Fin (k + 1), i ≠ j → ∃ i' : Fin k, enc i' = i := by
        intro i hi
        by_cases h : (i : ℕ) < (j : ℕ)
        · use ⟨i.val, by omega⟩
          simp [enc, h]
        · push_neg at h
          have hi_gt : (j : ℕ) < (i : ℕ) := Nat.lt_of_le_of_ne h (by intro h_eq; exact hi (Fin.ext h_eq.symm))
          use ⟨i.val - 1, by omega⟩
          simp [enc]
          have h1 : ¬((⟨i.val - 1, by omega⟩ : Fin k).castSucc : Fin (k + 1)) < j := by
            rw [Fin.lt_iff_val_lt_val]; simp; omega
          split_ifs with h2
          · exfalso; omega
          · -- Need to show j.succAbove ⟨i.val - 1, _⟩ = i
            apply Fin.ext
            simp [Fin.succAbove]
            split_ifs with h3
            · exfalso; exact h1 h3
            · have hi_ge : (i : ℕ) ≥ 1 := by omega
              exact Nat.sub_add_cancel hi_ge
      -- enc is injective (same as in rank_counting_one)
      have enc_inj : Function.Injective enc := by
        intro i i' heq
        simp only [enc] at heq
        by_cases hi : (i : ℕ) < (j : ℕ) <;> by_cases hi' : (i' : ℕ) < (j : ℕ)
        · simp only [hi, hi', ↓reduceIte] at heq
          exact Fin.ext (by simpa using congrArg Fin.val heq)
        · simp only [hi, hi', ↓reduceIte] at heq
          exfalso
          have h_valid : (i : ℕ) < k + 1 := Nat.lt_succ_of_lt i.is_lt
          have h_lt : (i.castLT h_valid : ℕ) < j := hi
          have h_ge : (j.succAbove i' : ℕ) ≥ j := by
            rw [Fin.succAbove]
            by_cases h : i'.castSucc < j
            · exfalso; exact hi' (by simpa [Fin.castSucc] using h)
            · simp [h]; omega
          have h_eq := congrArg Fin.val heq
          simp only [Fin.val_castLT] at h_eq
          omega
        · simp only [hi, hi', ↓reduceIte] at heq
          exfalso
          have h_valid : (i' : ℕ) < k + 1 := Nat.lt_succ_of_lt i'.is_lt
          have h_ge : (j.succAbove i : ℕ) ≥ j := by
            rw [Fin.succAbove]
            by_cases h : i.castSucc < j
            · exfalso; exact hi (by simpa [Fin.castSucc] using h)
            · simp [h]; omega
          have h_lt : (i'.castLT h_valid : ℕ) < j := hi'
          have h_eq := congrArg Fin.val heq
          simp only [Fin.val_castLT] at h_eq
          omega
        · simp only [hi, hi', ↓reduceIte] at heq
          exact Fin.ext (by
            have heq' := congrArg Fin.val heq
            simp only [Fin.succAbove] at heq'
            split_ifs at heq' <;> simp_all)
      let f : (Fin (k + 1) → ℤ) → (Fin k → ℤ) := fun A i => A (enc i)
      have hbounded : ∀ A ∈ qVectors q (k + 1), ∀ i, 1 ≤ A i ∧ A i ≤ q := by
        intro A hA
        rw [qVectors] at hA
        rw [Finset.mem_image] at hA
        obtain ⟨A', _, rfl⟩ := hA
        intro i
        constructor <;> simp <;> omega
      let D' : Fin r' → Fin k → ℤ := fun i p =>
        D (i.succ) (enc p) * D 0 j - D (i.succ) j * D 0 (enc p)
      -- Show D' is linearly independent over ℚ
      have hli' : LinearIndependent ℚ (fun i p => (D' i p : ℚ)) := by
        refine Fintype.linearIndependent_iff.mpr ?_
        intro g hg i₀
        have hg' : ∀ p : Fin k, ∑ i : Fin r', g i * (D' i p : ℚ) = 0 := by
          intro p
          have := congrFun hg p
          simp only [Finset.sum_apply, Pi.zero_apply] at this
          exact this
        let S : Fin (k + 1) → ℚ := fun q => ∑ i : Fin r', g i * (D (i.succ) q : ℚ)
        have heq : ∀ p : Fin k, S (enc p) * (D 0 j : ℚ) = S j * (D 0 (enc p) : ℚ) := by
          intro p
          have := hg' p
          simp only [D'] at this
          push_cast at this
          simp only [mul_sub, Finset.sum_sub_distrib] at this
          have h1 : ∑ x : Fin r', g x * ((D (x.succ) (enc p) : ℚ) * (D 0 j : ℚ)) =
                    (∑ x : Fin r', g x * (D (x.succ) (enc p) : ℚ)) * (D 0 j : ℚ) := by
            rw [Finset.sum_mul]; congr; ext x; ring
          have h2 : ∑ x : Fin r', g x * ((D (x.succ) j : ℚ) * (D 0 (enc p) : ℚ)) =
                    (∑ x : Fin r', g x * (D (x.succ) j : ℚ)) * (D 0 (enc p) : ℚ) := by
            rw [Finset.sum_mul]; congr; ext x; ring
          rw [h1, h2] at this
          linarith
        -- The relation forces `S = c * D 0`, and independence of `D` then kills
        -- every coefficient.
        let c : ℚ := S j / (D 0 j : ℚ)
        have hS_eq : ∀ q : Fin (k + 1), S q = c * (D 0 q : ℚ) := by
          intro q
          by_cases hq : q = j
          · rw [hq]; simp only [c]; field_simp [hj']
          · obtain ⟨p, hp⟩ := enc_surj q hq
            have := heq p
            simp only [hp] at this ⊢
            calc S q = (S q * (D 0 j : ℚ)) / (D 0 j : ℚ) := by field_simp [hj']
              _ = (S j * (D 0 q : ℚ)) / (D 0 j : ℚ) := by rw [this]
              _ = (S j / (D 0 j : ℚ)) * (D 0 q : ℚ) := by ring
              _ = c * (D 0 q : ℚ) := rfl
        let coeffs : Fin (r' + 1) → ℚ := fun i =>
          match i with
          | ⟨0, _⟩ => -c
          | ⟨n + 1, _⟩ => g ⟨n, by omega⟩
        have hsum : ∑ i : Fin (r' + 1), coeffs i • (fun p => (D i p : ℚ)) = 0 := by
          ext q
          simp only [Finset.sum_apply, Pi.zero_apply]
          -- Split off the i = 0 term
          rw [Fin.sum_univ_succ]
          simp only [coeffs]
          have key : (-c) * (D 0 q : ℚ) + ∑ i : Fin r', g i * (D (i.succ) q : ℚ) = 0 := by
            have := hS_eq q
            linarith
          convert key using 2
        -- Apply linear independence of D to get g i₀ = 0
        have := (Fintype.linearIndependent_iff.mp hli) coeffs hsum i₀.succ
        simp [coeffs] at this
        exact this
      -- Apply the induction hypothesis to `D'`.
      have hbound := ih D' hrk' hli'
      -- Restriction sends solutions of `D` to solutions of `D'`, and is injective
      -- because `D 0` recovers the coordinate we dropped.
      have enc_ne_j : ∀ p : Fin k, enc p ≠ j := by
        intro p hp
        simp only [enc] at hp
        split_ifs at hp with hlt
        · have := congrArg Fin.val hp; simp at this; omega
        · rw [Fin.succAbove] at hp
          split_ifs at hp with hlt2
          · have : (p.castSucc : Fin (k + 1)) < j := hlt2
            rw [hp] at this
            exact lt_irrefl _ this
          · have := congrArg Fin.val hp; simp at this; omega
      have himage : Finset.univ.image enc = Finset.univ.erase j := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨p, _, rfl⟩ := hx
          simp [enc_ne_j p]
        · simp [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_image_of_injective _ enc_inj]
      have hinj_on : Set.InjOn enc (Finset.univ : Finset (Fin k)) := by
        intro x _ y _ hxy; exact enc_inj hxy
      have hFA_in_qVec : ∀ A ∈ qVectors q (k + 1), f A ∈ qVectors q k := by
        intro A hA
        rw [qVectors] at hA ⊢
        rw [Finset.mem_image] at hA ⊢
        obtain ⟨A', _, rfl⟩ := hA
        use fun p => A' (enc p)
        constructor
        · exact Finset.mem_univ _
        · ext p
          rfl
      have hmaps : ∀ A ∈ relationSolutions q D, f A ∈ relationSolutions q D' := by
        intro A hA
        simp only [relationSolutions] at hA ⊢
        simp only [Finset.mem_filter] at hA ⊢
        constructor
        · exact hFA_in_qVec A hA.1
        · intro i
          simp only [Satisfies] at hA ⊢
          simp only [f] at ⊢
          have hD_isucc : ∑ q, D (i.succ) q * A q = 0 := hA.2 (i.succ)
          have hD0 : ∑ q, D 0 q * A q = 0 := hA.2 0
          have hsum_eq : ∑ p : Fin k, D (i.succ) (enc p) * A (enc p) =
                         ∑ q : Fin (k + 1), D (i.succ) q * A q - D (i.succ) j * A j := by
            have h1 : ∑ p : Fin k, D (i.succ) (enc p) * A (enc p) =
                      ∑ q ∈ Finset.univ.image enc, D (i.succ) q * A q := by
              rw [Finset.sum_image hinj_on]
            rw [h1, himage]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
            ring
          have hsum_eq' : ∑ p : Fin k, D 0 (enc p) * A (enc p) =
                           ∑ q : Fin (k + 1), D 0 q * A q - D 0 j * A j := by
            have h1 : ∑ p : Fin k, D 0 (enc p) * A (enc p) =
                      ∑ q ∈ Finset.univ.image enc, D 0 q * A q := by
              rw [Finset.sum_image hinj_on]
            rw [h1, himage]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
            ring
          rw [show (∑ x, D' i x * A (enc x)) =
              ∑ x, (D (i.succ) (enc x) * D 0 j - D (i.succ) j * D 0 (enc x)) * A (enc x) from rfl]
          simp only [sub_mul]
          rw [Finset.sum_sub_distrib]
          have eq1 : ∑ x : Fin k, D (i.succ) (enc x) * D 0 j * A (enc x) =
                     D 0 j * ∑ x : Fin k, D (i.succ) (enc x) * A (enc x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
          have eq2 : ∑ x : Fin k, D (i.succ) j * D 0 (enc x) * A (enc x) =
                     D (i.succ) j * ∑ x : Fin k, D 0 (enc x) * A (enc x) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
          rw [eq1, eq2, hsum_eq, hsum_eq']
          rw [hD_isucc, hD0]
          ring
      have hfinj : ∀ A B : Fin (k + 1) → ℤ, A ∈ relationSolutions q D → B ∈ relationSolutions q D →
        f A = f B → A = B := by
        intro A B hA hB hAB
        simp only [relationSolutions, Finset.mem_filter] at hA hB
        ext q
        by_cases hq : q = j
        · rw [hq]
          have hAd0 : ∑ i, D 0 i * A i = 0 := hA.2 0
          have hBd0 : ∑ i, D 0 i * B i = 0 := hB.2 0
          -- Split sums at j
          have hsplit_A : ∑ i, D 0 i * A i = D 0 j * A j + ∑ i ∈ Finset.univ.erase j, D 0 i * A i := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have hsplit_B : ∑ i, D 0 i * B i = D 0 j * B j + ∑ i ∈ Finset.univ.erase j, D 0 i * B i := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          rw [hsplit_A] at hAd0; rw [hsplit_B] at hBd0
          have hago : ∑ i ∈ Finset.univ.erase j, D 0 i * A i = ∑ i ∈ Finset.univ.erase j, D 0 i * B i := by
            apply Finset.sum_congr rfl
            intro i hi_mem
            have hi_ne : i ≠ j := Finset.ne_of_mem_erase hi_mem
            have hAiBi : A i = B i := by
              obtain ⟨i', hi'⟩ := enc_surj i hi_ne
              have : f A i' = f B i' := congrFun hAB i'
              simp only [f] at this
              rw [hi'] at this
              exact this
            rw [hAiBi]
          exact mul_left_cancel₀ hj' (by linarith : D 0 j * A j = D 0 j * B j)
        · obtain ⟨q', hq'⟩ := enc_surj q hq
          have : f A q' = f B q' := congrFun hAB q'
          simp only [f] at this
          rw [hq'] at this
          exact this
      -- Use injectivity to bound cardinality
      have hcard : #(relationSolutions q D) ≤ #(relationSolutions q D') := by
        apply Finset.card_le_card_of_injOn
        · exact hmaps
        · intro A hA B hB hAB
          exact hfinj A B hA hB hAB
      calc #(relationSolutions q D) ≤ #(relationSolutions q D') := hcard
        _ ≤ q ^ (k - r') := hbound

theorem rank_counting_one {k q : ℕ} (d : Fin k → ℤ) (hd : d ≠ 0) :
    #((qVectors q k).filter fun A ↦ Satisfies A d) ≤ q ^ (k - 1) := by
  -- Pick `j` with `d j ≠ 0` and eliminate that coordinate.
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  rcases k with _ | k
  · exfalso
    exact hd (funext (fun i => i.elim0))
  · -- k = k' + 1, so k - 1 = k'
    simp only [Nat.add_sub_cancel]
    let enc : Fin k → Fin (k + 1) := fun i =>
      if i.val < j.val then Fin.castLT i (by omega) else Fin.succAbove j i
    let f : (Fin (k + 1) → ℤ) → (Fin k → ℤ) := fun A i => A (enc i)
    -- The surviving values still lie in `[1,q]`.
    have hbounded : ∀ A ∈ qVectors q (k + 1), ∀ i, 1 ≤ A i ∧ A i ≤ q := by
      intro A hA
      rw [qVectors] at hA
      rw [Finset.mem_image] at hA
      obtain ⟨A', _, rfl⟩ := hA
      intro i
      constructor <;> simp <;> omega
    -- enc is injective
    have enc_inj : Function.Injective enc := by
      intro i i' heq
      simp only [enc] at heq
      by_cases hi : (i : ℕ) < (j : ℕ) <;> by_cases hi' : (i' : ℕ) < (j : ℕ)
      · -- both < j: castLT is injective
        simp only [hi, hi', ↓reduceIte] at heq
        exact Fin.ext (by simpa using congrArg Fin.val heq)
      · -- i < j, i' ≥ j: impossible
        simp only [hi, hi', ↓reduceIte] at heq
        exfalso
        have h_valid : (i : ℕ) < k + 1 := Nat.lt_succ_of_lt i.is_lt
        have h_lt : (i.castLT h_valid : ℕ) < j := hi
        have h_ge : (j.succAbove i' : ℕ) ≥ j := by
          rw [Fin.succAbove]
          by_cases h : i'.castSucc < j
          · exfalso; exact hi' (by simpa [Fin.castSucc] using h)
          · simp [h]; omega
        have h_eq := congrArg Fin.val heq
        simp only [Fin.val_castLT] at h_eq
        omega
      · -- i ≥ j, i' < j: impossible
        simp only [hi, hi', ↓reduceIte] at heq
        exfalso
        have h_valid : (i' : ℕ) < k + 1 := Nat.lt_succ_of_lt i'.is_lt
        have h_ge : (j.succAbove i : ℕ) ≥ j := by
          rw [Fin.succAbove]
          by_cases h : i.castSucc < j
          · exfalso; exact hi (by simpa [Fin.castSucc] using h)
          · simp [h]; omega
        have h_lt : (i'.castLT h_valid : ℕ) < j := hi'
        have h_eq := congrArg Fin.val heq
        simp only [Fin.val_castLT] at h_eq
        omega
      · -- both ≥ j: succAbove is injective
        simp only [hi, hi', ↓reduceIte] at heq
        exact Fin.ext (by
          have heq' := congrArg Fin.val heq
          simp only [Fin.succAbove] at heq'
          split_ifs at heq' <;> simp_all)
    -- enc is surjective onto Fin (k+1) \ {j}
    have enc_surj : ∀ i : Fin (k + 1), i ≠ j → ∃ i' : Fin k, enc i' = i := by
      intro i hi
      by_cases h : (i : ℕ) < (j : ℕ)
      · use ⟨i.val, by omega⟩
        simp [enc, h]
      · push_neg at h
        use ⟨i.val - 1, by omega⟩
        simp [enc]
        have hval : ((⟨i.val - 1, by omega⟩ : Fin k).castSucc : Fin (k + 1)).val = i.val - 1 := rfl
        have h1 : ¬((⟨i.val - 1, by omega⟩ : Fin k).castSucc : Fin (k + 1)) < j := by
          rw [Fin.lt_iff_val_lt_val]; simp; omega
        split_ifs with h2
        · exfalso; omega
        · congr 1
          ext
          simp [Fin.succAbove]
          have : (i : ℕ) - 1 + 1 = i := by omega
          split_ifs <;> simp_all
    -- Show injectivity of the restriction
    have hinj : ∀ A B : Fin (k + 1) → ℤ, A ∈ qVectors q (k + 1) → B ∈ qVectors q (k + 1) →
        Satisfies A d → Satisfies B d → f A = f B → A = B := by
      intro A B hA hB hAd hBd heq
      ext i
      by_cases hi : i = j
      · -- At coordinate j: use the equation
        rw [hi]
        have hAd' : ∑ i, d i * A i = 0 := hAd
        have hBd' : ∑ i, d i * B i = 0 := hBd
        -- Split the sum into j and non-j parts
        have hsplit_A : ∑ i, d i * A i = d j * A j + ∑ i ∈ Finset.univ.erase j, d i * A i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have hsplit_B : ∑ i, d i * B i = d j * B j + ∑ i ∈ Finset.univ.erase j, d i * B i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        rw [hsplit_A] at hAd'
        rw [hsplit_B] at hBd'
        have hago : ∑ i ∈ Finset.univ.erase j, d i * A i = ∑ i ∈ Finset.univ.erase j, d i * B i := by
          apply Finset.sum_congr rfl
          intro i hi_mem
          have hi_ne : i ≠ j := Finset.ne_of_mem_erase hi_mem
          have hAiBi : A i = B i := by
            obtain ⟨i', hi'⟩ := enc_surj i hi_ne
            have : A (enc i') = B (enc i') := congrFun heq i'
            rw [hi'] at this
            exact this
          rw [hAiBi]
        have h_eq : d j * A j = d j * B j := by linarith
        exact mul_left_cancel₀ hj h_eq
      · -- At other coordinates: use heq
        obtain ⟨i', hi'⟩ := enc_surj i hi
        have : A (enc i') = B (enc i') := congrFun heq i'
        rw [hi'] at this
        exact this
    let S := (qVectors q (k + 1)).filter fun A => Satisfies A d
    -- Restriction embeds `S` into `Fin k → Fin q`, which has `q^k` elements.
    let g : {A : Fin (k + 1) → ℤ // A ∈ S} → (Fin k → Fin q) := fun ⟨A, hA⟩ i =>
      ⟨(Int.toNat (A (enc i) - 1)), by
        rw [Finset.mem_filter] at hA
        have := hbounded A hA.1 (enc i)
        omega⟩
    have hginj : Function.Injective g := by
      intro ⟨A, hA⟩ ⟨B, hB⟩ hAB
      simp only [Subtype.mk.injEq]
      apply hinj A B
      · rw [Finset.mem_filter] at hA; exact hA.1
      · rw [Finset.mem_filter] at hB; exact hB.1
      · rw [Finset.mem_filter] at hA; exact hA.2
      · rw [Finset.mem_filter] at hB; exact hB.2
      · ext i
        simp [g] at hAB
        have := congrFun hAB i
        simp only [Fin.mk.injEq] at this
        have hA_enc := hbounded A (by rw [Finset.mem_filter] at hA; exact hA.1) (enc i)
        have hB_enc := hbounded B (by rw [Finset.mem_filter] at hB; exact hB.1) (enc i)
        have h1 : (A (enc i)).toNat = (B (enc i)).toNat := by omega
        have hA_pos : 0 ≤ A (enc i) := by linarith [hA_enc]
        have hB_pos : 0 ≤ B (enc i) := by linarith [hB_enc]
        have h1' : (↑(A (enc i)).toNat : ℤ) = ↑(B (enc i)).toNat := by simp [h1]
        exact (Int.toNat_of_nonneg hA_pos).symm.trans (h1'.trans (Int.toNat_of_nonneg hB_pos))
    have hcard_eq : #S = #(Finset.univ.image g : Finset (Fin k → Fin q)) := by
      rw [← Fintype.card_coe]
      exact (Finset.card_image_of_injective Finset.univ hginj).symm
    have hsubset : (Finset.univ.image g : Finset (Fin k → Fin q)) ⊆ Fintype.piFinset fun _ : Fin k => Finset.univ := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨A, _, rfl⟩ := hx
      simp
    have hcard := Finset.card_le_card hsubset
    simp [Fintype.card_pi] at hcard
    exact hcard_eq ▸ hcard

theorem rank_counting_two {k q : ℕ} (d e : Fin k → ℤ) (hk : 2 ≤ k)
    (hli : LinearIndependent ℚ ![(fun i ↦ (d i : ℚ)), (fun i ↦ (e i : ℚ))]) :
    #((qVectors q k).filter fun A ↦ Satisfies A d ∧ Satisfies A e) ≤ q ^ (k - 2) := by
  let D : Fin 2 → Fin k → ℤ := ![d, e]
  have hrk : (2 : ℕ) ≤ k := hk
  have hli' : LinearIndependent ℚ (fun j i ↦ (D j i : ℚ)) := by
    have heq : (fun j i ↦ (D j i : ℚ)) = fun j ↦ ![fun i ↦ (d i : ℚ), fun i ↦ (e i : ℚ)] j := by
      ext j i
      fin_cases j <;> simp [D]
    rw [heq]
    exact hli
  have heq : relationSolutions q D = (qVectors q k).filter fun A ↦ Satisfies A d ∧ Satisfies A e := by
    ext A
    simp only [relationSolutions]
    simp only [Finset.mem_filter]
    have hfilter : (∀ j, Satisfies A (D j)) ↔ Satisfies A d ∧ Satisfies A e := by
      constructor
      · intro h
        exact ⟨h 0, h 1⟩
      · intro ⟨h0, h1⟩ j
        fin_cases j <;> [exact h0; exact h1]
    rw [hfilter]
  rw [← heq]
  exact rank_counting D hrk hli'

/-- `B_h` subsets, expressed via their unique increasing enumeration. -/
noncomputable def bhSubsets (h q k : ℕ) : Finset (Finset ℕ) :=
  (qSubsets q k).filter fun A ↦
    ∃ v ∈ increasingTuples q k,
      tupleSet v = A ∧ IsBh h (fun i ↦ v i)

/-- Union bound over collisions: at most `C(M h k, 2)` relations, each with at most
`q^(k-1)` solutions. -/
theorem nonBh_count_bound (h q k : ℕ) (hk : 0 < k) :
    #(qSubsets q k) - #(bhSubsets h q k) ≤
      Nat.choose (M h k) 2 * q ^ (k - 1) := by
  have hsub : bhSubsets h q k ⊆ qSubsets q k := by
    intro x hx
    simp [bhSubsets] at hx
    exact hx.1
  have hcard : #(qSubsets q k \ bhSubsets h q k) = #(qSubsets q k) - #(bhSubsets h q k) := by
    rw [Finset.card_sdiff]
    congr 1
    rw [Finset.inter_comm, Finset.inter_eq_right.mpr hsub]
  rw [← hcard]
  -- Transfer the count to increasing tuples.
  have hbij := tupleSet_bijective q k
  let nonBhTuples := (increasingTuples q k).filter fun v => ¬IsBh h (fun i => v i)
  have heq : #(qSubsets q k \ bhSubsets h q k) = #(nonBhTuples) := by
    let BhTuples := (increasingTuples q k).filter fun v => IsBh h (fun i => v i)
    have hbh_eq : bhSubsets h q k = (BhTuples.image tupleSet) := by
      ext A
      simp only [bhSubsets, bhSubsets, Finset.mem_filter, Finset.mem_image]
      constructor
      · intro ⟨hA, v, hv, heq_v, hBh⟩
        use v
        simp [BhTuples, hv, hBh, heq_v]
      · intro ⟨v, hv, hBh⟩
        rw [Finset.mem_filter] at hv
        rw [← hBh]
        exact ⟨hbij.1 hv.1, v, hv.1, rfl, hv.2⟩
    have hqsub_eq : qSubsets q k = (increasingTuples q k).image tupleSet := by
      ext A
      simp only [Finset.mem_image]
      constructor
      · intro h
        obtain ⟨v, hv, hvA⟩ := hbij.2.2 h
        exact ⟨v, hv, hvA⟩
      · intro ⟨v, hv, hvA⟩
        rw [← hvA]
        exact hbij.1 hv
    have hpart : BhTuples ∪ nonBhTuples = increasingTuples q k := by
      ext v
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
      · intro hv
        by_cases h : IsBh h (fun i => (v i : ℤ)) <;> [left; right] <;> exact ⟨hv, h⟩
    have hdisj : Disjoint (BhTuples.image tupleSet) (nonBhTuples.image tupleSet) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v', hv', heq⟩ := Finset.mem_image.mp hx'
      have hv'_mem : v' ∈ increasingTuples q k := by rw [Finset.mem_filter] at hv'; exact hv'.1
      have hv_mem : v ∈ increasingTuples q k := by rw [Finset.mem_filter] at hv; exact hv.1
      have := hbij.2.1 hv_mem hv'_mem
      have heq' := heq.symm
      have hv'' := this heq'
      rw [hv''] at hv
      rw [Finset.mem_filter] at hv hv'
      exact hv'.2 hv.2
    have himage_eq : (increasingTuples q k).image tupleSet \ BhTuples.image tupleSet = nonBhTuples.image tupleSet := by
      rw [← hpart]
      rw [Finset.image_union]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hx
        rcases hx.1 with ⟨v₁, hv₁, hv₁x⟩ | ⟨v₂, hv₂, hv₂x⟩
        · exact False.elim (hx.2 ⟨v₁, hv₁, hv₁x⟩)
        · exact ⟨v₂, hv₂, hv₂x⟩
      · intro ⟨v, hv, hvx⟩
        refine ⟨Or.inr ⟨v, hv, hvx⟩, ?_⟩
        intro ⟨v', hv', hvx'⟩
        have hex : x ∈ BhTuples.image tupleSet ∩ nonBhTuples.image tupleSet := by
          rw [Finset.mem_inter]
          exact ⟨Finset.mem_image.mpr ⟨v', hv', hvx'⟩, Finset.mem_image.mpr ⟨v, hv, hvx⟩⟩
        rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
        rw [hdisj] at hex
        simp at hex
    rw [hqsub_eq, hbh_eq, himage_eq]
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    have hx' : x ∈ increasingTuples q k := by simp [nonBhTuples] at hx; exact hx.1
    have hy' : y ∈ increasingTuples q k := by simp [nonBhTuples] at hy; exact hy.1
    exact hbij.2.1 hx' hy' hxy
  rw [heq]
  -- Each non-`B_h` tuple satisfies `x - y` for some pair of multiplicity vectors.
  -- There are `C(M h k, 2)` such pairs, and each one is satisfied by at most
  -- `q^(k-1)` tuples.

  let Xhk := X h k

  have hcard_X : #(X h k) = M h k := card_X h k hk
  have hcard_pairs : #(Xhk.powersetCard 2) = (M h k).choose 2 := by
    rw [Finset.card_powersetCard, hcard_X]

  let emb : (Fin k → ℕ) → (Fin k → ℤ) := fun v i => (v i : ℤ)
  have emb_inj : Function.Injective emb := by
    intro v v' h
    funext i
    have := congr_fun h i
    simp only [emb] at this
    exact Nat.cast_injective this

  -- For a two-element `p = {a,b}`, the collision set is `{v | Satisfies v (a-b)}`.



  have h_bound : #nonBhTuples ≤ #(Xhk.powersetCard 2) * q ^ (k - 1) := by


    -- First, show nonBhTuples ⊆ ⋃ p, CollisionSet p
    let CollisionSet := fun (p : Finset (Fin k → ℕ)) => (increasingTuples q k).filter fun v =>
      ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ Satisfies (fun i => (v i : ℤ)) (fun i => (x i : ℤ) - (y i : ℤ))

    have hsub : nonBhTuples ⊆ Finset.biUnion (Xhk.powersetCard 2) CollisionSet := by
      intro v hv
      simp [nonBhTuples] at hv
      have hnotBh : ¬ IsBh h (fun i => (v i : ℤ)) := hv.2
      rw [not_isBh_iff_collision] at hnotBh
      obtain ⟨x, hx, y, hy, hne, heq⟩ := hnotBh
      have hpair : ({x, y} : Finset (Fin k → ℕ)) ∈ Xhk.powersetCard 2 := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩, by simp [hne]⟩
      refine Finset.mem_biUnion.mpr ⟨{x, y}, hpair, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨hv.1, ?_⟩
      refine ⟨x, Finset.mem_insert_self _ _, y, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hne, ?_⟩
      simp [Satisfies]
      have h : ∑ i, ((x i : ℤ) - (y i : ℤ)) * (v i : ℤ) =
               ∑ i, (x i : ℤ) * (v i : ℤ) - ∑ i, (y i : ℤ) * (v i : ℤ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp [eval] at heq
      rw [h, heq, sub_self]
    -- Union bound.
    let toZ : (Fin k → ℕ) → (Fin k → ℤ) := fun v i => (v i : ℤ)
    have toZ_inj : Function.Injective toZ := fun v v' h => funext fun i =>
      Nat.cast_injective (congr_fun h i)
    -- Bound each CollisionSet
    have h_bound_each : ∀ p ∈ Xhk.powersetCard 2, #(CollisionSet p) ≤ q ^ (k - 1) := by
      intro p hp
      have hp2 : 1 < #p := by rw [Finset.mem_powersetCard] at hp; omega
      obtain ⟨x₀, hx₀, y₀, hy₀, hne⟩ := Finset.one_lt_card.mp hp2
      have hp_card : #p = 2 := by rw [Finset.mem_powersetCard] at hp; exact hp.2
      let a := x₀
      let b := y₀
      have hab : a ≠ b := hne
      have hsub : CollisionSet p ⊆ (increasingTuples q k).filter fun v =>
        Satisfies (fun i => (v i : ℤ)) (fun i => (a i : ℤ) - (b i : ℤ)) := by
        intro v hv
        rw [Finset.mem_filter] at hv ⊢
        obtain ⟨x, hx, y, hy, hne', heq⟩ := hv.2
        refine ⟨hv.1, ?_⟩
        have hxy_eq_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
          have hp_eq : p = {a, b} := by
            have := Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hx₀, Finset.singleton_subset_iff.mpr hy₀⟩)
            rw [Finset.card_pair hab, hp_card] at this
            have h1 : ({x₀, y₀} : Finset (Fin k → ℕ)) = {a, b} := by rfl
            exact h1 ▸ Eq.symm (this (le_refl 2))
          have hx_mem : x ∈ ({a, b} : Finset (Fin k → ℕ)) := hp_eq ▸ hx
          have hy_mem : y ∈ ({a, b} : Finset (Fin k → ℕ)) := hp_eq ▸ hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem hy_mem
          rcases hx_mem with rfl | rfl <;> rcases hy_mem with rfl | rfl
          <;> simp_all [a, b]
        rcases hxy_eq_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact heq
        · rw [Satisfies] at heq ⊢
          have : ∑ i, ((a i : ℤ) - (b i : ℤ)) * (v i : ℤ) =
                 -∑ i, ((x i : ℤ) - (y i : ℤ)) * (v i : ℤ) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun _ _ => by ring
          rw [this, heq, neg_zero]
      -- a - b ≠ 0 since a ≠ b
      have hne_d : (fun i => (a i : ℤ) - (b i : ℤ)) ≠ 0 := by
        intro h
        have : a = b := by
          funext i
          have := congr_fun h i
          simp only [Pi.zero_apply] at this
          omega
        exact hab this
      let emb : (Fin k → ℕ) → (Fin k → ℤ) := fun v i => (v i : ℤ)
      have emb_inj : Function.Injective emb := fun v v' h => by
        funext i; exact Nat.cast_injective (congr_fun h i)
      have hsub2 : (CollisionSet p).image emb ⊆ (qVectors q k).filter fun A => Satisfies A (fun i => (a i : ℤ) - (b i : ℤ)) := by
        intro A hA
        rw [Finset.mem_image] at hA
        obtain ⟨v, hv, rfl⟩ := hA
        rw [Finset.mem_filter]
        have := hsub hv
        rw [Finset.mem_filter] at this
        refine ⟨?_, this.2⟩
        rw [qVectors]
        have hv_mem : v ∈ increasingTuples q k := this.1
        rw [increasingTuples] at hv_mem
        simp only [Finset.mem_filter, Finset.mem_image] at hv_mem
        obtain ⟨A', _, rfl⟩ := hv_mem.1
        simp [emb]
      have hcard_eq : #(CollisionSet p) = #((CollisionSet p).image emb) := by
        rw [Finset.card_image_of_injective _ emb_inj]
      rw [hcard_eq]
      exact le_trans (Finset.card_le_card hsub2) (rank_counting_one _ hne_d)
    calc #nonBhTuples ≤ #(Finset.biUnion (Xhk.powersetCard 2) CollisionSet) := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ Xhk.powersetCard 2, #(CollisionSet p) := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ Xhk.powersetCard 2, q ^ (k - 1) := Finset.sum_le_sum h_bound_each
      _ = #(Xhk.powersetCard 2) * q ^ (k - 1) := by simp
  rw [hcard_pairs] at h_bound
  exact h_bound

/-- The proportion of `B_h` `k`-subsets tends to one (with `h,k` fixed). -/
theorem bh_proportion_tendsto_one (h k : ℕ) (hk : 0 < k) :
    Tendsto (fun q : ℕ ↦
      (#(bhSubsets h q k) : ℝ) / #(qSubsets q k)) atTop (nhds 1) := by
  set C := Nat.choose (M h k) 2
  have h_bound : ∀ q : ℕ, #(qSubsets q k) - #(bhSubsets h q k) ≤ C * q ^ (k - 1) := by
    intro q
    exact nonBh_count_bound h q k hk
  have h_qsub : ∀ q : ℕ, #(qSubsets q k) = Nat.choose q k := by
    intro q
    exact card_qSubsets q k
  have h_pos : ∀ q, k ≤ q → 0 < Nat.choose q k := fun q hq ↦ Nat.choose_pos hq
  have h_nonBh_le : ∀ q, #(bhSubsets h q k) ≤ #(qSubsets q k) :=
    fun q => Finset.card_le_card (Finset.filter_subset _ _)
  -- `bh/total = 1 - nonBh/total`, with `nonBh ≤ C q^(k-1)` and `total = C(q,k)`,
  -- so the error term is `O(1/q)`.
  have h_nonBh_bound : ∀ q : ℕ, #(qSubsets q k) - #(bhSubsets h q k) ≤ C * q ^ (k - 1) := h_bound
  rw [Metric.tendsto_atTop]
  intro ε hε

  have h_dist_eq : ∀ n, k ≤ n → dist ((#(bhSubsets h n k) : ℝ) / #(qSubsets n k)) 1 =
      (#(qSubsets n k) - #(bhSubsets h n k) : ℝ) / #(qSubsets n k) := by
    intro n hn
    have hpos : 0 < Nat.choose n k := h_pos n hn
    have h_ne : (Nat.choose n k : ℝ) ≠ 0 := by positivity
    have h_le : #(bhSubsets h n k) ≤ #(qSubsets n k) := h_nonBh_le n
    rw [h_qsub n] at h_le ⊢
    rw [dist_eq_norm, Real.norm_eq_abs]
    have h_cast_le : (#(bhSubsets h n k) : ℝ) ≤ (Nat.choose n k : ℝ) := Nat.cast_le.mpr h_le
    have h_nonpos' : ((#(bhSubsets h n k) : ℝ) / (Nat.choose n k : ℝ)) - 1 ≤ 0 := by
      have := div_le_one_of_le₀ h_cast_le (by positivity : (0 : ℝ) ≤ Nat.choose n k)
      linarith
    rw [abs_of_nonpos h_nonpos']
    field_simp [h_ne]
    ring

  let A := C * k.factorial * 2^k

  -- Choose `N` by Archimedes.
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, n ≥ N1 → (A : ℝ) / n < ε := by
    rcases exists_nat_gt (A / ε) with ⟨N1, hN1⟩
    use N1 + 1
    intro n hn
    have hn_cast : (n : ℝ) ≥ N1 + 1 := by norm_cast
    have hn_pos : (0 : ℝ) < n := by linarith
    rw [div_lt_iff₀ hn_pos]
    have hA_lt : (A : ℝ) < N1 * ε := by
      have := (div_lt_iff₀ hε).mp hN1
      linarith
    nlinarith

  use max k (max (2 * k) (N1 + 1))
  intro n hn
  have hn_k : k ≤ n := hn.trans' (le_max_left _ _)
  have hn_2k : 2 * k ≤ n := hn.trans' (le_max_of_le_right (le_max_left _ _))
  have hn_N1 : n ≥ N1 + 1 := hn.trans' (le_max_of_le_right (le_max_right _ _))
  rw [h_dist_eq n hn_k]

  -- The binomial lower bound: `C(n,k) ≥ n^k / (k! * 2^k)` once `n ≥ 2k`.
  have h_choose_bound : (Nat.choose n k : ℝ) ≥ (n : ℝ) ^ k / (k.factorial * 2 ^ k) := by
    have h_ineq : 2 ^ k * Nat.descFactorial n k ≥ n ^ k := by
      -- each factor `2(n-i)` is at least `n` when `n ≥ 2k`
      have hprod : 2 ^ k * Nat.descFactorial n k = ∏ i ∈ Finset.range k, 2 * (n - i) := by
        rw [Nat.descFactorial_eq_prod_range]
        rw [mul_comm, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_range]
        ring
      rw [hprod]
      have hfactor : ∀ i ∈ Finset.range k, n ≤ 2 * (n - i) := by
        intro i hi
        simp at hi
        omega
      have h1 : ∏ i ∈ Finset.range k, n = n ^ k := by simp
      exact le_trans h1.ge (Finset.prod_le_prod' hfactor)
    have hdesc : Nat.descFactorial n k = k.factorial * Nat.choose n k :=
      Nat.descFactorial_eq_factorial_mul_choose n k
    have h_rhs_pos : (0 : ℝ) < k.factorial * 2 ^ k := by positivity
    rw [ge_iff_le, div_le_iff₀ h_rhs_pos]
    calc (n : ℝ) ^ k = ((n ^ k : ℕ) : ℝ) := by simp
      _ ≤ 2 ^ k * Nat.descFactorial n k := by exact_mod_cast h_ineq
      _ = 2 ^ k * (k.factorial * Nat.choose n k) := by rw [hdesc]; norm_cast
      _ = k.factorial * 2 ^ k * Nat.choose n k := by ring
      _ = Nat.choose n k * (k.factorial * 2 ^ k) := by ring

  have h_num_le : (#(qSubsets n k) - #(bhSubsets h n k) : ℕ) ≤ C * n ^ (k - 1) := h_nonBh_bound n
  rw [h_qsub n]
  have h_cast_num : ((Nat.choose n k : ℕ) - #(bhSubsets h n k) : ℝ) ≤ (C : ℝ) * n ^ (k - 1) := by
    have h_le : #(bhSubsets h n k) ≤ Nat.choose n k := by
      calc #(bhSubsets h n k) ≤ #(qSubsets n k) := h_nonBh_le n
        _ = Nat.choose n k := h_qsub n
    have h_num_le' : (Nat.choose n k - #(bhSubsets h n k) : ℕ) ≤ C * n ^ (k - 1) := by
      rw [h_qsub n] at h_num_le
      exact h_num_le
    have h : ((Nat.choose n k - #(bhSubsets h n k) : ℕ) : ℝ) ≤ ((C * n ^ (k - 1)) : ℝ) := by
      exact_mod_cast h_num_le'
    simp only [Nat.cast_sub h_le] at h
    exact h
  have h_denom_pos : (0 : ℝ) < Nat.choose n k := by norm_cast; exact h_pos n hn_k


  have h_ratio_le : ((Nat.choose n k : ℝ) - #(bhSubsets h n k)) / Nat.choose n k ≤
      (C : ℝ) * n ^ (k - 1) / Nat.choose n k := by
    gcongr

  have h_choose_pos : (0 : ℝ) < Nat.choose n k := h_denom_pos
  have h_choose_bound' : (Nat.choose n k : ℝ) ≥ (n : ℝ) ^ k / ((k.factorial : ℝ) * 2 ^ k) := h_choose_bound
  have h_denom_bound : (k.factorial : ℝ) * 2 ^ k > 0 := by positivity

  have h_frac_le : (C : ℝ) * n ^ (k - 1) / Nat.choose n k ≤ (A : ℝ) / n := by
    rw [ge_iff_le, div_le_iff₀ h_denom_bound] at h_choose_bound'
    have hA_eq : (A : ℝ) = C * k.factorial * 2 ^ k := by simp [A]
    have hn_pos : (0 : ℝ) < n := by norm_cast; omega
    rw [div_le_div_iff₀ h_denom_pos hn_pos]
    have hpow : (n : ℝ) * n ^ (k - 1) = n ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    calc (C : ℝ) * n ^ (k - 1) * n = C * (n * n ^ (k - 1)) := by ring
      _ = C * n ^ k := by rw [hpow]
      _ ≤ C * (Nat.choose n k * (k.factorial * 2 ^ k)) := by gcongr
      _ = (A : ℝ) * Nat.choose n k := by rw [hA_eq]; ring

  -- Combine: the ratio is at most `A/n`, which is `< ε`.
  calc ((Nat.choose n k : ℝ) - #(bhSubsets h n k)) / Nat.choose n k
      ≤ (A : ℝ) / n := le_trans h_ratio_le h_frac_le
    _ < ε := hN1 n (by omega)
end
end Senger
