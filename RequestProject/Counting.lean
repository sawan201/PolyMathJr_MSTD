module

public import RequestProject.Prelim

/-!
# Counting lemmas

* `Sumsets.card_tuples_dot_eq_zero_le`, `Sumsets.card_tuples_two_dot_eq_zero_le`:
  the cases `r = 1, 2` of the rank lemma (Lemma `lem:rank-lemma`) in `[q]^k`.
* Transfer between `k`-subsets of `[q]` and injective tuples in `[q]^k`.
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset
open scoped Nat

variable {h k : ℕ}

/-- Tuples in `[q]^k`. -/
def tuples (q k : ℕ) : Finset (Fin k → ℤ) := Fintype.piFinset fun _ : Fin k => Finset.Icc (1 : ℤ) q

theorem card_Icc_one (q : ℕ) : (Finset.Icc (1 : ℤ) q).card = q := by
  rw [Int.card_Icc]; omega

/-- Rank lemma (`r = 1`) in `[q]^k`. -/
theorem card_tuples_dot_eq_zero_le (q : ℕ) (c : Fin k → ℤ) (hc : c ≠ 0) :
    ((tuples q k).filter (fun p => dot c p = 0)).card ≤ q ^ (k - 1) := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact hc (funext hcon)
  refine (card_filter_dot_eq_zero_le c i hi _).trans (le_of_eq ?_)
  rw [Finset.prod_const, card_Icc_one, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
    Fintype.card_fin]

/-- Rank lemma (`r = 2`) in `[q]^k` for two distinct coefficient vectors. -/
theorem card_tuples_two_dot_eq_zero_le (q : ℕ) {d e : Fin k → ℤ} (hd : d ∈ coeffVectors h k)
    (he : e ∈ coeffVectors h k) (hde : d ≠ e) :
    ((tuples q k).filter (fun p => dot d p = 0 ∧ dot e p = 0)).card ≤ q ^ (k - 2) := by
  obtain ⟨i, j, hij, hdet⟩ := exists_minor_ne_zero hd he hde
  refine (card_filter_two_dot_eq_zero_le d e i j hij hdet _).trans (le_of_eq ?_)
  rw [Finset.prod_const, card_Icc_one,
    Finset.card_erase_of_mem (mem_erase.mpr ⟨hij.symm, mem_univ j⟩),
    Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
  congr 1

theorem card_image_of_injective' {v : Fin k → ℤ} (hv : Function.Injective v) :
    (univ.image v).card = k := by
  rw [Finset.card_image_of_injective _ hv]; simp

theorem image_mem_kSubsets {q : ℕ} {v : Fin k → ℤ} (hv : v ∈ tuples q k)
    (hinj : Function.Injective v) : univ.image v ∈ kSubsets q k := by
  rw [kSubsets, Finset.mem_powersetCard]
  refine ⟨?_, card_image_of_injective' hinj⟩
  intro a ha
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  exact Fintype.mem_piFinset.mp hv i

/-- Counting `k`-subsets by injective tuples (upper bound). -/
theorem card_kSubsets_filter_le (q k : ℕ) (Q : Finset ℤ → Prop) [DecidablePred Q] :
    ((kSubsets q k).filter Q).card ≤
      ((tuples q k).filter (fun v => Function.Injective v ∧ Q (univ.image v))).card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun v => univ.image v))
  intro A hA
  rw [Finset.mem_filter, kSubsets, Finset.mem_powersetCard] at hA
  obtain ⟨⟨hAq, hAk⟩, hQ⟩ := hA
  rw [Finset.mem_image]
  refine ⟨fun i => A.orderEmbOfFin hAk i, ?_, Finset.image_orderEmbOfFin_univ A hAk⟩
  rw [Finset.mem_filter]
  refine ⟨?_, (A.orderEmbOfFin hAk).injective, by rwa [Finset.image_orderEmbOfFin_univ A hAk]⟩
  rw [tuples, Fintype.mem_piFinset]
  intro i
  exact hAq (Finset.orderEmbOfFin_mem A hAk i)

/-- Counting `k`-subsets by injective tuples (lower bound): each set has at most `k!`
enumerations. -/
theorem card_tuples_filter_le (q k : ℕ) (Q : Finset ℤ → Prop) [DecidablePred Q] :
    ((tuples q k).filter (fun v => Function.Injective v ∧ Q (univ.image v))).card ≤
      k ! * ((kSubsets q k).filter Q).card := by
  classical
  set T := (tuples q k).filter (fun v => Function.Injective v ∧ Q (univ.image v))
  have himage : T.image (fun v => univ.image v) ⊆ (kSubsets q k).filter Q := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hA
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨image_mem_kSubsets hv.1 hv.2.1, hv.2.2⟩
  refine (Finset.card_le_mul_card_image T (k !) ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card himage))
  intro A hA
  have hAk : A.card = k := by
    have := himage hA
    rw [Finset.mem_filter, kSubsets, Finset.mem_powersetCard] at this
    exact this.1.2
  set F := T.filter (fun v => univ.image v = A)
  have hmem : ∀ v ∈ F, ∀ i, v i ∈ A := by
    intro v hv i
    rw [Finset.mem_filter] at hv
    rw [← hv.2]
    exact Finset.mem_image_of_mem _ (mem_univ i)
  have hinj : ∀ v ∈ F, Function.Injective v := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.1
  let g : F → (Fin k ↪ A) := fun v =>
    ⟨fun i => ⟨v.1 i, hmem v.1 v.2 i⟩, fun i j hij => hinj v.1 v.2 (by simpa using hij)⟩
  have hg : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    funext i
    have := congrArg (fun f : Fin k ↪ A => (f i : ℤ)) hvw
    simpa [g] using this
  calc F.card = Fintype.card F := (Fintype.card_coe F).symm
    _ ≤ Fintype.card (Fin k ↪ A) := Fintype.card_le_of_injective g hg
    _ = k ! := by
      rw [Fintype.card_embedding_eq, Fintype.card_coe, hAk, Fintype.card_fin,
        Nat.descFactorial_self]

theorem setVec_eq {A : Finset ℤ} (hA : A.card = k) (i : Fin k) :
    setVec k A i = A.orderEmbOfFin hA i := by
  simp [setVec, hA]

theorem setVec_strictMono {A : Finset ℤ} (hA : A.card = k) : StrictMono (setVec k A) := by
  intro i j hij
  rw [setVec_eq hA, setVec_eq hA]
  exact (A.orderEmbOfFin hA).strictMono hij

theorem setVec_injective {A : Finset ℤ} (hA : A.card = k) : Function.Injective (setVec k A) :=
  (setVec_strictMono hA).injective

theorem image_setVec {A : Finset ℤ} (hA : A.card = k) : univ.image (setVec k A) = A := by
  have : setVec k A = fun i => (A.orderEmbOfFin hA i : ℤ) := funext (setVec_eq hA)
  rw [this]
  exact Finset.image_orderEmbOfFin_univ A hA

/-- `hA = {x · vec A : x ∈ 𝒳_{h,k}}`. -/
theorem nsmul_eq_sumsOf_setVec (h : ℕ) {A : Finset ℤ} (hA : A.card = k) :
    h • A = sumsOf h (setVec k A) := by
  conv_lhs => rw [← image_setVec hA]
  exact nsmul_image_eq_sumsOf h _

theorem setVec_mem_tuples {q : ℕ} {A : Finset ℤ} (hA : A ∈ kSubsets q k) :
    setVec k A ∈ tuples q k := by
  rw [kSubsets, Finset.mem_powersetCard] at hA
  rw [tuples, Fintype.mem_piFinset]
  intro i
  rw [setVec_eq hA.2]
  exact hA.1 (Finset.orderEmbOfFin_mem A hA.2 i)

end Sumsets
