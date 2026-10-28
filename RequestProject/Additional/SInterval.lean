module

public import RequestProject.Counting

/-!
# Proposition `prop:S-interval`

`𝒮_{h+1,k}(q) = {x · vec A : x ∈ 𝒳_{h+1,k}, A ∈ \binom{[q]}{k}}` is the full interval
`[(h+1) .. (h+1)q]`, and the representation counts `ν_q(s)` are symmetric about
`(h+1)(q+1)/2`.
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset

/-- The pairs `(x, A) ∈ 𝒳_{H,k} × \binom{[q]}{k}`. -/
def sumVecSubsetPairs (H k q : ℕ) : Finset ((Fin k → ℕ) × Finset ℤ) :=
  sumVectors H k ×ˢ kSubsets q k

/-- `𝒮_{H,k}(q) = {x · vec A : x ∈ 𝒳_{H,k}, A ∈ \binom{[q]}{k}}` (in the paper `H = h + 1`). -/
def Sset (H k q : ℕ) : Finset ℤ :=
  (sumVecSubsetPairs H k q).image (fun p => dotN p.1 (setVec k p.2))

/-- `ν_q(s) = #{(x, A) ∈ 𝒳_{H,k} × \binom{[q]}{k} : x · vec A = s}` (in the paper `H = h + 1`). -/
def nuCount (H k q : ℕ) (s : ℤ) : ℕ :=
  ((sumVecSubsetPairs H k q).filter (fun p => dotN p.1 (setVec k p.2) = s)).card

theorem dotN_single_add_single {k : ℕ} (v : Fin k → ℤ) (i j : Fin k) (c d : ℕ) :
    dotN (Pi.single i c + Pi.single j d) v = c * v i + d * v j := by
  simp only [dotN, Pi.add_apply, Nat.cast_add, add_mul, sum_add_distrib]
  congr 1
  · rw [sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]; simp
  · rw [sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp

theorem Sset_subset (H k q : ℕ) : Sset H k q ⊆ Icc (H : ℤ) (H * q) := by
  intro n hn
  simp only [Sset, sumVecSubsetPairs, mem_image, mem_product, Prod.exists] at hn
  obtain ⟨x, A, ⟨hx, hA⟩, rfl⟩ := hn
  have hv := setVec_mem_tuples hA
  simp only [tuples, Fintype.mem_piFinset, mem_Icc] at hv
  rw [sumVectors, Finset.Nat.mem_antidiagonalTuple] at hx
  have hH : (H : ℤ) = ∑ i, (x i : ℤ) := by exact_mod_cast hx.symm
  rw [mem_Icc, dotN, hH, sum_mul]
  constructor
  · exact sum_le_sum fun i _ => le_mul_of_one_le_right (by positivity) (hv i).1
  · exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i).2 (by positivity)

theorem Icc_subset_Sset {H k q : ℕ} (hH : 0 < H) (hk : 2 ≤ k) (hq : k ≤ q) :
    Icc (H : ℤ) (H * q) ⊆ Sset H k q := by
  intro n hn
  rw [mem_Icc] at hn
  have hHpos : (0 : ℤ) < H := by exact_mod_cast hH
  set a := n / H with ha
  set b := n % H with hb
  have hdiv : n = H * a + b := (Int.mul_ediv_add_emod n H).symm
  have hb0 : 0 ≤ b := Int.emod_nonneg _ hHpos.ne'
  have hbH : b < H := Int.emod_lt_of_pos _ hHpos
  have ha1 : 1 ≤ a := by
    by_contra hcon
    have : a ≤ 0 := by omega
    nlinarith
  have haq : a ≤ q := by
    by_contra hcon
    have : (q : ℤ) + 1 ≤ a := by omega
    nlinarith
  have hbq : 0 < b → a < q := by
    intro hbpos
    by_contra hcon
    have : (q : ℤ) ≤ a := by omega
    nlinarith
  set a' : ℤ := min (a + 1) q with ha'
  have hs : ({a, a'} : Finset ℤ) ⊆ Icc 1 (q : ℤ) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [mem_Icc]; omega
  have hscard : ({a, a'} : Finset ℤ).card ≤ k := (card_le_two).trans hk
  obtain ⟨A, hsA, hAI, hAcard⟩ := Finset.exists_subsuperset_card_eq hs hscard
    (by rw [card_Icc_one]; exact hq)
  have hAmem : A ∈ kSubsets q k := by
    rw [kSubsets, mem_powersetCard]; exact ⟨hAI, hAcard⟩
  have haA : a ∈ A := hsA (by simp)
  have ha'A : a' ∈ A := hsA (by simp)
  rw [← image_setVec hAcard, mem_image] at haA ha'A
  obtain ⟨i, -, hi⟩ := haA
  obtain ⟨j, -, hj⟩ := ha'A
  have hbN : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
  have hbH' : b.toNat ≤ H := by omega
  refine mem_image.mpr ⟨(Pi.single i (H - b.toNat) + Pi.single j b.toNat, A), ?_, ?_⟩
  · simp [sumVecSubsetPairs, hAmem, sumVectors, Finset.Nat.mem_antidiagonalTuple,
      sum_add_distrib]
    omega
  · simp only
    rw [dotN_single_add_single, hi, hj, Nat.cast_sub hbH', hbN]
    rcases eq_or_lt_of_le hb0 with h0 | h0
    · rw [← h0]; linarith
    · have : a' = a + 1 := by have := hbq h0; omega
      rw [this]; linarith

/-- **Proposition `prop:S-interval` (interval).**  For `2 ≤ k ≤ q`,
`𝒮_{h+1,k}(q) = [(h+1) .. (h+1)q]`. -/
theorem Sset_eq_Icc {h k q : ℕ} (hk : 2 ≤ k) (hq : k ≤ q) :
    Sset (h + 1) k q = Icc ((h + 1 : ℕ) : ℤ) ((h + 1 : ℕ) * q) :=
  (Sset_subset (h + 1) k q).antisymm (Icc_subset_Sset (Nat.succ_pos h) hk hq)

/-- **Proposition `prop:S-interval` (size).**  `|𝒮_{h+1,k}(q)| = (h+1)q - h` for `2 ≤ k ≤ q`. -/
theorem card_Sset {h k q : ℕ} (hk : 2 ≤ k) (hq : k ≤ q) :
    (Sset (h + 1) k q).card = (h + 1) * q - h := by
  rw [Sset_eq_Icc hk hq, Int.card_Icc]
  have : 1 ≤ q := by omega
  have : h ≤ (h + 1) * q := by nlinarith
  omega

/-- The reflection `A ↦ A' = {q + 1 - a : a ∈ A}`. -/
def reflSet (q : ℕ) (A : Finset ℤ) : Finset ℤ := A.image (fun a => (q : ℤ) + 1 - a)

theorem reflSet_reflSet (q : ℕ) (A : Finset ℤ) : reflSet q (reflSet q A) = A := by
  simp [reflSet, image_image]

theorem card_reflSet (q : ℕ) (A : Finset ℤ) : (reflSet q A).card = A.card :=
  card_image_of_injective _ (fun a b hab => by simpa using hab)

theorem reflSet_mem_kSubsets {q k : ℕ} {A : Finset ℤ} (hA : A ∈ kSubsets q k) :
    reflSet q A ∈ kSubsets q k := by
  rw [kSubsets, mem_powersetCard] at hA ⊢
  refine ⟨fun y hy => ?_, by rw [card_reflSet]; exact hA.2⟩
  simp only [reflSet, mem_image] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  have := hA.1 ha
  rw [mem_Icc] at this ⊢; omega

theorem setVec_reflSet {q k : ℕ} {A : Finset ℤ} (hA : A.card = k) (j : Fin k) :
    setVec k (reflSet q A) j = (q : ℤ) + 1 - setVec k A (Fin.rev j) := by
  have hA' : (reflSet q A).card = k := by rw [card_reflSet]; exact hA
  rw [setVec_eq hA']
  have key := Finset.orderEmbOfFin_unique hA'
    (f := fun j => (q : ℤ) + 1 - setVec k A (Fin.rev j)) (fun x => by
      simp only [reflSet, mem_image]
      exact ⟨_, by rw [setVec_eq hA]; exact orderEmbOfFin_mem A hA _, rfl⟩) (by
      intro i i' hii'
      have := setVec_strictMono hA (Fin.rev_lt_rev.mpr hii')
      simp only; linarith)
  exact (congrFun key j).symm

theorem refl_mem_and_dotN {H k q : ℕ} {x : Fin k → ℕ} {A : Finset ℤ}
    (hp : (x, A) ∈ sumVecSubsetPairs H k q) :
    (x ∘ Fin.rev, reflSet q A) ∈ sumVecSubsetPairs H k q ∧
      dotN (x ∘ Fin.rev) (setVec k (reflSet q A)) = H * (q + 1) - dotN x (setVec k A) := by
  simp only [sumVecSubsetPairs, mem_product, sumVectors, Finset.Nat.mem_antidiagonalTuple] at hp ⊢
  have hA := hp.2
  rw [kSubsets, mem_powersetCard] at hA
  have hsum : ∑ i, (x ∘ Fin.rev) i = ∑ i, x i :=
    Equiv.sum_comp Fin.revPerm x
  refine ⟨⟨hsum.trans hp.1, reflSet_mem_kSubsets hp.2⟩, ?_⟩
  have hH : (H : ℤ) = ∑ i, (x i : ℤ) := by exact_mod_cast hp.1.symm
  simp only [dotN, setVec_reflSet hA.2, Function.comp_apply]
  rw [show (∑ i, (x (Fin.rev i) : ℤ) * ((q : ℤ) + 1 - setVec k A (Fin.rev i))) =
      ∑ i, (x i : ℤ) * ((q : ℤ) + 1 - setVec k A i) from
    Equiv.sum_comp Fin.revPerm (fun i => (x i : ℤ) * ((q : ℤ) + 1 - setVec k A i)), hH,
    sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => by ring

/-- **Proposition `prop:S-interval` (symmetry).**  `ν_q(s) = ν_q(H(q+1) - s)` for every `s`
(the paper's statement is the case `H = h + 1`). -/
theorem nuCount_symm (H k q : ℕ) (s : ℤ) :
    nuCount H k q s = nuCount H k q (H * (q + 1) - s) := by
  unfold nuCount
  refine Finset.card_nbij' (fun p => (p.1 ∘ Fin.rev, reflSet q p.2))
    (fun p => (p.1 ∘ Fin.rev, reflSet q p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, A⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨h1, h2⟩ := refl_mem_and_dotN hp.1
    exact ⟨h1, by rw [h2, hp.2]⟩
  · rintro ⟨x, A⟩ hp
    simp only [coe_filter, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨h1, h2⟩ := refl_mem_and_dotN hp.1
    exact ⟨h1, by rw [h2, hp.2]; ring⟩
  all_goals
    rintro ⟨x, A⟩ -
    simp only [reflSet_reflSet, Prod.mk.injEq, and_true]
    funext i; simp

end Sumsets
