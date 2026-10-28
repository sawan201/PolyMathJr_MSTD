module

public import RequestProject.MainTheorem

/-!
# Examples `ex:E`, `ex:E-relation` and `ex:E-size`

`E = {1, 2, 3}`, `vec E = (1, 2, 3)`.
-/

@[expose] public section

open scoped Pointwise

namespace Sumsets

open Finset

/-- **Example `ex:E`.**  `8` is a collision in `4E`: `(1,2,1)·vec E = (2,0,2)·vec E = (0,4,0)·vec E = 8`. -/
theorem exE_collision :
    dotN ![1, 2, 1] ![(1 : ℤ), 2, 3] = 8 ∧ dotN ![2, 0, 2] ![(1 : ℤ), 2, 3] = 8 ∧
      dotN ![0, 4, 0] ![(1 : ℤ), 2, 3] = 8 := by
  decide

/-- **Example `ex:E`.**  `4E = [4..12]`, so `|4E| = 9 < 15 = M_{4,3}` and `E` is not a `B_4`-set. -/
theorem exE_nsmul : 4 • ({1, 2, 3} : Finset ℤ) = Icc 4 12 ∧
    (4 • ({1, 2, 3} : Finset ℤ)).card = 9 ∧ M 4 3 = 15 := by
  decide

theorem mem_coeffVectors_one_neg_two_one {h : ℕ} (hh : 2 ≤ h) :
    ![(1 : ℤ), -2, 1] ∈ coeffVectors h 3 := by
  rw [mem_coeffVectors]
  refine ⟨by decide, by decide, ?_, gcd_eq_one_of_entry (i := 0) rfl, ⟨0, by decide, by decide⟩⟩
  have : weight ![(1 : ℤ), -2, 1] = 2 := by decide
  omega

/-- **Example `ex:E-relation`.**  For every `h ≥ 2`, `(1,-2,1)` is the only vector of
`ℛ_{h,3}` orthogonal to `vec E = (1,2,3)`. -/
theorem exE_relation {h : ℕ} (hh : 2 ≤ h) (d : Fin 3 → ℤ) :
    (d ∈ coeffVectors h 3 ∧ dot d ![1, 2, 3] = 0) ↔ d = ![1, -2, 1] := by
  constructor
  · rintro ⟨hd, hdot⟩
    obtain ⟨-, hsum, -, hgcd, hlead⟩ := mem_coeffVectors.mp hd
    simp only [dot, Fin.sum_univ_three] at hsum hdot
    simp at hdot
    have h1 : d 1 = -2 * d 2 := by linarith
    have h0 : d 0 = d 2 := by linarith
    have hdvd : d 2 ∣ univ.gcd d := by
      refine Finset.dvd_gcd fun i _ => ?_
      fin_cases i
      · simp [h0]
      · simp [h1]
      · simp
    rw [hgcd] at hdvd
    have hd2 : d 2 = 1 ∨ d 2 = -1 := by
      rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hd2 with h2 | h2
    · funext i; fin_cases i <;> simp [h0, h1, h2]
    · exfalso
      obtain ⟨i, hi, hlt⟩ := hlead
      fin_cases i
      · simp at hi; omega
      · have := hlt 0 (by decide); omega
      · have := hlt 0 (by decide); omega
  · rintro rfl
    exact ⟨mem_coeffVectors_one_neg_two_one hh, by decide⟩

theorem M_three (h : ℕ) : M h 3 = (h + 2).choose 2 := rfl

/-- **Example `ex:E-size`.**  For every `h ≥ 2`, `|hE| = M_{h,3} - M_{h-2,3} = 2h + 1`. -/
theorem exE_size {h : ℕ} (hh : 2 ≤ h) : (h • ({1, 2, 3} : Finset ℤ)).card = 2 * h + 1 := by
  have himg : (univ.image ![(1 : ℤ), 2, 3]) = {1, 2, 3} := by decide
  rw [← himg, card_nsmul_image,
    gap_size_lemma (by norm_num) _ (mem_coeffVectors_one_neg_two_one hh) (by decide)
      (fun e he hev => (exE_relation hh e).mp ⟨he, hev⟩)]
  have hw : weight ![(1 : ℤ), -2, 1] = 2 := by decide
  rw [hw, M_three, M_three]
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.choose_one_right,
    Nat.choose_zero_right]
  omega

end Sumsets
