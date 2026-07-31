import Mathlib

/-!
# Multiplicity vectors, collisions, and the exact size of `hA`

Base file.  `X h k` is the set of multiplicity vectors, `hSumset h A` is `hA`, and
`M h k = C(h+k-1, k-1)` is the trivial upper bound on `|hA|`.  The dictionary
`collision_iff_relation` turns a repeated sum into a nonzero balanced integer
relation of weight `≤ h`.
-/

open scoped BigOperators
open Filter Finset

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Senger

/-- Multiplicity vectors: `x i` records how often `A i` is used, so `∑ x i = h`. -/
def X (h k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k ↦ Finset.range (h + 1)).filter
    (fun x ↦ ∑ i, x i = h)

/-- `M h k = C(h+k-1, k-1)`: how many multiplicity vectors there are, hence the
largest `|hA|` could possibly be. -/
def M (h k : ℕ) : ℕ := Nat.choose (h + k - 1) (k - 1)

/-- Evaluate a multiplicity vector against a tuple: `∑ x i * A i`. -/
def eval {k : ℕ} (A : Fin k → ℤ) (x : Fin k → ℕ) : ℤ :=
  ∑ i, (x i : ℤ) * A i

/-- `hA` itself, as the image of the multiplicity vectors. -/
def hSumset {k : ℕ} (h : ℕ) (A : Fin k → ℤ) : Finset ℤ :=
  (X h k).image (eval A)

/-- `A` is `B_h` exactly when different multiplicity vectors give different sums. -/
def IsBh {k : ℕ} (h : ℕ) (A : Fin k → ℤ) : Prop :=
  Set.InjOn (eval A) (X h k)

/-- Two different multiplicity vectors landing on the same sum. -/
def HasCollision {k : ℕ} (h : ℕ) (A : Fin k → ℤ) : Prop :=
  ∃ x ∈ X h k, ∃ y ∈ X h k, x ≠ y ∧ eval A x = eval A y

/-- Positive and negative parts of an integral relation. -/
def posPart {k : ℕ} (d : Fin k → ℤ) : Fin k → ℕ := fun i ↦ (d i).toNat
def negPart {k : ℕ} (d : Fin k → ℤ) : Fin k → ℕ := fun i ↦ (-d i).toNat

def weight {k : ℕ} (d : Fin k → ℤ) : ℕ := ∑ i, posPart d i

def Balanced {k : ℕ} (d : Fin k → ℤ) : Prop := ∑ i, d i = 0

def Satisfies {k : ℕ} (A d : Fin k → ℤ) : Prop := ∑ i, d i * A i = 0

/-- The relations that can matter at level `h`: nonzero, balanced, weight at most
`h`.  Phrased so that `d` and `-d` are both relevant — no arbitrary choice. -/
def Relevant {k : ℕ} (h : ℕ) (d : Fin k → ℤ) : Prop :=
  d ≠ 0 ∧ Balanced d ∧ weight d ≤ h

/-- Every collision between `h`-fold vectors runs along `d`.  This is what
"exactly one primitive relation" turns into once you unfold it. -/
def UniqueDirection {k : ℕ} (h : ℕ) (A : Fin k → ℤ) (d : Fin k → ℤ) : Prop :=
  ∀ x ∈ X h k, ∀ y ∈ X h k, eval A x = eval A y →
    ∃ m : ℤ, ∀ i, (x i : ℤ) - (y i : ℤ) = m * d i

/-- Stars and bars. -/
theorem card_X (h k : ℕ) (hk : 0 < k) : #(X h k) = M h k := by
  simp [X, M]
  have hxk : #(Finset.filter (fun x => ∑ i, x i = h) (Fintype.piFinset fun _ : Fin k => Finset.range (h + 1))) =
    Nat.multichoose k h := by
    -- Prove it for every `h` at once, by induction on `k`.
    have hxk_gen : ∀ k, ∀ h, #(Finset.filter (fun x => ∑ i, x i = h) (Fintype.piFinset fun _ : Fin k => Finset.range (h + 1))) = Nat.multichoose k h := by
      intro k
      induction k with
      | zero =>
        intro h
        by_cases hh : h = 0 <;> simp [Nat.multichoose_eq, hh]
        simp_all [Nat.multichoose_eq, Nat.choose_eq_zero_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hh) zero_lt_one)]
        exact fun h0 => hh h0.symm
      | succ k' ih =>
        intro h
        symm
        -- Split on `x 0 = j`; the other `k'` coordinates then sum to `h - j`.
        trans ∑ j ∈ Finset.range (h + 1), k'.multichoose (h - j)
        · -- the recurrence for multichoose
          have reindex : ∑ j ∈ Finset.range (h + 1), k'.multichoose (h - j) = ∑ j ∈ Finset.range (h + 1), k'.multichoose j :=
            Finset.sum_range_reflect (n := h + 1) (f := fun i => k'.multichoose i)
          rw [reindex]
          suffices h_rec : ∀ h, (k' + 1).multichoose h = ∑ j ∈ Finset.range (h + 1), k'.multichoose j by
            exact h_rec h
          intro h0
          induction h0 with
          | zero => simp [Nat.multichoose]
          | succ h' ih' =>
            simp [Finset.sum_range_succ]
            rw [Nat.multichoose]
            simp [ih']
            rw [Finset.sum_range_succ]
            ring
        · -- and the matching fibre count
          set S := Finset.filter (fun x => ∑ i, x i = h)
            (Fintype.piFinset fun _ : Fin (k' + 1) => Finset.range (h + 1))
          let proj : (Fin (k' + 1) → ℕ) → ℕ := fun x => x 0
          -- The fibre over `j` bijects with vectors of length `k'` summing to `h - j`.
          have fiber_eq : ∀ j ∈ Finset.range (h + 1),
              #(Finset.filter (fun x => proj x = j) S) = k'.multichoose (h - j) := by
            intro j hj
            set T := Finset.filter (fun y => ∑ i, y i = h - j)
              (Fintype.piFinset fun _ : Fin k' => Finset.range (h + 1))
            have T_card : #T = k'.multichoose (h - j) := by
              have set_eq : ∀ m ≤ h,
                Finset.filter (fun x => ∑ i, x i = m)
                  (Fintype.piFinset fun _ : Fin k' => Finset.range (m + 1)) =
                Finset.filter (fun x => ∑ i, x i = m)
                  (Fintype.piFinset fun _ : Fin k' => Finset.range (h + 1)) := by
                intro m hm
                ext x
                simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
                constructor
                · intro ⟨hx_bound, hx_sum⟩
                  exact ⟨fun i => by have := hx_bound i; omega, hx_sum⟩
                · intro ⟨hx_bound, hx_sum⟩
                  exact ⟨fun i => by
                    have h2 := Finset.single_le_sum (fun a _ => Nat.zero_le (x a)) (Finset.mem_univ i)
                    omega, hx_sum⟩
              have T_eq : T = Finset.filter (fun y => ∑ i, y i = h - j)
                  (Fintype.piFinset fun _ : Fin k' => Finset.range (h - j + 1)) := by
                symm
                rw [set_eq (h - j) (Nat.sub_le h j)]
              rw [T_eq]
              exact ih (h - j)
            rw [← T_card]
            apply Finset.card_bij (fun x hx => Fin.tail x)
            · -- the tail lands in `T`
              intro a ha
              simp only [S, proj, T, Finset.mem_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at ha ⊢
              rcases ha with ⟨⟨ha_bound, ha_sum⟩, haj⟩
              refine ⟨fun i => ?_, ?_⟩
              · exact ha_bound i.succ
              · simp [Fin.tail]
                rw [Fin.sum_univ_succ] at ha_sum; rw [haj] at ha_sum; omega
            · -- injective
              intro a₁ ha₁ a₂ ha₂ heq
              simp only [S, proj, T, Finset.mem_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at ha₁ ha₂ ⊢
              obtain ⟨⟨_, ha₁_sum⟩, ha₁_0⟩ := ha₁
              obtain ⟨⟨_, ha₂_sum⟩, ha₂_0⟩ := ha₂
              ext i
              induction i using Fin.cases with
              | zero => simp [ha₁_0, ha₂_0]
              | succ i => simpa [Fin.tail] using congrFun heq i
            · -- surjective
              intro b hb
              simp only [S, proj, T, Finset.mem_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hb ⊢
              use Fin.cons j b
              obtain ⟨hb_bound, hb_sum⟩ := hb
              refine ⟨⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_⟩
              · cases i using Fin.cases with
                | zero => simp [hj]
                | succ i => exact hb_bound i
              · have hj' : j ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                rw [Fin.sum_univ_succ]; simp [hb_sum]; omega
              · simp [proj]
              · rfl
          rw [← Finset.sum_congr rfl fiber_eq]
          rw [← Finset.card_biUnion]
          · congr 1
            ext x
            simp_all
            intro hx
            have := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx |>.1)) 0
            simp at this
            omega
          · intro j hj j' hj' h
            simp only [proj]
            rw [Function.onFun]
            exact Finset.disjoint_filter.mpr (fun x _ => by aesop)
    exact hxk_gen k h
  rw [hxk, Nat.multichoose_eq]
  rw [add_comm k h]
  have heq : (h + k - 1) = h + (k - 1) := by omega
  rw [heq, Nat.choose_symm_add]

/-- No sumset has more elements than there are multiplicity vectors. -/
theorem card_hSumset_le (h k : ℕ) (A : Fin k → ℤ) :
    #(hSumset h A) ≤ #(X h k) := by
  exact Finset.card_image_le

/-- The two standard definitions of a `B_h` set agree. -/
theorem isBh_iff_card (h k : ℕ) (hk : 0 < k) (A : Fin k → ℤ) :
    IsBh h A ↔ #(hSumset h A) = M h k := by
  rw [← card_X h k hk]
  constructor
  · intro hinj
    rw [hSumset, Finset.card_image_of_injOn hinj]
  · intro hcard
    rw [hSumset] at hcard
    exact Finset.injOn_of_card_image_eq hcard

/-- Failure of the `B_h` property is exactly the existence of a collision. -/
theorem not_isBh_iff_collision (h k : ℕ) (A : Fin k → ℤ) :
    ¬ IsBh h A ↔ HasCollision h A := by
  simp only [IsBh, HasCollision, Set.InjOn]
  apply Iff.intro
  · intro h_not_inj
    push_neg at h_not_inj
    obtain ⟨x, hx, y, hy, heq, hne⟩ := h_not_inj
    exact ⟨x, hx, y, hy, hne, heq⟩
  · intro ⟨x, hx, y, hy, hne, heq⟩
    exact fun hinj => hne (hinj hx hy heq)

/-- A balanced relation has equally large positive and negative parts. -/
theorem sum_negPart_eq_weight {k : ℕ} {d : Fin k → ℤ} (hd : Balanced d) :
    ∑ i, negPart d i = weight d := by
  have h : ∀ i, d i = (posPart d i : ℤ) - (negPart d i : ℤ) := fun i => by
    simp [posPart, negPart]
  have hsum : ∑ i, d i = ∑ i, (posPart d i : ℤ) - ∑ i, (negPart d i : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  rw [Balanced] at hd
  have hweight : (weight d : ℤ) = ∑ i, (posPart d i : ℤ) := by
    simp [weight]
  linarith

/-- A collision hands you a relevant relation: take `d = x - y`. -/
theorem collision_gives_relation {h k : ℕ} {A : Fin k → ℤ}
    (hc : HasCollision h A) :
    ∃ d, Relevant h d ∧ Satisfies A d := by
  obtain ⟨x, hx, y, hy, hne, heq⟩ := hc
  use fun i => (x i : ℤ) - y i
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- d ≠ 0
    intro heq'
    apply hne
    exact funext fun i => by
      have := congr_fun heq' i
      simp only [Pi.zero_apply] at this
      have : (x i : ℤ) = (y i : ℤ) := by linarith
      exact Nat.cast_injective this
  · -- Balanced d
    simp only [Balanced]
    simp only [X] at hx hy
    rw [Finset.mem_filter] at hx hy
    have hxsum := hx.2
    have hysum := hy.2
    simp_rw [Finset.sum_sub_distrib]
    rw [← Nat.cast_sum, hxsum, ← Nat.cast_sum, hysum]
    simp
  · -- weight d ≤ h
    simp only [weight, posPart]
    have hxmem := hx
    simp only [X] at hxmem
    rw [Finset.mem_filter] at hxmem
    have hxsum := hxmem.2
    rw [← hxsum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hxy : x i ≥ y i
    · have heq : (x i : ℤ) - (y i : ℤ) = (x i - y i : ℕ) := by omega
      rw [heq, Int.toNat_natCast]
      exact Nat.sub_le _ _
    · have hle : (x i : ℤ) - (y i : ℤ) ≤ 0 := by linarith [Nat.lt_iff_add_one_le.mp (Nat.not_le.mp hxy)]
      rw [Int.toNat_of_nonpos hle]
      exact Nat.zero_le _
  · -- Satisfies A d
    simp only [Satisfies]
    have hxsum := (Finset.mem_filter.mp hx).2
    have hysum := (Finset.mem_filter.mp hy).2
    simp only [X] at hx hy
    rw [Finset.mem_filter] at hx hy
    have : ∑ i, (↑(x i) - ↑(y i)) * A i = eval A x - eval A y := by
      simp [eval, sub_mul]
    rw [this, heq, sub_self]

/-- Conversely, every relevant satisfied relation creates a collision. -/
theorem relation_gives_collision {h k : ℕ} {A : Fin k → ℤ}
    {d : Fin k → ℤ} (hr : Relevant h d) (hs : Satisfies A d) :
    HasCollision h A := by
  obtain ⟨hd_ne, hd_bal, hd_wt⟩ := hr
  -- k must be positive since d ≠ 0
  have hk : k ≠ 0 := by
    intro hk0
    subst hk0
    have : d = 0 := funext fun i => Fin.elim0 i
    exact hd_ne this
  let i₀ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  -- Padding vector: put all extra weight at i₀
  let t : Fin k → ℕ := fun i => if i = i₀ then h - weight d else 0
  -- The colliding pair: `posPart d + t` and `negPart d + t`.
  let x : Fin k → ℕ := fun i => posPart d i + t i
  let y : Fin k → ℕ := fun i => negPart d i + t i
  -- Both are in `X h k`: the weights are `≤ h` and the padding makes the sums `h`.
  have hx_mem : x ∈ X h k := by
    simp only [X, Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [x, t, Finset.mem_range]
      by_cases hi : i = i₀
      · subst hi
        have hpi : posPart d i₀ ≤ weight d :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (posPart d j)) (Finset.mem_univ i₀)
        have h1 : posPart d i₀ + (h - weight d) ≤ h := by
          calc posPart d i₀ + (h - weight d)
              ≤ weight d + (h - weight d) := Nat.add_le_add_right hpi _
            _ = h := Nat.add_sub_of_le hd_wt
        exact Nat.lt_succ_of_le h1
      · simp only [hi, add_zero]
        have h1 : posPart d i ≤ h := by
          exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (posPart d j)) (Finset.mem_univ i)) hd_wt
        exact Nat.lt_succ_of_le h1
    · -- Prove ∑ i, x i = h
      unfold x t
      have hsum_if : ∑ i, (if i = i₀ then h - weight d else 0) = h - weight d := by
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      rw [Finset.sum_add_distrib, hsum_if]
      simp only [weight] at hd_wt ⊢
      exact Nat.add_sub_of_le hd_wt
  -- same for `y`
  have hy_mem : y ∈ X h k := by
    simp only [X, Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [y, t, Finset.mem_range]
      by_cases hi : i = i₀
      · subst hi
        have hpi : negPart d i₀ ≤ weight d := by
          have := sum_negPart_eq_weight hd_bal
          calc negPart d i₀ ≤ ∑ j, negPart d j := Finset.single_le_sum (fun j _ => Nat.zero_le (negPart d j)) (Finset.mem_univ i₀)
            _ = weight d := this
        have h1 : negPart d i₀ + (h - weight d) ≤ h := by
          calc negPart d i₀ + (h - weight d)
              ≤ weight d + (h - weight d) := Nat.add_le_add_right hpi _
            _ = h := Nat.add_sub_of_le hd_wt
        exact Nat.lt_succ_of_le h1
      · simp only [hi, add_zero]
        have h1 : negPart d i ≤ h := by
          have hsum_neg := sum_negPart_eq_weight hd_bal
          calc negPart d i ≤ ∑ j, negPart d j := Finset.single_le_sum (fun j _ => Nat.zero_le (negPart d j)) (Finset.mem_univ i)
            _ = weight d := hsum_neg
            _ ≤ h := hd_wt
        exact Nat.lt_succ_of_le h1
    · unfold y t
      have hsum_if : ∑ i, (if i = i₀ then h - weight d else 0) = h - weight d := by
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      rw [Finset.sum_add_distrib, hsum_if]
      have hsum_eq := sum_negPart_eq_weight hd_bal
      simp only [weight] at hd_wt hsum_eq ⊢
      omega
  -- They differ: `posPart d = negPart d` would force `d = 0`.
  have hxy_ne : x ≠ y := by
    unfold x y
    intro heq
    have : posPart d = negPart d := funext fun i => by have := congr_fun heq i; linarith
    have hd_zero : d = 0 := by
      funext i
      simp only [Pi.zero_apply]
      have h := congr_fun this i
      simp only [posPart, negPart] at h
      by_cases hpos : d i ≥ 0
      · have h2 : (-d i).toNat = 0 := Int.toNat_of_nonpos (by linarith : -d i ≤ 0)
        rw [h2] at h
        have hle := Int.toNat_eq_zero.mp h
        linarith
      · have hneg : d i < 0 := lt_of_not_ge hpos
        have h1 : (d i).toNat = 0 := Int.toNat_of_nonpos (by linarith : d i ≤ 0)
        rw [h1] at h
        have hle := Int.toNat_eq_zero.mp h.symm
        linarith
    exact hd_ne hd_zero
  -- Same image: the difference is exactly `∑ d i * A i = 0`.
  have heval_eq : eval A x = eval A y := by
    unfold eval x y
    have hkey : ∀ i, (posPart d i : ℤ) - (negPart d i : ℤ) = d i := fun i => by
      rw [posPart, negPart]
      simp
    have hsum_eq : ∑ i : Fin k, (((posPart d i : ℤ) + (t i : ℤ)) * A i) =
                   ∑ i : Fin k, (((negPart d i : ℤ) + (t i : ℤ)) * A i) := by
      simp only [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      have hdiff : ∑ i : Fin k, ((posPart d i : ℤ) - (negPart d i : ℤ)) * A i = 0 := by
        simp_rw [hkey]
        exact hs
      have hsub : ∑ i : Fin k, ((posPart d i : ℤ) - (negPart d i : ℤ)) * A i =
                  ∑ i : Fin k, (posPart d i : ℤ) * A i - ∑ i : Fin k, (negPart d i : ℤ) * A i := by
        simp [sub_mul, Finset.sum_sub_distrib]
      linarith [hsub.symm ▸ hdiff]
    convert hsum_eq using 2 <;> norm_cast
  exact ⟨x, hx_mem, y, hy_mem, hxy_ne, heval_eq⟩

/-- Both directions at once — Lemma 7 of `MainResults.tex`, with relations taken
up to scaling and sign. -/
theorem collision_iff_relation {h k : ℕ} {A : Fin k → ℤ} :
    HasCollision h A ↔ ∃ d, Relevant h d ∧ Satisfies A d := by
  exact ⟨collision_gives_relation, fun ⟨d, hr, hs⟩ => relation_gives_collision hr hs⟩

/-- The counting workhorse: `e` equal-image pairs whose graph is acyclic knock at
least `e` elements off the image.  Acyclicity only enters through the leaf
condition, which is all the induction needs. -/
theorem card_image_le_sub_of_forest {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (E : Finset (α × α))
    (hedge : ∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2)
    (hforest : ∀ T : Finset (α × α), T ⊆ E → T.Nonempty →
      ∃ v ∈ S, #{p ∈ T | p.1 = v ∨ p.2 = v} = 1) :
    #(S.image f) ≤ #S - #E := by
  -- Strong induction on `#E`, peeling off a leaf edge each time.
  have gen : ∀ (n : ℕ) (S : Finset α) (f : α → β) (E : Finset (α × α)),
      #E = n →
      (∀ p ∈ E, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2) →
      (∀ T : Finset (α × α), T ⊆ E → T.Nonempty → ∃ v ∈ S, #{p ∈ T | p.1 = v ∨ p.2 = v} = 1) →
      #(S.image f) ≤ #S - n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S f E hEn hedge hforest
      by_cases hE : E = ∅
      · rw [hE, Finset.card_empty] at hEn
        rw [← hEn]
        simp [Finset.card_image_le]
      · -- E is non-empty
        have hEne : E.Nonempty := Finset.nonempty_of_ne_empty hE
        obtain ⟨e, heE⟩ := hEne
        -- `v` is a leaf: exactly one edge of `E` touches it.
        obtain ⟨v, hvS, hv_deg⟩ := hforest E (by simp) (Finset.nonempty_of_ne_empty hE)
        rw [Finset.card_eq_one] at hv_deg
        obtain ⟨edge_e, hedge_e⟩ := hv_deg
        have he_mem : edge_e ∈ E := by
          have h1 : edge_e ∈ ({edge_e} : Finset (α × α)) := Finset.mem_singleton_self _
          rw [← hedge_e] at h1
          exact Finset.mem_filter.mp h1 |>.1
        have he_edge := hedge edge_e he_mem
        have hv_eq : v = edge_e.1 ∨ v = edge_e.2 := by
          have : edge_e ∈ Finset.filter (fun p => p.1 = v ∨ p.2 = v) E := by
            rw [hedge_e]; exact Finset.mem_singleton_self _
          simp at this
          tauto
        -- Nothing else in `E` touches `v`, so deleting it keeps the forest condition.
        have hnot_inc : ∀ p ∈ E, p ≠ edge_e → p.1 ≠ v ∧ p.2 ≠ v := by
          intro p hp hpec
          have hp_inc : ¬(p.1 = v ∨ p.2 = v) := by
            intro hpv
            have : p ∈ Finset.filter (fun q => q.1 = v ∨ q.2 = v) E := by
              simp [hp, hpv]
            rw [hedge_e] at this
            simp at this
            exact hpec this
          exact ⟨fun h => hp_inc (Or.inl h), fun h => hp_inc (Or.inr h)⟩
        let E' := E \ {edge_e}
        have hn_pos : 0 < n := by rw [← hEn]; exact Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hE)
        have hE'_card : #E' = n - 1 := by
          simp only [E']
          rw [Finset.card_sdiff]
          simp [he_mem, hEn]
        have hE'_lt : #E' < n := by omega
        cases' hv_eq with hv1 hv2
        · -- Case v = edge_e.1
          have hv_eq' : v = edge_e.1 := hv1
          let S' := S \ {v}
          have hwS'_if : edge_e.2 ∈ S' := by
            simp only [S', Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨he_edge.2.1, (ne_of_eq_of_ne hv_eq' he_edge.2.2.1).symm⟩
          -- Deleting `v` does not shrink the image: its partner carries the same value.
          have himage : S.image f = S'.image f := by
            ext x
            simp only [Finset.mem_image]
            constructor
            · intro ⟨a, haS, hxa⟩
              by_cases ha : a = v
              · use edge_e.2
                constructor
                · exact hwS'_if
                · rw [ha, hv_eq', he_edge.2.2.2] at hxa; exact hxa
              · use a
                constructor
                · simp only [S', Finset.mem_sdiff, Finset.mem_singleton]
                  exact ⟨haS, ha⟩
                · exact hxa
            · intro ⟨a, haS', hxa⟩
              use a
              exact ⟨(Finset.mem_sdiff.mp haS').1, hxa⟩
          -- Apply IH to E' and S'
          have hedge' : ∀ p ∈ E', p.1 ∈ S' ∧ p.2 ∈ S' ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2 := by
            intro p hp
            have hp' := Finset.mem_sdiff.mp hp
            have hpne : p ≠ edge_e := by simpa using hp'.2
            have hni := hnot_inc p hp'.1 hpne
            refine ⟨Finset.mem_sdiff.mpr ⟨(hedge p hp'.1).1, ?_⟩,
                    Finset.mem_sdiff.mpr ⟨(hedge p hp'.1).2.1, ?_⟩,
                    (hedge p hp'.1).2.2.1, (hedge p hp'.1).2.2.2⟩
            · intro h; exact hni.1 (Finset.mem_singleton.mp h)
            · intro h; exact hni.2 (Finset.mem_singleton.mp h)
          have hforest' : ∀ T : Finset (α × α), T ⊆ E' → T.Nonempty →
            ∃ w ∈ S', #{p ∈ T | p.1 = w ∨ p.2 = w} = 1 := by
            intro T hTES' hTne
            obtain ⟨w, hwS, hwdeg⟩ := hforest T (Finset.Subset.trans hTES' (Finset.sdiff_subset)) hTne
            have hw_ne_v : w ≠ v := by
              by_contra hw_eq_v
              rw [hw_eq_v] at hwdeg
              have hnd : ∀ p ∈ T, ¬(p.1 = v ∨ p.2 = v) := by
                intro p hp
                have hp' := Finset.mem_sdiff.mp (hTES' hp)
                have hpne : p ≠ edge_e := by simpa using hp'.2
                have hni := hnot_inc p hp'.1 hpne
                exact fun h => h.elim (fun h1 => hni.1 h1) (fun h2 => hni.2 h2)
              have : #{p ∈ T | p.1 = v ∨ p.2 = v} = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                exact hnd
              omega
            exact ⟨w, Finset.mem_sdiff.mpr ⟨hwS, fun h => hw_ne_v (Finset.mem_singleton.mp h)⟩, hwdeg⟩
          have himap_le : #(S'.image f) ≤ #S' - #E' := by
            have := @ih (n - 1) (by omega) S' f E' hE'_card hedge' hforest'
            rwa [hE'_card.symm] at this
          -- #S' = #S - 1
          have hS'_card : #S' = #S - 1 := by
            rw [show S' = S \ {v} from rfl]
            rw [Finset.card_sdiff]
            simp [hvS]
          rw [himage.symm, hS'_card, hE'_card] at himap_le
          omega
        · -- Case v = edge_e.2
          have hv_eq' : v = edge_e.2 := hv2
          let S' := S \ {v}
          have hwS'_if : edge_e.1 ∈ S' := by
            simp only [S', Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨he_edge.1, (ne_of_eq_of_ne hv_eq' he_edge.2.2.1.symm).symm⟩
          -- Same thing with the endpoints swapped.
          have himage : S.image f = S'.image f := by
            ext x
            simp only [Finset.mem_image]
            constructor
            · intro ⟨a, haS, hxa⟩
              by_cases ha : a = v
              · use edge_e.1
                constructor
                · exact hwS'_if
                · rw [ha, hv_eq', he_edge.2.2.2.symm] at hxa; exact hxa
              · use a
                constructor
                · simp only [S', Finset.mem_sdiff, Finset.mem_singleton]
                  exact ⟨haS, ha⟩
                · exact hxa
            · intro ⟨a, haS', hxa⟩
              use a
              exact ⟨(Finset.mem_sdiff.mp haS').1, hxa⟩
          -- Apply IH to E' and S'
          have hedge' : ∀ p ∈ E', p.1 ∈ S' ∧ p.2 ∈ S' ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2 := by
            intro p hp
            have hp' := Finset.mem_sdiff.mp hp
            have hpne : p ≠ edge_e := by simpa using hp'.2
            have hni := hnot_inc p hp'.1 hpne
            refine ⟨Finset.mem_sdiff.mpr ⟨(hedge p hp'.1).1, ?_⟩,
                    Finset.mem_sdiff.mpr ⟨(hedge p hp'.1).2.1, ?_⟩,
                    (hedge p hp'.1).2.2.1, (hedge p hp'.1).2.2.2⟩
            · intro h; exact hni.1 (Finset.mem_singleton.mp h)
            · intro h; exact hni.2 (Finset.mem_singleton.mp h)
          have hforest' : ∀ T : Finset (α × α), T ⊆ E' → T.Nonempty →
            ∃ w ∈ S', #{p ∈ T | p.1 = w ∨ p.2 = w} = 1 := by
            intro T hTES' hTne
            obtain ⟨w, hwS, hwdeg⟩ := hforest T (Finset.Subset.trans hTES' (Finset.sdiff_subset)) hTne
            have hw_ne_v : w ≠ v := by
              by_contra hw_eq_v
              rw [hw_eq_v] at hwdeg
              have hnd : ∀ p ∈ T, ¬(p.1 = v ∨ p.2 = v) := by
                intro p hp
                have hp' := Finset.mem_sdiff.mp (hTES' hp)
                have hpne : p ≠ edge_e := by simpa using hp'.2
                have hni := hnot_inc p hp'.1 hpne
                exact fun h => h.elim (fun h1 => hni.1 h1) (fun h2 => hni.2 h2)
              have : #{p ∈ T | p.1 = v ∨ p.2 = v} = 0 := by
                rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                exact hnd
              omega
            exact ⟨w, Finset.mem_sdiff.mpr ⟨hwS, fun h => hw_ne_v (Finset.mem_singleton.mp h)⟩, hwdeg⟩
          have himap_le : #(S'.image f) ≤ #S' - #E' := by
            have := @ih (n - 1) (by omega) S' f E' hE'_card hedge' hforest'
            rwa [hE'_card.symm] at this
          -- #S' = #S - 1
          have hS'_card : #S' = #S - 1 := by
            rw [show S' = S \ {v} from rfl]
            rw [Finset.card_sdiff]
            simp [hvS]
          rw [himage.symm, hS'_card, hE'_card] at himap_le
          omega
  exact gen #E S f E rfl hedge hforest

/-- The leaf lemma.  Our edges are translates of one fixed pair, so both endpoint
maps are injective, and the lexicographic minimum of the vertex set is a leaf. -/
theorem translated_edges_have_leaf {k : ℕ} (x y : Fin k → ℕ) (hne : x ≠ y)
    (T : Finset (Fin k → ℕ)) :
    let edge := fun t : Fin k → ℕ ↦
      ((fun i ↦ x i + t i), (fun i ↦ y i + t i))
    ∀ U : Finset ((Fin k → ℕ) × (Fin k → ℕ)),
      U ⊆ T.image edge → U.Nonempty →
      ∃ v ∈ (T.image edge).biUnion (fun p ↦ {p.1, p.2}),
        #{p ∈ U | p.1 = v ∨ p.2 = v} = 1 := by
  intro edge U hUsub hUne
  -- `V` = all endpoints of the edges in `U`.
  set V : Finset (Fin k → ℕ) := U.biUnion (fun p => {p.1, p.2})
  have hVne : V.Nonempty := by
    obtain ⟨e, heU⟩ := hUne
    exact ⟨e.1, Finset.mem_biUnion.mpr ⟨e, heU, by simp⟩⟩
  -- Lexicographic order on `Fin k → ℕ`; its minimum on `V` will be the leaf.
  let ltLex : (Fin k → ℕ) → (Fin k → ℕ) → Prop := fun u v =>
    ∃ i : Fin k, u i < v i ∧ ∀ j : Fin k, j < i → u j = v j
  let ltLexGen : ∀ n : ℕ, (Fin n → ℕ) → (Fin n → ℕ) → Prop := fun n => fun u v =>
    ∃ i : Fin n, u i < v i ∧ ∀ j : Fin n, j < i → u j = v j
  -- Well-foundedness: induct on `k` and embed into `Prod.Lex`.
  have hwf_gen : ∀ k, WellFounded (fun u v : Fin k → ℕ => ∃ i : Fin k, u i < v i ∧ ∀ j : Fin k, j < i → u j = v j) := by
    intro k
    induction k with
    | zero =>
      exact ⟨fun v => Acc.intro _ (fun u h => by obtain ⟨i, _, _⟩ := h; exact i.elim0)⟩
    | succ n IH =>
      let embed : (Fin (n + 1) → ℕ) → ℕ × (Fin n → ℕ) := fun v => (v 0, fun i => v i.succ)
      have hembed : ∀ u v : Fin (n + 1) → ℕ,
        (∃ i : Fin (n+1), u i < v i ∧ ∀ j : Fin (n+1), j < i → u j = v j) →
        Prod.Lex (· < ·) (fun u v => ∃ i : Fin n, u i < v i ∧ ∀ j : Fin n, j < i → u j = v j) (embed u) (embed v) := by
          intro u v ⟨i, hi_lt, hi_prefix⟩
          cases i using Fin.inductionOn with
          | zero =>
            apply Prod.Lex.left
            exact hi_lt
          | succ j _ =>
            have h0 : u 0 = v 0 := hi_prefix 0 (by simp)
            simp only [embed]
            rw [h0]
            apply Prod.Lex.right
            exact ⟨j, hi_lt, fun k hk => hi_prefix k.succ (by simp [hk])⟩
      have hinj : Function.Injective embed := by
        intro u v heq
        simp only [embed] at heq
        ext i
        cases i using Fin.inductionOn with
        | zero => exact congr_arg Prod.fst heq
        | succ j _ => exact congr_fun (congr_arg Prod.snd heq) j
      let rel_n : (Fin n → ℕ) → (Fin n → ℕ) → Prop := fun u v => ∃ i : Fin n, u i < v i ∧ ∀ j : Fin n, j < i → u j = v j
      let emb : (Fin (n + 1) → ℕ) ↪ ℕ × (Fin n → ℕ) := ⟨embed, hinj⟩
      have hembed_rev : ∀ u v : Fin (n + 1) → ℕ,
        Prod.Lex (· < ·) rel_n (emb u) (emb v) →
        (∃ i : Fin (n+1), u i < v i ∧ ∀ j : Fin (n+1), j < i → u j = v j) := by
          intro u v h
          simp only [emb] at h
          have h' : u 0 < v 0 ∨ (u 0 = v 0 ∧ rel_n (fun i => u i.succ) (fun i => v i.succ)) := Prod.lex_iff.mp h
          rcases h' with hleft | ⟨heq, hj⟩
          · exact ⟨0, hleft, fun j hj => by cases j; exact absurd hj (Nat.not_lt_zero _)⟩
          · obtain ⟨j, hj_lt, hj_prefix'⟩ := hj
            refine ⟨j.succ, hj_lt, fun k hk => ?_⟩
            rcases k with ⟨_ | k, hk'⟩
            · simp [heq.symm]
            · simp only [Fin.lt_def] at hk
              have hk'' : k < j := by
                simp [Fin.succ] at hk
                omega
              have hk''' : k < n := hk''.trans j.isLt
              exact hj_prefix' ⟨k, hk'''⟩ hk''
      let ltLex_n := fun u v : Fin n → ℕ => ∃ i : Fin n, u i < v i ∧ ∀ j < i, u j = v j
      have h_wf_prod : WellFounded (Prod.Lex Nat.lt ltLex_n) := by
        refine WellFounded.prod_lex wellFounded_lt IH
      let map_rel_iff : ∀ a b, Prod.Lex Nat.lt ltLex_n (emb a) (emb b) ↔ ∃ i : Fin (n+1), a i < b i ∧ ∀ j : Fin (n+1), j < i → a j = b j := fun a b => ⟨hembed_rev a b, hembed a b⟩
      let bridge : ∀ (a b : Fin (n + 1) → ℕ), Prod.Lex Nat.lt ltLex_n (emb a) (emb b) ↔ ∃ i : Fin (n+1), a i < b i ∧ ∀ j : Fin (n+1), j < i → a j = b j := map_rel_iff
      let relEmb : RelEmbedding
          (α := (Fin (n + 1) → ℕ))
          (β := (ℕ × (Fin n → ℕ)))
          (r := fun u v => ∃ i : Fin (n+1), u i < v i ∧ ∀ j : Fin (n+1), j < i → u j = v j)
          (s := Prod.Lex Nat.lt ltLex_n) :=
        { toEmbedding := emb
          map_rel_iff' := fun {a b} => bridge a b }
      exact relEmb.wellFounded h_wf_prod
  have hwf := hwf_gen k
  -- `m` = the lex-minimum of `V`.
  have hVne' : Set.Nonempty (V : Set (Fin k → ℕ)) := by rw [Finset.coe_nonempty]; exact hVne
  let m := hwf.min (V : Set _) hVne'
  have hmV : m ∈ V := hwf.min_mem _ hVne'
  have hVsub : V ⊆ (T.image edge).biUnion (fun p => {p.1, p.2}) := by
    intro v hv
    simp only [V, Finset.mem_biUnion] at hv ⊢
    obtain ⟨e, heU, hev⟩ := hv
    exact ⟨e, hUsub heU, hev⟩
  have hm_biUnion : m ∈ (T.image edge).biUnion (fun p => {p.1, p.2}) := hVsub hmV
  -- Edges of `U` touching `m`.  There is at least one; the work is showing there
  -- is at most one.
  set incidentEdges := U.filter (fun p => p.1 = m ∨ p.2 = m) with hIncEdges
  have hIncNonempty : incidentEdges.Nonempty := by
    have : ∃ e ∈ U, e.1 = m ∨ e.2 = m := by
      obtain ⟨e, heU, hev⟩ := Finset.mem_biUnion.mp hmV
      simp only [Finset.mem_insert, Finset.mem_singleton] at hev
      exact ⟨e, heU, by tauto⟩
    obtain ⟨e, heU, hev⟩ := this
    exact ⟨e, Finset.mem_filter.mpr ⟨heU, hev⟩⟩
  have hIncUnique : ∀ e1 e2, e1 ∈ incidentEdges → e2 ∈ incidentEdges → e1 = e2 := by
    intro e1 e2 he1 he2
    simp only [hIncEdges, Finset.mem_filter] at he1 he2
    obtain ⟨hU1, hm1⟩ := he1
    obtain ⟨hU2, hm2⟩ := he2
    have h1 := hUsub hU1
    have h2 := hUsub hU2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨t1, ht1, ht1_eq⟩ := h1
    obtain ⟨t2, ht2, ht2_eq⟩ := h2
    have he1_eq : e1 = (fun i => x i + t1 i, fun i => y i + t1 i) := ht1_eq.symm
    have he2_eq : e2 = (fun i => x i + t2 i, fun i => y i + t2 i) := ht2_eq.symm
    rw [he1_eq, he2_eq]
    -- Four ways two edges can meet `m`.  Minimality rules out the mixed ones.
    have hm_le : ∀ v ∈ V, ¬ltLex v m := fun v hv => hwf.not_lt_min _ hVne' hv
    have he1_in_V : (fun i => x i + t1 i) ∈ V ∧ (fun i => y i + t1 i) ∈ V := by
      simp only [V, Finset.mem_biUnion]
      constructor <;> exact ⟨e1, hU1, by simp [he1_eq]⟩
    have he2_in_V : (fun i => x i + t2 i) ∈ V ∧ (fun i => y i + t2 i) ∈ V := by
      simp only [V, Finset.mem_biUnion]
      constructor <;> exact ⟨e2, hU2, by simp [he2_eq]⟩
    rcases hm1 with hx1 | hy1 <;> rcases hm2 with hx2 | hy2
    -- 1. both at the `x` end, so `t1 = t2` by cancellation
    · have hx1' : (fun i => x i + t1 i) = m := by simp [he1_eq] at hx1; exact hx1
      have hx2' : (fun i => x i + t2 i) = m := by simp [he2_eq] at hx2; exact hx2
      have ht : (fun i => x i + t1 i) = (fun i => x i + t2 i) := hx1'.trans hx2'.symm
      congr 1
      ext i
      have := congr_fun ht i
      omega
    -- 2. mixed ends: minimality of `m` forbids this unless `x = y`
    · have hx1' : (fun i => x i + t1 i) = m := by simp [he1_eq] at hx1; exact hx1
      have hy2' : (fun i => y i + t2 i) = m := by simp [he2_eq] at hy2; exact hy2
      have h1 : ¬ltLex (fun i => y i + t1 i) m := hm_le _ he1_in_V.2
      have h2 : ¬ltLex (fun i => x i + t2 i) m := hm_le _ he2_in_V.1
      rw [hx1'.symm] at h1
      rw [hy2'.symm] at h2
      have h_eq : ∀ i, x i + t1 i = y i + t2 i := by
        have := congr_fun (hx1'.trans hy2'.symm)
        exact this
      have hxy : (fun i => x i) = (fun i => y i) := by
        -- Compare `x` and `y` at their first difference.
        let S := Finset.univ.filter (fun i => x i ≠ y i)
        by_cases hS : S.Nonempty
        · -- S is nonempty, so it has a minimum
          let i₀ := S.min' hS
          have hprefix : ∀ j < i₀, x j = y j := fun j hj => by
            by_contra hne'
            have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩
            have hle : i₀ ≤ j := Finset.min'_le S j hjS
            exact not_lt.mpr hle hj
          by_cases hne_i₀ : x i₀ = y i₀
          · -- This contradicts i₀ ∈ S
            have hi₀S : i₀ ∈ S := Finset.min'_mem S hS
            simp [S] at hi₀S
            contradiction
          · rcases Nat.lt_or_gt_of_ne hne_i₀ with hlt | hgt
            · -- Show ltLex (x + t2) (y + t2)
              have := h2 ⟨i₀, by simp [hlt], fun j hj => by have := hprefix j hj; simp [this]⟩
              exact False.elim this
            · -- Show ltLex (y + t1) (x + t1)
              have := h1 ⟨i₀, by simp [hgt], fun j hj => by have := hprefix j hj; simp [this]⟩
              exact False.elim this
        · -- S is empty, so x = y everywhere
          rw [Finset.not_nonempty_iff_eq_empty] at hS
          apply funext
          intro i
          by_contra hi
          have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
          rw [hS] at hiS
          simp at hiS
      simp [hxy]
      ext i
      have := congr_fun hxy i
      have := h_eq i
      omega
    -- 3. mirror image of case 2
    · have hy1' : (fun i => y i + t1 i) = m := by simp [he1_eq] at hy1; exact hy1
      have hx2' : (fun i => x i + t2 i) = m := by simp [he2_eq] at hx2; exact hx2
      have h1 : ¬ltLex (fun i => x i + t1 i) m := hm_le _ he1_in_V.1
      have h2 : ¬ltLex (fun i => y i + t2 i) m := hm_le _ he2_in_V.2
      rw [hy1'.symm] at h1
      rw [hx2'.symm] at h2
      have h_eq : ∀ i, y i + t1 i = x i + t2 i := by
        have := congr_fun (hy1'.trans hx2'.symm)
        exact this
      have hxy : (fun i => x i) = (fun i => y i) := by
        let S := Finset.univ.filter (fun i => x i ≠ y i)
        by_cases hS : S.Nonempty
        · let i₀ := S.min' hS
          have hprefix : ∀ j < i₀, x j = y j := fun j hj => by
            by_contra hne'
            have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩
            have hle : i₀ ≤ j := Finset.min'_le S j hjS
            exact not_lt.mpr hle hj
          by_cases hne_i₀ : x i₀ = y i₀
          · have hi₀S : i₀ ∈ S := Finset.min'_mem S hS
            simp [S] at hi₀S
            exact False.elim (hi₀S hne_i₀)
          · rcases Nat.lt_or_gt_of_ne hne_i₀ with hlt | hgt
            · have := h1 ⟨i₀, by simp [hlt], fun j hj => by have := hprefix j hj; simp [this]⟩
              exact False.elim this
            · have := h2 ⟨i₀, by simp [hgt], fun j hj => by have := hprefix j hj; simp [this]⟩
              exact False.elim this
        · rw [Finset.not_nonempty_iff_eq_empty] at hS
          apply funext
          intro i
          by_contra hi
          have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
          rw [hS] at hiS
          simp at hiS
      simp [hxy]
      ext i
      have := congr_fun hxy i
      have := h_eq i
      omega
    -- 4. both at the `y` end, so `t1 = t2` again
    · have hy1' : (fun i => y i + t1 i) = m := by simp [he1_eq] at hy1; exact hy1
      have hy2' : (fun i => y i + t2 i) = m := by simp [he2_eq] at hy2; exact hy2
      have ht : (fun i => y i + t1 i) = (fun i => y i + t2 i) := hy1'.trans hy2'.symm
      congr 1
      ext i
      have := congr_fun ht i
      omega
  have hIncSubsingleton : ∀ e ∈ incidentEdges, ∀ e' ∈ incidentEdges, e = e' := by
    intro e he e' he'
    exact hIncUnique e e' he he'
  refine ⟨m, hm_biUnion, ?_⟩
  rw [Finset.card_eq_one]
  obtain ⟨e0, he0⟩ := hIncNonempty
  use e0
  ext e
  simp only [Finset.mem_singleton]
  constructor
  · intro he
    exact hIncSubsingleton e he e0 he0
  · intro he
    rw [he]
    exact he0

/-- Adding every `t ∈ T` to a single collision produces `#T` disjoint edges, so the
image drops by at least `#T`. -/
theorem translated_collision_image_bound {k : ℕ} (n : ℕ) (A : Fin k → ℤ)
    (x y : Fin k → ℕ) (T : Finset (Fin k → ℕ))
    (hne : x ≠ y) (heq : eval A x = eval A y)
    (hadd : ∀ t ∈ T, (fun i ↦ x i + t i) ∈ X n k ∧
      (fun i ↦ y i + t i) ∈ X n k)
    (hinj : Set.InjOn (fun t : Fin k → ℕ ↦
      ((fun i ↦ x i + t i), (fun i ↦ y i + t i))) T) :
    #(hSumset n A) ≤ #(X n k) - #T := by
  let edge := fun t : Fin k → ℕ ↦
    ((fun i ↦ x i + t i), (fun i ↦ y i + t i))
  let E := T.image edge
  have hEcard : #E = #T := by
    exact Finset.card_image_iff.mpr hinj
  have hedge : ∀ p ∈ E, p.1 ∈ X n k ∧ p.2 ∈ X n k ∧
      p.1 ≠ p.2 ∧ eval A p.1 = eval A p.2 := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(hadd t ht).1, (hadd t ht).2, ?_, ?_⟩
    · intro hxy
      apply hne
      funext i
      have hi := congrFun hxy i
      simp only [edge] at hi
      exact Nat.add_right_cancel hi
    · simp only [edge, eval]
      simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
      exact congrArg (fun z => z + ∑ i, (t i : ℤ) * A i) heq
  have hforest : ∀ U : Finset ((Fin k → ℕ) × (Fin k → ℕ)),
      U ⊆ E → U.Nonempty →
      ∃ v ∈ X n k, #{p ∈ U | p.1 = v ∨ p.2 = v} = 1 := by
    intro U hUE hUne
    obtain ⟨v, hv, hvdeg⟩ := translated_edges_have_leaf x y hne T U hUE hUne
    refine ⟨v, ?_, hvdeg⟩
    obtain ⟨p, hpE, hvp⟩ := Finset.mem_biUnion.mp hv
    have hpdata := hedge p hpE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvp
    rcases hvp with rfl | rfl
    · exact hpdata.1
    · exact hpdata.2.1
  have hb := card_image_le_sub_of_forest (X n k) (eval A) E hedge hforest
  change #((X n k).image (eval A)) ≤ #(X n k) - #T
  omega

/-- Adding the same terms to both sides propagates one collision. -/
theorem propagate_collision {h ell k : ℕ} {A : Fin k → ℤ}
    (hell : 1 ≤ ell) (hc : HasCollision (h + 1) A) :
    #(hSumset (h + ell) A) ≤ M (h + ell) k - M (ell - 1) k := by
  have hk : 0 < k := by
    by_contra hk0
    push_neg at hk0
    interval_cases k
    simp [X, HasCollision] at hc
  obtain ⟨x, hx, y, hy, hne, heq⟩ := hc
  have hcard_X_hell : #(X (ell - 1) k) = M (ell - 1) k := card_X (ell - 1) k hk
  have hcard_X_hell' : #(X (h + ell) k) = M (h + ell) k := card_X (h + ell) k hk
  have hadd : ∀ t ∈ X (ell - 1) k, (fun i ↦ x i + t i) ∈ X (h + ell) k ∧
      (fun i ↦ y i + t i) ∈ X (h + ell) k := by
    intro t ht
    have hx' := hx
    have hy' := hy
    have ht' := ht
    simp only [X, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hx' hy' ht' ⊢
    constructor
    · constructor
      · intro i; have := hx'.1 i; have := ht'.1 i; omega
      · simp [Finset.sum_add_distrib, hx'.2, ht'.2]
        omega
    · constructor
      · intro i; have := hy'.1 i; have := ht'.1 i; omega
      · simp [Finset.sum_add_distrib, hy'.2, ht'.2]
        omega
  have hinj : Set.InjOn (fun t : Fin k → ℕ ↦
      ((fun i ↦ x i + t i), (fun i ↦ y i + t i))) (X (ell - 1) k) := by
    intro t1 ht1 t2 ht2 heq
    simp at heq
    exact funext fun i => by simpa using congr_fun heq.1 i
  have := translated_collision_image_bound (h + ell) A x y (X (ell - 1) k) hne heq hadd hinj
  rw [hcard_X_hell'] at this
  rw [hcard_X_hell] at this
  exact this

/-- Lower bound.  Under `UniqueDirection` each fibre of `eval A` is an interval in
the `d` direction, so its excess is the number of consecutive `d`-steps inside it,
and those inject into `X (h-s) k`. -/
theorem card_hSumset_unique_relation_lower {h k s : ℕ} {A : Fin k → ℤ}
    {d : Fin k → ℤ} (hk : 0 < k) (hd0 : d ≠ 0) (hbal : Balanced d)
    (hwt : weight d = s) (hs : s ≤ h)
    (hprim : ∀ m : ℤ, (∀ i, m ∣ d i) → m.natAbs = 1 ∨ m = 0)
    (hu : UniqueDirection h A d) :
    M h k - M (h - s) k ≤ #(hSumset h A) := by
  -- Count the "down edges": `x ↦ x - posPart d` is defined exactly on a copy of
  -- `X (h-s) k`, so discarding that many vectors from `X h k` leaves a set on
  -- which `eval A` is injective.
  let Y : Finset (Fin k → ℕ) := X (h - s) k
  let edgeFun : (Fin k → ℕ) → (Fin k → ℕ) := fun t => fun i => t i + (posPart d) i
  -- `edgeFun` lands in `X h k`.
  have hYtoXh : ∀ t ∈ Y, edgeFun t ∈ X h k := by
    intro t ht
    have ht' : t ∈ X (h - s) k := ht
    simp only [X, Finset.mem_filter] at ht' ⊢
    simp only [edgeFun]
    have ht_bound := ht'.1
    have ht_sum := ht'.2
    constructor
    · simp only [Fintype.mem_piFinset] at ht_bound ⊢
      intro i
      have hi := ht_bound i
      have hpd : posPart d i ≤ weight d := by
        simp only [weight]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (posPart d j)) (Finset.mem_univ i)
      rw [hwt] at hpd
      simp only [Finset.mem_range] at hi ⊢
      have : t i + posPart d i ≤ (h - s) + s := by omega
      have heq : (h - s) + s = h := by omega
      omega
    · simp [Finset.sum_add_distrib]
      have hposPart_sum : ∑ i, posPart d i = weight d := rfl
      rw [ht_sum, hposPart_sum, hwt]
      omega
  have hedgeFun_inj : Set.InjOn edgeFun Y := by
    intro t1 ht1 t2 ht2 heq
    have : edgeFun t1 = edgeFun t2 := heq
    funext i
    have := congr_fun this i
    simp only [edgeFun] at this
    exact Nat.add_right_cancel this
  let E := (X (h - s) k).image (fun t => (edgeFun t, t))
  have hE_card : #(E : Finset ((Fin k → ℕ) × (Fin k → ℕ))) = #(X (h - s) k) := by
    rw [Finset.card_image_of_injOn]
    intro t1 ht1 t2 ht2 heq
    have : t1 = t2 := by simpa using congr_arg Prod.snd heq
    exact this
  have hY_card : #(X (h - s) k) = M (h - s) k := card_X (h - s) k hk
  have hX_card : #(X h k) = M h k := card_X h k hk
  let V : Finset (Fin k → ℕ) := X h k
  -- Split on whether `A` satisfies `d` at all.
  rw [hSumset]
  by_cases hrel : Satisfies A d
  · -- `A` satisfies `d`.
    -- Throw away everything of the form `edgeFun t` and show `eval A` is injective
    -- on what is left; that is `M h k - M (h-s) k` distinct values.
    let Z := Finset.image edgeFun (X (h - s) k)
    have hZ_sub : Z ⊆ X h k := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hYtoXh t ht
    have hZ_card : #Z = #(X (h - s) k) := Finset.card_image_of_injOn hedgeFun_inj
    let Y' := X h k \ Z
    have hY'_card : #Y' = #(X h k) - #(X (h - s) k) := by
      simp only [Y']
      rw [Finset.card_sdiff]
      rw [Finset.inter_eq_left.mpr hZ_sub, hZ_card, hX_card]
    have hinjY' : Set.InjOn (eval A) Y' := by
      intro x hx y hy heq
      have hx_mem : x ∈ X h k := Finset.mem_sdiff.mp hx |>.1
      have hy_mem : y ∈ X h k := Finset.mem_sdiff.mp hy |>.1
      have hx_notZ : x ∉ Z := Finset.mem_sdiff.mp hx |>.2
      have hy_notZ : y ∉ Z := Finset.mem_sdiff.mp hy |>.2
      -- `UniqueDirection` gives `x - y = m * d`.
      have := hu x hx_mem y hy_mem heq
      obtain ⟨m, hm⟩ := this
      by_cases hm0 : m = 0
      · funext i; have := hm i; simp [hm0] at this; simp_all [sub_eq_zero]
      · -- `m ≠ 0` would drag `x` or `y` back into the discarded set.
        have hxdiff : ∀ i, (x i : ℤ) - (y i : ℤ) = m * (d i) := fun i => hm i
        by_cases hm_pos : 0 < m
        · -- `m > 0`: then `x - posPart d ∈ X (h-s) k`
          let z : Fin k → ℕ := fun i => x i - (posPart d) i
          have hx_ge : ∀ i, x i ≥ posPart d i := by
            intro i
            have hxy : (x i : ℤ) = y i + m * (d i) := by linarith [hxdiff i]
            by_cases hdi : d i > 0
            · show posPart d i ≤ x i
              have hx_ge_md : (x i : ℤ) ≥ m * (d i) := by
                calc (x i : ℤ) = y i + m * (d i) := hxy
                  _ ≥ 0 + m * (d i) := by linarith
                  _ = m * (d i) := by ring
              have hm1 : m ≥ 1 := hm_pos
              have hx_ge_d : (x i : ℤ) ≥ d i := by nlinarith
              simp only [posPart]
              have hdi_eq : d i = ↑(d i).toNat := (Int.toNat_of_nonneg (le_of_lt hdi)).symm
              omega
            · push_neg at hdi
              rw [posPart]
              simp only [Int.toNat_of_nonpos hdi]
              exact Nat.zero_le _
          have hz_nonneg : ∀ i, posPart d i ≤ x i := hx_ge
          have hz_eq : ∀ i, z i = x i - posPart d i := fun i => rfl
          have hz_mem : z ∈ X (h - s) k := by
            have hx_sum : ∑ i, x i = h := by
              simp only [X, Finset.mem_filter, Fintype.mem_piFinset] at hx_mem
              exact hx_mem.2
            have hposPart_sum : ∑ i, posPart d i = weight d := rfl
            rw [hwt] at hposPart_sum
            have hsum_z : ∑ i, z i = h - s := by
              have h1 : ∑ i, z i + ∑ i, posPart d i = ∑ i, x i := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [hz_eq i]; exact Nat.sub_add_cancel (hz_nonneg i)
              omega
            simp only [X, Finset.mem_filter, Fintype.mem_piFinset]
            constructor
            · -- z i < (h - s) + 1
              intro i
              simp only [Finset.mem_range]
              have := Finset.single_le_sum (fun j _ => Nat.zero_le (z j)) (Finset.mem_univ i)
              omega
            · -- ∑ z i = h - s
              exact hsum_z
          have hx_in_Z : x ∈ Z := by
            simp only [Z, Finset.mem_image]
            use z
            refine ⟨hz_mem, ?_⟩
            funext i
            simp only [edgeFun]
            rw [hz_eq i]
            exact Nat.sub_add_cancel (hz_nonneg i)
          exact False.elim (hx_notZ hx_in_Z)
        · -- `m < 0`: same with `x` and `y` swapped
          have hm_neg : m < 0 := lt_of_le_of_ne (le_of_not_gt hm_pos) hm0
          let w : Fin k → ℕ := fun i => y i - (posPart d) i
          have hy_ge : ∀ i, y i ≥ posPart d i := by
            intro i
            have hxy : (y i : ℤ) = x i - m * (d i) := by linarith [hxdiff i]
            by_cases hdi : d i > 0
            · show posPart d i ≤ y i
              simp only [posPart]
              have hy_ge_md : (y i : ℤ) ≥ -m * (d i) := by
                calc (y i : ℤ) = x i - m * (d i) := hxy
                  _ ≥ 0 - m * (d i) := by linarith
                  _ = -m * (d i) := by ring
              have hm1 : -m ≥ 1 := by omega
              have : (y i : ℤ) ≥ d i := by nlinarith
              omega
            · push_neg at hdi
              rw [posPart]
              simp only [Int.toNat_of_nonpos hdi]
              exact Nat.zero_le _
          have hw_nonneg : ∀ i, posPart d i ≤ y i := hy_ge
          have hw_eq : ∀ i, w i = y i - posPart d i := fun i => rfl
          have hy_sum : ∑ i, y i = h := by
            simp only [X, Finset.mem_filter, Fintype.mem_piFinset] at hy_mem
            exact hy_mem.2
          have hposPart_sum : ∑ i, posPart d i = weight d := rfl
          rw [hwt] at hposPart_sum
          have hw_sum : ∑ i, w i = h - s := by
            have h1 : ∑ i, w i + ∑ i, posPart d i = ∑ i, y i := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ => by rw [hw_eq i]; exact Nat.sub_add_cancel (hw_nonneg i)
            omega
          have hw_mem : w ∈ X (h - s) k := by
            simp only [X, Finset.mem_filter, Fintype.mem_piFinset]
            constructor
            · intro i
              simp only [Finset.mem_range]
              have := Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)
              omega
            · exact hw_sum
          have hy_in_Z : y ∈ Z := by
            simp only [Z, Finset.mem_image]
            use w
            refine ⟨hw_mem, ?_⟩
            funext i
            simp only [edgeFun]
            rw [hw_eq i]
            exact Nat.sub_add_cancel (hw_nonneg i)
          exact False.elim (hy_notZ hy_in_Z)
    have h_im_Y' : #(Y'.image (eval A)) = #Y' := Finset.card_image_of_injOn hinjY'
    have h_sub : (Y'.image (eval A)) ⊆ (X h k).image (eval A) := by
      apply Finset.image_subset_image
      exact Finset.subset_iff.mpr (fun x hx => Finset.mem_sdiff.mp hx |>.1)
    calc M h k - M (h - s) k
        = #(X h k) - #(X (h - s) k) := by rw [hX_card, hY_card]
      _ = #Y' := hY'_card.symm
      _ = #(Y'.image (eval A)) := h_im_Y'.symm
      _ ≤ #((X h k).image (eval A)) := Finset.card_le_card h_sub
  · -- `A` does not satisfy `d`: no collisions at all, so `|hA|` is maximal.
    have hNoCollision : ¬HasCollision h A := by
      intro hcol
      obtain ⟨x, hx, y, hy, hne, heq⟩ := hcol
      have := hu x hx y hy heq
      obtain ⟨m, hm⟩ := this
      by_cases hm0 : m = 0
      · have hxy : x = y := funext fun i => by
          have := hm i
          simp [hm0] at this
          exact Nat.cast_injective (by linarith : (x i : ℤ) = y i)
        exact hne hxy
      · have heq' : ∑ i, ((x i : ℤ) - (y i : ℤ)) * A i = 0 := by
          have h1 : ∑ i, ((x i : ℤ) - (y i : ℤ)) * A i = ∑ i, (x i : ℤ) * A i - ∑ i, (y i : ℤ) * A i := by
            simp [sub_mul, Finset.sum_sub_distrib]
          rw [h1]
          simp_rw [eval] at heq
          linarith
        have hsum2 : ∑ i, (m * (d i)) * A i = 0 := by
          have : ∀ i, ((x i : ℤ) - (y i : ℤ)) * A i = (m * (d i)) * A i := by
            intro i; rw [hm i]
          simp_rw [this] at heq'
          exact heq'
        have hsum3 : m * ∑ i, (d i) * A i = 0 := by
          have heq2 : ∑ i, (m * (d i)) * A i = m * ∑ i, (d i) * A i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [heq2] at hsum2
          exact hsum2
        have hrel' : ∑ i, (d i) * A i = 0 := by
          cases mul_eq_zero.mp hsum3 with
          | inl hm_zero => exact absurd hm_zero hm0
          | inr hsum_zero => exact hsum_zero
        exact hrel hrel'
    have hinj : Set.InjOn (eval A) (X h k) := fun x hx y hy heq => by
      by_contra hne
      exact hNoCollision ⟨x, hx, y, hy, hne, heq⟩
    rw [Finset.card_image_of_injOn hinj]
    exact Nat.sub_le_of_le_add <| by linarith [Nat.zero_le (M (h - s) k)]

/-- Upper bound, coming from the translated copies of the basic relation between
`posPart d` and `negPart d`. -/
theorem card_hSumset_relation_upper {h k s : ℕ} {A : Fin k → ℤ}
    {d : Fin k → ℤ} (hk : 0 < k) (hd0 : d ≠ 0) (hbal : Balanced d)
    (hwt : weight d = s) (hs : s ≤ h) (hrel : Satisfies A d) :
    #(hSumset h A) ≤ M h k - M (h - s) k := by
  have hs_pos : 1 ≤ s := by
    by_contra hs0
    push_neg at hs0
    interval_cases s
    apply hd0
    funext i
    have hpos : posPart d i = 0 := by simp [weight] at hwt; exact hwt i
    have hneg_le : negPart d i ≤ weight d := by
      calc negPart d i ≤ ∑ j, negPart d j := Finset.single_le_sum (fun j _ => Nat.zero_le (negPart d j)) (Finset.mem_univ i)
        _ = weight d := sum_negPart_eq_weight hbal
    rw [hwt] at hneg_le
    have hneg : negPart d i = 0 := Nat.eq_zero_of_le_zero hneg_le
    simp_all [posPart, negPart]
    linarith
  set h' := s - 1 with h'_eq
  have hcoll : HasCollision (h' + 1) A := by
    rw [h'_eq]
    have hs' : weight d ≤ s - 1 + 1 := by rw [hwt]; omega
    exact collision_iff_relation.mpr ⟨d, ⟨hd0, hbal, hs'⟩, hrel⟩
  have := propagate_collision (by omega : 1 ≤ h - s + 1) hcoll
  rw [h'_eq] at this
  have hsum : s - 1 + (h - s + 1) = h := by omega
  have hdiff : h - s + 1 - 1 = h - s := by omega
  rw [hsum, hdiff] at this
  exact this

/-- The exact count.  Once every collision runs in one primitive direction of
weight `s`, each fibre is a gapless chain and the chains are indexed by
`X (h-s) k`. -/
theorem card_hSumset_unique_relation {h k s : ℕ} {A : Fin k → ℤ}
    {d : Fin k → ℤ} (hk : 0 < k) (hd0 : d ≠ 0) (hbal : Balanced d)
    (hwt : weight d = s) (hs : s ≤ h) (hrel : Satisfies A d)
    (hprim : ∀ m : ℤ, (∀ i, m ∣ d i) → m.natAbs = 1 ∨ m = 0)
    (hu : UniqueDirection h A d) :
    #(hSumset h A) = M h k - M (h - s) k := by
  apply Nat.le_antisymm
  · exact card_hSumset_relation_upper hk hd0 hbal hwt hs hrel
  · exact card_hSumset_unique_relation_lower hk hd0 hbal hwt hs hprim hu

/-- The worked example: `4·{1,2,3} = {4,…,12}`, checked by `native_decide`. -/
theorem example_fourfold_AP :
    hSumset 4 (fun i : Fin 3 ↦ ([1, 2, 3] : List ℤ).get i) =
      {4, 5, 6, 7, 8, 9, 10, 11, 12} := by
  native_decide

/-- Nine sums, which is `M 4 3 - M 2 3 = 15 - 6`. -/
theorem example_fourfold_AP_card :
    #(hSumset 4 (fun i : Fin 3 ↦ ([1, 2, 3] : List ℤ).get i)) = 9 := by
  rw [example_fourfold_AP]
  decide

/-- Consecutive listed sizes differ by `C(ell+k-2, k-2)` — triangular numbers when
`k = 4`.  The `ell = 0` case uses the convention `M(-1,k) = 0`. -/
theorem consecutive_gap (k h ell : ℕ) (hk : 2 ≤ k) (hell : ell < h) :
    (M h k - (if ell = 0 then 0 else M (ell - 1) k)) -
      (M h k - M ell k) = Nat.choose (ell + k - 2) (k - 2) := by
  simp [M]
  split_ifs with hell0
  · -- ell = 0 case
    subst hell0
    simp
    have h1 : (h + k - 1).choose (k - 1) ≥ 1 := Nat.choose_pos (by omega : k - 1 ≤ h + k - 1)
    omega
  · -- ell > 0 case
    have hell_pos : 0 < ell := Nat.pos_of_ne_zero hell0
    -- Rewrite ell - 1 + k - 1 to ell + k - 2
    have h1 : ell - 1 + k - 1 = ell + k - 2 := by omega
    rw [h1]
    have hell_k : ell + k - 1 ≤ h + k - 1 := by omega
    have hell_k' : ell + k - 2 ≤ h + k - 1 := by omega
    -- `a - b - (a - c) = c - b` given `b, c ≤ a`; truncated subtraction, so `omega`
    -- needs those bounds up front.
    have key : (h + k - 1).choose (k - 1) - (ell + k - 2).choose (k - 1) -
               ((h + k - 1).choose (k - 1) - (ell + k - 1).choose (k - 1)) =
               (ell + k - 1).choose (k - 1) - (ell + k - 2).choose (k - 1) := by
      have hc : (ell + k - 1).choose (k - 1) ≤ (h + k - 1).choose (k - 1) :=
        Nat.choose_le_choose _ hell_k
      have hb : (ell + k - 2).choose (k - 1) ≤ (h + k - 1).choose (k - 1) :=
        Nat.choose_le_choose _ hell_k'
      omega
    rw [key]
    -- and what is left is Pascal
    have hk1 : 1 ≤ k := by omega
    have hellk : 2 ≤ ell + k := by omega
    have h_ellk : ell + k - 1 + 1 = ell + k := by omega
    rw [show ell + k - 1 = (ell + k - 2) + 1 by omega]
    rw [show k - 1 = (k - 2) + 1 by omega]
    rw [Nat.choose_succ_succ]
    simp

end Senger
