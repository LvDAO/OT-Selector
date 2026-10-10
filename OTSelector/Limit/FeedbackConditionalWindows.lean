import OTSelector.Limit.FeedbackConditionalRegularity
import OTSelector.Matching.FeedbackWindowComparison
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Deterministic spatial windows from actual cell prefix control

Uniform bounds for the four cell prefix sums control the roots, all complete blocks, and
windows between actual zero cuts. All geometry is read from the genuine marked cells.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators Classical

namespace OTSelector.Limit

open OTSelector.PointProcess OTSelector.Matching
set_option maxHeartbeats 600000

/-- Signed cumulative cell observable, using the same indexing convention as the physical roots. -/
noncomputable def feedbackCellSignedPrefix (C : ℝ) (r : Fin 4)
    (ω : FeedbackCellSequence) : ℤ → ℝ
  | .ofNat n => OTSelector.Probability.iidPrefix
      (feedbackCellRegularityObservable C r) (feedbackCellSideIndex false) n ω
  | .negSucc n => -OTSelector.Probability.iidPrefix
      (feedbackCellRegularityObservable C r) (feedbackCellSideIndex true) (n + 1) ω

@[simp]
theorem feedbackCellSignedPrefix_natCast (C : ℝ) (r : Fin 4)
    (ω : FeedbackCellSequence) (n : ℕ) :
    feedbackCellSignedPrefix C r ω (n : ℤ) =
      ∑ i ∈ Finset.range n, feedbackCellRegularityObservable C r (ω (i : ℤ)) := rfl

@[simp]
theorem feedbackCellSignedPrefix_neg_natCast (C : ℝ) (r : Fin 4)
    (ω : FeedbackCellSequence) (n : ℕ) :
    feedbackCellSignedPrefix C r ω (-(n : ℤ)) =
      -(∑ i ∈ Finset.range n,
        feedbackCellRegularityObservable C r (ω (-((i : ℤ) + 1)))) := by
  cases n with
  | zero => simp [feedbackCellSignedPrefix, OTSelector.Probability.iidPrefix]
  | succ n => rfl

/-- The signed cumulative observable has the actual cell value as each increment. -/
theorem feedbackCellSignedPrefix_add_one (C : ℝ) (r : Fin 4)
    (ω : FeedbackCellSequence) (j : ℤ) :
    feedbackCellSignedPrefix C r ω (j + 1) = feedbackCellSignedPrefix C r ω j +
      feedbackCellRegularityObservable C r (ω j) := by
  cases j with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, ← Nat.cast_add_one,
      feedbackCellSignedPrefix_natCast] using
      (Finset.sum_range_succ (fun i ↦ feedbackCellRegularityObservable C r (ω (i : ℤ))) n)
  | negSucc n =>
    rw [Int.negSucc_eq]
    have hi : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by omega
    rw [hi, ← Nat.cast_add_one, feedbackCellSignedPrefix_neg_natCast,
      feedbackCellSignedPrefix_neg_natCast, Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- The length primitive is exactly the existing physical root map. -/
theorem feedbackCellSignedPrefix_length (C : ℝ) (ω : FeedbackCellSequence) (j : ℤ) :
    feedbackCellSignedPrefix C 0 ω j = feedbackCellRoot ω j := by
  cases j <;> rfl

private theorem sum_Ico_eq_sub_of_increment (f F : ℤ → ℝ)
    (hF : ∀ j, F (j + 1) = F j + f j) {a b : ℤ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, f j = F b - F a := by
  have h (n : ℕ) : ∑ j ∈ Finset.Ico a (a + (n : ℤ)), f j = F (a + n) - F a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add_one, ← add_assoc,
        ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega : a ≤ a + (n : ℤ)) f, ih, hF]
      ring
  have heq : a + ((b - a).toNat : ℤ) = b := by omega
  simpa only [heq] using h (b - a).toNat

/-- Finite cell blocks are exact differences of the signed cumulative observable. -/
theorem sum_feedbackCellRegularityObservable_Ico (C : ℝ) (r : Fin 4)
    (ω : FeedbackCellSequence) {a b : ℤ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, feedbackCellRegularityObservable C r (ω j) =
      feedbackCellSignedPrefix C r ω b - feedbackCellSignedPrefix C r ω a :=
  sum_Ico_eq_sub_of_increment _ _ (feedbackCellSignedPrefix_add_one C r ω) hab

/-- Both half-line prefix estimates give one signed estimate on the full index interval. -/
theorem feedbackCellPrefixGood.signed {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (r : Fin 4) {j : ℤ} (hlo : -(M * k : ℕ) ≤ j) (hhi : j ≤ (M * k : ℕ)) :
    |feedbackCellSignedPrefix C r ω j - j * feedbackCellRegularityMean lam hlam0 hlam C r| ≤
      (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k := by
  cases j with
  | ofNat n =>
    apply hgood r false n
    change (n : ℤ) ≤ ((M * k : ℕ) : ℤ) at hhi
    exact_mod_cast hhi
  | negSucc n =>
    have hn : n + 1 ≤ M * k := by omega
    have h := hgood r true (n + 1) hn
    change |-OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
      (feedbackCellSideIndex true) (n + 1) ω -
      (Int.negSucc n : ℝ) * feedbackCellRegularityMean lam hlam0 hlam C r| ≤ _
    have heq : (Int.negSucc n : ℝ) = -((n + 1 : ℕ) : ℝ) := by
      simp only [Int.negSucc_eq, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one]
    rw [heq]
    have hneg : -OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
        (feedbackCellSideIndex true) (n + 1) ω -
        -((n + 1 : ℕ) : ℝ) * feedbackCellRegularityMean lam hlam0 hlam C r =
        -(OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
          (feedbackCellSideIndex true) (n + 1) ω -
          ((n + 1 : ℕ) : ℝ) * feedbackCellRegularityMean lam hlam0 hlam C r) := by ring
    rw [hneg, abs_neg]
    exact h

/-- All integer cell blocks inherit uniform linear approximation from the same finite grid. -/
theorem feedbackCellPrefixGood.int_block {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (r : Fin 4) {a b : ℤ} (hab : a ≤ b)
    (ha : -(M * k : ℕ) ≤ a) (hb : b ≤ (M * k : ℕ)) :
    |(∑ j ∈ Finset.Ico a b, feedbackCellRegularityObservable C r (ω j)) -
      (b - a : ℤ) * feedbackCellRegularityMean lam hlam0 hlam C r| ≤
      2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k := by
  have h1 := hgood.signed r ha (hab.trans hb)
  have h2 := hgood.signed r (ha.trans hab) hb
  rw [sum_feedbackCellRegularityObservable_Ico C r ω hab, Int.cast_sub]
  have htri := abs_sub_le
    (feedbackCellSignedPrefix C r ω b - b * feedbackCellRegularityMean lam hlam0 hlam C r) 0
    (feedbackCellSignedPrefix C r ω a - a * feedbackCellRegularityMean lam hlam0 hlam C r)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have heq : feedbackCellSignedPrefix C r ω b - feedbackCellSignedPrefix C r ω a -
      ((b : ℝ) - a) * feedbackCellRegularityMean lam hlam0 hlam C r =
      (feedbackCellSignedPrefix C r ω b - b * feedbackCellRegularityMean lam hlam0 hlam C r) -
      (feedbackCellSignedPrefix C r ω a - a * feedbackCellRegularityMean lam hlam0 hlam C r) := by ring
  rw [heq]
  linarith

/-- Prefix length control traps every point in the central spatial window in the finite index box. -/
theorem feedbackCellPrefixGood.index_bounds {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (hw : feedbackCellRootsGood ω) {x : ℝ}
    (hx : |x| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    -((M * k : ℕ) : ℤ) ≤ feedbackCellIndex ω x ∧
      feedbackCellIndex ω x < ((M * k : ℕ) : ℤ) := by
  have hleft := hgood.signed 0 (j := -((M * k : ℕ) : ℤ)) (le_refl _) (by omega)
  have hright := hgood.signed 0 (j := ((M * k : ℕ) : ℤ)) (by omega) (le_refl _)
  rw [feedbackCellSignedPrefix_length, feedbackCellRegularityMean_length] at hleft hright
  have hl := (abs_le.mp hleft).2
  have hr := (abs_le.mp hright).1
  push_cast at hl hr
  have hroots : feedbackCellRoot ω (-((M * k : ℕ) : ℤ)) ≤ x ∧
      x < feedbackCellRoot ω ((M * k : ℕ) : ℤ) := by
    simp only [Nat.cast_mul]
    constructor <;> nlinarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
  have hb := feedbackCellIndex_bounds hw x
  have hmono := (strictMono_feedbackCellRoot hw.1).monotone
  constructor
  · by_contra h
    have hh := hmono (show feedbackCellIndex ω x + 1 ≤ -((M * k : ℕ) : ℤ) by omega)
    linarith [hb.2, hroots.1]
  · by_contra h
    have hh := hmono (show ((M * k : ℕ) : ℤ) ≤ feedbackCellIndex ω x by omega)
    linarith [hb.1, hroots.2]

/-- The complete index box has only a linear amount of each nonnegative observable. -/
theorem feedbackCellPrefixGood.box_sum_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (r : Fin 4) :
    (∑ j ∈ Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ),
      feedbackCellRegularityObservable C r (ω j)) ≤
      (2 * M * feedbackCellRegularityMean lam hlam0 hlam C r +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r)) * k := by
  have h := (abs_le.mp (hgood.int_block r
    (a := -((M * k : ℕ) : ℤ)) (b := ((M * k : ℕ) : ℤ)) (by omega)
    (le_refl _) (le_refl _))).2
  push_cast at h
  simp only [Nat.cast_mul]
  nlinarith

/-- Any finite cell family inside that box inherits the same linear bound. -/
theorem feedbackCellPrefixGood.finite_sum_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (hC : 0 ≤ C)
    (r : Fin 4) (s : Finset ℤ)
    (hs : s ⊆ Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ)) :
    (∑ j ∈ s, feedbackCellRegularityObservable C r (ω j)) ≤
      (2 * M * feedbackCellRegularityMean lam hlam0 hlam C r +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r)) * k :=
  (Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun _ _ _ ↦ feedbackCellRegularityObservable_nonneg hC r _)).trans (hgood.box_sum_le r)

/-- The actual initial hold fits in the actual first-return roof. -/
theorem feedbackCell_initial_hold_le_length {ω : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood ω) (j : ℤ) :
    (ω j 1).1 ≤ feedbackCellLength (ω j) := by
  have hclock := (feedbackCellClock_strictMono (ω j) (hw.2 j).1).monotone
    (show 1 ≤ feedbackMarkedFirstReturnIndex (ω j) from (hw.2 j).2)
  rw [← feedbackCellLength_eq_clock (ω j) (hw.2 j).1 (hw.2 j).2] at hclock
  have hfirst : feedbackCellClock (ω j) 1 = (ω j 1).1 := by
    simpa only [feedbackCellClock_zero, zero_add] using feedbackCellClock_succ (ω j) 0
  rwa [hfirst] at hclock

/-- Every point of an initial hold has actual concatenated current zero. -/
theorem feedbackConcatenatedCurrent_eq_zero_of_mem_hold {ω : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood ω) (hstart : ∀ j, (ω j 0).2.2 = 0)
    {j : ℤ} {x : ℝ}
    (hx : x ∈ Ico (feedbackCellRoot ω j) (feedbackCellRoot ω j + (ω j 1).1)) :
    feedbackConcatenatedCurrent ω x = 0 := by
  have hhold := feedbackCell_initial_hold_le_length hw j
  have hcell : feedbackCellRoot ω j ≤ x ∧ x < feedbackCellRoot ω (j + 1) := by
    rw [feedbackCellRoot_add_one]
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hi := (feedbackCellIndex_eq_iff hw.1 x j).mpr hcell
  simp only [feedbackConcatenatedCurrent, hi]
  exact (feedbackCellCurrent_zero_iff_initial_hold (ω j) (hstart j)
    (hw.2 j).1 (hw.2 j).2 _ (by linarith [hx.1])
    (by rw [feedbackCellRoot_add_one] at hcell; linarith [hcell.2])).mpr (by linarith [hx.2])

/-- Initial zero-hold intervals of distinct cells are disjoint. -/
theorem disjoint_feedbackCell_holds {ω : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood ω) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (Ico (feedbackCellRoot ω i) (feedbackCellRoot ω i + (ω i 1).1))
      (Ico (feedbackCellRoot ω j) (feedbackCellRoot ω j + (ω j 1).1)) := by
  have hm := (strictMono_feedbackCellRoot hw.1.1).monotone
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hr := hm (show i + 1 ≤ j by omega)
    rw [feedbackCellRoot_add_one] at hr
    linarith [feedbackCell_initial_hold_le_length hw i, hxi.2, hxj.1]
  · have hr := hm (show j + 1 ≤ i by omega)
    rw [feedbackCellRoot_add_one] at hr
    linarith [feedbackCell_initial_hold_le_length hw j, hxj.2, hxi.1]

/-- The total initial hold of any complete cell family is a genuine zero-current occupation. -/
theorem sum_feedbackCell_holds_le_zero_occupation {ω : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood ω) (hstart : ∀ j, (ω j 0).2.2 = 0)
    (s : Finset ℤ) {a b : ℝ}
    (hs : ∀ j ∈ s, a ≤ feedbackCellRoot ω j ∧ feedbackCellRoot ω (j + 1) ≤ b) :
    (∑ j ∈ s, (ω j 1).1) ≤
      volume.real {x | x ∈ Icc a b ∧ feedbackConcatenatedCurrent ω x = 0} := by
  let H : ℤ → Set ℝ := fun j ↦
    Ico (feedbackCellRoot ω j) (feedbackCellRoot ω j + (ω j 1).1)
  have hd : PairwiseDisjoint (s : Set ℤ) H := fun i _ j _ hij ↦
    disjoint_feedbackCell_holds hw hij
  have hmeasure (j : ℤ) : volume.real (H j) = (ω j 1).1 := by
    change volume.real (Ico (feedbackCellRoot ω j) (feedbackCellRoot ω j + (ω j 1).1)) = _
    rw [Real.volume_real_Ico_of_le (by linarith [(hw.2 j).1 0])]
    ring
  have hsubset : (⋃ j ∈ s, H j) ⊆
      {x | x ∈ Icc a b ∧ feedbackConcatenatedCurrent ω x = 0} := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨j, hx⟩
    rcases mem_iUnion.mp hx with ⟨hj, hx⟩
    have hsj := hs j hj
    refine ⟨⟨hsj.1.trans hx.1, ?_⟩, feedbackConcatenatedCurrent_eq_zero_of_mem_hold hw hstart hx⟩
    rw [feedbackCellRoot_add_one] at hsj
    linarith [hx.2, feedbackCell_initial_hold_le_length hw j, hsj.2]
  calc
    _ = ∑ j ∈ s, volume.real (H j) := Finset.sum_congr rfl (fun j _ ↦ (hmeasure j).symm)
    _ = volume.real (⋃ j ∈ s, H j) :=
      (measureReal_biUnion_finset hd (fun _ _ ↦ measurableSet_Ico)
        (fun j _ ↦ by change volume (Ico _ _) ≠ ⊤; simp)).symm
    _ ≤ _ := measureReal_mono hsubset
      (measure_ne_top_of_subset (fun _ hx ↦ hx.1) (by simp : volume (Icc a b) ≠ ⊤))

/-- Every individual cell in the controlled box has a uniform length and reward bound. -/
theorem feedbackCellPrefixGood.int_cell_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (r : Fin 4)
    {j : ℤ} (hj0 : -((M * k : ℕ) : ℤ) ≤ j) (hj1 : j < ((M * k : ℕ) : ℤ)) :
    feedbackCellRegularityObservable C r (ω j) ≤
      feedbackCellRegularityMean lam hlam0 hlam C r +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k := by
  have h := (abs_le.mp (hgood.int_block r (a := j) (b := j + 1)
    (by omega) hj0 (by omega))).2
  have hi : Finset.Ico j (j + 1) = {j} := by ext q; simp; omega
  simpa only [hi, Finset.sum_singleton, add_sub_cancel_left,
    Int.cast_one, one_mul, sub_le_iff_le_add, add_comm] using h

/-- Occupation in any spatial interval is controlled by the actual cell length and hold prefixes.
The boundary loss is at most two cells, so no further union over spatial windows is necessary. -/
theorem feedbackCellPrefixGood.zero_occupation_lower {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (hC : 0 ≤ C)
    (hw : feedbackCellConfigurationGood ω) (hstart : ∀ j, (ω j 0).2.2 = 0)
    {a b : ℝ}
    (ha : -((M * k : ℕ) : ℤ) ≤ feedbackCellIndex ω a ∧
      feedbackCellIndex ω a < ((M * k : ℕ) : ℤ))
    (hb : -((M * k : ℕ) : ℤ) ≤ feedbackCellIndex ω b ∧
      feedbackCellIndex ω b < ((M * k : ℕ) : ℤ)) :
    feedbackCellMean lam hlam0 hlam *
      volume.real {x | x ∈ Icc a b ∧ feedbackConcatenatedCurrent ω x = 0} ≥
      feedbackCellRegularityMean lam hlam0 hlam C 1 *
        (b - a - 2 * feedbackCellMean lam hlam0 hlam -
          6 * (1 + feedbackCellMean lam hlam0 hlam) * k) -
        2 * feedbackCellMean lam hlam0 hlam *
          (1 + feedbackCellRegularityMean lam hlam0 hlam C 1) * k := by
  let l := feedbackCellMean lam hlam0 hlam
  let z := feedbackCellRegularityMean lam hlam0 hlam C 1
  let D := (1 + l) * k
  let E := (1 + z) * k
  let i := feedbackCellIndex ω a
  let j := feedbackCellIndex ω b
  let O := volume.real {x | x ∈ Icc a b ∧ feedbackConcatenatedCurrent ω x = 0}
  have hl : 0 < l := feedbackCellMean_pos hlam0 hlam
  have hz : 0 ≤ z := feedbackCellRegularityMean_nonneg hlam0 hlam hC 1
  have hD : 0 ≤ D := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hE : 0 ≤ E := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hO : 0 ≤ O := measureReal_nonneg
  have hia := feedbackCellIndex_bounds hw.1 a
  have hjb := feedbackCellIndex_bounds hw.1 b
  have hLi : feedbackCellLength (ω i) ≤ l + 2 * D := by
    simpa only [feedbackCellRegularityMean_length, feedbackCellRegularityObservable,
      Matrix.cons_val_zero, mul_assoc] using
      hgood.int_cell_le 0 ha.1 ha.2
  have hLj : feedbackCellLength (ω j) ≤ l + 2 * D := by
    simpa only [feedbackCellRegularityMean_length, feedbackCellRegularityObservable,
      Matrix.cons_val_zero, mul_assoc] using
      hgood.int_cell_le 0 hb.1 hb.2
  have hm := (strictMono_feedbackCellRoot hw.1.1).monotone
  suffices ht : l * O ≥ z * (b - a - 2 * l - 6 * D) - 2 * l * E by
    dsimp [l, O, z, D, E] at ht
    nlinarith
  by_cases hij : i + 1 ≤ j
  · have hs := hgood.int_block 0 hij (by dsimp [i]; omega) (le_of_lt hb.2)
    have hzsum := (abs_le.mp (hgood.int_block 1 hij
      (by dsimp [i]; omega) (le_of_lt hb.2))).1
    have hsumL : (∑ q ∈ Finset.Ico (i + 1) j, feedbackCellLength (ω q)) =
        feedbackCellRoot ω j - feedbackCellRoot ω (i + 1) := by
      simpa only [feedbackCellSignedPrefix_length, feedbackCellRegularityObservable,
        Matrix.cons_val_zero] using
        sum_feedbackCellRegularityObservable_Ico C 0 ω hij
    have hsumZ : (∑ q ∈ Finset.Ico (i + 1) j,
        feedbackCellRegularityObservable C 1 (ω q)) =
        ∑ q ∈ Finset.Ico (i + 1) j, (ω q 1).1 := by
      apply Finset.sum_congr rfl
      intro q _
      exact abs_of_pos ((hw.2 q).1 0)
    have hcontained (q : ℤ) (hq : q ∈ Finset.Ico (i + 1) j) :
        a ≤ feedbackCellRoot ω q ∧ feedbackCellRoot ω (q + 1) ≤ b := by
      have hq' := Finset.mem_Ico.mp hq
      exact ⟨(le_of_lt hia.2).trans (hm hq'.1),
        (hm (by omega : q + 1 ≤ j)).trans hjb.1⟩
    have hOsum := sum_feedbackCell_holds_le_zero_occupation hw hstart
      (Finset.Ico (i + 1) j) hcontained
    change (∑ q ∈ Finset.Ico (i + 1) j, (ω q 1).1) ≤ O at hOsum
    rw [hsumZ] at hzsum
    simp only [feedbackCellRegularityMean_length, feedbackCellRegularityObservable,
      Matrix.cons_val_zero, mul_assoc] at hs
    change |(∑ q ∈ Finset.Ico (i + 1) j, feedbackCellLength (ω q)) -
      (j - (i + 1) : ℤ) * l| ≤ 2 * D at hs
    rw [hsumL] at hs
    have hspan := (abs_le.mp hs).2
    rw [feedbackCellRoot_add_one] at hspan hjb
    have hzsum' : (j - (i + 1) : ℤ) * z - 2 * E ≤ O := by
      change -(2 * (1 + z) * k) ≤ _ - (j - (i + 1) : ℤ) * z at hzsum
      dsimp [E]
      linarith
    have hspan' : b - a - 2 * (l + 2 * D) ≤
        (j - (i + 1) : ℤ) * l + 2 * D := by linarith [hia.1, hjb.2]
    nlinarith [mul_le_mul_of_nonneg_left hspan' hz,
      mul_le_mul_of_nonneg_left hzsum' hl.le]
  · have hji : j ≤ i := by omega
    have hroot := hm hji
    rw [feedbackCellRoot_add_one] at hjb
    have hwidth : b - a ≤ l + 2 * D := by linarith [hia.1, hjb.2]
    have hneg : b - a - 2 * l - 6 * D ≤ 0 := by linarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz hneg, mul_nonneg hl.le hO,
      mul_nonneg hl.le hE]

/-- The complete-cell competitor window lies in the same finite box as its two cuts. -/
theorem feedbackCellPrefixGood.windowCells_subset {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (hw : feedbackCellRootsGood ω) {a b : ℝ}
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    feedbackWindowCells ω a b ⊆ Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ) := by
  intro j hj
  have hleft := hgood.index_bounds hw ha
  have hright := hgood.index_bounds hw hb
  have hj' := Finset.mem_Ico.mp hj
  exact Finset.mem_Ico.mpr ⟨hleft.1.trans hj'.1, hj'.2.trans hright.2⟩

/-- Actual interior event populations are linear throughout the controlled spatial window. -/
theorem feedbackCellPrefixGood.windowSourceCount_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (hw : feedbackCellRootsGood ω) {a b : ℝ}
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    feedbackWindowSourceCount ω a b ≤
      (2 * M * feedbackCellRegularityMean lam hlam0 hlam C 2 +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C 2)) * k :=
  (feedbackWindowSourceCount_le_sum (hgood.windowCells_subset hw ha hb)).trans (hgood.box_sum_le 2)

/-- The actual idle-free comparison rewards obey the same linear spatial-window bound. -/
theorem feedbackCellPrefixGood.windowReward_le {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam (quadraticUpperConstant lam) M k ω)
    (hw : feedbackCellRootsGood ω) {a b : ℝ}
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    feedbackWindowReward lam ω a b ≤
      (2 * M * feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 3 +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 3)) * k :=
  (feedbackWindowReward_le_sum hlam0.le (hgood.windowCells_subset hw ha hb)).trans (hgood.box_sum_le 3)

/-- Event locations are countable, so restricting zero occupation to valid non-event cuts
preserves its volume exactly. -/
theorem volume_feedbackZeroCut_eq (ω : FeedbackCellSequence) (a b : ℝ) :
    volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut ω x} =
      volume.real {x | x ∈ Icc a b ∧ feedbackConcatenatedCurrent ω x = 0} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [(Set.countable_range (fun i : ℤ × ℕ ↦ (feedbackCellEventPoint ω i).1)).ae_notMem
    (volume : Measure ℝ)] with x hx
  apply propext
  constructor
  · exact fun h ↦ ⟨h.1, h.2.1⟩
  · intro h
    refine ⟨h.1, h.2, fun i _ hi ↦ ?_⟩
    exact hx ⟨i, hi⟩

/-- The search-set of actual non-event zero cuts is measurable. -/
theorem measurableSet_feedbackZeroCut (ω : FeedbackCellSequence) :
    MeasurableSet {x | FeedbackZeroCut ω x} := by
  have hm : Measurable (fun x ↦ feedbackConcatenatedCurrent ω x) :=
    measurable_feedbackConcatenatedCurrent.comp
      (f := fun x : ℝ ↦ (ω, x)) (measurable_const.prodMk measurable_id)
  unfold FeedbackZeroCut
  simp only [ofPred_and, ofPred_forall]
  apply (measurableSet_eq_fun hm measurable_const).inter
  apply MeasurableSet.iInter fun i ↦ ?_
  apply MeasurableSet.iInter fun _ ↦ ?_
  exact (measurableSet_eq_fun measurable_const measurable_id).compl

/-- Uniform prefix regularity provides the genuine zero-cut occupation used by the bootstrap. -/
theorem feedbackCellPrefixGood.zeroCut_occupation_lower {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (hC : 0 ≤ C)
    (hw : feedbackCellConfigurationGood ω) (hstart : ∀ j, (ω j 0).2.2 = 0)
    {a b : ℝ}
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    feedbackCellMean lam hlam0 hlam *
      volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut ω x} ≥
      feedbackCellRegularityMean lam hlam0 hlam C 1 *
        (b - a - 2 * feedbackCellMean lam hlam0 hlam -
          6 * (1 + feedbackCellMean lam hlam0 hlam) * k) -
        2 * feedbackCellMean lam hlam0 hlam *
          (1 + feedbackCellRegularityMean lam hlam0 hlam C 1) * k := by
  rw [volume_feedbackZeroCut_eq]
  exact hgood.zero_occupation_lower hC hw hstart (hgood.index_bounds hw.1 ha)
    (hgood.index_bounds hw.1 hb)

/-- Once the deterministic mesh losses use at most half the available interval, the actual
zero-cut occupation is a fixed positive fraction of its length. -/
theorem feedbackCellPrefixGood.zeroCut_occupation_linear {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω) (hC : 0 ≤ C)
    (hw : feedbackCellConfigurationGood ω) (hstart : ∀ j, (ω j 0).2.2 = 0)
    {a b L : ℝ} (hwidth : L ≤ b - a)
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hmeshL : 2 * feedbackCellMean lam hlam0 hlam +
      6 * (1 + feedbackCellMean lam hlam0 hlam) * k ≤ L / 4)
    (hmeshZ : 2 * feedbackCellMean lam hlam0 hlam *
      (1 + feedbackCellRegularityMean lam hlam0 hlam C 1) * k ≤
        feedbackCellRegularityMean lam hlam0 hlam C 1 * L / 4) :
    (feedbackCellRegularityMean lam hlam0 hlam C 1 /
      (2 * feedbackCellMean lam hlam0 hlam)) * L ≤
        volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut ω x} := by
  have h := hgood.zeroCut_occupation_lower hC hw hstart ha hb
  have hz := feedbackCellRegularityMean_nonneg hlam0 hlam hC 1
  have hl := feedbackCellMean_pos hlam0 hlam
  have hbound : feedbackCellRegularityMean lam hlam0 hlam C 1 * L ≤
      2 * feedbackCellMean lam hlam0 hlam *
        volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut ω x} := by
    nlinarith [mul_le_mul_of_nonneg_left hwidth hz,
      mul_le_mul_of_nonneg_left hmeshL hz]
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity : 0 < 2 * feedbackCellMean lam hlam0 hlam)).mpr
    (by nlinarith [hbound])

end OTSelector.Limit
