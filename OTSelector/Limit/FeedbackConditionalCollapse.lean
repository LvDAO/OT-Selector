import OTSelector.Limit.FeedbackConditionalWindows

/-!
# Geometry of deleting the distinguished residual hold

The collapse changes only the first wait of cell zero. Excursion data, all cell rewards and
jump counts remain unchanged. Physical roots on the positive side move by exactly the deleted
residual, while nonpositive roots stay fixed.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators Classical

namespace OTSelector.Limit
open OTSelector.PointProcess OTSelector.Matching
set_option maxHeartbeats 600000

/-- The normalized actual roof law conditioned on the indicated residual band. -/
noncomputable def feedbackConditionalRoofLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) : Measure (FeedbackCellSequence × ℝ) :=
  (feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹ •
    (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)

/-- Original iid cell properties remain almost sure under the normalized roof and its conditioning. -/
theorem feedbackConditionalRoofLaw_ae_base {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) {P : FeedbackCellSequence → Prop}
    (hP : ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam, P ω) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h, P p.1 := by
  apply Measure.ae_smul_measure
  apply ae_restrict_of_ae
  apply Measure.ae_smul_measure
  apply ae_restrict_of_ae
  exact Measure.quasiMeasurePreserving_fst.ae hP

/-- Collapsed cell properties are also genuine iid almost-sure properties under every band. -/
theorem feedbackConditionalRoofLaw_ae_collapsed {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) {P : FeedbackCellSequence → Prop}
    (hP : ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam, P ω) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h, P (feedbackCollapseZeroHold p) := by
  rw [← feedbackStationaryRoofLaw_conditional_band_collapse_iid lam hlam0 hlam h hh] at hP
  exact ae_of_ae_map measurable_feedbackCollapseZeroHold.aemeasurable hP

/-- Erasing the initial wait after collapse gives the same complete excursion path as before. -/
theorem feedbackCollapseZeroHold_withoutFirstWait (p : FeedbackCellSequence × ℝ) :
    feedbackMarkedWithoutFirstWait (feedbackCollapseZeroHold p 0) =
      feedbackMarkedWithoutFirstWait (p.1 0) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [feedbackMarkedWithoutFirstWait_add_two, feedbackCollapseZeroHold,
        feedbackCollapseZeroHoldAssemble, feedbackZeroHoldRestReadout, feedbackEraseZeroHold,
        ↓reduceIte]
      simp

/-- Every actual return index survives deletion of the distinguished residual hold. -/
theorem feedbackCollapseZeroHold_returnIndex (p : FeedbackCellSequence × ℝ) (j : ℤ) :
    feedbackMarkedFirstReturnIndex (feedbackCollapseZeroHold p j) =
      feedbackMarkedFirstReturnIndex (p.1 j) := by
  by_cases hj : j = 0
  · subst j
    rw [← feedbackMarkedWithoutFirstWait_returnIndex (feedbackCollapseZeroHold p 0),
      feedbackCollapseZeroHold_withoutFirstWait, feedbackMarkedWithoutFirstWait_returnIndex]
  · rw [feedbackCollapseZeroHold_other_cell p hj]

/-- The entire excursion-length field is invariant under the residual collapse. -/
theorem feedbackCollapseZeroHold_excursionLength (p : FeedbackCellSequence × ℝ) (j : ℤ) :
    feedbackCellExcursionLength (feedbackCollapseZeroHold p j) =
      feedbackCellExcursionLength (p.1 j) := by
  by_cases hj : j = 0
  · subst j
    rw [← feedbackCellExcursionLength_withoutFirstWait (feedbackCollapseZeroHold p 0),
      feedbackCollapseZeroHold_withoutFirstWait, feedbackCellExcursionLength_withoutFirstWait]
  · rw [feedbackCollapseZeroHold_other_cell p hj]

/-- In particular the actual idle-free reward field, with its comparison coefficient, is unchanged. -/
theorem feedbackCollapseZeroHold_reward (C : ℝ) (p : FeedbackCellSequence × ℝ) (j : ℤ) :
    feedbackCellReward C (feedbackCollapseZeroHold p j) = feedbackCellReward C (p.1 j) := by
  simp only [feedbackCellReward, feedbackCollapseZeroHold_returnIndex,
    feedbackCollapseZeroHold_excursionLength]

/-- The distinguished original roof exceeds the collapsed roof by exactly its residual hold. -/
theorem feedbackConditionalRoofLaw_length_difference {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h,
      feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
        ((p.1 0 1).1 - p.2) := by
  have hbase : ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam,
      feedbackCellLength (ω 0) = (ω 0 1).1 + feedbackCellExcursionLength (ω 0) :=
    (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).quasiMeasurePreserving.ae
      (feedbackCellLength_eq_hold_add_excursion hlam0 hlam)
  filter_upwards [feedbackConditionalRoofLaw_ae_base hlam0 hlam h hbase,
    feedbackConditionalRoofLaw_ae_collapsed hlam0 hlam h hh hbase] with p hp hc
  rw [feedbackCollapseZeroHold_first_wait, feedbackCollapseZeroHold_excursionLength] at hc
  linarith

/-- Deleting the residual translates positive return roots and fixes all nonpositive roots. -/
theorem feedbackCollapseZeroHold_root_difference (p : FeedbackCellSequence × ℝ)
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) (j : ℤ) :
    feedbackCellRoot p.1 j = feedbackCellRoot (feedbackCollapseZeroHold p) j +
      if 0 < j then (p.1 0 1).1 - p.2 else 0 := by
  cases j with
  | ofNat n =>
    change feedbackCellRoot p.1 (n : ℤ) = feedbackCellRoot (feedbackCollapseZeroHold p) (n : ℤ) +
      if 0 < (n : ℤ) then (p.1 0 1).1 - p.2 else 0
    induction n with
    | zero => simp
    | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [feedbackCellRoot] using hL
      · have hn' : (0 : ℤ) < n := by omega
        have hs' : (0 : ℤ) < (n : ℤ) + 1 := by omega
        rw [Nat.cast_add_one, feedbackCellRoot_add_one, feedbackCellRoot_add_one, ih]
        simp only [hn', hs', ↓reduceIte]
        rw [feedbackCollapseZeroHold_other_cell p (show (n : ℤ) ≠ 0 by omega)]
        ring
  | negSucc n =>
    simp only [show ¬(0 : ℤ) < Int.negSucc n by omega, ↓reduceIte, add_zero]
    change -(∑ i ∈ Finset.range (n + 1), feedbackCellLength (p.1 (-((i : ℤ) + 1)))) =
      -(∑ i ∈ Finset.range (n + 1),
        feedbackCellLength (feedbackCollapseZeroHold p (-((i : ℤ) + 1))))
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro i _
    rw [feedbackCollapseZeroHold_other_cell p (show -((i : ℤ) + 1) ≠ 0 by omega)]

/-- The root translation formula holds under the actual conditioned stationary law. -/
theorem feedbackConditionalRoofLaw_roots_difference {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h, ∀ j : ℤ,
      feedbackCellRoot p.1 j = feedbackCellRoot (feedbackCollapseZeroHold p) j +
        if 0 < j then (p.1 0 1).1 - p.2 else 0 := by
  filter_upwards [feedbackConditionalRoofLaw_length_difference hlam0 hlam h hh] with p hp
  exact feedbackCollapseZeroHold_root_difference p hp

/-- On the negative half-line the original and collapsed cell indices coincide. -/
theorem feedbackCollapseZeroHold_index_neg (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {y : ℝ} (hy : y < 0) :
    feedbackCellIndex p.1 y = feedbackCellIndex (feedbackCollapseZeroHold p) y := by
  let j := feedbackCellIndex (feedbackCollapseZeroHold p) y
  have hb := feedbackCellIndex_bounds hc y
  have hj : j < 0 := by
    by_contra h
    have hr := (strictMono_feedbackCellRoot hc.1).monotone (show 0 ≤ j by omega)
    rw [feedbackCellRoot_zero] at hr
    linarith [hb.1]
  apply (feedbackCellIndex_eq_iff hw y j).mpr
  rw [feedbackCollapseZeroHold_root_difference p hL j,
    feedbackCollapseZeroHold_root_difference p hL (j + 1)]
  simpa only [show ¬0 < j by omega, show ¬0 < j + 1 by omega, ↓reduceIte, add_zero] using hb

/-- Before the distinguished return, collapse leaves the actual concatenated current unchanged. -/
theorem feedbackCollapseZeroHold_current_neg (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {y : ℝ} (hy : y < 0) :
    feedbackConcatenatedCurrent p.1 y =
      feedbackConcatenatedCurrent (feedbackCollapseZeroHold p) y := by
  let j := feedbackCellIndex (feedbackCollapseZeroHold p) y
  have hb := feedbackCellIndex_bounds hc y
  have hj : j < 0 := by
    by_contra h
    have hr := (strictMono_feedbackCellRoot hc.1).monotone (show 0 ≤ j by omega)
    rw [feedbackCellRoot_zero] at hr
    linarith [hb.1]
  simp only [feedbackConcatenatedCurrent, feedbackCollapseZeroHold_index_neg p hw hc hL hy]
  change feedbackCellCurrent (p.1 j) (y - feedbackCellRoot p.1 j) = _
  rw [feedbackCollapseZeroHold_root_difference p hL j,
    ite_eq_right (by omega : ¬0 < j), add_zero,
    feedbackCollapseZeroHold_other_cell p (show j ≠ 0 by omega)]

/-- Beyond cell zero, the original cell index is obtained by translating by the deleted residual. -/
theorem feedbackCollapseZeroHold_index_pos (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {y : ℝ}
    (hy : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ y) :
    feedbackCellIndex p.1 (y + ((p.1 0 1).1 - p.2)) =
      feedbackCellIndex (feedbackCollapseZeroHold p) y := by
  let j := feedbackCellIndex (feedbackCollapseZeroHold p) y
  have hb := feedbackCellIndex_bounds hc y
  have hj : 0 < j := by
    by_contra h
    have hr := (strictMono_feedbackCellRoot hc.1).monotone (show j + 1 ≤ 0 + 1 by omega)
    rw [feedbackCellRoot_add_one (feedbackCollapseZeroHold p) 0,
      feedbackCellRoot_zero, zero_add] at hr
    linarith [hb.2]
  apply (feedbackCellIndex_eq_iff hw _ j).mpr
  rw [feedbackCollapseZeroHold_root_difference p hL j,
    feedbackCollapseZeroHold_root_difference p hL (j + 1)]
  simp only [hj, show 0 < j + 1 by omega, ↓reduceIte]
  constructor <;> linarith [hb.1, hb.2]

/-- The positive-side current is exactly translated once the distinguished cell has ended. -/
theorem feedbackCollapseZeroHold_current_pos (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {y : ℝ}
    (hy : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ y) :
    feedbackConcatenatedCurrent p.1 (y + ((p.1 0 1).1 - p.2)) =
      feedbackConcatenatedCurrent (feedbackCollapseZeroHold p) y := by
  let j := feedbackCellIndex (feedbackCollapseZeroHold p) y
  have hb := feedbackCellIndex_bounds hc y
  have hj : 0 < j := by
    by_contra h
    have hr := (strictMono_feedbackCellRoot hc.1).monotone (show j + 1 ≤ 0 + 1 by omega)
    rw [feedbackCellRoot_add_one (feedbackCollapseZeroHold p) 0,
      feedbackCellRoot_zero, zero_add] at hr
    linarith [hb.2]
  simp only [feedbackConcatenatedCurrent, feedbackCollapseZeroHold_index_pos p hw hc hL hy]
  change feedbackCellCurrent (p.1 j)
    (y + ((p.1 0 1).1 - p.2) - feedbackCellRoot p.1 j) = _
  rw [feedbackCollapseZeroHold_root_difference p hL j, ite_eq_left hj]
  change feedbackCellCurrent (p.1 j) (_ - _) =
    feedbackCellCurrent (feedbackCollapseZeroHold p j) (y - _)
  rw [feedbackCollapseZeroHold_other_cell p (show j ≠ 0 by omega)]
  congr 1
  ring

/-- On a negative search interval the genuine zero-cut occupation is unchanged. -/
theorem feedbackCollapseZeroHold_zeroCut_volume_neg (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {a b : ℝ} (hb : b < 0) :
    volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut p.1 x} =
      volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut (feedbackCollapseZeroHold p) x} := by
  rw [volume_feedbackZeroCut_eq, volume_feedbackZeroCut_eq]
  apply congrArg (fun s : Set ℝ ↦ volume.real s)
  ext x
  by_cases hx : x ∈ Icc a b
  · simp only [mem_ofPred_eq, hx, true_and,
      feedbackCollapseZeroHold_current_neg p hw hc hL (hx.2.trans_lt hb)]
  · simp only [mem_ofPred_eq, hx, false_and]

/-- On a positive search interval the genuine zero-cut occupation is exactly translated. -/
theorem feedbackCollapseZeroHold_zeroCut_volume_pos (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {a b : ℝ}
    (ha : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ a) :
    volume.real {x | x ∈ Icc (a + ((p.1 0 1).1 - p.2)) (b + ((p.1 0 1).1 - p.2)) ∧
      FeedbackZeroCut p.1 x} =
      volume.real {x | x ∈ Icc a b ∧ FeedbackZeroCut (feedbackCollapseZeroHold p) x} := by
  rw [volume_feedbackZeroCut_eq, volume_feedbackZeroCut_eq]
  apply congrArg ENNReal.toReal
  rw [← measure_preimage_add_right (volume : Measure ℝ) ((p.1 0 1).1 - p.2)
    {x | x ∈ Icc (a + ((p.1 0 1).1 - p.2)) (b + ((p.1 0 1).1 - p.2)) ∧
      feedbackConcatenatedCurrent p.1 x = 0}]
  congr 1
  ext y
  change ((a + _ ≤ y + _ ∧ y + _ ≤ b + _) ∧ _) ↔ _
  simp only [add_le_add_iff_right]
  by_cases hy : y ∈ Icc a b
  · rw [feedbackCollapseZeroHold_current_pos p hw hc hL (ha.trans hy.1)]
    rfl
  · change ¬(a ≤ y ∧ y ≤ b) at hy
    simp only [mem_ofPred_eq, mem_Icc, hy, false_and]

/-- Opposite search cuts select exactly the same complete cell block before and after collapse. -/
theorem feedbackCollapseZeroHold_windowCells (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {a b : ℝ} (ha : a < 0)
    (hb : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ b) :
    feedbackWindowCells p.1 a (b + ((p.1 0 1).1 - p.2)) =
      feedbackWindowCells (feedbackCollapseZeroHold p) a b := by
  unfold feedbackWindowCells
  rw [feedbackCollapseZeroHold_index_neg p hw hc hL ha,
    feedbackCollapseZeroHold_index_pos p hw hc hL hb]

/-- The whole-window idle-free comparison budget is invariant under inserting the residual hold. -/
theorem feedbackCollapseZeroHold_windowReward (lam : ℝ) (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2)) {a b : ℝ} (ha : a < 0)
    (hb : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ b) :
    feedbackWindowReward lam p.1 a (b + ((p.1 0 1).1 - p.2)) =
      feedbackWindowReward lam (feedbackCollapseZeroHold p) a b := by
  unfold feedbackWindowReward
  rw [feedbackCollapseZeroHold_windowCells p hw hc hL ha hb]
  exact Finset.sum_congr rfl fun j _ ↦ (feedbackCollapseZeroHold_reward _ p j).symm

/-- Source populations in the original window are controlled by the same collapsed iid box. -/
theorem feedbackCollapseZeroHold_windowSourceCount_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellRootsGood p.1) (hc : feedbackCellRootsGood (feedbackCollapseZeroHold p))
    (hL : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2))
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k (feedbackCollapseZeroHold p))
    {a b : ℝ} (ha0 : a < 0) (hb0 : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ b)
    (ha : |a| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k)
    (hb : |b| < ((M : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * k) :
    feedbackWindowSourceCount p.1 a (b + ((p.1 0 1).1 - p.2)) ≤
      (2 * M * feedbackCellRegularityMean lam hlam0 hlam C 2 +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C 2)) * k := by
  have hs : feedbackWindowCells p.1 a (b + ((p.1 0 1).1 - p.2)) ⊆
      Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ) := by
    rw [feedbackCollapseZeroHold_windowCells p hw hc hL ha0 hb0]
    exact hgood.windowCells_subset hc ha hb
  apply (feedbackWindowSourceCount_le_sum hs).trans
  have heq : (∑ j ∈ Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ),
      (feedbackMarkedFirstReturnIndex (p.1 j) : ℝ)) =
      ∑ j ∈ Finset.Ico (-((M * k : ℕ) : ℤ)) ((M * k : ℕ) : ℤ),
        (feedbackMarkedFirstReturnIndex (feedbackCollapseZeroHold p j) : ℝ) := by
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (fun n : ℕ ↦ (n : ℝ))
      (feedbackCollapseZeroHold_returnIndex p j).symm
  rw [heq]
  exact hgood.box_sum_le 2

/-- All geometric support facts needed for conditional window transfer hold under the true law. -/
theorem feedbackConditionalRoofLaw_geometry {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h,
      feedbackCellConfigurationGood p.1 ∧
      feedbackCellConfigurationGood (feedbackCollapseZeroHold p) ∧
      (∀ j, (feedbackCollapseZeroHold p j 0).2.2 = 0) ∧
      feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
        ((p.1 0 1).1 - p.2) ∧
      h ≤ (p.1 0 1).1 - p.2 ∧ (p.1 0 1).1 - p.2 ≤ h + 1 := by
  have hband : ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h,
      p ∈ feedbackRoofHoldBand lam h :=
    Measure.ae_smul_measure (ae_restrict_mem (measurableSet_feedbackRoofHoldBand lam h)) _
  filter_upwards [feedbackConditionalRoofLaw_ae_base hlam0 hlam h
      (feedbackCellBase_configuration_good hlam0 hlam),
    feedbackConditionalRoofLaw_ae_collapsed hlam0 hlam h hh
      (feedbackCellBase_identification_good hlam0 hlam),
    feedbackConditionalRoofLaw_length_difference hlam0 hlam h hh, hband] with p hw hc hL hb
  exact ⟨hw, hc.1, hc.2.2.1, hL, hb.1.1, hb.1.2⟩

end OTSelector.Limit
