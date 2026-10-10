import OTSelector.Limit.FeedbackZeroHold

/-!
# Spatial translation of the actual stationary roof

Moving the observation point selects its actual containing cell, shifts that cell to index zero,
and subtracts its root from the observation coordinate. The occupation cancellation theorem
proves invariance of the actual normalized roof law under this concrete map.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace OTSelector.Limit

set_option maxHeartbeats 800000

/-- Translate the observation point and reindex its actual containing cell to zero. -/
noncomputable def feedbackRoofFlow (t : ℝ) (p : FeedbackCellSequence × ℝ) :
    FeedbackCellSequence × ℝ :=
  let k := feedbackCellIndex p.1 (p.2 + t)
  (IIDShift.shift k p.1, p.2 + t - feedbackCellRoot p.1 k)

@[fun_prop]
theorem measurable_feedbackRoofFlow :
    Measurable (fun q : ℝ × (FeedbackCellSequence × ℝ) ↦ feedbackRoofFlow q.1 q.2) := by
  have hshift : Measurable (fun q : FeedbackCellSequence × ℤ ↦ IIDShift.shift q.2 q.1) := by
    apply measurable_from_prod_countable_left
    exact IIDShift.measurable_shift
  have hroot : Measurable (fun q : FeedbackCellSequence × ℤ ↦ feedbackCellRoot q.1 q.2) := by
    apply measurable_from_prod_countable_left
    exact measurable_feedbackCellRoot
  have hk := measurable_feedbackCellIndex.comp
    (measurable_snd.fst.prodMk (measurable_snd.snd.add measurable_fst))
  exact (hshift.comp (measurable_snd.fst.prodMk hk)).prodMk
    ((measurable_snd.snd.add measurable_fst).sub
      (hroot.comp (measurable_snd.fst.prodMk hk)))

/-- Translation composes exactly, including the totalized behavior on invalid cell sequences. -/
theorem feedbackRoofFlow_add (a b : ℝ) (p : FeedbackCellSequence × ℝ) :
    feedbackRoofFlow a (feedbackRoofFlow b p) = feedbackRoofFlow (a + b) p := by
  by_cases hw : feedbackCellRootsGood p.1
  · let k := feedbackCellIndex p.1 (p.2 + b)
    have hidx : feedbackCellIndex (IIDShift.shift k p.1)
        (p.2 + b - feedbackCellRoot p.1 k + a) =
          feedbackCellIndex p.1 (p.2 + (a + b)) - k := by
      rw [show p.2 + b - feedbackCellRoot p.1 k + a =
        (p.2 + (a + b)) - feedbackCellRoot p.1 k by ring]
      exact feedbackCellIndex_shift hw k _
    change (IIDShift.shift (feedbackCellIndex (IIDShift.shift k p.1)
        (p.2 + b - feedbackCellRoot p.1 k + a)) (IIDShift.shift k p.1),
      p.2 + b - feedbackCellRoot p.1 k + a -
        feedbackCellRoot (IIDShift.shift k p.1)
          (feedbackCellIndex (IIDShift.shift k p.1)
            (p.2 + b - feedbackCellRoot p.1 k + a))) = _
    rw [hidx, ← IIDShift.shift_add, feedbackCellRoot_shift, sub_add_cancel]
    unfold feedbackRoofFlow
    congr 1
    ring
  · simp only [feedbackRoofFlow, feedbackCellIndex, hw, ↓reduceIte,
      IIDShift.shift_zero, feedbackCellRoot_zero, sub_zero]
    congr 1
    ring

/-- No cell reindexing occurs while the observation remains inside cell zero. -/
theorem feedbackRoofFlow_eq_of_initial_cell {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) {u : ℝ} (hu : u ∈ Ico 0 (feedbackCellLength (w 0))) :
    feedbackRoofFlow u (w, 0) = (w, u) := by
  have hk : feedbackCellIndex w u = 0 := (feedbackCellIndex_eq_iff hw u 0).mpr (by
    have hr : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
      simpa using feedbackCellRoot_add_one w 0
    simpa only [mem_Ico, zero_add, feedbackCellRoot_zero, hr] using hu)
  simp only [feedbackRoofFlow, zero_add, hk, IIDShift.shift_zero, feedbackCellRoot_zero, sub_zero]

/-- At the first roof endpoint the actual next cell becomes the new zero cell. -/
theorem feedbackRoofFlow_cellLength {w : FeedbackCellSequence} (hw : feedbackCellRootsGood w) :
    feedbackRoofFlow (feedbackCellLength (w 0)) (w, 0) = (IIDShift.shift 1 w, 0) := by
  have hr : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
    simpa using feedbackCellRoot_add_one w 0
  have hk : feedbackCellIndex w (feedbackCellLength (w 0)) = 1 :=
    (feedbackCellIndex_eq_iff hw _ 1).mpr ⟨hr.le.ge, by
      rw [feedbackCellRoot_add_one, hr]
      exact lt_add_of_pos_right _ (hw.1 1)⟩
  simp only [feedbackRoofFlow, zero_add, hk, hr, sub_self]

/-- Occupation of this concrete flow is exactly the original stationary roof law. -/
theorem feedbackRoofFlow_stationaryLaw_eq {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
      (fun w ↦ feedbackCellLength (w 0)) (fun q ↦ feedbackRoofFlow q.1 q.2)
      (fun w ↦ (w, 0)) = feedbackStationaryRoofLaw lam hlam0 hlam := by
  rw [renewalStationaryLaw, integral_feedbackCellBase_length, feedbackStationaryRoofLaw]
  congr 1
  unfold renewalOccupation
  have he : (fun p : FeedbackCellSequence × ℝ ↦ feedbackRoofFlow p.2 (p.1, 0)) =ᵐ[
      renewalRoofMeasure (feedbackCellBase lam hlam0 hlam) (fun w ↦ feedbackCellLength (w 0))] id := by
    have hgood := (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure ℝ))).ae
      (feedbackCellBase_roots_good hlam0 hlam)
    have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
        0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} :=
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd
          (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hroof] with p hw hp
    exact feedbackRoofFlow_eq_of_initial_cell hw hp
  rw [Measure.map_congr he, Measure.map_id]

/-- Every real translation preserves the actual stationary roof probability measure. -/
theorem measurePreserving_feedbackRoofFlow {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (t : ℝ) :
    MeasurePreserving (feedbackRoofFlow t) (feedbackStationaryRoofLaw lam hlam0 hlam)
      (feedbackStationaryRoofLaw lam hlam0 hlam) := by
  rw [← feedbackRoofFlow_stationaryLaw_eq hlam0 hlam]
  apply measurePreserving_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
    (integrable_feedbackCellBase_length hlam0 hlam 0)
    ((feedbackCellBase_lengths_positive hlam0 hlam).mono fun _ hw ↦ hw 0)
    (IIDShift.measurePreserving_shift (feedbackMarkedTrajectory lam hlam0 hlam 0) 1)
    measurable_feedbackRoofFlow (measurable_id.prodMk measurable_const)
    feedbackRoofFlow_add
  exact (feedbackCellBase_roots_good hlam0 hlam).mono fun _ hw ↦
    (feedbackRoofFlow_cellLength hw).symm

/-- The concrete translated roof reconstructs precisely the spatially rerooted environment. -/
theorem feedbackRoofFlow_environment_ae {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ p ∂feedbackStationaryRoofLaw lam hlam0 hlam, ∀ t : ℝ,
      feedbackRoofEnvironment lam (feedbackRoofFlow t p) =
        PointProcess.FeedbackEnvironment.reroot t (feedbackRoofEnvironment lam p) := by
  apply Measure.ae_smul_measure
  apply ae_restrict_of_ae
  have hw := (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure ℝ))).ae
    (ae_feedbackConcatenatedEnvironment_shift hlam0 hlam)
  filter_upwards [hw] with p hp t
  change PointProcess.FeedbackEnvironment.reroot
      (p.2 + t - feedbackCellRoot p.1 (feedbackCellIndex p.1 (p.2 + t)))
      (feedbackConcatenatedEnvironment lam (IIDShift.shift (feedbackCellIndex p.1 (p.2 + t)) p.1)) = _
  rw [hp, feedbackRoofEnvironment, PointProcess.FeedbackEnvironment.reroot_add,
    PointProcess.FeedbackEnvironment.reroot_add]
  congr 1
  ring

end OTSelector.Limit
