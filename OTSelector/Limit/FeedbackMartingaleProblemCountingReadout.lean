import OTSelector.PointProcess.LocalConfigurationFirstEvent
import OTSelector.Feedback.FeedbackI3ConditionalGap
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Reading marked counts at the first actual event

The test count integrates a geometric mark test against the actual configuration counting
measure. Its stopped readout follows from the first-event restriction identity. Local
finiteness also makes every such count locally constant immediately to the right of each time.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.PointProcess.LocalConfiguration

attribute [local instance] Classical.propDecidable

/-- The actual count of one color in `(0,t]`, weighted by its geometric mark. -/
noncomputable def firstEventTestCount (c : TwoColor) (b : Bool)
    (ψ : UnitMark → ℝ) (t : ℝ) : ℝ :=
  ∫ p in spatialIoc 0 t, ψ p.2 ∂countingMeasure (c b)

@[simp]
theorem firstEventTestCount_zero (c : TwoColor) (b : Bool) (ψ : UnitMark → ℝ) :
    firstEventTestCount c b ψ 0 = 0 := by
  simp [firstEventTestCount, spatialIoc]

/-- The constant-one mark test is the actual integer-valued interval count. -/
theorem firstEventTestCount_one (c : TwoColor) (b : Bool) (t : ℝ) :
    firstEventTestCount c b (fun _ ↦ 1) t = (spatialCount (c b) 0 t : ℝ) := by
  rw [firstEventTestCount, spatialCount_cast]
  simp

/-- On every smaller observation window, the marked count is controlled by the unweighted
count at the horizon. This supplies an envelope from the original constant-one martingale. -/
theorem norm_firstEventTestCount_le (c : TwoColor) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    ‖firstEventTestCount c b ψ s‖ ≤ ‖ψ‖ * (spatialCount (c b) 0 t : ℝ) := by
  rw [firstEventTestCount, spatialCount_cast]
  calc
    ‖∫ p in spatialIoc 0 s, ψ p.2 ∂countingMeasure (c b)‖ ≤
        ‖ψ‖ * (countingMeasure (c b)).real (spatialIoc 0 s) :=
      norm_setIntegral_le_of_norm_le_const
        (countingMeasure_lt_top_of_isBounded (c b) (isBounded_spatialIoc 0 s))
        (fun p _ ↦ ψ.norm_coe_le_norm p.2)
    _ ≤ ‖ψ‖ * (countingMeasure (c b)).real (spatialIoc 0 t) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg ψ)
      exact measureReal_mono (fun _ hp ↦ ⟨hp.1, hp.2.trans hst⟩)
        (countingMeasure_lt_top_of_isBounded (c b) (isBounded_spatialIoc 0 t)).ne

/-- The readout is valid for every mark function: the stopped measure is zero or a Dirac
measure, so no extra measurability or integrability premise is needed. -/
theorem firstEventTestCount_min (c : TwoColor) (hc : IsTimeSimple c) (b : Bool)
    (ψ : UnitMark → ℝ) (t : ℝ) :
    firstEventTestCount c b ψ (min (ENNReal.ofReal t) (firstPositiveTime c)).toReal =
      if firstPositiveTime c ≤ ENNReal.ofReal t ∧ (firstPositiveEvent c).1 = b
        then ψ (firstPositiveEvent c).2.2 else 0 := by
  unfold firstEventTestCount
  rw [countingMeasure_restrict_firstPositiveTime c hc b t]
  split_ifs <;> simp

private theorem firstEvent_cappedStoppingValue_coe (c : TwoColor) (t : ℝ≥0) :
    (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ firstPositiveTime c) () : ℝ) =
      (min (ENNReal.ofReal (t : ℝ)) (firstPositiveTime c)).toReal := by
  have h := congrArg ENNReal.toReal (CountingProcess.coe_cappedStoppingValue t
    (fun _ : Unit ↦ firstPositiveTime c) ())
  change (CountingProcess.cappedStoppingValue t
    (fun _ : Unit ↦ firstPositiveTime c) () : ℝ) =
      (min (firstPositiveTime c) (t : ℝ≥0∞)).toReal at h
  rw [ENNReal.ofReal_coe_nnreal, min_comm]
  exact h

/-- The continuous-test count stopped at the actual first event reads its selected mark. -/
theorem firstEventTestCount_capped (c : TwoColor) (hc : IsTimeSimple c) (b : Bool)
    (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    firstEventTestCount c b ψ
        (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ firstPositiveTime c) () : ℝ) =
      if firstPositiveTime c ≤ ENNReal.ofReal (t : ℝ) ∧ (firstPositiveEvent c).1 = b
        then ψ (firstPositiveEvent c).2.2 else 0 := by
  rw [firstEvent_cappedStoppingValue_coe]
  exact firstEventTestCount_min c hc b ψ t

/-- A stopped continuous-test count is bounded by the uniform norm of its mark test. -/
theorem norm_firstEventTestCount_capped_le (c : TwoColor) (hc : IsTimeSimple c) (b : Bool)
    (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    ‖firstEventTestCount c b ψ
      (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ firstPositiveTime c) () : ℝ)‖ ≤
      ‖ψ‖ := by
  rw [firstEventTestCount_capped c hc b ψ t]
  split_ifs
  · exact ψ.norm_coe_le_norm _
  · simpa only [norm_zero] using norm_nonneg ψ

/-- There is a nonempty interval immediately after each cut containing no actual points.
The proof reroots the existing first-positive-time construction. -/
theorem exists_right_gap_countingMeasure (c : TwoColor) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : Bool, countingMeasure (c b) (spatialIoc t (t + δ)) = 0 := by
  let shifted : TwoColor := fun b ↦ reroot t (c b)
  obtain ⟨δ, _, hδ0, hδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp
    (firstPositiveTime_pos shifted)
  refine ⟨δ, ENNReal.ofReal_pos.mp hδ0, fun b ↦ ?_⟩
  have hcount := spatialCount_eq_zero_before_firstPositiveTime shifted b hδ
  change spatialCount (reroot t (c b)) 0 δ = 0 at hcount
  rw [spatialCount_reroot, zero_add, add_comm δ t] at hcount
  apply (countingMeasure_eq_zero_iff (c b) (measurableSet_spatialIoc _ _)).mpr
  intro p hp
  by_contra hm
  have hpos := (spatialCount_pos_iff (c b) t (t + δ)).mpr ⟨p, hp, hm⟩
  omega

/-- Right local constancy is a property of the actual locally finite counting measure,
and holds even for mark tests without any regularity assumption. -/
theorem eventually_firstEventTestCount_eq (c : TwoColor) (b : Bool)
    (ψ : UnitMark → ℝ) (t : ℝ) :
    (fun s ↦ firstEventTestCount c b ψ s) =ᶠ[𝓝[≥] t]
      (fun _ ↦ firstEventTestCount c b ψ t) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_right_gap_countingMeasure c t
  filter_upwards [Ico_mem_nhdsGE (show t < t + δ by linarith)] with s hs
  apply setIntegral_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hgap b)] with p hp
  apply propext
  change (0 < p.1 ∧ p.1 ≤ s) ↔ (0 < p.1 ∧ p.1 ≤ t)
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hpt
    exact hp ⟨lt_of_not_ge hpt, h.2.trans hs.2.le⟩
  · intro h
    exact ⟨h.1, h.2.trans hs.1⟩

/-- Every actual marked-count path is right continuous. -/
theorem continuousWithinAt_firstEventTestCount (c : TwoColor) (b : Bool)
    (ψ : UnitMark → ℝ) (t : ℝ) :
    ContinuousWithinAt (fun s ↦ firstEventTestCount c b ψ s) (Ici t) t :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventually_firstEventTestCount_eq c b ψ t) rfl

/-- The same right continuity on the nonnegative time carrier used by the martingale problem. -/
theorem continuousWithinAt_firstEventTestCount_nnreal (c : TwoColor) (b : Bool)
    (ψ : UnitMark → ℝ) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 ↦ firstEventTestCount c b ψ s) (Ici t) t := by
  exact (continuousWithinAt_firstEventTestCount c b ψ (t : ℝ)).comp
    continuous_subtype_val.continuousWithinAt (fun _ hs ↦ hs)

end OTSelector.PointProcess.LocalConfiguration
