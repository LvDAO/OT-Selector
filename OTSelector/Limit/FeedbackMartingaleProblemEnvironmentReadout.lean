import OTSelector.Limit.FeedbackMartingaleProblemStoppedTest
import OTSelector.Limit.FeedbackMartingaleProblemMarkRate
import OTSelector.PointProcess.LocalConfigurationFirstEvent
import OTSelector.PointProcess.FeedbackEnvironment

/-!
# Actual first-event readouts of a feedback environment

The first event is selected from the real two point configurations. Its time, color and mark
are measurable; its stopping event is the revealed counting event. Before that event, the
current read from the actual source-minus-target count is exactly the root current.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

/-- The actual source and target configurations, with `true` denoting source. -/
def feedbackEnvironmentTwoColor (e : FeedbackEnvironment) : LocalConfiguration.TwoColor :=
  fun b ↦ if b then e.source else e.target

theorem measurable_feedbackEnvironmentTwoColor : Measurable feedbackEnvironmentTwoColor := by
  apply measurable_pi_lambda
  intro b
  cases b
  · exact FeedbackEnvironment.measurable_target
  · exact FeedbackEnvironment.measurable_source

/-- The first strictly positive event time of the bare environment, possibly infinite. -/
noncomputable def feedbackEnvironmentFirstTime (e : FeedbackEnvironment) : ℝ≥0∞ :=
  LocalConfiguration.firstPositiveTime (feedbackEnvironmentTwoColor e)

theorem measurable_feedbackEnvironmentFirstTime : Measurable feedbackEnvironmentFirstTime :=
  LocalConfiguration.measurable_firstPositiveTime.comp measurable_feedbackEnvironmentTwoColor

/-- The measurable first colored atom of the actual environment. -/
noncomputable def feedbackEnvironmentFirstEvent (e : FeedbackEnvironment) : Bool × MatchingPoint :=
  LocalConfiguration.firstPositiveEvent (feedbackEnvironmentTwoColor e)

theorem measurable_feedbackEnvironmentFirstEvent : Measurable feedbackEnvironmentFirstEvent :=
  LocalConfiguration.measurable_firstPositiveEvent.comp measurable_feedbackEnvironmentTwoColor

/-- The observable current at a spatial cut is the root current plus the actual integer count
increment of the two point configurations. -/
noncomputable def feedbackEnvironmentCurrent (e : FeedbackEnvironment) (x : ℝ) : ℤ :=
  e.path.rootCurrent + e.currentIncrement 0 x

/-- The observable current is jointly measurable in the cut and the environment. -/
theorem measurable_feedbackEnvironmentCurrent :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦ feedbackEnvironmentCurrent p.2 p.1) := by
  exact FeedbackEnvironment.measurable_rootCurrent.comp
    FeedbackEnvironment.measurable_uncurry_reroot

/-- The selected first mark together with the current after its color increment. -/
noncomputable def feedbackEnvironmentFirstJump (e : FeedbackEnvironment) : UnitMark × ℤ :=
  ((feedbackEnvironmentFirstEvent e).2.2,
    e.path.rootCurrent + if (feedbackEnvironmentFirstEvent e).1 then 1 else -1)

theorem measurable_feedbackEnvironmentFirstJump : Measurable feedbackEnvironmentFirstJump := by
  apply Measurable.prodMk
  · exact measurable_feedbackEnvironmentFirstEvent.snd.snd
  · exact FeedbackEnvironment.measurable_rootCurrent.add
      (measurable_const.ite
        (measurableSet_eq_fun measurable_feedbackEnvironmentFirstEvent.fst measurable_const)
        measurable_const)

/-- Before the first actual event, both forward counting configurations are empty and the
observable current equals the root current. -/
theorem feedbackEnvironmentCurrent_before_first (e : FeedbackEnvironment) {x : ℝ}
    (hx : 0 ≤ x) (hfirst : ENNReal.ofReal x < feedbackEnvironmentFirstTime e) :
    feedbackEnvironmentCurrent e x = e.path.rootCurrent := by
  have hnot : ¬1 ≤ LocalConfiguration.spatialCount e.source 0 x +
      LocalConfiguration.spatialCount e.target 0 x := by
    intro h
    have he := (LocalConfiguration.firstPositiveTime_le_iff
      (feedbackEnvironmentTwoColor e) hx).mpr h
    exact (not_le_of_gt hfirst) he
  have hs := LocalConfiguration.spatialCount_nonneg e.source 0 x
  have ht := LocalConfiguration.spatialCount_nonneg e.target 0 x
  have hs0 : LocalConfiguration.spatialCount e.source 0 x = 0 := by omega
  have ht0 : LocalConfiguration.spatialCount e.target 0 x = 0 := by omega
  simp [feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement,
    LocalConfiguration.orientedCount, hs0, ht0,
    LocalConfiguration.spatialCount_eq_zero_of_le _ hx]

/-- The actual first positive event is a stopping time whenever the revealed aggregate count
is adapted. No stopping-time property is assumed for the selected event. -/
theorem feedbackEnvironmentFirstTime_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (e : Ω → FeedbackEnvironment)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t)) :
    IsStoppingTime ℱ (fun ω ↦ feedbackEnvironmentFirstTime (e ω)) := by
  intro t
  change MeasurableSet[ℱ t] {ω | feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞)}
  have he : {ω | feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞)} =
      {ω | 1 ≤ LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t} := by
    ext ω
    exact (by simpa [feedbackEnvironmentFirstTime, feedbackEnvironmentTwoColor, ENNReal.ofReal_coe_nnreal] using
      LocalConfiguration.firstPositiveTime_le_iff (feedbackEnvironmentTwoColor (e ω)) t.property)
  rw [he]
  exact measurableSet_le measurable_const (hcount t)

/-- Integrating any state rate up to the actual first event freezes it at the root current.
The endpoint contributes zero Lebesgue measure. -/
theorem integral_feedbackEnvironmentCurrent_capped_first
    (e : FeedbackEnvironment) (g : ℤ → ℝ) (t : ℝ≥0) :
    (∫ s in 0..(CountingProcess.cappedStoppingValue t
      (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) () : ℝ),
      g (feedbackEnvironmentCurrent e s)) =
    g e.path.rootCurrent *
      ∫ s in 0..(t : ℝ), if ENNReal.ofReal s < feedbackEnvironmentFirstTime e
        then (1 : ℝ) else 0 := by
  let c := CountingProcess.cappedStoppingValue t
    (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ()
  have hc : (c : ℝ≥0∞) ≤ feedbackEnvironmentFirstTime e := by
    have he := CountingProcess.coe_cappedStoppingValue t
      (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ()
    change (c : ℝ≥0∞) = min (feedbackEnvironmentFirstTime e) (t : ℝ≥0∞) at he
    exact he.trans_le (min_le_left _ _)
  have heq : (∫ s in 0..(c : ℝ), g (feedbackEnvironmentCurrent e s)) =
      ∫ s in 0..(c : ℝ), g e.path.rootCurrent := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (c : ℝ) by
      simp [ae_iff]] with s hs
    intro hst
    have hst' : 0 < s ∧ s ≤ (c : ℝ) := by
      simpa only [uIoc_of_le (show (0 : ℝ) ≤ c from c.property), mem_Ioc] using hst
    have hlt : ENNReal.ofReal s < (c : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg hst'.1.le]
      exact lt_of_le_of_ne hst'.2 hs
    rw [feedbackEnvironmentCurrent_before_first e hst'.1.le (hlt.trans_le hc)]
  rw [integral_firstJump_survival_eq_cappedStoppingValue]
  change (∫ s in 0..(c : ℝ), g (feedbackEnvironmentCurrent e s)) =
    g e.path.rootCurrent * (c : ℝ)
  rw [heq]
  simp [mul_comm]

end OTSelector.Limit
