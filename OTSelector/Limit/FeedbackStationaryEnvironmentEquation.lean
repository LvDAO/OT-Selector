import OTSelector.Limit.FeedbackEnvironmentIdentification
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentReadout
import Mathlib.Topology.DenseEmbedding

/-!
# The actual stationary environment satisfies its graph equation

The velocity is a bounded measurable function of the current read from the two configurations.
The proved integral equation for every reroot of the concatenated environment therefore passes
through the actual occupation law. Rational cuts and continuity yield one full-measure event on
which the equation holds at every real cut.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

/-- The velocity read from the actual environment is jointly measurable. -/
theorem measurable_feedbackEnvironmentVelocity (lam : ℝ) :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦
      lam * currentSign (feedbackEnvironmentCurrent p.2 p.1)) :=
  measurable_const.mul ((measurable_of_countable currentSign).comp
    measurable_feedbackEnvironmentCurrent)

/-- The actual feedback velocity has the uniform bound `|lam|`. -/
theorem norm_feedbackEnvironmentVelocity_le (lam : ℝ) (e : FeedbackEnvironment) (s : ℝ) :
    ‖lam * currentSign (feedbackEnvironmentCurrent e s)‖ ≤ |lam| := by
  have hs (k : ℤ) : ‖currentSign k‖ ≤ 1 := by
    cases k with
    | ofNat n => cases n <;> norm_num [currentSign]
    | negSucc n => norm_num [currentSign]
  rw [norm_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hs _) (abs_nonneg lam)).trans_eq (mul_one _)

/-- On every finite interval, the actual feedback velocity is integrable. -/
theorem intervalIntegrable_feedbackEnvironmentVelocity
    (lam : ℝ) (e : FeedbackEnvironment) (a b : ℝ) :
    IntervalIntegrable (fun s ↦ lam * currentSign (feedbackEnvironmentCurrent e s)) volume a b := by
  have hi : Measurable (fun s : ℝ ↦ (s, e)) := measurable_id.prodMk measurable_const
  have hm := (measurable_feedbackEnvironmentVelocity lam).comp hi
  apply (intervalIntegrable_const (c := |lam|)).mono_fun' hm.aestronglyMeasurable
  exact Eventually.of_forall (norm_feedbackEnvironmentVelocity_le lam e)

/-- The graph reconstructed by integrating the actual current is continuous at every cut. -/
theorem continuous_feedbackEnvironmentIntegral (lam : ℝ) (e : FeedbackEnvironment) :
    Continuous (fun t : ℝ ↦ ∫ s in 0..t,
      lam * currentSign (feedbackEnvironmentCurrent e s)) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_feedbackEnvironmentVelocity lam e) 0

/-- At each fixed cut the reconstructed graph is a measurable environment observable. -/
theorem measurable_feedbackEnvironmentIntegral (lam t : ℝ) :
    Measurable (fun e : FeedbackEnvironment ↦ ∫ s in 0..t,
      lam * currentSign (feedbackEnvironmentCurrent e s)) := by
  have hm : Measurable (fun p : FeedbackEnvironment × ℝ ↦
      lam * currentSign (feedbackEnvironmentCurrent p.1 p.2)) :=
    (measurable_feedbackEnvironmentVelocity lam).comp measurable_swap
  exact ((hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) t))).sub
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc t (0 : ℝ))))).measurable

/-- At each cut, the actual stationary graph obeys the equation of its observable current. -/
theorem ae_feedbackStationaryEnvironment_integral_at {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (t : ℝ) :
    ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam,
      e.path.graphHeight t = ∫ s in 0..t, lam * currentSign (feedbackEnvironmentCurrent e s) := by
  have hi : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      (p.2, feedbackConcatenatedEnvironment lam p.1)) :=
    measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst)
  have hm := FeedbackEnvironment.measurable_uncurry_reroot.comp hi
  have heq : MeasurableSet {e : FeedbackEnvironment |
      e.path.graphHeight t = ∫ s in 0..t, lam * currentSign (feedbackEnvironmentCurrent e s)} :=
    measurableSet_eq_fun
      ((GraphHeight.continuous_apply t).measurable.comp FeedbackEnvironment.measurable_graphHeight)
      (measurable_feedbackEnvironmentIntegral lam t)
  unfold feedbackStationaryEnvironmentLaw renewalStationaryLaw
  apply Measure.ae_smul_measure
  unfold renewalOccupation
  apply (ae_map_iff hm.aemeasurable heq).mpr
  apply ae_restrict_of_ae
  have hbase : ∀ᵐ p : FeedbackCellSequence × ℝ ∂(feedbackCellBase lam hlam0 hlam).prod volume,
      ∀ a x : ℝ,
        (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam p.1)).path.graphHeight x =
          ∫ s in 0..x, lam * currentSign (feedbackEnvironmentCurrent
            (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam p.1)) s) :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_feedbackConcatenatedEnvironment_reroot_integral hlam0 hlam)
  filter_upwards [hbase] with p hp
  exact hp p.2 t

/-- One full-measure event carries the true feedback graph equation at every real cut. -/
theorem ae_feedbackStationaryEnvironment_integral {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam, ∀ t : ℝ,
      e.path.graphHeight t = ∫ s in 0..t, lam * currentSign (feedbackEnvironmentCurrent e s) := by
  have hrat : ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam, ∀ q : ℚ,
      e.path.graphHeight q = ∫ s in 0..(q : ℝ),
        lam * currentSign (feedbackEnvironmentCurrent e s) :=
    ae_all_iff.mpr (fun q ↦ ae_feedbackStationaryEnvironment_integral_at hlam0 hlam q)
  filter_upwards [hrat] with e he
  have hfun : (fun t : ℝ ↦ e.path.graphHeight t) =
      (fun t : ℝ ↦ ∫ s in 0..t, lam * currentSign (feedbackEnvironmentCurrent e s)) :=
    Rat.denseRange_cast.equalizer e.path.graphHeight.continuous
      (continuous_feedbackEnvironmentIntegral lam e) (funext he)
  exact congrFun hfun

end OTSelector.Limit
