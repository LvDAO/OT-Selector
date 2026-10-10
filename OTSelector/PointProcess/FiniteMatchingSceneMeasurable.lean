import OTSelector.PointProcess.FiniteMatchingScene
import OTSelector.Feedback.StateMeasurable
import OTSelector.Probability.SpatialAveraging

/-!
# Measurability of the actual finite rooted scene

The recursive curve, the capped A1 stopping coordinate, and the unique intersections are
measurable in the original finite sample.  The original Euclidean optimizer is only known to be
almost everywhere measurable; consequently its actual rooted scene has that same exact contract.
-/

open MeasureTheory Set Function
open scoped BigOperators Classical ENNReal NNReal
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.PointProcess.GraphHeight

/-- Rational evaluations determine a continuous graph height and form a measurable embedding. -/
theorem measurableEmbedding_rationalValues :
    MeasurableEmbedding (fun g : GraphHeight ↦ fun q : ℚ ↦ g (q : ℝ)) := by
  have hm : Measurable (fun g : GraphHeight ↦ fun q : ℚ ↦ g (q : ℝ)) :=
    measurable_pi_iff.mpr fun q ↦ (continuous_apply (q : ℝ)).measurable
  apply hm.measurableEmbedding
  intro g h heq
  apply ContinuousMapZero.ext
  exact congrFun (Rat.denseRange_cast.equalizer (map_continuous g) (map_continuous h) heq)

/-- The graph-height Borel structure can be checked on countably many actual evaluations. -/
theorem measurable_of_eval {Ω : Type*} [MeasurableSpace Ω] {f : Ω → GraphHeight}
    (hf : ∀ x : ℝ, Measurable (fun ω ↦ f ω x)) : Measurable f := by
  apply measurableEmbedding_rationalValues.measurable_comp_iff.mp
  exact measurable_pi_iff.mpr fun q ↦ hf q

end OTSelector.PointProcess.GraphHeight

namespace OTSelector.FiniteSample

variable {n : ℕ}

private theorem measurable_feedbackCurveAux_joint (lam x0 p0 : ℝ) (H : ℕ) :
    ∀ m, Measurable (fun p : FiniteSample n × ℝ ↦ p.1.feedbackCurveAux lam x0 p0 H m p.2) := by
  suffices h : ∀ d m, H - m = d → Measurable
      (fun p : FiniteSample n × ℝ ↦ p.1.feedbackCurveAux lam x0 p0 H m p.2) from
    fun m ↦ h (H - m) m rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro m hdm
      have hfst : Measurable (Prod.fst : FiniteSample n × ℝ → FiniteSample n) := measurable_fst
      have hx := (measurable_feedbackKnot (n := n) lam x0 p0 m).comp hfst
      have hp := (measurable_feedbackKnotValue (n := n) lam x0 p0 m).comp hfst
      have hnext := (measurable_feedbackKnot (n := n) lam x0 p0 (m + 1)).comp hfst
      have hq := ((FeedbackStepState.measurable_slope lam).comp
        (measurable_feedbackState (n := n) lam x0 p0 m)).comp hfst
      by_cases hm : m < H
      · conv => arg 1; ext p; rw [feedbackCurveAux, dite_eq_left hm]
        exact (hp.add (hq.mul (measurable_snd.sub hx))).ite
          (measurableSet_le measurable_snd hnext)
          (ih (H - (m + 1)) (by omega) (m + 1) rfl)
      · conv => arg 1; ext p; rw [feedbackCurveAux, dite_eq_right hm]
        exact hp

/-- The actual recursive graph curve is jointly measurable in sample and spatial coordinate. -/
theorem measurable_feedbackCurve_joint (lam x0 p0 : ℝ) :
    Measurable (fun p : FiniteSample n × ℝ ↦ p.1.feedbackCurve lam x0 p0 p.2) := by
  exact measurable_const.ite (measurableSet_le measurable_snd measurable_const)
    (measurable_feedbackCurveAux_joint lam x0 p0 (2 * n) 0)

/-- The finite A1 elapsed stopping coordinate is measurable in the original sample space. -/
theorem measurable_safeFeedbackA1StopElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) :
    Measurable (fun sample : FiniteSample n ↦
      sample.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T) := by
  have h := (safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta B 0 T).measurable'.untopD 0
  convert h using 1
  funext sample
  rw [← sample.coe_safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T]
  rfl

/-- The actual stopped graph is jointly measurable without conditioning on survival. -/
theorem measurable_stoppedContinuationFeedbackGraph_curve_joint
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) :
    Measurable (fun p : FiniteSample n × ℝ ↦
      (p.1.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve p.2) := by
  have htime := (measurable_safeFeedbackA1StopElapsed (n := n) hlam0 hlamHalf hB eta T).coe_nnreal_real
  have hclip : Measurable (fun p : FiniteSample n × ℝ ↦
      max B (min (B + (p.1.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T : ℝ)) p.2)) :=
    measurable_const.max ((measurable_const.add (htime.comp measurable_fst)).min measurable_snd)
  exact (measurable_feedbackCurve_joint lam B 0).comp (measurable_fst.prodMk hclip)

/-- The implicit source root is measurable whenever its actual graph evaluations are. -/
theorem measurable_sourceIntersection_of_curve {lam : ℝ}
    (graph : FiniteSample n → FeedbackGraph lam)
    (hgraph : ∀ x, Measurable (fun sample ↦ (graph sample).curve x)) (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.sourceIntersection (graph sample) i) := by
  apply measurable_of_Iic
  intro x
  have hphase : Measurable (fun sample : FiniteSample n ↦
      sample.sourcePhase i ((graph sample).curve x)) :=
    (measurable_const.mul (measurable_sourceHeight i).subtype_coe).add
      ((measurable_const.sub (measurable_sourceMark i).subtype_coe).mul (hgraph x))
  have heq : (fun sample : FiniteSample n ↦ sample.sourceIntersection (graph sample) i) ⁻¹'
      Iic x = {sample | sample.sourcePhase i ((graph sample).curve x) ≤ x} := by
    ext sample
    exact sample.sourceIntersection_le_iff (graph sample) i x
  rw [heq]
  exact measurableSet_le hphase measurable_const

/-- The target implicit root has the same actual cut-measurability proof. -/
theorem measurable_targetIntersection_of_curve {lam : ℝ}
    (graph : FiniteSample n → FeedbackGraph lam)
    (hgraph : ∀ x, Measurable (fun sample ↦ (graph sample).curve x)) (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.targetIntersection (graph sample) i) := by
  apply measurable_of_Iic
  intro x
  have hphase : Measurable (fun sample : FiniteSample n ↦
      sample.targetPhase i ((graph sample).curve x)) :=
    (measurable_const.mul (measurable_targetHeight i).subtype_coe).sub
      ((measurable_const.add (measurable_targetMark i).subtype_coe).mul (hgraph x))
  have heq : (fun sample : FiniteSample n ↦ sample.targetIntersection (graph sample) i) ⁻¹'
      Iic x = {sample | sample.targetPhase i ((graph sample).curve x) ≤ x} := by
    ext sample
    exact sample.targetIntersection_le_iff (graph sample) i x
  rw [heq]
  exact measurableSet_le hphase measurable_const

/-- Original optimizer scenes are jointly almost everywhere measurable for any independent root
law.  All graph and intersection coordinates are genuinely measurable. -/
theorem aemeasurable_rootedEuclideanScene_of_curve {lam : ℝ}
    (graph : FiniteSample n → FeedbackGraph lam)
    (hgraph : Measurable (fun p : FiniteSample n × ℝ ↦ (graph p.1).curve p.2))
    (ν : Measure ℝ) :
    AEMeasurable (fun p : FiniteSample n × ℝ ↦ p.1.rootedEuclideanScene (graph p.1) p.2)
      ((finiteSampleLaw n : Measure (FiniteSample n)).prod ν) := by
  have heval (x : ℝ) : Measurable (fun sample : FiniteSample n ↦ (graph sample).curve x) :=
    hgraph.comp (measurable_id.prodMk measurable_const)
  have hs (i : Fin n) := measurable_sourceIntersection_of_curve graph heval i
  have ht (i : Fin n) := measurable_targetIntersection_of_curve graph heval i
  have hsource (i : Fin n) : Measurable (fun p : FiniteSample n × ℝ ↦
      p.1.rootedSourcePoint (graph p.1) p.2 i) :=
    ((hs i).comp measurable_fst |>.sub measurable_snd).prodMk
      ((measurable_sourceMark i).comp measurable_fst)
  have htarget (i : Fin n) : Measurable (fun p : FiniteSample n × ℝ ↦
      p.1.rootedTargetPoint (graph p.1) p.2 i) :=
    ((ht i).comp measurable_fst |>.sub measurable_snd).prodMk
      ((measurable_targetMark i).comp measurable_fst)
  have htargetIndex : Measurable (fun p : (FiniteSample n × ℝ) × Fin n ↦
      p.1.1.rootedTargetPoint (graph p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable_left
    exact htarget
  have hedges : AEMeasurable (fun p : FiniteSample n × ℝ ↦ fun i : Fin n ↦
      (p.1.rootedSourcePoint (graph p.1) p.2 i,
        p.1.rootedTargetPoint (graph p.1) p.2 (p.1.euclideanOptimizer i)))
      ((finiteSampleLaw n : Measure (FiniteSample n)).prod ν) := by
    apply aemeasurable_pi_iff.mpr
    intro i
    have hσ : AEMeasurable (fun p : FiniteSample n × ℝ ↦ p.1.euclideanOptimizer i)
        ((finiteSampleLaw n : Measure (FiniteSample n)).prod ν) :=
      (aemeasurable_euclideanOptimizer_apply i).comp_fst
    have harg : AEMeasurable (fun p : FiniteSample n × ℝ ↦ (p, p.1.euclideanOptimizer i))
        ((finiteSampleLaw n : Measure (FiniteSample n)).prod ν) :=
      aemeasurable_id.prodMk hσ
    exact (hsource i).aemeasurable.prodMk (htargetIndex.comp_aemeasurable harg)
  have hheight : Measurable (fun p : FiniteSample n × ℝ ↦ (graph p.1).rootedHeight p.2) := by
    apply PointProcess.GraphHeight.measurable_of_eval
    intro x
    exact (hgraph.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))).sub hgraph
  have hcurrent : Measurable (fun p : FiniteSample n × ℝ ↦
      (p.1.sourceIntersectionCount (graph p.1) p.2 : ℤ) -
        p.1.targetIntersectionCount (graph p.1) p.2) := by
    have hsums : ∀ p : FiniteSample n × ℝ,
        (p.1.sourceIntersectionCount (graph p.1) p.2 : ℤ) =
          ∑ i, if p.1.sourceIntersection (graph p.1) i ≤ p.2 then 1 else 0 := by
      intro p
      exact (Finset.sum_boole _ _).symm
    have hsumt : ∀ p : FiniteSample n × ℝ,
        (p.1.targetIntersectionCount (graph p.1) p.2 : ℤ) =
          ∑ i, if p.1.targetIntersection (graph p.1) i ≤ p.2 then 1 else 0 := by
      intro p
      exact (Finset.sum_boole _ _).symm
    simp_rw [hsums, hsumt]
    exact (Finset.measurable_sum _ fun i _ ↦
      measurable_const.ite (measurableSet_le ((hs i).comp measurable_fst) measurable_snd)
        measurable_const).sub (Finset.measurable_sum _ fun i _ ↦
      measurable_const.ite (measurableSet_le ((ht i).comp measurable_fst) measurable_snd)
        measurable_const)
  have hpath : Measurable (fun p : FiniteSample n × ℝ ↦
      (p.1.rootedMatchingScene (graph p.1) p.1.euclideanOptimizer p.2).path) := by
    have hemb : MeasurableEmbedding PointProcess.FeedbackPath.coordinates :=
      PointProcess.FeedbackPath.isEmbedding_coordinates.continuous.measurable.measurableEmbedding
        PointProcess.FeedbackPath.equivCoordinates.injective
    apply hemb.measurable_comp_iff.mp
    exact hheight.prodMk hcurrent
  apply PointProcess.MatchingScene.measurableEquivCoordinates.measurableEmbedding.aemeasurable_comp_iff.mp
  exact ((PointProcess.LocalConfiguration.measurable_ofTuple _ n).comp
    (measurable_pi_iff.mpr hsource)).aemeasurable.prodMk <|
      ((PointProcess.LocalConfiguration.measurable_ofTuple _ n).comp
        (measurable_pi_iff.mpr htarget)).aemeasurable.prodMk <|
          ((PointProcess.LocalConfiguration.measurable_ofTuple _ n).comp_aemeasurable hedges).prodMk
            hpath.aemeasurable

/-- Actual capped-feedback optimizer scenes are jointly AE measurable for every independent root
measure, with no survival, no-tie, or environment-identification premise. -/
theorem aemeasurable_stoppedRootedEuclideanScene
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (ν : Measure ℝ) :
    AEMeasurable (fun p : FiniteSample n × ℝ ↦
      p.1.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T p.2)
      ((finiteSampleLaw n : Measure (FiniteSample n)).prod ν) :=
  aemeasurable_rootedEuclideanScene_of_curve (n := n)
    (fun sample : FiniteSample n ↦
      sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
    (measurable_stoppedContinuationFeedbackGraph_curve_joint
      (n := n) hlam0 hlamHalf hB eta T) ν

/-- The actual scene law with the original optimizer and an independent uniform spatial root. -/
noncomputable def stoppedRootedEuclideanSceneLaw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (a b : ℝ) : Measure PointProcess.MatchingScene :=
  Probability.spatialAverageLaw (finiteSampleLaw n : Measure (FiniteSample n))
    (fun p ↦ p.1.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T p.2) a b

/-- The constructed actual finite rooted-scene law is a probability measure. -/
theorem stoppedRootedEuclideanSceneLaw_isProbability
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (stoppedRootedEuclideanSceneLaw (n := n) hlam0 hlamHalf eta B T a b) := by
  let := Probability.spatialRootLaw_isProbability hab
  exact Measure.isProbabilityMeasure_map
    (aemeasurable_stoppedRootedEuclideanScene (n := n) hlam0 hlamHalf hB eta T _)

end OTSelector.FiniteSample
