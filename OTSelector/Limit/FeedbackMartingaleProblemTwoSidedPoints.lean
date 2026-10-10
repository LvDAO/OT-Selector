import OTSelector.Limit.FeedbackMartingaleProblemStationaryPathReadout
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRestartReadout
import OTSelector.PointProcess.LocalConfigurationBorel
import OTSelector.PointProcess.LocalConfigurationIntegral
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Recovering two-sided point laws from stationary positive-half-line laws

Every finite family of compactly supported configuration tests is visible from a sufficiently
far negative cut. Its positive point measures also recover the original root current through
the source-minus-target count between that cut and zero. The proved measurable separating
code of actual configurations then identifies the complete two-sided point law.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped NNReal ENNReal CompactlySupported

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 300000

namespace OTSelector.Limit

open PointProcess

attribute [local instance] Classical.propDecidable

abbrev FeedbackTwoSidedPointData := ℤ × LocalConfiguration matchingPointBase ×
  LocalConfiguration matchingPointBase

/-- The original root current together with both actual configurations on the whole real line. -/
def feedbackTwoSidedPointData (e : FeedbackEnvironment) : FeedbackTwoSidedPointData :=
  (e.path.rootCurrent, e.source, e.target)

theorem measurable_feedbackTwoSidedPointData : Measurable feedbackTwoSidedPointData :=
  FeedbackEnvironment.measurable_rootCurrent.prodMk
    (FeedbackEnvironment.measurable_source.prodMk FeedbackEnvironment.measurable_target)

private abbrev PositiveData := ℤ × Measure MatchingPoint × Measure MatchingPoint
private abbrev CodeIndex := Option (Bool × (ℕ × ℚ))

private noncomputable def positiveReadout (e : FeedbackEnvironment) : PositiveData :=
  (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)

private theorem measurable_positiveReadout : Measurable positiveReadout :=
  FeedbackEnvironment.measurable_rootCurrent.prodMk measurable_feedbackPositiveEnvironmentPoints

private noncomputable def twoSidedCode (z : FeedbackTwoSidedPointData) : CodeIndex → ℝ
  | none => (z.1 : ℝ)
  | some (b, i) => LocalConfiguration.separatingTestCode (if b then z.2.1 else z.2.2) i

private theorem measurable_twoSidedCode : Measurable twoSidedCode := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | none => exact (measurable_of_countable (fun k : ℤ ↦ (k : ℝ))).comp measurable_fst
  | some bi =>
    rcases bi with ⟨b, i⟩
    cases b
    · have h := LocalConfiguration.measurable_separatingTestCode.comp
        (measurable_snd.snd : Measurable (fun z : FeedbackTwoSidedPointData ↦ z.2.2))
      exact (measurable_pi_apply i).comp h
    · have h := LocalConfiguration.measurable_separatingTestCode.comp
        (measurable_snd.fst : Measurable (fun z : FeedbackTwoSidedPointData ↦ z.2.1))
      exact (measurable_pi_apply i).comp h

private theorem twoSidedCode_injective : Injective twoSidedCode := by
  intro z z' h
  have hroot : z.1 = z'.1 := by
    apply Int.cast_injective (α := ℝ)
    exact congrFun h none
  have hs : z.2.1 = z'.2.1 := by
    apply LocalConfiguration.separatingTestCode_injective
    funext i
    exact congrFun h (some (true, i))
  have ht : z.2.2 = z'.2.2 := by
    apply LocalConfiguration.separatingTestCode_injective
    funext i
    exact congrFun h (some (false, i))
  exact Prod.ext hroot (Prod.ext hs ht)

private noncomputable def recoverCurrent (a : ℝ≥0) (z : PositiveData) : ℤ :=
  z.1 + Int.floor (z.2.1.real (LocalConfiguration.spatialIoc 0 a) -
    z.2.2.real (LocalConfiguration.spatialIoc 0 a))

private theorem measurable_recoverCurrent (a : ℝ≥0) : Measurable (recoverCurrent a) := by
  have hs := (Measure.measurable_coe (LocalConfiguration.measurableSet_spatialIoc 0 a)).comp
    (measurable_snd.fst : Measurable (fun z : PositiveData ↦ z.2.1))
  have ht := (Measure.measurable_coe (LocalConfiguration.measurableSet_spatialIoc 0 a)).comp
    (measurable_snd.snd : Measurable (fun z : PositiveData ↦ z.2.2))
  exact measurable_fst.add ((hs.ennreal_toReal.sub ht.ennreal_toReal).floor)

private theorem positive_real_spatialIoc (c : LocalConfiguration matchingPointBase) (a : ℝ≥0) :
    ((LocalConfiguration.countingMeasure c).restrict (Ioi (0 : ℝ) ×ˢ univ)).real
      (LocalConfiguration.spatialIoc 0 a) = (LocalConfiguration.spatialCount c 0 a : ℝ) := by
  rw [LocalConfiguration.spatialCount_cast, Measure.real, Measure.restrict_apply
    (LocalConfiguration.measurableSet_spatialIoc 0 a)]
  have hs : LocalConfiguration.spatialIoc 0 (a : ℝ) ∩ (Ioi (0 : ℝ) ×ˢ univ) =
      LocalConfiguration.spatialIoc 0 a := by
    apply inter_eq_left.mpr
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  rw [hs]
  rfl

private theorem recoverCurrent_positiveReadout (e : FeedbackEnvironment) (a : ℝ≥0) :
    recoverCurrent a (positiveReadout e) = feedbackEnvironmentCurrent e a := by
  unfold recoverCurrent positiveReadout feedbackPositiveEnvironmentPoints
  rw [positive_real_spatialIoc, positive_real_spatialIoc, ← Int.cast_sub, Int.floor_intCast]
  have hs : LocalConfiguration.spatialCount e.source (a : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le e.source a.property
  have ht : LocalConfiguration.spatialCount e.target (a : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le e.target a.property
  simp only [feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement,
    LocalConfiguration.orientedCount]
  rw [hs, ht, sub_zero, sub_zero]

private theorem recoverCurrent_shift (e : FeedbackEnvironment) (a : ℝ≥0) :
    recoverCurrent a (positiveReadout (FeedbackEnvironment.reroot (-(a : ℝ)) e)) =
      e.path.rootCurrent := by
  rw [recoverCurrent_positiveReadout, feedbackEnvironmentCurrent_reroot]
  simp [feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement]

private noncomputable def positiveCode (a : ℝ≥0) (z : PositiveData) : CodeIndex → ℝ
  | none => (recoverCurrent a z : ℝ)
  | some (b, i) => (∫⁻ p, ENNReal.ofReal
      (LocalConfiguration.separatingTest matchingPointBase i
        (Configuration.pointTranslation (-(a : ℝ)) p))
        ∂(if b then z.2.1 else z.2.2)).toReal

private theorem measurable_positiveCode (a : ℝ≥0) : Measurable (positiveCode a) := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | none =>
    exact (measurable_of_countable (fun k : ℤ ↦ (k : ℝ))).comp
      (measurable_recoverCurrent a)
  | some bi =>
    rcases bi with ⟨b, i⟩
    have hf := ((LocalConfiguration.separatingTest matchingPointBase i).continuous.measurable.comp
      (Configuration.pointTranslation (-(a : ℝ))).measurable).ennreal_ofReal
    have hm := (Measure.measurable_lintegral hf).ennreal_toReal
    cases b
    · exact hm.comp measurable_snd.snd
    · exact hm.comp measurable_snd.fst

private theorem lintegral_positive_reroot_test
    (c : LocalConfiguration matchingPointBase) (a : ℝ≥0) (f : C_c(MatchingPoint, ℝ))
    (hsupport : ∀ p, f p ≠ 0 → -(a : ℝ) < p.1) :
    (∫⁻ p, ENNReal.ofReal (f (Configuration.pointTranslation (-(a : ℝ)) p))
      ∂((LocalConfiguration.countingMeasure (LocalConfiguration.reroot (-(a : ℝ)) c)).restrict
        (Ioi (0 : ℝ) ×ˢ univ))) =
      ∫⁻ p, ENNReal.ofReal (f p) ∂LocalConfiguration.countingMeasure c := by
  have hm := (Configuration.pointTranslation (M := UnitMark) (a : ℝ)).measurable
  have hf : Measurable (fun p : MatchingPoint ↦ ENNReal.ofReal
      (f (Configuration.pointTranslation (-(a : ℝ)) p))) :=
    (f.continuous.measurable.comp
      (Configuration.pointTranslation (-(a : ℝ))).measurable).ennreal_ofReal
  rw [LocalConfiguration.countingMeasure_reroot, neg_neg,
    Measure.restrict_map hm (measurableSet_Ioi.prod MeasurableSet.univ), lintegral_map hf hm]
  have hcomp : (fun p : MatchingPoint ↦ ENNReal.ofReal
      (f (Configuration.pointTranslation (-(a : ℝ)) (Configuration.pointTranslation (a : ℝ) p)))) =
      (fun p : MatchingPoint ↦ ENNReal.ofReal (f p)) := by
    funext p
    simp [Configuration.pointTranslation_apply]
  rw [hcomp, ← lintegral_indicator (hm (measurableSet_Ioi.prod MeasurableSet.univ))]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ Configuration.pointTranslation (a : ℝ) ⁻¹' (Ioi (0 : ℝ) ×ˢ univ)
  · simp only [indicator_of_mem hp]
  · have hz : f p = 0 := by
      by_contra hne
      have hx := hsupport p hne
      apply hp
      change 0 < p.1 + (a : ℝ) ∧ p.2 ∈ (univ : Set UnitMark)
      exact ⟨by linarith, mem_univ _⟩
    simp only [indicator_of_notMem hp, hz, ENNReal.ofReal_zero]

private theorem separatingTest_nonneg (i : ℕ × ℚ) (p : MatchingPoint) :
    0 ≤ LocalConfiguration.separatingTest matchingPointBase i p := le_max_left _ _

private theorem separatingTest_lintegral (c : LocalConfiguration matchingPointBase) (i : ℕ × ℚ) :
    (∫⁻ p, ENNReal.ofReal (LocalConfiguration.separatingTest matchingPointBase i p)
      ∂LocalConfiguration.countingMeasure c).toReal = LocalConfiguration.separatingTestCode c i := by
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (separatingTest_nonneg i))
    (LocalConfiguration.separatingTest matchingPointBase i).continuous.measurable.aestronglyMeasurable,
    LocalConfiguration.integral_countingMeasure]
  rfl

private theorem exists_test_lower_bound (i : ℕ × ℚ) :
    ∃ N : ℕ, ∀ p : MatchingPoint, LocalConfiguration.separatingTest matchingPointBase i p ≠ 0 →
      -(N : ℝ) < p.1 := by
  obtain ⟨N, hN⟩ := LocalConfiguration.exists_testSupport_subset_ball
    (LocalConfiguration.separatingTest matchingPointBase i) matchingPointBase
  refine ⟨N, fun p hp ↦ ?_⟩
  have hd := hN (subset_tsupport _ hp)
  have hx : |p.1| < (N : ℝ) := by
    have hd' : max (dist p.1 0) (dist p.2 (⟨0, by simp⟩ : UnitMark)) < (N : ℝ) := hd
    simpa only [Real.dist_eq, sub_zero] using (lt_of_le_of_lt (le_max_left _ _) hd')
  exact (abs_lt.mp hx).1

private theorem eventually_positiveCode_eq (i : CodeIndex) :
    ∀ᶠ n : ℕ in atTop, ∀ e : FeedbackEnvironment,
      positiveCode (n : ℝ≥0) (positiveReadout (FeedbackEnvironment.reroot (-(n : ℝ)) e)) i =
        twoSidedCode (feedbackTwoSidedPointData e) i := by
  cases i with
  | none =>
    exact Eventually.of_forall fun n e ↦ congrArg (fun k : ℤ ↦ (k : ℝ))
      (recoverCurrent_shift e n)
  | some bi =>
    rcases bi with ⟨b, i⟩
    obtain ⟨N, hN⟩ := exists_test_lower_bound i
    filter_upwards [eventually_ge_atTop N] with n hn
    intro e
    have hs (p : MatchingPoint) (hp : LocalConfiguration.separatingTest matchingPointBase i p ≠ 0) :
        -((n : ℝ≥0) : ℝ) < p.1 := by
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact lt_of_le_of_lt (neg_le_neg hn') (hN p hp)
    have heq (c : LocalConfiguration matchingPointBase) :=
      (congrArg ENNReal.toReal (lintegral_positive_reroot_test c (n : ℝ≥0)
        (LocalConfiguration.separatingTest matchingPointBase i) hs)).trans
        (separatingTest_lintegral c i)
    simp only [NNReal.coe_natCast] at heq
    cases b <;>
      simp only [positiveCode, positiveReadout, feedbackPositiveEnvironmentPoints,
        FeedbackEnvironment.reroot, Bool.false_eq_true, ite_false, ite_true,
        twoSidedCode, feedbackTwoSidedPointData, NNReal.coe_natCast]
    · exact heq e.target
    · exact heq e.source

private theorem measurable_reroot_fixed (a : ℝ) : Measurable (FeedbackEnvironment.reroot a) := by
  have hp : Measurable (fun e : FeedbackEnvironment ↦ (a, e)) := measurable_const.prodMk measurable_id
  have h := FeedbackEnvironment.measurable_uncurry_reroot.comp hp
  exact h

/-- Stationarity and equality of the current/whole-positive-point law determine the actual
current and both complete two-sided configurations. No graph identification is used. -/
theorem map_feedbackTwoSidedPointData_eq_of_stationary_positive
    (μ ν : Measure FeedbackEnvironment) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ a : ℝ, μ.map (FeedbackEnvironment.reroot a) = μ)
    (hν : ∀ a : ℝ, ν.map (FeedbackEnvironment.reroot a) = ν)
    (hpositive : μ.map (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)) =
      ν.map (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e))) :
    μ.map feedbackTwoSidedPointData = ν.map feedbackTwoSidedPointData := by
  have hcode := measurable_twoSidedCode.comp measurable_feedbackTwoSidedPointData
  have hfinite (I : Finset CodeIndex) :
      μ.map (fun e ↦ I.restrict (twoSidedCode (feedbackTwoSidedPointData e))) =
        ν.map (fun e ↦ I.restrict (twoSidedCode (feedbackTwoSidedPointData e))) := by
    have hevent : ∀ᶠ n : ℕ in atTop, ∀ i ∈ I, ∀ e : FeedbackEnvironment,
        positiveCode (n : ℝ≥0) (positiveReadout (FeedbackEnvironment.reroot (-(n : ℝ)) e)) i =
          twoSidedCode (feedbackTwoSidedPointData e) i :=
      (eventually_all_finset I).mpr (fun i _ ↦ eventually_positiveCode_eq i)
    obtain ⟨n, hn⟩ := hevent.exists
    have hshift : μ.map (positiveReadout ∘ FeedbackEnvironment.reroot (-(n : ℝ))) =
        ν.map (positiveReadout ∘ FeedbackEnvironment.reroot (-(n : ℝ))) := by
      rw [← Measure.map_map measurable_positiveReadout (measurable_reroot_fixed _),
        ← Measure.map_map measurable_positiveReadout (measurable_reroot_fixed _), hμ, hν]
      exact hpositive
    have htest := (Finset.measurable_restrict I).comp (measurable_positiveCode (n : ℝ≥0))
    have hh := congrArg (fun ρ : Measure PositiveData ↦
      ρ.map (I.restrict ∘ positiveCode (n : ℝ≥0))) hshift
    rw [Measure.map_map htest (measurable_positiveReadout.comp (measurable_reroot_fixed _)),
      Measure.map_map htest (measurable_positiveReadout.comp (measurable_reroot_fixed _))] at hh
    have heq : ((I.restrict ∘ positiveCode (n : ℝ≥0)) ∘
        (positiveReadout ∘ FeedbackEnvironment.reroot (-(n : ℝ)))) =
        (fun e ↦ I.restrict (twoSidedCode (feedbackTwoSidedPointData e))) := by
      funext e i
      exact hn i i.property e
    rw [heq] at hh
    exact hh
  have hμlim := isProjectiveLimit_map hcode.aemeasurable (P := μ)
  have hνlim := isProjectiveLimit_map hcode.aemeasurable (P := ν)
  have hνlim' : IsProjectiveLimit
      (ν.map (fun e ↦ twoSidedCode (feedbackTwoSidedPointData e)))
      (fun I : Finset CodeIndex ↦ μ.map (fun e ↦ I.restrict
        (twoSidedCode (feedbackTwoSidedPointData e)))) := by
    intro I
    exact (hνlim I).trans (hfinite I).symm
  have heq := hμlim.unique hνlim'
  apply (measurable_twoSidedCode.measurableEmbedding twoSidedCode_injective).map_injective
  rw [Measure.map_map measurable_twoSidedCode measurable_feedbackTwoSidedPointData,
    Measure.map_map measurable_twoSidedCode measurable_feedbackTwoSidedPointData]
  exact heq

/-- The same conclusion expressed directly in the two full counting measures. -/
theorem map_current_twoSided_countingMeasures_eq_of_stationary_positive
    (μ ν : Measure FeedbackEnvironment) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ a : ℝ, μ.map (FeedbackEnvironment.reroot a) = μ)
    (hν : ∀ a : ℝ, ν.map (FeedbackEnvironment.reroot a) = ν)
    (hpositive : μ.map (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)) =
      ν.map (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e))) :
    μ.map (fun e ↦ (e.path.rootCurrent, LocalConfiguration.countingMeasure e.source,
      LocalConfiguration.countingMeasure e.target)) =
    ν.map (fun e ↦ (e.path.rootCurrent, LocalConfiguration.countingMeasure e.source,
      LocalConfiguration.countingMeasure e.target)) := by
  have hs := LocalConfiguration.measurable_countingMeasure.comp
    (measurable_snd.fst : Measurable (fun z : FeedbackTwoSidedPointData ↦ z.2.1))
  have ht := LocalConfiguration.measurable_countingMeasure.comp
    (measurable_snd.snd : Measurable (fun z : FeedbackTwoSidedPointData ↦ z.2.2))
  have hm : Measurable (fun z : FeedbackTwoSidedPointData ↦
      (z.1, LocalConfiguration.countingMeasure z.2.1,
        LocalConfiguration.countingMeasure z.2.2)) := measurable_fst.prodMk (hs.prodMk ht)
  have heq := congrArg (fun ρ : Measure FeedbackTwoSidedPointData ↦
    ρ.map (fun z ↦ (z.1, LocalConfiguration.countingMeasure z.2.1,
      LocalConfiguration.countingMeasure z.2.2)))
    (map_feedbackTwoSidedPointData_eq_of_stationary_positive μ ν hμ hν hpositive)
  rw [Measure.map_map hm measurable_feedbackTwoSidedPointData,
    Measure.map_map hm measurable_feedbackTwoSidedPointData] at heq
  exact heq

end OTSelector.Limit
