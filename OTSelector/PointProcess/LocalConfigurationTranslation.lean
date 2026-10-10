import OTSelector.PointProcess.LocalConfigurationTopologyBridge

/-!
# Jointly measurable point maps and rerooting

Parameter-dependent point maps push the actual counting measure forward measurably.  Combining
this with the deterministic covariance theorem and the count-evaluation criterion proves joint
measurability of configuration translation and rerooting, including changes of shell membership.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace OTSelector.PointProcess.LocalConfiguration

section PointMap

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] {base : X}
  {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]

/-- Jointly measurable physical point maps induce jointly measurable pushforwards of the actual
configuration measure; local finiteness of the image is not needed for this measure statement. -/
@[fun_prop]
theorem measurable_map_countingMeasure_param {f : A × X → Y} (hf : Measurable f) :
    Measurable (fun p : A × LocalConfiguration base ↦
      (countingMeasure p.2).map (fun x ↦ f (p.1, x))) := by
  apply Measure.measurable_measure.mpr
  intro s hs
  have heq (p : A × LocalConfiguration base) :
      ((countingMeasure p.2).map (fun x ↦ f (p.1, x))) s =
        ∑' n, ((p.2 n).map (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞))
          (f (p.1, x.val)))).sum := by
    have hp : Measurable (fun x ↦ f (p.1, x)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hp hs, countingMeasure_apply _ (hs.preimage hp)]
    congr 1
    funext n
    rw [shellMeasure_apply _ _ (hs.preimage hp)]
    rfl
  simp_rw [heq]
  apply Measurable.tsum
  intro n
  have hpoint : Measurable (fun p : A × Shell base n ↦
      s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (f (p.1, p.2.val))) :=
    (measurable_const.indicator hs).comp
      (hf.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))
  exact (MultisetEncoding.measurable_sum_map_param hpoint).comp
    (measurable_fst.prodMk ((measurable_shell n).comp measurable_snd))

end PointMap

section Translation

variable {M : Type*} [MetricSpace M] [ProperSpace M] [MeasurableSpace M]
  [BorelSpace M] [SecondCountableTopology M] [StandardBorelSpace M] {base : ℝ × M}

/-- Translation is jointly measurable in the displacement and the complete local configuration. -/
@[fun_prop]
theorem measurable_uncurry_translate :
    Measurable (fun p : ℝ × LocalConfiguration base ↦ translate p.1 p.2) := by
  apply measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_translate]
  exact measurable_map_countingMeasure_param
    ((measurable_fst.comp measurable_snd).add measurable_fst |>.prodMk
      (measurable_snd.comp measurable_snd))

/-- Move the observation origin to `a`, subtracting `a` from all physical point coordinates. -/
noncomputable def reroot (a : ℝ) (config : LocalConfiguration base) : LocalConfiguration base :=
  translate (-a) config

/-- Rerooting is jointly measurable on the actual configuration probability carrier. -/
theorem measurable_uncurry_reroot :
    Measurable (fun p : ℝ × LocalConfiguration base ↦ reroot p.1 p.2) := by
  have harg : Measurable (fun p : ℝ × LocalConfiguration base ↦ (-p.1, p.2)) :=
    measurable_fst.neg.prodMk measurable_snd
  have h := (measurable_uncurry_translate (base := base)).comp harg
  simpa only [Function.comp_def, reroot] using h

omit [StandardBorelSpace M] in
@[simp]
theorem countingMeasure_reroot (a : ℝ) (config : LocalConfiguration base) :
    countingMeasure (reroot a config) =
      (countingMeasure config).map (Configuration.pointTranslation (-a)) :=
  countingMeasure_translate (-a) config

end Translation

end OTSelector.PointProcess.LocalConfiguration
