import OTSelector.PointProcess.LocalConfigurationIntegral
import OTSelector.PointProcess.LocalConfigurationMeasurable
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The deterministic vague-topology bridge and actual translation

On a proper marked metric line, decoding the shell code is a homeomorphism onto the existing
locally finite configuration carrier with its test-integral topology.  Translation therefore
has the same deterministic meaning on both carriers.  Its counting measure is exactly the
pushforward of the original counting measure by point translation.
-/

open MeasureTheory Set Topology
open scoped Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {M : Type*} [MetricSpace M] [ProperSpace M] {base : ℝ × M}

/-- The shell code and the existing deterministic carrier have exactly the same vague topology. -/
noncomputable def configurationHomeomorph (base : ℝ × M) :
    @Homeomorph (LocalConfiguration base) (Configuration M) (vagueTopology base) inferInstance := by
  letI : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  exact {
    toEquiv := equivLocallyFinsupp base
    continuous_toFun := by
      apply continuous_iInf_rng.mpr
      intro f
      apply continuous_induced_rng.mpr
      exact continuous_testIntegral f
    continuous_invFun := by
      apply continuous_iInf_rng.mpr
      intro f
      apply continuous_induced_rng.mpr
      have h := Configuration.continuous_testIntegral f
      convert h using 1
      funext config
      change testIntegral (ofLocallyFinsupp config) f = Configuration.testIntegral config f
      rw [testIntegral_eq_configuration_testIntegral, toLocallyFinsupp_ofLocallyFinsupp] }
/-- Translate the physical real coordinate; shell boundaries are only an encoding device. -/
noncomputable def translate (a : ℝ) (config : LocalConfiguration base) : LocalConfiguration base :=
  ofLocallyFinsupp (Configuration.translate a (toLocallyFinsupp config))

@[simp]
theorem toLocallyFinsupp_translate (a : ℝ) (config : LocalConfiguration base) :
    toLocallyFinsupp (translate a config) = Configuration.translate a (toLocallyFinsupp config) :=
  toLocallyFinsupp_ofLocallyFinsupp _

/-- Point multiplicities transform by the inverse point translation. -/
@[simp]
theorem multiplicity_translate (a : ℝ) (config : LocalConfiguration base) (z : ℝ × M) :
    multiplicity (translate a config) z = multiplicity config (z.1 - a, z.2) := by
  simp [translate, Configuration.translate_apply]

@[simp]
theorem translate_zero (config : LocalConfiguration base) : translate 0 config = config := by
  apply toLocallyFinsupp_injective
  simp

theorem translate_add (a b : ℝ) (config : LocalConfiguration base) :
    translate a (translate b config) = translate (a + b) config := by
  apply toLocallyFinsupp_injective
  simp [Configuration.translate_add]

/-- Translation of test integrals agrees with pullback of the compactly supported test. -/
theorem testIntegral_translate (a : ℝ) (config : LocalConfiguration base)
    (f : C_c(ℝ × M, ℝ)) :
    testIntegral (translate a config) f =
      testIntegral config (Configuration.translateTest a f) := by
  simp only [testIntegral_eq_configuration_testIntegral, toLocallyFinsupp_translate]
  exact Configuration.testIntegral_translate a _ f

/-- Every fixed translation is continuous for the actual vague topology. -/
theorem continuous_translate (a : ℝ) :
    Continuous[vagueTopology base, vagueTopology base] (translate a) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, testIntegral_translate] using
    continuous_testIntegral (base := base) (Configuration.translateTest a f)

section CountingMeasure

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The actual point measure is covariant under the deterministic configuration translation. -/
theorem countingMeasure_translate (a : ℝ) (config : LocalConfiguration base) :
    countingMeasure (translate a config) =
      (countingMeasure config).map (Configuration.pointTranslation a) := by
  let := Measure.Regular.map (μ := countingMeasure config) (Configuration.pointTranslation a)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_countingMeasure, testIntegral_translate, ← integral_countingMeasure]
  exact (integral_map_of_stronglyMeasurable (f := fun x ↦ f x)
    (Configuration.pointTranslation a).measurable f.continuous.stronglyMeasurable).symm

end CountingMeasure

end OTSelector.PointProcess.LocalConfiguration
