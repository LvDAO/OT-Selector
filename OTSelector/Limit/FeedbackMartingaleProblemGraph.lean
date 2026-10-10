import OTSelector.Limit.FeedbackMartingaleProblemTwoSidedPoints
import OTSelector.Limit.FeedbackStationaryEnvironmentEquation

/-!
# Recovering the entire feedback environment from its physical point data

The current at every cut is read from the root current and the two actual configurations.
Its feedback velocity has a continuous normalized integral. This produces a measurable
reconstruction of the graph from two-sided point data. Rational values of the feedback
integral equation suffice to identify the original continuous graph.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit
open PointProcess

/-- A measurable environment with the given actual point data and zero auxiliary height.
The graph is irrelevant to its observable current. -/
def feedbackPointDataEnvironment (d : FeedbackTwoSidedPointData) : FeedbackEnvironment :=
  ⟨d.2.1, d.2.2, ⟨0, d.1⟩⟩

theorem measurable_feedbackPointDataEnvironment : Measurable feedbackPointDataEnvironment :=
  FeedbackEnvironment.measurable_mk measurable_snd.fst measurable_snd.snd
    measurable_const measurable_fst

/-- The normalized graph reconstructed from the actual point-count current. -/
noncomputable def feedbackPointDataGraph (lam : ℝ) (d : FeedbackTwoSidedPointData) : GraphHeight where
  toContinuousMap := ⟨fun t ↦ ∫ s in 0..t,
    lam * currentSign (feedbackEnvironmentCurrent (feedbackPointDataEnvironment d) s),
    continuous_feedbackEnvironmentIntegral lam (feedbackPointDataEnvironment d)⟩
  map_zero' := by simp

theorem measurable_feedbackPointDataGraph (lam : ℝ) : Measurable (feedbackPointDataGraph lam) := by
  apply GraphHeight.measurable_of_eval
  intro t
  exact (measurable_feedbackEnvironmentIntegral lam t).comp measurable_feedbackPointDataEnvironment

/-- Reconstruct the complete feedback environment from its current and both full configurations. -/
noncomputable def feedbackEnvironmentFromPoints (lam : ℝ)
    (d : FeedbackTwoSidedPointData) : FeedbackEnvironment :=
  ⟨d.2.1, d.2.2, ⟨feedbackPointDataGraph lam d, d.1⟩⟩

theorem measurable_feedbackEnvironmentFromPoints (lam : ℝ) :
    Measurable (feedbackEnvironmentFromPoints lam) :=
  FeedbackEnvironment.measurable_mk measurable_snd.fst measurable_snd.snd
    (measurable_feedbackPointDataGraph lam) measurable_fst

@[simp]
theorem feedbackTwoSidedPointData_environmentFromPoints (lam : ℝ) (d : FeedbackTwoSidedPointData) :
    feedbackTwoSidedPointData (feedbackEnvironmentFromPoints lam d) = d := rfl

/-- Agreement with the actual feedback integral on rational cuts fixes the entire graph. -/
theorem feedbackEnvironmentFromPoints_eq_of_rational_integral (lam : ℝ) (e : FeedbackEnvironment)
    (hgraph : ∀ q : ℚ, e.path.graphHeight (q : ℝ) =
      ∫ s in 0..(q : ℝ), lam * currentSign (feedbackEnvironmentCurrent e s)) :
    feedbackEnvironmentFromPoints lam (feedbackTwoSidedPointData e) = e := by
  apply FeedbackEnvironment.ext
  · rfl
  · rfl
  · apply FeedbackPath.ext
    · apply GraphHeight.measurableEmbedding_rationalValues.injective
      funext q
      exact (hgraph q).symm
    · rfl

/-- The graph equation makes two-sided point-law identification an identification of the
complete bare environment law. Only countably many graph equations are needed. -/
theorem eq_of_feedbackTwoSidedPointData_law_of_rational_integral
    (lam : ℝ) (μ ν : Measure FeedbackEnvironment)
    (hμ : ∀ᵐ e ∂μ, ∀ q : ℚ, e.path.graphHeight (q : ℝ) =
      ∫ s in 0..(q : ℝ), lam * currentSign (feedbackEnvironmentCurrent e s))
    (hν : ∀ᵐ e ∂ν, ∀ q : ℚ, e.path.graphHeight (q : ℝ) =
      ∫ s in 0..(q : ℝ), lam * currentSign (feedbackEnvironmentCurrent e s))
    (hpoints : μ.map feedbackTwoSidedPointData = ν.map feedbackTwoSidedPointData) : μ = ν := by
  have hrecon (ρ : Measure FeedbackEnvironment)
      (hρ : ∀ᵐ e ∂ρ, ∀ q : ℚ, e.path.graphHeight (q : ℝ) =
        ∫ s in 0..(q : ℝ), lam * currentSign (feedbackEnvironmentCurrent e s)) :
      (ρ.map feedbackTwoSidedPointData).map (feedbackEnvironmentFromPoints lam) = ρ := by
    rw [Measure.map_map (measurable_feedbackEnvironmentFromPoints lam)
      measurable_feedbackTwoSidedPointData]
    calc
      _ = ρ.map id := Measure.map_congr (hρ.mono fun e he ↦
        feedbackEnvironmentFromPoints_eq_of_rational_integral lam e he)
      _ = ρ := Measure.map_id
  rw [← hrecon μ hμ, hpoints, hrecon ν hν]

end OTSelector.Limit
