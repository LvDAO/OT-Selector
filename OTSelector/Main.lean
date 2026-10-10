import OTSelector.Matching.FeedbackSelectorBlockConvergence
import OTSelector.Reconstruction.FeedbackProbabilityLift

/-!
# The empirical Euclidean selector

The original iid finite-sample Euclidean optimizer selects a deterministic coupling of the two
uniform marks. Its empirical plans converge weakly in probability to the reconstructed diagonal
plan. The auxiliary feedback parameter is fixed internally; no environment identification,
matching uniqueness or empirical convergence is assumed.
-/

open MeasureTheory

namespace OTSelector

/-- The original empirical Euclidean optimal plans select one deterministic uniform-marginal
mark coupling. This is the complete Selector theorem of `main.tex`. -/
theorem main_selector :
    ∃ κ : ProbabilityMeasure (UnitMark × UnitMark),
      Vlasov.IsCoupling (κ : Measure (UnitMark × UnitMark))
        (unitUniform : Measure UnitMark) (unitUniform : Measure UnitMark) ∧
      EuclideanEmpiricalWeakTendstoInProbability (reconstructedPlan κ) := by
  obtain ⟨κ, hsource, htarget, hblock⟩ :=
    Matching.exists_feedbackProjectiveBlockLimit
      (lam := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨κ, ⟨hsource, htarget⟩, ?_⟩
  exact euclideanEmpiricalWeakTendstoInProbability_of_sourceHeightBlockMarks
    (lam := (1 / 16 : ℝ)) (by norm_num) (by norm_num) κ hblock

end OTSelector
