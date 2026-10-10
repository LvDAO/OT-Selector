import OTSelector.Feedback.FeedbackRightBoundaryScalar
import OTSelector.Feedback.FeedbackRightCountingIntensity

/-!
# Exact scalar conditioning at the frozen right boundary

The scalar boundary estimate applied to a bounded observable and its negative gives the
conditional-law equality under the original finite-sample measure.  In particular the full
usual bulk history remains in the conditioning sigma-algebra.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

namespace OTSelector.FiniteSample

variable {n : ℕ}

/-- The actual frozen-tail height decoded from the revealed snapshot at the deterministic
boundary.  This definition remains meaningful on the exceptional samples as well. -/
noncomputable def actualRightTailHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)

theorem measurable_actualRightTailHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    Measurable (actualRightTailHeight (n := n) hlam0 hlamHalf x0 p0 T) :=
  (measurable_rightBoundaryFrozenHeight lam (x0 + (T : ℝ))).comp
    (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T)

theorem actualRightTailHeight_eq_rightBoundaryHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    actualRightTailHeight hlam0 hlamHalf x0 p0 T sample =
      rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample :=
  rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
    hlam0 hlamHalf x0 p0 T sample hNoTie

/-- The actual continuation retains the entire usual bulk filtration at the boundary before
adjoining frozen-tail observations and taking the usual augmentation. -/
noncomputable def actualRightTailUsualFiltration
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  rightTailJoinedUsualFiltration (usualRevealedFiltration hlam0 hlamHalf x0 p0) T
    (actualRightTailHeight hlam0 hlamHalf x0 p0 T)
    (measurable_actualRightTailHeight hlam0 hlamHalf x0 p0 T) (x0 + (T : ℝ))

theorem usualRevealedBoundary_le_actualRightTailUsualFiltration
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T s : ℝ≥0) :
    usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T ≤
      actualRightTailUsualFiltration hlam0 hlamHalf x0 p0 T s :=
  boundary_le_rightTailJoinedUsualFiltration _ _ _ _ _ _

theorem actualRightSourceMaskedRate_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T H : ℝ≥0) (areaFloor : ℝ) :
    IsStronglyPredictable (actualRightTailUsualFiltration (n := n) hlam0 hlamHalf x0 p0 T)
      (rightSourceMaskedRate n areaFloor H
        (actualRightTailHeight hlam0 hlamHalf x0 p0 T) (x0 + (T : ℝ))) :=
  rightSourceMaskedRate_predictable_joined _ _ _ _ _ _ _

theorem actualRightTargetMaskedRate_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T H : ℝ≥0) (areaFloor : ℝ) :
    IsStronglyPredictable (actualRightTailUsualFiltration (n := n) hlam0 hlamHalf x0 p0 T)
      (rightTargetMaskedRate n areaFloor H
        (actualRightTailHeight hlam0 hlamHalf x0 p0 T) (x0 + (T : ℝ))) :=
  rightTargetMaskedRate_predictable_joined _ _ _ _ _ _ _

theorem rightBoundaryScalarCandidate_neg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T u : ℝ≥0)
    (F : RevealedSnapshot n → FiniteSample n → ℝ) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u
        (fun boundary sample ↦ -F boundary sample) =
      -rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F := by
  funext sample
  simp [rightBoundaryScalarCandidate, twoSnapshotNormalizedScalar,
    normalizedRestrictionIntegral, integral_neg]

/-- The conditional expectation of any bounded jointly measurable boundary observable is its
normalized remaining-rectangle average.  The conditioning retains the entire usual revealed
filtration, rather than only the height and remaining counts at the boundary. -/
theorem condExp_actualBoundaryEvaluation_eq_candidate
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        (fun sample ↦ F
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] =ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F := by
  have hupper := condExp_actualBoundaryEvaluation_le_candidate
    hn hlam0 hlamHalf x0 p0 T hT0 F hF hC hbound
  have hlower := condExp_actualBoundaryEvaluation_le_candidate
    hn hlam0 hlamHalf x0 p0 T hT0
    (fun boundary sample ↦ -F boundary sample) hF.neg hC
    (fun boundary completed ↦ by simpa only [norm_neg] using hbound boundary completed)
  rw [rightBoundaryScalarCandidate_neg] at hlower
  have hneg := condExp_neg (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (fun sample ↦ F
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample)
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T)
  filter_upwards [hupper, hlower, hneg] with sample hupper hlower hneg
  change (finiteSampleLaw n : Measure (FiniteSample n))[
      (fun sample ↦ -F
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample = -_ at hneg
  rw [hneg] at hlower
  exact le_antisymm hupper (neg_le_neg_iff.mp hlower)

/-- Exact boundary-law testing on every event in the full usual bulk history.  This is the
rectangle-testing form used when adjoining future frozen-tail observations. -/
theorem setIntegral_actualBoundaryEvaluation_eq_candidate
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦ F p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C)
    {E : Set (FiniteSample n)}
    (hE : MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] E) :
    (∫ sample in E,
      F (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
    ∫ sample in E, rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  have hY : StronglyMeasurable fun sample : FiniteSample n ↦
      F (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample :=
    hF.comp_measurable ((measurable_revealedSnapshotAtElapsed
      (n := n) hlam0 hlamHalf x0 p0 T).prodMk measurable_id)
  have hYint : Integrable
      (fun sample ↦ F (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) :=
    Integrable.of_bound hY.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun sample ↦ hbound _ sample)
  have heq := condExp_actualBoundaryEvaluation_eq_candidate
    hn hlam0 hlamHalf x0 p0 T hT0 F hF hC hbound
  rw [← setIntegral_condExp
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T) hYint hE]
  exact setIntegral_congr_ae
    (((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T) E hE)
    (heq.mono fun _ h _ ↦ h)

end OTSelector.FiniteSample
