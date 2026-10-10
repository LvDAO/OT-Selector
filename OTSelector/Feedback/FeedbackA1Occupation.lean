import OTSelector.Feedback.FeedbackA1StoppedDrift
import OTSelector.Feedback.FiniteEventBulkIntensity
import OTSelector.Feedback.MarkedStoppedIntegrability

/-!
# Actual A1 stopped occupation for the finite feedback process

This file instantiates the generic stopped marked-Dynkin theorem with the bulk-thinned source and
target counts, their proved predictable intensities, and the combined bulk/regularity/horizon
stopping coordinate.  All finite-path integrability conditions are discharged internally.
-/

open MeasureTheory Set
open scoped Classical NNReal ProbabilityTheory

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

open CountingProcess

/-- The actual bulk current has a deterministic absolute bound at every strict-left time. -/
theorem abs_leftCurrentOfSafeBulkCounts_le_cutoff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    |(CountingProcess.leftCurrentOfCounts
        (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample : ℝ)| ≤
      (feedbackA1CurrentCutoff n : ℝ) := by
  have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
    (n := n) hlam0 hlamHalf B x0 p0 t sample
  rw [abs_le]
  constructor
  · exact_mod_cast hinterior.1.le
  · exact_mod_cast hinterior.2.le

/-- The combined A1 localization satisfies the full cubic occupation estimate under the original
finite-sample law.  No stopped-count intensity or occupation-integrability premise remains. -/
theorem safeFeedbackA1_cubic_stopped_occupation_bound
    {lam eta B x0 p0 : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0) :
    ∫ sample, CountingProcess.throughStopClippedQuadraticOccupation
        (safeFeedbackA1StopTime
          (n := n) hlam0.le (by linarith) eta B x0 p0 T)
        (safeK0 lam x0 p0)
        (safeSourceBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
        (safeTargetBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
        t sample ∂(finiteSampleLaw n) ≤
      ((∫ sample, CountingProcess.clippedObservable
          (feedbackA1CurrentCutoff n) cubicLyapunov
          (safeK0 lam x0 p0)
          (safeSourceBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
          (safeTargetBulkCount (n := n) hlam0.le (by linarith) B x0 p0)
          0 sample ∂(finiteSampleLaw n)) +
        (6 + 81 / lam) * (t : ℝ)) / (2 * lam) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let ℱ := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0.le hlamHalf B x0 p0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0.le hlamHalf B x0 p0
  let Λplus : ℝ≥0 → FiniteSample n → ℝ :=
    safeSourceBulkRate hlam0.le hlamHalf B x0 p0
  let Λminus : ℝ≥0 → FiniteSample n → ℝ :=
    safeTargetBulkRate hlam0.le hlamHalf B x0 p0
  let τ : FiniteSample n → WithTop ℝ≥0 :=
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T
  have hplus : CountingProcess.IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B x0 p0
  have hminus : CountingProcess.IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B x0 p0
  have hNo : ∀ u, CountingProcess.NoSimultaneousJumpsOn Nplus Nminus u := by
    intro u
    simpa only [Nplus, Nminus] using
      safeBulkCounts_noSimultaneousJumpsOn
        (n := n) hlam0.le hlamHalf B x0 p0 u
  have hΛplus : CountingProcess.HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nplus Λplus := by
    simpa only [ℱ, Nplus, Λplus] using
      safeSourceBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hΛminus : CountingProcess.HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nminus Λminus := by
    simpa only [ℱ, Nminus, Λminus] using
      safeTargetBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hK0 : StronglyMeasurable[ℱ 0]
      (fun sample : FiniteSample n ↦ (safeK0 lam x0 p0 sample : ℝ)) := by
    simpa only [ℱ] using
      safeK0_stronglyMeasurable_usual_zero
        (n := n) hlam0.le hlamHalf x0 p0
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      CountingProcess.throughStopMask τ := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0.le hlamHalf eta B x0 p0 T u sample
  have hMask : CountingProcess.IsBoundedSimplePredictable ℱ
      (CountingProcess.throughStopMask τ) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hAplus : ∀ u, Integrable
      (fun sample ↦ CountingProcess.integratedIntensity
        Λplus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply CountingProcess.integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeSourceBulkRate_le_cap
        hlam0.le hlamHalf B x0 p0 s sample) hplus hΛplus
  have hAminus : ∀ u, Integrable
      (fun sample ↦ CountingProcess.integratedIntensity
        Λminus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply CountingProcess.integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeTargetBulkRate_le_cap
        hlam0.le hlamHalf B x0 p0 s sample) hminus hΛminus
  have hCurrent : ∀ u sample,
      |(CountingProcess.leftCurrentOfCounts
        (safeK0 lam x0 p0) Nplus Nminus u sample : ℝ)| ≤
        (feedbackA1CurrentCutoff n : ℝ) := by
    intro u sample
    simpa only [Nplus, Nminus] using
      abs_leftCurrentOfSafeBulkCounts_le_cutoff
        (n := n) hlam0.le hlamHalf B x0 p0 u sample
  have h := cubic_clipped_throughStop_occupation_bound_of_rate_drift_of_current_bound
      (R := feedbackA1CurrentCutoff n)
      hplus hminus hNo hΛplus hΛminus hK0 hMask hAplus hAminus
      (K := (feedbackA1CurrentCutoff n : ℝ)) (by positivity) hCurrent
      (C := 3) (c := lam) (by norm_num) hlam0 t (by
        intro sample u hu
        have hdrift :=
          safeFeedbackBulk_clippedGeneratorRate_cubic_le_of_lt_A1Stop
            (n := n) hlam0 hlam hB heta0 hetaSmall T u sample hu
        dsimp only [τ, Nplus, Nminus, Λplus, Λminus]
        (convert hdrift using 1; norm_num))
  norm_num at h ⊢
  simpa only [τ, Nplus, Nminus, hlamHalf] using h

end FiniteSample

end OTSelector
