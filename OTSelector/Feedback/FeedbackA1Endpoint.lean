import OTSelector.Feedback.FeedbackA1ExponentialDrift
import OTSelector.Feedback.MarkedStoppedExponential
import OTSelector.Feedback.FeedbackInitialExponential
import OTSelector.Feedback.FeedbackA1EndpointBridge
import OTSelector.Feedback.FeedbackA2Asymptotic

/-!
# Actual A1 endpoint exponential tail

This file assembles the actual predictable intensities, exponential generator drift, initial
product-binomial MGF, right-closed A1 stop, and deterministic endpoint bridge.  The public
statements contain no conditional-expectation, Dynkin, MGF, or target-tail hypothesis.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace OTSelector

/-- Explicit finite-`n` envelope obtained from `(1.25a)` and the coarse actual `(1.25b)` bound. -/
noncomputable def feedbackA1EndpointExponentialEnvelope
    (lam B : ℝ) (T : ℝ≥0) : ℝ :=
  Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ))) *
      (2 * Real.exp (2 * B *
        (Real.exp (feedbackA1ExponentialTheta lam) - 1))) +
    (1 + 12 / lam) *
      (1 - Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ))))

namespace FiniteSample

open CountingProcess
open OTSelector.Probability

variable {n : ℕ}

private theorem stronglyMeasurable_section_of_predictable
    {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H) (T : ℝ≥0) :
    StronglyMeasurable (H T) := by
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry H) := hH.mono (predictable_le_ambient ℱ)
  have hEval : Measurable (fun sample : Ω ↦ (T, sample)) :=
    measurable_const.prodMk measurable_id
  exact hambient.comp_measurable hEval

/-- Terminal rank discrepancy killed outside the right-closed A1 survival event.  Multiplication
by the mask realizes the cemetery value `0` without adding a cemetery carrier. -/
noncomputable def safeFeedbackA1KilledEndpointRank
    {lam eta B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  throughStopMask
      (safeFeedbackA1StopTime
        (n := n) hlam0 hlamHalf eta B B 0 T)
      T sample *
    RelativeVC.feedbackRankDiscrepancy
      (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
      (safeFeedbackHeightAtElapsed
        (n := n) hlam0 hlamHalf B 0 T sample)
      (elapsedFeedbackCoordinate B T)

/-- The actual killed endpoint row under the standard `B_n = A sqrt n`,
`T_n = n - 2 B_n`, and A1 tolerance used by the stopped A2 argument. -/
noncomputable def safeFeedbackA1KilledEndpointRow
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude : ℝ) (n : ℕ) : FiniteSample n → ℝ :=
  safeFeedbackA1KilledEndpointRank hlam0 hlamHalf
    (eta := feedbackA2AsymptoticEta lam)
    (B := feedbackA2AsymptoticBuffer amplitude n)
    (feedbackA2AsymptoticHorizon amplitude n)

/-- Once the decayed initial exponent is nonpositive, the finite-`n` endpoint envelope is bounded
by the explicit constant `3 + 12 / lam`. -/
theorem feedbackA1EndpointExponentialEnvelope_le_uniform
    {lam B : ℝ} (hlam0 : 0 < lam) (T : ℝ≥0)
    (hExponent : 2 * B *
        (Real.exp (feedbackA1ExponentialTheta lam) - 1) ≤
      feedbackA1ExponentialDecay lam * (T : ℝ)) :
    feedbackA1EndpointExponentialEnvelope lam B T ≤ 3 + 12 / lam := by
  have hfirst :
      Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ))) *
          (2 * Real.exp (2 * B *
            (Real.exp (feedbackA1ExponentialTheta lam) - 1))) ≤ 2 := by
    calc
      _ = 2 * Real.exp
          (-(feedbackA1ExponentialDecay lam * (T : ℝ)) +
            2 * B * (Real.exp (feedbackA1ExponentialTheta lam) - 1)) := by
          rw [Real.exp_add]
          ring
      _ ≤ 2 * Real.exp 0 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          linarith
      _ = 2 := by norm_num
  have hratio0 : 0 ≤ 1 + 12 / lam := by positivity
  have hsecond :
      (1 + 12 / lam) *
          (1 - Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ)))) ≤
        1 + 12 / lam := by
    calc
      _ ≤ (1 + 12 / lam) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hratio0
        linarith [Real.exp_pos
          (-(feedbackA1ExponentialDecay lam * (T : ℝ)))]
      _ = _ := by ring
  unfold feedbackA1EndpointExponentialEnvelope
  calc
    _ ≤ 2 + (1 + 12 / lam) := add_le_add hfirst hsecond
    _ = 3 + 12 / lam := by ring

/-- Actual finite-sample `(1.25a)` with `(1.25b)` substituted.  The killed quantity is represented
directly by the right-closed mask `T ≤ τA1`; no cemetery carrier is needed. -/
theorem integral_safeFeedbackA1_alive_exponential_current_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) :
    ∫ sample : FiniteSample n,
        throughStopMask
            (safeFeedbackA1StopTime
              (n := n) hlam0.le (by linarith) eta B B 0 T)
            T sample *
          exponentialLyapunov (feedbackA1ExponentialTheta lam)
            (currentOfCounts (safeK0 lam B 0)
              (safeSourceBulkCount (n := n) hlam0.le (by linarith) B B 0)
              (safeTargetBulkCount (n := n) hlam0.le (by linarith) B B 0)
              T sample) ∂(finiteSampleLaw n) ≤
      feedbackA1EndpointExponentialEnvelope lam B T := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let ℱ := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0.le hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0.le hlamHalf B B 0
  let LambdaPlus : ℝ≥0 → FiniteSample n → ℝ :=
    safeSourceBulkRate hlam0.le hlamHalf B B 0
  let LambdaMinus : ℝ≥0 → FiniteSample n → ℝ :=
    safeTargetBulkRate hlam0.le hlamHalf B B 0
  let tau : FiniteSample n → WithTop ℝ≥0 :=
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T
  let theta := feedbackA1ExponentialTheta lam
  let W := exponentialLyapunov theta
  have hplus : IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
  have hminus : IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
  have hNo : ∀ u, NoSimultaneousJumpsOn Nplus Nminus u := by
    intro u
    simpa only [Nplus, Nminus] using
      safeBulkCounts_noSimultaneousJumpsOn
        (n := n) hlam0.le hlamHalf B B 0 u
  have hLambdaPlus : HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nplus LambdaPlus := by
    simpa only [ℱ, Nplus, LambdaPlus] using
      safeSourceBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hLambdaMinus : HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nminus LambdaMinus := by
    simpa only [ℱ, Nminus, LambdaMinus] using
      safeTargetBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hK0 : StronglyMeasurable[ℱ 0]
      (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) := by
    simpa only [ℱ] using safeK0_stronglyMeasurable_usual_zero
      (n := n) hlam0.le hlamHalf B 0
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta B 0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0.le hlamHalf eta B B 0 T = throughStopMask tau := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0.le hlamHalf eta B B 0 T u sample
  have hMask : IsBoundedSimplePredictable ℱ (throughStopMask tau) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hAplus : ∀ u, Integrable
      (fun sample ↦ integratedIntensity
        LambdaPlus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeSourceBulkRate_le_cap
        hlam0.le hlamHalf B B 0 s sample) hplus hLambdaPlus
  have hAminus : ∀ u, Integrable
      (fun sample ↦ integratedIntensity
        LambdaMinus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeTargetBulkRate_le_cap
        hlam0.le hlamHalf B B 0 s sample) hminus hLambdaMinus
  have hObs0 : Integrable
      (clippedObservable (feedbackA1CurrentCutoff n) W
        (safeK0 lam B 0) Nplus Nminus 0) (finiteSampleLaw n) := by
    exact clippedObservable_zero_integrable hplus hminus hK0
      (feedbackA1CurrentCutoff n) W
  have hGeneratorBound : ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
        (s : WithTop ℝ≥0) < tau sample →
          clippedGeneratorRate (feedbackA1CurrentCutoff n) W
              (LambdaPlus s sample) (LambdaMinus s sample)
              (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample) ≤
            -feedbackA1ExponentialDecay lam *
                W (integerClip (feedbackA1CurrentCutoff n)
                  (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample)) +
              feedbackA1ExponentialForcing lam := by
    apply ae_of_all
    intro sample
    apply ae_of_all
    intro s hs
    have hraw :=
      safeFeedbackBulk_clippedGeneratorRate_exponential_le_of_lt_A1Stop
        (n := n) hlam0 hlam hB heta0 hetaSmall T s sample hs
    have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
      (n := n) hlam0.le hlamHalf B B 0 s sample
    have hclip : integerClip (feedbackA1CurrentCutoff n)
        (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample) =
      leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample := by
      apply integerClip_eq_self_of_mem
      rw [cutoffStates, Finset.mem_Icc]
      exact ⟨hinterior.1.le, hinterior.2.le⟩
    rw [hclip]
    simpa only [tau, W, theta, Nplus, Nminus, LambdaPlus, LambdaMinus] using hraw
  have hGeneric := exponential_clipped_throughStop_moment_bound_of_rate_drift_ae
    hplus hminus hNo hLambdaPlus hLambdaMinus hK0 hMask hAplus hAminus
    (a := feedbackA1ExponentialDecay lam)
    (b := feedbackA1ExponentialForcing lam)
    (feedbackA1ExponentialDecay_pos hlam0)
    (feedbackA1ExponentialForcing_nonneg hlam0)
    T (feedbackA1CurrentCutoff n) W
    (fun k ↦ by exact (Real.exp_pos _).le) hObs0 hGeneratorBound
  have hInitial := integral_safeFeedback_initial_clippedExponential_le
    (n := n) hlam0 hlam hn hB.le hBn
  have hTerminalEq : (fun sample : FiniteSample n ↦
      throughStopMask tau T sample *
        clippedObservable (feedbackA1CurrentCutoff n) W
          (safeK0 lam B 0) Nplus Nminus T sample) =
      (fun sample ↦ throughStopMask tau T sample *
        exponentialLyapunov (feedbackA1ExponentialTheta lam)
          (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample)) := by
    funext sample
    have hinterior := currentOfSafeBulkCounts_strictInterior_post
      (n := n) hlam0.le hlamHalf B B 0 T sample
    have hclip : integerClip (feedbackA1CurrentCutoff n)
        (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample) =
      currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample := by
      apply integerClip_eq_self_of_mem
      rw [cutoffStates, Finset.mem_Icc]
      exact ⟨hinterior.1.le, hinterior.2.le⟩
    unfold clippedObservable W theta
    rw [hclip]
  rw [← hTerminalEq]
  calc
    (∫ sample, throughStopMask tau T sample *
        clippedObservable (feedbackA1CurrentCutoff n) W
          (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n)) ≤
        Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ))) *
            (∫ sample, clippedObservable (feedbackA1CurrentCutoff n) W
              (safeK0 lam B 0) Nplus Nminus 0 sample ∂(finiteSampleLaw n)) +
          (feedbackA1ExponentialForcing lam / feedbackA1ExponentialDecay lam) *
            (1 - Real.exp
              (-(feedbackA1ExponentialDecay lam * (T : ℝ)))) := by
      simpa only [tau] using hGeneric
    _ ≤ Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ))) *
          (2 * Real.exp (2 * B *
            (Real.exp (feedbackA1ExponentialTheta lam) - 1))) +
        (feedbackA1ExponentialForcing lam / feedbackA1ExponentialDecay lam) *
            (1 - Real.exp (-(feedbackA1ExponentialDecay lam * (T : ℝ)))) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [W, theta, Nplus, Nminus] using hInitial
      · exact le_rfl
    _ = feedbackA1EndpointExponentialEnvelope lam B T := by
      unfold feedbackA1EndpointExponentialEnvelope
      rw [feedbackA1ExponentialForcing_div_decay hlam0]

/-- Actual endpoint form of `(1.25a)`: on the closed survival event, the terminal post-current is
the rank discrepancy at `B + T`.  The deterministic endpoint itself is retained. -/
theorem integral_safeFeedbackA1_alive_endpointRankExponential_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) (hT : 0 < T) :
    ∫ sample : FiniteSample n,
        throughStopMask
            (safeFeedbackA1StopTime
              (n := n) hlam0.le (by linarith) eta B B 0 T)
            T sample *
          Real.exp (feedbackA1ExponentialTheta lam *
            |RelativeVC.feedbackRankDiscrepancy
              (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
              (safeFeedbackHeightAtElapsed
                (n := n) hlam0.le (by linarith) B 0 T sample)
              (elapsedFeedbackCoordinate B T)|) ∂(finiteSampleLaw n) ≤
      feedbackA1EndpointExponentialEnvelope lam B T := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hBridge :=
    currentOfSafeBulkCounts_cast_eq_feedbackRankDiscrepancy_ae_on_closed_A1_endpoint
      (n := n) (eta := eta) (B := B) hlam0.le hlamHalf T hT
  calc
    (∫ sample : FiniteSample n,
        throughStopMask
            (safeFeedbackA1StopTime
              (n := n) hlam0.le hlamHalf eta B B 0 T)
            T sample *
          Real.exp (feedbackA1ExponentialTheta lam *
            |RelativeVC.feedbackRankDiscrepancy
              (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
              (safeFeedbackHeightAtElapsed
                (n := n) hlam0.le hlamHalf B 0 T sample)
              (elapsedFeedbackCoordinate B T)|) ∂(finiteSampleLaw n)) =
        ∫ sample : FiniteSample n,
          throughStopMask
              (safeFeedbackA1StopTime
                (n := n) hlam0.le hlamHalf eta B B 0 T)
              T sample *
            exponentialLyapunov (feedbackA1ExponentialTheta lam)
              (currentOfCounts (safeK0 lam B 0)
                (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
                (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
                T sample) ∂(finiteSampleLaw n) := by
      apply integral_congr_ae
      filter_upwards [hBridge] with sample hsample
      by_cases hAlive : (T : WithTop ℝ≥0) ≤
          safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample
      · have hCurrent := hsample hAlive
        simp only [throughStopMask, ite_eq_left hAlive, one_mul, exponentialLyapunov]
        rw [hCurrent]
      · simp only [throughStopMask, ite_eq_right hAlive, zero_mul]
    _ ≤ feedbackA1EndpointExponentialEnvelope lam B T :=
      integral_safeFeedbackA1_alive_exponential_current_le
        hlam0 hlam hn hB hBn heta0 hetaSmall T

set_option maxHeartbeats 5000000 in
private theorem integrable_safeFeedbackA1_alive_exponential_current
    {lam eta B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hB : 0 < B) (T : ℝ≥0) :
    Integrable (fun sample : FiniteSample n ↦
      throughStopMask
          (safeFeedbackA1StopTime
            (n := n) hlam0 hlamHalf eta B B 0 T)
          T sample *
        exponentialLyapunov (feedbackA1ExponentialTheta lam)
          (currentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
            (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
            T sample)) (finiteSampleLaw n) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0 hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0 hlamHalf B B 0
  let tau : FiniteSample n → WithTop ℝ≥0 :=
    safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T
  let theta := feedbackA1ExponentialTheta lam
  have hplus : IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0 hlamHalf B B 0
  have hminus : IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0 hlamHalf B B 0
  have hK0 : StronglyMeasurable[ℱ 0]
      (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) := by
    simpa only [ℱ] using safeK0_stronglyMeasurable_usual_zero
      (n := n) hlam0 hlamHalf B 0
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta B 0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0 hlamHalf eta B B 0 T = throughStopMask tau := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0 hlamHalf eta B B 0 T u sample
  have hMask : IsBoundedSimplePredictable ℱ (throughStopMask tau) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hK : StronglyMeasurable
      (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) :=
    hK0.mono (ℱ.le 0)
  have hplusT : StronglyMeasurable
      (fun sample : FiniteSample n ↦ (Nplus T sample : ℝ)) :=
    (hplus.stronglyAdapted T).mono (ℱ.le T)
  have hminusT : StronglyMeasurable
      (fun sample : FiniteSample n ↦ (Nminus T sample : ℝ)) :=
    (hminus.stronglyAdapted T).mono (ℱ.le T)
  have hCurrent : StronglyMeasurable (fun sample : FiniteSample n ↦
      (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)) := by
    convert (hK.add hplusT).sub hminusT using 1
    funext sample
    simp [currentOfCounts]
  have hExponential : StronglyMeasurable (fun sample : FiniteSample n ↦
      exponentialLyapunov theta
        (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample)) := by
    unfold exponentialLyapunov
    have hAbs : StronglyMeasurable (fun sample : FiniteSample n ↦
        |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|) := by
      simpa only [Real.norm_eq_abs] using hCurrent.norm
    exact Real.continuous_exp.comp_stronglyMeasurable
      (stronglyMeasurable_const.mul hAbs)
  have hMaskSection : StronglyMeasurable (throughStopMask tau T) := by
    exact stronglyMeasurable_section_of_predictable hMask.1 T
  refine Integrable.of_bound (hMaskSection.mul hExponential).aestronglyMeasurable
    (Real.exp (theta * (feedbackA1CurrentCutoff n : ℝ))) ?_
  apply ae_of_all
  intro sample
  have hinterior := currentOfSafeBulkCounts_strictInterior_post
    (n := n) hlam0 hlamHalf B B 0 T sample
  have habs : |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)| ≤
      (feedbackA1CurrentCutoff n : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hinterior.1.le
    · exact_mod_cast hinterior.2.le
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta, feedbackA1ExponentialTheta]
    positivity
  have hExponentialBound : exponentialLyapunov theta
        (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample) ≤
      Real.exp (theta * (feedbackA1CurrentCutoff n : ℝ)) := by
    unfold exponentialLyapunov
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs htheta0)
  have hMaskAbs : |throughStopMask tau T sample| ≤ (1 : ℝ) := by
    unfold throughStopMask
    split <;> norm_num
  have hExponential0 : 0 ≤ exponentialLyapunov theta
      (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample) :=
    (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hExponential0]
  exact (mul_le_mul_of_nonneg_right hMaskAbs hExponential0).trans
    (by simpa only [one_mul] using hExponentialBound)

set_option maxHeartbeats 5000000 in
/-- Actual exponential endpoint tail.  The event is the closed-survival endpoint
`T ≤ τA1` intersected with the large terminal rank-discrepancy event. -/
theorem measureReal_safeFeedbackA1_alive_endpointRank_tail_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) (hT : 0 < T) (M : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          (T : WithTop ℝ≥0) ≤
              safeFeedbackA1StopTime
                (n := n) hlam0.le (by linarith) eta B B 0 T sample ∧
            M ≤ |RelativeVC.feedbackRankDiscrepancy
              (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
              (safeFeedbackHeightAtElapsed
                (n := n) hlam0.le (by linarith) B 0 T sample)
              (elapsedFeedbackCoordinate B T)|} ≤
      Real.exp (-(feedbackA1ExponentialTheta lam * M)) *
        feedbackA1EndpointExponentialEnvelope lam B T := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0.le hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0.le hlamHalf B B 0
  let tau : FiniteSample n → WithTop ℝ≥0 :=
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T
  let theta := feedbackA1ExponentialTheta lam
  let Z : FiniteSample n → ℝ := fun sample ↦
    throughStopMask tau T sample *
      exponentialLyapunov theta
        (currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample)
  have hBridge :=
    currentOfSafeBulkCounts_cast_eq_feedbackRankDiscrepancy_ae_on_closed_A1_endpoint
      (n := n) (eta := eta) (B := B) hlam0.le hlamHalf T hT
  have hEventEq :
      {sample : FiniteSample n |
        (T : WithTop ℝ≥0) ≤ tau sample ∧
          M ≤ |RelativeVC.feedbackRankDiscrepancy
            (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
            (safeFeedbackHeightAtElapsed
              (n := n) hlam0.le hlamHalf B 0 T sample)
            (elapsedFeedbackCoordinate B T)|} =ᵐ[
              (finiteSampleLaw n : Measure (FiniteSample n))]
      {sample : FiniteSample n |
        (T : WithTop ℝ≥0) ≤ tau sample ∧
          M ≤ |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|} := by
    filter_upwards [hBridge] with sample hsample
    change ((T : WithTop ℝ≥0) ≤ tau sample ∧
      M ≤ |RelativeVC.feedbackRankDiscrepancy
        (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed
          (n := n) hlam0.le hlamHalf B 0 T sample)
        (elapsedFeedbackCoordinate B T)|) =
      ((T : WithTop ℝ≥0) ≤ tau sample ∧
        M ≤ |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|)
    apply propext
    constructor
    · rintro ⟨hAlive, hLarge⟩
      exact ⟨hAlive, by rwa [hsample hAlive]⟩
    · rintro ⟨hAlive, hLarge⟩
      exact ⟨hAlive, by rwa [← hsample hAlive]⟩
  have hZIntegrable : Integrable Z (finiteSampleLaw n) := by
    simpa only [Z, tau, theta, Nplus, Nminus] using
      integrable_safeFeedbackA1_alive_exponential_current
        (n := n) (eta := eta) hlam0.le hlamHalf hB T
  have hZnonneg : ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      0 ≤ Z sample := by
    apply ae_of_all
    intro sample
    apply mul_nonneg
    · unfold throughStopMask
      split <;> norm_num
    · exact (Real.exp_pos _).le
  have hThreshold :
      {sample : FiniteSample n | Real.exp (theta * M) ≤ Z sample} =
      {sample : FiniteSample n |
          (T : WithTop ℝ≥0) ≤ tau sample ∧
          M ≤ |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|} := by
    ext sample
    change (Real.exp (theta * M) ≤
        throughStopMask tau T sample *
          Real.exp (theta * |(currentOfCounts
            (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|)) ↔
      ((T : WithTop ℝ≥0) ≤ tau sample ∧
        M ≤ |(currentOfCounts (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|)
    by_cases hAlive : (T : WithTop ℝ≥0) ≤ tau sample
    · have hmask : throughStopMask tau T sample = 1 := by
        unfold throughStopMask
        exact ite_eq_left hAlive
      rw [hmask, one_mul, Real.exp_le_exp]
      simp only [hAlive, true_and]
      exact (mul_le_mul_iff_of_pos_left (feedbackA1ExponentialTheta_pos hlam0))
    · have hNotLe : ¬ Real.exp (theta * M) ≤ 0 :=
        not_le.mpr (Real.exp_pos _)
      have hmask : throughStopMask tau T sample = 0 := by
        unfold throughStopMask
        exact ite_eq_right hAlive
      rw [hmask, zero_mul]
      simp only [hNotLe, hAlive, false_and]
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) (f := Z)
      hZnonneg hZIntegrable
      (Real.exp (theta * M))
  have hMoment : ∫ sample : FiniteSample n, Z sample ∂(finiteSampleLaw n) ≤
      feedbackA1EndpointExponentialEnvelope lam B T := by
    simpa only [Z, tau, theta, Nplus, Nminus] using
      integral_safeFeedbackA1_alive_exponential_current_le
        hlam0 hlam hn hB hBn heta0 hetaSmall T
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          (T : WithTop ℝ≥0) ≤
              safeFeedbackA1StopTime
                (n := n) hlam0.le hlamHalf eta B B 0 T sample ∧
            M ≤ |RelativeVC.feedbackRankDiscrepancy
              (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
              (safeFeedbackHeightAtElapsed
                (n := n) hlam0.le hlamHalf B 0 T sample)
              (elapsedFeedbackCoordinate B T)|} =
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            (T : WithTop ℝ≥0) ≤ tau sample ∧
              M ≤ |(currentOfCounts
                (safeK0 lam B 0) Nplus Nminus T sample : ℝ)|} := by
      exact measureReal_congr hEventEq
    _ = (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n | Real.exp (theta * M) ≤ Z sample} := by
      rw [hThreshold]
    _ ≤ (∫ sample : FiniteSample n, Z sample ∂(finiteSampleLaw n)) /
          Real.exp (theta * M) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa only [mul_comm] using hMarkov
    _ ≤ feedbackA1EndpointExponentialEnvelope lam B T /
          Real.exp (theta * M) :=
      div_le_div_of_nonneg_right hMoment (Real.exp_pos _).le
    _ = Real.exp (-(feedbackA1ExponentialTheta lam * M)) *
          feedbackA1EndpointExponentialEnvelope lam B T := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      simp only [theta]
      ring

private theorem eventually_feedbackA1Endpoint_decay_dominates_initial
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      0 < feedbackA2AsymptoticHorizon amplitude n ∧
        2 * feedbackA2AsymptoticBuffer amplitude n *
            (Real.exp (feedbackA1ExponentialTheta lam) - 1) ≤
          feedbackA1ExponentialDecay lam *
            (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
  let a := feedbackA1ExponentialDecay lam
  let c := Real.exp (feedbackA1ExponentialTheta lam) - 1
  let L := max 2 (max (4 * amplitude) (4 * amplitude * c / a))
  have ha : 0 < a := by
    simpa only [a] using feedbackA1ExponentialDecay_pos hlam0
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    hsqrt.eventually (eventually_ge_atTop L)] with n hgeometry hnL
  rcases hgeometry with ⟨hn4, _hBpos, _hBn, hcoordinate, _hTle, _hB8⟩
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtAmplitude : 4 * amplitude ≤ Real.sqrt (n : ℝ) :=
    (le_max_left (4 * amplitude) (4 * amplitude * c / a)).trans
      ((le_max_right 2 (max (4 * amplitude) (4 * amplitude * c / a))).trans hnL)
  have hsqrtExponent : 4 * amplitude * c / a ≤ Real.sqrt (n : ℝ) :=
    (le_max_right (4 * amplitude) (4 * amplitude * c / a)).trans
      ((le_max_right 2 (max (4 * amplitude) (4 * amplitude * c / a))).trans hnL)
  have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = n :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hfourB : 4 * feedbackA2AsymptoticBuffer amplitude n ≤ (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hsqrtAmplitude hsqrt0
    rw [hsquare] at hmul
    rw [feedbackA2AsymptoticBuffer_eq]
    simpa only [mul_assoc] using hmul
  have hTcoe : (feedbackA2AsymptoticHorizon amplitude n : ℝ) =
      (n : ℝ) - 2 * feedbackA2AsymptoticBuffer amplitude n := by
    linarith
  have hn0 : 0 < n := by omega
  have hnReal0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hTlower : (n : ℝ) / 2 ≤
      (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
    rw [hTcoe]
    linarith
  have hTreal0 : 0 < (feedbackA2AsymptoticHorizon amplitude n : ℝ) :=
    (half_pos hnReal0).trans_le hTlower
  have hT0 : 0 < feedbackA2AsymptoticHorizon amplitude n := by
    exact_mod_cast hTreal0
  have hscaled : 4 * amplitude * c ≤ a * Real.sqrt (n : ℝ) := by
    have h := (div_le_iff₀ ha).mp hsqrtExponent
    simpa only [mul_comm] using h
  have hscaledSqrt : 4 * amplitude * c * Real.sqrt (n : ℝ) ≤
      a * (n : ℝ) := by
    calc
      _ ≤ (a * Real.sqrt (n : ℝ)) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hscaled hsqrt0
      _ = a * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = a * (n : ℝ) := by rw [hsquare]
  have hInitialHalf :
      2 * feedbackA2AsymptoticBuffer amplitude n * c ≤ a * (n : ℝ) / 2 := by
    rw [feedbackA2AsymptoticBuffer_eq]
    nlinarith
  have hDecayHalf : a * (n : ℝ) / 2 ≤
      a * (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hTlower ha.le
    nlinarith
  refine ⟨hT0, ?_⟩
  simpa only [a, c] using hInitialHalf.trans hDecayHalf

/-- Eventual uniform tail for the actual killed endpoint row in the square-root buffer regime. -/
theorem eventually_measureReal_safeFeedbackA1KilledEndpointRow_tail_le
    {lam amplitude M : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hamp : 0 < amplitude) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            M ≤ |safeFeedbackA1KilledEndpointRow
              hlam0.le (by linarith) amplitude n sample|} ≤
        Real.exp (-(feedbackA1ExponentialTheta lam * M)) *
          (3 + 12 / lam) := by
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedbackA1Endpoint_decay_dominates_initial hlam0 hamp] with
      n hgeometry hdecay
  rcases hgeometry with ⟨hn4, hBpos, hBn, _hcoordinate, _hTle, _hB8⟩
  rcases hdecay with ⟨hT, hExponent⟩
  let hlamHalf : lam < 1 / 2 := by linarith
  let eta := feedbackA2AsymptoticEta lam
  let B := feedbackA2AsymptoticBuffer amplitude n
  let T := feedbackA2AsymptoticHorizon amplitude n
  have htail := measureReal_safeFeedbackA1_alive_endpointRank_tail_le
    (n := n) (eta := eta) (B := B) hlam0 hlam (by omega)
      (by simpa only [B] using hBpos) (by simpa only [B] using hBn)
      (by simpa only [eta] using (feedbackA2AsymptoticEta_pos hlam0).le)
      (by simpa only [eta] using feedbackA2AsymptoticEta_small hlam0)
      T (by simpa only [T] using hT) M
  have hEnvelope := feedbackA1EndpointExponentialEnvelope_le_uniform
    hlam0 T (by simpa only [B, T] using hExponent)
  have hsubset :
      {sample : FiniteSample n |
        M ≤ |safeFeedbackA1KilledEndpointRow
          hlam0.le hlamHalf amplitude n sample|} ⊆
      {sample : FiniteSample n |
        (T : WithTop ℝ≥0) ≤
            safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample ∧
          M ≤ |RelativeVC.feedbackRankDiscrepancy
            (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
            (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 T sample)
        (elapsedFeedbackCoordinate B T)|} := by
    intro sample hLarge
    change M ≤ |safeFeedbackA1KilledEndpointRow
      hlam0.le hlamHalf amplitude n sample| at hLarge
    by_cases hAlive : (T : WithTop ℝ≥0) ≤
        safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample
    · refine ⟨hAlive, ?_⟩
      have hLarge' : M ≤ |throughStopMask
          (safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T) T sample *
        RelativeVC.feedbackRankDiscrepancy
          (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 T sample)
          (elapsedFeedbackCoordinate B T)| := by
        simpa only [safeFeedbackA1KilledEndpointRow,
          safeFeedbackA1KilledEndpointRank, eta, B, T] using hLarge
      have hmask : throughStopMask
          (safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T) T sample = 1 := by
        unfold throughStopMask
        exact ite_eq_left hAlive
      rw [hmask, one_mul] at hLarge'
      exact hLarge'
    · have hzero : safeFeedbackA1KilledEndpointRow
          hlam0.le hlamHalf amplitude n sample = 0 := by
        simp only [safeFeedbackA1KilledEndpointRow,
          safeFeedbackA1KilledEndpointRank, eta, B, T, throughStopMask,
          ite_eq_right hAlive, zero_mul]
      rw [hzero, abs_zero] at hLarge
      exact False.elim ((not_le_of_gt hM) hLarge)
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          M ≤ |safeFeedbackA1KilledEndpointRow
            hlam0.le hlamHalf amplitude n sample|} ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            (T : WithTop ℝ≥0) ≤
                safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample ∧
              M ≤ |RelativeVC.feedbackRankDiscrepancy
                (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
                (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 T sample)
                (elapsedFeedbackCoordinate B T)|} := measureReal_mono hsubset
    _ ≤ Real.exp (-(feedbackA1ExponentialTheta lam * M)) *
          feedbackA1EndpointExponentialEnvelope lam B T := by
      simpa only [eta, B, T] using htail
    _ ≤ Real.exp (-(feedbackA1ExponentialTheta lam * M)) *
          (3 + 12 / lam) :=
      mul_le_mul_of_nonneg_left hEnvelope (Real.exp_pos _).le

/-- Equation `(1.23)`: the alive-intersected (equivalently cemetery-killed) terminal rank
discrepancy is `O_P(1)` across the actual finite-sample rows. -/
theorem safeFeedbackA1KilledEndpointRow_isBigOInProbability
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hamp : 0 < amplitude) :
    IsBigOInProbability
      (fun n : ℕ ↦ (finiteSampleLaw n : Measure (FiniteSample n)))
      (fun n ↦ safeFeedbackA1KilledEndpointRow
        hlam0.le (by linarith) amplitude n)
      (fun _n ↦ (1 : ℝ)) := by
  intro epsilon hepsilon
  let theta := feedbackA1ExponentialTheta lam
  let K := 3 + 12 / lam
  let ratio := K / epsilon + 1
  let C := Real.log ratio / theta
  have htheta : 0 < theta := by
    simpa only [theta] using feedbackA1ExponentialTheta_pos hlam0
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hratioOne : 1 < ratio := by
    dsimp only [ratio]
    have hpositive : 0 < K / epsilon := div_pos hK hepsilon
    linarith
  have hratio : 0 < ratio := zero_lt_one.trans hratioOne
  have hC : 0 < C := by
    dsimp only [C]
    exact div_pos (Real.log_pos hratioOne) htheta
  refine ⟨C, hC, ?_⟩
  have htail := eventually_measureReal_safeFeedbackA1KilledEndpointRow_tail_le
    hlam0 hlam hamp hC
  have hthetaC : theta * C = Real.log ratio := by
    dsimp only [C]
    field_simp [htheta.ne']
  have hsmall : Real.exp (-(theta * C)) * K < epsilon := by
    rw [hthetaC, Real.exp_neg, Real.exp_log hratio]
    have hdiv : K / ratio < epsilon := by
      apply (div_lt_iff₀ hratio).2
      dsimp only [ratio]
      calc
        K < K + epsilon := lt_add_of_pos_right K hepsilon
        _ = epsilon * (K / epsilon + 1) := by
          field_simp [hepsilon.ne']
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  filter_upwards [htail] with n hnTail
  have hsubset :
      {sample : FiniteSample n |
        C * (1 : ℝ) <
          |safeFeedbackA1KilledEndpointRow
            hlam0.le (by linarith) amplitude n sample|} ⊆
      {sample : FiniteSample n |
        C ≤ |safeFeedbackA1KilledEndpointRow
          hlam0.le (by linarith) amplitude n sample|} := by
    intro sample hLarge
    change C * (1 : ℝ) <
      |safeFeedbackA1KilledEndpointRow
        hlam0.le (by linarith) amplitude n sample| at hLarge
    change C ≤ |safeFeedbackA1KilledEndpointRow
      hlam0.le (by linarith) amplitude n sample|
    simpa only [mul_one] using hLarge.le
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          C * (1 : ℝ) <
            |safeFeedbackA1KilledEndpointRow
              hlam0.le (by linarith) amplitude n sample|} ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            C ≤ |safeFeedbackA1KilledEndpointRow
              hlam0.le (by linarith) amplitude n sample|} := measureReal_mono hsubset
    _ ≤ Real.exp (-(feedbackA1ExponentialTheta lam * C)) *
          (3 + 12 / lam) := hnTail
    _ ≤ epsilon := by
      simpa only [theta, K] using hsmall.le

end FiniteSample

end OTSelector
