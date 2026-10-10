import OTSelector.Feedback.FeedbackRightIntervalCountsMoment
import OTSelector.Feedback.FeedbackA1Endpoint
import OTSelector.Feedback.FeedbackA2HorizonRange

/-!
# Actual right-boundary localization on square-root buffers

The public A2 event reaches the closed deterministic horizon.  Its endpoint regularity,
together with the actual killed endpoint current, therefore controls the frozen boundary
snapshot.  The constants below are fixed before the sample-size limit is taken.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace OTSelector

open FiniteSample RelativeVC

/-- The actual frozen boundary moment event at `B = amplitude * sqrt n`, `T = n - 2 B`. -/
noncomputable def feedbackRightBoundaryAsymptoticMomentGoodEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude L : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  {sample | rightBoundaryMomentGood lam
    (feedbackA2AsymptoticBuffer amplitude n + feedbackA2AsymptoticHorizon amplitude n)
    (feedbackA2AsymptoticBuffer amplitude n) L
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf
      (feedbackA2AsymptoticBuffer amplitude n) 0 (feedbackA2AsymptoticHorizon amplitude n))}

/-- The actual asymptotic boundary event is measurable under the original sample law. -/
theorem measurableSet_feedbackRightBoundaryAsymptoticMomentGoodEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude L : ℝ) (n : ℕ) :
    MeasurableSet (feedbackRightBoundaryAsymptoticMomentGoodEvent
      hlam0 hlamHalf amplitude L n) := by
  exact (usualRevealedFiltration (n := n) hlam0 hlamHalf
    (feedbackA2AsymptoticBuffer amplitude n) 0).le
    (feedbackA2AsymptoticHorizon amplitude n) _
    (measurableSet_actual_rightBoundaryMomentGood hlam0 hlamHalf
      (feedbackA2AsymptoticBuffer amplitude n) 0 (feedbackA2AsymptoticHorizon amplitude n)
      (feedbackA2AsymptoticBuffer amplitude n) L)

private theorem eventually_endpoint_envelope_geometry
    {amplitude q : ℝ} (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.sqrt (endpointBuffer amplitude n) ∧
      endpointEnvelopeCoefficient q * endpointScale amplitude n ≤
        endpointBuffer amplitude n / 8 := by
  have hB : Tendsto (endpointBuffer amplitude) atTop atTop :=
    Tendsto.const_mul_atTop hamp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsqrt := Real.tendsto_sqrt_atTop.comp hB
  filter_upwards [hsqrt.eventually
    (eventually_ge_atTop (max 1 (8 * endpointEnvelopeCoefficient q)))] with n hn
  have h1 : 1 ≤ Real.sqrt (endpointBuffer amplitude n) :=
    (le_max_left _ _).trans hn
  have h8 : 8 * endpointEnvelopeCoefficient q ≤ Real.sqrt (endpointBuffer amplitude n) :=
    (le_max_right _ _).trans hn
  have hB0 : 0 ≤ endpointBuffer amplitude n := by
    exact mul_nonneg hamp.le (Real.sqrt_nonneg _)
  refine ⟨h1, ?_⟩
  have hm := mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg (endpointBuffer amplitude n))
  have hs := Real.mul_self_sqrt hB0
  dsimp only [endpointScale]
  nlinarith

/-- On A2 survival, a fixed bound on the killed endpoint current gives the actual frozen
boundary moment event.  The current is un-killed using the closed-endpoint A1 survival identity. -/
theorem eventually_feedbackRightBoundaryMomentGood_of_A2Good_of_killedEndpoint_le
    {lam amplitude globalQ endpointQ M : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop, ∀ sample : FiniteSample n,
      sample ∈ feedbackA2AsymptoticGoodEvent
        hlam0 hlam amplitude globalQ endpointQ n →
      |safeFeedbackA1KilledEndpointRow
        hlam0.le (hlam.trans (by norm_num)) amplitude n sample| ≤ M →
      sample ∈ feedbackRightBoundaryAsymptoticMomentGoodEvent
        hlam0.le (hlam.trans (by norm_num)) amplitude
        (endpointEnvelopeCoefficient endpointQ + M) n := by
  have hamp : 0 < amplitude := by linarith
  have hE : 0 ≤ endpointEnvelopeCoefficient endpointQ := by
    unfold endpointEnvelopeCoefficient
    positivity
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedbackA2Asymptotic_regularity_inequalities hlam0 hamp,
    eventually_feedbackA2Asymptotic_threshold hcoefficient,
    eventually_endpointBuffer_geometry hamp,
    eventually_endpoint_envelope_geometry (q := endpointQ) hamp]
      with n hn hreg hthreshold hep henv
  intro sample hgood hcurrent
  let B := feedbackA2AsymptoticBuffer amplitude n
  let T := feedbackA2AsymptoticHorizon amplitude n
  have hgood' : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num)) (feedbackA2AsymptoticEta lam)
      amplitude globalQ endpointQ B T (feedbackA2AsymptoticRadius n) := hgood
  have hA1 : sample ∈ feedbackA1GoodEvent n lam B 0 := by
    by_contra hbad
    exact hgood' (Or.inr (Or.inr (Or.inl hbad)))
  have hEndpoint : sample ∈ feedbackA2EndpointGoodEvent amplitude endpointQ n := by
    intro hbad
    exact hgood' (Or.inr (Or.inl hbad))
  have hNoTie := feedbackA1GoodEvent.noFeedbackTies hA1
  have hbulk := feedbackA2StoppedGoodEvent.horizon_le_safeFeedbackBulkExitTime sample
    hlam0 hlam hn.1 hn.2.1 hn.2.2.1 (feedbackA2AsymptoticEta_pos hlam0).le
    hn.2.2.2.1.le hreg.1 hreg.2 hthreshold hgood'
  have hstop := feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon sample
    hlam0 hlam hn.1 hn.2.1 hn.2.2.1 (feedbackA2AsymptoticEta_pos hlam0).le
    hn.2.2.2.1.le hreg.1 hreg.2 hthreshold hgood'
  have hp : |rightBoundaryHeight hlam0.le (hlam.trans (by norm_num)) B 0 T sample| ≤
      B / 8 :=
    sample.abs_safeFeedbackHeightAtElapsed_le_of_horizon_le_bulkExit
      hlam0.le (hlam.trans (by norm_num)) hn.2.1 hbulk le_rfl
  have hcurrent' : |feedbackRankDiscrepancy (feedbackSourceRankArray sample)
      (feedbackTargetRankArray sample)
      (rightBoundaryHeight hlam0.le (hlam.trans (by norm_num)) B 0 T sample)
      (B + (T : ℝ))| ≤ M := by
    simpa only [safeFeedbackA1KilledEndpointRow, safeFeedbackA1KilledEndpointRank,
      CountingProcess.throughStopMask, hstop, le_refl, ite_true, one_mul,
      elapsedFeedbackCoordinate, rightBoundaryHeight, B, T] using hcurrent
  have hBn : endpointBuffer amplitude n ≤ (n : ℝ) / 2 := by
    have hT : 0 ≤ (T : ℝ) := T.coe_nonneg
    change B ≤ (n : ℝ) / 2
    have hright : B + (T : ℝ) = (n : ℝ) - B := hn.2.2.2.1
    linarith
  have hboundary : B + (T : ℝ) = (n : ℝ) - endpointBuffer amplitude n := hn.2.2.2.1
  have hbuffer := rightBoundaryBufferGood_of_endpoint_controls (currentBound := M) hep.1
    hlam0.le (hlam.trans (by norm_num)) B 0 T sample hNoTie
    hn.2.2.2.1 hep.2.2.2.2 hBn hendpointQ hEndpoint hp henv.2
    (by rwa [← hboundary])
  change rightBoundaryMomentGood _ _ _ _ _
  refine ⟨hbuffer.2.1, hbuffer.2.2, ?_, ?_, ?_⟩
  · rw [rightBoundaryUnseenGap_eq_rankDiscrepancy
      hlam0.le (hlam.trans (by norm_num)) B 0 T sample hNoTie]
    exact hcurrent'.trans (by linarith)
  · apply hbuffer.1.trans
    change endpointEnvelopeCoefficient endpointQ * Real.sqrt B + M / 2 ≤
      (endpointEnvelopeCoefficient endpointQ + M) * Real.sqrt B
    have hm := mul_le_mul_of_nonneg_left henv.1 hM
    change M * 1 ≤ M * Real.sqrt B at hm
    nlinarith
  · rwa [rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
      hlam0.le (hlam.trans (by norm_num)) B 0 T sample hNoTie]

/-- Localization loses only the A2 bad event and one actual killed-current tail. -/
theorem eventually_measureReal_not_feedbackRightBoundaryMomentGood_le
    {lam amplitude globalQ endpointQ M : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackRightBoundaryAsymptoticMomentGoodEvent
          hlam0.le (hlam.trans (by norm_num)) amplitude
          (endpointEnvelopeCoefficient endpointQ + M) n)ᶜ ≤
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n) +
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | M < |safeFeedbackA1KilledEndpointRow
          hlam0.le (hlam.trans (by norm_num)) amplitude n sample|} := by
  filter_upwards [eventually_feedbackRightBoundaryMomentGood_of_A2Good_of_killedEndpoint_le
    hlam0 hlam hglobalQ hendpointQ hcoefficient hM] with n hn
  have hsubset :
      (feedbackRightBoundaryAsymptoticMomentGoodEvent
        hlam0.le (hlam.trans (by norm_num)) amplitude
        (endpointEnvelopeCoefficient endpointQ + M) n)ᶜ ⊆
      feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n ∪
        {sample | M < |safeFeedbackA1KilledEndpointRow
          hlam0.le (hlam.trans (by norm_num)) amplitude n sample|} := by
    intro sample hbad
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    exact hbad (hn sample hnot.1 hnot.2)
  exact (measureReal_mono hsubset).trans (measureReal_union_le _ _)

/-- For any fixed admissible A2 parameters, choose one boundary constant at a prescribed
additional error budget.  This leaves the bulk parameter choice available to other estimates. -/
theorem exists_feedbackRightBoundaryMoment_constant_eventually_bad_probability_le_add
    {lam amplitude globalQ endpointQ ε : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackRightBoundaryAsymptoticMomentGoodEvent
          hlam0.le (hlam.trans (by norm_num)) amplitude L n)ᶜ ≤
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n) + ε := by
  have hamp : 0 < amplitude := by linarith
  obtain ⟨M, hM, htail⟩ := safeFeedbackA1KilledEndpointRow_isBigOInProbability
    hlam0 hlam hamp ε hε
  refine ⟨endpointEnvelopeCoefficient endpointQ + M, ?_, ?_⟩
  · have : 0 ≤ endpointEnvelopeCoefficient endpointQ := by
      unfold endpointEnvelopeCoefficient
      positivity
    linarith
  · filter_upwards [htail,
      eventually_measureReal_not_feedbackRightBoundaryMomentGood_le
        hlam0 hlam hglobalQ hendpointQ hcoefficient hM.le] with n hnTail hnMoment
    simp only [mul_one] at hnTail
    linarith

/-- For every error tolerance there are fixed A2 parameters and a fixed boundary moment
constant, with both actual bad probabilities eventually below that tolerance. -/
theorem exists_feedbackRightBoundaryAsymptotic_parameters_bad_probability_lt
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ globalQ endpointQ amplitude L : ℝ,
      0 < globalQ ∧ 1 ≤ endpointQ ∧ 8 * (globalQ + 33) < amplitude ∧ 0 < L ∧
      ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n) < δ ∧
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackRightBoundaryAsymptoticMomentGoodEvent
            hlam0.le (hlam.trans (by norm_num)) amplitude L n)ᶜ < δ := by
  obtain ⟨globalQ, endpointQ, amplitude, hglobalQ, hendpointQ, hcoefficient, hA2⟩ :=
    exists_feedbackA2Asymptotic_parameters_bad_probability_lt hlam0 hlam
      (show 0 < δ / 2 by positivity)
  obtain ⟨L, hL, hMoment⟩ :=
    exists_feedbackRightBoundaryMoment_constant_eventually_bad_probability_le_add
      hlam0 hlam hglobalQ hendpointQ hcoefficient (show 0 < δ / 2 by positivity)
  refine ⟨globalQ, endpointQ, amplitude, L, hglobalQ, hendpointQ, hcoefficient, hL, ?_⟩
  filter_upwards [hA2, hMoment] with n hnA2 hnMoment
  exact ⟨by linarith, by linarith⟩

end OTSelector
