import OTSelector.Feedback.FeedbackFGL2

/-!
# One actual good event for environment identification and matching compactness

The stopped A2 event supplies the same graph's survival, VC controls and no-tie property.
Its comparison energy transfers to the original Euclidean optimizer. All parameters are chosen
once at a fixed outer probability tolerance; no energy moment is inferred by conditioning.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace OTSelector

open FiniteSample

/-- The actual stopped good event together with the original optimizer's linear energy bound. -/
noncomputable def feedbackSelectorGoodEvent {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (amplitude globalQ endpointQ C : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  feedbackA2AsymptoticGoodEvent hlam0 hlam amplitude globalQ endpointQ n ∩
    {sample | sample.feedbackFGL2OptimizerEnergy
      hlam0.le (hlam.trans (by norm_num)) amplitude ≤ C * n}

theorem feedbackSelectorGoodEvent.a1 {lam amplitude globalQ endpointQ C : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {n : ℕ} {sample : FiniteSample n}
    (h : sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) :
    sample ∈ feedbackA1GoodEvent n lam (feedbackA2AsymptoticBuffer amplitude n) 0 := by
  by_contra hn
  exact h.1 (Or.inr (Or.inr (Or.inl hn)))

theorem feedbackSelectorGoodEvent.globalCut {lam amplitude globalQ endpointQ C : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {n : ℕ} {sample : FiniteSample n}
    (h : sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) :
    sample ∈ feedbackA2GlobalCutGoodEvent globalQ n := by
  intro hn
  exact h.1 (Or.inl hn)

theorem feedbackSelectorGoodEvent.noFeedbackTies {lam amplitude globalQ endpointQ C : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {n : ℕ} {sample : FiniteSample n}
    (h : sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) :
    sample.NoFeedbackTies lam (feedbackA2AsymptoticBuffer amplitude n) 0 :=
  feedbackA1GoodEvent.noFeedbackTies (feedbackSelectorGoodEvent.a1 h)

theorem feedbackSelectorGoodEvent.energy {lam amplitude globalQ endpointQ C : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {n : ℕ} {sample : FiniteSample n}
    (h : sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) :
    sample.feedbackFGL2OptimizerEnergy
      hlam0.le (hlam.trans (by norm_num)) amplitude ≤ C * n := h.2

/-- The same fixed amplitude and energy level make the entire actual good event arbitrarily
likely. This is the event used before the countable residual/constraint extraction. -/
theorem exists_feedbackSelectorGood_parameters {lam δ : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ amplitude globalQ endpointQ C : ℝ,
      0 < amplitude ∧ 0 < globalQ ∧ 1 ≤ endpointQ ∧
      8 * (globalQ + 33) < amplitude ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n)ᶜ < δ := by
  obtain ⟨q, qE, A, C, hq, hqE, hA, hC, htail⟩ :=
    FiniteSample.exists_feedbackFGL2_comparison_parameters hlam0 hlam
      (show 0 < δ / 2 by positivity)
  let ratio := quadraticUpperConstant lam /
    (euclideanCurvatureLower * quadraticLowerConstant' lam)
  have hratio : 0 < ratio := by
    apply div_pos
    · unfold quadraticUpperConstant
      positivity
    · exact mul_pos euclideanCurvatureLower_pos (quadraticLowerConstant'_pos hlam0.le hlam)
  refine ⟨A, q, qE, ratio * C, by linarith, hq, hqE, hA, mul_pos hratio hC, ?_⟩
  filter_upwards [htail,
    FiniteSample.eventually_feedbackFGL2OptimizerEnergy_le_of_A2Good_of_comparisonEnergy
      (C := C) (endpointQ := qE) hlam0 hlam hq hA] with n hn htransfer
  have hsub : (feedbackSelectorGoodEvent hlam0 hlam A q qE (ratio * C) n)ᶜ ⊆
      feedbackA2AsymptoticBadEvent hlam0 hlam A q qE n ∪
      {sample : FiniteSample n | C * n < sample.graphComparisonEnergy
        (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) A)} := by
    intro sample hs
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    apply hs
    refine ⟨hnot.1, ?_⟩
    have hb := htransfer sample hnot.1 hnot.2
    change _ ≤ ratio * (C * n) at hb
    simpa only [mem_ofPred_eq, mul_assoc] using hb
  have hm := (measureReal_mono
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) hsub).trans
    (measureReal_union_le _ _)
  linarith [hn.1, hn.2]

/-- Good samples survive to the genuine A2 horizon; all numerical inputs are discharged
eventually by the original square-root-buffer parameter choice. -/
theorem eventually_feedbackSelectorGood_survival
    {lam amplitude globalQ endpointQ C : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hcoefficient : 8 * (globalQ + 33) < amplitude) :
    ∀ᶠ n : ℕ in atTop, ∀ sample : FiniteSample n,
      sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n →
      safeFeedbackA1StopTime hlam0.le (hlam.trans (by norm_num))
        (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude n)
        (feedbackA2AsymptoticBuffer amplitude n) 0
        (feedbackA2AsymptoticHorizon amplitude n) sample =
          (feedbackA2AsymptoticHorizon amplitude n : WithTop ℝ≥0) := by
  have hA : 0 < amplitude := by linarith
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hA,
    eventually_feedbackA2Asymptotic_regularity_inequalities hlam0 hA,
    eventually_feedbackA2Asymptotic_threshold hcoefficient] with n hn hreg hthreshold
  intro sample hs
  exact feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon
    sample hlam0 hlam hn.1 hn.2.1 hn.2.2.1
    (feedbackA2AsymptoticEta_pos hlam0).le hn.2.2.2.1.le
    hreg.1 hreg.2 hthreshold hs.1

end OTSelector
