import OTSelector.Feedback.RevealedCounting

/-!
# Predictable pre-jump remaining counts

The remaining-count processes in this file deliberately use `countBefore`.  Thus a jump at `t`
is not included in the state used at time `t`.  The file stops at predictability.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Initial remaining counts -/

noncomputable def initialSourceRemainingReal
    (x0 p0 : ℝ) (ω : FiniteSample n) : ℝ :=
  (n : ℝ) - (ω.initialSeenSource x0 p0).card

noncomputable def initialTargetRemainingReal
    (x0 p0 : ℝ) (ω : FiniteSample n) : ℝ :=
  (n : ℝ) - (ω.initialSeenTarget x0 p0).card

/-- The safe initial source remainder is zero on the tie fallback branch. -/
noncomputable def safeInitialSourceRemainingReal
    (lam x0 p0 : ℝ) (ω : FiniteSample n) : ℝ :=
  if ω.NoFeedbackTies lam x0 p0 then
    initialSourceRemainingReal x0 p0 ω else 0

/-- The safe initial target remainder is zero on the tie fallback branch. -/
noncomputable def safeInitialTargetRemainingReal
    (lam x0 p0 : ℝ) (ω : FiniteSample n) : ℝ :=
  if ω.NoFeedbackTies lam x0 p0 then
    initialTargetRemainingReal x0 p0 ω else 0

private theorem stronglyMeasurable_initialSourceRemaining_usual_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ safeInitialSourceRemainingReal lam x0 p0 ω) := by
  have hseen : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ ω.initialSeenSource x0 p0) := by
    exact @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0)
      (fun ω ↦ ω.initialSeenSource x0 p0) (fun i ↦
        measurableSet_mem_initialSeenSource_usual_zero
          (n := n) hlam0 hlamHalf x0 p0 i)
  have hcardNat : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ (ω.initialSeenSource x0 p0).card) :=
    measurable_finset_card.comp hseen
  have hcard : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ ((ω.initialSeenSource x0 p0).card : ℝ)) :=
    (continuous_of_discreteTopology
      (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp hcardNat
  have hgood : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (feedbackGoodEvent (n := n) lam x0 p0) :=
    measurableSet_feedbackGoodEvent_usual_zero
      (n := n) hlam0 hlamHalf x0 p0
  have hsafe : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ safeInitialSourceRemainingReal lam x0 p0 ω) := by
    change Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦
        if ω.NoFeedbackTies lam x0 p0 then
          (n : ℝ) - (ω.initialSeenSource x0 p0).card else 0)
    exact Measurable.ite hgood
      ((measurable_const : Measurable[
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
        (fun _ : FiniteSample n ↦ (n : ℝ))).sub hcard)
      measurable_const
  exact hsafe.stronglyMeasurable

private theorem stronglyMeasurable_initialTargetRemaining_usual_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ safeInitialTargetRemainingReal lam x0 p0 ω) := by
  have hseen : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ ω.initialSeenTarget x0 p0) := by
    exact @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0)
      (fun ω ↦ ω.initialSeenTarget x0 p0) (fun j ↦
        measurableSet_mem_initialSeenTarget_usual_zero
          (n := n) hlam0 hlamHalf x0 p0 j)
  have hcardNat : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ (ω.initialSeenTarget x0 p0).card) :=
    measurable_finset_card.comp hseen
  have hcard : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ ((ω.initialSeenTarget x0 p0).card : ℝ)) :=
    (continuous_of_discreteTopology
      (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp hcardNat
  have hgood : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (feedbackGoodEvent (n := n) lam x0 p0) :=
    measurableSet_feedbackGoodEvent_usual_zero
      (n := n) hlam0 hlamHalf x0 p0
  have hsafe : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ safeInitialTargetRemainingReal lam x0 p0 ω) := by
    change Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦
        if ω.NoFeedbackTies lam x0 p0 then
          (n : ℝ) - (ω.initialSeenTarget x0 p0).card else 0)
    exact Measurable.ite hgood
      ((measurable_const : Measurable[
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
        (fun _ : FiniteSample n ↦ (n : ℝ))).sub hcard)
      measurable_const
  exact hsafe.stronglyMeasurable

/-! ## Strictly pre-jump remaining counts -/

noncomputable def safeSourceRemainingBefore
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) : ℝ :=
  safeInitialSourceRemainingReal lam x0 p0 ω -
    (CountingProcess.countBefore
      (safeSourceCount hlam0 hlamHalf x0 p0) t ω : ℝ)

noncomputable def safeTargetRemainingBefore
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) : ℝ :=
  safeInitialTargetRemainingReal lam x0 p0 ω -
    (CountingProcess.countBefore
      (safeTargetCount hlam0 hlamHalf x0 p0) t ω : ℝ)

theorem safeSourceRemainingBefore_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t ω) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hinit : IsStronglyPredictable ℱ
      (fun _ ω ↦ safeInitialSourceRemainingReal lam x0 p0 ω) :=
    CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
      (fun t ↦ (stronglyMeasurable_initialSourceRemaining_usual_zero
        hlam0 hlamHalf x0 p0).mono (ℱ.mono bot_le))
      (fun _ ↦ continuous_const)
  have hN := safeSourceCount_isSimpleCountingProcess (n := n) hlam0 hlamHalf x0 p0
  have hcount : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) z.1 z.2 : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry fun t ω ↦
      safeInitialSourceRemainingReal lam x0 p0 ω -
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t ω : ℝ))
  convert hinit.sub hcount using 1
  funext z
  rfl

theorem safeTargetRemainingBefore_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t ω) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hinit : IsStronglyPredictable ℱ
      (fun _ ω ↦ safeInitialTargetRemainingReal lam x0 p0 ω) :=
    CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
      (fun t ↦ (stronglyMeasurable_initialTargetRemaining_usual_zero
        hlam0 hlamHalf x0 p0).mono (ℱ.mono bot_le))
      (fun _ ↦ continuous_const)
  have hN := safeTargetCount_isSimpleCountingProcess (n := n) hlam0 hlamHalf x0 p0
  have hcount : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) z.1 z.2 : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry fun t ω ↦
      safeInitialTargetRemainingReal lam x0 p0 ω -
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t ω : ℝ))
  convert hinit.sub hcount using 1
  funext z
  rfl

end FiniteSample

end OTSelector
