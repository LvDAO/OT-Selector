import OTSelector.Limit.FeedbackRegenerationMarks
import OTSelector.Limit.FeedbackRegenerationHolding

/-!
# Marked physical feedback jumps

A physical step consists of an exponential wait, a mark, and the new current. The wait is
independent of the marked jump at the present current. Forgetting the mark recovers the existing
physical-step kernel exactly.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Limit

/-- Waiting time, jump mark, and current after the jump. -/
abbrev FeedbackMarkedStep := ℝ × UnitMark × ℤ

/-- Retain the physical waiting time and the new current. -/
def feedbackMarkedStepProjection (z : FeedbackMarkedStep) : ℝ × ℤ := (z.1, z.2.2)

@[fun_prop]
theorem measurable_feedbackMarkedStepProjection : Measurable feedbackMarkedStepProjection := by
  exact measurable_fst.prodMk measurable_snd.snd

/-- The real exponential waiting law followed by the real marked jump law. -/
noncomputable def feedbackMarkedHoldingKernel (lam : ℝ) : Kernel ℤ FeedbackMarkedStep where
  toFun k := (feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k)
  measurable' := measurable_of_countable _

theorem feedbackMarkedHoldingKernel_isMarkov {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackMarkedHoldingKernel lam) := by
  let := feedbackHoldingKernel_isMarkov hlam0 hlam
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  constructor
  intro k
  change IsProbabilityMeasure ((feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k))
  infer_instance

/-- The marked step projects to the previously constructed physical feedback step. -/
theorem feedbackMarkedHoldingKernel_map_step {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedHoldingKernel lam k).map feedbackMarkedStepProjection =
      feedbackHoldingJumpKernel lam k := by
  let := feedbackHoldingKernel_isMarkov hlam0 hlam
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  change (((feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k)).map
    (Prod.map id Prod.snd)) = (feedbackHoldingKernel lam k).prod (feedbackJumpKernel lam k)
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    feedbackMarkedJumpKernel_map_current hlam0 hlam]

theorem feedbackMarkedHoldingKernel_map {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedHoldingKernel lam).map feedbackMarkedStepProjection =
      feedbackHoldingJumpKernel lam := by
  ext k s hs
  rw [Kernel.map_apply _ measurable_feedbackMarkedStepProjection,
    feedbackMarkedHoldingKernel_map_step hlam0 hlam]

end OTSelector.Limit
