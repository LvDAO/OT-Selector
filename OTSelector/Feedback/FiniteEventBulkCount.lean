import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Feedback.RevealedCounting
import OTSelector.Probability.CountingProcess.FiniteEventUsualRectangle

/-!
# Finite bulk-event counts

The predictable bulk mask thins the safe source and target event families.  This file gives the
resulting event times and counts public names and records the stopping-time, path, and adaptedness
properties needed by the finite-event intensity construction.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Bulk-thinned event times and counts -/

/-- The safe source event time retained precisely when the predictable bulk mask is nonzero at
that event. -/
noncomputable def safeSourceBulkEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (i : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.thinnedEventTime
    (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
    (sourceEventTime hlam0 hlamHalf x0 p0 i)

/-- The safe target event time retained precisely when the predictable bulk mask is nonzero at
that event. -/
noncomputable def safeTargetBulkEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (j : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.thinnedEventTime
    (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
    (targetEventTime hlam0 hlamHalf x0 p0 j)

/-- The finite source count after predictable bulk-mask thinning. -/
noncomputable def safeSourceBulkCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountThinned
    (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t

/-- The finite target count after predictable bulk-mask thinning. -/
noncomputable def safeTargetBulkCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountThinned
    (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t

/-! ## Event-time properties -/

theorem safeSourceBulkEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (i : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i) := by
  simpa only [safeSourceBulkEventTime] using
    (CountingProcess.isStoppingTime_thinnedEventTime_of_predictable
      (sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 i)
      (safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0))

theorem safeTargetBulkEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (j : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j) := by
  simpa only [safeTargetBulkEventTime] using
    (CountingProcess.isStoppingTime_thinnedEventTime_of_predictable
      (targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 j)
      (safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0))

theorem safeSourceBulkEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (sample : FiniteSample n) (i : Fin n) :
    safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample = ⊤ ∨
      (0 : WithTop ℝ≥0) <
        safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample := by
  simpa only [safeSourceBulkEventTime] using
    (CountingProcess.thinnedEventTime_eq_top_or_pos
      (G := safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun sample ↦ sourceEventTime_eq_top_or_pos
        (n := n) hlam0 hlamHalf x0 p0 sample i) sample)

theorem safeTargetBulkEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (sample : FiniteSample n) (j : Fin n) :
    safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j sample = ⊤ ∨
      (0 : WithTop ℝ≥0) <
        safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j sample := by
  simpa only [safeTargetBulkEventTime] using
    (CountingProcess.thinnedEventTime_eq_top_or_pos
      (G := safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun sample ↦ targetEventTime_eq_top_or_pos
        (n := n) hlam0 hlamHalf x0 p0 sample j) sample)

theorem safeSourceBulkEventTime_injective
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    ∀ (sample : FiniteSample n) (i j : Fin n),
      safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≠ ⊤ →
      safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j sample ≠ ⊤ →
      safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample =
        safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j sample →
      i = j := by
  simpa only [safeSourceBulkEventTime] using
    (CountingProcess.thinnedEventTime_family_injective
      (m := n) (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i)
      (sourceEventTime_injective (n := n) hlam0 hlamHalf x0 p0))

theorem safeTargetBulkEventTime_injective
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    ∀ (sample : FiniteSample n) (i j : Fin n),
      safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≠ ⊤ →
      safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j sample ≠ ⊤ →
      safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample =
        safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j sample →
      i = j := by
  simpa only [safeTargetBulkEventTime] using
    (CountingProcess.thinnedEventTime_family_injective
      (m := n) (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j)
      (targetEventTime_injective (n := n) hlam0 hlamHalf x0 p0))

/-! ## Adaptedness and simple-counting-process structure -/

theorem safeSourceBulkCount_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ (safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample : ℝ)) := by
  simpa only [safeSourceBulkCount, CountingProcess.finiteEventCountThinned,
    safeSourceBulkEventTime] using
    (CountingProcess.finiteEventCountTop_stronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
      (fun i ↦ safeSourceBulkEventTime_isStoppingTime
        (n := n) hlam0 hlamHalf B x0 p0 i))

theorem safeTargetBulkCount_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ (safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample : ℝ)) := by
  simpa only [safeTargetBulkCount, CountingProcess.finiteEventCountThinned,
    safeTargetBulkEventTime] using
    (CountingProcess.finiteEventCountTop_stronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
      (fun j ↦ safeTargetBulkEventTime_isStoppingTime
        (n := n) hlam0 hlamHalf B x0 p0 j))

theorem safeSourceBulkCount_isSimpleCountingProcess
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    CountingProcess.IsSimpleCountingProcess
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample) := by
  simpa only [safeSourceBulkCount, CountingProcess.finiteEventCountThinned,
    safeSourceBulkEventTime] using
    (CountingProcess.IsSimpleCountingProcess.of_finiteEventCountTop
      (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
      (fun sample i ↦ safeSourceBulkEventTime_eq_top_or_pos
        (n := n) hlam0 hlamHalf B x0 p0 sample i)
      (safeSourceBulkEventTime_injective (n := n) hlam0 hlamHalf B x0 p0)
      (safeSourceBulkCount_stronglyAdapted
        (n := n) hlam0 hlamHalf B x0 p0))

theorem safeTargetBulkCount_isSimpleCountingProcess
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    CountingProcess.IsSimpleCountingProcess
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample) := by
  simpa only [safeTargetBulkCount, CountingProcess.finiteEventCountThinned,
    safeTargetBulkEventTime] using
    (CountingProcess.IsSimpleCountingProcess.of_finiteEventCountTop
      (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
      (fun sample j ↦ safeTargetBulkEventTime_eq_top_or_pos
        (n := n) hlam0 hlamHalf B x0 p0 sample j)
      (safeTargetBulkEventTime_injective (n := n) hlam0 hlamHalf B x0 p0)
      (safeTargetBulkCount_stronglyAdapted
        (n := n) hlam0 hlamHalf B x0 p0))

/-! ## Cross-colour jump separation -/

theorem safeBulkCounts_noSimultaneousJumpsOn
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (T : ℝ≥0) :
    CountingProcess.NoSimultaneousJumpsOn
      (safeSourceBulkCount (n := n) hlam0 hlamHalf B x0 p0)
      (safeTargetBulkCount (n := n) hlam0 hlamHalf B x0 p0) T := by
  intro ω k l hk hl
  change CountingProcess.jumpTime
      (fun t ω' ↦ CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i) t ω') k ω ≠
      CountingProcess.jumpTime
        (fun t ω' ↦ CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j) t ω') l ω
  exact CountingProcess.finiteEventCountTop_cross_jumpTime_ne
    (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
    (fun ω i j hi hj ↦ by
      classical
      intro hij
      by_cases hiacc : CountingProcess.eventAccepted
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (sourceEventTime hlam0 hlamHalf x0 p0 i) ω
      · by_cases hjacc : CountingProcess.eventAccepted
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (targetEventTime hlam0 hlamHalf x0 p0 j) ω
        · apply sourceEventTime_ne_targetEventTime
            hlam0 hlamHalf x0 p0 ω i j hiacc.1 hjacc.1
          simpa only [safeSourceBulkEventTime, safeTargetBulkEventTime,
            CountingProcess.thinnedEventTime_of_accepted hiacc,
            CountingProcess.thinnedEventTime_of_accepted hjacc] using hij
        · exact hj (by
            simpa only [safeTargetBulkEventTime] using
              CountingProcess.thinnedEventTime_of_not_accepted hjacc)
      · exact hi (by
          simpa only [safeSourceBulkEventTime] using
            CountingProcess.thinnedEventTime_of_not_accepted hiacc))
    ω hk hl

end FiniteSample

end OTSelector
