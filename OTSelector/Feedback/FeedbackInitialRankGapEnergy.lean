import OTSelector.Feedback.FeedbackI3ConditionalGap
import OTSelector.Feedback.FeedbackA1Excursion

/-!
# Initial-crossing rank-gap suffix energy

Full-rank arrivals compress the part left of `(B,0)` to time zero.  This file controls only
an edge's suffix from that boundary to its later endpoint, retained through A1.
-/

open Filter MeasureTheory Set
open scoped Classical ENNReal NNReal ProbabilityTheory

namespace OTSelector.FiniteSample
open OTSelector.CountingProcess
variable {n : ℕ}

/-- Remaining length of a source-first rank edge crossing the initial boundary, through A1. -/
noncomputable def sourceInitialStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
      0 < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample then
    (cappedStoppingValue T (targetFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)
  else 0

/-- Initial opposite-colour backlog, charged only to initially seen source ranks. -/
noncomputable def sourceInitialFullRankBacklog
    (B : ℝ) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if r.val < (sample.initialSeenSource B 0).card then
    max 0 ((r.val : ℝ) - (sample.initialSeenTarget B 0).card)
  else 0

theorem measurable_sourceInitialStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    Measurable (sourceInitialStoppedFullRankGap
      (n := n) hlam0 hlamHalf eta B T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta B 0 T
  exact Measurable.ite
    ((measurableSet_eq_fun hsource.measurable' measurable_const).inter
      ((measurableSet_lt measurable_const htarget.measurable').inter
        (measurableSet_le htarget.measurable' hA1.measurable')))
    (measurable_coe_nnreal_real.comp (measurable_cappedStoppingValue F htarget T))
    measurable_const

theorem sourceInitialStoppedFullRankGap_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ sourceInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample := by
  unfold sourceInitialStoppedFullRankGap
  split_ifs <;> positivity

theorem sourceInitialFullRankBacklog_nonneg
    (B : ℝ) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ sourceInitialFullRankBacklog B r sample := by
  unfold sourceInitialFullRankBacklog
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem sourceInitialFullRankBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    StronglyMeasurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (sourceInitialFullRankBacklog B r) := by
  have hsource : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (fun sample : FiniteSample n ↦ sample.initialSeenSource B 0) :=
    @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0)
      _ (fun i ↦ measurableSet_mem_initialSeenSource_usual_zero
        (n := n) hlam0 hlamHalf B 0 i)
  have htarget : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (fun sample : FiniteSample n ↦ sample.initialSeenTarget B 0) :=
    @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0)
      _ (fun i ↦ measurableSet_mem_initialSeenTarget_usual_zero
        (n := n) hlam0 hlamHalf B 0 i)
  have hscard := measurable_finset_card.comp hsource
  have htcard := (continuous_of_discreteTopology
    (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp
      (measurable_finset_card.comp htarget)
  exact (Measurable.ite (measurableSet_lt measurable_const hscard)
    (measurable_const.max (measurable_const.sub htcard)) measurable_const).stronglyMeasurable

theorem sourceInitialFullRankBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦ sourceInitialFullRankBacklog B r sample ^ 2)
      (finiteSampleLaw n) := by
  have hm := (sourceInitialFullRankBacklog_stronglyMeasurable hlam0 hlamHalf B r).mono
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf B 0).le 0)
  refine Integrable.of_bound (hm.pow 2).aestronglyMeasurable ((n : ℝ) ^ 2)
    (ae_of_all _ fun sample ↦ ?_)
  have h0 := sourceInitialFullRankBacklog_nonneg B r sample
  have hle : sourceInitialFullRankBacklog B r sample ≤ n := by
    unfold sourceInitialFullRankBacklog
    split_ifs
    · apply max_le (by positivity)
      have hr : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
      have hcard : (0 : ℝ) ≤ (sample.initialSeenTarget B 0).card := by positivity
      linarith
    · positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- The zero-start suffix reduces to initial backlog or the actual bulk lower occupation. -/
theorem sourceInitialStoppedFullRankGap_tail_subset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n | (q : ℝ) <
      sourceInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample} ⊆
    {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      sourceInitialFullRankBacklog B r sample} ∪
    stoppedLowerOccupationEvent
      (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) (fun _ ↦ 0)
      (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B B 0 T)
      (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  simp only [Set.mem_ofPred_eq] at hgap
  unfold sourceInitialStoppedFullRankGap at hgap
  split_ifs at hgap with hgood
  swap
  · exact (not_lt_of_ge q.2 hgap).elim
  have hfirst : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r := by
    change sourceFullRankEventTime hlam0 hlamHalf B r sample < _
    rw [hgood.1]
    exact hgood.2.1
  have hstart : feedbackFullRankStart hlam0 hlamHalf B T r sample = 0 := by
    apply WithTop.coe_eq_coe.mp
    simpa only [hgood.1, WithTop.coe_zero] using
      coe_feedbackFullRankStart_eq_source_of_sourceFirst_of_target_le_A1
        hlam0 hlamHalf eta B B 0 T r sample hfirst hgood.2.2
  have hcap : cappedStoppingValue T
      (sourceFullRankEventTime hlam0 hlamHalf B r) sample = 0 := by
    apply WithTop.coe_eq_coe.mp
    rw [coe_cappedStoppingValue, hgood.1]
    exact min_eq_left (WithTop.coe_le_coe.mpr bot_le)
  have hmask : r.val < (sample.initialSeenSource B 0).card := by
    have hcount := (sourceFullRankEventTime_le_iff_lt_sourceFullCount
      hlam0 hlamHalf B r 0 sample).mp (le_of_eq hgood.1)
    simpa only [sourceFullCount_eq_initial_card_add_safeSourceCount,
      safeSourceCount_zero, Nat.add_zero] using hcount
  have hback : sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample =
      sourceInitialFullRankBacklog B r sample := by
    simp only [sourceFirstFullRankBacklog, hstart,
      targetFullCount_eq_initial_card_add_safeTargetCount, safeTargetCount_zero,
      Nat.add_zero, sourceInitialFullRankBacklog, hmask, ↓reduceIte]
  have h := sourceFirstFullRank_cappedGap_tail hlam0 hlamHalf eta B T q r sample
    hfirst hgood.2.2 (by simpa only [hcap, NNReal.coe_zero, sub_zero] using hgap)
  rcases h with h | h
  · exact Or.inl (by simpa only [Set.mem_ofPred_eq, ← hback] using h)
  · right
    simpa only [stoppedLowerOccupationEvent, Set.mem_ofPred_eq, hstart] using h

/-- Remaining length of a target-first rank edge crossing the initial boundary, through A1. -/
noncomputable def targetInitialStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if targetFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
      0 < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample then
    (cappedStoppingValue T (sourceFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)
  else 0

/-- Initial opposite-colour backlog, charged only to initially seen target ranks. -/
noncomputable def targetInitialFullRankBacklog
    (B : ℝ) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if r.val < (sample.initialSeenTarget B 0).card then
    max 0 ((r.val : ℝ) - (sample.initialSeenSource B 0).card)
  else 0

theorem measurable_targetInitialStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    Measurable (targetInitialStoppedFullRankGap
      (n := n) hlam0 hlamHalf eta B T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta B 0 T
  exact Measurable.ite
    ((measurableSet_eq_fun htarget.measurable' measurable_const).inter
      ((measurableSet_lt measurable_const hsource.measurable').inter
        (measurableSet_le hsource.measurable' hA1.measurable')))
    (measurable_coe_nnreal_real.comp (measurable_cappedStoppingValue F hsource T))
    measurable_const

theorem targetInitialStoppedFullRankGap_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ targetInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample := by
  unfold targetInitialStoppedFullRankGap
  split_ifs <;> positivity

theorem targetInitialFullRankBacklog_nonneg
    (B : ℝ) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ targetInitialFullRankBacklog B r sample := by
  unfold targetInitialFullRankBacklog
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem targetInitialFullRankBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    StronglyMeasurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (targetInitialFullRankBacklog B r) := by
  have htarget : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (fun sample : FiniteSample n ↦ sample.initialSeenTarget B 0) :=
    @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0)
      _ (fun i ↦ measurableSet_mem_initialSeenTarget_usual_zero
        (n := n) hlam0 hlamHalf B 0 i)
  have hsource : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0]
      (fun sample : FiniteSample n ↦ sample.initialSeenSource B 0) :=
    @measurable_finset_of_mem n (FiniteSample n)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 0)
      _ (fun i ↦ measurableSet_mem_initialSeenSource_usual_zero
        (n := n) hlam0 hlamHalf B 0 i)
  have hscard := measurable_finset_card.comp htarget
  have htcard := (continuous_of_discreteTopology
    (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp
      (measurable_finset_card.comp hsource)
  exact (Measurable.ite (measurableSet_lt measurable_const hscard)
    (measurable_const.max (measurable_const.sub htcard)) measurable_const).stronglyMeasurable

theorem targetInitialFullRankBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦ targetInitialFullRankBacklog B r sample ^ 2)
      (finiteSampleLaw n) := by
  have hm := (targetInitialFullRankBacklog_stronglyMeasurable hlam0 hlamHalf B r).mono
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf B 0).le 0)
  refine Integrable.of_bound (hm.pow 2).aestronglyMeasurable ((n : ℝ) ^ 2)
    (ae_of_all _ fun sample ↦ ?_)
  have h0 := targetInitialFullRankBacklog_nonneg B r sample
  have hle : targetInitialFullRankBacklog B r sample ≤ n := by
    unfold targetInitialFullRankBacklog
    split_ifs
    · apply max_le (by positivity)
      have hr : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
      have hcard : (0 : ℝ) ≤ (sample.initialSeenSource B 0).card := by positivity
      linarith
    · positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- The zero-start suffix reduces to initial backlog or the actual bulk lower occupation. -/
theorem targetInitialStoppedFullRankGap_tail_subset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n | (q : ℝ) <
      targetInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample} ⊆
    {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      targetInitialFullRankBacklog B r sample} ∪
    stoppedLowerOccupationEvent
      (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0) (fun _ ↦ 0)
      (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B B 0 T)
      (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  simp only [Set.mem_ofPred_eq] at hgap
  unfold targetInitialStoppedFullRankGap at hgap
  split_ifs at hgap with hgood
  swap
  · exact (not_lt_of_ge q.2 hgap).elim
  have hfirst : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r := by
    change targetFullRankEventTime hlam0 hlamHalf B r sample < _
    rw [hgood.1]
    exact hgood.2.1
  have hstart : feedbackFullRankStart hlam0 hlamHalf B T r sample = 0 := by
    apply WithTop.coe_eq_coe.mp
    simpa only [hgood.1, WithTop.coe_zero] using
      coe_feedbackFullRankStart_eq_target_of_targetFirst_of_source_le_A1
        hlam0 hlamHalf eta B B 0 T r sample hfirst hgood.2.2
  have hcap : cappedStoppingValue T
      (targetFullRankEventTime hlam0 hlamHalf B r) sample = 0 := by
    apply WithTop.coe_eq_coe.mp
    rw [coe_cappedStoppingValue, hgood.1]
    exact min_eq_left (WithTop.coe_le_coe.mpr bot_le)
  have hmask : r.val < (sample.initialSeenTarget B 0).card := by
    have hcount := (targetFullRankEventTime_le_iff_lt_targetFullCount
      hlam0 hlamHalf B r 0 sample).mp (le_of_eq hgood.1)
    simpa only [targetFullCount_eq_initial_card_add_safeTargetCount,
      safeTargetCount_zero, Nat.add_zero] using hcount
  have hback : targetFirstFullRankBacklog hlam0 hlamHalf B T r sample =
      targetInitialFullRankBacklog B r sample := by
    simp only [targetFirstFullRankBacklog, hstart,
      sourceFullCount_eq_initial_card_add_safeSourceCount, safeSourceCount_zero,
      Nat.add_zero, targetInitialFullRankBacklog, hmask, ↓reduceIte]
  have h := targetFirstFullRank_cappedGap_tail hlam0 hlamHalf eta B T q r sample
    hfirst hgood.2.2 (by simpa only [hcap, NNReal.coe_zero, sub_zero] using hgap)
  rcases h with h | h
  · exact Or.inl (by simpa only [Set.mem_ofPred_eq, ← hback] using h)
  · right
    simpa only [stoppedLowerOccupationEvent, Set.mem_ofPred_eq, hstart] using h


/-- The initial-crossing tail is conditioned on the original time-zero revealed history. -/
theorem condExp_sourceInitialStoppedFullRankGap_tail_le
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n)
    {q : ℝ≥0} (hq : 0 < q) :
    condExp (usualRevealedFiltration (n := n) hlam0.le (by linarith) B 0 0)
      (finiteSampleLaw n : Measure (FiniteSample n))
      ({sample | (q : ℝ) < sourceInitialStoppedFullRankGap
        hlam0.le (by linarith) eta B T r sample}.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
          (finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦
        (if sourceInitialFullRankBacklog B r sample >
          lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) then 1 else 0) +
        Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (q : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  have hsigma : IsStoppingTime F (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0)) :=
    isStoppingTime_const F 0
  let E : Set (FiniteSample n) := {sample | (q : ℝ) <
    sourceInitialStoppedFullRankGap hlam0.le hlamHalf eta B T r sample}
  let D : Set (FiniteSample n) := {sample |
    lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      sourceInitialFullRankBacklog B r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0) (fun _ ↦ 0)
    (safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_sourceInitialStoppedFullRankGap hlam0.le hlamHalf hB eta T r)
  have hD : MeasurableSet[F 0] D := measurableSet_lt measurable_const
    (sourceInitialFullRankBacklog_stronglyMeasurable hlam0.le hlamHalf B r).measurable
  have hO : MeasurableSet O :=
    measurableSet_stoppedLowerOccupationEvent_bounded
      (safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0)
      hsigma (fun _ ↦ (show (0 : ℝ≥0) ≤ T from bot_le))
      (safeFeedbackA1StopTime_isStoppingTime
        (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hOcc := safeTargetBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (fun _ ↦ (show (0 : ℝ≥0) ≤ T from bot_le))
  rw [IsStoppingTime.measurableSpace_const F 0] at hOcc
  have hout := condExp_indicator_le_indicator_add_of_subset
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    (F.le 0) hE hD hO
    (sourceInitialStoppedFullRankGap_tail_subset hlam0.le hlamHalf eta B T q r) hOcc
  simpa only [E, D, O, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-- The actual initial-crossing suffix has a conditional second moment with the masked
initial backlog.  No tail or energy bound is assumed. -/
theorem sourceInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      sourceInitialStoppedFullRankGap hlam0.le (by linarith) eta B T r sample ^ 2)
      (finiteSampleLaw n) ∧
    condExp (usualRevealedFiltration (n := n) hlam0.le (by linarith) B 0 0)
      (finiteSampleLaw n : Measure (FiniteSample n))
      (fun sample ↦ sourceInitialStoppedFullRankGap
        hlam0.le (by linarith) eta B T r sample ^ 2) ≤ᵐ[
          (finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦ (sourceInitialFullRankBacklog B r sample /
        lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
        2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  have hrates := lowerOccupation_rates_pos (c₀ := (1 : ℝ) / 2) (by norm_num)
  simpa only [mul_one] using (integrable_sq_and_condExp_sq_le_of_tail (C := 1)
    (F.le 0)
    (sourceInitialStoppedFullRankGap hlam0.le hlamHalf eta B T r)
    (sourceInitialFullRankBacklog B r)
    (measurable_sourceInitialStoppedFullRankGap hlam0.le hlamHalf hB eta T r)
    (sourceInitialStoppedFullRankGap_nonneg hlam0.le hlamHalf eta B T r)
    (sourceInitialFullRankBacklog_stronglyMeasurable hlam0.le hlamHalf B r)
    (sourceInitialFullRankBacklog_nonneg B r)
    (sourceInitialFullRankBacklog_sq_integrable hlam0.le hlamHalf B r)
    hrates.1 (by norm_num) hrates.2 (by
    intro q hq
    let qnn : ℝ≥0 := Real.toNNReal q
    have hqnn : 0 < qnn := Real.toNNReal_pos.mpr hq
    have hqcoe : (qnn : ℝ) = q := Real.coe_toNNReal q hq.le
    simpa only [hqcoe, one_mul] using
      condExp_sourceInitialStoppedFullRankGap_tail_le hlam0 hlam hn hB heta0 hetaSmall T r hqnn))

/-- The initial-crossing tail is conditioned on the original time-zero revealed history. -/
theorem condExp_targetInitialStoppedFullRankGap_tail_le
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n)
    {q : ℝ≥0} (hq : 0 < q) :
    condExp (usualRevealedFiltration (n := n) hlam0.le (by linarith) B 0 0)
      (finiteSampleLaw n : Measure (FiniteSample n))
      ({sample | (q : ℝ) < targetInitialStoppedFullRankGap
        hlam0.le (by linarith) eta B T r sample}.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
          (finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦
        (if targetInitialFullRankBacklog B r sample >
          lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) then 1 else 0) +
        Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (q : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  have hsigma : IsStoppingTime F (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0)) :=
    isStoppingTime_const F 0
  let E : Set (FiniteSample n) := {sample | (q : ℝ) <
    targetInitialStoppedFullRankGap hlam0.le hlamHalf eta B T r sample}
  let D : Set (FiniteSample n) := {sample |
    lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      targetInitialFullRankBacklog B r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0) (fun _ ↦ 0)
    (safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_targetInitialStoppedFullRankGap hlam0.le hlamHalf hB eta T r)
  have hD : MeasurableSet[F 0] D := measurableSet_lt measurable_const
    (targetInitialFullRankBacklog_stronglyMeasurable hlam0.le hlamHalf B r).measurable
  have hO : MeasurableSet O :=
    measurableSet_stoppedLowerOccupationEvent_bounded
      (safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0)
      hsigma (fun _ ↦ (show (0 : ℝ≥0) ≤ T from bot_le))
      (safeFeedbackA1StopTime_isStoppingTime
        (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hOcc := safeSourceBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (fun _ ↦ (show (0 : ℝ≥0) ≤ T from bot_le))
  rw [IsStoppingTime.measurableSpace_const F 0] at hOcc
  have hout := condExp_indicator_le_indicator_add_of_subset
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    (F.le 0) hE hD hO
    (targetInitialStoppedFullRankGap_tail_subset hlam0.le hlamHalf eta B T q r) hOcc
  simpa only [E, D, O, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-- The actual initial-crossing suffix has a conditional second moment with the masked
initial backlog.  No tail or energy bound is assumed. -/
theorem targetInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      targetInitialStoppedFullRankGap hlam0.le (by linarith) eta B T r sample ^ 2)
      (finiteSampleLaw n) ∧
    condExp (usualRevealedFiltration (n := n) hlam0.le (by linarith) B 0 0)
      (finiteSampleLaw n : Measure (FiniteSample n))
      (fun sample ↦ targetInitialStoppedFullRankGap
        hlam0.le (by linarith) eta B T r sample ^ 2) ≤ᵐ[
          (finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦ (targetInitialFullRankBacklog B r sample /
        lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
        2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  have hrates := lowerOccupation_rates_pos (c₀ := (1 : ℝ) / 2) (by norm_num)
  simpa only [mul_one] using (integrable_sq_and_condExp_sq_le_of_tail (C := 1)
    (F.le 0)
    (targetInitialStoppedFullRankGap hlam0.le hlamHalf eta B T r)
    (targetInitialFullRankBacklog B r)
    (measurable_targetInitialStoppedFullRankGap hlam0.le hlamHalf hB eta T r)
    (targetInitialStoppedFullRankGap_nonneg hlam0.le hlamHalf eta B T r)
    (targetInitialFullRankBacklog_stronglyMeasurable hlam0.le hlamHalf B r)
    (targetInitialFullRankBacklog_nonneg B r)
    (targetInitialFullRankBacklog_sq_integrable hlam0.le hlamHalf B r)
    hrates.1 (by norm_num) hrates.2 (by
    intro q hq
    let qnn : ℝ≥0 := Real.toNNReal q
    have hqnn : 0 < qnn := Real.toNNReal_pos.mpr hq
    have hqcoe : (qnn : ℝ) = q := Real.coe_toNNReal q hq.le
    simpa only [hqcoe, one_mul] using
      condExp_targetInitialStoppedFullRankGap_tail_le hlam0 hlam hn hB heta0 hetaSmall T r hqnn))


private theorem integral_sq_le_of_initial_condExp
    {Ω : Type*} [m0 : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    {mu : @Measure Ω m0} [IsProbabilityMeasure mu] (hm : m ≤ m0)
    (X K : Ω → ℝ) (c d : ℝ)
    (hK : Integrable (fun sample ↦ K sample ^ 2) mu)
    (hbound : condExp m mu
      (fun sample ↦ X sample ^ 2) ≤ᵐ[mu]
        fun sample ↦ (K sample / c) ^ 2 + 2 / d ^ 2) :
    (∫ sample, X sample ^ 2 ∂mu) ≤
      (1 / c ^ 2) * (∫ sample, K sample ^ 2 ∂mu) + 2 / d ^ 2 := by
  have hscaled : Integrable (fun sample ↦ (K sample / c) ^ 2) mu := by
    simpa only [div_pow] using hK.div_const (c ^ 2)
  have hmono := integral_mono_ae integrable_condExp
    (hscaled.add (integrable_const (2 / d ^ 2))) hbound
  rw [integral_condExp hm] at hmono
  simp only [Pi.add_apply] at hmono
  rw [integral_add hscaled (integrable_const _)] at hmono
  simp only [div_pow] at hmono
  rw [integral_div, integral_const] at hmono
  simpa only [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one,
    one_smul, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hmono

private theorem integral_abs_initialFeedbackCurrent_cube_le
    {lam B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    ∫ sample : FiniteSample n, |(sample.initialFeedbackCurrent B 0 : ℝ)| ^ 3
      ∂(finiteSampleLaw n) ≤ 2 * B + 5 * B * Real.sqrt B := by
  have heq : (fun sample : FiniteSample n ↦ |(sample.initialFeedbackCurrent B 0 : ℝ)| ^ 3)
      =ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
        (fun sample ↦ |(safeK0 lam B 0 sample : ℝ)| ^ 3) := by
    filter_upwards [finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := B) (p0 := 0) hlam0 hlamHalf] with sample hNoTie
    simp only [safeK0, hNoTie, ↓reduceIte]
  rw [integral_congr_ae heq]
  exact integral_abs_safeK0_cube_le hlam0 hlamHalf hn hB0 hBn

private theorem initialFeedbackCurrent_abs_cube_integrable (B : ℝ) :
    Integrable (fun sample : FiniteSample n ↦ |(sample.initialFeedbackCurrent B 0 : ℝ)| ^ 3)
      (finiteSampleLaw n) := by
  have hm : Measurable (fun sample : FiniteSample n ↦ (sample.initialFeedbackCurrent B 0 : ℝ)) :=
    (continuous_of_discreteTopology (f := fun k : ℤ ↦ (k : ℝ))).measurable.comp
      (measurable_initialFeedbackCurrent B 0)
  refine Integrable.of_bound (hm.abs.pow_const 3).aestronglyMeasurable ((n : ℝ) ^ 3)
    (ae_of_all _ fun sample ↦ ?_)
  have hs : (sample.initialSeenSource B 0).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (sample.initialSeenSource B 0))
  have ht : (sample.initialSeenTarget B 0).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (sample.initialSeenTarget B 0))
  have hk : -(n : ℤ) ≤ sample.initialFeedbackCurrent B 0 ∧
      sample.initialFeedbackCurrent B 0 ≤ (n : ℤ) := by
    rw [initialFeedbackCurrent]
    omega
  have hkr : -(n : ℝ) ≤ (sample.initialFeedbackCurrent B 0 : ℝ) ∧
      (sample.initialFeedbackCurrent B 0 : ℝ) ≤ n := by exact_mod_cast hk
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr hkr) 3

private theorem initialBacklog_oneSide_sum_le
    (n a b : ℕ) (hba : b ≤ a) :
    (∑ r : Fin n, (if r.val < a then max (0 : ℝ) ((r.val : ℝ) - b) else 0) ^ 2) ≤
      (((a - b : ℕ) : ℝ)) ^ 3 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun r ↦ b ≤ r.val ∧ r.val < a)
  have hmem (r : Fin n) : r ∈ S ↔ b ≤ r.val ∧ r.val < a := by simp [S]
  let f : {r : Fin n // r ∈ S} → Fin (a - b) := fun r ↦
    ⟨r.val.val - b, by have hr := (hmem r.val).mp r.property; omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hx := (hmem x.val).mp x.property
    have hy := (hmem y.val).mp y.property
    have hv := congrArg Fin.val hxy
    change x.val.val - b = y.val.val - b at hv
    apply Subtype.ext
    apply Fin.ext
    omega
  have hcard : S.card ≤ a - b := by
    simpa using Fintype.card_le_of_injective f hf
  have hpoint (r : Fin n) :
      (if r.val < a then max (0 : ℝ) ((r.val : ℝ) - b) else 0) ^ 2 ≤
        if r ∈ S then (((a - b : ℕ) : ℝ)) ^ 2 else 0 := by
    by_cases hra : r.val < a
    · by_cases hbr : b ≤ r.val
      · have hrS : r ∈ S := (hmem r).mpr ⟨hbr, hra⟩
        have hbr' : (b : ℝ) ≤ r.val := by exact_mod_cast hbr
        have hra' : (r.val : ℝ) ≤ a := by exact_mod_cast hra.le
        have hcast : (((a - b : ℕ) : ℝ)) = (a : ℝ) - b := Nat.cast_sub hba
        rw [ite_eq_left hra, ite_eq_left hrS, max_eq_right (sub_nonneg.mpr hbr'), hcast]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hbr') (sub_le_sub_right hra' _) 2
      · have hrS : r ∉ S := fun h ↦ hbr ((hmem r).mp h).1
        have hneg : (r.val : ℝ) - b ≤ 0 := by
          have hn : r.val ≤ b := by omega
          have h : (r.val : ℝ) ≤ b := by exact_mod_cast hn
          linarith
        simp [hra, hrS, max_eq_left hneg]
    · have hrS : r ∉ S := fun h ↦ hra ((hmem r).mp h).2
      simp [hra, hrS]
  calc
    (∑ r : Fin n, (if r.val < a then max (0 : ℝ) ((r.val : ℝ) - b) else 0) ^ 2) ≤
        ∑ r : Fin n, if r ∈ S then (((a - b : ℕ) : ℝ)) ^ 2 else 0 :=
      Finset.sum_le_sum (fun r _ ↦ hpoint r)
    _ = (S.card : ℝ) * (((a - b : ℕ) : ℝ)) ^ 2 := by simp
    _ ≤ (((a - b : ℕ) : ℝ)) * (((a - b : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = (((a - b : ℕ) : ℝ)) ^ 3 := by ring

private theorem initialBacklog_oneSide_sum_eq_zero
    (n a b : ℕ) (hab : a ≤ b) :
    (∑ r : Fin n, (if r.val < a then max (0 : ℝ) ((r.val : ℝ) - b) else 0) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r.val < a
  · have hle : (r.val : ℝ) ≤ b := by exact_mod_cast hr.le.trans hab
    simp [hr, max_eq_left (sub_nonpos.mpr hle)]
  · simp [hr]

/-- The two initial rank backlogs are supported on the excess colour and have a cubic
pointwise bound by the actual initial current. -/
theorem source_targetInitialFullRankBacklog_sq_sum_le_initialCurrent
    (B : ℝ) (sample : FiniteSample n) :
    (∑ r : Fin n, sourceInitialFullRankBacklog B r sample ^ 2) +
      (∑ r : Fin n, targetInitialFullRankBacklog B r sample ^ 2) ≤
        |(sample.initialFeedbackCurrent B 0 : ℝ)| ^ 3 := by
  let a := (sample.initialSeenSource B 0).card
  let b := (sample.initialSeenTarget B 0).card
  have hk : (sample.initialFeedbackCurrent B 0 : ℝ) = (a : ℝ) - b := by
    simp [initialFeedbackCurrent, a, b]
  rw [hk]
  change (∑ r : Fin n, (if r.val < a then max (0 : ℝ) ((r.val : ℝ) - b) else 0) ^ 2) +
    (∑ r : Fin n, (if r.val < b then max (0 : ℝ) ((r.val : ℝ) - a) else 0) ^ 2) ≤ _
  rcases le_total a b with hab | hba
  · rw [initialBacklog_oneSide_sum_eq_zero n a b hab, zero_add]
    have h := initialBacklog_oneSide_sum_le n b a hab
    have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
    rw [Nat.cast_sub hab] at h
    simpa only [abs_of_nonpos (sub_nonpos.mpr habr), neg_sub] using h
  · rw [initialBacklog_oneSide_sum_eq_zero n b a hba, add_zero]
    have h := initialBacklog_oneSide_sum_le n a b hba
    have hbar : (b : ℝ) ≤ a := by exact_mod_cast hba
    rw [Nat.cast_sub hba] at h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hbar)] using h

/-- Expected sum of squared initial-crossing suffixes through A1, under the original
finite-sample law.  This controls only the part of each crossing edge after `(B,0)`. -/
theorem source_targetInitialStoppedFullRankGap_sq_sum_integrable_and_integral_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (fun sample : FiniteSample n ↦
      (∑ r : Fin n,
          sourceInitialStoppedFullRankGap
            hlam0.le (by linarith) eta B T r sample ^ 2) +
        (∑ r : Fin n,
          targetInitialStoppedFullRankGap
            hlam0.le (by linarith) eta B T r sample ^ 2))
      (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n,
        (∑ r : Fin n,
            sourceInitialStoppedFullRankGap
              hlam0.le (by linarith) eta B T r sample ^ 2) +
          (∑ r : Fin n,
            targetInitialStoppedFullRankGap
              hlam0.le (by linarith) eta B T r sample ^ 2)
        ∂(finiteSampleLaw n)) ≤
      (2 * B + 5 * B * Real.sqrt B) /
        lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
        4 * (n : ℝ) / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let c := lowerOccupationCountRate ((1 : ℝ) / 2)
  let d := lowerOccupationDecayRate ((1 : ℝ) / 2)
  let Xplus : Fin n → FiniteSample n → ℝ := fun r ↦
    sourceInitialStoppedFullRankGap
      hlam0.le hlamHalf eta B T r
  let Xminus : Fin n → FiniteSample n → ℝ := fun r ↦
    targetInitialStoppedFullRankGap
      hlam0.le hlamHalf eta B T r
  let Kplus : Fin n → FiniteSample n → ℝ := fun r ↦
    sourceInitialFullRankBacklog B r
  let Kminus : Fin n → FiniteSample n → ℝ := fun r ↦
    targetInitialFullRankBacklog B r
  let Xsum : FiniteSample n → ℝ := fun sample ↦
    (∑ r : Fin n, Xplus r sample ^ 2) +
      (∑ r : Fin n, Xminus r sample ^ 2)
  let Ksum : FiniteSample n → ℝ := fun sample ↦
    (∑ r : Fin n, Kplus r sample ^ 2) +
      (∑ r : Fin n, Kminus r sample ^ 2)
  have hXplusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Xplus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Xplus] using
      (sourceInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
        (n := n) hlam0 hlam hn hB heta0 hetaSmall T r).1
  have hXminusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Xminus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Xminus] using
      (targetInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
        (n := n) hlam0 hlam hn hB heta0 hetaSmall T r).1
  have hXplusSumInt : Integrable
      (fun sample ↦ ∑ r : Fin n, Xplus r sample ^ 2) (finiteSampleLaw n) :=
    integrable_finsetSum _ fun r _ ↦ hXplusInt r
  have hXminusSumInt : Integrable
      (fun sample ↦ ∑ r : Fin n, Xminus r sample ^ 2) (finiteSampleLaw n) :=
    integrable_finsetSum _ fun r _ ↦ hXminusInt r
  have hXsumInt : Integrable Xsum (finiteSampleLaw n) := by
    change Integrable
      (fun sample ↦ (∑ r : Fin n, Xplus r sample ^ 2) +
        (∑ r : Fin n, Xminus r sample ^ 2)) (finiteSampleLaw n)
    apply Integrable.add
    · exact hXplusSumInt
    · exact hXminusSumInt
  have hKplusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Kplus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Kplus] using sourceInitialFullRankBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf B r
  have hKminusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Kminus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Kminus] using targetInitialFullRankBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf B r
  have hKplusSumInt : Integrable
      (fun sample ↦ ∑ r : Fin n, Kplus r sample ^ 2) (finiteSampleLaw n) :=
    integrable_finsetSum _ fun r _ ↦ hKplusInt r
  have hKminusSumInt : Integrable
      (fun sample ↦ ∑ r : Fin n, Kminus r sample ^ 2) (finiteSampleLaw n) :=
    integrable_finsetSum _ fun r _ ↦ hKminusInt r
  have hKsumInt : Integrable Ksum (finiteSampleLaw n) := by
    change Integrable
      (fun sample ↦ (∑ r : Fin n, Kplus r sample ^ 2) +
        (∑ r : Fin n, Kminus r sample ^ 2)) (finiteSampleLaw n)
    apply Integrable.add
    · exact hKplusSumInt
    · exact hKminusSumInt
  have hplusRank : ∀ r : Fin n,
      (∫ sample, Xplus r sample ^ 2 ∂(finiteSampleLaw n)) ≤
        (1 / c ^ 2) *
          (∫ sample, Kplus r sample ^ 2 ∂(finiteSampleLaw n)) + 2 / d ^ 2 := by
    intro r
    exact integral_sq_le_of_initial_condExp
      ((usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0).le 0)
      (Xplus r) (Kplus r) c d (hKplusInt r)
      (sourceInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
        hlam0 hlam hn hB heta0 hetaSmall T r).2
  have hminusRank : ∀ r : Fin n,
      (∫ sample, Xminus r sample ^ 2 ∂(finiteSampleLaw n)) ≤
        (1 / c ^ 2) *
          (∫ sample, Kminus r sample ^ 2 ∂(finiteSampleLaw n)) + 2 / d ^ 2 := by
    intro r
    exact integral_sq_le_of_initial_condExp
      ((usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0).le 0)
      (Xminus r) (Kminus r) c d (hKminusInt r)
      (targetInitialStoppedFullRankGap_integrable_sq_and_condExp_sq_le
        hlam0 hlam hn hB heta0 hetaSmall T r).2
  have hsplitX : (∫ sample, Xsum sample ∂(finiteSampleLaw n)) =
      (∑ r : Fin n, ∫ sample, Xplus r sample ^ 2 ∂(finiteSampleLaw n)) +
        (∑ r : Fin n, ∫ sample, Xminus r sample ^ 2 ∂(finiteSampleLaw n)) := by
    rw [show Xsum = fun sample ↦
        (∑ r : Fin n, Xplus r sample ^ 2) +
          (∑ r : Fin n, Xminus r sample ^ 2) by rfl,
      integral_add hXplusSumInt hXminusSumInt,
      integral_finsetSum _ (fun r _ ↦ hXplusInt r),
      integral_finsetSum _ (fun r _ ↦ hXminusInt r)]
  have hsplitK : (∫ sample, Ksum sample ∂(finiteSampleLaw n)) =
      (∑ r : Fin n, ∫ sample, Kplus r sample ^ 2 ∂(finiteSampleLaw n)) +
        (∑ r : Fin n, ∫ sample, Kminus r sample ^ 2 ∂(finiteSampleLaw n)) := by
    rw [show Ksum = fun sample ↦
        (∑ r : Fin n, Kplus r sample ^ 2) +
          (∑ r : Fin n, Kminus r sample ^ 2) by rfl,
      integral_add hKplusSumInt hKminusSumInt,
      integral_finsetSum _ (fun r _ ↦ hKplusInt r),
      integral_finsetSum _ (fun r _ ↦ hKminusInt r)]
  have hXK : (∫ sample, Xsum sample ∂(finiteSampleLaw n)) ≤
      (1 / c ^ 2) * (∫ sample, Ksum sample ∂(finiteSampleLaw n)) +
        4 * (n : ℝ) / d ^ 2 := by
    rw [hsplitX, hsplitK]
    have hp := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun r _ ↦ hplusRank r)
    have hm := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun r _ ↦ hminusRank r)
    calc
      (∑ r : Fin n, ∫ sample, Xplus r sample ^ 2 ∂(finiteSampleLaw n)) +
          (∑ r : Fin n, ∫ sample, Xminus r sample ^ 2 ∂(finiteSampleLaw n)) ≤
        (∑ r : Fin n, ((1 / c ^ 2) *
            (∫ sample, Kplus r sample ^ 2 ∂(finiteSampleLaw n)) + 2 / d ^ 2)) +
          (∑ r : Fin n, ((1 / c ^ 2) *
            (∫ sample, Kminus r sample ^ 2 ∂(finiteSampleLaw n)) + 2 / d ^ 2)) :=
        add_le_add hp hm
      _ = (1 / c ^ 2) *
          ((∑ r : Fin n, ∫ sample, Kplus r sample ^ 2 ∂(finiteSampleLaw n)) +
            (∑ r : Fin n, ∫ sample, Kminus r sample ^ 2 ∂(finiteSampleLaw n))) +
          4 * (n : ℝ) / d ^ 2 := by
        simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        ring
  have hKbound : (∫ sample, Ksum sample ∂(finiteSampleLaw n)) ≤
      2 * B + 5 * B * Real.sqrt B := by
    calc
      ∫ sample, Ksum sample ∂(finiteSampleLaw n) ≤
          ∫ sample : FiniteSample n, |(sample.initialFeedbackCurrent B 0 : ℝ)| ^ 3
            ∂(finiteSampleLaw n) :=
        integral_mono hKsumInt (initialFeedbackCurrent_abs_cube_integrable B)
          (source_targetInitialFullRankBacklog_sq_sum_le_initialCurrent B)
      _ ≤ 2 * B + 5 * B * Real.sqrt B :=
        integral_abs_initialFeedbackCurrent_cube_le hlam0.le hlamHalf hn hB.le hBn
  constructor
  · exact hXsumInt
  · have hfinal := hXK.trans (add_le_add
      (mul_le_mul_of_nonneg_left hKbound (by positivity : 0 ≤ 1 / c ^ 2))
      (le_refl (4 * (n : ℝ) / d ^ 2)))
    simpa only [Xsum, Xplus, Xminus, c, d, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hfinal

end OTSelector.FiniteSample
