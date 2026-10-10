import OTSelector.Feedback.FeedbackI3ConditionalGap
import OTSelector.Feedback.FeedbackA1Occupation
import OTSelector.Feedback.MarkedStoppedExponential
import OTSelector.Probability.CountingProcess.FiniteEventIntegral
import OTSelector.Probability.CountingProcess.CurrentExcursion

/-!
# Summable full-rank backlogs and the interior I3 energy

The conditional rank-gap estimate is sharpened by masking its visible backlog to the branch on
which the first same-rank endpoint is positive and occurs strictly before A1.  This mask is known
at the capped minimum stopping time.  The retained backlog squares are then charged pathwise to
the source and target bulk counting integrals of the squared strict-left current.

All graph objects in this file still refer to the raw full-recursion graph.  Boundary and terminal
edges, and transport to the stopped-continuation graph, are separate layers.
-/

open Filter MeasureTheory Set
open scoped Classical ENNReal NNReal ProbabilityTheory

namespace OTSelector

namespace FiniteSample

open CountingProcess

variable {n : ℕ}

/-! ## The backlog visible on an interior A1 start -/

/-- The source full-rank endpoint is the positive capped minimum and A1 has not yet occurred. -/
def sourceInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) : Set (FiniteSample n) :=
  {sample |
    sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      ¬targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      (0 : WithTop ℝ≥0) <
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) <
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample}

/-- The symmetric target-first positive A1-start event. -/
def targetInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) : Set (FiniteSample n) :=
  {sample |
    targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      ¬sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      (0 : WithTop ℝ≥0) <
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ∧
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) <
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample}

/-- Source backlog, zeroed unless its positive source-first endpoint is strictly before A1. -/
noncomputable def sourceInteriorA1StartBacklog
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r then
    sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample
  else 0

/-- Target analogue of `sourceInteriorA1StartBacklog`. -/
noncomputable def targetInteriorA1StartBacklog
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ targetInteriorA1StartEvent hlam0 hlamHalf eta B T r then
    targetFirstFullRankBacklog hlam0 hlamHalf B T r sample
  else 0

theorem measurableSet_sourceInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    MeasurableSet[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let sigma := fun sample : FiniteSample n ↦
    (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0)
  let hsigma : IsStoppingTime F sigma :=
    feedbackFullRankStart_isStoppingTime (n := n) hlam0 hlamHalf B T r
  let hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta B 0 T
  have hsourceLe : MeasurableSet[hsigma.measurableSpace]
      {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} :=
    hsource.measurableSet_stopping_time_le hsigma
  have htargetLe : MeasurableSet[hsigma.measurableSpace]
      {sample | targetFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} :=
    htarget.measurableSet_stopping_time_le hsigma
  have hzero : MeasurableSet[hsigma.measurableSpace]
      {sample | sigma sample ≤ (0 : WithTop ℝ≥0)} := by
    simpa only [WithTop.coe_zero] using hsigma.measurableSet_le' 0
  have hA1Le : MeasurableSet[hsigma.measurableSpace]
      {sample | safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤ sigma sample} :=
    hA1.measurableSet_stopping_time_le hsigma
  have heq : sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r =
      {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} ∩
        {sample | targetFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample}ᶜ ∩
        {sample | sigma sample ≤ (0 : WithTop ℝ≥0)}ᶜ ∩
        {sample | safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤
          sigma sample}ᶜ := by
    ext sample
    simp only [sourceInteriorA1StartEvent, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
      sigma, not_le]
    tauto
  rw [heq]
  exact ((hsourceLe.inter htargetLe.compl).inter hzero.compl).inter hA1Le.compl

theorem measurableSet_targetInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    MeasurableSet[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (targetInteriorA1StartEvent hlam0 hlamHalf eta B T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let sigma := fun sample : FiniteSample n ↦
    (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0)
  let hsigma : IsStoppingTime F sigma :=
    feedbackFullRankStart_isStoppingTime (n := n) hlam0 hlamHalf B T r
  let hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta B 0 T
  have hsourceLe : MeasurableSet[hsigma.measurableSpace]
      {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} :=
    hsource.measurableSet_stopping_time_le hsigma
  have htargetLe : MeasurableSet[hsigma.measurableSpace]
      {sample | targetFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} :=
    htarget.measurableSet_stopping_time_le hsigma
  have hzero : MeasurableSet[hsigma.measurableSpace]
      {sample | sigma sample ≤ (0 : WithTop ℝ≥0)} := by
    simpa only [WithTop.coe_zero] using hsigma.measurableSet_le' 0
  have hA1Le : MeasurableSet[hsigma.measurableSpace]
      {sample | safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤ sigma sample} :=
    hA1.measurableSet_stopping_time_le hsigma
  have heq : targetInteriorA1StartEvent hlam0 hlamHalf eta B T r =
      {sample | targetFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample} ∩
        {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ sigma sample}ᶜ ∩
        {sample | sigma sample ≤ (0 : WithTop ℝ≥0)}ᶜ ∩
        {sample | safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤
          sigma sample}ᶜ := by
    ext sample
    simp only [targetInteriorA1StartEvent, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
      sigma, not_le]
    tauto
  rw [heq]
  exact ((htargetLe.inter hsourceLe.compl).inter hzero.compl).inter hA1Le.compl

theorem sourceInteriorA1StartBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    StronglyMeasurable[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r) := by
  exact Measurable.ite
    (measurableSet_sourceInteriorA1StartEvent
      (n := n) hlam0 hlamHalf hB eta T r)
    (sourceFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf B T r).measurable measurable_const |>.stronglyMeasurable

theorem targetInteriorA1StartBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    StronglyMeasurable[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r) := by
  exact Measurable.ite
    (measurableSet_targetInteriorA1StartEvent
      (n := n) hlam0 hlamHalf hB eta T r)
    (targetFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf B T r).measurable measurable_const |>.stronglyMeasurable

theorem sourceInteriorA1StartBacklog_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample := by
  unfold sourceInteriorA1StartBacklog
  split_ifs
  · exact sourceFirstFullRankBacklog_nonneg hlam0 hlamHalf B T r sample
  · exact le_rfl

theorem targetInteriorA1StartBacklog_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample := by
  unfold targetInteriorA1StartBacklog
  split_ifs
  · exact targetFirstFullRankBacklog_nonneg hlam0 hlamHalf B T r sample
  · exact le_rfl

/-! ## Start-gated conditional tails -/

theorem mem_sourceInteriorA1StartEvent_of_gap_active
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hactive : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample) :
    sample ∈ sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r := by
  have hstart := coe_feedbackFullRankStart_eq_source_of_sourceFirst_of_target_le_A1
    (n := n) hlam0 hlamHalf eta B B 0 T r sample hactive.1 hactive.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstart]
  · rw [hstart]
    exact not_le_of_gt hactive.1
  · rw [hstart]
    exact hactive.2.1
  · rw [hstart]
    exact hactive.1.trans_le hactive.2.2

theorem mem_targetInteriorA1StartEvent_of_gap_active
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hactive : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample) :
    sample ∈ targetInteriorA1StartEvent hlam0 hlamHalf eta B T r := by
  have hstart := coe_feedbackFullRankStart_eq_target_of_targetFirst_of_source_le_A1
    (n := n) hlam0 hlamHalf eta B B 0 T r sample hactive.1 hactive.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstart]
  · rw [hstart]
    exact not_le_of_gt hactive.1
  · rw [hstart]
    exact hactive.2.1
  · rw [hstart]
    exact hactive.1.trans_le hactive.2.2

theorem sourceInteriorStoppedFullRankGap_tail_subset_startGated
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n |
      (q : ℝ) < sourceInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample} ⊆
      {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample} ∪
      stoppedLowerOccupationEvent
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  have hold := sourceInteriorStoppedFullRankGap_tail_subset
    (n := n) hlam0 hlamHalf eta B T q r hgap
  have hactive : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    change (q : ℝ) < sourceInteriorStoppedFullRankGap
      hlam0 hlamHalf eta B B 0 T r sample at hgap
    unfold sourceInteriorStoppedFullRankGap at hgap
    split_ifs at hgap with hgood
    · exact hgood
    · exact (not_lt_of_ge q.2 hgap).elim
  have hstart := mem_sourceInteriorA1StartEvent_of_gap_active
    (n := n) hlam0 hlamHalf eta B T r sample hactive
  rcases hold with hback | hoccupation
  · left
    change lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample
    rw [sourceInteriorA1StartBacklog, ite_eq_left hstart]
    exact hback
  · exact Or.inr hoccupation

theorem targetInteriorStoppedFullRankGap_tail_subset_startGated
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n |
      (q : ℝ) < targetInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample} ⊆
      {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample} ∪
      stoppedLowerOccupationEvent
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  have hold := targetInteriorStoppedFullRankGap_tail_subset
    (n := n) hlam0 hlamHalf eta B T q r hgap
  have hactive : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    change (q : ℝ) < targetInteriorStoppedFullRankGap
      hlam0 hlamHalf eta B B 0 T r sample at hgap
    unfold targetInteriorStoppedFullRankGap at hgap
    split_ifs at hgap with hgood
    · exact hgood
    · exact (not_lt_of_ge q.2 hgap).elim
  have hstart := mem_targetInteriorA1StartEvent_of_gap_active
    (n := n) hlam0 hlamHalf eta B T r sample hactive
  rcases hold with hback | hoccupation
  · left
    change lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample
    rw [targetInteriorA1StartBacklog, ite_eq_left hstart]
    exact hback
  · exact Or.inr hoccupation

private theorem condExp_indicator_le_indicator_add_of_subset_i3Backlog
    {m0 m : MeasurableSpace (FiniteSample n)}
    {mu : @Measure (FiniteSample n) m0} [IsFiniteMeasure mu]
    (hm : m ≤ m0) {E D O : Set (FiniteSample n)}
    (hE : MeasurableSet[m0] E) (hD : MeasurableSet[m] D)
    (hO : MeasurableSet[m0] O) (hsubset : E ⊆ D ∪ O) {c : ℝ}
    (hOcc : condExp m mu (O.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[mu]
      fun _ ↦ c) :
    condExp m mu (E.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[mu]
      fun sample ↦ D.indicator (fun _ ↦ (1 : ℝ)) sample + c := by
  let IE : FiniteSample n → ℝ := E.indicator fun _ ↦ 1
  let ID : FiniteSample n → ℝ := D.indicator fun _ ↦ 1
  let IO : FiniteSample n → ℝ := O.indicator fun _ ↦ 1
  have hD0 : MeasurableSet[m0] D := hm D hD
  have hIEint : Integrable IE mu := (integrable_const (1 : ℝ)).indicator hE
  have hIDint : Integrable ID mu := (integrable_const (1 : ℝ)).indicator hD0
  have hIOint : Integrable IO mu := (integrable_const (1 : ℝ)).indicator hO
  have hpoint : IE ≤ fun sample ↦ ID sample + IO sample := by
    intro sample
    by_cases he : sample ∈ E
    · by_cases hd : sample ∈ D
      · by_cases ho : sample ∈ O <;> simp [IE, ID, IO, he, hd, ho]
      · have ho : sample ∈ O := (hsubset he).resolve_left hd
        simp [IE, ID, IO, he, hd, ho]
    · by_cases hd : sample ∈ D <;> by_cases ho : sample ∈ O <;>
        simp [IE, ID, IO, he, hd, ho]
  have hmono : condExp m mu IE ≤ᵐ[mu]
      condExp m mu (fun sample ↦ ID sample + IO sample) :=
    condExp_mono hIEint (hIDint.add hIOint) (Eventually.of_forall hpoint)
  have hadd : condExp m mu (fun sample ↦ ID sample + IO sample) =ᵐ[mu]
      condExp m mu ID + condExp m mu IO := condExp_add hIDint hIOint m
  have hIDstrong : StronglyMeasurable[m] ID :=
    stronglyMeasurable_const.indicator hD
  have hIDce : condExp m mu ID = ID :=
    condExp_of_stronglyMeasurable hm hIDstrong hIDint
  filter_upwards [hmono, hadd, hOcc] with sample hmonoSample haddSample hOccSample
  rw [haddSample, hIDce] at hmonoSample
  change condExp m mu IE sample ≤ ID sample + condExp m mu IO sample at hmonoSample
  change condExp m mu IE sample ≤ ID sample + c
  change condExp m mu IO sample ≤ c at hOccSample
  linarith

/-- Conditional source-first tail with the backlog zeroed outside the measurable interior A1
start branch. -/
theorem condExp_sourceInteriorStoppedFullRankGap_tail_le_startGated
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n)
    {q : ℝ≥0} (hq : 0 < q) :
    let hsigma := feedbackFullRankStart_isStoppingTime
      (n := n) hlam0.le (by linarith) B T r
    condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
        ({sample | (q : ℝ) < sourceInteriorStoppedFullRankGap
          hlam0.le (by linarith) eta B B 0 T r sample}.indicator
            (fun _ ↦ (1 : ℝ))) ≤ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦
        (if sourceInteriorA1StartBacklog hlam0.le (by linarith) eta B T r sample >
            lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) then 1 else 0) +
          Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (q : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let sigma := feedbackFullRankStart hlam0.le hlamHalf B T r
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let E : Set (FiniteSample n) :=
    {sample | (q : ℝ) < sourceInteriorStoppedFullRankGap
      hlam0.le hlamHalf eta B B 0 T r sample}
  let D : Set (FiniteSample n) :=
    {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      sourceInteriorA1StartBacklog hlam0.le hlamHalf eta B T r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0) sigma
    (safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_sourceInteriorStoppedFullRankGap
      (n := n) hlam0.le hlamHalf hB eta B 0 T r)
  have hD : MeasurableSet[hsigma.measurableSpace] D := measurableSet_lt measurable_const
    (sourceInteriorA1StartBacklog_stronglyMeasurable
      (n := n) hlam0.le hlamHalf hB eta T r).measurable
  have hO : MeasurableSet O := measurableSet_stoppedLowerOccupationEvent_bounded
    (safeTargetBulkCount_isSimpleCountingProcess
      (n := n) hlam0.le hlamHalf B B 0)
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
    (safeFeedbackA1StopTime_isStoppingTime
      (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hsubset : E ⊆ D ∪ O := by
    simpa only [E, D, O, sigma] using
      sourceInteriorStoppedFullRankGap_tail_subset_startGated
        (n := n) hlam0.le hlamHalf eta B T q r
  have hOcc := safeTargetBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
  have hout := condExp_indicator_le_indicator_add_of_subset_i3Backlog
    (m0 := (inferInstance : MeasurableSpace (FiniteSample n)))
    (m := hsigma.measurableSpace)
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    hsigma.measurableSpace_le hE hD hO hsubset hOcc
  simpa only [E, D, O, sigma, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-- Symmetric start-gated conditional tail. -/
theorem condExp_targetInteriorStoppedFullRankGap_tail_le_startGated
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n)
    {q : ℝ≥0} (hq : 0 < q) :
    let hsigma := feedbackFullRankStart_isStoppingTime
      (n := n) hlam0.le (by linarith) B T r
    condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
        ({sample | (q : ℝ) < targetInteriorStoppedFullRankGap
          hlam0.le (by linarith) eta B B 0 T r sample}.indicator
            (fun _ ↦ (1 : ℝ))) ≤ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦
        (if targetInteriorA1StartBacklog hlam0.le (by linarith) eta B T r sample >
            lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) then 1 else 0) +
          Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (q : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let sigma := feedbackFullRankStart hlam0.le hlamHalf B T r
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let E : Set (FiniteSample n) :=
    {sample | (q : ℝ) < targetInteriorStoppedFullRankGap
      hlam0.le hlamHalf eta B B 0 T r sample}
  let D : Set (FiniteSample n) :=
    {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      targetInteriorA1StartBacklog hlam0.le hlamHalf eta B T r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0) sigma
    (safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_targetInteriorStoppedFullRankGap
      (n := n) hlam0.le hlamHalf hB eta B 0 T r)
  have hD : MeasurableSet[hsigma.measurableSpace] D := measurableSet_lt measurable_const
    (targetInteriorA1StartBacklog_stronglyMeasurable
      (n := n) hlam0.le hlamHalf hB eta T r).measurable
  have hO : MeasurableSet O := measurableSet_stoppedLowerOccupationEvent_bounded
    (safeSourceBulkCount_isSimpleCountingProcess
      (n := n) hlam0.le hlamHalf B B 0)
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
    (safeFeedbackA1StopTime_isStoppingTime
      (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hsubset : E ⊆ D ∪ O := by
    simpa only [E, D, O, sigma] using
      targetInteriorStoppedFullRankGap_tail_subset_startGated
        (n := n) hlam0.le hlamHalf eta B T q r
  have hOcc := safeSourceBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
  have hout := condExp_indicator_le_indicator_add_of_subset_i3Backlog
    (m0 := (inferInstance : MeasurableSpace (FiniteSample n)))
    (m := hsigma.measurableSpace)
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    hsigma.measurableSpace_le hE hD hO hsubset hOcc
  simpa only [E, D, O, sigma, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-! ## Start-gated conditional second moments -/

theorem sourceInteriorA1StartBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ (2 : ℕ))
      (finiteSampleLaw n) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hmeas : Measurable
      (sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r) :=
    (sourceInteriorA1StartBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf hB eta T r).mono hsigma.measurableSpace_le |>.measurable
  refine Integrable.of_bound (hmeas.pow measurable_const).aestronglyMeasurable
    ((n : ℝ) ^ 2) (Eventually.of_forall fun sample ↦ ?_)
  have hback : sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ≤ n := by
    unfold sourceInteriorA1StartBacklog
    split_ifs
    · have hrn : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
      unfold sourceFirstFullRankBacklog
      rw [max_le_iff]
      constructor
      · positivity
      · have hcount0 : 0 ≤ (targetFullCount hlam0 hlamHalf B
            (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by
          positivity
        linarith
    · positivity
  have hback0 := sourceInteriorA1StartBacklog_nonneg
    hlam0 hlamHalf eta B T r sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

theorem targetInteriorA1StartBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta : ℝ) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ (2 : ℕ))
      (finiteSampleLaw n) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hmeas : Measurable
      (targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r) :=
    (targetInteriorA1StartBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf hB eta T r).mono hsigma.measurableSpace_le |>.measurable
  refine Integrable.of_bound (hmeas.pow measurable_const).aestronglyMeasurable
    ((n : ℝ) ^ 2) (Eventually.of_forall fun sample ↦ ?_)
  have hback : targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ≤ n := by
    unfold targetInteriorA1StartBacklog
    split_ifs
    · have hrn : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
      unfold targetFirstFullRankBacklog
      rw [max_le_iff]
      constructor
      · positivity
      · have hcount0 : 0 ≤ (sourceFullCount hlam0 hlamHalf B
            (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by
          positivity
        linarith
    · positivity
  have hback0 := targetInteriorA1StartBacklog_nonneg
    hlam0 hlamHalf eta B T r sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- The source-first conditional square bound with the summable start-gated backlog. -/
theorem sourceInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    let hsigma := feedbackFullRankStart_isStoppingTime
      (n := n) hlam0.le (by linarith) B T r
    Integrable (fun sample : FiniteSample n ↦
        sourceInteriorStoppedFullRankGap
          hlam0.le (by linarith) eta B B 0 T r sample ^ (2 : ℕ))
        (finiteSampleLaw n) ∧
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
          (fun sample ↦ sourceInteriorStoppedFullRankGap
            hlam0.le (by linarith) eta B B 0 T r sample ^ (2 : ℕ)) ≤ᵐ[
              (finiteSampleLaw n : Measure (FiniteSample n))]
        fun sample ↦
          (sourceInteriorA1StartBacklog
              hlam0.le (by linarith) eta B T r sample /
            lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X := sourceInteriorStoppedFullRankGap
    (n := n) hlam0.le hlamHalf eta B B 0 T r
  let K := sourceInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
  have hrates := lowerOccupation_rates_pos (c₀ := (1 : ℝ) / 2) (by norm_num)
  have hActualTail : ∀ q : ℝ, 0 < q →
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
          ({sample | q < X sample}.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
            (finiteSampleLaw n : Measure (FiniteSample n))]
        fun sample ↦
          (if K sample > lowerOccupationCountRate ((1 : ℝ) / 2) * q then 1 else 0) +
            Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * q) := by
    intro q hq
    let qnn : ℝ≥0 := Real.toNNReal q
    have hqnn : 0 < qnn := Real.toNNReal_pos.mpr hq
    have hqcoe : (qnn : ℝ) = q := Real.coe_toNNReal q hq.le
    have h := condExp_sourceInteriorStoppedFullRankGap_tail_le_startGated
      (n := n) hlam0 hlam hn hB heta0 hetaSmall T r hqnn
    simpa only [X, K, qnn, hqcoe] using h
  simpa only [X, K, hsigma, one_mul, mul_one] using
    integrable_sq_and_condExp_sq_le_of_tail
      (c := lowerOccupationCountRate ((1 : ℝ) / 2)) (C := 1)
      (d := lowerOccupationDecayRate ((1 : ℝ) / 2))
      hsigma.measurableSpace_le X K
      (measurable_sourceInteriorStoppedFullRankGap
        (n := n) hlam0.le hlamHalf hB eta B 0 T r)
      (sourceInteriorStoppedFullRankGap_nonneg
        (n := n) hlam0.le hlamHalf eta B B 0 T r)
      (sourceInteriorA1StartBacklog_stronglyMeasurable
        (n := n) hlam0.le hlamHalf hB eta T r)
      (sourceInteriorA1StartBacklog_nonneg
        (n := n) hlam0.le hlamHalf eta B T r)
      (sourceInteriorA1StartBacklog_sq_integrable
        (n := n) hlam0.le hlamHalf hB eta T r)
      hrates.1 (by norm_num : (0 : ℝ) ≤ 1) hrates.2
      (by simpa only [one_mul] using hActualTail)

/-- The symmetric target-first conditional square bound with summable start-gated backlog. -/
theorem targetInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    let hsigma := feedbackFullRankStart_isStoppingTime
      (n := n) hlam0.le (by linarith) B T r
    Integrable (fun sample : FiniteSample n ↦
        targetInteriorStoppedFullRankGap
          hlam0.le (by linarith) eta B B 0 T r sample ^ (2 : ℕ))
        (finiteSampleLaw n) ∧
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
          (fun sample ↦ targetInteriorStoppedFullRankGap
            hlam0.le (by linarith) eta B B 0 T r sample ^ (2 : ℕ)) ≤ᵐ[
              (finiteSampleLaw n : Measure (FiniteSample n))]
        fun sample ↦
          (targetInteriorA1StartBacklog
              hlam0.le (by linarith) eta B T r sample /
            lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X := targetInteriorStoppedFullRankGap
    (n := n) hlam0.le hlamHalf eta B B 0 T r
  let K := targetInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
  have hrates := lowerOccupation_rates_pos (c₀ := (1 : ℝ) / 2) (by norm_num)
  have hActualTail : ∀ q : ℝ, 0 < q →
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
          ({sample | q < X sample}.indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
            (finiteSampleLaw n : Measure (FiniteSample n))]
        fun sample ↦
          (if K sample > lowerOccupationCountRate ((1 : ℝ) / 2) * q then 1 else 0) +
            Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * q) := by
    intro q hq
    let qnn : ℝ≥0 := Real.toNNReal q
    have hqnn : 0 < qnn := Real.toNNReal_pos.mpr hq
    have hqcoe : (qnn : ℝ) = q := Real.coe_toNNReal q hq.le
    have h := condExp_targetInteriorStoppedFullRankGap_tail_le_startGated
      (n := n) hlam0 hlam hn hB heta0 hetaSmall T r hqnn
    simpa only [X, K, qnn, hqcoe] using h
  simpa only [X, K, hsigma, one_mul, mul_one] using
    integrable_sq_and_condExp_sq_le_of_tail
      (c := lowerOccupationCountRate ((1 : ℝ) / 2)) (C := 1)
      (d := lowerOccupationDecayRate ((1 : ℝ) / 2))
      hsigma.measurableSpace_le X K
      (measurable_targetInteriorStoppedFullRankGap
        (n := n) hlam0.le hlamHalf hB eta B 0 T r)
      (targetInteriorStoppedFullRankGap_nonneg
        (n := n) hlam0.le hlamHalf eta B B 0 T r)
      (targetInteriorA1StartBacklog_stronglyMeasurable
        (n := n) hlam0.le hlamHalf hB eta T r)
      (targetInteriorA1StartBacklog_nonneg
        (n := n) hlam0.le hlamHalf eta B T r)
      (targetInteriorA1StartBacklog_sq_integrable
        (n := n) hlam0.le hlamHalf hB eta T r)
      hrates.1 (by norm_num : (0 : ℝ) ≤ 1) hrates.2
      (by simpa only [one_mul] using hActualTail)

/-! ## Rank/current bridge for the start-gated backlog -/

private theorem countBefore_finiteEventCountTop_at_positive_rank_eq
    {m : ℕ} {Omega : Type*} (tau : Fin m → Omega → WithTop ℝ≥0)
    (r : Fin m) (sample : Omega) (s : ℝ≥0)
    (hrank : CountingProcess.finiteRankEventTime tau r sample = (s : WithTop ℝ≥0))
    (hunique : ∀ i j : Fin m, tau i sample = (s : WithTop ℝ≥0) →
      tau j sample = (s : WithTop ℝ≥0) → i = j) :
    countBefore (fun u sample' ↦ finiteEventCountTop tau u sample') s sample = r.val := by
  classical
  let values : Fin m → WithTop ℝ≥0 := fun i ↦ tau i sample
  let sigma : Equiv.Perm (Fin m) := Tuple.sort values
  have hrank' : values (sigma r) = (s : WithTop ℝ≥0) := by
    simpa only [CountingProcess.finiteRankEventTime, values, sigma] using hrank
  have hmono : Monotone (values ∘ sigma) := Tuple.monotone_sort values
  have hlt : ∀ k : Fin m, values (sigma k) < (s : WithTop ℝ≥0) ↔ k < r := by
    intro k
    constructor
    · intro hk
      by_contra hkr
      have hrk : r ≤ k := le_of_not_gt hkr
      have hle := hmono hrk
      simp only [Function.comp_apply, hrank'] at hle
      exact (not_lt_of_ge hle) hk
    · intro hkr
      have hle := hmono hkr.le
      simp only [Function.comp_apply, hrank'] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlabels : sigma k = sigma r := hunique (sigma k) (sigma r) heq hrank'
      exact hkr.ne (sigma.injective hlabels)
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  have hcard :
      (Finset.univ.filter fun k : Fin m ↦ values (sigma k) < (s : WithTop ℝ≥0)).card =
        (Finset.univ.filter fun i : Fin m ↦ values i < (s : WithTop ℝ≥0)).card := by
    apply Finset.card_equiv sigma
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hcard]
  have hfilter :
      (Finset.univ.filter fun k : Fin m ↦ values (sigma k) < (s : WithTop ℝ≥0)) =
        Finset.Iio r := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact hlt k
  rw [hfilter]
  simp

private theorem noFeedbackTies_of_mem_sourceInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    sample.NoFeedbackTies lam B 0 := by
  classical
  by_contra hbad
  let i := Tuple.sort
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample) r
  have hcapLe : (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [feedbackFullRankStart, coe_cappedStoppingValue, feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hsourceEq : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) :=
    le_antisymm hstart.1 hcapLe
  have hselected : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      sourceFullEventTime hlam0 hlamHalf B i sample := rfl
  by_cases hi : i ∈ sample.initialSeenSource B 0
  · have hzero := sourceFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B i sample hi
    have hz : (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) = 0 := by
      calc
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) =
            sourceFullRankEventTime hlam0 hlamHalf B r sample := hsourceEq.symm
        _ = sourceFullEventTime hlam0 hlamHalf B i sample := hselected
        _ = 0 := hzero
    exact (ne_of_gt hstart.2.2.1) hz
  · have htop : sourceFullEventTime hlam0 hlamHalf B i sample = ⊤ := by
      rw [sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B i sample hi]
      simp [sourceEventTime, hbad]
    have hfinite : sourceFullEventTime hlam0 hlamHalf B i sample ≠ ⊤ := by
      rw [← hselected, hsourceEq]
      exact WithTop.coe_ne_top
    exact hfinite htop

private theorem noFeedbackTies_of_mem_targetInteriorA1StartEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ targetInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    sample.NoFeedbackTies lam B 0 := by
  classical
  by_contra hbad
  let j := Tuple.sort
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample) r
  have hcapLe : (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [feedbackFullRankStart, coe_cappedStoppingValue, feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have htargetEq : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) :=
    le_antisymm hstart.1 hcapLe
  have hselected : targetFullRankEventTime hlam0 hlamHalf B r sample =
      targetFullEventTime hlam0 hlamHalf B j sample := rfl
  by_cases hj : j ∈ sample.initialSeenTarget B 0
  · have hzero := targetFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B j sample hj
    have hz : (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) = 0 := by
      calc
        (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) =
            targetFullRankEventTime hlam0 hlamHalf B r sample := htargetEq.symm
        _ = targetFullEventTime hlam0 hlamHalf B j sample := hselected
        _ = 0 := hzero
    exact (ne_of_gt hstart.2.2.1) hz
  · have htop : targetFullEventTime hlam0 hlamHalf B j sample = ⊤ := by
      rw [targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B j sample hj]
      simp [targetEventTime, hbad]
    have hfinite : targetFullEventTime hlam0 hlamHalf B j sample ≠ ⊤ := by
      rw [← hselected, htargetEq]
      exact WithTop.coe_ne_top
    exact hfinite htop

private theorem sourceFullEventTime_injective_at_positive
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (s : ℝ≥0) (hs : 0 < s) :
    ∀ i j : Fin n,
      sourceFullEventTime hlam0 hlamHalf B i sample = (s : WithTop ℝ≥0) →
      sourceFullEventTime hlam0 hlamHalf B j sample = (s : WithTop ℝ≥0) → i = j := by
  intro i j hi hj
  have hi0 : i ∉ sample.initialSeenSource B 0 := by
    intro himem
    rw [sourceFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B i sample himem] at hi
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hi
  have hj0 : j ∉ sample.initialSeenSource B 0 := by
    intro hjmem
    rw [sourceFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B j sample hjmem] at hj
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hj
  apply sourceEventTime_injOn_of_noFeedbackTies
    (n := n) hlam0 hlamHalf B 0 sample hNoTie i j
  · rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi0, hi]
    exact WithTop.coe_ne_top
  · rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B j sample hj0, hj]
    exact WithTop.coe_ne_top
  · rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B i sample hi0,
      ← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B j sample hj0, hi, hj]

private theorem targetFullEventTime_injective_at_positive
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (s : ℝ≥0) (hs : 0 < s) :
    ∀ i j : Fin n,
      targetFullEventTime hlam0 hlamHalf B i sample = (s : WithTop ℝ≥0) →
      targetFullEventTime hlam0 hlamHalf B j sample = (s : WithTop ℝ≥0) → i = j := by
  intro i j hi hj
  have hi0 : i ∉ sample.initialSeenTarget B 0 := by
    intro himem
    rw [targetFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B i sample himem] at hi
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hi
  have hj0 : j ∉ sample.initialSeenTarget B 0 := by
    intro hjmem
    rw [targetFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B j sample hjmem] at hj
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hj
  apply targetEventTime_injOn_of_noFeedbackTies
    (n := n) hlam0 hlamHalf B 0 sample hNoTie i j
  · rw [← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi0, hi]
    exact WithTop.coe_ne_top
  · rw [← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B j sample hj0, hj]
    exact WithTop.coe_ne_top
  · rw [← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B i sample hi0,
      ← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B j sample hj0, hi, hj]

private theorem countBefore_sourceFullCount_eq_initial_card_add_safeSourceCountBefore
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (s : ℝ≥0) (sample : FiniteSample n) (hs : 0 < s) :
    countBefore (sourceFullCount (n := n) hlam0 hlamHalf B) s sample =
      (sample.initialSeenSource B 0).card +
        countBefore (safeSourceCount hlam0 hlamHalf B 0) s sample := by
  classical
  let initial := sample.initialSeenSource B 0
  let arrived := Finset.univ.filter fun i : Fin n ↦
    sourceEventTime hlam0 hlamHalf B 0 i sample < (s : WithTop ℝ≥0)
  have hdisjoint : Disjoint initial arrived := by
    rw [Finset.disjoint_left]
    intro i hiInitial hiArrived
    have hiTime := (Finset.mem_filter.mp hiArrived).2.le
    have hiDiff :=
      (sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 i s).mp hiTime
    exact (Finset.mem_sdiff.mp hiDiff.2).2 hiInitial
  have hset :
      Finset.univ.filter (fun i : Fin n ↦
        sourceFullEventTime hlam0 hlamHalf B i sample < (s : WithTop ℝ≥0)) =
        initial ∪ arrived := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hi : i ∈ initial
    · have hi' : i ∈ sample.initialSeenSource B 0 := by simpa [initial] using hi
      simp only [sourceFullEventTime, hi', ite_true]
      constructor
      · intro _
        exact Or.inl hi
      · intro _
        exact_mod_cast hs
    · have hi' : i ∉ sample.initialSeenSource B 0 := by simpa [initial] using hi
      simp only [sourceFullEventTime, hi', ite_false, hi, false_or]
      simp only [arrived, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold sourceFullCount safeSourceCount
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  change (Finset.univ.filter fun i : Fin n ↦
    sourceFullEventTime hlam0 hlamHalf B i sample < (s : WithTop ℝ≥0)).card = _
  rw [hset, Finset.card_union_of_disjoint hdisjoint,
    countBefore_finiteEventCountTop_eq_card_filter_lt]

private theorem countBefore_targetFullCount_eq_initial_card_add_safeTargetCountBefore
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (s : ℝ≥0) (sample : FiniteSample n) (hs : 0 < s) :
    countBefore (targetFullCount (n := n) hlam0 hlamHalf B) s sample =
      (sample.initialSeenTarget B 0).card +
        countBefore (safeTargetCount hlam0 hlamHalf B 0) s sample := by
  classical
  let initial := sample.initialSeenTarget B 0
  let arrived := Finset.univ.filter fun j : Fin n ↦
    targetEventTime hlam0 hlamHalf B 0 j sample < (s : WithTop ℝ≥0)
  have hdisjoint : Disjoint initial arrived := by
    rw [Finset.disjoint_left]
    intro j hjInitial hjArrived
    have hjTime := (Finset.mem_filter.mp hjArrived).2.le
    have hjDiff :=
      (sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 j s).mp hjTime
    exact (Finset.mem_sdiff.mp hjDiff.2).2 hjInitial
  have hset :
      Finset.univ.filter (fun j : Fin n ↦
        targetFullEventTime hlam0 hlamHalf B j sample < (s : WithTop ℝ≥0)) =
        initial ∪ arrived := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hj : j ∈ initial
    · have hj' : j ∈ sample.initialSeenTarget B 0 := by simpa [initial] using hj
      simp only [targetFullEventTime, hj', ite_true]
      constructor
      · intro _
        exact Or.inl hj
      · intro _
        exact_mod_cast hs
    · have hj' : j ∉ sample.initialSeenTarget B 0 := by simpa [initial] using hj
      simp only [targetFullEventTime, hj', ite_false, hj, false_or]
      simp only [arrived, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold targetFullCount safeTargetCount
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  change (Finset.univ.filter fun j : Fin n ↦
    targetFullEventTime hlam0 hlamHalf B j sample < (s : WithTop ℝ≥0)).card = _
  rw [hset, Finset.card_union_of_disjoint hdisjoint,
    countBefore_finiteEventCountTop_eq_card_filter_lt]

private theorem finiteEventCountTop_eq_countBefore_of_no_event_at
    {m : ℕ} {Omega : Type*} (tau : Fin m → Omega → WithTop ℝ≥0)
    (s : ℝ≥0) (sample : Omega)
    (hne : ∀ i : Fin m, tau i sample ≠ (s : WithTop ℝ≥0)) :
    finiteEventCountTop tau s sample =
      countBefore (fun u sample' ↦ finiteEventCountTop tau u sample') s sample := by
  classical
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hi ↦ lt_of_le_of_ne hi (hne i), fun hi ↦ hi.le⟩

private theorem sourceFullEventTime_ne_targetFullEventTime_at_positive
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) (_hNoTie : sample.NoFeedbackTies lam B 0)
    (s : ℝ≥0) (hs : 0 < s) (i j : Fin n)
    (hi : sourceFullEventTime hlam0 hlamHalf B i sample = (s : WithTop ℝ≥0)) :
    targetFullEventTime hlam0 hlamHalf B j sample ≠ (s : WithTop ℝ≥0) := by
  intro hj
  have hi0 : i ∉ sample.initialSeenSource B 0 := by
    intro himem
    rw [sourceFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B i sample himem] at hi
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hi
  have hj0 : j ∉ sample.initialSeenTarget B 0 := by
    intro hjmem
    rw [targetFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B j sample hjmem] at hj
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hj
  have hsourceFinite : sourceEventTime hlam0 hlamHalf B 0 i sample ≠ ⊤ := by
    rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi0, hi]
    exact WithTop.coe_ne_top
  have htargetFinite : targetEventTime hlam0 hlamHalf B 0 j sample ≠ ⊤ := by
    rw [← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B j sample hj0, hj]
    exact WithTop.coe_ne_top
  apply sourceEventTime_ne_targetEventTime
    hlam0 hlamHalf B 0 sample i j hsourceFinite htargetFinite
  rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi0,
    ← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B j sample hj0, hi, hj]

private theorem sourceInteriorA1StartBacklog_eq_leftCurrent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample =
      (leftCurrentOfCounts (safeK0 lam B 0)
        (safeSourceBulkCount hlam0 hlamHalf B B 0)
        (safeTargetBulkCount hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by
  classical
  let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
  have hs : 0 < s := by
    exact_mod_cast hstart.2.2.1
  have hNoTie := noFeedbackTies_of_mem_sourceInteriorA1StartEvent
    (n := n) hlam0 hlamHalf eta B T r sample hstart
  have hcapLe : (s : WithTop ℝ≥0) ≤
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    change (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      sourceFullRankEventTime hlam0 hlamHalf B r sample
    rw [feedbackFullRankStart, coe_cappedStoppingValue,
      feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hsourceEq : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (s : WithTop ℝ≥0) := le_antisymm hstart.1 hcapLe
  let i := Tuple.sort
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample) r
  have hi : sourceFullEventTime hlam0 hlamHalf B i sample = (s : WithTop ℝ≥0) := by
    exact hsourceEq
  have hsourceBefore : countBefore
      (sourceFullCount (n := n) hlam0 hlamHalf B) s sample = r.val := by
    exact countBefore_finiteEventCountTop_at_positive_rank_eq
      (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) r sample s
      hsourceEq
      (sourceFullEventTime_injective_at_positive
        (n := n) hlam0 hlamHalf B sample hNoTie s hs)
  have htargetNe : ∀ j : Fin n,
      targetFullEventTime hlam0 hlamHalf B j sample ≠ (s : WithTop ℝ≥0) := by
    intro j
    exact sourceFullEventTime_ne_targetFullEventTime_at_positive
      (n := n) hlam0 hlamHalf B sample hNoTie s hs i j hi
  have htargetAt : targetFullCount hlam0 hlamHalf B s sample =
      countBefore (targetFullCount (n := n) hlam0 hlamHalf B) s sample := by
    exact finiteEventCountTop_eq_countBefore_of_no_event_at
      (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) s sample htargetNe
  have hbulk : (s : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    lt_safeFeedbackBulkExitTime_of_lt_A1Stop
      (n := n) hlam0 hlamHalf eta B B 0 T s sample hstart.2.2.2
  have hleft := leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B B 0 s sample hbulk
  rw [sourceInteriorA1StartBacklog, ite_eq_left hstart,
    sourceFirstFullRankBacklog, htargetAt]
  have hsourceDecomp :=
    countBefore_sourceFullCount_eq_initial_card_add_safeSourceCountBefore
      (n := n) hlam0 hlamHalf B s sample hs
  have htargetDecomp :=
    countBefore_targetFullCount_eq_initial_card_add_safeTargetCountBefore
      (n := n) hlam0 hlamHalf B s sample hs
  have hpre : (safePreCurrentAt hlam0 hlamHalf B 0 s sample : ℝ) =
      (r.val : ℝ) -
        (countBefore (targetFullCount (n := n) hlam0 hlamHalf B) s sample : ℝ) := by
    rw [safePreCurrentAt, leftCurrentOfCounts, safeK0, ite_eq_left hNoTie,
      initialFeedbackCurrent]
    rw [← hsourceBefore, hsourceDecomp, htargetDecomp]
    push_cast
    ring
  have htargetLe : targetFullCount hlam0 hlamHalf B s sample ≤ r.val := by
    exact Nat.le_of_not_gt ((targetFullRankEventTime_le_iff_lt_targetFullCount
      (n := n) hlam0 hlamHalf B r s sample).not.mp hstart.2.1)
  have htargetBeforeLe :
      countBefore (targetFullCount (n := n) hlam0 hlamHalf B) s sample ≤ r.val := by
    rw [← htargetAt]
    exact htargetLe
  rw [max_eq_right]
  · rw [hleft, hpre]
  · apply sub_nonneg.mpr
    exact_mod_cast htargetBeforeLe

private theorem targetInteriorA1StartBacklog_eq_neg_leftCurrent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ targetInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample =
      -(leftCurrentOfCounts (safeK0 lam B 0)
        (safeSourceBulkCount hlam0 hlamHalf B B 0)
        (safeTargetBulkCount hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by
  classical
  let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
  have hs : 0 < s := by
    exact_mod_cast hstart.2.2.1
  have hNoTie := noFeedbackTies_of_mem_targetInteriorA1StartEvent
    (n := n) hlam0 hlamHalf eta B T r sample hstart
  have hcapLe : (s : WithTop ℝ≥0) ≤
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    change (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      targetFullRankEventTime hlam0 hlamHalf B r sample
    rw [feedbackFullRankStart, coe_cappedStoppingValue,
      feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have htargetEq : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (s : WithTop ℝ≥0) := le_antisymm hstart.1 hcapLe
  let j := Tuple.sort
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample) r
  have hj : targetFullEventTime hlam0 hlamHalf B j sample = (s : WithTop ℝ≥0) := by
    exact htargetEq
  have htargetBefore : countBefore
      (targetFullCount (n := n) hlam0 hlamHalf B) s sample = r.val := by
    exact countBefore_finiteEventCountTop_at_positive_rank_eq
      (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) r sample s
      htargetEq
      (targetFullEventTime_injective_at_positive
        (n := n) hlam0 hlamHalf B sample hNoTie s hs)
  have hsourceNe : ∀ i : Fin n,
      sourceFullEventTime hlam0 hlamHalf B i sample ≠ (s : WithTop ℝ≥0) := by
    intro i hi
    exact (sourceFullEventTime_ne_targetFullEventTime_at_positive
      (n := n) hlam0 hlamHalf B sample hNoTie s hs i j hi) hj
  have hsourceAt : sourceFullCount hlam0 hlamHalf B s sample =
      countBefore (sourceFullCount (n := n) hlam0 hlamHalf B) s sample := by
    exact finiteEventCountTop_eq_countBefore_of_no_event_at
      (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) s sample hsourceNe
  have hbulk : (s : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    lt_safeFeedbackBulkExitTime_of_lt_A1Stop
      (n := n) hlam0 hlamHalf eta B B 0 T s sample hstart.2.2.2
  have hleft := leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B B 0 s sample hbulk
  rw [targetInteriorA1StartBacklog, ite_eq_left hstart,
    targetFirstFullRankBacklog, hsourceAt]
  have hsourceDecomp :=
    countBefore_sourceFullCount_eq_initial_card_add_safeSourceCountBefore
      (n := n) hlam0 hlamHalf B s sample hs
  have htargetDecomp :=
    countBefore_targetFullCount_eq_initial_card_add_safeTargetCountBefore
      (n := n) hlam0 hlamHalf B s sample hs
  have hpre : (safePreCurrentAt hlam0 hlamHalf B 0 s sample : ℝ) =
      (countBefore (sourceFullCount (n := n) hlam0 hlamHalf B) s sample : ℝ) -
        (r.val : ℝ) := by
    rw [safePreCurrentAt, leftCurrentOfCounts, safeK0, ite_eq_left hNoTie,
      initialFeedbackCurrent]
    rw [hsourceDecomp, ← htargetBefore, htargetDecomp]
    push_cast
    ring
  have hsourceLe : sourceFullCount hlam0 hlamHalf B s sample ≤ r.val := by
    exact Nat.le_of_not_gt ((sourceFullRankEventTime_le_iff_lt_sourceFullCount
      (n := n) hlam0 hlamHalf B r s sample).not.mp hstart.2.1)
  have hsourceBeforeLe :
      countBefore (sourceFullCount (n := n) hlam0 hlamHalf B) s sample ≤ r.val := by
    rw [← hsourceAt]
    exact hsourceLe
  rw [max_eq_right]
  · rw [hleft, hpre]
    ring
  · apply sub_nonneg.mpr
    exact_mod_cast hsourceBeforeLe

/-! ## Pathwise charging to the two bulk counting integrals -/

/-- The bounded predictable integrand that charges a retained rank backlog to the squared
strict-left bulk current. -/
noncomputable def feedbackI3BacklogIntegrand
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) : ℝ≥0 → FiniteSample n → ℝ :=
  fun s sample ↦
    throughStopMask
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B B 0 T) s sample *
      (integerClip (feedbackA1CurrentCutoff n)
        (leftCurrentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount hlam0 hlamHalf B B 0)
          (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample) : ℝ) ^ 2

private theorem feedbackI3ClippedLeftSquare_boundedSimplePredictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) :
    IsBoundedSimplePredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (fun s sample ↦
        (integerClip (feedbackA1CurrentCutoff n)
          (leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0 hlamHalf B B 0)
            (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample) : ℝ) ^ 2) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0 hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0 hlamHalf B B 0
  let R := feedbackA1CurrentCutoff n
  let g : ℤ → ℝ := fun k ↦ (integerClip R k : ℝ) ^ 2
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
    simpa only [ℱ] using
      safeK0_stronglyMeasurable_usual_zero
        (n := n) hlam0 hlamHalf B 0
  refine ⟨leftCurrentOfCounts_comp_predictable hplus hminus hK0 g, ?_,
    clippedValueAbsBound R (fun k : ℤ ↦ (k : ℝ) ^ 2),
    clippedValueAbsBound_nonneg R (fun k : ℤ ↦ (k : ℝ) ^ 2), ?_⟩
  · have hfinite : ((cutoffStates R : Finset ℤ) : Set ℤ).Finite :=
      (cutoffStates R).finite_toSet
    apply (hfinite.image fun k : ℤ ↦ (k : ℝ) ^ 2).subset
    rintro y ⟨z, rfl⟩
    refine ⟨integerClip R
        (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus z.1 z.2), ?_, rfl⟩
    exact integerClip_mem_cutoffStates R _
  · intro s sample
    exact abs_apply_integerClip_le_clippedValueAbsBound R
      (fun k : ℤ ↦ (k : ℝ) ^ 2)
      (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample)

theorem feedbackI3BacklogIntegrand_boundedSimplePredictable
    {lam eta B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hB : 0 < B) (T : ℝ≥0) :
    IsBoundedSimplePredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (feedbackI3BacklogIntegrand hlam0 hlamHalf eta B T) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let tau := safeFeedbackA1StopTime
    (n := n) hlam0 hlamHalf eta B B 0 T
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta B 0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0 hlamHalf eta B B 0 T = throughStopMask tau := by
    funext s sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0 hlamHalf eta B B 0 T s sample
  have hMask : IsBoundedSimplePredictable ℱ (throughStopMask tau) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hSquare := feedbackI3ClippedLeftSquare_boundedSimplePredictable
    (n := n) hlam0 hlamHalf B
  change IsBoundedSimplePredictable ℱ (fun s sample ↦
    throughStopMask tau s sample *
      (integerClip (feedbackA1CurrentCutoff n)
        (leftCurrentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount hlam0 hlamHalf B B 0)
          (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample) : ℝ) ^ 2)
  simpa only [feedbackI3BacklogIntegrand, tau, ℱ] using
    hMask.mul_process hSquare

private theorem sourceSelectedBulkEventTime_eq_start
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    safeSourceBulkEventTime hlam0 hlamHalf B B 0
        (Tuple.sort
          (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample) r) sample =
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) := by
  classical
  let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
  let i := Tuple.sort
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample) r
  have hs : 0 < s := by exact_mod_cast hstart.2.2.1
  have hcapLe : (s : WithTop ℝ≥0) ≤
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    change (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      sourceFullRankEventTime hlam0 hlamHalf B r sample
    rw [feedbackFullRankStart, coe_cappedStoppingValue,
      feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hsourceEq : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (s : WithTop ℝ≥0) := le_antisymm hstart.1 hcapLe
  have hiFull : sourceFullEventTime hlam0 hlamHalf B i sample =
      (s : WithTop ℝ≥0) := hsourceEq
  have hi0 : i ∉ sample.initialSeenSource B 0 := by
    intro himem
    rw [sourceFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B i sample himem] at hiFull
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hiFull
  have hiEvent : sourceEventTime hlam0 hlamHalf B 0 i sample =
      (s : WithTop ℝ≥0) := by
    rw [← sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi0]
    exact hiFull
  have hbulk : (s : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    lt_safeFeedbackBulkExitTime_of_lt_A1Stop
      (n := n) hlam0 hlamHalf eta B B 0 T s sample hstart.2.2.2
  have hretained :=
    safeSourceBulkEventTime_eq_sourceEventTime_of_le_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 s sample i hiEvent.le hbulk
  simpa only [s, i, hretained] using hiEvent

private theorem targetSelectedBulkEventTime_eq_start
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hstart : sample ∈ targetInteriorA1StartEvent hlam0 hlamHalf eta B T r) :
    safeTargetBulkEventTime hlam0 hlamHalf B B 0
        (Tuple.sort
          (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample) r) sample =
      (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) := by
  classical
  let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
  let j := Tuple.sort
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample) r
  have hs : 0 < s := by exact_mod_cast hstart.2.2.1
  have hcapLe : (s : WithTop ℝ≥0) ≤
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    change (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) ≤
      targetFullRankEventTime hlam0 hlamHalf B r sample
    rw [feedbackFullRankStart, coe_cappedStoppingValue,
      feedbackFullRankLeftTime_eq_min]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have htargetEq : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (s : WithTop ℝ≥0) := le_antisymm hstart.1 hcapLe
  have hjFull : targetFullEventTime hlam0 hlamHalf B j sample =
      (s : WithTop ℝ≥0) := htargetEq
  have hj0 : j ∉ sample.initialSeenTarget B 0 := by
    intro hjmem
    rw [targetFullEventTime_eq_zero_of_mem_initialSeen
      hlam0 hlamHalf B j sample hjmem] at hjFull
    have hs' : (0 : WithTop ℝ≥0) < (s : WithTop ℝ≥0) := WithTop.coe_lt_coe.mpr hs
    exact (ne_of_lt hs') hjFull
  have hjEvent : targetEventTime hlam0 hlamHalf B 0 j sample =
      (s : WithTop ℝ≥0) := by
    rw [← targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B j sample hj0]
    exact hjFull
  have hbulk : (s : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    lt_safeFeedbackBulkExitTime_of_lt_A1Stop
      (n := n) hlam0 hlamHalf eta B B 0 T s sample hstart.2.2.2
  have hretained :=
    safeTargetBulkEventTime_eq_targetEventTime_of_le_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 s sample j hjEvent.le hbulk
  simpa only [s, j, hretained] using hjEvent

/-- Pathwise, the complete start-gated backlog energy is charged to the source and target
bulk counting integrals of the stopped strict-left current square. -/
theorem source_targetInteriorA1StartBacklog_sq_sum_le_countingIntegrals
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (sample : FiniteSample n) :
    (∑ r : Fin n,
        sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2) +
      (∑ r : Fin n,
        targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2) ≤
      countingIntegral
          (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
          (feedbackI3BacklogIntegrand hlam0 hlamHalf eta B T) T sample +
        countingIntegral
          (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
          (feedbackI3BacklogIntegrand hlam0 hlamHalf eta B T) T sample := by
  classical
  let H := feedbackI3BacklogIntegrand
    (n := n) hlam0 hlamHalf eta B T
  let xiPlus : Fin n → FiniteSample n → WithTop ℝ≥0 :=
    fun i ↦ safeSourceBulkEventTime hlam0 hlamHalf B B 0 i
  let xiMinus : Fin n → FiniteSample n → WithTop ℝ≥0 :=
    fun j ↦ safeTargetBulkEventTime hlam0 hlamHalf B B 0 j
  let sigmaPlus : Equiv.Perm (Fin n) := Tuple.sort
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample)
  let sigmaMinus : Equiv.Perm (Fin n) := Tuple.sort
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample)
  let termPlus : Fin n → ℝ := fun i ↦
    if xiPlus i sample ≤ (T : WithTop ℝ≥0) then
      H (finiteEventTimeValue xiPlus sample i) sample else 0
  let termMinus : Fin n → ℝ := fun j ↦
    if xiMinus j sample ≤ (T : WithTop ℝ≥0) then
      H (finiteEventTimeValue xiMinus sample j) sample else 0
  have hHnonneg : ∀ s sample', 0 ≤ H s sample' := by
    intro s sample'
    dsimp only [H, feedbackI3BacklogIntegrand]
    exact mul_nonneg (by unfold throughStopMask; split_ifs <;> norm_num) (sq_nonneg _)
  have hsourceRank : ∀ r : Fin n,
      sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2 ≤
        termPlus (sigmaPlus r) := by
    intro r
    by_cases hstart : sample ∈
        sourceInteriorA1StartEvent hlam0 hlamHalf eta B T r
    · let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
      have hxi : xiPlus (sigmaPlus r) sample = (s : WithTop ℝ≥0) := by
        simpa only [xiPlus, sigmaPlus, s] using
          sourceSelectedBulkEventTime_eq_start
            (n := n) hlam0 hlamHalf eta B T r sample hstart
      have hsT : s ≤ T := feedbackFullRankStart_le
        (n := n) hlam0 hlamHalf B T r sample
      have hle : xiPlus (sigmaPlus r) sample ≤ (T : WithTop ℝ≥0) := by
        rw [hxi]
        exact_mod_cast hsT
      have hne : xiPlus (sigmaPlus r) sample ≠ ⊤ := by
        rw [hxi]
        exact WithTop.coe_ne_top
      have hvalue : finiteEventTimeValue xiPlus sample (sigmaPlus r) = s := by
        apply WithTop.coe_eq_coe.mp
        rw [finiteEventTimeValue_coe xiPlus sample (sigmaPlus r) hne, hxi]
      have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
        (n := n) hlam0 hlamHalf B B 0 s sample
      have hclip : integerClip (feedbackA1CurrentCutoff n)
          (leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0 hlamHalf B B 0)
            (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample) =
          leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0 hlamHalf B B 0)
            (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨hinterior.1.le, hinterior.2.le⟩
      have hstop : (s : WithTop ℝ≥0) ≤
          safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
        simpa only [s] using hstart.2.2.2.le
      simp only [termPlus, ite_eq_left hle, hvalue]
      rw [sourceInteriorA1StartBacklog_eq_leftCurrent
        (n := n) hlam0 hlamHalf eta B T r sample hstart]
      dsimp only [H, feedbackI3BacklogIntegrand]
      simp only [throughStopMask, ite_eq_left hstop, one_mul, hclip]
      dsimp only [s]
      exact le_rfl
    · rw [sourceInteriorA1StartBacklog]
      simp only [hstart, ite_false]
      unfold termPlus
      split_ifs
      · simpa using hHnonneg _ _
      · norm_num
  have htargetRank : ∀ r : Fin n,
      targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2 ≤
        termMinus (sigmaMinus r) := by
    intro r
    by_cases hstart : sample ∈
        targetInteriorA1StartEvent hlam0 hlamHalf eta B T r
    · let s := feedbackFullRankStart hlam0 hlamHalf B T r sample
      have hxi : xiMinus (sigmaMinus r) sample = (s : WithTop ℝ≥0) := by
        simpa only [xiMinus, sigmaMinus, s] using
          targetSelectedBulkEventTime_eq_start
            (n := n) hlam0 hlamHalf eta B T r sample hstart
      have hsT : s ≤ T := feedbackFullRankStart_le
        (n := n) hlam0 hlamHalf B T r sample
      have hle : xiMinus (sigmaMinus r) sample ≤ (T : WithTop ℝ≥0) := by
        rw [hxi]
        exact_mod_cast hsT
      have hne : xiMinus (sigmaMinus r) sample ≠ ⊤ := by
        rw [hxi]
        exact WithTop.coe_ne_top
      have hvalue : finiteEventTimeValue xiMinus sample (sigmaMinus r) = s := by
        apply WithTop.coe_eq_coe.mp
        rw [finiteEventTimeValue_coe xiMinus sample (sigmaMinus r) hne, hxi]
      have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
        (n := n) hlam0 hlamHalf B B 0 s sample
      have hclip : integerClip (feedbackA1CurrentCutoff n)
          (leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0 hlamHalf B B 0)
            (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample) =
          leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0 hlamHalf B B 0)
            (safeTargetBulkCount hlam0 hlamHalf B B 0) s sample := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨hinterior.1.le, hinterior.2.le⟩
      have hstop : (s : WithTop ℝ≥0) ≤
          safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
        simpa only [s] using hstart.2.2.2.le
      simp only [termMinus, ite_eq_left hle, hvalue]
      rw [targetInteriorA1StartBacklog_eq_neg_leftCurrent
        (n := n) hlam0 hlamHalf eta B T r sample hstart]
      dsimp only [H, feedbackI3BacklogIntegrand]
      simp only [throughStopMask, ite_eq_left hstop, one_mul, hclip]
      dsimp only [s]
      nlinarith
    · rw [targetInteriorA1StartBacklog]
      simp only [hstart, ite_false]
      unfold termMinus
      split_ifs
      · simpa using hHnonneg _ _
      · norm_num
  have hsourceCount := countingIntegral_finiteEventCountTop_eq_sum
    xiPlus H sample T
    (safeSourceBulkEventTime_injective
      (n := n) hlam0 hlamHalf B B 0 sample)
  have htargetCount := countingIntegral_finiteEventCountTop_eq_sum
    xiMinus H sample T
    (safeTargetBulkEventTime_injective
      (n := n) hlam0 hlamHalf B B 0 sample)
  calc
    (∑ r : Fin n,
        sourceInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2) +
      (∑ r : Fin n,
        targetInteriorA1StartBacklog hlam0 hlamHalf eta B T r sample ^ 2) ≤
        (∑ r : Fin n, termPlus (sigmaPlus r)) +
          (∑ r : Fin n, termMinus (sigmaMinus r)) :=
      add_le_add (Finset.sum_le_sum fun _ _ ↦ hsourceRank _)
        (Finset.sum_le_sum fun _ _ ↦ htargetRank _)
    _ = (∑ i : Fin n, termPlus i) + (∑ j : Fin n, termMinus j) := by
      rw [Equiv.sum_comp sigmaPlus termPlus, Equiv.sum_comp sigmaMinus termMinus]
    _ = countingIntegral
          (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0) H T sample +
        countingIntegral
          (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) H T sample := by
      rw [← hsourceCount, ← htargetCount]
      rfl

/-! ## Actual compensator and occupation bound -/

theorem integral_feedbackI3Backlog_countingIntegrals_le_six_occupation
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (fun sample ↦
        countingIntegral
            (safeSourceBulkCount
              (n := n) hlam0.le (by linarith) B B 0)
            (feedbackI3BacklogIntegrand
              (n := n) hlam0.le (by linarith) eta B T) T sample +
          countingIntegral
            (safeTargetBulkCount
              (n := n) hlam0.le (by linarith) B B 0)
            (feedbackI3BacklogIntegrand
              (n := n) hlam0.le (by linarith) eta B T) T sample)
        (finiteSampleLaw n) ∧
      (∫ sample,
          countingIntegral
              (safeSourceBulkCount
                (n := n) hlam0.le (by linarith) B B 0)
              (feedbackI3BacklogIntegrand
                (n := n) hlam0.le (by linarith) eta B T) T sample +
            countingIntegral
              (safeTargetBulkCount
                (n := n) hlam0.le (by linarith) B B 0)
              (feedbackI3BacklogIntegrand
                (n := n) hlam0.le (by linarith) eta B T) T sample
          ∂(finiteSampleLaw n)) ≤
        6 * (∫ sample, throughStopClippedQuadraticOccupation
          (safeFeedbackA1StopTime
            (n := n) hlam0.le (by linarith) eta B B 0 T)
          (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0.le (by linarith) B B 0)
          (safeTargetBulkCount (n := n) hlam0.le (by linarith) B B 0)
          T sample ∂(finiteSampleLaw n)) := by
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
  let H := feedbackI3BacklogIntegrand
    (n := n) hlam0.le hlamHalf eta B T
  have hplus : IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
  have hminus : IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
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
    simpa only [ℱ] using
      safeK0_stronglyMeasurable_usual_zero
        (n := n) hlam0.le hlamHalf B 0
  have hH : IsBoundedSimplePredictable ℱ H := by
    simpa only [ℱ, H] using
      feedbackI3BacklogIntegrand_boundedSimplePredictable
        (n := n) hlam0.le hlamHalf hB T
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
  have hCurrent : ∀ s sample,
      |(leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample : ℝ)| ≤
        (feedbackA1CurrentCutoff n : ℝ) := by
    intro s sample
    simpa only [Nplus, Nminus] using
      abs_leftCurrentOfSafeBulkCounts_le_cutoff
        (n := n) hlam0.le hlamHalf B B 0 s sample
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta B 0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0.le hlamHalf eta B B 0 T = throughStopMask tau := by
    funext s sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0.le hlamHalf eta B B 0 T s sample
  have hMask : IsBoundedSimplePredictable ℱ (throughStopMask tau) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hOccupation : Integrable
      (throughStopClippedQuadraticOccupation
        tau (safeK0 lam B 0) Nplus Nminus T) (finiteSampleLaw n) :=
    throughStopClippedQuadraticOccupation_integrable_of_current_bound
      hplus hminus hK0 hMask (K := (feedbackA1CurrentCutoff n : ℝ))
      (by positivity) hCurrent T
  have hOccupationTime : ∀ sample, IntegrableOn
      (fun s ↦ throughStopMask tau s sample *
        (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) T) timeMeasure := by
    intro sample
    exact throughStopClippedQuadraticOccupation_integrableOn_of_current_bound
      hplus hminus hK0 hMask (K := (feedbackA1CurrentCutoff n : ℝ))
      (by positivity) hCurrent T sample
  have hCountPlus : Integrable (countingIntegral Nplus H T) (finiteSampleLaw n) :=
    countingIntegral_integrable_of_intensity hLambdaPlus hH hAplus T
  have hCountMinus : Integrable (countingIntegral Nminus H T) (finiteSampleLaw n) :=
    countingIntegral_integrable_of_intensity hLambdaMinus hH hAminus T
  have hIntensityPlus : Integrable
      (fun sample ↦ integratedIntensity LambdaPlus H T sample) (finiteSampleLaw n) :=
    integratedIntensity_integrable_of_boundedPredictable
      hLambdaPlus hH.isBoundedPredictable hAplus T
  have hIntensityMinus : Integrable
      (fun sample ↦ integratedIntensity LambdaMinus H T sample) (finiteSampleLaw n) :=
    integratedIntensity_integrable_of_boundedPredictable
      hLambdaMinus hH.isBoundedPredictable hAminus T
  have hplusTime : ∀ sample, IntegrableOn
      (fun s ↦ H s sample * LambdaPlus s sample)
      (Ioc (0 : ℝ≥0) T) timeMeasure := fun sample ↦
    hH.isBoundedPredictable.integrableOn_mul_intensity hLambdaPlus T sample
  have hminusTime : ∀ sample, IntegrableOn
      (fun s ↦ H s sample * LambdaMinus s sample)
      (Ioc (0 : ℝ≥0) T) timeMeasure := fun sample ↦
    hH.isBoundedPredictable.integrableOn_mul_intensity hLambdaMinus T sample
  have hpath : ∀ sample,
      integratedIntensity LambdaPlus H T sample +
          integratedIntensity LambdaMinus H T sample ≤
        6 * throughStopClippedQuadraticOccupation
          tau (safeK0 lam B 0) Nplus Nminus T sample := by
    intro sample
    have hendpoint := ae_coe_ne_stoppingCoordinate tau T sample
    have hpoint : ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
        H s sample * LambdaPlus s sample + H s sample * LambdaMinus s sample ≤
          6 * (throughStopMask tau s sample *
            (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample : ℝ) ^ 2) := by
      filter_upwards [hendpoint] with s hsne
      by_cases hsle : (s : WithTop ℝ≥0) ≤ tau sample
      · have hslt : (s : WithTop ℝ≥0) < tau sample :=
          lt_of_le_of_ne hsle hsne
        have hratePlus := (safeSourceBulkRate_mem_Icc_of_lt_A1Stop
          (n := n) hlam0 hlam hB heta0 hetaSmall T s sample hslt).2
        have hrateMinus := (safeTargetBulkRate_mem_Icc_of_lt_A1Stop
          (n := n) hlam0 hlam hB heta0 hetaSmall T s sample hslt).2
        have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
          (n := n) hlam0.le hlamHalf B B 0 s sample
        have hclip : integerClip (feedbackA1CurrentCutoff n)
            (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample) =
            leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample := by
          apply integerClip_eq_self_of_mem
          rw [cutoffStates, Finset.mem_Icc]
          exact ⟨hinterior.1.le, hinterior.2.le⟩
        dsimp only [H, feedbackI3BacklogIntegrand]
        simp only [tau, Nplus, Nminus, LambdaPlus, LambdaMinus,
          throughStopMask, ite_eq_left hsle, one_mul, hclip]
        nlinarith [sq_nonneg
          (leftCurrentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount hlam0.le hlamHalf B B 0)
            (safeTargetBulkCount hlam0.le hlamHalf B B 0) s sample : ℝ)]
      · dsimp only [H, feedbackI3BacklogIntegrand]
        simp only [tau, throughStopMask, ite_eq_right hsle, zero_mul]
        norm_num
    have hleftInt : IntegrableOn
        (fun s ↦ H s sample * LambdaPlus s sample +
          H s sample * LambdaMinus s sample)
        (Ioc (0 : ℝ≥0) T) timeMeasure :=
      (hplusTime sample).add (hminusTime sample)
    have hrightInt : IntegrableOn
        (fun s ↦ 6 * (throughStopMask tau s sample *
          (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample : ℝ) ^ 2))
        (Ioc (0 : ℝ≥0) T) timeMeasure :=
      (hOccupationTime sample).const_mul 6
    have hmono := integral_mono_ae hleftInt hrightInt hpoint
    rw [integratedIntensity, integratedIntensity,
      ← integral_add (hplusTime sample) (hminusTime sample)]
    rw [throughStopClippedQuadraticOccupation, ← integral_const_mul]
    exact hmono
  have hIntensityBound :
      (∫ sample, integratedIntensity LambdaPlus H T sample +
          integratedIntensity LambdaMinus H T sample ∂(finiteSampleLaw n)) ≤
        6 * (∫ sample, throughStopClippedQuadraticOccupation
          tau (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n)) := by
    have hmono := integral_mono_ae (hIntensityPlus.add hIntensityMinus)
      (hOccupation.const_mul 6) (ae_of_all _ hpath)
    simpa only [integral_const_mul, Pi.add_apply] using hmono
  constructor
  · change Integrable
      (fun sample ↦ countingIntegral Nplus H T sample +
        countingIntegral Nminus H T sample) (finiteSampleLaw n)
    exact hCountPlus.add hCountMinus
  · rw [integral_add hIntensityPlus hIntensityMinus] at hIntensityBound
    change (∫ sample, countingIntegral Nplus H T sample +
        countingIntegral Nminus H T sample ∂(finiteSampleLaw n)) ≤ _
    rw [integral_add hCountPlus hCountMinus,
      integral_countingIntegral_eq_integratedIntensity
        hplus hLambdaPlus hH hAplus T,
      integral_countingIntegral_eq_integratedIntensity
        hminus hLambdaMinus hH hAminus T]
    simpa only [tau, Nplus, Nminus, H, hlamHalf] using hIntensityBound

/-- The two start-gated full-rank backlog families have a genuinely summable square moment.
The right-hand side is the actual A1 stopped occupation bound; no backlog-moment premise remains.
-/
theorem source_targetInteriorA1StartBacklog_sq_sum_integrable_and_integral_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (fun sample : FiniteSample n ↦
      (∑ r : Fin n,
          sourceInteriorA1StartBacklog
            hlam0.le (by linarith) eta B T r sample ^ 2) +
        (∑ r : Fin n,
          targetInteriorA1StartBacklog
            hlam0.le (by linarith) eta B T r sample ^ 2))
      (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n,
        (∑ r : Fin n,
            sourceInteriorA1StartBacklog
              hlam0.le (by linarith) eta B T r sample ^ 2) +
          (∑ r : Fin n,
            targetInteriorA1StartBacklog
              hlam0.le (by linarith) eta B T r sample ^ 2)
        ∂(finiteSampleLaw n)) ≤
      6 * (((∫ sample : FiniteSample n,
          clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
            (safeK0 lam B 0)
            (safeSourceBulkCount
              (n := n) hlam0.le (by linarith) B B 0)
            (safeTargetBulkCount
              (n := n) hlam0.le (by linarith) B B 0)
            0 sample ∂(finiteSampleLaw n)) +
        (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let Ksum : FiniteSample n → ℝ := fun sample ↦
    (∑ r : Fin n,
        sourceInteriorA1StartBacklog
          hlam0.le hlamHalf eta B T r sample ^ 2) +
      (∑ r : Fin n,
        targetInteriorA1StartBacklog
          hlam0.le hlamHalf eta B T r sample ^ 2)
  let Csum : FiniteSample n → ℝ := fun sample ↦
    countingIntegral
        (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
        (feedbackI3BacklogIntegrand
          (n := n) hlam0.le hlamHalf eta B T) T sample +
      countingIntegral
        (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
        (feedbackI3BacklogIntegrand
          (n := n) hlam0.le hlamHalf eta B T) T sample
  have hKint : Integrable Ksum (finiteSampleLaw n) := by
    apply Integrable.add
    · exact integrable_finsetSum _ fun r _ ↦
        sourceInteriorA1StartBacklog_sq_integrable
          (n := n) hlam0.le hlamHalf hB eta T r
    · exact integrable_finsetSum _ fun r _ ↦
        targetInteriorA1StartBacklog_sq_integrable
          (n := n) hlam0.le hlamHalf hB eta T r
  have hcount := integral_feedbackI3Backlog_countingIntegrals_le_six_occupation
    (n := n) hlam0 hlam hn hB heta0 hetaSmall T
  have hCint : Integrable Csum (finiteSampleLaw n) := by
    simpa only [Csum, hlamHalf] using hcount.1
  have hpath : Ksum ≤ Csum := by
    intro sample
    simpa only [Ksum, Csum] using
      source_targetInteriorA1StartBacklog_sq_sum_le_countingIntegrals
        (n := n) hlam0.le hlamHalf eta B T sample
  have hKC : ∫ sample, Ksum sample ∂(finiteSampleLaw n) ≤
      ∫ sample, Csum sample ∂(finiteSampleLaw n) :=
    integral_mono_ae hKint hCint (ae_of_all _ hpath)
  have hoccupation := safeFeedbackA1_cubic_stopped_occupation_bound
    (n := n) (x0 := B) (p0 := 0)
    hlam0 hlam hn hB heta0 hetaSmall T T
  constructor
  · simpa only [Ksum, hlamHalf] using hKint
  · change (∫ sample, Ksum sample ∂(finiteSampleLaw n)) ≤ _
    calc
      ∫ sample, Ksum sample ∂(finiteSampleLaw n) ≤
          ∫ sample, Csum sample ∂(finiteSampleLaw n) := hKC
      _ ≤ 6 * (∫ sample, throughStopClippedQuadraticOccupation
          (safeFeedbackA1StopTime
            (n := n) hlam0.le hlamHalf eta B B 0 T)
          (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
          (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
          T sample ∂(finiteSampleLaw n)) := by
        simpa only [Csum, hlamHalf] using hcount.2
      _ ≤ 6 * (((∫ sample : FiniteSample n,
          clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
            (safeK0 lam B 0)
            (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
            (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
            0 sample ∂(finiteSampleLaw n)) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) :=
        mul_le_mul_of_nonneg_left hoccupation (by norm_num)

/-! ## Total interior same-rank gap energy -/

private theorem integral_sourceInteriorStoppedFullRankGap_sq_le_startBacklog
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    (∫ sample : FiniteSample n,
      sourceInteriorStoppedFullRankGap
        hlam0.le (by linarith) eta B B 0 T r sample ^ 2
      ∂(finiteSampleLaw n)) ≤
      (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
        (∫ sample : FiniteSample n,
          sourceInteriorA1StartBacklog
            hlam0.le (by linarith) eta B T r sample ^ 2
          ∂(finiteSampleLaw n)) +
        2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X : FiniteSample n → ℝ := sourceInteriorStoppedFullRankGap
    hlam0.le hlamHalf eta B B 0 T r
  let K : FiniteSample n → ℝ :=
    sourceInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
  let c := lowerOccupationCountRate ((1 : ℝ) / 2)
  let d := lowerOccupationDecayRate ((1 : ℝ) / 2)
  have hPer :=
    sourceInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
      (n := n) hlam0 hlam hn hB heta0 hetaSmall T r
  have hKint : Integrable (fun sample ↦ K sample ^ 2) (finiteSampleLaw n) := by
    simpa only [K] using sourceInteriorA1StartBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf hB eta T r
  have hscaled : Integrable (fun sample ↦ (K sample / c) ^ 2)
      (finiteSampleLaw n) := by
    have hc : c ≠ 0 := (lowerOccupation_rates_pos
      (c₀ := (1 : ℝ) / 2) (by norm_num)).1.ne'
    have heq : (fun sample ↦ (K sample / c) ^ 2) =
        fun sample ↦ (1 / c ^ 2) * K sample ^ 2 := by
      funext sample
      field_simp
    rw [heq]
    exact hKint.const_mul _
  have hRHSint : Integrable
      (fun sample ↦ (K sample / c) ^ 2 + 2 / d ^ 2)
      (finiteSampleLaw n) := hscaled.add (integrable_const _)
  have hmono := integral_mono_ae integrable_condExp hRHSint hPer.2
  have hcond : (∫ sample,
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
        (fun sample ↦ X sample ^ 2) sample ∂(finiteSampleLaw n)) =
      ∫ sample, X sample ^ 2 ∂(finiteSampleLaw n) :=
    integral_condExp hsigma.measurableSpace_le
  rw [hcond] at hmono
  have hbound : (∫ sample, X sample ^ 2 ∂(finiteSampleLaw n)) ≤
      (1 / c ^ 2) * (∫ sample, K sample ^ 2 ∂(finiteSampleLaw n)) +
        2 / d ^ 2 := by
    calc
      ∫ sample, X sample ^ 2 ∂(finiteSampleLaw n) ≤
          ∫ sample, (K sample / c) ^ 2 + 2 / d ^ 2 ∂(finiteSampleLaw n) := hmono
      _ = (1 / c ^ 2) * (∫ sample, K sample ^ 2 ∂(finiteSampleLaw n)) +
          2 / d ^ 2 := by
        rw [integral_add hscaled (integrable_const _), integral_const]
        congr 1
        rw [show (fun sample ↦ (K sample / c) ^ 2) =
            fun sample ↦ (1 / c ^ 2) * K sample ^ 2 by
          funext sample
          field_simp [(lowerOccupation_rates_pos
            (c₀ := (1 : ℝ) / 2) (by norm_num)).1.ne'],
          integral_const_mul]
        rw [Measure.real, IsProbabilityMeasure.measure_univ]
        simp
  simpa only [X, K, c, d, hlamHalf] using hbound

private theorem integral_targetInteriorStoppedFullRankGap_sq_le_startBacklog
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {eta B : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (r : Fin n) :
    (∫ sample : FiniteSample n,
      targetInteriorStoppedFullRankGap
        hlam0.le (by linarith) eta B B 0 T r sample ^ 2
      ∂(finiteSampleLaw n)) ≤
      (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
        (∫ sample : FiniteSample n,
          targetInteriorA1StartBacklog
            hlam0.le (by linarith) eta B T r sample ^ 2
          ∂(finiteSampleLaw n)) +
        2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X : FiniteSample n → ℝ := targetInteriorStoppedFullRankGap
    hlam0.le hlamHalf eta B B 0 T r
  let K : FiniteSample n → ℝ :=
    targetInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
  let c := lowerOccupationCountRate ((1 : ℝ) / 2)
  let d := lowerOccupationDecayRate ((1 : ℝ) / 2)
  have hPer :=
    targetInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
      (n := n) hlam0 hlam hn hB heta0 hetaSmall T r
  have hKint : Integrable (fun sample ↦ K sample ^ 2) (finiteSampleLaw n) := by
    simpa only [K] using targetInteriorA1StartBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf hB eta T r
  have hscaled : Integrable (fun sample ↦ (K sample / c) ^ 2)
      (finiteSampleLaw n) := by
    have hc : c ≠ 0 := (lowerOccupation_rates_pos
      (c₀ := (1 : ℝ) / 2) (by norm_num)).1.ne'
    have heq : (fun sample ↦ (K sample / c) ^ 2) =
        fun sample ↦ (1 / c ^ 2) * K sample ^ 2 := by
      funext sample
      field_simp
    rw [heq]
    exact hKint.const_mul _
  have hRHSint : Integrable
      (fun sample ↦ (K sample / c) ^ 2 + 2 / d ^ 2)
      (finiteSampleLaw n) := hscaled.add (integrable_const _)
  have hmono := integral_mono_ae integrable_condExp hRHSint hPer.2
  have hcond : (∫ sample,
      condExp hsigma.measurableSpace (finiteSampleLaw n : Measure (FiniteSample n))
        (fun sample ↦ X sample ^ 2) sample ∂(finiteSampleLaw n)) =
      ∫ sample, X sample ^ 2 ∂(finiteSampleLaw n) :=
    integral_condExp hsigma.measurableSpace_le
  rw [hcond] at hmono
  have hbound : (∫ sample, X sample ^ 2 ∂(finiteSampleLaw n)) ≤
      (1 / c ^ 2) * (∫ sample, K sample ^ 2 ∂(finiteSampleLaw n)) +
        2 / d ^ 2 := by
    calc
      ∫ sample, X sample ^ 2 ∂(finiteSampleLaw n) ≤
          ∫ sample, (K sample / c) ^ 2 + 2 / d ^ 2 ∂(finiteSampleLaw n) := hmono
      _ = (1 / c ^ 2) * (∫ sample, K sample ^ 2 ∂(finiteSampleLaw n)) +
          2 / d ^ 2 := by
        rw [integral_add hscaled (integrable_const _), integral_const]
        congr 1
        rw [show (fun sample ↦ (K sample / c) ^ 2) =
            fun sample ↦ (1 / c ^ 2) * K sample ^ 2 by
          funext sample
          field_simp [(lowerOccupation_rates_pos
            (c₀ := (1 : ℝ) / 2) (by norm_num)).1.ne'],
          integral_const_mul]
        rw [Measure.real, IsProbabilityMeasure.measure_univ]
        simp
  simpa only [X, K, c, d, hlamHalf] using hbound

/-- Actual O(n) energy for all raw/full-recursion interior same-rank gaps.  The two explicit
constants are the A1 occupation multiplier and the per-rank exponential-tail moment.  Boundary
and terminal edges, and the stopped-continuation transport, are not included. -/
theorem source_targetInteriorStoppedFullRankGap_sq_sum_integrable_and_integral_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (fun sample : FiniteSample n ↦
      (∑ r : Fin n,
          sourceInteriorStoppedFullRankGap
            hlam0.le (by linarith) eta B B 0 T r sample ^ 2) +
        (∑ r : Fin n,
          targetInteriorStoppedFullRankGap
            hlam0.le (by linarith) eta B B 0 T r sample ^ 2))
      (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n,
        (∑ r : Fin n,
            sourceInteriorStoppedFullRankGap
              hlam0.le (by linarith) eta B B 0 T r sample ^ 2) +
          (∑ r : Fin n,
            targetInteriorStoppedFullRankGap
              hlam0.le (by linarith) eta B B 0 T r sample ^ 2)
        ∂(finiteSampleLaw n)) ≤
      (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
          (((∫ sample : FiniteSample n,
              clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
                (safeK0 lam B 0)
                (safeSourceBulkCount
                  (n := n) hlam0.le (by linarith) B B 0)
                (safeTargetBulkCount
                  (n := n) hlam0.le (by linarith) B B 0)
                0 sample ∂(finiteSampleLaw n)) +
            (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
        4 * (n : ℝ) /
          lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let c := lowerOccupationCountRate ((1 : ℝ) / 2)
  let d := lowerOccupationDecayRate ((1 : ℝ) / 2)
  let Xplus : Fin n → FiniteSample n → ℝ := fun r ↦
    sourceInteriorStoppedFullRankGap
      hlam0.le hlamHalf eta B B 0 T r
  let Xminus : Fin n → FiniteSample n → ℝ := fun r ↦
    targetInteriorStoppedFullRankGap
      hlam0.le hlamHalf eta B B 0 T r
  let Kplus : Fin n → FiniteSample n → ℝ := fun r ↦
    sourceInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
  let Kminus : Fin n → FiniteSample n → ℝ := fun r ↦
    targetInteriorA1StartBacklog hlam0.le hlamHalf eta B T r
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
      (sourceInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
        (n := n) hlam0 hlam hn hB heta0 hetaSmall T r).1
  have hXminusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Xminus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Xminus] using
      (targetInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le_startGated
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
    simpa only [Kplus] using sourceInteriorA1StartBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf hB eta T r
  have hKminusInt : ∀ r : Fin n,
      Integrable (fun sample ↦ Kminus r sample ^ 2) (finiteSampleLaw n) := by
    intro r
    simpa only [Kminus] using targetInteriorA1StartBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf hB eta T r
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
    simpa only [Xplus, Kplus, c, d, hlamHalf] using
      integral_sourceInteriorStoppedFullRankGap_sq_le_startBacklog
        (n := n) hlam0 hlam hn hB heta0 hetaSmall T r
  have hminusRank : ∀ r : Fin n,
      (∫ sample, Xminus r sample ^ 2 ∂(finiteSampleLaw n)) ≤
        (1 / c ^ 2) *
          (∫ sample, Kminus r sample ^ 2 ∂(finiteSampleLaw n)) + 2 / d ^ 2 := by
    intro r
    simpa only [Xminus, Kminus, c, d, hlamHalf] using
      integral_targetInteriorStoppedFullRankGap_sq_le_startBacklog
        (n := n) hlam0 hlam hn hB heta0 hetaSmall T r
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
  have hKbound :=
    source_targetInteriorA1StartBacklog_sq_sum_integrable_and_integral_le
      (n := n) hlam0 hlam hn hB heta0 hetaSmall T
  have hKbound' : (∫ sample, Ksum sample ∂(finiteSampleLaw n)) ≤
      6 * (((∫ sample : FiniteSample n,
          clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
            (safeK0 lam B 0)
            (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
            (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
            0 sample ∂(finiteSampleLaw n)) +
        (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) := by
    simpa only [Ksum, Kplus, Kminus, hlamHalf] using hKbound.2
  constructor
  · simpa only [Xsum, Xplus, Xminus, hlamHalf] using hXsumInt
  · have hfinal : (∫ sample, Xsum sample ∂(finiteSampleLaw n)) ≤
        (6 / c ^ 2) *
            (((∫ sample : FiniteSample n,
                clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
                  (safeK0 lam B 0)
                  (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
                  (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
                  0 sample ∂(finiteSampleLaw n)) +
              (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
            4 * (n : ℝ) / d ^ 2 := by
      calc
        ∫ sample, Xsum sample ∂(finiteSampleLaw n) ≤
            (1 / c ^ 2) * (∫ sample, Ksum sample ∂(finiteSampleLaw n)) +
              4 * (n : ℝ) / d ^ 2 := hXK
        _ ≤ (1 / c ^ 2) *
              (6 * (((∫ sample : FiniteSample n,
                  clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
                    (safeK0 lam B 0)
                    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
                    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
                    0 sample ∂(finiteSampleLaw n)) +
                (6 + 81 / lam) * (T : ℝ)) / (2 * lam))) +
              4 * (n : ℝ) / d ^ 2 :=
          by
            have hmul := mul_le_mul_of_nonneg_left hKbound'
              (by positivity : 0 ≤ (1 / c ^ 2))
            simpa [add_comm] using add_le_add_right hmul (4 * (n : ℝ) / d ^ 2)
        _ = (6 / c ^ 2) *
              (((∫ sample : FiniteSample n,
                  clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
                    (safeK0 lam B 0)
                    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
                    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
                    0 sample ∂(finiteSampleLaw n)) +
                (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
              4 * (n : ℝ) / d ^ 2 := by ring
    simpa only [Xsum, Xplus, Xminus, c, d, hlamHalf] using hfinal

end FiniteSample

end OTSelector
