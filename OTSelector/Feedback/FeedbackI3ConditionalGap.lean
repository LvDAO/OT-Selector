import OTSelector.Feedback.FeedbackFullRankArrival
import OTSelector.Feedback.FeedbackI3SegmentedIntensity

/-!
# Conditional full-rank gap bounds in the feedback bulk

This file treats the two strict orientations of a same-full-rank increasing edge.  Initial
full-rank ties and all edges whose left elapsed time is zero are excluded from the interior gap;
they belong to the separately controlled left-boundary contribution.  The right endpoint is
retained only when it lies through the actual A1 stopping coordinate.

All graph statements here refer to the raw full-recursion feedback graph through the bridges in
`FeedbackFullRankArrival`.  Transport to the stopped-continuation graph is a separate I4 step.
-/

open Filter MeasureTheory Set
open scoped Classical ENNReal NNReal ProbabilityTheory

namespace OTSelector

namespace CountingProcess

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A top-valued stopping coordinate cut at a deterministic horizon, represented in `NNReal`. -/
noncomputable def cappedStoppingValue (T : ℝ≥0) (tau : Omega → WithTop ℝ≥0) :
    Omega → ℝ≥0 :=
  fun omega ↦ WithTop.untopD 0 (min (tau omega) (T : WithTop ℝ≥0))

omit [MeasurableSpace Omega] in
theorem coe_cappedStoppingValue (T : ℝ≥0) (tau : Omega → WithTop ℝ≥0)
    (omega : Omega) :
    (cappedStoppingValue T tau omega : WithTop ℝ≥0) =
      min (tau omega) (T : WithTop ℝ≥0) := by
  have hne : min (tau omega) (T : WithTop ℝ≥0) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top T)).ne
  have hc := (WithTop.untopD_eq_iff (d := (0 : ℝ≥0))
    (y := WithTop.untopD 0 (min (tau omega) (T : WithTop ℝ≥0)))
    (x := min (tau omega) (T : WithTop ℝ≥0))).mp rfl
  rcases hc with hcoe | htop
  · exact hcoe.symm
  · exact (hne htop.1).elim

omit [MeasurableSpace Omega] in
theorem cappedStoppingValue_le (T : ℝ≥0) (tau : Omega → WithTop ℝ≥0)
    (omega : Omega) : cappedStoppingValue T tau omega ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [coe_cappedStoppingValue]
  exact min_le_right _ _

theorem cappedStoppingValue_isStoppingTime
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega))
    {tau : Omega → WithTop ℝ≥0} (htau : IsStoppingTime F tau) (T : ℝ≥0) :
    IsStoppingTime F
      (fun omega ↦ (cappedStoppingValue T tau omega : WithTop ℝ≥0)) := by
  have hmin := htau.min_const T
  intro t
  rw [show {omega | (cappedStoppingValue T tau omega : WithTop ℝ≥0) ≤
      (t : WithTop ℝ≥0)} =
      {omega | min (tau omega) (T : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} by
    ext omega
    simp only [Set.mem_ofPred_eq]
    rw [coe_cappedStoppingValue]]
  exact hmin t

theorem measurable_cappedStoppingValue
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega))
    {tau : Omega → WithTop ℝ≥0} (htau : IsStoppingTime F tau) (T : ℝ≥0) :
    Measurable (cappedStoppingValue T tau) := by
  exact ((htau.min_const T).measurable'.untopD 0)

/-- A finite-event count evaluated at a bounded stopping coordinate is measurable in the
stopping-time sigma algebra. -/
theorem finiteEventCountTop_cast_stronglyMeasurable_at_stopping
    {m : ℕ} (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega))
    (tau : Fin m → Omega → WithTop ℝ≥0) (htau : ∀ i, IsStoppingTime F (tau i))
    (sigma : Omega → ℝ≥0)
    (hsigma : IsStoppingTime F (fun omega ↦ (sigma omega : WithTop ℝ≥0))) :
    StronglyMeasurable[hsigma.measurableSpace]
      (fun omega ↦ (finiteEventCountTop tau (sigma omega) omega : ℝ)) := by
  classical
  let contribution : Fin m → Omega → ℝ := fun i omega ↦
    if tau i omega ≤ (sigma omega : WithTop ℝ≥0) then 1 else 0
  have hsum' : StronglyMeasurable[hsigma.measurableSpace]
      (∑ i : Fin m, contribution i) := by
    apply Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin m))
    intro i _hi
    exact Measurable.ite ((htau i).measurableSet_stopping_time_le hsigma)
      measurable_const measurable_const |>.stronglyMeasurable
  convert hsum' using 1
  funext omega
  simpa only [contribution, Finset.sum_apply] using
    (finiteEventCountTop_cast_eq_sum (R := ℝ) tau (sigma omega) omega)

end CountingProcess

namespace FiniteSample

open CountingProcess

variable {n : ℕ}

/-- The first same-full-rank arrival, capped at the deterministic feedback horizon. -/
noncomputable def feedbackFullRankStart
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) : FiniteSample n → ℝ≥0 :=
  cappedStoppingValue T (feedbackFullRankLeftTime hlam0 hlamHalf B r)

theorem feedbackFullRankStart_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (fun sample ↦ (feedbackFullRankStart hlam0 hlamHalf B T r sample :
        WithTop ℝ≥0)) := by
  exact cappedStoppingValue_isStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (feedbackFullRankLeftTime_isStoppingTime
      (n := n) hlam0 hlamHalf B r) T

theorem feedbackFullRankStart_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    feedbackFullRankStart hlam0 hlamHalf B T r sample ≤ T :=
  cappedStoppingValue_le T (feedbackFullRankLeftTime hlam0 hlamHalf B r) sample

theorem safeFeedbackA1StopTime_le_horizon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) :
    safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample ≤
      (T : WithTop ℝ≥0) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem coe_feedbackFullRankStart_eq_source_of_sourceFirst_of_target_le_A1
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hsource : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r)
    (htarget : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) =
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
  have hsourceT : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      (T : WithTop ℝ≥0) :=
    hsource.le.trans (htarget.trans
      (safeFeedbackA1StopTime_le_horizon hlam0 hlamHalf eta B x0 p0 T sample))
  rw [feedbackFullRankStart, coe_cappedStoppingValue,
    feedbackFullRankLeftTime_eq_sourceFullRankEventTime_of_sourceFirst
      hlam0 hlamHalf B r sample hsource,
    min_eq_left hsourceT]

theorem coe_feedbackFullRankStart_eq_target_of_targetFirst_of_source_le_A1
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (htarget : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r)
    (hsource : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    (feedbackFullRankStart hlam0 hlamHalf B T r sample : WithTop ℝ≥0) =
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
  have htargetT : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      (T : WithTop ℝ≥0) :=
    htarget.le.trans (hsource.trans
      (safeFeedbackA1StopTime_le_horizon hlam0 hlamHalf eta B x0 p0 T sample))
  rw [feedbackFullRankStart, coe_cappedStoppingValue,
    feedbackFullRankLeftTime_eq_targetFullRankEventTime_of_targetFirst
      hlam0 hlamHalf B r sample htarget,
    min_eq_left htargetT]

/-- Number of still-missing target arrivals below full rank `r`, measured when the first endpoint
of rank `r` is exposed. -/
noncomputable def sourceFirstFullRankBacklog
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  max 0 ((r.val : ℝ) -
    targetFullCount hlam0 hlamHalf B
      (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample)

/-- Source analogue used on the target-first branch. -/
noncomputable def targetFirstFullRankBacklog
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  max 0 ((r.val : ℝ) -
    sourceFullCount hlam0 hlamHalf B
      (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample)

theorem sourceFirstFullRankBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) :
    StronglyMeasurable[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (sourceFirstFullRankBacklog hlam0 hlamHalf B T r) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hcount := finiteEventCountTop_cast_stronglyMeasurable_at_stopping
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j)
    (fun j ↦ targetFullEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B j)
    (feedbackFullRankStart hlam0 hlamHalf B T r) hsigma
  exact (Measurable.max measurable_const
    (stronglyMeasurable_const.sub hcount).measurable).stronglyMeasurable

theorem targetFirstFullRankBacklog_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) :
    StronglyMeasurable[
      (feedbackFullRankStart_isStoppingTime
        (n := n) hlam0 hlamHalf B T r).measurableSpace]
      (targetFirstFullRankBacklog hlam0 hlamHalf B T r) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hcount := finiteEventCountTop_cast_stronglyMeasurable_at_stopping
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i)
    (fun i ↦ sourceFullEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B i)
    (feedbackFullRankStart hlam0 hlamHalf B T r) hsigma
  exact (Measurable.max measurable_const
    (stronglyMeasurable_const.sub hcount).measurable).stronglyMeasurable

theorem sourceFirstFullRankBacklog_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample :=
  le_max_left _ _

theorem targetFirstFullRankBacklog_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ targetFirstFullRankBacklog hlam0 hlamHalf B T r sample :=
  le_max_left _ _

/-! ## Interior stopped rank gaps -/

/-- The source-first full-rank gap, retained only for a positive interior left endpoint and a
right endpoint through A1. -/
noncomputable def sourceInteriorStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample then
    (cappedStoppingValue T (targetFullRankEventTime hlam0 hlamHalf B r) sample : ℝ) -
      (cappedStoppingValue T (sourceFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)
  else 0

/-- The symmetric target-first interior stopped full-rank gap. -/
noncomputable def targetInteriorStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample then
    (cappedStoppingValue T (sourceFullRankEventTime hlam0 hlamHalf B r) sample : ℝ) -
      (cappedStoppingValue T (targetFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)
  else 0

theorem measurable_sourceInteriorStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) :
    Measurable (sourceInteriorStoppedFullRankGap
      (n := n) hlam0 hlamHalf eta B x0 p0 T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta x0 p0 T
  have hevent : MeasurableSet
      {sample : FiniteSample n |
        sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∧
        (0 : WithTop ℝ≥0) < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
        targetFullRankEventTime hlam0 hlamHalf B r sample ≤
          safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample} := by
    exact (measurableSet_lt hsource.measurable' htarget.measurable').inter
      ((measurableSet_lt measurable_const hsource.measurable').inter
        (measurableSet_le htarget.measurable' hA1.measurable'))
  exact Measurable.ite hevent
    ((measurable_coe_nnreal_real.comp
        (measurable_cappedStoppingValue F htarget T)).sub
      (measurable_coe_nnreal_real.comp
        (measurable_cappedStoppingValue F hsource T))) measurable_const

theorem measurable_targetInteriorStoppedFullRankGap
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) :
    Measurable (targetInteriorStoppedFullRankGap
      (n := n) hlam0 hlamHalf eta B x0 p0 T r) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have hA1 := safeFeedbackA1StopTime_isStoppingTime
    (n := n) hlam0 hlamHalf hB eta x0 p0 T
  have hevent : MeasurableSet
      {sample : FiniteSample n |
        sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r ∧
        (0 : WithTop ℝ≥0) < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
        sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
          safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample} := by
    exact (measurableSet_lt htarget.measurable' hsource.measurable').inter
      ((measurableSet_lt measurable_const htarget.measurable').inter
        (measurableSet_le hsource.measurable' hA1.measurable'))
  exact Measurable.ite hevent
    ((measurable_coe_nnreal_real.comp
        (measurable_cappedStoppingValue F hsource T)).sub
      (measurable_coe_nnreal_real.comp
        (measurable_cappedStoppingValue F htarget T))) measurable_const

theorem sourceInteriorStoppedFullRankGap_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ sourceInteriorStoppedFullRankGap
      hlam0 hlamHalf eta B x0 p0 T r sample := by
  unfold sourceInteriorStoppedFullRankGap
  split_ifs with h
  · apply sub_nonneg.mpr
    have hcap : cappedStoppingValue T
        (sourceFullRankEventTime hlam0 hlamHalf B r) sample ≤
        cappedStoppingValue T
          (targetFullRankEventTime hlam0 hlamHalf B r) sample := by
      apply WithTop.coe_le_coe.mp
      rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
      exact min_le_min h.1.le le_rfl
    exact_mod_cast hcap
  · exact le_rfl

theorem targetInteriorStoppedFullRankGap_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (r : Fin n) (sample : FiniteSample n) :
    0 ≤ targetInteriorStoppedFullRankGap
      hlam0 hlamHalf eta B x0 p0 T r sample := by
  unfold targetInteriorStoppedFullRankGap
  split_ifs with h
  · apply sub_nonneg.mpr
    have hcap : cappedStoppingValue T
        (targetFullRankEventTime hlam0 hlamHalf B r) sample ≤
        cappedStoppingValue T
          (sourceFullRankEventTime hlam0 hlamHalf B r) sample := by
      apply WithTop.coe_le_coe.mp
      rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
      exact min_le_min h.1.le le_rfl
    exact_mod_cast hcap
  · exact le_rfl

/-! ## Pointwise reduction to lower occupation -/

/-- A source-first capped rank gap, including a zero-time start, is controlled by backlog
or the actual target bulk lower-occupation event. -/
theorem sourceFirstFullRank_cappedGap_tail
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hfirst : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r)
    (hretained : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample)
    (hgap : (q : ℝ) <
      (cappedStoppingValue T (targetFullRankEventTime hlam0 hlamHalf B r) sample : ℝ) -
        (cappedStoppingValue T (sourceFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)) :
    lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample ∨
      sample ∈ stoppedLowerOccupationEvent
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  by_cases hback : lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample
  · exact Or.inl hback
  right
  let sigma := feedbackFullRankStart hlam0 hlamHalf B T r sample
  let targetCap := cappedStoppingValue T
    (targetFullRankEventTime hlam0 hlamHalf B r) sample
  let sourceCap := cappedStoppingValue T
    (sourceFullRankEventTime hlam0 hlamHalf B r) sample
  have hA1T := safeFeedbackA1StopTime_le_horizon
    (n := n) hlam0 hlamHalf eta B B 0 T sample
  have htargetT : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      (T : WithTop ℝ≥0) := hretained.trans hA1T
  have htargetCap : (targetCap : WithTop ℝ≥0) =
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    dsimp only [targetCap]
    rw [coe_cappedStoppingValue, min_eq_left htargetT]
  have hsigma : (sigma : WithTop ℝ≥0) =
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    exact coe_feedbackFullRankStart_eq_source_of_sourceFirst_of_target_le_A1
      hlam0 hlamHalf eta B B 0 T r sample hfirst hretained
  have hsourceCapEq : sourceCap = sigma := by
    apply WithTop.coe_eq_coe.mp
    dsimp only [sourceCap]
    rw [coe_cappedStoppingValue]
    have hsourceT : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        (T : WithTop ℝ≥0) := hfirst.le.trans (hretained.trans hA1T)
    rw [min_eq_left hsourceT, hsigma]
  have hgapNN : sigma + q < targetCap := by
    have hreal : (sigma : ℝ) + (q : ℝ) < (targetCap : ℝ) := by
      change (q : ℝ) < (targetCap : ℝ) - (sourceCap : ℝ) at hgap
      rw [hsourceCapEq] at hgap
      linarith
    exact_mod_cast hreal
  have hgapTime : ((sigma + q : ℝ≥0) : WithTop ℝ≥0) <
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [← htargetCap]
    exact WithTop.coe_lt_coe.mpr hgapNN
  have hsurvival : ((sigma + q : ℝ≥0) : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample :=
    hgapTime.le.trans hretained
  refine ⟨?_, hsurvival⟩
  have htargetSigma : ¬targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      (sigma : WithTop ℝ≥0) := by
    rw [hsigma]
    exact not_le_of_gt hfirst
  have htargetEnd : ¬targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      ((sigma + q : ℝ≥0) : WithTop ℝ≥0) := not_le_of_gt hgapTime
  have hcountSigma : targetFullCount hlam0 hlamHalf B sigma sample ≤ r.val := by
    have hnot : ¬r.val < targetFullCount hlam0 hlamHalf B sigma sample := by
      intro hlt
      exact htargetSigma ((targetFullRankEventTime_le_iff_lt_targetFullCount
        hlam0 hlamHalf B r sigma sample).2 hlt)
    exact Nat.le_of_not_gt hnot
  have hcountEnd : targetFullCount hlam0 hlamHalf B (sigma + q) sample ≤ r.val := by
    have hnot : ¬r.val < targetFullCount hlam0 hlamHalf B (sigma + q) sample := by
      intro hlt
      exact htargetEnd ((targetFullRankEventTime_le_iff_lt_targetFullCount
        hlam0 hlamHalf B r (sigma + q) sample).2 hlt)
    exact Nat.le_of_not_gt hnot
  have hA1Bulk : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := min_le_left _ _
  have hendExit : (((sigma + q : ℝ≥0) : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample) :=
    hgapTime.trans_le (hretained.trans hA1Bulk)
  have hsigmaExit : (sigma : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    exact (WithTop.coe_le_coe.mpr (le_add_right le_rfl)).trans_lt hendExit
  rw [safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 (sigma + q) sample hendExit,
    safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 sigma sample hsigmaExit]
  have hdiff :
      (safeTargetCount hlam0 hlamHalf B 0 (sigma + q) sample : ℝ) -
          safeTargetCount hlam0 hlamHalf B 0 sigma sample =
        (targetFullCount hlam0 hlamHalf B (sigma + q) sample : ℝ) -
          targetFullCount hlam0 hlamHalf B sigma sample := by
    rw [targetFullCount_eq_initial_card_add_safeTargetCount,
      targetFullCount_eq_initial_card_add_safeTargetCount]
    push_cast
    ring
  rw [hdiff]
  have hcountSigmaReal : (targetFullCount hlam0 hlamHalf B sigma sample : ℝ) ≤
      r.val := by exact_mod_cast hcountSigma
  have hcountEndReal : (targetFullCount hlam0 hlamHalf B (sigma + q) sample : ℝ) ≤
      r.val := by exact_mod_cast hcountEnd
  have hbackEq : sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample =
      (r.val : ℝ) - targetFullCount hlam0 hlamHalf B sigma sample := by
    unfold sourceFirstFullRankBacklog
    change max 0 ((r.val : ℝ) -
      targetFullCount hlam0 hlamHalf B sigma sample) = _
    rw [max_eq_right]
    linarith
  rw [hbackEq] at hback
  have hbackLe := le_of_not_gt hback
  linarith

/-- On the source-first branch, a long stopped full-rank edge is explained either by the
already-visible target backlog or by a lower-occupation event for the actual target bulk count.
-/
theorem sourceInteriorStoppedFullRankGap_tail_subset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n |
      (q : ℝ) < sourceInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample} ⊆
      {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample} ∪
      stoppedLowerOccupationEvent
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  simp only [Set.mem_ofPred_eq] at hgap
  unfold sourceInteriorStoppedFullRankGap at hgap
  split_ifs at hgap with hgood
  · exact sourceFirstFullRank_cappedGap_tail hlam0 hlamHalf eta B T q r sample
      hgood.1 hgood.2.2 hgap
  · exact (not_lt_of_ge q.2 hgap).elim

/-- The target-first capped-gap reduction also permits a zero-time start. -/
theorem targetFirstFullRank_cappedGap_tail
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) (sample : FiniteSample n)
    (hfirst : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r)
    (hretained : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample)
    (hgap : (q : ℝ) <
      (cappedStoppingValue T (sourceFullRankEventTime hlam0 hlamHalf B r) sample : ℝ) -
        (cappedStoppingValue T (targetFullRankEventTime hlam0 hlamHalf B r) sample : ℝ)) :
    lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        targetFirstFullRankBacklog hlam0 hlamHalf B T r sample ∨
      sample ∈ stoppedLowerOccupationEvent
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  by_cases hback : lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
      targetFirstFullRankBacklog hlam0 hlamHalf B T r sample
  · exact Or.inl hback
  right
  let sigma := feedbackFullRankStart hlam0 hlamHalf B T r sample
  let sourceCap := cappedStoppingValue T
    (sourceFullRankEventTime hlam0 hlamHalf B r) sample
  let targetCap := cappedStoppingValue T
    (targetFullRankEventTime hlam0 hlamHalf B r) sample
  have hA1T := safeFeedbackA1StopTime_le_horizon
    (n := n) hlam0 hlamHalf eta B B 0 T sample
  have hsourceT : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      (T : WithTop ℝ≥0) := hretained.trans hA1T
  have hsourceCap : (sourceCap : WithTop ℝ≥0) =
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    dsimp only [sourceCap]
    rw [coe_cappedStoppingValue, min_eq_left hsourceT]
  have hsigma : (sigma : WithTop ℝ≥0) =
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    exact coe_feedbackFullRankStart_eq_target_of_targetFirst_of_source_le_A1
      hlam0 hlamHalf eta B B 0 T r sample hfirst hretained
  have htargetCapEq : targetCap = sigma := by
    apply WithTop.coe_eq_coe.mp
    dsimp only [targetCap]
    rw [coe_cappedStoppingValue]
    have htargetT : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        (T : WithTop ℝ≥0) := hfirst.le.trans (hretained.trans hA1T)
    rw [min_eq_left htargetT, hsigma]
  have hgapNN : sigma + q < sourceCap := by
    have hreal : (sigma : ℝ) + (q : ℝ) < (sourceCap : ℝ) := by
      change (q : ℝ) < (sourceCap : ℝ) - (targetCap : ℝ) at hgap
      rw [htargetCapEq] at hgap
      linarith
    exact_mod_cast hreal
  have hgapTime : ((sigma + q : ℝ≥0) : WithTop ℝ≥0) <
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [← hsourceCap]
    exact WithTop.coe_lt_coe.mpr hgapNN
  have hsurvival : ((sigma + q : ℝ≥0) : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample :=
    hgapTime.le.trans hretained
  refine ⟨?_, hsurvival⟩
  have hsourceSigma : ¬sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      (sigma : WithTop ℝ≥0) := by
    rw [hsigma]
    exact not_le_of_gt hfirst
  have hsourceEnd : ¬sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      ((sigma + q : ℝ≥0) : WithTop ℝ≥0) := not_le_of_gt hgapTime
  have hcountSigma : sourceFullCount hlam0 hlamHalf B sigma sample ≤ r.val := by
    have hnot : ¬r.val < sourceFullCount hlam0 hlamHalf B sigma sample := by
      intro hlt
      exact hsourceSigma ((sourceFullRankEventTime_le_iff_lt_sourceFullCount
        hlam0 hlamHalf B r sigma sample).2 hlt)
    exact Nat.le_of_not_gt hnot
  have hcountEnd : sourceFullCount hlam0 hlamHalf B (sigma + q) sample ≤ r.val := by
    have hnot : ¬r.val < sourceFullCount hlam0 hlamHalf B (sigma + q) sample := by
      intro hlt
      exact hsourceEnd ((sourceFullRankEventTime_le_iff_lt_sourceFullCount
        hlam0 hlamHalf B r (sigma + q) sample).2 hlt)
    exact Nat.le_of_not_gt hnot
  have hA1Bulk : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := min_le_left _ _
  have hendExit : (((sigma + q : ℝ≥0) : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample) :=
    hgapTime.trans_le (hretained.trans hA1Bulk)
  have hsigmaExit : (sigma : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    exact (WithTop.coe_le_coe.mpr (le_add_right le_rfl)).trans_lt hendExit
  rw [safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 (sigma + q) sample hendExit,
    safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 sigma sample hsigmaExit]
  have hdiff :
      (safeSourceCount hlam0 hlamHalf B 0 (sigma + q) sample : ℝ) -
          safeSourceCount hlam0 hlamHalf B 0 sigma sample =
        (sourceFullCount hlam0 hlamHalf B (sigma + q) sample : ℝ) -
          sourceFullCount hlam0 hlamHalf B sigma sample := by
    rw [sourceFullCount_eq_initial_card_add_safeSourceCount,
      sourceFullCount_eq_initial_card_add_safeSourceCount]
    push_cast
    ring
  rw [hdiff]
  have hcountSigmaReal : (sourceFullCount hlam0 hlamHalf B sigma sample : ℝ) ≤
      r.val := by exact_mod_cast hcountSigma
  have hcountEndReal : (sourceFullCount hlam0 hlamHalf B (sigma + q) sample : ℝ) ≤
      r.val := by exact_mod_cast hcountEnd
  have hbackEq : targetFirstFullRankBacklog hlam0 hlamHalf B T r sample =
      (r.val : ℝ) - sourceFullCount hlam0 hlamHalf B sigma sample := by
    unfold targetFirstFullRankBacklog
    change max 0 ((r.val : ℝ) -
      sourceFullCount hlam0 hlamHalf B sigma sample) = _
    rw [max_eq_right]
    linarith
  rw [hbackEq] at hback
  have hbackLe := le_of_not_gt hback
  linarith

/-- Symmetric target-first reduction to source lower occupation. -/
theorem targetInteriorStoppedFullRankGap_tail_subset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T q : ℝ≥0) (r : Fin n) :
    {sample : FiniteSample n |
      (q : ℝ) < targetInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample} ⊆
      {sample | lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
        targetFirstFullRankBacklog hlam0 hlamHalf B T r sample} ∪
      stoppedLowerOccupationEvent
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (feedbackFullRankStart hlam0 hlamHalf B T r)
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B B 0 T)
        (lowerOccupationCountRate ((1 : ℝ) / 2)) q := by
  intro sample hgap
  simp only [Set.mem_ofPred_eq] at hgap
  unfold targetInteriorStoppedFullRankGap at hgap
  split_ifs at hgap with hgood
  · exact targetFirstFullRank_cappedGap_tail hlam0 hlamHalf eta B T q r sample
      hgood.1 hgood.2.2 hgap
  · exact (not_lt_of_ge q.2 hgap).elim

/-- Transfer an event inclusion into a past-measurable indicator plus a conditional
occupation bound. -/
theorem condExp_indicator_le_indicator_add_of_subset
    {m0 m : MeasurableSpace (FiniteSample n)}
    {mu : @Measure (FiniteSample n) m0} [IsFiniteMeasure mu]
    (hm : m ≤ m0)
    {E D O : Set (FiniteSample n)}
    (hE : MeasurableSet[m0] E) (hD : MeasurableSet[m] D)
    (hO : MeasurableSet[m0] O)
    (hsubset : E ⊆ D ∪ O) {c : ℝ}
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
      condExp m mu ID + condExp m mu IO :=
    condExp_add hIDint hIOint m
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

/-! ## Actual conditional exponential tails -/

/-- Conditional source-first stopped gap tail at the same full rank. -/
theorem condExp_sourceInteriorStoppedFullRankGap_tail_le
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
        (if sourceFirstFullRankBacklog hlam0.le (by linarith) B T r sample >
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
      sourceFirstFullRankBacklog hlam0.le hlamHalf B T r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0) sigma
    (safeFeedbackA1StopTime
      (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := by
    exact measurableSet_lt measurable_const
      (measurable_sourceInteriorStoppedFullRankGap
        (n := n) hlam0.le hlamHalf hB eta B 0 T r)
  have hD : MeasurableSet[hsigma.measurableSpace] D := by
    exact measurableSet_lt measurable_const
      (sourceFirstFullRankBacklog_stronglyMeasurable
        (n := n) hlam0.le hlamHalf B T r).measurable
  have hO : MeasurableSet O := by
    exact measurableSet_stoppedLowerOccupationEvent_bounded
      (safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0)
      hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
      (safeFeedbackA1StopTime_isStoppingTime
        (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hsubset : E ⊆ D ∪ O := by
    simpa only [E, D, O, sigma] using
      sourceInteriorStoppedFullRankGap_tail_subset
        (n := n) hlam0.le hlamHalf eta B T q r
  have hOcc := safeTargetBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
  have hout := condExp_indicator_le_indicator_add_of_subset
    (m0 := (inferInstance : MeasurableSpace (FiniteSample n)))
    (m := hsigma.measurableSpace)
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    hsigma.measurableSpace_le hE hD hO hsubset hOcc
  simpa only [E, D, O, sigma, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-- Conditional target-first stopped gap tail at the same full rank. -/
theorem condExp_targetInteriorStoppedFullRankGap_tail_le
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
        (if targetFirstFullRankBacklog hlam0.le (by linarith) B T r sample >
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
      targetFirstFullRankBacklog hlam0.le hlamHalf B T r sample}
  let O : Set (FiniteSample n) := stoppedLowerOccupationEvent
    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0) sigma
    (safeFeedbackA1StopTime
      (n := n) hlam0.le hlamHalf eta B B 0 T)
    (lowerOccupationCountRate ((1 : ℝ) / 2)) q
  have hE : MeasurableSet E := by
    exact measurableSet_lt measurable_const
      (measurable_targetInteriorStoppedFullRankGap
        (n := n) hlam0.le hlamHalf hB eta B 0 T r)
  have hD : MeasurableSet[hsigma.measurableSpace] D := by
    exact measurableSet_lt measurable_const
      (targetFirstFullRankBacklog_stronglyMeasurable
        (n := n) hlam0.le hlamHalf B T r).measurable
  have hO : MeasurableSet O := by
    exact measurableSet_stoppedLowerOccupationEvent_bounded
      (safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0)
      hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
      (safeFeedbackA1StopTime_isStoppingTime
        (n := n) hlam0.le hlamHalf hB eta B 0 T)
  have hsubset : E ⊆ D ∪ O := by
    simpa only [E, D, O, sigma] using
      targetInteriorStoppedFullRankGap_tail_subset
        (n := n) hlam0.le hlamHalf eta B T q r
  have hOcc := safeSourceBulkCount_condExp_lowerOccupation_through_A1
    (n := n) (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hq
    hsigma (feedbackFullRankStart_le hlam0.le hlamHalf B T r)
  have hout := condExp_indicator_le_indicator_add_of_subset
    (m0 := (inferInstance : MeasurableSpace (FiniteSample n)))
    (m := hsigma.measurableSpace)
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    hsigma.measurableSpace_le hE hD hO hsubset hOcc
  simpa only [E, D, O, sigma, Set.indicator, Set.mem_ofPred_eq, gt_iff_lt] using hout

/-! ## Conditional second moments -/

private theorem sourceFirstFullRankBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample ^ (2 : ℕ))
      (finiteSampleLaw n) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hmeas : Measurable (sourceFirstFullRankBacklog hlam0 hlamHalf B T r) :=
    (sourceFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf B T r).mono hsigma.measurableSpace_le |>.measurable
  refine Integrable.of_bound (hmeas.pow measurable_const).aestronglyMeasurable
    ((n : ℝ) ^ 2) (Eventually.of_forall fun sample ↦ ?_)
  have hrn : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
  have hback : sourceFirstFullRankBacklog hlam0 hlamHalf B T r sample ≤ n := by
    unfold sourceFirstFullRankBacklog
    rw [max_le_iff]
    constructor
    · positivity
    · have hcount0 : 0 ≤ (targetFullCount hlam0 hlamHalf B
          (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by positivity
      linarith
  have hback0 := sourceFirstFullRankBacklog_nonneg
    hlam0 hlamHalf B T r sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

private theorem targetFirstFullRankBacklog_sq_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n) :
    Integrable (fun sample : FiniteSample n ↦
      targetFirstFullRankBacklog hlam0 hlamHalf B T r sample ^ (2 : ℕ))
      (finiteSampleLaw n) := by
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0 hlamHalf B T r
  have hmeas : Measurable (targetFirstFullRankBacklog hlam0 hlamHalf B T r) :=
    (targetFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0 hlamHalf B T r).mono hsigma.measurableSpace_le |>.measurable
  refine Integrable.of_bound (hmeas.pow measurable_const).aestronglyMeasurable
    ((n : ℝ) ^ 2) (Eventually.of_forall fun sample ↦ ?_)
  have hrn : (r.val : ℝ) ≤ n := by exact_mod_cast r.isLt.le
  have hback : targetFirstFullRankBacklog hlam0 hlamHalf B T r sample ≤ n := by
    unfold targetFirstFullRankBacklog
    rw [max_le_iff]
    constructor
    · positivity
    · have hcount0 : 0 ≤ (sourceFullCount hlam0 hlamHalf B
          (feedbackFullRankStart hlam0 hlamHalf B T r sample) sample : ℝ) := by positivity
      linarith
  have hback0 := targetFirstFullRankBacklog_nonneg
    hlam0 hlamHalf B T r sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- The actual source-first interior stopped rank gap is square-integrable and has the expected
conditional second-moment bound.  No tail or energy premise remains. -/
theorem sourceInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le
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
          (sourceFirstFullRankBacklog
              hlam0.le (by linarith) B T r sample /
            lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X := sourceInteriorStoppedFullRankGap
    (n := n) hlam0.le hlamHalf eta B B 0 T r
  let K := sourceFirstFullRankBacklog hlam0.le hlamHalf B T r
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
    have h := condExp_sourceInteriorStoppedFullRankGap_tail_le
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
    (sourceFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0.le hlamHalf B T r)
    (sourceFirstFullRankBacklog_nonneg
      (n := n) hlam0.le hlamHalf B T r)
    (sourceFirstFullRankBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf B T r)
    hrates.1 (by norm_num : (0 : ℝ) ≤ 1) hrates.2
    (by simpa only [one_mul] using hActualTail)

/-- Symmetric target-first conditional second-moment theorem. -/
theorem targetInteriorStoppedFullRankGap_integrable_sq_and_condExp_sq_le
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
          (targetFirstFullRankBacklog
              hlam0.le (by linarith) B T r sample /
            lowerOccupationCountRate ((1 : ℝ) / 2)) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let hsigma := feedbackFullRankStart_isStoppingTime
    (n := n) hlam0.le hlamHalf B T r
  let X := targetInteriorStoppedFullRankGap
    (n := n) hlam0.le hlamHalf eta B B 0 T r
  let K := targetFirstFullRankBacklog hlam0.le hlamHalf B T r
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
    have h := condExp_targetInteriorStoppedFullRankGap_tail_le
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
    (targetFirstFullRankBacklog_stronglyMeasurable
      (n := n) hlam0.le hlamHalf B T r)
    (targetFirstFullRankBacklog_nonneg
      (n := n) hlam0.le hlamHalf B T r)
    (targetFirstFullRankBacklog_sq_integrable
      (n := n) hlam0.le hlamHalf B T r)
    hrates.1 (by norm_num : (0 : ℝ) ≤ 1) hrates.2
    (by simpa only [one_mul] using hActualTail)

end FiniteSample

end OTSelector
