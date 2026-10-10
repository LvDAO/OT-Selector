import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentReadout
import OTSelector.Limit.FeedbackMartingaleProblemCountingReadout
import OTSelector.Limit.FeedbackMartingaleProblemStoppedProcess

/-!
# The next actual event after a stopping coordinate

The next event is selected from the actual rerooted configurations. Its stopping event is
exactly a strict increase of the revealed aggregate count. Right continuity makes the
aggregate count at a capped stopping coordinate measurable in the present filtration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess CountingProcess

private theorem coe_cappedStoppingValue_ennreal {Ω : Type*} (t : ℝ≥0)
    (τ : Ω → ℝ≥0∞) (ω : Ω) :
    (cappedStoppingValue t τ ω : ℝ≥0∞) = min (τ ω) (t : ℝ≥0∞) :=
  coe_cappedStoppingValue t τ ω

/-- The total actual number of source and target points in `(0,t]`, with multiplicities. -/
noncomputable def feedbackEnvironmentEventCount (e : FeedbackEnvironment) (t : ℝ≥0) : ℤ :=
  LocalConfiguration.spatialCount e.source 0 t +
    LocalConfiguration.spatialCount e.target 0 t

/-- The first actual event strictly after the finite cut `a`, in absolute coordinates. -/
noncomputable def feedbackEnvironmentNextTime (e : FeedbackEnvironment) (a : ℝ≥0) : ℝ≥0∞ :=
  (a : ℝ≥0∞) + feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)

theorem lt_feedbackEnvironmentNextTime (e : FeedbackEnvironment) (a : ℝ≥0) :
    (a : ℝ≥0∞) < feedbackEnvironmentNextTime e a :=
  ENNReal.lt_add_right ENNReal.coe_ne_top
    (LocalConfiguration.firstPositiveTime_pos
      (feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e))).ne'

/-- A strict count increase detects the next event, including its multiplicity. No
simplicity of the configurations is required. -/
theorem feedbackEnvironmentNextTime_le_iff (e : FeedbackEnvironment) (a t : ℝ≥0) :
    feedbackEnvironmentNextTime e a ≤ (t : ℝ≥0∞) ↔
      a ≤ t ∧ feedbackEnvironmentEventCount e a < feedbackEnvironmentEventCount e t := by
  by_cases hat : a ≤ t
  · have htime : feedbackEnvironmentNextTime e a ≤ (t : ℝ≥0∞) ↔
        feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e) ≤
          ((t - a : ℝ≥0) : ℝ≥0∞) := by
      unfold feedbackEnvironmentNextTime
      calc
        _ ↔ (a : ℝ≥0∞) + feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e) ≤
            (a : ℝ≥0∞) + ((t - a : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_add, add_tsub_cancel_of_le hat]
        _ ↔ _ := ENNReal.add_le_add_iff_left ENNReal.coe_ne_top
    have hfirst := LocalConfiguration.firstPositiveTime_le_iff
      (feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e))
      (t := (t : ℝ) - (a : ℝ)) (sub_nonneg.mpr (show (a : ℝ) ≤ t from hat))
    change feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e) ≤
        ENNReal.ofReal ((t : ℝ) - (a : ℝ)) ↔
      1 ≤ LocalConfiguration.spatialCount (LocalConfiguration.reroot a e.source) 0
        ((t : ℝ) - (a : ℝ)) +
        LocalConfiguration.spatialCount (LocalConfiguration.reroot a e.target) 0
          ((t : ℝ) - (a : ℝ)) at hfirst
    rw [LocalConfiguration.spatialCount_reroot, LocalConfiguration.spatialCount_reroot,
      zero_add, sub_add_cancel] at hfirst
    have hd : ENNReal.ofReal ((t : ℝ) - (a : ℝ)) = ((t - a : ℝ≥0) : ℝ≥0∞) := by
      rw [← NNReal.coe_sub hat, ENNReal.ofReal_coe_nnreal]
    rw [hd] at hfirst
    have hs := LocalConfiguration.spatialCount_add e.source a.property
      (show (a : ℝ) ≤ t from hat)
    have ht := LocalConfiguration.spatialCount_add e.target a.property
      (show (a : ℝ) ≤ t from hat)
    rw [htime, hfirst, and_iff_right hat]
    change 1 ≤ LocalConfiguration.spatialCount e.source a t +
        LocalConfiguration.spatialCount e.target a t ↔
      LocalConfiguration.spatialCount e.source 0 a +
          LocalConfiguration.spatialCount e.target 0 a <
        LocalConfiguration.spatialCount e.source 0 t +
          LocalConfiguration.spatialCount e.target 0 t
    rw [hs, ht]
    exact (show ∀ A B C D : ℤ, 1 ≤ C + D ↔ A + B < (A + C) + (B + D) by
      intros; omega) _ _ _ _
  · have hnot : ¬feedbackEnvironmentNextTime e a ≤ (t : ℝ≥0∞) := by
      intro h
      exact hat (ENNReal.coe_le_coe.mp ((lt_feedbackEnvironmentNextTime e a).le.trans h))
    simp only [hnot, hat, false_and]

/-- The actual aggregate count is right continuous on the nonnegative time carrier. -/
theorem continuousWithinAt_feedbackEnvironmentEventCount
    (e : FeedbackEnvironment) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 ↦ (feedbackEnvironmentEventCount e s : ℝ)) (Ici t) t := by
  have hs := LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal
    (feedbackEnvironmentTwoColor e) true (fun _ ↦ (1 : ℝ)) t
  have ht := LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal
    (feedbackEnvironmentTwoColor e) false (fun _ ↦ (1 : ℝ)) t
  convert hs.add ht using 1
  funext s
  simp only [Pi.add_apply, LocalConfiguration.firstEventTestCount_one,
    feedbackEnvironmentTwoColor, ite_true, Bool.false_eq_true, ite_false,
    feedbackEnvironmentEventCount, Int.cast_add]


/-- Next-event selection after a finite stopping coordinate is itself a stopping time. -/
theorem feedbackEnvironmentNextTime_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (e : Ω → FeedbackEnvironment)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) :
    IsStoppingTime ℱ (fun ω ↦ feedbackEnvironmentNextTime (e ω) (σ ω)) := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ feedbackEnvironmentEventCount (e ω) t
  have hN : StronglyAdapted ℱ N := fun t ↦
    ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp (hcount t)).stronglyMeasurable
  have hstop := stronglyAdapted_cappedStoppingValue_of_rightContinuous hN hσ
    (fun ω t ↦ continuousWithinAt_feedbackEnvironmentEventCount (e ω) t)
  intro t
  have hset : {ω | feedbackEnvironmentNextTime (e ω) (σ ω) ≤ (t : ℝ≥0∞)} =
      {ω | (σ ω : WithTop ℝ≥0) ≤ t} ∩
        {ω | N (cappedStoppingValue t (fun ω ↦ (σ ω : WithTop ℝ≥0)) ω) ω < N t ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, feedbackEnvironmentNextTime_le_iff,
      WithTop.coe_le_coe]
    by_cases hω : σ ω ≤ t
    · have hc : cappedStoppingValue t (fun ω ↦ (σ ω : WithTop ℝ≥0)) ω = σ ω := by
        apply WithTop.coe_injective
        rw [coe_cappedStoppingValue, min_eq_left (by exact_mod_cast hω)]
      rw [hc, and_iff_right hω, and_iff_right hω]
      exact Int.cast_lt.symm
    · simp only [hω, false_and]
  change MeasurableSet[ℱ t] {ω | feedbackEnvironmentNextTime (e ω) (σ ω) ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact (hσ t).inter (measurableSet_lt (hstop t).measurable (hN t).measurable)

/-- The actual next event, capped by a deterministic duration after its starting cut. -/
noncomputable def feedbackEnvironmentNextCappedTime (e : FeedbackEnvironment)
    (a t : ℝ≥0) : ℝ≥0 :=
  a + cappedStoppingValue t
    (fun _ : Unit ↦ feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)) ()

theorem coe_feedbackEnvironmentNextCappedTime (e : FeedbackEnvironment) (a t : ℝ≥0) :
    (feedbackEnvironmentNextCappedTime e a t : ℝ≥0∞) =
      min (feedbackEnvironmentNextTime e a) ((a + t : ℝ≥0) : ℝ≥0∞) := by
  unfold feedbackEnvironmentNextCappedTime feedbackEnvironmentNextTime
  rw [ENNReal.coe_add, coe_cappedStoppingValue_ennreal, ENNReal.coe_add]
  exact add_min _ _ _

theorem feedbackEnvironmentNextCappedTime_le (e : FeedbackEnvironment) (a t : ℝ≥0) :
    feedbackEnvironmentNextCappedTime e a t ≤ a + t :=
  add_le_add le_rfl (cappedStoppingValue_le t _ ())

theorem le_feedbackEnvironmentNextCappedTime (e : FeedbackEnvironment) (a t : ℝ≥0) :
    a ≤ feedbackEnvironmentNextCappedTime e a t := le_add_of_nonneg_right (by positivity)

theorem feedbackEnvironmentNextCappedTime_le_of_le (e : FeedbackEnvironment)
    {a S : ℝ≥0} (ha : a ≤ S) (t : ℝ≥0) :
    feedbackEnvironmentNextCappedTime e a t ≤ S + t :=
  (feedbackEnvironmentNextCappedTime_le e a t).trans (add_le_add ha le_rfl)

theorem feedbackEnvironmentNextCappedTime_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (e : Ω → FeedbackEnvironment)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    IsStoppingTime ℱ (fun ω ↦ (feedbackEnvironmentNextCappedTime (e ω) (σ ω) t :
      WithTop ℝ≥0)) := by
  have heq : (fun ω ↦ (feedbackEnvironmentNextCappedTime (e ω) (σ ω) t : WithTop ℝ≥0)) =
      (fun ω ↦ min (feedbackEnvironmentNextTime (e ω) (σ ω))
        ((σ ω + t : ℝ≥0) : WithTop ℝ≥0)) := by
    funext ω
    exact coe_feedbackEnvironmentNextCappedTime (e ω) (σ ω) t
  rw [heq]
  exact (feedbackEnvironmentNextTime_isStoppingTime e ℱ hcount hσ).min
    (CountingProcess.IsStoppingTime.coe_add_const hσ t)

/-- The chronological successor of a possibly infinite cut. Infinity remains absorbing. -/
noncomputable def feedbackEnvironmentNextTimeExtended (e : FeedbackEnvironment)
    (a : ℝ≥0∞) : ℝ≥0∞ :=
  if a = ∞ then ∞ else feedbackEnvironmentNextTime e a.toNNReal

@[simp]
theorem feedbackEnvironmentNextTimeExtended_coe (e : FeedbackEnvironment) (a : ℝ≥0) :
    feedbackEnvironmentNextTimeExtended e (a : ℝ≥0∞) = feedbackEnvironmentNextTime e a := by
  simp [feedbackEnvironmentNextTimeExtended]

@[simp]
theorem feedbackEnvironmentNextTimeExtended_top (e : FeedbackEnvironment) :
    feedbackEnvironmentNextTimeExtended e ∞ = ∞ := by
  simp [feedbackEnvironmentNextTimeExtended]

/-- For a finite observation horizon the successor event is unchanged by capping its start.
Strict positivity of the next wait excludes a spurious event when the cap equals the horizon. -/
theorem feedbackEnvironmentNextTimeExtended_le_iff_capped
    (e : FeedbackEnvironment) (a : ℝ≥0∞) (t : ℝ≥0) :
    feedbackEnvironmentNextTimeExtended e a ≤ (t : ℝ≥0∞) ↔
      feedbackEnvironmentNextTime e (cappedStoppingValue t (fun _ : Unit ↦ a) ()) ≤
        (t : ℝ≥0∞) := by
  cases a using ENNReal.recTopCoe with
  | top =>
    have hc : cappedStoppingValue t (fun _ : Unit ↦ (∞ : ℝ≥0∞)) () = t := by
      apply ENNReal.coe_injective
      rw [coe_cappedStoppingValue_ennreal, min_eq_right le_top]
    rw [hc, feedbackEnvironmentNextTimeExtended_top]
    exact iff_of_false (not_le_of_gt ENNReal.coe_lt_top)
      (not_le_of_gt (lt_feedbackEnvironmentNextTime e t))
  | coe a =>
    have hc : cappedStoppingValue t (fun _ : Unit ↦ (a : ℝ≥0∞)) () = min a t := by
      apply ENNReal.coe_injective
      rw [coe_cappedStoppingValue_ennreal, ENNReal.coe_min]
    rw [hc, feedbackEnvironmentNextTimeExtended_coe]
    by_cases hat : a ≤ t
    · rw [min_eq_left hat]
    · rw [min_eq_right (le_of_not_ge hat)]
      exact iff_of_false
        (fun h ↦ hat ((feedbackEnvironmentNextTime_le_iff e a t).mp h).1)
        (not_le_of_gt (lt_feedbackEnvironmentNextTime e t))

/-- Actual chronological successors are stopping times even when the starting time can be
infinite. The finite-cap argument avoids assigning any artificial finite start at infinity. -/
theorem feedbackEnvironmentNextTimeExtended_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (e : Ω → FeedbackEnvironment)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) :
    IsStoppingTime ℱ (fun ω ↦ feedbackEnvironmentNextTimeExtended (e ω) (σ ω)) := by
  intro t
  have hs := feedbackEnvironmentNextTime_isStoppingTime e ℱ hcount
    (cappedStoppingValue_isStoppingTime ℱ hσ t)
  have hset : {ω | feedbackEnvironmentNextTimeExtended (e ω) (σ ω) ≤ (t : ℝ≥0∞)} =
      {ω | feedbackEnvironmentNextTime (e ω) (cappedStoppingValue t σ ω) ≤ (t : ℝ≥0∞)} := by
    ext ω
    exact feedbackEnvironmentNextTimeExtended_le_iff_capped (e ω) (σ ω) t
  change MeasurableSet[ℱ t] {ω | feedbackEnvironmentNextTimeExtended (e ω) (σ ω) ≤ (t : ℝ≥0∞)}
  rw [hset]
  exact hs t

end OTSelector.Limit
