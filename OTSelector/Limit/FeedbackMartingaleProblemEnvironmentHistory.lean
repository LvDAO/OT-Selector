import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentNextStopping
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRestartReadout
import OTSelector.Limit.FeedbackCellGeometry

/-!
# The chronological path encoded by an actual environment

Successive event times are obtained by repeatedly selecting the first strictly positive point
of the physically rerooted configurations. The path records their actual waits, marks and
post-event currents. Infinity is absorbing; coordinates after an infinite event time use a
virtual fallback. Geometric identities are asserted only for reached, finite event times.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 200000

namespace OTSelector.Limit

open PointProcess

/-- Joint measurability of the actual chronological successor, including the absorbing value. -/
theorem measurable_feedbackEnvironmentNextTimeExtended :
    Measurable (fun p : FeedbackEnvironment × ℝ≥0∞ ↦
      feedbackEnvironmentNextTimeExtended p.1 p.2) := by
  have hp : Measurable (fun p : FeedbackEnvironment × ℝ≥0∞ ↦ (p.2.toReal, p.1)) :=
    measurable_snd.ennreal_toReal.prodMk measurable_fst
  have hr := FeedbackEnvironment.measurable_uncurry_reroot.comp hp
  have hc : Measurable (fun p : FeedbackEnvironment × ℝ≥0∞ ↦ (p.2.toNNReal : ℝ≥0∞)) :=
    measurable_snd.ennreal_toNNReal.coe_nnreal_ennreal
  have ht := measurable_feedbackEnvironmentFirstTime.comp hr
  have hi : Measurable (fun p : FeedbackEnvironment × ℝ≥0∞ ↦
      if p.2 = ∞ then ∞ else (p.2.toNNReal : ℝ≥0∞) +
        feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot p.2.toReal p.1)) :=
    measurable_const.ite (measurableSet_eq_fun measurable_snd measurable_const) (hc.add ht)
  exact hi

/-- Zero is the root cut; every successor is the next actual event after the preceding cut. -/
noncomputable def feedbackEnvironmentEventTime (e : FeedbackEnvironment) : ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => feedbackEnvironmentNextTimeExtended e (feedbackEnvironmentEventTime e n)

@[simp]
theorem feedbackEnvironmentEventTime_zero (e : FeedbackEnvironment) :
    feedbackEnvironmentEventTime e 0 = 0 := rfl

theorem feedbackEnvironmentEventTime_succ (e : FeedbackEnvironment) (n : ℕ) :
    feedbackEnvironmentEventTime e (n + 1) =
      feedbackEnvironmentNextTimeExtended e (feedbackEnvironmentEventTime e n) := rfl

@[fun_prop]
theorem measurable_feedbackEnvironmentEventTime (n : ℕ) :
    Measurable (fun e ↦ feedbackEnvironmentEventTime e n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable (fun e : FeedbackEnvironment ↦ (e, feedbackEnvironmentEventTime e n)) :=
      measurable_id.prodMk ih
    have hh := measurable_feedbackEnvironmentNextTimeExtended.comp hp
    exact hh

theorem le_feedbackEnvironmentNextTimeExtended (e : FeedbackEnvironment) (a : ℝ≥0∞) :
    a ≤ feedbackEnvironmentNextTimeExtended e a := by
  cases a using ENNReal.recTopCoe with
  | top => simp
  | coe a =>
    rw [feedbackEnvironmentNextTimeExtended_coe]
    exact (lt_feedbackEnvironmentNextTime e a).le

theorem feedbackEnvironmentEventTime_le_succ (e : FeedbackEnvironment) (n : ℕ) :
    feedbackEnvironmentEventTime e n ≤ feedbackEnvironmentEventTime e (n + 1) :=
  le_feedbackEnvironmentNextTimeExtended e _

theorem monotone_feedbackEnvironmentEventTime (e : FeedbackEnvironment) :
    Monotone (feedbackEnvironmentEventTime e) :=
  monotone_nat_of_le_succ (feedbackEnvironmentEventTime_le_succ e)

theorem feedbackEnvironmentEventTime_ne_top_of_le (e : FeedbackEnvironment)
    {m n : ℕ} (hmn : m ≤ n) (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackEnvironmentEventTime e m ≠ ∞ :=
  ne_top_of_le_ne_top hn (monotone_feedbackEnvironmentEventTime e hmn)

/-- Every chronological event time is stopping for a filtration revealing the aggregate
actual count. This assertion does not require adaptedness of the marks. -/
theorem feedbackEnvironmentEventTime_isStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] (e : Ω → FeedbackEnvironment)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t)) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ feedbackEnvironmentEventTime (e ω) n) := by
  induction n with
  | zero => exact isStoppingTime_const ℱ 0
  | succ n ih => exact feedbackEnvironmentNextTimeExtended_isStoppingTime e ℱ hcount ih

/-- The actual environment viewed from event `n`. At infinity this is a measurable total
fallback, and statements about its event geometry require a finite event time. -/
noncomputable def feedbackEnvironmentAfterEvent (e : FeedbackEnvironment) (n : ℕ) :
    FeedbackEnvironment :=
  FeedbackEnvironment.reroot (feedbackEnvironmentEventTime e n).toReal e

@[fun_prop]
theorem measurable_feedbackEnvironmentAfterEvent (n : ℕ) :
    Measurable (fun e ↦ feedbackEnvironmentAfterEvent e n) := by
  have hp : Measurable (fun e : FeedbackEnvironment ↦
      ((feedbackEnvironmentEventTime e n).toReal, e)) :=
    (measurable_feedbackEnvironmentEventTime n).ennreal_toReal.prodMk measurable_id
  have hh := FeedbackEnvironment.measurable_uncurry_reroot.comp hp
  exact hh

theorem feedbackEnvironmentEventTime_succ_eq_add (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackEnvironmentEventTime e (n + 1) = feedbackEnvironmentEventTime e n +
      feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n) := by
  rw [feedbackEnvironmentEventTime_succ]
  unfold feedbackEnvironmentNextTimeExtended
  rw [ite_eq_right hn]
  unfold feedbackEnvironmentNextTime
  rw [ENNReal.coe_toNNReal hn]
  rfl

theorem feedbackEnvironmentEventTime_lt_succ (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackEnvironmentEventTime e n < feedbackEnvironmentEventTime e (n + 1) := by
  rw [feedbackEnvironmentEventTime_succ_eq_add e n hn]
  exact ENNReal.lt_add_right hn (LocalConfiguration.firstPositiveTime_pos
    (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n))).ne'

theorem feedbackEnvironmentAfterEvent_firstTime_ne_top
    (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞) :
    feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n) ≠ ∞ := by
  have hprev := feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn
  rw [feedbackEnvironmentEventTime_succ_eq_add e n hprev] at hn
  exact (ENNReal.add_ne_top.mp hn).2

theorem feedbackEnvironmentEventTime_succ_toReal (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞) :
    (feedbackEnvironmentEventTime e (n + 1)).toReal =
      (feedbackEnvironmentEventTime e n).toReal +
        (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal := by
  have hprev := feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn
  rw [feedbackEnvironmentEventTime_succ_eq_add e n hprev,
    ENNReal.toReal_add hprev (feedbackEnvironmentAfterEvent_firstTime_ne_top e n hn)]

/-- The actual marked path in the existing trajectory carrier. The coordinate at zero is
virtual; the next coordinate records the first event after the preceding physical cut. -/
noncomputable def feedbackEnvironmentFuturePath (e : FeedbackEnvironment) : FeedbackCellPath
  | 0 => feedbackMarkedVirtual e.path.rootCurrent
  | n + 1 => if feedbackEnvironmentEventTime e n = ∞ then
      feedbackMarkedVirtual e.path.rootCurrent else
      ((feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal,
        feedbackEnvironmentFirstJump (feedbackEnvironmentAfterEvent e n))

@[simp]
theorem feedbackEnvironmentFuturePath_zero (e : FeedbackEnvironment) :
    feedbackEnvironmentFuturePath e 0 = feedbackMarkedVirtual e.path.rootCurrent := rfl

theorem feedbackEnvironmentFuturePath_succ (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackEnvironmentFuturePath e (n + 1) =
      ((feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal,
        feedbackEnvironmentFirstJump (feedbackEnvironmentAfterEvent e n)) := by
  simp only [feedbackEnvironmentFuturePath, hn, ite_false]

@[fun_prop]
theorem measurable_feedbackEnvironmentFuturePath : Measurable feedbackEnvironmentFuturePath := by
  classical
  apply measurable_pi_lambda
  intro n
  have hv := (measurable_of_countable feedbackMarkedVirtual).comp
    FeedbackEnvironment.measurable_rootCurrent
  cases n with
  | zero => exact hv
  | succ n =>
    have ht := measurable_feedbackEnvironmentFirstTime.comp
      (measurable_feedbackEnvironmentAfterEvent n)
    have hj := measurable_feedbackEnvironmentFirstJump.comp
      (measurable_feedbackEnvironmentAfterEvent n)
    have hg := ht.ennreal_toReal.prodMk hj
    have hset : MeasurableSet {e : FeedbackEnvironment | feedbackEnvironmentEventTime e n = ∞} :=
      measurableSet_eq_fun (measurable_feedbackEnvironmentEventTime n) measurable_const
    exact hv.ite hset hg

/-- The encoded clock of every reached event is its physical event time. -/
theorem feedbackCellClock_feedbackEnvironmentFuturePath
    (e : FeedbackEnvironment) (n : ℕ) (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackCellClock (feedbackEnvironmentFuturePath e) n =
      (feedbackEnvironmentEventTime e n).toReal := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn
    rw [feedbackCellClock_succ, ih hprev, feedbackEnvironmentFuturePath_succ e n hprev,
      feedbackEnvironmentEventTime_succ_toReal e n hn]

/-- Every reached actual waiting time is strictly positive. -/
theorem feedbackEnvironmentFuturePath_wait_pos (e : FeedbackEnvironment) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞) :
    0 < (feedbackEnvironmentFuturePath e (n + 1)).1 := by
  rw [feedbackEnvironmentFuturePath_succ e n
    (feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn)]
  exact ENNReal.toReal_pos
    (LocalConfiguration.firstPositiveTime_pos
      (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n))).ne'
    (feedbackEnvironmentAfterEvent_firstTime_ne_top e n hn)

/-- Under actual time simplicity, the selected post-event current is the actual current at
that absolute physical cut. -/
theorem feedbackEnvironmentFuturePath_current_succ
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞) :
    (feedbackEnvironmentFuturePath e (n + 1)).2.2 =
      feedbackEnvironmentCurrent e (feedbackEnvironmentEventTime e (n + 1)).toReal := by
  rw [feedbackEnvironmentFuturePath_succ e n
    (feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn)]
  have hc := feedbackEnvironmentCurrent_firstTime (feedbackEnvironmentAfterEvent e n)
    (feedbackEnvironment_isTimeSimple_reroot e hsimple _)
    (feedbackEnvironmentAfterEvent_firstTime_ne_top e n hn)
  change feedbackEnvironmentCurrent
    (FeedbackEnvironment.reroot (feedbackEnvironmentEventTime e n).toReal e)
    (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal = _ at hc
  rw [feedbackEnvironmentCurrent_reroot] at hc
  rw [feedbackEnvironmentEventTime_succ_toReal e n hn, add_comm]
  exact hc.symm

theorem feedbackEnvironmentFuturePath_current
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    (feedbackEnvironmentFuturePath e n).2.2 =
      feedbackEnvironmentCurrent e (feedbackEnvironmentEventTime e n).toReal := by
  cases n with
  | zero =>
    simp [feedbackMarkedVirtual, feedbackEnvironmentCurrent,
      FeedbackEnvironment.currentIncrement]
  | succ n => exact feedbackEnvironmentFuturePath_current_succ e hsimple n hn

/-- At a reached event the root current of the genuinely rerooted environment is the current
stored by the chronological path. -/
theorem feedbackEnvironmentAfterEvent_rootCurrent
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    (feedbackEnvironmentAfterEvent e n).path.rootCurrent =
      (feedbackEnvironmentFuturePath e n).2.2 :=
  (feedbackEnvironmentFuturePath_current e hsimple n hn).symm

end OTSelector.Limit
