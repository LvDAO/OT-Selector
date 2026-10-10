import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentHistory
import OTSelector.Limit.FeedbackStationaryFutureEnvironment
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Recovering the actual positive configurations from chronological events

Consecutive event intervals partition the positive half-line. The actual counting measure
restricted to each interval is exactly its selected colored atom, so the chronological path
recovers both physical point measures, including their sampled marks.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

attribute [local instance] Classical.propDecidable

/-- In absolute coordinates, the actual interval from a cut through its first next event
contains precisely that selected colored point. -/
theorem countingMeasure_feedbackEnvironment_nextInterval
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (a : ℝ) (hfinite : feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e) ≠ ∞)
    (b : Bool) :
    (LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b)).restrict
      (LocalConfiguration.spatialIoc a
        (a + (feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)).toReal)) =
      if (feedbackEnvironmentFirstEvent (FeedbackEnvironment.reroot a e)).1 = b then
        Measure.dirac
          (a + (feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)).toReal,
            (feedbackEnvironmentFirstEvent (FeedbackEnvironment.reroot a e)).2.2) else 0 := by
  let c := feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e)
  let τ := feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)
  have ht : ENNReal.ofReal τ.toReal = τ := ENNReal.ofReal_toReal hfinite
  have hfirst := LocalConfiguration.countingMeasure_restrict_firstPositiveTime c
    (feedbackEnvironment_isTimeSimple_reroot e hsimple a) b τ.toReal
  change (LocalConfiguration.countingMeasure (c b)).restrict
      (LocalConfiguration.spatialIoc 0 (min (ENNReal.ofReal τ.toReal) τ).toReal) = _ at hfirst
  rw [ht, min_self] at hfirst
  have hle : LocalConfiguration.firstPositiveTime c ≤ τ := le_rfl
  simp only [hle, true_and] at hfirst
  have hback : (LocalConfiguration.countingMeasure (c b)).map
      (Configuration.pointTranslation a) =
      LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b) := by
    dsimp only [c]
    rw [feedbackEnvironmentTwoColor_reroot, LocalConfiguration.countingMeasure_reroot,
      Measure.map_map (Configuration.pointTranslation a).measurable
        (Configuration.pointTranslation (-a)).measurable]
    have heq : (Configuration.pointTranslation a : MatchingPoint → MatchingPoint) ∘
        Configuration.pointTranslation (-a) = id := by
      funext p
      simp
    rw [heq, Measure.map_id]
  have hwindow : (Configuration.pointTranslation a) ⁻¹'
      LocalConfiguration.spatialIoc a (a + τ.toReal) =
        LocalConfiguration.spatialIoc 0 τ.toReal := by
    ext p
    simp only [mem_preimage, Configuration.pointTranslation_apply,
      LocalConfiguration.spatialIoc, mem_Ioc]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  rw [← hback, Measure.restrict_map (Configuration.pointTranslation a).measurable
    (LocalConfiguration.measurableSet_spatialIoc _ _), hwindow, hfirst]
  have hpoint : (LocalConfiguration.firstPositiveEvent c).2.1 = τ.toReal := by
    have hspec := LocalConfiguration.firstPositiveEvent_spec c hfinite
    change (LocalConfiguration.firstPositiveEvent c).2.1 =
      (LocalConfiguration.firstPositiveTime c).toReal
    rw [← hspec.2, ENNReal.toReal_ofReal hspec.1.1.le]
  by_cases hb : (LocalConfiguration.firstPositiveEvent c).1 = b
  · have hb' : (feedbackEnvironmentFirstEvent (FeedbackEnvironment.reroot a e)).1 = b := hb
    simp only [hb, hb', ite_true, Measure.map_dirac]
    congr 1
    apply Prod.ext
    · simp only [Configuration.pointTranslation_apply, hpoint]
      exact add_comm _ _
    · rfl
  · have hb' : ¬(feedbackEnvironmentFirstEvent (FeedbackEnvironment.reroot a e)).1 = b := hb
    simp only [hb, hb', ite_false, Measure.map_zero]

/-- Each chronological current increment is the sign of the actual selected event color. -/
theorem feedbackEnvironmentFuturePath_jump
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (n : ℕ) (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackCellJump (feedbackEnvironmentFuturePath e) n =
      if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 then 1 else -1 := by
  unfold feedbackCellJump
  rw [feedbackEnvironmentFuturePath_succ e n hn]
  change ((feedbackEnvironmentAfterEvent e n).path.rootCurrent +
      (if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 then 1 else -1)) -
        (feedbackEnvironmentFuturePath e n).2.2 = _
  rw [feedbackEnvironmentAfterEvent_rootCurrent e hsimple n hn]
  omega

/-- Each actual consecutive event interval is the corresponding atom of the chronological
point-measure readout. -/
theorem countingMeasure_feedbackEnvironment_eventInterval
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (n : ℕ) (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞) (b : Bool) :
    (LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b)).restrict
      (LocalConfiguration.spatialIoc (feedbackEnvironmentEventTime e n).toReal
        (feedbackEnvironmentEventTime e (n + 1)).toReal) =
      if feedbackCellJump (feedbackEnvironmentFuturePath e) n = (if b then 1 else -1) then
        Measure.dirac (feedbackCellClock (feedbackEnvironmentFuturePath e) (n + 1),
          (feedbackEnvironmentFuturePath e (n + 1)).2.1) else 0 := by
  have hp := feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn
  have hinterval := countingMeasure_feedbackEnvironment_nextInterval e hsimple
    (feedbackEnvironmentEventTime e n).toReal
    (feedbackEnvironmentAfterEvent_firstTime_ne_top e n hn) b
  change (LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b)).restrict
    (LocalConfiguration.spatialIoc (feedbackEnvironmentEventTime e n).toReal
      ((feedbackEnvironmentEventTime e n).toReal +
        (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal)) =
    (if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 = b then
      Measure.dirac _ else 0) at hinterval
  rw [feedbackEnvironmentEventTime_succ_toReal e n hn, hinterval,
    feedbackEnvironmentFuturePath_jump e hsimple n hp,
    feedbackCellClock_feedbackEnvironmentFuturePath e (n + 1) hn,
    feedbackEnvironmentEventTime_succ_toReal e n hn,
    feedbackEnvironmentFuturePath_succ e n hp]
  change (if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 = b then
      Measure.dirac _ else 0) =
    if (if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 then
      (1 : ℤ) else -1) = (if b then 1 else -1) then Measure.dirac _ else 0
  cases hb : (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 <;>
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
      reduceCtorEq, Int.reduceNeg]
  all_goals rfl

/-- When all actual event times are finite and escape every bounded window, the two positive
physical counting measures are exactly the point measures encoded by the actual future path. -/
theorem feedbackPositiveEnvironmentPoints_eq_futurePath
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (hfinite : ∀ n, feedbackEnvironmentEventTime e n ≠ ∞)
    (hescape : Tendsto (fun n ↦ (feedbackEnvironmentEventTime e n).toReal) atTop atTop) :
    feedbackPositiveEnvironmentPoints e =
      feedbackFuturePointMeasures (feedbackEnvironmentFuturePath e) := by
  let t : ℕ → ℝ := fun n ↦ (feedbackEnvironmentEventTime e n).toReal
  have htmono : Monotone t := fun i j hij ↦ ENNReal.toReal_mono (hfinite j)
    (monotone_feedbackEnvironmentEventTime e hij)
  have htzero : t 0 = 0 := by simp [t]
  have hintervals : (⋃ n, Ioc (t n) (t (n + 1))) = Ioi (0 : ℝ) := by
    simpa only [Order.succ_eq_add_one, Nat.bot_eq_zero, htzero] using
      iUnion_Ioc_map_succ_eq_Ioi (fun n ↦ htmono (Nat.zero_le n))
        (not_bddAbove_of_tendsto_atTop hescape)
  have hcover : (⋃ n, LocalConfiguration.spatialIoc (t n) (t (n + 1))) =
      Ioi (0 : ℝ) ×ˢ (univ : Set UnitMark) := by
    ext p
    simp only [mem_iUnion]
    have hh := Set.ext_iff.mp hintervals p.1
    simpa only [LocalConfiguration.spatialIoc, mem_preimage, mem_Ioc, mem_iUnion, mem_prod, mem_Ioi,
      mem_univ, and_true] using hh
  have hdis : Pairwise (fun n m ↦ Disjoint
      (LocalConfiguration.spatialIoc (t n) (t (n + 1)))
      (LocalConfiguration.spatialIoc (t m) (t (m + 1)))) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro p hp hq
    rcases lt_or_gt_of_ne hnm with h | h
    · have hh := htmono (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hp.2.trans hh)) hq.1
    · have hh := htmono (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hq.2.trans hh)) hp.1
  have hcolor (b : Bool) :
      (LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b)).restrict
        (Ioi (0 : ℝ) ×ˢ univ) =
      feedbackFutureDirectionMeasure (if b then 1 else -1) (feedbackEnvironmentFuturePath e) := by
    rw [← hcover, Measure.restrict_iUnion hdis
      (fun n ↦ LocalConfiguration.measurableSet_spatialIoc _ _)]
    unfold feedbackFutureDirectionMeasure
    congr 1
    funext n
    exact countingMeasure_feedbackEnvironment_eventInterval e hsimple n (hfinite (n + 1)) b
  exact Prod.ext (hcolor true) (hcolor false)

end OTSelector.Limit
