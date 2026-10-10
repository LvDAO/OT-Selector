import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRegularity
import OTSelector.Limit.FeedbackMartingaleProblemRestartTest

/-!
# Restarting the actual spatial marked compensators

Rerooting at a cut transforms the original marked-count compensator into its increment after
that cut. This is a deterministic identity of the actual configurations and current, and is
the geometric input to optional sampling on a revealed jump history.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess

/-- At a finite first event, the selected next current equals the current computed from the
actual point counts at that cut. -/
theorem feedbackEnvironmentCurrent_firstTime
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (hfinite : feedbackEnvironmentFirstTime e ≠ ∞) :
    feedbackEnvironmentCurrent e (feedbackEnvironmentFirstTime e).toReal =
      (feedbackEnvironmentFirstJump e).2 := by
  classical
  have htime : ENNReal.ofReal (feedbackEnvironmentFirstTime e).toReal =
      feedbackEnvironmentFirstTime e := ENNReal.ofReal_toReal hfinite
  have hc (b : Bool) := LocalConfiguration.firstEventTestCount_min
    (feedbackEnvironmentTwoColor e) hsimple b (fun _ ↦ (1 : ℝ))
    (feedbackEnvironmentFirstTime e).toReal
  have hc' (b : Bool) :
      (LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor e b) 0
        (feedbackEnvironmentFirstTime e).toReal : ℝ) =
        if (feedbackEnvironmentFirstEvent e).1 = b then 1 else 0 := by
    have h := hc b
    change LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b
      (fun _ ↦ (1 : ℝ))
      (min (ENNReal.ofReal (feedbackEnvironmentFirstTime e).toReal)
        (feedbackEnvironmentFirstTime e)).toReal = _ at h
    rw [htime, min_self, LocalConfiguration.firstEventTestCount_one] at h
    by_cases hb : (LocalConfiguration.firstPositiveEvent (feedbackEnvironmentTwoColor e)).1 = b
    · simpa [htime, feedbackEnvironmentFirstTime, feedbackEnvironmentFirstEvent, hb] using h
    · simpa [htime, feedbackEnvironmentFirstTime, feedbackEnvironmentFirstEvent, hb] using h
  have hs := hc' true
  have ht := hc' false
  have hz (b : Bool) : LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor e b)
      (feedbackEnvironmentFirstTime e).toReal 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le _ ENNReal.toReal_nonneg
  change e.path.rootCurrent +
      ((LocalConfiguration.spatialCount e.source 0 (feedbackEnvironmentFirstTime e).toReal -
        LocalConfiguration.spatialCount e.source (feedbackEnvironmentFirstTime e).toReal 0) -
        (LocalConfiguration.spatialCount e.target 0 (feedbackEnvironmentFirstTime e).toReal -
          LocalConfiguration.spatialCount e.target (feedbackEnvironmentFirstTime e).toReal 0)) =
    e.path.rootCurrent + if (feedbackEnvironmentFirstEvent e).1 then 1 else -1
  have hzs : LocalConfiguration.spatialCount e.source (feedbackEnvironmentFirstTime e).toReal 0 = 0 := hz true
  have hzt : LocalConfiguration.spatialCount e.target (feedbackEnvironmentFirstTime e).toReal 0 = 0 := hz false
  rw [hzs, hzt, sub_zero, sub_zero]
  cases hb : (feedbackEnvironmentFirstEvent e).1
  · simp [feedbackEnvironmentTwoColor, hb] at hs ht
    have hs' : LocalConfiguration.spatialCount e.source 0 (feedbackEnvironmentFirstTime e).toReal = 0 := by exact_mod_cast hs
    have ht' : LocalConfiguration.spatialCount e.target 0 (feedbackEnvironmentFirstTime e).toReal = 1 := by exact_mod_cast ht
    simp [hs', ht']
  · simp [feedbackEnvironmentTwoColor, hb] at hs ht
    have hs' : LocalConfiguration.spatialCount e.source 0 (feedbackEnvironmentFirstTime e).toReal = 1 := by exact_mod_cast hs
    have ht' : LocalConfiguration.spatialCount e.target 0 (feedbackEnvironmentFirstTime e).toReal = 0 := by exact_mod_cast ht
    simp [hs', ht']

/-- The current read from an environment commutes with its actual reroot action. -/
theorem feedbackEnvironmentCurrent_reroot (e : FeedbackEnvironment) (a x : ℝ) :
    feedbackEnvironmentCurrent (FeedbackEnvironment.reroot a e) x =
      feedbackEnvironmentCurrent e (x + a) := by
  change (e.path.rootCurrent + e.currentIncrement 0 a) +
      (FeedbackEnvironment.reroot a e).currentIncrement 0 x =
    e.path.rootCurrent + e.currentIncrement 0 (x + a)
  rw [FeedbackEnvironment.currentIncrement_reroot, zero_add, add_assoc,
    e.currentIncrement_add 0 a (x + a)]

/-- The two-color readout of a rerooted environment is the actual reroot of each color. -/
theorem feedbackEnvironmentTwoColor_reroot (e : FeedbackEnvironment) (a : ℝ) (b : Bool) :
    feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e) b =
      LocalConfiguration.reroot a (feedbackEnvironmentTwoColor e b) := by
  cases b <;> rfl

/-- Actual time simplicity is preserved by the physical rerooting action. -/
theorem feedbackEnvironment_isTimeSimple_reroot
    (e : FeedbackEnvironment)
    (he : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) (a : ℝ) :
    LocalConfiguration.IsTimeSimple
      (feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e)) := by
  constructor
  · rintro ⟨b, x, u⟩ hp
    simp only [feedbackEnvironmentTwoColor_reroot, LocalConfiguration.reroot,
      LocalConfiguration.multiplicity_translate, sub_neg_eq_add] at hp ⊢
    exact he.1 (b, (x + a, u)) hp
  · rintro ⟨b, x, u⟩ ⟨c, y, v⟩ hp hq hxy
    simp only [feedbackEnvironmentTwoColor_reroot, LocalConfiguration.reroot,
      LocalConfiguration.multiplicity_translate, sub_neg_eq_add] at hp hq
    have h := he.2 (b, (x + a, u)) (c, (y + a, v)) hp hq (by simpa using hxy)
    have hb : b = c := congrArg Prod.fst h
    have hx : x + a = y + a := congrArg (fun z : Bool × MatchingPoint ↦ z.2.1) h
    have hu : u = v := congrArg (fun z : Bool × MatchingPoint ↦ z.2.2) h
    exact Prod.ext hb (Prod.ext (by linarith) hu)

private theorem integrableOn_mark_window
    (c : LocalConfiguration matchingPointBase) (ψ : UnitMark →ᵇ ℝ) (a t : ℝ) :
    IntegrableOn (fun p : MatchingPoint ↦ ψ p.2) (LocalConfiguration.spatialIoc a t)
      (LocalConfiguration.countingMeasure c) := by
  let : IsFiniteMeasure ((LocalConfiguration.countingMeasure c).restrict
      (LocalConfiguration.spatialIoc a t)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      LocalConfiguration.countingMeasure_lt_top_of_isBounded c
        (LocalConfiguration.isBounded_spatialIoc a t)⟩
  exact Integrable.of_bound
    (ψ.continuous.measurable.comp measurable_snd).aestronglyMeasurable ‖ψ‖
    (Eventually.of_forall fun p ↦ ψ.norm_coe_le_norm p.2)

/-- Rerooting moves the observation window and retains the original geometric mark. -/
theorem firstEventTestCount_feedbackEnvironment_reroot
    (e : FeedbackEnvironment) (a t : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e)) b ψ t =
    ∫ p in LocalConfiguration.spatialIoc a (t + a), ψ p.2
      ∂LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b) := by
  have hm : Measurable (fun p : MatchingPoint ↦ ψ p.2) :=
    ψ.continuous.measurable.comp measurable_snd
  unfold LocalConfiguration.firstEventTestCount
  rw [feedbackEnvironmentTwoColor_reroot, LocalConfiguration.countingMeasure_reroot,
    setIntegral_map (LocalConfiguration.measurableSet_spatialIoc 0 t)
      hm.aestronglyMeasurable
      (Configuration.pointTranslation (-a)).measurable.aemeasurable]
  have hset : Configuration.pointTranslation (-a) ⁻¹' LocalConfiguration.spatialIoc 0 t =
      LocalConfiguration.spatialIoc a (t + a) := by
    ext p
    simp only [mem_preimage, Configuration.pointTranslation_apply,
      LocalConfiguration.spatialIoc, mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hset]
  rfl

/-- The actual weighted count after a nonnegative cut is the increment of its original count. -/
theorem firstEventTestCount_feedbackEnvironment_add
    (e : FeedbackEnvironment) (a t : ℝ≥0) (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b ψ (a + t) -
      LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b ψ a =
    LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot a e)) b ψ t := by
  rw [firstEventTestCount_feedbackEnvironment_reroot]
  have hset : LocalConfiguration.spatialIoc 0 ((a : ℝ) + t) =
      LocalConfiguration.spatialIoc 0 a ∪ LocalConfiguration.spatialIoc a ((t : ℝ) + a) := by
    ext p
    simp only [LocalConfiguration.spatialIoc, mem_preimage, mem_Ioc, mem_union]
    constructor
    · intro hp
      by_cases hpa : p.1 ≤ a
      · exact Or.inl ⟨hp.1, hpa⟩
      · exact Or.inr ⟨lt_of_not_ge hpa, by linarith [hp.2]⟩
    · rintro (hp | hp)
      · exact ⟨hp.1, by linarith [hp.2, t.property]⟩
      · exact ⟨lt_of_le_of_lt a.property hp.1, by linarith [hp.2]⟩
  have hd : Disjoint (LocalConfiguration.spatialIoc 0 (a : ℝ))
      (LocalConfiguration.spatialIoc (a : ℝ) ((t : ℝ) + a)) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.2) hq.1
  unfold LocalConfiguration.firstEventTestCount
  rw [hset, setIntegral_union hd (LocalConfiguration.measurableSet_spatialIoc _ _)
    (integrableOn_mark_window _ ψ _ _) (integrableOn_mark_window _ ψ _ _)]
  ring

/-- The original compensator increment is exactly the compensator of the actual rerooted
configuration; no conditional-law or martingale assumption enters this identity. -/
theorem feedbackEnvironmentMarkedCompensator_add
    (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    (e : FeedbackEnvironment) (a t : ℝ≥0) :
    feedbackEnvironmentMarkedCompensator lam b ψ (a + t) e -
      feedbackEnvironmentMarkedCompensator lam b ψ a e =
    feedbackEnvironmentMarkedCompensator lam b ψ t (FeedbackEnvironment.reroot a e) := by
  have hcount := firstEventTestCount_feedbackEnvironment_add e a t b ψ
  have hshift : (∫ s in 0..(t : ℝ), feedbackEnvironmentMarkRate lam b ψ
      (feedbackEnvironmentCurrent (FeedbackEnvironment.reroot a e) s)) =
      ∫ s in (a : ℝ)..((a : ℝ) + t), feedbackEnvironmentMarkRate lam b ψ
        (feedbackEnvironmentCurrent e s) := by
    simp_rw [feedbackEnvironmentCurrent_reroot]
    simpa only [zero_add, add_zero, add_comm] using intervalIntegral.integral_comp_add_right
      (fun s ↦ feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent e s)) (a : ℝ)
      (a := 0) (b := (t : ℝ))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_feedbackEnvironmentMarkRate lam b ψ e 0 a)
    (intervalIntegrable_feedbackEnvironmentMarkRate lam b ψ e a ((a : ℝ) + t))
  simp only [feedbackEnvironmentMarkedCompensator, NNReal.coe_add, hshift]
  linarith [hcount]

/-- Two-color next-current tests have the same actual restart identity. -/
theorem feedbackEnvironmentJumpCompensator_add
    (lam : ℝ) (k : ℤ) (ψ : (UnitMark × ℤ) →ᵇ ℝ)
    (e : FeedbackEnvironment) (a t : ℝ≥0) :
    feedbackEnvironmentJumpCompensator lam k ψ (a + t) e -
      feedbackEnvironmentJumpCompensator lam k ψ a e =
    feedbackEnvironmentJumpCompensator lam k ψ t (FeedbackEnvironment.reroot a e) := by
  have hs := feedbackEnvironmentMarkedCompensator_add lam true
    (feedbackNextCurrentTest k ψ true) e a t
  have ht := feedbackEnvironmentMarkedCompensator_add lam false
    (feedbackNextCurrentTest k ψ false) e a t
  unfold feedbackEnvironmentJumpCompensator
  linarith

/-- After a genuine spatial cut, the stopped increment of the original next-current test is
the actual first-jump test of the rerooted configuration. -/
theorem feedbackEnvironmentJumpCompensator_stopped_after
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (a t : ℝ≥0) (k : ℤ) (hk : feedbackEnvironmentCurrent e a = k)
    (ψ : (UnitMark × ℤ) →ᵇ ℝ) :
    feedbackEnvironmentJumpCompensator lam k ψ
      (a + CountingProcess.cappedStoppingValue t
        (fun _ : Unit ↦ feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot a e)) ()) e -
      feedbackEnvironmentJumpCompensator lam k ψ a e =
    firstJumpTestCompensator (totalJumpRate lam k) (feedbackMarkedJumpKernel lam k)
      feedbackEnvironmentFirstTime feedbackEnvironmentFirstJump ψ t
      (FeedbackEnvironment.reroot a e) := by
  rw [feedbackEnvironmentJumpCompensator_add]
  exact feedbackEnvironmentJumpCompensator_stopped hlam0 hlam
    (FeedbackEnvironment.reroot a e) (feedbackEnvironment_isTimeSimple_reroot e hsimple a)
    k hk ψ t

end OTSelector.Limit
