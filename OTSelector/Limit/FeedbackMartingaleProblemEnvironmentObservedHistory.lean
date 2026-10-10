import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentHistory
import Mathlib.Topology.Order.ProjIcc

/-!
# Recovering the actual marked history from revealed counts

Right-continuous adapted real processes can be evaluated measurably in the stopping-time
sigma algebra. Constant-one and coordinate mark tests then recover the actual marked prefix
from revealed counts. An explicit measurable version also handles configurations that fail
time simplicity; it agrees with the actual prefix wherever time simplicity holds.
-/

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped NNReal ENNReal BoundedContinuousFunction Topology

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 300000

namespace OTSelector.Limit

open PointProcess CountingProcess

/-- Evaluation of a right-continuous adapted real process is measurable at its stopping time.
The convention at infinity is evaluation at zero. -/
theorem measurable_eval_stopping_of_rightContinuous
    {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : StronglyAdapted ℱ M)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime ℱ τ)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t) :
    Measurable[hτ.measurableSpace] (fun ω ↦ M (τ ω).toNNReal ω) := by
  have hcap := stronglyAdapted_cappedStoppingValue_of_rightContinuous hM hτ hRight
  have heq (ω : Ω) (t : ℝ≥0) (h : τ ω ≤ (t : ℝ≥0∞)) :
      cappedStoppingValue t τ ω = (τ ω).toNNReal := by
    apply ENNReal.coe_injective
    have hc := coe_cappedStoppingValue t τ ω
    change (cappedStoppingValue t τ ω : ℝ≥0∞) = min (τ ω) (t : ℝ≥0∞) at hc
    rw [hc, min_eq_left h, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top h)]
  intro B hB
  have hlocal (t : ℝ≥0) : MeasurableSet[ℱ t]
      ((fun ω ↦ M (τ ω).toNNReal ω) ⁻¹' B ∩ {ω | τ ω ≤ (t : ℝ≥0∞)}) := by
    have he : ((fun ω ↦ M (τ ω).toNNReal ω) ⁻¹' B ∩ {ω | τ ω ≤ (t : ℝ≥0∞)}) =
        ((fun ω ↦ M (cappedStoppingValue t τ ω) ω) ⁻¹' B ∩ {ω | τ ω ≤ (t : ℝ≥0∞)}) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor <;> rintro ⟨hω, ht⟩ <;> exact ⟨by simpa only [heq ω t ht] using hω, ht⟩
    rw [he]
    exact ((hcap t).measurable hB).inter (hτ t)
  refine ⟨?_, hlocal⟩
  have hsplit : (fun ω ↦ M (τ ω).toNNReal ω) ⁻¹' B =
      (⋃ n : ℕ, (fun ω ↦ M (τ ω).toNNReal ω) ⁻¹' B ∩
        {ω | τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)}) ∪
      ((M 0) ⁻¹' B ∩ {ω | τ ω = ∞}) := by
    ext ω
    simp only [mem_union, mem_iUnion, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · intro hω
      by_cases ht : τ ω = ∞
      · exact Or.inr ⟨by simpa [ht] using hω, ht⟩
      · obtain ⟨n, hn⟩ := exists_nat_ge (τ ω).toNNReal
        left
        refine ⟨n, hω, ?_⟩
        rw [← ENNReal.coe_toNNReal ht]
        exact_mod_cast hn
    · rintro (⟨n, hω, _⟩ | ⟨hω, ht⟩)
      · exact hω
      · simpa [ht] using hω
  rw [hsplit]
  exact (MeasurableSet.iUnion fun n : ℕ ↦ (le_iSup ℱ (n : ℝ≥0)) _ (hlocal n)).union
    (((hM 0).measurable.mono (le_iSup ℱ 0) le_rfl hB).inter hτ.measurableSet_eq_top')

/-- The continuous coordinate test on the physical mark interval. -/
noncomputable def feedbackObservedMarkTest : UnitMark →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨Subtype.val, continuous_subtype_val⟩

private theorem coe_feedbackObserved_one :
    (⇑(BoundedContinuousFunction.const UnitMark (1 : ℝ))) = (fun _ : UnitMark ↦ (1 : ℝ)) := rfl

/-- Reading a fixed mark test at an actual chronological cut. -/
noncomputable def feedbackEnvironmentObservedCount (e : FeedbackEnvironment)
    (n : ℕ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) : ℝ :=
  LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b ψ
    (feedbackEnvironmentEventTime e n).toReal

/-- The current read solely from the root current and revealed constant-one counts. -/
noncomputable def feedbackEnvironmentObservedCurrent (e : FeedbackEnvironment) (n : ℕ) : ℤ :=
  e.path.rootCurrent + Int.floor
    (feedbackEnvironmentObservedCount e n true (BoundedContinuousFunction.const UnitMark 1) -
      feedbackEnvironmentObservedCount e n false (BoundedContinuousFunction.const UnitMark 1))

theorem feedbackEnvironmentObservedCurrent_eq (e : FeedbackEnvironment) (n : ℕ) :
    feedbackEnvironmentObservedCurrent e n =
      feedbackEnvironmentCurrent e (feedbackEnvironmentEventTime e n).toReal := by
  simp only [feedbackEnvironmentObservedCurrent, feedbackEnvironmentObservedCount,
    coe_feedbackObserved_one, LocalConfiguration.firstEventTestCount_one,
    feedbackEnvironmentTwoColor, ite_true, Bool.false_eq_true, ite_false,
    ← Int.cast_sub, Int.floor_intCast]
  simp only [feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement,
    LocalConfiguration.orientedCount,
    LocalConfiguration.spatialCount_eq_zero_of_le _ ENNReal.toReal_nonneg, sub_zero]

/-- The total coordinate-weight increment across one reached event is its physical mark. -/
theorem feedbackEnvironmentObservedCount_increment
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) (n : ℕ)
    (hn : feedbackEnvironmentEventTime e (n + 1) ≠ ∞)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    feedbackEnvironmentObservedCount e (n + 1) b ψ - feedbackEnvironmentObservedCount e n b ψ =
      if (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 = b
        then ψ (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).2.2 else 0 := by
  have hfinite := feedbackEnvironmentAfterEvent_firstTime_ne_top e n hn
  have hsimple' := feedbackEnvironment_isTimeSimple_reroot e hsimple
    (feedbackEnvironmentEventTime e n).toReal
  have hread := LocalConfiguration.firstEventTestCount_min
    (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n)) hsimple' b ψ
    (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal
  have ht : ENNReal.ofReal (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal =
      feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n) := ENNReal.ofReal_toReal hfinite
  change LocalConfiguration.firstEventTestCount
    (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n)) b ψ
    (min (ENNReal.ofReal (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal)
      (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n))).toReal = _ at hread
  rw [ht, min_self] at hread
  have hadd := firstEventTestCount_feedbackEnvironment_add e
    (feedbackEnvironmentEventTime e n).toNNReal
    (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toNNReal b ψ
  change LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b ψ
      ((feedbackEnvironmentEventTime e n).toReal +
        (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal) -
    feedbackEnvironmentObservedCount e n b ψ =
    LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n)) b ψ
      (feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n)).toReal at hadd
  rw [← feedbackEnvironmentEventTime_succ_toReal e n hn] at hadd
  change feedbackEnvironmentObservedCount e (n + 1) b ψ -
    feedbackEnvironmentObservedCount e n b ψ = _ at hadd
  rw [hadd, hread]
  simp only [feedbackEnvironmentFirstTime, feedbackEnvironmentFirstEvent, le_refl, true_and]
  split
  · rename_i hb
    exact (ite_eq_left hb).symm
  · rename_i hb
    exact (ite_eq_right hb).symm

/-- A total version of the chronological path reconstructed from revealed tests. Clipping the
reconstructed mark merely gives a total map on configurations without time simplicity. -/
noncomputable def feedbackEnvironmentObservedPath (e : FeedbackEnvironment) : FeedbackCellPath
  | 0 => feedbackMarkedVirtual e.path.rootCurrent
  | n + 1 => if feedbackEnvironmentEventTime e n = ∞ then feedbackMarkedVirtual e.path.rootCurrent
    else if feedbackEnvironmentEventTime e (n + 1) = ∞ then
      (0, ⟨0, by simp⟩, feedbackEnvironmentObservedCurrent e n - 1)
    else
      ((feedbackEnvironmentEventTime e (n + 1)).toReal - (feedbackEnvironmentEventTime e n).toReal,
       Set.projIcc 0 1 zero_le_one
         ((feedbackEnvironmentObservedCount e (n + 1) true feedbackObservedMarkTest -
             feedbackEnvironmentObservedCount e n true feedbackObservedMarkTest) +
           (feedbackEnvironmentObservedCount e (n + 1) false feedbackObservedMarkTest -
             feedbackEnvironmentObservedCount e n false feedbackObservedMarkTest)),
       feedbackEnvironmentObservedCurrent e (n + 1))

theorem feedbackEnvironmentObservedPath_eq
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e)) :
    feedbackEnvironmentObservedPath e = feedbackEnvironmentFuturePath e := by
  funext i
  cases i with
  | zero => rfl
  | succ n =>
    by_cases hp : feedbackEnvironmentEventTime e n = ∞
    · simp only [feedbackEnvironmentObservedPath, feedbackEnvironmentFuturePath, hp, ite_true]
    rw [feedbackEnvironmentFuturePath_succ e n hp]
    by_cases hn : feedbackEnvironmentEventTime e (n + 1) = ∞
    · have hf : feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n) = ∞ := by
        have hadd := feedbackEnvironmentEventTime_succ_eq_add e n hp
        have hs : feedbackEnvironmentEventTime e n +
            feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent e n) = ∞ := hadd.symm.trans hn
        exact (ENNReal.add_eq_top.mp hs).resolve_left hp
      have hJ : feedbackEnvironmentFirstJump (feedbackEnvironmentAfterEvent e n) =
          (⟨0, by simp⟩, feedbackEnvironmentCurrent e (feedbackEnvironmentEventTime e n).toReal - 1) := by
        simp only [feedbackEnvironmentFirstJump, feedbackEnvironmentFirstEvent,
          LocalConfiguration.firstPositiveEvent,
          show LocalConfiguration.firstPositiveTime
            (feedbackEnvironmentTwoColor (feedbackEnvironmentAfterEvent e n)) = ∞ from hf,
          ite_true]
        rfl
      simp only [feedbackEnvironmentObservedPath, hp, hn, ite_false, ite_true,
        hf, ENNReal.toReal_top, hJ, feedbackEnvironmentObservedCurrent_eq]
    · have hmark :
          (feedbackEnvironmentObservedCount e (n + 1) true feedbackObservedMarkTest -
              feedbackEnvironmentObservedCount e n true feedbackObservedMarkTest) +
            (feedbackEnvironmentObservedCount e (n + 1) false feedbackObservedMarkTest -
              feedbackEnvironmentObservedCount e n false feedbackObservedMarkTest) =
          ((feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).2.2 : ℝ) := by
        rw [feedbackEnvironmentObservedCount_increment e hsimple n hn,
          feedbackEnvironmentObservedCount_increment e hsimple n hn]
        cases hb : (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 <;>
          simp [feedbackObservedMarkTest]
      have hcurrent := feedbackEnvironmentFuturePath_current_succ e hsimple n hn
      rw [feedbackEnvironmentFuturePath_succ e n hp] at hcurrent
      simp only [feedbackEnvironmentObservedPath, hp, hn, ite_false]
      apply Prod.ext
      · rw [feedbackEnvironmentEventTime_succ_toReal e n hn]
        simp
      · apply Prod.ext
        · rw [hmark, Set.projIcc_of_mem zero_le_one
            (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).2.2.property]
          rfl
        · exact (feedbackEnvironmentObservedCurrent_eq e (n + 1)).trans hcurrent.symm


section Adapted

variable {Ω : Type*} [MeasurableSpace Ω]
  (e : Ω → FeedbackEnvironment) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (hroot : Measurable[ℱ 0] (fun ω ↦ (e ω).path.rootCurrent))
  (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (e ω)) b ψ t))

include htest

theorem feedbackEnvironmentEventCount_adapted_of_tests (t : ℝ≥0) :
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.spatialCount (e ω).source 0 t +
      LocalConfiguration.spatialCount (e ω).target 0 t) := by
  let : MeasurableSpace Ω := ℱ t
  have hs := htest true (BoundedContinuousFunction.const UnitMark 1) t
  have ht := htest false (BoundedContinuousFunction.const UnitMark 1) t
  have hm := (hs.add ht).floor
  convert hm using 1
  funext ω
  simp only [Pi.add_apply, coe_feedbackObserved_one,
    LocalConfiguration.firstEventTestCount_one, feedbackEnvironmentTwoColor,
    ite_true, Bool.false_eq_true, ite_false, ← Int.cast_add, Int.floor_intCast]

/-- The sigma algebra at actual event `n`, derived from adapted revealed tests. -/
@[instance_reducible]
noncomputable def feedbackEnvironmentEventHistory (n : ℕ) : MeasurableSpace Ω :=
  (feedbackEnvironmentEventTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) n).measurableSpace

theorem feedbackEnvironmentEventHistory_mono {i n : ℕ} (hin : i ≤ n) :
    feedbackEnvironmentEventHistory e ℱ htest i ≤ feedbackEnvironmentEventHistory e ℱ htest n :=
  IsStoppingTime.measurableSpace_mono _ _
    (fun ω ↦ monotone_feedbackEnvironmentEventTime (e ω) hin)

theorem measurable_feedbackEnvironmentEventTime_history {i n : ℕ} (hin : i ≤ n) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentEventTime (e ω) i) := by
  have hstop := feedbackEnvironmentEventTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) i
  exact hstop.measurable.mono (feedbackEnvironmentEventHistory_mono e ℱ htest hin) le_rfl

theorem measurable_feedbackEnvironmentObservedCount_history {i n : ℕ} (hin : i ≤ n)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentObservedCount (e ω) i b ψ) := by
  have hstop := feedbackEnvironmentEventTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) i
  have hm := measurable_eval_stopping_of_rightContinuous
    (fun t ↦ (htest b ψ t).stronglyMeasurable) hstop
    (fun ω t ↦ LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal
      (feedbackEnvironmentTwoColor (e ω)) b ψ t)
  exact hm.mono (feedbackEnvironmentEventHistory_mono e ℱ htest hin) le_rfl

include hroot in
private theorem measurable_root_history (n : ℕ) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ (e ω).path.rootCurrent) := by
  apply hroot.mono _ le_rfl
  have hstop := feedbackEnvironmentEventTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) n
  exact hstop.le_measurableSpace_of_const_le (i := 0) (fun _ ↦ by
    change (0 : ℝ≥0∞) ≤ _
    exact bot_le)

include hroot in
theorem measurable_feedbackEnvironmentObservedCurrent_history {i n : ℕ} (hin : i ≤ n) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentObservedCurrent (e ω) i) := by
  have hr := measurable_root_history e ℱ hroot htest n
  have hs := measurable_feedbackEnvironmentObservedCount_history e ℱ htest hin true
    (BoundedContinuousFunction.const UnitMark 1)
  have ht := measurable_feedbackEnvironmentObservedCount_history e ℱ htest hin false
    (BoundedContinuousFunction.const UnitMark 1)
  let : MeasurableSpace Ω := feedbackEnvironmentEventHistory e ℱ htest n
  exact hr.add ((hs.sub ht).floor)

include hroot in
theorem measurable_feedbackEnvironmentObservedPath_history {i n : ℕ} (hin : i ≤ n) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentObservedPath (e ω) i) := by
  classical
  have hr := measurable_root_history e ℱ hroot htest n
  have htime (j : ℕ) (hj : j ≤ n) :=
    measurable_feedbackEnvironmentEventTime_history e ℱ htest hj
  have hcurrent (j : ℕ) (hj : j ≤ n) :=
    measurable_feedbackEnvironmentObservedCurrent_history e ℱ hroot htest hj
  have hcount (j : ℕ) (hj : j ≤ n) (b : Bool) :=
    measurable_feedbackEnvironmentObservedCount_history e ℱ htest hj b feedbackObservedMarkTest
  let : MeasurableSpace Ω := feedbackEnvironmentEventHistory e ℱ htest n
  have hvirt := (measurable_of_countable feedbackMarkedVirtual).comp hr
  cases i with
  | zero => exact hvirt
  | succ i =>
    have hi : i ≤ n := (Nat.le_succ i).trans hin
    have hti := htime i hi
    have htj := htime (i + 1) hin
    have hci := hcurrent i hi
    have hcj := hcurrent (i + 1) hin
    have hinc (b : Bool) := (hcount (i + 1) hin b).sub (hcount i hi b)
    have hproj : Measurable (Set.projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc.measurable
    have hmark := hproj.comp ((hinc true).add (hinc false))
    exact hvirt.ite (measurableSet_eq_fun hti measurable_const)
      ((measurable_const.prodMk (measurable_const.prodMk (hci.sub measurable_const))).ite
        (measurableSet_eq_fun htj measurable_const)
        ((htj.ennreal_toReal.sub hti.ennreal_toReal).prodMk (hmark.prodMk hcj)))

/-- The explicit observed prefix, on the same finite-history carrier as the actual path. -/
noncomputable def feedbackEnvironmentObservedPrefix (n : ℕ) (e : FeedbackEnvironment) :
    (i : Finset.Iic n) → FeedbackMarkedStep :=
  frestrictLe n (feedbackEnvironmentObservedPath e)

include hroot in
theorem measurable_feedbackEnvironmentObservedPrefix (n : ℕ) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentObservedPrefix n (e ω)) := by
  have hc (i : Finset.Iic n) := measurable_feedbackEnvironmentObservedPath_history
    e ℱ hroot htest (Finset.mem_Iic.mp i.property)
  let : MeasurableSpace Ω := feedbackEnvironmentEventHistory e ℱ htest n
  apply measurable_pi_lambda
  intro i
  exact hc i

include hroot in
theorem measurable_feedbackEnvironmentFuturePrefix (n : ℕ)
    (hsimple : ∀ ω, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω))) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω))) := by
  have heq : (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω))) =
      (fun ω ↦ feedbackEnvironmentObservedPrefix n (e ω)) := by
    funext ω
    rw [feedbackEnvironmentObservedPrefix, feedbackEnvironmentObservedPath_eq (e ω) (hsimple ω)]
  rw [heq]
  exact measurable_feedbackEnvironmentObservedPrefix e ℱ hroot htest n

include hroot in
/-- Under almost-everywhere simplicity, this supplies an actual stopped-history measurable
version with ambient-measure almost-everywhere equality. No completion of the filtration is
implicitly assumed. -/
theorem feedbackEnvironmentFuturePrefix_measurable_version
    (μ : Measure Ω) (n : ℕ)
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω))) :
    Measurable[feedbackEnvironmentEventHistory e ℱ htest n]
      (fun ω ↦ feedbackEnvironmentObservedPrefix n (e ω)) ∧
    (fun ω ↦ feedbackEnvironmentObservedPrefix n (e ω)) =ᵐ[μ]
      (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω))) := by
  refine ⟨measurable_feedbackEnvironmentObservedPrefix e ℱ hroot htest n, ?_⟩
  filter_upwards [hsimple] with ω hω
  simp only [feedbackEnvironmentObservedPrefix, feedbackEnvironmentObservedPath_eq (e ω) hω]

end Adapted
/-- Every reached chronological event increases the actual aggregate count by exactly one. -/
theorem feedbackEnvironmentEventCount_at_eventTime
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (n : ℕ) (hn : feedbackEnvironmentEventTime e n ≠ ∞) :
    feedbackEnvironmentEventCount e (feedbackEnvironmentEventTime e n).toNNReal = (n : ℤ) := by
  induction n with
  | zero => simp [feedbackEnvironmentEventCount]
  | succ n ih =>
    have hi := ih (feedbackEnvironmentEventTime_ne_top_of_le e (Nat.le_succ n) hn)
    have hinc (b : Bool) := feedbackEnvironmentObservedCount_increment e hsimple n hn b
      (BoundedContinuousFunction.const UnitMark 1)
    have hs := hinc true
    have ht := hinc false
    simp only [feedbackEnvironmentObservedCount,
      LocalConfiguration.firstEventTestCount_one, feedbackEnvironmentTwoColor,
      ite_true, Bool.false_eq_true, ite_false, BoundedContinuousFunction.const_apply] at hs ht
    have hi' : (feedbackEnvironmentEventCount e (feedbackEnvironmentEventTime e n).toNNReal : ℝ) =
        (n : ℝ) := by exact_mod_cast hi
    apply Int.cast_injective (α := ℝ)
    change ((LocalConfiguration.spatialCount e.source 0 (feedbackEnvironmentEventTime e (n + 1)).toReal +
      LocalConfiguration.spatialCount e.target 0 (feedbackEnvironmentEventTime e (n + 1)).toReal : ℤ) : ℝ) =
        ((n + 1 : ℕ) : ℤ)
    change ((LocalConfiguration.spatialCount e.source 0 (feedbackEnvironmentEventTime e n).toReal +
      LocalConfiguration.spatialCount e.target 0 (feedbackEnvironmentEventTime e n).toReal : ℤ) : ℝ) =
        (n : ℝ) at hi'
    push_cast at hi' ⊢
    cases hb : (feedbackEnvironmentFirstEvent (feedbackEnvironmentAfterEvent e n)).1 <;>
      simp only [hb, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] at hs ht <;>
      linarith

private theorem monotone_feedbackEnvironmentEventCount (e : FeedbackEnvironment) :
    Monotone (feedbackEnvironmentEventCount e) := by
  intro a b hab
  have hs := LocalConfiguration.spatialCount_add e.source a.property
    (show (a : ℝ) ≤ b from hab)
  have ht := LocalConfiguration.spatialCount_add e.target a.property
    (show (a : ℝ) ≤ b from hab)
  unfold feedbackEnvironmentEventCount
  rw [hs, ht]
  exact add_le_add
    (le_add_of_nonneg_right (LocalConfiguration.spatialCount_nonneg e.source a b))
    (le_add_of_nonneg_right (LocalConfiguration.spatialCount_nonneg e.target a b))

/-- A locally finite, time-simple actual configuration cannot contain infinitely many
chronological events in a bounded window. If every event is reached, its times tend to infinity. -/
theorem tendsto_feedbackEnvironmentEventTime_toReal_atTop
    (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (hfinite : ∀ n, feedbackEnvironmentEventTime e n ≠ ∞) :
    Tendsto (fun n ↦ (feedbackEnvironmentEventTime e n).toReal) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  let T : ℝ≥0 := Real.toNNReal b
  obtain ⟨N, hN⟩ := exists_nat_gt (feedbackEnvironmentEventCount e T)
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra hnb
  have htime : (feedbackEnvironmentEventTime e n).toNNReal ≤ T := by
    change (feedbackEnvironmentEventTime e n).toReal ≤ (T : ℝ)
    exact (lt_of_not_ge hnb).le.trans (Real.le_coe_toNNReal b)
  have hcount := monotone_feedbackEnvironmentEventCount e htime
  rw [feedbackEnvironmentEventCount_at_eventTime e hsimple n (hfinite n)] at hcount
  have hn' : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  omega

end OTSelector.Limit
