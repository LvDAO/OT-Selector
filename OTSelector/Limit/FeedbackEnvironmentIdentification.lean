import OTSelector.Limit.FeedbackCellConcatenation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Recovering the actual feedback current from the marked environment

Partial-cell point counts recover the true finite path increments. Balanced completed cells
then identify the current at every spatial cut with the source-minus-target oriented count.
The graph therefore solves the feedback integral equation with that observable current.
-/

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators Classical ENNReal Interval

set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

/-- Counting a partial physical cell retains exactly the actual jumps before the cut. -/
theorem countingMeasure_feedbackConcatenatedPoints_partialCell {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (direction k : ℤ) {x : ℝ}
    (hx : x ≤ feedbackCellRoot w (k + 1)) :
    LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w)
      (LocalConfiguration.spatialIoc (feedbackCellRoot w k) x) =
      (((Finset.range (feedbackMarkedFirstReturnIndex (w k))).filter
        (fun n ↦ (w k (n + 1)).2.2 - (w k n).2.2 = direction ∧
          feedbackCellClock (w k) (n + 1) ≤ x - feedbackCellRoot w k)).card : ℝ≥0∞) := by
  let s := LocalConfiguration.spatialIoc (feedbackCellRoot w k) x
  have hs : MeasurableSet s := LocalConfiguration.measurableSet_spatialIoc _ _
  rw [countingMeasure_feedbackConcatenatedPoints, Measure.sum_apply _ hs]
  let t := (Finset.range (feedbackMarkedFirstReturnIndex (w k))).image (fun n ↦ (k, n))
  rw [tsum_eq_sum (s := t)]
  · rw [Finset.sum_image]
    · have hterm (n : ℕ) (hn : n ∈ Finset.range (feedbackMarkedFirstReturnIndex (w k))) :
          (if feedbackCellEventActive w direction (k, n) then
            Measure.dirac (feedbackCellEventPoint w (k, n)) else 0) s =
          if (w k (n + 1)).2.2 - (w k n).2.2 = direction ∧
            feedbackCellClock (w k) (n + 1) ≤ x - feedbackCellRoot w k
          then (1 : ℝ≥0∞) else 0 := by
        by_cases hd : (w k (n + 1)).2.2 - (w k n).2.2 = direction
        · have hi : feedbackCellEventActive w direction (k, n) :=
            ⟨hw, Finset.mem_range.mp hn, hd⟩
          have hp : feedbackCellEventPoint w (k, n) ∈ s ↔
              feedbackCellClock (w k) (n + 1) ≤ x - feedbackCellRoot w k := by
            have hpos := (feedbackCellEventPoint_mem_cell hi).1
            change (_ < _ ∧ _ ≤ _) ↔ _
            simp only [feedbackCellEventPoint] at hpos ⊢
            constructor
            · intro h; linarith [h.2]
            · intro h; exact ⟨hpos, by linarith⟩
          simp only [hi, ↓reduceIte, Measure.dirac_apply' _ hs, Set.indicator_apply,
            Pi.one_apply, hp, hd, true_and]
        · have hi : ¬feedbackCellEventActive w direction (k, n) := fun h ↦ hd h.2.2
          simp [hi, hd]
      rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    · intro a ha b hb hab
      exact (Prod.mk.inj hab).2
  · intro i hi
    by_cases ha : feedbackCellEventActive w direction i
    · rw [ite_eq_left ha, Measure.dirac_apply' _ hs]
      apply Set.indicator_of_notMem
      intro hp
      have hik := (feedbackCellEventPoint_mem_Ioc_roots_iff ha k).mp ⟨hp.1, hp.2.trans hx⟩
      apply hi
      exact Finset.mem_image.mpr ⟨i.2, Finset.mem_range.mpr (by simpa [hik] using ha.2.1),
        by ext <;> simp [hik]⟩
    · simp [ha]

/-- The integer count on a partial cell is the corresponding finite arrival count. -/
theorem spatialCount_feedbackConcatenatedPoints_partialCell {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (direction k : ℤ) {x : ℝ}
    (hx : x ≤ feedbackCellRoot w (k + 1)) :
    LocalConfiguration.spatialCount (feedbackConcatenatedPoints direction w)
      (feedbackCellRoot w k) x =
      (((Finset.range (feedbackMarkedFirstReturnIndex (w k))).filter
        (fun n ↦ (w k (n + 1)).2.2 - (w k n).2.2 = direction ∧
          feedbackCellClock (w k) (n + 1) ≤ x - feedbackCellRoot w k)).card : ℤ) := by
  simp only [LocalConfiguration.spatialCount, Measure.real,
    countingMeasure_feedbackConcatenatedPoints_partialCell hw direction k hx,
    ENNReal.toReal_natCast, Int.floor_natCast]

/-- On any cell the observed net count equals the finite path current, including cut endpoints. -/
theorem currentIncrement_feedbackConcatenatedEnvironment_partialCell (lam : ℝ)
    {w : FeedbackCellSequence} (hw : feedbackCellConfigurationGood w) (k : ℤ) {x : ℝ}
    (hlo : feedbackCellRoot w k ≤ x) (hhi : x ≤ feedbackCellRoot w (k + 1))
    (hneigh : ∀ i, (w k (i + 1)).2.2 = (w k i).2.2 + 1 ∨
      (w k (i + 1)).2.2 = (w k i).2.2 - 1) :
    (feedbackConcatenatedEnvironment lam w).currentIncrement (feedbackCellRoot w k) x =
      feedbackCellCurrent (w k) (x - feedbackCellRoot w k) := by
  simp only [FeedbackEnvironment.currentIncrement, feedbackConcatenatedEnvironment,
    LocalConfiguration.orientedCount, LocalConfiguration.spatialCount_eq_zero_of_le _ hlo,
    sub_zero, feedbackConcatenatedSource, feedbackConcatenatedTarget,
    spatialCount_feedbackConcatenatedPoints_partialCell hw _ k hhi]
  rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
  unfold feedbackCellCurrent
  apply Finset.sum_congr rfl
  intro i hi
  rcases hneigh i with h | h
  · have hd : (w k (i + 1)).2.2 - (w k i).2.2 = 1 := by omega
    by_cases ht : feedbackCellClock (w k) (i + 1) ≤ x - feedbackCellRoot w k <;>
      simp [hd, ht, feedbackCellJump]
  · have hd : (w k (i + 1)).2.2 - (w k i).2.2 = -1 := by omega
    by_cases ht : feedbackCellClock (w k) (i + 1) ≤ x - feedbackCellRoot w k <;>
      simp [hd, ht, feedbackCellJump]

/-- Every completed return cell has zero net count, so all return roots carry zero current. -/
theorem currentIncrement_feedbackConcatenatedEnvironment_root (lam : ℝ)
    {w : FeedbackCellSequence} (hw : feedbackCellConfigurationGood w)
    (hbal : ∀ j, (feedbackCellSourceJumps (w j)).card = (feedbackCellTargetJumps (w j)).card)
    (k : ℤ) :
    (feedbackConcatenatedEnvironment lam w).currentIncrement 0 (feedbackCellRoot w k) = 0 := by
  let e := feedbackConcatenatedEnvironment lam w
  have hs (j : ℤ) : e.currentIncrement (feedbackCellRoot w j)
      (feedbackCellRoot w (j + 1)) = 0 :=
    orientedCount_feedbackConcatenated_cell_balanced hw j (hbal j)
  have ha (j : ℤ) := e.currentIncrement_add 0 (feedbackCellRoot w j)
    (feedbackCellRoot w (j + 1))
  change e.currentIncrement 0 (feedbackCellRoot w k) = 0
  induction k using Int.induction_on with
  | zero => simp [e, feedbackCellRoot_zero, FeedbackEnvironment.currentIncrement]
  | succ n hn => rw [ha, hn, hs, add_zero]
  | pred n hn =>
      have h := ha (-(n : ℤ) - 1)
      have heq : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      rw [hs, heq, hn] at h
      omega

/-- At every spatial cut, the current read from the point configurations is exactly the
current obtained by concatenating the actual finite return paths. -/
theorem currentAt_feedbackConcatenatedEnvironment (lam : ℝ)
    {w : FeedbackCellSequence} (hw : feedbackCellConfigurationGood w)
    (hbal : ∀ j, (feedbackCellSourceJumps (w j)).card = (feedbackCellTargetJumps (w j)).card)
    (hneigh : ∀ j i, (w j (i + 1)).2.2 = (w j i).2.2 + 1 ∨
      (w j (i + 1)).2.2 = (w j i).2.2 - 1) (x : ℝ) :
    FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
      (feedbackConcatenatedEnvironment lam w).path x = feedbackConcatenatedCurrent w x := by
  let k := feedbackCellIndex w x
  have hx := feedbackCellIndex_bounds hw.1 x
  have hadd := (feedbackConcatenatedEnvironment lam w).currentIncrement_add
    0 (feedbackCellRoot w k) x
  rw [currentIncrement_feedbackConcatenatedEnvironment_root lam hw hbal,
    currentIncrement_feedbackConcatenatedEnvironment_partialCell lam hw k hx.1 hx.2.le
      (hneigh k), zero_add] at hadd
  change (0 : ℤ) + (feedbackConcatenatedEnvironment lam w).currentIncrement 0 x = _
  rw [zero_add]
  exact hadd

/-- All cellwise path identities used for the current recovery hold simultaneously under the
actual iid marked cell law. -/
theorem feedbackCellBase_identification_good {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      feedbackCellConfigurationGood w ∧
      (∀ j, (feedbackCellSourceJumps (w j)).card = (feedbackCellTargetJumps (w j)).card) ∧
      (∀ j, (w j 0).2.2 = 0) ∧
      (∀ j i, (w j (i + 1)).2.2 = (w j i).2.2 + 1 ∨
        (w j (i + 1)).2.2 = (w j i).2.2 - 1) := by
  have hc : ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ,
      (feedbackCellSourceJumps (w j)).card = (feedbackCellTargetJumps (w j)).card ∧
      (w j 0).2.2 = 0 ∧
      (∀ i, (w j (i + 1)).2.2 = (w j i).2.2 + 1 ∨
        (w j (i + 1)).2.2 = (w j i).2.2 - 1) := by
    rw [ae_all_iff]
    intro j
    have h := (feedbackCellBase_eval_measurePreserving hlam0 hlam j).quasiMeasurePreserving.ae
      ((feedbackMarkedTrajectory_cell_balanced hlam0 hlam).and
        ((feedbackMarkedTrajectory_initial hlam0 hlam 0).and
          (feedbackMarkedTrajectory_neighbors hlam0 hlam 0)))
    filter_upwards [h] with w hw
    exact ⟨hw.1, by rw [hw.2.1]; rfl, hw.2.2⟩
  filter_upwards [feedbackCellBase_configuration_good hlam0 hlam, hc] with w hw hc
  exact ⟨hw, fun j ↦ (hc j).1, fun j ↦ (hc j).2.1, fun j ↦ (hc j).2.2⟩

/-- Current recovery is simultaneous over every cut, with only the original parameter regime. -/
theorem ae_currentAt_feedbackConcatenatedEnvironment {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ x : ℝ,
      FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
        (feedbackConcatenatedEnvironment lam w).path x = feedbackConcatenatedCurrent w x := by
  filter_upwards [feedbackCellBase_identification_good hlam0 hlam] with w hw x
  exact currentAt_feedbackConcatenatedEnvironment lam hw.1 hw.2.1 hw.2.2.2 x


/-- Every integer cell shift reroots the genuine environment; the current field is included. -/
theorem ae_feedbackConcatenatedEnvironment_shift {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ,
      feedbackConcatenatedEnvironment lam (IIDShift.shift j w) =
        FeedbackEnvironment.reroot (feedbackCellRoot w j) (feedbackConcatenatedEnvironment lam w) := by
  filter_upwards [feedbackCellBase_identification_good hlam0 hlam] with w hw j
  apply FeedbackEnvironment.ext
  · exact feedbackConcatenatedSource_shift w j
  · exact feedbackConcatenatedTarget_shift w j
  · apply FeedbackPath.ext
    · exact feedbackConcatenatedGraphHeight_shift lam hw.1.1 j
    · change (0 : ℤ) = 0 +
        (feedbackConcatenatedEnvironment lam w).currentIncrement 0 (feedbackCellRoot w j)
      rw [currentIncrement_feedbackConcatenatedEnvironment_root lam hw.1 hw.2.1, add_zero]

/-- Current observation commutes with actual spatial rerooting for every environment. -/
theorem currentAt_feedbackEnvironment_reroot (e : FeedbackEnvironment) (a x : ℝ) :
    FeedbackPath.currentAt (FeedbackEnvironment.reroot a e).currentIncrement
      (FeedbackEnvironment.reroot a e).path x =
      FeedbackPath.currentAt e.currentIncrement e.path (x + a) := by
  change (e.path.rootCurrent + e.currentIncrement 0 a) +
    (FeedbackEnvironment.reroot a e).currentIncrement 0 x = _
  rw [FeedbackEnvironment.currentIncrement_reroot, zero_add]
  change (e.path.rootCurrent + e.currentIncrement 0 a) + e.currentIncrement a (x + a) =
    e.path.rootCurrent + e.currentIncrement 0 (x + a)
  rw [e.currentIncrement_add 0 a (x + a), add_assoc]

/-- The actual concatenated velocity is locally integrable on the whole line. -/
theorem locallyIntegrable_feedbackConcatenatedVelocity (lam : ℝ) (w : FeedbackCellSequence) :
    LocallyIntegrable (feedbackConcatenatedVelocity lam w) volume := by
  apply locallyIntegrable_iff.mpr
  intro s hs
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.measure_lt_top.ne
  exact Integrable.of_bound
    ((measurable_feedbackConcatenatedVelocity lam).comp
      (f := fun x : ℝ ↦ (w, x)) measurable_prodMk_left).aestronglyMeasurable
    |lam| (ae_of_all _ (norm_feedbackConcatenatedVelocity_le lam w))

/-- The graph's derivative equals the actual feedback velocity at Lebesgue-almost every cut. -/
theorem ae_hasDerivAt_feedbackConcatenatedHeight (lam : ℝ) (w : FeedbackCellSequence) :
    ∀ᵐ x ∂volume, HasDerivAt (feedbackConcatenatedHeight lam w)
      (lam * currentSign (feedbackConcatenatedCurrent w x)) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (locallyIntegrable_feedbackConcatenatedVelocity lam w)]
    with x hx
  exact hx 0

/-- The feedback equation uses the current observable of the actual two-color environment. -/
theorem ae_feedbackConcatenatedEnvironment_integral {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ x : ℝ,
      (feedbackConcatenatedEnvironment lam w).path.graphHeight x =
        ∫ t in 0..x, lam * currentSign
          (FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
            (feedbackConcatenatedEnvironment lam w).path t) := by
  filter_upwards [ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw x
  change (∫ t in 0..x, lam * currentSign (feedbackConcatenatedCurrent w t)) = _
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hw]

/-- The same feedback equation holds after every spatial reroot, with the true updated current. -/
theorem ae_feedbackConcatenatedEnvironment_reroot_integral {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ a x : ℝ,
      (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).path.graphHeight x =
        ∫ t in 0..x, lam * currentSign
          (FeedbackPath.currentAt
            (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).currentIncrement
            (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).path t) := by
  filter_upwards [ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw a x
  have hi (b c : ℝ) : IntervalIntegrable (feedbackConcatenatedVelocity lam w) volume b c :=
    intervalIntegrable_iff.mpr
      (((locallyIntegrable_feedbackConcatenatedVelocity lam w).integrableOn_isCompact
        isCompact_uIcc).mono_set uIoc_subset_uIcc)
  change feedbackConcatenatedHeight lam w (x + a) - feedbackConcatenatedHeight lam w a = _
  rw [show feedbackConcatenatedHeight lam w (x + a) - feedbackConcatenatedHeight lam w a =
      ∫ t in a..(x + a), feedbackConcatenatedVelocity lam w t from
    intervalIntegral.integral_interval_sub_left (hi 0 (x + a)) (hi 0 a)]
  have htrans := intervalIntegral.integral_comp_add_right
    (f := feedbackConcatenatedVelocity lam w) (a := 0) (b := x) a
  simp only [zero_add] at htrans
  rw [← htrans]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [currentAt_feedbackEnvironment_reroot, hw]
  rfl

/-- Almost-everywhere differentiation of the actual graph gives the feedback equation in terms
of source-minus-target counts, with no independent current process postulated. -/
theorem ae_feedbackConcatenatedEnvironment_hasDerivAt {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ᵐ x ∂volume,
      HasDerivAt (fun y ↦ (feedbackConcatenatedEnvironment lam w).path.graphHeight y)
        (lam * currentSign
          (FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
            (feedbackConcatenatedEnvironment lam w).path x)) x := by
  filter_upwards [ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw
  filter_upwards [ae_hasDerivAt_feedbackConcatenatedHeight lam w] with x hx
  rw [hw]
  exact hx


/-- Strictly before the first positive return, every positive-index current is nonzero. -/
theorem feedbackMarkedFirstReturnIndex_current_ne_zero (w : FeedbackCellPath)
    {n : ℕ} (hn : 0 < n) (hlt : n < feedbackMarkedFirstReturnIndex w) :
    (w n).2.2 ≠ 0 := by
  have ht : 0 < feedbackMarkedFirstReturnIndex w := hn.trans hlt
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have h := (feedbackMarkedFirstReturnIndex_eq_succ_iff w m).mp hm
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact h.2 i (by omega)

/-- Among retained cell arrivals, current zero identifies exactly the final arrival. -/
theorem feedbackCell_postCurrent_zero_iff_terminal (w : FeedbackCellPath) {n : ℕ}
    (hn : n < feedbackMarkedFirstReturnIndex w) :
    (w (n + 1)).2.2 = 0 ↔ n + 1 = feedbackMarkedFirstReturnIndex w := by
  constructor
  · intro hz
    by_contra hne
    exact feedbackMarkedFirstReturnIndex_current_ne_zero w (Nat.succ_pos n) (by omega) hz
  · intro h
    rw [h]
    exact feedbackMarkedFirstReturnIndex_current w (by omega)

/-- The concatenated current is zero at each actual return root, simultaneously on both sides. -/
theorem feedbackConcatenatedCurrent_root {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) :
    feedbackConcatenatedCurrent w (feedbackCellRoot w k) = 0 := by
  have h := feedbackConcatenatedCurrent_shift hw.1 k 0
  have hz : feedbackConcatenatedCurrent (IIDShift.shift k w) 0 = 0 :=
    feedbackConcatenatedCurrent_zero (hw.1.shift k) (by
      simpa only [IIDShift.shift, zero_add] using (hw.2 k).1)
  simpa only [zero_add, hz] using h.symm

/-- Reading the current just at an actual arrival gives its sampled post-jump current, including
terminal arrivals, which are simultaneously the following cell's zero root. -/
theorem feedbackConcatenatedCurrent_at_event {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) {n : ℕ}
    (hn : n < feedbackMarkedFirstReturnIndex (w k)) (hstart : (w k 0).2.2 = 0) :
    feedbackConcatenatedCurrent w (feedbackCellEventPoint w (k, n)).1 =
      (w k (n + 1)).2.2 := by
  have hc := feedbackCellClock_strictMono (w k) (hw.2 k).1
  have hroof := feedbackCellLength_eq_clock (w k) (hw.2 k).1 (hw.2 k).2
  by_cases ht : n + 1 = feedbackMarkedFirstReturnIndex (w k)
  · have hevent : (feedbackCellEventPoint w (k, n)).1 = feedbackCellRoot w (k + 1) := by
      simp only [feedbackCellEventPoint, ht, feedbackCellRoot_add_one, hroof]
    rw [hevent, feedbackConcatenatedCurrent_root hw, ht,
      feedbackMarkedFirstReturnIndex_current (w k) (hw.2 k).2]
  · have hi : feedbackCellIndex w (feedbackCellEventPoint w (k, n)).1 = k := by
      apply (feedbackCellIndex_eq_iff hw.1 _ k).mpr
      have hpos := hc (Nat.succ_pos n)
      rw [feedbackCellClock_zero] at hpos
      have hlt := hc (show n + 1 < feedbackMarkedFirstReturnIndex (w k) by omega)
      rw [← hroof] at hlt
      simp only [feedbackCellEventPoint, feedbackCellRoot_add_one]
      constructor <;> linarith
    unfold feedbackConcatenatedCurrent
    rw [hi]
    dsimp only
    have hsub : (feedbackCellEventPoint w (k, n)).1 - feedbackCellRoot w k =
        feedbackCellClock (w k) (n + 1) := by simp only [feedbackCellEventPoint]; ring
    rw [hsub]
    exact feedbackCellCurrent_eq_of_clock_bounds (w k) (n + 1) _ (by omega)
      hstart hc le_rfl (hc (Nat.lt_succ_self _))

/-- Zero post-current at a retained event is equivalent to being an actual return root. -/
theorem feedbackCellEvent_current_zero_iff_root {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) {n : ℕ}
    (hn : n < feedbackMarkedFirstReturnIndex (w k)) (hstart : (w k 0).2.2 = 0) :
    feedbackConcatenatedCurrent w (feedbackCellEventPoint w (k, n)).1 = 0 ↔
      ∃ j : ℤ, (feedbackCellEventPoint w (k, n)).1 = feedbackCellRoot w j := by
  constructor
  · intro hz
    rw [feedbackConcatenatedCurrent_at_event hw k hn hstart] at hz
    have ht := (feedbackCell_postCurrent_zero_iff_terminal (w k) hn).mp hz
    refine ⟨k + 1, ?_⟩
    simp only [feedbackCellEventPoint, feedbackCellRoot_add_one, ht,
      feedbackCellLength_eq_clock (w k) (hw.2 k).1 (hw.2 k).2]
  · rintro ⟨j, hj⟩
    rw [hj, feedbackConcatenatedCurrent_root hw]

/-- Each return arrival comes from a genuinely nonzero current, as opposed to a zero hold. -/
theorem feedbackCell_terminal_preCurrent_ne_zero (w : FeedbackCellPath) {n : ℕ}
    (ht : n + 1 = feedbackMarkedFirstReturnIndex w)
    (hneigh : (w (n + 1)).2.2 = (w n).2.2 + 1 ∨
      (w (n + 1)).2.2 = (w n).2.2 - 1) : (w n).2.2 ≠ 0 := by
  have hz : (w (n + 1)).2.2 = 0 := by
    rw [ht]
    exact feedbackMarkedFirstReturnIndex_current w (by omega)
  omega

/-- Under the actual iid law, return roots among event locations are detected by the current
observable of the two-color environment. This is independent of an added root decoration. -/
theorem ae_feedbackCellEvent_observedCurrent_zero_iff_root {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ k : ℤ, ∀ n : ℕ,
      n < feedbackMarkedFirstReturnIndex (w k) →
      (FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
        (feedbackConcatenatedEnvironment lam w).path (feedbackCellEventPoint w (k, n)).1 = 0 ↔
        ∃ j : ℤ, (feedbackCellEventPoint w (k, n)).1 = feedbackCellRoot w j) := by
  filter_upwards [feedbackCellBase_identification_good hlam0 hlam,
    ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw hcurrent k n hn
  rw [hcurrent]
  exact feedbackCellEvent_current_zero_iff_root hw.1 k hn (hw.2.2.1 k)


/-- Strict clocks and disjoint right-closed cells exclude simultaneous distinct arrival labels. -/
theorem feedbackCellEventPoint_fst_injective {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) {i j : ℤ × ℕ}
    (hi : i.2 < feedbackMarkedFirstReturnIndex (w i.1))
    (hj : j.2 < feedbackMarkedFirstReturnIndex (w j.1))
    (heq : (feedbackCellEventPoint w i).1 = (feedbackCellEventPoint w j).1) : i = j := by
  have hai : feedbackCellEventActive w ((w i.1 (i.2 + 1)).2.2 - (w i.1 i.2).2.2) i :=
    ⟨hw, hi, rfl⟩
  have haj : feedbackCellEventActive w ((w j.1 (j.2 + 1)).2.2 - (w j.1 j.2).2.2) j :=
    ⟨hw, hj, rfl⟩
  have hk : i.1 = j.1 := (feedbackCellEventPoint_mem_Ioc_roots_iff hai j.1).mp
    (heq ▸ feedbackCellEventPoint_mem_cell haj)
  apply Prod.ext hk
  have hclock : feedbackCellClock (w i.1) (i.2 + 1) =
      feedbackCellClock (w i.1) (j.2 + 1) := by
    simp only [feedbackCellEventPoint, ← hk] at heq
    linarith
  have hindex := (feedbackCellClock_strictMono (w i.1) (hw.2 i.1).1).injective hclock
  omega

/-- Every return root is the terminal arrival of its preceding actual cell. -/
theorem exists_feedbackCellEventPoint_eq_root {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (j : ℤ) :
    ∃ n : ℕ, n < feedbackMarkedFirstReturnIndex (w (j - 1)) ∧
      n + 1 = feedbackMarkedFirstReturnIndex (w (j - 1)) ∧
      (feedbackCellEventPoint w (j - 1, n)).1 = feedbackCellRoot w j := by
  have ht := (hw.2 (j - 1)).2
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  refine ⟨n, by omega, hn.symm, ?_⟩
  have hr := feedbackCellRoot_add_one w (j - 1)
  have hid : j - 1 + 1 = j := by omega
  rw [hid] at hr
  simp only [feedbackCellEventPoint, hr,
    feedbackCellLength_eq_clock (w (j - 1)) (hw.2 (j - 1)).1 ht, hn]

/-- Actual return roots are exactly the retained arrivals with nonzero pre-current and zero
observed post-current. This includes every root, not only roots already known to be event points. -/
theorem ae_feedbackCellRoot_iff_nonzero_to_zero_event {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ x : ℝ,
      (∃ j : ℤ, x = feedbackCellRoot w j) ↔
      ∃ k : ℤ, ∃ n : ℕ, n < feedbackMarkedFirstReturnIndex (w k) ∧
        x = (feedbackCellEventPoint w (k, n)).1 ∧ (w k n).2.2 ≠ 0 ∧
        FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
          (feedbackConcatenatedEnvironment lam w).path x = 0 := by
  filter_upwards [feedbackCellBase_identification_good hlam0 hlam,
    ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw hcurrent x
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨n, hn, ht, hp⟩ := exists_feedbackCellEventPoint_eq_root hw.1 j
    refine ⟨j - 1, n, hn, hp.symm,
      feedbackCell_terminal_preCurrent_ne_zero (w (j - 1)) ht (hw.2.2.2 (j - 1) n), ?_⟩
    rw [hcurrent, feedbackConcatenatedCurrent_root hw.1]
  · rintro ⟨k, n, hn, rfl, hpre, hzero⟩
    rw [hcurrent] at hzero
    exact (feedbackCellEvent_current_zero_iff_root hw.1 k hn (hw.2.2.1 k)).mp hzero


/-- Between consecutive physical clocks, the full two-sided current equals the sampled state
of that cell. In particular this recovers the actual left limit at an arrival. -/
theorem feedbackConcatenatedCurrent_eq_of_cell_clock_bounds {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) {n : ℕ}
    (hn : n < feedbackMarkedFirstReturnIndex (w k)) (hstart : (w k 0).2.2 = 0)
    {x : ℝ} (hlo : feedbackCellRoot w k + feedbackCellClock (w k) n ≤ x)
    (hhi : x < feedbackCellRoot w k + feedbackCellClock (w k) (n + 1)) :
    feedbackConcatenatedCurrent w x = (w k n).2.2 := by
  have hc := feedbackCellClock_strictMono (w k) (hw.2 k).1
  have hclock0 : 0 ≤ feedbackCellClock (w k) n := by
    simpa only [feedbackCellClock_zero] using hc.monotone (Nat.zero_le n)
  have hclockEnd : feedbackCellClock (w k) (n + 1) ≤ feedbackCellLength (w k) := by
    rw [feedbackCellLength_eq_clock (w k) (hw.2 k).1 (hw.2 k).2]
    exact hc.monotone (by omega)
  have hindex : feedbackCellIndex w x = k := by
    apply (feedbackCellIndex_eq_iff hw.1 x k).mpr
    rw [feedbackCellRoot_add_one]
    constructor <;> linarith
  unfold feedbackConcatenatedCurrent
  rw [hindex]
  dsimp only
  exact feedbackCellCurrent_eq_of_clock_bounds (w k) n _ hn.le hstart hc
    (by linarith) (by linarith)

/-- Every return root is a spatial jump from a nonzero left-neighborhood current into zero;
the neighborhood length is the actual final holding time of the preceding cell. -/
theorem ae_feedbackCellRoot_nonzero_left_zero_at {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ,
      FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
        (feedbackConcatenatedEnvironment lam w).path (feedbackCellRoot w j) = 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ioo (feedbackCellRoot w j - ε) (feedbackCellRoot w j),
        FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
          (feedbackConcatenatedEnvironment lam w).path x ≠ 0 := by
  filter_upwards [feedbackCellBase_identification_good hlam0 hlam,
    ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw hcurrent j
  constructor
  · rw [hcurrent, feedbackConcatenatedCurrent_root hw.1]
  · obtain ⟨n, hn, ht, hp⟩ := exists_feedbackCellEventPoint_eq_root hw.1 j
    let ε := feedbackCellClock (w (j - 1)) (n + 1) - feedbackCellClock (w (j - 1)) n
    have heps : 0 < ε := sub_pos.mpr
      (feedbackCellClock_strictMono (w (j - 1)) (hw.1.2 (j - 1)).1 (Nat.lt_succ_self n))
    refine ⟨ε, heps, ?_⟩
    intro x hx
    rw [hcurrent, feedbackConcatenatedCurrent_eq_of_cell_clock_bounds hw.1 (j - 1) hn
      (hw.2.2.1 (j - 1))]
    · exact feedbackCell_terminal_preCurrent_ne_zero (w (j - 1)) ht (hw.2.2.2 (j - 1) n)
    · have hp' : feedbackCellRoot w j = feedbackCellRoot w (j - 1) +
          feedbackCellClock (w (j - 1)) (n + 1) := hp.symm
      dsimp [ε] at hx
      linarith [hx.1]
    · rw [← show feedbackCellRoot w j = feedbackCellRoot w (j - 1) +
        feedbackCellClock (w (j - 1)) (n + 1) from hp.symm]
      exact hx.2


/-- The differential feedback equation also holds after every choice of spatial origin. -/
theorem ae_feedbackConcatenatedEnvironment_reroot_hasDerivAt {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ a : ℝ, ∀ᵐ x ∂volume,
      HasDerivAt
        (fun y ↦ (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).path.graphHeight y)
        (lam * currentSign (FeedbackPath.currentAt
          (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).currentIncrement
          (FeedbackEnvironment.reroot a (feedbackConcatenatedEnvironment lam w)).path x)) x := by
  filter_upwards [ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam] with w hw a
  have hd := (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae
    (ae_hasDerivAt_feedbackConcatenatedHeight lam w)
  filter_upwards [hd] with x hx
  rw [currentAt_feedbackEnvironment_reroot, hw]
  have hcomp := hx.comp x ((hasDerivAt_id x).add_const a)
  have hsub := hcomp.sub_const (feedbackConcatenatedHeight lam w a)
  simp only [Function.comp_def, id_eq, mul_one] at hsub
  exact hsub

end OTSelector.Limit
