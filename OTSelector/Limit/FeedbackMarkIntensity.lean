import OTSelector.Limit.FeedbackOccupationBalance
import OTSelector.PointProcess.FeedbackReturnPalm

/-!
# Actual uniform marked intensities of the stationary feedback environment

First-return mark rewards are computed from the genuine marked transition kernel. The actual
root-sweep identity converts those cell rewards into spatial intensities of the concatenated
point configurations.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal BigOperators Classical

set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

attribute [local instance] Classical.propDecidable

/-- The number of actual color-`direction` arrivals with a mark in `B` during the return cell. -/
noncomputable def feedbackCellMarkedReward (direction : ℤ) (B : Set UnitMark)
    (w : FeedbackCellPath) : ℝ≥0∞ :=
  ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex w ∧
      (w (n + 1)).2.2 = (w n).2.2 + direction ∧ (w (n + 1)).2.1 ∈ B then 1 else 0

theorem measurable_feedbackCellMarkedReward (direction : ℤ) {B : Set UnitMark}
    (hB : MeasurableSet B) : Measurable (feedbackCellMarkedReward direction B) := by
  apply Measurable.tsum
  intro n
  apply measurable_const.ite _ measurable_const
  exact (measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
    ((measurableSet_eq_fun ((measurable_pi_apply (n + 1)).snd.snd)
      (((measurable_pi_apply n).snd.snd).add_const direction)).inter
      (hB.preimage ((measurable_pi_apply (n + 1)).snd.fst)))

private theorem feedbackCellMarkedReward_eq_state_sum (direction : ℤ) (B : Set UnitMark)
    (w : FeedbackCellPath) :
    feedbackCellMarkedReward direction B w = ∑' k : ℤ, ∑' n : ℕ,
      if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
        if (w (n + 1)).2.2 = k + direction ∧ (w (n + 1)).2.1 ∈ B then 1 else 0 else 0 := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  rw [tsum_eq_single ((w n).2.2)]
  · simp only [and_true]
    split_ifs <;> simp_all
  · intro k hk
    simp only [Ne.symm hk, and_false, ↓reduceIte]

/-- Decomposing the actual first-return mark count by the current before each jump. -/
theorem lintegral_feedbackCellMarkedReward_eq_state_sum {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (direction : ℤ) {B : Set UnitMark} (hB : MeasurableSet B) :
    (∫⁻ w, feedbackCellMarkedReward direction B w ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      ∑' k : ℤ, (∫⁻ w, feedbackCellStateVisits w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) *
        ∫⁻ z, if z.2.2 = k + direction ∧ z.2.1 ∈ B then (1 : ℝ≥0∞) else 0
          ∂feedbackMarkedHoldingKernel lam k := by
  have hf (k : ℤ) : Measurable (fun z : FeedbackMarkedStep ↦
      if z.2.2 = k + direction ∧ z.2.1 ∈ B then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite
      ((measurableSet_eq_fun measurable_snd.snd measurable_const).inter
        (hB.preimage measurable_snd.fst)) measurable_const
  have hm (k : ℤ) (n : ℕ) : Measurable (fun w : FeedbackCellPath ↦
      if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
        if (w (n + 1)).2.2 = k + direction ∧ (w (n + 1)).2.1 ∈ B then (1 : ℝ≥0∞) else 0 else 0) :=
    ((hf k).comp (measurable_pi_apply (n + 1))).ite
      ((measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
        (measurableSet_eq_fun ((measurable_pi_apply n).snd.snd) measurable_const)) measurable_const
  simp_rw [feedbackCellMarkedReward_eq_state_sum]
  rw [lintegral_tsum (fun k ↦ (Measurable.tsum (hm k)).aemeasurable)]
  apply tsum_congr
  intro k
  rw [lintegral_tsum (fun n ↦ (hm k n).aemeasurable)]
  simp_rw [lintegral_feedbackMarkedTrajectory_beforeReturn_next hlam0 hlam _ k (hf k)]
  rw [ENNReal.tsum_mul_right, lintegral_feedbackCellStateVisits]

/-- The marked physical step assigns the source rate measure to an upward mark slice. -/
theorem feedbackMarkedHoldingKernel_source_slice {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {B : Set UnitMark} (hB : MeasurableSet B) :
    ∫⁻ z, (if z.2.2 = k + 1 ∧ z.2.1 ∈ B then 1 else 0 : ℝ≥0∞)
      ∂feedbackMarkedHoldingKernel lam k =
      (ENNReal.ofReal (totalJumpRate lam k))⁻¹ * sourceMarkRateMeasure lam k B := by
  classical
  let S : Set (UnitMark × ℤ) := {z | z.2 = k + 1 ∧ z.1 ∈ B}
  have hS : MeasurableSet S :=
    ((measurableSet_singleton (k + 1)).preimage measurable_snd).inter
      (hB.preimage measurable_fst)
  have hmap : (feedbackMarkedHoldingKernel lam k).map Prod.snd =
      feedbackMarkedJumpKernel lam k := by
    let := feedbackHoldingKernel_isMarkov hlam0 hlam
    let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
    change ((feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k)).map Prod.snd = _
    simp
  have heq : (fun z : FeedbackMarkedStep ↦
      if z.2.2 = k + 1 ∧ z.2.1 ∈ B then (1 : ℝ≥0∞) else 0) =
      fun z ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) z.2 := by
    funext z
    simp [Set.indicator, S]
  rw [heq]
  rw [← lintegral_map (measurable_const.indicator hS) measurable_snd,
    hmap, lintegral_indicator_const hS, one_mul]
  change ((ENNReal.ofReal (totalJumpRate lam k))⁻¹ •
    ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
      (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))) S = _
  rw [Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_prodMk_right hS,
    Measure.map_apply measurable_prodMk_right hS]
  have hne : k - 1 ≠ k + 1 := by omega
  simp [S, hne]

/-- The marked physical step assigns the target rate measure to a downward mark slice. -/
theorem feedbackMarkedHoldingKernel_target_slice {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {B : Set UnitMark} (hB : MeasurableSet B) :
    ∫⁻ z, (if z.2.2 = k - 1 ∧ z.2.1 ∈ B then 1 else 0 : ℝ≥0∞)
      ∂feedbackMarkedHoldingKernel lam k =
      (ENNReal.ofReal (totalJumpRate lam k))⁻¹ * targetMarkRateMeasure lam k B := by
  classical
  let S : Set (UnitMark × ℤ) := {z | z.2 = k - 1 ∧ z.1 ∈ B}
  have hS : MeasurableSet S :=
    ((measurableSet_singleton (k - 1)).preimage measurable_snd).inter
      (hB.preimage measurable_fst)
  have hmap : (feedbackMarkedHoldingKernel lam k).map Prod.snd =
      feedbackMarkedJumpKernel lam k := by
    let := feedbackHoldingKernel_isMarkov hlam0 hlam
    let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
    change ((feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k)).map Prod.snd = _
    simp
  have heq : (fun z : FeedbackMarkedStep ↦
      if z.2.2 = k - 1 ∧ z.2.1 ∈ B then (1 : ℝ≥0∞) else 0) =
      fun z ↦ S.indicator (fun _ ↦ (1 : ℝ≥0∞)) z.2 := by
    funext z
    simp [Set.indicator, S]
  rw [heq]
  rw [← lintegral_map (measurable_const.indicator hS) measurable_snd,
    hmap, lintegral_indicator_const hS, one_mul]
  change ((ENNReal.ofReal (totalJumpRate lam k))⁻¹ •
    ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
      (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))) S = _
  rw [Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_prodMk_right hS,
    Measure.map_apply measurable_prodMk_right hS]
  have hne : k + 1 ≠ k - 1 := by omega
  simp [S, hne]


/-- The actual invariant current law mixes source mark densities to unit density. -/
theorem tsum_invariant_sourceMarkDensity_ofReal {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (u : UnitMark) :
    ∑' k : ℤ, ENNReal.ofReal (invariantMass lam k) *
      ENNReal.ofReal (sourceMarkDensity lam k u) = 1 := by
  have hs : Summable (fun k : ℤ ↦ invariantMass lam k * sourceMarkDensity lam k u) := by
    refine ((summable_invariantMass hlam0 hlam).sub
      ((summable_signedMass hlam0 hlam).mul_left (lam * (1 - (u : ℝ))))).congr ?_
    intro k
    simp only [sourceMarkDensity, signedMass]
    ring
  simp_rw [← ENNReal.ofReal_mul (invariantMass_nonneg hlam0 hlam _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k ↦ mul_nonneg (invariantMass_nonneg hlam0 hlam k)
      (sourceMarkDensity_nonneg hlam0 hlam k u)) hs,
    tsum_sourceMarkDensity hlam0 hlam, ENNReal.ofReal_one]

/-- The actual invariant current law mixes target mark densities to unit density. -/
theorem tsum_invariant_targetMarkDensity_ofReal {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (u : UnitMark) :
    ∑' k : ℤ, ENNReal.ofReal (invariantMass lam k) *
      ENNReal.ofReal (targetMarkDensity lam k u) = 1 := by
  have hs : Summable (fun k : ℤ ↦ invariantMass lam k * targetMarkDensity lam k u) := by
    refine ((summable_invariantMass hlam0 hlam).add
      ((summable_signedMass hlam0 hlam).mul_left (lam * (1 + (u : ℝ))))).congr ?_
    intro k
    simp only [targetMarkDensity, signedMass]
    ring
  simp_rw [← ENNReal.ofReal_mul (invariantMass_nonneg hlam0 hlam _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k ↦ mul_nonneg (invariantMass_nonneg hlam0 hlam k)
      (targetMarkDensity_nonneg hlam0 hlam k u)) hs,
    tsum_targetMarkDensity hlam0 hlam, ENNReal.ofReal_one]

/-- Mixing the actual source rate measures by the invariant current law gives uniform marks. -/
theorem tsum_invariant_sourceMarkRateMeasure {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    ∑' k : ℤ, ENNReal.ofReal (invariantMass lam k) * sourceMarkRateMeasure lam k B =
      volume B := by
  simp_rw [sourceMarkRateMeasure, withDensity_apply _ hB]
  have hmul (k : ℤ) : ENNReal.ofReal (invariantMass lam k) *
      (∫⁻ u in B, ENNReal.ofReal (sourceMarkDensity lam k u)) =
      ∫⁻ u in B, ENNReal.ofReal (invariantMass lam k) *
        ENNReal.ofReal (sourceMarkDensity lam k u) := by
    rw [lintegral_const_mul _ (by unfold sourceMarkDensity; fun_prop)]
  simp_rw [hmul]
  rw [← lintegral_tsum (fun k ↦ by unfold sourceMarkDensity; fun_prop)]
  simp_rw [tsum_invariant_sourceMarkDensity_ofReal hlam0 hlam]
  simp

/-- Mixing the actual target rate measures by the invariant current law gives uniform marks. -/
theorem tsum_invariant_targetMarkRateMeasure {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    ∑' k : ℤ, ENNReal.ofReal (invariantMass lam k) * targetMarkRateMeasure lam k B =
      volume B := by
  simp_rw [targetMarkRateMeasure, withDensity_apply _ hB]
  have hmul (k : ℤ) : ENNReal.ofReal (invariantMass lam k) *
      (∫⁻ u in B, ENNReal.ofReal (targetMarkDensity lam k u)) =
      ∫⁻ u in B, ENNReal.ofReal (invariantMass lam k) *
        ENNReal.ofReal (targetMarkDensity lam k u) := by
    rw [lintegral_const_mul _ (by unfold targetMarkDensity; fun_prop)]
  simp_rw [hmul]
  rw [← lintegral_tsum (fun k ↦ by unfold targetMarkDensity; fun_prop)]
  simp_rw [tsum_invariant_targetMarkDensity_ofReal hlam0 hlam]
  simp

/-- The normalized actual source mark reward has the uniform mark intensity. -/
theorem normalized_feedbackCellMarkedReward_source {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
      (∫⁻ w, feedbackCellMarkedReward 1 B w ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
        volume B := by
  rw [lintegral_feedbackCellMarkedReward_eq_state_sum hlam0 hlam 1 hB]
  simp_rw [feedbackMarkedHoldingKernel_source_slice hlam0 hlam _ hB]
  rw [← ENNReal.tsum_mul_left]
  calc
    _ = ∑' k : ℤ, feedbackStationaryCurrentLaw lam hlam0 hlam {k} * sourceMarkRateMeasure lam k B := by
      apply tsum_congr
      intro k
      rw [feedbackStationaryCurrentLaw_singleton_eq_occupation hlam0 hlam,
        lintegral_feedbackCellStateOccupation_eq_visits hlam0 hlam,
        ENNReal.ofReal_inv_of_pos (totalJumpRate_pos hlam0 hlam k)]
      ac_rfl
    _ = volume B := by
      simp_rw [feedbackStationaryCurrentLaw_singleton hlam0 hlam]
      exact tsum_invariant_sourceMarkRateMeasure hlam0 hlam hB

/-- The normalized actual target mark reward has the uniform mark intensity. -/
theorem normalized_feedbackCellMarkedReward_target {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
      (∫⁻ w, feedbackCellMarkedReward (-1) B w ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
        volume B := by
  rw [lintegral_feedbackCellMarkedReward_eq_state_sum hlam0 hlam (-1) hB]
  simp only [← sub_eq_add_neg]
  simp_rw [feedbackMarkedHoldingKernel_target_slice hlam0 hlam _ hB]
  rw [← ENNReal.tsum_mul_left]
  calc
    _ = ∑' k : ℤ, feedbackStationaryCurrentLaw lam hlam0 hlam {k} * targetMarkRateMeasure lam k B := by
      apply tsum_congr
      intro k
      rw [feedbackStationaryCurrentLaw_singleton_eq_occupation hlam0 hlam,
        lintegral_feedbackCellStateOccupation_eq_visits hlam0 hlam,
        ENNReal.ofReal_inv_of_pos (totalJumpRate_pos hlam0 hlam k)]
      ac_rfl
    _ = volume B := by
      simp_rw [feedbackStationaryCurrentLaw_singleton hlam0 hlam]
      exact tsum_invariant_targetMarkRateMeasure hlam0 hlam hB

/-- One cell's contribution to a shifted physical unit window and a measurable mark class. -/
noncomputable def feedbackCellMarkedWindow (direction : ℤ) (B : Set UnitMark)
    (p : FeedbackCellSequence × ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex (p.1 0) ∧
      (p.1 0 (n + 1)).2.2 = (p.1 0 n).2.2 + direction ∧ (p.1 0 (n + 1)).2.1 ∈ B ∧
      p.2 + feedbackCellClock (p.1 0) (n + 1) ∈ Ioc (0 : ℝ) 1 then 1 else 0

theorem measurable_feedbackCellMarkedWindow (direction : ℤ) {B : Set UnitMark}
    (hB : MeasurableSet B) : Measurable (feedbackCellMarkedWindow direction B) := by
  apply Measurable.tsum
  intro n
  have hw (i : ℕ) : Measurable (fun p : FeedbackCellSequence × ℝ ↦ p.1 0 i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply 0).comp measurable_fst)
  apply measurable_const.ite _ measurable_const
  exact (measurableSet_lt measurable_const (measurable_feedbackMarkedFirstReturnIndex.comp
    ((measurable_pi_apply 0).comp measurable_fst))).inter
    ((measurableSet_eq_fun (hw (n + 1)).snd.snd ((hw n).snd.snd.add_const direction)).inter
      ((hB.preimage (hw (n + 1)).snd.fst).inter
        (measurableSet_Ioc.preimage (measurable_snd.add
          ((measurable_feedbackCellClock (n + 1)).comp
            ((measurable_pi_apply 0).comp measurable_fst))))))

private theorem countingMeasure_feedbackCellMarkedWindow {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (direction : ℤ) {B : Set UnitMark}
    (hB : MeasurableSet B) (t : ℝ) :
    LocalConfiguration.countingMeasure (LocalConfiguration.reroot t
      (feedbackConcatenatedPoints direction w)) (Ioc (0 : ℝ) 1 ×ˢ B) =
      ∑' j : ℤ, feedbackCellMarkedWindow direction B
        (IIDShift.shift j w, feedbackCellRoot w j - t) := by
  have hs : MeasurableSet (Ioc (0 : ℝ) 1 ×ˢ B) := measurableSet_Ioc.prod hB
  have hp : Measurable (Configuration.pointTranslation (-t) : MatchingPoint → MatchingPoint) :=
    (Configuration.pointTranslation (-t)).continuous.measurable
  rw [LocalConfiguration.countingMeasure_reroot, Measure.map_apply hp hs,
    countingMeasure_feedbackConcatenatedPoints, Measure.sum_apply _ (hs.preimage hp),
    ENNReal.tsum_prod']
  apply tsum_congr
  intro j
  unfold feedbackCellMarkedWindow
  apply tsum_congr
  intro n
  have hd : (w j (n + 1)).2.2 - (w j n).2.2 = direction ↔
      (w j (n + 1)).2.2 = (w j n).2.2 + direction := by omega
  have hl : feedbackCellRoot w j + feedbackCellClock (w j) (n + 1) + -t =
      feedbackCellRoot w j - t + feedbackCellClock (w j) (n + 1) := by ring
  by_cases ha : feedbackCellEventActive w direction (j, n)
  · rw [ite_eq_left ha, Measure.dirac_apply' _ (hs.preimage hp)]
    have hn := ha.2.1
    have hdir := hd.mp ha.2.2
    simp only [IIDShift.shift, zero_add, hn, hdir, true_and,
      Set.indicator_apply, Set.mem_preimage, Set.mem_prod,
      Configuration.pointTranslation_apply, feedbackCellEventPoint, hl]
    split_ifs <;> simp_all
  · rw [ite_eq_right ha]
    have hnot : ¬(n < feedbackMarkedFirstReturnIndex (w j) ∧
        (w j (n + 1)).2.2 = (w j n).2.2 + direction) := by
      rintro ⟨hn, hj⟩
      exact ha ⟨hw, hn, hd.mpr hj⟩
    simp only [Measure.coe_zero, Pi.zero_apply, IIDShift.shift, zero_add]
    split_ifs with h
    · exact (hnot ⟨h.1, h.2.1⟩).elim
    · rfl

/-- Integrating a marked cell's shifted unit-window count recovers its full marked reward. -/
theorem lintegral_feedbackCellMarkedWindow (direction : ℤ) {B : Set UnitMark}
    (_hB : MeasurableSet B) (w : FeedbackCellSequence) :
    ∫⁻ x : ℝ, feedbackCellMarkedWindow direction B (w, x) =
      feedbackCellMarkedReward direction B (w 0) := by
  have hP (P : Prop) : MeasurableSet {x : ℝ | P} := by
    by_cases h : P <;> simp [h]
  have hm (n : ℕ) : Measurable (fun x : ℝ ↦
      if n < feedbackMarkedFirstReturnIndex (w 0) ∧
        (w 0 (n + 1)).2.2 = (w 0 n).2.2 + direction ∧ (w 0 (n + 1)).2.1 ∈ B ∧
        x + feedbackCellClock (w 0) (n + 1) ∈ Ioc (0 : ℝ) 1 then (1 : ℝ≥0∞) else 0) := by
    apply measurable_const.ite _ measurable_const
    exact (hP _).inter ((hP _).inter
      ((hP _).inter (measurableSet_Ioc.preimage (measurable_id.add_const _))))
  unfold feedbackCellMarkedWindow feedbackCellMarkedReward
  rw [lintegral_tsum (fun n ↦ (hm n).aemeasurable)]
  apply tsum_congr
  intro n
  by_cases h1 : n < feedbackMarkedFirstReturnIndex (w 0)
  · by_cases h2 : (w 0 (n + 1)).2.2 = (w 0 n).2.2 + direction
    · by_cases h3 : (w 0 (n + 1)).2.1 ∈ B
      · simp only [h1, h2, h3, true_and, ↓reduceIte]
        let c := feedbackCellClock (w 0) (n + 1)
        have hi : (fun x : ℝ ↦ if x + c ∈ Ioc (0 : ℝ) 1 then (1 : ℝ≥0∞) else 0) =
            (Ioc (-c) (1 - c)).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
          funext x
          have he : x + c ∈ Ioc (0 : ℝ) 1 ↔ x ∈ Ioc (-c) (1 - c) := by
            simp only [mem_Ioc]
            constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
          simp [Set.indicator, he]
        change (∫⁻ x : ℝ, if x + c ∈ Ioc (0 : ℝ) 1 then (1 : ℝ≥0∞) else 0) = 1
        rw [hi, lintegral_indicator_const measurableSet_Ioc, one_mul, Real.volume_Ioc]
        norm_num
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- Integrating the actual concatenated color process over the stationary roof gives exactly its
cell mark reward per mean cell length. -/
theorem lintegral_feedbackReturnRoof_marked_count {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (direction : ℤ) {B : Set UnitMark} (hB : MeasurableSet B) :
    (∫⁻ p, LocalConfiguration.countingMeasure (LocalConfiguration.reroot p.2
      (feedbackConcatenatedPoints direction p.1)) (Ioc (0 : ℝ) 1 ×ˢ B)
      ∂feedbackReturnRoofLaw lam hlam0 hlam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
        ∫⁻ w, feedbackCellMarkedReward direction B w ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  rw [feedbackReturnRoofLaw, lintegral_smul_measure, smul_eq_mul]
  congr 1
  have hterm (j : ℤ) : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      feedbackCellMarkedWindow direction B (IIDShift.shift j p.1, feedbackCellRoot p.1 j - p.2)) :=
    (measurable_feedbackCellMarkedWindow direction hB).comp
      (f := fun p : FeedbackCellSequence × ℝ ↦ (IIDShift.shift j p.1, feedbackCellRoot p.1 j - p.2))
      (((IIDShift.measurable_shift j).comp measurable_fst).prodMk
        (((measurable_feedbackCellRoot j).comp measurable_fst).sub measurable_snd))
  have hgood : ∀ᵐ p ∂renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun w ↦ feedbackCellLength (w 0)), feedbackCellConfigurationGood p.1 :=
    ae_restrict_of_ae (Measure.quasiMeasurePreserving_fst.ae
      (feedbackCellBase_configuration_good hlam0 hlam))
  calc
    _ = ∫⁻ p, ∑' j : ℤ, feedbackCellMarkedWindow direction B
        (IIDShift.shift j p.1, feedbackCellRoot p.1 j - p.2)
        ∂renewalRoofMeasure (feedbackCellBase lam hlam0 hlam) (fun w ↦ feedbackCellLength (w 0)) := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with p hp
      exact countingMeasure_feedbackCellMarkedWindow hp direction hB p.2
    _ = ∑' j : ℤ, ∫⁻ p, feedbackCellMarkedWindow direction B
        (IIDShift.shift j p.1, feedbackCellRoot p.1 j - p.2)
        ∂renewalRoofMeasure (feedbackCellBase lam hlam0 hlam) (fun w ↦ feedbackCellLength (w 0)) := by
      rw [lintegral_tsum (fun j ↦ (hterm j).aemeasurable)]
    _ = ∑' j : ℤ, ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
        feedbackCellMarkedWindow direction B (IIDShift.shift j w, feedbackCellRoot w j - t)
          ∂volume ∂feedbackCellBase lam hlam0 hlam := by
      apply tsum_congr
      intro j
      exact lintegral_feedbackOccupationRoof hlam0 hlam (hterm j)
    _ = ∫⁻ w, ∫⁻ x, feedbackCellMarkedWindow direction B (w, x)
        ∂volume ∂feedbackCellBase lam hlam0 hlam :=
      tsum_lintegral_feedbackReturnRootSweep hlam0 hlam
        (measurable_feedbackCellMarkedWindow direction hB)
    _ = ∫⁻ w, feedbackCellMarkedReward direction B (w 0) ∂feedbackCellBase lam hlam0 hlam := by
      simp_rw [lintegral_feedbackCellMarkedWindow direction hB]
    _ = _ := by
      rw [← (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).map_eq,
        lintegral_map (measurable_feedbackCellMarkedReward direction hB) (measurable_pi_apply 0)]

/-- Nonnegative observables of the actual stationary environment are evaluated under the actual
normalized cell-roof law. -/
theorem lintegral_feedbackStationaryEnvironmentLaw_nonneg {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) {f : FeedbackEnvironment → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ e, f e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) =
      ∫⁻ p, f (FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1))
        ∂feedbackReturnRoofLaw lam hlam0 hlam := by
  rw [feedbackStationaryEnvironmentLaw, renewalStationaryLaw, renewalOccupation,
    feedbackReturnRoofLaw, lintegral_smul_measure, lintegral_smul_measure,
    integral_feedbackCellBase_length, lintegral_map hf]
  · rfl
  · exact FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun p : FeedbackCellSequence × ℝ ↦ (p.2, feedbackConcatenatedEnvironment lam p.1))
      (measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst))

/-- Under the actual stationary feedback environment, source marks have Lebesgue unit intensity. -/
theorem lintegral_feedbackStationary_source_marks {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    (∫⁻ e, LocalConfiguration.countingMeasure e.source (Ioc (0 : ℝ) 1 ×ˢ B)
      ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) = volume B := by
  have hf : Measurable (fun e : FeedbackEnvironment ↦
      LocalConfiguration.countingMeasure e.source (Ioc (0 : ℝ) 1 ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (LocalConfiguration.measurable_countingMeasure.comp FeedbackEnvironment.measurable_source)
  rw [lintegral_feedbackStationaryEnvironmentLaw_nonneg hlam0 hlam hf]
  change (∫⁻ p, LocalConfiguration.countingMeasure (LocalConfiguration.reroot p.2
      (feedbackConcatenatedPoints 1 p.1)) (Ioc (0 : ℝ) 1 ×ˢ B)
      ∂feedbackReturnRoofLaw lam hlam0 hlam) = _
  rw [lintegral_feedbackReturnRoof_marked_count hlam0 hlam 1 hB,
    normalized_feedbackCellMarkedReward_source hlam0 hlam hB]

/-- Under the actual stationary feedback environment, target marks have Lebesgue unit intensity. -/
theorem lintegral_feedbackStationary_target_marks {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {B : Set UnitMark} (hB : MeasurableSet B) :
    (∫⁻ e, LocalConfiguration.countingMeasure e.target (Ioc (0 : ℝ) 1 ×ˢ B)
      ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) = volume B := by
  have hf : Measurable (fun e : FeedbackEnvironment ↦
      LocalConfiguration.countingMeasure e.target (Ioc (0 : ℝ) 1 ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (LocalConfiguration.measurable_countingMeasure.comp FeedbackEnvironment.measurable_target)
  rw [lintegral_feedbackStationaryEnvironmentLaw_nonneg hlam0 hlam hf]
  change (∫⁻ p, LocalConfiguration.countingMeasure (LocalConfiguration.reroot p.2
      (feedbackConcatenatedPoints (-1) p.1)) (Ioc (0 : ℝ) 1 ×ˢ B)
      ∂feedbackReturnRoofLaw lam hlam0 hlam) = _
  rw [lintegral_feedbackReturnRoof_marked_count hlam0 hlam (-1) hB,
    normalized_feedbackCellMarkedReward_target hlam0 hlam hB]

private theorem meanMarkedMeasure_eq_volume_prod {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (config : FeedbackEnvironment → LocalConfiguration matchingPointBase)
    (hc : Measurable config)
    (hcov : ∀ t e, config (FeedbackEnvironment.reroot t e) = LocalConfiguration.reroot t (config e))
    (hunit : ∀ B : Set UnitMark, MeasurableSet B →
      (∫⁻ e, LocalConfiguration.countingMeasure (config e) (Ioc (0 : ℝ) 1 ×ˢ B)
        ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) = volume B) :
    (feedbackStationaryEnvironmentLaw lam hlam0 hlam).bind
      (fun e ↦ LocalConfiguration.countingMeasure (config e)) =
      (volume : Measure ℝ).prod (volume : Measure UnitMark) := by
  let C := (feedbackStationaryEnvironmentLaw lam hlam0 hlam).bind
    (fun e ↦ LocalConfiguration.countingMeasure (config e))
  have hN : Measurable (fun e ↦ LocalConfiguration.countingMeasure (config e)) :=
    LocalConfiguration.measurable_countingMeasure.comp hc
  have hstat (a : ℝ) : MeasurePreserving (fun z : MatchingPoint ↦ (a + z.1, z.2)) C C := by
    apply measurePreserving_bind_of_covariant _ _ hN
      (measurePreserving_feedbackStationaryEnvironmentLaw hlam0 hlam (-a))
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
    apply Filter.Eventually.of_forall
    intro e
    change LocalConfiguration.countingMeasure (config (FeedbackEnvironment.reroot (-a) e)) = _
    rw [hcov, LocalConfiguration.countingMeasure_reroot]
    congr 1
    funext z
    simp only [Configuration.pointTranslation_apply, neg_neg, add_comm, Pi.add_apply]
  have hpalm : unitWindowPalm C = (volume : Measure UnitMark) := by
    ext B hB
    rw [unitWindowPalm_apply _ hB, Measure.bind_apply (measurableSet_Ioc.prod hB) hN.aemeasurable]
    exact hunit B hB
  have hfinite : C (Ioc (0 : ℝ) 1 ×ˢ univ) < ∞ := by
    rw [Measure.bind_apply (measurableSet_Ioc.prod MeasurableSet.univ) hN.aemeasurable,
      hunit univ MeasurableSet.univ]
    exact measure_lt_top _ _
  exact (campbell_eq_volume_prod_palm C hstat hfinite).trans (congrArg (volume.prod) hpalm)

/-- The actual expected source counting measure is spatial Lebesgue measure times uniform marks. -/
theorem feedbackStationary_source_intensity {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackStationaryEnvironmentLaw lam hlam0 hlam).bind
      (fun e ↦ LocalConfiguration.countingMeasure e.source) =
      (volume : Measure ℝ).prod (volume : Measure UnitMark) :=
  meanMarkedMeasure_eq_volume_prod hlam0 hlam FeedbackEnvironment.source
    FeedbackEnvironment.measurable_source (fun _ _ ↦ rfl)
    (fun _ hB ↦ lintegral_feedbackStationary_source_marks hlam0 hlam hB)

/-- The actual expected target counting measure is spatial Lebesgue measure times uniform marks. -/
theorem feedbackStationary_target_intensity {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackStationaryEnvironmentLaw lam hlam0 hlam).bind
      (fun e ↦ LocalConfiguration.countingMeasure e.target) =
      (volume : Measure ℝ).prod (volume : Measure UnitMark) :=
  meanMarkedMeasure_eq_volume_prod hlam0 hlam FeedbackEnvironment.target
    FeedbackEnvironment.measurable_target (fun _ _ ↦ rfl)
    (fun _ hB ↦ lintegral_feedbackStationary_target_marks hlam0 hlam hB)

end OTSelector.Limit
