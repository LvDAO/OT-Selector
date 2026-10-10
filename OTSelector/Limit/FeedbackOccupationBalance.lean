import OTSelector.Limit.FeedbackEnvironmentIdentification
import OTSelector.Limit.FeedbackInvariantUniqueness
import Mathlib.Order.Interval.Set.Union

/-!
# Actual occupation and balance of feedback return cells

The occupation masses are read from the actual stationary environment. Their balance identities
come from the finite first-return path and its genuine holding/jump transition kernel.
-/

open MeasureTheory ProbabilityTheory Set Function Preorder
open scoped ENNReal BigOperators Classical

set_option maxHeartbeats 600000

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

open PointProcess

/-- The actual current marginal of the stationary feedback environment. -/
noncomputable def feedbackStationaryCurrentLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure ℤ :=
  (feedbackStationaryEnvironmentLaw lam hlam0 hlam).map (fun e ↦ e.path.rootCurrent)

instance feedbackStationaryCurrentLaw_isProbability {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure (feedbackStationaryCurrentLaw lam hlam0 hlam) :=
  Measure.isProbabilityMeasure_map FeedbackEnvironment.measurable_rootCurrent.aemeasurable

/-- Spatial occupation mass of a current state under the actual stationary feedback law. -/
noncomputable def feedbackOccupationMass (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : ℝ :=
  (feedbackStationaryCurrentLaw lam hlam0 hlam {k}).toReal

theorem feedbackOccupationMass_nonneg {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : 0 ≤ feedbackOccupationMass lam hlam0 hlam k :=
  ENNReal.toReal_nonneg

private theorem tsum_feedbackCurrent_atoms {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (∑' k : ℤ, feedbackStationaryCurrentLaw lam hlam0 hlam {k}) = 1 := by
  have h := congrArg (fun μ : Measure ℤ ↦ μ univ)
    (Measure.sum_smul_dirac (feedbackStationaryCurrentLaw lam hlam0 hlam))
  simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one, measure_univ] using h

theorem summable_feedbackOccupationMass {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Summable (feedbackOccupationMass lam hlam0 hlam) :=
  ENNReal.summable_toReal (by rw [tsum_feedbackCurrent_atoms hlam0 hlam]; exact ENNReal.one_ne_top)

theorem tsum_feedbackOccupationMass {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : ∑' k : ℤ, feedbackOccupationMass lam hlam0 hlam k = 1 := by
  simp only [feedbackOccupationMass]
  rw [← ENNReal.tsum_toReal_eq (fun k ↦ measure_ne_top _ _),
    tsum_feedbackCurrent_atoms hlam0 hlam, ENNReal.toReal_one]

/-- A finite history has not yet returned to zero at a positive jump index. -/
def feedbackBeforeReturnHistory (n : ℕ)
    (x : (i : Finset.Iic n) → FeedbackMarkedStep) : Prop :=
  ∀ i : Finset.Iic n, 0 < i.val → (x i).2.2 ≠ 0

theorem measurableSet_feedbackBeforeReturnHistory (n : ℕ) :
    MeasurableSet {x | feedbackBeforeReturnHistory n x} := by
  simp only [feedbackBeforeReturnHistory, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    (measurableSet_eq_fun ((measurable_pi_apply i).snd.snd) measurable_const).compl

theorem feedbackBeforeReturnHistory_iff {w : FeedbackCellPath} (n : ℕ)
    (ht : 0 < feedbackMarkedFirstReturnIndex w) :
    feedbackBeforeReturnHistory n (frestrictLe n w) ↔ n < feedbackMarkedFirstReturnIndex w := by
  constructor
  · intro hg
    by_contra hn
    have hh := hg ⟨feedbackMarkedFirstReturnIndex w, Finset.mem_Iic.mpr (by omega)⟩ ht
    exact hh (feedbackMarkedFirstReturnIndex_current w ht)
  · intro hn i hi
    exact feedbackMarkedFirstReturnIndex_current_ne_zero w hi
      ((Finset.mem_Iic.mp i.property).trans_lt hn)

/-- Conditional integration of a real marked next step against the actual finite-history kernel. -/
theorem lintegral_feedbackMarkedTrajectory_next {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ)
    {f : (((i : Finset.Iic n) → FeedbackMarkedStep) × FeedbackMarkedStep) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ w, f (frestrictLe n w, w (n + 1)) ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      ∫⁻ x, ∫⁻ z, f (x, z) ∂feedbackMarkedHistoryKernel lam n x
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hj : (feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) ⊗ₘ
      feedbackMarkedHistoryKernel lam n =
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map (fun w ↦ (frestrictLe n w, w (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  rw [← lintegral_map hf ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))),
    ← hj, Measure.lintegral_compProd hf]

/-- The actual occupation at a revealed state multiplies the genuine next-step expectation.
The stopping event is replaced by a finite-history event only on the proved returning set. -/
theorem lintegral_feedbackMarkedTrajectory_beforeReturn_next {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (n : ℕ) (k : ℤ)
    {f : FeedbackMarkedStep → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then f (w (n + 1)) else 0
      ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} *
        ∫⁻ z, f z ∂feedbackMarkedHoldingKernel lam k := by
  let A : Set ((i : Finset.Iic n) → FeedbackMarkedStep) :=
    {x | feedbackBeforeReturnHistory n x ∧ (x ⟨n, by simp⟩).2.2 = k}
  have hA : MeasurableSet A := (measurableSet_feedbackBeforeReturnHistory n).inter
    (measurableSet_eq_fun ((measurable_pi_apply _).snd.snd) measurable_const)
  have hae : ∀ᵐ (w : FeedbackCellPath) ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      (frestrictLe n w ∈ A) ↔ n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k := by
    filter_upwards [feedbackMarkedFirstReturnIndex_pos hlam0 hlam] with w hw
    exact and_congr_left (fun _ ↦ feedbackBeforeReturnHistory_iff n hw)
  have hprod : Measurable (fun p : ((i : Finset.Iic n) → FeedbackMarkedStep) × FeedbackMarkedStep ↦
      if p.1 ∈ A then f p.2 else 0) :=
    (hf.comp measurable_snd).ite (hA.preimage measurable_fst) measurable_const
  calc
    _ = ∫⁻ w, if frestrictLe n w ∈ A then f (w (n + 1)) else 0
        ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
      apply lintegral_congr_ae
      filter_upwards [hae] with w hw
      simp only [hw]
    _ = ∫⁻ x, ∫⁻ z, if x ∈ A then f z else 0 ∂feedbackMarkedHistoryKernel lam n x
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) :=
      lintegral_feedbackMarkedTrajectory_next hlam0 hlam n hprod
    _ = ∫⁻ x, A.indicator (fun _ ↦ ∫⁻ z, f z ∂feedbackMarkedHoldingKernel lam k) x
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        simp only [hx, ↓reduceIte]
        change (∫⁻ z, f z ∂feedbackMarkedHoldingKernel lam (x ⟨n, by simp⟩).2.2) = _
        rw [hx.2]
      · simp only [hx, ↓reduceIte, lintegral_zero, Set.indicator_of_notMem hx]
    _ = _ := by
      rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ,
        Measure.map_apply (measurable_frestrictLe n) hA, mul_comm]
      congr 1
      apply measure_congr
      exact hae.mono fun w hw ↦ propext hw

/-- Physical occupation time of state `k` during the first-return cell. -/
noncomputable def feedbackCellStateOccupation (w : FeedbackCellPath) (k : ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
    ENNReal.ofReal (w (n + 1)).1 else 0

/-- Number of departures from state `k` before the first positive return. -/
noncomputable def feedbackCellStateVisits (w : FeedbackCellPath) (k : ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then 1 else 0

theorem measurable_feedbackCellStateOccupation (k : ℤ) :
    Measurable (fun w ↦ feedbackCellStateOccupation w k) := by
  apply Measurable.tsum
  intro n
  apply ((measurable_pi_apply (n + 1)).fst.ennreal_ofReal).ite
  · exact (measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
      (measurableSet_eq_fun ((measurable_pi_apply n).snd.snd) measurable_const)
  · exact measurable_const

theorem measurable_feedbackCellStateVisits (k : ℤ) :
    Measurable (fun w ↦ feedbackCellStateVisits w k) := by
  apply Measurable.tsum
  intro n
  apply measurable_const.ite
  · exact (measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
      (measurableSet_eq_fun ((measurable_pi_apply n).snd.snd) measurable_const)
  · exact measurable_const

theorem feedbackCellStateOccupation_eq_sum (w : FeedbackCellPath) (k : ℤ) :
    feedbackCellStateOccupation w k =
      ∑ n ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
        if (w n).2.2 = k then ENNReal.ofReal (w (n + 1)).1 else 0 := by
  rw [feedbackCellStateOccupation, tsum_eq_sum (s := Finset.range (feedbackMarkedFirstReturnIndex w))]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range.mp hn, true_and]
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [hn, false_and, ↓reduceIte]

theorem feedbackCellStateVisits_eq_sum (w : FeedbackCellPath) (k : ℤ) :
    feedbackCellStateVisits w k =
      ∑ n ∈ Finset.range (feedbackMarkedFirstReturnIndex w), if (w n).2.2 = k then 1 else 0 := by
  rw [feedbackCellStateVisits, tsum_eq_sum (s := Finset.range (feedbackMarkedFirstReturnIndex w))]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range.mp hn, true_and]
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [hn, false_and, ↓reduceIte]

/-- The first nonnegative moment of an exponential waiting time is its inverse rate. -/
theorem lintegral_ofReal_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫⁻ t, ENNReal.ofReal t ∂expMeasure r = ENNReal.ofReal r⁻¹ := by
  have hgamma : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hpdf (t : ℝ) : exponentialPDF r t * ENNReal.ofReal t =
      ENNReal.ofReal r⁻¹ * gammaPDF 2 r t := by
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, gammaPDF_of_nonneg ht, hgamma]
      simp only [Real.rpow_two, div_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
      congr 1
      field_simp
    · simp [exponentialPDF_of_neg (lt_of_not_ge ht), gammaPDF_of_neg (lt_of_not_ge ht)]
  change ∫⁻ t, ENNReal.ofReal t ∂volume.withDensity (exponentialPDF r) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  simp only [Pi.mul_apply, hpdf]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by norm_num) hr, mul_one]

/-- The marked physical step retains the actual exponential holding-time mean. -/
theorem feedbackMarkedHoldingKernel_wait_mean {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∫⁻ z, ENNReal.ofReal z.1 ∂feedbackMarkedHoldingKernel lam k =
      ENNReal.ofReal (totalJumpRate lam k)⁻¹ := by
  have hmap : (feedbackMarkedHoldingKernel lam k).map Prod.fst =
      expMeasure (totalJumpRate lam k) := by
    let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
    change ((feedbackHoldingKernel lam k).prod (feedbackMarkedJumpKernel lam k)).map Prod.fst = _
    simp [feedbackHoldingKernel]
  rw [← lintegral_map (by fun_prop) measurable_fst, hmap]
  exact lintegral_ofReal_expMeasure (totalJumpRate_pos hlam0 hlam k)


theorem lintegral_feedbackCellStateVisits {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (∫⁻ w, feedbackCellStateVisits w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      ∑' n : ℕ, feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} := by
  have hm (n : ℕ) : MeasurableSet {w : FeedbackCellPath |
      n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} := by measurability
  change (∫⁻ w, ∑' n : ℕ, _ ∂_) = _
  rw [lintegral_tsum (fun n ↦ (measurable_const.ite (hm n) measurable_const).aemeasurable)]
  apply tsum_congr
  intro n
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, one_mul] using
    (lintegral_indicator_const (μ := feedbackMarkedTrajectory lam hlam0 hlam 0) (hm n) (1 : ℝ≥0∞))

/-- Expected physical occupation is expected departure count divided by the actual holding rate. -/
theorem lintegral_feedbackCellStateOccupation_eq_visits {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (∫⁻ w, feedbackCellStateOccupation w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      (∫⁻ w, feedbackCellStateVisits w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) *
        ENNReal.ofReal (totalJumpRate lam k)⁻¹ := by
  have hm (n : ℕ) : MeasurableSet {w : FeedbackCellPath |
      n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} := by measurability
  change (∫⁻ w, ∑' n : ℕ, _ ∂_) = _
  rw [lintegral_tsum (fun n ↦ (((measurable_pi_apply (n + 1)).fst.ennreal_ofReal).ite
    (hm n) measurable_const).aemeasurable)]
  simp_rw [lintegral_feedbackMarkedTrajectory_beforeReturn_next hlam0 hlam _ k
    measurable_fst.ennreal_ofReal, feedbackMarkedHoldingKernel_wait_mean hlam0 hlam k]
  rw [lintegral_feedbackCellStateVisits, ENNReal.tsum_mul_right]

private theorem sum_closed_current (w : FeedbackCellPath) (N : ℕ) (k : ℤ)
    (h : (w N).2.2 = (w 0).2.2) :
    (∑ n ∈ Finset.range N, if (w n).2.2 = k then (1 : ℕ) else 0) =
      ∑ n ∈ Finset.range N, if (w (n + 1)).2.2 = k then (1 : ℕ) else 0 := by
  have hs := Finset.sum_range_succ' (fun n ↦ if (w n).2.2 = k then (1 : ℕ) else 0) N
  rw [Finset.sum_range_succ, h] at hs
  omega

/-- A closed return cell has as many arrivals as departures at each state. -/
theorem feedbackCellStateVisits_eq_arrivals (w : FeedbackCellPath) (k : ℤ)
    (hstart : (w 0).2.2 = 0) (ht : 0 < feedbackMarkedFirstReturnIndex w) :
    feedbackCellStateVisits w k = ∑' n : ℕ,
      if n < feedbackMarkedFirstReturnIndex w ∧ (w (n + 1)).2.2 = k then 1 else 0 := by
  rw [feedbackCellStateVisits_eq_sum, tsum_eq_sum (s := Finset.range (feedbackMarkedFirstReturnIndex w))]
  · have h := sum_closed_current w (feedbackMarkedFirstReturnIndex w) k
      ((feedbackMarkedFirstReturnIndex_current w ht).trans hstart.symm)
    have he := congrArg (fun m : ℕ ↦ (m : ℝ≥0∞)) h
    push_cast at he
    rw [he]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range.mp hn, true_and]
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [hn, false_and, ↓reduceIte]

private theorem markedHoldingKernel_current_singleton {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (j k : ℤ) :
    (∫⁻ z, if z.2.2 = k then (1 : ℝ≥0∞) else 0 ∂feedbackMarkedHoldingKernel lam j) =
      feedbackJumpKernel lam j {k} := by
  have hf : Measurable (fun q : ℤ ↦ if q = k then (1 : ℝ≥0∞) else 0) := measurable_of_countable _
  rw [← lintegral_map hf measurable_snd.snd, feedbackMarkedHoldingKernel_map_current hlam0 hlam j]
  simpa only [Set.indicator_apply, Set.mem_singleton_iff, one_mul] using
    (lintegral_indicator_const (μ := feedbackJumpKernel lam j) (measurableSet_singleton k)
      (1 : ℝ≥0∞))

private theorem jumpKernel_arrive_from_left (lam : ℝ) (k : ℤ) :
    feedbackJumpKernel lam (k - 1) {k} = ENNReal.ofReal (jumpUpProbability lam (k - 1)) := by
  rw [feedbackJumpKernel_apply]
  have hne : k - 1 - 1 ≠ k := by omega
  simp [hne]

private theorem jumpKernel_arrive_from_right (lam : ℝ) (k : ℤ) :
    feedbackJumpKernel lam (k + 1) {k} = ENNReal.ofReal (jumpDownProbability lam (k + 1)) := by
  rw [feedbackJumpKernel_apply]
  have hne : k + 1 + 1 ≠ k := by omega
  simp [hne]

private theorem lintegral_stopped_arrival {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) (k : ℤ) :
    (∫⁻ w, if n < feedbackMarkedFirstReturnIndex w ∧ (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0
      ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k - 1} *
          ENNReal.ofReal (jumpUpProbability lam (k - 1)) +
      feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k + 1} *
          ENNReal.ofReal (jumpDownProbability lam (k + 1)) := by
  have hm (j : ℤ) : Measurable (fun w : FeedbackCellPath ↦
      if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = j then
        if (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0 else 0) := by
    apply (measurable_const.ite
      (measurableSet_eq_fun ((measurable_pi_apply (n + 1)).snd.snd) measurable_const)
      measurable_const).ite
    · exact (measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
        (measurableSet_eq_fun ((measurable_pi_apply n).snd.snd) measurable_const)
    · exact measurable_const
  have heq : (fun w : FeedbackCellPath ↦
      if n < feedbackMarkedFirstReturnIndex w ∧ (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0) =ᵐ[
        feedbackMarkedTrajectory lam hlam0 hlam 0] (fun w ↦
      (if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k - 1 then
        if (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0 else 0) +
      (if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k + 1 then
        if (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0 else 0)) := by
    filter_upwards [feedbackMarkedTrajectory_neighbors hlam0 hlam 0] with w hw
    have hj := hw n
    by_cases hn : n < feedbackMarkedFirstReturnIndex w
    · by_cases hk : (w (n + 1)).2.2 = k
      · rcases (show (w n).2.2 = k - 1 ∨ (w n).2.2 = k + 1 by omega) with hp | hp
        · have hq : (w n).2.2 ≠ k + 1 := by omega
          simp only [hn, hk, hq, true_and, ↓reduceIte]
          simp only [hp, ↓reduceIte, add_zero]
        · have hq : (w n).2.2 ≠ k - 1 := by omega
          simp only [hn, hk, hq, true_and, ↓reduceIte]
          simp only [hp, ↓reduceIte, zero_add]
      · simp only [hn, hk, true_and, ↓reduceIte, ite_self, add_zero]
    · simp only [hn, false_and, ↓reduceIte, add_zero]
  rw [lintegral_congr_ae heq, lintegral_add_left (hm (k - 1)),
    lintegral_feedbackMarkedTrajectory_beforeReturn_next hlam0 hlam n (k - 1)
      (f := fun z : FeedbackMarkedStep ↦ if z.2.2 = k then (1 : ℝ≥0∞) else 0)
      (measurable_const.ite (measurableSet_eq_fun measurable_snd.snd measurable_const)
        measurable_const),
    lintegral_feedbackMarkedTrajectory_beforeReturn_next hlam0 hlam n (k + 1)
      (f := fun z : FeedbackMarkedStep ↦ if z.2.2 = k then (1 : ℝ≥0∞) else 0)
      (measurable_const.ite (measurableSet_eq_fun measurable_snd.snd measurable_const)
        measurable_const),
    markedHoldingKernel_current_singleton hlam0 hlam,
    markedHoldingKernel_current_singleton hlam0 hlam,
    jumpKernel_arrive_from_left, jumpKernel_arrive_from_right]

/-- Expected state visits of the actual first-return cell satisfy the embedded-chain balance. -/
theorem lintegral_feedbackCellStateVisits_balance {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (∫⁻ w, feedbackCellStateVisits w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      (∫⁻ w, feedbackCellStateVisits w (k - 1) ∂feedbackMarkedTrajectory lam hlam0 hlam 0) *
        ENNReal.ofReal (jumpUpProbability lam (k - 1)) +
      (∫⁻ w, feedbackCellStateVisits w (k + 1) ∂feedbackMarkedTrajectory lam hlam0 hlam 0) *
        ENNReal.ofReal (jumpDownProbability lam (k + 1)) := by
  have hmeas (n : ℕ) : Measurable (fun w : FeedbackCellPath ↦
      if n < feedbackMarkedFirstReturnIndex w ∧ (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite
      ((measurableSet_lt measurable_const measurable_feedbackMarkedFirstReturnIndex).inter
        (measurableSet_eq_fun ((measurable_pi_apply (n + 1)).snd.snd) measurable_const))
      measurable_const
  have heq : (fun w ↦ feedbackCellStateVisits w k) =ᵐ[feedbackMarkedTrajectory lam hlam0 hlam 0]
      (fun w ↦ ∑' n : ℕ,
        if n < feedbackMarkedFirstReturnIndex w ∧ (w (n + 1)).2.2 = k then (1 : ℝ≥0∞) else 0) := by
    filter_upwards [feedbackMarkedTrajectory_initial hlam0 hlam 0,
      feedbackMarkedFirstReturnIndex_pos hlam0 hlam] with w hw ht
    apply feedbackCellStateVisits_eq_arrivals w k _ ht
    rw [hw]
    rfl
  rw [lintegral_congr_ae heq, lintegral_tsum (fun n ↦ (hmeas n).aemeasurable)]
  simp_rw [lintegral_stopped_arrival hlam0 hlam, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    lintegral_feedbackCellStateVisits]

/-- The cell occupation is the literal physical-time occupation of its sampled current. -/
theorem feedbackCellStateOccupation_eq_lintegral (w : FeedbackCellPath) (k : ℤ)
    (hw : ∀ i, 0 < (w (i + 1)).1) (ht : 0 < feedbackMarkedFirstReturnIndex w)
    (hstart : (w 0).2.2 = 0) :
    feedbackCellStateOccupation w k =
      ∫⁻ x in Ico 0 (feedbackCellLength w), if feedbackCellCurrent w x = k then 1 else 0 := by
  have hc := feedbackCellClock_strictMono w hw
  have hu : (⋃ n ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
      Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1))) = Ico 0 (feedbackCellLength w) := by
    rw [feedbackCellLength_eq_clock w hw ht, ← feedbackCellClock_zero w]
    apply le_antisymm
    · apply iUnion_subset
      intro n
      apply iUnion_subset
      intro hn
      exact Ico_subset_Ico (hc.monotone (Nat.zero_le _))
        (hc.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hn)))
    · exact Ico_subset_biUnion_Ico _ _
  have hd : Set.PairwiseDisjoint (↑(Finset.range (feedbackMarkedFirstReturnIndex w)) : Set ℕ)
      (fun n ↦ Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1))) := by
    intro n hn m hm hnm
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hnm with h | h
    · have hh := hc.monotone (Nat.succ_le_of_lt h)
      linarith [hx.2, hy.1]
    · have hh := hc.monotone (Nat.succ_le_of_lt h)
      linarith [hy.2, hx.1]
  rw [← hu, lintegral_biUnion_finset hd (fun _ _ ↦ measurableSet_Ico),
    feedbackCellStateOccupation_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have heq : (fun x ↦ if feedbackCellCurrent w x = k then (1 : ℝ≥0∞) else 0) =ᵐ[
      volume.restrict (Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1)))]
      (fun _ ↦ if (w n).2.2 = k then (1 : ℝ≥0∞) else 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [feedbackCellCurrent_eq_of_clock_bounds w n x (Finset.mem_range.mp hn).le
      hstart hc hx.1 hx.2]
  rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ico, feedbackCellClock_succ]
  by_cases hk : (w n).2.2 = k <;> simp [hk]

/-- Nonnegative integration over the actual cell roof is integration over its physical interval. -/
theorem lintegral_feedbackOccupationRoof {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {F : FeedbackCellSequence × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun w ↦ feedbackCellLength (w 0))) =
      ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)), F (w, t)
        ∂volume ∂feedbackCellBase lam hlam0 hlam := by
  have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
  rw [renewalRoofMeasure, ← lintegral_indicator hroof,
    lintegral_prod _ (hF.indicator hroof).aemeasurable]
  apply lintegral_congr
  intro w
  exact lintegral_indicator (measurableSet_Ico (a := (0 : ℝ))
    (b := feedbackCellLength (w 0))) (fun t ↦ F (w, t))

/-- The actual current atom equals the normalized physical holding reward of its true return cell. -/
theorem feedbackStationaryCurrentLaw_singleton_eq_occupation {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    feedbackStationaryCurrentLaw lam hlam0 hlam {k} =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
        ∫⁻ w, feedbackCellStateOccupation w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  let f : FeedbackEnvironment → ℝ≥0∞ := fun e ↦ if e.path.rootCurrent = k then 1 else 0
  have hf : Measurable f := measurable_const.ite
    (measurableSet_eq_fun FeedbackEnvironment.measurable_rootCurrent measurable_const)
    measurable_const
  have hmass : feedbackStationaryCurrentLaw lam hlam0 hlam {k} =
      ∫⁻ e, f e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
    rw [feedbackStationaryCurrentLaw, Measure.map_apply FeedbackEnvironment.measurable_rootCurrent
      (measurableSet_singleton k)]
    simpa only [f, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, one_mul] using
      (lintegral_indicator_const (μ := feedbackStationaryEnvironmentLaw lam hlam0 hlam)
        (FeedbackEnvironment.measurable_rootCurrent (measurableSet_singleton k)) (1 : ℝ≥0∞)).symm
  rw [hmass, feedbackStationaryEnvironmentLaw, renewalStationaryLaw,
    lintegral_smul_measure, smul_eq_mul, integral_feedbackCellBase_length,
    renewalOccupation, lintegral_map hf]
  · rw [lintegral_feedbackOccupationRoof hlam0 hlam]
    · congr 1
      calc
        _ = ∫⁻ w, feedbackCellStateOccupation (w 0) k ∂feedbackCellBase lam hlam0 hlam := by
          apply lintegral_congr_ae
          filter_upwards [feedbackCellBase_identification_good hlam0 hlam] with w hw
          rw [feedbackCellStateOccupation_eq_lintegral (w 0) k (hw.1.2 0).1 (hw.1.2 0).2
            (hw.2.2.1 0)]
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
          have hi : feedbackCellIndex w x = 0 := by
            apply (feedbackCellIndex_eq_iff hw.1.1 x 0).mpr
            have hr : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
              simpa only [feedbackCellRoot_zero, zero_add] using feedbackCellRoot_add_one w 0
            simpa only [zero_add, feedbackCellRoot_zero, hr, Set.mem_Ico] using hx
          change (if FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam w).currentIncrement
            (feedbackConcatenatedEnvironment lam w).path x = k then 1 else 0) = _
          rw [currentAt_feedbackConcatenatedEnvironment lam hw.1 hw.2.1 hw.2.2.2]
          simp only [feedbackConcatenatedCurrent, hi, feedbackCellRoot_zero, sub_zero]
        _ = _ := by
          rw [← (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).map_eq,
            lintegral_map (measurable_feedbackCellStateOccupation k) (measurable_pi_apply 0)]
    · exact hf.comp (FeedbackEnvironment.measurable_uncurry_reroot.comp
        (f := fun p : FeedbackCellSequence × ℝ ↦ (p.2, feedbackConcatenatedEnvironment lam p.1))
        (measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst)))
  · exact FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun p : FeedbackCellSequence × ℝ ↦ (p.2, feedbackConcatenatedEnvironment lam p.1))
      (measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst))

/-- The physical occupation masses satisfy the actual continuous-time balance equation. -/
theorem feedbackOccupationMass_global_balance {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    feedbackOccupationMass lam hlam0 hlam k * totalJumpRate lam k =
      feedbackOccupationMass lam hlam0 hlam (k - 1) * birthRate lam (k - 1) +
      feedbackOccupationMass lam hlam0 hlam (k + 1) * deathRate lam (k + 1) := by
  let c := (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹
  let V (j : ℤ) := ∫⁻ w, feedbackCellStateVisits w j ∂feedbackMarkedTrajectory lam hlam0 hlam 0
  have hm (j : ℤ) : feedbackStationaryCurrentLaw lam hlam0 hlam {j} =
      c * V j * (ENNReal.ofReal (totalJumpRate lam j))⁻¹ := by
    rw [feedbackStationaryCurrentLaw_singleton_eq_occupation hlam0 hlam,
      lintegral_feedbackCellStateOccupation_eq_visits hlam0 hlam,
      ENNReal.ofReal_inv_of_pos (totalJumpRate_pos hlam0 hlam j)]
    exact (mul_assoc _ _ _).symm
  have hout : feedbackStationaryCurrentLaw lam hlam0 hlam {k} *
      ENNReal.ofReal (totalJumpRate lam k) = c * V k := by
    rw [hm, ENNReal.inv_mul_cancel_right
      (ENNReal.ofReal_pos.mpr (totalJumpRate_pos hlam0 hlam k)).ne' ENNReal.ofReal_ne_top]
  have hup : feedbackStationaryCurrentLaw lam hlam0 hlam {k - 1} *
      ENNReal.ofReal (birthRate lam (k - 1)) = c *
        (V (k - 1) * ENNReal.ofReal (jumpUpProbability lam (k - 1))) := by
    rw [hm, jumpUpProbability, ENNReal.ofReal_div_of_pos (totalJumpRate_pos hlam0 hlam (k - 1))]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hdown : feedbackStationaryCurrentLaw lam hlam0 hlam {k + 1} *
      ENNReal.ofReal (deathRate lam (k + 1)) = c *
        (V (k + 1) * ENNReal.ofReal (jumpDownProbability lam (k + 1))) := by
    rw [hm, jumpDownProbability, ENNReal.ofReal_div_of_pos (totalJumpRate_pos hlam0 hlam (k + 1))]
    simp only [div_eq_mul_inv]
    ac_rfl
  have hmass : feedbackStationaryCurrentLaw lam hlam0 hlam {k} *
      ENNReal.ofReal (totalJumpRate lam k) =
      feedbackStationaryCurrentLaw lam hlam0 hlam {k - 1} * ENNReal.ofReal (birthRate lam (k - 1)) +
      feedbackStationaryCurrentLaw lam hlam0 hlam {k + 1} * ENNReal.ofReal (deathRate lam (k + 1)) := by
    rw [hout, hup, hdown, ← mul_add]
    exact congrArg (c * ·) (lintegral_feedbackCellStateVisits_balance hlam0 hlam k)
  have h := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)] at h
  simpa only [feedbackOccupationMass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (totalJumpRate_pos hlam0 hlam k).le,
    ENNReal.toReal_ofReal (birthRate_nonneg hlam0 hlam (k - 1)),
    ENNReal.toReal_ofReal (deathRate_nonneg hlam0 hlam (k + 1))] using h

/-- The actual stationary current masses equal the explicit invariant masses. -/
theorem feedbackOccupationMass_eq_invariantMass {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : feedbackOccupationMass lam hlam0 hlam = invariantMass lam :=
  feedback_invariantMass_unique hlam0 hlam (summable_feedbackOccupationMass hlam0 hlam)
    (tsum_feedbackOccupationMass hlam0 hlam) (feedbackOccupationMass_global_balance hlam0 hlam)

/-- The actual current marginal is the explicit invariant current measure. -/
theorem feedbackStationaryCurrentLaw_eq_invariantCurrentMeasure {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    feedbackStationaryCurrentLaw lam hlam0 hlam = invariantCurrentMeasure lam := by
  apply Measure.ext_of_singleton
  intro k
  rw [invariantCurrentMeasure, withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]
  simp only [Measure.count_singleton, mul_one]
  rw [← feedbackOccupationMass_eq_invariantMass hlam0 hlam]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Each actual current atom has exactly the explicit invariant mass. -/
theorem feedbackStationaryCurrentLaw_singleton {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    feedbackStationaryCurrentLaw lam hlam0 hlam {k} = ENNReal.ofReal (invariantMass lam k) := by
  rw [feedbackStationaryCurrentLaw_eq_invariantCurrentMeasure hlam0 hlam,
    invariantCurrentMeasure, withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]
  simp

end OTSelector.Limit
