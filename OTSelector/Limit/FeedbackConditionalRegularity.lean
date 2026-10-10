import OTSelector.Limit.FeedbackZeroHold
import OTSelector.Probability.IIDMonotoneGrid
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Conditional cell regularity from second moments

Collapsing the residual zero hold restores the actual independent Palm cell law, uniformly in
its conditioned residual band. Nonnegative cell observables can then be controlled on a finite
index grid with Chebyshev's inequality; monotonicity fills the gaps between grid points.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators

namespace OTSelector.Limit

set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

/-- Erasing and reinstalling the first hold preserves every actual path coordinate. -/
theorem feedbackCollapseZeroHoldAssemble_reconstruct (ω : FeedbackCellSequence)
    (hzero : ω 0 0 = feedbackMarkedVirtual 0) :
    feedbackCollapseZeroHoldAssemble ((ω 0 1).1, feedbackEraseZeroHold ω) = ω := by
  funext j n
  by_cases hj : j = 0
  · subst j
    cases n with
    | zero =>
      simpa [feedbackCollapseZeroHoldAssemble, feedbackEraseZeroHold,
        feedbackMarkedWithoutFirstWait, feedbackMarkedRemainderAssemble] using hzero.symm
    | succ n =>
      cases n with
      | zero => simp [feedbackCollapseZeroHoldAssemble, feedbackEraseZeroHold]
      | succ n =>
        simp [feedbackCollapseZeroHoldAssemble, feedbackEraseZeroHold,
          show n + 1 + 1 = n + 2 by omega]
  · simp [feedbackCollapseZeroHoldAssemble, feedbackEraseZeroHold, hj]

/-- Reinstalling an independent rate-two hold gives precisely the original iid cell law. -/
theorem feedbackCollapseZeroHoldAssemble_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ((expMeasure 2).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam)).map
      feedbackCollapseZeroHoldAssemble = feedbackCellBase lam hlam0 hlam := by
  rw [← feedbackCellBase_zero_hold_remainder_map lam hlam0 hlam,
    Measure.map_map measurable_feedbackCollapseZeroHoldAssemble (by fun_prop)]
  have hzero : ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam,
      ω 0 0 = feedbackMarkedVirtual 0 :=
    (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).quasiMeasurePreserving.ae
      (feedbackMarkedTrajectory_initial hlam0 hlam 0)
  calc
    _ = (feedbackCellBase lam hlam0 hlam).map id := Measure.map_congr <|
      hzero.mono fun ω hω ↦ feedbackCollapseZeroHoldAssemble_reconstruct ω hω
    _ = _ := Measure.map_id

/-- Conditional collapse produces the actual iid Palm law, independently of the band location. -/
theorem feedbackStationaryRoofLaw_conditional_band_collapse_iid (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    (((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
        feedbackCollapseZeroHold = feedbackCellBase lam hlam0 hlam := by
  rw [feedbackStationaryRoofLaw_conditional_band_collapse_map lam hlam0 hlam h hh,
    feedbackCollapseZeroHoldAssemble_map]

private theorem integrable_pow_of_nonneg_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : ∀ w, 0 ≤ X w) {theta : ℝ} (htheta : 0 < theta)
    (hI : Integrable (fun w ↦ Real.exp (theta * X w)) μ) (p : ℕ) :
    Integrable (fun w ↦ X w ^ p) μ := by
  have hneg : Integrable (fun w ↦ Real.exp (-theta * X w)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hX.const_mul _ |>.exp.aestronglyMeasurable)
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) (hX0 w))
  exact integrable_pow_of_integrable_exp_mul htheta.ne' hI hneg p

/-- Actual jump counts have the finite second moment used by the grid estimate. -/
theorem memLp_feedbackMarkedFirstReturnIndex {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    MemLp (fun w ↦ (feedbackMarkedFirstReturnIndex w : ℝ)) 2
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have hm : Measurable (fun w ↦ (feedbackMarkedFirstReturnIndex w : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp measurable_feedbackMarkedFirstReturnIndex
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr <|
    integrable_pow_of_nonneg_exp _ hm (fun w ↦ Nat.cast_nonneg _)
      (feedbackCellExpRate_pos hlam0 hlam)
      (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam) 2

/-- Actual cell lengths have finite variance. -/
theorem memLp_feedbackCellLength {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    MemLp feedbackCellLength 2 (feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  (memLp_two_iff_integrable_sq measurable_feedbackCellLength.aestronglyMeasurable).mpr <|
    integrable_pow_of_nonneg_exp _ measurable_feedbackCellLength feedbackCellLength_nonneg
      (feedbackCellExpRate_pos hlam0 hlam) (feedbackCellLength_exp_integrable hlam0 hlam) 2

/-- The initial zero hold is bounded by the full roof almost surely and has finite variance. -/
theorem memLp_feedbackCellZeroHold {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    MemLp (fun w : FeedbackCellPath ↦ (w 1).1) 2
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have hm : Measurable (fun w : FeedbackCellPath ↦ (w 1).1) := by fun_prop
  refine (memLp_feedbackCellLength hlam0 hlam).mono' hm.aestronglyMeasurable ?_
  filter_upwards [feedbackMarkedTrajectory_waits_positive hlam0 hlam 0,
    feedbackCellLength_eq_hold_add_excursion hlam0 hlam] with w hw heq
  rw [Real.norm_eq_abs, abs_of_pos (hw 0)]
  linarith [feedbackCellExcursionLength_nonneg w]

/-- The untruncated idle-free reward has finite variance under the actual cell law. -/
theorem memLp_feedbackCellReward {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    MemLp (feedbackCellReward C) 2 (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have hN := integrable_pow_of_nonneg_exp (feedbackMarkedTrajectory lam hlam0 hlam 0)
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp measurable_feedbackMarkedFirstReturnIndex)
    (fun w ↦ Nat.cast_nonneg (feedbackMarkedFirstReturnIndex w))
    (feedbackCellExpRate_pos hlam0 hlam) (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam) 6
  have hE := integrable_pow_of_nonneg_exp (feedbackMarkedTrajectory lam hlam0 hlam 0)
    measurable_feedbackCellExcursionLength feedbackCellExcursionLength_nonneg
    (feedbackCellExpRate_pos hlam0 hlam) (feedbackCellExcursionLength_exp_integrable hlam0 hlam) 6
  apply (memLp_two_iff_integrable_sq (measurable_feedbackCellReward C).aestronglyMeasurable).mpr
  apply ((hN.add hE).const_mul (C ^ 2)).mono' (by fun_prop)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (C * (feedbackMarkedFirstReturnIndex w : ℝ) * feedbackCellExcursionLength w ^ 2) ^ 2 ≤ _
  have hN0 : 0 ≤ (feedbackMarkedFirstReturnIndex w : ℝ) := Nat.cast_nonneg _
  have hE0 := feedbackCellExcursionLength_nonneg w
  have hprod : (feedbackMarkedFirstReturnIndex w : ℝ) ^ 2 *
      feedbackCellExcursionLength w ^ 4 ≤
      (feedbackMarkedFirstReturnIndex w : ℝ) ^ 6 + feedbackCellExcursionLength w ^ 6 := by
    by_cases h : (feedbackMarkedFirstReturnIndex w : ℝ) ≤ feedbackCellExcursionLength w
    · calc
        _ ≤ feedbackCellExcursionLength w ^ 2 * feedbackCellExcursionLength w ^ 4 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN0 h 2) (pow_nonneg hE0 4)
        _ = feedbackCellExcursionLength w ^ 6 := by ring
        _ ≤ _ := le_add_of_nonneg_left (pow_nonneg hN0 _)
    · calc
        _ ≤ (feedbackMarkedFirstReturnIndex w : ℝ) ^ 2 *
            (feedbackMarkedFirstReturnIndex w : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE0 (le_of_not_ge h) 4) (sq_nonneg _)
        _ = (feedbackMarkedFirstReturnIndex w : ℝ) ^ 6 := by ring
        _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hE0 _)
  simp only [Pi.add_apply, Function.comp_def] at *
  nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg C)]

/-- The four nonnegative cell observables needed in a regular window: physical length, initial
zero hold, jump count, and idle-free reward. The absolute value only totalizes exceptional paths. -/
noncomputable def feedbackCellRegularityObservable (C : ℝ) : Fin 4 → FeedbackCellPath → ℝ :=
  ![feedbackCellLength, (fun w ↦ |(w 1).1|),
    (fun w ↦ (feedbackMarkedFirstReturnIndex w : ℝ)), feedbackCellReward C]

@[fun_prop]
theorem measurable_feedbackCellRegularityObservable (C : ℝ) (r : Fin 4) :
    Measurable (feedbackCellRegularityObservable C r) := by
  fin_cases r <;> simp [feedbackCellRegularityObservable] <;> fun_prop

theorem feedbackCellRegularityObservable_nonneg {C : ℝ} (hC : 0 ≤ C)
    (r : Fin 4) (w : FeedbackCellPath) : 0 ≤ feedbackCellRegularityObservable C r w := by
  fin_cases r
  · exact feedbackCellLength_nonneg w
  · exact abs_nonneg _
  · exact Nat.cast_nonneg _
  · exact feedbackCellReward_nonneg hC w

theorem memLp_feedbackCellRegularityObservable {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) (r : Fin 4) :
    MemLp (feedbackCellRegularityObservable C r) 2
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  fin_cases r
  · exact memLp_feedbackCellLength hlam0 hlam
  · change MemLp (fun w : FeedbackCellPath ↦ |(w 1).1|) 2 _
    simpa only [Real.norm_eq_abs] using (memLp_feedbackCellZeroHold hlam0 hlam).norm
  · exact memLp_feedbackMarkedFirstReturnIndex hlam0 hlam
  · exact memLp_feedbackCellReward hlam0 hlam

/-- Enumerate the cells to the right (`false`) or to the left (`true`) of the distinguished root. -/
def feedbackCellSideIndex (b : Bool) (n : ℕ) : ℤ :=
  if b then -((n : ℤ) + 1) else (n : ℤ)

theorem feedbackCellSideIndex_injective (b : Bool) : Injective (feedbackCellSideIndex b) := by
  intro m n h
  cases b <;> simp only [feedbackCellSideIndex, Bool.false_eq_true, ↓reduceIte] at h <;> omega

noncomputable def feedbackCellRegularityMean (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) (r : Fin 4) : ℝ :=
  ∫ w, feedbackCellRegularityObservable C r w ∂feedbackMarkedTrajectory lam hlam0 hlam 0

theorem feedbackCellRegularityMean_nonneg {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) (r : Fin 4) :
    0 ≤ feedbackCellRegularityMean lam hlam0 hlam C r :=
  integral_nonneg (feedbackCellRegularityObservable_nonneg hC r)

/-- Uniform simultaneous prefix control for the four actual cell observables on both sides. -/
def feedbackCellPrefixGood (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (C : ℝ) (M k : ℕ) (ω : FeedbackCellSequence) : Prop :=
  ∀ (r : Fin 4) (b : Bool) (n : ℕ), n ≤ M * k →
    |OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
      (feedbackCellSideIndex b) n ω - n * feedbackCellRegularityMean lam hlam0 hlam C r| ≤
      (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k

theorem measurableSet_feedbackCellPrefixGood (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) (M k : ℕ) :
    MeasurableSet {ω | feedbackCellPrefixGood lam hlam0 hlam C M k ω} := by
  unfold feedbackCellPrefixGood
  simp only [ofPred_forall]
  apply MeasurableSet.iInter fun r ↦ ?_
  apply MeasurableSet.iInter fun b ↦ ?_
  apply MeasurableSet.iInter fun n ↦ ?_
  apply MeasurableSet.iInter fun _ ↦ ?_
  exact measurableSet_le (by fun_prop) measurable_const

/-- This finite constant contains only the four actual cell variances and the fixed index horizon. -/
noncomputable def feedbackCellPrefixTailConstant (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) (M : ℕ) : ℝ :=
  ∑ p : Fin 4 × Bool, (M + 2 : ℕ) * (M + 1 : ℕ) *
    variance (feedbackCellRegularityObservable C p.1) (feedbackMarkedTrajectory lam hlam0 hlam 0)

theorem feedbackCellPrefixTailConstant_nonneg (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) (M : ℕ) :
    0 ≤ feedbackCellPrefixTailConstant lam hlam0 hlam C M := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (variance_nonneg _ _)

/-- Actual iid cells satisfy simultaneous prefix regularity with a reciprocal-scale error. -/
theorem feedbackCellBase_prefix_bad_le {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) (M : ℕ) {k : ℕ} (hk : 0 < k) :
    (feedbackCellBase lam hlam0 hlam).real
      {ω | ¬feedbackCellPrefixGood lam hlam0 hlam C M k ω} ≤
      feedbackCellPrefixTailConstant lam hlam0 hlam C M / k := by
  let bad : Fin 4 × Bool → Set FeedbackCellSequence := fun p ↦
    {ω | ∃ n ≤ M * k, (1 + feedbackCellRegularityMean lam hlam0 hlam C p.1) * k <
      |OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C p.1)
        (feedbackCellSideIndex p.2) n ω - n * feedbackCellRegularityMean lam hlam0 hlam C p.1|}
  have hset : {ω | ¬feedbackCellPrefixGood lam hlam0 hlam C M k ω} = ⋃ p, bad p := by
    ext ω
    simp only [feedbackCellPrefixGood, not_forall, not_le, mem_ofPred_eq, mem_iUnion, bad]
    constructor
    · rintro ⟨r, b, n, hn, hd⟩
      exact ⟨(r, b), n, hn, hd⟩
    · rintro ⟨⟨r, b⟩, n, hn, hd⟩
      exact ⟨r, b, n, hn, hd⟩
  rw [hset]
  apply (measureReal_iUnion_fintype_le bad).trans
  change (∑ p, (feedbackCellBase lam hlam0 hlam).real (bad p)) ≤ _
  rw [feedbackCellPrefixTailConstant, Finset.sum_div]
  apply Finset.sum_le_sum
  intro p _
  exact OTSelector.Probability.iidPrefix_uniform_deviation_le _
    (measurable_feedbackCellRegularityObservable C p.1)
    (memLp_feedbackCellRegularityObservable hlam0 hlam C p.1)
    (feedbackCellRegularityObservable_nonneg hC p.1)
    (feedbackCellSideIndex_injective p.2) M hk

/-- The same quantitative bound holds after conditioning the actual stationary roof on any
nonnegative residual band. No regenerative-law assumption is introduced. -/
theorem feedbackStationaryRoofLaw_conditional_prefix_bad_le {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) (M : ℕ) {k : ℕ} (hk : 0 < k)
    (h : ℝ) (hh : 0 ≤ h) :
    ((((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h))).real
      {p | ¬feedbackCellPrefixGood lam hlam0 hlam C M k (feedbackCollapseZeroHold p)} ≤
      feedbackCellPrefixTailConstant lam hlam0 hlam C M / k := by
  have heq := feedbackStationaryRoofLaw_conditional_band_collapse_iid lam hlam0 hlam h hh
  have hmeas : MeasurableSet {ω | ¬feedbackCellPrefixGood lam hlam0 hlam C M k ω} :=
    (measurableSet_feedbackCellPrefixGood lam hlam0 hlam C M k).compl
  have hmass := congrArg (fun μ : Measure FeedbackCellSequence ↦
    μ {ω | ¬feedbackCellPrefixGood lam hlam0 hlam C M k ω}) heq
  rw [Measure.map_apply measurable_feedbackCollapseZeroHold hmeas] at hmass
  simp only [Set.preimage_ofPred_eq] at hmass
  change ENNReal.toReal _ ≤ _
  rw [hmass]
  exact feedbackCellBase_prefix_bad_le hlam0 hlam hC M hk

/-- Prefix control also controls every block inside the index horizon. -/
theorem feedbackCellPrefixGood.block {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (r : Fin 4) (b : Bool) {m n : ℕ} (hmn : m + n ≤ M * k) :
    |(∑ i ∈ Finset.range n, feedbackCellRegularityObservable C r
        (ω (feedbackCellSideIndex b (m + i)))) -
      n * feedbackCellRegularityMean lam hlam0 hlam C r| ≤
      2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k := by
  have hm := hgood r b m (by omega)
  have hmn' := hgood r b (m + n) hmn
  have htri := (abs_sub_le
    (OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
      (feedbackCellSideIndex b) (m + n) ω -
        (m + n : ℕ) * feedbackCellRegularityMean lam hlam0 hlam C r) 0
    (OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
      (feedbackCellSideIndex b) m ω -
        m * feedbackCellRegularityMean lam hlam0 hlam C r))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have heq :
      (OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
        (feedbackCellSideIndex b) (m + n) ω -
          (m + n : ℕ) * feedbackCellRegularityMean lam hlam0 hlam C r) -
      (OTSelector.Probability.iidPrefix (feedbackCellRegularityObservable C r)
        (feedbackCellSideIndex b) m ω -
          m * feedbackCellRegularityMean lam hlam0 hlam C r) =
      (∑ i ∈ Finset.range n, feedbackCellRegularityObservable C r
        (ω (feedbackCellSideIndex b (m + i)))) -
          n * feedbackCellRegularityMean lam hlam0 hlam C r := by
    simp only [OTSelector.Probability.iidPrefix, Finset.sum_range_add, Nat.cast_add]
    ring
  rw [heq] at htri
  linarith

/-- A single cell cannot hide between the prefix anchors. -/
theorem feedbackCellPrefixGood.cell_le {lam C : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} {M k : ℕ} {ω : FeedbackCellSequence}
    (hgood : feedbackCellPrefixGood lam hlam0 hlam C M k ω)
    (r : Fin 4) (b : Bool) {m : ℕ} (hm : m < M * k) :
    feedbackCellRegularityObservable C r (ω (feedbackCellSideIndex b m)) ≤
      feedbackCellRegularityMean lam hlam0 hlam C r +
        2 * (1 + feedbackCellRegularityMean lam hlam0 hlam C r) * k := by
  have h := hgood.block r b (m := m) (n := 1) (by omega)
  simp only [Finset.sum_range_one, Nat.add_zero, Nat.cast_one, one_mul] at h
  linarith [(abs_le.mp h).2]

/-- The zero-hold mean is strictly positive for the actual marked return cell. -/
theorem feedbackCellRegularityMean_hold_pos {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    0 < feedbackCellRegularityMean lam hlam0 hlam C 1 := by
  change 0 < ∫ w, |(w 1).1| ∂feedbackMarkedTrajectory lam hlam0 hlam 0
  have hi : Integrable (fun w : FeedbackCellPath ↦ |(w 1).1|)
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
    simpa only [Real.norm_eq_abs] using
      ((memLp_feedbackCellZeroHold hlam0 hlam).integrable (by norm_num)).norm
  apply (integral_pos_iff_support_of_nonneg (fun _ ↦ abs_nonneg _) hi).mpr
  have heq : Function.support (fun w : FeedbackCellPath ↦ |(w 1).1|) =ᵐ[
      feedbackMarkedTrajectory lam hlam0 hlam 0] univ := by
    filter_upwards [feedbackMarkedTrajectory_waits_positive hlam0 hlam 0] with w hw
    exact propext ⟨fun _ ↦ Set.mem_univ w, fun _ ↦ abs_ne_zero.mpr (hw 0).ne'⟩
  rw [measure_congr heq, measure_univ]
  exact zero_lt_one

/-- The length mean used in prefix regularity is the original roof normalizing constant. -/
theorem feedbackCellRegularityMean_length (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    feedbackCellRegularityMean lam hlam0 hlam C 0 = feedbackCellMean lam hlam0 hlam := rfl

/-- Passing from an integer mesh to a real spatial scale loses only a fixed factor. -/
theorem feedbackStationaryRoofLaw_conditional_prefix_bad_le_real {lam C : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (hC : 0 ≤ C) (M : ℕ)
    {R L : ℝ} (hR : 0 < R) (hL : 2 * R ≤ L) (h : ℝ) (hh : 0 ≤ h) :
    ((((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h))).real
      {p | ¬feedbackCellPrefixGood lam hlam0 hlam C M ⌊L / R⌋₊
        (feedbackCollapseZeroHold p)} ≤
      (2 * R * feedbackCellPrefixTailConstant lam hlam0 hlam C M) / L := by
  have hx : 2 ≤ L / R := (le_div_iff₀ hR).mpr hL
  have hk : 0 < ⌊L / R⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hhalf : L / R / 2 ≤ (⌊L / R⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (L / R)
    linarith
  apply (feedbackStationaryRoofLaw_conditional_prefix_bad_le hlam0 hlam hC M hk h hh).trans
  apply (div_le_div_of_nonneg_left (feedbackCellPrefixTailConstant_nonneg lam hlam0 hlam C M)
    (by linarith : 0 < L / R / 2) hhalf).trans_eq
  field_simp

end OTSelector.Limit
