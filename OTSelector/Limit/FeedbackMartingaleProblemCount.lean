import OTSelector.Limit.FeedbackMartingaleProblemFirstJump
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# First-jump martingales determine the actual marked holding law

The first waiting coordinate may be infinite. Only attained jumps enter its finite measure.
The martingales below are the marked counts stopped at the first jump, minus the integrated
constant rate while that jump has not yet occurred. Their martingale equations identify the
holding law and prove that the infinite-wait event is null.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The finite measure of attained first jumps; an infinite wait contributes no mass. -/
noncomputable def attainedFirstJumpLaw (μ : Measure Ω) (τ : Ω → ℝ≥0∞) (J : Ω → E) :
    Measure (ℝ × E) :=
  (μ.restrict {ω | τ ω ≠ ∞}).map (fun ω ↦ ((τ ω).toReal, J ω))

instance attainedFirstJumpLaw_isFinite (μ : Measure Ω) [IsFiniteMeasure μ]
    (τ : Ω → ℝ≥0∞) (J : Ω → E) : IsFiniteMeasure (attainedFirstJumpLaw μ τ J) := by
  unfold attainedFirstJumpLaw
  infer_instance

theorem attainedFirstJumpLaw_Iic (μ : Measure Ω) {τ : Ω → ℝ≥0∞} {J : Ω → E}
    (hτ : Measurable τ) (hJ : Measurable J) {t : ℝ} (ht : 0 ≤ t)
    {B : Set E} (hB : MeasurableSet B) :
    attainedFirstJumpLaw μ τ J (Iic t ×ˢ B) =
      μ {ω | τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B} := by
  rw [attainedFirstJumpLaw, Measure.map_apply (hτ.ennreal_toReal.prodMk hJ)
    (measurableSet_Iic.prod hB), Measure.restrict_apply
      ((hτ.ennreal_toReal.prodMk hJ) (measurableSet_Iic.prod hB))]
  congr 1
  ext ω
  constructor
  · rintro ⟨⟨hw, hB⟩, hfin⟩
    exact ⟨(ENNReal.le_ofReal_iff_toReal_le hfin ht).mpr hw, hB⟩
  · rintro ⟨hw, hB⟩
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hw
    exact ⟨⟨(ENNReal.le_ofReal_iff_toReal_le hfin ht).mp hw, hB⟩, hfin⟩

/-- The marked first count compensated until the first jump. -/
noncomputable def firstJumpCompensator (r : ℝ) (π : Measure E) (τ : Ω → ℝ≥0∞)
    (J : Ω → E) (B : Set E) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (if τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B then 1 else 0) -
    r * π.real B * ∫ s in 0..(t : ℝ), if ENNReal.ofReal s < τ ω then 1 else 0

/-- Fubini converts the expected pre-jump occupation time to the survival probability integral. -/
theorem integral_firstJump_survival (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) (t : ℝ) :
    (∫ ω, (∫ s in 0..t, if ENNReal.ofReal s < τ ω then (1 : ℝ) else 0) ∂μ) =
      ∫ s in 0..t, μ.real {ω | ENNReal.ofReal s < τ ω} := by
  let : IsFiniteMeasure (volume.restrict (uIoc 0 t)) := ⟨by simp [Real.volume_uIoc]⟩
  have hm : Measurable (fun p : ℝ × Ω ↦
      if ENNReal.ofReal p.1 < τ p.2 then (1 : ℝ) else 0) := by
    exact measurable_const.ite
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hτ.comp measurable_snd)) measurable_const
  have hi : Integrable (fun p : ℝ × Ω ↦
      if ENNReal.ofReal p.1 < τ p.2 then (1 : ℝ) else 0)
      ((volume.restrict (uIoc 0 t)).prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall fun p ↦ by split_ifs <;> norm_num)
  rw [← intervalIntegral_integral_swap hi]
  apply intervalIntegral.integral_congr
  intro s _
  have hs : MeasurableSet {ω | ENNReal.ofReal s < τ ω} :=
    measurableSet_lt measurable_const hτ
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := μ) (s := {ω | ENNReal.ofReal s < τ ω}) (1 : ℝ) hs

/-- Zero means of the integrable first-jump compensators identify the entire attained law.
This form is useful after optional stopping an original marked-count martingale. -/
theorem attainedFirstJumpLaw_eq_of_zero_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    (hInt : ∀ B, MeasurableSet B → ∀ t,
      Integrable (firstJumpCompensator r π τ J B t) μ)
    (hmean : ∀ B, MeasurableSet B → ∀ t,
      (∫ ω, firstJumpCompensator r π τ J B t ω ∂μ) = 0) :
    attainedFirstJumpLaw μ τ J = (expMeasure r).prod π := by
  apply markedWaitingLaw_eq_of_compensator _ π hr
  intro t ht B hB
  let tNN : ℝ≥0 := Real.toNNReal t
  have htNN : (tNN : ℝ) = t := Real.coe_toNNReal t ht
  have hc : Integrable (fun ω ↦ if τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B
      then (1 : ℝ) else 0) μ := by
    have hmc : Measurable (fun ω ↦ if τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B
        then (1 : ℝ) else 0) :=
      measurable_const.ite
        ((measurableSet_le hτ measurable_const).inter (hJ hB))
        measurable_const
    apply Integrable.of_bound hmc.aestronglyMeasurable 1
    exact Eventually.of_forall fun ω ↦ by split_ifs <;> norm_num
  have hi := hmean B hB tNN
  have hiocc : Integrable (fun ω ↦ r * π.real B *
      ∫ s in 0..t, if ENNReal.ofReal s < τ ω then (1 : ℝ) else 0) μ := by
    have := hc.sub (hInt B hB tNN)
    convert this using 1
    funext ω
    simp only [Pi.sub_apply, firstJumpCompensator, htNN]
    ring
  have hmean :
      μ.real {ω | τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B} =
        r * π.real B * ∫ s in 0..t, μ.real {ω | ENNReal.ofReal s < τ ω} := by
    simp only [firstJumpCompensator, htNN] at hi
    rw [integral_sub hc hiocc, integral_const_mul,
      integral_firstJump_survival μ hτ] at hi
    have hset : MeasurableSet {ω | τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B} :=
      (measurableSet_le hτ measurable_const).inter (hJ hB)
    have hcount : (∫ ω, if τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B
        then (1 : ℝ) else 0 ∂μ) = μ.real {ω | τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B} := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := μ) (1 : ℝ) hset
    rw [hcount] at hi
    linarith
  rw [measureReal_def, attainedFirstJumpLaw_Iic μ hτ hJ ht hB]
  change μ.real {ω | τ ω ≤ ENNReal.ofReal t ∧ J ω ∈ B} = _
  rw [hmean]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le ht ▸ hs).1
  change μ.real {ω | ENNReal.ofReal s < τ ω} =
    1 - (attainedFirstJumpLaw μ τ J (Iic s ×ˢ univ)).toReal
  rw [attainedFirstJumpLaw_Iic μ hτ hJ hs0 MeasurableSet.univ]
  simp only [mem_univ, and_true]
  have hcompl : {ω | ENNReal.ofReal s < τ ω} = {ω | τ ω ≤ ENNReal.ofReal s}ᶜ := by
    ext ω
    simp
  rw [hcompl, probReal_compl_eq_one_sub (measurableSet_le hτ measurable_const)]
  rfl

/-- The explicit one-jump martingale problem forces the exponential marked holding law.
An infinite first wait is allowed in the input and excluded by the conclusion. -/
theorem attainedFirstJumpLaw_eq_of_martingale (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (hτ0 : ∀ᵐ ω ∂μ, 0 < τ ω) (π : Measure E) [IsProbabilityMeasure π]
    {r : ℝ} (hr : 0 < r) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hM : ∀ B, MeasurableSet B → Martingale (firstJumpCompensator r π τ J B) ℱ μ) :
    attainedFirstJumpLaw μ τ J = (expMeasure r).prod π := by
  apply attainedFirstJumpLaw_eq_of_zero_mean μ hτ hJ π hr
    (fun B hB t ↦ (hM B hB).integrable t)
  intro B hB t
  have hzero : firstJumpCompensator r π τ J B 0 =ᵐ[μ] 0 := by
    filter_upwards [hτ0] with ω hω
    simp [firstJumpCompensator, not_le.mpr hω]
  have he := (hM B hB).setIntegral_eq (i := 0) (j := t) zero_le
    MeasurableSet.univ
  simpa [setIntegral_univ, integral_congr_ae hzero] using he.symm

/-- The model-specific first-jump martingale problem identifies the feedback holding kernel and
rules out an infinite waiting coordinate. -/
theorem feedbackMarkedHoldingKernel_eq_of_firstJump_martingale {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → ℝ≥0∞} {J : Ω → UnitMark × ℤ} (hτ : Measurable τ) (hJ : Measurable J)
    (hτ0 : ∀ᵐ ω ∂μ, 0 < τ ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hM : ∀ B, MeasurableSet B →
      Martingale (firstJumpCompensator (totalJumpRate lam k)
        (feedbackMarkedJumpKernel lam k) τ J B) ℱ μ) :
    attainedFirstJumpLaw μ τ J = feedbackMarkedHoldingKernel lam k ∧
      ∀ᵐ ω ∂μ, τ ω ≠ ∞ := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  have heq : attainedFirstJumpLaw μ τ J = feedbackMarkedHoldingKernel lam k :=
    attainedFirstJumpLaw_eq_of_martingale μ hτ hJ hτ0 (feedbackMarkedJumpKernel lam k)
      (totalJumpRate_pos hlam0 hlam k) ℱ hM
  refine ⟨heq, ?_⟩
  have hu : attainedFirstJumpLaw μ τ J univ = 1 := by rw [heq]; exact measure_univ
  rw [attainedFirstJumpLaw, Measure.map_apply (hτ.ennreal_toReal.prodMk hJ)
    MeasurableSet.univ] at hu
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hu
  exact (mem_ae_iff_prob_eq_one ((hτ (measurableSet_singleton ∞)).compl)).mpr hu

end OTSelector.Limit
