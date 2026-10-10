import OTSelector.Limit.FeedbackRegeneration
import OTSelector.Basic.ModelLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Actual marks at feedback jumps

The source and target mark intensities are finite measures on the unit interval.
Their masses are the previously constructed birth and death rates. Dividing their
sum by the total rate gives the marked jump law; forgetting the mark recovers the
actual nearest-neighbor jump kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Limit

private theorem integrable_unitMark : Integrable (fun u : UnitMark ↦ (u : ℝ)) volume := by
  apply Integrable.of_bound continuous_subtype_val.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg u.2.1]
    exact u.2.2

private theorem integral_unitMark : (∫ u : UnitMark, (u : ℝ)) = 1 / 2 := by
  change (∫ u : Icc (0 : ℝ) 1, id (u : ℝ) ∂volume.comap Subtype.val) = _
  rw [integral_subtype_comap measurableSet_Icc id, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  norm_num

theorem integrable_sourceMarkDensity (lam : ℝ) (k : ℤ) :
    Integrable (fun u : UnitMark ↦ sourceMarkDensity lam k u) volume :=
  (integrable_const 1).sub (((integrable_const 1).sub integrable_unitMark).const_mul _)

theorem integrable_targetMarkDensity (lam : ℝ) (k : ℤ) :
    Integrable (fun u : UnitMark ↦ targetMarkDensity lam k u) volume :=
  (integrable_const 1).add (((integrable_const 1).add integrable_unitMark).const_mul _)

theorem integral_sourceMarkDensity (lam : ℝ) (k : ℤ) :
    (∫ u : UnitMark, sourceMarkDensity lam k u) = birthRate lam k := by
  change (∫ u : UnitMark, (1 : ℝ) - (lam * currentSign k) * (1 - (u : ℝ))) = _
  have hsub := integral_sub (integrable_const (1 : ℝ) : Integrable (fun _ : UnitMark ↦ (1 : ℝ)))
    (((integrable_const 1).sub integrable_unitMark).const_mul (lam * currentSign k))
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_const_mul]
  have hsub' := integral_sub (integrable_const (1 : ℝ)) integrable_unitMark
  rw [hsub', integral_unitMark]
  simp only [integral_const, probReal_univ, one_smul]
  unfold birthRate
  ring

theorem integral_targetMarkDensity (lam : ℝ) (k : ℤ) :
    (∫ u : UnitMark, targetMarkDensity lam k u) = deathRate lam k := by
  change (∫ u : UnitMark, (1 : ℝ) + (lam * currentSign k) * (1 + (u : ℝ))) = _
  have hadd := integral_add (integrable_const (1 : ℝ) : Integrable (fun _ : UnitMark ↦ (1 : ℝ)))
    (((integrable_const 1).add integrable_unitMark).const_mul (lam * currentSign k))
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_const_mul]
  have hadd' := integral_add (integrable_const (1 : ℝ)) integrable_unitMark
  rw [hadd', integral_unitMark]
  simp only [integral_const, probReal_univ, one_smul]
  unfold deathRate
  ring

theorem sourceMarkDensity_nonneg {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (u : UnitMark) : 0 ≤ sourceMarkDensity lam k u := by
  rcases k with (n | n)
  · rcases n with (_ | n)
    · simp [sourceMarkDensity, currentSign]
    · simp only [sourceMarkDensity, currentSign]
      nlinarith [u.2.1, u.2.2]
  · simp only [sourceMarkDensity, currentSign]
    nlinarith [u.2.1, u.2.2]

theorem targetMarkDensity_nonneg {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (u : UnitMark) : 0 ≤ targetMarkDensity lam k u := by
  rcases k with (n | n)
  · rcases n with (_ | n)
    · simp [targetMarkDensity, currentSign]
    · simp only [targetMarkDensity, currentSign]
      nlinarith [u.2.1, u.2.2]
  · simp only [targetMarkDensity, currentSign]
    nlinarith [u.2.1, u.2.2]

noncomputable def sourceMarkRateMeasure (lam : ℝ) (k : ℤ) : Measure UnitMark :=
  volume.withDensity fun u ↦ ENNReal.ofReal (sourceMarkDensity lam k u)

noncomputable def targetMarkRateMeasure (lam : ℝ) (k : ℤ) : Measure UnitMark :=
  volume.withDensity fun u ↦ ENNReal.ofReal (targetMarkDensity lam k u)

theorem sourceMarkRateMeasure_univ {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    sourceMarkRateMeasure lam k univ = ENNReal.ofReal (birthRate lam k) := by
  rw [sourceMarkRateMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sourceMarkDensity lam k)
      (Filter.Eventually.of_forall (sourceMarkDensity_nonneg hlam0 hlam k)),
    integral_sourceMarkDensity]

theorem targetMarkRateMeasure_univ {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    targetMarkRateMeasure lam k univ = ENNReal.ofReal (deathRate lam k) := by
  rw [targetMarkRateMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_targetMarkDensity lam k)
      (Filter.Eventually.of_forall (targetMarkDensity_nonneg hlam0 hlam k)),
    integral_targetMarkDensity]

/-- The actual marked next jump: its mark and the resulting neighboring current. -/
noncomputable def feedbackMarkedJumpKernel (lam : ℝ) : Kernel ℤ (UnitMark × ℤ) where
  toFun k := (ENNReal.ofReal (totalJumpRate lam k))⁻¹ •
    ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
      (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))
  measurable' := measurable_of_countable _

theorem feedbackMarkedJumpKernel_isMarkov {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackMarkedJumpKernel lam) := by
  constructor
  intro k
  constructor
  simp only [feedbackMarkedJumpKernel, Kernel.coe_mk, Measure.smul_apply,
    Measure.add_apply, Measure.map_apply measurable_prodMk_right MeasurableSet.univ,
    preimage_univ, smul_eq_mul]
  rw [sourceMarkRateMeasure_univ hlam0 hlam, targetMarkRateMeasure_univ hlam0 hlam,
    ← ENNReal.ofReal_add (birthRate_nonneg hlam0 hlam k) (deathRate_nonneg hlam0 hlam k)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
    (totalJumpRate_pos hlam0 hlam k)) ENNReal.ofReal_ne_top

/-- Forgetting the mark recovers the actual embedded feedback jump law. -/
theorem feedbackMarkedJumpKernel_map_current {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedJumpKernel lam k).map Prod.snd = feedbackJumpKernel lam k := by
  change (((ENNReal.ofReal (totalJumpRate lam k))⁻¹) •
    ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
      (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))).map Prod.snd = _
  rw [Measure.map_smul, Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd measurable_prodMk_right,
    Measure.map_map measurable_snd measurable_prodMk_right]
  simp only [Function.comp_def, Measure.map_const,
    sourceMarkRateMeasure_univ hlam0 hlam, targetMarkRateMeasure_univ hlam0 hlam,
    smul_add, smul_smul]
  simp only [feedbackJumpKernel, Kernel.coe_mk, jumpUpProbability, jumpDownProbability]
  rw [ENNReal.ofReal_div_of_pos (totalJumpRate_pos hlam0 hlam k),
    ENNReal.ofReal_div_of_pos (totalJumpRate_pos hlam0 hlam k)]
  simp only [div_eq_mul_inv, mul_comm]

/-- The same forgetting identity at the level of transition kernels. -/
theorem feedbackMarkedJumpKernel_map_snd {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedJumpKernel lam).map Prod.snd = feedbackJumpKernel lam := by
  ext k s hs
  rw [Kernel.map_apply _ measurable_snd, feedbackMarkedJumpKernel_map_current hlam0 hlam]

@[simp]
theorem sourceMarkRateMeasure_zero (lam : ℝ) : sourceMarkRateMeasure lam 0 = volume := by
  simp [sourceMarkRateMeasure, sourceMarkDensity, currentSign]

@[simp]
theorem targetMarkRateMeasure_zero (lam : ℝ) : targetMarkRateMeasure lam 0 = volume := by
  simp [targetMarkRateMeasure, targetMarkDensity, currentSign]

/-- At zero the joint law factors: the jump mark is uniform and independent of its direction. -/
theorem feedbackMarkedJumpKernel_zero (lam : ℝ) :
    feedbackMarkedJumpKernel lam 0 =
      (volume : Measure UnitMark).prod (feedbackJumpKernel lam 0) := by
  simp [feedbackMarkedJumpKernel, feedbackJumpKernel, Measure.prod_add,
    Measure.prod_smul_right, Measure.prod_dirac, smul_add]

/-- A jump out of zero has the original uniform mark law. -/
theorem feedbackMarkedJumpKernel_zero_map_mark {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedJumpKernel lam 0).map Prod.fst = (unitUniform : Measure UnitMark) := by
  let := feedbackJumpKernel_isMarkov hlam0 hlam
  rw [feedbackMarkedJumpKernel_zero]
  simp [unitUniform]

/-- Uniformity at zero holds jointly with independence from the new current. -/
theorem feedbackMarkedJumpKernel_zero_indep {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun Prod.fst Prod.snd (feedbackMarkedJumpKernel lam 0) := by
  let := feedbackJumpKernel_isMarkov hlam0 hlam
  rw [feedbackMarkedJumpKernel_zero]
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

end OTSelector.Limit
