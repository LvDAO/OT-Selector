import OTSelector.Limit.FeedbackInvariant
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Invariance

/-!
# Actual jump and holding laws for the feedback current

The embedded nearest-neighbor jump kernel is constructed from the rates of
`FeedbackInvariant`. Its stationary mass is the continuous-time mass multiplied by the total
jump rate and divided by two. The waiting law at current `k` is exponential with that total rate.
These constructions are inputs for the trajectory and regenerative-cell construction; no return,
nonexplosion, or spatial-stationarity assertion is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Limit

/-- The total feedback jump rate. It is not constant off zero. -/
noncomputable def totalJumpRate (lam : ℝ) (k : ℤ) : ℝ :=
  birthRate lam k + deathRate lam k

@[simp]
theorem totalJumpRate_eq (lam : ℝ) (k : ℤ) :
    totalJumpRate lam k = 2 + lam * currentSign k := by
  unfold totalJumpRate birthRate deathRate
  ring

@[simp]
theorem totalJumpRate_zero (lam : ℝ) : totalJumpRate lam 0 = 2 := by simp

@[simp]
theorem totalJumpRate_positive (lam : ℝ) (n : ℕ) :
    totalJumpRate lam ((n : ℤ) + 1) = 2 + lam := by simp

@[simp]
theorem totalJumpRate_negative (lam : ℝ) (n : ℕ) :
    totalJumpRate lam (-((n : ℤ) + 1)) = 2 - lam := by
  rw [totalJumpRate_eq, currentSign_neg_nat_add_one]
  ring

/-- Uniform bounds on the actual total jump rate. -/
theorem totalJumpRate_bounds {lam : ℝ} (hlam₀ : 0 < lam) (k : ℤ) :
    2 - lam ≤ totalJumpRate lam k ∧ totalJumpRate lam k ≤ 2 + lam := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simpa using hlam₀.le
      | succ n => simp [totalJumpRate, birthRate, deathRate, currentSign]; constructor <;> linarith
  | negSucc n =>
      simp [totalJumpRate, birthRate, deathRate, currentSign]
      constructor <;> linarith

theorem totalJumpRate_pos {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 < totalJumpRate lam k := by
  have := (totalJumpRate_bounds hlam₀ k).1
  linarith

/-- Probability of an upward step in the embedded jump chain. -/
noncomputable def jumpUpProbability (lam : ℝ) (k : ℤ) : ℝ :=
  birthRate lam k / totalJumpRate lam k

/-- Probability of a downward step in the embedded jump chain. -/
noncomputable def jumpDownProbability (lam : ℝ) (k : ℤ) : ℝ :=
  deathRate lam k / totalJumpRate lam k

theorem jumpUpProbability_nonneg {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : 0 ≤ jumpUpProbability lam k :=
  div_nonneg (birthRate_nonneg hlam₀ hlam k) (totalJumpRate_pos hlam₀ hlam k).le

theorem jumpDownProbability_nonneg {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : 0 ≤ jumpDownProbability lam k :=
  div_nonneg (deathRate_nonneg hlam₀ hlam k) (totalJumpRate_pos hlam₀ hlam k).le

theorem jumpProbabilities_sum {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    jumpUpProbability lam k + jumpDownProbability lam k = 1 := by
  rw [jumpUpProbability, jumpDownProbability, ← add_div]
  exact div_self (ne_of_gt (totalJumpRate_pos hlam₀ hlam k))

@[simp]
theorem jumpUpProbability_zero (lam : ℝ) : jumpUpProbability lam 0 = 1 / 2 := by
  simp [jumpUpProbability, birthRate]

@[simp]
theorem jumpDownProbability_zero (lam : ℝ) : jumpDownProbability lam 0 = 1 / 2 := by
  simp [jumpDownProbability, deathRate]

/-- A positive excursion has a strict bias toward zero. -/
theorem jumpUpProbability_positive_lt_half {lam : ℝ} (hlam₀ : 0 < lam) (n : ℕ) :
    jumpUpProbability lam ((n : ℤ) + 1) < 1 / 2 := by
  rw [jumpUpProbability, totalJumpRate_positive]
  simp only [birthRate, currentSign_nat_add_one, mul_one]
  apply (div_lt_iff₀ (by linarith : 0 < 2 + lam)).mpr
  linarith

/-- A negative excursion also has a strict bias toward zero, with its different total rate. -/
theorem jumpDownProbability_negative_lt_half {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    jumpDownProbability lam (-((n : ℤ) + 1)) < 1 / 2 := by
  rw [jumpDownProbability, totalJumpRate_negative]
  simp only [deathRate, currentSign_neg_nat_add_one, mul_neg_one]
  apply (div_lt_iff₀ (by linarith : 0 < 2 - lam)).mpr
  linarith

/-- The real feedback jump kernel, with no artificial self-loops. -/
noncomputable def feedbackJumpKernel (lam : ℝ) : Kernel ℤ ℤ where
  toFun k := ENNReal.ofReal (jumpUpProbability lam k) • Measure.dirac (k + 1) +
    ENNReal.ofReal (jumpDownProbability lam k) • Measure.dirac (k - 1)
  measurable' := measurable_of_countable _

theorem feedbackJumpKernel_apply (lam : ℝ) (k : ℤ) (s : Set ℤ) :
    feedbackJumpKernel lam k s =
      ENNReal.ofReal (jumpUpProbability lam k) * s.indicator (fun _ ↦ 1) (k + 1) +
      ENNReal.ofReal (jumpDownProbability lam k) * s.indicator (fun _ ↦ 1) (k - 1) := by
  simp [feedbackJumpKernel, Measure.dirac_apply', Set.indicator]

/-- Every row is a probability measure in the actual parameter range. -/
theorem feedbackJumpKernel_isMarkov {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackJumpKernel lam) := by
  constructor
  intro k
  constructor
  simp only [feedbackJumpKernel, Kernel.coe_mk, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (jumpUpProbability_nonneg hlam₀ hlam k)
    (jumpDownProbability_nonneg hlam₀ hlam k), jumpProbabilities_sum hlam₀ hlam k]
  norm_num

/-- Every step is to one of the two neighboring currents. -/
theorem feedbackJumpKernel_neighbors {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    feedbackJumpKernel lam k {k + 1, k - 1} = 1 := by
  rw [feedbackJumpKernel_apply]
  simp only [Set.indicator_of_mem (by simp : k + 1 ∈ ({k + 1, k - 1} : Set ℤ)),
    Set.indicator_of_mem (by simp : k - 1 ∈ ({k + 1, k - 1} : Set ℤ)), mul_one]
  rw [← ENNReal.ofReal_add (jumpUpProbability_nonneg hlam₀ hlam k)
    (jumpDownProbability_nonneg hlam₀ hlam k), jumpProbabilities_sum hlam₀ hlam k]
  norm_num

/-- Rate bias of the spatial current mass at jump times. -/
noncomputable def jumpInvariantMass (lam : ℝ) (k : ℤ) : ℝ :=
  invariantMass lam k * totalJumpRate lam k / 2

theorem jumpInvariantMass_eq (lam : ℝ) (k : ℤ) :
    jumpInvariantMass lam k = invariantMass lam k + lam / 2 * signedMass lam k := by
  simp only [jumpInvariantMass, totalJumpRate_eq, signedMass]
  ring

theorem jumpInvariantMass_nonneg {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : 0 ≤ jumpInvariantMass lam k :=
  div_nonneg (mul_nonneg (invariantMass_nonneg hlam₀ hlam k)
    (totalJumpRate_pos hlam₀ hlam k).le) (by norm_num)

theorem summable_jumpInvariantMass {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    Summable (jumpInvariantMass lam) := by
  exact ((summable_invariantMass hlam₀ hlam).add
    ((summable_signedMass hlam₀ hlam).mul_left (lam / 2))).congr
      fun k ↦ (jumpInvariantMass_eq lam k).symm

/-- The total rate bias is exactly two, so the embedded mass is normalized. -/
theorem tsum_jumpInvariantMass {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    ∑' k : ℤ, jumpInvariantMass lam k = 1 := by
  simp only [jumpInvariantMass_eq]
  rw [Summable.tsum_add (summable_invariantMass hlam₀ hlam)
    ((summable_signedMass hlam₀ hlam).mul_left (lam / 2)), tsum_mul_left,
    tsum_invariantMass hlam₀ hlam, tsum_signedMass hlam₀ hlam]
  ring

/-- The probability law of current at a stationary jump time. -/
noncomputable def jumpInvariantMeasure (lam : ℝ) : Measure ℤ :=
  Measure.count.withDensity fun k ↦ ENNReal.ofReal (jumpInvariantMass lam k)

theorem jumpInvariantMeasure_isProbability {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure (jumpInvariantMeasure lam) := by
  constructor
  rw [jumpInvariantMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_count]
  rw [← ENNReal.ofReal_tsum_of_nonneg (jumpInvariantMass_nonneg hlam₀ hlam)
    (summable_jumpInvariantMass hlam₀ hlam), tsum_jumpInvariantMass hlam₀ hlam]
  norm_num

/-- Detailed balance for the normalized embedded chain. -/
theorem jump_detailed_balance {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    jumpInvariantMass lam k * jumpUpProbability lam k =
      jumpInvariantMass lam (k + 1) * jumpDownProbability lam (k + 1) := by
  unfold jumpInvariantMass jumpUpProbability jumpDownProbability
  have hk := ne_of_gt (totalJumpRate_pos hlam₀ hlam k)
  have hk' := ne_of_gt (totalJumpRate_pos hlam₀ hlam (k + 1))
  field_simp
  nlinarith [detailed_balance hlam₀ hlam k]

/-- The embedded law satisfies global balance at every current. -/
theorem jump_global_balance {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    jumpInvariantMass lam (k - 1) * jumpUpProbability lam (k - 1) +
      jumpInvariantMass lam (k + 1) * jumpDownProbability lam (k + 1) =
        jumpInvariantMass lam k := by
  have hleft := jump_detailed_balance hlam₀ hlam (k - 1)
  have hright := jump_detailed_balance hlam₀ hlam k
  simp only [sub_add_cancel] at hleft
  rw [hleft, ← hright, ← mul_add, add_comm (jumpDownProbability lam k),
    jumpProbabilities_sum hlam₀ hlam k, mul_one]

@[simp]
theorem jumpInvariantMeasure_singleton (lam : ℝ) (k : ℤ) :
    jumpInvariantMeasure lam {k} = ENNReal.ofReal (jumpInvariantMass lam k) := by
  rw [jumpInvariantMeasure, withDensity_apply _ (measurableSet_singleton k),
    lintegral_singleton]
  simp

/-- The rate-biased probability law is invariant under the actual jump kernel. -/
theorem feedbackJumpKernel_invariant {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackJumpKernel lam).Invariant (jumpInvariantMeasure lam) := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.bind_apply (measurableSet_singleton k) (Kernel.aemeasurable _),
    lintegral_countable', jumpInvariantMeasure_singleton]
  simp only [jumpInvariantMeasure_singleton]
  have hterm (i : ℤ) :
      feedbackJumpKernel lam i {k} * ENNReal.ofReal (jumpInvariantMass lam i) =
        (if i = k - 1 then ENNReal.ofReal
          (jumpInvariantMass lam i * jumpUpProbability lam i) else 0) +
        (if i = k + 1 then ENNReal.ofReal
          (jumpInvariantMass lam i * jumpDownProbability lam i) else 0) := by
    rw [feedbackJumpKernel_apply]
    have hu : i + 1 = k ↔ i = k - 1 := by omega
    have hd : i - 1 = k ↔ i = k + 1 := by omega
    simp only [Set.indicator, Set.mem_singleton_iff, hu, hd,
      add_mul, ENNReal.ofReal_mul (jumpInvariantMass_nonneg hlam₀ hlam i)]
    split_ifs <;> simp_all [mul_comm]
  simp_rw [hterm]
  rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq,
    ← ENNReal.ofReal_add
      (mul_nonneg (jumpInvariantMass_nonneg hlam₀ hlam _)
        (jumpUpProbability_nonneg hlam₀ hlam _))
      (mul_nonneg (jumpInvariantMass_nonneg hlam₀ hlam _)
        (jumpDownProbability_nonneg hlam₀ hlam _)), jump_global_balance hlam₀ hlam]

/-- Dividing the jump-time mass by its rate recovers the spatial mass. -/
theorem jumpInvariantMass_div_rate {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    2 * jumpInvariantMass lam k / totalJumpRate lam k = invariantMass lam k := by
  unfold jumpInvariantMass
  field_simp [ne_of_gt (totalJumpRate_pos hlam₀ hlam k)]
  exact mul_div_cancel_right₀ _ (ne_of_gt (totalJumpRate_pos hlam₀ hlam k))

/-- Exponential waiting law at each actual current. -/
noncomputable def feedbackHoldingKernel (lam : ℝ) : Kernel ℤ ℝ where
  toFun k := expMeasure (totalJumpRate lam k)
  measurable' := measurable_of_countable _

theorem feedbackHoldingKernel_isMarkov {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackHoldingKernel lam) :=
  ⟨fun k ↦ isProbabilityMeasure_expMeasure (totalJumpRate_pos hlam₀ hlam k)⟩

/-- In particular the initial zero hold is a genuine rate-two exponential law. -/
@[simp]
theorem feedbackHoldingKernel_zero (lam : ℝ) :
    feedbackHoldingKernel lam 0 = expMeasure 2 := by
  simp [feedbackHoldingKernel]

end OTSelector.Limit
