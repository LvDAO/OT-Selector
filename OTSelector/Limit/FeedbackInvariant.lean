import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The invariant current law of the limiting feedback environment

This file proves the deterministic summation and balance identities for the stationary feedback current
in `main.tex`.  The invariant mass is given explicitly on the two integer tails.  Mathlib's
integer-indexed summation decomposition and geometric-series theorem then give normalization,
detailed balance, zero mean sign, and the uniform stationary mark densities.

The construction contains no martingale-problem, path-law, or environment-tightness assertion.
Those are separate probabilistic parts of ENV.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace OTSelector.Limit

/-- The real-valued sign of an integer current. -/
def currentSign : ℤ → ℝ
  | .ofNat 0 => 0
  | .ofNat (_ + 1) => 1
  | .negSucc _ => -1

/-- The upward jump rate in (3.1). -/
noncomputable def birthRate (lam : ℝ) (k : ℤ) : ℝ :=
  1 - lam / 2 * currentSign k

/-- The downward jump rate in (3.1). -/
noncomputable def deathRate (lam : ℝ) (k : ℤ) : ℝ :=
  1 + 3 * lam / 2 * currentSign k

/-- The mass at current zero in (3.5). -/
noncomputable def centralMass (lam : ℝ) : ℝ :=
  lam / (1 + lam)

/-- The geometric ratio of the positive tail in (3.6). -/
noncomputable def positiveRatio (lam : ℝ) : ℝ :=
  (1 - lam / 2) / (1 + 3 * lam / 2)

/-- The geometric ratio of the negative tail in (3.7). -/
noncomputable def negativeRatio (lam : ℝ) : ℝ :=
  (1 - 3 * lam / 2) / (1 + lam / 2)

/-- The explicit invariant current mass from (3.5)--(3.7). -/
noncomputable def invariantMass (lam : ℝ) : ℤ → ℝ
  | .ofNat 0 => centralMass lam
  | .ofNat (n + 1) =>
      centralMass lam / (1 + 3 * lam / 2) * positiveRatio lam ^ n
  | .negSucc n =>
      centralMass lam / (1 + lam / 2) * negativeRatio lam ^ n

/-- Signed invariant mass, named separately to keep integer-tail summation reducible. -/
noncomputable def signedMass (lam : ℝ) (k : ℤ) : ℝ :=
  invariantMass lam k * currentSign k

@[simp]
theorem currentSign_nat_add_one (n : ℕ) : currentSign ((n : ℤ) + 1) = 1 := by
  change currentSign (.ofNat (n + 1)) = 1
  simp [currentSign]

@[simp]
theorem currentSign_neg_nat_add_one (n : ℕ) : currentSign (-((n : ℤ) + 1)) = -1 := by
  change currentSign (.negSucc n) = -1
  rfl

@[simp]
theorem invariantMass_nat_add_one (lam : ℝ) (n : ℕ) :
    invariantMass lam ((n : ℤ) + 1) =
      centralMass lam / (1 + 3 * lam / 2) * positiveRatio lam ^ n := by
  change invariantMass lam (.ofNat (n + 1)) = _
  rfl

@[simp]
theorem invariantMass_neg_nat_add_one (lam : ℝ) (n : ℕ) :
    invariantMass lam (-((n : ℤ) + 1)) =
      centralMass lam / (1 + lam / 2) * negativeRatio lam ^ n := by
  change invariantMass lam (.negSucc n) = _
  rfl

@[simp]
theorem currentSign_neg_one : currentSign (-1) = -1 := by
  change currentSign (.negSucc 0) = -1
  rfl

@[simp]
theorem currentSign_zero : currentSign 0 = 0 :=
  rfl

@[simp]
theorem invariantMass_neg_one (lam : ℝ) :
    invariantMass lam (-1) = centralMass lam / (1 + lam / 2) := by
  change invariantMass lam (.negSucc 0) = _
  simp [invariantMass]

@[simp]
theorem invariantMass_zero (lam : ℝ) : invariantMass lam 0 = centralMass lam :=
  rfl

@[simp]
theorem signedMass_nat_add_one (lam : ℝ) (n : ℕ) :
    signedMass lam ((n : ℤ) + 1) = invariantMass lam ((n : ℤ) + 1) := by
  simp [signedMass]

@[simp]
theorem signedMass_neg_nat_add_one (lam : ℝ) (n : ℕ) :
    signedMass lam (-((n : ℤ) + 1)) = -invariantMass lam (-((n : ℤ) + 1)) := by
  rw [signedMass, currentSign_neg_nat_add_one]
  ring

@[simp]
theorem signedMass_zero (lam : ℝ) : signedMass lam 0 = 0 := by
  simp [signedMass]

/-- The source-mark density in (3.2), before normalization by the jump rate. -/
def sourceMarkDensity (lam : ℝ) (k : ℤ) (u : ℝ) : ℝ :=
  1 - lam * currentSign k * (1 - u)

/-- The target-mark density in (3.3), before normalization by the jump rate. -/
def targetMarkDensity (lam : ℝ) (k : ℤ) (v : ℝ) : ℝ :=
  1 + lam * currentSign k * (1 + v)

section ParameterRange

variable {lam : ℝ}

private theorem positive_denominator_pos (hlam₀ : 0 < lam) : 0 < 1 + 3 * lam / 2 := by
  nlinarith

private theorem negative_denominator_pos (hlam₀ : 0 < lam) : 0 < 1 + lam / 2 := by
  nlinarith

private theorem positiveRatio_nonneg (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    0 ≤ positiveRatio lam := by
  rw [positiveRatio]
  apply div_nonneg
  · nlinarith
  · exact (positive_denominator_pos hlam₀).le

private theorem positiveRatio_lt_one (hlam₀ : 0 < lam) (_hlam : lam < 1 / 2) :
    positiveRatio lam < 1 := by
  rw [positiveRatio, div_lt_one (positive_denominator_pos hlam₀)]
  nlinarith

private theorem negativeRatio_nonneg (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    0 ≤ negativeRatio lam := by
  rw [negativeRatio]
  apply div_nonneg
  · nlinarith
  · exact (negative_denominator_pos hlam₀).le

private theorem negativeRatio_lt_one (hlam₀ : 0 < lam) (_hlam : lam < 1 / 2) :
    negativeRatio lam < 1 := by
  rw [negativeRatio, div_lt_one (negative_denominator_pos hlam₀)]
  nlinarith

/-- Every upward jump rate is nonnegative in the paper's parameter range. -/
theorem birthRate_nonneg (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 ≤ birthRate lam k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp [birthRate, currentSign]
      | succ n =>
          simp only [birthRate, currentSign]
          nlinarith
  | negSucc n =>
      simp only [birthRate, currentSign]
      nlinarith

/-- Every downward jump rate is nonnegative in the paper's parameter range. -/
theorem deathRate_nonneg (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 ≤ deathRate lam k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => simp [deathRate, currentSign]
      | succ n =>
          simp only [deathRate, currentSign]
          nlinarith
  | negSucc n =>
      simp only [deathRate, currentSign]
      nlinarith

/-- Every invariant current mass is nonnegative in the paper's parameter range. -/
theorem invariantMass_nonneg (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 ≤ invariantMass lam k := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          simp only [invariantMass, centralMass]
          positivity
      | succ n =>
          simp only [invariantMass]
          exact mul_nonneg (div_nonneg (by simp [centralMass]; positivity)
            (positive_denominator_pos hlam₀).le) (pow_nonneg (positiveRatio_nonneg hlam₀ hlam) _)
  | negSucc n =>
      simp only [invariantMass]
      exact mul_nonneg (div_nonneg (by simp [centralMass]; positivity)
        (negative_denominator_pos hlam₀).le) (pow_nonneg (negativeRatio_nonneg hlam₀ hlam) _)

/-- The positive tail is summable. -/
theorem summable_positive_tail (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    Summable fun n : ℕ ↦ invariantMass lam (n + 1) := by
  simpa only [invariantMass_nat_add_one] using
    (summable_geometric_of_lt_one (positiveRatio_nonneg hlam₀ hlam)
      (positiveRatio_lt_one hlam₀ hlam)).mul_left
      (centralMass lam / (1 + 3 * lam / 2))

/-- The negative tail is summable. -/
theorem summable_negative_tail (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    Summable fun n : ℕ ↦ invariantMass lam (-(n + 1)) := by
  simpa only [invariantMass_neg_nat_add_one] using
    (summable_geometric_of_lt_one (negativeRatio_nonneg hlam₀ hlam)
      (negativeRatio_lt_one hlam₀ hlam)).mul_left
      (centralMass lam / (1 + lam / 2))

/-- The positive tail has the mass stated in the ENV proof. -/
theorem tsum_positive_tail (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    ∑' n : ℕ, invariantMass lam (n + 1) = centralMass lam / (2 * lam) := by
  rw [show (∑' n : ℕ, invariantMass lam (n + 1)) =
      centralMass lam / (1 + 3 * lam / 2) *
        ∑' n : ℕ, positiveRatio lam ^ n by
    simp only [invariantMass_nat_add_one, tsum_mul_left]]
  rw [tsum_geometric_of_lt_one (positiveRatio_nonneg hlam₀ hlam)
    (positiveRatio_lt_one hlam₀ hlam)]
  have hgap : 1 - positiveRatio lam = (2 * lam) / (1 + 3 * lam / 2) := by
    rw [positiveRatio]
    field_simp [ne_of_gt (positive_denominator_pos hlam₀)]
    ring
  rw [hgap, centralMass]
  field_simp [ne_of_gt hlam₀, ne_of_gt (positive_denominator_pos hlam₀)]

/-- The negative tail has the same mass as the positive tail. -/
theorem tsum_negative_tail (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    ∑' n : ℕ, invariantMass lam (-(n + 1)) = centralMass lam / (2 * lam) := by
  rw [show (∑' n : ℕ, invariantMass lam (-(n + 1))) =
      centralMass lam / (1 + lam / 2) *
        ∑' n : ℕ, negativeRatio lam ^ n by
    simp only [invariantMass_neg_nat_add_one, tsum_mul_left]]
  rw [tsum_geometric_of_lt_one (negativeRatio_nonneg hlam₀ hlam)
    (negativeRatio_lt_one hlam₀ hlam)]
  have hgap : 1 - negativeRatio lam = (2 * lam) / (1 + lam / 2) := by
    rw [negativeRatio]
    field_simp [ne_of_gt (negative_denominator_pos hlam₀)]
    ring
  rw [hgap, centralMass]
  field_simp [ne_of_gt hlam₀, ne_of_gt (negative_denominator_pos hlam₀)]

/-- The explicit invariant mass is summable on all of `ℤ`. -/
theorem summable_invariantMass (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    Summable (invariantMass lam) :=
  Summable.of_add_one_of_neg_add_one (summable_positive_tail hlam₀ hlam)
    (summable_negative_tail hlam₀ hlam)

/-- Equation (3.5)--(3.7) defines a probability mass function. -/
theorem tsum_invariantMass (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    ∑' k : ℤ, invariantMass lam k = 1 := by
  rw [tsum_of_add_one_of_neg_add_one (summable_positive_tail hlam₀ hlam)
    (summable_negative_tail hlam₀ hlam)]
  rw [tsum_positive_tail hlam₀ hlam, tsum_negative_tail hlam₀ hlam]
  simp only [invariantMass, centralMass]
  field_simp
  nlinarith

private theorem detailed_balance_zero (hlam₀ : 0 < lam) :
    invariantMass lam 0 * birthRate lam 0 = invariantMass lam 1 * deathRate lam 1 := by
  rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 by norm_num]
  simp [invariantMass, birthRate, deathRate, currentSign, centralMass]
  field_simp [ne_of_gt (positive_denominator_pos hlam₀)]

private theorem detailed_balance_positive (hlam₀ : 0 < lam) (n : ℕ) :
    invariantMass lam ((n : ℤ) + 1) * birthRate lam ((n : ℤ) + 1) =
      invariantMass lam ((n : ℤ) + 2) * deathRate lam ((n : ℤ) + 2) := by
  rw [show (n : ℤ) + 2 = ((n + 1 : ℕ) : ℤ) + 1 by omega]
  simp only [invariantMass_nat_add_one, birthRate, deathRate, currentSign_nat_add_one]
  rw [pow_succ, positiveRatio]
  field_simp [ne_of_gt (positive_denominator_pos hlam₀)]

private theorem detailed_balance_negative_one (hlam₀ : 0 < lam) :
    invariantMass lam (-1) * birthRate lam (-1) = invariantMass lam 0 * deathRate lam 0 := by
  rw [invariantMass_neg_one, invariantMass_zero, birthRate, deathRate, currentSign_neg_one,
    currentSign_zero, centralMass]
  field_simp [ne_of_gt (negative_denominator_pos hlam₀)]
  ring

private theorem detailed_balance_negative (hlam₀ : 0 < lam) (n : ℕ) :
    invariantMass lam (-((n : ℤ) + 2)) * birthRate lam (-((n : ℤ) + 2)) =
      invariantMass lam (-((n : ℤ) + 1)) * deathRate lam (-((n : ℤ) + 1)) := by
  rw [show -((n : ℤ) + 2) = -(((n + 1 : ℕ) : ℤ) + 1) by omega]
  simp only [invariantMass_neg_nat_add_one, birthRate, deathRate,
    currentSign_neg_nat_add_one]
  rw [pow_succ, negativeRatio]
  field_simp [ne_of_gt (negative_denominator_pos hlam₀)]
  ring

/-- The explicit mass satisfies the detailed-balance equation across every neighboring pair. -/
theorem detailed_balance (hlam₀ : 0 < lam) (_hlam : lam < 1 / 2) (k : ℤ) :
    invariantMass lam k * birthRate lam k =
      invariantMass lam (k + 1) * deathRate lam (k + 1) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact detailed_balance_zero hlam₀
      | succ n =>
          change invariantMass lam ((n : ℤ) + 1) * birthRate lam ((n : ℤ) + 1) =
            invariantMass lam (((n : ℤ) + 1) + 1) *
              deathRate lam (((n : ℤ) + 1) + 1)
          simpa only [add_assoc, one_add_one_eq_two] using detailed_balance_positive hlam₀ n
  | negSucc n =>
      cases n with
      | zero => exact detailed_balance_negative_one hlam₀
      | succ n =>
          change invariantMass lam (-((n : ℤ) + 2)) * birthRate lam (-((n : ℤ) + 2)) =
            invariantMass lam (-((n : ℤ) + 2) + 1) *
              deathRate lam (-((n : ℤ) + 2) + 1)
          rw [show -((n : ℤ) + 2) + 1 = -((n : ℤ) + 1) by omega]
          exact detailed_balance_negative hlam₀ n

/-- Detailed balance implies the stationary global-balance equation at every state. -/
theorem global_balance (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    invariantMass lam k * (birthRate lam k + deathRate lam k) =
      invariantMass lam (k - 1) * birthRate lam (k - 1) +
        invariantMass lam (k + 1) * deathRate lam (k + 1) := by
  have hleft : invariantMass lam (k - 1) * birthRate lam (k - 1) =
      invariantMass lam k * deathRate lam k := by
    simpa using detailed_balance hlam₀ hlam (k - 1)
  have hright := detailed_balance hlam₀ hlam k
  rw [hleft, ← hright]
  ring

/-- The invariant signed mass is summable. -/
theorem summable_signedMass (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    Summable (signedMass lam) := by
  apply Summable.of_add_one_of_neg_add_one
  · simpa using summable_positive_tail hlam₀ hlam
  · exact (summable_negative_tail hlam₀ hlam).neg.congr fun n ↦ by
      change -invariantMass lam (-((n : ℤ) + 1)) = signedMass lam (-((n : ℤ) + 1))
      rw [signedMass_neg_nat_add_one]

/- Equation (3.8): the invariant current has zero mean sign. -/
theorem tsum_signedMass (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    ∑' k : ℤ, signedMass lam k = 0 := by
  have hpos : Summable fun n : ℕ ↦ signedMass lam ((n : ℤ) + 1) := by
    simpa using summable_positive_tail hlam₀ hlam
  have hneg : Summable fun n : ℕ ↦ signedMass lam (-((n : ℤ) + 1)) := by
    exact (summable_negative_tail hlam₀ hlam).neg.congr fun n ↦ by
      change -invariantMass lam (-((n : ℤ) + 1)) = signedMass lam (-((n : ℤ) + 1))
      rw [signedMass_neg_nat_add_one]
  rw [tsum_of_add_one_of_neg_add_one hpos hneg]
  simp only [signedMass_nat_add_one, signedMass_zero, signedMass_neg_nat_add_one,
    add_zero, tsum_neg]
  rw [tsum_positive_tail hlam₀ hlam, tsum_negative_tail hlam₀ hlam]
  ring

/-- The stationary mixture of the source-mark densities is the uniform density. -/
theorem tsum_sourceMarkDensity (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (u : ℝ) :
    ∑' k : ℤ, invariantMass lam k * sourceMarkDensity lam k u = 1 := by
  have hsigned := summable_signedMass hlam₀ hlam
  have hscaled : Summable fun k : ℤ ↦
      (lam * (1 - u)) * signedMass lam k :=
    hsigned.mul_left _
  rw [show (fun k : ℤ ↦ invariantMass lam k * sourceMarkDensity lam k u) =
      fun k ↦ invariantMass lam k -
        (lam * (1 - u)) * signedMass lam k by
    funext k
    simp only [sourceMarkDensity, signedMass]
    ring]
  rw [(summable_invariantMass hlam₀ hlam).tsum_sub hscaled,
    tsum_mul_left, tsum_invariantMass hlam₀ hlam, tsum_signedMass hlam₀ hlam]
  ring

/-- The stationary mixture of the target-mark densities is the uniform density. -/
theorem tsum_targetMarkDensity (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (v : ℝ) :
    ∑' k : ℤ, invariantMass lam k * targetMarkDensity lam k v = 1 := by
  have hsigned := summable_signedMass hlam₀ hlam
  have hscaled : Summable fun k : ℤ ↦
      (lam * (1 + v)) * signedMass lam k :=
    hsigned.mul_left _
  rw [show (fun k : ℤ ↦ invariantMass lam k * targetMarkDensity lam k v) =
      fun k ↦ invariantMass lam k +
        (lam * (1 + v)) * signedMass lam k by
    funext k
    simp only [targetMarkDensity, signedMass]
    ring]
  rw [(summable_invariantMass hlam₀ hlam).tsum_add hscaled,
    tsum_mul_left, tsum_invariantMass hlam₀ hlam, tsum_signedMass hlam₀ hlam]
  ring

/-- The invariant probability measure on the integer current, obtained by weighting counting
measure with the explicit mass function. -/
noncomputable def invariantCurrentMeasure (lam : ℝ) : Measure ℤ :=
  Measure.count.withDensity fun k ↦ ENNReal.ofReal (invariantMass lam k)

/-- The current measure has total mass one. -/
theorem invariantCurrentMeasure_apply_univ (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    invariantCurrentMeasure lam Set.univ = 1 := by
  rw [invariantCurrentMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_count]
  rw [← ENNReal.ofReal_tsum_of_nonneg (invariantMass_nonneg hlam₀ hlam)
    (summable_invariantMass hlam₀ hlam), tsum_invariantMass hlam₀ hlam]
  norm_num

/-- The explicit current law packaged as a probability measure. -/
noncomputable def invariantCurrentProbability (lam : ℝ) (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) : ProbabilityMeasure ℤ :=
  ⟨invariantCurrentMeasure lam,
    { measure_univ := invariantCurrentMeasure_apply_univ hlam₀ hlam }⟩

end ParameterRange

end OTSelector.Limit
