import OTSelector.PointProcess.MatchingSceneCollisionSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Explicit collision grids for sample selection

A positive threshold and a positive failure budget determine an explicit finite grid. Every
resolution for radius `A` lies inside the same enlarged interval `[-(3*A+3), 3*A+3]`. Thus each
fixed radius needs only eventual bulk fit, uniformly over all grid resolutions. The probability
bounds are restricted to one shared survival mask and do not repay its complement.
-/

open MeasureTheory Set Filter Function Topology
open scoped Classical BigOperators ENNReal NNReal

set_option maxHeartbeats 600000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

/-- A fixed positive sequence of empirical collision thresholds tending to zero. -/
noncomputable def collisionSelectionThreshold (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem collisionSelectionThreshold_pos (j : ℕ) : 0 < collisionSelectionThreshold j := by
  unfold collisionSelectionThreshold
  positivity

theorem tendsto_collisionSelectionThreshold :
    Tendsto collisionSelectionThreshold atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Explicit resolution for a collision threshold and its assigned failure probability. -/
noncomputable def collisionSelectionGridSize (A eps weight : ℝ) : ℕ :=
  Nat.ceil (324 * (2 * A + 2)^2 / (eps * weight)) + 1

theorem collisionSelectionGridSize_pos (A eps weight : ℝ) :
    0 < collisionSelectionGridSize A eps weight := Nat.zero_lt_succ _

/-- The quadratic grid cost is proportional to the reciprocal resolution. -/
theorem collisionGrid_quadratic_budget_eq_div (A : ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ k : Fin m, ENNReal.ofReal
      (36 * (collisionGridRight A k - collisionGridLeft A k)^2)) =
      ENNReal.ofReal (324 * (2 * A + 2)^2 / (m : ℝ)) := by
  rw [collisionGrid_quadratic_budget, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold collisionGridMesh
  field_simp

/-- The chosen explicit grid meets its budget after Markov division by the threshold. -/
theorem collisionSelectionGrid_budget_le (A : ℝ) {eps weight : ℝ}
    (heps : 0 < eps) (hweight : 0 < weight) :
    (∑ k : Fin (collisionSelectionGridSize A eps weight), ENNReal.ofReal
      (36 * (collisionGridRight A k - collisionGridLeft A k)^2)) / ENNReal.ofReal eps ≤
      ENNReal.ofReal weight := by
  let m := collisionSelectionGridSize A eps weight
  have hm : 0 < m := collisionSelectionGridSize_pos A eps weight
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hceil : 324 * (2 * A + 2)^2 / (eps * weight) ≤ (m : ℝ) := by
    have h := Nat.le_ceil (324 * (2 * A + 2)^2 / (eps * weight))
    dsimp [m, collisionSelectionGridSize]
    push_cast
    linarith
  have hnum : 324 * (2 * A + 2)^2 ≤ (m : ℝ) * (eps * weight) :=
    (div_le_iff₀ (mul_pos heps hweight)).mp hceil
  have hreal : (324 * (2 * A + 2)^2 / (m : ℝ)) / eps ≤ weight := by
    apply (div_le_iff₀ heps).mpr
    apply (div_le_iff₀ hmreal).mpr
    nlinarith only [hnum]
  rw [collisionGrid_quadratic_budget_eq_div A hm, ← ENNReal.ofReal_div_of_pos heps]
  exact ENNReal.ofReal_le_ofReal hreal

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess PointProcess.MatchingScene CountingProcess

variable {n : ℕ} {lam : ℝ}

/-- The actual empirical collision sum on the explicitly selected finite grid. -/
noncomputable def stoppedEmpiricalSelectedCollisionGrid
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (A eps weight c d : ℝ) (sample : FiniteSample n) : ℝ≥0∞ :=
  ∑ k : Fin (collisionSelectionGridSize A eps weight),
    stoppedEmpiricalCollisionFraction hlam0 hlamHalf eta B T
      (collisionGridLeft A k) (collisionGridRight A k) c d sample

theorem measurable_stoppedEmpiricalSelectedCollisionGrid
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (A eps weight c d : ℝ) :
    Measurable (stoppedEmpiricalSelectedCollisionGrid (n := n)
      hlam0 hlamHalf eta B T A eps weight c d) :=
  Finset.measurable_sum _ fun k _ ↦
    measurable_stoppedEmpiricalCollisionFraction hlam0 hlamHalf hB eta T
      (collisionGridLeft A k) (collisionGridRight A k) c d

/-- A shared mask contained in survival pays only the assigned collision budget. -/
theorem measure_stoppedEmpiricalSelectedCollisionGrid_on_mask_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B A eps weight c d : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (hA : 0 ≤ A)
    (heps : 0 < eps) (hweight : 0 < weight) (hcd : c < d)
    (hleft : B ≤ c - (3 * A + 3)) (hright : d + (3 * A + 3) < B + (T : ℝ))
    (G : Set (FiniteSample n))
    (hG : G ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample}) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | sample ∈ G ∧ ENNReal.ofReal eps ≤ stoppedEmpiricalSelectedCollisionGrid
        hlam0.le (by linarith) eta B T A eps weight c d sample} ≤ ENNReal.ofReal weight := by
  let m := collisionSelectionGridSize A eps weight
  have hm : 0 < m := collisionSelectionGridSize_pos A eps weight
  have hl (k : Fin m) : B ≤ c + collisionGridLeft A k := by
    have hk := (collisionGrid_endpoint_bounds hA hm k).1
    linarith
  have hr (k : Fin m) : d + collisionGridRight A k < B + (T : ℝ) := by
    have hk := (collisionGrid_endpoint_bounds hA hm k).2
    linarith
  have hbudget := measure_stoppedEmpiricalCollisionGrid_on_survival_ge_le
    hlam0 hlam hn hB heta hetaSmall T (collisionGridLeft A) (collisionGridRight A)
    (collisionGrid_ordered hA hm) hcd hl hr
    (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
  apply (measure_mono (show {sample | sample ∈ G ∧ ENNReal.ofReal eps ≤
      stoppedEmpiricalSelectedCollisionGrid hlam0.le (by linarith) eta B T A eps weight c d sample} ⊆
      {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample ∧
        ENNReal.ofReal eps ≤ ∑ k : Fin m, stoppedEmpiricalCollisionFraction
          hlam0.le (by linarith) eta B T (collisionGridLeft A k) (collisionGridRight A k) c d sample}
    from fun _ hs ↦ ⟨hG hs.1, hs.2⟩)).trans
  exact hbudget.trans (collisionSelectionGrid_budget_le A heps hweight)

/-- Real probability version for deterministic good-sample extraction. -/
theorem measureReal_stoppedEmpiricalSelectedCollisionGrid_on_mask_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B A eps weight c d : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (hA : 0 ≤ A)
    (heps : 0 < eps) (hweight : 0 < weight) (hcd : c < d)
    (hleft : B ≤ c - (3 * A + 3)) (hright : d + (3 * A + 3) < B + (T : ℝ))
    (G : Set (FiniteSample n))
    (hG : G ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample}) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | sample ∈ G ∧ ENNReal.ofReal eps ≤ stoppedEmpiricalSelectedCollisionGrid
        hlam0.le (by linarith) eta B T A eps weight c d sample} ≤ weight :=
  ENNReal.toReal_le_of_le_ofReal hweight.le
    (measure_stoppedEmpiricalSelectedCollisionGrid_on_mask_ge_le
      hlam0 hlam hn hB heta hetaSmall T hA heps hweight hcd hleft hright G hG)

/-- For each fixed radius, eventual bulk fit suffices for every grid precision at once.
No finite sample size is required to accommodate all radii simultaneously. -/
theorem eventually_stoppedEmpiricalSelectedCollisionGrid_budgets
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (eta B c d : ℕ → ℝ) (T : ℕ → ℝ≥0) (A eps : ℕ → ℝ) (weight : ℕ → ℕ → ℝ)
    (hA : ∀ R, 0 ≤ A R) (heps : ∀ j, 0 < eps j) (hweight : ∀ R j, 0 < weight R j)
    (G : (n : ℕ) → Set (FiniteSample n))
    (hG : ∀ n, G n ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith)
      (eta n) (B n) (T n) sample})
    (hparams : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < B n ∧ 0 ≤ eta n ∧
      eta n * (2 + lam) ≤ lam ∧ c n < d n)
    (hbulk : ∀ R, ∀ᶠ n : ℕ in atTop,
      B n ≤ c n - (3 * A R + 3) ∧ d n + (3 * A R + 3) < B n + (T n : ℝ)) :
    ∀ R, ∀ᶠ n : ℕ in atTop, ∀ j,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | sample ∈ G n ∧ ENNReal.ofReal (eps j) ≤ stoppedEmpiricalSelectedCollisionGrid
          hlam0.le (by linarith) (eta n) (B n) (T n) (A R) (eps j) (weight R j) (c n) (d n) sample}
        ≤ weight R j := by
  intro R
  filter_upwards [hparams, hbulk R] with n hn hfit
  intro j
  exact measureReal_stoppedEmpiricalSelectedCollisionGrid_on_mask_ge_le hlam0 hlam
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 (T n) (hA R) (heps j) (hweight R j)
    hn.2.2.2.2 hfit.1 hfit.2 (G n) (hG n)

end OTSelector.FiniteSample
