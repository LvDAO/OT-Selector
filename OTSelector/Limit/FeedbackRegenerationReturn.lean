import OTSelector.Limit.FeedbackRegenerationTrajectory
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Return to zero for the actual embedded feedback chain

An explicit exponential weight contracts at every nonzero current. Applying the contraction to
the actual trajectory killed at zero gives a geometric return-time tail and almost sure return.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Exponential weight of a current, with base adapted to the actual asymmetric rates. -/
noncomputable def feedbackExcursionWeight (lam : ℝ) (k : ℤ) : ℝ :=
  (1 + lam) ^ k.natAbs

/-- Uniform contraction factor on both nonzero half-lines. -/
noncomputable def feedbackExcursionRatio (lam : ℝ) : ℝ :=
  1 - lam ^ 2 / (2 * (1 + lam))

theorem feedbackExcursionRatio_pos {lam : ℝ} (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) :
    0 < feedbackExcursionRatio lam := by
  unfold feedbackExcursionRatio
  have hd : 0 < 2 * (1 + lam) := by positivity
  have hq : lam ^ 2 / (2 * (1 + lam)) < 1 := by
    apply (div_lt_one hd).mpr
    nlinarith
  linarith

theorem feedbackExcursionRatio_lt_one {lam : ℝ} (hlam₀ : 0 < lam) :
    feedbackExcursionRatio lam < 1 := by
  unfold feedbackExcursionRatio
  have : 0 < lam ^ 2 / (2 * (1 + lam)) := by positivity
  linarith

private theorem feedbackExcursionRatio_mul_base {lam : ℝ} (hlam₀ : 0 < lam) :
    feedbackExcursionRatio lam * (1 + lam) = 1 + lam - lam ^ 2 / 2 := by
  unfold feedbackExcursionRatio
  field_simp

private theorem positive_excursion_coefficient {lam : ℝ} (hlam₀ : 0 < lam) (n : ℕ) :
    jumpUpProbability lam ((n : ℤ) + 1) * (1 + lam) ^ 2 +
      jumpDownProbability lam ((n : ℤ) + 1) = feedbackExcursionRatio lam * (1 + lam) := by
  rw [feedbackExcursionRatio_mul_base hlam₀]
  simp only [jumpUpProbability, jumpDownProbability, totalJumpRate_positive,
    birthRate, deathRate, currentSign_nat_add_one, mul_one]
  have hd : 2 + lam ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

private theorem negative_excursion_coefficient {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    jumpUpProbability lam (-((n : ℤ) + 1)) +
      jumpDownProbability lam (-((n : ℤ) + 1)) * (1 + lam) ^ 2 ≤
        feedbackExcursionRatio lam * (1 + lam) := by
  rw [feedbackExcursionRatio_mul_base hlam₀]
  simp only [jumpUpProbability, jumpDownProbability, totalJumpRate_negative,
    birthRate, deathRate, currentSign_neg_nat_add_one, mul_neg_one]
  rw [div_mul_eq_mul_div, ← add_div]
  apply (div_le_iff₀ (by linarith : 0 < 2 - lam)).mpr
  nlinarith [pow_pos hlam₀ 3]

/-- Exact feedback rates give one uniform exponential drift toward zero. -/
theorem feedbackExcursionWeight_drift {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (hk : k ≠ 0) :
    jumpUpProbability lam k * feedbackExcursionWeight lam (k + 1) +
      jumpDownProbability lam k * feedbackExcursionWeight lam (k - 1) ≤
        feedbackExcursionRatio lam * feedbackExcursionWeight lam k := by
  have ha : 0 ≤ 1 + lam := by linarith
  cases k with
  | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n =>
          have hplus : (Int.ofNat (n + 1) + 1).natAbs = n + 2 := rfl
          have hminus : (Int.ofNat (n + 1) - 1).natAbs = n := by
            change ((n : ℤ) + 1 - 1).natAbs = n
            simp
          have hbase : (Int.ofNat (n + 1)).natAbs = n + 1 := rfl
          simp only [feedbackExcursionWeight, hplus, hminus, hbase]
          have hcoef := (positive_excursion_coefficient hlam₀ n).le
          have hm := mul_le_mul_of_nonneg_left hcoef (pow_nonneg ha n)
          simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
          convert hm using 1 <;> first | rfl | ring
  | negSucc n =>
      have hplus : (Int.negSucc n + 1).natAbs = n := by omega
      have hminus : (Int.negSucc n - 1).natAbs = n + 2 := by omega
      have hbase : (Int.negSucc n).natAbs = n + 1 := rfl
      simp only [feedbackExcursionWeight, hplus, hminus, hbase]
      have hm := mul_le_mul_of_nonneg_left (negative_excursion_coefficient hlam₀ hlam n)
        (pow_nonneg ha n)
      simp only [Int.negSucc_eq]
      convert hm using 1 <;> first | rfl | ring

/-- The exponential weight killed on arrival at zero. -/
noncomputable def feedbackKilledWeight (lam : ℝ) (k : ℤ) : ℝ≥0∞ :=
  if k = 0 then 0 else ENNReal.ofReal (feedbackExcursionWeight lam k)

theorem feedbackKilledWeight_le (lam : ℝ) (k : ℤ) :
    feedbackKilledWeight lam k ≤ ENNReal.ofReal (feedbackExcursionWeight lam k) := by
  unfold feedbackKilledWeight
  split_ifs <;> simp

/-- The genuine feedback kernel contracts the weight before hitting zero. -/
theorem feedbackJumpKernel_killed_drift {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (hk : k ≠ 0) :
    ∫⁻ j, feedbackKilledWeight lam j ∂feedbackJumpKernel lam k ≤
      ENNReal.ofReal (feedbackExcursionRatio lam) * feedbackKilledWeight lam k := by
  calc
    _ ≤ ∫⁻ j, ENNReal.ofReal (feedbackExcursionWeight lam j) ∂feedbackJumpKernel lam k :=
      lintegral_mono (feedbackKilledWeight_le lam)
    _ = ENNReal.ofReal (jumpUpProbability lam k * feedbackExcursionWeight lam (k + 1) +
        jumpDownProbability lam k * feedbackExcursionWeight lam (k - 1)) := by
      simp only [feedbackJumpKernel, Kernel.coe_mk, lintegral_add_measure,
        lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
      rw [ENNReal.ofReal_add
        (mul_nonneg (jumpUpProbability_nonneg hlam₀ hlam k) (by
          unfold feedbackExcursionWeight; positivity))
        (mul_nonneg (jumpDownProbability_nonneg hlam₀ hlam k) (by
          unfold feedbackExcursionWeight; positivity)),
        ENNReal.ofReal_mul (jumpUpProbability_nonneg hlam₀ hlam k),
        ENNReal.ofReal_mul (jumpDownProbability_nonneg hlam₀ hlam k)]
    _ ≤ ENNReal.ofReal (feedbackExcursionRatio lam * feedbackExcursionWeight lam k) :=
      ENNReal.ofReal_le_ofReal (feedbackExcursionWeight_drift hlam₀ hlam k hk)
    _ = _ := by
      rw [ENNReal.ofReal_mul (feedbackExcursionRatio_pos hlam₀ hlam).le,
        feedbackKilledWeight, ite_eq_right hk]

/-- No zero has occurred at any of the first n+1 inspected currents. -/
def feedbackAvoidsZero (n : ℕ) (w : ℕ → ℤ) : Prop :=
  ∀ i ∈ Finset.Iic n, w i ≠ 0

/-- The corresponding event expressed directly on a finite history. -/
def feedbackHistoryAvoidsZero (n : ℕ) (x : (i : Finset.Iic n) → ℤ) : Prop :=
  ∀ i, x i ≠ 0

theorem measurableSet_feedbackAvoidsZero (n : ℕ) : MeasurableSet {w | feedbackAvoidsZero n w} := by
  unfold feedbackAvoidsZero
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ ?_
  exact (measurableSet_singleton (0 : ℤ)).preimage (measurable_pi_apply i) |>.compl

theorem measurableSet_feedbackHistoryAvoidsZero (n : ℕ) :
    MeasurableSet {x | feedbackHistoryAvoidsZero n x} := by
  unfold feedbackHistoryAvoidsZero
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact (measurableSet_singleton (0 : ℤ)).preimage (measurable_pi_apply i) |>.compl

@[simp]
theorem feedbackHistoryAvoidsZero_restrict (n : ℕ) (w : ℕ → ℤ) :
    feedbackHistoryAvoidsZero n (frestrictLe n w) ↔ feedbackAvoidsZero n w := by
  simp [feedbackHistoryAvoidsZero, feedbackAvoidsZero, frestrictLe]

theorem feedbackAvoidsZero_succ (n : ℕ) (w : ℕ → ℤ) :
    feedbackAvoidsZero (n + 1) w ↔ feedbackAvoidsZero n w ∧ w (n + 1) ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp hi).trans n.le_succ)), h (n + 1) (by simp)⟩
  · rintro ⟨h, hnext⟩ i hi
    by_cases heq : i = n + 1
    · simpa [heq] using hnext
    · exact h i (Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp hi; omega))

/-- Exponential weight of the actual chain, set to zero once a zero current has occurred. -/
noncomputable def feedbackSurvivalWeight (lam : ℝ) (n : ℕ) (w : ℕ → ℤ) : ℝ≥0∞ :=
  if feedbackAvoidsZero n w then ENNReal.ofReal (feedbackExcursionWeight lam (w n)) else 0

@[fun_prop]
theorem measurable_feedbackSurvivalWeight (lam : ℝ) (n : ℕ) :
    Measurable (feedbackSurvivalWeight lam n) := by
  unfold feedbackSurvivalWeight
  exact Measurable.ite (measurableSet_feedbackAvoidsZero n)
    ((measurable_of_countable (fun j : ℤ ↦ ENNReal.ofReal (feedbackExcursionWeight lam j))).comp
      (measurable_pi_apply n)) measurable_const

@[simp]
theorem feedbackSurvivalWeight_zero (lam : ℝ) (w : ℕ → ℤ) :
    feedbackSurvivalWeight lam 0 w = feedbackKilledWeight lam (w 0) := by
  simp [feedbackSurvivalWeight, feedbackAvoidsZero, ← Nat.range_succ_eq_Iic,
    feedbackKilledWeight, ite_not]

theorem feedbackSurvivalWeight_succ (lam : ℝ) (n : ℕ) (w : ℕ → ℤ) :
    feedbackSurvivalWeight lam (n + 1) w =
      if feedbackAvoidsZero n w then feedbackKilledWeight lam (w (n + 1)) else 0 := by
  by_cases h : feedbackAvoidsZero n w <;>
    simp [feedbackSurvivalWeight, feedbackAvoidsZero_succ, feedbackKilledWeight, h, ite_not]

/-- Conditional drift for the genuine path, killed at its first zero current. -/
theorem feedbackSurvivalWeight_integral_succ_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, feedbackSurvivalWeight lam (n + 1) w
      ∂feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k) ≤
      ENNReal.ofReal (feedbackExcursionRatio lam) * ∫⁻ w, feedbackSurvivalWeight lam n w
        ∂feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k) := by
  let μ := feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k)
  let f : ((i : Finset.Iic n) → ℤ) × ℤ → ℝ≥0∞ :=
    fun p ↦ if feedbackHistoryAvoidsZero n p.1 then feedbackKilledWeight lam p.2 else 0
  let g : ((i : Finset.Iic n) → ℤ) → ℝ≥0∞ :=
    fun x ↦ if feedbackHistoryAvoidsZero n x then
      ENNReal.ofReal (feedbackExcursionWeight lam (x ⟨n, by simp⟩)) else 0
  have hf : Measurable f := by
    exact Measurable.ite ((measurableSet_feedbackHistoryAvoidsZero n).preimage measurable_fst)
      ((measurable_of_countable (feedbackKilledWeight lam)).comp measurable_snd) measurable_const
  have hg : Measurable g := by
    exact Measurable.ite (measurableSet_feedbackHistoryAvoidsZero n)
      ((measurable_of_countable
        (fun j : ℤ ↦ ENNReal.ofReal (feedbackExcursionWeight lam j))).comp
          (measurable_pi_apply _)) measurable_const
  change ∫⁻ w, feedbackSurvivalWeight lam (n + 1) w ∂μ ≤ _
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun w ↦ (frestrictLe n w, w (n + 1))) := by
      rw [lintegral_map hf (by fun_prop)]
      apply lintegral_congr
      intro w
      simp [f, feedbackSurvivalWeight_succ]
    _ = ∫⁻ x, (∫⁻ j, f (x, j) ∂condDistrib
          (fun w : ℕ → ℤ ↦ w (n + 1)) (frestrictLe n) μ x)
        ∂μ.map (frestrictLe n) := by
      rw [← compProd_map_condDistrib (μ := μ) (X := frestrictLe n)
        (Y := fun w : ℕ → ℤ ↦ w (n + 1))
        (measurable_pi_apply (n + 1)).aemeasurable, Measure.lintegral_compProd hf]
    _ ≤ ∫⁻ x, ENNReal.ofReal (feedbackExcursionRatio lam) * g x
        ∂μ.map (frestrictLe n) := by
      apply lintegral_mono_ae
      filter_upwards [feedbackJumpTrajectory_condDistrib hlam₀ hlam (Measure.dirac k) n]
        with x hx
      rw [hx]
      by_cases h : feedbackHistoryAvoidsZero n x
      · have hk := h ⟨n, by simp⟩
        simpa [f, g, h, feedbackJumpHistoryKernel, feedbackKilledWeight, hk] using
          feedbackJumpKernel_killed_drift hlam₀ hlam (x ⟨n, by simp⟩) hk
      · simp [f, g, h]
    _ = _ := by
      rw [lintegral_const_mul _ hg, lintegral_map hg (measurable_frestrictLe n)]
      congr 1
      apply lintegral_congr
      intro w
      simp only [g, feedbackSurvivalWeight, feedbackHistoryAvoidsZero_restrict]
      rfl

/-- Geometric decay of the actual killed exponential moment. -/
theorem feedbackSurvivalWeight_integral_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, feedbackSurvivalWeight lam n w
      ∂feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k) ≤
      ENNReal.ofReal (feedbackExcursionWeight lam k) *
        ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  induction n with
  | zero =>
      simp only [feedbackSurvivalWeight_zero, pow_zero, mul_one]
      rw [← lintegral_map (measurable_of_countable (feedbackKilledWeight lam))
        (measurable_pi_apply 0), feedbackJumpTrajectory_map_zero, lintegral_dirac]
      exact feedbackKilledWeight_le lam k
  | succ n ih =>
      apply (feedbackSurvivalWeight_integral_succ_le hlam₀ hlam k n).trans
      calc
        _ ≤ ENNReal.ofReal (feedbackExcursionRatio lam) *
            (ENNReal.ofReal (feedbackExcursionWeight lam k) *
              ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) := mul_le_mul_right ih _
        _ = _ := by rw [pow_succ]; ac_rfl

/-- A geometric first-hitting tail under the constructed infinite-trajectory law. -/
theorem feedbackJumpTrajectory_return_tail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k)
      {w | feedbackAvoidsZero n w} ≤
      ENNReal.ofReal (feedbackExcursionWeight lam k) *
        ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  let μ := feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k)
  calc
    _ = ∫⁻ w, {w | feedbackAvoidsZero n w}.indicator (fun _ ↦ (1 : ℝ≥0∞)) w ∂μ := by
      rw [lintegral_indicator (measurableSet_feedbackAvoidsZero n)]
      simp [μ]
    _ ≤ ∫⁻ w, feedbackSurvivalWeight lam n w ∂μ := by
      apply lintegral_mono
      intro w
      by_cases h : feedbackAvoidsZero n w
      · rw [Set.indicator_of_mem (show w ∈ {w | feedbackAvoidsZero n w} from h)]
        simp only [feedbackSurvivalWeight, ite_eq_left h]
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact one_le_pow₀ (by linarith : 1 ≤ 1 + lam)
      · simp [feedbackSurvivalWeight, h]
    _ ≤ _ := feedbackSurvivalWeight_integral_le hlam₀ hlam k n

/-- From every prescribed current, the actual embedded chain hits zero almost surely. -/
theorem feedbackJumpTrajectory_hits_zero {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k), ∃ n, w n = 0 := by
  have hr : ENNReal.ofReal (feedbackExcursionRatio lam) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact feedbackExcursionRatio_lt_one hlam₀
  have hsum : (∑' n : ℕ, ENNReal.ofReal (feedbackExcursionWeight lam k) *
      ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hr).ne')
  have htail := ae_eventually_notMem
    (μ := feedbackJumpTrajectory lam hlam₀ hlam (Measure.dirac k))
    (s := fun n ↦ {w | feedbackAvoidsZero n w})
    (ne_top_of_le_ne_top hsum
      (ENNReal.tsum_le_tsum (fun n ↦ feedbackJumpTrajectory_return_tail hlam₀ hlam k n)))
  filter_upwards [htail] with w hw
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  have h := hN N le_rfl
  change ¬ feedbackAvoidsZero N w at h
  simp only [feedbackAvoidsZero, not_forall, not_not] at h
  obtain ⟨n, _, hn⟩ := h
  exact ⟨n, hn⟩

end OTSelector.Limit
