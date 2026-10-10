import OTSelector.Limit.FeedbackRegenerationReturn
import OTSelector.Limit.FeedbackRegenerationHolding

/-!
# Actual positive return of the physical feedback trajectory

The initial pair has a virtual zero waiting time. The first positive return inspects currents
at coordinates `1, 2, ...` of the actual joint holding/jump trajectory; its geometric tail is
proved from that trajectory's own conditional transition law.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Current sequence after the initial coordinate, on the actual joint trajectory. -/
def feedbackPostInitialCurrent (w : ℕ → ℝ × ℤ) (n : ℕ) : ℤ := (w (n + 1)).2

@[fun_prop]
theorem measurable_feedbackPostInitialCurrent : Measurable feedbackPostInitialCurrent := by
  unfold feedbackPostInitialCurrent
  fun_prop

/-- All positive-index currents in a finite physical history are nonzero. -/
def feedbackHistoryAvoidsPositiveZero (n : ℕ) (x : (i : Finset.Iic (n + 1)) → ℝ × ℤ) : Prop :=
  ∀ i, i.val ≠ 0 → (x i).2 ≠ 0

theorem measurableSet_feedbackHistoryAvoidsPositiveZero (n : ℕ) :
    MeasurableSet {x | feedbackHistoryAvoidsPositiveZero n x} := by
  unfold feedbackHistoryAvoidsPositiveZero
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ ?_
  exact (measurableSet_singleton (0 : ℤ)).preimage (by fun_prop) |>.compl

@[simp]
theorem feedbackHistoryAvoidsPositiveZero_restrict (n : ℕ) (w : ℕ → ℝ × ℤ) :
    feedbackHistoryAvoidsPositiveZero n (frestrictLe (n + 1) w) ↔
      feedbackAvoidsZero n (feedbackPostInitialCurrent w) := by
  constructor
  · intro h i hi
    exact h ⟨i + 1, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp hi; omega)⟩
      (by simp)
  · intro h ⟨i, hi⟩ hpos
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    exact h j (Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp hi; omega))

/-- The joint physical step has the same killed-current contraction as its jump marginal. -/
theorem feedbackHoldingJumpKernel_killed_drift {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (hk : k ≠ 0) :
    ∫⁻ z : ℝ × ℤ, feedbackKilledWeight lam z.2 ∂feedbackHoldingJumpKernel lam k ≤
      ENNReal.ofReal (feedbackExcursionRatio lam) * feedbackKilledWeight lam k := by
  rw [← lintegral_map (measurable_of_countable (feedbackKilledWeight lam)) measurable_snd,
    feedbackHoldingJumpKernel_map_current hlam₀ hlam]
  exact feedbackJumpKernel_killed_drift hlam₀ hlam k hk

/-- The first nonzero current reached from zero has exponential weight `1 + lam`. -/
theorem feedbackHoldingJumpKernel_zero_weight {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∫⁻ z : ℝ × ℤ, feedbackKilledWeight lam z.2 ∂feedbackHoldingJumpKernel lam 0 =
      ENNReal.ofReal (1 + lam) := by
  rw [← lintegral_map (measurable_of_countable (feedbackKilledWeight lam)) measurable_snd,
    feedbackHoldingJumpKernel_map_current hlam₀ hlam]
  simp only [feedbackJumpKernel, Kernel.coe_mk, lintegral_add_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  simp [feedbackKilledWeight, feedbackExcursionWeight, jumpUpProbability_zero,
    jumpDownProbability_zero, ← add_mul, ENNReal.inv_two_add_inv_two]

/-- Killed-weight contraction on the actual physical path, starting after its virtual coordinate. -/
theorem feedbackPositiveSurvival_integral_succ_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    ∫⁻ w, feedbackSurvivalWeight lam (n + 1) (feedbackPostInitialCurrent w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0 ≤
      ENNReal.ofReal (feedbackExcursionRatio lam) * ∫⁻ w,
        feedbackSurvivalWeight lam n (feedbackPostInitialCurrent w)
        ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0 := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  let f : ((i : Finset.Iic (n + 1)) → ℝ × ℤ) × (ℝ × ℤ) → ℝ≥0∞ :=
    fun p ↦ if feedbackHistoryAvoidsPositiveZero n p.1 then
      feedbackKilledWeight lam p.2.2 else 0
  let g : ((i : Finset.Iic (n + 1)) → ℝ × ℤ) → ℝ≥0∞ :=
    fun x ↦ if feedbackHistoryAvoidsPositiveZero n x then
      ENNReal.ofReal (feedbackExcursionWeight lam (x ⟨n + 1, by simp⟩).2) else 0
  have hf : Measurable f := by
    exact Measurable.ite
      ((measurableSet_feedbackHistoryAvoidsPositiveZero n).preimage measurable_fst)
      ((measurable_of_countable (feedbackKilledWeight lam)).comp (by fun_prop)) measurable_const
  have hg : Measurable g := by
    exact Measurable.ite (measurableSet_feedbackHistoryAvoidsPositiveZero n)
      ((measurable_of_countable
        (fun j : ℤ ↦ ENNReal.ofReal (feedbackExcursionWeight lam j))).comp (by fun_prop))
      measurable_const
  change ∫⁻ w, feedbackSurvivalWeight lam (n + 1) (feedbackPostInitialCurrent w) ∂μ ≤ _
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun w ↦ (frestrictLe (n + 1) w, w (n + 2))) := by
      rw [lintegral_map hf (by fun_prop)]
      apply lintegral_congr
      intro w
      simp only [f, feedbackHistoryAvoidsPositiveZero_restrict, feedbackSurvivalWeight_succ]
      rfl
    _ = ∫⁻ x, (∫⁻ z, f (x, z) ∂condDistrib
          (fun w : ℕ → ℝ × ℤ ↦ w (n + 2)) (frestrictLe (n + 1)) μ x)
        ∂μ.map (frestrictLe (n + 1)) := by
      rw [← compProd_map_condDistrib (μ := μ) (X := frestrictLe (n + 1))
        (Y := fun w : ℕ → ℝ × ℤ ↦ w (n + 2))
        (measurable_pi_apply (n + 2)).aemeasurable, Measure.lintegral_compProd hf]
    _ ≤ ∫⁻ x, ENNReal.ofReal (feedbackExcursionRatio lam) * g x
        ∂μ.map (frestrictLe (n + 1)) := by
      apply lintegral_mono_ae
      filter_upwards [feedbackHoldingJumpTrajectory_condDistrib hlam₀ hlam 0 (n + 1)]
        with x hx
      rw [hx]
      by_cases h : feedbackHistoryAvoidsPositiveZero n x
      · have hk := h ⟨n + 1, by simp⟩ (by simp)
        simpa [f, g, h, feedbackHoldingJumpHistoryKernel, feedbackKilledWeight, hk] using
          feedbackHoldingJumpKernel_killed_drift hlam₀ hlam (x ⟨n + 1, by simp⟩).2 hk
      · simp [f, g, h]
    _ = _ := by
      rw [lintegral_const_mul _ hg, lintegral_map hg (measurable_frestrictLe (n + 1))]
      congr 1
      apply lintegral_congr
      intro w
      simp only [g, feedbackHistoryAvoidsPositiveZero_restrict, feedbackSurvivalWeight]
      rfl

/-- The actual first positive return has a geometric killed-moment bound. -/
theorem feedbackPositiveSurvival_integral_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    ∫⁻ w, feedbackSurvivalWeight lam n (feedbackPostInitialCurrent w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0 ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  induction n with
  | zero =>
      simp only [feedbackSurvivalWeight_zero, feedbackPostInitialCurrent, zero_add,
        pow_zero, mul_one]
      have hm : Measurable (fun z : ℝ × ℤ ↦ feedbackKilledWeight lam z.2) :=
        (measurable_of_countable (feedbackKilledWeight lam)).comp measurable_snd
      rw [← lintegral_map hm (measurable_pi_apply 1),
        feedbackHoldingJumpTrajectory_map_one, feedbackHoldingJumpKernel_zero_weight hlam₀ hlam]
  | succ n ih =>
      apply (feedbackPositiveSurvival_integral_succ_le hlam₀ hlam n).trans
      calc
        _ ≤ ENNReal.ofReal (feedbackExcursionRatio lam) *
            (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) :=
          mul_le_mul_right ih _
        _ = _ := by rw [pow_succ]; ac_rfl

/-- A geometric tail for avoiding zero at physical jump indices `1, ..., n + 1`. -/
theorem feedbackHoldingJumpTrajectory_positive_return_tail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
      {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  have hm : MeasurableSet {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} :=
    (measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent
  calc
    _ = ∫⁻ w, {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) w ∂μ := by
      rw [lintegral_indicator hm]
      simp [μ]
    _ ≤ ∫⁻ w, feedbackSurvivalWeight lam n (feedbackPostInitialCurrent w) ∂μ := by
      apply lintegral_mono
      intro w
      by_cases h : feedbackAvoidsZero n (feedbackPostInitialCurrent w)
      · rw [Set.indicator_of_mem (show
          w ∈ {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} from h)]
        simp only [feedbackSurvivalWeight, ite_eq_left h]
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact one_le_pow₀ (by linarith : 1 ≤ 1 + lam)
      · simp [feedbackSurvivalWeight, h]
    _ ≤ _ := feedbackPositiveSurvival_integral_le hlam₀ hlam n

/-- On the actual joint waiting/current space, zero is revisited at a strictly positive index. -/
theorem feedbackHoldingJumpTrajectory_returns_zero {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0,
      ∃ n, 0 < n ∧ (w n).2 = 0 := by
  have hr : ENNReal.ofReal (feedbackExcursionRatio lam) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact feedbackExcursionRatio_lt_one hlam₀
  have hsum : (∑' n : ℕ, ENNReal.ofReal (1 + lam) *
      ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hr).ne')
  have htail := ae_eventually_notMem
    (μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0)
    (s := fun n ↦ {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)})
    (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum
      (fun n ↦ feedbackHoldingJumpTrajectory_positive_return_tail hlam₀ hlam n)))
  filter_upwards [htail] with w hw
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  have h := hN N le_rfl
  change ¬ feedbackAvoidsZero N (feedbackPostInitialCurrent w) at h
  simp only [feedbackAvoidsZero, not_forall, not_not] at h
  obtain ⟨n, _, hn⟩ := h
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end OTSelector.Limit
