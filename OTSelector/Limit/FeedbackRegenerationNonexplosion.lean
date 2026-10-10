import OTSelector.Limit.FeedbackRegenerationLaplace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Nonexplosion of the actual feedback holding/jump trajectory

Conditional Laplace transforms contract uniformly because the actual total jump rate is bounded.
Iteration gives a geometric bound on the probability that n jumps fit into a fixed time window.
Borel--Cantelli then proves that the cumulative physical waiting time diverges almost surely.
No independence of the state-dependent waiting times is required.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

/-- Physical time after n jumps; coordinate zero is the initial state, not a holding time. -/
noncomputable def feedbackJumpTime (n : ℕ) (w : ℕ → ℝ × ℤ) : ℝ :=
  ∑ i ∈ Finset.Iic n, if i = 0 then 0 else (w i).1

/-- The same finite clock, expressed as an observable of the history through n. -/
noncomputable def feedbackHistoryTime (n : ℕ) (x : (i : Finset.Iic n) → ℝ × ℤ) : ℝ :=
  ∑ i, if i.val = 0 then 0 else (x i).1

@[fun_prop]
theorem measurable_feedbackJumpTime (n : ℕ) : Measurable (feedbackJumpTime n) := by
  unfold feedbackJumpTime
  apply Finset.measurable_sum
  intro i hi
  split_ifs <;> fun_prop

@[fun_prop]
theorem measurable_feedbackHistoryTime (n : ℕ) : Measurable (feedbackHistoryTime n) := by
  unfold feedbackHistoryTime
  apply Finset.measurable_sum
  intro i hi
  split_ifs <;> fun_prop

@[simp]
theorem feedbackHistoryTime_restrict (n : ℕ) (w : ℕ → ℝ × ℤ) :
    feedbackHistoryTime n (frestrictLe n w) = feedbackJumpTime n w := by
  simpa [feedbackHistoryTime, feedbackJumpTime, frestrictLe] using
    (Finset.sum_coe_sort (Finset.Iic n) (fun i ↦ if i = 0 then (0 : ℝ) else (w i).1))

@[simp]
theorem feedbackJumpTime_zero (w : ℕ → ℝ × ℤ) : feedbackJumpTime 0 w = 0 := by
  simp [feedbackJumpTime, ← Nat.range_succ_eq_Iic]

theorem feedbackJumpTime_succ (n : ℕ) (w : ℕ → ℝ × ℤ) :
    feedbackJumpTime (n + 1) w = feedbackJumpTime n w + (w (n + 1)).1 := by
  simp only [feedbackJumpTime, ← Nat.range_succ_eq_Iic]
  rw [Finset.sum_range_succ]
  simp

/-- The largest-rate Laplace transform at parameter one, used uniformly along the trajectory. -/
noncomputable def feedbackLaplaceRatio (lam : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 + lam) / (2 + lam + 1))

theorem feedbackLaplaceRatio_lt_one {lam : ℝ} (hlam₀ : 0 < lam) :
    feedbackLaplaceRatio lam < 1 := by
  rw [feedbackLaplaceRatio, ENNReal.ofReal_lt_one]
  apply (div_lt_one (by linarith : 0 < 2 + lam + 1)).mpr
  linarith

private theorem waitLaplace_add (theta s t : ℝ) :
    waitLaplace theta (s + t) = waitLaplace theta s * waitLaplace theta t := by
  unfold waitLaplace
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- One contraction step, computed from the proved conditional distribution of the actual path. -/
theorem feedbackJumpTime_laplace_succ_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, waitLaplace 1 (feedbackJumpTime (n + 1) w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k ≤
      feedbackLaplaceRatio lam * ∫⁻ w, waitLaplace 1 (feedbackJumpTime n w)
        ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k
  let f : ((i : Finset.Iic n) → ℝ × ℤ) × (ℝ × ℤ) → ℝ≥0∞ :=
    fun p ↦ waitLaplace 1 (feedbackHistoryTime n p.1) * waitLaplace 1 p.2.1
  have hf : Measurable f := by dsimp [f]; fun_prop
  change ∫⁻ w, waitLaplace 1 (feedbackJumpTime (n + 1) w) ∂μ ≤ _
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun w ↦ (frestrictLe n w, w (n + 1))) := by
      rw [lintegral_map hf (by fun_prop)]
      apply lintegral_congr
      intro w
      simp [f, feedbackJumpTime_succ, waitLaplace_add]
    _ = ∫⁻ x, waitLaplace 1 (feedbackHistoryTime n x) *
        (∫⁻ z, waitLaplace 1 z.1 ∂condDistrib
          (fun w : ℕ → ℝ × ℤ ↦ w (n + 1)) (frestrictLe n) μ x)
        ∂μ.map (frestrictLe n) := by
      rw [← compProd_map_condDistrib (μ := μ) (X := frestrictLe n)
        (Y := fun w : ℕ → ℝ × ℤ ↦ w (n + 1))
        (measurable_pi_apply (n + 1)).aemeasurable, Measure.lintegral_compProd hf]
      apply lintegral_congr
      intro x
      change (∫⁻ z : ℝ × ℤ,
        waitLaplace 1 (feedbackHistoryTime n x) * waitLaplace 1 z.1 ∂_) = _
      exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ x, waitLaplace 1 (feedbackHistoryTime n x) * feedbackLaplaceRatio lam
        ∂μ.map (frestrictLe n) := by
      apply lintegral_mono_ae
      filter_upwards [feedbackHoldingJumpTrajectory_condLaplace hlam₀ hlam
        (show (0 : ℝ) ≤ 1 by norm_num) k n] with x hx
      apply mul_le_mul_right
      rw [hx]
      simpa [feedbackLaplaceRatio, feedbackHoldingJumpKernel_laplace hlam₀ hlam
        (show (0 : ℝ) ≤ 1 by norm_num)] using
        feedbackHoldingJumpKernel_laplace_le hlam₀ hlam (show (0 : ℝ) ≤ 1 by norm_num)
          (x ⟨n, by simp⟩).2
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)]
      simp only [feedbackHistoryTime_restrict, mul_comm]
      rfl

/-- A geometric Laplace bound for cumulative waiting time, without iid waiting assumptions. -/
theorem feedbackJumpTime_laplace_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, waitLaplace 1 (feedbackJumpTime n w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k ≤ feedbackLaplaceRatio lam ^ n := by
  induction n with
  | zero => simp [waitLaplace]
  | succ n ih =>
      exact (feedbackJumpTime_laplace_succ_le hlam₀ hlam k n).trans
        ((mul_le_mul_right ih _).trans_eq (pow_succ' _ _).symm)

/-- A geometric upper bound for fitting n actual jumps into any fixed physical time window. -/
theorem feedbackJumpTime_lowerTail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) (T : ℝ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam k {w | feedbackJumpTime n w ≤ T} ≤
      ENNReal.ofReal (Real.exp T) * feedbackLaplaceRatio lam ^ n := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k
  have hm : Measurable (fun w ↦ waitLaplace 1 (feedbackJumpTime n w)) := by fun_prop
  have he : waitLaplace 1 T ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have he' : waitLaplace 1 T ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {w | waitLaplace 1 T ≤ waitLaplace 1 (feedbackJumpTime n w)} := by
      apply measure_mono
      intro w hw
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      simp only [one_mul]
      exact neg_le_neg hw
    _ ≤ (∫⁻ w, waitLaplace 1 (feedbackJumpTime n w) ∂μ) / waitLaplace 1 T :=
      meas_ge_le_lintegral_div hm.aemeasurable he he'
    _ ≤ feedbackLaplaceRatio lam ^ n / waitLaplace 1 T := by
      apply ENNReal.div_le_div_right
      exact feedbackJumpTime_laplace_le hlam₀ hlam k n
    _ = _ := by
      rw [ENNReal.div_eq_inv_mul, waitLaplace, one_mul,
        ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]

/-- At each fixed threshold, the actual clock eventually exceeds that threshold almost surely. -/
theorem feedbackJumpTime_eventually_gt {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (T : ℝ) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k,
      ∀ᶠ n in atTop, T < feedbackJumpTime n w := by
  have hsum : (∑' n : ℕ, ENNReal.ofReal (Real.exp T) * feedbackLaplaceRatio lam ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr (feedbackLaplaceRatio_lt_one hlam₀)).ne')
  have htail := ae_eventually_notMem (μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k)
    (s := fun n ↦ {w | feedbackJumpTime n w ≤ T})
    (ne_top_of_le_ne_top hsum
      (ENNReal.tsum_le_tsum (fun n ↦ feedbackJumpTime_lowerTail hlam₀ hlam k n T)))
  simpa only [Set.mem_ofPred_eq, not_le] using htail

/-- The actual state-dependent exponential holding times cannot accumulate in finite time. -/
theorem feedbackHoldingJumpTrajectory_nonexplosion {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k,
      Tendsto (fun n ↦ feedbackJumpTime n w) atTop atTop := by
  have hcountable : ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k,
      ∀ m : ℕ, ∀ᶠ n in atTop, (m : ℝ) < feedbackJumpTime n w :=
    ae_all_iff.mpr (fun m ↦ feedbackJumpTime_eventually_gt hlam₀ hlam k m)
  filter_upwards [hcountable] with w hw
  rw [tendsto_atTop]
  intro T
  obtain ⟨m, hm⟩ := exists_nat_gt T
  filter_upwards [hw m] with n hn
  exact (hm.trans hn).le

/-- Every bounded physical time window contains only finitely many jump indices. -/
theorem feedbackHoldingJumpTrajectory_finite_jumps {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k,
      ∀ T : ℝ, Set.Finite {n | feedbackJumpTime n w ≤ T} := by
  filter_upwards [feedbackHoldingJumpTrajectory_nonexplosion hlam₀ hlam k] with w hw
  intro T
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp hw) (T + 1))
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have := hN n (Nat.le_of_not_gt h)
  change feedbackJumpTime n w ≤ T at hn
  linarith

end OTSelector.Limit
