import OTSelector.Limit.FeedbackRegenerationHolding

/-!
# Laplace transforms of the actual feedback waits

The exponential density gives its Laplace transform directly. The feedback kernel then yields a
uniform contraction and the actual conditional Laplace transform along the constructed trajectory.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace OTSelector.Limit

/-- The nonnegative Laplace weight on a real waiting time. -/
noncomputable def waitLaplace (theta t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(theta * t)))

@[fun_prop]
theorem measurable_waitLaplace (theta : ℝ) : Measurable (waitLaplace theta) := by
  unfold waitLaplace
  fun_prop

/-- The exponential waiting law has its exact Laplace transform. -/
theorem lintegral_waitLaplace_expMeasure {r theta : ℝ} (hr : 0 < r) (htheta : 0 ≤ theta) :
    ∫⁻ t, waitLaplace theta t ∂expMeasure r = ENNReal.ofReal (r / (r + theta)) := by
  have hr' : 0 < r + theta := by linarith
  have hpdf (t : ℝ) : exponentialPDF r t * waitLaplace theta t =
      ENNReal.ofReal (r / (r + theta)) * exponentialPDF (r + theta) t := by
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht, waitLaplace,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        r * Real.exp (-(r * t)) * Real.exp (-(theta * t)) =
            r * Real.exp (-((r + theta) * t)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ = r / (r + theta) * ((r + theta) * Real.exp (-((r + theta) * t))) := by
          field_simp
    · simp [exponentialPDF_of_neg (lt_of_not_ge ht)]
  change ∫⁻ t, waitLaplace theta t ∂volume.withDensity (exponentialPDF r) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold exponentialPDF; fun_prop)
      (measurable_waitLaplace theta)]
  simp only [Pi.mul_apply, hpdf]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one hr', mul_one]

/-- Exact one-step Laplace transform under the actual feedback product kernel. -/
theorem feedbackHoldingJumpKernel_laplace {lam theta : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (htheta : 0 ≤ theta) (k : ℤ) :
    ∫⁻ z, waitLaplace theta z.1 ∂feedbackHoldingJumpKernel lam k =
      ENNReal.ofReal (totalJumpRate lam k / (totalJumpRate lam k + theta)) := by
  rw [← lintegral_map (measurable_waitLaplace theta) measurable_fst,
    feedbackHoldingJumpKernel_map_wait hlam₀ hlam]
  exact lintegral_waitLaplace_expMeasure (totalJumpRate_pos hlam₀ hlam k) htheta

/-- Every actual one-step Laplace transform is bounded by the largest-rate transform. -/
theorem feedbackHoldingJumpKernel_laplace_le {lam theta : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (htheta : 0 ≤ theta) (k : ℤ) :
    ∫⁻ z, waitLaplace theta z.1 ∂feedbackHoldingJumpKernel lam k ≤
      ENNReal.ofReal ((2 + lam) / (2 + lam + theta)) := by
  rw [feedbackHoldingJumpKernel_laplace hlam₀ hlam htheta]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ (by linarith [totalJumpRate_pos hlam₀ hlam k]) (by linarith)).mpr
  nlinarith [(totalJumpRate_bounds hlam₀ k).2]

/-- The conditional Laplace transform is derived from the trajectory's proved conditional law. -/
theorem feedbackHoldingJumpTrajectory_condLaplace {lam theta : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (htheta : 0 ≤ theta) (k : ℤ) (n : ℕ) :
    (fun x ↦ ∫⁻ z, waitLaplace theta z.1 ∂condDistrib
      (fun w : ℕ → ℝ × ℤ ↦ w (n + 1)) (frestrictLe n)
      (feedbackHoldingJumpTrajectory lam hlam₀ hlam k) x) =ᵐ[
        (feedbackHoldingJumpTrajectory lam hlam₀ hlam k).map (frestrictLe n)]
      fun x ↦ ENNReal.ofReal (totalJumpRate lam (x ⟨n, by simp⟩).2 /
        (totalJumpRate lam (x ⟨n, by simp⟩).2 + theta)) := by
  filter_upwards [feedbackHoldingJumpTrajectory_condDistrib hlam₀ hlam k n] with x hx
  rw [hx]
  exact feedbackHoldingJumpKernel_laplace hlam₀ hlam htheta _

end OTSelector.Limit
