import OTSelector.Limit.FeedbackMarkedTrajectory
import OTSelector.Limit.FeedbackMartingaleProblemFirstJump

/-!+# Identification of the feedback marked history law

Once the conditional holding/mark/current kernel has been identified at successive jump times,
its initial value and finite-history transitions determine the whole marked trajectory. This is
the discrete-history part of martingale-problem uniqueness; deriving these transitions from the
spatial martingale equations is a separate step.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal

namespace OTSelector.Limit

/-- A law with the actual feedback one-step conditional kernels is the constructed marked
trajectory law. The coordinate at zero is the virtual initial state, with zero wait and mark. -/
theorem feedbackMarkedTrajectory_eq_of_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (μ : Measure (ℕ → FeedbackMarkedStep))
    [IsProbabilityMeasure μ]
    (hinit : μ.map (fun w ↦ w 0) = Measure.dirac (0, ⟨0, by simp⟩, k))
    (hstep : ∀ n, condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1))
      (frestrictLe n) μ =ᵐ[μ.map (frestrictLe n)] feedbackMarkedHistoryKernel lam n) :
    μ = feedbackMarkedTrajectory lam hlam0 hlam k := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  apply TrajectoryProjection.ext_prefix
  intro n
  induction n with
  | zero =>
      unfold feedbackMarkedTrajectory
      rw [TrajectoryProjection.trajMeasure_prefix_zero, ← hinit]
      rw [Measure.map_map (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic (0 : ℕ) ↦ FeedbackMarkedStep)).symm.measurable
        (measurable_pi_apply 0)]
      congr 1
      funext w i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.2; omega
      simp [hi]
  | succ n ih =>
      have hpair : μ.map (fun w ↦ (frestrictLe n w, w (n + 1))) =
          μ.map (frestrictLe n) ⊗ₘ feedbackMarkedHistoryKernel lam n :=
        (condDistrib_ae_eq_iff_measure_eq_compProd _
          (measurable_pi_apply _).aemeasurable _).mp (hstep n)
      have hnext : μ.map (frestrictLe (n + 1)) =
          (μ.map (frestrictLe n) ⊗ₘ feedbackMarkedHistoryKernel lam n).map
            (TrajectoryProjection.snoc n) := by
        rw [← hpair, Measure.map_map (TrajectoryProjection.measurable_snoc n) (by fun_prop)]
        simp only [Function.comp_def, TrajectoryProjection.snoc_restrict]
      rw [hnext, ih]
      exact (TrajectoryProjection.trajMeasure_prefix_succ _ _ n).symm

/-- Identification of the marked history law also identifies every measurable path observable. -/
theorem feedbackMarkedTrajectory_map_eq_of_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (μ : Measure (ℕ → FeedbackMarkedStep))
    [IsProbabilityMeasure μ]
    (hinit : μ.map (fun w ↦ w 0) = Measure.dirac (0, ⟨0, by simp⟩, k))
    (hstep : ∀ n, condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1))
      (frestrictLe n) μ =ᵐ[μ.map (frestrictLe n)] feedbackMarkedHistoryKernel lam n)
    {E : Type*} [MeasurableSpace E] (f : (ℕ → FeedbackMarkedStep) → E) :
    μ.map f = (feedbackMarkedTrajectory lam hlam0 hlam k).map f := by
  rw [feedbackMarkedTrajectory_eq_of_condDistrib hlam0 hlam k μ hinit hstep]

/-- The identified conditional kernels force nonexplosion; no nonexplosion hypothesis is needed
at the level of the infinite holding/mark/current sequence. -/
theorem feedbackMarkedTrajectory_nonexplosion_of_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (μ : Measure (ℕ → FeedbackMarkedStep))
    [IsProbabilityMeasure μ]
    (hinit : μ.map (fun w ↦ w 0) = Measure.dirac (0, ⟨0, by simp⟩, k))
    (hstep : ∀ n, condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1))
      (frestrictLe n) μ =ᵐ[μ.map (frestrictLe n)] feedbackMarkedHistoryKernel lam n) :
    ∀ᵐ w ∂μ, Tendsto
      (fun n ↦ feedbackJumpTime n (feedbackMarkedTrajectoryProjection w)) atTop atTop := by
  rw [feedbackMarkedTrajectory_eq_of_condDistrib hlam0 hlam k μ hinit hstep]
  exact feedbackMarkedTrajectory_nonexplosion hlam0 hlam k

/-- Conditional stopped first-count equations at every finite history identify the whole actual
marked trajectory. The premises are the linear compensator equations, not transition-law or
process-law uniqueness assumptions. -/
theorem feedbackMarkedTrajectory_eq_of_conditional_compensator {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (μ : Measure (ℕ → FeedbackMarkedStep))
    [IsProbabilityMeasure μ]
    (hinit : μ.map (fun w ↦ w 0) = Measure.dirac (0, ⟨0, by simp⟩, k))
    (hcomp : ∀ n, ∀ᵐ x ∂μ.map (frestrictLe n),
      ∀ t, 0 ≤ t → ∀ B : Set (UnitMark × ℤ), MeasurableSet B →
        (condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1)) (frestrictLe n) μ x).real
          (Set.Iic t ×ˢ B) =
        totalJumpRate lam (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2 *
          (feedbackMarkedJumpKernel lam (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2).real B *
            ∫ s in 0..t, 1 -
              (condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1))
                (frestrictLe n) μ x).real (Set.Iic s ×ˢ Set.univ)) :
    μ = feedbackMarkedTrajectory lam hlam0 hlam k := by
  apply feedbackMarkedTrajectory_eq_of_condDistrib hlam0 hlam k μ hinit
  intro n
  filter_upwards [hcomp n] with x hx
  exact feedbackMarkedHoldingKernel_eq_of_compensator hlam0 hlam _ _ hx

end OTSelector.Limit
