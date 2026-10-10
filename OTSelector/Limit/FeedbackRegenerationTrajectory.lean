import OTSelector.Limit.FeedbackRegeneration
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite trajectories of the actual feedback jump chain

Ionescu--Tulcea constructs the path measure from the explicit nearest-neighbor feedback kernel.
The conditional next-state law is proved, and the rate-biased invariant law gives stationary
one-time marginals. This is the discrete skeleton; its spatial suspension is a separate step.
-/

open MeasureTheory ProbabilityTheory Function Preorder
open scoped ENNReal ProbabilityTheory

namespace OTSelector.Limit

/-- The feedback transition reads the last current in the finite history. -/
noncomputable def feedbackJumpHistoryKernel (lam : ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℤ) ℤ :=
  (feedbackJumpKernel lam).comap (fun x ↦ x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

theorem feedbackJumpHistoryKernel_isMarkov {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) : IsMarkovKernel (feedbackJumpHistoryKernel lam n) := by
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  unfold feedbackJumpHistoryKernel
  infer_instance

/-- The actual infinite jump-chain law from any initial current distribution. -/
noncomputable def feedbackJumpTrajectory (lam : ℝ) (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (μ : Measure ℤ) : Measure (ℕ → ℤ) := by
  let := feedbackJumpHistoryKernel_isMarkov hlam₀ hlam
  exact Kernel.trajMeasure (X := fun _ ↦ ℤ) μ (feedbackJumpHistoryKernel lam)

instance feedbackJumpTrajectory_isProbability {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (feedbackJumpTrajectory lam hlam₀ hlam μ) := by
  let := feedbackJumpHistoryKernel_isMarkov hlam₀ hlam
  unfold feedbackJumpTrajectory
  infer_instance

/-- Its conditional transition law is the actual feedback kernel, not an input assumption. -/
theorem feedbackJumpTrajectory_condDistrib {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    condDistrib (fun x : ℕ → ℤ ↦ x (n + 1)) (frestrictLe n)
      (feedbackJumpTrajectory lam hlam₀ hlam μ) =ᵐ[
        (feedbackJumpTrajectory lam hlam₀ hlam μ).map (frestrictLe n)]
          feedbackJumpHistoryKernel lam n := by
  let := feedbackJumpHistoryKernel_isMarkov hlam₀ hlam
  exact Kernel.condDistrib_trajMeasure (X := fun _ ↦ ℤ)

/-- The initial coordinate retains the prescribed law. -/
theorem feedbackJumpTrajectory_map_zero {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (μ : Measure ℤ) :
    (feedbackJumpTrajectory lam hlam₀ hlam μ).map (fun x ↦ x 0) = μ := by
  let := feedbackJumpHistoryKernel_isMarkov hlam₀ hlam
  have hmap : (Kernel.traj (X := fun _ ↦ ℤ) (feedbackJumpHistoryKernel lam) 0).map
      (fun x : ℕ → ℤ ↦ x 0) =
      Kernel.deterministic (fun x : (i : Finset.Iic 0) → ℤ ↦ x ⟨0, by simp⟩)
        (measurable_pi_apply _) := by
    change (Kernel.traj (X := fun _ ↦ ℤ) (feedbackJumpHistoryKernel lam) 0).map
      ((fun x : (i : Finset.Iic 0) → ℤ ↦ x ⟨0, by simp⟩) ∘ frestrictLe 0) = _
    rw [Kernel.map_comp_right _ (measurable_frestrictLe _) (measurable_pi_apply _),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map]
  unfold feedbackJumpTrajectory Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply _), hmap,
    Measure.deterministic_comp_eq_map, Measure.map_map]
  · convert (Measure.map_id (μ := μ)) using 1
    congr 1
  · exact measurable_pi_apply _
  · fun_prop

/-- The one-time marginal evolves by the constructed jump kernel. -/
theorem feedbackJumpTrajectory_map_succ {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    (feedbackJumpTrajectory lam hlam₀ hlam μ).map (fun x ↦ x (n + 1)) =
      (feedbackJumpKernel lam) ∘ₘ
        (feedbackJumpTrajectory lam hlam₀ hlam μ).map (fun x ↦ x n) := by
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  let := feedbackJumpHistoryKernel_isMarkov hlam₀ hlam
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ ℤ) (μ₀ := μ) (κ := feedbackJumpHistoryKernel lam) (a := n)
  have hs := congrArg Measure.snd h
  rw [Measure.snd_compProd] at hs
  have hright : ((Kernel.trajMeasure (X := fun _ ↦ ℤ) μ (feedbackJumpHistoryKernel lam)).map
      (fun x ↦ (frestrictLe n x, x (n + 1)))).snd =
      (Kernel.trajMeasure (X := fun _ ↦ ℤ) μ (feedbackJumpHistoryKernel lam)).map
        (fun x ↦ x (n + 1)) := by
    rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hright] at hs
  unfold feedbackJumpTrajectory
  rw [← hs]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)]
  rfl

/-- Starting at the derived jump-time law makes every current marginal equal to that law. -/
theorem feedbackJumpTrajectory_stationary_marginals {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    (feedbackJumpTrajectory lam hlam₀ hlam (jumpInvariantMeasure lam)).map
      (fun x ↦ x n) = jumpInvariantMeasure lam := by
  let := jumpInvariantMeasure_isProbability hlam₀ hlam
  induction n with
  | zero => exact feedbackJumpTrajectory_map_zero hlam₀ hlam _
  | succ n ih =>
      rw [feedbackJumpTrajectory_map_succ hlam₀ hlam, ih]
      exact feedbackJumpKernel_invariant hlam₀ hlam

end OTSelector.Limit
