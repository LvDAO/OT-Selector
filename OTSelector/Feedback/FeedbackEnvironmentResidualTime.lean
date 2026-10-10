import OTSelector.PointProcess.MatchingScenePastCountApproximation
import OTSelector.PointProcess.MatchingSceneMartingaleClosureTime

/-!
# Nonnegative rational times determine the original past-cylinder residuals

The actual marked compensator is right continuous. Rounding a time up on successive integer
grids keeps every approximation below a single larger horizon, whose genuine local count
is an integrable envelope. Thus the rational-time identities extend by dominated convergence
to all nonnegative times without changing the compact past tests or their outer cylinder.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology CompactlySupported BoundedContinuousFunction

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

/-- Identities at the countable times `a / (d + 1)` suffice for the full original compact
past-cylinder residual family. The only domination input is the first moment of the actual
local two-color counts. -/
theorem pastCylinderResidualIdentities_of_nonneg_rational
    (μ : Measure MatchingScene) [IsFiniteMeasure μ] (lam : ℝ)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b)
    0 t : ℝ)) μ)
    (hrat : ∀ (ns nt : ℕ) (fs : Fin ns → C_c(MatchingPoint, ℝ))
      (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ),
      (∀ i p, 0 ≤ p.1 → fs i p = 0) → (∀ i p, 0 ≤ p.1 → ft i p = 0) →
      ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (d a : ℕ),
        (∫ scene, pastMarkedResidual lam fs ft H b ψ
          ((a : ℝ≥0) / (d + 1 : ℕ)) scene ∂μ) = 0) :
    PastCylinderResidualIdentities μ lam := by
  intro ns nt fs ft H hfs hft b ψ t
  let M (r : ℝ≥0) (scene : MatchingScene) :=
    Limit.feedbackEnvironmentMarkedCompensator lam b ψ r
      (Matching.feedbackSceneEnvironment scene)
  let D (scene : MatchingScene) : ℝ :=
    ‖ψ‖ * (LocalConfiguration.spatialCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b)
        0 (t + 1) : ℝ) +
      Limit.feedbackEnvironmentMarkRateBound lam b ψ * ((t + 1 : ℝ≥0) : ℝ)
  have hiD : Integrable D μ :=
    ((hcount b (t + 1)).const_mul ‖ψ‖).add (integrable_const _)
  have hgridBound (n : ℕ) : CountingProcess.rightGrid (n + 1) t ≤ t + 1 := by
    apply (CountingProcess.rightGrid_lt_add_inv (n + 1) t (by omega)).le.trans
    apply add_le_add le_rfl
    apply (inv_le_one₀ (show (0 : ℝ≥0) < (n + 1 : ℕ) by positivity)).mpr
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hbound (n : ℕ) (scene : MatchingScene) :
      ‖pastMarkedResidual lam fs ft H b ψ
        (CountingProcess.rightGrid (n + 1) t) scene‖ ≤ ‖H‖ * D scene := by
    have hMbound := norm_markedCompensator_le_localCount lam b ψ scene
      (s := CountingProcess.rightGrid (n + 1) t) (T := t + 1) (hgridBound n)
    change ‖M (CountingProcess.rightGrid (n + 1) t) scene‖ ≤ D scene at hMbound
    rw [pastMarkedResidual, norm_mul]
    exact mul_le_mul
      (norm_environmentPastCylinder_le fs ft H (Matching.feedbackSceneEnvironment scene))
      hMbound
      (norm_nonneg _) (norm_nonneg _)
  have hlim (scene : MatchingScene) :
      Tendsto (fun n ↦ M (CountingProcess.rightGrid (n + 1) t) scene)
        atTop (𝓝 (M t scene)) := by
    apply (Limit.continuousWithinAt_feedbackEnvironmentMarkedCompensator
      lam b ψ (Matching.feedbackSceneEnvironment scene) t).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨CountingProcess.tendsto_rightGrid_succ t,
      Eventually.of_forall fun n ↦ CountingProcess.le_rightGrid (n + 1) t (by omega)⟩
  have hconv := tendsto_integral_of_dominated_convergence
    (f := fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene)
    (fun scene ↦ ‖H‖ * D scene)
    (fun n ↦ (measurable_pastMarkedResidual lam fs ft H b ψ
      (CountingProcess.rightGrid (n + 1) t)).aestronglyMeasurable)
    (hiD.const_mul ‖H‖)
    (fun n ↦ Eventually.of_forall (hbound n))
    (Eventually.of_forall fun scene ↦ tendsto_const_nhds.mul (hlim scene))
  have hzero (n : ℕ) :
      (∫ scene, pastMarkedResidual lam fs ft H b ψ
        (CountingProcess.rightGrid (n + 1) t) scene ∂μ) = 0 :=
    hrat ns nt fs ft H hfs hft b ψ n ⌈((n + 1 : ℕ) : ℝ≥0) * t⌉₊
  exact tendsto_nhds_unique hconv (by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))

end OTSelector.PointProcess.MatchingScene
