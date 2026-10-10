import OTSelector.PointProcess.MatchingSceneMartingaleClosure

/-!
# Rational grids suffice for the actual marked martingale identities

Every observed time and both increment endpoints are rounded up on the same integer grid.
Order is preserved, count paths are right continuous, and the local unweighted count gives an
integrable common envelope. Consequently grid-cylinder identities imply all real-time ones.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

/-- A countable time/color index, before selecting a continuous geometric mark test. -/
abbrev GridPastCountIndex := Unit ⊕ (ℕ × Bool × (UnitMark →ᵇ ℝ))

noncomputable def gridPastCountIndex (d : ℕ) : GridPastCountIndex → PastCountIndex
  | .inl u => .inl u
  | .inr q => .inr ((q.1 : ℝ≥0) / d, q.2.1, q.2.2)

private noncomputable def roundPastCountIndex (d : ℕ) : PastCountIndex → GridPastCountIndex
  | .inl u => .inl u
  | .inr q => .inr (⌈(d : ℝ≥0) * q.1⌉₊, q.2.1, q.2.2)

private theorem rightGrid_mono (d : ℕ) : Monotone (CountingProcess.rightGrid d) := by
  intro s t hst
  unfold CountingProcess.rightGrid
  exact div_le_div_of_nonneg_right (by
    exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_left hst (show 0 ≤ (d : ℝ≥0) from bot_le)))
    (show 0 ≤ (d : ℝ≥0) from bot_le)

private theorem rightGrid_succ_le_add_one (n : ℕ) (t : ℝ≥0) :
    CountingProcess.rightGrid (n + 1) t ≤ t + 1 := by
  apply (CountingProcess.rightGrid_lt_add_inv (n + 1) t (by omega)).le.trans
  apply add_le_add le_rfl
  apply (inv_le_one₀ (show (0 : ℝ≥0) < (n + 1 : ℕ) by positivity)).mpr
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

private theorem roundPastCount_time_le (d : ℕ) (i : PastCountIndex) :
    pastCountTime (gridPastCountIndex d (roundPastCountIndex d i)) ≤
      CountingProcess.rightGrid d (pastCountTime i) := by
  cases i with
  | inl u => exact bot_le
  | inr q => exact le_rfl

private theorem tendsto_roundPastCountObservable (i : PastCountIndex) (scene : MatchingScene) :
    Tendsto (fun n ↦ pastCountObservable
      (gridPastCountIndex (n + 1) (roundPastCountIndex (n + 1) i)) scene)
      atTop (𝓝 (pastCountObservable i scene)) := by
  cases i with
  | inl u => exact tendsto_const_nhds
  | inr q =>
      apply (LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene))
        q.2.1 q.2.2 q.1).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨CountingProcess.tendsto_rightGrid_succ q.1,
        Eventually.of_forall fun n ↦ CountingProcess.le_rightGrid (n + 1) q.1 (by omega)⟩

/-- The grid identities use finite vectors indexed by `Fin m`, so their time coordinates
form a countable family. Mark and outer-function separability may be applied independently. -/
def GridMarkedResidualIdentities (μ : Measure MatchingScene) (lam : ℝ) : Prop :=
  ∀ (d a b : ℕ), 0 < d → a ≤ b → ∀ (m : ℕ) (i : Fin m → GridPastCountIndex),
    (∀ j, pastCountTime (gridPastCountIndex d (i j)) ≤ (a : ℝ≥0) / d) →
    ∀ (color : Bool) (ψ : UnitMark →ᵇ ℝ) (F : (Fin m → ℝ) →ᵇ ℝ),
      (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam color ψ ((b : ℝ≥0) / d)
        (Matching.feedbackSceneEnvironment scene) -
        Limit.feedbackEnvironmentMarkedCompensator lam color ψ ((a : ℝ≥0) / d)
        (Matching.feedbackSceneEnvironment scene)) *
        F (fun j ↦ pastCountObservable (gridPastCountIndex d (i j)) scene) ∂μ) = 0

private theorem gridMarkedResidual_of_fintype {μ : Measure MatchingScene} {lam : ℝ}
    (hgrid : GridMarkedResidualIdentities μ lam)
    {J : Type*} [Fintype J] (d a b : ℕ) (hd : 0 < d) (hab : a ≤ b)
    (i : J → GridPastCountIndex)
    (hi : ∀ j, pastCountTime (gridPastCountIndex d (i j)) ≤ (a : ℝ≥0) / d)
    (color : Bool) (ψ : UnitMark →ᵇ ℝ) (F : (J → ℝ) →ᵇ ℝ) :
    (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam color ψ ((b : ℝ≥0) / d)
      (Matching.feedbackSceneEnvironment scene) -
      Limit.feedbackEnvironmentMarkedCompensator lam color ψ ((a : ℝ≥0) / d)
      (Matching.feedbackSceneEnvironment scene)) *
      F (fun j ↦ pastCountObservable (gridPastCountIndex d (i j)) scene) ∂μ) = 0 := by
  let e := Fintype.equivFin J
  let G : (Fin (Fintype.card J) → ℝ) →ᵇ ℝ :=
    F.compContinuous ⟨fun x j ↦ x (e j), continuous_pi fun _ ↦ continuous_apply _⟩
  have hh := hgrid d a b hd hab (Fintype.card J) (fun k ↦ i (e.symm k))
    (fun k ↦ hi (e.symm k)) color ψ G
  simpa only [G, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    Equiv.symm_apply_apply] using hh

/-- One local count at the horizon dominates every earlier actual marked compensator. -/
theorem norm_markedCompensator_le_localCount (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    (scene : MatchingScene) {s T : ℝ≥0} (hsT : s ≤ T) :
    ‖Limit.feedbackEnvironmentMarkedCompensator lam b ψ s
      (Matching.feedbackSceneEnvironment scene)‖ ≤
      ‖ψ‖ * (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 T : ℝ) +
      Limit.feedbackEnvironmentMarkRateBound lam b ψ * (T : ℝ) := by
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact LocalConfiguration.norm_firstEventTestCount_le _ b ψ (by exact_mod_cast hsT)
  · apply (Limit.norm_integral_feedbackEnvironmentMarkRate_current_le lam b ψ _ s).trans
    exact mul_le_mul_of_nonneg_left
      ((abs_of_nonneg s.property).le.trans (show (s : ℝ) ≤ (T : ℝ) by exact_mod_cast hsT))
      (Limit.feedbackEnvironmentMarkRateBound_nonneg lam b ψ)

/-- Right-grid cylinder identities extend to arbitrary real times under the actual local
count integrability bound. No continuity of the scene carrier is needed in this limit. -/
theorem cylinder_residuals_of_grid
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (lam : ℝ) (hgrid : GridMarkedResidualIdentities μ lam)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (J : Finset (PastCountAt s)) (F : (J → ℝ) →ᵇ ℝ) :
    (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene) -
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ s
      (Matching.feedbackSceneEnvironment scene)) *
        F (J.restrict (pastCountHistory s scene)) ∂μ) = 0 := by
  let M := fun r scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ r
    (Matching.feedbackSceneEnvironment scene)
  let D : MatchingScene → ℝ := fun scene ↦
    ‖ψ‖ * (LocalConfiguration.spatialCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 (t + 1) : ℝ) +
      Limit.feedbackEnvironmentMarkRateBound lam b ψ * ((t + 1 : ℝ≥0) : ℝ)
  let X : ℕ → MatchingScene → J → ℝ := fun n scene j ↦
    pastCountObservable (gridPastCountIndex (n + 1)
      (roundPastCountIndex (n + 1) j.1.1)) scene
  let U : ℕ → MatchingScene → ℝ := fun n scene ↦
    (M (CountingProcess.rightGrid (n + 1) t) scene -
      M (CountingProcess.rightGrid (n + 1) s) scene) * F (X n scene)
  have hiD : Integrable D μ := ((hcount b (t + 1)).const_mul ‖ψ‖).add (integrable_const _)
  have hMm (r : ℝ≥0) : Measurable (M r) :=
    ((markedCompensator_stronglyAdapted lam b ψ r).measurable).mono
      (markedCountFiltration.le r) le_rfl
  have hXm (n : ℕ) : Measurable (X n) :=
    measurable_pi_lambda _ fun j ↦ measurable_pastCountObservable _
  have hlim (r : ℝ≥0) (scene : MatchingScene) :
      Tendsto (fun n ↦ M (CountingProcess.rightGrid (n + 1) r) scene) atTop (𝓝 (M r scene)) := by
    apply (Limit.continuousWithinAt_feedbackEnvironmentMarkedCompensator lam b ψ _ r).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨CountingProcess.tendsto_rightGrid_succ r,
      Eventually.of_forall fun n ↦ CountingProcess.le_rightGrid (n + 1) r (by omega)⟩
  have hU0 (n : ℕ) : (∫ scene, U n scene ∂μ) = 0 := by
    exact gridMarkedResidual_of_fintype hgrid (n + 1)
      ⌈((n + 1 : ℕ) : ℝ≥0) * s⌉₊ ⌈((n + 1 : ℕ) : ℝ≥0) * t⌉₊ (by omega)
      (Nat.ceil_mono (mul_le_mul_of_nonneg_left hst (by positivity)))
      (fun j : J ↦ roundPastCountIndex (n + 1) j.1.1)
      (fun j ↦ (roundPastCount_time_le (n + 1) j.1.1).trans
        (rightGrid_mono (n + 1) j.1.2)) b ψ F
  have hbound (n : ℕ) (scene : MatchingScene) : ‖U n scene‖ ≤ (2 * D scene) * ‖F‖ := by
    have hs : CountingProcess.rightGrid (n + 1) s ≤ t + 1 :=
      (rightGrid_mono (n + 1) hst).trans (rightGrid_succ_le_add_one n t)
    have ht := rightGrid_succ_le_add_one n t
    have hsD := norm_markedCompensator_le_localCount lam b ψ scene hs
    have htD := norm_markedCompensator_le_localCount lam b ψ scene ht
    change ‖M (CountingProcess.rightGrid (n + 1) s) scene‖ ≤ D scene at hsD
    change ‖M (CountingProcess.rightGrid (n + 1) t) scene‖ ≤ D scene at htD
    calc
      _ = ‖M (CountingProcess.rightGrid (n + 1) t) scene -
          M (CountingProcess.rightGrid (n + 1) s) scene‖ * ‖F (X n scene)‖ := norm_mul _ _
      _ ≤ (D scene + D scene) * ‖F‖ :=
        mul_le_mul ((norm_sub_le _ _).trans (add_le_add htD hsD)) (F.norm_coe_le_norm _)
          (norm_nonneg _) (by linarith [norm_nonneg (M (CountingProcess.rightGrid (n + 1) t) scene)])
      _ = _ := by ring
  have hconv := tendsto_integral_of_dominated_convergence
    (fun scene ↦ (2 * D scene) * ‖F‖)
    (fun n ↦ ((hMm _).sub (hMm _) |>.mul (F.continuous.measurable.comp (hXm n))).aestronglyMeasurable)
    ((hiD.const_mul 2).mul_const ‖F‖)
    (fun n ↦ Eventually.of_forall (hbound n))
    (Eventually.of_forall fun scene ↦ (hlim t scene).sub (hlim s scene) |>.mul
      (F.continuous.tendsto _ |>.comp (tendsto_pi_nhds.mpr fun j ↦
        tendsto_roundPastCountObservable j.1.1 scene)))
  have hz : Tendsto (fun n ↦ ∫ scene, U n scene ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hU0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  exact (tendsto_nhds_unique hconv hz)

/-- The actual marked martingale problem needs only residual tests with rational grid times. -/
theorem markedCompensator_martingale_of_grid_residuals
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (lam : ℝ) (hgrid : GridMarkedResidualIdentities μ lam)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    Martingale (fun t scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) markedCountFiltration μ :=
  markedCompensator_martingale_of_cylinder_residuals μ hcount lam
    (cylinder_residuals_of_grid μ hcount lam hgrid) b ψ

end OTSelector.PointProcess.MatchingScene
