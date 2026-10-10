import OTSelector.PointProcess.MatchingSceneMartingaleClosureCylinder
import OTSelector.PointProcess.CountingKernel
import OTSelector.Probability.CountingProcess.RightGridStopping
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The marked martingale problem from actual past-count cylinders

The filtration reveals only the root current and the marked counts already observed. Its
compensator drift is adapted by right-grid approximation of the actual count paths. Finite
continuous cylinder residual identities then imply the full martingale property.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.Probability

/-- Right-continuous observed paths admit jointly measurable evaluation below a fixed horizon.
No regularity of the sample-space topology is required. -/
theorem measurable_capped_of_rightContinuous {Ω : Type*} [MeasurableSpace Ω]
    (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ t ≤ T, Measurable (M t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t) :
    Measurable (fun p : ℝ≥0 × Ω ↦ M (min p.1 T) p.2) := by
  let A : ℕ → ℝ≥0 × Ω → ℝ := fun n p ↦
    M (min (CountingProcess.rightGrid (n + 1) p.1) T) p.2
  have hA (n : ℕ) : Measurable (A n) := by
    have hd : Measurable (fun p : ℕ × Ω ↦
        M (min ((p.1 : ℝ≥0) / (n + 1 : ℝ≥0)) T) p.2) :=
      measurable_from_prod_countable_right fun k ↦ by
        exact hm (min ((k : ℝ≥0) / (n + 1 : ℝ≥0)) T) (min_le_right _ _)
    have hp : Measurable (fun p : ℝ≥0 × Ω ↦
        (⌈(n + 1 : ℝ≥0) * p.1⌉₊, p.2)) :=
      (Nat.measurable_ceil.comp (measurable_const.mul measurable_fst)).prodMk measurable_snd
    simpa only [A, CountingProcess.rightGrid, Function.comp_def, Nat.cast_add, Nat.cast_one] using hd.comp hp
  apply measurable_of_tendsto_metrizable hA
  rw [tendsto_pi_nhds]
  intro p
  apply (hr p.2 (min p.1 T)).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨(CountingProcess.tendsto_rightGrid_succ p.1).min tendsto_const_nhds,
    Eventually.of_forall fun n ↦ min_le_min
      (CountingProcess.le_rightGrid (n + 1) p.1 (by omega)) le_rfl⟩

end OTSelector.Probability

namespace OTSelector.PointProcess.MatchingScene

/-- Root current, or one real marked-count observation at a specified time. -/
abbrev PastCountIndex := Unit ⊕ (ℝ≥0 × Bool × (UnitMark →ᵇ ℝ))

def pastCountTime : PastCountIndex → ℝ≥0
  | .inl _ => 0
  | .inr q => q.1

noncomputable def pastCountObservable (i : PastCountIndex) (scene : MatchingScene) : ℝ :=
  match i with
  | .inl _ => scene.path.rootCurrent
  | .inr q => LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene))
      q.2.1 q.2.2 q.1

/-- Fixed physical count readouts are measurable through the actual counting kernel. -/
theorem measurable_markedCount (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Measurable (fun scene : MatchingScene ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) b ψ t) := by
  have hi : Measurable (fun p : MatchingPoint ↦
      (LocalConfiguration.spatialIoc 0 t).indicator (fun p : MatchingPoint ↦ ψ p.2) p) :=
    (ψ.continuous.measurable.comp measurable_snd).indicator
      (LocalConfiguration.measurableSet_spatialIoc 0 t)
  have hm := (hi.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := LocalConfiguration.countingKernel (base := matchingPointBase))
  have hc : Measurable (fun scene : MatchingScene ↦
      Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) := by
    cases b <;> [exact measurable_target; exact measurable_source]
  have hh := hm.measurable.comp hc
  simpa only [Function.comp_def, LocalConfiguration.countingKernel_apply,
    LocalConfiguration.firstEventTestCount,
    integral_indicator (LocalConfiguration.measurableSet_spatialIoc 0 t)] using hh

theorem measurable_pastCountObservable (i : PastCountIndex) :
    Measurable (pastCountObservable i) := by
  cases i with
  | inl u =>
      exact (measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
        (FeedbackEnvironment.measurable_rootCurrent.comp Matching.measurable_feedbackSceneEnvironment)
  | inr q => exact measurable_markedCount q.2.1 q.2.2 q.1

abbrev PastCountAt (t : ℝ≥0) := {i : PastCountIndex // pastCountTime i ≤ t}

noncomputable def pastCountHistory (t : ℝ≥0) (scene : MatchingScene) : PastCountAt t → ℝ :=
  fun i ↦ pastCountObservable i.1 scene

theorem measurable_pastCountHistory (t : ℝ≥0) : Measurable (pastCountHistory t) :=
  measurable_pi_lambda _ fun i ↦ measurable_pastCountObservable i.1

/-- The actual minimal marked-count filtration, without graph or matching information. -/
noncomputable def markedCountFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace MatchingScene) where
  seq t := MeasurableSpace.comap (pastCountHistory t) inferInstance
  mono' s t hst := by
    let r : (PastCountAt t → ℝ) → PastCountAt s → ℝ :=
      fun x i ↦ x ⟨i.1, i.2.trans hst⟩
    have hr : Measurable r := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
    exact (hr.comp (comap_measurable (pastCountHistory t))).comap_le
  le' t := (measurable_pastCountHistory t).comap_le

/-- Every past coordinate is genuinely revealed by the natural count filtration. -/
theorem measurable_pastCountObservable_at {i : PastCountIndex} {t : ℝ≥0}
    (hit : pastCountTime i ≤ t) : Measurable[markedCountFiltration t] (pastCountObservable i) :=
  (measurable_pi_apply (⟨i, hit⟩ : PastCountAt t)).comp
    (comap_measurable (pastCountHistory t))

theorem markedCount_adapted (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Measurable[markedCountFiltration t] (fun scene ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) b ψ t) :=
  measurable_pastCountObservable_at (i := .inr (t, b, ψ)) le_rfl

theorem rootCurrent_markedCountFiltration (t : ℝ≥0) :
    Measurable[markedCountFiltration t] (fun scene : MatchingScene ↦ scene.path.rootCurrent) := by
  have hm := measurable_pastCountObservable_at (i := .inl ()) (t := t) (show (0 : ℝ≥0) ≤ t from bot_le)
  have hh := Int.measurable_floor.comp hm
  simpa only [Function.comp_def, pastCountObservable, Int.floor_intCast] using hh

private theorem current_eq_root_add_counts (scene : MatchingScene) (t : ℝ≥0) :
    Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment scene) t =
      Int.floor ((scene.path.rootCurrent : ℝ) +
        LocalConfiguration.firstEventTestCount
          (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene))
          true (fun _ ↦ 1) t -
        LocalConfiguration.firstEventTestCount
          (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene))
          false (fun _ ↦ 1) t) := by
  simp only [LocalConfiguration.firstEventTestCount_one, Limit.feedbackEnvironmentTwoColor,
    ite_true, Bool.false_eq_true, ite_false, ← Int.cast_add, ← Int.cast_sub, Int.floor_intCast]
  simp only [Limit.feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement,
    LocalConfiguration.orientedCount, Matching.feedbackSceneEnvironment]
  have hs : LocalConfiguration.spatialCount scene.source (t : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le scene.source t.property
  have ht : LocalConfiguration.spatialCount scene.target (t : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le scene.target t.property
  omega

/-- The actual compensator drift is measurable from counts up to its own horizon. -/
theorem drift_markedCountFiltration (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    (t : ℝ≥0) : Measurable[markedCountFiltration t] (fun scene ↦
      ∫ s in 0..(t : ℝ), Limit.feedbackEnvironmentMarkRate lam b ψ
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment scene) s)) := by
  let : MeasurableSpace MatchingScene := markedCountFiltration t
  let count (b : Bool) (s : ℝ≥0) (scene : MatchingScene) :=
    LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) b
      (fun _ ↦ (1 : ℝ)) s
  have hm (b : Bool) : Measurable (fun p : ℝ≥0 × MatchingScene ↦ count b (min p.1 t) p.2) :=
    Probability.measurable_capped_of_rightContinuous (count b) t
      (fun s hs ↦ (markedCount_adapted b (BoundedContinuousFunction.const UnitMark 1) s).mono
        (markedCountFiltration.mono hs) le_rfl)
      (fun scene s ↦ LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal _ _ _ _)
  have hr : Measurable (fun p : ℝ≥0 × MatchingScene ↦
      Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment p.2) ((min p.1 t : ℝ≥0) : ℝ)) := by
    have he (p : ℝ≥0 × MatchingScene) := current_eq_root_add_counts p.2 (min p.1 t)
    simp_rw [he]
    exact Int.measurable_floor.comp
      (((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
        ((rootCurrent_markedCountFiltration t).comp measurable_snd)).add (hm true) |>.sub (hm false))
  have hi : Measurable (fun p : MatchingScene × ℝ ↦
      Limit.feedbackEnvironmentMarkRate lam b ψ
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment p.1)
          ((min p.2.toNNReal t : ℝ≥0) : ℝ))) :=
    (measurable_of_countable (Limit.feedbackEnvironmentMarkRate lam b ψ)).comp
      (hr.comp (measurable_snd.real_toNNReal.prodMk measurable_fst))
  have hint := hi.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (t : ℝ)))
  have heq : (fun scene ↦ ∫ s in Ioc 0 (t : ℝ),
      Limit.feedbackEnvironmentMarkRate lam b ψ
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment scene)
          ((min s.toNNReal t : ℝ≥0) : ℝ))) =
      (fun scene ↦ ∫ s in 0..(t : ℝ), Limit.feedbackEnvironmentMarkRate lam b ψ
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment scene) s)) := by
    funext scene
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hst : s.toNNReal ≤ t := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2
    have he : ((min s.toNNReal t : ℝ≥0) : ℝ) = s := by
      rw [min_eq_left hst, Real.coe_toNNReal s hs.1.le]
    exact congrArg (fun r ↦ Limit.feedbackEnvironmentMarkRate lam b ψ
      (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment scene) r)) he
  exact heq ▸ hint.measurable

/-- Adaptedness of the genuine marked compensator is derived from the actual count history. -/
theorem markedCompensator_stronglyAdapted (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    StronglyAdapted markedCountFiltration (fun t scene ↦
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
        (Matching.feedbackSceneEnvironment scene)) := fun t ↦
  ((markedCount_adapted b ψ t).sub (drift_markedCountFiltration lam b ψ t)).stronglyMeasurable

/-- Finite mean local counts supply integrability of every continuous marked compensator. -/
theorem integrable_markedCompensator (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Integrable (fun scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) μ := by
  have htest : Integrable (fun scene ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) b ψ t) μ :=
    ((hcount b t).const_mul ‖ψ‖).mono' (measurable_markedCount b ψ t).aestronglyMeasurable
      (Eventually.of_forall fun scene ↦
        LocalConfiguration.norm_firstEventTestCount_le _ b ψ (le_refl (t : ℝ)))
  exact htest.sub (Limit.integrable_integral_feedbackEnvironmentMarkRate_current μ
    Matching.feedbackSceneEnvironment Matching.measurable_feedbackSceneEnvironment lam b ψ t)

/-- Actual finite past-count cylinder residual identities imply the complete marked spatial
martingale problem on the canonical count filtration. No martingale premise is used. -/
theorem markedCompensator_martingale_of_cylinder_residuals
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (lam : ℝ)
    (hres : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (s t : ℝ≥0), s ≤ t →
      ∀ (J : Finset (PastCountAt s)) (F : (J → ℝ) →ᵇ ℝ),
        (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
          (Matching.feedbackSceneEnvironment scene) -
          Limit.feedbackEnvironmentMarkedCompensator lam b ψ s
          (Matching.feedbackSceneEnvironment scene)) *
            F (J.restrict (pastCountHistory s scene)) ∂μ) = 0)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    Martingale (fun t scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) markedCountFiltration μ :=
  Probability.martingale_of_finite_continuous_cylinder_residuals μ markedCountFiltration _
    PastCountAt pastCountHistory measurable_pastCountHistory (fun _ ↦ rfl)
    (markedCompensator_stronglyAdapted lam b ψ)
    (integrable_markedCompensator μ hcount lam b ψ) (hres b ψ)

end OTSelector.PointProcess.MatchingScene
