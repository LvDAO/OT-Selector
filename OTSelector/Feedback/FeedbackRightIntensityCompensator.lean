import OTSelector.Feedback.FeedbackRightIntensityConditionalLaw
import OTSelector.Feedback.FeedbackTerminalAreaGeometry

/-!
# One-point compensator calculation for the frozen right tail

The calculation integrates a surviving marked point under its genuine law conditioned to the
boundary complement.  The remaining area cancels against the one-point survival probability.
Fubini then identifies the expected crossing-window count with its integrated hazard.

`FeedbackRightIntensityRawRectangle` proves the future-fiber invariance, the finite-product
Fubini identity, and the source/target fixed-boundary raw rectangles.  It also converts the
integrated hazard to the strict-left remaining count by removing finitely many path times.
`FeedbackRightIntensityRawRectangleBoundary` transports those formulas to the actual dependent
unseen-label tuple and its normalized remaining rectangle.  The snapshot completion identities
and measurability of future-history sections are in `FeedbackRightIntensityRawRectangleSnapshot`.

The remaining bridge tests these section formulas against a bulk-boundary event using
`setIntegral_actualBoundaryEvaluation_eq_candidate`, then extends boundary-event/future-cylinder
intersections to the joined raw sigma-algebra.  Predictable masking and the almost-everywhere
tie-free transfer must still be matched to the resulting rectangle identity before concluding
`HasPredictableIntensity` for the actual masked rank process.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

/-- The elementary Fubini calculation for a lifetime whose survival mass is affine on the
interval.  The survival hypothesis describes its one-point distribution; no martingale or
compensator identity is assumed. -/
theorem affineSurvival_onePoint_compensator
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (X : Ω → ℝ) (hX : Measurable X)
    {s t K D : ℝ} (hst : s ≤ t) (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ u ∈ Icc s t, ν.real {ω | u < X ω} = (K - u) / D)
    (c : ℝ) :
    (∫ _ω in {ω | s < X ω ∧ X ω ≤ t}, c ∂ν) =
      ∫ ω, ∫ u in Ioc s t, if u < X ω then c / (K - u) else 0 ∂volume ∂ν := by
  let R : Ω × ℝ → ℝ := fun z ↦
    if z.2 ∈ Ioc s t ∧ z.2 < X z.1 then c / (K - z.2) else 0
  have hRmeas : Measurable R :=
    Measurable.ite ((measurable_snd measurableSet_Ioc).inter
      (measurableSet_lt measurable_snd (hX.comp measurable_fst)))
      (measurable_const.div (measurable_const.sub measurable_snd)) measurable_const
  have hRbound : ∀ z, ‖R z‖ ≤ ‖c‖ / (K - t) := by
    intro z
    by_cases hz : z.2 ∈ Ioc s t ∧ z.2 < X z.1
    · have hden : 0 < K - z.2 := hfloor.trans_le (sub_le_sub_left hz.1.2 K)
      rw [show R z = c / (K - z.2) by simp only [R, ite_eq_left hz], norm_div,
        Real.norm_of_nonneg hden.le]
      exact div_le_div_of_nonneg_left (norm_nonneg c) hfloor (sub_le_sub_left hz.1.2 K)
    · simp only [R, ite_eq_right hz, norm_zero]
      exact div_nonneg (norm_nonneg c) hfloor.le
  have hRint : Integrable R (ν.prod (volume.restrict (Ioc s t))) :=
    Integrable.of_bound hRmeas.aestronglyMeasurable (‖c‖ / (K - t))
      (ae_of_all _ hRbound)
  have hinner : ∀ u ∈ Ioc s t, (∫ ω, R (ω, u) ∂ν) = c / D := by
    intro u hu
    have hden : K - u ≠ 0 :=
      ne_of_gt (hfloor.trans_le (sub_le_sub_left hu.2 K))
    have hfun : (fun ω ↦ R (ω, u)) =
        {ω | u < X ω}.indicator (fun _ ↦ c / (K - u)) := by
      funext ω
      simp only [R, hu, true_and, Set.indicator, mem_ofPred_eq]
    rw [hfun, integral_indicator_const _ (measurableSet_lt measurable_const hX)]
    change ν.real {ω | u < X ω} * (c / (K - u)) = c / D
    rw [hsurvival u ⟨hu.1.le, hu.2⟩]
    field_simp
  have hleft : (∫ ω in {ω | s < X ω ∧ X ω ≤ t}, c ∂ν) =
      (t - s) * (c / D) := by
    have hset : {ω | s < X ω ∧ X ω ≤ t} =
        {ω | s < X ω} \ {ω | t < X ω} := by
      ext ω
      simp
    have hsubset : {ω | t < X ω} ⊆ {ω | s < X ω} := fun ω hω ↦ hst.trans_lt hω
    rw [setIntegral_const, smul_eq_mul, hset,
      measureReal_sdiff (μ := ν) hsubset
        (measurableSet_lt measurable_const hX),
      hsurvival s ⟨le_rfl, hst⟩, hsurvival t ⟨hst, le_rfl⟩]
    ring
  rw [hleft]
  calc
    (t - s) * (c / D) = ∫ u in Ioc s t, c / D ∂volume := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hst]
    _ = ∫ u in Ioc s t, ∫ ω, R (ω, u) ∂ν ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioc
      exact fun u hu ↦ (hinner u hu).symm
    _ = ∫ ω, ∫ u in Ioc s t, R (ω, u) ∂volume ∂ν :=
      (integral_integral_swap hRint).symm
    _ = ∫ ω, ∫ u in Ioc s t, if u < X ω then c / (K - u) else 0 ∂volume ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω ↦ by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        simp only [R, hu, true_and]

/-- The actual one-point law at a fixed frozen boundary is uniform on its strict source
complement.  Its later survival mass is the ratio of the physical remaining areas. -/
theorem rightFrozenSourceLaw_survival
    {n : ℕ} (hn : 0 < n) {q xR y : ℝ} (hxy : xR ≤ y)
    (hR : (xR, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hy : (y, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
    ((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]).real
      (sourceRawRemainingSet n q y) =
      sourceUnclippedRemainingMass n q y / sourceUnclippedRemainingMass n q xR := by
  have hsR := FiniteSample.sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hsy := FiniteSample.sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hy
  rw [unitSquareUniform_cond_sourceRemaining_real n q xR y hxy,
    unitSquareUniform_sourceRawRemainingSet hn (fun u ↦ (hsy u).1.le) (fun u ↦ (hsy u).2.le),
    unitSquareUniform_sourceRawRemainingSet hn (fun u ↦ (hsR u).1.le) (fun u ↦ (hsR u).2.le),
    div_div_div_cancel_right₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne')]

/-- A genuine one-point crossing-window versus integrated-hazard identity under the
boundary-conditioned source law.  The proof uses the known marked-square law and Fubini. -/
theorem rightFrozenSourceLaw_onePoint_compensator
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hfloor : 0 < sourceUnclippedRemainingMass n q t) (c : ℝ) :
    (∫ _z in sourceRawRemainingSet n q s \ sourceRawRemainingSet n q t, c
      ∂((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR])) =
      ∫ z, ∫ u in Ioc s t,
        (sourceRawRemainingSet n q u).indicator
          (fun _ ↦ c / sourceUnclippedRemainingMass n q u) z ∂volume
        ∂((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]) := by
  let ν : Measure MarkedHeight :=
    (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]
  let X : MarkedHeight → ℝ := fun z ↦ (n : ℝ) * (z.1 : ℝ) + q * (1 - (z.2 : ℝ))
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hK : ∀ u, (n : ℝ) + q / 2 - u = sourceUnclippedRemainingMass n q u := by
    intro u
    unfold sourceUnclippedRemainingMass
    ring
  have hD : sourceUnclippedRemainingMass n q xR ≠ 0 := by
    have hRt := hRs.trans hst
    unfold sourceUnclippedRemainingMass at hfloor ⊢
    linarith
  have hsurvival : ∀ u ∈ Icc s t,
      ν.real {z | u < X z} =
        ((n : ℝ) + q / 2 - u) / sourceUnclippedRemainingMass n q xR := by
    intro u hu
    rw [hK]
    exact rightFrozenSourceLaw_survival hn (hRs.trans hu.1)
      (hstrip xR ⟨le_rfl, hRs.trans hst⟩) (hstrip u ⟨hRs.trans hu.1, hu.2⟩)
  have hbase := affineSurvival_onePoint_compensator ν X hX hst
    (by rwa [hK]) hD hsurvival c
  have hset : {z | s < X z ∧ X z ≤ t} =
      sourceRawRemainingSet n q s \ sourceRawRemainingSet n q t := by
    ext z
    simp [X, sourceRawRemainingSet]
  rw [hset] at hbase
  simp_rw [hK] at hbase
  exact hbase

/-- The actual one-point law at a fixed frozen boundary is uniform on its strict target
complement.  Its later survival mass is the ratio of the physical remaining areas. -/
theorem rightFrozenTargetLaw_survival
    {n : ℕ} (hn : 0 < n) {q xR y : ℝ} (hxy : xR ≤ y)
    (hR : (xR, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hy : (y, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
    ((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]).real
      (targetRawRemainingSet n q y) =
      targetUnclippedRemainingMass n q y / targetUnclippedRemainingMass n q xR := by
  have hsR := FiniteSample.targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hsy := FiniteSample.targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hy
  rw [unitSquareUniform_cond_targetRemaining_real n q xR y hxy,
    unitSquareUniform_targetRawRemainingSet hn (fun u ↦ (hsy u).1.le) (fun u ↦ (hsy u).2.le),
    unitSquareUniform_targetRawRemainingSet hn (fun u ↦ (hsR u).1.le) (fun u ↦ (hsR u).2.le),
    div_div_div_cancel_right₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne')]

/-- A genuine one-point crossing-window versus integrated-hazard identity under the
boundary-conditioned target law.  The proof uses the known marked-square law and Fubini. -/
theorem rightFrozenTargetLaw_onePoint_compensator
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hfloor : 0 < targetUnclippedRemainingMass n q t) (c : ℝ) :
    (∫ _z in targetRawRemainingSet n q s \ targetRawRemainingSet n q t, c
      ∂((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR])) =
      ∫ z, ∫ u in Ioc s t,
        (targetRawRemainingSet n q u).indicator
          (fun _ ↦ c / targetUnclippedRemainingMass n q u) z ∂volume
        ∂((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]) := by
  let ν : Measure MarkedHeight :=
    (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]
  let X : MarkedHeight → ℝ := fun z ↦ (n : ℝ) * (z.1 : ℝ) - q * (1 + (z.2 : ℝ))
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hK : ∀ u, (n : ℝ) - 3 * q / 2 - u = targetUnclippedRemainingMass n q u := by
    intro u
    unfold targetUnclippedRemainingMass
    ring
  have hD : targetUnclippedRemainingMass n q xR ≠ 0 := by
    have hRt := hRs.trans hst
    unfold targetUnclippedRemainingMass at hfloor ⊢
    linarith
  have hsurvival : ∀ u ∈ Icc s t,
      ν.real {z | u < X z} =
        ((n : ℝ) - 3 * q / 2 - u) / targetUnclippedRemainingMass n q xR := by
    intro u hu
    rw [hK]
    exact rightFrozenTargetLaw_survival hn (hRs.trans hu.1)
      (hstrip xR ⟨le_rfl, hRs.trans hst⟩) (hstrip u ⟨hRs.trans hu.1, hu.2⟩)
  have hbase := affineSurvival_onePoint_compensator ν X hX hst
    (by rwa [hK]) hD hsurvival c
  have hset : {z | s < X z ∧ X z ≤ t} =
      targetRawRemainingSet n q s \ targetRawRemainingSet n q t := by
    ext z
    simp [X, targetRawRemainingSet]
  rw [hset] at hbase
  simp_rw [hK] at hbase
  exact hbase

end OTSelector
