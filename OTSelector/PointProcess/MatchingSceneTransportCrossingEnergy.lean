import OTSelector.PointProcess.MatchingSceneTransportCurrent

/-!
# Crossing-energy means of actual weak matching limits

The fixed-sample squared energy controls the full crossing count plus crossing-length sum.
A continuous soft crossing approximation transports that bound without an annealed energy
assumption or an assumed matching Palm factorization.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal CompactlySupported

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.FiniteMatching

private theorem rootWindow_indicator (x ε z : ℝ) :
    (if |x - z| ≤ ε then (1 : ℝ) else 0) = (Icc (x - ε) (x + ε)).indicator (fun _ ↦ 1) z := by
  have he : |x - z| ≤ ε ↔ z ∈ Icc (x - ε) (x + ε) := by
    rw [abs_le, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [he, Set.indicator_apply]

/-- A finite sum of genuinely root-near endpoint weights. -/
noncomputable def endpointWindowWeight {n : ℕ} (endpoint weight : Fin n → ℝ) (ε z : ℝ) : ℝ :=
  ∑ i, (if |endpoint i - z| ≤ ε then 1 else 0) * weight i

theorem integrable_endpointWindowWeight {n : ℕ} (endpoint weight : Fin n → ℝ) (ε : ℝ) :
    Integrable (endpointWindowWeight endpoint weight ε) := by
  apply integrable_finsetSum
  intro i hi
  simp_rw [rootWindow_indicator]
  apply Integrable.mul_const
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem integral_endpointWindowWeight {n : ℕ} (endpoint weight : Fin n → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ z, endpointWindowWeight endpoint weight ε z) = 2 * ε * ∑ i, weight i := by
  have hi (i : Fin n) : Integrable (fun z : ℝ ↦
      (if |endpoint i - z| ≤ ε then (1 : ℝ) else 0) * weight i) := by
    simp_rw [rootWindow_indicator]
    exact ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))).mul_const _
  change (∫ z, ∑ i, _) = _
  rw [integral_finsetSum _ (fun i _ ↦ hi i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi'
  simp_rw [rootWindow_indicator]
  rw [integral_mul_const, integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le (by linarith)]
  simp only [smul_eq_mul, mul_one]
  ring

end OTSelector.PointProcess.FiniteMatching

namespace OTSelector.PointProcess.MatchingScene

/-- The continuous soft crossing count plus soft crossing-length contribution of one edge. -/
noncomputable def softCrossingEnergy (ε : ℝ) (e : MatchingPoint × MatchingPoint) : ℝ :=
  |softCrossing ε e| * (1 + |e.2.1 - e.1.1|)

theorem continuous_softCrossingEnergy (ε : ℝ) : Continuous (softCrossingEnergy ε) :=
  (continuous_softCrossing ε).abs.mul (continuous_const.add
    ((continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)).abs)

theorem softCrossingEnergy_nonneg (ε : ℝ) (e : MatchingPoint × MatchingPoint) :
    0 ≤ softCrossingEnergy ε e := mul_nonneg (abs_nonneg _) (by positivity)

theorem abs_softCrossing_le {ε : ℝ} (hε : 0 < ε) (e : MatchingPoint × MatchingPoint) :
    |softCrossing ε e| ≤ |(crossingSign e.1.1 e.2.1 0 : ℝ)| +
      ((if |e.1.1| ≤ ε then 1 else 0) + (if |e.2.1| ≤ ε then 1 else 0)) := by
  have h := abs_crossingSign_sub_softCrossing_le hε e
  have ht := abs_sub_abs_le_abs_sub (softCrossing ε e) (crossingSign e.1.1 e.2.1 0 : ℝ)
  rw [abs_sub_comm] at ht
  exact (sub_le_iff_le_add.mp (ht.trans h)).trans_eq (add_comm _ _)

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- Weighted continuous crossing tests have the original finite assignment energy bound. -/
theorem lintegral_softCrossingEnergy_test_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) (r : ℕ) :
    (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges
      (LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase))
        (MatchingScene.softCrossingEnergy ε) (MatchingScene.continuous_softCrossingEnergy ε) r))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((b - a)⁻¹ * ((((n : ℝ) + 3 * (∑ i,
        (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2)) / 2) +
          2 * ε * (3 * n + ∑ i,
            (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2))) := by
  let d (i : Fin n) := sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i
  let w (i : Fin n) := 1 + |d i|
  let f := LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase))
    (MatchingScene.softCrossingEnergy ε) (MatchingScene.continuous_softCrossingEnergy ε) r
  let G : ℝ → ℝ := fun z ↦
    (∑ i, |(crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)| * w i) +
      (FiniteMatching.endpointWindowWeight (sample.sourceIntersection graph) w ε z +
        FiniteMatching.endpointWindowWeight (fun i ↦ sample.targetIntersection graph (σ i)) w ε z)
  have hi₁ : Integrable (fun z ↦ ∑ i, |(crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)| * w i) :=
    integrable_finsetSum _ (fun i _ ↦ (FiniteMatching.integrable_abs_crossingSign _ _).mul_const _)
  have hi₂ := FiniteMatching.integrable_endpointWindowWeight (sample.sourceIntersection graph) w ε
  have hi₃ := FiniteMatching.integrable_endpointWindowWeight
    (fun i ↦ sample.targetIntersection graph (σ i)) w ε
  have hdom (z : ℝ) : LocalConfiguration.testIntegral
      (sample.rootedMatchingScene graph σ z).edges f ≤ G z := by
    change LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _ _) f ≤ _
    rw [LocalConfiguration.testIntegral_ofTuple]
    have hc (a b z : ℝ) : crossingSign (a - z) (b - z) 0 = crossingSign a b z := by
      simp only [crossingSign, sub_nonpos]
    have hp (i : Fin n) : f (sample.rootedSourcePoint graph z i,
        sample.rootedTargetPoint graph z (σ i)) ≤
        |(crossingSign (sample.sourceIntersection graph i)
          (sample.targetIntersection graph (σ i)) z : ℝ)| * w i +
          (((if |sample.sourceIntersection graph i - z| ≤ ε then 1 else 0) * w i) +
            (if |sample.targetIntersection graph (σ i) - z| ≤ ε then 1 else 0) * w i) := by
      apply (LocalConfiguration.compactWeightTest_le
        (MatchingScene.continuous_softCrossingEnergy ε)
        (MatchingScene.softCrossingEnergy_nonneg ε) r _).trans
      have hh := mul_le_mul_of_nonneg_right (MatchingScene.abs_softCrossing_le hε
        (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i)))
        (by positivity : 0 ≤ w i)
      simp only [rootedSourcePoint, rootedTargetPoint, hc, w, d, add_mul] at hh
      convert hh using 1 <;>
        simp only [MatchingScene.softCrossingEnergy, rootedSourcePoint, rootedTargetPoint,
          sub_sub_sub_cancel_right, w, d]
      congr 2
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hp i)
    simpa only [G, FiniteMatching.endpointWindowWeight, Finset.sum_add_distrib] using hs
  apply (sample.lintegral_rootedMatchingSceneLaw_le_of_integrable_domination graph σ hab
    (MatchingScene.continuous_edgeTest f).measurable (fun scene ↦ by
      rw [← LocalConfiguration.integral_countingMeasure]
      exact integral_nonneg (LocalConfiguration.compactWeightTest_nonneg
        (MatchingScene.continuous_softCrossingEnergy ε)
        (MatchingScene.softCrossingEnergy_nonneg ε) r))
    (hi₁.add (hi₂.add hi₃)) hdom).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  have hadd₁ := integral_add hi₁ (hi₂.add hi₃)
  have hadd₂ := integral_add hi₂ hi₃
  simp only [Pi.add_apply] at hadd₁ hadd₂
  change (∫ z, G z) ≤ _
  dsimp only [G]
  rw [hadd₁, hadd₂, FiniteMatching.integral_endpointWindowWeight _ _ hε.le,
    FiniteMatching.integral_endpointWindowWeight _ _ hε.le,
    integral_finsetSum _ (fun i _ ↦ (FiniteMatching.integrable_abs_crossingSign _ _).mul_const _)]
  simp_rw [integral_mul_const, FiniteMatching.integral_abs_crossingSign]
  have hc (i : Fin n) : |d i| * w i ≤ (1 + 3 * (d i)^2) / 2 := by
    dsimp [w]
    nlinarith [sq_nonneg (|d i| - 1), sq_abs (d i)]
  have hw (i : Fin n) : w i ≤ (3 + (d i)^2) / 2 := by
    dsimp [w]
    nlinarith [sq_nonneg (|d i| - 1), sq_abs (d i)]
  have hcSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hwSum : (∑ i, w i) ≤ (3 * n + ∑ i, (d i)^2) / 2 := by
    calc
      _ ≤ ∑ i, (3 + (d i)^2) / 2 := Finset.sum_le_sum (fun i _ ↦ hw i)
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        simp [mul_comm]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum] at hcSum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcSum
  change (∑ i, |d i| * w i) + ((2 * ε * ∑ i, w i) + (2 * ε * ∑ i, w i)) ≤
    ((n : ℝ) + 3 * ∑ i, (d i)^2) / 2 + 2 * ε * (3 * n + ∑ i, (d i)^2)
  nlinarith

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- Full weighted soft crossing moments pass from the actual finite root laws to their weak
limit. The constants depend only on energy and number of samples per root length. -/
theorem lintegral_softCrossingEnergy_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν)) {C ρ : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ * (b k - a k))
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (softCrossingEnergy ε e)
      ∂LocalConfiguration.countingMeasure scene.edges ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal ((ρ + 3 * C) / 2 + 2 * ε * (3 * ρ + C)) := by
  apply lintegral_countingWeight_le_of_compactTest_bounds _
    (continuous_softCrossingEnergy ε) (softCrossingEnergy_nonneg ε)
  intro r
  apply lintegral_edgeTest_le_of_tendsto hμ
  filter_upwards [henergy, hcount] with k hk hn
  rw [hlaw k]
  apply ((sample k).lintegral_softCrossingEnergy_test_le
    (graph k) (assignment k) (hab k) hε r).trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  calc
    _ ≤ (b k - a k)⁻¹ * ((ρ * (b k - a k) + 3 * (C * (b k - a k))) / 2 +
        2 * ε * (3 * (ρ * (b k - a k)) + C * (b k - a k))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_right (add_le_add hn (mul_le_mul_of_nonneg_left hk (by norm_num)))
          (by norm_num))
        (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hn (by norm_num)) hk)
          (by positivity))) (inv_nonneg.mpr hlen.le)
    _ = _ := by field_simp

/-- Actual crossing energy computed directly from the marked edge counting measure. -/
noncomputable def crossingEnergyMoment (scene : MatchingScene) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ e, ENNReal.ofReal (|(crossingSign e.1.1 e.2.1 x : ℝ)| * (1 + |e.2.1 - e.1.1|))
    ∂LocalConfiguration.countingMeasure scene.edges

theorem measurable_softCrossingEnergyMoment (ε : ℝ) : Measurable
    (fun scene : MatchingScene ↦ ∫⁻ e, ENNReal.ofReal (softCrossingEnergy ε e)
      ∂LocalConfiguration.countingMeasure scene.edges) := by
  simp_rw [LocalConfiguration.lintegral_countingWeight_eq_iSup_test _
    (continuous_softCrossingEnergy ε) (softCrossingEnergy_nonneg ε)]
  exact Measurable.iSup fun n ↦ (continuous_edgeTest
    (LocalConfiguration.compactWeightTest _ (continuous_softCrossingEnergy ε) n)).measurable.ennreal_ofReal

/-- At every cut with finite signed crossing support, the counting integral is precisely the
crossing energy of the actual spatial matching. -/
theorem crossingEnergyMoment_eq_spatialMatching {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene) (x : ℝ)
    (hfinite : (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 x)).Finite) :
    crossingEnergyMoment scene x = ENNReal.ofReal ((spatialMatching hp).crossingEnergy x) := by
  rw [crossingEnergyMoment, lintegral_edges_eq_tsum_source hp]
  have hout (i : SourceAtom scene) (hi : i ∉ hfinite.toFinset) :
      |(crossingSign i.val.1 (atomAssignment hp i).val.1 x : ℝ)| *
        (1 + |(atomAssignment hp i).val.1 - i.val.1|) = 0 := by
    have hz : crossingSign i.val.1 (atomAssignment hp i).val.1 x = 0 := by
      simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hi
    rw [hz, Int.cast_zero, abs_zero, zero_mul]
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun i hi ↦ by rw [hout i hi, ENNReal.ofReal_zero])]
  change _ = ENNReal.ofReal (∑' i : SourceAtom scene,
    |(crossingSign i.val.1 (atomAssignment hp i).val.1 x : ℝ)| *
      (1 + |(atomAssignment hp i).val.1 - i.val.1|))
  rw [tsum_eq_sum (s := hfinite.toFinset) hout, ENNReal.ofReal_sum_of_nonneg
    (fun _ _ ↦ mul_nonneg (abs_nonneg _) (by positivity))]

/-- Away from endpoint atoms, all weighted soft crossing moments eventually equal the actual
crossing moment, simultaneously across all edges. -/
theorem eventually_softCrossingEnergyMoment_eq {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene)
    (hsource : ∀ x : SourceAtom scene, x.val.1 ≠ 0)
    (htarget : ∀ y : TargetAtom scene, y.val.1 ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ e, ENNReal.ofReal (softCrossingEnergy (1 / ((n : ℝ) + 1)) e)
        ∂LocalConfiguration.countingMeasure scene.edges) = crossingEnergyMoment scene 0 := by
  filter_upwards [eventually_softCrossing_eq_crossingSign hp hsource htarget] with n hn
  rw [crossingEnergyMoment, lintegral_edges_eq_tsum_source hp, lintegral_edges_eq_tsum_source hp]
  apply tsum_congr
  intro i
  simp only [softCrossingEnergy, hn]

/-- The full actual root crossing energy has a finite mean in a true fixed-energy weak limit.
This is obtained directly from the original squared assignment energy, without conditioning
an annealed law on the finite-energy event. -/
theorem lintegral_crossingEnergyMoment_zero_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν)) {C ρ : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ * (b k - a k))
    (hperfect : ∀ᵐ scene ∂(ν : Measure MatchingScene), IsSimplePerfectMatching scene)
    (hzero : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ x : SourceAtom scene, x.val.1 ≠ 0) ∧ (∀ y : TargetAtom scene, y.val.1 ≠ 0)) :
    (∫⁻ scene, crossingEnergyMoment scene 0 ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal ((ρ + 3 * C) / 2) := by
  let f (n : ℕ) (scene : MatchingScene) : ℝ≥0∞ := ∫⁻ e,
    ENNReal.ofReal (softCrossingEnergy (1 / ((n : ℝ) + 1)) e)
      ∂LocalConfiguration.countingMeasure scene.edges
  have hbound (n : ℕ) : (∫⁻ scene, f n scene ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal ((ρ + 3 * C) / 2 + 2 * (1 / ((n : ℝ) + 1)) * (3 * ρ + C)) :=
    lintegral_softCrossingEnergy_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hab hlaw hμ henergy hcount (by positivity)
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((ρ + 3 * C) / 2 + 2 * (1 / ((n : ℝ) + 1)) * (3 * ρ + C)))
      atTop (𝓝 (ENNReal.ofReal ((ρ + 3 * C) / 2))) := by
    have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, zero_mul, add_zero] using
      ENNReal.tendsto_ofReal (((h.const_mul 2).mul_const (3 * ρ + C)).const_add ((ρ + 3 * C) / 2))
  have heq : (fun scene ↦ crossingEnergyMoment scene 0) =ᵐ[(ν : Measure MatchingScene)]
      (fun scene ↦ liminf (fun n ↦ f n scene) atTop) := by
    filter_upwards [hperfect, hzero] with scene hp hz
    have htest : (fun n ↦ f n scene) =ᶠ[atTop] (fun _ ↦ crossingEnergyMoment scene 0) :=
      eventually_softCrossingEnergyMoment_eq hp hz.1 hz.2
    exact (tendsto_const_nhds.congr' htest.symm).liminf_eq.symm
  rw [lintegral_congr_ae heq]
  apply (lintegral_liminf_le (fun n ↦ measurable_softCrossingEnergyMoment _)).trans
  exact (liminf_le_liminf (Eventually.of_forall hbound)).trans_eq hlim.liminf_eq

end OTSelector.PointProcess.MatchingScene
