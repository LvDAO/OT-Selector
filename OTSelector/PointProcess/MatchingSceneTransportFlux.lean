import OTSelector.PointProcess.MatchingSceneTransportPerfect
import OTSelector.PointProcess.MatchingSceneTransportPalm

/-!
# Actual crossing-current transport

Continuous approximations of the finite matching current use the original signed crossing
contribution and actual marked edge configuration. Spatial-root error is controlled by the
existing long-crossing energy bound and the two endpoint counts in a shrinking root window.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal CompactlySupported

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.MatchingScene

/-- Continuous decreasing approximation of the indicator of the left half-line. -/
noncomputable def leftRamp (ε x : ℝ) : ℝ := min 1 (max 0 ((ε - x) / (2 * ε)))

theorem continuous_leftRamp (ε : ℝ) : Continuous (leftRamp ε) :=
  continuous_const.min (continuous_const.max ((continuous_const.sub continuous_id).div_const _))

theorem leftRamp_nonneg (ε x : ℝ) : 0 ≤ leftRamp ε x :=
  le_min zero_le_one (le_max_left _ _)

theorem leftRamp_le_one (ε x : ℝ) : leftRamp ε x ≤ 1 := min_le_left _ _

theorem leftRamp_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ -ε) : leftRamp ε x = 1 := by
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  apply (le_div_iff₀ (by positivity : 0 < 2 * ε)).mpr
  linarith

theorem leftRamp_eq_zero {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) : leftRamp ε x = 0 := by
  have h : (ε - x) / (2 * ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by positivity)
  simp only [leftRamp, max_eq_left h, min_eq_right zero_le_one]

/-- Smoothing affects a point's half-line indicator only within the stated root window. -/
theorem abs_leftIndicator_sub_leftRamp_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |(if x ≤ 0 then (1 : ℝ) else 0) - leftRamp ε x| ≤
      if |x| ≤ ε then 1 else 0 := by
  by_cases hx : |x| ≤ ε
  · rw [ite_eq_left hx]
    by_cases hx0 : x ≤ 0
    · rw [ite_eq_left hx0, abs_of_nonneg (sub_nonneg.mpr (leftRamp_le_one _ _))]
      linarith [leftRamp_nonneg ε x]
    · rw [ite_eq_right hx0, zero_sub, abs_neg, abs_of_nonneg (leftRamp_nonneg _ _)]
      exact leftRamp_le_one _ _
  · rw [ite_eq_right hx]
    rcases lt_or_ge x 0 with hx0 | hx0
    · rw [ite_eq_left hx0.le, leftRamp_eq_one hε]
      · norm_num
      · rw [abs_of_neg hx0] at hx
        linarith
    · rw [ite_eq_right (by intro h; have : x = 0 := le_antisymm h hx0; subst x; simp at hx; linarith)]
      rw [leftRamp_eq_zero hε (by rw [abs_of_nonneg hx0] at hx; linarith)]
      norm_num

/-- The signed soft crossing of an actual marked edge. -/
noncomputable def softCrossing (ε : ℝ) (e : MatchingPoint × MatchingPoint) : ℝ :=
  leftRamp ε e.1.1 - leftRamp ε e.2.1

theorem continuous_softCrossing (ε : ℝ) : Continuous (softCrossing ε) :=
  ((continuous_leftRamp ε).comp (continuous_fst.comp continuous_fst)).sub
    ((continuous_leftRamp ε).comp (continuous_fst.comp continuous_snd))

/-- The total edgewise smoothing error is charged to its two actual endpoint windows. -/
theorem abs_crossingSign_sub_softCrossing_le {ε : ℝ} (hε : 0 < ε)
    (e : MatchingPoint × MatchingPoint) :
    |(crossingSign e.1.1 e.2.1 0 : ℝ) - softCrossing ε e| ≤
      (if |e.1.1| ≤ ε then 1 else 0) + (if |e.2.1| ≤ ε then 1 else 0) := by
  have hs := abs_leftIndicator_sub_leftRamp_le hε e.1.1
  have ht := abs_leftIndicator_sub_leftRamp_le hε e.2.1
  have hid : (crossingSign e.1.1 e.2.1 0 : ℝ) - softCrossing ε e =
      ((if e.1.1 ≤ 0 then (1 : ℝ) else 0) - leftRamp ε e.1.1) -
        ((if e.2.1 ≤ 0 then (1 : ℝ) else 0) - leftRamp ε e.2.1) := by
    simp only [crossingSign, softCrossing, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add hs ht)

/-- A compact continuous test of the actual edge current. -/
noncomputable def crossingTest (ε : ℝ) (r : ℕ) : C_c(MatchingPoint × MatchingPoint, ℝ) :=
  LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase))
    (softCrossing ε) (continuous_softCrossing ε) r

private theorem dist_matchingPoint_base_le {R : ℝ} (hR : 1 ≤ R) (x : MatchingPoint)
    (hx : |x.1| ≤ R) : dist x matchingPointBase ≤ R := by
  rw [Prod.dist_eq]
  apply max_le
  · simpa only [matchingPointBase, Real.dist_eq, sub_zero] using hx
  · change dist (x.2 : ℝ) 0 ≤ R
    rw [Real.dist_eq, sub_zero, abs_of_nonneg x.2.property.1]
    exact x.2.property.2.trans hR

private theorem crossingSign_abs_endpoints_le {a b : ℝ} (h : crossingSign a b 0 ≠ 0) :
    |a| ≤ |b - a| ∧ |b| ≤ |b - a| := by
  by_cases ha : a ≤ 0 <;> by_cases hb : b ≤ 0
  · simp [crossingSign, ha, hb] at h
  · have hb' : 0 < b := lt_of_not_ge hb
    rw [abs_of_nonpos ha, abs_of_pos hb', abs_of_nonneg (by linarith : 0 ≤ b - a)]
    constructor <;> linarith
  · have ha' : 0 < a := lt_of_not_ge ha
    rw [abs_of_pos ha', abs_of_nonpos hb, abs_of_nonpos (by linarith : b - a ≤ 0)]
    constructor <;> linarith
  · simp [crossingSign, ha, hb] at h

/-- Compact cutoff error can arise only from a genuinely long crossing edge. -/
theorem abs_crossingSign_sub_crossingTest_le {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 ≤ r) (e : MatchingPoint × MatchingPoint) :
    |(crossingSign e.1.1 e.2.1 0 : ℝ) - crossingTest ε r e| ≤
      (if (r : ℝ) < |e.2.1 - e.1.1| then |(crossingSign e.1.1 e.2.1 0 : ℝ)| else 0) +
        ((if |e.1.1| ≤ ε then 1 else 0) + (if |e.2.1| ≤ ε then 1 else 0)) := by
  let χ : ℝ := min 1 (max 0 ((r : ℝ) + 1 - dist e (matchingPointBase, matchingPointBase)))
  let c : ℝ := crossingSign e.1.1 e.2.1 0
  have hχ0 : 0 ≤ χ := le_min zero_le_one (le_max_left _ _)
  have hχ1 : χ ≤ 1 := min_le_left _ _
  have hwindow0 : 0 ≤ (if |e.1.1| ≤ ε then (1 : ℝ) else 0) +
      (if |e.2.1| ≤ ε then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hcut : |(1 - χ) * c| ≤ if (r : ℝ) < |e.2.1 - e.1.1| then |c| else 0 := by
    by_cases hd : (r : ℝ) < |e.2.1 - e.1.1|
    · rw [ite_eq_left hd, abs_mul, abs_of_nonneg (sub_nonneg.mpr hχ1)]
      exact (mul_le_mul_of_nonneg_right (by linarith : 1 - χ ≤ 1) (abs_nonneg c)).trans_eq (one_mul _)
    · rw [ite_eq_right hd]
      by_cases hc : crossingSign e.1.1 e.2.1 0 = 0
      · simp [c, hc]
      · obtain ⟨hs, ht⟩ := crossingSign_abs_endpoints_le hc
        have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
        have hdist : dist e (matchingPointBase, matchingPointBase) ≤ r := by
          rw [Prod.dist_eq]
          exact max_le (dist_matchingPoint_base_le hr' e.1 (hs.trans (le_of_not_gt hd)))
            (dist_matchingPoint_base_le hr' e.2 (ht.trans (le_of_not_gt hd)))
        have hχ : χ = 1 := min_eq_left <|
          (by linarith : (1 : ℝ) ≤ (r : ℝ) + 1 - dist e (matchingPointBase, matchingPointBase)).trans
            (le_max_right _ _)
        simp [hχ]
  have hsmooth := abs_crossingSign_sub_softCrossing_le hε e
  have hid : c - crossingTest ε r e = (1 - χ) * c + χ * (c - softCrossing ε e) := by
    change c - χ * softCrossing ε e = _
    ring
  change |c - crossingTest ε r e| ≤ _
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add hcut
  rw [abs_mul, abs_of_nonneg hχ0]
  exact (mul_le_mul_of_nonneg_left hsmooth hχ0).trans
    ((mul_le_mul_of_nonneg_right hχ1 hwindow0).trans_eq (one_mul _))

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.FiniteMatching

variable {n : ℕ}

/-- The actual number of endpoints in a closed root window, as a real finite sum. -/
noncomputable def endpointWindowCount (endpoint : Fin n → ℝ) (ε z : ℝ) : ℝ :=
  ∑ i, if |endpoint i - z| ≤ ε then 1 else 0

private theorem endpointWindowCount_eq (endpoint : Fin n → ℝ) (ε z : ℝ) :
    endpointWindowCount endpoint ε z = (rootWindowTailCount endpoint (fun _ ↦ 1) ε 0 z : ℝ) := by
  simp [rootWindowTailCount_eq_sum, endpointWindowCount]

theorem integrable_endpointWindowCount (endpoint : Fin n → ℝ) (ε : ℝ) :
    Integrable (endpointWindowCount endpoint ε) := by
  change Integrable (fun z ↦ endpointWindowCount endpoint ε z)
  simp_rw [endpointWindowCount_eq]
  exact integrable_rootWindowTailCount _ _ _ _

theorem integral_endpointWindowCount (endpoint : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ z, endpointWindowCount endpoint ε z) = 2 * ε * n := by
  simp_rw [endpointWindowCount_eq]
  rw [integral_rootWindowTailCount _ _ hε]
  simp

end OTSelector.PointProcess.FiniteMatching

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- Spatial averaging of a concrete finite scene transports any nonnegative observable dominated
by an integrable actual root function. -/
theorem lintegral_rootedMatchingSceneLaw_le_of_integrable_domination
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b : ℝ} (hab : a < b) {f : MatchingScene → ℝ}
    (hf : Measurable f) (hf0 : ∀ scene, 0 ≤ f scene) {G : ℝ → ℝ} (hG : Integrable G)
    (hdom : ∀ z, f (sample.rootedMatchingScene graph σ z) ≤ G z) :
    (∫⁻ scene, ENNReal.ofReal (f scene) ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((b - a)⁻¹ * ∫ z, G z) := by
  let F : ℝ → ℝ := fun z ↦ f (sample.rootedMatchingScene graph σ z)
  have hF : Integrable F := hG.mono'
    (hf.comp (sample.measurable_rootedMatchingScene graph σ)).aestronglyMeasurable
    (ae_of_all _ fun z ↦ by simpa only [F, Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hdom z)
  have hroot : Integrable f (sample.rootedMatchingSceneLaw graph σ a b) := by
    rw [rootedMatchingSceneLaw]
    apply (integrable_map_measure hf.aestronglyMeasurable
      (sample.measurable_rootedMatchingScene graph σ).aemeasurable).mpr
    simp only [Probability.spatialRootLaw, ProbabilityTheory.cond, Real.volume_Ioc]
    exact hF.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr
      ((ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'))
  rw [← ofReal_integral_eq_lintegral_ofReal hroot (ae_of_all _ hf0),
    sample.integral_rootedMatchingSceneLaw graph σ hab.le f hf,
    intervalIntegral.integral_of_le hab.le]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  exact (setIntegral_mono_on hF.integrableOn hG.integrableOn measurableSet_Ioc
    (fun z _ ↦ hdom z)).trans
    (setIntegral_le_integral hG (ae_of_all _ fun z ↦ (hf0 _).trans (hdom z)))

/-- Pointwise current approximation is charged only to actual long crossings and root-near
endpoints of the same original finite assignment. -/
theorem abs_rootCurrent_sub_crossingTest_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) (z : ℝ) :
    |((sample.rootedMatchingScene graph σ z).path.rootCurrent : ℝ) -
      LocalConfiguration.testIntegral (sample.rootedMatchingScene graph σ z).edges
        (MatchingScene.crossingTest ε r)| ≤
      FiniteMatching.longCrossingCount (sample.sourceIntersection graph)
        (sample.targetIntersection graph) σ r z +
      (FiniteMatching.endpointWindowCount (sample.sourceIntersection graph) ε z +
        FiniteMatching.endpointWindowCount (fun i ↦ sample.targetIntersection graph (σ i)) ε z) := by
  rw [sample.rootedMatchingScene_rootCurrent_eq_crossingCurrent graph σ z,
    assignmentCrossingCurrent, Int.cast_sum]
  change |(∑ i, (crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)) -
    LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _ _)
      (MatchingScene.crossingTest ε r)| ≤ _
  rw [LocalConfiguration.testIntegral_ofTuple, ← Finset.sum_sub_distrib]
  have h (i : Fin n) := MatchingScene.abs_crossingSign_sub_crossingTest_le hε hr
    (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i))
  have hc (a b z : ℝ) : crossingSign (a - z) (b - z) 0 = crossingSign a b z := by
    simp only [crossingSign, sub_nonpos]
  simp only [rootedSourcePoint, rootedTargetPoint, hc, sub_sub_sub_cancel_right] at h
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ h i)
  simp only [Finset.sum_add_distrib] at hs
  convert hs using 1 <;> simp only [rootedSourcePoint, rootedTargetPoint,
    FiniteMatching.longCrossingCount, FiniteMatching.endpointWindowCount]
  congr 2

/-- Exact root-averaged error estimate before taking any sample or matching limit. -/
theorem lintegral_rootCurrent_sub_crossingTest_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) :
    (∫⁻ scene, ENNReal.ofReal |(scene.path.rootCurrent : ℝ) -
      LocalConfiguration.testIntegral scene.edges (MatchingScene.crossingTest ε r)|
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((b - a)⁻¹ * ((∑ i,
        (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) / r +
          4 * ε * n)) := by
  have hcurrent : Continuous (fun scene : MatchingScene ↦ (scene.path.rootCurrent : ℝ)) :=
    (continuous_of_discreteTopology : Continuous (fun k : ℤ ↦ (k : ℝ))).comp
      MatchingScene.continuous_rootCurrent
  have hi₁ := FiniteMatching.integrable_longCrossingCount (sample.sourceIntersection graph)
    (sample.targetIntersection graph) σ r
  have hi₂ := FiniteMatching.integrable_endpointWindowCount (sample.sourceIntersection graph) ε
  have hi₃ := FiniteMatching.integrable_endpointWindowCount
    (fun i ↦ sample.targetIntersection graph (σ i)) ε
  apply (sample.lintegral_rootedMatchingSceneLaw_le_of_integrable_domination graph σ hab
    (hcurrent.sub (MatchingScene.continuous_edgeTest _)).abs.measurable
    (fun _ ↦ abs_nonneg _) (hi₁.add (hi₂.add hi₃))
    (sample.abs_rootCurrent_sub_crossingTest_le graph σ hε hr)).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  simp only [Pi.add_apply]
  have hadd₁ := integral_add hi₁ (hi₂.add hi₃)
  have hadd₂ := integral_add hi₂ hi₃
  simp only [Pi.add_apply] at hadd₁ hadd₂
  rw [hadd₁, hadd₂,
    FiniteMatching.integral_endpointWindowCount _ hε.le,
    FiniteMatching.integral_endpointWindowCount _ hε.le]
  have htail := FiniteMatching.setIntegral_longCrossingCount_le
    (sample.sourceIntersection graph) (sample.targetIntersection graph) σ univ
    (R := (r : ℝ)) (by exact_mod_cast (show 0 < r from lt_of_lt_of_le Nat.zero_lt_one hr))
  simp only [Measure.restrict_univ] at htail
  linarith

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- The actual weak limit retains the quantitative approximation to its integer root current.
Only deterministic finite-sample energy and count per root length are used. -/
theorem lintegral_rootCurrent_sub_crossingTest_of_rootedMatchingSceneLaw_tendsto
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
    {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) :
    (∫⁻ scene, ENNReal.ofReal |(scene.path.rootCurrent : ℝ) -
      LocalConfiguration.testIntegral scene.edges (crossingTest ε r)|
      ∂(ν : Measure MatchingScene)) ≤ ENNReal.ofReal (C / r + 4 * ε * ρ) := by
  have hcurrent : Continuous (fun scene : MatchingScene ↦ (scene.path.rootCurrent : ℝ)) :=
    (continuous_of_discreteTopology : Continuous (fun k : ℤ ↦ (k : ℝ))).comp
      continuous_rootCurrent
  apply lintegral_ofReal_le_of_probability_tendsto hμ
    (hcurrent.sub (continuous_edgeTest _)).abs
  filter_upwards [henergy, hcount] with k hk hn
  rw [hlaw k]
  apply ((sample k).lintegral_rootCurrent_sub_crossingTest_le
    (graph k) (assignment k) (hab k) hε hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  have hr' : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  calc
    _ ≤ (b k - a k)⁻¹ * (C * (b k - a k) / r + 4 * ε * (ρ * (b k - a k))) :=
      mul_le_mul_of_nonneg_left (add_le_add (div_le_div_of_nonneg_right hk hr'.le)
        (mul_le_mul_of_nonneg_left hn (by positivity))) (inv_nonneg.mpr hlen.le)
    _ = _ := by field_simp

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- Every compact truncation of the unsigned soft crossing is controlled by the true finite
crossing lengths and actual endpoint windows. -/
theorem lintegral_abs_softCrossing_test_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) (r : ℕ) :
    (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges
      (LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase))
        (fun e ↦ |MatchingScene.softCrossing ε e|)
        (MatchingScene.continuous_softCrossing ε).abs r))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((b - a)⁻¹ * (((n : ℝ) + (∑ i,
        (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2)) / 2 +
          4 * ε * n)) := by
  let f := LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase))
    (fun e ↦ |MatchingScene.softCrossing ε e|)
    (MatchingScene.continuous_softCrossing ε).abs r
  let G : ℝ → ℝ := fun z ↦
    (∑ i, |(crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)|) +
      (FiniteMatching.endpointWindowCount (sample.sourceIntersection graph) ε z +
        FiniteMatching.endpointWindowCount (fun i ↦ sample.targetIntersection graph (σ i)) ε z)
  have hi₁ : Integrable (fun z ↦ ∑ i, |(crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)|) :=
    integrable_finsetSum _ (fun i _ ↦ FiniteMatching.integrable_abs_crossingSign _ _)
  have hi₂ := FiniteMatching.integrable_endpointWindowCount (sample.sourceIntersection graph) ε
  have hi₃ := FiniteMatching.integrable_endpointWindowCount
    (fun i ↦ sample.targetIntersection graph (σ i)) ε
  have hdom (z : ℝ) : LocalConfiguration.testIntegral
      (sample.rootedMatchingScene graph σ z).edges f ≤ G z := by
    change LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _ _) f ≤ _
    rw [LocalConfiguration.testIntegral_ofTuple]
    have hc (a b z : ℝ) : crossingSign (a - z) (b - z) 0 = crossingSign a b z := by
      simp only [crossingSign, sub_nonpos]
    have hp (i : Fin n) : f (sample.rootedSourcePoint graph z i,
        sample.rootedTargetPoint graph z (σ i)) ≤
        |(crossingSign (sample.sourceIntersection graph i)
          (sample.targetIntersection graph (σ i)) z : ℝ)| +
          ((if |sample.sourceIntersection graph i - z| ≤ ε then 1 else 0) +
            if |sample.targetIntersection graph (σ i) - z| ≤ ε then 1 else 0) := by
      apply (LocalConfiguration.compactWeightTest_le
        (MatchingScene.continuous_softCrossing ε).abs (fun _ ↦ abs_nonneg _) r _).trans
      have h := MatchingScene.abs_crossingSign_sub_softCrossing_le hε
        (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i))
      have ht := abs_sub_abs_le_abs_sub
        (MatchingScene.softCrossing ε (sample.rootedSourcePoint graph z i,
          sample.rootedTargetPoint graph z (σ i)))
        (crossingSign (sample.sourceIntersection graph i)
          (sample.targetIntersection graph (σ i)) z : ℝ)
      simp only [rootedSourcePoint, rootedTargetPoint, hc] at h
      rw [abs_sub_comm] at ht
      simp only [rootedSourcePoint, rootedTargetPoint] at ht ⊢
      exact (sub_le_iff_le_add.mp (ht.trans h)).trans_eq (add_comm _ _)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hp i)
    simpa only [G, FiniteMatching.endpointWindowCount, Finset.sum_add_distrib] using hs
  apply (sample.lintegral_rootedMatchingSceneLaw_le_of_integrable_domination graph σ hab
    (MatchingScene.continuous_edgeTest f).measurable (fun scene ↦ by
      rw [← LocalConfiguration.integral_countingMeasure]
      exact integral_nonneg (LocalConfiguration.compactWeightTest_nonneg
        (MatchingScene.continuous_softCrossing ε).abs (fun _ ↦ abs_nonneg _) r))
    (hi₁.add (hi₂.add hi₃)) hdom).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  have hadd₁ := integral_add hi₁ (hi₂.add hi₃)
  have hadd₂ := integral_add hi₂ hi₃
  simp only [Pi.add_apply] at hadd₁ hadd₂
  change (∫ z, G z) ≤ _
  dsimp only [G]
  rw [hadd₁, hadd₂, FiniteMatching.integral_endpointWindowCount _ hε.le,
    FiniteMatching.integral_endpointWindowCount _ hε.le,
    integral_finsetSum _ (fun i _ ↦ FiniteMatching.integrable_abs_crossingSign _ _)]
  simp_rw [FiniteMatching.integral_abs_crossingSign]
  have h (i : Fin n) : |sample.targetIntersection graph (σ i) -
      sample.sourceIntersection graph i| ≤
      (1 + (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|sample.targetIntersection graph (σ i) -
      sample.sourceIntersection graph i| - 1),
      sq_abs (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ h i)
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  linarith

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- Unsigned soft crossings have a finite full counting moment in the actual weak limit.
In particular, the estimate has no bound on the distant partner's position. -/
theorem lintegral_abs_softCrossing_of_rootedMatchingSceneLaw_tendsto
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
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal |softCrossing ε e|
      ∂LocalConfiguration.countingMeasure scene.edges ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal ((ρ + C) / 2 + 4 * ε * ρ) := by
  apply lintegral_countingWeight_le_of_compactTest_bounds _
    (continuous_softCrossing ε).abs (fun _ ↦ abs_nonneg _)
  intro r
  apply lintegral_edgeTest_le_of_tendsto hμ
  filter_upwards [henergy, hcount] with k hk hn
  rw [hlaw k]
  apply ((sample k).lintegral_abs_softCrossing_test_le
    (graph k) (assignment k) (hab k) hε r).trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  calc
    _ ≤ (b k - a k)⁻¹ * ((ρ * (b k - a k) + C * (b k - a k)) / 2 +
        4 * ε * (ρ * (b k - a k))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_right (add_le_add hn hk) (by norm_num))
        (mul_le_mul_of_nonneg_left hn (by positivity))) (inv_nonneg.mpr hlen.le)
    _ = _ := by field_simp

end OTSelector.PointProcess.MatchingScene
