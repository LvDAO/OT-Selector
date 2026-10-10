import OTSelector.PointProcess.MatchingScenePerfect
import OTSelector.PointProcess.FiniteMatchingSceneLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Energy transport through actual rooted matching laws

All estimates below average a fixed finite sample over its spatial root. A deterministic bound
on that sample's energy passes to a weak limit of these laws through nonnegative continuous
tests. This does not infer an untruncated annealed moment from a high-probability energy bound.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal CompactlySupported Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess

/-- Nonnegative continuous moments pass to weak probability limits. The proof uses bounded
truncations and needs no metrization of the underlying scene topology. -/
theorem lintegral_ofReal_le_of_probability_tendsto
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {ι : Type*} {l : Filter ι} [NeBot l]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hμ : Tendsto μ l (𝓝 ν)) {f : X → ℝ} (hf : Continuous f)
    {B : ℝ≥0∞} (hB : ∀ᶠ i in l, (∫⁻ x, ENNReal.ofReal (f x) ∂(μ i : Measure X)) ≤ B) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure X)) ≤ B := by
  let g (n : ℕ) : BoundedContinuousFunction X ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ min (n : ℝ) (max 0 (f x)), continuous_const.min (continuous_const.max hf)⟩
    n (fun x y ↦ by
      rw [Real.dist_eq, abs_le]
      change -(n : ℝ) ≤ min (n : ℝ) (max 0 (f x)) - min (n : ℝ) (max 0 (f y)) ∧
        min (n : ℝ) (max 0 (f x)) - min (n : ℝ) (max 0 (f y)) ≤ (n : ℝ)
      have hx0 : 0 ≤ min (n : ℝ) (max 0 (f x)) := le_min (Nat.cast_nonneg _) (le_max_left _ _)
      have hy0 : 0 ≤ min (n : ℝ) (max 0 (f y)) := le_min (Nat.cast_nonneg _) (le_max_left _ _)
      have hxn := min_le_left (n : ℝ) (max 0 (f x))
      have hyn := min_le_left (n : ℝ) (max 0 (f y))
      constructor <;> linarith)
  have hlim (n : ℕ) := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ
    (g n).nnrealPart
  have htrunc (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (min (n : ℝ) (max 0 (f x))) ∂(ν : Measure X)) ≤ B := by
    apply le_of_tendsto (hlim n)
    filter_upwards [hB] with i hi
    apply le_trans (lintegral_mono (fun x ↦ ?_)) hi
    change ENNReal.ofReal (min (n : ℝ) (max 0 (f x))) ≤ ENNReal.ofReal (f x)
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (f x) from zero_le)] using
      ENNReal.ofReal_le_ofReal (min_le_right (n : ℝ) (max 0 (f x)))
  have hsup (x : X) :
      (⨆ n : ℕ, ENNReal.ofReal (min (n : ℝ) (max 0 (f x)))) = ENNReal.ofReal (f x) := by
    apply le_antisymm
    · refine iSup_le fun n ↦ ?_
      simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (f x) from zero_le)] using
        ENNReal.ofReal_le_ofReal (min_le_right (n : ℝ) (max 0 (f x)))
    · obtain ⟨n, hn⟩ := exists_nat_ge (max 0 (f x))
      calc
        ENNReal.ofReal (f x) = ENNReal.ofReal (min (n : ℝ) (max 0 (f x))) := by
          rw [min_eq_right hn, ENNReal.ofReal_max]
          simp
        _ ≤ _ := le_iSup (fun k : ℕ ↦ ENNReal.ofReal (min (k : ℝ) (max 0 (f x)))) n
  simp_rw [← hsup]
  rw [lintegral_iSup (fun n ↦ (continuous_const.min (continuous_const.max hf)).measurable.ennreal_ofReal)
    (fun n m hnm x ↦ ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hnm)))]
  exact iSup_le htrunc

namespace LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] {base : X}

/-- Compact truncations increase to a continuous nonnegative counting weight. -/
noncomputable def compactWeightTest (w : X → ℝ) (hw : Continuous w) (n : ℕ) : C_c(X, ℝ) where
  toFun x := min 1 (max 0 ((n : ℝ) + 1 - dist x base)) * w x
  continuous_toFun := (continuous_const.min (continuous_const.max
    (continuous_const.sub (continuous_id.dist continuous_const)))).mul hw
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall base ((n : ℝ) + 1))
    intro x hx
    by_contra hn
    have hdist : (n : ℝ) + 1 ≤ dist x base := (lt_of_not_ge hn).le
    exact hx (by simp only [max_eq_left (sub_nonpos.mpr hdist), min_eq_right zero_le_one, zero_mul])

omit [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] in
theorem compactWeightTest_nonneg {w : X → ℝ} (hw : Continuous w) (h0 : ∀ x, 0 ≤ w x)
    (n : ℕ) (x : X) : 0 ≤ compactWeightTest (base := base) w hw n x :=
  mul_nonneg (le_min zero_le_one (le_max_left _ _)) (h0 x)

omit [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] in
theorem compactWeightTest_le {w : X → ℝ} (hw : Continuous w) (h0 : ∀ x, 0 ≤ w x)
    (n : ℕ) (x : X) : compactWeightTest (base := base) w hw n x ≤ w x := by
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (h0 x)).trans_eq (one_mul _)

omit [StandardBorelSpace X] in
/-- The full, possibly infinite counting moment is the increasing supremum of genuine compact
continuous edge tests, so no partner-radius truncation remains in this identity. -/
theorem lintegral_countingWeight_eq_iSup_test
    (config : LocalConfiguration base) {w : X → ℝ} (hw : Continuous w) (h0 : ∀ x, 0 ≤ w x) :
    (∫⁻ x, ENNReal.ofReal (w x) ∂countingMeasure config) =
      ⨆ n : ℕ, ENNReal.ofReal (testIntegral config (compactWeightTest (base := base) w hw n)) := by
  have hmono : Monotone (fun n : ℕ ↦ fun x ↦ ENNReal.ofReal
      (compactWeightTest (base := base) w hw n x)) := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (h0 x)
    apply min_le_min_left
    apply max_le_max_left
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hsup (x : X) : (⨆ n : ℕ, ENNReal.ofReal
      (compactWeightTest (base := base) w hw n x)) = ENNReal.ofReal (w x) := by
    apply le_antisymm (iSup_le fun n ↦ ENNReal.ofReal_le_ofReal (compactWeightTest_le hw h0 n x))
    obtain ⟨n, hn⟩ := exists_nat_ge (dist x base)
    have heq : compactWeightTest (base := base) w hw n x = w x := by
      have h1 : (1 : ℝ) ≤ max 0 ((n : ℝ) + 1 - dist x base) :=
        (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1 - dist x base).trans (le_max_right _ _)
      change min 1 (max 0 ((n : ℝ) + 1 - dist x base)) * w x = w x
      rw [min_eq_left h1, one_mul]
    rw [← heq]
    exact le_iSup (fun k : ℕ ↦ ENNReal.ofReal (compactWeightTest (base := base) w hw k x)) n
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (compactWeightTest (base := base) w hw n x)
        ∂countingMeasure config := by simp only [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (compactWeightTest (base := base) w hw n x)
        ∂countingMeasure config := lintegral_iSup
      (fun n ↦ (compactWeightTest w hw n).continuous.measurable.ennreal_ofReal) hmono
    _ = _ := by
      congr 1
      funext n
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_countingMeasure _ _)
        (ae_of_all _ (compactWeightTest_nonneg hw h0 n)), integral_countingMeasure]

end LocalConfiguration

namespace MatchingScene

noncomputable local instance transportEdgeTopology : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

/-- Continuous edge occupation observables use the actual configuration counting measure. -/
theorem continuous_edgeTest (f : C_c(MatchingPoint × MatchingPoint, ℝ)) :
    Continuous (fun scene : MatchingScene ↦ LocalConfiguration.testIntegral scene.edges f) :=
  (LocalConfiguration.continuous_testIntegral f).comp continuous_edges

/-- Any uniform finite bound on a nonnegative actual edge test survives a weak scene-law limit. -/
theorem lintegral_edgeTest_le_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {μ : ι → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hμ : Tendsto μ l (𝓝 ν)) (f : C_c(MatchingPoint × MatchingPoint, ℝ))
    {B : ℝ≥0∞}
    (hB : ∀ᶠ i in l, (∫⁻ scene, ENNReal.ofReal
      (LocalConfiguration.testIntegral scene.edges f) ∂(μ i : Measure MatchingScene)) ≤ B) :
    (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges f)
      ∂(ν : Measure MatchingScene)) ≤ B :=
  lintegral_ofReal_le_of_probability_tendsto hμ (continuous_edgeTest f) hB

/-- A bound for all compact truncations controls the full counting moment, including partners
arbitrarily far from the root. -/
theorem lintegral_countingWeight_le_of_compactTest_bounds
    (P : Measure MatchingScene) {w : MatchingPoint × MatchingPoint → ℝ}
    (hw : Continuous w) (h0 : ∀ e, 0 ≤ w e) {B : ℝ≥0∞}
    (hB : ∀ n : ℕ, (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges
      (LocalConfiguration.compactWeightTest (base := (matchingPointBase, matchingPointBase)) w hw n)) ∂P) ≤ B) :
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (w e)
      ∂LocalConfiguration.countingMeasure scene.edges ∂P) ≤ B := by
  simp_rw [LocalConfiguration.lintegral_countingWeight_eq_iSup_test _ hw h0]
  rw [lintegral_iSup (fun n ↦
    (continuous_edgeTest (LocalConfiguration.compactWeightTest w hw n)).measurable.ennreal_ofReal) ?_]
  · exact iSup_le hB
  · intro n m hnm scene
    apply ENNReal.ofReal_le_ofReal
    rw [← LocalConfiguration.integral_countingMeasure, ← LocalConfiguration.integral_countingMeasure]
    apply integral_mono (LocalConfiguration.integrable_countingMeasure _ _)
      (LocalConfiguration.integrable_countingMeasure _ _)
    intro e
    change min 1 (max 0 ((n : ℝ) + 1 - dist e (matchingPointBase, matchingPointBase))) * w e ≤
      min 1 (max 0 ((m : ℝ) + 1 - dist e (matchingPointBase, matchingPointBase))) * w e
    apply mul_le_mul_of_nonneg_right _ (h0 e)
    apply min_le_min_left
    apply max_le_max_left
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith

end MatchingScene
end OTSelector.PointProcess

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

private theorem integrable_energyWindow (x A d : ℝ) :
    Integrable (fun z : ℝ ↦ if |x - z| ≤ A then d ^ 2 else 0) := by
  have heq : (fun z : ℝ ↦ if |x - z| ≤ A then d ^ 2 else 0) =
      (Icc (x - A) (x + A)).indicator (fun _ ↦ d ^ 2) := by
    funext z
    have h : |x - z| ≤ A ↔ z ∈ Icc (x - A) (x + A) := by
      rw [abs_le, mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [Set.indicator_apply, h]
  rw [heq]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

private theorem integral_energyWindow (x d : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫ z : ℝ, if |x - z| ≤ A then d ^ 2 else 0) = 2 * A * d ^ 2 := by
  have heq : (fun z : ℝ ↦ if |x - z| ≤ A then d ^ 2 else 0) =
      (Icc (x - A) (x + A)).indicator (fun _ ↦ d ^ 2) := by
    funext z
    have h : |x - z| ≤ A ↔ z ∈ Icc (x - A) (x + A) := by
      rw [abs_le, mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [Set.indicator_apply, h]
  rw [heq, integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le (by linarith)]
  simp only [smul_eq_mul]
  ring

/-- Fixed-sample source-window energy bound for every nonnegative compact edge test dominated
by the actual squared displacement. The assignment and the original graph are unrestricted. -/
theorem lintegral_rootedMatchingSceneLaw_edgeTest_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b A : ℝ} (hab : a < b) (hA : 0 ≤ A)
    (f : C_c(MatchingPoint × MatchingPoint, ℝ))
    (hf0 : ∀ e, 0 ≤ f e)
    (hfbound : ∀ e, f e ≤ (e.2.1 - e.1.1) ^ 2)
    (hfsupport : ∀ e, A < |e.1.1| → f e = 0) :
    (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges f)
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((2 * A / (b - a)) *
        ∑ i, (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) := by
  let F : ℝ → ℝ := fun z ↦ LocalConfiguration.testIntegral
    (sample.rootedMatchingScene graph σ z).edges f
  let G : ℝ → ℝ := fun z ↦ ∑ i, if |sample.sourceIntersection graph i - z| ≤ A then
    (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2 else 0
  have hG : Integrable G := integrable_finsetSum _ fun i _ ↦ integrable_energyWindow _ _ _
  have hG0 (z : ℝ) : 0 ≤ G z := Finset.sum_nonneg fun i _ ↦ by split_ifs <;> positivity
  have hF0 (z : ℝ) : 0 ≤ F z := by
    dsimp [F, rootedMatchingScene]
    rw [LocalConfiguration.testIntegral_ofTuple]
    exact Finset.sum_nonneg fun i _ ↦ hf0 _
  have hFG (z : ℝ) : F z ≤ G z := by
    dsimp [F, G, rootedMatchingScene]
    rw [LocalConfiguration.testIntegral_ofTuple]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hz : |sample.sourceIntersection graph i - z| ≤ A
    · rw [ite_eq_left hz]
      have h := hfbound (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i))
      simpa only [rootedSourcePoint, rootedTargetPoint, sub_sub_sub_cancel_right] using h
    · rw [ite_eq_right hz, hfsupport _ (lt_of_not_ge hz)]
  have hFm : Measurable F :=
    (MatchingScene.continuous_edgeTest f).measurable.comp
      (sample.measurable_rootedMatchingScene graph σ)
  have hF : Integrable F := hG.mono' hFm.aestronglyMeasurable <| ae_of_all _ fun z ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 z)] using hFG z
  have hroot : Integrable (fun scene ↦ LocalConfiguration.testIntegral scene.edges f)
      (sample.rootedMatchingSceneLaw graph σ a b) := by
    rw [rootedMatchingSceneLaw]
    apply (integrable_map_measure (MatchingScene.continuous_edgeTest f).measurable.aestronglyMeasurable
      (sample.measurable_rootedMatchingScene graph σ).aemeasurable).mpr
    simp only [Probability.spatialRootLaw, ProbabilityTheory.cond, Real.volume_Ioc]
    exact hF.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr
      ((ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'))
  rw [← ofReal_integral_eq_lintegral_ofReal hroot (ae_of_all _ fun scene ↦ by
    change 0 ≤ LocalConfiguration.testIntegral scene.edges f
    rw [← LocalConfiguration.integral_countingMeasure]
    exact integral_nonneg hf0)]
  apply ENNReal.ofReal_le_ofReal
  rw [sample.integral_rootedMatchingSceneLaw graph σ hab.le _
    (MatchingScene.continuous_edgeTest f).measurable]
  change (b - a)⁻¹ * ∫ z in a..b, F z ≤ _
  rw [intervalIntegral.integral_of_le hab.le]
  calc
    (b - a)⁻¹ * ∫ z in Ioc a b, F z ≤ (b - a)⁻¹ * ∫ z, G z := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
      exact (setIntegral_mono_on hF.integrableOn hG.integrableOn measurableSet_Ioc
        (fun z _ ↦ hFG z)).trans (setIntegral_le_integral hG (ae_of_all _ hG0))
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_energyWindow _ _ _)]
      simp_rw [integral_energyWindow _ _ hA]
      rw [← Finset.mul_sum]
      ring

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- A fixed-energy sequence of actual finite rooted laws has a full local second moment in
any weak limit. The hypotheses concern the concrete samples, not their annealed energy. -/
theorem lintegral_sourceWeightedEnergy_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν)) {C : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    {ψ : MatchingPoint → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∀ x, ψ x ≤ 1) {A : ℝ} (hA : 0 ≤ A)
    (hψsupport : ∀ x, A < |x.1| → ψ x = 0) :
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (ψ e.1 * (e.2.1 - e.1.1) ^ 2)
      ∂LocalConfiguration.countingMeasure scene.edges ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal (2 * A * C) := by
  let w : MatchingPoint × MatchingPoint → ℝ := fun e ↦ ψ e.1 * (e.2.1 - e.1.1) ^ 2
  have hw : Continuous w := (hψ.comp continuous_fst).mul
    (((continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)).pow 2)
  have hw0 (e : MatchingPoint × MatchingPoint) : 0 ≤ w e := mul_nonneg (hψ0 _) (sq_nonneg _)
  apply lintegral_countingWeight_le_of_compactTest_bounds _ hw hw0
  intro r
  apply lintegral_edgeTest_le_of_tendsto hμ
  filter_upwards [henergy] with k hk
  rw [hlaw k]
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  apply ((sample k).lintegral_rootedMatchingSceneLaw_edgeTest_le
    (graph k) (assignment k) (hab k) hA
    (LocalConfiguration.compactWeightTest w hw r)
    (LocalConfiguration.compactWeightTest_nonneg hw hw0 r) (fun e ↦ ?_) (fun e he ↦ ?_)).trans
  · apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 * A / (b k - a k)) * (C * (b k - a k)) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by field_simp [ne_of_gt hlen]
  · exact (LocalConfiguration.compactWeightTest_le hw hw0 r e).trans
      ((mul_le_mul_of_nonneg_right (hψ1 _) (sq_nonneg _)).trans_eq (one_mul _))
  · change min 1 (max 0 ((r : ℝ) + 1 - dist e (matchingPointBase, matchingPointBase))) *
      (ψ e.1 * (e.2.1 - e.1.1) ^ 2) = 0
    rw [hψsupport _ he, zero_mul, mul_zero]

end OTSelector.PointProcess.MatchingScene
