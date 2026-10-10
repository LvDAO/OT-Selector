import OTSelector.Feedback.FeedbackSelectorGood
import OTSelector.PointProcess.MatchingSceneCutVacancy
import OTSelector.PointProcess.MatchingSceneLocalMinimality
import OTSelector.PointProcess.MatchingScenePhysicalHeightBlocks
import OTSelector.Matching.FeedbackSceneEnergyMoment

/-!
# Actual optimizer limits on a fixed macroscopic block

The original good event bounds the same stopped graph and the original Euclidean optimizer.
For a fixed block, its population and squared-displacement bounds scale by the block width.
The actual weak-limit theorems then supply stationarity, the geometric energy candidate, a finite
root crossing moment, and linear window energy means. The physical height-block mark average
converges to the genuine source Palm coupling. Environment identification remains an explicit
input of this intermediate assembly; none of the matching conclusions is an input.
-/

open MeasureTheory Set Filter Function Topology
open scoped BigOperators Classical ENNReal

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample

/-- The actual square-root-buffer graph has uniformly vanishing normalized absolute height
along every diverging sequence of no-tie samples. -/
theorem eventually_abs_feedbackFGL2Graph_div_lt
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hNpos : ∀ k, 0 < N k)
    (sample : ∀ k, FiniteSample (N k)) {lam amplitude : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hamp : 0 < amplitude)
    (hNoTie : ∀ k,
      (sample k).NoFeedbackTies lam (feedbackA2AsymptoticBuffer amplitude (N k)) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ z : ℝ,
      |((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude).curve z / N k| < ε := by
  have hsmall : Tendsto (fun k ↦ amplitude / 8 * (Real.sqrt (N k : ℝ) / N k))
      atTop (𝓝 0) := by
    convert (tendsto_sqrt_nat_div_nat.comp hN).const_mul (amplitude / 8) using 1 <;>
      simp only [mul_zero, Function.comp_def]
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with k hk
  intro z
  have hn : 0 < (N k : ℝ) := by exact_mod_cast hNpos k
  have hB : 0 < feedbackA2AsymptoticBuffer amplitude (N k) :=
    mul_pos hamp (Real.sqrt_pos.mpr hn)
  have hgraph := (sample k).abs_stoppedContinuationFeedbackGraph_curve_le
    hlam0 hlamHalf (feedbackA2AsymptoticEta lam) hB
    (feedbackA2AsymptoticHorizon amplitude (N k)) (hNoTie k) z
  rw [abs_div, abs_of_pos hn]
  apply (div_le_div_of_nonneg_right hgraph hn.le).trans_lt
  rw [feedbackA2AsymptoticBuffer_eq]
  convert hk using 1
  ring

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

private theorem measurableSet_multiset_nodup {X : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableSet {m : Multiset X | m.Nodup} := by
  have he (m : Multiset X) : m.Nodup ↔ ∀ i j : ℕ, i < j → j < m.card →
      (MultisetEncoding.paddedCode m).2 i ≠ (MultisetEncoding.paddedCode m).2 j := by
    rw [← Multiset.sort_eq m (MultisetEncoding.codingLE X), Multiset.coe_nodup,
      List.nodup_iff_getElem?_ne_getElem?]
    simp only [MultisetEncoding.paddedCode, Multiset.length_sort, Multiset.sort_eq]
  simp_rw [he]
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (measurableSet_lt measurable_const MultisetEncoding.measurable_card).imp
    (measurableSet_eq_fun
      ((measurable_pi_apply i).comp MultisetEncoding.measurable_paddedCode.snd)
      ((measurable_pi_apply j).comp MultisetEncoding.measurable_paddedCode.snd)).compl

private theorem endpoint_simple_iff_shell_nodup
    (config : LocalConfiguration matchingPointBase) :
    (∀ p, LocalConfiguration.multiplicity config p ≤ 1) ↔ ∀ n, (config n).Nodup := by
  let : DecidableEq MatchingPoint := Classical.decEq _
  constructor
  · intro h n
    apply Multiset.nodup_iff_count_le_one.mpr
    intro p
    simpa only [LocalConfiguration.multiplicity_shell] using h p.val
  · intro h p
    exact Multiset.nodup_iff_count_le_one.mp
      (h (LocalConfiguration.shellIndex matchingPointBase p)) ⟨p, rfl⟩

private theorem measurableSet_endpoint_simple :
    MeasurableSet {config : LocalConfiguration matchingPointBase |
      ∀ p, LocalConfiguration.multiplicity config p ≤ 1} := by
  simp_rw [endpoint_simple_iff_shell_nodup]
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun n ↦
    (LocalConfiguration.measurable_shell n) measurableSet_multiset_nodup

/-- The actual environment law transfers multiplicity one to each endpoint configuration.
The measurable shell code proves the support predicate measurable before it is pushed through
the original scene marginal of the actual roof joining. -/
theorem ae_endpoint_multiplicity_le_one_of_feedbackEnvironment
    {lam : ℝ} (hlam0 : 0 < lam) (hlamHalf : lam < 1 / 2)
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlamHalf) :
    ∀ᵐ scene ∂P,
      (∀ p, LocalConfiguration.multiplicity scene.source p ≤ 1) ∧
      (∀ p, LocalConfiguration.multiplicity scene.target p ≤ 1) := by
  let J := Matching.feedbackSceneRoofJoining lam hlam0 hlamHalf P P
  have hscene : J.map (fun q ↦ q.2.2.1) = P :=
    Matching.feedbackSceneRoofJoining_scene_left lam hlam0 hlamHalf P P henv
  rw [← hscene]
  apply (ae_map_iff measurable_snd.snd.fst.aemeasurable
    ((measurable_source measurableSet_endpoint_simple).inter
      (measurable_target measurableSet_endpoint_simple))).mpr
  filter_upwards [Matching.feedbackSceneRoofJoining_ae_environment
    lam hlam0 hlamHalf P P henv henv] with q hq
  constructor
  · have hs := congrArg FeedbackEnvironment.source hq.1
    change q.2.2.1.source = _ at hs
    change ∀ p, LocalConfiguration.multiplicity q.2.2.1.source p ≤ 1
    rw [hs]
    exact Matching.feedbackRerootedPoints_multiplicity_le_one q.2.1.1 q.2.1.2 1
  · have ht := congrArg FeedbackEnvironment.target hq.1
    change q.2.2.1.target = _ at ht
    change ∀ p, LocalConfiguration.multiplicity q.2.2.1.target p ≤ 1
    rw [ht]
    exact Matching.feedbackRerootedPoints_multiplicity_le_one q.2.1.1 q.2.1.2 (-1)

/-- All matching-limit conclusions on one fixed interior macroscopic block follow from actual
good samples and their weak root-law limit. The sole remaining environment input is its stated
law identity; stationarity, matching optimality, and both energy bounds are derived here. -/
theorem feedbackFGL2_selectorLimit_of_good
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hNpos : ∀ k, 0 < N k)
    (sample : ∀ k, FiniteSample (N k))
    {lam amplitude globalQ endpointQ C u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hamp : 0 < amplitude)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hgood : ∀ k, sample k ∈
      feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (N k))
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw
        ((sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)
        (sample k).euclideanOptimizer ((N k : ℝ) * u) ((N k : ℝ) * v))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    (henv : (ν : Measure MatchingScene).map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num))) :
    (∀ t : ℝ, MeasurePreserving (reroot t) (ν : Measure MatchingScene) ν) ∧
      (∀ᵐ scene ∂(ν : Measure MatchingScene), Matching.FeedbackSceneEnergyCandidate lam scene) ∧
      ((∫⁻ scene, crossingEnergyMoment scene 0 ∂(ν : Measure MatchingScene)) ≤
        ENNReal.ofReal ((1 / (v-u) + 3 * (C / (v-u))) / 2)) ∧
      ((∫⁻ scene, crossingEnergyMoment scene 0 ∂(ν : Measure MatchingScene)) < ∞) ∧
      (∀ h L : ℝ, 0 ≤ L →
        Integrable (fun scene ↦ Matching.feedbackSceneWindowEnergy scene h L)
          (ν : Measure MatchingScene) ∧
        (∫ scene, Matching.feedbackSceneWindowEnergy scene h L ∂(ν : Measure MatchingScene)) ≤
          ((1 / (v-u) + 3 * (C / (v-u))) / 2) * L) ∧
      (∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (sample k).euclideanOptimizer ψ u v)
          atTop (𝓝 (∫ m, ψ m ∂Matching.feedbackProjectiveLaw (ν : Measure MatchingScene)))) := by
  let graph (k : ℕ) :=
    (sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude
  let a (k : ℕ) : ℝ := (N k : ℝ) * u
  let b (k : ℕ) : ℝ := (N k : ℝ) * v
  have hn (k : ℕ) : 0 < (N k : ℝ) := by exact_mod_cast hNpos k
  have hw : 0 < v-u := sub_pos.mpr huv
  have hab (k : ℕ) : a k < b k := mul_lt_mul_of_pos_left huv (hn k)
  have hwidth (k : ℕ) : b k - a k = (N k : ℝ) * (v-u) := by
    dsimp only [a, b]
    ring
  have hscale : Tendsto (fun k ↦ (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hwindow : Tendsto (fun k ↦ b k-a k) atTop atTop := by
    simp_rw [hwidth]
    exact hscale.atTop_mul_const hw
  have hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ (1 / (v-u)) * (b k-a k) := by
    apply Eventually.of_forall
    intro k
    apply le_of_eq
    rw [hwidth]
    field_simp [hw.ne']
  have henergy : ∀ᶠ k in atTop,
      (∑ i, ((sample k).targetIntersection (graph k) ((sample k).euclideanOptimizer i) -
        (sample k).sourceIntersection (graph k) i)^2) ≤ (C / (v-u)) * (b k-a k) := by
    apply Eventually.of_forall
    intro k
    have he := feedbackSelectorGoodEvent.energy (hgood k)
    change (∑ i, ((sample k).targetIntersection (graph k) ((sample k).euclideanOptimizer i) -
      (sample k).sourceIntersection (graph k) i)^2) ≤ C * (N k : ℝ) at he
    rw [hwidth]
    convert he using 1
    field_simp [hw.ne']
  have hC : 0 ≤ C := by
    have he := feedbackSelectorGoodEvent.energy (hgood 0)
    have he0 : 0 ≤ (sample 0).feedbackFGL2OptimizerEnergy
        hlam0.le (hlam.trans (by norm_num)) amplitude :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    exact nonneg_of_mul_nonneg_left (he0.trans he) (hn 0)
  have hbound0 : 0 ≤ (1 / (v-u) + 3 * (C / (v-u))) / 2 := by positivity
  have hNoTie (k : ℕ) := feedbackSelectorGoodEvent.noFeedbackTies (hgood k)
  have hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ z ∈ Ioc (a k) (b k), |(graph k).curve z / N k| < ε := by
    intro ε hε
    exact (FiniteSample.eventually_abs_feedbackFGL2Graph_div_lt
      hN hNpos sample hlam0.le (hlam.trans (by norm_num)) hamp hNoTie hε).mono
        fun k hk z _ ↦ hk z
  have hstat : ∀ t : ℝ, MeasurePreserving (reroot t) (ν : Measure MatchingScene) ν :=
    measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto_of_count_bound
      sample graph (fun k ↦ (sample k).euclideanOptimizer) a b hab
      hlaw hlim htight hwindow hcount
  have hvac := ae_vacantCut_of_rootedMatchingSceneLaw_tendsto
    sample graph (fun k ↦ (sample k).euclideanOptimizer) a b hab hlaw hlim hcount 0
  have hzero : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ x : SourceAtom scene, x.val.1 ≠ 0) ∧ (∀ y : TargetAtom scene, y.val.1 ≠ 0) := by
    filter_upwards [hvac] with scene hs
    exact ⟨fun x hx ↦ x.property (hs.1 x.val hx), fun y hy ↦ y.property (hs.2 y.val hy)⟩
  have hsimple := ae_endpoint_multiplicity_le_one_of_feedbackEnvironment
    hlam0 (hlam.trans (by norm_num)) (ν : Measure MatchingScene) henv
  have hcandidate := ae_feedbackSceneEnergyCandidate_of_rootedEuclideanSceneLaw_tendsto
    sample graph a b hab hlam0.le hlam hlaw hlim htight hscale hheight henergy hcount hzero hsimple
  have hperfect := hcandidate.mono fun _ hc ↦ hc.perfect
  have hcross := lintegral_crossingEnergyMoment_zero_of_rootedMatchingSceneLaw_tendsto
    sample graph (fun k ↦ (sample k).euclideanOptimizer) a b hab hlaw hlim
      henergy hcount hperfect hzero
  refine ⟨hstat, hcandidate, hcross, hcross.trans_lt ENNReal.ofReal_lt_top, ?_, ?_⟩
  · intro h L hL
    exact Matching.feedbackSceneWindowEnergy_moment_le (ν : Measure MatchingScene) hstat
      (hcandidate.mono fun _ hc ↦ ⟨hc.perfect, hc.finite_crossings⟩) hbound0 hcross h L hL
  · intro ψ
    exact FiniteSample.tendsto_feedbackFGL2_sourceHeightBlockMarks
      hN hNpos sample hlam0 (hlam.trans (by norm_num)) hamp hu huv hv hNoTie
      (fun k ↦ feedbackSelectorGoodEvent.globalCut (hgood k))
      (fun k ↦ (sample k).euclideanOptimizer) hlaw hlim henv hperfect hstat ψ

end OTSelector.PointProcess.MatchingScene
