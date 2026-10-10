import OTSelector.Feedback.FeedbackAggregateCountMoment
import OTSelector.Feedback.FeedbackBulkBackwardWindow
import OTSelector.PointProcess.MatchingSceneStationarity

/-!
# Aggregate spatial collision budgets

Actual stopped two-colour count increments are identified with physical spatial windows on
survival.  This retains cross-colour pairs and the original finite-sample probability law.
-/

open MeasureTheory ProbabilityTheory Set Filter Function Topology
open scoped Classical BigOperators ENNReal NNReal CompactlySupported
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

/-- Number of source and target points in the same spatial interval, with all multiplicities. -/
noncomputable def aggregateSpatialIocCount (scene : MatchingScene) (a b : ℝ) : ℝ :=
  (LocalConfiguration.spatialCount scene.source a b : ℝ) +
    (LocalConfiguration.spatialCount scene.target a b : ℝ)

theorem measurable_aggregateSpatialIocCount :
    Measurable (fun p : (ℝ×ℝ) × MatchingScene ↦ aggregateSpatialIocCount p.2 p.1.1 p.1.2) := by
  have hs := LocalConfiguration.measurable_spatialCount.comp
    (measurable_fst.prodMk (measurable_source.comp measurable_snd))
  have ht := LocalConfiguration.measurable_spatialCount.comp
    (measurable_fst.prodMk (measurable_target.comp measurable_snd))
  exact ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp hs).add
    ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp ht)

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample
open PointProcess CountingProcess
variable {n : ℕ} {lam : ℝ}

attribute [local irreducible] feedbackState feedbackCurve stoppedContinuationFeedbackGraph

local instance (c d : ℝ) : SFinite (Probability.spatialRootLaw c d) := by
  unfold Probability.spatialRootLaw ProbabilityTheory.cond
  infer_instance

private theorem spatialCount_ofTuple_eq_cut_difference
    (points : Fin n → MatchingPoint) {a b : ℝ} (hab : a ≤ b) :
    (LocalConfiguration.spatialCount (LocalConfiguration.ofTuple matchingPointBase points) a b : ℝ) =
      ((Finset.univ.filter fun i ↦ (points i).1 ≤ b).card : ℝ) -
        (Finset.univ.filter fun i ↦ (points i).1 ≤ a).card := by
  have h := LocalConfiguration.orientedCount_ofTuple points a b
  rw [LocalConfiguration.orientedCount,
    LocalConfiguration.spatialCount_eq_zero_of_le _ hab, sub_zero] at h
  simpa only [Int.cast_sub, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Finset.sum_boole, Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℝ)) h

/-- The scene's aggregate count is the actual difference of finite spatial cut counts. -/
theorem aggregateSpatialIocCount_rootedMatchingScene
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (z : ℝ) {a b : ℝ} (hab : a ≤ b) :
    MatchingScene.aggregateSpatialIocCount (sample.rootedMatchingScene graph σ z) a b =
      ((sample.graphSourceCutCount graph (z+b) : ℝ) - sample.graphSourceCutCount graph (z+a)) +
      ((sample.graphTargetCutCount graph (z+b) : ℝ) - sample.graphTargetCutCount graph (z+a)) := by
  unfold MatchingScene.aggregateSpatialIocCount rootedMatchingScene
  rw [spatialCount_ofTuple_eq_cut_difference _ hab,
    spatialCount_ofTuple_eq_cut_difference _ hab]
  simp only [rootedSourcePoint, rootedTargetPoint, graphSourceCutCount, graphTargetCutCount,
    sub_le_iff_le_add, add_comm]

/-- Aggregate physical count in a retained elapsed-time window of the actual frozen graph. -/
noncomputable def stoppedGraphAggregateWindowCount
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T s t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
  ((sample.graphSourceCutCount graph (B+(t:ℝ)) : ℝ) -
    sample.graphSourceCutCount graph (B+(s:ℝ))) +
  ((sample.graphTargetCutCount graph (B+(t:ℝ)) : ℝ) -
    sample.graphTargetCutCount graph (B+(s:ℝ)))

/-- On actual A1 survival, any strictly interior physical window is exactly the stopped aggregate
count window. Initial backlogs cancel and no assumption about the matching is used. -/
theorem stoppedGraphAggregateWindowCount_eq_of_survival
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ht : t < T)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    stoppedGraphAggregateWindowCount hlam0 hlamHalf eta B T s t sample =
      safeAggregateA1WindowCount hlam0 hlamHalf eta B B 0 T s t sample := by
  have hsT : s ≤ T := hst.trans ht.le
  have hA1Bulk : (T : WithTop ℝ≥0) ≤ safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    rw [← hstop]
    exact min_le_left _ _
  have htExit : (t : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_lt_coe.mpr ht).trans_le hA1Bulk
  have hsExit : (s : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_le_coe.mpr hst).trans_lt htExit
  rw [safeAggregateA1WindowCount,
    stoppedProcess_eq_of_le (show (t : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample by rw [hstop]; exact_mod_cast ht.le),
    stoppedProcess_eq_of_le (show (s : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample by rw [hstop]; exact_mod_cast hsT)]
  unfold stoppedGraphAggregateWindowCount safeAggregateBulkCount
  dsimp only
  rw [← sourceFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T t sample hNoTie hstop ht.le,
    ← sourceFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T s sample hNoTie hstop hsT,
    ← targetFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T t sample hNoTie hstop ht.le,
    ← targetFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T s sample hNoTie hstop hsT,
    safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 t sample htExit,
    safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 s sample hsExit,
    safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 t sample htExit,
    safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 s sample hsExit,
    sourceFullCount_eq_initial_card_add_safeSourceCount, sourceFullCount_eq_initial_card_add_safeSourceCount,
    targetFullCount_eq_initial_card_add_safeTargetCount, targetFullCount_eq_initial_card_add_safeTargetCount]
  push_cast
  ring

/-- The actual graph window has a two-point probability of order window length squared on
survival, under the original sample law. This covers every pair of colours. -/
theorem measureReal_stoppedGraphAggregateWindowCount_ge_two_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t < T) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | sample.NoFeedbackTies lam B 0 ∧
        safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T sample = (T : WithTop ℝ≥0) ∧
        2 ≤ stoppedGraphAggregateWindowCount hlam0.le (by linarith) eta B T s t sample} ≤
      36 * ((t : ℝ)-s)^2 := by
  apply (measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (show {sample | sample.NoFeedbackTies lam B 0 ∧
        safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T sample = (T : WithTop ℝ≥0) ∧
        2 ≤ stoppedGraphAggregateWindowCount hlam0.le (by linarith) eta B T s t sample} ⊆
      {sample | 2 ≤ safeAggregateA1WindowCount hlam0.le (by linarith) eta B B 0 T s t sample} from ?_)).trans
        (measureReal_safeAggregateA1WindowCount_ge_two_le hlam0 hlam hn hB heta hetaSmall T hst)
  intro sample hs
  change 2 ≤ safeAggregateA1WindowCount _ _ eta B B 0 T s t sample
  rw [← stoppedGraphAggregateWindowCount_eq_of_survival hlam0.le (by linarith)
    eta B T hst ht sample hs.1 hs.2.1]
  exact hs.2.2

attribute [local irreducible] LocalConfiguration.spatialCount LocalConfiguration.ofTuple

/-- Aggregate endpoint counts are measurable for any measurable family of actual graph curves. -/
theorem measurable_aggregateSpatialIocCount_rootedScene_of_curve
    (graph : FiniteSample n → FeedbackGraph lam)
    (heval : ∀ x : ℝ, Measurable (fun sample : FiniteSample n ↦ (graph sample).curve x))
    (a b : ℝ) :
    Measurable (fun p : FiniteSample n × ℝ ↦ MatchingScene.aggregateSpatialIocCount
      (p.1.rootedEuclideanScene (graph p.1) p.2) a b) := by
  dsimp only [MatchingScene.aggregateSpatialIocCount, rootedEuclideanScene, rootedMatchingScene]
  have hs (i : Fin n) : Measurable (fun p : FiniteSample n × ℝ ↦
      p.1.rootedSourcePoint (graph p.1) p.2 i) :=
    ((measurable_sourceIntersection_of_curve graph heval i).comp measurable_fst |>.sub
      measurable_snd).prodMk ((measurable_sourceMark i).comp measurable_fst)
  have ht (i : Fin n) : Measurable (fun p : FiniteSample n × ℝ ↦
      p.1.rootedTargetPoint (graph p.1) p.2 i) :=
    ((measurable_targetIntersection_of_curve graph heval i).comp measurable_fst |>.sub
      measurable_snd).prodMk ((measurable_targetMark i).comp measurable_fst)
  have hcs := (LocalConfiguration.measurable_ofTuple matchingPointBase n).comp
    (measurable_pi_iff.mpr hs)
  have hct := (LocalConfiguration.measurable_ofTuple matchingPointBase n).comp
    (measurable_pi_iff.mpr ht)
  have hsCount : Measurable (fun p : FiniteSample n × ℝ ↦
      LocalConfiguration.spatialCount (LocalConfiguration.ofTuple matchingPointBase
        (p.1.rootedSourcePoint (graph p.1) p.2)) a b) :=
    LocalConfiguration.measurable_spatialCount.comp
      ((measurable_const (a := (a,b))).prodMk hcs)
  have htCount : Measurable (fun p : FiniteSample n × ℝ ↦
      LocalConfiguration.spatialCount (LocalConfiguration.ofTuple matchingPointBase
        (p.1.rootedTargetPoint (graph p.1) p.2)) a b) :=
    LocalConfiguration.measurable_spatialCount.comp
      ((measurable_const (a := (a,b))).prodMk hct)
  exact ((measurable_of_countable (fun k : ℤ ↦ (k : ℝ))).comp hsCount).add
    ((measurable_of_countable (fun k : ℤ ↦ (k : ℝ))).comp htCount)

/-- The original stopped optimizer has measurable collision counts because these only use its
actual endpoint arrays. -/
theorem measurable_aggregateSpatialIocCount_stoppedScene
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (a b : ℝ) :
    Measurable (fun p : FiniteSample n × ℝ ↦ MatchingScene.aggregateSpatialIocCount
      (p.1.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T p.2) a b) := by
  apply measurable_aggregateSpatialIocCount_rootedScene_of_curve
    (fun sample ↦ sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
  intro x
  exact (measurable_stoppedContinuationFeedbackGraph_curve_joint (n := n)
    hlam0 hlamHalf hB eta T).comp (measurable_id.prodMk (measurable_const (a := x)))

/-- The same survival event is used for every collision window: its masked annealed collision
probability is quadratic without adding a failure term for each window. -/
theorem measure_prod_stoppedScene_collision_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hleft : B ≤ c+a) (hright : d+b < B+(T:ℝ)) :
    ((finiteSampleLaw n : Measure (FiniteSample n)).prod (Probability.spatialRootLaw c d))
      {p | (p.1.NoFeedbackTies lam B 0 ∧
          safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T p.1 = (T : WithTop ℝ≥0)) ∧
        2 ≤ MatchingScene.aggregateSpatialIocCount
          (p.1.stoppedRootedEuclideanScene hlam0.le (by linarith) eta B T p.2) a b} ≤
      ENNReal.ofReal (36*(b-a)^2) := by
  have hlamHalf : lam < 1/2 := by linarith
  let P : Measure (FiniteSample n) := finiteSampleLaw n
  let R := Probability.spatialRootLaw c d
  let : IsProbabilityMeasure R := Probability.spatialRootLaw_isProbability hcd
  let G : Set (FiniteSample n) := {sample | sample.NoFeedbackTies lam B 0 ∧
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)}
  let E : Set (FiniteSample n × ℝ) := {p | 2 ≤ MatchingScene.aggregateSpatialIocCount
    (p.1.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T p.2) a b}
  have hτ : Measurable (safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B B 0 T) :=
    (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta B 0 T).measurable.mono
      (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta B 0 T).measurableSpace_le le_rfl
  have hNoTie : MeasurableSet {sample : FiniteSample n | sample.NoFeedbackTies lam B 0} := by
    simpa only [feedbackTieEvent, compl_ofPred, not_not] using
      (measurableSet_feedbackTieEvent_ambient (n := n) lam B 0).compl
  have hG : MeasurableSet G := hNoTie.inter
    (measurableSet_eq_fun hτ (measurable_const (a := (T : WithTop ℝ≥0))))
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_aggregateSpatialIocCount_stoppedScene hlam0.le hlamHalf hB eta T a b)
  have hpoint (z : ℝ) (hz : z ∈ Ioc c d) :
      P {ω | ω ∈ G ∧ (ω,z) ∈ E} ≤ ENNReal.ofReal (36*(b-a)^2) := by
    let s := (z+a-B).toNNReal
    let t := (z+b-B).toNNReal
    have hs0 : 0 ≤ z+a-B := by linarith [hz.1]
    have ht0 : 0 ≤ z+b-B := by linarith [hz.1]
    have hs : (s : ℝ) = z+a-B := by simp only [s, Real.coe_toNNReal', max_eq_left hs0]
    have ht : (t : ℝ) = z+b-B := by simp only [t, Real.coe_toNNReal', max_eq_left ht0]
    have hst : s ≤ t := by apply NNReal.coe_le_coe.mp; rw [hs, ht]; linarith
    have htT : t < T := by apply NNReal.coe_lt_coe.mp; rw [ht]; linarith [hz.2]
    have hcount (ω : FiniteSample n) : MatchingScene.aggregateSpatialIocCount
        (ω.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T z) a b =
        stoppedGraphAggregateWindowCount hlam0.le hlamHalf eta B T s t ω := by
      rw [stoppedRootedEuclideanScene, rootedEuclideanScene,
        aggregateSpatialIocCount_rootedMatchingScene _ _ _ _ hab]
      simp only [stoppedGraphAggregateWindowCount, hs, ht,
        show B+(z+b-B) = z+b by ring, show B+(z+a-B) = z+a by ring]
    have hsub : {ω | ω ∈ G ∧ (ω,z) ∈ E} ⊆
        {ω | ω.NoFeedbackTies lam B 0 ∧
          safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T ω = (T : WithTop ℝ≥0) ∧
          2 ≤ stoppedGraphAggregateWindowCount hlam0.le hlamHalf eta B T s t ω} := by
      intro ω hω
      refine ⟨hω.1.1, hω.1.2, ?_⟩
      rw [← hcount ω]
      exact hω.2
    have hreal := (measureReal_mono (μ := P) hsub).trans
      (measureReal_stoppedGraphAggregateWindowCount_ge_two_on_survival_le
        hlam0 hlam hn hB heta hetaSmall T hst htT)
    have hdiff : (t : ℝ)-s = b-a := by rw [ht, hs]; ring
    rw [hdiff] at hreal
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hreal
  have hroot : ∀ᵐ z ∂R, z ∈ Ioc c d := by
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  have hprod : P.prod R (E ∩ (G ×ˢ univ)) ≤ ENNReal.ofReal (36*(b-a)^2) := by
    rw [Measure.prod_apply_symm (hE.inter (hG.prod MeasurableSet.univ))]
    calc
      _ ≤ ∫⁻ _z, ENNReal.ofReal (36*(b-a)^2) ∂R := by
        apply lintegral_mono_ae
        filter_upwards [hroot] with z hz
        have heq : (fun ω ↦ (ω,z)) ⁻¹' (E ∩ (G ×ˢ univ)) =
            {ω | ω ∈ G ∧ (ω,z) ∈ E} := by
          ext ω
          simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, mem_ofPred_eq]
          tauto
        rw [heq]
        exact hpoint z hz
      _ = _ := by simp
  change P.prod R {p | p.1 ∈ G ∧ p ∈ E} ≤ _
  have heq : {p | p.1 ∈ G ∧ p ∈ E} = E ∩ (G ×ˢ univ) := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ]
    tauto
  rw [heq]
  exact hprod

/-- The actual probability law of a spatially rooted finite optimizer has a quadratic aggregate
collision budget, plus the actual A1/no-tie failure probability.  It is an annealed statement;
it does not assert a deterministic bound for each sampled configuration. -/
theorem measure_stoppedRootedEuclideanSceneLaw_aggregate_ge_two_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hleft : B ≤ c+a) (hright : d+b < B+(T:ℝ)) :
    stoppedRootedEuclideanSceneLaw (n := n) hlam0.le (by linarith) eta B T c d
      {scene | 2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} ≤
      (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | ¬(sample.NoFeedbackTies lam B 0 ∧
          safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T sample = (T : WithTop ℝ≥0))} +
        ENNReal.ofReal (36*(b-a)^2) := by
  have hlamHalf : lam < 1/2 := by linarith
  let P : Measure (FiniteSample n) := finiteSampleLaw n
  let R := Probability.spatialRootLaw c d
  let : IsProbabilityMeasure R := Probability.spatialRootLaw_isProbability hcd
  let G : Set (FiniteSample n) := {sample | sample.NoFeedbackTies lam B 0 ∧
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)}
  let E : Set (FiniteSample n × ℝ) := {p | 2 ≤ MatchingScene.aggregateSpatialIocCount
    (p.1.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T p.2) a b}
  have hsceneE : MeasurableSet {scene : MatchingScene |
      2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} :=
    measurableSet_le measurable_const
      (MatchingScene.measurable_aggregateSpatialIocCount.comp
        ((measurable_const (a := (a,b))).prodMk measurable_id))
  rw [stoppedRootedEuclideanSceneLaw, Probability.spatialAverageLaw,
    Measure.map_apply_of_aemeasurable
      (aemeasurable_stoppedRootedEuclideanScene hlam0.le hlamHalf hB eta T R) hsceneE]
  change P.prod R E ≤ P Gᶜ + ENNReal.ofReal (36*(b-a)^2)
  have hsub : E ⊆ (Gᶜ ×ˢ univ) ∪ {p | p.1 ∈ G ∧ p ∈ E} := by
    intro p hp
    by_cases hg : p.1 ∈ G
    · exact Or.inr ⟨hg, hp⟩
    · exact Or.inl ⟨hg, mem_univ _⟩
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact add_le_add_right (measure_prod_stoppedScene_collision_on_survival_le
    hlam0 hlam hn hB heta hetaSmall T hab hcd hleft hright) _

/-- The empirical collision fraction is the actual uniform-root law of one sampled optimizer. -/
noncomputable def stoppedEmpiricalCollisionFraction
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (a b c d : ℝ) (sample : FiniteSample n) : ℝ≥0∞ :=
  sample.rootedMatchingSceneLaw
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
    sample.euclideanOptimizer c d
      {scene | 2 ≤ MatchingScene.aggregateSpatialIocCount scene a b}

/-- Joint endpoint measurability makes the empirical collision fraction measurable in the
original sample, without modifying the Euclidean optimizer selection. -/
theorem measurable_stoppedEmpiricalCollisionFraction
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (a b c d : ℝ) :
    Measurable (stoppedEmpiricalCollisionFraction (n := n) hlam0 hlamHalf eta B T a b c d) := by
  let E : Set (FiniteSample n × ℝ) := {p | 2 ≤ MatchingScene.aggregateSpatialIocCount
    (p.1.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T p.2) a b}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_aggregateSpatialIocCount_stoppedScene hlam0 hlamHalf hB eta T a b)
  have hsceneE : MeasurableSet {scene : MatchingScene |
      2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} :=
    measurableSet_le measurable_const
      (MatchingScene.measurable_aggregateSpatialIocCount.comp ((measurable_const (a := (a,b))).prodMk measurable_id))
  have heq : stoppedEmpiricalCollisionFraction (n := n) hlam0 hlamHalf eta B T a b c d =
      (fun sample ↦ Probability.spatialRootLaw c d (Prod.mk sample ⁻¹' E)) := by
    funext sample
    unfold stoppedEmpiricalCollisionFraction rootedMatchingSceneLaw
    rw [Measure.map_apply (sample.measurable_rootedMatchingScene _ _) hsceneE]
    rfl
  rw [heq]
  exact measurable_measure_prodMk_left hE

/-- Averaging the actual empirical fraction gives exactly the annealed rooted-scene law. -/
theorem lintegral_stoppedEmpiricalCollisionFraction
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (a b c d : ℝ) :
    (∫⁻ sample, stoppedEmpiricalCollisionFraction (n := n) hlam0 hlamHalf eta B T a b c d sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      stoppedRootedEuclideanSceneLaw (n := n) hlam0 hlamHalf eta B T c d
        {scene | 2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} := by
  let E : Set (FiniteSample n × ℝ) := {p | 2 ≤ MatchingScene.aggregateSpatialIocCount
    (p.1.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T p.2) a b}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_aggregateSpatialIocCount_stoppedScene hlam0 hlamHalf hB eta T a b)
  have hsceneE : MeasurableSet {scene : MatchingScene |
      2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} :=
    measurableSet_le measurable_const
      (MatchingScene.measurable_aggregateSpatialIocCount.comp ((measurable_const (a := (a,b))).prodMk measurable_id))
  rw [stoppedRootedEuclideanSceneLaw, Probability.spatialAverageLaw,
    Measure.map_apply_of_aemeasurable
      (aemeasurable_stoppedRootedEuclideanScene hlam0 hlamHalf hB eta T _) hsceneE]
  change _ = ((finiteSampleLaw n : Measure (FiniteSample n)).prod
    (Probability.spatialRootLaw c d)) E
  rw [Measure.prod_apply hE]
  apply lintegral_congr
  intro sample
  unfold stoppedEmpiricalCollisionFraction rootedMatchingSceneLaw
  rw [Measure.map_apply (sample.measurable_rootedMatchingScene _ _) hsceneE]
  rfl

/-- The collision constraint can be included in actual high-probability sample selection.
The bound concerns the empirical fraction itself, with an explicit Markov budget. -/
theorem measure_stoppedEmpiricalCollisionFraction_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hleft : B ≤ c+a) (hright : d+b < B+(T:ℝ))
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ ∞) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | r ≤ stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T a b c d sample} ≤
      ((finiteSampleLaw n : Measure (FiniteSample n))
        {sample | ¬(sample.NoFeedbackTies lam B 0 ∧
          safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T sample = (T : WithTop ℝ≥0))} +
        ENNReal.ofReal (36*(b-a)^2)) / r := by
  apply (meas_ge_le_lintegral_div
    (measurable_stoppedEmpiricalCollisionFraction hlam0.le (by linarith) hB eta T a b c d).aemeasurable
    hr0 hrtop).trans
  rw [lintegral_stoppedEmpiricalCollisionFraction hlam0.le (by linarith) hB eta T a b c d]
  exact ENNReal.div_le_div_right
    (measure_stoppedRootedEuclideanSceneLaw_aggregate_ge_two_le
      hlam0 hlam hn hB heta hetaSmall T hab hcd hleft hright) r

/-- One common actual survival event for all observation windows and grid resolutions. -/
def StoppedCollisionGood (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : Prop :=
  sample.NoFeedbackTies lam B 0 ∧
    safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)

theorem measurableSet_stoppedCollisionGood
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) :
    MeasurableSet {sample : FiniteSample n | StoppedCollisionGood hlam0 hlamHalf eta B T sample} := by
  have hτ : Measurable (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B B 0 T) :=
    (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta B 0 T).measurable.mono
      (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta B 0 T).measurableSpace_le le_rfl
  have hNoTie : MeasurableSet {sample : FiniteSample n | sample.NoFeedbackTies lam B 0} := by
    simpa only [feedbackTieEvent, compl_ofPred, not_not] using
      (measurableSet_feedbackTieEvent_ambient (n := n) lam B 0).compl
  exact hNoTie.inter (measurableSet_eq_fun hτ (measurable_const (a := (T : WithTop ℝ≥0))))

/-- The spatial empirical collision fraction, restricted to the common survival event, has a
quadratic expectation with no repeated stopping-failure penalty. -/
theorem setLIntegral_stoppedEmpiricalCollisionFraction_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hleft : B ≤ c+a) (hright : d+b < B+(T:ℝ)) :
    (∫⁻ sample in {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample},
      stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T a b c d sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤ ENNReal.ofReal (36*(b-a)^2) := by
  have hlamHalf : lam < 1/2 := by linarith
  let G : Set (FiniteSample n) := {sample | StoppedCollisionGood hlam0.le hlamHalf eta B T sample}
  let E : Set (FiniteSample n × ℝ) := {p | 2 ≤ MatchingScene.aggregateSpatialIocCount
    (p.1.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T p.2) a b}
  have hG := measurableSet_stoppedCollisionGood (n := n) hlam0.le hlamHalf hB eta T
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (measurable_aggregateSpatialIocCount_stoppedScene hlam0.le hlamHalf hB eta T a b)
  have hsceneE : MeasurableSet {scene : MatchingScene |
      2 ≤ MatchingScene.aggregateSpatialIocCount scene a b} :=
    measurableSet_le measurable_const
      (MatchingScene.measurable_aggregateSpatialIocCount.comp
        ((measurable_const (a := (a,b))).prodMk measurable_id))
  have heq : (∫⁻ sample in G,
      stoppedEmpiricalCollisionFraction hlam0.le hlamHalf eta B T a b c d sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ((finiteSampleLaw n : Measure (FiniteSample n)).prod (Probability.spatialRootLaw c d))
        {p | p.1 ∈ G ∧ p ∈ E} := by
    have hGE : MeasurableSet {p : FiniteSample n × ℝ | p.1 ∈ G ∧ p ∈ E} :=
      (hG.preimage measurable_fst).inter hE
    rw [Measure.prod_apply hGE, ← lintegral_indicator hG]
    apply lintegral_congr
    intro sample
    by_cases hg : sample ∈ G
    · rw [indicator_of_mem hg]
      unfold stoppedEmpiricalCollisionFraction rootedMatchingSceneLaw
      rw [Measure.map_apply (sample.measurable_rootedMatchingScene _ _) hsceneE]
      congr 1
      ext z
      simp only [mem_preimage, mem_ofPred_eq, hg, true_and]
      rfl
    · rw [indicator_of_notMem hg]
      have hempty : Prod.mk sample ⁻¹' {p : FiniteSample n × ℝ | p.1 ∈ G ∧ p ∈ E} = ∅ := by
        ext z
        simp only [mem_preimage, mem_ofPred_eq, hg, false_and, notMem_empty]
      rw [hempty, measure_empty]
  rw [heq]
  exact measure_prod_stoppedScene_collision_on_survival_le
    hlam0 hlam hn hB heta hetaSmall T hab hcd hleft hright

/-- Any finite grid shares the same survival mask; expectation is the sum of quadratic window
budgets. This is the quantity used in deterministic good-sample extraction. -/
theorem setLIntegral_stoppedEmpiricalCollisionGrid_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {m : ℕ} (a b : Fin m → ℝ) {c d : ℝ} (hab : ∀ k, a k ≤ b k) (hcd : c < d)
    (hleft : ∀ k, B ≤ c+a k) (hright : ∀ k, d+b k < B+(T:ℝ)) :
    (∫⁻ sample in {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample},
      ∑ k : Fin m, stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T
        (a k) (b k) c d sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ∑ k : Fin m, ENNReal.ofReal (36*(b k-a k)^2) := by
  rw [lintegral_finsetSum Finset.univ (fun k _ ↦
    measurable_stoppedEmpiricalCollisionFraction hlam0.le (by linarith) hB eta T (a k) (b k) c d)]
  exact Finset.sum_le_sum fun k _ ↦
    setLIntegral_stoppedEmpiricalCollisionFraction_on_survival_le
      hlam0 hlam hn hB heta hetaSmall T (hab k) hcd (hleft k) (hright k)

/-- Markov's inequality on the shared survival event. Countably many grids can be union-bounded
inside this event before its complement is paid for once. -/
theorem measure_stoppedEmpiricalCollisionGrid_on_survival_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {m : ℕ} (a b : Fin m → ℝ) {c d : ℝ} (hab : ∀ k, a k ≤ b k) (hcd : c < d)
    (hleft : ∀ k, B ≤ c+a k) (hright : ∀ k, d+b k < B+(T:ℝ))
    {r : ℝ≥0∞} (hr0 : r ≠ 0) (hrtop : r ≠ ∞) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample ∧
        r ≤ ∑ k : Fin m, stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T
          (a k) (b k) c d sample} ≤
      (∑ k : Fin m, ENNReal.ofReal (36*(b k-a k)^2)) / r := by
  have hf : Measurable (fun sample : FiniteSample n ↦
      ∑ k : Fin m, stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T
        (a k) (b k) c d sample) :=
    Finset.measurable_sum _ fun k _ ↦
      measurable_stoppedEmpiricalCollisionFraction hlam0.le (by linarith) hB eta T (a k) (b k) c d
  have h := meas_ge_le_lintegral_div (μ := (finiteSampleLaw n : Measure (FiniteSample n)).restrict
    {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample})
    hf.aemeasurable hr0 hrtop
  rw [Measure.restrict_apply (measurableSet_le measurable_const hf)] at h
  have heq : {sample : FiniteSample n | StoppedCollisionGood hlam0.le (by linarith) eta B T sample ∧
        r ≤ ∑ k : Fin m, stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T
          (a k) (b k) c d sample} =
      {sample | r ≤ ∑ k : Fin m, stoppedEmpiricalCollisionFraction hlam0.le (by linarith) eta B T
          (a k) (b k) c d sample} ∩
        {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample} := by
    ext sample
    exact and_comm
  rw [heq]
  exact h.trans (ENNReal.div_le_div_right
    (setLIntegral_stoppedEmpiricalCollisionGrid_on_survival_le
      hlam0 hlam hn hB heta hetaSmall T a b hab hcd hleft hright) r)

/-- All resolutions share one survival event. Its complement is paid once, after the countable
union of the masked grid failures. -/
theorem measure_stoppedEmpiricalCollisionGrids_failure_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    (m : ℕ → ℕ) (a b : (j : ℕ) → Fin (m j) → ℝ) {c d : ℝ}
    (hab : ∀ j k, a j k ≤ b j k) (hcd : c < d)
    (hleft : ∀ j k, B ≤ c+a j k) (hright : ∀ j k, d+b j k < B+(T:ℝ))
    (r : ℕ → ℝ≥0∞) (hr0 : ∀ j, r j ≠ 0) (hrtop : ∀ j, r j ≠ ∞) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | ¬ StoppedCollisionGood hlam0.le (by linarith) eta B T sample ∨
        ∃ j, r j ≤ ∑ k : Fin (m j), stoppedEmpiricalCollisionFraction
          hlam0.le (by linarith) eta B T (a j k) (b j k) c d sample} ≤
      (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | ¬ StoppedCollisionGood hlam0.le (by linarith) eta B T sample} +
      ∑' j, (∑ k : Fin (m j), ENNReal.ofReal (36*(b j k-a j k)^2)) / r j := by
  let P : Measure (FiniteSample n) := finiteSampleLaw n
  let G : Set (FiniteSample n) := {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample}
  let E : ℕ → Set (FiniteSample n) := fun j ↦ {sample | sample ∈ G ∧
    r j ≤ ∑ k : Fin (m j), stoppedEmpiricalCollisionFraction
      hlam0.le (by linarith) eta B T (a j k) (b j k) c d sample}
  have hsub : {sample | ¬ StoppedCollisionGood hlam0.le (by linarith) eta B T sample ∨
        ∃ j, r j ≤ ∑ k : Fin (m j), stoppedEmpiricalCollisionFraction
          hlam0.le (by linarith) eta B T (a j k) (b j k) c d sample} ⊆ Gᶜ ∪ ⋃ j, E j := by
    intro sample hs
    by_cases hg : sample ∈ G
    · rcases hs with hn | ⟨j, hj⟩
      · exact False.elim (hn hg)
      · exact Or.inr (mem_iUnion.mpr ⟨j, hg, hj⟩)
    · exact Or.inl hg
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  apply add_le_add_right
  apply (measure_iUnion_le E).trans
  exact ENNReal.tsum_le_tsum fun j ↦
    measure_stoppedEmpiricalCollisionGrid_on_survival_ge_le
      hlam0 hlam hn hB heta hetaSmall T (a j) (b j) (hab j) hcd (hleft j) (hright j)
      (hr0 j) (hrtop j)

end OTSelector.FiniteSample
