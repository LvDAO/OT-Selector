import OTSelector.PointProcess.MatchingSceneCollision

/-!
# Actual shared-event second-moment budgets for good-sample extraction

The stopped aggregate intensity gives a true annealed second moment, uniformly in sample size.
On the single survival event its physical window count is the actual rooted-scene count.
Tonelli and Markov then give masked sample-selection budgets for the empirical second moments.
Closed windows are covered by slightly larger half-open windows, retaining all multiplicities.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Classical BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample
open PointProcess CountingProcess
variable {n : ℕ} {lam : ℝ}

attribute [local irreducible] feedbackState feedbackCurve stoppedContinuationFeedbackGraph

local instance (c d : ℝ) : SFinite (Probability.spatialRootLaw c d) := by
  unfold Probability.spatialRootLaw ProbabilityTheory.cond
  infer_instance

/-- The aggregate stopped count has its true local second moment under the original sample law. -/
theorem integral_sq_safeAggregateA1WindowCount_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ sample : FiniteSample n,
      (safeAggregateA1WindowCount hlam0.le (by linarith) eta B x0 p0 T s t sample)^2
        ∂finiteSampleLaw n) ≤ 6*((t:ℝ)-s)+72*((t:ℝ)-s)^2 := by
  have hlamHalf : lam < 1/2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u sample
  rw [heq] at hmask
  have hbound (u : ℝ≥0) (sample : FiniteSample n) :
      safeAggregateBulkCount hlam0.le hlamHalf B x0 p0 u sample ≤ n+n :=
    add_le_add (finiteEventCountTop_le
      (fun i ↦ safeSourceBulkEventTime hlam0.le hlamHalf B x0 p0 i) u sample)
      (finiteEventCountTop_le
        (fun i ↦ safeTargetBulkEventTime hlam0.le hlamHalf B x0 p0 i) u sample)
  have hh := integral_sq_stoppedCount_increment_le
    (safeAggregateBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeAggregateBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    hbound (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 6) (fun u sample hu ↦ by
      have hr := safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T u sample hu
      linarith [hr.1, hr.2]) hst
  convert hh using 1 <;> first | rfl | ring

/-- Finite population gives the integrability needed to use the real second-moment estimate. -/
theorem integrable_sq_safeAggregateA1WindowCount
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta : ℝ) {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun sample : FiniteSample n ↦
      (safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t sample)^2)
        (finiteSampleLaw n) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  let N := safeAggregateBulkCount (n := n) hlam0 hlamHalf B x0 p0
  have hN := safeAggregateBulkCount_isSimpleCountingProcess (n := n) hlam0 hlamHalf B x0 p0
  have hQ : StronglyAdapted F (stoppedProcess (fun u sample ↦ (N u sample : ℝ)) τ) := by
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous hN.stronglyAdapted
      (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T) hN.rightContinuous
  have hm : StronglyMeasurable
      (safeAggregateA1WindowCount (n := n) hlam0 hlamHalf eta B x0 p0 T s t) :=
    ((hQ t).mono (F.le t)).sub ((hQ s).mono (F.le s))
  apply Integrable.of_bound (hm.pow 2).aestronglyMeasurable (((n+n:ℕ):ℝ)^2)
  filter_upwards with sample
  obtain ⟨q, hq, heq⟩ := safeAggregateA1WindowCount_eq_nat
    hlam0 hlamHalf eta B x0 p0 T hst sample
  simp only [Pi.pow_apply, heq, Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hq) 2

/-- The actual empirical second moment in a physical half-open window. -/
noncomputable def stoppedEmpiricalIocCountSq
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (a b c d : ℝ) (sample : FiniteSample n) : ℝ≥0∞ :=
  ∫⁻ scene, ENNReal.ofReal (MatchingScene.aggregateSpatialIocCount scene a b ^ 2)
    ∂sample.rootedMatchingSceneLaw
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) sample.euclideanOptimizer c d

private theorem measurable_sceneIocCountSq (a b : ℝ) :
    Measurable (fun scene : MatchingScene ↦
      ENNReal.ofReal (MatchingScene.aggregateSpatialIocCount scene a b ^ 2)) :=
  ((MatchingScene.measurable_aggregateSpatialIocCount.comp
    (f := fun scene : MatchingScene ↦ ((a, b), scene))
    ((measurable_const (a := (a, b))).prodMk measurable_id)).pow_const 2).ennreal_ofReal

theorem stoppedEmpiricalIocCountSq_eq_rootIntegral
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (a b c d : ℝ) (sample : FiniteSample n) :
    stoppedEmpiricalIocCountSq hlam0 hlamHalf eta B T a b c d sample =
      ∫⁻ z, ENNReal.ofReal (MatchingScene.aggregateSpatialIocCount
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z) a b ^ 2)
        ∂Probability.spatialRootLaw c d := by
  unfold stoppedEmpiricalIocCountSq rootedMatchingSceneLaw
  rw [lintegral_map (measurable_sceneIocCountSq a b) (sample.measurable_rootedMatchingScene _ _)]
  rfl

theorem measurable_stoppedEmpiricalIocCountSq
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (a b c d : ℝ) :
    Measurable (stoppedEmpiricalIocCountSq (n := n) hlam0 hlamHalf eta B T a b c d) := by
  change Measurable (fun sample : FiniteSample n ↦
    stoppedEmpiricalIocCountSq hlam0 hlamHalf eta B T a b c d sample)
  simp_rw [stoppedEmpiricalIocCountSq_eq_rootIntegral]
  exact ((measurable_aggregateSpatialIocCount_stoppedScene hlam0 hlamHalf hB eta T a b).pow_const 2
    |>.ennreal_ofReal).lintegral_prod_right'

/-- Actual annealed local second moment on the single common survival event. -/
theorem setLIntegral_stoppedEmpiricalIocCountSq_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hleft : B ≤ c+a) (hright : d+b < B+(T:ℝ)) :
    (∫⁻ sample in {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample},
      stoppedEmpiricalIocCountSq hlam0.le (by linarith) eta B T a b c d sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ENNReal.ofReal (6*(b-a)+72*(b-a)^2) := by
  have hlamHalf : lam < 1/2 := by linarith
  let P : Measure (FiniteSample n) := finiteSampleLaw n
  let G : Set (FiniteSample n) := {sample | StoppedCollisionGood hlam0.le hlamHalf eta B T sample}
  let R := Probability.spatialRootLaw c d
  let : IsProbabilityMeasure R := Probability.spatialRootLaw_isProbability hcd
  have hf : Measurable (fun p : FiniteSample n × ℝ ↦ ENNReal.ofReal
      (MatchingScene.aggregateSpatialIocCount
        (p.1.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T p.2) a b ^ 2)) :=
    ((measurable_aggregateSpatialIocCount_stoppedScene hlam0.le hlamHalf hB eta T a b).pow_const 2).ennreal_ofReal
  simp_rw [stoppedEmpiricalIocCountSq_eq_rootIntegral]
  rw [lintegral_lintegral_swap hf.aemeasurable]
  have hroot : ∀ᵐ z ∂R, z ∈ Ioc c d :=
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (6*(b-a)+72*(b-a)^2) ∂R := by
      apply lintegral_mono_ae
      filter_upwards [hroot] with z hz
      let s := (z+a-B).toNNReal
      let t := (z+b-B).toNNReal
      have hs0 : 0 ≤ z+a-B := by linarith [hz.1]
      have ht0 : 0 ≤ z+b-B := by linarith [hz.1]
      have hs : (s : ℝ) = z+a-B := Real.coe_toNNReal _ hs0
      have ht : (t : ℝ) = z+b-B := Real.coe_toNNReal _ ht0
      have hst : s ≤ t := by apply NNReal.coe_le_coe.mp; rw [hs, ht]; linarith
      have htT : t < T := by apply NNReal.coe_lt_coe.mp; rw [ht]; linarith [hz.2]
      have hcount (sample : FiniteSample n) (hg : sample ∈ G) :
          MatchingScene.aggregateSpatialIocCount
            (sample.stoppedRootedEuclideanScene hlam0.le hlamHalf eta B T z) a b =
          safeAggregateA1WindowCount hlam0.le hlamHalf eta B B 0 T s t sample := by
        rw [← stoppedGraphAggregateWindowCount_eq_of_survival hlam0.le hlamHalf
          eta B T hst htT sample hg.1 hg.2]
        rw [stoppedRootedEuclideanScene, rootedEuclideanScene,
          aggregateSpatialIocCount_rootedMatchingScene _ _ _ _ hab]
        simp only [stoppedGraphAggregateWindowCount, hs, ht,
          show B+(z+b-B) = z+b by ring, show B+(z+a-B) = z+a by ring]
      have hG := measurableSet_stoppedCollisionGood (n := n) hlam0.le hlamHalf hB eta T
      calc
        _ = ∫⁻ sample in G, ENNReal.ofReal
            (safeAggregateA1WindowCount hlam0.le hlamHalf eta B B 0 T s t sample ^ 2) ∂P := by
          apply setLIntegral_congr_fun hG
          intro sample hg
          exact congrArg (fun x : ℝ ↦ ENNReal.ofReal (x^2)) (hcount sample hg)
        _ ≤ ∫⁻ sample, ENNReal.ofReal
            (safeAggregateA1WindowCount hlam0.le hlamHalf eta B B 0 T s t sample ^ 2) ∂P :=
          setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ sample,
            safeAggregateA1WindowCount hlam0.le hlamHalf eta B B 0 T s t sample ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal
            (integrable_sq_safeAggregateA1WindowCount hlam0.le hlamHalf eta hB B 0 T hst)
              (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hh := integral_sq_safeAggregateA1WindowCount_le
            (x0 := B) (p0 := 0) hlam0 hlam hn hB heta hetaSmall T hst
          have hdiff : (t:ℝ)-s = b-a := by rw [ht, hs]; ring
          rwa [hdiff] at hh
    _ = _ := by simp

/-- The empirical squared total counting mass of the closed physical window `[-R,R]`. -/
noncomputable def stoppedEmpiricalClosedCountSq
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (R c d : ℝ) (sample : FiniteSample n) : ℝ≥0∞ :=
  ∫⁻ scene, (LocalConfiguration.countingMeasure scene.source
      (Icc (-R) R ×ˢ (univ : Set UnitMark)) +
    LocalConfiguration.countingMeasure scene.target (Icc (-R) R ×ˢ (univ : Set UnitMark)))^2
    ∂sample.rootedMatchingSceneLaw
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) sample.euclideanOptimizer c d

private theorem measurable_sceneClosedCountSq (R : ℝ) :
    Measurable (fun scene : MatchingScene ↦
      (LocalConfiguration.countingMeasure scene.source (Icc (-R) R ×ˢ (univ : Set UnitMark)) +
        LocalConfiguration.countingMeasure scene.target (Icc (-R) R ×ˢ (univ : Set UnitMark)))^2) := by
  have hS : MeasurableSet (Icc (-R) R ×ˢ (univ : Set UnitMark)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hs := (Measure.measurable_coe hS).comp
    (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_source)
  have ht := (Measure.measurable_coe hS).comp
    (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_target)
  exact (hs.add ht).pow_const 2

/-- The actual empirical closed-window moment is AE measurable under the original sample law. -/
theorem aemeasurable_stoppedEmpiricalClosedCountSq
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B : ℝ} (hB : 0 < B)
    (eta : ℝ) (T : ℝ≥0) (R c d : ℝ) :
    AEMeasurable (stoppedEmpiricalClosedCountSq (n := n) hlam0 hlamHalf eta B T R c d)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  have heq (sample : FiniteSample n) :
      stoppedEmpiricalClosedCountSq hlam0 hlamHalf eta B T R c d sample =
      ∫⁻ z, (LocalConfiguration.countingMeasure
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z).source
          (Icc (-R) R ×ˢ (univ : Set UnitMark)) +
        LocalConfiguration.countingMeasure
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z).target
          (Icc (-R) R ×ˢ (univ : Set UnitMark)))^2 ∂Probability.spatialRootLaw c d := by
    unfold stoppedEmpiricalClosedCountSq rootedMatchingSceneLaw
    rw [lintegral_map (measurable_sceneClosedCountSq R) (sample.measurable_rootedMatchingScene _ _)]
    rfl
  have hm := (measurable_sceneClosedCountSq R).comp_aemeasurable
    (aemeasurable_stoppedRootedEuclideanScene (n := n) hlam0 hlamHalf hB eta T
      (Probability.spatialRootLaw c d))
  convert hm.lintegral_prod_right' using 1
  funext sample
  exact heq sample

/-- Closed-window counts retain boundary atoms and are bounded by a slightly larger half-open window. -/
theorem stoppedEmpiricalClosedCountSq_le_Ioc
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T : ℝ≥0) (R c d : ℝ) (sample : FiniteSample n) :
    stoppedEmpiricalClosedCountSq hlam0 hlamHalf eta B T R c d sample ≤
      stoppedEmpiricalIocCountSq hlam0 hlamHalf eta B T (-R-1) (R+1) c d sample := by
  apply lintegral_mono
  intro scene
  have hsub : Icc (-R) R ×ˢ (univ : Set UnitMark) ⊆
      LocalConfiguration.spatialIoc (-R-1) (R+1) := by
    intro p hp
    exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  have hmass (cfg : LocalConfiguration matchingPointBase) :
      LocalConfiguration.countingMeasure cfg (LocalConfiguration.spatialIoc (-R-1) (R+1)) =
        ENNReal.ofReal (LocalConfiguration.spatialCount cfg (-R-1) (R+1) : ℝ) := by
    rw [LocalConfiguration.spatialCount_cast, Measure.real, ENNReal.ofReal_toReal]
    exact (LocalConfiguration.countingMeasure_lt_top_of_isBounded cfg
      (LocalConfiguration.isBounded_spatialIoc _ _)).ne
  have hs : (0 : ℝ) ≤ LocalConfiguration.spatialCount scene.source (-R-1) (R+1) := by
    rw [LocalConfiguration.spatialCount_cast]
    exact measureReal_nonneg
  have ht : (0 : ℝ) ≤ LocalConfiguration.spatialCount scene.target (-R-1) (R+1) := by
    rw [LocalConfiguration.spatialCount_cast]
    exact measureReal_nonneg
  calc
    _ ≤ (LocalConfiguration.countingMeasure scene.source (LocalConfiguration.spatialIoc (-R-1) (R+1)) +
        LocalConfiguration.countingMeasure scene.target (LocalConfiguration.spatialIoc (-R-1) (R+1)))^2 :=
      pow_le_pow_left' (add_le_add (measure_mono hsub) (measure_mono hsub)) 2
    _ = _ := by
      rw [hmass, hmass, ← ENNReal.ofReal_add hs ht, ← ENNReal.ofReal_pow (add_nonneg hs ht)]
      rfl

/-- An explicit sample-size-independent closed-window second-moment constant. -/
def selectionClosedCountBound (R : ℝ) : ℝ := 6*(2*R+2)+72*(2*R+2)^2

theorem selectionClosedCountBound_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ selectionClosedCountBound R := by unfold selectionClosedCountBound; positivity

/-- The actual closed-window empirical square has a shared-event annealed bound. -/
theorem setLIntegral_stoppedEmpiricalClosedCountSq_on_survival_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {R c d : ℝ} (hR : 0 ≤ R) (hcd : c < d)
    (hleft : B ≤ c-R-1) (hright : d+R+1 < B+(T:ℝ)) :
    (∫⁻ sample in {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample},
      stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ENNReal.ofReal (selectionClosedCountBound R) := by
  apply (lintegral_mono (fun sample ↦ stoppedEmpiricalClosedCountSq_le_Ioc
    hlam0.le (by linarith) eta B T R c d sample)).trans
  convert setLIntegral_stoppedEmpiricalIocCountSq_on_survival_le
    hlam0 hlam hn hB heta hetaSmall T (by linarith : -R-1 ≤ R+1) hcd
    (by linarith : B ≤ c+(-R-1)) (by linarith : d+(R+1) < B+(T:ℝ)) using 1
  congr 1
  unfold selectionClosedCountBound
  ring

/-- Markov's inequality controls bad samples inside any common good set contained in survival. -/
theorem measure_stoppedEmpiricalClosedCountSq_on_mask_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {R c d : ℝ} (hR : 0 ≤ R) (hcd : c < d)
    (hleft : B ≤ c-R-1) (hright : d+R+1 < B+(T:ℝ))
    (G : Set (FiniteSample n))
    (hG : G ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample})
    {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ∞) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      (G ∩ {sample | K ≤ stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample}) ≤
        ENNReal.ofReal (selectionClosedCountBound R) / K := by
  let S : Set (FiniteSample n) := {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample}
  have hf := measurable_stoppedEmpiricalIocCountSq (n := n) hlam0.le (by linarith) hB eta T
    (-R-1) (R+1) c d
  have hmark := meas_ge_le_lintegral_div
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)).restrict S) hf.aemeasurable hK0 hKtop
  rw [Measure.restrict_apply (measurableSet_le measurable_const hf)] at hmark
  apply (measure_mono (show G ∩ {sample | K ≤ stoppedEmpiricalClosedCountSq
      hlam0.le (by linarith) eta B T R c d sample} ⊆
      {sample | K ≤ stoppedEmpiricalIocCountSq hlam0.le (by linarith) eta B T (-R-1) (R+1) c d sample} ∩ S from ?_)).trans
  · apply hmark.trans
    apply ENNReal.div_le_div_right
    convert setLIntegral_stoppedEmpiricalIocCountSq_on_survival_le
      hlam0 hlam hn hB heta hetaSmall T (by linarith : -R-1 ≤ R+1) hcd
      (by linarith : B ≤ c+(-R-1)) (by linarith : d+(R+1) < B+(T:ℝ)) using 1
    congr 1
    unfold selectionClosedCountBound
    ring
  · intro sample hs
    exact ⟨hs.2.trans (stoppedEmpiricalClosedCountSq_le_Ioc
      hlam0.le (by linarith) eta B T R c d sample), hG hs.1⟩

/-- A real-valued form of the same shared-event Markov budget. -/
theorem measureReal_stoppedEmpiricalClosedCountSq_on_mask_ge_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {R c d : ℝ} (hR : 0 ≤ R) (hcd : c < d)
    (hleft : B ≤ c-R-1) (hright : d+R+1 < B+(T:ℝ))
    (G : Set (FiniteSample n))
    (hG : G ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample})
    {K : ℝ} (hK : 0 < K) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G ∩ {sample | ENNReal.ofReal K ≤
        stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample}) ≤
      selectionClosedCountBound R / K := by
  have hb := measure_stoppedEmpiricalClosedCountSq_on_mask_ge_le
    hlam0 hlam hn hB heta hetaSmall T hR hcd hleft hright G hG
    (ENNReal.ofReal_ne_zero_iff.mpr hK) ENNReal.ofReal_ne_top
  have hfin : ENNReal.ofReal (selectionClosedCountBound R) / ENNReal.ofReal K ≠ ∞ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hK)
  have hh := ENNReal.toReal_mono hfin hb
  simpa only [Measure.real, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (selectionClosedCountBound_nonneg hR),
    ENNReal.toReal_ofReal hK.le] using hh

/-- Explicit threshold allocating any positive probability budget to one closed-window moment. -/
noncomputable def selectionClosedCountThreshold (R weight : ℝ) : ℝ :=
  (selectionClosedCountBound R + 1) / weight

theorem selectionClosedCountThreshold_pos {R weight : ℝ} (hR : 0 ≤ R) (hw : 0 < weight) :
    0 < selectionClosedCountThreshold R weight :=
  div_pos (by linarith [selectionClosedCountBound_nonneg hR]) hw

/-- A single actual good-sample moment constraint spends at most its assigned budget. -/
theorem measureReal_stoppedEmpiricalClosedCountSq_constraint_failure_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    {eta B : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    {R c d : ℝ} (hR : 0 ≤ R) (hcd : c < d)
    (hleft : B ≤ c-R-1) (hright : d+R+1 < B+(T:ℝ))
    (G : Set (FiniteSample n))
    (hG : G ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) eta B T sample})
    {weight : ℝ} (hw : 0 < weight) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G ∩ {sample | stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample ≤
        ENNReal.ofReal (selectionClosedCountThreshold R weight)}ᶜ) ≤ weight := by
  have hK := selectionClosedCountThreshold_pos hR hw
  apply (measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (show G ∩ {sample | stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample ≤
        ENNReal.ofReal (selectionClosedCountThreshold R weight)}ᶜ ⊆
      G ∩ {sample | ENNReal.ofReal (selectionClosedCountThreshold R weight) ≤
        stoppedEmpiricalClosedCountSq hlam0.le (by linarith) eta B T R c d sample} from
      fun sample hx ↦ ⟨hx.1, (not_le.mp (show ¬ stoppedEmpiricalClosedCountSq
        hlam0.le (by linarith) eta B T R c d sample ≤
        ENNReal.ofReal (selectionClosedCountThreshold R weight) from hx.2)).le⟩)).trans
  apply (measureReal_stoppedEmpiricalClosedCountSq_on_mask_ge_le
    hlam0 hlam hn hB heta hetaSmall T hR hcd hleft hright G hG hK).trans
  apply (div_le_iff₀ hK).mpr
  rw [selectionClosedCountThreshold, mul_div_cancel₀ _ hw.ne']
  linarith

/-- Window constraints are eventual separately at every fixed radius, as required by the
finite-prefix sample extraction. No row is required to fit all radii at once. -/
theorem eventually_stoppedEmpiricalClosedCountSq_constraint_failure_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8)
    (eta B c d : ℕ → ℝ) (T : ℕ → ℝ≥0) (G : ∀ n, Set (FiniteSample n))
    (hparams : ∀ᶠ n in atTop, 0 < n ∧ 0 < B n ∧ 0 ≤ eta n ∧
      eta n*(2+lam) ≤ lam ∧ c n < d n ∧
      G n ⊆ {sample | StoppedCollisionGood hlam0.le (by linarith) (eta n) (B n) (T n) sample})
    (hfit : ∀ R : ℝ, 0 ≤ R → ∀ᶠ n in atTop,
      B n ≤ c n-R-1 ∧ d n+R+1 < B n+(T n:ℝ))
    (R : ℝ) (hR : 0 ≤ R) (weight : ℝ) (hw : 0 < weight) :
    ∀ᶠ n in atTop, (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G n ∩ {sample | stoppedEmpiricalClosedCountSq hlam0.le (by linarith)
        (eta n) (B n) (T n) R (c n) (d n) sample ≤
        ENNReal.ofReal (selectionClosedCountThreshold R weight)}ᶜ) ≤ weight := by
  filter_upwards [hparams, hfit R hR] with n hn hwin
  exact measureReal_stoppedEmpiricalClosedCountSq_constraint_failure_le
    hlam0 hlam hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 (T n) hR hn.2.2.2.2.1
    hwin.1 hwin.2 (G n) hn.2.2.2.2.2 hw

end OTSelector.FiniteSample
