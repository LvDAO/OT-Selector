import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Binomial
import OTSelector.Basic.FiniteSampleLaw
import OTSelector.Feedback.BoundaryEnergy
import OTSelector.Feedback.CrossingCounts
import OTSelector.Feedback.FeedbackA1StoppedDrift
import OTSelector.Feedback.InitialCurrent
import OTSelector.Feedback.RankGapTail
import OTSelector.Feedback.Comparison
import OTSelector.Gauge.FeedbackLocalization

/-!
# Boundary estimates and increasing-comparison matching

This file closes the deterministic and finite-product-law inputs that do not depend on the
right-tail regularity-survival theorem.  In particular, the left-boundary counts below have their
actual binomial laws under `finiteSampleLaw`; no law or moment conclusion is supplied as a free
hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace OTSelector

/-! ## Uniform positive feedback rates -/

private theorem crossing_eta_le_one_sixteenth'
    {lam eta rMinus rPlus : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    eta ≤ 1 / 16 := by
  have htwo : 2 * eta ≤ eta * (2 + lam) := by
    have h := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) ≤ 2 + lam by linarith) hreg.eta_nonneg
    nlinarith
  nlinarith [hreg.eta_small]

/-- In the regularity window the source crossing rate is uniformly at least `1/2`. -/
theorem one_half_le_sourceTotalRate
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    1 / 2 ≤ sourceTotalRate rMinus (feedbackSlope lam k) := by
  have heta := crossing_eta_le_one_sixteenth' hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hr : (3 : ℝ) / 4 ≤ rMinus := by
    nlinarith [hreg.source_lower]
  have hf : (3 : ℝ) / 4 ≤ 1 - feedbackSlope lam k / 2 := by
    nlinarith [abs_le.mp hw]
  have hprod : ((3 : ℝ) / 4) * (3 / 4) ≤
      rMinus * (1 - feedbackSlope lam k / 2) :=
    mul_le_mul hr hf (by norm_num) (by linarith)
  simpa only [sourceTotalRate] using (show
    (1 : ℝ) / 2 ≤ rMinus * (1 - feedbackSlope lam k / 2) by nlinarith)

/-- In the regularity window the target crossing rate is uniformly at least `1/2`. -/
theorem one_half_le_targetTotalRate
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    1 / 2 ≤ targetTotalRate rPlus (feedbackSlope lam k) := by
  have heta := crossing_eta_le_one_sixteenth' hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hr : (3 : ℝ) / 4 ≤ rPlus := by
    nlinarith [hreg.target_lower]
  have hf : (3 : ℝ) / 4 ≤ 1 + 3 * feedbackSlope lam k / 2 := by
    nlinarith [abs_le.mp hw]
  have hprod : ((3 : ℝ) / 4) * (3 / 4) ≤
      rPlus * (1 + 3 * feedbackSlope lam k / 2) :=
    mul_le_mul hr hf (by norm_num) (by linarith)
  simpa only [targetTotalRate] using (show
    (1 : ℝ) / 2 ≤ rPlus * (1 + 3 * feedbackSlope lam k / 2) by nlinarith)

namespace FiniteSample

variable {n : ℕ}

/-- Before the combined A1 stop, the actual safe source rate lies in `[1/2,3]`. -/
theorem safeSourceBulkRate_mem_Icc_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T sample) :
    safeSourceBulkRate hlam0.le (by linarith) B x0 p0 t sample ∈
      Set.Icc ((1 : ℝ) / 2) 3 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hbulkExit := lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    (n := n) hlam0.le hlamHalf eta B x0 p0 T t sample ht
  have hreg := crossingRegularity_of_lt_safeFeedbackA1Stop
    (n := n) hlam0.le hlamHalf hB heta0 hetaSmall T t sample ht
  rw [safeSourceBulkRate_eq_feedbackSourceIntensity_of_lt_exit
    (n := n) hlam0.le hlamHalf hB t sample hbulkExit]
  simp only [feedbackSourceIntensity]
  exact ⟨one_half_le_sourceTotalRate hlam0 hlam hreg,
    (sourceTotalRate_bounds hlam0 hlam hreg).2⟩

/-- Before the combined A1 stop, the actual safe target rate lies in `[1/2,3]`. -/
theorem safeTargetBulkRate_mem_Icc_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T sample) :
    safeTargetBulkRate hlam0.le (by linarith) B x0 p0 t sample ∈
      Set.Icc ((1 : ℝ) / 2) 3 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hbulkExit := lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    (n := n) hlam0.le hlamHalf eta B x0 p0 T t sample ht
  have hreg := crossingRegularity_of_lt_safeFeedbackA1Stop
    (n := n) hlam0.le hlamHalf hB heta0 hetaSmall T t sample ht
  rw [safeTargetBulkRate_eq_feedbackTargetIntensity_of_lt_exit
    (n := n) hlam0.le hlamHalf hB t sample hbulkExit]
  simp only [feedbackTargetIntensity]
  exact ⟨one_half_le_targetTotalRate hlam0 hlam hreg,
    (targetTotalRate_bounds hlam0 hlam hreg).2⟩

/-! ## Actual left-boundary binomial counts -/

/-- Number of source heights below a unit-interval threshold. -/
noncomputable def leftSourceCountAt (p : UnitMark) (sample : FiniteSample n) : ℕ :=
  Set.ncard {i : Fin n | sample.sourceHeight i ≤ p}

/-- Number of target heights below a unit-interval threshold. -/
noncomputable def leftTargetCountAt (p : UnitMark) (sample : FiniteSample n) : ℕ :=
  Set.ncard {i : Fin n | sample.targetHeight i ≤ p}

/-- The actual zero-shear left current at a unit-interval threshold. -/
noncomputable def leftBoundaryCurrentAt (p : UnitMark) (sample : FiniteSample n) : ℝ :=
  (sample.leftSourceCountAt p : ℝ) - sample.leftTargetCountAt p

theorem measurable_leftSourceCountAt (p : UnitMark) :
    Measurable (leftSourceCountAt p : FiniteSample n → ℕ) := by
  unfold leftSourceCountAt
  apply measurable_ncard.comp
  rw [measurable_set_iff]
  intro i
  exact measurableSet_setOfPred.mp
    (measurableSet_le (FiniteSample.measurable_sourceHeight i) measurable_const)

theorem measurable_leftTargetCountAt (p : UnitMark) :
    Measurable (leftTargetCountAt p : FiniteSample n → ℕ) := by
  unfold leftTargetCountAt
  apply measurable_ncard.comp
  rw [measurable_set_iff]
  intro i
  exact measurableSet_setOfPred.mp
    (measurableSet_le (FiniteSample.measurable_targetHeight i) measurable_const)

theorem measurable_leftBoundaryCurrentAt (p : UnitMark) :
    Measurable (leftBoundaryCurrentAt p : FiniteSample n → ℝ) := by
  exact (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_leftSourceCountAt p) |>.sub
    ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_leftTargetCountAt p))

private theorem map_unitUniform_le (p : UnitMark) :
    Measure.map (fun u : UnitMark ↦ u ≤ p) (unitUniform : Measure UnitMark) =
      Ber(True, False, p) := by
  apply Measure.ext_of_singleton
  intro b
  classical
  by_cases hb : b
  · have hbeq : b = True := propext (iff_true_intro hb)
    subst b
    have hm : Measurable (fun u : UnitMark ↦ u ≤ p) :=
      measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const)
    rw [Measure.map_apply hm (MeasurableSet.singleton True)]
    rw [show (fun u : UnitMark ↦ u ≤ p) ⁻¹' {True} = Set.Iic p by
      ext u
      simp]
    change volume (Set.Iic p) = Ber(True, False, p) {True}
    rw [unitInterval.volume_Iic]
    simp [ProbabilityTheory.bernoulliMeasure_def]
    rw [ENNReal.ofReal_eq_coe_nnreal p.2.1]
    rfl
  · have hbeq : b = False := propext (iff_false_intro hb)
    subst b
    have hm : Measurable (fun u : UnitMark ↦ u ≤ p) :=
      measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const)
    rw [Measure.map_apply hm (MeasurableSet.singleton False)]
    rw [show (fun u : UnitMark ↦ u ≤ p) ⁻¹' {False} = Set.Ioi p by
      ext u
      simp]
    change volume (Set.Ioi p) = Ber(True, False, p) {False}
    rw [unitInterval.volume_Ioi]
    simp [ProbabilityTheory.bernoulliMeasure_def]
    rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr p.2.2)]
    rfl

private theorem map_ncard_setBernoulli_univ_fin (p : UnitMark) :
    (setBer((Set.univ : Set (Fin n)), p)).map Set.ncard = Bin(n, p) := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [map_ncard_setBernoulli_real_singleton (Set.finite_univ : (Set.univ : Set (Fin n)).Finite)]
  simp [ProbabilityTheory.binomial_real_singleton]

private theorem hasLaw_thresholdSet_source (p : UnitMark) :
    HasLaw (fun sample : FiniteSample n ↦
      {i : Fin n | sample.sourceHeight i ≤ p})
      setBer((Set.univ : Set (Fin n)), p) (finiteSampleLaw n) := by
  let X : Fin n → FiniteSample n → Prop :=
    fun i sample ↦ sample.sourceHeight i ≤ p
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    exact measurableSet_setOfPred.mp
      (measurableSet_le (FiniteSample.measurable_sourceHeight i) measurable_const)
  have hXindep : iIndepFun X (finiteSampleLaw n : Measure (FiniteSample n)) := by
    exact (finiteSampleLaw_sourceHeight_iIndep n).comp
      (fun _ u ↦ u ≤ p) (fun _ ↦ by fun_prop)
  have hXlaw : ∀ i, HasLaw (X i) Ber(True, False, p) (finiteSampleLaw n) := by
    intro i
    have hle : Measurable (fun u : UnitMark ↦ u ≤ p) :=
      measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const)
    refine ⟨(hXmeas i).aemeasurable, ?_⟩
    have hheight : Measure.map
        (fun sample : FiniteSample n ↦ sample.sourceHeight i)
        (finiteSampleLaw n : Measure (FiniteSample n)) = unitUniform := by
      simpa only [ProbabilityMeasure.toMeasure_map] using congrArg
        ProbabilityMeasure.toMeasure (finiteSampleLaw_map_sourceHeight n i)
    rw [show X i = (fun u : UnitMark ↦ u ≤ p) ∘
        (fun sample : FiniteSample n ↦ sample.sourceHeight i) by rfl,
      ← Measure.map_map hle (FiniteSample.measurable_sourceHeight i),
      hheight, map_unitUniform_le]
  have hpi := hXindep.hasLaw_pi hXlaw
  have hset : HasLaw (fun sample : FiniteSample n ↦ {i | X i sample})
      setBer((Set.univ : Set (Fin n)), p) (finiteSampleLaw n) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun sample : FiniteSample n ↦ {i | X i sample}) =
        (fun q : Fin n → Prop ↦ {i | q i}) ∘ (fun sample i ↦ X i sample) by rfl,
      ← Measure.map_map measurable_setOfPred
        (measurable_pi_lambda _ hXmeas), hpi.map_eq,
      ProbabilityTheory.setBernoulli_eq_map, Measure.infinitePi_eq_pi]
    congr 2
  simpa [X] using hset

private theorem hasLaw_thresholdSet_target (p : UnitMark) :
    HasLaw (fun sample : FiniteSample n ↦
      {i : Fin n | sample.targetHeight i ≤ p})
      setBer((Set.univ : Set (Fin n)), p) (finiteSampleLaw n) := by
  let X : Fin n → FiniteSample n → Prop :=
    fun i sample ↦ sample.targetHeight i ≤ p
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    exact measurableSet_setOfPred.mp
      (measurableSet_le (FiniteSample.measurable_targetHeight i) measurable_const)
  have hXindep : iIndepFun X (finiteSampleLaw n : Measure (FiniteSample n)) := by
    exact (finiteSampleLaw_targetHeight_iIndep n).comp
      (fun _ u ↦ u ≤ p) (fun _ ↦ by fun_prop)
  have hXlaw : ∀ i, HasLaw (X i) Ber(True, False, p) (finiteSampleLaw n) := by
    intro i
    have hle : Measurable (fun u : UnitMark ↦ u ≤ p) :=
      measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const)
    refine ⟨(hXmeas i).aemeasurable, ?_⟩
    have hheight : Measure.map
        (fun sample : FiniteSample n ↦ sample.targetHeight i)
        (finiteSampleLaw n : Measure (FiniteSample n)) = unitUniform := by
      simpa only [ProbabilityMeasure.toMeasure_map] using congrArg
        ProbabilityMeasure.toMeasure (finiteSampleLaw_map_targetHeight n i)
    rw [show X i = (fun u : UnitMark ↦ u ≤ p) ∘
        (fun sample : FiniteSample n ↦ sample.targetHeight i) by rfl,
      ← Measure.map_map hle (FiniteSample.measurable_targetHeight i),
      hheight, map_unitUniform_le]
  have hpi := hXindep.hasLaw_pi hXlaw
  have hset : HasLaw (fun sample : FiniteSample n ↦ {i | X i sample})
      setBer((Set.univ : Set (Fin n)), p) (finiteSampleLaw n) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun sample : FiniteSample n ↦ {i | X i sample}) =
        (fun q : Fin n → Prop ↦ {i | q i}) ∘ (fun sample i ↦ X i sample) by rfl,
      ← Measure.map_map measurable_setOfPred
        (measurable_pi_lambda _ hXmeas), hpi.map_eq,
      ProbabilityTheory.setBernoulli_eq_map, Measure.infinitePi_eq_pi]
    congr 2
  simpa [X] using hset

/-- The actual source count on the left constant segment has the mathlib binomial law. -/
theorem leftSourceCountAt_hasLaw_binomial (p : UnitMark) :
    HasLaw (leftSourceCountAt p : FiniteSample n → ℕ) Bin(n, p)
      (finiteSampleLaw n) := by
  have hset := hasLaw_thresholdSet_source (n := n) p
  have hncard : HasLaw (fun s : Set (Fin n) ↦ s.ncard)
      ((setBer((Set.univ : Set (Fin n)), p)).map Set.ncard)
      setBer((Set.univ : Set (Fin n)), p) :=
    ⟨measurable_ncard.aemeasurable, rfl⟩
  have h := hncard.comp hset
  rw [map_ncard_setBernoulli_univ_fin] at h
  change HasLaw ((fun s : Set (Fin n) ↦ s.ncard) ∘
      fun sample : FiniteSample n ↦
        {i : Fin n | sample.sourceHeight i ≤ p}) Bin(n, p) (finiteSampleLaw n)
  exact h

/-- The actual target count on the left constant segment has the mathlib binomial law. -/
theorem leftTargetCountAt_hasLaw_binomial (p : UnitMark) :
    HasLaw (leftTargetCountAt p : FiniteSample n → ℕ) Bin(n, p)
      (finiteSampleLaw n) := by
  have hset := hasLaw_thresholdSet_target (n := n) p
  have hncard : HasLaw (fun s : Set (Fin n) ↦ s.ncard)
      ((setBer((Set.univ : Set (Fin n)), p)).map Set.ncard)
      setBer((Set.univ : Set (Fin n)), p) :=
    ⟨measurable_ncard.aemeasurable, rfl⟩
  have h := hncard.comp hset
  rw [map_ncard_setBernoulli_univ_fin] at h
  change HasLaw ((fun s : Set (Fin n) ↦ s.ncard) ∘
      fun sample : FiniteSample n ↦
        {i : Fin n | sample.targetHeight i ≤ p}) Bin(n, p) (finiteSampleLaw n)
  exact h

private theorem leftSourceCountAt_indep_leftTargetCountAt (p : UnitMark) :
    IndepFun (leftSourceCountAt p : FiniteSample n → ℕ)
      (leftTargetCountAt p : FiniteSample n → ℕ) (finiteSampleLaw n) := by
  have harrays := finiteSampleLaw_arrays_iIndep n
  have h12 := harrays.indepFun (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have hm : Measurable (fun a : SampleArray n ↦ Set.ncard {i : Fin n | a i ≤ p}) := by
    apply measurable_ncard.comp
    rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_pi_apply i) measurable_const)
  have hcomp := h12.comp hm hm
  change IndepFun
    (fun sample : FiniteSample n ↦ Set.ncard {i : Fin n | sample.sourceHeight i ≤ p})
    (fun sample : FiniteSample n ↦ Set.ncard {i : Fin n | sample.targetHeight i ≤ p})
    (finiteSampleLaw n)
  simpa [FiniteSample.toFourArrays, Function.comp_def] using hcomp

/-- The two actual left counts have the product of their binomial laws. -/
theorem leftBoundaryCounts_hasLaw_binomial_prod (p : UnitMark) :
    HasLaw (fun sample : FiniteSample n ↦
      (sample.leftSourceCountAt p, sample.leftTargetCountAt p))
      (Bin(n, p).prod Bin(n, p)) (finiteSampleLaw n) := by
  exact (leftSourceCountAt_indep_leftTargetCountAt (n := n) p).hasLaw_prod
    (leftSourceCountAt_hasLaw_binomial (n := n) p)
    (leftTargetCountAt_hasLaw_binomial (n := n) p)

/-- Exact second moment of the actual zero-shear left current. -/
theorem integral_leftBoundaryCurrentAt_sq (p : UnitMark) :
    ∫ sample : FiniteSample n, sample.leftBoundaryCurrentAt p ^ 2 ∂(finiteSampleLaw n) =
      2 * (n : ℝ) * p * (1 - p) := by
  have hlaw := leftBoundaryCounts_hasLaw_binomial_prod (n := n) p
  have hcast : HasLaw (fun z : ℕ × ℕ ↦ ((z.1 : ℝ), (z.2 : ℝ)))
      (Bin(ℝ, n, p).prod Bin(ℝ, n, p)) (Bin(n, p).prod Bin(n, p)) := by
    refine ⟨by fun_prop, ?_⟩
    exact (Measure.map_prod_map (Bin(n, p)) (Bin(n, p))
      ((MeasurableEmbedding.natCast (α := ℝ)).measurable)
      ((MeasurableEmbedding.natCast (α := ℝ)).measurable)).symm
  have hreal := hcast.comp hlaw
  have hreal' : HasLaw (fun sample : FiniteSample n ↦
      ((sample.leftSourceCountAt p : ℝ), (sample.leftTargetCountAt p : ℝ)))
      (Bin(ℝ, n, p).prod Bin(ℝ, n, p)) (finiteSampleLaw n) := by
    change HasLaw ((fun z : ℕ × ℕ ↦ ((z.1 : ℝ), (z.2 : ℝ))) ∘
      fun sample : FiniteSample n ↦
        (sample.leftSourceCountAt p, sample.leftTargetCountAt p))
      (Bin(ℝ, n, p).prod Bin(ℝ, n, p)) (finiteSampleLaw n)
    exact hreal
  -- The product-binomial moment theorem is already proved in `InitialCurrent`.
  calc
    ∫ sample : FiniteSample n, sample.leftBoundaryCurrentAt p ^ 2 ∂(finiteSampleLaw n) =
        ∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2
          ∂(Bin(ℝ, n, p).prod Bin(ℝ, n, p)) := by
      simpa [leftBoundaryCurrentAt, Function.comp_def] using
        hreal'.integral_comp (f := fun z : ℝ × ℝ ↦ (z.1 - z.2) ^ 2) (by fun_prop)
    _ = 2 * (n : ℝ) * p * (1 - p) :=
      Feedback.binomial_difference_second_moment n p

/-! ### Left-boundary energy in rank coordinates -/

/-- Clip the rank coordinate `x` to a unit-height threshold after dividing by `n`. -/
noncomputable def leftBoundaryRankThreshold (n : ℕ) (x : ℝ) : UnitMark :=
  Set.projIcc 0 1 zero_le_one (x / (n : ℝ))

theorem continuous_leftBoundaryRankThreshold (n : ℕ) :
    Continuous (leftBoundaryRankThreshold n) := by
  unfold leftBoundaryRankThreshold
  exact Continuous.subtype_mk (by fun_prop) _

theorem leftBoundaryRankThreshold_coe_of_mem
    (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    (leftBoundaryRankThreshold n x : ℝ) = x / n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxmem : x / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    unitInterval.div_mem hx0 hnreal.le hxn
  unfold leftBoundaryRankThreshold
  rw [Set.projIcc_of_mem zero_le_one hxmem]

/-- The actual zero-shear left current at the rank coordinate `x`. -/
noncomputable def leftBoundaryCurrent (n : ℕ) (x : ℝ) (sample : FiniteSample n) : ℝ :=
  sample.leftBoundaryCurrentAt (leftBoundaryRankThreshold n x)

theorem measurable_leftBoundaryCurrent :
    Measurable (fun p : ℝ × FiniteSample n ↦ leftBoundaryCurrent n p.1 p.2) := by
  have hthreshold : Measurable (fun p : ℝ × FiniteSample n ↦
      leftBoundaryRankThreshold n p.1) :=
    (continuous_leftBoundaryRankThreshold n).measurable.comp measurable_fst
  have hsource : Measurable (fun p : ℝ × FiniteSample n ↦
      leftSourceCountAt (leftBoundaryRankThreshold n p.1) p.2) := by
    unfold leftSourceCountAt
    apply measurable_ncard.comp
    rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp (measurableSet_le
      ((FiniteSample.measurable_sourceHeight i).comp measurable_snd) hthreshold)
  have htarget : Measurable (fun p : ℝ × FiniteSample n ↦
      leftTargetCountAt (leftBoundaryRankThreshold n p.1) p.2) := by
    unfold leftTargetCountAt
    apply measurable_ncard.comp
    rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp (measurableSet_le
      ((FiniteSample.measurable_targetHeight i).comp measurable_snd) hthreshold)
  exact ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp hsource).sub
    ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp htarget)

private theorem leftSourceCountAt_le (p : UnitMark) (sample : FiniteSample n) :
    sample.leftSourceCountAt p ≤ n := by
  unfold leftSourceCountAt
  simpa using Set.ncard_le_card {i : Fin n | sample.sourceHeight i ≤ p}

private theorem leftTargetCountAt_le (p : UnitMark) (sample : FiniteSample n) :
    sample.leftTargetCountAt p ≤ n := by
  unfold leftTargetCountAt
  simpa using Set.ncard_le_card {i : Fin n | sample.targetHeight i ≤ p}

theorem integrable_leftBoundaryCurrent_sq (x : ℝ) :
    Integrable (fun sample : FiniteSample n ↦ leftBoundaryCurrent n x sample ^ 2)
      (finiteSampleLaw n) := by
  have hmeas : Measurable (fun sample : FiniteSample n ↦
      leftBoundaryCurrent n x sample) := by
    simpa [Function.comp_def] using measurable_leftBoundaryCurrent (n := n) |>.comp
      (measurable_const.prodMk measurable_id)
  refine Integrable.of_bound (hmeas.pow measurable_const).aestronglyMeasurable
    ((n : ℝ) ^ 2) (Filter.Eventually.of_forall fun sample ↦ ?_)
  let p := leftBoundaryRankThreshold n x
  have hs := leftSourceCountAt_le (n := n) p sample
  have ht := leftTargetCountAt_le (n := n) p sample
  have hs' : (sample.leftSourceCountAt p : ℝ) ≤ n := by exact_mod_cast hs
  have ht' : (sample.leftTargetCountAt p : ℝ) ≤ n := by exact_mod_cast ht
  have hs0 : 0 ≤ (sample.leftSourceCountAt p : ℝ) := by positivity
  have ht0 : 0 ≤ (sample.leftTargetCountAt p : ℝ) := by positivity
  have habs : |(sample.leftSourceCountAt p : ℝ) - sample.leftTargetCountAt p| ≤
      (n : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have habs' : |(sample.leftSourceCountAt p : ℝ) - sample.leftTargetCountAt p| ≤
      |(n : ℝ)| := by simpa using habs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [leftBoundaryCurrent, leftBoundaryCurrentAt, p] using sq_le_sq.mpr habs'

/-- The pointwise left-boundary second moment is bounded by twice the rank coordinate. -/
theorem integral_leftBoundaryCurrent_sq_le
    (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    ∫ sample : FiniteSample n, leftBoundaryCurrent n x sample ^ 2 ∂(finiteSampleLaw n) ≤
      2 * x := by
  let p := leftBoundaryRankThreshold n x
  have hpcoe : (p : ℝ) = x / n :=
    leftBoundaryRankThreshold_coe_of_mem (n := n) hn hx0 hxn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnp : (n : ℝ) * (p : ℝ) = x := by
    rw [hpcoe]
    field_simp
  rw [show leftBoundaryCurrent n x = leftBoundaryCurrentAt p by rfl,
    integral_leftBoundaryCurrentAt_sq]
  nlinarith [p.2.1, p.2.2]

/-- The actual left-boundary binomial current satisfies the quadratic area estimate from
`BoundaryEnergy`; no moment estimate is assumed by the theorem. -/
theorem expected_leftBoundaryArea_le
    (hn : 0 < n) {B : ℝ} (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    ∫ sample : FiniteSample n,
        ∫ x : ℝ in Set.Ioc 0 B, leftBoundaryCurrent n x sample ^ 2 ∂volume
      ∂(finiteSampleLaw n) ≤ B ^ 2 := by
  have harea := expected_area_le_of_linear_bound
    (finiteSampleLaw n : Measure (FiniteSample n)) hB0 (by norm_num : (0 : ℝ) ≤ 2)
    (leftBoundaryCurrent n) measurable_leftBoundaryCurrent
    (fun x _ ↦ integrable_leftBoundaryCurrent_sq (n := n) x)
    (fun x hx ↦ integral_leftBoundaryCurrent_sq_le (n := n) hn hx.1.le
      (hx.2.trans hBn))
  nlinarith [harea]

/-! ## Increasing intersection matching -/

/-- Increasing matching preserves the target sublevel count at every cut. -/
theorem increasingAssignment_target_count (source target : Fin n → ℝ) (x : ℝ) :
    (∑ i, if target (increasingAssignment source target i) ≤ x then (1 : ℤ) else 0) =
      ∑ j, if target j ≤ x then (1 : ℤ) else 0 :=
  target_count_comp_perm target (increasingAssignment source target) x

/-- The crossing current of the increasing matching is exactly the two-list rank discrepancy. -/
theorem increasingAssignment_crossingCurrent_eq_count_sub
    (source target : Fin n → ℝ) (x : ℝ) :
    assignmentCrossingCurrent source target (increasingAssignment source target) x =
      ((Finset.univ.filter fun i ↦ source i ≤ x).card : ℤ) -
        ((Finset.univ.filter fun j ↦ target j ≤ x).card : ℤ) := by
  rw [assignmentCrossingCurrent_eq_rankDiscrepancy]
  unfold assignmentRankDiscrepancy
  rw [increasingAssignment_target_count]
  simp only [Finset.sum_boole]

/-- The I3 intersection assignment is definitionally the same assignment used by the concrete
FGL2 comparison theorem in `FeedbackLocalization`. -/
noncomputable def increasingIntersectionAssignment {lam : ℝ}
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) : Assignment n :=
  sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0

@[simp] theorem increasingIntersectionAssignment_eq_feedbackComparisonAssignment
    {lam : ℝ} (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    sample.increasingIntersectionAssignment hlam0 hlamHalf x0 p0 =
      sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 := rfl

/-- For the actual graph intersections, increasing-matching current equals the intersection-count
difference, hence the feedback rank discrepancy by `intersectionCurrent_eq_feedbackRankDiscrepancy`.
-/
theorem increasingIntersectionCrossingCurrent_eq_count_sub {lam : ℝ}
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 x : ℝ) :
    let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
    assignmentCrossingCurrent (sample.sourceIntersection graph)
        (sample.targetIntersection graph)
        (sample.increasingIntersectionAssignment hlam0 hlamHalf x0 p0) x =
      (sample.sourceIntersectionCount graph x : ℤ) -
        sample.targetIntersectionCount graph x := by
  dsimp only
  rw [assignmentCrossingCurrent_eq_rankDiscrepancy]
  unfold assignmentRankDiscrepancy
  rw [target_count_comp_perm]
  simp only [Finset.sum_boole, sourceIntersectionCount, targetIntersectionCount]

theorem increasingIntersectionCrossingCurrent_cast_eq_feedbackRankDiscrepancy
    {lam : ℝ} (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 x : ℝ) :
    let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
    (assignmentCrossingCurrent (sample.sourceIntersection graph)
        (sample.targetIntersection graph)
        (sample.increasingIntersectionAssignment hlam0 hlamHalf x0 p0) x : ℝ) =
      RelativeVC.feedbackRankDiscrepancy
        (fun i ↦ sample.rankSourcePoint i) (fun j ↦ sample.rankTargetPoint j)
        (graph.curve x) x := by
  dsimp only
  rw [sample.increasingIntersectionCrossingCurrent_eq_count_sub hlam0 hlamHalf x0 p0 x]
  exact_mod_cast sample.intersectionCurrent_eq_feedbackRankDiscrepancy
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) x

end FiniteSample

end OTSelector
