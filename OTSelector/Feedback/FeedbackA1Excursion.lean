import OTSelector.Feedback.FeedbackA1Occupation
import OTSelector.Feedback.FeedbackBoundaryComparison
import OTSelector.Probability.CountingProcess.CurrentExcursion

/-!
# Actual A1 stopped-current excursion

This file instantiates the stopped two-colour current tail with the safe bulk source and target
counts.  The initial third moment is transported from the actual product-binomial boundary law,
and the stopped quadratic occupation is supplied by the A1 cubic drift estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

open CountingProcess

private theorem initialSeenSource_card_eq_leftSourceCountAt
    (hn : 0 < n) {B : ℝ} (hB0 : 0 ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    (sample.initialSeenSource B 0).card =
      sample.leftSourceCountAt (leftBoundaryRankThreshold n B) := by
  classical
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem (n := n) hn hB0 hBn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold initialSeenSource leftSourceCountAt
  rw [show {i : Fin n | sample.sourceHeight i ≤ p} =
      (↑(Finset.univ.filter fun i : Fin n ↦
        (n : ℝ) * (sample.sourceHeight i : ℝ) +
          sample.sourceSlope i * 0 ≤ B) : Set (Fin n)) by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, mul_zero, add_zero]
    change ((sample.sourceHeight i : ℝ) ≤ (p : ℝ)) ↔ _
    rw [hp, le_div_iff₀ hnreal]
    ring_nf]
  exact (Set.ncard_coe_finset _).symm

private theorem initialSeenTarget_card_eq_leftTargetCountAt
    (hn : 0 < n) {B : ℝ} (hB0 : 0 ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    (sample.initialSeenTarget B 0).card =
      sample.leftTargetCountAt (leftBoundaryRankThreshold n B) := by
  classical
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem (n := n) hn hB0 hBn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold initialSeenTarget leftTargetCountAt
  rw [show {i : Fin n | sample.targetHeight i ≤ p} =
      (↑(Finset.univ.filter fun i : Fin n ↦
        (n : ℝ) * (sample.targetHeight i : ℝ) -
          sample.targetSlope i * 0 ≤ B) : Set (Fin n)) by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, mul_zero, sub_zero]
    change ((sample.targetHeight i : ℝ) ≤ (p : ℝ)) ↔ _
    rw [hp, le_div_iff₀ hnreal]
    ring_nf]
  exact (Set.ncard_coe_finset _).symm

private theorem initialFeedbackCurrent_cast_eq_leftBoundaryCurrentAt
    (hn : 0 < n) {B : ℝ} (hB0 : 0 ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    (sample.initialFeedbackCurrent B 0 : ℝ) =
      sample.leftBoundaryCurrentAt (leftBoundaryRankThreshold n B) := by
  rw [initialFeedbackCurrent, leftBoundaryCurrentAt,
    initialSeenSource_card_eq_leftSourceCountAt hn hB0 hBn,
    initialSeenTarget_card_eq_leftTargetCountAt hn hB0 hBn]
  norm_cast

/-- Away from the null tie set, the safe initial current is the actual zero-shear boundary
binomial current at rank `B`. -/
theorem safeK0_cast_ae_eq_leftBoundaryCurrentAt
    {lam B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) =ᵐ[
        (finiteSampleLaw n : Measure (FiniteSample n))]
      (fun sample ↦
        sample.leftBoundaryCurrentAt (leftBoundaryRankThreshold n B)) := by
  filter_upwards [finiteSampleLaw_noFeedbackTies_ae
    (n := n) (x0 := B) (p0 := 0) hlam0 hlamHalf] with sample hNoTie
  simp only [safeK0, hNoTie, ↓reduceIte]
  exact initialFeedbackCurrent_cast_eq_leftBoundaryCurrentAt hn hB0 hBn sample

private theorem abs_safeK0_cast_le
    (lam B : ℝ) (sample : FiniteSample n) :
    |(safeK0 lam B 0 sample : ℝ)| ≤ n := by
  classical
  have hsource : (sample.initialSeenSource B 0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenSource B 0))
  have htarget : (sample.initialSeenTarget B 0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenTarget B 0))
  by_cases hNoTie : sample.NoFeedbackTies lam B 0
  · have hcurrent : -(n : ℤ) ≤ sample.initialFeedbackCurrent B 0 ∧
        sample.initialFeedbackCurrent B 0 ≤ (n : ℤ) := by
      rw [initialFeedbackCurrent]
      omega
    have hlower : -(n : ℝ) ≤ (sample.initialFeedbackCurrent B 0 : ℝ) := by
      exact_mod_cast hcurrent.1
    have hupper : (sample.initialFeedbackCurrent B 0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hcurrent.2
    simp only [safeK0, hNoTie, ↓reduceIte]
    exact abs_le.mpr ⟨hlower, hupper⟩
  · simp [safeK0, hNoTie]

private theorem safeK0_abs_cube_integrable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) :
    Integrable (fun sample : FiniteSample n ↦ |(safeK0 lam B 0 sample : ℝ)| ^ 3)
      (finiteSampleLaw n) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have hstrong : StronglyMeasurable
      (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) := by
    exact (safeK0_stronglyMeasurable_usual_zero
      (n := n) hlam0 hlamHalf B 0).mono (ℱ.le 0)
  refine Integrable.of_bound ((hstrong.measurable.abs.pow_const 3).aestronglyMeasurable)
    ((n : ℝ) ^ 3) (ae_of_all _ fun sample ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_safeK0_cast_le lam B sample) 3

private theorem integral_abs_leftBoundaryCurrentAt_cube_le
    (p : UnitMark) {B : ℝ}
    (hmean : (n : ℝ) * (p : ℝ) = B) :
    ∫ sample : FiniteSample n, |sample.leftBoundaryCurrentAt p| ^ 3
        ∂(finiteSampleLaw n) ≤
      2 * B + 5 * B * Real.sqrt B := by
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
  calc
    ∫ sample : FiniteSample n, |sample.leftBoundaryCurrentAt p| ^ 3
        ∂(finiteSampleLaw n) =
        ∫ z : ℝ × ℝ, |z.1 - z.2| ^ 3
          ∂(Bin(ℝ, n, p).prod Bin(ℝ, n, p)) := by
      simpa [leftBoundaryCurrentAt, Function.comp_def] using
        hreal'.integral_comp (f := fun z : ℝ × ℝ ↦ |z.1 - z.2| ^ 3) (by fun_prop)
    _ ≤ 2 * B + 5 * B * Real.sqrt B :=
      Feedback.binomial_difference_third_moment_le_of_mean_eq n p B hmean

/-- The actual safe initial current at `(B,0)` has the required sparse cubic moment. -/
theorem integral_abs_safeK0_cube_le
    {lam B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    ∫ sample : FiniteSample n, |(safeK0 lam B 0 sample : ℝ)| ^ 3
        ∂(finiteSampleLaw n) ≤
      2 * B + 5 * B * Real.sqrt B := by
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem (n := n) hn hB0 hBn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean : (n : ℝ) * (p : ℝ) = B := by
    rw [hp]
    field_simp
  calc
    ∫ sample : FiniteSample n, |(safeK0 lam B 0 sample : ℝ)| ^ 3
        ∂(finiteSampleLaw n) =
        ∫ sample : FiniteSample n, |sample.leftBoundaryCurrentAt p| ^ 3
          ∂(finiteSampleLaw n) := by
      apply integral_congr_ae
      filter_upwards [safeK0_cast_ae_eq_leftBoundaryCurrentAt
        (n := n) hlam0 hlamHalf hn hB0 hBn] with sample heq
      rw [heq]
    _ ≤ 2 * B + 5 * B * Real.sqrt B :=
      integral_abs_leftBoundaryCurrentAt_cube_le p hmean

/-! ## Actual stopped-current event -/

/-- Raw A1-stopped excursion event for the safe bulk current started at `(B,0)`. -/
noncomputable def safeFeedbackA1StoppedCurrentExcursionRaw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (R : ℕ) : Set (FiniteSample n) :=
  throughStopCurrentExcursionRaw
    (safeFeedbackA1StopTime
      (n := n) hlam0 hlamHalf eta B B 0 T)
    R (safeK0 lam B 0)
    (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
    (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T

/-- Measurable hull of the actual A1-stopped excursion event. -/
noncomputable def safeFeedbackA1StoppedCurrentExcursionEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (R : ℕ) : Set (FiniteSample n) :=
  throughStopCurrentExcursionEvent (finiteSampleLaw n)
    (safeFeedbackA1StopTime
      (n := n) hlam0 hlamHalf eta B B 0 T)
    R (safeK0 lam B 0)
    (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
    (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T

theorem measurableSet_safeFeedbackA1StoppedCurrentExcursionEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (R : ℕ) :
    MeasurableSet
      (safeFeedbackA1StoppedCurrentExcursionEvent
        (n := n) hlam0 hlamHalf eta B T R) := by
  exact measurableSet_throughStopCurrentExcursionEvent _ _ _ _ _ _ _

theorem safeFeedbackA1StoppedCurrentExcursionRaw_subset_event
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (R : ℕ) :
    safeFeedbackA1StoppedCurrentExcursionRaw
        (n := n) hlam0 hlamHalf eta B T R ⊆
      safeFeedbackA1StoppedCurrentExcursionEvent
        (n := n) hlam0 hlamHalf eta B T R := by
  exact throughStopCurrentExcursionRaw_subset_event _ _ _ _ _ _ _

/-- A strict-survival witness is contained in the raw stopped-current event.  This is the
interface used later by a first-hit argument. -/
theorem mem_safeFeedbackA1StoppedCurrentExcursionRaw_of_reaches
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B : ℝ} {T u : ℝ≥0} {R : ℕ} {sample : FiniteSample n}
    (huT : u ≤ T)
    (huStop : (u : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample)
    (hreaches : 2 * (R : ℝ) ≤
      |(currentOfCounts (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) u sample : ℝ)|) :
    sample ∈ safeFeedbackA1StoppedCurrentExcursionRaw
      (n := n) hlam0 hlamHalf eta B T R := by
  exact ⟨u, huT, huStop.le, hreaches⟩

theorem mem_safeFeedbackA1StoppedCurrentExcursionEvent_of_reaches
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B : ℝ} {T u : ℝ≥0} {R : ℕ} {sample : FiniteSample n}
    (huT : u ≤ T)
    (huStop : (u : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample)
    (hreaches : 2 * (R : ℝ) ≤
      |(currentOfCounts (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) u sample : ℝ)|) :
    sample ∈ safeFeedbackA1StoppedCurrentExcursionEvent
      (n := n) hlam0 hlamHalf eta B T R := by
  apply safeFeedbackA1StoppedCurrentExcursionRaw_subset_event
    (n := n) hlam0 hlamHalf eta B T R
  exact mem_safeFeedbackA1StoppedCurrentExcursionRaw_of_reaches
    (n := n) hlam0 hlamHalf huT huStop hreaches

private theorem safeFeedback_initial_clippedObservable_eq_abs_cube
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) :
    clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
        (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        0 sample =
      |(safeK0 lam B 0 sample : ℝ)| ^ 3 := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0 hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0 hlamHalf B B 0
  have hplus : IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0 hlamHalf B B 0
  have hminus : IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0 hlamHalf B B 0
  have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
    (n := n) hlam0 hlamHalf B B 0 0 sample
  simp only [leftCurrentOfCounts_zero] at hinterior
  have hclip : integerClip (feedbackA1CurrentCutoff n)
      (safeK0 lam B 0 sample) = safeK0 lam B 0 sample := by
    apply integerClip_eq_self_of_mem
    rw [cutoffStates, Finset.mem_Icc]
    exact ⟨hinterior.1.le, hinterior.2.le⟩
  rw [clippedObservable_zero hplus hminus, hclip]
  rfl

/-- The initial clipped cubic observable satisfies the actual sparse boundary moment bound. -/
theorem integral_safeFeedback_initial_clippedObservable_le
    {lam B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    ∫ sample, clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
        (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        0 sample ∂(finiteSampleLaw n) ≤
      2 * B + 5 * B * Real.sqrt B := by
  rw [show (fun sample : FiniteSample n ↦
      clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
        (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        0 sample) =
      (fun sample ↦ |(safeK0 lam B 0 sample : ℝ)| ^ 3) by
    funext sample
    exact safeFeedback_initial_clippedObservable_eq_abs_cube
      hlam0 hlamHalf B sample]
  exact integral_abs_safeK0_cube_le hlam0 hlamHalf hn hB0 hBn

/-! ## Actual cubic excursion tail -/

/-- Under the actual finite-sample law, the A1-stopped safe bulk current has an explicit cubic
tail.  Both the initial moment and stopped occupation are discharged internally. -/
theorem finiteSampleLaw_real_safeFeedbackA1StoppedCurrentExcursion_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) {R : ℕ} (hR : 0 < R) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (safeFeedbackA1StoppedCurrentExcursionEvent
          (n := n) hlam0.le (by linarith) eta B T R) ≤
      (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let ℱ := usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0
  let Nplus : ℝ≥0 → FiniteSample n → ℕ :=
    safeSourceBulkCount hlam0.le hlamHalf B B 0
  let Nminus : ℝ≥0 → FiniteSample n → ℕ :=
    safeTargetBulkCount hlam0.le hlamHalf B B 0
  let Λplus : ℝ≥0 → FiniteSample n → ℝ :=
    safeSourceBulkRate hlam0.le hlamHalf B B 0
  let Λminus : ℝ≥0 → FiniteSample n → ℝ :=
    safeTargetBulkRate hlam0.le hlamHalf B B 0
  let τ : FiniteSample n → WithTop ℝ≥0 :=
    safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T
  have hplus : IsSimpleCountingProcess ℱ Nplus := by
    simpa only [ℱ, Nplus] using
      safeSourceBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
  have hminus : IsSimpleCountingProcess ℱ Nminus := by
    simpa only [ℱ, Nminus] using
      safeTargetBulkCount_isSimpleCountingProcess
        (n := n) hlam0.le hlamHalf B B 0
  have hNo : ∀ u, NoSimultaneousJumpsOn Nplus Nminus u := by
    intro u
    simpa only [Nplus, Nminus] using
      safeBulkCounts_noSimultaneousJumpsOn
        (n := n) hlam0.le hlamHalf B B 0 u
  have hΛplus : HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nplus Λplus := by
    simpa only [ℱ, Nplus, Λplus] using
      safeSourceBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hΛminus : HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n)) ℱ Nminus Λminus := by
    simpa only [ℱ, Nminus, Λminus] using
      safeTargetBulkCount_hasPredictableIntensity
        (n := n) hlam0.le hlamHalf hn hB
  have hK0 : StronglyMeasurable[ℱ 0]
      (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) := by
    simpa only [ℱ] using safeK0_stronglyMeasurable_usual_zero
      (n := n) hlam0.le hlamHalf B 0
  have hMaskProduct := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta B 0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask
      (n := n) hlam0.le hlamHalf eta B B 0 T =
      throughStopMask τ := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0.le hlamHalf eta B B 0 T u sample
  have hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ) := by
    rw [← hMaskEq]
    simpa only [ℱ] using hMaskProduct
  have hAplus : ∀ u, Integrable
      (fun sample ↦ integratedIntensity
        Λplus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeSourceBulkRate_le_cap
        hlam0.le hlamHalf B B 0 s sample) hplus hΛplus
  have hAminus : ∀ u, Integrable
      (fun sample ↦ integratedIntensity
        Λminus (fun _ _ ↦ (1 : ℝ)) u sample) (finiteSampleLaw n) := by
    intro u
    apply integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (fun s sample ↦ safeTargetBulkRate_le_cap
        hlam0.le hlamHalf B B 0 s sample) hminus hΛminus
  have hRate : ∀ sample (s : ℝ≥0), (s : WithTop ℝ≥0) < τ sample →
      Λplus s sample ≤ 3 ∧ Λminus s sample ≤ 3 := by
    intro sample s hs
    exact ⟨(safeSourceBulkRate_mem_Icc_of_lt_A1Stop
        (n := n) hlam0 hlam hB heta0 hetaSmall T s sample hs).2,
      (safeTargetBulkRate_mem_Icc_of_lt_A1Stop
        (n := n) hlam0 hlam hB heta0 hetaSmall T s sample hs).2⟩
  have hCurrent : ∀ u sample,
      |(leftCurrentOfCounts (safeK0 lam B 0)
        Nplus Nminus u sample : ℝ)| ≤
        (feedbackA1CurrentCutoff n : ℝ) := by
    intro u sample
    simpa only [Nplus, Nminus] using
      abs_leftCurrentOfSafeBulkCounts_le_cutoff
        (n := n) hlam0.le hlamHalf B B 0 u sample
  have hOccupation : Integrable
      (throughStopClippedQuadraticOccupation
        τ (safeK0 lam B 0) Nplus Nminus T) (finiteSampleLaw n) :=
    throughStopClippedQuadraticOccupation_integrable_of_current_bound
      hplus hminus hK0 hMask (K := (feedbackA1CurrentCutoff n : ℝ))
      (by positivity) hCurrent T
  have hOccupationTime : ∀ sample, IntegrableOn
      (fun s ↦ throughStopMask τ s sample *
        (leftCurrentOfCounts (safeK0 lam B 0) Nplus Nminus s sample : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) T) timeMeasure := by
    intro sample
    exact throughStopClippedQuadraticOccupation_integrableOn_of_current_bound
      hplus hminus hK0 hMask (K := (feedbackA1CurrentCutoff n : ℝ))
      (by positivity) hCurrent T sample
  have hInitialIntegrable := safeK0_abs_cube_integrable
    (n := n) hlam0.le hlamHalf B
  have hGeneric := measureReal_throughStopCurrentExcursionEvent_le
    hplus hminus hNo hΛplus hΛminus hK0 hMask hAplus hAminus
    (C := 3) (by norm_num) hRate hR T hInitialIntegrable
    hOccupation hOccupationTime
  have hInitialBound := integral_abs_safeK0_cube_le
    (n := n) hlam0.le hlamHalf hn hB.le hBn
  have hClippedInitialBound := integral_safeFeedback_initial_clippedObservable_le
    (n := n) hlam0.le hlamHalf hn hB.le hBn
  have hOccupationRaw := safeFeedbackA1_cubic_stopped_occupation_bound
    (n := n) (x0 := B) (p0 := 0)
    hlam0 hlam hn hB heta0 hetaSmall T T
  have hOccupationBound :
      ∫ sample, throughStopClippedQuadraticOccupation
          τ (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n) ≤
        ((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam) := by
    calc
      ∫ sample, throughStopClippedQuadraticOccupation
          τ (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n) ≤
          ((∫ sample, clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
              (safeK0 lam B 0) Nplus Nminus 0 sample ∂(finiteSampleLaw n)) +
            (6 + 81 / lam) * (T : ℝ)) / (2 * lam) := by
        simpa only [τ, Nplus, Nminus, hlamHalf] using hOccupationRaw
      _ ≤ ((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam) := by
        have hClip :
            (∫ sample, clippedObservable (feedbackA1CurrentCutoff n) cubicLyapunov
              (safeK0 lam B 0) Nplus Nminus 0 sample ∂(finiteSampleLaw n)) ≤
              2 * B + 5 * B * Real.sqrt B := by
          simpa only [Nplus, Nminus] using hClippedInitialBound
        exact div_le_div_of_nonneg_right
          (add_le_add hClip le_rfl)
          (by positivity)
  have hRcube : 0 ≤ (R : ℝ) ^ 3 := by positivity
  have hInitialTail := div_le_div_of_nonneg_right hInitialBound hRcube
  have hOccupationTail :
      3 * (∫ sample, throughStopClippedQuadraticOccupation
          τ (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n)) /
          (R : ℝ) ^ 3 ≤
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hOccupationBound (by norm_num)) hRcube
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (safeFeedbackA1StoppedCurrentExcursionEvent
          (n := n) hlam0.le (by linarith) eta B T R) ≤
        (∫ sample, |(safeK0 lam B 0 sample : ℝ)| ^ 3 ∂(finiteSampleLaw n)) /
            (R : ℝ) ^ 3 +
          3 * (∫ sample, throughStopClippedQuadraticOccupation
            τ (safeK0 lam B 0) Nplus Nminus T sample ∂(finiteSampleLaw n)) /
            (R : ℝ) ^ 3 := by
      simpa only [safeFeedbackA1StoppedCurrentExcursionEvent,
        τ, Nplus, Nminus, hlamHalf] using hGeneric
    _ ≤ (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 :=
      add_le_add hInitialTail hOccupationTail

end FiniteSample

end OTSelector
