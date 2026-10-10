import OTSelector.Feedback.FeedbackA1Excursion
import OTSelector.Feedback.FeedbackA1ExponentialDrift

/-!
# Actual exponential moment of the initial feedback current

The safe current at the left boundary agrees almost surely with the difference of the two
actual binomial boundary counts.  This file transports the product-binomial MGF to that current
and records an explicit sparse bound.  No distributional or MGF hypothesis is exposed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ProbabilityTheory

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

open CountingProcess

/-- The actual safe initial current has the exponential moment furnished by the two independent
boundary binomials.  The exponential bound is a deliberately coarse finite-`n` version of
`(1.25b)`. -/
theorem integral_exponentialLyapunov_safeK0_le
    {lam B theta : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) (htheta : 0 ≤ theta) :
    ∫ sample : FiniteSample n, exponentialLyapunov theta (safeK0 lam B 0 sample)
        ∂(finiteSampleLaw n) ≤
      2 * Real.exp (2 * B * (Real.exp theta - 1)) := by
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem (n := n) hn hB0 hBn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmean : (n : ℝ) * (p : ℝ) = B := by
    rw [hp]
    field_simp
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
  have htransport :
      (∫ sample : FiniteSample n,
          exponentialLyapunov theta (safeK0 lam B 0 sample)
          ∂(finiteSampleLaw n)) =
        ∫ z : ℝ × ℝ, Real.exp (theta * |z.1 - z.2|)
          ∂(Bin(ℝ, n, p).prod Bin(ℝ, n, p)) := by
    calc
      (∫ sample : FiniteSample n,
          exponentialLyapunov theta (safeK0 lam B 0 sample)
          ∂(finiteSampleLaw n)) =
          ∫ sample : FiniteSample n,
            Real.exp (theta * |sample.leftBoundaryCurrentAt p|)
            ∂(finiteSampleLaw n) := by
        apply integral_congr_ae
        filter_upwards [safeK0_cast_ae_eq_leftBoundaryCurrentAt
          (n := n) hlam0 hlamHalf hn hB0 hBn] with sample heq
        unfold exponentialLyapunov
        rw [heq]
      _ = ∫ z : ℝ × ℝ, Real.exp (theta * |z.1 - z.2|)
          ∂(Bin(ℝ, n, p).prod Bin(ℝ, n, p)) := by
        simpa [leftBoundaryCurrentAt, Function.comp_def] using
          hreal'.integral_comp
            (f := fun z : ℝ × ℝ ↦ Real.exp (theta * |z.1 - z.2|)) (by fun_prop)
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hbase0 : 0 ≤ 1 - (p : ℝ) + (p : ℝ) * Real.exp theta := by
    have hexp0 := (Real.exp_pos theta).le
    nlinarith
  have hbase : 1 - (p : ℝ) + (p : ℝ) * Real.exp theta ≤
      Real.exp ((p : ℝ) * (Real.exp theta - 1)) := by
    calc
      1 - (p : ℝ) + (p : ℝ) * Real.exp theta =
          (p : ℝ) * (Real.exp theta - 1) + 1 := by ring
      _ ≤ Real.exp ((p : ℝ) * (Real.exp theta - 1)) :=
        Real.add_one_le_exp _
  have hpow :
      (1 - (p : ℝ) + (p : ℝ) * Real.exp theta) ^ (2 * n) ≤
        Real.exp ((p : ℝ) * (Real.exp theta - 1)) ^ (2 * n) :=
    pow_le_pow_left₀ hbase0 hbase (2 * n)
  have hexpPow :
      Real.exp ((p : ℝ) * (Real.exp theta - 1)) ^ (2 * n) =
        Real.exp (2 * B * (Real.exp theta - 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    calc
      ((2 * n : ℕ) : ℝ) * ((p : ℝ) * (Real.exp theta - 1)) =
          2 * ((n : ℝ) * (p : ℝ)) * (Real.exp theta - 1) := by
        push_cast
        ring
      _ = 2 * B * (Real.exp theta - 1) := by rw [hmean]
  calc
    (∫ sample : FiniteSample n,
        exponentialLyapunov theta (safeK0 lam B 0 sample)
        ∂(finiteSampleLaw n)) =
        ∫ z : ℝ × ℝ, Real.exp (theta * |z.1 - z.2|)
          ∂(Bin(ℝ, n, p).prod Bin(ℝ, n, p)) := htransport
    _ ≤ 2 * (1 - (p : ℝ) + (p : ℝ) * Real.exp theta) ^ (2 * n) :=
      Feedback.integral_exp_abs_sub_binomial_prod_le n p theta htheta
    _ ≤ 2 * (Real.exp ((p : ℝ) * (Real.exp theta - 1)) ^ (2 * n)) := by
      gcongr
    _ = 2 * Real.exp (2 * B * (Real.exp theta - 1)) := by rw [hexpPow]

/-- The standard A1 cutoff leaves the safe initial exponential observable unchanged. -/
theorem safeFeedback_initial_clippedExponential_eq_exponentialLyapunov
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) :
    clippedObservable (feedbackA1CurrentCutoff n)
        (exponentialLyapunov (feedbackA1ExponentialTheta lam))
        (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
        0 sample =
      exponentialLyapunov (feedbackA1ExponentialTheta lam) (safeK0 lam B 0 sample) := by
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
  have hclip : integerClip (feedbackA1CurrentCutoff n) (safeK0 lam B 0 sample) =
      safeK0 lam B 0 sample := by
    apply integerClip_eq_self_of_mem
    rw [cutoffStates, Finset.mem_Icc]
    exact ⟨hinterior.1.le, hinterior.2.le⟩
  simpa only [Nplus, Nminus] using
    (show clippedObservable (feedbackA1CurrentCutoff n)
          (exponentialLyapunov (feedbackA1ExponentialTheta lam))
          (safeK0 lam B 0) Nplus Nminus 0 sample =
        exponentialLyapunov (feedbackA1ExponentialTheta lam) (safeK0 lam B 0 sample) by
      rw [clippedObservable_zero hplus hminus, hclip])

/-- Actual `(1.25b)` in the form consumed by the stopped exponential envelope. -/
theorem integral_safeFeedback_initial_clippedExponential_le
    {lam B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB0 : 0 ≤ B) (hBn : B ≤ n) :
    ∫ sample : FiniteSample n,
        clippedObservable (feedbackA1CurrentCutoff n)
          (exponentialLyapunov (feedbackA1ExponentialTheta lam))
          (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0.le (by linarith) B B 0)
          (safeTargetBulkCount (n := n) hlam0.le (by linarith) B B 0)
          0 sample ∂(finiteSampleLaw n) ≤
      2 * Real.exp (2 * B *
        (Real.exp (feedbackA1ExponentialTheta lam) - 1)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  rw [show (fun sample : FiniteSample n ↦
      clippedObservable (feedbackA1CurrentCutoff n)
        (exponentialLyapunov (feedbackA1ExponentialTheta lam))
        (safeK0 lam B 0)
        (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
        (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
        0 sample) =
      (fun sample ↦ exponentialLyapunov
        (feedbackA1ExponentialTheta lam) (safeK0 lam B 0 sample)) by
    funext sample
    exact safeFeedback_initial_clippedExponential_eq_exponentialLyapunov
      (n := n) hlam0.le hlamHalf B sample]
  exact integral_exponentialLyapunov_safeK0_le
    (n := n) hlam0.le hlamHalf hn hB0 hBn
      (feedbackA1ExponentialTheta_pos hlam0).le

end FiniteSample

end OTSelector
