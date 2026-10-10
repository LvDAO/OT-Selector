import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Ring

/-!
# Energy bootstraps under a fixed conditioning event

A pathwise one-step inclusion is iterated over geometric scales.  A uniform unconditional mean
bound and thresholds tending to infinity remove the terminal event by Markov's inequality.  The
conditional version derives its mean bound by restriction, so the probability of the fixed
conditioning event only affects the vanishing terminal term.
-/

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A summable one-step error controls the initial event when its successors have bounded-mean
nonnegative energy and thresholds tending to infinity. -/
theorem measure_bad_le_tsum_of_energy_bootstrap
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (bad error : ℕ → Set Ω) (r ε : ℕ → ℝ) (C : ℝ)
    (hX0 : ∀ n, 0 ≤ᵐ[μ] X n) (hXint : ∀ n, Integrable (X n) μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ ≤ C)
    (hr0 : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop)
    (hbad : ∀ n, bad n ⊆ {ω | r n ≤ X n ω})
    (hstep : ∀ n, ∀ᵐ ω ∂μ, ω ∈ bad n → ω ∈ bad (n + 1) ∪ error n)
    (herror : ∀ n, μ.real (error n) ≤ ε n) (hε : Summable ε) :
    μ.real (bad 0) ≤ ∑' n, ε n := by
  have hrec (n : ℕ) : μ.real (bad n) ≤ μ.real (bad (n + 1)) + ε n := by
    calc
      μ.real (bad n) ≤ μ.real (bad (n + 1) ∪ error n) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hstep n))
      _ ≤ μ.real (bad (n + 1)) + μ.real (error n) := measureReal_union_le _ _
      _ ≤ μ.real (bad (n + 1)) + ε n := add_le_add le_rfl (herror n)
  have hmarkov (n : ℕ) : μ.real (bad n) ≤ C / r n := by
    apply (le_div_iff₀ (hr0 n)).mpr
    calc
      μ.real (bad n) * r n ≤ μ.real {ω | r n ≤ X n ω} * r n :=
        mul_le_mul_of_nonneg_right (measureReal_mono (hbad n)) (hr0 n).le
      _ ≤ ∫ ω, X n ω ∂μ := by
        simpa only [mul_comm] using
          mul_meas_ge_le_integral_of_nonneg (hX0 n) (hXint n) (r n)
      _ ≤ C := hmean n
  have hzero : Tendsto (fun n ↦ μ.real (bad n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ measureReal_nonneg) hmarkov
      (Tendsto.div_atTop tendsto_const_nhds hr)
  have hiter (N : ℕ) : μ.real (bad 0) ≤
      μ.real (bad N) + ∑ n ∈ Finset.range N, ε n := by
    induction N with
    | zero => simp
    | succ N ih =>
      calc
        μ.real (bad 0) ≤ μ.real (bad N) + ∑ n ∈ Finset.range N, ε n := ih
        _ ≤ (μ.real (bad (N + 1)) + ε N) + ∑ n ∈ Finset.range N, ε n :=
          add_le_add (hrec N) le_rfl
        _ = μ.real (bad (N + 1)) + ∑ n ∈ Finset.range (N + 1), ε n := by
          rw [Finset.sum_range_succ]
          ring
  have hlim := hzero.add hε.hasSum.tendsto_sum_nat
  simpa only [zero_add] using ge_of_tendsto hlim (Eventually.of_forall hiter)

/-- Conditioning is fixed before sending the terminal scale to infinity.  The energy mean is
assumed under the original law; no conditional energy bound or terminal convergence is an input. -/
theorem cond_measure_bad_le_tsum_of_energy_bootstrap
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (hA0 : μ A ≠ 0)
    (X : ℕ → Ω → ℝ) (bad error : ℕ → Set Ω) (r ε : ℕ → ℝ) (C : ℝ)
    (hX0 : ∀ n, 0 ≤ᵐ[μ] X n) (hXint : ∀ n, Integrable (X n) μ)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ ≤ C)
    (hr0 : ∀ n, 0 < r n) (hr : Tendsto r atTop atTop)
    (hbad : ∀ n, bad n ⊆ {ω | r n ≤ X n ω})
    (hstep : ∀ n, ∀ ω ∈ A, ω ∈ bad n → ω ∈ bad (n + 1) ∪ error n)
    (herror : ∀ n, (ProbabilityTheory.cond μ A).real (error n) ≤ ε n)
    (hε : Summable ε) :
    (ProbabilityTheory.cond μ A).real (bad 0) ≤ ∑' n, ε n := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ A) :=
    ProbabilityTheory.cond_isProbabilityMeasure hA0
  apply measure_bad_le_tsum_of_energy_bootstrap (ProbabilityTheory.cond μ A) X bad error
    r ε ((μ A).toReal⁻¹ * C) _ _ _ hr0 hr hbad _ herror hε
  · intro n
    exact ProbabilityTheory.cond_absolutelyContinuous.ae_le (hX0 n)
  · intro n
    exact ((hXint n).mono_measure μ.restrict_le_self).smul_measure
      (ENNReal.inv_ne_top.mpr hA0)
  · intro n
    rw [ProbabilityTheory.cond, integral_smul_measure]
    simp only [ENNReal.toReal_inv, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      ((integral_mono_measure μ.restrict_le_self (hX0 n) (hXint n)).trans (hmean n))
      (inv_nonneg.mpr ENNReal.toReal_nonneg)
  · intro n
    exact ProbabilityTheory.ae_cond_of_forall_mem hA (hstep n)

end OTSelector.Probability
