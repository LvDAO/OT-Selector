import OTSelector.PointProcess.LocalConfigurationCompactness
import OTSelector.PointProcess.LocalConfigurationProbability
import OTSelector.PointProcess.LocalConfigurationMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tightness from local counting estimates

Uniform tails for the actual shell counts give compact containment through closed-annulus
assembly.  Uniform finite first moments of actual counting measures on integer balls imply
these tails by Markov's inequality.  The resulting tightness yields weakly convergent
subsequences of configuration laws in the proved vague topology.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators Classical ENNReal NNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [StandardBorelSpace X] {base : X}

noncomputable local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology base

/-- One compact set simultaneously bounds the escaped mass of every measure by its shell tails. -/
theorem exists_isCompact_measure_compl_le_shellTail (N : ℕ → ℕ) :
    ∃ K : Set (LocalConfiguration base), IsCompact K ∧
      ∀ μ : Measure (LocalConfiguration base),
        μ Kᶜ ≤ ∑' n, μ {config | N n < (config n).card} := by
  obtain ⟨K, hK, hsub⟩ := exists_isCompact_superset_shellCard_le (base := base) N
  refine ⟨K, hK, fun μ ↦ ?_⟩
  have hcompl : Kᶜ ⊆ ⋃ n, {config | N n < (config n).card} := by
    intro config hconfig
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    exact hconfig (hsub h)
  exact (measure_mono hcompl).trans (measure_iUnion_le _)

/-- Uniform vanishing tails of each actual shell count imply tightness in the vague topology. -/
theorem isTightMeasureSet_of_shell_tail (S : Set (Measure (LocalConfiguration base)))
    (htail : ∀ n, ∀ ε : ℝ≥0, 0 < ε → ∃ M : ℕ,
      ∀ μ ∈ S, μ {config | M < (config n).card} ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose N hN using fun n ↦ htail n (δ n) (hδpos n)
  obtain ⟨K, hK, hbound⟩ := exists_isCompact_measure_compl_le_shellTail (base := base) N
  refine ⟨K, hK, fun μ hμ ↦ ?_⟩
  exact (hbound μ).trans ((ENNReal.tsum_le_tsum fun n ↦ hN n μ hμ).trans hδsum.le)

omit [ProperSpace X] [StandardBorelSpace X] in
/-- A shell count is bounded by the count in its enclosing integer-radius open ball. -/
theorem shellCard_le_countingMeasure_ball (config : LocalConfiguration base) (n : ℕ) :
    ((config n).card : ℝ≥0∞) ≤ countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ)) := by
  rw [countingMeasure_ball, card_window]
  exact_mod_cast Finset.single_le_sum (fun i _ ↦ Nat.zero_le (config i).card)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

omit [ProperSpace X] in
/-- Markov's inequality applied to the multiplicity-preserving count of an actual shell. -/
theorem measure_shellTail_le_lintegral_countingMeasure_ball_div
    (μ : Measure (LocalConfiguration base)) (n M : ℕ) :
    μ {config | M < (config n).card} ≤
      (∫⁻ config, countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ)) ∂μ) /
        ((M + 1 : ℕ) : ℝ≥0∞) := by
  have hmeas : Measurable (fun config : LocalConfiguration base ↦
      ((config n).card : ℝ≥0∞)) :=
    (measurable_of_countable (fun m : ℕ ↦ (m : ℝ≥0∞))).comp (measurable_shell_card n)
  have hset : {config : LocalConfiguration base | M < (config n).card} =
      {config | ((M + 1 : ℕ) : ℝ≥0∞) ≤ ((config n).card : ℝ≥0∞)} := by
    ext config
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
    omega
  rw [hset]
  exact (meas_ge_le_lintegral_div hmeas.aemeasurable (by simp) (by simp)).trans
    (ENNReal.div_le_div_right (lintegral_mono fun config ↦
      shellCard_le_countingMeasure_ball config n) _)

/-- Uniform finite first moments of actual local counts imply tightness.  The bound may depend
on the ball radius, and no configuration-space compactness premise is assumed. -/
theorem isTightMeasureSet_of_lintegral_countingMeasure_ball_le
    (S : Set (Measure (LocalConfiguration base))) (b : ℕ → ℝ≥0∞)
    (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ μ ∈ S, ∀ n,
      ∫⁻ config, countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ)) ∂μ ≤ b n) :
    IsTightMeasureSet S := by
  apply isTightMeasureSet_of_shell_tail S
  intro n ε hε
  have hεzero : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top (hb n) hεzero)
  have hratio : b n / ((M + 1 : ℕ) : ℝ≥0∞) ≤ ε := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    rw [mul_comm]
    apply (ENNReal.div_le_iff hεzero ENNReal.coe_ne_top).mp
    exact hM.le.trans (by exact_mod_cast Nat.le_succ M)
  refine ⟨M, fun μ hμ ↦ ?_⟩
  exact (measure_shellTail_le_lintegral_countingMeasure_ball_div μ n M).trans
    ((ENNReal.div_le_div_right (hbound μ hμ n) _).trans hratio)

/-- Uniform local counting moments of measurable random configurations give tight laws. -/
theorem isTightMeasureSet_map_of_lintegral_countingMeasure_ball_le
    {Ω ι : Type*} [MeasurableSpace Ω] (P : ι → Measure Ω)
    (config : ι → Ω → LocalConfiguration base) (hconfig : ∀ i, Measurable (config i))
    (b : ℕ → ℝ≥0∞) (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n,
      ∫⁻ ω, countingMeasure (config i ω) (Metric.ball base ((n + 1 : ℕ) : ℝ)) ∂P i ≤ b n) :
    IsTightMeasureSet (Set.range fun i ↦ (P i).map (config i)) := by
  apply isTightMeasureSet_of_lintegral_countingMeasure_ball_le _ b hb
  rintro μ ⟨i, rfl⟩ n
  rw [lintegral_map]
  · exact hbound i n
  · exact (Measure.measurable_coe (Metric.isOpen_ball.measurableSet)).comp
      measurable_countingMeasure
  · exact hconfig i

section Subsequences

variable [SecondCountableTopology X]

local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace

/-- Uniform local count moments produce an actual weakly convergent subsequence of vague
configuration laws, by compact containment and the proved configuration-law subsequence theorem. -/
theorem exists_tendsto_subseq_of_lintegral_countingMeasure_ball_le
    (μ : ℕ → ProbabilityMeasure (LocalConfiguration base)) (b : ℕ → ℝ≥0∞)
    (hb : ∀ n, b n ≠ ∞)
    (hbound : ∀ i n,
      ∫⁻ config, countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ))
        ∂(μ i : Measure (LocalConfiguration base)) ≤ b n) :
    ∃ ν : ProbabilityMeasure (LocalConfiguration base), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  apply exists_tendsto_subseq_of_isTightMeasureSet μ
  apply isTightMeasureSet_of_lintegral_countingMeasure_ball_le _ b hb
  rintro _ ⟨i, rfl⟩ n
  exact hbound i n

end Subsequences

end OTSelector.PointProcess.LocalConfiguration
