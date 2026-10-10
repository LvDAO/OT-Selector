import OTSelector.PointProcess.MatchingSceneResidualLimit
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Continuous past-window tests

The complement of mathlib's continuous approximation to a closed set gives tests supported
inside an open spatial interval. Their actual configuration integrals converge to marked hard
window counts whenever the right endpoint has no atom. All multiplicities are retained.
-/

open MeasureTheory Set Filter Function Topology
open scoped Classical ENNReal NNReal CompactlySupported BoundedContinuousFunction

namespace OTSelector.PointProcess

private noncomputable def windowCutoff (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 - ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ)

private theorem continuous_windowCutoff (a b : ℝ) (n : ℕ) :
    Continuous (windowCutoff a b n) :=
  continuous_const.sub (continuous_subtype_val.comp
    ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n).continuous)

private theorem windowCutoff_bounds (a b : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ windowCutoff a b n x ∧ windowCutoff a b n x ≤ 1 := by
  have h := HasOuterApproxClosed.apprSeq_apply_le_one
    (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl n x
  have h' : ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x : ℝ) ≤ 1 := h
  have hn := ((isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n x).property
  dsimp [windowCutoff]
  constructor <;> linarith

private theorem windowCutoff_eq_zero (a b : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∉ Ioo a b) : windowCutoff a b n x = 0 := by
  have h := HasOuterApproxClosed.apprSeq_apply_eq_one
    (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl n (show x ∈ (Ioo a b)ᶜ from hx)
  simp [windowCutoff, h]

/-- Compact point test approximating a marked spatial interval from its interior. -/
noncomputable def pastWindowTest (a b : ℝ) (ψ : UnitMark →ᵇ ℝ) (n : ℕ) :
    C_c(MatchingPoint, ℝ) where
  toFun p := windowCutoff a b n p.1 * ψ p.2
  continuous_toFun := ((continuous_windowCutoff a b n).comp continuous_fst).mul
    (ψ.continuous.comp continuous_snd)
  hasCompactSupport' := by
    have hK : IsCompact (Icc a b ×ˢ (univ : Set UnitMark)) :=
      isCompact_Icc.prod isCompact_univ
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_Icc.prod isClosed_univ)
    intro p hp
    have hp' : p.1 ∈ Ioo a b := by
      by_contra h
      exact hp (by simp [windowCutoff_eq_zero a b n h])
    exact ⟨⟨hp'.1.le, hp'.2.le⟩, mem_univ _⟩

/-- These are legal past tests, including at the root itself. -/
theorem pastWindowTest_eq_zero_of_nonneg {a b : ℝ} (hb : b ≤ 0)
    (ψ : UnitMark →ᵇ ℝ) (n : ℕ) (p : MatchingPoint) (hp : 0 ≤ p.1) :
    pastWindowTest a b ψ n p = 0 := by
  change windowCutoff a b n p.1 * ψ p.2 = 0
  rw [windowCutoff_eq_zero a b n (by intro h; linarith [h.2]), zero_mul]

/-- The actual marked hard count is the limit of compactly supported past-test integrals.
Only vacancy at the right endpoint is needed because both approximants and the hard window
exclude the left endpoint. -/
theorem tendsto_testIntegral_pastWindowTest
    (c : LocalConfiguration matchingPointBase) (a b : ℝ) (ψ : UnitMark →ᵇ ℝ)
    (hb : ∀ p : MatchingPoint, p.1 = b → LocalConfiguration.multiplicity c p = 0) :
    Tendsto (fun n ↦ LocalConfiguration.testIntegral c (pastWindowTest a b ψ n)) atTop
      (𝓝 (∫ p in LocalConfiguration.spatialIoc a b, ψ p.2
        ∂LocalConfiguration.countingMeasure c)) := by
  let K : Set MatchingPoint := Icc a b ×ˢ univ
  have hK : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hfin : LocalConfiguration.countingMeasure c K ≠ ∞ :=
    (LocalConfiguration.countingMeasure_lt_top_of_isBounded c
      (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set UnitMark))).isBounded).ne
  have hbound : Integrable (K.indicator (fun _ ↦ ‖ψ‖))
      (LocalConfiguration.countingMeasure c) :=
    (integrable_indicator_iff hK).mpr (integrableOn_const hfin)
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n p ↦ pastWindowTest a b ψ n p)
    (f := (LocalConfiguration.spatialIoc a b).indicator (fun p ↦ ψ p.2))
    (K.indicator (fun _ ↦ ‖ψ‖))
    (fun n ↦ (pastWindowTest a b ψ n).continuous.measurable.aestronglyMeasurable)
    hbound ?_ ?_
  · simpa only [LocalConfiguration.integral_countingMeasure,
      integral_indicator (LocalConfiguration.measurableSet_spatialIoc a b)] using h
  · intro n
    exact Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ K
      · rw [indicator_of_mem hp]
        change ‖windowCutoff a b n p.1 * ψ p.2‖ ≤ ‖ψ‖
        rw [norm_mul, Real.norm_of_nonneg (windowCutoff_bounds a b n p.1).1]
        calc
          _ ≤ 1 * ‖ψ‖ := mul_le_mul (windowCutoff_bounds a b n p.1).2
            (ψ.norm_coe_le_norm _) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      · rw [indicator_of_notMem hp]
        have hnot : p.1 ∉ Ioo a b := fun h ↦ hp ⟨⟨h.1.le, h.2.le⟩, mem_univ _⟩
        change ‖windowCutoff a b n p.1 * ψ p.2‖ ≤ 0
        rw [windowCutoff_eq_zero a b n hnot, zero_mul, norm_zero]
  · filter_upwards [LocalConfiguration.ae_mem_multiplicity_support c] with p hp
    have hpb : p.1 ≠ b := fun h ↦ hp (hb p h)
    have hraw : Tendsto (fun n ↦
        (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl.apprSeq n p.1) atTop
        (𝓝 (((Ioo a b)ᶜ).indicator (fun _ : ℝ ↦ (1 : ℝ≥0)) p.1)) :=
      (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq
        (isOpen_Ioo : IsOpen (Ioo a b)).isClosed_compl)) p.1
    by_cases hx : p.1 ∈ Ioo a b
    · have hI : p ∈ LocalConfiguration.spatialIoc a b := ⟨hx.1, hx.2.le⟩
      have he : ((Ioo a b)ᶜ).indicator (fun _ : ℝ ↦ (1 : ℝ≥0)) p.1 = 0 :=
        indicator_of_notMem (show p.1 ∉ (Ioo a b)ᶜ from fun h ↦ h hx) _
      rw [he] at hraw
      have hlim := (NNReal.continuous_coe.tendsto _).comp hraw
      have hmul := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).mul
        (tendsto_const_nhds (x := ψ p.2))
      simpa [pastWindowTest, windowCutoff, hI, Function.comp_def] using hmul
    · have hI : p ∉ LocalConfiguration.spatialIoc a b := by
        intro h
        exact hx ⟨h.1, lt_of_le_of_ne h.2 hpb⟩
      have he : ((Ioo a b)ᶜ).indicator (fun _ : ℝ ↦ (1 : ℝ≥0)) p.1 = 1 :=
        indicator_of_mem (show p.1 ∈ (Ioo a b)ᶜ from hx) _
      rw [he] at hraw
      have hlim := (NNReal.continuous_coe.tendsto _).comp hraw
      have hmul := ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).mul
        (tendsto_const_nhds (x := ψ p.2))
      simpa [pastWindowTest, windowCutoff, hI, Function.comp_def] using hmul

end OTSelector.PointProcess
