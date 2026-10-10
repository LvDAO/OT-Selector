import OTSelector.Basic.FiniteSamplePointLaw
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Instances.Real.Lemmas

open MeasureTheory ProbabilityTheory Set
open scoped Set.Notation

namespace OTSelector

theorem unitUniform_isOpenPosMeasure :
    Measure.IsOpenPosMeasure (unitUniform : Measure UnitMark) := by
  change Measure.IsOpenPosMeasure (volume : Measure UnitMark)
  constructor
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨V, hV, hVU⟩ := IsOpen.image_val hU
  have hxV : (x : ℝ) ∈ V := by
    have hxV' : (x : ℝ) ∈ V ∩ UnitMark := by
      rw [← hVU]
      exact ⟨x, hxU, rfl⟩
    exact hxV'.1
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hε) (by norm_num)
  have hδe : δ < ε := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδhalf : δ ≤ (1 / 2 : ℝ) := by
    exact min_le_right _ _
  have hA : ∃ A : Set ℝ, 0 < volume A ∧ A ⊆ Subtype.val '' U := by
    by_cases hxhalf : (x : ℝ) ≤ 1 / 2
    · let A : Set ℝ := Icc (x : ℝ) ((x : ℝ) + δ)
      have hAvol : 0 < volume A := by
        rw [show A = Icc (x : ℝ) ((x : ℝ) + δ) by rfl, Real.volume_Icc]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      have hAsub : A ⊆ Subtype.val '' U := by
        intro y hy
        have hyc : y ∈ V := by
          apply hεV
          rw [Metric.mem_ball, Real.dist_eq]
          have hyx : 0 ≤ y - (x : ℝ) := by linarith [hy.1]
          rw [abs_of_nonneg hyx]
          exact lt_of_le_of_lt (by linarith [hy.2]) hδe
        have hyI : y ∈ Icc (0 : ℝ) 1 := by
          constructor
          · exact le_trans (x.property.1) hy.1
          · linarith [hy.2, hxhalf, hδhalf]
        rw [hVU]
        exact ⟨hyc, hyI⟩
      exact ⟨A, hAvol, hAsub⟩
    · let A : Set ℝ := Icc ((x : ℝ) - δ) (x : ℝ)
      have hAvol : 0 < volume A := by
        rw [show A = Icc ((x : ℝ) - δ) (x : ℝ) by rfl, Real.volume_Icc]
        exact ENNReal.ofReal_pos.mpr (by linarith)
      have hAsub : A ⊆ Subtype.val '' U := by
        intro y hy
        have hyc : y ∈ V := by
          apply hεV
          rw [Metric.mem_ball, Real.dist_eq]
          have hyx : 0 ≤ (x : ℝ) - y := by linarith [hy.2]
          rw [abs_of_nonpos (by linarith)]
          exact lt_of_le_of_lt (by linarith [hy.1]) hδe
        have hyI : y ∈ Icc (0 : ℝ) 1 := by
          constructor
          · linarith [hy.1, hxhalf, hδhalf]
          · exact le_trans hy.2 x.property.2
        rw [hVU]
        exact ⟨hyc, hyI⟩
      exact ⟨A, hAvol, hAsub⟩
  obtain ⟨A, hAvol, hAsub⟩ := hA
  have hle : volume A ≤ volume (Subtype.val '' U) := measure_mono hAsub
  rw [unitInterval.volume_apply]
  exact ne_of_gt (lt_of_lt_of_le hAvol hle)

theorem unitSquareUniform_isOpenPosMeasure :
    Measure.IsOpenPosMeasure (unitSquareUniform : Measure MarkedHeight) := by
  let _ := unitUniform_isOpenPosMeasure
  simpa [unitSquareUniform_toMeasure] using
    (inferInstance : Measure.IsOpenPosMeasure
      ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)))

end OTSelector
