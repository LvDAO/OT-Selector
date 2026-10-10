import OTSelector.Matching.FeedbackSceneJoiningFlow

/-!
# The actual translation on a measurable full-measure scene support

The supported law uses only valid scene assignments. Translation agrees almost surely with the
actual spatial translation; the harmless fallback keeps it defined on every point of the support.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

/-- The actual translation restricted to a support, fixing a point when its image is outside. -/
noncomputable def feedbackSceneSupportFlow (S : Set FeedbackSceneRoofPoint) (t : ℝ) (q : S) : S :=
  if h : feedbackSceneRoofFlow t q.val ∈ S then ⟨feedbackSceneRoofFlow t q.val, h⟩ else q

@[fun_prop]
theorem measurable_feedbackSceneSupportFlow {S : Set FeedbackSceneRoofPoint}
    (hS : MeasurableSet S) (t : ℝ) : Measurable (feedbackSceneSupportFlow S t) := by
  let U : Set S := {q | feedbackSceneRoofFlow t q.val ∈ S}
  have hU : MeasurableSet U := hS.preimage
    ((measurable_feedbackSceneRoofFlow t).comp measurable_subtype_coe)
  let f : U → S := fun q ↦ ⟨feedbackSceneRoofFlow t q.val.val, q.property⟩
  let g : (Uᶜ : Set S) → S := Subtype.val
  have hf : Measurable f := ((measurable_feedbackSceneRoofFlow t).comp
    (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk
  have hg : Measurable g := measurable_subtype_coe
  have he : feedbackSceneSupportFlow S t =
      (fun q ↦ if h : q ∈ U then f ⟨q, h⟩ else g ⟨q, h⟩) := by
    funext q
    by_cases hq : feedbackSceneRoofFlow t q.val ∈ S
    · simp only [feedbackSceneSupportFlow, U, mem_ofPred_eq, hq, dite_true, f]
    · simp only [feedbackSceneSupportFlow, U, mem_ofPred_eq, hq, dite_false, g]
  rw [he]
  exact hf.dite hg hU

/-- On every full-measure support the restricted map is almost surely the actual translation. -/
theorem feedbackSceneSupportFlow_ae {S : Set FeedbackSceneRoofPoint}
    (hS : MeasurableSet S) (μ : Measure FeedbackSceneRoofPoint)
    (hfull : ∀ᵐ q ∂μ, q ∈ S) (t : ℝ)
    (ht : MeasurePreserving (feedbackSceneRoofFlow t) μ μ) :
    (fun q : S ↦ (feedbackSceneSupportFlow S t q).val) =ᵐ[μ.comap Subtype.val]
      (fun q ↦ feedbackSceneRoofFlow t q.val) := by
  have hmap : (μ.comap (Subtype.val : S → _)).map Subtype.val = μ := by
    rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]
  have hh := ht.quasiMeasurePreserving.ae hfull
  rw [← hmap] at hh
  filter_upwards [ae_of_ae_map measurable_subtype_coe.aemeasurable hh] with q hq
  simp only [feedbackSceneSupportFlow, dite_eq_left hq]

/-- Passing to the actual measurable support preserves stationarity of the joined law. -/
theorem measurePreserving_feedbackSceneSupportFlow {S : Set FeedbackSceneRoofPoint}
    (hS : MeasurableSet S) (μ : Measure FeedbackSceneRoofPoint)
    (hfull : ∀ᵐ q ∂μ, q ∈ S) (t : ℝ)
    (ht : MeasurePreserving (feedbackSceneRoofFlow t) μ μ) :
    MeasurePreserving (feedbackSceneSupportFlow S t) (μ.comap Subtype.val)
      (μ.comap Subtype.val) := by
  have hf := measurable_feedbackSceneSupportFlow hS t
  refine ⟨hf, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hS).map_injective
  have hmap : (μ.comap (Subtype.val : S → _)).map Subtype.val = μ := by
    rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]
  rw [Measure.map_map measurable_subtype_coe hf]
  calc
    _ = (μ.comap (Subtype.val : S → _)).map (fun q ↦ feedbackSceneRoofFlow t q.val) :=
      Measure.map_congr (feedbackSceneSupportFlow_ae hS μ hfull t ht)
    _ = ((μ.comap (Subtype.val : S → _)).map Subtype.val).map (feedbackSceneRoofFlow t) :=
      (Measure.map_map ht.measurable measurable_subtype_coe).symm
    _ = _ := by rw [hmap, ht.map_eq]

end OTSelector.Matching
