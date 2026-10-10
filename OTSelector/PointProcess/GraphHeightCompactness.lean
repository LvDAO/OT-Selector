import OTSelector.PointProcess.FeedbackPath
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Compact sets of normalized feedback graph heights

The graphs used by the feedback construction vanish at the root and share a deterministic
Lipschitz constant.  This file proves that their entire class is compact in the compact-open
topology already used by `GraphHeight`.  The proof uses pointwise compact containment and the
Arzelà--Ascoli theorem; no global bound on graph heights is required.

Re-rooting is jointly continuous in the displacement and graph, and preserves the Lipschitz
class.  These are deterministic ingredients for spatial averaging and environment tightness.
-/

open Filter Function Set Topology
open scoped NNReal

namespace OTSelector.PointProcess.GraphHeight

/-- All normalized graph heights with a fixed Lipschitz bound. -/
def lipschitzSet (K : ℝ≥0) : Set GraphHeight :=
  {g | LipschitzWith K g}

/-- The graph-height Lipschitz condition is closed in compact-open topology. -/
theorem isClosed_lipschitzSet (K : ℝ≥0) : IsClosed (lipschitzSet K) := by
  exact (isClosed_setOfPred_lipschitzWith K).preimage
    (continuous_pi fun x ↦ continuous_apply x)

private theorem isCompact_normalized_lipschitz_functions (K : ℝ≥0) :
    IsCompact {f : ℝ → ℝ | LipschitzWith K f ∧ f 0 = 0} := by
  have hclosed : IsClosed {f : ℝ → ℝ | LipschitzWith K f ∧ f 0 = 0} :=
    (isClosed_setOfPred_lipschitzWith K).inter
      (isClosed_eq (_root_.continuous_apply 0) continuous_const)
  have hbox : IsCompact (univ.pi (fun x : ℝ ↦
      Icc (-((K : ℝ) * |x|)) ((K : ℝ) * |x|))) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro f hf x hx
  have hbound : |f x| ≤ (K : ℝ) * |x| := by
    simpa only [hf.2, Real.dist_eq, sub_zero] using hf.1.dist_le_mul x 0
  exact abs_le.mp hbound

/-- The normalized graph heights with Lipschitz constant at most `K` form a compact set. -/
theorem isCompact_lipschitzSet (K : ℝ≥0) : IsCompact (lipschitzSet K) := by
  let S : Set C(ℝ, ℝ) := {g | LipschitzWith K g ∧ g 0 = 0}
  have himage : ContinuousMap.toFun '' S =
      {f : ℝ → ℝ | LipschitzWith K f ∧ f 0 = 0} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
  have hequi : Equicontinuous ((↑) : S → ℝ → ℝ) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ (K : ℝ) * r)
      (by simpa using
        (show Continuous (fun r : ℝ ↦ (K : ℝ) * r) from
          continuous_const.mul continuous_id).tendsto 0)
    intro x y g
    exact g.property.1.dist_le_mul x y
  have hcompact : IsCompact S :=
    ArzelaAscoli.isCompact_of_equicontinuous S
      (himage.symm ▸ isCompact_normalized_lipschitz_functions K) hequi
  have hpreimage := ContinuousMapZero.isClosedEmbedding_toContinuousMap.isCompact_preimage hcompact
  change IsCompact {g : GraphHeight | LipschitzWith K g ∧ g 0 = 0} at hpreimage
  simpa only [lipschitzSet, apply_zero, and_true] using hpreimage

/-- Re-rooting is continuous jointly in the root displacement and the normalized graph. -/
theorem continuous_uncurry_reroot :
    Continuous (fun p : ℝ × GraphHeight ↦ reroot p.1 p.2) := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hshift : Continuous (fun p : (ℝ × GraphHeight) × ℝ ↦ p.1.2 (p.2 + p.1.1)) :=
    continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.add (continuous_fst.comp continuous_fst)))
  have hbase : Continuous (fun p : (ℝ × GraphHeight) × ℝ ↦ p.1.2 p.1.1) :=
    continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk (continuous_fst.comp continuous_fst))
  exact hshift.sub hbase

/-- Translation is continuous jointly in the displacement and graph. -/
theorem continuous_uncurry_translate :
    Continuous (fun p : ℝ × GraphHeight ↦ translate p.1 p.2) :=
  continuous_uncurry_reroot.comp (continuous_fst.neg.prodMk continuous_snd)

/-- Re-rooting preserves a graph's deterministic Lipschitz bound. -/
theorem lipschitzWith_reroot {K : ℝ≥0} {g : GraphHeight}
    (hg : LipschitzWith K g) (a : ℝ) : LipschitzWith K (reroot a g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [reroot_apply, dist_sub_right, dist_add_right] using hg.dist_le_mul (x + a) (y + a)

/-- Every spatial re-rooting maps the compact Lipschitz class into itself. -/
theorem reroot_mem_lipschitzSet {K : ℝ≥0} {g : GraphHeight}
    (hg : g ∈ lipschitzSet K) (a : ℝ) : reroot a g ∈ lipschitzSet K :=
  lipschitzWith_reroot hg a

end OTSelector.PointProcess.GraphHeight
