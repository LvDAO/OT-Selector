import OTSelector.Matching.DisagreementMassTransport

/-!+# A common empty cut determines both locally minimizing matchings

Finite partner orbits are excluded by the actual no-tie property. The proved
finite-crossing end alternatives and the one-sided-orbit mass-transport exclusion
then force every differing orbit to cross every cut. A common empty cut is thus
incompatible with a difference.
-/

open Function Set Filter
open scoped Classical

namespace OTSelector.Matching.SpatialMatching

open OTSelector.Limit OTSelector.PointProcess

variable {S T : Type*}

/-- Deterministic assembly of the finite-cycle, spatial-end, and mass-transport
conclusions. The only orbit exclusion premise is the precise almost-sure conclusion
already proved by `ae_not_oneSidedAnchoredOrbit`. -/
theorem assignment_eq_of_no_ties_of_common_empty_cut
    (M₁ M₂ : SpatialMatching S T) {e : FeedbackEnvironment} (hnotie : FeedbackNoFiniteTies e)
    (source : S → MatchingPoint) (target : T → MatchingPoint)
    (hsource : Injective source) (htarget : Injective target)
    (hsa : ∀ i, LocalConfiguration.countingMeasure e.source {source i} ≠ 0)
    (hta : ∀ i, LocalConfiguration.countingMeasure e.target {target i} ≠ 0)
    (hmin₁ : M₁.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    (hmin₂ : M₂.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target)
    (hinj : Injective M₁.source) (hloc₁ : M₁.LocallyFinite) (hloc₂ : M₂.LocallyFinite)
    (hcross₁ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₁.source i) (M₁.target (M₁.assignment i))}.Finite)
    (hcross₂ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₂.source i) (M₂.target (M₂.assignment i))}.Finite)
    (hnoanchor : ∀ i, ¬ LowerAnchoredOrbit (M₁.partnerPermutation M₂) M₁.source i ∧
      ¬ LowerAnchoredOrbit (M₁.partnerPermutation M₂) (fun j ↦ -M₁.source j) i)
    (cut : ℝ) (hsne : ∀ i, M₁.source i ≠ cut) (htne : ∀ j, M₁.target j ≠ cut)
    (hcut₁ : ∀ i, ¬ Crosses cut (M₁.source i) (M₁.target (M₁.assignment i)))
    (hcut₂ : ∀ i, ¬ Crosses cut (M₂.source i) (M₂.target (M₂.assignment i))) :
    M₁.assignment = M₂.assignment := by
  ext i
  by_contra hi
  have hinfinite := infinite_partnerOrbit_of_no_ties M₁ M₂ hnotie source target
    hsource htarget hsa hta hmin₁ hmin₂ hi
  have hz := zpow_apply_injective_of_infinite_sameCycle (M₁.partnerPermutation M₂) i hinfinite
  have hf := partner_forward_tendsto_infinity M₁ M₂ hs ht hloc₁ hloc₂ hcross₁ hcross₂ i hinfinite
  have hb := partner_backward_tendsto_infinity M₁ M₂ hs ht hloc₁ hloc₂ hcross₁ hcross₂ i hinfinite
  have hop := not_opposite_ends_of_empty_cut M₁ M₂ hs ht cut hsne htne hcut₁ hcut₂ i
  rcases hf with hft | hfb <;> rcases hb with hbt | hbb
  · exact (hnoanchor i).1 ⟨hinj.comp hz,
      partner_orbit_bddBelow_of_two_right_ends _ _ _ hft hbt⟩
  · exact hop (Or.inl ⟨hft, hbb⟩)
  · exact hop (Or.inr ⟨hfb, hbt⟩)
  · apply (hnoanchor i).2
    refine ⟨neg_injective.comp (hinj.comp hz), ?_⟩
    obtain ⟨a, ha⟩ := partner_orbit_bddAbove_of_two_left_ends _ _ _ hfb hbb
    refine ⟨-a, ?_⟩
    rintro x ⟨n, rfl⟩
    exact neg_le_neg (ha ⟨n, rfl⟩)

end OTSelector.Matching.SpatialMatching
