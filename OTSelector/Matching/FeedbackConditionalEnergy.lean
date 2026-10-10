import OTSelector.Limit.FeedbackConditionalRegularityFinal
import OTSelector.Probability.ConditionalBootstrap

/-!
# Actual feedback comparisons in the geometric energy bootstrap

The comparison matchings and regularity errors come from the actual marked cell law. Geometric
lengths and thresholds remove the auxiliary cube-root parameter from the deterministic iteration.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000

variable {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2}

/-- A single coefficient covers the two actual comparison budgets. -/
noncomputable def feedbackComparisonCoefficient
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) : ℝ :=
  max P.sourceCoefficient P.rewardCoefficient

/-- Length-`L` interval centred at the middle of the conditioned zero hold. -/
def feedbackEnergyInterval (p : FeedbackCellSequence × ℝ) (h L : ℝ) : Set ℝ :=
  Icc (p.2 + h / 2 - L / 2) (p.2 + h / 2 + L / 2)

/-- Integral of the actual retained-label crossing energy in the physical interval. -/
noncomputable def feedbackWindowEnergy (p : FeedbackCellSequence × ℝ)
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1))
    (h L : ℝ) : ℝ :=
  ∫ x in feedbackEnergyInterval p h L, (feedbackLabelMatching p.1 assignment).crossingEnergy x

theorem feedbackWindowEnergy_nonneg (p : FeedbackCellSequence × ℝ)
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1)) (h L : ℝ) :
    0 ≤ feedbackWindowEnergy p assignment h L :=
  integral_nonneg fun x ↦ (feedbackLabelMatching p.1 assignment).crossingEnergy_nonneg x

/-- Every bounded physical interval is integrable whenever the actual matching has finite
crossing families at all cuts. -/
theorem integrableOn_feedbackLabelEnergy (p : FeedbackCellSequence × ℝ)
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1))
    (hfinite : ∀ cut, {i : FeedbackEventLabel p.1 1 |
      Crosses cut (feedbackCellEventPoint p.1 i).1
        (feedbackCellEventPoint p.1 (assignment i)).1}.Finite)
    (h L : ℝ) :
    IntegrableOn (feedbackLabelMatching p.1 assignment).crossingEnergy
      (feedbackEnergyInterval p h L) := by
  apply (feedbackLabelMatching p.1 assignment).integrableOn_crossingEnergy
    (feedbackLabelMatching_locallyFinite p.1 assignment)
    (hfinite (p.2 + h / 2 - L / 2 - 1)) (hfinite (p.2 + h / 2 + L / 2 + 1))
    _ measurableSet_Icc
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  constructor <;> linarith

/-- The actual quadratic cost has the uniform two-sided displacement bounds. -/
theorem feedbackLabelCost_bounds (hlam0 : 0 < lam) (hlam8 : lam < 1 / 8) (w : FeedbackCellSequence)
    (i : FeedbackEventLabel w 1) (j : FeedbackEventLabel w (-1)) :
    quadraticLowerConstant' lam *
        ((feedbackCellEventPoint w j).1 - (feedbackCellEventPoint w i).1) ^ 2 ≤
      feedbackLabelCost lam w i j ∧
    feedbackLabelCost lam w i j ≤ quadraticUpperConstant lam *
      ((feedbackCellEventPoint w j).1 - (feedbackCellEventPoint w i).1) ^ 2 := by
  have hLip : ScalarLipschitz lam (feedbackConcatenatedGraphHeight lam w) := by
    intro x y
    have h := (lipschitzWith_feedbackConcatenatedHeight lam w).dist_le_mul y x
    rw [Real.coe_toNNReal _ (abs_nonneg lam), abs_of_pos hlam0] at h
    exact h
  exact markedQuadraticCost_bounds (feedbackConcatenatedGraphHeight lam w).continuous
    hLip hlam0.le hlam8 _ _

/-- Actual window regularity and actual cell comparisons imply the deterministic one-step
energy inclusion for any locally minimizing, zero-current matching of the retained labels. -/
theorem feedbackWindowEnergy_one_step (hlam8 : lam < 1 / 8)
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (p : FeedbackCellSequence × ℝ)
    (hcomparison : ∀ left right : ℝ, FeedbackZeroCut p.1 left → FeedbackZeroCut p.1 right →
      ∀ assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1),
      (∀ cut ∈ ({left, right} : Set ℝ),
        {i : FeedbackEventLabel p.1 1 | Crosses cut (feedbackCellEventPoint p.1 i).1
          (feedbackCellEventPoint p.1 (assignment i)).1}.Finite) →
      Nonempty ((feedbackLabelMatching p.1 assignment).WindowComparison (feedbackLabelCost lam p.1)
        left right (feedbackWindowSourceCount p.1 left right)
          (feedbackWindowReward lam p.1 left right)))
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1))
    (hfinite : ∀ cut, {i : FeedbackEventLabel p.1 1 |
      Crosses cut (feedbackCellEventPoint p.1 i).1
        (feedbackCellEventPoint p.1 (assignment i)).1}.Finite)
    (hcurrent : ∀ cut, FeedbackZeroCut p.1 cut →
      (feedbackLabelMatching p.1 assignment).current cut = 0)
    (hminimal : (feedbackLabelMatching p.1 assignment).IsLocallyMinimizing
      (feedbackLabelCost lam p.1))
    {h L r theta : ℝ} (hL : 0 < L) (htheta : 0 < theta) (hthetaL : theta ≤ L)
    (hlevel : 2 * (feedbackComparisonCoefficient P / 2 + 1 +
      (3 / 2) * feedbackComparisonCoefficient P / quadraticLowerConstant' lam) ≤ r)
    (hcubic : (12 * quadraticUpperConstant lam / quadraticLowerConstant' lam) * theta ^ 3 ≤
      r * L / 2)
    (hregular : feedbackConditionalWindowRegular P h L p)
    (hlarge : r * L < feedbackWindowEnergy p assignment h L) :
    (P.zeroCoefficient / 8) * theta * (4 * L) <
      feedbackWindowEnergy p assignment h (4 * L) := by
  let Zm := {x | x ∈ Icc (p.2 + h / 2 - 2 * L) (p.2 + h / 2 - L) ∧
    FeedbackZeroCut p.1 x}
  let Zp := {x | x ∈ Icc (p.2 + h / 2 + L) (p.2 + h / 2 + 2 * L) ∧
    FeedbackZeroCut p.1 x}
  have hZm : MeasurableSet Zm := measurableSet_Icc.inter (measurableSet_feedbackZeroCut p.1)
  have hZp : MeasurableSet Zp := measurableSet_Icc.inter (measurableSet_feedbackZeroCut p.1)
  apply (feedbackLabelMatching p.1 assignment).one_step_bootstrap
    (feedbackLabelCost lam p.1) (Zminus := Zm) (Zplus := Zp)
    hL htheta hthetaL P.zeroCoefficient_pos
    (show 0 ≤ quadraticUpperConstant lam by unfold quadraticUpperConstant; positivity)
    (quadraticLowerConstant'_pos hlam0.le hlam8)
    measurableSet_Icc ⟨hZm, hZp⟩ _ _ hregular.2
    (integrableOn_feedbackLabelEnergy p assignment hfinite h (4 * L)) _ _ _ _
    (fun i j ↦ (feedbackLabelCost_bounds (hlam0 := hlam0) hlam8 p.1 i j).2)
    (fun i ↦ (feedbackLabelCost_bounds (hlam0 := hlam0) hlam8 p.1 i (assignment i)).1)
    hminimal hlevel hcubic hlarge
  · exact ⟨((measure_mono (show Zm ⊆ Icc _ _ from fun _ hx ↦ hx.1)).trans_lt
        measure_Icc_lt_top).ne,
      ((measure_mono (show Zp ⊆ Icc _ _ from fun _ hx ↦ hx.1)).trans_lt
        measure_Icc_lt_top).ne⟩
  · constructor <;> intro x hx <;> rcases hx with ⟨⟨hx1, hx2⟩, _⟩ <;>
      change _ ≤ x ∧ x ≤ _ <;> constructor <;> linarith
  · intro left hl right hr
    refine ⟨by linarith [hl.1.2, hr.1.1], ?_⟩
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    constructor <;> linarith [hl.1.2, hr.1.1]
  · intro cut hc i
    have hz : FeedbackZeroCut p.1 cut := hc.elim And.right And.right
    exact ⟨hz.2 i i.property.2.1, hz.2 (assignment i) (assignment i).property.2.1⟩
  · intro cut hc
    exact hcurrent cut (hc.elim And.right And.right)
  · intro left hl right hr
    obtain ⟨cmp⟩ := hcomparison left right hl.2 hr.2 assignment (fun cut _ ↦ hfinite cut)
    refine ⟨cmp.enlargeBounds ?_ ?_⟩
    · exact (hregular.1 left hl.1 right hr.1).1.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le)
    · exact (hregular.1 left hl.1 right hr.1).2.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le)

/-- Conditions at the initial scale persist for lengths `4^n L` and thresholds `2^n r`. -/
theorem feedbackEnergy_geometric_conditions {L r c B A : ℝ}
    (hL : 0 < L) (hr : 0 < r)
    (htheta : (16 / c) * r ≤ L) (hlevel : A ≤ r)
    (hcubic : B * ((16 / c) * r) ^ 3 ≤ r * L / 2) (n : ℕ) :
    0 < (4 : ℝ) ^ n * L ∧ 0 < (2 : ℝ) ^ n * r ∧
    (16 / c) * ((2 : ℝ) ^ n * r) ≤ (4 : ℝ) ^ n * L ∧
    A ≤ (2 : ℝ) ^ n * r ∧
    B * ((16 / c) * ((2 : ℝ) ^ n * r)) ^ 3 ≤
      ((2 : ℝ) ^ n * r) * ((4 : ℝ) ^ n * L) / 2 := by
  induction n with
  | zero => simpa using And.intro hL ⟨hr, htheta, hlevel, hcubic⟩
  | succ n ih =>
    simp only [pow_succ]
    have hL' : 0 < (4 : ℝ) ^ n * 4 * L := by positivity
    have hr' : 0 < (2 : ℝ) ^ n * 2 * r := by positivity
    refine ⟨hL', hr', ?_, ?_, ?_⟩
    · nlinarith [ih.2.2.1]
    · nlinarith [ih.2.2.2.1, ih.2.1]
    · calc
        B * ((16 / c) * (2 ^ n * 2 * r)) ^ 3 =
            8 * (B * ((16 / c) * (2 ^ n * r)) ^ 3) := by ring
        _ ≤ 8 * ((2 ^ n * r) * (4 ^ n * L) / 2) := by
          exact mul_le_mul_of_nonneg_left ih.2.2.2.2 (by norm_num)
        _ = (2 ^ n * 2 * r) * (4 ^ n * 4 * L) / 2 := by ring

/-- The next threshold is exactly the conclusion of the deterministic bootstrap. -/
theorem feedbackEnergy_geometric_threshold {c r L : ℝ} (hc : 0 < c) :
    (c / 8) * ((16 / c) * r) * (4 * L) = (2 * r) * (4 * L) := by
  field_simp [hc.ne']
  ring

end OTSelector.Matching
