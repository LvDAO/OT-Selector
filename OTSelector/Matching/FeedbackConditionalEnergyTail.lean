import OTSelector.Matching.FeedbackConditionalEnergy

/-!
# Conditional energy tails from the actual environmental law

An arbitrary joint law may attach a locally minimizing matching to the actual stationary roof
configuration. The environmental marginal supplies all errors. The unconditional linear energy
mean, after fixed conditioning, removes the terminal event in the geometric bootstrap.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1000000

variable {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2}

/-- The structural matching hypotheses used by finite surgery; no energy bound is included. -/
structure FeedbackMatchingAdmissible (p : FeedbackCellSequence × ℝ)
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1)) (lam : ℝ) : Prop where
  finite_crossings : ∀ cut, {i : FeedbackEventLabel p.1 1 |
    Crosses cut (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (assignment i)).1}.Finite
  current_zero : ∀ cut, FeedbackZeroCut p.1 cut →
    (feedbackLabelMatching p.1 assignment).current cut = 0
  locally_minimizing : (feedbackLabelMatching p.1 assignment).IsLocallyMinimizing
    (feedbackLabelCost lam p.1)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Conditioning a joint law on the actual residual band preserves exactly the proved
conditional roof marginal. -/
theorem feedbackConditionalRoofLaw_map_joint (μ : Measure Ω)
    {p : Ω → FeedbackCellSequence × ℝ} (hp : Measurable p)
    (hmap : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam) (h : ℝ) :
    (cond μ (p ⁻¹' feedbackRoofHoldBand lam h)).map p =
      feedbackConditionalRoofLaw lam hlam0 hlam h := by
  have hA := measurableSet_feedbackRoofHoldBand lam h
  have hmass : μ (p ⁻¹' feedbackRoofHoldBand lam h) =
      feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h) := by
    rw [← hmap, Measure.map_apply hp hA]
  rw [ProbabilityTheory.cond, Measure.map_smul, ← Measure.restrict_map hp hA, hmap, hmass]
  rfl

/-- Under the true stationary roof marginal, the energy tail follows from actual cell
regularity. The only moment input is the unconditional linear energy mean. -/
theorem feedbackConditionalEnergy_tail_le (hlam8 : lam < 1 / 8)
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : Ω → FeedbackCellSequence × ℝ} (hp : Measurable p)
    (hmap : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam)
    (assignment : (ω : Ω) → FeedbackEventLabel (p ω).1 1 ≃ FeedbackEventLabel (p ω).1 (-1))
    (hadmissible : ∀ᵐ ω ∂μ, FeedbackMatchingAdmissible (p ω) (assignment ω) lam)
    {h L r Cenergy : ℝ} (hh : 0 ≤ h) (hL : 0 < L) (hr : 0 < r)
    (hLmesh : 2 * P.mesh ≤ L) (hLroof : 32 * feedbackCellMean lam hlam0 hlam ≤ L)
    (hLhold : 16 * (h + 1) ≤ L)
    (htheta : (16 / P.zeroCoefficient) * r ≤ L)
    (hlevel : 2 * (feedbackComparisonCoefficient P / 2 + 1 +
      (3 / 2) * feedbackComparisonCoefficient P / quadraticLowerConstant' lam) ≤ r)
    (hcubic : (12 * quadraticUpperConstant lam / quadraticLowerConstant' lam) *
      ((16 / P.zeroCoefficient) * r) ^ 3 ≤ r * L / 2)
    (henergyInt : ∀ R > 0,
      Integrable (fun ω ↦ feedbackWindowEnergy (p ω) (assignment ω) h R) μ)
    (hmean : ∀ R > 0,
      (∫ ω, feedbackWindowEnergy (p ω) (assignment ω) h R ∂μ) ≤ Cenergy * R) :
    (cond μ (p ⁻¹' feedbackRoofHoldBand lam h)).real
      {ω | r * L < feedbackWindowEnergy (p ω) (assignment ω) h L} ≤
        4 * P.tailCoefficient / (3 * L) := by
  let A := p ⁻¹' feedbackRoofHoldBand lam h
  let ν := cond μ A
  have hA : MeasurableSet A := hp (measurableSet_feedbackRoofHoldBand lam h)
  have hA0 : μ A ≠ 0 := by
    have hmass := congrArg (fun m : Measure (FeedbackCellSequence × ℝ) ↦
      m (feedbackRoofHoldBand lam h)) hmap
    rw [Measure.map_apply hp (measurableSet_feedbackRoofHoldBand lam h)] at hmass
    exact hmass.trans_ne (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh).ne'
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hA0
  have hνmap : ν.map p = feedbackConditionalRoofLaw lam hlam0 hlam h :=
    feedbackConditionalRoofLaw_map_joint μ hp hmap h
  let lengths : ℕ → ℝ := fun n ↦ (4 : ℝ) ^ n * L
  let levels : ℕ → ℝ := fun n ↦ (2 : ℝ) ^ n * r
  let energy : ℕ → Ω → ℝ := fun n ω ↦
    feedbackWindowEnergy (p ω) (assignment ω) h (lengths n) / lengths n
  let bad : ℕ → Set Ω := fun n ↦ {ω |
    levels n * lengths n < feedbackWindowEnergy (p ω) (assignment ω) h (lengths n)}
  let error : ℕ → Set Ω := fun n ↦
    {ω | ¬feedbackConditionalWindowRegular P h (lengths n) (p ω)}
  have hconditions (n : ℕ) := feedbackEnergy_geometric_conditions hL hr htheta hlevel hcubic n
  have hlen (n : ℕ) : 0 < lengths n := (hconditions n).1
  have hlower (n : ℕ) : L ≤ lengths n := by
    have hn : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn hL.le
  have henergy0 (n : ℕ) : 0 ≤ᵐ[ν] energy n := ae_of_all _ fun ω ↦
    div_nonneg (feedbackWindowEnergy_nonneg _ _ _ _) (hlen n).le
  have henergyint (n : ℕ) : Integrable (energy n) ν :=
    (((henergyInt (lengths n) (hlen n)).div_const (lengths n)).mono_measure
      μ.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hA0)
  have henergymean (n : ℕ) : ∫ ω, energy n ω ∂ν ≤ (μ A).toReal⁻¹ * Cenergy := by
    rw [show ν = (μ A)⁻¹ • μ.restrict A from rfl, integral_smul_measure]
    simp only [ENNReal.toReal_inv, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    calc
      (∫ ω, energy n ω ∂μ.restrict A) ≤ ∫ ω, energy n ω ∂μ :=
        integral_mono_measure μ.restrict_le_self
          (ae_of_all _ fun ω ↦ div_nonneg (feedbackWindowEnergy_nonneg _ _ _ _) (hlen n).le)
          ((henergyInt _ (hlen n)).div_const _)
      _ = (∫ ω, feedbackWindowEnergy (p ω) (assignment ω) h (lengths n) ∂μ) /
          lengths n := integral_div _ _
      _ ≤ Cenergy := (div_le_iff₀ (hlen n)).mpr (hmean _ (hlen n))
  have hcomp : ∀ᵐ ω ∂ν, ∀ left right : ℝ,
      FeedbackZeroCut (p ω).1 left → FeedbackZeroCut (p ω).1 right →
      ∀ a : FeedbackEventLabel (p ω).1 1 ≃ FeedbackEventLabel (p ω).1 (-1),
      (∀ cut ∈ ({left, right} : Set ℝ),
        {i : FeedbackEventLabel (p ω).1 1 | Crosses cut (feedbackCellEventPoint (p ω).1 i).1
          (feedbackCellEventPoint (p ω).1 (a i)).1}.Finite) →
      Nonempty ((feedbackLabelMatching (p ω).1 a).WindowComparison (feedbackLabelCost lam (p ω).1)
        left right (feedbackWindowSourceCount (p ω).1 left right)
          (feedbackWindowReward lam (p ω).1 left right)) := by
    have hb := feedbackConditionalRoofLaw_ae_base hlam0 hlam h
      (feedbackCellBase_windowComparison hlam0 hlam8)
    rw [← hνmap] at hb
    exact ae_of_ae_map hp.aemeasurable hb
  have hstep (n : ℕ) : ∀ᵐ ω ∂ν, ω ∈ bad n → ω ∈ bad (n + 1) ∪ error n := by
    filter_upwards [hcomp, cond_absolutelyContinuous.ae_le hadmissible] with ω hc ha
    intro hbad
    by_cases hg : feedbackConditionalWindowRegular P h (lengths n) (p ω)
    · left
      have htpos : 0 < (16 / P.zeroCoefficient) * levels n :=
        mul_pos (div_pos (by norm_num) P.zeroCoefficient_pos) (hconditions n).2.1
      have hs := feedbackWindowEnergy_one_step hlam8 P (p ω) hc (assignment ω)
        ha.finite_crossings ha.current_zero ha.locally_minimizing (hlen n) htpos
        (hconditions n).2.2.1 (hconditions n).2.2.2.1 (hconditions n).2.2.2.2 hg hbad
      rw [feedbackEnergy_geometric_threshold P.zeroCoefficient_pos] at hs
      simpa only [bad, levels, lengths, pow_succ, Set.mem_ofPred_eq,
        mul_assoc, mul_left_comm, mul_comm] using hs
    · exact Or.inr hg
  have herror (n : ℕ) : ν.real (error n) ≤ P.tailCoefficient / lengths n := by
    have hmeasure := Measure.le_map_apply (μ := ν) hp.aemeasurable
      {p | ¬feedbackConditionalWindowRegular P h (lengths n) p}
    rw [hνmap] at hmeasure
    have : IsProbabilityMeasure (feedbackConditionalRoofLaw lam hlam0 hlam h) :=
      feedbackConditionalRoofLaw_isProbability hlam0 hlam h hh
    exact (ENNReal.toReal_mono (measure_ne_top _ _) hmeasure).trans
      (feedbackConditionalWindowRegular_bad_le P hh (hLmesh.trans (hlower n))
        (hLroof.trans (hlower n)) (hLhold.trans (hlower n)))
  have hsum := hasSum_feedbackConditionalWindow_errors P L
  have htail := OTSelector.Probability.measure_bad_le_tsum_of_energy_bootstrap ν energy bad error
    levels (fun n ↦ P.tailCoefficient / lengths n) ((μ A).toReal⁻¹ * Cenergy)
    henergy0 henergyint henergymean (fun n ↦ (hconditions n).2.1)
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hr)
    (fun n ω hω ↦ ((lt_div_iff₀ (hlen n)).mpr hω).le) hstep herror hsum.summable
  rw [hsum.tsum_eq] at htail
  simpa only [bad, levels, lengths, pow_zero, one_mul] using htail

end OTSelector.Matching
