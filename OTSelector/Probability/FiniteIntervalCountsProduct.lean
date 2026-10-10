import OTSelector.Probability.FiniteIntervalCountsGrid

/-!
# Interval grids for one color of an independent product

A selected group of coordinates with a common marginal is iid even when the other coordinates
have different laws.  This transports the finite interval-grid estimate without discarding any
of the other coordinates from the sample space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.FiniteIntervalCounts

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Real count in a specified finite group of labels. -/
noncomputable def groupCount (J : Finset ι) (X : ι → Ω) (A : Set Ω) : ℝ :=
  ∑ i ∈ J, RelativeVC.indicatorReal A (X i)

/-- Integer-grid lower-count certificate for a group in a larger sample. -/
def groupGridGood (N : ℕ) (J : Finset ι) (phase : Ω → ℝ) (lo hi c r : ℝ)
    (sample : ι → Ω) : Prop :=
  ∀ a b : Fin (N + 1), lo ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
    (b.val : ℝ) ≤ hi → c * ((b.val : ℝ) - a.val) - r ≤
      groupCount J sample (phase ⁻¹' Ioo (a.val : ℝ) (b.val : ℝ))

private noncomputable def groupIndex (J : Finset ι) : Fin J.card ↪ ι :=
  ⟨fun k ↦ ((Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm k).val,
    Subtype.val_injective.comp (Equiv.injective _)⟩

omit [Fintype ι] in
private theorem groupIndex_mem (J : Finset ι) (k : Fin J.card) : groupIndex J k ∈ J :=
  ((Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm k).property

omit [MeasurableSpace Ω] [Fintype ι] in
private theorem count_groupIndex (J : Finset ι) (sample : ι → Ω) (A : Set Ω) :
    count (fun k ↦ sample (groupIndex J k)) A = groupCount J sample A := by
  have h := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm.sum_comp
    (fun i : J ↦ RelativeVC.indicatorReal A (sample i))
  apply h.trans
  simpa only [Finset.attach_eq_univ, groupCount] using
    Finset.sum_attach J (fun i ↦ RelativeVC.indicatorReal A (sample i))

omit [MeasurableSpace Ω] [Fintype ι] in
private theorem gridGood_groupIndex (N : ℕ) (J : Finset ι) (phase : Ω → ℝ)
    (lo hi c r : ℝ) (sample : ι → Ω) :
    gridGood N phase lo hi c r (fun k ↦ sample (groupIndex J k)) ↔
      groupGridGood N J phase lo hi c r sample := by
  unfold gridGood groupGridGood
  simp only [count_comp, count_groupIndex]

/-- Uniform group interval counts inherited from the independent product factors. -/
theorem measure_not_groupGridGood_pi_le
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (J : Finset ι)
    (hPQ : ∀ i ∈ J, P i = Q) (N : ℕ) {phase : Ω → ℝ} (hphase : Measurable phase)
    (lo hi c : ℝ) {r : ℝ} (hr : 0 < r)
    (hmass : ∀ a b : Fin (N + 1), lo ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
      (b.val : ℝ) ≤ hi → 2 * c * ((b.val : ℝ) - a.val) ≤
        (J.card : ℝ) * Q.real (phase ⁻¹' Ioo (a.val : ℝ) (b.val : ℝ))) :
    Measure.pi P {sample | ¬groupGridGood N J phase lo hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  have hindep : iIndepFun (fun i (sample : ι → Ω) ↦ sample i) (Measure.pi P) :=
    iIndepFun_pi fun _ ↦ measurable_id.aemeasurable
  have hselected := hindep.precomp (groupIndex J).injective
  have hlaw : ∀ k : Fin J.card,
      (Measure.pi P).map (fun sample : ι → Ω ↦ sample (groupIndex J k)) = Q := by
    intro k
    rw [(measurePreserving_eval P (groupIndex J k)).map_eq]
    exact hPQ _ (groupIndex_mem J k)
  have hbound := measure_not_gridGood_le Q
    (fun k ↦ measurable_pi_apply (groupIndex J k)) hselected hlaw N hphase lo hi c hr hmass
  simpa only [gridGood_groupIndex] using hbound

omit [MeasurableSpace Ω] [Fintype ι] in
/-- The same group certificate controls every open interval, including samples with ties. -/
theorem groupCount_Ioo_lower_of_groupGridGood
    {N : ℕ} {J : Finset ι} {phase : Ω → ℝ} {lo hi c r : ℝ} {sample : ι → Ω}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hlo : 0 ≤ lo) (hhi : hi ≤ N)
    (hgood : groupGridGood N J phase lo hi c r sample)
    {s t : ℝ} (hls : lo ≤ s) (hst : s ≤ t) (hth : t ≤ hi) :
    c * (t - s) - (r + 2 * c) ≤ groupCount J sample (phase ⁻¹' Ioo s t) := by
  have h := count_Ioo_lower_of_gridGood hc hr hlo hhi
    ((gridGood_groupIndex N J phase lo hi c r sample).mpr hgood) hls hst hth
  simpa only [count_comp, count_groupIndex] using h

end OTSelector.FiniteIntervalCounts
