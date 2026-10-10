import OTSelector.Probability.FiniteIntervalCounts

/-!
# Integer grids for uniform lower interval counts

An inward rounding of both endpoints loses at most two units of length.  A finite measurable
grid event therefore controls every open interval, with no assumption about ties in the sample.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.FiniteIntervalCounts

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

omit [MeasurableSpace Ω] in
theorem count_mono {m : ℕ} (X : Fin m → Ω) {A B : Set Ω} (hAB : A ⊆ B) :
    count X A ≤ count X B := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hA : X i ∈ A
  · simp [RelativeVC.indicatorReal, hA, hAB hA]
  · simp only [RelativeVC.indicatorReal, indicator_of_notMem hA]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

omit [MeasurableSpace Ω] in
theorem count_comp {m : ℕ} (X : Fin m → Ω) (phase : Ω → ℝ) (A : Set ℝ) :
    count (fun i ↦ phase (X i)) A = count X (phase ⁻¹' A) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  simp [RelativeVC.indicatorReal, Set.indicator_apply]

/-- The finite grid certificate; all inequalities concern open intervals. -/
def gridGood (N : ℕ) {m : ℕ} (phase : Ω → ℝ) (lo hi c r : ℝ)
    (sample : Fin m → Ω) : Prop :=
  ∀ a b : Fin (N + 1), lo ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
    (b.val : ℝ) ≤ hi →
    c * ((b.val : ℝ) - a.val) - r ≤
      count (fun i ↦ phase (sample i)) (Ioo (a.val : ℝ) (b.val : ℝ))

theorem measurableSet_gridGood (N m : ℕ) {phase : Ω → ℝ}
    (hphase : Measurable phase) (lo hi c r : ℝ) :
    MeasurableSet {sample : Fin m → Ω | gridGood N phase lo hi c r sample} := by
  simp only [gridGood, ofPred_forall]
  refine MeasurableSet.iInter fun (a : Fin (N + 1)) ↦
    MeasurableSet.iInter fun (b : Fin (N + 1)) ↦ ?_
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le measurable_const
    (count_measurable (fun i ↦ hphase.comp (measurable_pi_apply i)) measurableSet_Ioo)

omit [MeasurableSpace Ω] in
/-- Every open interval is controlled by the integer grid, with an extra `2*c` rounding error. -/
theorem count_Ioo_lower_of_gridGood {N m : ℕ} {phase : Ω → ℝ}
    {lo hi c r : ℝ} {sample : Fin m → Ω}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hlo : 0 ≤ lo) (hhi : hi ≤ N)
    (hgood : gridGood N phase lo hi c r sample)
    {s t : ℝ} (hls : lo ≤ s) (hst : s ≤ t) (hth : t ≤ hi) :
    c * (t - s) - (r + 2 * c) ≤ count (fun i ↦ phase (sample i)) (Ioo s t) := by
  have hs0 : 0 ≤ s := hlo.trans hls
  have ht0 : 0 ≤ t := hs0.trans hst
  have hsN : s ≤ N := hst.trans (hth.trans hhi)
  have htN : t ≤ N := hth.trans hhi
  by_cases hshort : t - s ≤ 2
  · have hmul := mul_le_mul_of_nonneg_left hshort hc
    exact (by linarith : c * (t - s) - (r + 2 * c) ≤ 0).trans
      (count_nonneg _ _)
  let a : Fin (N + 1) := ⟨⌈s⌉₊, Nat.lt_succ_of_le (Nat.ceil_le.mpr hsN)⟩
  let b : Fin (N + 1) := ⟨⌊t⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le htN)⟩
  have hsa : s ≤ (a.val : ℝ) := Nat.le_ceil s
  have has : (a.val : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  have hbt : (b.val : ℝ) ≤ t := Nat.floor_le ht0
  have htb : t - 1 < (b.val : ℝ) := Nat.sub_one_lt_floor t
  have hab : (a.val : ℝ) ≤ b.val := by linarith
  have hgrid := hgood a b (hls.trans hsa) hab (hbt.trans hth)
  have hsub : Ioo (a.val : ℝ) (b.val : ℝ) ⊆ Ioo s t := by
    intro x hx
    exact ⟨hsa.trans_lt hx.1, hx.2.trans_le hbt⟩
  have hmul := mul_le_mul_of_nonneg_left
    (show t - s - 2 ≤ (b.val : ℝ) - a.val by linarith) hc
  exact (by linarith : c * (t - s) - (r + 2 * c) ≤
      c * ((b.val : ℝ) - a.val) - r).trans
    (hgrid.trans (count_mono _ hsub))

/-- A deterministic lower mass bound on the grid gives a simultaneous interval certificate. -/
theorem measure_not_gridGood_le
    (P : Measure Ω) [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {m : ℕ} {X : Fin m → Ξ → Ω} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = P)
    (N : ℕ) {phase : Ω → ℝ} (hphase : Measurable phase) (lo hi c : ℝ)
    {r : ℝ} (hr : 0 < r)
    (hmass : ∀ a b : Fin (N + 1), lo ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
      (b.val : ℝ) ≤ hi →
      2 * c * ((b.val : ℝ) - a.val) ≤
        (m : ℝ) * P.real (phase ⁻¹' Ioo (a.val : ℝ) (b.val : ℝ))) :
    μ {ω | ¬gridGood N phase lo hi c r (fun i ↦ X i ω)} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  let A : Fin (N + 1) × Fin (N + 1) → Set Ω :=
    fun j ↦ phase ⁻¹' Ioo (j.1.val : ℝ) (j.2.val : ℝ)
  have hA : ∀ j, MeasurableSet (A j) := fun _ ↦ hphase measurableSet_Ioo
  have hbound := measure_exists_count_lt_half_mean_sub_le P hX hindep hlaw A hA hr
  have hsub : {ω | ¬gridGood N phase lo hi c r (fun i ↦ X i ω)} ⊆
      {ω | ∃ j, count (fun i ↦ X i ω) (A j) < (m : ℝ) * P.real (A j) / 2 - r} := by
    intro ω hω
    simp only [gridGood, not_forall] at hω
    obtain ⟨a, b, hla, hab, hbh, hbad⟩ := hω
    refine ⟨(a, b), ?_⟩
    have hmean := hmass a b hla hab hbh
    have hbad : count (fun i ↦ phase (X i ω)) (Ioo (a.val : ℝ) (b.val : ℝ)) <
        c * ((b.val : ℝ) - a.val) - r := lt_of_not_ge hbad
    rw [count_comp] at hbad
    change count (fun i ↦ X i ω) (A (a, b)) < _
    dsimp [A] at *
    linarith
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using
    (measure_mono hsub).trans hbound

/-- Canonical product-law form of the grid certificate estimate. -/
theorem measure_not_gridGood_pi_le
    (P : Measure Ω) [IsProbabilityMeasure P] (m N : ℕ)
    {phase : Ω → ℝ} (hphase : Measurable phase) (lo hi c : ℝ)
    {r : ℝ} (hr : 0 < r)
    (hmass : ∀ a b : Fin (N + 1), lo ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
      (b.val : ℝ) ≤ hi →
      2 * c * ((b.val : ℝ) - a.val) ≤
        (m : ℝ) * P.real (phase ⁻¹' Ioo (a.val : ℝ) (b.val : ℝ))) :
    Measure.pi (fun _ : Fin m ↦ P) {sample | ¬gridGood N phase lo hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  apply measure_not_gridGood_le P (fun i ↦ measurable_pi_apply i)
    (iIndepFun_pi fun _ ↦ measurable_id.aemeasurable)
    (fun i ↦ (measurePreserving_eval (fun _ : Fin m ↦ P) i).map_eq) N hphase lo hi c hr hmass

end OTSelector.FiniteIntervalCounts
