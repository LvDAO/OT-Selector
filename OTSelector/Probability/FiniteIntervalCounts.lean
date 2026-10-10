import OTSelector.Feedback.RelativeVC

/-!
# Finite-family lower bounds for independent interval counts

A variance-sensitive Bernstein bound gives an additive-error lower bound on every member of a
finite family of measurable sets.  The error does not depend on the mass of an individual set,
which allows a logarithmic error after a union bound over a polynomial-sized interval grid.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.FiniteIntervalCounts

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Number of observations in a set, viewed as a real sum. -/
noncomputable def count {m : ℕ} (X : Fin m → Ω) (A : Set Ω) : ℝ :=
  ∑ i, RelativeVC.indicatorReal A (X i)

omit [MeasurableSpace Ω] in
theorem count_nonneg {m : ℕ} (X : Fin m → Ω) (A : Set Ω) : 0 ≤ count X A := by
  apply Finset.sum_nonneg
  intro i _
  exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

theorem count_measurable {m : ℕ} {X : Fin m → Ξ → Ω}
    (hX : ∀ i, Measurable (X i)) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (fun ω ↦ count (fun i ↦ X i ω) A) := by
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_const.indicator hA).comp (hX i)

private theorem empiricalProcess_indicator_eq_count
    (P : Measure Ω) {m : ℕ} (hm : 0 < m) (X : Fin m → Ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    EmpiricalProcess.empiricalProcess P m X (RelativeVC.indicatorReal A) =
      (count X A - m * P.real A) / Real.sqrt m := by
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsqrt_sq : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
  rw [RelativeVC.empiricalProcess_indicator _ _ _ _ hA]
  unfold RelativeVC.empiricalSetDeviation RelativeVC.empiricalSetMass
    EmpiricalProcess.empiricalAverage count
  field_simp
  rw [hsqrt_sq]

/-- A count is at least half its mean minus `r`, except with probability `2 exp(-r/12)`.
The bound is uniform in the set mass and includes an empty sample. -/
theorem measure_count_lt_half_mean_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {m : ℕ}
    {X : Fin m → Ξ → Ω} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = P)
    {A : Set Ω} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r) :
    μ {ω | count (fun i ↦ X i ω) A < (m : ℝ) * P.real A / 2 - r} ≤
      ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  by_cases ha : (m : ℝ) * P.real A ≤ 2 * r
  · have hempty : {ω | count (fun i ↦ X i ω) A <
        (m : ℝ) * P.real A / 2 - r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hc := count_nonneg (fun i ↦ X i ω) A
      change count (fun i ↦ X i ω) A < _ at hω
      linarith
    rw [hempty, measure_empty]
    exact bot_le
  have ha : 2 * r < (m : ℝ) * P.real A := lt_of_not_ge ha
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp only [hm0, Nat.cast_zero, zero_mul] at ha
    linarith
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp : 0 < P.real A := (mul_pos_iff.mp (lt_trans (by positivity) ha)).resolve_right
    (fun h ↦ (not_lt_of_ge hmreal.le) h.1) |>.2
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmreal
  have hsqrt_sq : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt hmreal.le
  let x := ((m : ℝ) * P.real A / 2) / Real.sqrt m
  have hx : 0 < x := by dsimp [x]; positivity
  have hbern := RelativeVC.centeredIndicator_bernstein P A hA m (by omega)
    hX hindep hlaw hx
  have hsub : {ω | count (fun i ↦ X i ω) A < (m : ℝ) * P.real A / 2 - r} ⊆
      {ω | x < |EmpiricalProcess.empiricalProcess P m (fun i ↦ X i ω)
        (RelativeVC.indicatorReal A)|} := by
    intro ω hω
    change count (fun i ↦ X i ω) A < _ at hω
    change x < _
    rw [empiricalProcess_indicator_eq_count P hm _ hA]
    have hneg : count (fun i ↦ X i ω) A - (m : ℝ) * P.real A < 0 := by
      nlinarith
    rw [abs_of_neg (div_neg_of_neg_of_pos hneg hsqrt)]
    dsimp [x]
    rw [← neg_div]
    apply (div_lt_div_iff_of_pos_right hsqrt).2
    linarith
  have hexponent : x ^ 2 / (4 * (P.real A + x / Real.sqrt m)) =
      (m : ℝ) * P.real A / 24 := by
    dsimp [x]
    field_simp
    nlinarith [hsqrt_sq]
  apply (measure_mono hsub).trans (hbern.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  rw [neg_div, hexponent]
  linarith

/-- The same additive lower error controls all members of a finite measurable family. -/
theorem measure_exists_count_lt_half_mean_sub_le
    {ι : Type*} [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {m : ℕ}
    {X : Fin m → Ξ → Ω} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = P)
    (A : ι → Set Ω) (hA : ∀ j, MeasurableSet (A j)) {r : ℝ} (hr : 0 < r) :
    μ {ω | ∃ j, count (fun i ↦ X i ω) (A j) < (m : ℝ) * P.real (A j) / 2 - r} ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  have hset : {ω | ∃ j, count (fun i ↦ X i ω) (A j) <
      (m : ℝ) * P.real (A j) / 2 - r} =
      ⋃ j, {ω | count (fun i ↦ X i ω) (A j) < (m : ℝ) * P.real (A j) / 2 - r} := by
    ext ω
    simp
  rw [hset]
  refine (measure_iUnion_fintype_le μ _).trans ?_
  calc
    _ ≤ ∑ _j : ι, ENNReal.ofReal (2 * Real.exp (-r / 12)) :=
      Finset.sum_le_sum fun j _ ↦
        measure_count_lt_half_mean_sub_le P hX hindep hlaw (hA j) hr
    _ = _ := by simp [nsmul_eq_mul]

end OTSelector.FiniteIntervalCounts
