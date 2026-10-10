import OTSelector.Probability.CountingProcess.StoppingEvaluation
import Mathlib.MeasureTheory.Function.Floor

/-!
# Right-grid approximation of bounded stopping coordinates

For a positive integer denominator `n`, `rightGrid n t` is the least point of the grid
`{k / n : k ∈ ℕ}` lying above `t`.  Applying this map to a stopping coordinate preserves the
stopping-time property and gives a finite range on every deterministic bounded horizon.
-/

open Filter Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The least `1 / n` grid point above `t`.  The useful estimates assume `0 < n`. -/
noncomputable def rightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈(n : ℝ≥0) * t⌉₊ : ℝ≥0) / (n : ℝ≥0)

/-- The greatest `1 / n` grid point below `t`. -/
noncomputable def leftGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌊(n : ℝ≥0) * t⌋₊ : ℝ≥0) / (n : ℝ≥0)

omit [MeasurableSpace Ω] in
theorem leftGrid_le (n : ℕ) (t : ℝ≥0) (hn : 0 < n) : leftGrid n t ≤ t := by
  rw [leftGrid, div_le_iff₀ (by exact_mod_cast hn)]
  simpa [mul_comm] using Nat.floor_le (a := (n : ℝ≥0) * t) (by positivity)

omit [MeasurableSpace Ω] in
theorem le_rightGrid (n : ℕ) (t : ℝ≥0) (hn : 0 < n) : t ≤ rightGrid n t := by
  rw [rightGrid, le_div_iff₀ (by exact_mod_cast hn)]
  simpa [mul_comm] using Nat.le_ceil ((n : ℝ≥0) * t)

omit [MeasurableSpace Ω] in
theorem rightGrid_lt_add_inv (n : ℕ) (t : ℝ≥0) (hn : 0 < n) :
    rightGrid n t < t + (n : ℝ≥0)⁻¹ := by
  rw [rightGrid, div_lt_iff₀ (by exact_mod_cast hn)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ≥0) * t by positivity)
  rw [add_mul, inv_mul_cancel₀ (show (n : ℝ≥0) ≠ 0 by exact_mod_cast hn.ne')]
  simpa [mul_comm] using hceil

omit [MeasurableSpace Ω] in
theorem rightGrid_le_iff_le_leftGrid (n : ℕ) (s t : ℝ≥0) (hn : 0 < n) :
    rightGrid n s ≤ t ↔ s ≤ leftGrid n t := by
  rw [rightGrid, leftGrid, div_le_iff₀ (by exact_mod_cast hn),
    le_div_iff₀ (by exact_mod_cast hn)]
  simp only [mul_comm t (n : ℝ≥0), mul_comm s (n : ℝ≥0)]
  constructor
  · intro h
    have hcf : ⌈(n : ℝ≥0) * s⌉₊ ≤ ⌊(n : ℝ≥0) * t⌋₊ := Nat.le_floor h
    exact (Nat.le_ceil ((n : ℝ≥0) * s)).trans (by exact_mod_cast hcf)
  · intro h
    have hcf : ⌈(n : ℝ≥0) * s⌉₊ ≤ ⌊(n : ℝ≥0) * t⌋₊ :=
      Nat.ceil_le.mpr h
    exact (by exact_mod_cast hcf :
      (⌈(n : ℝ≥0) * s⌉₊ : ℝ≥0) ≤ (⌊(n : ℝ≥0) * t⌋₊ : ℝ≥0)) |>.trans
        (Nat.floor_le (a := (n : ℝ≥0) * t) (by positivity))

/-- Right-grid approximation preserves the stopping-time property. -/
theorem IsStoppingTime.rightGridApprox
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) (n : ℕ) (hn : 0 < n) :
    IsStoppingTime ℱ fun ω ↦ (rightGrid n (σ ω) : WithTop ℝ≥0) := by
  intro t
  have hset : {ω | (rightGrid n (σ ω) : WithTop ℝ≥0) ≤ t} =
      {ω | (σ ω : WithTop ℝ≥0) ≤ leftGrid n t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    exact rightGrid_le_iff_le_leftGrid n (σ ω) t hn
  rw [hset]
  exact ℱ.mono (leftGrid_le n t hn) _ (hσ (leftGrid n t))

omit [MeasurableSpace Ω] in
set_option linter.unusedVariables.funArgs false in
/-- A right-grid approximation of a deterministically bounded coordinate has finite range. -/
theorem finiteRange_rightGrid_of_le {σ : Ω → ℝ≥0} {B : ℝ≥0} (n : ℕ) (hn : 0 < n)
    (hσB : ∀ ω, σ ω ≤ B) : (Set.range fun ω ↦ rightGrid n (σ ω)).Finite := by
  let K : ℕ := ⌈(n : ℝ≥0) * B⌉₊
  refine (Finset.finite_toSet (Finset.range (K + 1) |>.image
    (fun k : ℕ ↦ (k : ℝ≥0) / (n : ℝ≥0)))).subset ?_
  rintro _ ⟨ω, rfl⟩
  simp only [rightGrid, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  refine ⟨⌈(n : ℝ≥0) * σ ω⌉₊, ?_, rfl⟩
  apply Nat.lt_succ_of_le
  apply Nat.ceil_mono
  gcongr
  exact hσB ω

omit [MeasurableSpace Ω] in
/-- The right-grid approximation lies between the original coordinate and one mesh above it. -/
theorem rightGrid_bounds (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) :
    (∀ ω, σ ω ≤ rightGrid n (σ ω)) ∧
      (∀ ω, rightGrid n (σ ω) < σ ω + (n : ℝ≥0)⁻¹) :=
  ⟨fun ω ↦ le_rightGrid n (σ ω) hn, fun ω ↦ rightGrid_lt_add_inv n (σ ω) hn⟩

omit [MeasurableSpace Ω] in
/-- Successively finer right grids converge to the original coordinate. -/
theorem tendsto_rightGrid_succ (t : ℝ≥0) :
    Tendsto (fun k : ℕ ↦ rightGrid (k + 1) t) atTop (nhds t) := by
  have hinv : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ≥0)⁻¹)) atTop (nhds 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun k : ℕ ↦ t + ((k + 1 : ℕ) : ℝ≥0)⁻¹) atTop (nhds t) := by
    simpa using (show Tendsto (fun k : ℕ ↦ t + (((k + 1 : ℕ) : ℝ≥0)⁻¹)) atTop
      (nhds (t + 0)) from (tendsto_const_nhds (x := t)).add hinv)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun k ↦ le_rightGrid (k + 1) t (by omega)
  · exact Filter.Eventually.of_forall fun k ↦
      (rightGrid_lt_add_inv (k + 1) t (by omega)).le

/-- Evaluating a right-continuous adapted counting process at an arbitrary deterministically
bounded stopping coordinate is measurable. -/
theorem stronglyMeasurable_eval_boundedStopping
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {σ : Ω → ℝ≥0}
    (hN : IsSimpleCountingProcess ℱ N)
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) {B : ℝ≥0}
    (hσB : ∀ ω, σ ω ≤ B) : StronglyMeasurable (fun ω ↦ (N (σ ω) ω : ℝ)) := by
  let σk : ℕ → Ω → ℝ≥0 := fun k ω ↦ rightGrid (k + 1) (σ ω)
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun k ω ↦ (N (σk k ω) ω : ℝ)) ?_ ?_
  · intro k
    have hσk : IsStoppingTime ℱ fun ω ↦ (σk k ω : WithTop ℝ≥0) := by
      exact OTSelector.CountingProcess.IsStoppingTime.rightGridApprox hσ (k + 1) (by omega)
    apply stronglyMeasurable_eval_finiteRange hN.stronglyAdapted hσk
    exact finiteRange_rightGrid_of_le (k + 1) (by omega) hσB
  · rw [tendsto_pi_nhds]
    intro ω
    apply (hN.rightContinuous ω (σ ω)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_rightGrid_succ (σ ω), Filter.Eventually.of_forall fun k ↦
      le_rightGrid (k + 1) (σ ω) (by omega)⟩

/-- Adding a deterministic nonnegative duration to a finite stopping coordinate preserves the
stopping-time property; no countability assumption on its range is needed. -/
theorem IsStoppingTime.coe_add_const
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) (r : ℝ≥0) :
    IsStoppingTime ℱ fun ω ↦ ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  by_cases hrt : r ≤ t
  · have hset : {ω | ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | (σ ω : WithTop ℝ≥0) ≤ ((t - r : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right hrt).symm
    rw [hset]
    exact ℱ.mono (tsub_le_self) _ (hσ (t - r))
  · have hset : {ω | ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, WithTop.coe_le_coe]
      exact fun h ↦ hrt ((le_add_of_nonneg_left (show 0 ≤ σ ω by positivity)).trans h)
    rw [hset]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- The stopped lower-occupation event is measurable for every deterministically bounded start.
The proof evaluates the right-continuous counting path through successively finer finite grids. -/
theorem measurableSet_stoppedLowerOccupationEvent_bounded
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {σ : Ω → ℝ≥0}
    {τ : Ω → WithTop ℝ≥0} {a : ℝ} {r B : ℝ≥0}
    (hN : IsSimpleCountingProcess ℱ N)
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0)) (hσB : ∀ ω, σ ω ≤ B)
    (hτ : IsStoppingTime ℱ τ) : MeasurableSet (stoppedLowerOccupationEvent N σ τ a r) := by
  have hρ : IsStoppingTime ℱ fun ω ↦ ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) :=
    OTSelector.CountingProcess.IsStoppingTime.coe_add_const hσ r
  have hNs : StronglyMeasurable (fun ω ↦ (N (σ ω) ω : ℝ)) :=
    stronglyMeasurable_eval_boundedStopping hN hσ hσB
  have hNr : StronglyMeasurable (fun ω ↦ (N (σ ω + r) ω : ℝ)) := by
    apply stronglyMeasurable_eval_boundedStopping hN hρ (B := B + r)
    intro ω
    simpa [add_comm] using add_le_add_right (hσB ω) r
  have hcount : MeasurableSet
      {ω | (N (σ ω + r) ω : ℝ) - N (σ ω) ω ≤ a * (r : ℝ)} :=
    (hNr.sub hNs).measurableSet_le stronglyMeasurable_const
  have hsurvival : MeasurableSet
      {ω | ((σ ω + r : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω} :=
    hρ.measurableSpace_le _ (hρ.measurableSet_le_stopping_time hτ)
  exact hcount.inter hsurvival

end OTSelector.CountingProcess
