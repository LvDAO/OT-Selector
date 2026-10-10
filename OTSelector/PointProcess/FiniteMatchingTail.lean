import OTSelector.Feedback.Comparison
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Root-integrated partner and crossing tails for finite matchings

For actual finite endpoint arrays and a permutation, spatial integration of the number of long
edges with an endpoint near the root is at most `2 A / R²` times the squared edge energy.
Spatial integration of long-edge crossings is at most the same energy divided by `R`.
The estimates hold on every root set and require no optimality or probabilistic tail premise.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector.PointProcess.FiniteMatching

variable {n : ℕ}

/-- Count actual endpoints within distance `A` of a root whose paired displacement exceeds `R`. -/
noncomputable def rootWindowTailCount (endpoint displacement : Fin n → ℝ) (A R z : ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ |endpoint i - z| ≤ A ∧ R < |displacement i|).card

private theorem windowIndicator_eq (a A z : ℝ) :
    (if |a - z| ≤ A then (1 : ℝ) else 0) =
      (Icc (a - A) (a + A)).indicator (fun _ : ℝ ↦ (1 : ℝ)) z := by
  have h : |a - z| ≤ A ↔ z ∈ Icc (a - A) (a + A) := by
    rw [abs_le, Set.mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [Set.indicator_apply, h]

private theorem integrable_windowIndicator (a A : ℝ) :
    Integrable (fun z : ℝ ↦ if |a - z| ≤ A then (1 : ℝ) else 0) := by
  simp_rw [windowIndicator_eq]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

private theorem integral_windowIndicator (a : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫ z : ℝ, if |a - z| ≤ A then (1 : ℝ) else 0) = 2 * A := by
  simp_rw [windowIndicator_eq]
  rw [integral_indicator_const 1 measurableSet_Icc,
    Real.volume_real_Icc_of_le (by linarith)]
  simp only [smul_eq_mul, mul_one]
  ring

/-- The literal endpoint count is the finite sum of the root-window indicators. -/
theorem rootWindowTailCount_eq_sum (endpoint displacement : Fin n → ℝ) (A R z : ℝ) :
    (rootWindowTailCount endpoint displacement A R z : ℝ) =
      ∑ i, if R < |displacement i| then (if |endpoint i - z| ≤ A then 1 else 0) else 0 := by
  rw [rootWindowTailCount, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : R < |displacement i| <;> simp [h]

/-- Root-window counts have finite spatial integral for every finite array. -/
theorem integrable_rootWindowTailCount (endpoint displacement : Fin n → ℝ) (A R : ℝ) :
    Integrable (fun z : ℝ ↦ (rootWindowTailCount endpoint displacement A R z : ℝ)) := by
  simp_rw [rootWindowTailCount_eq_sum]
  apply integrable_finsetSum
  intro i hi
  by_cases h : R < |displacement i|
  · simpa only [h, ↓reduceIte] using integrable_windowIndicator (endpoint i) A
  · simp [h]

/-- Each long edge endpoint occupies precisely a root interval of length `2 A`. -/
theorem integral_rootWindowTailCount (endpoint displacement : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    (∫ z : ℝ, (rootWindowTailCount endpoint displacement A R z : ℝ)) =
      2 * A * ∑ i, if R < |displacement i| then (1 : ℝ) else 0 := by
  simp_rw [rootWindowTailCount_eq_sum]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : R < |displacement i|
    · simpa only [h, ↓reduceIte, mul_one] using integral_windowIndicator (endpoint i) hA
    · simp [h]
  · intro i hi
    by_cases h : R < |displacement i|
    · simpa only [h, ↓reduceIte] using integrable_windowIndicator (endpoint i) A
    · simp [h]

private theorem longCount_le_energy_div (displacement : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    (∑ i, if R < |displacement i| then (1 : ℝ) else 0) ≤
      (∑ i, displacement i ^ 2) / R ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : R < |displacement i|
  · simp only [h, ↓reduceIte]
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [sq_abs (displacement i)]
  · simp only [h, ↓reduceIte]
    positivity

/-- Spatially integrated endpoint escape is controlled by the actual squared displacements. -/
theorem setIntegral_rootWindowTailCount_le (endpoint displacement : Fin n → ℝ)
    (I : Set ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (∫ z in I, (rootWindowTailCount endpoint displacement A R z : ℝ)) ≤
      (2 * A / R ^ 2) * ∑ i, displacement i ^ 2 := by
  calc
    _ ≤ ∫ z : ℝ, (rootWindowTailCount endpoint displacement A R z : ℝ) :=
      setIntegral_le_integral (integrable_rootWindowTailCount endpoint displacement A R)
        (ae_of_all _ fun z ↦ Nat.cast_nonneg _)
    _ = 2 * A * ∑ i, if R < |displacement i| then (1 : ℝ) else 0 :=
      integral_rootWindowTailCount endpoint displacement hA R
    _ ≤ 2 * A * ((∑ i, displacement i ^ 2) / R ^ 2) :=
      mul_le_mul_of_nonneg_left (longCount_le_energy_div displacement hR) (by positivity)
    _ = _ := by ring

/-- Source endpoints near the root whose actual assigned partners are farther than `R`. -/
noncomputable def sourceRootLongEdgeCount (source target : Fin n → ℝ)
    (σ : Assignment n) (A R z : ℝ) : ℕ :=
  rootWindowTailCount source (fun i ↦ target (σ i) - source i) A R z

/-- Target endpoints near the root whose actual inverse-assigned partners are farther than `R`. -/
noncomputable def targetRootLongEdgeCount (source target : Fin n → ℝ)
    (σ : Assignment n) (A R z : ℝ) : ℕ :=
  rootWindowTailCount target (fun j ↦ target j - source (σ.symm j)) A R z

/-- The source partner escape bound for an arbitrary actual finite assignment. -/
theorem setIntegral_sourceRootLongEdgeCount_le (source target : Fin n → ℝ)
    (σ : Assignment n) (I : Set ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (∫ z in I, (sourceRootLongEdgeCount source target σ A R z : ℝ)) ≤
      (2 * A / R ^ 2) * ∑ i, (target (σ i) - source i) ^ 2 :=
  setIntegral_rootWindowTailCount_le _ _ I hA hR

/-- The target partner escape bound uses the same forward-indexed squared assignment energy. -/
theorem setIntegral_targetRootLongEdgeCount_le (source target : Fin n → ℝ)
    (σ : Assignment n) (I : Set ℝ) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (∫ z in I, (targetRootLongEdgeCount source target σ A R z : ℝ)) ≤
      (2 * A / R ^ 2) * ∑ i, (target (σ i) - source i) ^ 2 := by
  have h := setIntegral_rootWindowTailCount_le target
    (fun j ↦ target j - source (σ.symm j)) I hA hR
  have heq : (∑ j, (target j - source (σ.symm j)) ^ 2) =
      ∑ i, (target (σ i) - source i) ^ 2 := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp σ (fun j ↦ (target j - source (σ.symm j)) ^ 2)).symm
  simpa only [targetRootLongEdgeCount, heq] using h

/-- The unsigned contribution of an actual edge is its half-open crossing interval indicator. -/
theorem abs_crossingSign_eq_indicator (a b z : ℝ) :
    |(crossingSign a b z : ℝ)| =
      (Ico (min a b) (max a b)).indicator (fun _ : ℝ ↦ (1 : ℝ)) z := by
  by_cases ha : a ≤ z <;> by_cases hb : b ≤ z <;>
    simp [crossingSign, ha, hb, Set.mem_Ico, min_le_iff, not_lt_of_ge, lt_of_not_ge]

/-- The unsigned crossing contribution has finite root integral. -/
theorem integrable_abs_crossingSign (a b : ℝ) :
    Integrable (fun z : ℝ ↦ |(crossingSign a b z : ℝ)|) := by
  simp_rw [abs_crossingSign_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

/-- Integrating an edge's unsigned crossing current gives its actual length. -/
theorem integral_abs_crossingSign (a b : ℝ) :
    (∫ z : ℝ, |(crossingSign a b z : ℝ)|) = |b - a| := by
  simp_rw [abs_crossingSign_eq_indicator]
  rw [integral_indicator_const 1 measurableSet_Ico,
    Real.volume_real_Ico_of_le min_le_max]
  simp only [smul_eq_mul, mul_one, max_sub_min_eq_abs, abs_sub_comm]

/-- Number of long assigned edges crossing the root, written using the existing signed current. -/
noncomputable def longCrossingCount (source target : Fin n → ℝ)
    (σ : Assignment n) (R z : ℝ) : ℝ :=
  ∑ i, if R < |target (σ i) - source i| then
    |(crossingSign (source i) (target (σ i)) z : ℝ)| else 0

/-- The long crossing count is spatially integrable. -/
theorem integrable_longCrossingCount (source target : Fin n → ℝ)
    (σ : Assignment n) (R : ℝ) : Integrable (longCrossingCount source target σ R) := by
  apply integrable_finsetSum
  intro i hi
  by_cases h : R < |target (σ i) - source i|
  · simpa only [h, ↓reduceIte] using integrable_abs_crossingSign (source i) (target (σ i))
  · simp [h]

/-- Root integration of long crossings equals the sum of their lengths. -/
theorem integral_longCrossingCount (source target : Fin n → ℝ)
    (σ : Assignment n) (R : ℝ) :
    (∫ z : ℝ, longCrossingCount source target σ R z) =
      ∑ i, if R < |target (σ i) - source i| then |target (σ i) - source i| else 0 := by
  unfold longCrossingCount
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases h : R < |target (σ i) - source i|
    · simpa only [h, ↓reduceIte] using integral_abs_crossingSign (source i) (target (σ i))
    · simp [h]
  · intro i hi
    by_cases h : R < |target (σ i) - source i|
    · simpa only [h, ↓reduceIte] using integrable_abs_crossingSign (source i) (target (σ i))
    · simp [h]

/-- Spatially integrated long crossings are bounded by squared assignment energy divided by `R`.
This transports the actual finite energy estimate to a first-moment flux tail. -/
theorem setIntegral_longCrossingCount_le (source target : Fin n → ℝ)
    (σ : Assignment n) (I : Set ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ z in I, longCrossingCount source target σ R z) ≤
      (∑ i, (target (σ i) - source i) ^ 2) / R := by
  calc
    _ ≤ ∫ z : ℝ, longCrossingCount source target σ R z :=
      setIntegral_le_integral (integrable_longCrossingCount source target σ R)
        (ae_of_all _ fun z ↦ Finset.sum_nonneg fun i hi ↦ by split_ifs <;> positivity)
    _ = ∑ i, if R < |target (σ i) - source i| then |target (σ i) - source i| else 0 :=
      integral_longCrossingCount source target σ R
    _ ≤ _ := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : R < |target (σ i) - source i|
      · simp only [h, ↓reduceIte]
        apply (le_div_iff₀ hR).mpr
        have hnonneg := abs_nonneg (target (σ i) - source i)
        nlinarith [sq_abs (target (σ i) - source i)]
      · simp only [h, ↓reduceIte]
        positivity

end OTSelector.PointProcess.FiniteMatching
