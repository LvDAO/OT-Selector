import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Finite event-time counting paths

This file records the elementary pathwise facts for a finite family of event times.  The
definition is deliberately independent of filtrations and intensities: it is only the finite
cardinality of the events attained by a deterministic time threshold.
-/

open Filter Set
open scoped NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*}

/-- The number of event times in a finite family that have been attained by time `t`. -/
noncomputable def finiteEventCount {m : ℕ} (ξ : Fin m → Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i ↦ ξ i ω ≤ t)).card

/-- A finite event count is bounded by the number of event labels. -/
theorem finiteEventCount_le {m : ℕ} (ξ : Fin m → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    finiteEventCount ξ t ω ≤ m := by
  classical
  simpa [finiteEventCount] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i ↦ ξ i ω ≤ t))

/-- Increasing the threshold cannot decrease the finite event count. -/
theorem finiteEventCount_mono {m : ℕ} (ξ : Fin m → Ω → ℝ≥0) (ω : Ω)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCount ξ s ω ≤ finiteEventCount ξ t ω := by
  classical
  unfold finiteEventCount
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hi).2.trans hst⟩

/-- The threshold-zero count vanishes when every event time is strictly positive. -/
theorem finiteEventCount_zero {m : ℕ} (ξ : Fin m → Ω → ℝ≥0) (ω : Ω)
    (hξ : ∀ i, 0 < ξ i ω) :
    finiteEventCount ξ 0 ω = 0 := by
  classical
  rw [finiteEventCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact not_le_of_gt (hξ i)

/-- The count is a finite sum of the indicator contributions of its event labels. -/
theorem finiteEventCount_eq_sum {m : ℕ} (ξ : Fin m → Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    finiteEventCount ξ t ω =
      ∑ i : Fin m, if ξ i ω ≤ t then 1 else 0 := by
  classical
  change (Finset.univ.filter (fun i : Fin m ↦ ξ i ω ≤ t)).card = _
  exact Finset.card_filter (fun i : Fin m ↦ ξ i ω ≤ t) (Finset.univ : Finset (Fin m))

/-- A cast of the finite event count has the corresponding finite indicator sum. -/
theorem finiteEventCount_cast_eq_sum {m : ℕ} {R : Type*}
    [AddCommMonoidWithOne R] (ξ : Fin m → Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (finiteEventCount ξ t ω : R) =
      ∑ i : Fin m, if ξ i ω ≤ t then (1 : R) else 0 := by
  classical
  change ((Finset.univ.filter (fun i : Fin m ↦ ξ i ω ≤ t)).card : R) = _
  exact Finset.natCast_card_filter (R := R) (fun i : Fin m ↦ ξ i ω ≤ t)
    (Finset.univ : Finset (Fin m))

/-- If no event lies strictly after `t`, the filter of attained events is already stable. -/
theorem finiteEventCount_filter_eq_of_no_future {m : ℕ}
    (ξ : Fin m → Ω → ℝ≥0) (ω : Ω) (t s : ℝ≥0) (hst : t ≤ s)
    (hfuture : ∀ i, ¬ t < ξ i ω) :
    (Finset.univ.filter (fun i ↦ ξ i ω ≤ s)) =
      Finset.univ.filter (fun i ↦ ξ i ω ≤ t) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact le_of_not_gt (hfuture i)
  · intro hi
    exact hi.trans hst

/-- Below the first future event, the finite event filter is locally constant. -/
theorem finiteEventCount_filter_eq_of_mem_Ico {m : ℕ}
    (ξ : Fin m → Ω → ℝ≥0) (ω : Ω) (t s : ℝ≥0)
    (hS : (Finset.univ.filter (fun i ↦ t < ξ i ω)).Nonempty)
    (hst : t ≤ s) (hs : s <
      ((Finset.univ.filter (fun i ↦ t < ξ i ω)).image (fun i ↦ ξ i ω)).min'
        (Finset.image_nonempty.mpr hS)) :
    (Finset.univ.filter (fun i ↦ ξ i ω ≤ s)) =
      Finset.univ.filter (fun i ↦ ξ i ω ≤ t) := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i ↦ t < ξ i ω)
  let A : Finset ℝ≥0 := S.image (fun i ↦ ξ i ω)
  have hS' : S.Nonempty := by simpa [S] using hS
  have hA : A.Nonempty := S.image_nonempty.mpr hS'
  have hminmem : A.min' hA ∈ A := Finset.min'_mem A hA
  have hmin_gt : t < A.min' hA := by
    rcases Finset.mem_image.mp hminmem with ⟨i, hiS, hiEq⟩
    rw [← hiEq]
    exact (Finset.mem_filter.mp hiS).2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro his
    by_cases hit : t < ξ i ω
    · have hiS : i ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩
      have hmin_le : A.min' hA ≤ ξ i ω := by
        exact Finset.min'_le A (ξ i ω) (Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
      exfalso
      exact (not_lt_of_ge his) (lt_of_lt_of_le hs hmin_le)
    · exact le_of_not_gt hit
  · intro hit
    exact hit.trans hst

/-- Every finite event-count path is right-continuous after casting to the reals. -/
theorem finiteEventCount_rightContinuous {m : ℕ} (ξ : Fin m → Ω → ℝ≥0)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ (finiteEventCount ξ s ω : ℝ)) (Ici t) t := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i ↦ t < ξ i ω)
  by_cases hS : S.Nonempty
  · let A : Finset ℝ≥0 := S.image (fun i ↦ ξ i ω)
    have hA : A.Nonempty := S.image_nonempty.mpr hS
    have hmin_gt : t < A.min' hA := by
      rcases Finset.mem_image.mp (Finset.min'_mem A hA) with ⟨i, hiS, hiEq⟩
      rw [← hiEq]
      exact (Finset.mem_filter.mp hiS).2
    have hev : (fun s ↦ (finiteEventCount ξ s ω : ℝ)) =ᶠ[𝓝[Ici t] t]
        (fun _ ↦ (finiteEventCount ξ t ω : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmin_gt)] with s hst hs
      have hfilter := finiteEventCount_filter_eq_of_mem_Ico ξ ω t s
        (by simpa [S] using hS) hst hs
      change (finiteEventCount ξ s ω : ℝ) = (finiteEventCount ξ t ω : ℝ)
      rw [finiteEventCount, finiteEventCount, hfilter]
    have hconst : ContinuousWithinAt
        (fun _ : ℝ≥0 ↦ (finiteEventCount ξ t ω : ℝ)) (Ici t) t :=
      continuousWithinAt_const
    exact hconst.congr_of_eventuallyEq hev rfl
  · have hfuture : ∀ i, ¬ t < ξ i ω := by
      intro i hi
      apply hS
      refine ⟨i, ?_⟩
      simpa [S] using
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩ :
          i ∈ (Finset.univ : Finset (Fin m)).filter (fun j ↦ t < ξ j ω))
    have hev : (fun s ↦ (finiteEventCount ξ s ω : ℝ)) =ᶠ[𝓝[Ici t] t]
        (fun _ ↦ (finiteEventCount ξ t ω : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hst
      have hfilter := finiteEventCount_filter_eq_of_no_future ξ ω t s hst hfuture
      change (finiteEventCount ξ s ω : ℝ) = (finiteEventCount ξ t ω : ℝ)
      rw [finiteEventCount, finiteEventCount, hfilter]
    have hconst : ContinuousWithinAt
        (fun _ : ℝ≥0 ↦ (finiteEventCount ξ t ω : ℝ)) (Ici t) t :=
      continuousWithinAt_const
    exact hconst.congr_of_eventuallyEq hev rfl

end OTSelector.CountingProcess
