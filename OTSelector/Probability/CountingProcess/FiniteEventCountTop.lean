import OTSelector.Probability.CountingProcess.FiniteEventCount
import OTSelector.Probability.CountingProcess.OccupationBound
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Finite event-time counting paths with a top fallback

This file extends `FiniteEventCount` to event times in `WithTop ℝ≥0`.  The value `⊤` is a
fallback label that is never attained at a finite time.  All statements below are pathwise and
remain independent of filtrations and intensities.
-/

open Filter Set
open scoped NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*}

/-- The number of finite event times in a finite family that have been attained by time `t`. -/
noncomputable def finiteEventCountTop {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0))).card

/-- A finite event count with top-valued fallback labels is bounded by the number of labels. -/
theorem finiteEventCountTop_le {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : finiteEventCountTop ξ t ω ≤ m := by
  classical
  simpa [finiteEventCountTop] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin m))
      (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0)))

/-- Increasing the finite threshold cannot decrease the attained count. -/
theorem finiteEventCountTop_mono {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountTop ξ s ω ≤ finiteEventCountTop ξ t ω := by
  classical
  unfold finiteEventCountTop
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hi).2.trans (WithTop.coe_le_coe.mpr hst)⟩

/-- The threshold-zero count vanishes when every label is either positive or the top fallback. -/
theorem finiteEventCountTop_zero {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    (hξ : ∀ i, ξ i ω = ⊤ ∨ (0 : WithTop ℝ≥0) < ξ i ω) :
    finiteEventCountTop ξ 0 ω = 0 := by
  classical
  rw [finiteEventCountTop, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rcases hξ i with htop | hpos
  · rw [htop]
    exact WithTop.not_top_le_coe 0
  · exact not_le_of_gt hpos

/-- The same zero-count fact with the positive-or-top premise in its natural order. -/
theorem finiteEventCountTop_zero_of_pos_or_top {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    (hξ : ∀ i, (0 : WithTop ℝ≥0) < ξ i ω ∨ ξ i ω = ⊤) :
    finiteEventCountTop ξ 0 ω = 0 := by
  apply finiteEventCountTop_zero ξ ω
  intro i
  rcases hξ i with hpos | htop
  · exact Or.inr hpos
  · exact Or.inl htop

/-- A top-valued finite-event count is a finite sum of indicator contributions. -/
theorem finiteEventCountTop_eq_sum {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    finiteEventCountTop ξ t ω =
      ∑ i : Fin m, if ξ i ω ≤ (t : WithTop ℝ≥0) then 1 else 0 := by
  classical
  change (Finset.univ.filter (fun i : Fin m ↦ ξ i ω ≤ (t : WithTop ℝ≥0))).card = _
  exact Finset.card_filter (fun i : Fin m ↦ ξ i ω ≤ (t : WithTop ℝ≥0))
    (Finset.univ : Finset (Fin m))

/- The strict left-limit count is exactly the number of finite event labels strictly
   below the evaluation time.  The statement is pathwise and does not need a positivity
   assumption: labels at zero are excluded when `t = 0`, while top-valued labels are
   excluded at every finite time. -/
theorem countBefore_finiteEventCountTop_eq_card_filter_lt {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    countBefore (fun s ω' ↦ finiteEventCountTop ξ s ω') t ω =
      (Finset.univ.filter (fun i ↦ ξ i ω < (t : WithTop ℝ≥0))).card := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω' ↦ finiteEventCountTop ξ s ω'
  let C : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ ξ i ω < (t : WithTop ℝ≥0))
  let S : Finset ℕ :=
    (Finset.range (N t ω + 1)).filter
      (fun k ↦ ∃ u : ℝ≥0, u < t ∧ k < N u ω)
  have hmono : Monotone (fun s : ℝ≥0 ↦ N s ω) := by
    intro s u hsu
    exact finiteEventCountTop_mono ξ ω hsu
  have hS_eq : S = Finset.range C.card := by
    ext k
    simp only [S, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hkT, ⟨u, hut, hku⟩⟩
      have hsub :
          (Finset.univ.filter (fun i : Fin m ↦ ξ i ω ≤ (u : WithTop ℝ≥0))) ⊆ C := by
        intro i hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact lt_of_le_of_lt (Finset.mem_filter.mp hi).2
          (WithTop.coe_lt_coe.mpr hut)
      have hcard : N u ω ≤ C.card := by
        change (Finset.univ.filter
          (fun i : Fin m ↦ ξ i ω ≤ (u : WithTop ℝ≥0))).card ≤ C.card
        exact Finset.card_le_card (by simpa [C] using hsub)
      exact Nat.lt_of_lt_of_le hku hcard
    · intro hkC
      have hCnonempty : C.Nonempty := by
        exact Finset.nonempty_of_ne_empty (by
          intro hCempty
          rw [hCempty] at hkC
          simp at hkC)
      obtain ⟨i, hiC, hmax⟩ := Finset.exists_max_image C (fun j ↦ ξ j ω) hCnonempty
      have hxi_lt : ξ i ω < (t : WithTop ℝ≥0) := (Finset.mem_filter.mp hiC).2
      have hxi_ne_top : ξ i ω ≠ ⊤ := by
        intro htop
        rw [htop] at hxi_lt
        exact (WithTop.not_top_lt (t : WithTop ℝ≥0)) hxi_lt
      let u : ℝ≥0 := (ξ i ω).untop hxi_ne_top
      have hxi_eq : (u : WithTop ℝ≥0) = ξ i ω := WithTop.coe_untop _ _
      have hut : u < t := by
        apply WithTop.coe_lt_coe.mp
        rw [hxi_eq]
        exact hxi_lt
      have hsub : C ⊆ Finset.univ.filter
          (fun j : Fin m ↦ ξ j ω ≤ (u : WithTop ℝ≥0)) := by
        intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        calc
          ξ j ω ≤ ξ i ω := hmax j hj
          _ = (u : WithTop ℝ≥0) := hxi_eq.symm
      have hcard : C.card ≤ N u ω := by
        change C.card ≤ (Finset.univ.filter
          (fun j : Fin m ↦ ξ j ω ≤ (u : WithTop ℝ≥0))).card
        exact Finset.card_le_card (by simpa using hsub)
      have hku : k < N u ω := Nat.lt_of_lt_of_le hkC hcard
      have hkT : k < N t ω + 1 := by
        exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hku (hmono hut.le))
      exact ⟨hkT, ⟨u, hut, hku⟩⟩
  change S.card = C.card
  rw [hS_eq, Finset.card_range]

/-- A finite-event count is eventually constant on the strict left neighborhood of `t`, with
value equal to `countBefore` at `t`.  Event labels attained exactly at `t` are therefore excluded
from the left limit. -/
theorem finiteEventCountTop_eventuallyEq_countBefore_nhdsWithin_Iio {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) =ᶠ[𝓝[(Iio t : Set ℝ≥0)] t]
      fun _ ↦ (countBefore (fun s ω' ↦ finiteEventCountTop ξ s ω') t ω : ℝ) := by
  classical
  have hlabel : ∀ i : Fin m, ∀ᶠ (s : ℝ≥0) in 𝓝[(Iio t : Set ℝ≥0)] t,
      (ξ i ω ≤ (s : WithTop ℝ≥0) ↔ ξ i ω < (t : WithTop ℝ≥0)) := by
    intro i
    by_cases hxi : ξ i ω < (t : WithTop ℝ≥0)
    · have hne : ξ i ω ≠ ⊤ := ne_top_of_lt hxi
      let a : ℝ≥0 := (ξ i ω).untop hne
      have haeq : (a : WithTop ℝ≥0) = ξ i ω := WithTop.coe_untop _ hne
      have hat : a < t := WithTop.coe_lt_coe.mp (haeq.trans_lt hxi)
      have hright : Ici a ∈ 𝓝[Iio t] t := by
        apply Filter.mem_of_superset
          (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat))
        intro s hs
        change a < s at hs
        change a ≤ s
        exact hs.le
      filter_upwards [hright] with s hs
      constructor
      · intro _
        exact hxi
      · intro _
        rw [← haeq]
        exact WithTop.coe_le_coe.mpr hs
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s < t at hs
      constructor
      · intro his
        exact False.elim (hxi (his.trans_lt (WithTop.coe_lt_coe.mpr hs)))
      · intro hit
        exact False.elim (hxi hit)
  have hall : ∀ᶠ (s : ℝ≥0) in 𝓝[(Iio t : Set ℝ≥0)] t, ∀ i : Fin m,
      (ξ i ω ≤ (s : WithTop ℝ≥0) ↔ ξ i ω < (t : WithTop ℝ≥0)) :=
    Filter.eventually_all.mpr hlabel
  filter_upwards [hall] with s hs
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hs i

/-- The real-valued finite-event count tends to its strict-left count from below. -/
theorem finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    Filter.Tendsto (fun s ↦ (finiteEventCountTop ξ s ω : ℝ))
      (𝓝[(Iio t : Set ℝ≥0)] t)
      (𝓝 (countBefore (fun s ω' ↦ finiteEventCountTop ξ s ω') t ω : ℝ)) := by
  exact Tendsto.congr'
    (finiteEventCountTop_eventuallyEq_countBefore_nhdsWithin_Iio ξ ω t).symm
    tendsto_const_nhds

/-- A cast of a top-valued finite-event count has the corresponding indicator sum. -/
theorem finiteEventCountTop_cast_eq_sum {m : ℕ} {R : Type*}
    [AddCommMonoidWithOne R] (ξ : Fin m → Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (finiteEventCountTop ξ t ω : R) =
      ∑ i : Fin m, if ξ i ω ≤ (t : WithTop ℝ≥0) then (1 : R) else 0 := by
  classical
  change ((Finset.univ.filter
    (fun i : Fin m ↦ ξ i ω ≤ (t : WithTop ℝ≥0))).card : R) = _
  exact Finset.natCast_card_filter (R := R)
    (fun i : Fin m ↦ ξ i ω ≤ (t : WithTop ℝ≥0)) (Finset.univ : Finset (Fin m))

/-- If no finite threshold lies strictly before a future label, the attained filter is stable. -/
theorem finiteEventCountTop_filter_eq_of_no_future {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t s : ℝ≥0) (hst : t ≤ s)
    (hfuture : ∀ i, ¬(t : WithTop ℝ≥0) < ξ i ω) :
    (Finset.univ.filter (fun i ↦ ξ i ω ≤ (s : WithTop ℝ≥0))) =
      Finset.univ.filter (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0)) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact le_of_not_gt (hfuture i)
  · intro hi
    exact hi.trans (WithTop.coe_le_coe.mpr hst)

/-- Below the first future event, including a possible top fallback, the attained filter is stable.
-/
theorem finiteEventCountTop_filter_eq_of_mem_Ico {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t s : ℝ≥0)
    (hS : (Finset.univ.filter (fun i ↦ (t : WithTop ℝ≥0) < ξ i ω)).Nonempty)
    (hst : t ≤ s) (hs : (s : WithTop ℝ≥0) <
      ((Finset.univ.filter (fun i ↦ (t : WithTop ℝ≥0) < ξ i ω)).image
        (fun i ↦ ξ i ω)).min'
        (Finset.image_nonempty.mpr hS)) :
    (Finset.univ.filter (fun i ↦ ξ i ω ≤ (s : WithTop ℝ≥0))) =
      Finset.univ.filter (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0)) := by
  classical
  let S : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ (t : WithTop ℝ≥0) < ξ i ω)
  let A : Finset (WithTop ℝ≥0) := S.image (fun i ↦ ξ i ω)
  have hS' : S.Nonempty := by simpa [S] using hS
  have hA : A.Nonempty := S.image_nonempty.mpr hS'
  have hs' : (s : WithTop ℝ≥0) < A.min' hA := by
    simpa [A, S] using hs
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro his
    by_cases hit : (t : WithTop ℝ≥0) < ξ i ω
    · have hiS : i ∈ S := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩
      have hmin_le : A.min' hA ≤ ξ i ω := by
        exact Finset.min'_le A (ξ i ω) (Finset.mem_image.mpr ⟨i, hiS, rfl⟩)
      exfalso
      exact (not_lt_of_ge his) (lt_of_lt_of_le hs' hmin_le)
    · exact le_of_not_gt hit
  · intro hit
    exact hit.trans (WithTop.coe_le_coe.mpr hst)

/-- Every top-valued finite-event count path is right-continuous after casting to the reals. -/
theorem finiteEventCountTop_rightContinuous {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) (Ici t) t := by
  classical
  let S : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ (t : WithTop ℝ≥0) < ξ i ω)
  by_cases hS : S.Nonempty
  · let A : Finset (WithTop ℝ≥0) := S.image (fun i ↦ ξ i ω)
    have hA : A.Nonempty := S.image_nonempty.mpr hS
    have hmin_gt : (t : WithTop ℝ≥0) < A.min' hA := by
      rcases Finset.mem_image.mp (Finset.min'_mem A hA) with ⟨i, hiS, hiEq⟩
      rw [← hiEq]
      exact (Finset.mem_filter.mp hiS).2
    cases hmin : A.min' hA with
    | top =>
        have hlt : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < A.min' hA := by
          intro s
          rw [hmin]
          exact WithTop.coe_lt_top s
        have hev : (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) =ᶠ[𝓝[Ici t] t]
            (fun _ ↦ (finiteEventCountTop ξ t ω : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin] with s hst
          have hfilter := finiteEventCountTop_filter_eq_of_mem_Ico ξ ω t s
            (by simpa [S] using hS) hst (by simpa [A, S, hmin] using hlt s)
          change (finiteEventCountTop ξ s ω : ℝ) = (finiteEventCountTop ξ t ω : ℝ)
          rw [finiteEventCountTop, finiteEventCountTop, hfilter]
        have hconst : ContinuousWithinAt
            (fun _ : ℝ≥0 ↦ (finiteEventCountTop ξ t ω : ℝ)) (Ici t) t :=
          continuousWithinAt_const
        exact hconst.congr_of_eventuallyEq hev rfl
    | coe r =>
        have hmin_gt' : t < r := by
          apply WithTop.coe_lt_coe.mp
          simpa [hmin] using hmin_gt
        have hev : (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) =ᶠ[𝓝[Ici t] t]
            (fun _ ↦ (finiteEventCountTop ξ t ω : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmin_gt')] with s hst hs
          have hsTop : (s : WithTop ℝ≥0) < (r : WithTop ℝ≥0) :=
            WithTop.coe_lt_coe.mpr (show s < r from hs)
          have hsMin : (s : WithTop ℝ≥0) < A.min' hA := by
            rw [hmin]
            exact hsTop
          have hfilter := finiteEventCountTop_filter_eq_of_mem_Ico ξ ω t s
            (by simpa [S] using hS) hst (by
              simpa [A, S] using hsMin)
          change (finiteEventCountTop ξ s ω : ℝ) = (finiteEventCountTop ξ t ω : ℝ)
          rw [finiteEventCountTop, finiteEventCountTop, hfilter]
        have hconst : ContinuousWithinAt
            (fun _ : ℝ≥0 ↦ (finiteEventCountTop ξ t ω : ℝ)) (Ici t) t :=
          continuousWithinAt_const
        exact hconst.congr_of_eventuallyEq hev rfl
  · have hfuture : ∀ i, ¬(t : WithTop ℝ≥0) < ξ i ω := by
      intro i hi
      exact hS ⟨i, by
        simpa [S] using
          (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩ :
            i ∈ (Finset.univ : Finset (Fin m)).filter
              (fun j ↦ (t : WithTop ℝ≥0) < ξ j ω))⟩
    have hev : (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) =ᶠ[𝓝[Ici t] t]
        (fun _ ↦ (finiteEventCountTop ξ t ω : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hst
      have hfilter := finiteEventCountTop_filter_eq_of_no_future ξ ω t s hst hfuture
      change (finiteEventCountTop ξ s ω : ℝ) = (finiteEventCountTop ξ t ω : ℝ)
      rw [finiteEventCountTop, finiteEventCountTop, hfilter]
    have hconst : ContinuousWithinAt
        (fun _ : ℝ≥0 ↦ (finiteEventCountTop ξ t ω : ℝ)) (Ici t) t :=
      continuousWithinAt_const
    exact hconst.congr_of_eventuallyEq hev rfl

/-- The labels strictly below an attained generalized jump have cardinality at most its label. -/
theorem finiteEventCountTop_strictBelow_card_le {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (k : ℕ) (q : ℝ≥0)
    (hq : jumpTime (fun t ω ↦ finiteEventCountTop ξ t ω) k ω = q) :
    ((Finset.univ.filter (fun i ↦ ξ i ω < (q : WithTop ℝ≥0))).card) ≤ k := by
  classical
  let C : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω < (q : WithTop ℝ≥0))
  by_cases hC : C.Nonempty
  · obtain ⟨i, hiC, hmax⟩ := Finset.exists_max_image C (fun j ↦ ξ j ω) hC
    have hxi_lt : ξ i ω < (q : WithTop ℝ≥0) := (Finset.mem_filter.mp hiC).2
    have hxi_ne_top : ξ i ω ≠ ⊤ := by
      intro htop
      rw [htop] at hxi_lt
      exact (WithTop.not_top_lt (q : WithTop ℝ≥0)) hxi_lt
    let u : ℝ≥0 := (ξ i ω).untop hxi_ne_top
    have hxi_eq : (u : WithTop ℝ≥0) = ξ i ω := WithTop.coe_untop _ _
    have huq : u < q := by
      apply WithTop.coe_lt_coe.mp
      rw [hxi_eq]
      exact hxi_lt
    have hsub : C ⊆ Finset.univ.filter
        (fun j ↦ ξ j ω ≤ (u : WithTop ℝ≥0)) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        calc
          ξ j ω ≤ ξ i ω := hmax j hj
          _ = (u : WithTop ℝ≥0) := hxi_eq.symm⟩
    have hcard_sub : C.card ≤ finiteEventCountTop ξ u ω := by
      rw [finiteEventCountTop]
      exact Finset.card_le_card hsub
    have hNu : finiteEventCountTop ξ u ω ≤ k := by
      by_contra hnot
      have hku : k < finiteEventCountTop ξ u ω := Nat.lt_of_not_ge hnot
      have hle : q ≤ u := by
        rw [← hq]
        exact jumpTime_le_of_lt hku
      exact (not_le_of_gt huq) hle
    exact hcard_sub.trans hNu
  · have hCeq : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    change C.card ≤ k
    rw [hCeq]
    simp

/-- Every attained generalized jump time is one of the finite event labels. -/
theorem finiteEventCountTop_jumpTime_mem {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) {k : ℕ} {T : ℝ≥0}
    (hk : k < finiteEventCountTop ξ T ω) :
    ∃ i : Fin m, ξ i ω ≠ ⊤ ∧
      ξ i ω = (jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω') k ω :
        WithTop ℝ≥0) := by
  let N : ℝ≥0 → Ω → ℕ := fun t ω' ↦ finiteEventCountTop ξ t ω'
  have hkN : k < N T ω := by
    simpa [N] using hk
  have hmono : Monotone (fun t ↦ N t ω) := by
    intro s t hst
    exact finiteEventCountTop_mono ξ ω hst
  have hrc : ∀ t, ContinuousWithinAt
      (fun s ↦ (N s ω : ℝ)) (Ici t) t := by
    intro t
    simpa [N] using finiteEventCountTop_rightContinuous ξ ω t
  have hkq : k < N (jumpTime N k ω) ω := by
    apply lt_of_jumpTime_le hmono hrc ⟨T, hkN⟩
    exact le_rfl
  let q : ℝ≥0 := jumpTime N k ω
  have hkq' : k < N q ω := by
    simpa [q] using hkq
  have hq : jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω') k ω = q := by
    rfl
  let B : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω ≤ (q : WithTop ℝ≥0))
  let C : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω < (q : WithTop ℝ≥0))
  let D : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω = (q : WithTop ℝ≥0))
  have hB_gt : k < B.card := by
    change k < finiteEventCountTop ξ q ω
    exact hkq'
  have hC_le : C.card ≤ k := by
    simpa [C] using (finiteEventCountTop_strictBelow_card_le ξ ω k q hq)
  have hB_eq : B = C ∪ D := by
    ext i
    simp only [B, C, D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hi
      rcases lt_or_eq_of_le hi with hi_lt | hi_eq
      · exact Or.inl hi_lt
      · exact Or.inr hi_eq
    · rintro (hi | hi)
      · exact hi.le
      · exact hi.le
  have hD_nonempty : D.Nonempty := by
    by_contra hD
    have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hB_le : B.card ≤ k := by
      simpa [hB_eq, hDempty] using hC_le
    exact (Nat.not_lt_of_ge hB_le) hB_gt
  rcases hD_nonempty with ⟨i, hiD⟩
  have hiEq : ξ i ω = (q : WithTop ℝ≥0) :=
    (Finset.mem_filter.mp hiD).2
  have hiTop : ξ i ω ≠ ⊤ := by
    intro hi_top
    rw [hi_top] at hiEq
    exact WithTop.coe_ne_top hiEq.symm
  refine ⟨i, hiTop, ?_⟩
  simpa [q, N] using hiEq

/-- Cross-family finite-label separation gives separation of attained generalized jump times. -/
theorem finiteEventCountTop_cross_jumpTime_ne {m n : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (η : Fin n → Ω → WithTop ℝ≥0)
    (hξη : ∀ ω i j, ξ i ω ≠ ⊤ → η j ω ≠ ⊤ → ξ i ω ≠ η j ω)
    (ω : Ω) {k l : ℕ} {T : ℝ≥0}
    (hk : k < finiteEventCountTop ξ T ω)
    (hl : l < finiteEventCountTop η T ω) :
    jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω') k ω ≠
      jumpTime (fun t ω' ↦ finiteEventCountTop η t ω') l ω := by
  intro htimes
  rcases finiteEventCountTop_jumpTime_mem ξ ω hk with ⟨i, hi_top, hi_eq⟩
  rcases finiteEventCountTop_jumpTime_mem η ω hl with ⟨j, hj_top, hj_eq⟩
  apply hξη ω i j hi_top hj_top
  calc
    ξ i ω = (jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω') k ω :
      WithTop ℝ≥0) := hi_eq
    _ = (jumpTime (fun t ω' ↦ finiteEventCountTop η t ω') l ω :
      WithTop ℝ≥0) := by rw [htimes]
    _ = η j ω := hj_eq.symm

/-- Distinct finite event labels yield injective generalized jump times on attained labels. -/
theorem finiteEventCountTop_jumpTime_injOn {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    (hξ : ∀ i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (hrc : ∀ t, ContinuousWithinAt
      (fun s ↦ (finiteEventCountTop ξ s ω : ℝ)) (Ici t) t)
    (t : ℝ≥0) :
    Set.InjOn
      (fun k ↦ jumpTime (fun s ω' ↦ finiteEventCountTop ξ s ω') k ω)
      (Iio (finiteEventCountTop ξ t ω)) := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω' ↦ finiteEventCountTop ξ s ω'
  have hmono : Monotone (fun s ↦ N s ω) := by
    intro s u hsu
    exact finiteEventCountTop_mono ξ ω hsu
  have hstrict : ∀ {k l : ℕ}, k < l → k < N t ω → l < N t ω →
      jumpTime N k ω ≠ jumpTime N l ω := by
    intro k l hkl hk hl heq
    let q : ℝ≥0 := jumpTime N k ω
    have hq_eq_l : jumpTime N l ω = q := by
      simpa [q] using heq.symm
    have hqk : k < N q ω := by
      exact lt_of_jumpTime_le hmono hrc ⟨t, hk⟩ le_rfl
    have hql : l < N q ω := by
      rw [← hq_eq_l]
      exact lt_of_jumpTime_le hmono hrc ⟨t, hl⟩ le_rfl
    let B : Finset (Fin m) := Finset.univ.filter
      (fun i ↦ ξ i ω ≤ (q : WithTop ℝ≥0))
    let C : Finset (Fin m) := Finset.univ.filter
      (fun i ↦ ξ i ω < (q : WithTop ℝ≥0))
    let D : Finset (Fin m) := Finset.univ.filter
      (fun i ↦ ξ i ω = (q : WithTop ℝ≥0))
    have hBcard : l < B.card := by
      change l < finiteEventCountTop ξ q ω
      exact hql
    have hCcard : C.card ≤ k := by
      apply finiteEventCountTop_strictBelow_card_le ξ ω k q
      exact rfl
    have hB_eq : B = C ∪ D := by
      ext i
      simp only [B, C, D, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      constructor
      · intro hi
        rcases lt_or_eq_of_le hi with hi_lt | hi_eq
        · exact Or.inl hi_lt
        · exact Or.inr hi_eq
      · rintro (hi | hi)
        · exact hi.le
        · exact hi.le
    have hCD : Disjoint C D := by
      rw [Finset.disjoint_left]
      intro i hiC hiD
      exact (ne_of_lt (Finset.mem_filter.mp hiC).2) (Finset.mem_filter.mp hiD).2
    have hBDcard : B.card = C.card + D.card := by
      rw [hB_eq, Finset.card_union_of_disjoint hCD]
    have hDcard : D.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      apply hξ i j
      · intro htop
        apply WithTop.not_top_le_coe q
        rw [← htop]
        exact (Finset.mem_filter.mp hi).2.le
      · intro htop
        apply WithTop.not_top_le_coe q
        rw [← htop]
        exact (Finset.mem_filter.mp hj).2.le
      · exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    have hB_le : B.card ≤ k + 1 := by
      rw [hBDcard]
      omega
    omega
  intro k hk l hl heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hkl
  · exact hstrict hkl hk hl heq
  · exact hstrict hkl hl hk heq.symm

open _root_.MeasureTheory

/-- Construct a simple counting process from top-valued finite event times and explicit adaptedness.

The first hypothesis handles zero-time fallback labels, the second excludes simultaneous finite
event times, and adaptedness is intentionally supplied as a separate hypothesis.
-/
theorem IsSimpleCountingProcess.of_finiteEventCountTop
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hξpos : ∀ ω i, ξ i ω = ⊤ ∨ (0 : WithTop ℝ≥0) < ξ i ω)
    (hξ : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (hadapt : StronglyAdapted ℱ
      (fun t ω ↦ (finiteEventCountTop ξ t ω : ℝ))) :
    IsSimpleCountingProcess ℱ (fun t ω ↦ finiteEventCountTop ξ t ω) := by
  refine ⟨?_, hadapt, ?_, ?_, ?_⟩
  · funext ω
    exact finiteEventCountTop_zero ξ ω (hξpos ω)
  · intro ω s u hsu
    exact finiteEventCountTop_mono ξ ω hsu
  · intro ω t
    exact finiteEventCountTop_rightContinuous ξ ω t
  · intro ω t
    exact finiteEventCountTop_jumpTime_injOn ξ ω (hξ ω)
      (finiteEventCountTop_rightContinuous ξ ω) t

end OTSelector.CountingProcess
