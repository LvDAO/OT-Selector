import Mathlib.Data.Fin.Tuple.Sort
import OTSelector.Feedback.RevealedCounting

/-!
# Finite rank-arrival stopping times

This file defines the `k`-th arrival time of a finite family of top-valued event times.  The
order statistic is characterized exactly by the number of labels attained by a finite threshold;
this turns any finite family of stopping times into a stopping rank time.

The second half specializes the construction to the actual safe source and target event times.
Their pointwise minimum is the left rank-arrival time.  No cross-colour orientation event is
claimed to belong to a stopping-time sigma algebra here.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

namespace CountingProcess

variable {Omega : Type*} {n : ℕ}

/-! ## Generic finite rank times -/

/-- The `k`-th order statistic of a finite family of top-valued event times. -/
noncomputable def finiteRankEventTime
    (tau : Fin n → Omega → WithTop ℝ≥0) (k : Fin n) : Omega → WithTop ℝ≥0 :=
  fun omega ↦ tau (Tuple.sort (fun i ↦ tau i omega) k) omega

/-- A finite rank time has arrived by `t` exactly when more than `k` labels have arrived by `t`.

The rank is zero-based: `k = 0` is the first order statistic. -/
theorem finiteRankEventTime_le_iff_lt_finiteEventCountTop
    (tau : Fin n → Omega → WithTop ℝ≥0) (k : Fin n) (omega : Omega) (t : ℝ≥0) :
    finiteRankEventTime tau k omega ≤ (t : WithTop ℝ≥0) ↔
      k.val < finiteEventCountTop tau t omega := by
  classical
  let values : Fin n → WithTop ℝ≥0 := fun i ↦ tau i omega
  have hsorted : Monotone (values ∘ Tuple.sort values) :=
    Tuple.monotone_sort values
  have horder :
      k.val < (Finset.univ.filter (fun i : Fin n ↦
        values (Tuple.sort values i) ≤ (t : WithTop ℝ≥0))).card ↔
        values (Tuple.sort values k) ≤ (t : WithTop ℝ≥0) := by
    simpa only [Function.comp_apply] using
      (Tuple.lt_card_le_iff_apply_le_of_monotone
        (j := k) (a := (t : WithTop ℝ≥0)) hsorted)
  have hcard :
      (Finset.univ.filter (fun i : Fin n ↦
        values (Tuple.sort values i) ≤ (t : WithTop ℝ≥0))).card =
        (Finset.univ.filter (fun i : Fin n ↦
          values i ≤ (t : WithTop ℝ≥0))).card := by
    apply Finset.card_equiv (Tuple.sort values)
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change values (Tuple.sort values k) ≤ (t : WithTop ℝ≥0) ↔
    k.val < (Finset.univ.filter (fun i : Fin n ↦
      values i ≤ (t : WithTop ℝ≥0))).card
  rw [← hcard]
  exact horder.symm

/-- Selecting an order statistic preserves the positive-or-top alternative. -/
theorem finiteRankEventTime_eq_top_or_pos
    (tau : Fin n → Omega → WithTop ℝ≥0) (k : Fin n) (omega : Omega)
    (htau : ∀ i, tau i omega = ⊤ ∨ (0 : WithTop ℝ≥0) < tau i omega) :
    finiteRankEventTime tau k omega = ⊤ ∨
      (0 : WithTop ℝ≥0) < finiteRankEventTime tau k omega := by
  simpa only [finiteRankEventTime] using
    htau (Tuple.sort (fun i ↦ tau i omega) k)

section Stopping

variable [MeasurableSpace Omega]

/-- The real cast of a finite attained-label count is measurable at the current filtration time
when every label time is a stopping time. -/
theorem finiteEventCountTop_cast_measurable_of_stoppingTimes
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega))
    (tau : Fin n → Omega → WithTop ℝ≥0)
    (htau : ∀ i, IsStoppingTime F (tau i)) (t : ℝ≥0) :
    Measurable[F t] (fun omega ↦ (finiteEventCountTop tau t omega : ℝ)) := by
  classical
  let contribution : Fin n → Omega → ℝ := fun i omega ↦
    if tau i omega ≤ (t : WithTop ℝ≥0) then 1 else 0
  have hsum : Measurable[F t]
      (fun omega ↦ ∑ i : Fin n, contribution i omega) := by
    apply Finset.measurable_sum (Finset.univ : Finset (Fin n))
    intro i hi
    exact Measurable.ite ((htau i).measurableSet_le t)
      measurable_const measurable_const
  convert hsum using 1
  funext omega
  simpa only [contribution] using
    (finiteEventCountTop_cast_eq_sum (R := ℝ) tau t omega)

/-- Every order statistic of a finite family of stopping times is a stopping time. -/
theorem finiteRankEventTime_isStoppingTime
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega))
    (tau : Fin n → Omega → WithTop ℝ≥0) (k : Fin n)
    (htau : ∀ i, IsStoppingTime F (tau i)) :
    IsStoppingTime F (finiteRankEventTime tau k) := by
  intro t
  have hcount : MeasurableSet[F t]
      {omega | k.val < finiteEventCountTop tau t omega} := by
    have hreal : MeasurableSet[F t]
        {omega | (k.val : ℝ) < (finiteEventCountTop tau t omega : ℝ)} :=
      measurableSet_lt measurable_const
        (finiteEventCountTop_cast_measurable_of_stoppingTimes F tau htau t)
    convert hreal using 1
    ext omega
    simp
  rw [show {omega | finiteRankEventTime tau k omega ≤ (t : WithTop ℝ≥0)} =
      {omega | k.val < finiteEventCountTop tau t omega} by
    ext omega
    exact finiteRankEventTime_le_iff_lt_finiteEventCountTop tau k omega t]
  exact hcount

end Stopping

end CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-! ## Actual source and target rank times -/

/-- The `k`-th safe source-event arrival time. -/
noncomputable def sourceRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.finiteRankEventTime
    (fun i ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) k

/-- The `k`-th safe target-event arrival time. -/
noncomputable def targetRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.finiteRankEventTime
    (fun j ↦ targetEventTime hlam0 hlamHalf x0 p0 j) k

/-- The source rank time is controlled by the actual safe source count. -/
theorem sourceRankEventTime_le_iff_lt_safeSourceCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (t : ℝ≥0) (omega : FiniteSample n) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k omega ≤ (t : WithTop ℝ≥0) ↔
      k.val < safeSourceCount hlam0 hlamHalf x0 p0 t omega := by
  simpa only [sourceRankEventTime, safeSourceCount] using
    (CountingProcess.finiteRankEventTime_le_iff_lt_finiteEventCountTop
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) k omega t)

/-- The target rank time is controlled by the actual safe target count. -/
theorem targetRankEventTime_le_iff_lt_safeTargetCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (t : ℝ≥0) (omega : FiniteSample n) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k omega ≤ (t : WithTop ℝ≥0) ↔
      k.val < safeTargetCount hlam0 hlamHalf x0 p0 t omega := by
  simpa only [targetRankEventTime, safeTargetCount] using
    (CountingProcess.finiteRankEventTime_le_iff_lt_finiteEventCountTop
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) k omega t)

/-- The actual source rank time is a stopping time. -/
theorem sourceRankEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (sourceRankEventTime hlam0 hlamHalf x0 p0 k) := by
  exact CountingProcess.finiteRankEventTime_isStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) k
    (fun i ↦ sourceEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf x0 p0 i)

/-- The actual target rank time is a stopping time. -/
theorem targetRankEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (targetRankEventTime hlam0 hlamHalf x0 p0 k) := by
  exact CountingProcess.finiteRankEventTime_isStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) k
    (fun j ↦ targetEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf x0 p0 j)

/-- The actual source rank time is either the top fallback or strictly positive. -/
theorem sourceRankEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (omega : FiniteSample n) (k : Fin n) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k omega = ⊤ ∨
      (0 : WithTop ℝ≥0) < sourceRankEventTime hlam0 hlamHalf x0 p0 k omega := by
  apply CountingProcess.finiteRankEventTime_eq_top_or_pos
  intro i
  exact sourceEventTime_eq_top_or_pos
    (n := n) hlam0 hlamHalf x0 p0 omega i

/-- The actual target rank time is either the top fallback or strictly positive. -/
theorem targetRankEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (omega : FiniteSample n) (k : Fin n) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k omega = ⊤ ∨
      (0 : WithTop ℝ≥0) < targetRankEventTime hlam0 hlamHalf x0 p0 k omega := by
  apply CountingProcess.finiteRankEventTime_eq_top_or_pos
  intro j
  exact targetEventTime_eq_top_or_pos
    (n := n) hlam0 hlamHalf x0 p0 omega j

/-! ## Left rank arrival and elementary orientation facts -/

/-- The first of the source and target arrivals at rank `k`. -/
noncomputable def feedbackRankLeftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun omega ↦ min
    (sourceRankEventTime hlam0 hlamHalf x0 p0 k omega)
    (targetRankEventTime hlam0 hlamHalf x0 p0 k omega)

@[simp]
theorem feedbackRankLeftTime_eq_min
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (omega : FiniteSample n) :
    feedbackRankLeftTime hlam0 hlamHalf x0 p0 k omega = min
      (sourceRankEventTime hlam0 hlamHalf x0 p0 k omega)
      (targetRankEventTime hlam0 hlamHalf x0 p0 k omega) :=
  rfl

private theorem stoppingTime_min_nnreal
    {Omega : Type*} {m : MeasurableSpace Omega}
    {F : Filtration ℝ≥0 m} {sigma tau : Omega → WithTop ℝ≥0}
    (hsigma : IsStoppingTime F sigma) (htau : IsStoppingTime F tau) :
    IsStoppingTime F (fun omega ↦ min (sigma omega) (tau omega)) :=
  hsigma.min htau

/-- The left rank-arrival time is a stopping time. -/
theorem feedbackRankLeftTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (feedbackRankLeftTime hlam0 hlamHalf x0 p0 k) := by
  change IsStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun omega ↦ min
      (sourceRankEventTime hlam0 hlamHalf x0 p0 k omega)
      (targetRankEventTime hlam0 hlamHalf x0 p0 k omega))
  exact stoppingTime_min_nnreal
    (sourceRankEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf x0 p0 k)
    (targetRankEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf x0 p0 k)

/-- The left rank arrival occurs no later than the source rank arrival. -/
theorem feedbackRankLeftTime_le_sourceRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (omega : FiniteSample n) :
    feedbackRankLeftTime hlam0 hlamHalf x0 p0 k omega ≤
      sourceRankEventTime hlam0 hlamHalf x0 p0 k omega := by
  exact min_le_left _ _

/-- The left rank arrival occurs no later than the target rank arrival. -/
theorem feedbackRankLeftTime_le_targetRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (omega : FiniteSample n) :
    feedbackRankLeftTime hlam0 hlamHalf x0 p0 k omega ≤
      targetRankEventTime hlam0 hlamHalf x0 p0 k omega := by
  exact min_le_right _ _

/-- Distinct source and target rank arrivals have one of the two strict orientations. -/
theorem sourceRankEventTime_lt_or_gt_targetRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) (omega : FiniteSample n)
    (hne : sourceRankEventTime hlam0 hlamHalf x0 p0 k omega ≠
      targetRankEventTime hlam0 hlamHalf x0 p0 k omega) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k omega <
        targetRankEventTime hlam0 hlamHalf x0 p0 k omega ∨
      targetRankEventTime hlam0 hlamHalf x0 p0 k omega <
        sourceRankEventTime hlam0 hlamHalf x0 p0 k omega :=
  lt_or_gt_of_ne hne

end FiniteSample

end OTSelector
