import OTSelector.Feedback.FeedbackMarkedMean
import OTSelector.Feedback.FiniteEventBulkGlobalBranchSum
import OTSelector.Feedback.FiniteEventBulkIntensity

/-!
# The actual geometric-mark sums on finite bulk events

Each retained labelled crossing contributes the test of its original geometric mark. The
revealed snapshot contains that mark by the crossing time, which proves adaptation without
assuming a marked intensity. Finite sums give pathwise bounds and right continuity.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*} {m : ℕ}

/-- A finite labelled event sum with an arbitrary real weight on each original label. -/
noncomputable def finiteEventWeightedSum (ξ : Fin m → Ω → WithTop ℝ≥0)
    (w : Fin m → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin m, if ξ i ω ≤ (t : WithTop ℝ≥0) then w i ω else 0

theorem finiteEventWeightedSum_sub (ξ : Fin m → Ω → WithTop ℝ≥0)
    (w : Fin m → Ω → ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    finiteEventWeightedSum ξ w t ω - finiteEventWeightedSum ξ w s ω =
      ∑ i : Fin m, if ξ i ω ∈ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)
        then w i ω else 0 := by
  classical
  unfold finiteEventWeightedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : ξ i ω ≤ (s : WithTop ℝ≥0)
  · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
    simp only [mem_Ioc, ite_eq_left hs, ite_eq_left ht, not_lt_of_ge hs, false_and,
      ite_false, sub_self]
  · by_cases ht : ξ i ω ≤ (t : WithTop ℝ≥0)
    · simp only [mem_Ioc, ite_eq_right hs, ite_eq_left ht, lt_of_not_ge hs,
        true_and, sub_zero]
    · simp only [mem_Ioc, ite_eq_right hs, ht, and_false, sub_zero]

theorem finiteEventWeightedSum_rightContinuous (ξ : Fin m → Ω → WithTop ℝ≥0)
    (w : Fin m → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ finiteEventWeightedSum ξ w s ω) (Ici t) t := by
  classical
  apply tendsto_finsetSum
  intro i _
  have h := (finiteEventCountTop_rightContinuous (fun _ : Fin 1 ↦ ξ i) ω t).mul_const
    (w i ω)
  simpa only [finiteEventCountTop_cast_eq_sum, Fin.sum_univ_one, ite_mul, one_mul,
    zero_mul] using h.tendsto

theorem norm_finiteEventWeightedSum_le (ξ : Fin m → Ω → WithTop ℝ≥0)
    (w : Fin m → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i ω, ‖w i ω‖ ≤ C)
    (t : ℝ≥0) (ω : Ω) : ‖finiteEventWeightedSum ξ w t ω‖ ≤ (m : ℝ) * C := by
  classical
  unfold finiteEventWeightedSum
  calc
    _ ≤ ∑ i : Fin m, ‖if ξ i ω ≤ (t : WithTop ℝ≥0) then w i ω else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin m, C := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact hw i ω
      · simpa using hC
    _ = _ := by simp

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess

variable {n : ℕ} {lam : ℝ}

/-- Sum the original source marks over the actual bulk-retained crossings. -/
noncomputable def safeSourceBulkMarkSum (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  finiteEventWeightedSum
    (fun i ↦ thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i))
    (fun i sample ↦ ψ (sample.sourceMark i))

/-- Sum the original target marks over the actual bulk-retained crossings. -/
noncomputable def safeTargetBulkMarkSum (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  finiteEventWeightedSum
    (fun j ↦ thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (targetEventTime hlam0 hlamHalf x0 p0 j))
    (fun j sample ↦ ψ (sample.targetMark j))

/-- The actual source mark sum is adapted because every counted mark is already revealed. -/
theorem safeSourceBulkMarkSum_stronglyAdapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Measurable ψ) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ) := by
  classical
  intro t
  have hsnap := (stronglyAdapted_rawRevealedSnapshot (n := n) hlam0 hlamHalf x0 p0 t).mono
    (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 t)
  unfold safeSourceBulkMarkSum finiteEventWeightedSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hvisible : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample ↦ ψ ((((sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).2.1) i).2.2)) :=
    hψ.comp (((measurable_pi_apply i).comp hsnap.measurable.snd.fst).snd.snd)
  have ht := isStoppingTime_thinnedEventTime_of_predictable
    (sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 i)
    (safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0)
  have hm : StronglyMeasurable[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample ↦ if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ≤ (t : WithTop ℝ≥0) then
          ψ (((sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).2.1 i).2.2)
        else 0) := (Measurable.ite (ht t) hvisible measurable_const).stronglyMeasurable
  convert hm using 1
  funext sample
  split_ifs with h
  · have he := (thinnedEventTime_le_iff sample t).mp h
    have hseen := (sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 i t).mp he.2
    have hi := (Finset.mem_sdiff.mp hseen.2).1
    simp only [revealedSnapshotAtElapsed, revealedSnapshotFromState, maskedSourceArray,
      maskedSourcePoint, ite_eq_left hi, sourcePoint]
  · rfl

theorem safeSourceBulkMarkSum_rightContinuous
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ s sample)
      (Ici t) t :=
  finiteEventWeightedSum_rightContinuous _ _ sample t

theorem norm_safeSourceBulkMarkSum_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) {C : ℝ} (hC : 0 ≤ C) (hψ : ∀ u, ‖ψ u‖ ≤ C)
    (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤ (n : ℝ) * C :=
  norm_finiteEventWeightedSum_le (m := n) _ _ hC
    (fun i (sample : FiniteSample n) ↦ hψ (sample.sourceMark i)) t sample

/-- The actual target mark sum is adapted because every counted mark is already revealed. -/
theorem safeTargetBulkMarkSum_stronglyAdapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Measurable ψ) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ) := by
  classical
  intro t
  have hsnap := (stronglyAdapted_rawRevealedSnapshot (n := n) hlam0 hlamHalf x0 p0 t).mono
    (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 t)
  unfold safeTargetBulkMarkSum finiteEventWeightedSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hvisible : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample ↦ ψ ((((sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).2.2) i).2.2)) :=
    hψ.comp (((measurable_pi_apply i).comp hsnap.measurable.snd.snd).snd.snd)
  have ht := isStoppingTime_thinnedEventTime_of_predictable
    (targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 i)
    (safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0)
  have hm : StronglyMeasurable[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample ↦ if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 i) sample ≤ (t : WithTop ℝ≥0) then
          ψ (((sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).2.2 i).2.2)
        else 0) := (Measurable.ite (ht t) hvisible measurable_const).stronglyMeasurable
  convert hm using 1
  funext sample
  split_ifs with h
  · have he := (thinnedEventTime_le_iff sample t).mp h
    have hseen := (sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 i t).mp he.2
    have hi := (Finset.mem_sdiff.mp hseen.2).1
    simp only [revealedSnapshotAtElapsed, revealedSnapshotFromState, maskedTargetArray,
      maskedTargetPoint, ite_eq_left hi, targetPoint]
  · rfl

theorem safeTargetBulkMarkSum_rightContinuous
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ s sample)
      (Ici t) t :=
  finiteEventWeightedSum_rightContinuous _ _ sample t

theorem norm_safeTargetBulkMarkSum_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) {C : ℝ} (hC : 0 ≤ C) (hψ : ∀ u, ‖ψ u‖ ≤ C)
    (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤ (n : ℝ) * C :=
  norm_finiteEventWeightedSum_le (m := n) _ _ hC
    (fun i (sample : FiniteSample n) ↦ hψ (sample.targetMark i)) t sample

end OTSelector.FiniteSample
