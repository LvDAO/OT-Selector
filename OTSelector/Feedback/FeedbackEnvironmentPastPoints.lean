import OTSelector.Feedback.FeedbackMarkedSceneReadout
import OTSelector.Feedback.FeedbackRightBoundary
import OTSelector.PointProcess.MatchingScenePerfect

/-!
# Past point tests from the actual revealed exploration

A test vanishing on the nonnegative half line sees only labels already revealed. Its
post-initial contribution can use the event time capped at the observation time: unrevealed
labels then have coordinate zero and contribute zero. This gives a globally adapted process
before any comparison with the stopped graph.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped Classical BigOperators NNReal CompactlySupported

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector
namespace CountingProcess

/-- A capped genuine stopping coordinate is measurable at the cap, not only ambient measurable. -/
theorem measurable_cappedStoppingValue_at_cap {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (u : ℝ≥0) :
    Measurable[F u] (cappedStoppingValue u τ) := by
  exact ((hτ.min_const u).measurable_of_le (fun _ ↦ min_le_right _ _)).untopD 0

/-- Joint measurability of the actual cap in time and sample. -/
theorem measurable_uncurry_cappedStoppingValue {Ω : Type*} [MeasurableSpace Ω]
    {τ : Ω → WithTop ℝ≥0} (hτ : Measurable τ) :
    Measurable (fun p : ℝ≥0 × Ω ↦ cappedStoppingValue p.1 τ p.2) :=
  ((hτ.comp measurable_snd).min (Measurable.withTop_coe measurable_fst)).untopD 0

/-- A non-arrived label has capped coordinate exactly at the observation root. -/
theorem cappedStoppingValue_eq_cap_of_not_le {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → WithTop ℝ≥0) (u : ℝ≥0) (ω : Ω) (h : ¬ τ ω ≤ (u : WithTop ℝ≥0)) :
    cappedStoppingValue u τ ω = u := by
  apply WithTop.coe_injective
  rw [coe_cappedStoppingValue, min_eq_right (le_of_lt (lt_of_not_ge h))]

end CountingProcess

namespace FiniteSample

open PointProcess CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual source past test, represented using the original initial labels and event clocks. -/
noncomputable def safeSourcePastTest (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  ∑ i : Fin n, if i ∈ sample.initialSeenSource B 0 then
    f ((n : ℝ) * sample.sourceHeight i - (B + (u : ℝ)), sample.sourceMark i)
  else f ((cappedStoppingValue u (sourceEventTime hlam0 hlamHalf B 0 i) sample : ℝ) - u,
    sample.sourceMark i)

/-- Each past test is adapted in the original usual revealed filtration. -/
theorem safeSourcePastTest_stronglyAdapted (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : Measurable f) (hf0 : ∀ v, f (0,v) = 0) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (safeSourcePastTest hlam0 hlamHalf B f) := by
  classical
  intro u
  have hsnap := (stronglyAdapted_rawRevealedSnapshot (n := n) hlam0 hlamHalf B 0 u).mono
    (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf B 0 u)
  unfold safeSourcePastTest
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hm := ((measurable_pi_apply i).comp hsnap.measurable.snd.fst).snd
  have hcap := measurable_cappedStoppingValue_at_cap _
    (sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i) u
  have hinit := measurableSet_mem_initialSeenSource_usual hlam0 hlamHalf B 0 u i
  have hvisible : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 u]
      (fun sample ↦ if i ∈ sample.initialSeenSource B 0 then
        f ((n : ℝ) * (((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.1 i).2.1 : ℝ) -
          (B + (u : ℝ)), ((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.1 i).2.2)
      else f ((cappedStoppingValue u (sourceEventTime hlam0 hlamHalf B 0 i) sample : ℝ) - u,
        ((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.1 i).2.2)) :=
    Measurable.ite hinit
      (hf.comp (((measurable_const.mul hm.fst.subtype_coe).sub measurable_const).prodMk hm.snd))
      (hf.comp (((measurable_coe_nnreal_real.comp hcap).sub measurable_const).prodMk hm.snd))
  convert hvisible.stronglyMeasurable using 1
  funext sample
  by_cases hi : i ∈ sample.initialSeenSource B 0
  · have hseen : i ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf B 0 u).seenSource := by
      apply sample.mem_feedbackState_seenSource_mono lam B 0 i (Nat.zero_le _)
      simpa [feedbackState_zero, initialFeedbackState] using hi
    simp only [hi, ite_true, revealedSnapshotAtElapsed, revealedSnapshotFromState,
      maskedSourceArray, maskedSourcePoint, hseen, sourcePoint]
  · by_cases he : sourceEventTime hlam0 hlamHalf B 0 i sample ≤ (u : WithTop ℝ≥0)
    · have hseen := (Finset.mem_sdiff.mp
        ((sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 i u).mp he).2).1
      simp only [hi, ite_false, revealedSnapshotAtElapsed, revealedSnapshotFromState,
        maskedSourceArray, maskedSourcePoint, hseen, ite_true, sourcePoint]
    · rw [ite_eq_right hi, ite_eq_right hi, cappedStoppingValue_eq_cap_of_not_le _ u sample he]
      simp only [sub_self, hf0]

/-- The same actual past process is jointly measurable in observation time and sample. -/
theorem measurable_safeSourcePastTest (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : Measurable f) :
    Measurable (Function.uncurry (safeSourcePastTest (n := n) hlam0 hlamHalf B f)) := by
  classical
  unfold Function.uncurry safeSourcePastTest
  apply Finset.measurable_sum
  intro i _
  have hinit := (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0).le 0 _
    (measurableSet_mem_initialSeenSource_usual_zero hlam0 hlamHalf B 0 i)
  have hh : Measurable (fun p : ℝ≥0 × FiniteSample n ↦ p.2.sourceHeight i) :=
    (FiniteSample.measurable_sourceHeight i).comp measurable_snd
  have hm : Measurable (fun p : ℝ≥0 × FiniteSample n ↦ p.2.sourceMark i) :=
    (FiniteSample.measurable_sourceMark i).comp measurable_snd
  have hcap := measurable_uncurry_cappedStoppingValue
    (sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i).measurable'
  exact Measurable.ite (hinit.preimage measurable_snd)
    (hf.comp (((measurable_const.mul hh.subtype_coe).sub
      (measurable_const.add measurable_fst.subtype_coe)).prodMk hm))
    (hf.comp (((measurable_coe_nnreal_real.comp hcap).sub measurable_fst.subtype_coe).prodMk hm))

/-- Before exploration starts the original graph is horizontal, so an initial label retains
its original horizontal coordinate. -/
theorem sourceIntersection_eq_initial_coordinate (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (sample : FiniteSample n) (i : Fin n) (hi : i ∈ sample.initialSeenSource B 0) :
    sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i =
      (n : ℝ) * sample.sourceHeight i := by
  have hx : (n : ℝ) * sample.sourceHeight i ≤ B := by
    simpa [initialSeenSource, sourcePhase] using hi
  symm
  apply sample.sourceIntersection_unique
  change sample.sourcePhase i (sample.feedbackCurve lam B 0 ((n : ℝ) * sample.sourceHeight i)) = _
  simp [feedbackCurve, hx, sourcePhase]

/-- A noninitial actual event clock is exactly its raw graph intersection minus the initial cut. -/
theorem sourceEventTime_eq_raw_intersection (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0)
    (i : Fin n) (hi : i ∉ sample.initialSeenSource B 0) :
    sourceEventTime hlam0 hlamHalf B 0 i sample =
      (Real.toNNReal (sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) :
        WithTop ℝ≥0) := by
  have hx : B < sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i := by
    rw [sample.initialSeenSource_eq_sourceIntersection_filter hlam0 hlamHalf B 0] at hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  rw [sourceEventTime_le_iff_raw_intersection hlam0 hlamHalf B 0 t sample hgood i,
    WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  constructor
  · rintro ⟨_,h⟩; linarith
  · intro h; exact ⟨hx, by linarith⟩

/-- The adapted representation is the actual raw graph past point sum. -/
theorem safeSourcePastTest_eq_raw_sum (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0)
    (u : ℝ≥0) (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0) :
    safeSourcePastTest hlam0 hlamHalf B f u sample =
      ∑ i : Fin n, f (sample.rootedSourcePoint (sample.feedbackGraph hlam0 hlamHalf B 0)
        (B + (u : ℝ)) i) := by
  classical
  unfold safeSourcePastTest
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rootedSourcePoint]
  by_cases hi : i ∈ sample.initialSeenSource B 0
  · rw [ite_eq_left hi, sourceIntersection_eq_initial_coordinate hlam0 hlamHalf B sample i hi]
  · rw [ite_eq_right hi]
    have he := sourceEventTime_eq_raw_intersection hlam0 hlamHalf B sample hgood i hi
    have hx : 0 ≤ sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B := by
      rw [sample.initialSeenSource_eq_sourceIntersection_filter hlam0 hlamHalf B 0] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      linarith
    by_cases hu : sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i ≤ B + (u : ℝ)
    · have hle : Real.toNNReal (sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) ≤ u :=
        Real.toNNReal_le_iff_le_coe.mpr (by linarith)
      simp only [cappedStoppingValue, he, min_eq_left (WithTop.coe_le_coe.mpr hle),
        WithTop.untopD_coe, Real.coe_toNNReal _ hx]
      congr 2
      ring
    · have hle : u ≤ Real.toNNReal (sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hx]
        linarith
      simp only [cappedStoppingValue, he, min_eq_right (WithTop.coe_le_coe.mpr hle),
        WithTop.untopD_coe, sub_self, hf 0 _ le_rfl]
      exact (hf _ _ (by linarith)).symm

/-- The actual target past test, represented using the original initial labels and event clocks. -/
noncomputable def safeTargetPastTest (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  ∑ i : Fin n, if i ∈ sample.initialSeenTarget B 0 then
    f ((n : ℝ) * sample.targetHeight i - (B + (u : ℝ)), sample.targetMark i)
  else f ((cappedStoppingValue u (targetEventTime hlam0 hlamHalf B 0 i) sample : ℝ) - u,
    sample.targetMark i)

/-- Each past test is adapted in the original usual revealed filtration. -/
theorem safeTargetPastTest_stronglyAdapted (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : Measurable f) (hf0 : ∀ v, f (0,v) = 0) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (safeTargetPastTest hlam0 hlamHalf B f) := by
  classical
  intro u
  have hsnap := (stronglyAdapted_rawRevealedSnapshot (n := n) hlam0 hlamHalf B 0 u).mono
    (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf B 0 u)
  unfold safeTargetPastTest
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hm := ((measurable_pi_apply i).comp hsnap.measurable.snd.snd).snd
  have hcap := measurable_cappedStoppingValue_at_cap _
    (targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i) u
  have hinit := measurableSet_mem_initialSeenTarget_usual hlam0 hlamHalf B 0 u i
  have hvisible : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 u]
      (fun sample ↦ if i ∈ sample.initialSeenTarget B 0 then
        f ((n : ℝ) * (((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.2 i).2.1 : ℝ) -
          (B + (u : ℝ)), ((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.2 i).2.2)
      else f ((cappedStoppingValue u (targetEventTime hlam0 hlamHalf B 0 i) sample : ℝ) - u,
        ((sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 u).2.2 i).2.2)) :=
    Measurable.ite hinit
      (hf.comp (((measurable_const.mul hm.fst.subtype_coe).sub measurable_const).prodMk hm.snd))
      (hf.comp (((measurable_coe_nnreal_real.comp hcap).sub measurable_const).prodMk hm.snd))
  convert hvisible.stronglyMeasurable using 1
  funext sample
  by_cases hi : i ∈ sample.initialSeenTarget B 0
  · have hseen : i ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf B 0 u).seenTarget := by
      apply sample.mem_feedbackState_seenTarget_mono lam B 0 i (Nat.zero_le _)
      simpa [feedbackState_zero, initialFeedbackState] using hi
    simp only [hi, ite_true, revealedSnapshotAtElapsed, revealedSnapshotFromState,
      maskedTargetArray, maskedTargetPoint, hseen, targetPoint]
  · by_cases he : targetEventTime hlam0 hlamHalf B 0 i sample ≤ (u : WithTop ℝ≥0)
    · have hseen := (Finset.mem_sdiff.mp
        ((sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 i u).mp he).2).1
      simp only [hi, ite_false, revealedSnapshotAtElapsed, revealedSnapshotFromState,
        maskedTargetArray, maskedTargetPoint, hseen, ite_true, targetPoint]
    · rw [ite_eq_right hi, ite_eq_right hi, cappedStoppingValue_eq_cap_of_not_le _ u sample he]
      simp only [sub_self, hf0]

/-- The same actual past process is jointly measurable in observation time and sample. -/
theorem measurable_safeTargetPastTest (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : Measurable f) :
    Measurable (Function.uncurry (safeTargetPastTest (n := n) hlam0 hlamHalf B f)) := by
  classical
  unfold Function.uncurry safeTargetPastTest
  apply Finset.measurable_sum
  intro i _
  have hinit := (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0).le 0 _
    (measurableSet_mem_initialSeenTarget_usual_zero hlam0 hlamHalf B 0 i)
  have hh : Measurable (fun p : ℝ≥0 × FiniteSample n ↦ p.2.targetHeight i) :=
    (FiniteSample.measurable_targetHeight i).comp measurable_snd
  have hm : Measurable (fun p : ℝ≥0 × FiniteSample n ↦ p.2.targetMark i) :=
    (FiniteSample.measurable_targetMark i).comp measurable_snd
  have hcap := measurable_uncurry_cappedStoppingValue
    (targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i).measurable'
  exact Measurable.ite (hinit.preimage measurable_snd)
    (hf.comp (((measurable_const.mul hh.subtype_coe).sub
      (measurable_const.add measurable_fst.subtype_coe)).prodMk hm))
    (hf.comp (((measurable_coe_nnreal_real.comp hcap).sub measurable_fst.subtype_coe).prodMk hm))

/-- Before exploration starts the original graph is horizontal, so an initial label retains
its original horizontal coordinate. -/
theorem targetIntersection_eq_initial_coordinate (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (sample : FiniteSample n) (i : Fin n) (hi : i ∈ sample.initialSeenTarget B 0) :
    sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i =
      (n : ℝ) * sample.targetHeight i := by
  have hx : (n : ℝ) * sample.targetHeight i ≤ B := by
    simpa [initialSeenTarget, targetPhase] using hi
  symm
  apply sample.targetIntersection_unique
  change sample.targetPhase i (sample.feedbackCurve lam B 0 ((n : ℝ) * sample.targetHeight i)) = _
  simp [feedbackCurve, hx, targetPhase]

/-- A noninitial actual event clock is exactly its raw graph intersection minus the initial cut. -/
theorem targetEventTime_eq_raw_intersection (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0)
    (i : Fin n) (hi : i ∉ sample.initialSeenTarget B 0) :
    targetEventTime hlam0 hlamHalf B 0 i sample =
      (Real.toNNReal (sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) :
        WithTop ℝ≥0) := by
  have hx : B < sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i := by
    rw [sample.initialSeenTarget_eq_targetIntersection_filter hlam0 hlamHalf B 0] at hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  rw [targetEventTime_le_iff_raw_intersection hlam0 hlamHalf B 0 t sample hgood i,
    WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  constructor
  · rintro ⟨_,h⟩; linarith
  · intro h; exact ⟨hx, by linarith⟩

/-- The adapted representation is the actual raw graph past point sum. -/
theorem safeTargetPastTest_eq_raw_sum (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) (f : MatchingPoint → ℝ) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0)
    (u : ℝ≥0) (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0) :
    safeTargetPastTest hlam0 hlamHalf B f u sample =
      ∑ i : Fin n, f (sample.rootedTargetPoint (sample.feedbackGraph hlam0 hlamHalf B 0)
        (B + (u : ℝ)) i) := by
  classical
  unfold safeTargetPastTest
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rootedTargetPoint]
  by_cases hi : i ∈ sample.initialSeenTarget B 0
  · rw [ite_eq_left hi, targetIntersection_eq_initial_coordinate hlam0 hlamHalf B sample i hi]
  · rw [ite_eq_right hi]
    have he := targetEventTime_eq_raw_intersection hlam0 hlamHalf B sample hgood i hi
    have hx : 0 ≤ sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B := by
      rw [sample.initialSeenTarget_eq_targetIntersection_filter hlam0 hlamHalf B 0] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      linarith
    by_cases hu : sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i ≤ B + (u : ℝ)
    · have hle : Real.toNNReal (sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) ≤ u :=
        Real.toNNReal_le_iff_le_coe.mpr (by linarith)
      simp only [cappedStoppingValue, he, min_eq_left (WithTop.coe_le_coe.mpr hle),
        WithTop.untopD_coe, Real.coe_toNNReal _ hx]
      congr 2
      ring
    · have hle : u ≤ Real.toNNReal (sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i - B) := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hx]
        linarith
      simp only [cappedStoppingValue, he, min_eq_right (WithTop.coe_le_coe.mpr hle),
        WithTop.untopD_coe, sub_self, hf 0 _ le_rfl]
      exact (hf _ _ (by linarith)).symm

/-- A past compact point test is unchanged by continuation beyond the surviving horizon. -/
theorem source_past_test_stopped_eq_raw (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) (f : MatchingPoint → ℝ) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0)
    (i : Fin n) :
    f (sample.rootedSourcePoint (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      (B + (u : ℝ)) i) =
    f (sample.rootedSourcePoint (sample.feedbackGraph hlam0 hlamHalf B 0) (B + (u : ℝ)) i) := by
  let X := sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i
  let Y := sample.sourceIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i
  have hcut : B + (u : ℝ) ≤ B + (T : ℝ) := add_le_add_right (NNReal.coe_le_coe.mpr hu) B
  have he (x : ℝ) (hx : x ≤ B + (T : ℝ)) : Y ≤ x ↔ X ≤ x :=
    sourceIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i hx
  change f (Y - (B + (u : ℝ)), sample.sourceMark i) =
    f (X - (B + (u : ℝ)), sample.sourceMark i)
  by_cases hx : X ≤ B + (u : ℝ)
  · have hyx : Y ≤ X := (he X (hx.trans hcut)).mpr le_rfl
    have hxy : X ≤ Y := (he Y (hyx.trans (hx.trans hcut))).mp le_rfl
    rw [le_antisymm hyx hxy]
  · have hy : ¬ Y ≤ B + (u : ℝ) := fun h ↦ hx ((he _ hcut).mp h)
    rw [hf _ _ (by linarith), hf _ _ (by linarith)]

/-- The globally adapted past process reads the actual stopped environment on survival. -/
theorem safeSourcePastTest_eq_stopped_environment_test (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) (f : C_c(MatchingPoint, ℝ)) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0) :
    safeSourcePastTest hlam0 hlamHalf B f u sample =
      LocalConfiguration.testIntegral (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B + (u : ℝ)))).source f := by
  rw [safeSourcePastTest_eq_raw_sum hlam0 hlamHalf B f hf u sample hgood]
  change (∑ i : Fin n, f (sample.rootedSourcePoint _ _ i)) =
    LocalConfiguration.testIntegral (LocalConfiguration.ofTuple matchingPointBase
      (sample.rootedSourcePoint _ _)) f
  rw [LocalConfiguration.testIntegral_ofTuple]
  apply Finset.sum_congr rfl
  intro i _
  exact (source_past_test_stopped_eq_raw hlam0 hlamHalf eta B T u sample hstop hu f hf i).symm

/-- A past compact point test is unchanged by continuation beyond the surviving horizon. -/
theorem target_past_test_stopped_eq_raw (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) (f : MatchingPoint → ℝ) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0)
    (i : Fin n) :
    f (sample.rootedTargetPoint (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      (B + (u : ℝ)) i) =
    f (sample.rootedTargetPoint (sample.feedbackGraph hlam0 hlamHalf B 0) (B + (u : ℝ)) i) := by
  let X := sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i
  let Y := sample.targetIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i
  have hcut : B + (u : ℝ) ≤ B + (T : ℝ) := add_le_add_right (NNReal.coe_le_coe.mpr hu) B
  have he (x : ℝ) (hx : x ≤ B + (T : ℝ)) : Y ≤ x ↔ X ≤ x :=
    targetIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i hx
  change f (Y - (B + (u : ℝ)), sample.targetMark i) =
    f (X - (B + (u : ℝ)), sample.targetMark i)
  by_cases hx : X ≤ B + (u : ℝ)
  · have hyx : Y ≤ X := (he X (hx.trans hcut)).mpr le_rfl
    have hxy : X ≤ Y := (he Y (hyx.trans (hx.trans hcut))).mp le_rfl
    rw [le_antisymm hyx hxy]
  · have hy : ¬ Y ≤ B + (u : ℝ) := fun h ↦ hx ((he _ hcut).mp h)
    rw [hf _ _ (by linarith), hf _ _ (by linarith)]

/-- The globally adapted past process reads the actual stopped environment on survival. -/
theorem safeTargetPastTest_eq_stopped_environment_test (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) (f : C_c(MatchingPoint, ℝ)) (hf : ∀ x v, 0 ≤ x → f (x,v) = 0) :
    safeTargetPastTest hlam0 hlamHalf B f u sample =
      LocalConfiguration.testIntegral (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B + (u : ℝ)))).target f := by
  rw [safeTargetPastTest_eq_raw_sum hlam0 hlamHalf B f hf u sample hgood]
  change (∑ i : Fin n, f (sample.rootedTargetPoint _ _ i)) =
    LocalConfiguration.testIntegral (LocalConfiguration.ofTuple matchingPointBase
      (sample.rootedTargetPoint _ _)) f
  rw [LocalConfiguration.testIntegral_ofTuple]
  apply Finset.sum_congr rfl
  intro i _
  exact (target_past_test_stopped_eq_raw hlam0 hlamHalf eta B T u sample hstop hu f hf i).symm

end FiniteSample
end OTSelector
