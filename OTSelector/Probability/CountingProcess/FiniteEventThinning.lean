import OTSelector.Probability.CountingProcess.FiniteEventCountTop
import Mathlib.Probability.Process.Stopping

/-!
# Predictable thinning of finitely many event times

An event label is retained when its stopping-time value is finite and a strongly progressive
process is nonzero at that stopped value.  The retained label is sent to `⊤` otherwise.  The
stopping-time proof uses the stopped-value preimage only after intersecting it with the event
`{ξ ≤ t}`; the stopped value at a general stopping time is not assumed to be globally `F t`
measurable.

The resulting finite count is a pathwise `finiteEventCountTop`.  Its cardinality formula and the
usual finite-path bounds are exposed here so that later intensity arguments can use the thinned
labels without unfolding the acceptance predicate.
-/

open Filter Set
open scoped NNReal Topology

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*}

noncomputable section

/-- A finite event label is accepted when its stopped value under `G` is nonzero. -/
def eventAccepted (G : ℝ≥0 → Ω → ℝ) (ξ : Ω → WithTop ℝ≥0) (ω : Ω) : Prop :=
  ξ ω ≠ ⊤ ∧ stoppedValue G ξ ω ≠ 0

local instance eventAcceptedDecidable (G : ℝ≥0 → Ω → ℝ)
    (ξ : Ω → WithTop ℝ≥0) (ω : Ω) : Decidable (eventAccepted G ξ ω) :=
  Classical.propDecidable _

/-- Retain an accepted event label and send a rejected or top-valued label to `⊤`. -/
noncomputable def thinnedEventTime (G : ℝ≥0 → Ω → ℝ)
    (ξ : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω ↦ if eventAccepted G ξ ω then ξ ω else ⊤

@[simp]
theorem thinnedEventTime_of_accepted {G : ℝ≥0 → Ω → ℝ}
    {ξ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : eventAccepted G ξ ω) :
    thinnedEventTime G ξ ω = ξ ω := by
  simp [thinnedEventTime, hω]

@[simp]
theorem thinnedEventTime_of_not_accepted {G : ℝ≥0 → Ω → ℝ}
    {ξ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : ¬eventAccepted G ξ ω) :
    thinnedEventTime G ξ ω = ⊤ := by
  simp [thinnedEventTime, hω]

/-- Thinning preserves the property that every event time is either `⊤` or strictly
positive. -/
theorem thinnedEventTime_eq_top_or_pos {G : ℝ≥0 → Ω → ℝ}
    {ξ : Ω → WithTop ℝ≥0}
    (hpos : ∀ ω, ξ ω = ⊤ ∨ (0 : WithTop ℝ≥0) < ξ ω) (ω : Ω) :
    thinnedEventTime G ξ ω = ⊤ ∨
      (0 : WithTop ℝ≥0) < thinnedEventTime G ξ ω := by
  classical
  by_cases hacc : eventAccepted G ξ ω
  · rw [thinnedEventTime_of_accepted hacc]
    exact hpos ω
  · exact Or.inl (thinnedEventTime_of_not_accepted hacc)

/-- Thinning preserves pairwise distinctness of finite event times in a finite family. -/
theorem thinnedEventTime_family_injective {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hdist : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j) :
    ∀ ω i j,
      thinnedEventTime G (ξ i) ω ≠ ⊤ →
      thinnedEventTime G (ξ j) ω ≠ ⊤ →
      thinnedEventTime G (ξ i) ω = thinnedEventTime G (ξ j) ω →
      i = j := by
  classical
  intro ω i j hi hj hij
  by_cases hiacc : eventAccepted G (ξ i) ω
  · by_cases hjacc : eventAccepted G (ξ j) ω
    · have hxi : ξ i ω ≠ ⊤ := by
        rw [thinnedEventTime_of_accepted hiacc] at hi
        exact hi
      have hxj : ξ j ω ≠ ⊤ := by
        rw [thinnedEventTime_of_accepted hjacc] at hj
        exact hj
      rw [thinnedEventTime_of_accepted hiacc,
        thinnedEventTime_of_accepted hjacc] at hij
      exact hdist ω i j hxi hxj hij
    · exact False.elim (hj (thinnedEventTime_of_not_accepted hjacc))
  · exact False.elim (hi (thinnedEventTime_of_not_accepted hiacc))

/-! ## The stopped-value event at a finite threshold -/

theorem thinnedEventTime_le_iff {G : ℝ≥0 → Ω → ℝ}
    {ξ : Ω → WithTop ℝ≥0} (ω : Ω) (t : ℝ≥0) :
    thinnedEventTime G ξ ω ≤ (t : WithTop ℝ≥0) ↔
      eventAccepted G ξ ω ∧ ξ ω ≤ (t : WithTop ℝ≥0) := by
  classical
  by_cases hacc : eventAccepted G ξ ω
  · simp [thinnedEventTime, hacc]
  · simp [thinnedEventTime, hacc]
    exact WithTop.not_top_le_coe t

/-- The accepted label event below a finite threshold is measurable at that threshold.

The proof deliberately invokes `measurableSet_preimage_stoppedValue_inter`: it does not claim
that `stoppedValue G ξ` is itself `F t`-measurable before restricting to `{ξ ≤ t}`.
-/
theorem measurableSet_eventAccepted_and_le
    [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {G : ℝ≥0 → Ω → ℝ} {ξ : Ω → WithTop ℝ≥0}
    (hξ : IsStoppingTime ℱ ξ) (hG : IsStronglyProgressive ℱ G) (t : ℝ≥0) :
    MeasurableSet[ℱ t] {ω | eventAccepted G ξ ω ∧ ξ ω ≤ (t : WithTop ℝ≥0)} := by
  have hzero : MeasurableSet {x : ℝ | x ≠ 0} :=
    (measurableSet_singleton (0 : ℝ)).compl
  have hinter := measurableSet_preimage_stoppedValue_inter hG hξ hzero t
  have hEq : {ω | eventAccepted G ξ ω ∧ ξ ω ≤ (t : WithTop ℝ≥0)} =
      (stoppedValue G ξ ⁻¹' {x : ℝ | x ≠ 0}) ∩
        {ω | ξ ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    constructor
    · intro h
      exact ⟨h.1.2, h.2⟩
    · intro h
      have hfinite : ξ ω ≠ ⊤ := by
        intro htop
        exact (WithTop.not_top_le_coe t) (by simpa [htop] using h.2)
      exact ⟨⟨hfinite, h.1⟩, h.2⟩
  rw [hEq]
  exact hinter

/-! ## Stopping-time closure -/

theorem isStoppingTime_thinnedEventTime
    [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {G : ℝ≥0 → Ω → ℝ} {ξ : Ω → WithTop ℝ≥0}
    (hξ : IsStoppingTime ℱ ξ) (hG : IsStronglyProgressive ℱ G) :
    IsStoppingTime ℱ (thinnedEventTime G ξ) := by
  intro t
  have hAcc := measurableSet_eventAccepted_and_le hξ hG t
  have hEq : {ω | thinnedEventTime G ξ ω ≤ (t : WithTop ℝ≥0)} =
      {ω | eventAccepted G ξ ω ∧ ξ ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    exact thinnedEventTime_le_iff ω t
  rw [hEq]
  exact hAcc

theorem isStoppingTime_thinnedEventTime_of_predictable
    [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {G : ℝ≥0 → Ω → ℝ} {ξ : Ω → WithTop ℝ≥0}
    (hξ : IsStoppingTime ℱ ξ) (hG : IsStronglyPredictable ℱ G) :
    IsStoppingTime ℱ (thinnedEventTime G ξ) :=
  isStoppingTime_thinnedEventTime hξ hG.isStronglyProgressive

theorem isStoppingTime_thinnedEventTime_family {m : ℕ}
    [MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {G : ℝ≥0 → Ω → ℝ} {ξ : Fin m → Ω → WithTop ℝ≥0}
    (hξ : ∀ i, IsStoppingTime ℱ (ξ i)) (hG : IsStronglyProgressive ℱ G) :
    ∀ i, IsStoppingTime ℱ (thinnedEventTime G (ξ i)) :=
  fun i ↦ isStoppingTime_thinnedEventTime (hξ i) hG

/-! ## The finite thinned count -/

/-- Count accepted labels whose thinned event time is attained by `t`. -/
noncomputable def finiteEventCountThinned {m : ℕ} (G : ℝ≥0 → Ω → ℝ)
    (ξ : Fin m → Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℕ :=
  finiteEventCountTop (fun i ↦ thinnedEventTime G (ξ i)) t ω

theorem finiteEventCountThinned_eq_card_filter {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    finiteEventCountThinned G ξ t ω =
      (Finset.univ.filter
        (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0) ∧ eventAccepted G (ξ i) ω)).card := by
  classical
  rw [finiteEventCountThinned, finiteEventCountTop]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [thinnedEventTime_le_iff]
  exact and_comm

theorem finiteEventCountThinned_le {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : finiteEventCountThinned G ξ t ω ≤ m := by
  simpa [finiteEventCountThinned] using
    (finiteEventCountTop_le (fun i ↦ thinnedEventTime G (ξ i)) t ω)

theorem finiteEventCountThinned_mono {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountThinned G ξ s ω ≤ finiteEventCountThinned G ξ t ω := by
  simpa [finiteEventCountThinned] using
    (finiteEventCountTop_mono (fun i ↦ thinnedEventTime G (ξ i)) ω hst)

theorem finiteEventCountThinned_rightContinuous {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ (finiteEventCountThinned G ξ s ω : ℝ)) (Ici t) t := by
  simpa [finiteEventCountThinned] using
    (finiteEventCountTop_rightContinuous (fun i ↦ thinnedEventTime G (ξ i)) ω t)

theorem finiteEventCountThinned_zero_of_pos_or_top {m : ℕ}
    (G : ℝ≥0 → Ω → ℝ) (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω)
    (hξ : ∀ i, ξ i ω = ⊤ ∨ (0 : WithTop ℝ≥0) < ξ i ω) :
    finiteEventCountThinned G ξ 0 ω = 0 := by
  apply finiteEventCountTop_zero (fun i ↦ thinnedEventTime G (ξ i)) ω
  intro i
  by_cases hacc : eventAccepted G (ξ i) ω
  · rcases hξ i with htop | hpos
    · exact False.elim (hacc.1 htop)
    · exact Or.inr (by simpa [thinnedEventTime, hacc] using hpos)
  · exact Or.inl (by simp [thinnedEventTime, hacc])

end

end OTSelector.CountingProcess
