import Mathlib.MeasureTheory.Function.Floor
import OTSelector.Feedback.LyapunovCutoff
import OTSelector.Probability.CountingProcess.BoundedGridStopping
import OTSelector.Probability.CountingProcess.MarkedCurrent
import OTSelector.Probability.CountingProcess.Occupation

/-!
# Predictable state transforms for a two-colour counting current

The left current is the initial integer state plus the two real-cast counts strictly before the
current time.  Once the initial state is measurable at time zero, this makes the real cast of the
left current predictable.  Arbitrary functions of its integer value are then predictable by
composing with the measurable floor map.  The clipped one-step increments are uniformly bounded,
so they belong to the bounded-predictable class used by the compensator closure theorem.
-/

open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real cast of the left current is predictable when the initial current is measurable at
time zero. -/
theorem leftCurrentOfCounts_cast_predictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ))) :
    IsStronglyPredictable ℱ
      (fun t ω => (leftCurrentOfCounts K0 Nplus Nminus t ω : ℝ)) := by
  have hKpred : IsStronglyPredictable ℱ (fun _ ω => (K0 ω : ℝ)) :=
    MeasureTheory.IsStronglyPredictable.of_continuous_adapted
      (fun t => hK0.mono (ℱ.mono bot_le)) (fun _ => continuous_const)
  have hplusPred : IsStronglyPredictable ℱ
      (fun t ω => (countBefore Nplus t ω : ℝ)) :=
    stronglyMeasurable_countBefore hplus.stronglyAdapted hplus.monotone
  have hminusPred : IsStronglyPredictable ℱ
      (fun t ω => (countBefore Nminus t ω : ℝ)) :=
    stronglyMeasurable_countBefore hminus.stronglyAdapted hminus.monotone
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry fun t ω => (leftCurrentOfCounts K0 Nplus Nminus t ω : ℝ))
  convert hKpred.add hplusPred |>.sub hminusPred using 1
  funext z
  rcases z with ⟨t, ω⟩
  simp [leftCurrentOfCounts]

/-- Any real-valued function of the integer left current is predictable. -/
theorem leftCurrentOfCounts_comp_predictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (g : ℤ → ℝ) :
    IsStronglyPredictable ℱ
      (fun t ω => g (leftCurrentOfCounts K0 Nplus Nminus t ω)) := by
  have hleft := leftCurrentOfCounts_cast_predictable hplus hminus hK0
  have hg : Measurable (fun x : ℝ => g (Int.floor x)) :=
    (measurable_of_countable g).comp Int.measurable_floor
  have hcomp : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × Ω => g (Int.floor
        (leftCurrentOfCounts K0 Nplus Nminus z.1 z.2 : ℝ))) :=
    (hg.comp hleft.measurable).stronglyMeasurable
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × Ω => g (leftCurrentOfCounts K0 Nplus Nminus z.1 z.2))
  convert hcomp using 1
  funext z
  rw [Int.floor_intCast]

/-- The clipped upward increment evaluated at the left current is bounded predictable. -/
theorem clippedUpwardIncrement_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ
      (fun t ω => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus t ω)) := by
  refine ⟨leftCurrentOfCounts_comp_predictable hplus hminus hK0
    (clippedUpwardIncrement R f), clippedUpwardAbsBound R f, ?_, ?_⟩
  · exact (abs_nonneg (clippedUpwardIncrement R f 0)).trans
      (clippedUpwardIncrement_abs_le_bound R f 0)
  · exact fun t ω => clippedUpwardIncrement_abs_le_bound R f
      (leftCurrentOfCounts K0 Nplus Nminus t ω)

/-- The clipped downward increment evaluated at the left current is bounded predictable. -/
theorem clippedDownwardIncrement_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ
      (fun t ω => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus t ω)) := by
  refine ⟨leftCurrentOfCounts_comp_predictable hplus hminus hK0
    (clippedDownwardIncrement R f), clippedDownwardAbsBound R f, ?_, ?_⟩
  · exact (abs_nonneg (clippedDownwardIncrement R f 0)).trans
      (clippedDownwardIncrement_abs_le_bound R f 0)
  · exact fun t ω => clippedDownwardIncrement_abs_le_bound R f
      (leftCurrentOfCounts K0 Nplus Nminus t ω)

end OTSelector.CountingProcess
