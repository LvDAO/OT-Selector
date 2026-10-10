import OTSelector.Probability.CountConditioning
import OTSelector.Probability.NestedCDF

/-!
# Conditional empirical CDFs inside a selected region

An iid sample conditioned only on its number of visits to a set is not iid in its original
labeling.  This module conditions on every full membership pattern, applies the one-dimensional
Kolmogorov bound to the reindexed selected coordinates, and then mixes the patternwise estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Probability.ConditionalNestedCDF

set_option linter.style.haveILetI false

open OTSelector.CountConditioning
open OTSelector.Probability.NestedCDF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Applying a measurable score to the selected coordinates preserves their conditional
independence on a full membership pattern. -/
theorem score_selected_iIndep_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (score : Ω → ℝ) (hscore : Measurable score) :
    iIndepFun
      (fun j sample ↦ score (selectedCoordinates J hJ sample j))
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) := by
  exact (selectedCoordinates_iIndep_cond_membershipPattern P A hA hA0 hAc0 J hJ).comp
    (fun _ z ↦ score z) (fun _ ↦ hscore)

/-- Every scored selected coordinate has the pushforward of the one-point conditional law. -/
theorem map_score_selectedCoordinate_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (score : Ω → ℝ) (hscore : Measurable score)
    (j : Fin k) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
        (fun sample ↦ score (selectedCoordinates J hJ sample j)) =
      (P[|A]).map score := by
  change ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
      (score ∘ fun sample ↦ selectedCoordinates J hJ sample j) = (P[|A]).map score
  rw [← Measure.map_map hscore (measurable_selectedCoordinate J hJ j),
    map_selectedCoordinate_cond_membershipPattern P A hA hA0 hAc0 J hJ j]

/-- On a nonempty full pattern, the scored selected observations satisfy the Kolmogorov Markov
tail bound under the conditional product law. -/
theorem selected_ksDist_tail_pattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (hk : 0 < k)
    (score : Ω → ℝ) (hscore : Measurable score) {ε : ℝ} (hε : 0 < ε) :
    let μJ := (Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]
    let Q := (P[|A]).map score
    let X : Fin k → (Fin n → Ω) → ℝ :=
      fun j sample ↦ score (selectedCoordinates J hJ sample j)
    μJ.real {sample | ε ≤ ksDist X Q sample} ≤ 4 / (ε * Real.sqrt k) := by
  dsimp only
  letI : IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) :=
    cond_isProbabilityMeasure (measure_membershipPattern_ne_zero P A hA0 hAc0 J)
  letI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hA0
  letI : IsProbabilityMeasure ((P[|A]).map score) :=
    Measure.isProbabilityMeasure_map hscore.aemeasurable
  exact ksDist_tail_markov hk ((P[|A]).map score)
    (fun j sample ↦ score (selectedCoordinates J hJ sample j))
    (fun j ↦ hscore.comp (measurable_selectedCoordinate J hJ j))
    (score_selected_iIndep_cond_membershipPattern P A hA hA0 hAc0 J hJ score hscore)
    (map_score_selectedCoordinate_cond_membershipPattern P A hA hA0 hAc0 J hJ score hscore)
    hε

/-- Patternwise bad Kolmogorov event at the natural count scale.  Empty patterns contribute the
empty event, since there is no empirical CDF to estimate. -/
noncomputable def patternKSEvent
    {n : ℕ} (P : Measure Ω) (A : Set Ω) (score : Ω → ℝ) (d : ℝ)
    (J : Finset (Fin n)) : Set (Fin n → Ω) :=
  if _hJ : 0 < J.card then
    {sample | d / Real.sqrt J.card ≤
      ksDist
        (fun j : Fin J.card ↦
          fun sample' ↦ score (selectedCoordinates J rfl sample' j))
        ((P[|A]).map score) sample}
  else ∅

/-- Every nonempty pattern has the same `4 / d` upper tail after scaling the empirical CDF by the
square root of its selected count. -/
theorem cond_patternKSEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score) {d : ℝ} (hd : 0 < d)
    (J : Finset (Fin n)) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J])
        (patternKSEvent P A score d J) ≤ ENNReal.ofReal (4 / d) := by
  by_cases hJ : 0 < J.card
  · have hsqrt : 0 < Real.sqrt (J.card : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.2 hJ)
    have hreal := selected_ksDist_tail_pattern P A hA hA0 hAc0 J rfl hJ score hscore
      (div_pos hd hsqrt)
    have hbound :
        ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).real
            (patternKSEvent P A score d J) ≤ 4 / d := by
      rw [patternKSEvent, dite_eq_left hJ]
      calc
        _ ≤ 4 / ((d / Real.sqrt J.card) * Real.sqrt J.card) := hreal
        _ = 4 / d := by field_simp
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hbound
  · rw [patternKSEvent, dite_eq_right hJ]
    simp

/-- Mixing the full-pattern bounds returns an unconditional iid-sample bound without asserting
that the original labels are iid after conditioning on the total count. -/
theorem measure_patternKSEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score) {d : ℝ} (hd : 0 < d) :
    Measure.pi (fun _ : Fin n ↦ P)
        (patternwiseEvent A (patternKSEvent P A score d)) ≤ ENNReal.ofReal (4 / d) := by
  exact CountConditioning.measure_patternwiseEvent_le P A hA
    (patternKSEvent P A score d) (ENNReal.ofReal (4 / d))
    (cond_patternKSEvent_le P A hA hA0 hAc0 score hscore hd)

end OTSelector.Probability.ConditionalNestedCDF
