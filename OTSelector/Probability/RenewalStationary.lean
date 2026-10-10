import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Stationarity of the actual renewal occupation law

A probability law on rooted cell sequences, a measure-preserving cell shift, and a measurable
concatenation with the one-cell translation identity determine a stationary law by occupation
inside the initial cell. Stationarity follows by cancellation of the two boundary integrals.
No stationary-law or renewal-inversion premise is used.
-/

open MeasureTheory Set
open scoped ENNReal Interval

namespace OTSelector

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The actual product measure restricted to the half-open region below the cell roof. -/
noncomputable def renewalRoofMeasure (Q : Measure Ω) (L : Ω → ℝ) : Measure (Ω × ℝ) :=
  (Q.prod volume).restrict {p | 0 ≤ p.2 ∧ p.2 < L p.1}

/-- Unnormalized occupation of the concatenated scene inside its initial cell. -/
noncomputable def renewalOccupation (Q : Measure Ω) (L : Ω → ℝ)
    (θ : ℝ × X → X) (c : Ω → X) : Measure X :=
  (renewalRoofMeasure Q L).map (fun p ↦ θ (p.2, c p.1))

/-- Renewal occupation normalized by the actual mean cell length. -/
noncomputable def renewalStationaryLaw (Q : Measure Ω) (L : Ω → ℝ)
    (θ : ℝ × X → X) (c : Ω → X) : Measure X :=
  (ENNReal.ofReal (∫ ω, L ω ∂Q))⁻¹ • renewalOccupation Q L θ c

private theorem measurableSet_renewalRoof {L : Ω → ℝ} (hL : Measurable L) :
    MeasurableSet {p : Ω × ℝ | 0 ≤ p.2 ∧ p.2 < L p.1} :=
  (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hL.comp measurable_fst))

private theorem measurable_renewalEvaluation {θ : ℝ × X → X} {c : Ω → X}
    (hθ : Measurable θ) (hc : Measurable c) :
    Measurable (fun p : Ω × ℝ ↦ θ (p.2, c p.1)) :=
  hθ.comp (measurable_snd.prodMk (hc.comp measurable_fst))

/-- The roof region has mass equal to the nonnegative mean roof length. -/
theorem renewalRoofMeasure_univ (Q : Measure Ω) {L : Ω → ℝ} (hL : Measurable L) :
    renewalRoofMeasure Q L univ = ∫⁻ ω, ENNReal.ofReal (L ω) ∂Q := by
  rw [renewalRoofMeasure, Measure.restrict_apply_univ,
    Measure.prod_apply (measurableSet_renewalRoof hL)]
  apply lintegral_congr
  intro ω
  change volume (Ico 0 (L ω)) = _
  simp

private theorem renewalRoofMeasure_univ_eq (Q : Measure Ω) {L : Ω → ℝ}
    (hL : Measurable L) (hLi : Integrable L Q) (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) :
    renewalRoofMeasure Q L univ = ENNReal.ofReal (∫ ω, L ω ∂Q) := by
  rw [renewalRoofMeasure_univ Q hL,
    ← ofReal_integral_eq_lintegral_ofReal hLi hL0]

private theorem finite_renewalRoofMeasure (Q : Measure Ω) {L : Ω → ℝ}
    (hL : Measurable L) (hLi : Integrable L Q) (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) :
    IsFiniteMeasure (renewalRoofMeasure Q L) := by
  constructor
  rw [renewalRoofMeasure_univ_eq Q hL hLi hL0]
  exact ENNReal.ofReal_lt_top

private theorem mean_roof_pos (Q : Measure Ω) [IsProbabilityMeasure Q] {L : Ω → ℝ}
    (hLi : Integrable L Q) (hLpos : ∀ᵐ ω ∂Q, 0 < L ω) : 0 < ∫ ω, L ω ∂Q := by
  have h0 : ∀ᵐ ω ∂Q, 0 ≤ L ω := hLpos.mono fun _ h ↦ h.le
  have hn := integral_nonneg_of_ae h0
  by_contra h
  have hz : (∫ ω, L ω ∂Q) = 0 := le_antisymm (le_of_not_gt h) hn
  have hzero := (integral_eq_zero_iff_of_nonneg_ae h0 hLi).mp hz
  obtain ⟨ω, hp, he⟩ := (hLpos.and hzero).exists
  simp only [he, Pi.zero_apply, lt_self_iff_false] at hp

/-- The explicit normalized occupation is a probability measure. -/
theorem isProbabilityMeasure_renewalStationaryLaw (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω) {θ : ℝ × X → X} {c : Ω → X}
    (hθ : Measurable θ) (hc : Measurable c) :
    IsProbabilityMeasure (renewalStationaryLaw Q L θ c) := by
  have hm : 0 < ∫ ω, L ω ∂Q := mean_roof_pos Q hLi hLpos
  constructor
  rw [renewalStationaryLaw, Measure.smul_apply, smul_eq_mul, renewalOccupation,
    Measure.map_apply (measurable_renewalEvaluation hθ hc) MeasurableSet.univ]
  simp only [preimage_univ]
  rw [renewalRoofMeasure_univ_eq Q hL hLi (hLpos.mono fun _ h ↦ h.le)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hm) ENNReal.ofReal_ne_top

private theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (Ι a b)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hbound)

private theorem stronglyMeasurable_fixed_intervalIntegral {F : Ω × ℝ → ℝ}
    (hF : Measurable F) (a b : ℝ) :
    StronglyMeasurable (fun ω ↦ ∫ u in a..b, F (ω, u)) := by
  exact (hF.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc a b))).sub
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc b a)))

private theorem integrable_fixed_intervalIntegral (Q : Measure Ω) [IsFiniteMeasure Q]
    {F : Ω × ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hbound : ∀ p, ‖F p‖ ≤ C) (a b : ℝ) :
    Integrable (fun ω ↦ ∫ u in a..b, F (ω, u)) Q := by
  apply Integrable.of_bound (stronglyMeasurable_fixed_intervalIntegral hF a b).aestronglyMeasurable
    (C * |b - a|)
  exact ae_of_all _ fun ω ↦ intervalIntegral.norm_integral_le_of_norm_le_const
    (fun u _ ↦ hbound (ω, u))

private theorem integral_renewalRoofMeasure (Q : Measure Ω) [SFinite Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) {F : Ω × ℝ → ℝ}
    (hF : Measurable F) {C : ℝ} (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F p ∂renewalRoofMeasure Q L) = ∫ ω, (∫ u in 0..L ω, F (ω, u)) ∂Q := by
  let A : Set (Ω × ℝ) := {p | 0 ≤ p.2 ∧ p.2 < L p.1}
  have hA : MeasurableSet A := measurableSet_renewalRoof hL
  let := finite_renewalRoofMeasure Q hL hLi hL0
  have hFi : Integrable F (renewalRoofMeasure Q L) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)
  have hAi : Integrable (A.indicator F) (Q.prod volume) :=
    (integrable_indicator_iff hA).2 hFi
  rw [renewalRoofMeasure, ← integral_indicator hA, integral_prod _ hAi]
  apply integral_congr_ae
  filter_upwards [hL0] with ω hω
  have heq : (fun u ↦ A.indicator F (ω, u)) =
      (Ico 0 (L ω)).indicator (fun u ↦ F (ω, u)) := rfl
  rw [heq, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hω]

private theorem integrable_renewalRoofIntegral (Q : Measure Ω) [SFinite Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) {F : Ω × ℝ → ℝ}
    (hF : Measurable F) {C : ℝ} (hbound : ∀ p, ‖F p‖ ≤ C) :
    Integrable (fun ω ↦ ∫ u in 0..L ω, F (ω, u)) Q := by
  let A : Set (Ω × ℝ) := {p | 0 ≤ p.2 ∧ p.2 < L p.1}
  have hA : MeasurableSet A := measurableSet_renewalRoof hL
  let := finite_renewalRoofMeasure Q hL hLi hL0
  have hFi : Integrable F (renewalRoofMeasure Q L) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)
  have hAi : Integrable (A.indicator F) (Q.prod volume) :=
    (integrable_indicator_iff hA).2 hFi
  apply hAi.integral_prod_left.congr
  filter_upwards [hL0] with ω hω
  have heq : (fun u ↦ A.indicator F (ω, u)) =
      (Ico 0 (L ω)).indicator (fun u ↦ F (ω, u)) := rfl
  rw [heq, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hω]

/-- Bounded measurable observables of the actual occupation law are the corresponding
cell integrals. This formula also fixes the sign convention for the real action. -/
theorem integral_renewalOccupation (Q : Measure Ω) [SFinite Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) {θ : ℝ × X → X} {c : Ω → X}
    (hθ : Measurable θ) (hc : Measurable c) {f : X → ℝ}
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂renewalOccupation Q L θ c) =
      ∫ ω, (∫ u in 0..L ω, f (θ (u, c ω))) ∂Q := by
  rw [renewalOccupation, integral_map
    (measurable_renewalEvaluation hθ hc).aemeasurable hf.aestronglyMeasurable]
  exact integral_renewalRoofMeasure Q hL hLi hL0
    (hf.comp (measurable_renewalEvaluation hθ hc)) (fun p ↦ hbound _)

private theorem interval_boundary_cancel {f : ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hbound : ∀ u, ‖f u‖ ≤ C) (L t : ℝ) :
    (∫ u in 0..L, f (u + t)) + (∫ u in 0..t, f u) =
      (∫ u in 0..L, f u) + (∫ u in 0..t, f (u + L)) := by
  rw [intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  have hi := intervalIntegrable_of_bounded hf hbound
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (L + t))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (hi 0 L) (hi L (t + L))
  rw [add_comm t L] at h₂ ⊢
  linarith

/-- Cancellation of the two boundary terms proves invariance of occupation integrals.
The only relation between the base shift and the real action is actual one-cell covariance. -/
theorem integral_renewalOccupation_comp_action
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω)
    {S : Ω → Ω} (hS : MeasurePreserving S Q Q)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = θ (L ω, c ω))
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (t : ℝ) :
    (∫ x, f (θ (t, x)) ∂renewalOccupation Q L θ c) =
      ∫ x, f x ∂renewalOccupation Q L θ c := by
  let F : Ω × ℝ → ℝ := fun p ↦ f (θ (p.2, c p.1))
  have hF : Measurable F := hf.comp (measurable_renewalEvaluation hθ hc)
  have hbF : ∀ p, ‖F p‖ ≤ C := fun p ↦ hbound _
  let J : Ω → ℝ := fun ω ↦ ∫ u in 0..t, F (ω, u)
  have hJi : Integrable J Q := integrable_fixed_intervalIntegral Q hF hbF 0 t
  have hJm : StronglyMeasurable J := stronglyMeasurable_fixed_intervalIntegral hF 0 t
  have hJS : Integrable (fun ω ↦ J (S ω)) Q := hS.integrable_comp_of_integrable hJi
  have hJSeq : (∫ ω, J (S ω) ∂Q) = ∫ ω, J ω ∂Q := by
    rw [← integral_map hS.measurable.aemeasurable hJm.aestronglyMeasurable, hS.map_eq]
  have htmeas : Measurable (fun x ↦ θ (t, x)) := hθ.comp measurable_prodMk_left
  let A : Ω → ℝ := fun ω ↦ ∫ u in 0..L ω, f (θ (t, θ (u, c ω)))
  let B : Ω → ℝ := fun ω ↦ ∫ u in 0..L ω, F (ω, u)
  have hAi : Integrable A Q := integrable_renewalRoofIntegral Q hL hLi hL0
    ((hf.comp htmeas).comp (measurable_renewalEvaluation hθ hc)) (fun p ↦ hbound _)
  have hBi : Integrable B Q := integrable_renewalRoofIntegral Q hL hLi hL0 hF hbF
  have hboundary : ∀ᵐ ω ∂Q, A ω + J ω = B ω + J (S ω) := by
    filter_upwards [hcell] with ω hω
    have h := interval_boundary_cancel (hF.comp measurable_prodMk_left)
      (fun u ↦ hbF (ω, u)) (L ω) t
    convert h using 1
    · dsimp [A, J, F]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [hadd, add_comm t u]
    · dsimp [B, J, F]
      rw [hω]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [hadd]
  have hsum := integral_congr_ae hboundary
  rw [integral_add hAi hJi, integral_add hBi hJS, hJSeq] at hsum
  rw [integral_renewalOccupation Q hL hLi hL0 hθ hc (f := fun x ↦ f (θ (t, x)))
      (hf.comp htmeas)
      (fun x ↦ hbound _),
    integral_renewalOccupation Q hL hLi hL0 hθ hc hf hbound]
  exact add_right_cancel hsum

/-- The unnormalized occupation measure is invariant under every real translation.
The base shift only needs to preserve `Q`; it need not be invertible. -/
theorem measurePreserving_renewalOccupation
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω)
    {S : Ω → Ω} (hS : MeasurePreserving S Q Q)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = θ (L ω, c ω)) (t : ℝ) :
    MeasurePreserving (fun x ↦ θ (t, x)) (renewalOccupation Q L θ c)
      (renewalOccupation Q L θ c) := by
  classical
  let := finite_renewalRoofMeasure Q hL hLi hL0
  let : IsFiniteMeasure (renewalOccupation Q L θ c) :=
    Measure.isFiniteMeasure_map (renewalRoofMeasure Q L) _
  have ht : Measurable (fun x ↦ θ (t, x)) := hθ.comp measurable_prodMk_left
  refine ⟨ht, Measure.ext fun s hs ↦ ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((renewalOccupation Q L θ c).map (fun x ↦ θ (t, x))).real s =
    (renewalOccupation Q L θ c).real s
  let f : X → ℝ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hb : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [f, hx]
  calc
    _ = ∫ x, f x ∂(renewalOccupation Q L θ c).map (fun x ↦ θ (t, x)) :=
      (integral_indicator_one hs).symm
    _ = ∫ x, f (θ (t, x)) ∂renewalOccupation Q L θ c :=
      integral_map ht.aemeasurable hf.aestronglyMeasurable
    _ = ∫ x, f x ∂renewalOccupation Q L θ c :=
      integral_renewalOccupation_comp_action Q hL hLi hL0 hS hθ hc hadd hcell hf hb t
    _ = _ := integral_indicator_one hs

/-- The explicit normalized occupation law is stationary. Together with
`isProbabilityMeasure_renewalStationaryLaw`, this constructs a stationary probability law
from a positive integrable actual cell roof and its one-cell concatenation identity. -/
theorem measurePreserving_renewalStationaryLaw
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω)
    {S : Ω → Ω} (hS : MeasurePreserving S Q Q)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = θ (L ω, c ω)) (t : ℝ) :
    MeasurePreserving (fun x ↦ θ (t, x)) (renewalStationaryLaw Q L θ c)
      (renewalStationaryLaw Q L θ c) :=
  (measurePreserving_renewalOccupation Q hL hLi (hLpos.mono fun _ h ↦ h.le)
    hS hθ hc hadd hcell t).smul_measure _

/-- The normalized law's bounded-observable formula has the actual mean roof as denominator. -/
theorem integral_renewalStationaryLaw (Q : Measure Ω) [SFinite Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hL0 : ∀ᵐ ω ∂Q, 0 ≤ L ω) {θ : ℝ × X → X} {c : Ω → X}
    (hθ : Measurable θ) (hc : Measurable c) {f : X → ℝ}
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂renewalStationaryLaw Q L θ c) =
      (∫ ω, L ω ∂Q)⁻¹ * ∫ ω, (∫ u in 0..L ω, f (θ (u, c ω))) ∂Q := by
  rw [renewalStationaryLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hL0), smul_eq_mul,
    integral_renewalOccupation Q hL hLi hL0 hθ hc hf hbound]

end OTSelector
