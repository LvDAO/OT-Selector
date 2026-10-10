import OTSelector.Probability.RenewalStationary
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Ergodicity of the renewal occupation law

The ergodicity of the cell shift passes to the entire real action on the actual occupation law.
Fixed-time almost-everywhere invariance is first exchanged by Fubini with occupation inside a
positive-length cell. This gives an almost-everywhere constant time trajectory. Its measurable
unit-interval average is invariant under the cell shift, hence constant by base ergodicity.
No value on the zero-occupation Palm section is used, and no random time is substituted into a
fixed-time almost-everywhere statement.
-/

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace OTSelector

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

private theorem measurable_evaluation {θ : ℝ × X → X} {c : Ω → X}
    (hθ : Measurable θ) (hc : Measurable c) :
    Measurable (fun p : Ω × ℝ ↦ θ (p.2, c p.1)) :=
  hθ.comp (measurable_snd.prodMk (hc.comp measurable_fst))

private theorem measurable_roof {L : Ω → ℝ} (hL : Measurable L) :
    MeasurableSet {p : Ω × ℝ | 0 ≤ p.2 ∧ p.2 < L p.1} :=
  (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (hL.comp measurable_fst))

private theorem timeAverage_eq_of_ae_const {f : ℝ → ℝ} {k : ℝ}
    (h : ∀ᵐ t ∂volume, f t = k) : (∫ t in (0 : ℝ)..1, f t) = k := by
  calc
    _ = ∫ t in (0 : ℝ)..1, k :=
      intervalIntegral.integral_congr_ae (h.mono fun _ ht _ ↦ ht)
    _ = k := by simp

private theorem measurable_timeAverage {F : Ω × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun ω ↦ ∫ u in (0 : ℝ)..1, F (ω, u)) := by
  exact ((hF.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).sub
    (hF.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (1 : ℝ) 0)))).measurable

/-- The Fubini step: a real observable invariant at every fixed time under the occupation law
has an almost-everywhere constant complete time trajectory for almost every rooted cell. -/
private theorem ae_time_trajectory_const
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    {f : X → ℝ} (hf : Measurable f)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂renewalStationaryLaw Q L θ c, f (θ (t, x)) = f x) :
    ∀ᵐ ω ∂Q, ∃ k : ℝ, ∀ᵐ t ∂volume, f (θ (t, c ω)) = k := by
  let ν := renewalRoofMeasure Q L
  let : IsFiniteMeasure ν := by
    constructor
    rw [show ν = renewalRoofMeasure Q L from rfl, renewalRoofMeasure_univ Q hL,
      ← ofReal_integral_eq_lintegral_ofReal hLi (hLpos.mono fun _ h ↦ h.le)]
    exact ENNReal.ofReal_lt_top
  have hEval := measurable_evaluation hθ hc
  have hfixed (t : ℝ) : ∀ᵐ p ∂ν,
      f (θ (t, θ (p.2, c p.1))) = f (θ (p.2, c p.1)) := by
    have h := hinv t
    rw [renewalStationaryLaw, Measure.ae_ennreal_smul_measure_iff
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)] at h
    exact ae_of_ae_map hEval.aemeasurable h
  have hmeas : MeasurableSet {p : ℝ × (Ω × ℝ) |
      f (θ (p.1, θ (p.2.2, c p.2.1))) = f (θ (p.2.2, c p.2.1))} := by
    apply measurableSet_eq_fun
    · exact hf.comp (hθ.comp (measurable_fst.prodMk (hEval.comp measurable_snd)))
    · exact (hf.comp hEval).comp measurable_snd
  have hswap : ∀ᵐ p ∂ν, ∀ᵐ t ∂volume,
      f (θ (t, θ (p.2, c p.1))) = f (θ (p.2, c p.1)) :=
    (Measure.ae_ae_comm hmeas).mp (ae_of_all volume hfixed)
  have hprod : ∀ᵐ p ∂Q.prod volume,
      p ∈ {p : Ω × ℝ | 0 ≤ p.2 ∧ p.2 < L p.1} →
      ∀ᵐ t ∂volume, f (θ (t, θ (p.2, c p.1))) = f (θ (p.2, c p.1)) :=
    (ae_restrict_iff' (measurable_roof hL)).mp hswap
  filter_upwards [Measure.ae_ae_of_ae_prod hprod, hLpos] with ω hω hpos
  have hne : volume.restrict (Ico 0 (L ω)) ≠ 0 := by
    rw [ne_eq, Measure.restrict_eq_zero, Real.volume_Ico, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hpos
  let : NeZero (volume.restrict (Ico 0 (L ω))) := ⟨hne⟩
  have hu : ∀ᵐ u ∂volume.restrict (Ico 0 (L ω)),
      ∀ᵐ t ∂volume, f (θ (t, θ (u, c ω))) = f (θ (u, c ω)) :=
    (ae_restrict_iff' measurableSet_Ico).mpr hω
  obtain ⟨u, hu⟩ := hu.exists
  refine ⟨f (θ (u, c ω)), ?_⟩
  have hu' : ∀ᵐ t ∂volume, f (θ (t + u, c ω)) = f (θ (u, c ω)) := by
    simpa only [hadd] using hu
  have hp := (measurePreserving_add_right (volume : Measure ℝ) (-u)).quasiMeasurePreserving.ae hu'
  simpa only [add_assoc, neg_add_cancel, add_zero] using hp

/-- A measurable real observable invariant almost everywhere under every fixed real time is
almost everywhere constant under the actual normalized occupation law. -/
theorem ae_eq_const_of_renewal_invariant
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω)
    {S : Ω → Ω} (hS : Ergodic S Q)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = θ (L ω, c ω))
    {f : X → ℝ} (hf : Measurable f)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂renewalStationaryLaw Q L θ c, f (θ (t, x)) = f x) :
    ∃ k : ℝ, ∀ᵐ x ∂renewalStationaryLaw Q L θ c, f x = k := by
  let g : Ω → ℝ := fun ω ↦ ∫ t in (0 : ℝ)..1, f (θ (t, c ω))
  have hF : Measurable (fun p : Ω × ℝ ↦ f (θ (p.2, c p.1))) :=
    hf.comp (measurable_evaluation hθ hc)
  have hgm : Measurable g := measurable_timeAverage hF
  have htraj : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume, f (θ (t, c ω)) = g ω := by
    filter_upwards [ae_time_trajectory_const Q hL hLi hLpos hθ hc hadd hf hinv] with ω hω
    obtain ⟨k, hk⟩ := hω
    have hg : g ω = k := timeAverage_eq_of_ae_const hk
    rwa [hg]
  have hgS : g ∘ S =ᵐ[Q] g := by
    filter_upwards [htraj, hcell] with ω hω hcellω
    have ht := (measurePreserving_add_right (volume : Measure ℝ) (L ω)).quasiMeasurePreserving.ae hω
    change g (S ω) = g ω
    apply timeAverage_eq_of_ae_const
    simpa only [hcellω, hadd] using ht
  obtain ⟨k, hk⟩ := hS.ae_eq_const_of_ae_eq_comp₀ hgm.nullMeasurable hgS
  refine ⟨k, ?_⟩
  have hQ : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume, f (θ (t, c ω)) = k := by
    filter_upwards [htraj, hk] with ω hω hkω
    simpa only [Function.const_apply, hkω] using hω
  have hp : ∀ᵐ p ∂Q.prod volume, f (θ (p.2, c p.1)) = k :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF measurable_const)).mpr hQ
  have hr : ∀ᵐ p ∂renewalRoofMeasure Q L, f (θ (p.2, c p.1)) = k :=
    ae_mono Measure.restrict_le_self hp
  rw [renewalStationaryLaw, Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top), renewalOccupation]
  exact (ae_map_iff (measurable_evaluation hθ hc).aemeasurable
    (measurableSet_eq_fun hf measurable_const)).mpr hr

/-- Every measurable set almost invariant under each real time is null or conull for the
constructed occupation law. This is ergodicity of the whole action, not of its time-one map. -/
theorem aeconst_set_renewalStationaryLaw
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω)
    {S : Ω → Ω} (hS : Ergodic S Q)
    {θ : ℝ × X → X} {c : Ω → X} (hθ : Measurable θ) (hc : Measurable c)
    (hadd : ∀ a b x, θ (a, θ (b, x)) = θ (a + b, x))
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = θ (L ω, c ω))
    {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ t : ℝ, (fun x ↦ θ (t, x)) ⁻¹' s =ᵐ[renewalStationaryLaw Q L θ c] s) :
    EventuallyConst s (ae (renewalStationaryLaw Q L θ c)) := by
  classical
  let f : X → ℝ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hfi (t : ℝ) : ∀ᵐ x ∂renewalStationaryLaw Q L θ c, f (θ (t, x)) = f x := by
    filter_upwards [hinv t] with x hx
    change (θ (t, x) ∈ s) = (x ∈ s) at hx
    simp only [f, Set.indicator_apply, hx, Pi.one_apply]
  obtain ⟨k, hk⟩ := ae_eq_const_of_renewal_invariant Q hL hLi hLpos hS hθ hc hadd hcell hf hfi
  apply eventuallyConst_set.mpr
  by_cases hk0 : k = 0
  · right
    filter_upwards [hk] with x hx
    intro hm
    simp only [f, Set.indicator_of_mem hm, Pi.one_apply, hk0, one_ne_zero] at hx
  · left
    filter_upwards [hk] with x hx
    by_contra hm
    have heq : (0 : ℝ) = k := by simpa only [f, Set.indicator_of_notMem hm] using hx
    exact hk0 heq.symm

/-- The actual renewal law is an ergodic probability law for a jointly measurable real additive
action whenever the measure-preserving cell shift is ergodic and concatenation is covariant. -/
theorem ergodicVAdd_renewalStationaryLaw [AddAction ℝ X]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    {L : Ω → ℝ} (hL : Measurable L) (hLi : Integrable L Q)
    (hLpos : ∀ᵐ ω ∂Q, 0 < L ω)
    {S : Ω → Ω} (hS : Ergodic S Q)
    (hθ : Measurable (fun p : ℝ × X ↦ p.1 +ᵥ p.2))
    {c : Ω → X} (hc : Measurable c)
    (hcell : ∀ᵐ ω ∂Q, c (S ω) = L ω +ᵥ c ω) :
    ErgodicVAdd ℝ X (renewalStationaryLaw Q L (fun p ↦ p.1 +ᵥ p.2) c) := by
  have hadd (a b : ℝ) (x : X) : a +ᵥ (b +ᵥ x) = (a + b) +ᵥ x :=
    (add_vadd a b x).symm
  let : VAddInvariantMeasure ℝ X
      (renewalStationaryLaw Q L (fun p ↦ p.1 +ᵥ p.2) c) := by
    constructor
    intro t s hs
    exact (measurePreserving_renewalStationaryLaw Q hL hLi hLpos
      hS.toMeasurePreserving hθ hc hadd hcell t).measure_preimage hs.nullMeasurableSet
  constructor
  intro s hs hinv
  exact aeconst_set_renewalStationaryLaw Q hL hLi hLpos hS hθ hc hadd hcell hs hinv

end OTSelector
