import OTSelector.Gauge.Coercivity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real

/-!
# Peano--hinge and quadratic coercivity

This file contains the deterministic scalar core of the quadratic-localisation argument.  The
objects below deliberately do not mention a finite sample: endpoint coordinates, marks, and a
Lipschitz graph are the only data used here.  The super-level convention in the kernel is closed
(``γ x ≥ t``).  It is the convenient representative for interval integration; replacing it by
the strict convention in `main.tex` changes the kernel only on a null set of levels.

Only the forward endpoint order `ξ ≤ η` is developed here.  The reverse order is obtained by the
reflection described in `main.tex` and is intentionally left to the downstream endpoint wrapper.
-/

open Set MeasureTheory
open scoped BigOperators Interval

namespace OTSelector

/-! ## Compact Peano identities -/

/-- The positive part used by the hinge representation. -/
def positivePart (x : ℝ) : ℝ := max x 0

@[simp] theorem positivePart_of_nonneg {x : ℝ} (hx : 0 ≤ x) : positivePart x = x := by
  simp [positivePart, max_eq_left hx]

@[simp] theorem positivePart_of_nonpos {x : ℝ} (hx : x ≤ 0) : positivePart x = 0 := by
  simp [positivePart, max_eq_right hx]

/-!
The first theorem is the compact-interval, second-order identity used below.  The derivative
functions are explicit so that later applications may use an ordinary `C²` representative rather
than unfold `iteratedDerivWithin` at interval endpoints.
-/

theorem fundamental_theorem_on_Icc
    {a b x : ℝ} (_hab : a ≤ b) (hx : x ∈ Icc a b)
    {f f' : ℝ → ℝ}
    (hf : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y)
    (hf'cont : ContinuousOn f' (Icc a b)) :
    f x = f a + ∫ y in a..x, f' y := by
  have hax : a ≤ x := hx.1
  have hmem : ∀ y ∈ [[a, x]], y ∈ Icc a b := by
    intro y hy
    rw [uIcc_of_le hax] at hy
    exact ⟨hy.1, hy.2.trans hx.2⟩
  have hderiv : ∀ y ∈ [[a, x]], HasDerivAt f (f' y) y := fun y hy => hf y (hmem y hy)
  have hfi : IntervalIntegrable f' volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hax]
    exact hf'cont.mono (Icc_subset_Icc le_rfl hx.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hfi
  linarith

theorem peano_second_order_on_Icc
    {a b x : ℝ} (_hab : a ≤ b) (hx : x ∈ Icc a b)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc a b, HasDerivAt f' (f'' y) y)
    (hf'cont : ContinuousOn f' (Icc a b))
    (hf''cont : ContinuousOn f'' (Icc a b)) :
    f x = f a + f' a * (x - a) + ∫ y in a..x, (x - y) * f'' y := by
  have hax : a ≤ x := hx.1
  have hmem : ∀ y ∈ [[a, x]], y ∈ Icc a b := by
    intro y hy
    rw [uIcc_of_le hax] at hy
    exact ⟨hy.1, hy.2.trans hx.2⟩
  have hfx : ∫ y in a..x, f' y = f x - f a := by
    have hderiv : ∀ y ∈ [[a, x]], HasDerivAt f (f' y) y :=
      fun y hy => hf y (hmem y hy)
    have hfi : IntervalIntegrable f' volume a x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hax]
      exact hf'cont.mono (Icc_subset_Icc le_rfl hx.2)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hfi
  have hparts : ∫ y in a..x, (x - y) * f'' y =
      -(x - a) * f' a + ∫ y in a..x, f' y := by
    have hu : ∀ y ∈ [[a, x]], HasDerivAt (fun z : ℝ => x - z) (-1) y := by
      intro y hy
      have h := (hasDerivAt_const (x := y) x).sub (hasDerivAt_id y)
      have hfun : (fun z : ℝ => x - z) = (fun z : ℝ => x) - id := by
        funext z
        simp [Pi.sub_apply, id_eq]
      rw [hfun]
      simpa using h
    have hv : ∀ y ∈ [[a, x]], HasDerivAt f' (f'' y) y := fun y hy => hf' y (hmem y hy)
    have hu' : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume a x :=
      intervalIntegrable_const
    have hv' : IntervalIntegrable f'' volume a x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hax]
      exact hf''cont.mono (Icc_subset_Icc le_rfl hx.2)
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun z : ℝ => x - z) (u' := fun _ : ℝ => (-1 : ℝ))
      (v := f') (v' := f'') hu hv hu' hv'
    have h' : ∫ y in a..x, (x - y) * f'' y =
        (x - x) * f' x - (x - a) * f' a - ∫ y in a..x, (-1 : ℝ) * f' y := h
    rw [intervalIntegral.integral_const_mul] at h'
    convert h' using 1; ring
  linarith

/-! A compact-interval form of the positive-part remainder. -/

theorem positivePart_remainder_on_Icc
    {a b x : ℝ} (_hab : a ≤ b) (hx : x ∈ Icc a b) {g : ℝ → ℝ} :
    (∫ y in a..x, (x - y) * g y) =
      ∫ y in a..b, g y * positivePart (x - y) := by
  have hind : (fun y : ℝ => g y * positivePart (x - y)) =
      (fun y : ℝ => indicator {y : ℝ | y ≤ x} (fun z => g z * (x - z)) y) := by
    funext y
    by_cases hy : y ≤ x
    · rw [positivePart_of_nonneg (sub_nonneg.mpr hy)]
      have hymem : y ∈ {z : ℝ | z ≤ x} := hy
      rw [Set.indicator_of_mem hymem]
    · have hy' : x ≤ y := le_of_not_ge hy
      rw [positivePart_of_nonpos (sub_nonpos.mpr hy')]
      have hynmem : y ∉ {z : ℝ | z ≤ x} := hy
      rw [Set.indicator_of_notMem hynmem]
      ring
  calc
    (∫ y in a..x, (x - y) * g y) = ∫ y in a..x, g y * (x - y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      ring
    _ = ∫ y in a..b, indicator {y : ℝ | y ≤ x} (fun z => g z * (x - z)) y :=
      (intervalIntegral.integral_indicator hx).symm
    _ = ∫ y in a..b, g y * positivePart (x - y) := by rw [← hind]

theorem first_derivative_remainder_on_Icc
    {a b x : ℝ} (_hab : a ≤ b) (hx : x ∈ Icc a b) {g : ℝ → ℝ} :
    (∫ y in a..x, g y) =
      ∫ y in a..b, indicator {y : ℝ | y ≤ x} g y := by
  exact (intervalIntegral.integral_indicator hx).symm

/-! ## Four-point scalar objects -/

/-- The rank-scale source/target four-point data used by (2.1)--(2.4). -/
def fourPointGap (_gamma : ℝ → ℝ) (xi eta _a _b : ℝ) : ℝ :=
  eta - xi

def fourPointSourceValue (gamma : ℝ → ℝ) (xi : ℝ) : ℝ := gamma xi

def fourPointTargetValue (gamma : ℝ → ℝ) (eta : ℝ) : ℝ := gamma eta

def fourPointDenominator (a b : ℝ) : ℝ := a + b

noncomputable def fourPointQuotient (gamma : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  (fourPointGap gamma xi eta a b + a * fourPointSourceValue gamma xi +
      b * fourPointTargetValue gamma eta) / fourPointDenominator a b

def graphSuperlevel (gamma : ℝ → ℝ) (xi eta t : ℝ) : Set ℝ :=
  Ioc xi eta ∩ {x | t ≤ gamma x}

/-- Length of the closed super-level representative on the feedback interval. -/
noncomputable def graphOccupation (gamma : ℝ → ℝ) (xi eta t : ℝ) : ℝ :=
  ∫ x in xi..eta, ({x : ℝ | t ≤ gamma x}).indicator (fun _ => (1 : ℝ)) x

noncomputable def hingeKernel (gamma : ℝ → ℝ) (xi eta a b t : ℝ) : ℝ :=
  let u := fourPointSourceValue gamma xi
  let v := fourPointTargetValue gamma eta
  let D := fourPointDenominator a b
  let q := fourPointQuotient gamma xi eta a b
  D * positivePart (q - t) - a * positivePart (u - t) -
      b * positivePart (v - t) - graphOccupation gamma xi eta t

/-- The exact gauged scalar cost, with the graph integral written explicitly. -/
noncomputable def gaugedFourPointCost (f f' : ℝ → ℝ) (gamma : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  let q := fourPointQuotient gamma xi eta a b
  let u := fourPointSourceValue gamma xi
  let v := fourPointTargetValue gamma eta
  let D := fourPointDenominator a b
  D * f q - a * f u - b * f v - ∫ x in xi..eta, f' (gamma x)

noncomputable def quadraticCost (gamma : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  gaugedFourPointCost (fun x => x ^ 2 / 2) id gamma xi eta a b

noncomputable def chord (xi eta u v x : ℝ) : ℝ :=
  u + (v - u) * (x - xi) / (eta - xi)

/-! ## Measurability and the layer-cake/Fubini identity -/

theorem graphSuperlevel_measurable {gamma : ℝ → ℝ} (hgamma : Continuous gamma) :
    MeasurableSet (graphSuperlevel gamma xi eta t) := by
  unfold graphSuperlevel
  exact measurableSet_Ioc.inter (measurableSet_le measurable_const hgamma.measurable)

theorem graphOccupation_eq_measure {gamma : ℝ → ℝ} (hxi : xi ≤ eta)
    (hgamma : Continuous gamma) :
    graphOccupation gamma xi eta t = Measure.real volume (graphSuperlevel gamma xi eta t) := by
  unfold graphOccupation
  rw [intervalIntegral.integral_of_le hxi]
  rw [setIntegral_indicator]
  · simp [graphSuperlevel]
  exact measurableSet_le measurable_const hgamma.measurable

private theorem graph_relation_measurable {gamma : ℝ → ℝ} (hgamma : Continuous gamma) :
    MeasurableSet {p : ℝ × ℝ | p.2 ≤ gamma p.1} := by
  exact measurableSet_le measurable_snd (hgamma.measurable.comp measurable_fst)

theorem graph_layer_cake
    {A B xi eta : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (_hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf''cont : ContinuousOn f'' (Icc A B)) :
    (∫ x in xi..eta, ∫ t in A..B,
        (fun p : ℝ × ℝ => (if p.2 ≤ gamma p.1 then f'' p.2 else 0)) (x, t)) =
      ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
  let relation : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ gamma p.1}
  let F : ℝ → ℝ → ℝ := fun x t => relation.indicator (fun p : ℝ × ℝ => f'' p.2) (x, t)
  have hrel : MeasurableSet relation := by
    dsimp [relation]
    exact graph_relation_measurable hgamma
  have hcontprod : ContinuousOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) := by
    apply hf''cont.comp continuousOn_snd
    intro p hp
    rw [uIcc_of_le hxi, uIcc_of_le hAB] at hp
    exact hp.2
  have hbase : IntegrableOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) :=
    hcontprod.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hF : IntegrableOn F.uncurry (uIoc xi eta ×ˢ uIoc A B) := by
    change IntegrableOn (relation.indicator (fun p : ℝ × ℝ => f'' p.2))
      (uIoc xi eta ×ˢ uIoc A B)
    exact hbase.indicator hrel |>.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hFprod : Integrable F.uncurry
      ((volume.restrict (uIoc xi eta)).prod (volume.restrict (uIoc A B))) := by
    change Integrable F.uncurry ((volume.prod volume).restrict
      (uIoc xi eta ×ˢ uIoc A B)) at hF
    rw [← Measure.prod_restrict] at hF
    exact hF
  have hswap := intervalIntegral_intervalIntegral_swap (F := F) hF
  have hinner_eq : ∀ x, (∫ t, F x t ∂(volume.restrict (uIoc A B))) =
      ∫ t in A..B, F x t := by
    intro x
    rw [intervalIntegral.integral_of_le hAB, uIoc_of_le hAB]
  have hinner_int : IntervalIntegrable (fun x => ∫ t in A..B, F x t) volume xi eta := by
    rw [intervalIntegrable_iff]
    have h := hFprod.integral_prod_left
    exact h.congr (Filter.Eventually.of_forall hinner_eq)
  have hfactor : ∀ t, (∫ x in xi..eta, F x t) =
      f'' t * graphOccupation gamma xi eta t := by
    intro t
    have hpoint : (fun x : ℝ => F x t) =
        (fun x => f'' t * ({y : ℝ | t ≤ gamma y}).indicator
          (fun _ => (1 : ℝ)) x) := by
      funext x
      by_cases hxt : t ≤ gamma x <;> simp [F, relation, hxt]
    rw [hpoint, intervalIntegral.integral_const_mul]
    rfl
  have houter_int : IntervalIntegrable
      (fun t => f'' t * graphOccupation gamma xi eta t) volume A B := by
    rw [intervalIntegrable_iff]
    have h := hFprod.integral_prod_right
    have h' : Integrable (fun t => ∫ x, F x t ∂(volume.restrict (uIoc xi eta)))
        (volume.restrict (uIoc A B)) := h
    apply h'.congr
    filter_upwards [] with t
    rw [← hfactor t]
    rw [intervalIntegral.integral_of_le hxi, uIoc_of_le hxi]
  have hswap' :
      (∫ x in xi..eta, ∫ t in A..B, F x t) =
        ∫ t in A..B, ∫ x in xi..eta, F x t := hswap
  calc
    (∫ x in xi..eta, ∫ t in A..B,
        (fun p : ℝ × ℝ => if p.2 ≤ gamma p.1 then f'' p.2 else 0) (x, t)) =
        ∫ x in xi..eta, ∫ t in A..B, F x t := by rfl
    _ = ∫ t in A..B, ∫ x in xi..eta, F x t := hswap'
    _ = ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hfactor t

private theorem graph_layer_inner_integrable
    {A B xi eta : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (_hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf''cont : ContinuousOn f'' (Icc A B)) :
    IntervalIntegrable
      (fun x => ∫ t in A..B,
        (fun p : ℝ × ℝ => if p.2 ≤ gamma p.1 then f'' p.2 else 0) (x, t)) volume xi eta := by
  let relation : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ gamma p.1}
  let F : ℝ → ℝ → ℝ := fun x t => relation.indicator (fun p : ℝ × ℝ => f'' p.2) (x, t)
  have hcontprod : ContinuousOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) := by
    apply hf''cont.comp continuousOn_snd
    intro p hp
    rw [uIcc_of_le hxi, uIcc_of_le hAB] at hp
    exact hp.2
  have hbase : IntegrableOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) :=
    hcontprod.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hF : IntegrableOn F.uncurry (uIoc xi eta ×ˢ uIoc A B) := by
    change IntegrableOn (relation.indicator (fun p : ℝ × ℝ => f'' p.2))
      (uIoc xi eta ×ˢ uIoc A B)
    exact hbase.indicator (by dsimp [relation]; exact graph_relation_measurable hgamma) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hFprod : Integrable F.uncurry
      ((volume.restrict (uIoc xi eta)).prod (volume.restrict (uIoc A B))) := by
    change Integrable F.uncurry ((volume.prod volume).restrict
      (uIoc xi eta ×ˢ uIoc A B)) at hF
    rw [← Measure.prod_restrict] at hF
    exact hF
  rw [intervalIntegrable_iff]
  have h := hFprod.integral_prod_left
  apply h.congr
  filter_upwards [] with x
  simp only [uIoc_of_le hAB, intervalIntegral.integral_of_le hAB]
  simp [F, relation, Set.indicator]

/-- Integrability in the level coordinate of a continuous weight times graph occupation. -/
theorem graph_occupation_product_integrable
    {A B xi eta : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (_hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf''cont : ContinuousOn f'' (Icc A B)) :
    IntervalIntegrable (fun t => f'' t * graphOccupation gamma xi eta t) volume A B := by
  let relation : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ gamma p.1}
  let F : ℝ → ℝ → ℝ := fun x t => relation.indicator (fun p : ℝ × ℝ => f'' p.2) (x, t)
  have hcontprod : ContinuousOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) := by
    apply hf''cont.comp continuousOn_snd
    intro p hp
    rw [uIcc_of_le hxi, uIcc_of_le hAB] at hp
    exact hp.2
  have hbase : IntegrableOn (fun p : ℝ × ℝ => f'' p.2)
      (uIcc xi eta ×ˢ uIcc A B) :=
    hcontprod.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hF : IntegrableOn F.uncurry (uIoc xi eta ×ˢ uIoc A B) := by
    change IntegrableOn (relation.indicator (fun p : ℝ × ℝ => f'' p.2))
      (uIoc xi eta ×ˢ uIoc A B)
    exact hbase.indicator (by dsimp [relation]; exact graph_relation_measurable hgamma) |>.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hFprod : Integrable F.uncurry
      ((volume.restrict (uIoc xi eta)).prod (volume.restrict (uIoc A B))) := by
    change Integrable F.uncurry ((volume.prod volume).restrict
      (uIoc xi eta ×ˢ uIoc A B)) at hF
    rw [← Measure.prod_restrict] at hF
    exact hF
  rw [intervalIntegrable_iff]
  have h := hFprod.integral_prod_right
  apply h.congr
  filter_upwards [] with t
  have hfactor : (∫ x in xi..eta, F x t) =
      f'' t * graphOccupation gamma xi eta t := by
    have hpoint : (fun x : ℝ => F x t) =
        (fun x => f'' t * ({y : ℝ | t ≤ gamma y}).indicator
          (fun _ => (1 : ℝ)) x) := by
      funext x
      by_cases hxt : t ≤ gamma x <;> simp [F, relation, hxt]
    rw [hpoint, intervalIntegral.integral_const_mul]
    rfl
  rw [← hfactor]
  simp only [uIoc_of_le hxi, intervalIntegral.integral_of_le hxi]
  simp [F, Set.indicator]

/-- The four-point hinge kernel is interval-integrable on every compact level interval that
contains the graph range. -/
theorem hingeKernel_intervalIntegrable
    {A B xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma : ℝ → ℝ} (hgamma : Continuous gamma)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B) :
    IntervalIntegrable (hingeKernel gamma xi eta a b) volume A B := by
  let u := fourPointSourceValue gamma xi
  let v := fourPointTargetValue gamma eta
  let D := fourPointDenominator a b
  let q := fourPointQuotient gamma xi eta a b
  have hpos : ∀ z : ℝ,
      IntervalIntegrable (fun t : ℝ ↦ positivePart (z - t)) volume A B := by
    intro z
    apply ContinuousOn.intervalIntegrable
    exact ((continuous_const.sub continuous_id).max continuous_const).continuousOn
  have hOcc : IntervalIntegrable (graphOccupation gamma xi eta) volume A B := by
    have h := graph_occupation_product_integrable hAB hxi hgamma hrange
      (f'' := fun _ : ℝ ↦ (1 : ℝ)) continuousOn_const
    simpa only [one_mul] using h
  have hD := (hpos q).const_mul D
  have ha := (hpos u).const_mul a
  have hb := (hpos v).const_mul b
  change IntervalIntegrable
    (fun t ↦ D * positivePart (q - t) - a * positivePart (u - t) -
      b * positivePart (v - t) - graphOccupation gamma xi eta t) volume A B
  exact ((hD.sub ha).sub hb).sub hOcc

/-! ## Peano--hinge representation -/

theorem gaugedFourPointCost_eq_hinge_integral
    {A B xi eta : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma f f' f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc A B, HasDerivAt f' (f'' y) y)
    (hf'cont : ContinuousOn f' (Icc A B))
    (hf''cont : ContinuousOn f'' (Icc A B))
    (hq_mem : fourPointQuotient gamma xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    gaugedFourPointCost f f' gamma xi eta a b =
      ∫ t in A..B, f'' t * hingeKernel gamma xi eta a b t := by
  let d := fourPointGap gamma xi eta a b
  let u := fourPointSourceValue gamma xi
  let v := fourPointTargetValue gamma eta
  let D := fourPointDenominator a b
  let q := fourPointQuotient gamma xi eta a b
  have hD : 0 < D := by
    dsimp [D, fourPointDenominator]
    linarith [ha.1, hb.1]
  have hq_mem : q ∈ Icc A B := hq_mem
  have hu_mem : u ∈ Icc A B := hrange xi ⟨le_rfl, hxi⟩
  have hv_mem : v ∈ Icc A B := hrange eta ⟨hxi, le_rfl⟩
  have hq := peano_second_order_on_Icc hAB hq_mem hf hf' hf'cont hf''cont
  have hu := peano_second_order_on_Icc hAB hu_mem hf hf' hf'cont hf''cont
  have hv := peano_second_order_on_Icc hAB hv_mem hf hf' hf'cont hf''cont
  have hq' : f q = f A + f' A * (q - A) +
      ∫ t in A..B, f'' t * positivePart (q - t) := by
    rw [hq, positivePart_remainder_on_Icc hAB hq_mem]
  have hu' : f u = f A + f' A * (u - A) +
      ∫ t in A..B, f'' t * positivePart (u - t) := by
    rw [hu, positivePart_remainder_on_Icc hAB hu_mem]
  have hv' : f v = f A + f' A * (v - A) +
      ∫ t in A..B, f'' t * positivePart (v - t) := by
    rw [hv, positivePart_remainder_on_Icc hAB hv_mem]
  have hfp : ∀ x ∈ Icc xi eta,
      f' (gamma x) = f' A +
        ∫ t in A..B, ({t : ℝ | t ≤ gamma x}).indicator f'' t := by
    intro x hx
    have hxg := hrange x hx
    have h := fundamental_theorem_on_Icc hAB hxg hf' hf''cont
    rw [h, first_derivative_remainder_on_Icc hAB hxg]
  have hgraph : ∫ x in xi..eta, f' (gamma x) =
      (eta - xi) * f' A + ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
    let F : ℝ → ℝ → ℝ := fun x t =>
      ({p : ℝ × ℝ | p.2 ≤ gamma p.1}).indicator
        (fun p : ℝ × ℝ => f'' p.2) (x, t)
    have hF := graph_layer_cake hAB hxi hgamma hrange hf''cont
    have hinner : IntervalIntegrable (fun x => ∫ t in A..B, F x t) volume xi eta := by
      apply graph_layer_inner_integrable hAB hxi hgamma hrange hf''cont
    have hleft : ∫ x in xi..eta, f' (gamma x) =
        ∫ x in xi..eta, (f' A + ∫ t in A..B, F x t) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hxi] at hx
      exact hfp x hx
    rw [hleft, intervalIntegral.integral_add intervalIntegrable_const hinner]
    rw [intervalIntegral.integral_const]
    simpa [F, Set.indicator, smul_eq_mul] using hF
  have hP : ∀ z : ℝ, IntervalIntegrable
      (fun t => f'' t * positivePart (z - t)) volume A B := by
    intro z
    have hc : ContinuousOn (fun t : ℝ => f'' t * positivePart (z - t))
        (uIcc A B) := by
      rw [uIcc_of_le hAB]
      change ContinuousOn (fun t : ℝ => f'' t * max (z - t) 0) (Icc A B)
      fun_prop
    exact hc.intervalIntegrable
  have hPq := hP q
  have hPu := hP u
  have hPv := hP v
  have hOcc := graph_occupation_product_integrable hAB hxi hgamma hrange hf''cont
  have hDq : IntervalIntegrable
      (fun t => D * (f'' t * positivePart (q - t))) volume A B := hPq.const_mul D
  have hDu : IntervalIntegrable
      (fun t => a * (f'' t * positivePart (u - t))) volume A B := hPu.const_mul a
  have hDv : IntervalIntegrable
      (fun t => b * (f'' t * positivePart (v - t))) volume A B := hPv.const_mul b
  have hleftInt : IntervalIntegrable
      (fun t => D * (f'' t * positivePart (q - t)) -
        a * (f'' t * positivePart (u - t))) volume A B := hDq.sub hDu
  have hrightInt : IntervalIntegrable
      (fun t => b * (f'' t * positivePart (v - t)) +
        f'' t * graphOccupation gamma xi eta t) volume A B := hDv.add hOcc
  have hcomb :
      (∫ t in A..B, f'' t *
        (D * positivePart (q - t) - a * positivePart (u - t) -
          b * positivePart (v - t) - graphOccupation gamma xi eta t)) =
        D * (∫ t in A..B, f'' t * positivePart (q - t)) -
          a * (∫ t in A..B, f'' t * positivePart (u - t)) -
          b * (∫ t in A..B, f'' t * positivePart (v - t)) -
          ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
    calc
      (∫ t in A..B, f'' t *
          (D * positivePart (q - t) - a * positivePart (u - t) -
            b * positivePart (v - t) - graphOccupation gamma xi eta t)) =
          ∫ t in A..B,
            (D * (f'' t * positivePart (q - t)) -
              a * (f'' t * positivePart (u - t)) -
              b * (f'' t * positivePart (v - t)) -
              f'' t * graphOccupation gamma xi eta t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
      _ = ∫ t in A..B,
            (D * (f'' t * positivePart (q - t)) -
              a * (f'' t * positivePart (u - t))) -
            (b * (f'' t * positivePart (v - t)) +
              f'' t * graphOccupation gamma xi eta t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
      _ = (∫ t in A..B, D * (f'' t * positivePart (q - t)) -
              a * (f'' t * positivePart (u - t))) -
            (∫ t in A..B, b * (f'' t * positivePart (v - t)) +
              f'' t * graphOccupation gamma xi eta t) :=
          intervalIntegral.integral_sub hleftInt hrightInt
      _ = (∫ t in A..B, D * (f'' t * positivePart (q - t))) -
            (∫ t in A..B, a * (f'' t * positivePart (u - t))) -
            ((∫ t in A..B, b * (f'' t * positivePart (v - t))) +
              ∫ t in A..B, f'' t * graphOccupation gamma xi eta t) := by
          rw [intervalIntegral.integral_sub hDq hDu]
          rw [intervalIntegral.integral_add hDv hOcc]
      _ = D * (∫ t in A..B, f'' t * positivePart (q - t)) -
            a * (∫ t in A..B, f'' t * positivePart (u - t)) -
            b * (∫ t in A..B, f'' t * positivePart (v - t)) -
            ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
          have hDq' :
              (∫ t in A..B, D * (f'' t * positivePart (q - t))) =
                D * (∫ t in A..B, f'' t * positivePart (q - t)) :=
            intervalIntegral.integral_const_mul D
              (fun t : ℝ => f'' t * positivePart (q - t))
          have hDu' :
              (∫ t in A..B, a * (f'' t * positivePart (u - t))) =
                a * (∫ t in A..B, f'' t * positivePart (u - t)) :=
            intervalIntegral.integral_const_mul a
              (fun t : ℝ => f'' t * positivePart (u - t))
          have hDv' :
              (∫ t in A..B, b * (f'' t * positivePart (v - t))) =
                b * (∫ t in A..B, f'' t * positivePart (v - t)) :=
            intervalIntegral.integral_const_mul b
              (fun t : ℝ => f'' t * positivePart (v - t))
          rw [hDq', hDu', hDv']
          ring
  have hqdef : D * q = d + a * u + b * v := by
    have hD' : a + b ≠ 0 := by
      dsimp [D] at hD ⊢
      exact ne_of_gt hD
    dsimp [D, q, d, fourPointQuotient, fourPointGap, fourPointSourceValue,
      fourPointTargetValue, fourPointDenominator]
    exact mul_div_cancel₀ _ hD'
  have hexp : gaugedFourPointCost f f' gamma xi eta a b =
      D * (f A + f' A * (q - A) +
          ∫ t in A..B, f'' t * positivePart (q - t)) -
        a * (f A + f' A * (u - A) +
          ∫ t in A..B, f'' t * positivePart (u - t)) -
        b * (f A + f' A * (v - A) +
          ∫ t in A..B, f'' t * positivePart (v - t)) -
        ((eta - xi) * f' A +
          ∫ t in A..B, f'' t * graphOccupation gamma xi eta t) := by
    change D * f q - a * f u - b * f v - ∫ x in xi..eta, f' (gamma x) = _
    rw [hq', hu', hv', hgraph]
  calc
    gaugedFourPointCost f f' gamma xi eta a b = _ := hexp
    _ = D * (∫ t in A..B, f'' t * positivePart (q - t)) -
          a * (∫ t in A..B, f'' t * positivePart (u - t)) -
      b * (∫ t in A..B, f'' t * positivePart (v - t)) -
          ∫ t in A..B, f'' t * graphOccupation gamma xi eta t := by
      dsimp [D, d, u, v, fourPointDenominator, fourPointGap,
        fourPointSourceValue, fourPointTargetValue] at hqdef ⊢
      ring_nf
      linear_combination (f' A) * hqdef
    _ = ∫ t in A..B, f'' t * hingeKernel gamma xi eta a b t := by
      symm
      simpa [hingeKernel, d, u, v, D, q] using hcomb

/-! The quadratic specialization is kept as a small API corollary.  It still uses the forward
endpoint order and the same compact mark range; the Euclidean comparison is a later layer. -/

theorem quadraticCost_eq_hinge_integral
    {A B xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta)
    {gamma : ℝ → ℝ} (hgamma : Continuous gamma)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hq_mem : fourPointQuotient gamma xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    quadraticCost gamma xi eta a b =
      ∫ t in A..B, hingeKernel gamma xi eta a b t := by
  have hf : ∀ y ∈ Icc A B,
      HasDerivAt (fun x : ℝ => x ^ 2 / 2) (id y) y := by
    intro y hy
    convert ((hasDerivAt_id y).mul (hasDerivAt_id y)).div_const 2 using 1
    · rfl
    · rfl
    · funext x
      simp [id]
      ring
    · simp [id]
  have hf' : ∀ y ∈ Icc A B, HasDerivAt id (1 : ℝ) y := by
    intro y hy
    simpa using hasDerivAt_id y
  have h := gaugedFourPointCost_eq_hinge_integral (a := a) (b := b)
    (gamma := gamma) (f := fun x : ℝ => x ^ 2 / 2) (f' := id)
    (f'' := fun _ : ℝ => (1 : ℝ)) hAB hxi hgamma hrange hf hf'
    continuousOn_id continuousOn_const hq_mem ha hb
  simpa [quadraticCost, id] using h

/-! ## Hinge non-negativity -/

def ScalarLipschitz (lam : ℝ) (gamma : ℝ → ℝ) : Prop :=
  ∀ x y, |gamma y - gamma x| ≤ lam * |y - x|

private lemma graph_occupation_le_interval
    {gamma : ℝ → ℝ} (hxi : xi ≤ eta) (hgamma : Continuous gamma)
    (hsub : graphSuperlevel gamma xi eta t ⊆ Icc c d) (hcd : c ≤ d) :
    graphOccupation gamma xi eta t ≤ d - c := by
  rw [graphOccupation_eq_measure hxi hgamma]
  calc
    Measure.real volume (graphSuperlevel gamma xi eta t) ≤
        Measure.real volume (Icc c d) := by
          refine measureReal_mono hsub ?_
          exact (show volume (Icc c d) < ⊤ from measure_Icc_lt_top).ne
    _ = d - c := by simp [Measure.real, Real.volume_Icc, hcd]

private lemma endpoint_left_subset
    {lam xi eta u t : ℝ} (hlam : 0 < lam) (_hxi : xi ≤ eta)
    {gamma : ℝ → ℝ} (hgamma : ScalarLipschitz lam gamma)
    (hu : gamma xi = u) (_htu : u ≤ t) :
    graphSuperlevel gamma xi eta t ⊆ Icc (xi + (t - u) / lam) eta := by
  intro x hx
  have hxmem := hx.1
  have hdist := hgamma xi x
  have hbound : t - u ≤ lam * (x - xi) := by
    calc
      t - u ≤ gamma x - u := sub_le_sub_right hx.2 _
      _ ≤ |gamma x - u| := le_abs_self _
      _ = |gamma x - gamma xi| := by rw [hu]
      _ ≤ lam * |x - xi| := hdist
      _ = lam * (x - xi) := by rw [abs_of_nonneg (sub_nonneg.mpr hxmem.1.le)]
  have hleft : (t - u) / lam ≤ x - xi :=
    (div_le_iff₀ hlam).2 (by simpa [mul_comm] using hbound)
  constructor
  · linarith
  · exact hxmem.2

private lemma endpoint_right_subset
    {lam xi eta v t : ℝ} (hlam : 0 < lam) (_hxi : xi ≤ eta)
    {gamma : ℝ → ℝ} (hgamma : ScalarLipschitz lam gamma)
    (hv : gamma eta = v) (_htv : v ≤ t) :
    graphSuperlevel gamma xi eta t ⊆ Icc xi (eta - (t - v) / lam) := by
  intro x hx
  have hxmem := hx.1
  have hdist := hgamma eta x
  have hbound : t - v ≤ lam * (eta - x) := by
    calc
      t - v ≤ gamma x - v := sub_le_sub_right hx.2 _
      _ ≤ |gamma x - v| := le_abs_self _
      _ = |gamma x - gamma eta| := by rw [hv]
      _ ≤ lam * |x - eta| := hdist
      _ = lam * (eta - x) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxmem.2)]
        ring
  have hright : (t - v) / lam ≤ eta - x :=
    (div_le_iff₀ hlam).2 (by simpa [mul_comm] using hbound)
  constructor
  · exact hxmem.1.le
  · linarith

private lemma q_above_graph
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    ∀ x ∈ Icc xi eta,
      gamma x < fourPointQuotient gamma xi eta a b := by
  let d := eta - xi
  let u := gamma xi
  let v := gamma eta
  let D := a + b
  let q := (d + a * u + b * v) / D
  have hd : 0 < d := sub_pos.mpr hxi
  have hD : 0 < D := by
    dsimp [D]
    linarith [ha.1, hb.1]
  have hD' : a + b ≠ 0 := by
    dsimp [D] at hD ⊢
    exact ne_of_gt hD
  have hΔ : |v - u| ≤ lam * d := by
    dsimp [v, u, d]
    calc
      |gamma eta - gamma xi| ≤ lam * |eta - xi| := hgamma xi eta
      _ = lam * d := by rw [abs_of_nonneg (sub_nonneg.mpr hxi.le)]
  have hΔlo : -lam * d ≤ v - u := by
    have := neg_le_of_abs_le hΔ
    linarith
  have hΔhi : v - u ≤ lam * d := le_trans (le_abs_self _) hΔ
  have hbl : lam * b < 1 := by
    have h1 : lam * b ≤ lam * 2 := mul_le_mul_of_nonneg_left hb.2 hlam0
    nlinarith
  have hal : lam * a < 1 := by
    have h1 : lam * a ≤ lam * 1 := mul_le_mul_of_nonneg_left ha.2 hlam0
    nlinarith
  have hqu : 0 < q - u := by
    have hn : 0 < d + b * (v - u) := by
      have hb0 : 0 ≤ b := le_trans (by norm_num) hb.1
      have hmul := mul_le_mul_of_nonneg_left hΔlo hb0
      have hp : 0 < d * (1 - lam * b) := mul_pos hd (sub_pos.mpr hbl)
      nlinarith
    have heq : q - u = (d + b * (v - u)) / D := by
      dsimp [q, D, u, v]
      field_simp [hD']
      ring
    rw [heq]
    exact div_pos hn hD
  have hqv : 0 < q - v := by
    have hn : 0 < d - a * (v - u) := by
      have ha0 : 0 ≤ a := ha.1
      have hmul := mul_le_mul_of_nonneg_left hΔhi ha0
      have hp : 0 < d * (1 - lam * a) := mul_pos hd (sub_pos.mpr hal)
      nlinarith
    have heq : q - v = (d - a * (v - u)) / D := by
      dsimp [q, D, u, v]
      field_simp [hD']
      ring
    rw [heq]
    exact div_pos hn hD
  have hqsum : lam * d < (q - u) + (q - v) := by
    have hba : 0 ≤ b - a := by linarith [ha.2, hb.1]
    have hmul := mul_le_mul_of_nonneg_left hΔlo hba
    have hp : 0 < 2 * d * (1 - lam * b) := by positivity
    have hnum : lam * d * D < 2 * d + (b - a) * (v - u) := by
      dsimp [D]
      nlinarith
    have hid : ((q - u) + (q - v)) * D = 2 * d + (b - a) * (v - u) := by
      dsimp [q, D, u, v]
      field_simp [hD']
      ring
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hid]
    exact hnum
  intro x hx
  by_contra hnot
  have hqx : q ≤ gamma x := le_of_not_gt hnot
  have hs : 0 ≤ x - xi := sub_nonneg.mpr hx.1
  have ht : 0 ≤ eta - x := sub_nonneg.mpr hx.2
  have hxu : q - u ≤ lam * (x - xi) := by
    calc
      q - u ≤ gamma x - u := sub_le_sub_right hqx _
      _ ≤ |gamma x - u| := le_abs_self _
      _ ≤ lam * |x - xi| := hgamma xi x
      _ = lam * (x - xi) := by rw [abs_of_nonneg hs]
  have hxv : q - v ≤ lam * (eta - x) := by
    calc
      q - v ≤ gamma x - v := sub_le_sub_right hqx _
      _ ≤ |gamma x - v| := le_abs_self _
      _ ≤ lam * |x - eta| := hgamma eta x
      _ = lam * (eta - x) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
        ring
  nlinarith [hqx, hxu, hxv, hqsum]

/-! The nonnegative closed-level hinge kernel. -/

theorem hingeKernel_nonneg
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma_cont : Continuous gamma) (hgamma : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) (t : ℝ) :
    0 ≤ hingeKernel gamma xi eta a b t := by
  let d := eta - xi
  let u := gamma xi
  let v := gamma eta
  let D := a + b
  let q := (d + a * u + b * v) / D
  have hd : 0 < d := sub_pos.mpr hxi
  have hD : 0 < D := by
    dsimp [D]
    linarith [ha.1, hb.1]
  have hD' : a + b ≠ 0 := by
    dsimp [D] at hD ⊢
    exact ne_of_gt hD
  have hqabove := q_above_graph hxi hgamma hlam0 hlam ha hb
  have hqu : u < q := by
    have := hqabove xi ⟨le_rfl, hxi.le⟩
    dsimp [u, q, d, D]
    exact this
  have hqv : v < q := by
    have := hqabove eta ⟨hxi.le, le_rfl⟩
    dsimp [v, q, d, D]
    exact this
  have hDelta : |v - u| ≤ lam * d := by
    dsimp [v, u, d]
    calc
      |gamma eta - gamma xi| ≤ lam * |eta - xi| := hgamma xi eta
      _ = lam * d := by rw [abs_of_nonneg (sub_nonneg.mpr hxi.le)]
  have hqeq : D * q = d + a * u + b * v := by
    dsimp [q, D]
    exact mul_div_cancel₀ _ hD'
  have hocc_nonneg : 0 ≤ graphOccupation gamma xi eta t := by
    unfold graphOccupation
    exact intervalIntegral.integral_nonneg_of_forall hxi.le
      (fun x => indicator_nonneg (by intro y hy; norm_num) x)
  have hocc_le_d : graphOccupation gamma xi eta t ≤ d := by
    have hsub : graphSuperlevel gamma xi eta t ⊆ Icc xi eta :=
      fun x hx => ⟨hx.1.1.le, hx.1.2⟩
    simpa [d] using graph_occupation_le_interval hxi.le hgamma_cont hsub hxi.le
  change 0 ≤ D * positivePart (q - t) - a * positivePart (u - t) -
      b * positivePart (v - t) - graphOccupation gamma xi eta t
  by_cases hqt : q ≤ t
  · have hempty : graphSuperlevel gamma xi eta t = ∅ := by
      ext x
      constructor
      · intro hx
        have hxle := hqabove x ⟨hx.1.1.le, hx.1.2⟩
        change gamma x < q at hxle
        exfalso
        exact (not_lt_of_ge hqt (lt_of_le_of_lt hx.2 hxle))
      · simp
    have hocc : graphOccupation gamma xi eta t = 0 := by
      rw [graphOccupation_eq_measure hxi.le hgamma_cont, hempty]
      simp
    have hut : u ≤ t := hqu.le.trans hqt
    have hvt : v ≤ t := hqv.le.trans hqt
    rw [positivePart_of_nonpos (sub_nonpos.mpr hqt),
      positivePart_of_nonpos (sub_nonpos.mpr hut),
      positivePart_of_nonpos (sub_nonpos.mpr hvt), hocc]
    norm_num
  · have htq : t < q := lt_of_not_ge hqt
    by_cases htu : t < u
    · by_cases htv : t < v
      · have h1 : positivePart (q - t) = q - t := positivePart_of_nonneg (by linarith [hqu, hqv])
        have h2 : positivePart (u - t) = u - t := positivePart_of_nonneg (sub_nonneg.mpr (le_of_lt htu))
        have h3 : positivePart (v - t) = v - t := positivePart_of_nonneg (sub_nonneg.mpr (le_of_lt htv))
        rw [h1, h2, h3]
        rw [mul_sub, hqeq]
        nlinarith [hocc_le_d]
      · have htv' : v ≤ t := le_of_not_gt htv
        have h1 : positivePart (q - t) = q - t := positivePart_of_nonneg (by linarith [hqu, hqv])
        have h2 : positivePart (u - t) = u - t := positivePart_of_nonneg (sub_nonneg.mpr (le_of_lt htu))
        have h3 : positivePart (v - t) = 0 := positivePart_of_nonpos (sub_nonpos.mpr htv')
        by_cases hlamz : lam = 0
        · have hconst : v = u := by
            have h := q_above_graph hxi hgamma hlam0 hlam ha hb
            have hΔ := hDelta
            simp [hlamz] at hΔ
            linarith
          exfalso
          linarith
        · have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hlamz)
          let c := eta - (t - v) / lam
          have hsub := endpoint_right_subset hlampos hxi.le hgamma rfl htv'
          have hce : xi ≤ c := by
            have hΔ := hDelta
            have hbound : t - v ≤ lam * d := by
              calc
                t - v ≤ u - v := sub_le_sub_right (le_of_lt htu) _
                _ ≤ |u - v| := le_abs_self _
                _ ≤ lam * d := by simpa [u, v, d, abs_sub_comm] using hΔ
            have hdiv : (t - v) / lam ≤ d :=
              (div_le_iff₀ hlampos).2 (by nlinarith [hbound])
            dsimp [c]
            linarith
          have hocc : graphOccupation gamma xi eta t ≤ d - (t - v) / lam := by
            simpa [c, d, v, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              graph_occupation_le_interval hxi.le hgamma_cont hsub hce
          have hcoef : b * (t - v) ≤ (t - v) / lam := by
            have hbcoef : b * lam ≤ 1 := by
              have := mul_le_mul_of_nonneg_right hb.2 hlam0
              nlinarith [hlam]
            apply (le_div_iff₀ hlampos).2
            have := mul_le_mul_of_nonneg_right hbcoef (sub_nonneg.mpr htv')
            nlinarith
          rw [h1, h2, h3]
          rw [mul_sub, hqeq]
          nlinarith [hocc, hcoef]
    · have htu' : u ≤ t := le_of_not_gt htu
      by_cases htv : t < v
      · have h1 : positivePart (q - t) = q - t := positivePart_of_nonneg (by linarith [hqu, hqv])
        have h2 : positivePart (u - t) = 0 := positivePart_of_nonpos (sub_nonpos.mpr htu')
        have h3 : positivePart (v - t) = v - t := positivePart_of_nonneg (sub_nonneg.mpr (le_of_lt htv))
        by_cases hlamz : lam = 0
        · have hconst : v = u := by
            have hΔ := hDelta
            simp [hlamz] at hΔ
            linarith
          exfalso
          linarith
        · have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hlamz)
          let c := xi + (t - u) / lam
          have hsub := endpoint_left_subset hlampos hxi.le hgamma rfl htu'
          have hce : c ≤ eta := by
            have hΔ := hgamma xi eta
            have hbound : t - u ≤ lam * d := by
              calc
                t - u ≤ v - u := sub_le_sub_right (le_of_lt htv) _
                _ ≤ |v - u| := le_abs_self _
                _ ≤ lam * d := by simpa [u, v, d, abs_sub_comm] using hDelta
            have hdiv : (t - u) / lam ≤ d :=
              (div_le_iff₀ hlampos).2 (by nlinarith [hbound])
            dsimp [c]
            linarith
          have hocc : graphOccupation gamma xi eta t ≤ d - (t - u) / lam := by
            simpa [c, d, u, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              graph_occupation_le_interval hxi.le hgamma_cont hsub hce
          have hcoef : a * (t - u) ≤ (t - u) / lam := by
            have hacoef : a * lam ≤ 1 := by
              have := mul_le_mul_of_nonneg_right ha.2 hlam0
              nlinarith [hlam]
            apply (le_div_iff₀ hlampos).2
            have := mul_le_mul_of_nonneg_right hacoef (sub_nonneg.mpr htu')
            nlinarith
          rw [h1, h2, h3]
          rw [mul_sub, hqeq]
          nlinarith [hocc, hcoef]
      · have htv' : v ≤ t := le_of_not_gt htv
        have h1 : positivePart (q - t) = q - t := positivePart_of_nonneg (by linarith [htq])
        have h2 : positivePart (u - t) = 0 := positivePart_of_nonpos (sub_nonpos.mpr htu')
        have h3 : positivePart (v - t) = 0 := positivePart_of_nonpos (sub_nonpos.mpr htv')
        by_cases hlamz : lam = 0
        · have hconst : ∀ x ∈ Icc xi eta, gamma x = u := by
            intro x hx
            have h := hgamma xi x
            have hz : |gamma x - gamma xi| = 0 := by
              apply le_antisymm
              · simpa [hlamz] using h
              · exact abs_nonneg _
            have heq : gamma x = gamma xi := sub_eq_zero.mp (abs_eq_zero.mp hz)
            simpa [u] using heq
          have hocc : graphOccupation gamma xi eta t = 0 ∨
              graphOccupation gamma xi eta t = d := by
            by_cases htu' : u < t
            · left
              have hempty : graphSuperlevel gamma xi eta t = ∅ := by
                ext x
                constructor
                · intro hx
                  have heq := hconst x ⟨hx.1.1.le, hx.1.2⟩
                  have htx : t ≤ gamma x := hx.2
                  exfalso
                  rw [heq] at htx
                  linarith
                · simp
              rw [graphOccupation_eq_measure hxi.le hgamma_cont, hempty]
              simp
            · right
              have hut0 : t = u := by linarith [htu']
              rw [graphOccupation_eq_measure hxi.le hgamma_cont]
              have hset : graphSuperlevel gamma xi eta t = Ioc xi eta := by
                ext x
                constructor
                · exact (·.1)
                · intro hx
                  have heq := hconst x ⟨hx.1.le, hx.2⟩
                  exact ⟨hx, by
                    change t ≤ gamma x
                    rw [hut0, heq]⟩
              rw [hset]
              simp [Measure.real, Real.volume_Ioc, d]
              exact hxi.le
          have htu_eq : graphOccupation gamma xi eta t = d → t = u := by
            intro hoccD
            by_contra hne
            have hstrict : u < t := lt_of_le_of_ne htu' (Ne.symm hne)
            have hempty : graphSuperlevel gamma xi eta t = ∅ := by
              ext x
              constructor
              · intro hx
                have heq := hconst x ⟨hx.1.1.le, hx.1.2⟩
                have htx : t ≤ gamma x := hx.2
                exfalso
                rw [heq] at htx
                linarith
              · simp
            have hzero : graphOccupation gamma xi eta t = 0 := by
              rw [graphOccupation_eq_measure hxi.le hgamma_cont, hempty]
              simp
            linarith [hoccD, hzero, hd]
          rcases hocc with hocc | hocc
          · rw [h1, h2, h3, hocc]
            have hqtpos : 0 < q - t := sub_pos.mpr htq
            simpa using mul_nonneg hD.le hqtpos.le
          · rw [h1, h2, h3, hocc]
            rw [mul_sub, hqeq]
            have hut0 := htu_eq hocc
            have hv_eq : v = u := by
              simpa [v] using hconst eta ⟨hxi.le, le_rfl⟩
            rw [hv_eq, hut0]
            dsimp [D]
            ring_nf
            exact le_rfl
        · have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hlamz)
          by_cases hempty : graphSuperlevel gamma xi eta t = ∅
          · have hocc : graphOccupation gamma xi eta t = 0 := by
              rw [graphOccupation_eq_measure hxi.le hgamma_cont, hempty]
              simp
            rw [h1, h2, h3, hocc]
            have hqtpos : 0 < q - t := sub_pos.mpr htq
            simpa using mul_nonneg hD.le hqtpos.le
          · have hne : (graphSuperlevel gamma xi eta t).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
            obtain ⟨x, hx⟩ := hne
            let c₁ := xi + (t - u) / lam
            let c₂ := eta - (t - v) / lam
            have hleft : graphSuperlevel gamma xi eta t ⊆ Icc c₁ eta := by
              simpa [c₁, u] using endpoint_left_subset hlampos hxi.le hgamma rfl htu'
            have hright : graphSuperlevel gamma xi eta t ⊆ Icc xi c₂ := by
              simpa [c₂, v] using endpoint_right_subset hlampos hxi.le hgamma rfl htv'
            have hsub : graphSuperlevel gamma xi eta t ⊆ Icc c₁ c₂ := by
              intro y hy
              exact ⟨(hleft hy).1, (hright hy).2⟩
            have hc : c₁ ≤ c₂ := le_trans (hleft hx).1 (hright hx).2
            have hocc : graphOccupation gamma xi eta t ≤ c₂ - c₁ := by
              simpa [c₁, c₂, d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                graph_occupation_le_interval hxi.le hgamma_cont hsub hc
            have hcoef1 : a * (t - u) ≤ (t - u) / lam := by
              have hacoef : a * lam ≤ 1 := by
                have := mul_le_mul_of_nonneg_right ha.2 hlam0
                nlinarith [hlam]
              apply (le_div_iff₀ hlampos).2
              have := mul_le_mul_of_nonneg_right hacoef (sub_nonneg.mpr htu')
              nlinarith
            have hcoef2 : b * (t - v) ≤ (t - v) / lam := by
              have hbcoef : b * lam ≤ 1 := by
                have := mul_le_mul_of_nonneg_right hb.2 hlam0
                nlinarith [hlam]
              apply (le_div_iff₀ hlampos).2
              have := mul_le_mul_of_nonneg_right hbcoef (sub_nonneg.mpr htv')
              nlinarith
            rw [h1, h2, h3]
            rw [mul_sub, hqeq]
            nlinarith [hocc, hcoef1, hcoef2]

/-! ## Quadratic identity and explicit coercive constants -/

noncomputable def quadraticLowerConstant' (lam : ℝ) : ℝ := quadraticLowerConstant lam

noncomputable def quadraticUpperConstant (lam : ℝ) : ℝ :=
  (1 + lam) * (1 + 2 * lam) / 2 + lam / 2

theorem quadraticLowerConstant'_pos {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8) :
    0 < quadraticLowerConstant' lam := by
  exact quadraticLowerConstant_pos hlam0 hlam

theorem quadraticGauge_eq_affine_plus_area
    {xi eta a b : ℝ} (hxi : xi < eta) (hD : a + b ≠ 0)
    {gamma : ℝ → ℝ} (hgamma : Continuous gamma) :
    quadraticCost gamma xi eta a b =
      ((eta - xi - a * (gamma eta - gamma xi)) *
          (eta - xi + b * (gamma eta - gamma xi))) / (2 * (a + b)) +
        ∫ x in xi..eta, (chord xi eta (gamma xi) (gamma eta) x - gamma x) := by
  let d := eta - xi
  let Δ := gamma eta - gamma xi
  have hd : 0 < d := sub_pos.mpr hxi
  have hchord : ∫ x in xi..eta, chord xi eta (gamma xi) (gamma eta) x =
      d * (gamma xi + gamma eta) / 2 := by
    have hden : eta - xi ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxi)
    have hxi_const : IntervalIntegrable (fun _ : ℝ => xi) volume xi eta :=
      intervalIntegrable_const
    have hconst : IntervalIntegrable (fun _ : ℝ => gamma xi) volume xi eta :=
      intervalIntegrable_const
    have hid : IntervalIntegrable (fun x : ℝ => x) volume xi eta :=
      continuousOn_id.intervalIntegrable
    have hsub : IntervalIntegrable (fun x : ℝ => x - xi) volume xi eta :=
      hid.sub hxi_const
    have hlin : IntervalIntegrable
        (fun x => ((gamma eta - gamma xi) / (eta - xi)) * (x - xi)) volume xi eta :=
      hsub.const_mul _
    dsimp [chord]
    have hfun : (fun x : ℝ => (gamma eta - gamma xi) * (x - xi) / (eta - xi)) =
        (fun x => ((gamma eta - gamma xi) / (eta - xi)) * (x - xi)) := by
      funext x
      field_simp [hden]
    change (∫ x in xi..eta, gamma xi +
      (gamma eta - gamma xi) * (x - xi) / (eta - xi)) = _
    have hrewrite :
        (∫ x in xi..eta, gamma xi +
            (gamma eta - gamma xi) * (x - xi) / (eta - xi)) =
          ∫ x in xi..eta, gamma xi +
            ((gamma eta - gamma xi) / (eta - xi)) * (x - xi) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change gamma xi + (gamma eta - gamma xi) * (x - xi) / (eta - xi) =
        gamma xi + (gamma eta - gamma xi) / (eta - xi) * (x - xi)
      rw [congrFun hfun x]
    rw [hrewrite]
    rw [intervalIntegral.integral_add hconst hlin]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub hid hxi_const]
    rw [integral_id, intervalIntegral.integral_const]
    dsimp [d]
    field_simp [hD, hden]
    ring
  unfold quadraticCost gaugedFourPointCost
  dsimp [fourPointQuotient, fourPointGap, fourPointSourceValue,
    fourPointTargetValue, fourPointDenominator]
  have hchord_int : IntervalIntegrable
      (fun x => chord xi eta (gamma xi) (gamma eta) x) volume xi eta := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxi.le]
    dsimp [chord]
    fun_prop
  have hgamma_int : IntervalIntegrable (fun x => gamma x) volume xi eta :=
    hgamma.intervalIntegrable xi eta
  rw [intervalIntegral.integral_sub hchord_int hgamma_int, hchord]
  field_simp [hD, hd.ne']
  ring

private lemma chord_deviation_abs_le
    {lam xi eta : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam)
    (x : ℝ) (hx : x ∈ Icc xi eta) :
    |chord xi eta (gamma xi) (gamma eta) x - gamma x| ≤ lam * (eta - xi) / 2 := by
  let d := eta - xi
  let s := x - xi
  let r := eta - x
  have hd : 0 < d := sub_pos.mpr hxi
  have hs : 0 ≤ s := sub_nonneg.mpr hx.1
  have hr : 0 ≤ r := sub_nonneg.mpr hx.2
  have hsu : |gamma x - gamma xi| ≤ lam * s := by
    calc
      |gamma x - gamma xi| ≤ lam * |x - xi| := hgamma xi x
      _ = lam * s := by rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have hrv : |gamma x - gamma eta| ≤ lam * r := by
    calc
      |gamma x - gamma eta| ≤ lam * |x - eta| := hgamma eta x
      _ = lam * r := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
        ring
  have hdecomp : chord xi eta (gamma xi) (gamma eta) x - gamma x =
      (r / d) * (gamma xi - gamma x) + (s / d) * (gamma eta - gamma x) := by
    have hden : eta - xi ≠ 0 := (sub_pos.mpr hxi).ne'
    dsimp [chord, d, s, r]
    field_simp [hden]
    ring
  have hmain : |chord xi eta (gamma xi) (gamma eta) x - gamma x| ≤
      2 * lam * s * r / d := by
    have hrd : 0 ≤ r / d := div_nonneg hr hd.le
    have hsd : 0 ≤ s / d := div_nonneg hs hd.le
    rw [hdecomp]
    calc
      |(r / d) * (gamma xi - gamma x) + (s / d) * (gamma eta - gamma x)| ≤
          |(r / d) * (gamma xi - gamma x)| + |(s / d) * (gamma eta - gamma x)| :=
        abs_add_le _ _
      _ = |r / d| * |gamma xi - gamma x| + |s / d| * |gamma eta - gamma x| := by
        rw [abs_mul, abs_mul]
      _ =
          (r / d) * |gamma xi - gamma x| + (s / d) * |gamma eta - gamma x| := by
            rw [abs_of_nonneg hrd, abs_of_nonneg hsd]
      _ ≤ (r / d) * (lam * s) + (s / d) * (lam * r) := by
        gcongr
        · simpa [abs_sub_comm] using hsu
        · simpa [abs_sub_comm] using hrv
      _ = 2 * lam * s * r / d := by field_simp [hd.ne']; ring
  have hsr : s * r ≤ d ^ 2 / 4 := by
    have hsquare := sq_nonneg (s - r)
    dsimp [d, s, r] at hsquare ⊢
    nlinarith
  have hmul : 2 * lam * s * r / d ≤ 2 * lam * (d ^ 2 / 4) / d := by
    apply (div_le_div_iff₀ hd hd).2
    have hscale : 0 ≤ 2 * lam := by positivity
    have hnum := mul_le_mul_of_nonneg_left hsr hscale
    nlinarith
  calc
    |chord xi eta (gamma xi) (gamma eta) x - gamma x| ≤ 2 * lam * s * r / d := hmain
    _ ≤ 2 * lam * (d ^ 2 / 4) / d := hmul
    _ = lam * d / 2 := by field_simp [hd.ne']; ring

theorem quadraticGauge_lower_bound
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma_cont : Continuous gamma) (hgamma : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤ quadraticCost gamma xi eta a b := by
  let d := eta - xi
  let Δ := gamma eta - gamma xi
  have hd : 0 < d := sub_pos.mpr hxi
  have hΔ : |Δ| ≤ lam * d := by
    dsimp [Δ, d]
    calc
      |gamma eta - gamma xi| ≤ lam * |eta - xi| := hgamma xi eta
      _ = lam * d := by rw [abs_of_nonneg (sub_nonneg.mpr hxi.le)]
  have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
  have harea := quadraticGauge_eq_affine_plus_area hxi hD hgamma_cont
  have hdevcont : ContinuousOn (fun x => chord xi eta (gamma xi) (gamma eta) x - gamma x)
      (Icc xi eta) := by
    dsimp [chord]
    fun_prop
  have harea_int : IntervalIntegrable
      (fun x => chord xi eta (gamma xi) (gamma eta) x - gamma x) volume xi eta :=
    by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hxi.le]
      exact hdevcont
  have harea_low : -(lam * d ^ 2 / 2) ≤
      ∫ x in xi..eta, (chord xi eta (gamma xi) (gamma eta) x - gamma x) := by
    have hlow : (∫ x in xi..eta, (-(lam * d / 2) : ℝ)) ≤
        ∫ x in xi..eta, (chord xi eta (gamma xi) (gamma eta) x - gamma x) := by
      apply intervalIntegral.integral_mono_on hxi.le intervalIntegrable_const harea_int
      intro x hx
      exact neg_le_of_abs_le (chord_deviation_abs_le hxi hgamma hlam0 x
        hx)
    calc
      -(lam * d ^ 2 / 2) = ∫ x in xi..eta, (-(lam * d / 2) : ℝ) := by
        rw [intervalIntegral.integral_const]
        dsimp [d]
        ring
      _ ≤ _ := hlow
  have h1 : (1 - lam) * d ≤ d - a * Δ := by
    have haΔ : a * Δ ≤ lam * d := by
      calc
        a * Δ ≤ a * |Δ| := mul_le_mul_of_nonneg_left (le_abs_self Δ) ha.1
        _ ≤ a * (lam * d) := mul_le_mul_of_nonneg_left hΔ ha.1
        _ ≤ lam * d := by
          simpa using mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hlam0 hd.le)
    calc
      (1 - lam) * d = d - lam * d := by ring
      _ ≤ d - a * Δ := sub_le_sub_left haΔ d
  have h2 : (1 - 2 * lam) * d ≤ d + b * Δ := by
    have hb0 : 0 ≤ b := le_trans (by norm_num) hb.1
    have hblam : 0 ≤ lam * d := mul_nonneg hlam0 hd.le
    have hbabs : b * |Δ| ≤ 2 * (lam * d) := by
      calc
        b * |Δ| ≤ b * (lam * d) := mul_le_mul_of_nonneg_left hΔ hb0
        _ ≤ 2 * (lam * d) := by
          exact mul_le_mul_of_nonneg_right hb.2 hblam
    have hbΔ : -2 * (lam * d) ≤ b * Δ := by
      calc
        -2 * (lam * d) ≤ -b * (lam * d) := by
          have h := mul_le_mul_of_nonneg_right hb.2 hblam
          nlinarith
        _ ≤ b * Δ := by
          have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hΔ) hb0
          nlinarith
    calc
      (1 - 2 * lam) * d = d - 2 * (lam * d) := by ring
      _ ≤ d + b * Δ := by nlinarith [hbΔ]
  have hprod : ((1 - lam) * d) * ((1 - 2 * lam) * d) ≤
      (d - a * Δ) * (d + b * Δ) := by
    have hp1 : 0 ≤ (1 - lam) * d := mul_nonneg (by linarith) hd.le
    have hp2 : 0 ≤ (1 - 2 * lam) * d := mul_nonneg (by linarith) hd.le
    have hq1 : 0 ≤ d - a * Δ := by nlinarith [h1]
    exact mul_le_mul h1 h2 hp2 hq1
  have hDlo : 1 ≤ a + b := by linarith [ha.1, hb.1]
  have hDhi : a + b ≤ 3 := by linarith [ha.2, hb.2]
  have hAffine : ((1 - lam) * (1 - 2 * lam) / 6) * d ^ 2 ≤
      ((d - a * Δ) * (d + b * Δ)) / (2 * (a + b)) := by
    have hden : 0 < 2 * (a + b) := by positivity
    apply (le_div_iff₀ hden).2
    have hleft : 0 ≤ (1 - lam) * (1 - 2 * lam) * d ^ 2 := by
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg d)
    have hprod' : (1 - lam) * (1 - 2 * lam) * d ^ 2 ≤
        (d - a * Δ) * (d + b * Δ) := by
      nlinarith [hprod]
    nlinarith [hprod', hDhi]
  rw [harea] at *
  dsimp [quadraticLowerConstant', quadraticLowerConstant, d] at *
  nlinarith

theorem quadraticGauge_upper_bound
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma_cont : Continuous gamma) (hgamma : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    quadraticCost gamma xi eta a b ≤ quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  let d := eta - xi
  let Δ := gamma eta - gamma xi
  have hd : 0 < d := sub_pos.mpr hxi
  have hΔ : |Δ| ≤ lam * d := by
    dsimp [Δ, d]
    calc
      |gamma eta - gamma xi| ≤ lam * |eta - xi| := hgamma xi eta
      _ = lam * d := by rw [abs_of_nonneg (sub_nonneg.mpr hxi.le)]
  have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
  have harea := quadraticGauge_eq_affine_plus_area hxi hD hgamma_cont
  have hdevcont : ContinuousOn (fun x => chord xi eta (gamma xi) (gamma eta) x - gamma x)
      (Icc xi eta) := by
    dsimp [chord]
    fun_prop
  have harea_int : IntervalIntegrable
      (fun x => chord xi eta (gamma xi) (gamma eta) x - gamma x) volume xi eta :=
    by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hxi.le]
      exact hdevcont
  have harea_up : ∫ x in xi..eta,
      (chord xi eta (gamma xi) (gamma eta) x - gamma x) ≤ lam * d ^ 2 / 2 := by
    have hup : (∫ x in xi..eta, (chord xi eta (gamma xi) (gamma eta) x - gamma x)) ≤
        ∫ x in xi..eta, (lam * d / 2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hxi.le harea_int intervalIntegrable_const
      intro x hx
      exact (le_abs_self _).trans (chord_deviation_abs_le hxi hgamma hlam0 x
        hx)
    calc
      _ ≤ ∫ x in xi..eta, (lam * d / 2 : ℝ) := hup
      _ = lam * d ^ 2 / 2 := by rw [intervalIntegral.integral_const]; dsimp [d]; ring
  have h1 : d - a * Δ ≤ (1 + lam) * d := by
    have hblam : 0 ≤ lam * d := mul_nonneg hlam0 hd.le
    have haΔlo : -(lam * d) ≤ a * Δ := by
      calc
        -(lam * d) ≤ -(a * (lam * d)) := by
          have h := mul_le_mul_of_nonneg_right ha.2 hblam
          nlinarith
        _ ≤ a * Δ := by
          have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hΔ) ha.1
          nlinarith
    have hneg : -(a * Δ) ≤ lam * d := by
      simpa using neg_le_neg haΔlo
    have haΔ : a * Δ ≤ lam * d := by
      calc
        a * Δ ≤ a * |Δ| := mul_le_mul_of_nonneg_left (le_abs_self Δ) ha.1
        _ ≤ a * (lam * d) := mul_le_mul_of_nonneg_left hΔ ha.1
        _ ≤ lam * d := by
          simpa using mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hlam0 hd.le)
    calc
      d - a * Δ = d + (-(a * Δ)) := by ring
      _ ≤ d + lam * d := by
        simpa [add_comm] using add_le_add_left hneg d
      _ = (1 + lam) * d := by ring
  have h2 : d + b * Δ ≤ (1 + 2 * lam) * d := by
    have hb0 : 0 ≤ b := le_trans (by norm_num) hb.1
    have hblam : 0 ≤ lam * d := mul_nonneg hlam0 hd.le
    have hbabs : b * |Δ| ≤ 2 * (lam * d) := by
      calc
        b * |Δ| ≤ b * (lam * d) := mul_le_mul_of_nonneg_left hΔ hb0
        _ ≤ 2 * (lam * d) := by
          exact mul_le_mul_of_nonneg_right hb.2 hblam
    have hbΔ : b * Δ ≤ 2 * (lam * d) := by
      calc
        b * Δ ≤ b * |Δ| := mul_le_mul_of_nonneg_left (le_abs_self Δ) hb0
        _ ≤ 2 * (lam * d) := hbabs
    calc
      d + b * Δ ≤ d + 2 * (lam * d) := by
        simpa [add_comm] using add_le_add_left hbΔ d
      _ = (1 + 2 * lam) * d := by ring
  have hprod : (d - a * Δ) * (d + b * Δ) ≤
      ((1 + lam) * d) * ((1 + 2 * lam) * d) := by
    have hp1 : 0 ≤ d - a * Δ := by
      have haΔ : a * Δ ≤ lam * d := by
        calc
          a * Δ ≤ a * |Δ| := mul_le_mul_of_nonneg_left (le_abs_self Δ) ha.1
          _ ≤ a * (lam * d) := mul_le_mul_of_nonneg_left hΔ ha.1
          _ ≤ lam * d := by
            simpa using mul_le_mul_of_nonneg_right ha.2 (mul_nonneg hlam0 hd.le)
      nlinarith [haΔ, hlam0, hd]
    have hq2 : 0 ≤ d + b * Δ := by
      have hbΔ : -2 * (lam * d) ≤ b * Δ := by
        calc
          -2 * (lam * d) ≤ -b * (lam * d) := by
            have h := mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hlam0 hd.le)
            nlinarith
          _ ≤ b * Δ := by
            have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hΔ) (le_trans (by norm_num) hb.1)
            nlinarith
      nlinarith [hbΔ, hlam0, hd]
    have hp2 : 0 ≤ (1 + 2 * lam) * d := mul_nonneg (by linarith) hd.le
    have hright : 0 ≤ (1 + lam) * d := mul_nonneg (by linarith) hd.le
    exact mul_le_mul h1 h2 hq2 hright
  have hDlo : 1 ≤ a + b := by linarith [ha.1, hb.1]
  have hAffine : ((d - a * Δ) * (d + b * Δ)) / (2 * (a + b)) ≤
      ((1 + lam) * (1 + 2 * lam) / 2) * d ^ 2 := by
    have hden : 0 < 2 * (a + b) := by positivity
    apply (div_le_iff₀ hden).2
    have hright : 0 ≤ (1 + lam) * (1 + 2 * lam) * d ^ 2 := by positivity
    nlinarith [hprod, hDlo]
  rw [harea] at *
  dsimp [quadraticUpperConstant, d] at *
  nlinarith

end OTSelector
