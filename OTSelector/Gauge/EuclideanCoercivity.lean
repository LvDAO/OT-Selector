import OTSelector.Gauge.PeanoHinge
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Euclidean four-point coercivity

This module specializes the Peano--hinge representation to
`L(x) = sqrt (1+x^2) - 1`.  It first proves the analytic derivative identities, then compares
the Euclidean and quadratic hinge integrals on the strip `|x| <= 1`.
-/

open Set MeasureTheory
open scoped Interval

namespace OTSelector

/-- The scalar residual obtained after removing the permutation-invariant horizontal length. -/
noncomputable def euclideanResidual (x : ℝ) : ℝ :=
  Real.sqrt (1 + x ^ 2) - 1

/-- First derivative of the Euclidean residual. -/
noncomputable def euclideanResidualDeriv (x : ℝ) : ℝ :=
  x / Real.sqrt (1 + x ^ 2)

/-- Second derivative of the Euclidean residual. -/
noncomputable def euclideanResidualSecond (x : ℝ) : ℝ :=
  1 / Real.sqrt (1 + x ^ 2) ^ 3

/-- The lower curvature bound on `[-1,1]`; this equals `2^(-3/2)`. -/
noncomputable def euclideanCurvatureLower : ℝ :=
  1 / (2 * Real.sqrt 2)

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

theorem euclideanResidual_hasDerivAt (x : ℝ) :
    HasDerivAt euclideanResidual (euclideanResidualDeriv x) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_add 1 using 1
    · rfl
    · rfl
    · funext y
      simp [pow_two, id_eq]
    · simp [id_eq]
      ring
  have hsqrt := hinner.sqrt (ne_of_gt (one_add_sq_pos x))
  have h := hsqrt.sub_const 1
  change HasDerivAt euclideanResidual _ x at h
  have hcoeff : 2 * x / (2 * Real.sqrt (1 + x ^ 2)) =
      x / Real.sqrt (1 + x ^ 2) := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 (one_add_sq_pos x))]
  exact h.congr_deriv (by simpa [euclideanResidualDeriv] using hcoeff)

theorem euclideanResidualDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt euclideanResidualDeriv (euclideanResidualSecond x) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_add 1 using 1
    · rfl
    · rfl
    · funext y
      simp [pow_two, id_eq]
    · simp [id_eq]
      ring
  have hsqrt := hinner.sqrt (ne_of_gt (one_add_sq_pos x))
  have hrootpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (one_add_sq_pos x)
  have h := (hasDerivAt_id x).div hsqrt hrootpos.ne'
  change HasDerivAt euclideanResidualDeriv _ x at h
  have hsquare : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := by
    exact Real.sq_sqrt (one_add_sq_pos x).le
  have hcoeff :
      (1 * Real.sqrt (1 + x ^ 2) -
          x * (2 * x / (2 * Real.sqrt (1 + x ^ 2)))) /
          Real.sqrt (1 + x ^ 2) ^ 2 =
        1 / Real.sqrt (1 + x ^ 2) ^ 3 := by
    field_simp [hrootpos.ne']
    nlinarith
  exact h.congr_deriv (by simpa [euclideanResidualSecond, id_eq] using hcoeff)

theorem euclideanResidualDeriv_continuous : Continuous euclideanResidualDeriv := by
  exact continuous_iff_continuousAt.mpr fun x ↦
    (euclideanResidualDeriv_hasDerivAt x).continuousAt

theorem euclideanResidualSecond_continuous : Continuous euclideanResidualSecond := by
  unfold euclideanResidualSecond
  apply continuous_const.div
  · fun_prop
  · intro x
    positivity

theorem euclideanCurvatureLower_pos : 0 < euclideanCurvatureLower := by
  unfold euclideanCurvatureLower
  positivity

theorem euclideanResidualSecond_pos (x : ℝ) : 0 < euclideanResidualSecond x := by
  unfold euclideanResidualSecond
  positivity

theorem euclideanResidualSecond_le_one (x : ℝ) : euclideanResidualSecond x ≤ 1 := by
  have hroot : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg x]
  have hpow : 1 ≤ Real.sqrt (1 + x ^ 2) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hroot 3
  rw [euclideanResidualSecond, one_div]
  exact inv_le_one₀ (by positivity) |>.2 hpow

theorem euclideanCurvatureLower_le_second {x : ℝ} (hx : |x| ≤ 1) :
    euclideanCurvatureLower ≤ euclideanResidualSecond x := by
  have hxsq : x ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa [sq_abs] using h
  have hsqrt : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt 2 := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
  have htwo : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hpow : Real.sqrt (1 + x ^ 2) ^ 3 ≤ (Real.sqrt 2) ^ 3 := by
    exact pow_le_pow_left₀ hsqrt0 hsqrt 3
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt (1 + x ^ 2) ^ 3 ≤ 2 * Real.sqrt 2 := by
    calc
      _ ≤ Real.sqrt 2 ^ 3 := hpow
      _ = 2 * Real.sqrt 2 := by rw [show Real.sqrt 2 ^ 3 =
          Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsqrt2]
  have hdenpos : 0 < Real.sqrt (1 + x ^ 2) ^ 3 := by positivity
  have hcapos : 0 < 2 * Real.sqrt 2 := by positivity
  unfold euclideanCurvatureLower euclideanResidualSecond
  exact one_div_le_one_div_of_le hdenpos hden

/-- The Euclidean four-point gauged cost. -/
noncomputable def euclideanGaugedCost (gamma : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  gaugedFourPointCost euclideanResidual euclideanResidualDeriv gamma xi eta a b

/-- Peano--hinge representation of the Euclidean gauged cost on the normalized strip. -/
theorem euclideanGaugedCost_eq_hinge_integral
    {xi eta a b : ℝ} (hxi : xi ≤ eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanGaugedCost gamma xi eta a b =
      ∫ t in (-1 : ℝ)..1, euclideanResidualSecond t *
        hingeKernel gamma xi eta a b t := by
  apply gaugedFourPointCost_eq_hinge_integral (hAB := by norm_num) hxi hgamma hrange
  · intro y hy
    exact euclideanResidual_hasDerivAt y
  · intro y hy
    exact euclideanResidualDeriv_hasDerivAt y
  · exact euclideanResidualDeriv_continuous.continuousOn
  · exact euclideanResidualSecond_continuous.continuousOn
  · exact hq
  · exact ha
  · exact hb

/-- On the normalized strip, the Euclidean hinge integral lies between the lower-curvature
multiple of the quadratic integral and the quadratic integral itself. -/
theorem euclideanGaugedCost_compare_quadratic
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hgammaLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanCurvatureLower * quadraticCost gamma xi eta a b ≤
        euclideanGaugedCost gamma xi eta a b ∧
      euclideanGaugedCost gamma xi eta a b ≤ quadraticCost gamma xi eta a b := by
  let H : ℝ → ℝ := hingeKernel gamma xi eta a b
  have hH : IntervalIntegrable H volume (-1 : ℝ) 1 :=
    hingeKernel_intervalIntegrable (by norm_num) hxi.le hgamma hrange
  have hEH : IntervalIntegrable (fun t ↦ euclideanResidualSecond t * H t)
      volume (-1 : ℝ) 1 :=
    hH.continuousOn_mul euclideanResidualSecond_continuous.continuousOn
  have hcH : IntervalIntegrable (fun t ↦ euclideanCurvatureLower * H t)
      volume (-1 : ℝ) 1 := hH.const_mul _
  have hHnonneg : ∀ t, 0 ≤ H t :=
    hingeKernel_nonneg hxi hgamma hgammaLip hlam0 hlam ha hb
  have hlow : (∫ t in (-1 : ℝ)..1, euclideanCurvatureLower * H t) ≤
      ∫ t in (-1 : ℝ)..1, euclideanResidualSecond t * H t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hcH hEH
    intro t ht
    exact mul_le_mul_of_nonneg_right
      (euclideanCurvatureLower_le_second (abs_le.mpr ht)) (hHnonneg t)
  have hupp : (∫ t in (-1 : ℝ)..1, euclideanResidualSecond t * H t) ≤
      ∫ t in (-1 : ℝ)..1, H t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hEH hH
    intro t ht
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (euclideanResidualSecond_le_one t) (hHnonneg t)
  have hE := euclideanGaugedCost_eq_hinge_integral hxi.le hgamma hrange hq ha hb
  have hQ := quadraticCost_eq_hinge_integral (by norm_num) hxi.le hgamma hrange hq ha hb
  constructor
  · rw [hE, hQ, ← intervalIntegral.integral_const_mul]
    exact hlow
  · rw [hE, hQ]
    exact hupp

/-- Forward-order Euclidean coercive lower bound `(2.13)`. -/
theorem euclideanGauge_lower_bound_forward
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hgammaLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanCurvatureLower * quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤
      euclideanGaugedCost gamma xi eta a b := by
  have hQ := quadraticGauge_lower_bound hxi hgamma hgammaLip hlam0 hlam ha hb
  have hcomp := (euclideanGaugedCost_compare_quadratic hxi hgamma hgammaLip hlam0
    (hlam.trans (by norm_num)) hrange hq ha hb).1
  have hc : 0 ≤ euclideanCurvatureLower := euclideanCurvatureLower_pos.le
  calc
    euclideanCurvatureLower * quadraticLowerConstant' lam * (eta - xi) ^ 2 =
        euclideanCurvatureLower *
          (quadraticLowerConstant' lam * (eta - xi) ^ 2) := by ring
    _ ≤ euclideanCurvatureLower * quadraticCost gamma xi eta a b :=
      mul_le_mul_of_nonneg_left hQ hc
    _ ≤ euclideanGaugedCost gamma xi eta a b := hcomp

/-- Forward-order Euclidean coercive upper bound `(2.13)`. -/
theorem euclideanGauge_upper_bound_forward
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hgammaLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanGaugedCost gamma xi eta a b ≤
      quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  exact (euclideanGaugedCost_compare_quadratic hxi hgamma hgammaLip hlam0
    (hlam.trans (by norm_num)) hrange hq ha hb).2.trans
      (quadraticGauge_upper_bound hxi hgamma hgammaLip hlam0 hlam ha hb)

/-! ## Reverse endpoint order -/

/-- Reflection used for an edge whose target coordinate precedes its source coordinate. -/
def reflectedGraph (gamma : ℝ → ℝ) (x : ℝ) : ℝ :=
  -gamma (-x)

theorem reflectedGraph_continuous {gamma : ℝ → ℝ} (hgamma : Continuous gamma) :
    Continuous (reflectedGraph gamma) := by
  unfold reflectedGraph
  fun_prop

theorem reflectedGraph_lipschitz {lam : ℝ} {gamma : ℝ → ℝ}
    (hgamma : ScalarLipschitz lam gamma) :
    ScalarLipschitz lam (reflectedGraph gamma) := by
  intro x y
  unfold reflectedGraph
  convert hgamma (-y) (-x) using 1 <;> congr 1 <;> ring_nf

@[simp] theorem euclideanResidual_neg (x : ℝ) :
    euclideanResidual (-x) = euclideanResidual x := by
  simp [euclideanResidual]

@[simp] theorem euclideanResidualDeriv_neg (x : ℝ) :
    euclideanResidualDeriv (-x) = -euclideanResidualDeriv x := by
  simp only [euclideanResidualDeriv, neg_sq]
  ring

theorem fourPointQuotient_reflectedGraph
    (gamma : ℝ → ℝ) (xi eta a b : ℝ) :
    fourPointQuotient (reflectedGraph gamma) (-xi) (-eta) a b =
      -fourPointQuotient gamma xi eta a b := by
  unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
    fourPointDenominator reflectedGraph
  ring_nf

/-- The reflected forward-order gauged Euclidean functional equals the original reverse-order
functional. -/
theorem euclideanGaugedCost_reflected
    (gamma : ℝ → ℝ) (xi eta a b : ℝ) :
    euclideanGaugedCost (reflectedGraph gamma) (-xi) (-eta) a b =
      euclideanGaugedCost gamma xi eta a b := by
  have hint : (∫ x in -xi..-eta,
      euclideanResidualDeriv (reflectedGraph gamma x)) =
        ∫ x in xi..eta, euclideanResidualDeriv (gamma x) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun y : ℝ ↦ euclideanResidualDeriv (-gamma y))
      (a := -xi) (b := -eta)
    have hleft : (fun x : ℝ ↦ euclideanResidualDeriv (-gamma (-x))) =
        (fun x ↦ euclideanResidualDeriv (reflectedGraph gamma x)) := by
      funext x
      rfl
    rw [hleft] at hcomp
    have hodd : (fun y : ℝ ↦ euclideanResidualDeriv (-gamma y)) =
        (fun y ↦ -euclideanResidualDeriv (gamma y)) := by
      funext y
      exact euclideanResidualDeriv_neg (gamma y)
    rw [hodd, intervalIntegral.integral_neg] at hcomp
    calc
      (∫ x in -xi..-eta, euclideanResidualDeriv (reflectedGraph gamma x)) =
          -(∫ x in eta..xi, euclideanResidualDeriv (gamma x)) := by
            simpa only [neg_neg] using hcomp
      _ = ∫ x in xi..eta, euclideanResidualDeriv (gamma x) :=
        (intervalIntegral.integral_symm eta xi).symm
  unfold euclideanGaugedCost gaugedFourPointCost
  dsimp only
  rw [fourPointQuotient_reflectedGraph, euclideanResidual_neg]
  simp only [fourPointDenominator, fourPointSourceValue, fourPointTargetValue,
    reflectedGraph, euclideanResidual_neg]
  simp only [neg_neg]
  change (a + b) * euclideanResidual (fourPointQuotient gamma xi eta a b) -
      a * euclideanResidual (gamma xi) - b * euclideanResidual (gamma eta) -
        (∫ x in -xi..-eta, euclideanResidualDeriv (reflectedGraph gamma x)) = _
  rw [hint]

theorem reflectedGraph_range
    {xi eta : ℝ} {gamma : ℝ → ℝ}
    (hrange : ∀ x ∈ Icc eta xi, gamma x ∈ Icc (-1 : ℝ) 1) :
    ∀ x ∈ Icc (-xi) (-eta), reflectedGraph gamma x ∈ Icc (-1 : ℝ) 1 := by
  intro x hx
  have hmx : -x ∈ Icc eta xi := by constructor <;> linarith [hx.1, hx.2]
  have hg := hrange (-x) hmx
  unfold reflectedGraph
  constructor <;> linarith [hg.1, hg.2]

theorem reflectedGraph_quotient_range
    {xi eta a b : ℝ} {gamma : ℝ → ℝ}
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1) :
    fourPointQuotient (reflectedGraph gamma) (-xi) (-eta) a b ∈ Icc (-1 : ℝ) 1 := by
  rw [fourPointQuotient_reflectedGraph]
  constructor <;> linarith [hq.1, hq.2]

/-- Reverse-order Euclidean coercive lower bound. -/
theorem euclideanGauge_lower_bound_reverse
    {lam xi eta a b : ℝ} (hxi : eta < xi) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hgammaLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ Icc eta xi, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanCurvatureLower * quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤
      euclideanGaugedCost gamma xi eta a b := by
  have href := euclideanGauge_lower_bound_forward (show -xi < -eta by linarith)
    (reflectedGraph_continuous hgamma) (reflectedGraph_lipschitz hgammaLip)
    hlam0 hlam (reflectedGraph_range hrange) (reflectedGraph_quotient_range hq) ha hb
  rw [euclideanGaugedCost_reflected] at href
  nlinarith [href]

/-- Reverse-order Euclidean coercive upper bound. -/
theorem euclideanGauge_upper_bound_reverse
    {lam xi eta a b : ℝ} (hxi : eta < xi) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hgammaLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ Icc eta xi, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanGaugedCost gamma xi eta a b ≤
      quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  have href := euclideanGauge_upper_bound_forward (show -xi < -eta by linarith)
    (reflectedGraph_continuous hgamma) (reflectedGraph_lipschitz hgammaLip)
    hlam0 hlam (reflectedGraph_range hrange) (reflectedGraph_quotient_range hq) ha hb
  rw [euclideanGaugedCost_reflected] at href
  nlinarith [href]

end OTSelector
