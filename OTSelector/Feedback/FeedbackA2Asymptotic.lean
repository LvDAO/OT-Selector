import OTSelector.Feedback.FeedbackA2HorizonRange
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotic parameter choice for the actual stopped A2 event

This file specializes the stopped-current A2 assembly to

* `eta = lam / (2 * (2 + lam))`,
* `B_n = amplitude * sqrt n`,
* `T_n = n - 2 * B_n`, truncated to `NNReal`, and
* `R_n = Nat.sqrt n`.

The only non-vanishing terms in the resulting probability bound are the prescribed global-cut
and endpoint constants.  All numerical hypotheses and the cubic stopped-current remainder are
discharged here, rather than exposed as asymptotic assumptions.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace OTSelector

open FiniteSample RelativeVC

/-! ## The deterministic parameter sequence -/

/-- A fixed positive A1 tolerance satisfying `eta * (2 + lam) <= lam`. -/
noncomputable def feedbackA2AsymptoticEta (lam : ℝ) : ℝ :=
  lam / (2 * (2 + lam))

/-- The square-root endpoint buffer used by the stopped A2 argument. -/
noncomputable def feedbackA2AsymptoticBuffer (amplitude : ℝ) (n : ℕ) : ℝ :=
  endpointBuffer amplitude n

/-- The bulk horizon `n - 2 B_n`, truncated only for the finitely many rows where it is negative. -/
noncomputable def feedbackA2AsymptoticHorizon (amplitude : ℝ) (n : ℕ) : ℝ≥0 :=
  Real.toNNReal ((n : ℝ) - 2 * feedbackA2AsymptoticBuffer amplitude n)

/-- Integer stopped-current excursion radius on the square-root scale. -/
def feedbackA2AsymptoticRadius (n : ℕ) : ℕ :=
  Nat.sqrt n

/-- The two cubic stopped-current terms in the explicit A2 probability bound. -/
noncomputable def feedbackA2AsymptoticCubicRemainder
    (lam amplitude : ℝ) (n : ℕ) : ℝ :=
  (2 * feedbackA2AsymptoticBuffer amplitude n +
        5 * feedbackA2AsymptoticBuffer amplitude n *
          Real.sqrt (feedbackA2AsymptoticBuffer amplitude n)) /
    (feedbackA2AsymptoticRadius n : ℝ) ^ 3 +
    3 * (((2 * feedbackA2AsymptoticBuffer amplitude n +
          5 * feedbackA2AsymptoticBuffer amplitude n *
            Real.sqrt (feedbackA2AsymptoticBuffer amplitude n)) +
        (6 + 81 / lam) * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) /
      (2 * lam)) / (feedbackA2AsymptoticRadius n : ℝ) ^ 3

/-- The full vanishing part of the explicit stopped A2 probability bound. -/
noncomputable def feedbackA2AsymptoticRemainder
    (lam amplitude : ℝ) (n : ℕ) : ℝ :=
  ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
    feedbackA2AsymptoticCubicRemainder lam amplitude n

/-- A convenient `1 / sqrt n` envelope coefficient for the cubic remainder. -/
noncomputable def feedbackA2AsymptoticCubicCoefficient
    (lam amplitude : ℝ) : ℝ :=
  56 * amplitude +
    (12 / lam) * (7 * amplitude + (6 + 81 / lam))

/-- The actual stopped A2 bad event under the asymptotic parameter sequence. -/
noncomputable def feedbackA2AsymptoticBadEvent
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (amplitude globalQ endpointQ : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  feedbackA2StoppedBadEvent
    hlam0.le (hlam.trans (by norm_num))
    (feedbackA2AsymptoticEta lam) amplitude globalQ endpointQ
    (feedbackA2AsymptoticBuffer amplitude n)
    (feedbackA2AsymptoticHorizon amplitude n)
    (feedbackA2AsymptoticRadius n)

/-- The complement of the actual asymptotic stopped A2 bad event. -/
noncomputable def feedbackA2AsymptoticGoodEvent
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (amplitude globalQ endpointQ : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  (feedbackA2AsymptoticBadEvent
    hlam0 hlam amplitude globalQ endpointQ n)ᶜ

theorem feedbackA2AsymptoticEta_pos
    {lam : ℝ} (hlam0 : 0 < lam) :
    0 < feedbackA2AsymptoticEta lam := by
  unfold feedbackA2AsymptoticEta
  positivity

theorem feedbackA2AsymptoticEta_small
    {lam : ℝ} (hlam0 : 0 < lam) :
    feedbackA2AsymptoticEta lam * (2 + lam) ≤ lam := by
  have hden : 0 < 2 + lam := by linarith
  unfold feedbackA2AsymptoticEta
  field_simp
  linarith

theorem feedbackA2AsymptoticBuffer_eq
    (amplitude : ℝ) (n : ℕ) :
    feedbackA2AsymptoticBuffer amplitude n = amplitude * Real.sqrt n := by
  rfl

theorem feedbackA2AsymptoticRadius_pos {n : ℕ} (hn : 0 < n) :
    0 < feedbackA2AsymptoticRadius n := by
  simpa [feedbackA2AsymptoticRadius] using (Nat.sqrt_pos.mpr hn)

theorem feedbackA2AsymptoticRadius_le_real_sqrt (n : ℕ) :
    (feedbackA2AsymptoticRadius n : ℝ) ≤ Real.sqrt n := by
  simpa [feedbackA2AsymptoticRadius] using
    (Real.nat_sqrt_le_real_sqrt (a := n))

theorem real_sqrt_lt_feedbackA2AsymptoticRadius_add_one (n : ℕ) :
    Real.sqrt n < (feedbackA2AsymptoticRadius n : ℝ) + 1 := by
  simpa [feedbackA2AsymptoticRadius] using
    (Real.real_sqrt_lt_nat_sqrt_succ (a := n))

/-! ## Eventual endpoint and horizon geometry -/

/-- The exact horizon identity and all elementary bulk geometry hold eventually. -/
theorem eventually_feedbackA2Asymptotic_horizon_geometry
    {amplitude : ℝ} (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      4 ≤ n ∧
        0 < feedbackA2AsymptoticBuffer amplitude n ∧
        feedbackA2AsymptoticBuffer amplitude n ≤ (n : ℝ) ∧
        feedbackA2AsymptoticBuffer amplitude n +
            (feedbackA2AsymptoticHorizon amplitude n : ℝ) =
          (n : ℝ) - feedbackA2AsymptoticBuffer amplitude n ∧
        (feedbackA2AsymptoticHorizon amplitude n : ℝ) ≤ (n : ℝ) ∧
        feedbackA2AsymptoticBuffer amplitude n / 8 ≤ (n : ℝ) := by
  let M : ℝ := max 2 (2 * amplitude)
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 4,
    hsqrt.eventually (eventually_ge_atTop M)] with n hn hnM
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt2 : 2 ≤ Real.sqrt (n : ℝ) := (le_max_left _ _).trans hnM
  have hcoef : 2 * amplitude ≤ Real.sqrt (n : ℝ) :=
    (le_max_right _ _).trans hnM
  have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = n :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have htwo : 2 * feedbackA2AsymptoticBuffer amplitude n ≤ (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hsqrt0
    rw [hsquare] at hmul
    rw [feedbackA2AsymptoticBuffer_eq]
    nlinarith
  have hBpos : 0 < feedbackA2AsymptoticBuffer amplitude n := by
    rw [feedbackA2AsymptoticBuffer_eq]
    exact mul_pos hamp (Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega)))
  have hTcoe : (feedbackA2AsymptoticHorizon amplitude n : ℝ) =
      (n : ℝ) - 2 * feedbackA2AsymptoticBuffer amplitude n := by
    rw [feedbackA2AsymptoticHorizon, Real.coe_toNNReal]
    linarith
  constructor
  · exact hn
  constructor
  · exact hBpos
  constructor
  · linarith
  constructor
  · rw [hTcoe]
    ring
  constructor
  · rw [hTcoe]
    linarith
  · linarith

/-! ## Eventual numerical hypotheses -/

/-- The elementary specialization of `log n = o(sqrt n)` used by both A1 inequalities. -/
private theorem eventually_log_nat_le_mul_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * Real.sqrt n := by
  have hLittle : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / (2 : ℝ))) :=
    (isLittleO_log_rpow_atTop (r := (1 / (2 : ℝ))) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop
  filter_upwards [hLittle.bound hc, eventually_ge_atTop 1] with n hn hn1
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] using hn

/-- Both VC-regularity survival inequalities hold for the chosen fixed positive `eta`. -/
theorem eventually_feedbackA2Asymptotic_regularity_inequalities
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      4 * (33280 : ℝ) ^ 2 * Real.log n ≤
          feedbackA2AsymptoticEta lam ^ 2 *
            (13 * feedbackA2AsymptoticBuffer amplitude n / 16) ∧
        2 * (33280 : ℝ) * Real.log n ≤
          feedbackA2AsymptoticEta lam *
            (13 * feedbackA2AsymptoticBuffer amplitude n / 16) := by
  have heta : 0 < feedbackA2AsymptoticEta lam :=
    feedbackA2AsymptoticEta_pos hlam0
  let cSquare : ℝ :=
    feedbackA2AsymptoticEta lam ^ 2 * (13 * amplitude / 16) /
      (4 * (33280 : ℝ) ^ 2)
  let cLinear : ℝ :=
    feedbackA2AsymptoticEta lam * (13 * amplitude / 16) /
      (2 * (33280 : ℝ))
  have hcSquare : 0 < cSquare := by
    dsimp [cSquare]
    positivity
  have hcLinear : 0 < cLinear := by
    dsimp [cLinear]
    positivity
  filter_upwards [eventually_log_nat_le_mul_sqrt hcSquare,
    eventually_log_nat_le_mul_sqrt hcLinear] with n hSquare hLinear
  rw [feedbackA2AsymptoticBuffer_eq]
  constructor
  · dsimp [cSquare] at hSquare
    nlinarith
  · dsimp [cLinear] at hLinear
    nlinarith

/-- The explicit coefficient condition that closes the A2 shear threshold eventually. -/
theorem eventually_feedbackA2Asymptotic_threshold
    {amplitude globalQ : ℝ}
    (hcoefficient : 8 * (globalQ + 33) < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      2 * (globalQ + 32) * Real.sqrt n +
          (2 * (feedbackA2AsymptoticRadius n : ℝ) + 2) <
        feedbackA2AsymptoticBuffer amplitude n / 4 := by
  let gap : ℝ := amplitude / 4 - (2 * (globalQ + 32) + 2)
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually (eventually_gt_atTop (2 / gap))] with n hn
  have hrad := feedbackA2AsymptoticRadius_le_real_sqrt n
  rw [feedbackA2AsymptoticBuffer_eq]
  have hgapSqrt : 2 < gap * Real.sqrt (n : ℝ) := by
    rw [div_lt_iff₀ hgap] at hn
    simpa [mul_comm] using hn
  dsimp [gap] at hgapSqrt
  nlinarith

/-! ## Vanishing of the cubic stopped-current remainder -/

/-- A pointwise `1 / sqrt n` envelope for the two actual stopped-current terms. -/
theorem feedbackA2AsymptoticCubicRemainder_le
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude)
    {n : ℕ} (hn : 4 ≤ n)
    (hBn : feedbackA2AsymptoticBuffer amplitude n ≤ (n : ℝ))
    (hTn : (feedbackA2AsymptoticHorizon amplitude n : ℝ) ≤ (n : ℝ)) :
    feedbackA2AsymptoticCubicRemainder lam amplitude n ≤
      feedbackA2AsymptoticCubicCoefficient lam amplitude / Real.sqrt n := by
  let s : ℝ := Real.sqrt n
  let r : ℝ := feedbackA2AsymptoticRadius n
  let B : ℝ := feedbackA2AsymptoticBuffer amplitude n
  let C : ℝ := 6 + 81 / lam
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn0
  have hs0 : 0 < s := by
    exact Real.sqrt_pos.2 hnR
  have hs2 : 2 ≤ s := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)]
    norm_num
    exact_mod_cast hn
  have hsquare : s * s = (n : ℝ) := by
    exact Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsLeN : s ≤ (n : ℝ) := by
    nlinarith
  have hr0 : 0 < r := by
    dsimp [r]
    exact_mod_cast feedbackA2AsymptoticRadius_pos hn0
  have hsRad : s / 2 ≤ r := by
    have happrox := real_sqrt_lt_feedbackA2AsymptoticRadius_add_one n
    change s < r + 1 at happrox
    nlinarith
  have hden : (n : ℝ) * s / 8 ≤ r ^ 3 := by
    calc
      (n : ℝ) * s / 8 = (s / 2) ^ 3 := by
        rw [← hsquare]
        ring
      _ ≤ r ^ 3 := pow_le_pow_left₀ (by positivity) hsRad 3
  have hden0 : 0 < (n : ℝ) * s / 8 := by positivity
  have hBpos : 0 < B := by
    dsimp [B]
    rw [feedbackA2AsymptoticBuffer_eq]
    positivity
  have hsqrtB : Real.sqrt B ≤ s := by
    exact Real.sqrt_le_sqrt hBn
  have hBsqrt : B * Real.sqrt B ≤ amplitude * (n : ℝ) := by
    calc
      B * Real.sqrt B ≤ B * s :=
        mul_le_mul_of_nonneg_left hsqrtB hBpos.le
      _ = amplitude * (n : ℝ) := by
        dsimp [B, s]
        rw [feedbackA2AsymptoticBuffer_eq]
        nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hBlinear : B ≤ amplitude * (n : ℝ) := by
    dsimp [B, s] at hsLeN ⊢
    rw [feedbackA2AsymptoticBuffer_eq]
    exact mul_le_mul_of_nonneg_left hsLeN hamp.le
  have hbase : 2 * B + 5 * B * Real.sqrt B ≤
      7 * amplitude * (n : ℝ) := by
    nlinarith
  have hbase0 : 0 ≤ 2 * B + 5 * B * Real.sqrt B := by positivity
  have hfirst :
      (2 * B + 5 * B * Real.sqrt B) / r ^ 3 ≤
        56 * amplitude / s := by
    calc
      (2 * B + 5 * B * Real.sqrt B) / r ^ 3 ≤
          (7 * amplitude * (n : ℝ)) / ((n : ℝ) * s / 8) :=
        div_le_div₀ (by positivity) hbase hden0 hden
      _ = 56 * amplitude / s := by
        field_simp
        ring
  have hC0 : 0 < C := by
    dsimp [C]
    positivity
  have htotal :
      (2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ) ≤
        (7 * amplitude + C) * (n : ℝ) := by
    have hCT := mul_le_mul_of_nonneg_left hTn hC0.le
    nlinarith
  have htotal0 : 0 ≤
      (2 * B + 5 * B * Real.sqrt B) +
        C * (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
    positivity
  have hdivLam :
      ((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam) ≤
        ((7 * amplitude + C) * (n : ℝ)) / (2 * lam) :=
    (div_le_div_iff_of_pos_right (by positivity)).2 htotal
  have hsecond :
      3 * ((((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam)) /
            r ^ 3) ≤
        (12 / lam) * (7 * amplitude + C) / s := by
    calc
      3 * ((((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam)) /
            r ^ 3) ≤
          3 * ((((7 * amplitude + C) * (n : ℝ)) / (2 * lam)) /
            ((n : ℝ) * s / 8)) := by
        gcongr
      _ = (12 / lam) * (7 * amplitude + C) / s := by
        field_simp
        ring
  have hsecondActual :
      (3 * (((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam))) /
            r ^ 3 ≤
        (12 / lam) * (7 * amplitude + C) / s := by
    calc
      (3 * (((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam))) /
            r ^ 3 =
        3 * ((((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam)) /
            r ^ 3) := by ring
      _ ≤ (12 / lam) * (7 * amplitude + C) / s := hsecond
  unfold feedbackA2AsymptoticCubicRemainder
    feedbackA2AsymptoticCubicCoefficient
  change
    (2 * B + 5 * B * Real.sqrt B) / r ^ 3 +
        (3 * (((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam))) /
            r ^ 3 ≤
      (56 * amplitude + (12 / lam) * (7 * amplitude + C)) / s
  calc
    (2 * B + 5 * B * Real.sqrt B) / r ^ 3 +
        (3 * (((2 * B + 5 * B * Real.sqrt B) +
          C * (feedbackA2AsymptoticHorizon amplitude n : ℝ)) / (2 * lam))) /
            r ^ 3 ≤
      56 * amplitude / s + (12 / lam) * (7 * amplitude + C) / s :=
        add_le_add hfirst hsecondActual
    _ = (56 * amplitude + (12 / lam) * (7 * amplitude + C)) / s := by ring

theorem feedbackA2AsymptoticCubicCoefficient_pos
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    0 < feedbackA2AsymptoticCubicCoefficient lam amplitude := by
  unfold feedbackA2AsymptoticCubicCoefficient
  positivity

/-- The two actual stopped-current terms tend to zero for `R_n = Nat.sqrt n`. -/
theorem tendsto_feedbackA2AsymptoticCubicRemainder
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    Tendsto (feedbackA2AsymptoticCubicRemainder lam amplitude)
      atTop (nhds 0) := by
  let coefficient := feedbackA2AsymptoticCubicCoefficient lam amplitude
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := hsqrt.inv_tendsto_atTop
  have hupper : Tendsto (fun n : ℕ ↦ coefficient / Real.sqrt n)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds (x := coefficient)).mul hinv using 1 <;>
      simp [div_eq_mul_inv]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun n ↦ by
      unfold feedbackA2AsymptoticCubicRemainder
        feedbackA2AsymptoticBuffer endpointBuffer
      positivity
  · filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp]
      with n hn
    exact feedbackA2AsymptoticCubicRemainder_le
      hlam0 hamp hn.1 hn.2.2.1 hn.2.2.2.2.1

/-- The VC term and both stopped-current terms vanish jointly. -/
theorem tendsto_feedbackA2AsymptoticRemainder
    {lam amplitude : ℝ} (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    Tendsto (feedbackA2AsymptoticRemainder lam amplitude)
      atTop (nhds 0) := by
  have hregENN : Tendsto
      (fun n ↦ 2 * RelativeVC.regularityPolynomialBadBound n)
      atTop (nhds 0) := by
    simpa [two_mul] using
      RelativeVC.tendsto_regularityPolynomialBadBound.add
        RelativeVC.tendsto_regularityPolynomialBadBound
  have hreg : Tendsto
      (fun n ↦ ENNReal.toReal
        (2 * RelativeVC.regularityPolynomialBadBound n))
      atTop (nhds 0) := by
    exact (ENNReal.tendsto_toReal (by simp)).comp hregENN
  unfold feedbackA2AsymptoticRemainder
  simpa only [zero_add] using hreg.add
    (tendsto_feedbackA2AsymptoticCubicRemainder hlam0 hamp)

/-! ## Actual stopped A2 survival with fixed parameters -/

/-- All pointwise hypotheses of the stopped A2 assembly hold eventually under the explicit
parameter sequence.  The good event simultaneously gives strict horizon survival and the
all-real normalized stopped-graph range. -/
theorem eventually_feedbackA2Asymptotic_assembly
    {lam amplitude globalQ endpointQ : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent
            hlam0 hlam amplitude globalQ endpointQ n) ≤
        18832 / globalQ + 44 / endpointQ +
          feedbackA2AsymptoticRemainder lam amplitude n ∧
      ∀ sample : FiniteSample n,
        sample ∈ feedbackA2AsymptoticGoodEvent
          hlam0 hlam amplitude globalQ endpointQ n →
          (∀ t : ℝ≥0,
            t < feedbackA2AsymptoticHorizon amplitude n →
              |safeFeedbackHeightAtElapsed
                hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticBuffer amplitude n) 0 t sample| <
              feedbackA2AsymptoticBuffer amplitude n / 8) ∧
          ∀ z : ℝ,
            sample.normalizedStoppedContinuationFeedbackCurve
                hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticEta lam)
                (feedbackA2AsymptoticBuffer amplitude n)
                (feedbackA2AsymptoticHorizon amplitude n) z ∈
              Icc (-1 : ℝ) 1 := by
  have hamp : 0 < amplitude := by
    have hq33 : 0 < globalQ + 33 := by linarith
    linarith
  filter_upwards [eventually_endpointBuffer_geometry hamp,
    eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedbackA2Asymptotic_regularity_inequalities hlam0 hamp,
    eventually_feedbackA2Asymptotic_threshold hcoefficient]
      with n hendpoint hhorizon hregular hthreshold
  rcases hendpoint with
    ⟨hn0, hbuffer, hfitSource, hfitTarget, hbufferOne⟩
  rcases hhorizon with
    ⟨hn, _hbuffer, hBn, hRightEq, hTn, hscale⟩
  have heta0 : 0 ≤ feedbackA2AsymptoticEta lam :=
    (feedbackA2AsymptoticEta_pos hlam0).le
  have hassembly := feedbackA2StoppedAssembly
    hlam0 hlam hn hbuffer hBn heta0
    (feedbackA2AsymptoticEta_small hlam0) hglobalQ
    hRightEq.le hregular.1 hregular.2 hthreshold hbuffer
    hfitSource hfitTarget hbufferOne hendpointQ
    (feedbackA2AsymptoticRadius_pos hn0)
  constructor
  · calc
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent
            hlam0 hlam amplitude globalQ endpointQ n) ≤
          18832 / globalQ + 44 / endpointQ +
            ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
            (2 * feedbackA2AsymptoticBuffer amplitude n +
                5 * feedbackA2AsymptoticBuffer amplitude n *
                  Real.sqrt (feedbackA2AsymptoticBuffer amplitude n)) /
              (feedbackA2AsymptoticRadius n : ℝ) ^ 3 +
            3 * (((2 * feedbackA2AsymptoticBuffer amplitude n +
                  5 * feedbackA2AsymptoticBuffer amplitude n *
                    Real.sqrt (feedbackA2AsymptoticBuffer amplitude n)) +
                (6 + 81 / lam) *
                  (feedbackA2AsymptoticHorizon amplitude n : ℝ)) /
              (2 * lam)) / (feedbackA2AsymptoticRadius n : ℝ) ^ 3 := by
        simpa only [feedbackA2AsymptoticBadEvent,
          feedbackA2AsymptoticBuffer] using hassembly.1
      _ = 18832 / globalQ + 44 / endpointQ +
          feedbackA2AsymptoticRemainder lam amplitude n := by
        unfold feedbackA2AsymptoticRemainder
          feedbackA2AsymptoticCubicRemainder
        ring
  · intro sample hgood
    have hgoodStopped : sample ∈ feedbackA2StoppedGoodEvent
        hlam0.le (hlam.trans (by norm_num))
        (feedbackA2AsymptoticEta lam) amplitude globalQ endpointQ
        (feedbackA2AsymptoticBuffer amplitude n)
        (feedbackA2AsymptoticHorizon amplitude n)
        (feedbackA2AsymptoticRadius n) := by
      simpa only [feedbackA2AsymptoticGoodEvent,
        feedbackA2AsymptoticBadEvent, feedbackA2StoppedGoodEvent] using hgood
    constructor
    · exact hassembly.2 sample hgoodStopped
    · exact
        sample.normalizedStoppedContinuationFeedbackCurve_mem_Icc_of_actualGood
          hlam0 hlam hn hbuffer hBn heta0 hRightEq.le
          hregular.1 hregular.2 hthreshold hscale hgoodStopped

/-- Fixed-parameter stopped A2 survival: the explicit remainder may be absorbed into any
positive `epsilon`; the global-cut and endpoint terms correctly remain as fixed constants. -/
theorem eventually_feedbackA2Asymptotic_bad_probability_le_add
    {lam amplitude globalQ endpointQ ε : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent
            hlam0 hlam amplitude globalQ endpointQ n) ≤
        18832 / globalQ + 44 / endpointQ + ε := by
  have hamp : 0 < amplitude := by
    have hq33 : 0 < globalQ + 33 := by linarith
    linarith
  have hremainder :=
    (tendsto_feedbackA2AsymptoticRemainder hlam0 hamp).eventually
      (eventually_lt_nhds hε)
  filter_upwards [eventually_feedbackA2Asymptotic_assembly
    hlam0 hlam hglobalQ hendpointQ hcoefficient, hremainder]
      with n hn hrem
  exact hn.1.trans (by linarith)

/-- Final fixed-parameter form: eventual epsilon probability control is packaged with strict
horizon survival and normalized stopped-graph range on the same actual good event. -/
theorem eventually_feedbackA2Asymptotic_survival
    {lam amplitude globalQ endpointQ ε : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hendpointQ : 1 ≤ endpointQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent
            hlam0 hlam amplitude globalQ endpointQ n) ≤
        18832 / globalQ + 44 / endpointQ + ε ∧
      ∀ sample : FiniteSample n,
        sample ∈ feedbackA2AsymptoticGoodEvent
          hlam0 hlam amplitude globalQ endpointQ n →
          (∀ t : ℝ≥0,
            t < feedbackA2AsymptoticHorizon amplitude n →
              |safeFeedbackHeightAtElapsed
                hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticBuffer amplitude n) 0 t sample| <
              feedbackA2AsymptoticBuffer amplitude n / 8) ∧
          ∀ z : ℝ,
            sample.normalizedStoppedContinuationFeedbackCurve
                hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticEta lam)
                (feedbackA2AsymptoticBuffer amplitude n)
                (feedbackA2AsymptoticHorizon amplitude n) z ∈
              Icc (-1 : ℝ) 1 := by
  have hamp : 0 < amplitude := by
    have hq33 : 0 < globalQ + 33 := by linarith
    linarith
  have hremainder :=
    (tendsto_feedbackA2AsymptoticRemainder hlam0 hamp).eventually
      (eventually_lt_nhds hε)
  filter_upwards [eventually_feedbackA2Asymptotic_assembly
    hlam0 hlam hglobalQ hendpointQ hcoefficient, hremainder]
      with n hn hrem
  exact ⟨hn.1.trans (by linarith), hn.2⟩

/-- For every prescribed error level, explicit fixed parameters make the actual stopped A2 bad
probability eventually smaller than that level. -/
theorem exists_feedbackA2Asymptotic_parameters_bad_probability_lt
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ globalQ endpointQ amplitude : ℝ,
      0 < globalQ ∧ 1 ≤ endpointQ ∧
        8 * (globalQ + 33) < amplitude ∧
        ∀ᶠ n : ℕ in atTop,
          (finiteSampleLaw n : Measure (FiniteSample n)).real
              (feedbackA2AsymptoticBadEvent
                hlam0 hlam amplitude globalQ endpointQ n) < δ := by
  let globalQ : ℝ := 75328 / δ
  let endpointQ : ℝ := 176 / δ + 1
  let amplitude : ℝ := 8 * (globalQ + 33) + 1
  have hglobalQ : 0 < globalQ := by
    dsimp [globalQ]
    positivity
  have hendpointQ : 1 ≤ endpointQ := by
    dsimp [endpointQ]
    have : 0 ≤ 176 / δ := by positivity
    linarith
  have hcoefficient : 8 * (globalQ + 33) < amplitude := by
    dsimp [amplitude]
    linarith
  have hglobalTerm : 18832 / globalQ = δ / 4 := by
    dsimp [globalQ]
    field_simp
    ring
  have hendpointTerm : 44 / endpointQ < δ / 4 := by
    dsimp [endpointQ]
    rw [div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  refine ⟨globalQ, endpointQ, amplitude, hglobalQ, hendpointQ,
    hcoefficient, ?_⟩
  filter_upwards [eventually_feedbackA2Asymptotic_bad_probability_le_add
    hlam0 hlam hglobalQ hendpointQ hcoefficient (show 0 < δ / 4 by positivity)]
      with n hn
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2AsymptoticBadEvent
          hlam0 hlam amplitude globalQ endpointQ n) ≤
      18832 / globalQ + 44 / endpointQ + δ / 4 := hn
    _ < δ := by rw [hglobalTerm]; linarith

end OTSelector
