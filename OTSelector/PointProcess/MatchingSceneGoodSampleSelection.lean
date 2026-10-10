import OTSelector.Probability.GoodSampleExtraction
import OTSelector.PointProcess.MatchingSceneSelectionBounds
import OTSelector.PointProcess.MatchingSceneSelectionCollision
import OTSelector.Feedback.FeedbackSelectorGood
import Mathlib.Logic.Encodable.Basic

/-!
# Actual good-sample extraction on macroscopic windows

The original good-event factory supplies survival, VC control, no ties and optimizer energy.
Actual stopped moments and collision grids spend a summable budget on countably many window
constraints. Only their finite prefixes are imposed when selecting each actual bad sample.
The residual input is convergence under the original finite-sample law with this same mask.
-/

open MeasureTheory Filter Set
open scoped Classical BigOperators ENNReal NNReal Topology

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

namespace OTSelector

open FiniteSample PointProcess PointProcess.MatchingScene

/-- Count windows and collision resolutions share one countable constraint index. -/
abbrev FeedbackSelectionIndex := ℕ ⊕ (ℕ × ℕ)

/-- A strictly positive summable probability budget for each encoded constraint. -/
noncomputable def feedbackSelectionWeight (δ : ℝ) (a : FeedbackSelectionIndex) : ℝ :=
  δ / 16 * (1 / 2 : ℝ) ^ Encodable.encode a

theorem feedbackSelectionWeight_pos {δ : ℝ} (hδ : 0 < δ) (a : FeedbackSelectionIndex) :
    0 < feedbackSelectionWeight δ a := by
  unfold feedbackSelectionWeight
  positivity

/-- The actual closed-window moment for a macroscopic root interval. -/
noncomputable def feedbackSelectionClosedCountSq {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude u v : ℝ) (R : ℕ)
    (sample : FiniteSample n) : ℝ≥0∞ :=
  stoppedEmpiricalClosedCountSq hlam0 hlamHalf (feedbackA2AsymptoticEta lam)
    (feedbackA2AsymptoticBuffer amplitude n) (feedbackA2AsymptoticHorizon amplitude n)
    R ((n : ℝ) * u) ((n : ℝ) * v) sample

/-- The actual finite collision grid at radius `R`, with threshold tending to zero in `j`. -/
noncomputable def feedbackSelectionCollisionGrid {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude δ u v : ℝ) (R j : ℕ)
    (sample : FiniteSample n) : ℝ≥0∞ :=
  stoppedEmpiricalSelectedCollisionGrid hlam0 hlamHalf (feedbackA2AsymptoticEta lam)
    (feedbackA2AsymptoticBuffer amplitude n) (feedbackA2AsymptoticHorizon amplitude n)
    R (collisionSelectionThreshold j) (feedbackSelectionWeight δ (.inr (R, j)))
    ((n : ℝ) * u) ((n : ℝ) * v) sample

private theorem eventually_buffer_add_lt_mul {amplitude w : ℝ} (hw : 0 < w) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, feedbackA2AsymptoticBuffer amplitude n + D < (n : ℝ) * w := by
  have hsqrt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually
    (eventually_gt_atTop (max 1 ((amplitude + |D| + 1) / w)))] with n hn
  have h1 : 1 < Real.sqrt (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hpos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hc : amplitude + |D| + 1 < Real.sqrt (n : ℝ) * w :=
    (div_lt_iff₀ hw).mp ((le_max_right _ _).trans_lt hn)
  have hm : (amplitude + |D| + 1) * Real.sqrt (n : ℝ) < (n : ℝ) * w := by
    calc
      _ < (Real.sqrt (n : ℝ) * w) * Real.sqrt n := mul_lt_mul_of_pos_right hc hpos
      _ = (n : ℝ) * w := by
        rw [mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hd := mul_le_mul_of_nonneg_left h1.le (abs_nonneg D)
  rw [feedbackA2AsymptoticBuffer_eq]
  nlinarith [le_abs_self D]

/-- Every fixed observation margin eventually fits into the genuine bulk, for all roots
in the fixed interior macroscopic interval. -/
theorem eventually_feedbackSelection_bulk_fit {amplitude u v : ℝ}
    (hamp : 0 < amplitude) (hu : 0 < u) (hv : v < 1) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < feedbackA2AsymptoticBuffer amplitude n ∧
      feedbackA2AsymptoticBuffer amplitude n ≤ (n : ℝ) * u - D ∧
      (n : ℝ) * v + D < feedbackA2AsymptoticBuffer amplitude n +
        (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_buffer_add_lt_mul (amplitude := amplitude) hu D,
    eventually_buffer_add_lt_mul (amplitude := amplitude) (sub_pos.mpr hv) D]
    with n hn hl hr
  refine ⟨by omega, hn.2.1, by linarith, ?_⟩
  rw [hn.2.2.2.1]
  nlinarith

private noncomputable def selectionConstraint {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude δ u v : ℝ)
    (m : ℕ) : Set (FiniteSample n) :=
  match Encodable.decode₂ FeedbackSelectionIndex m with
  | none => univ
  | some (.inl R) => {sample | feedbackSelectionClosedCountSq hlam0 hlamHalf amplitude u v R sample ≤
      ENNReal.ofReal (selectionClosedCountThreshold R (δ / 16 * (1 / 2 : ℝ) ^ m))}
  | some (.inr (R, j)) => {sample | stoppedEmpiricalSelectedCollisionGrid hlam0 hlamHalf
      (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude n)
      (feedbackA2AsymptoticHorizon amplitude n) R (collisionSelectionThreshold j)
      (δ / 16 * (1 / 2 : ℝ) ^ m) ((n : ℝ) * u) ((n : ℝ) * v) sample ≤
        ENNReal.ofReal (collisionSelectionThreshold j)}

private theorem eventually_selectionConstraint_budget
    {lam amplitude globalQ endpointQ C δ u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude)
    (hδ : 0 < δ) (hu : 0 < u) (huv : u < v) (hv : v < 1) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, (finiteSampleLaw n : Measure (FiniteSample n)).real
      (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ∩
        (selectionConstraint hlam0.le (hlam.trans (by norm_num)) amplitude δ u v m)ᶜ) ≤
      δ / 16 * (1 / 2 : ℝ) ^ m := by
  have hw : 0 < δ / 16 * (1 / 2 : ℝ) ^ m := by positivity
  have heta := (feedbackA2AsymptoticEta_pos hlam0).le
  have hsmall := feedbackA2AsymptoticEta_small hlam0
  have hsurvival := eventually_feedbackSelectorGood_survival (C := C) (endpointQ := endpointQ)
    hlam0 hlam hglobalQ hcoefficient
  cases hd : Encodable.decode₂ FeedbackSelectionIndex m with
  | none =>
      filter_upwards with n
      simp only [selectionConstraint, hd, compl_univ, inter_empty, measureReal_empty]
      exact hw.le
  | some a =>
      cases a with
      | inl R =>
          filter_upwards [eventually_feedbackSelection_bulk_fit hamp hu hv ((R : ℝ) + 1),
            hsurvival] with n hn hs
          have hG : feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ⊆
              {sample | StoppedCollisionGood hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude n)
                (feedbackA2AsymptoticHorizon amplitude n) sample} := by
            intro sample hg
            exact ⟨feedbackSelectorGoodEvent.noFeedbackTies hg, hs sample hg⟩
          simpa only [selectionConstraint, hd, feedbackSelectionClosedCountSq] using
            measureReal_stoppedEmpiricalClosedCountSq_constraint_failure_le
              hlam0 hlam hn.1 hn.2.1 heta hsmall (feedbackA2AsymptoticHorizon amplitude n)
              (Nat.cast_nonneg R) (mul_lt_mul_of_pos_left huv (Nat.cast_pos.mpr hn.1))
              (by linarith [hn.2.2.1]) (by linarith [hn.2.2.2])
              (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) hG hw
      | inr p =>
          rcases p with ⟨R, j⟩
          filter_upwards [eventually_feedbackSelection_bulk_fit hamp hu hv (3 * (R : ℝ) + 3),
            hsurvival] with n hn hs
          have hG : feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ⊆
              {sample | StoppedCollisionGood hlam0.le (hlam.trans (by norm_num))
                (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude n)
                (feedbackA2AsymptoticHorizon amplitude n) sample} := by
            intro sample hg
            exact ⟨feedbackSelectorGoodEvent.noFeedbackTies hg, hs sample hg⟩
          have hb := measureReal_stoppedEmpiricalSelectedCollisionGrid_on_mask_ge_le
            hlam0 hlam hn.1 hn.2.1 heta hsmall (feedbackA2AsymptoticHorizon amplitude n)
            (Nat.cast_nonneg R) (collisionSelectionThreshold_pos j) hw
            (mul_lt_mul_of_pos_left huv (Nat.cast_pos.mpr hn.1)) hn.2.2.1 hn.2.2.2
            (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n) hG
          apply (measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
            (show feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ∩
                (selectionConstraint hlam0.le (hlam.trans (by norm_num)) amplitude δ u v m)ᶜ ⊆
              {sample | sample ∈ feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ∧
                ENNReal.ofReal (collisionSelectionThreshold j) ≤
                  stoppedEmpiricalSelectedCollisionGrid hlam0.le (hlam.trans (by norm_num))
                    (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude n)
                    (feedbackA2AsymptoticHorizon amplitude n) R (collisionSelectionThreshold j)
                    (δ / 16 * (1 / 2 : ℝ) ^ m) ((n : ℝ) * u) ((n : ℝ) * v) sample} from ?_)).trans hb
          intro sample hg
          refine ⟨hg.1, ?_⟩
          have hh := hg.2
          simp only [selectionConstraint, hd, mem_compl_iff, mem_ofPred_eq] at hh
          exact (not_le.mp hh).le

/-- Choose the actual factory parameters once, then extract witnesses to any persistent bad
probability, while retaining every original-law masked residual and the explicit count/collision
budgets. The size of row `n` is `n+1`, so all empirical laws are probability measures. -/
theorem exists_feedbackSelectorGood_sample_parameters {lam δ u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ∃ amplitude globalQ endpointQ C : ℝ,
      0 < amplitude ∧ 0 < globalQ ∧ 1 ≤ endpointQ ∧
      8 * (globalQ + 33) < amplitude ∧ 0 < C ∧
      ∀ (bad : ∀ n, Set (FiniteSample (n + 1)))
        (residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ),
        (∃ᶠ n in atTop, δ ≤ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
          (bad n)) →
        (∀ m ε, 0 < ε → Tendsto (fun n ↦
          (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
            (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (n + 1) ∩
              {sample | ε < |residual m n sample|})) atTop (𝓝 0)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ sample : ∀ j, FiniteSample (φ j + 1),
          (∀ j, sample j ∈ feedbackSelectorGoodEvent
              hlam0 hlam amplitude globalQ endpointQ C (φ j + 1) ∧ sample j ∈ bad (φ j)) ∧
          (∀ m, Tendsto (fun j ↦ residual m (φ j) (sample j)) atTop (𝓝 0)) ∧
          (∀ R : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ j in atTop,
            feedbackSelectionClosedCountSq hlam0.le (hlam.trans (by norm_num))
              amplitude u v R (sample j) ≤ ENNReal.ofReal K) ∧
          (∀ R j : ℕ, ∀ᶠ k in atTop,
            feedbackSelectionCollisionGrid hlam0.le (hlam.trans (by norm_num))
              amplitude δ u v R j (sample k) ≤ ENNReal.ofReal (collisionSelectionThreshold j)) := by
  obtain ⟨amplitude, globalQ, endpointQ, C, hamp, hq, hqE, hcoefficient, hC, hgood⟩ :=
    exists_feedbackSelectorGood_parameters hlam0 hlam (show 0 < δ / 4 by positivity)
  refine ⟨amplitude, globalQ, endpointQ, C, hamp, hq, hqE, hcoefficient, hC, ?_⟩
  intro bad residual hbad hres
  let good (n : ℕ) := feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (n + 1)
  let constraint (m n : ℕ) : Set (FiniteSample (n + 1)) :=
    selectionConstraint hlam0.le (hlam.trans (by norm_num)) amplitude δ u v m
  let weight (m : ℕ) := δ / 16 * (1 / 2 : ℝ) ^ m
  have hweight (j : ℕ) : ∑ m ∈ Finset.range (j + 1), weight m ≤ δ / 4 := by
    change (∑ m ∈ Finset.range (j + 1), δ / 16 * (1 / 2 : ℝ) ^ m) ≤ _
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (sum_geometric_two_le (j + 1))
      (show 0 ≤ δ / 16 by positivity)
    linarith
  have hg : ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real (good n)ᶜ ≤ δ / 4 := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hgood] with n hn
    exact hn.le
  have hcon (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
        (good n ∩ (constraint m n)ᶜ) ≤ weight m :=
    (tendsto_add_atTop_nat 1).eventually
      (eventually_selectionConstraint_budget (endpointQ := endpointQ) (C := C)
        hlam0 hlam hamp hq hcoefficient hδ hu huv hv m)
  obtain ⟨φ, hφ, sample, hs, hc, hr⟩ :=
    Probability.exists_good_bad_samples_with_constraints_of_frequently
      (fun n ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))))
      good bad constraint residual weight hδ hbad hg hweight hcon hres
  refine ⟨φ, hφ, sample, hs, hr, ?_, ?_⟩
  · intro R
    let K := selectionClosedCountThreshold R (feedbackSelectionWeight δ (.inl R))
    refine ⟨K, selectionClosedCountThreshold_pos (Nat.cast_nonneg R)
      (feedbackSelectionWeight_pos hδ (.inl R)), ?_⟩
    simpa only [constraint, selectionConstraint, Encodable.decode₂_encode,
      mem_ofPred_eq, K, feedbackSelectionWeight] using hc (Encodable.encode (.inl R : FeedbackSelectionIndex))
  · intro R j
    simpa only [constraint, selectionConstraint, Encodable.decode₂_encode,
      mem_ofPred_eq, feedbackSelectionCollisionGrid, feedbackSelectionWeight] using
      hc (Encodable.encode (.inr (R, j) : FeedbackSelectionIndex))

end OTSelector
