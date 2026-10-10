import OTSelector.Limit.FeedbackRegenerationCells
import OTSelector.Limit.FeedbackMarkedFirstHold
import Mathlib.Probability.Moments.Basic

/-!
# Positive exponential moments of the actual return cell

The previously proved geometric return-count and physical-clock tails give a common positive
exponential moment for the number of cell jumps and its physical duration. No independence of
holding times conditional on the return count is required.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

private theorem exponential_grid_series {d theta r : ℝ} (hr : 0 ≤ r)
    (hcontract : Real.exp (theta * d) * r < 1) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))) *
      ENNReal.ofReal r ^ n) < ∞ := by
  have hs := (summable_geometric_of_lt_one
    (mul_nonneg (Real.exp_pos _).le hr) hcontract).mul_left
      (Real.exp (2 * theta * d))
  have heq (n : ℕ) :
      Real.exp (2 * theta * d) * (Real.exp (theta * d) * r) ^ n =
        Real.exp (theta * (d * (n + 2))) * r ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hs' := hs.congr heq
  have hcast (n : ℕ) :
      ENNReal.ofReal (Real.exp (theta * (d * (n + 2))) * r ^ n) =
        ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))) * ENNReal.ofReal r ^ n := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hr]
  simpa only [hcast] using hs'.tsum_ofReal_lt_top

/-- A real observable with a geometric tail on a fixed grid has an exponential moment whenever
that grid's exponential weight preserves geometric contraction. -/
theorem integrable_exp_of_geometric_grid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {d theta r A : ℝ} (hd : 0 < d) (htheta : 0 ≤ theta) (hr : 0 ≤ r)
    (hcontract : Real.exp (theta * d) * r < 1)
    (htail : ∀ n : ℕ, μ {w | d * (n + 1) < X w} ≤
      ENNReal.ofReal A * ENNReal.ofReal r ^ n) :
    Integrable (fun w ↦ Real.exp (theta * X w)) μ := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ↦
    {w | d * (n + 1) < X w}.indicator
      (fun _ ↦ ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))))
  have hm (n : ℕ) : MeasurableSet {w | d * (n + 1) < X w} :=
    measurableSet_lt measurable_const hX
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hm n)
  have hbound (w : Ω) : ENNReal.ofReal (Real.exp (theta * X w)) ≤
      ENNReal.ofReal (Real.exp (theta * d)) + ∑' n : ℕ, F n w := by
    have hex : ∃ n : ℕ, X w ≤ d * (n + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt (X w / d)
      refine ⟨n, ?_⟩
      have hn' := (div_lt_iff₀ hd).mp hn
      nlinarith
    have hle := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Nat.find_spec hex) htheta))
    cases hi : Nat.find hex with
    | zero =>
        simp only [hi, Nat.cast_zero, zero_add, mul_one] at hle
        exact hle.trans le_self_add
    | succ j =>
        have hj : d * (j + 1) < X w :=
          lt_of_not_ge (Nat.find_min hex (by rw [hi]; omega))
        calc
          _ ≤ ENNReal.ofReal (Real.exp (theta * (d * (j + 2)))) := by
            simpa only [hi, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hle
          _ = F j w := by
            dsimp [F]
            rw [Set.indicator_of_mem (show w ∈ {w | d * (j + 1) < X w} from hj)]
          _ ≤ ∑' n : ℕ, F n w := ENNReal.le_tsum j
          _ ≤ _ := le_add_self
  have hseries : (∑' n : ℕ, ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))) *
      (ENNReal.ofReal A * ENNReal.ofReal r ^ n)) < ∞ := by
    have heq : (∑' n : ℕ, ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))) *
        (ENNReal.ofReal A * ENNReal.ofReal r ^ n)) =
        ENNReal.ofReal A * ∑' n : ℕ,
          ENNReal.ofReal (Real.exp (theta * (d * (n + 2)))) * ENNReal.ofReal r ^ n := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext n
      ac_rfl
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (exponential_grid_series hr hcontract)
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hX.const_mul theta |>.exp.aestronglyMeasurable)
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).mp
  apply ne_of_lt
  apply lt_of_le_of_lt (lintegral_mono hbound)
  rw [lintegral_add_left measurable_const, lintegral_tsum (fun n ↦ (hF n).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  apply lt_of_le_of_lt (add_le_add_right (ENNReal.tsum_le_tsum (fun n ↦ ?_)) _)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hseries⟩)
  change (∫⁻ w, F n w ∂μ) ≤ _
  rw [show F n = {w | d * (n + 1) < X w}.indicator
      (fun _ ↦ ENNReal.ofReal (Real.exp (theta * (d * (n + 2))))) from rfl,
    lintegral_indicator (hm n), lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_mul_right (htail n) _

/-- One geometric ratio controls both jump count and physical duration. -/
noncomputable def feedbackCellTailRatio (lam : ℝ) : ℝ :=
  max (feedbackExcursionRatio lam) (2 * Real.exp (-2))

theorem feedbackCellTailRatio_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    0 < feedbackCellTailRatio lam :=
  (feedbackExcursionRatio_pos hlam0 hlam).trans_le (le_max_left _ _)

theorem feedbackCellTailRatio_lt_one {lam : ℝ} (hlam0 : 0 < lam) :
    feedbackCellTailRatio lam < 1 := by
  exact max_lt (feedbackExcursionRatio_lt_one hlam0)
    (ENNReal.ofReal_lt_one.mp feedbackClockTailRatio_lt_one)

/-- Explicit positive common exponent for the actual count and length. -/
noncomputable def feedbackCellExpRate (lam : ℝ) : ℝ :=
  -Real.log (feedbackCellTailRatio lam) / 8

theorem feedbackCellExpRate_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    0 < feedbackCellExpRate lam := by
  exact div_pos (neg_pos.mpr (Real.log_neg (feedbackCellTailRatio_pos hlam0 hlam)
    (feedbackCellTailRatio_lt_one hlam0))) (by norm_num)

theorem feedbackCellExpRate_contract {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    Real.exp (feedbackCellExpRate lam * 4) * feedbackCellTailRatio lam < 1 := by
  have hr := feedbackCellTailRatio_pos hlam0 hlam
  have hl := Real.log_neg hr (feedbackCellTailRatio_lt_one hlam0)
  rw [← Real.exp_log hr, ← Real.exp_add, Real.exp_lt_one_iff]
  unfold feedbackCellExpRate
  linarith

/-- The literal first return index has the previously proved actual survival tail. -/
theorem feedbackMarkedFirstReturnIndex_tail {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackMarkedTrajectory lam hlam0 hlam 0 {w | n + 1 < feedbackMarkedFirstReturnIndex w} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  apply (measure_mono (fun w hw ↦ ?_)).trans
    (feedbackMarkedTrajectory_positive_return_tail hlam0 hlam n)
  change n + 1 < feedbackMarkedFirstReturnIndex w at hw
  have hex : ∃ j, (w (j + 1)).2.2 = 0 := by
    by_contra hn
    have hzero := (feedbackMarkedFirstReturnIndex_eq_zero_iff w).mpr hn
    rw [hzero] at hw
    omega
  rw [feedbackMarkedFirstReturnIndex_eq_find w hex] at hw
  intro i hi
  exact Nat.find_min hex (lt_of_le_of_lt (Finset.mem_Iic.mp hi) (by omega))

private theorem feedbackMarkedFirstReturnIndex_grid_tail {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackMarkedTrajectory lam hlam0 hlam 0
      {w | 4 * ((n : ℝ) + 1) < (feedbackMarkedFirstReturnIndex w : ℝ)} ≤
      ENNReal.ofReal (2 + lam) * ENNReal.ofReal (feedbackCellTailRatio lam) ^ n := by
  apply ((measure_mono (fun w hw ↦ ?_)).trans
    (feedbackMarkedFirstReturnIndex_tail hlam0 hlam n)).trans
  · gcongr
    · linarith
    · exact le_max_left _ _
  · have hn : (n : ℝ) + 1 < (feedbackMarkedFirstReturnIndex w : ℝ) := by
      change 4 * ((n : ℝ) + 1) < (feedbackMarkedFirstReturnIndex w : ℝ) at hw
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact_mod_cast hn

/-- The actual real cell length retains the geometric physical-clock tail. -/
theorem feedbackCellLength_grid_tail {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackMarkedTrajectory lam hlam0 hlam 0
      {w | 4 * ((n : ℝ) + 1) < feedbackCellLength w} ≤
      ENNReal.ofReal (2 + lam) * ENNReal.ofReal (feedbackCellTailRatio lam) ^ n := by
  have h := feedbackReturnLength_tail hlam0 hlam n
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0,
    Measure.map_apply measurable_feedbackMarkedTrajectoryProjection (by measurability)] at h
  apply ((measure_mono (fun w hw ↦ ?_)).trans h).trans
  · calc
      _ ≤ ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackCellTailRatio lam) ^ n +
          1 * ENNReal.ofReal (feedbackCellTailRatio lam) ^ n := by
        apply add_le_add
        · gcongr
          exact le_max_left _ _
        · rw [pow_succ']
          apply mul_le_mul'
          · exact feedbackClockTailRatio_lt_one.le
          · exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) n
      _ = _ := by
        rw [← add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) (by norm_num)]
        congr 2
        ring
  · change ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) <
      feedbackReturnLength (feedbackMarkedTrajectoryProjection w)
    change 4 * ((n : ℝ) + 1) <
      (feedbackReturnLength (feedbackMarkedTrajectoryProjection w)).toReal at hw
    have hn : feedbackReturnLength (feedbackMarkedTrajectoryProjection w) ≠ ∞ := by
      intro hn
      rw [hn, ENNReal.toReal_top] at hw
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hn]
    simpa only [Nat.cast_add, Nat.cast_one] using hw

/-- The actual first-return event count has a positive exponential moment. -/
theorem feedbackMarkedFirstReturnIndex_exp_integrable {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    Integrable (fun w ↦ Real.exp (feedbackCellExpRate lam *
      (feedbackMarkedFirstReturnIndex w : ℝ))) (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  exact integrable_exp_of_geometric_grid _
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      measurable_feedbackMarkedFirstReturnIndex) (by norm_num : (0 : ℝ) < 4)
    (feedbackCellExpRate_pos hlam0 hlam).le (feedbackCellTailRatio_pos hlam0 hlam).le
    (feedbackCellExpRate_contract hlam0 hlam) (feedbackMarkedFirstReturnIndex_grid_tail hlam0 hlam)

/-- The full physical cell duration, including its initial zero hold, has a positive exponential moment. -/
theorem feedbackCellLength_exp_integrable {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    Integrable (fun w ↦ Real.exp (feedbackCellExpRate lam * feedbackCellLength w))
      (feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  integrable_exp_of_geometric_grid _ measurable_feedbackCellLength (by norm_num : (0 : ℝ) < 4)
    (feedbackCellExpRate_pos hlam0 hlam).le (feedbackCellTailRatio_pos hlam0 hlam).le
    (feedbackCellExpRate_contract hlam0 hlam) (feedbackCellLength_grid_tail hlam0 hlam)

/-- A common strictly positive exponential moment for the actual return count and duration. -/
theorem feedbackCell_exponential_moments {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∃ theta : ℝ, 0 < theta ∧
      Integrable (fun w ↦ Real.exp (theta * (feedbackMarkedFirstReturnIndex w : ℝ)))
        (feedbackMarkedTrajectory lam hlam0 hlam 0) ∧
      Integrable (fun w ↦ Real.exp (theta * feedbackCellLength w))
        (feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  ⟨feedbackCellExpRate lam, feedbackCellExpRate_pos hlam0 hlam,
    feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam,
    feedbackCellLength_exp_integrable hlam0 hlam⟩

/-- The earlier survival-indicator count is the literal marked first-return index almost surely. -/
theorem feedbackReturnJumpCount_eq_markedFirstReturnIndex {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      feedbackReturnJumpCount (feedbackMarkedTrajectoryProjection w) =
        (feedbackMarkedFirstReturnIndex w : ℝ≥0∞) := by
  filter_upwards [feedbackMarkedTrajectory_returns_zero hlam0 hlam] with w hw
  obtain ⟨i, hi, hz⟩ := hw
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have hex : ∃ j, (w (j + 1)).2.2 = 0 := ⟨j, hz⟩
  rw [feedbackMarkedFirstReturnIndex_eq_find w hex]
  exact feedbackReturnJumpCount_eq_first (feedbackMarkedTrajectoryProjection w) hex

/-- The original actual jump-count observable has the same positive exponential moment. -/
theorem feedbackReturnJumpCount_exp_integrable {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    Integrable (fun w ↦ Real.exp (feedbackCellExpRate lam *
      (feedbackReturnJumpCount (feedbackMarkedTrajectoryProjection w)).toReal))
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  apply (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam).congr
  filter_upwards [feedbackReturnJumpCount_eq_markedFirstReturnIndex hlam0 hlam] with w hw
  simp only [hw, ENNReal.toReal_natCast]

end OTSelector.Limit
