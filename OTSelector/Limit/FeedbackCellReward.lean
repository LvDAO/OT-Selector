import OTSelector.Limit.FeedbackCellExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Idle-free rewards of actual return cells

The excursion duration excludes the first zero-state hold. It is measurable from the remaining
marked path, has a positive exponential moment, and gives the cubic reward `C N E²` its
stretched-exponential tail under the actual cell law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Actual excursion duration after removing the initial zero-state hold. -/
noncomputable def feedbackCellExcursionLength (w : FeedbackCellPath) : ℝ :=
  (feedbackExcursionLength (feedbackMarkedTrajectoryProjection w)).toReal

@[fun_prop]
theorem measurable_feedbackCellExcursionLength : Measurable feedbackCellExcursionLength :=
  (measurable_feedbackExcursionLength.comp measurable_feedbackMarkedTrajectoryProjection).ennreal_toReal

theorem feedbackCellExcursionLength_nonneg (w : FeedbackCellPath) :
    0 ≤ feedbackCellExcursionLength w := ENNReal.toReal_nonneg

/-- Removing the first wait preserves the whole excursion-duration observable. -/
theorem feedbackCellExcursionLength_withoutFirstWait (w : FeedbackCellPath) :
    feedbackCellExcursionLength (feedbackMarkedWithoutFirstWait w) =
      feedbackCellExcursionLength w := by
  have hc : feedbackPostInitialCurrent
      (feedbackMarkedTrajectoryProjection (feedbackMarkedWithoutFirstWait w)) =
      feedbackPostInitialCurrent (feedbackMarkedTrajectoryProjection w) := by
    funext n
    exact feedbackMarkedWithoutFirstWait_current w n
  unfold feedbackCellExcursionLength feedbackExcursionLength
  congr 1
  apply tsum_congr
  intro n
  simp only [Set.indicator, Set.mem_ofPred_eq, hc,
    feedbackMarkedTrajectoryProjection, feedbackMarkedStepProjection,
    feedbackMarkedWithoutFirstWait_add_two]

/-- The excursion is the full actual cell duration minus its initial zero hold. -/
theorem feedbackCellLength_eq_hold_add_excursion {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      feedbackCellLength w = (w 1).1 + feedbackCellExcursionLength w := by
  have hf := feedbackReturnLength_finite hlam0 hlam
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0] at hf
  have hf' := ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable hf
  filter_upwards [hf', feedbackMarkedTrajectory_waits_positive hlam0 hlam 0] with w hfin hw
  have he : feedbackExcursionLength (feedbackMarkedTrajectoryProjection w) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (feedbackExcursionLength_le_returnLength _)
  unfold feedbackCellLength feedbackReturnLength feedbackCellExcursionLength
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top he]
  change (ENNReal.ofReal (w 1).1).toReal + _ = _
  rw [ENNReal.toReal_ofReal (hw 0).le]

theorem feedbackCellExcursionLength_le_length {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      feedbackCellExcursionLength w ≤ feedbackCellLength w := by
  filter_upwards [feedbackCellLength_eq_hold_add_excursion hlam0 hlam,
    feedbackMarkedTrajectory_waits_positive hlam0 hlam 0] with w he hw
  rw [he]
  exact le_add_of_nonneg_left (hw 0).le

/-- The idle-free excursion has the same positive exponential-moment parameter as the full cell. -/
theorem feedbackCellExcursionLength_exp_integrable {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    Integrable (fun w ↦ Real.exp (feedbackCellExpRate lam * feedbackCellExcursionLength w))
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  apply (feedbackCellLength_exp_integrable hlam0 hlam).mono'
    (measurable_feedbackCellExcursionLength.const_mul _ |>.exp.aestronglyMeasurable)
  filter_upwards [feedbackCellExcursionLength_le_length hlam0 hlam] with w hw
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw (feedbackCellExpRate_pos hlam0 hlam).le)

/-- Cubic comparison-reward envelope; `C` is the deterministic graph-cost coefficient. -/
noncomputable def feedbackCellReward (C : ℝ) (w : FeedbackCellPath) : ℝ :=
  C * (feedbackMarkedFirstReturnIndex w : ℝ) * feedbackCellExcursionLength w ^ 2

@[fun_prop]
theorem measurable_feedbackCellReward (C : ℝ) : Measurable (feedbackCellReward C) := by
  unfold feedbackCellReward
  exact (measurable_const.mul ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
    measurable_feedbackMarkedFirstReturnIndex)).mul (measurable_feedbackCellExcursionLength.pow_const 2)

theorem feedbackCellReward_nonneg {C : ℝ} (hC : 0 ≤ C) (w : FeedbackCellPath) :
    0 ≤ feedbackCellReward C w := by
  unfold feedbackCellReward
  positivity

theorem feedbackCellReward_withoutFirstWait (C : ℝ) (w : FeedbackCellPath) :
    feedbackCellReward C (feedbackMarkedWithoutFirstWait w) = feedbackCellReward C w := by
  rw [feedbackCellReward, feedbackMarkedWithoutFirstWait_returnIndex,
    feedbackCellExcursionLength_withoutFirstWait]
  rfl

/-- The reward depends only on excursion data and is independent of its initial zero hold. -/
theorem feedbackCellReward_zero_hold_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    IndepFun (fun w : FeedbackCellPath ↦ (w 1).1) (feedbackCellReward C)
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have h := (feedbackMarkedTrajectory_zero_hold_indep lam hlam0 hlam).comp
    measurable_id (measurable_feedbackCellReward C)
  simpa only [Function.comp_def, id_eq, feedbackCellReward_withoutFirstWait] using h

/-- Rewards read from the actual two-sided cell base form an independent identically distributed field. -/
theorem feedbackCellReward_field_law (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    (feedbackCellBase lam hlam0 hlam).map (fun ω j ↦ feedbackCellReward C (ω j)) =
      Measure.infinitePi (fun _ : ℤ ↦
        (feedbackMarkedTrajectory lam hlam0 hlam 0).map (feedbackCellReward C)) :=
  Measure.infinitePi_map_pi _ (fun _ ↦ measurable_feedbackCellReward C)

theorem feedbackCellReward_iIndep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    iIndepFun (fun j (ω : FeedbackCellSequence) ↦ feedbackCellReward C (ω j))
      (feedbackCellBase lam hlam0 hlam) :=
  iIndepFun_infinitePi (X := fun _ ↦ feedbackCellReward C) (fun _ ↦ measurable_feedbackCellReward C)

/-- Sum of the actual count and excursion exponential moments, a finite tail prefactor. -/
noncomputable def feedbackCellRewardTailConstant (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : ℝ :=
  mgf (fun w : FeedbackCellPath ↦ (feedbackMarkedFirstReturnIndex w : ℝ))
    (feedbackMarkedTrajectory lam hlam0 hlam 0) (feedbackCellExpRate lam) +
  mgf feedbackCellExcursionLength (feedbackMarkedTrajectory lam hlam0 hlam 0) (feedbackCellExpRate lam)

/-- A cubic threshold reduces to two actual exponential tails. -/
theorem feedbackCellReward_cubic_tail {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) (x : ℝ) (hx : 0 ≤ x) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).real {w | C * x ^ 3 < feedbackCellReward C w} ≤
      feedbackCellRewardTailConstant lam hlam0 hlam * Real.exp (-feedbackCellExpRate lam * x) := by
  let μ := feedbackMarkedTrajectory lam hlam0 hlam 0
  calc
    _ ≤ μ.real ({w | x ≤ (feedbackMarkedFirstReturnIndex w : ℝ)} ∪
        {w | x ≤ feedbackCellExcursionLength w}) := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro w hw
      by_contra hn
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
      have hbound : feedbackCellReward C w ≤ C * x ^ 3 := by
        calc
          _ ≤ C * x * x ^ 2 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hn.1.le hC
            · exact pow_le_pow_left₀ (feedbackCellExcursionLength_nonneg w) hn.2.le 2
            · positivity
            · positivity
          _ = _ := by ring
      exact not_lt_of_ge hbound hw
    _ ≤ μ.real {w | x ≤ (feedbackMarkedFirstReturnIndex w : ℝ)} +
        μ.real {w | x ≤ feedbackCellExcursionLength w} := measureReal_union_le _ _
    _ ≤ Real.exp (-feedbackCellExpRate lam * x) *
        mgf (fun w : FeedbackCellPath ↦ (feedbackMarkedFirstReturnIndex w : ℝ)) μ
          (feedbackCellExpRate lam) +
        Real.exp (-feedbackCellExpRate lam * x) *
          mgf feedbackCellExcursionLength μ (feedbackCellExpRate lam) := by
      exact add_le_add
        (measure_ge_le_exp_mul_mgf x (feedbackCellExpRate_pos hlam0 hlam).le
          (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam))
        (measure_ge_le_exp_mul_mgf x (feedbackCellExpRate_pos hlam0 hlam).le
          (feedbackCellExcursionLength_exp_integrable hlam0 hlam))
    _ = _ := by unfold feedbackCellRewardTailConstant; dsimp [μ]; ring

/-- The true cell reward has a stretched-exponential tail with exponent one third. -/
theorem feedbackCellReward_stretched_tail {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) (t : ℝ) (ht : 0 ≤ t) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).real {w | t < feedbackCellReward C w} ≤
      feedbackCellRewardTailConstant lam hlam0 hlam *
        Real.exp (-(feedbackCellExpRate lam / max 1 C) * t ^ (1 / 3 : ℝ)) := by
  let D : ℝ := max 1 C
  let x : ℝ := t ^ (1 / 3 : ℝ) / D
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hx : 0 ≤ x := div_nonneg (Real.rpow_nonneg ht _) hD.le
  have hcube : (t ^ (1 / 3 : ℝ)) ^ 3 = t := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow ht (by norm_num : (3 : ℕ) ≠ 0)
  have hDC : C ≤ D ^ 3 := by
    have hD1 : 1 ≤ D := le_max_left _ _
    have hCD : C ≤ D := le_max_right _ _
    nlinarith [sq_nonneg (D - 1)]
  have hthreshold : C * x ^ 3 ≤ t := by
    calc
      _ ≤ D ^ 3 * x ^ 3 := mul_le_mul_of_nonneg_right hDC (pow_nonneg hx _)
      _ = (D * x) ^ 3 := (mul_pow _ _ _).symm
      _ = t := by
        dsimp [x]
        rw [mul_div_cancel₀ _ hD.ne', hcube]
  apply (measureReal_mono (fun w hw ↦ lt_of_le_of_lt hthreshold hw)).trans
    ((feedbackCellReward_cubic_tail hlam0 hlam hC x hx).trans_eq ?_)
  congr 2
  dsimp [x, D]
  ring

theorem feedbackCellRewardTailConstant_pos {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : 0 < feedbackCellRewardTailConstant lam hlam0 hlam :=
  add_pos (mgf_pos (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam))
    (mgf_pos (feedbackCellExcursionLength_exp_integrable hlam0 hlam))

/-- Positive finite constants in the usual stretched-exponential formulation. -/
theorem feedbackCellReward_exists_stretched_tail {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      (feedbackMarkedTrajectory lam hlam0 hlam 0).real {w | t < feedbackCellReward C w} ≤
        K * Real.exp (-c * t ^ (1 / 3 : ℝ)) := by
  refine ⟨feedbackCellRewardTailConstant lam hlam0 hlam, feedbackCellExpRate lam / max 1 C,
    feedbackCellRewardTailConstant_pos hlam0 hlam, ?_,
    feedbackCellReward_stretched_tail hlam0 hlam hC⟩
  exact div_pos (feedbackCellExpRate_pos hlam0 hlam)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

/-- Independence inside each iid row lifts to independence of the two entire coordinate fields. -/
theorem indepFun_fields_infinitePi {ι Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → A} {g : Ω → B} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) :
    IndepFun (fun ω : ι → Ω ↦ fun i ↦ f (ω i)) (fun ω ↦ fun i ↦ g (ω i))
      (Measure.infinitePi (fun _ : ι ↦ μ)) := by
  classical
  let Q := Measure.infinitePi (fun _ : ι ↦ μ)
  let μf := μ.map f
  let μg := μ.map g
  let : IsProbabilityMeasure μf := Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure μg := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hfinite (S : Finset ι) :
      IndepFun (fun ω : ι → Ω ↦ fun i : S ↦ f (ω i))
        (fun ω ↦ fun i : S ↦ g (ω i)) Q := by
    have hind := (iIndepFun_infinitePi (P := fun _ : ι ↦ μ)
      (X := fun _ ↦ fun w ↦ (f w, g w)) (fun _ ↦ hf.prodMk hg)).restrict S
    change iIndepFun (fun (i : S) (ω : ι → Ω) ↦ (f (ω i), g (ω i))) Q at hind
    have hm (i : S) : AEMeasurable (fun ω : ι → Ω ↦ (f (ω i), g (ω i))) Q :=
      ((hf.prodMk hg).comp (measurable_pi_apply (i : ι))).aemeasurable
    have hmap := hind.map_fun_eq_pi_map hm
    have hrow (i : S) : Q.map (fun ω ↦ (f (ω i), g (ω i))) = μf.prod μg := by
      rw [show (fun ω : ι → Ω ↦ (f (ω i), g (ω i))) =
          (fun w ↦ (f w, g w)) ∘ (fun ω ↦ ω (i : ι)) from rfl,
        ← Measure.map_map (hf.prodMk hg) (measurable_pi_apply _),
        Measure.infinitePi_map_eval]
      exact hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
    change Q.map (fun ω (i : S) ↦ (f (ω i), g (ω i))) =
      Measure.pi (fun i : S ↦ Q.map (fun ω ↦ (f (ω i), g (ω i)))) at hmap
    simp_rw [hrow] at hmap
    have hp := congrArg (fun ν : Measure (S → A × B) ↦
      ν.map (MeasurableEquiv.arrowProdEquivProdArrow A B S)) hmap
    rw [Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
      (measurePreserving_arrowProdEquivProdArrow A B S (fun _ ↦ μf) (fun _ ↦ μg)).map_eq] at hp
    change Q.map (fun ω ↦ ((fun i : S ↦ f (ω i)), (fun i : S ↦ g (ω i)))) =
      (Measure.pi (fun _ : S ↦ μf)).prod (Measure.pi (fun _ : S ↦ μg)) at hp
    have hl := congrArg (fun ν : Measure ((S → A) × (S → B)) ↦ ν.map Prod.fst) hp
    have hr := congrArg (fun ν : Measure ((S → A) × (S → B)) ↦ ν.map Prod.snd) hp
    rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at hl
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod] at hr
    simp only [measure_univ, one_smul, Function.comp_def] at hl hr
    apply (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_lambda _ fun i : S ↦ hf.comp (measurable_pi_apply (i : ι))).aemeasurable
      (measurable_pi_lambda _ fun i : S ↦ hg.comp (measurable_pi_apply (i : ι))).aemeasurable).mpr
    simp only [Function.comp_def]
    rw [hl, hr]
    exact hp
  apply IndepFun.process_indepFun_process
    (fun i ↦ hf.comp (measurable_pi_apply i)) (fun i ↦ hg.comp (measurable_pi_apply i))
  intro I J
  have h := (hfinite (I ∪ J)).comp
    (show Measurable (fun v : ↥(I ∪ J) → A ↦ fun i : I ↦
      v ⟨i, Finset.mem_union_left J i.2⟩) from by fun_prop)
    (show Measurable (fun v : ↥(I ∪ J) → B ↦ fun i : J ↦
      v ⟨i, Finset.mem_union_right I i.2⟩) from by fun_prop)
  exact h

/-- All actual initial zero holds are independent of the entire remaining marked-path field. -/
theorem feedbackCellBase_hold_excursion_fields_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun (fun ω : FeedbackCellSequence ↦ fun j ↦ (ω j 1).1)
      (fun ω ↦ fun j ↦ feedbackMarkedWithoutFirstWait (ω j))
      (feedbackCellBase lam hlam0 hlam) :=
  indepFun_fields_infinitePi _ (by fun_prop) measurable_feedbackMarkedWithoutFirstWait
    (feedbackMarkedTrajectory_zero_hold_indep lam hlam0 hlam)

/-- Every idle-free reward is independent of the entire zero-hold field simultaneously. -/
theorem feedbackCellReward_zero_hold_fields_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (C : ℝ) :
    IndepFun (fun ω : FeedbackCellSequence ↦ fun j ↦ (ω j 1).1)
      (fun ω ↦ fun j ↦ feedbackCellReward C (ω j)) (feedbackCellBase lam hlam0 hlam) :=
  indepFun_fields_infinitePi _ (by fun_prop) (measurable_feedbackCellReward C)
    (feedbackCellReward_zero_hold_indep lam hlam0 hlam C)

/-- The zero-hold field has the actual iid rate-two exponential law. -/
theorem feedbackCellBase_zero_hold_field_law (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackCellBase lam hlam0 hlam).map (fun ω j ↦ (ω j 1).1) =
      Measure.infinitePi (fun _ : ℤ ↦ expMeasure 2) := by
  have hf : Measurable (fun w : FeedbackCellPath ↦ (w 1).1) := by fun_prop
  simpa only [feedbackCellBase, feedbackMarkedTrajectory_zero_hold_law lam hlam0 hlam] using
    Measure.infinitePi_map_pi (fun _ : ℤ ↦ feedbackMarkedTrajectory lam hlam0 hlam 0)
      (fun _ ↦ hf)

private theorem integrable_pow_of_nonneg_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX0 : ∀ w, 0 ≤ X w) {theta : ℝ} (htheta : 0 < theta)
    (hI : Integrable (fun w ↦ Real.exp (theta * X w)) μ) (p : ℕ) :
    Integrable (fun w ↦ X w ^ p) μ := by
  have hneg : Integrable (fun w ↦ Real.exp (-theta * X w)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hX.const_mul _ |>.exp.aestronglyMeasurable)
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta.le) (hX0 w))
  exact integrable_pow_of_integrable_exp_mul htheta.ne' hI hneg p

/-- The actual idle-free comparison envelope is integrable, as needed by renewal rewards. -/
theorem integrable_feedbackCellReward {lam C : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hC : 0 ≤ C) :
    Integrable (feedbackCellReward C) (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have hN := integrable_pow_of_nonneg_exp (feedbackMarkedTrajectory lam hlam0 hlam 0)
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp measurable_feedbackMarkedFirstReturnIndex)
    (fun w ↦ Nat.cast_nonneg (feedbackMarkedFirstReturnIndex w))
    (feedbackCellExpRate_pos hlam0 hlam) (feedbackMarkedFirstReturnIndex_exp_integrable hlam0 hlam) 3
  have hE := integrable_pow_of_nonneg_exp (feedbackMarkedTrajectory lam hlam0 hlam 0)
    measurable_feedbackCellExcursionLength feedbackCellExcursionLength_nonneg
    (feedbackCellExpRate_pos hlam0 hlam) (feedbackCellExcursionLength_exp_integrable hlam0 hlam) 3
  apply ((hN.add hE).const_mul C).mono' (measurable_feedbackCellReward C).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (feedbackCellReward_nonneg hC w)]
  change C * (feedbackMarkedFirstReturnIndex w : ℝ) * feedbackCellExcursionLength w ^ 2 ≤
    C * ((feedbackMarkedFirstReturnIndex w : ℝ) ^ 3 + feedbackCellExcursionLength w ^ 3)
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  have hN0 : 0 ≤ (feedbackMarkedFirstReturnIndex w : ℝ) := Nat.cast_nonneg _
  have hE0 := feedbackCellExcursionLength_nonneg w
  by_cases h : (feedbackMarkedFirstReturnIndex w : ℝ) ≤ feedbackCellExcursionLength w
  · calc
      _ ≤ feedbackCellExcursionLength w * feedbackCellExcursionLength w ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = feedbackCellExcursionLength w ^ 3 := by ring
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg hN0 _)
  · calc
      _ ≤ (feedbackMarkedFirstReturnIndex w : ℝ) * (feedbackMarkedFirstReturnIndex w : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE0 (le_of_not_ge h) 2) hN0
      _ = (feedbackMarkedFirstReturnIndex w : ℝ) ^ 3 := by ring
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hE0 _)

end OTSelector.Limit
