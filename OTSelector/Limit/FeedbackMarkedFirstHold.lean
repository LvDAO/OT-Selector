import OTSelector.Limit.FeedbackMarkedRestart

/-!
# The initial zero hold is independent of the remaining marked path

The actual first step is sampled from an exponential law times the marked jump law. Its full
continuation depends only on the resulting current. The resulting factorization separates the
first wait from every later wait, every jump mark, and every visited current simultaneously.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory

namespace OTSelector.Limit

/-- Continue after a marked jump using only its resulting current. -/
noncomputable def feedbackMarkedAfterJumpKernel (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Kernel (UnitMark × ℤ) (ℕ → FeedbackMarkedStep) where
  toFun z := feedbackMarkedTrajectory lam hlam0 hlam z.2
  measurable' := (measurable_of_countable (feedbackMarkedTrajectory lam hlam0 hlam)).comp measurable_snd

instance feedbackMarkedAfterJumpKernel_isMarkov (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackMarkedAfterJumpKernel lam hlam0 hlam) := by
  constructor
  intro z
  change IsProbabilityMeasure (feedbackMarkedTrajectory lam hlam0 hlam z.2)
  infer_instance

private theorem prod_compProd_assoc {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (κ : Kernel B C) [IsSFiniteKernel κ] :
    ((μ.prod ν) ⊗ₘ Kernel.prodMkLeft A κ).map MeasurableEquiv.prodAssoc = μ.prod (ν ⊗ₘ κ) := by
  have hk : (Kernel.const A ν) ⊗ₖ (Kernel.prodMkLeft A κ) = Kernel.const A (ν ⊗ₘ κ) := by
    ext a s hs
    rw [Kernel.compProd_apply hs]
    simp only [Kernel.const_apply, Kernel.prodMkLeft_apply]
    rw [Measure.compProd_apply hs]
  rw [← Measure.compProd_const (μ := μ) (ν := ν), Measure.compProd_assoc', hk,
    Measure.compProd_const]

/-- The first marked jump and its complete continuation have the actual conditional product law. -/
theorem feedbackMarkedTrajectory_first_step_restart (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ (w 1, feedbackMarkedRestart 1 w)) =
      feedbackMarkedHoldingKernel lam k ⊗ₘ
        Kernel.prodMkLeft ℝ (feedbackMarkedAfterJumpKernel lam hlam0 hlam) := by
  let f : ((i : Finset.Iic 1) → FeedbackMarkedStep) → FeedbackMarkedStep :=
    fun x ↦ x ⟨1, by simp⟩
  have hf : Measurable f := measurable_pi_apply _
  have h := TrajectoryProjection.map_compProd
    ((feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe 1))
    (feedbackMarkedRestartKernel lam hlam0 hlam 1)
    (Kernel.prodMkLeft ℝ (feedbackMarkedAfterJumpKernel lam hlam0 hlam)) hf measurable_id
    (fun x ↦ by rw [Measure.map_id]; rfl)
  rw [← feedbackMarkedTrajectory_history_restart,
    Measure.map_map (hf.prodMap measurable_id) (by fun_prop),
    Measure.map_map hf (measurable_frestrictLe 1)] at h
  change (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ (w 1, feedbackMarkedRestart 1 w)) =
    (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ w 1) ⊗ₘ _ at h
  rwa [feedbackMarkedTrajectory_map_one] at h

/-- The first wait is independent of the first mark/current and the full restarted continuation. -/
theorem feedbackMarkedTrajectory_first_wait_product (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map
      (fun w ↦ ((w 1).1, (w 1).2, feedbackMarkedRestart 1 w)) =
      (expMeasure (totalJumpRate lam k)).prod
        (feedbackMarkedJumpKernel lam k ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam) := by
  let := feedbackHoldingKernel_isMarkov hlam0 hlam
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  have hfun : (fun w : ℕ → FeedbackMarkedStep ↦ ((w 1).1, (w 1).2, feedbackMarkedRestart 1 w)) =
      MeasurableEquiv.prodAssoc ∘ (fun w ↦ (w 1, feedbackMarkedRestart 1 w)) := rfl
  rw [hfun, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
    feedbackMarkedTrajectory_first_step_restart]
  exact prod_compProd_assoc (feedbackHoldingKernel lam k) (feedbackMarkedJumpKernel lam k)
    (feedbackMarkedAfterJumpKernel lam hlam0 hlam)

/-- Reconstruct all meaningful path data except the first holding time. -/
def feedbackMarkedRemainderAssemble (p : (UnitMark × ℤ) × (ℕ → FeedbackMarkedStep)) :
    ℕ → FeedbackMarkedStep
  | 0 => feedbackMarkedVirtual 0
  | 1 => (0, p.1)
  | n + 2 => p.2 (n + 1)

@[fun_prop]
theorem measurable_feedbackMarkedRemainderAssemble : Measurable feedbackMarkedRemainderAssemble := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => cases n <;> dsimp [feedbackMarkedRemainderAssemble] <;> fun_prop

/-- Replace only the initial hold by zero, retaining all jump marks/currents and all later waits.
The virtual coordinate zero is fixed to the zero-start state. -/
def feedbackMarkedWithoutFirstWait (w : ℕ → FeedbackMarkedStep) : ℕ → FeedbackMarkedStep :=
  feedbackMarkedRemainderAssemble ((w 1).2, feedbackMarkedRestart 1 w)

@[fun_prop]
theorem measurable_feedbackMarkedWithoutFirstWait : Measurable feedbackMarkedWithoutFirstWait := by
  exact measurable_feedbackMarkedRemainderAssemble.comp
    (((measurable_pi_apply 1).snd).prodMk (measurable_feedbackMarkedRestart 1))

@[simp]
theorem feedbackMarkedWithoutFirstWait_one (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedWithoutFirstWait w 1 = (0, (w 1).2) := rfl

@[simp]
theorem feedbackMarkedWithoutFirstWait_add_two (w : ℕ → FeedbackMarkedStep) (n : ℕ) :
    feedbackMarkedWithoutFirstWait w (n + 2) = w (n + 2) := by
  simp [feedbackMarkedWithoutFirstWait, feedbackMarkedRemainderAssemble,
    feedbackMarkedRestart, Nat.add_left_comm]

/-- The actual first zero hold is exponential of rate two and independent of the entire remaining path. -/
theorem feedbackMarkedTrajectory_zero_hold_remainder_product (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map
      (fun w ↦ ((w 1).1, feedbackMarkedWithoutFirstWait w)) =
    (expMeasure 2).prod ((feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackMarkedWithoutFirstWait) := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  let := isProbabilityMeasure_expMeasure (totalJumpRate_pos hlam0 hlam 0)
  let ν := feedbackMarkedJumpKernel lam 0 ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam
  have h := congrArg (fun μ : Measure (ℝ × (UnitMark × ℤ) × (ℕ → FeedbackMarkedStep)) ↦
      μ.map (Prod.map id feedbackMarkedRemainderAssemble))
    (feedbackMarkedTrajectory_first_wait_product lam hlam0 hlam 0)
  rw [Measure.map_map (measurable_id.prodMap measurable_feedbackMarkedRemainderAssemble)
    (by fun_prop), ← Measure.map_prod_map _ _ measurable_id measurable_feedbackMarkedRemainderAssemble,
    Measure.map_id, totalJumpRate_zero] at h
  change (feedbackMarkedTrajectory lam hlam0 hlam 0).map
      (fun w ↦ ((w 1).1, feedbackMarkedWithoutFirstWait w)) =
    (expMeasure 2).prod (ν.map feedbackMarkedRemainderAssemble) at h
  have hm := congrArg (fun μ : Measure (ℝ × (ℕ → FeedbackMarkedStep)) ↦ μ.map Prod.snd) h
  rw [Measure.map_map measurable_snd (by fun_prop)] at hm
  let := isProbabilityMeasure_expMeasure (show (0 : ℝ) < 2 by norm_num)
  have hm' : (feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackMarkedWithoutFirstWait =
      ν.map feedbackMarkedRemainderAssemble := by simpa [Function.comp_def] using hm
  rwa [← hm'] at h

/-- Removing the first wait leaves every positive-index current unchanged. -/
theorem feedbackMarkedWithoutFirstWait_current (w : ℕ → FeedbackMarkedStep) (n : ℕ) :
    (feedbackMarkedWithoutFirstWait w (n + 1)).2.2 = (w (n + 1)).2.2 := by
  cases n with
  | zero => rfl
  | succ n => simp [feedbackMarkedWithoutFirstWait_add_two]

/-- The first return cell ends at the same index after its initial hold is removed. -/
theorem feedbackMarkedWithoutFirstWait_returnIndex (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedFirstReturnIndex (feedbackMarkedWithoutFirstWait w) = feedbackMarkedFirstReturnIndex w := by
  cases hτ : feedbackMarkedFirstReturnIndex w with
  | zero =>
      rw [feedbackMarkedFirstReturnIndex_eq_zero_iff]
      simpa only [feedbackMarkedWithoutFirstWait_current] using
        (feedbackMarkedFirstReturnIndex_eq_zero_iff w).mp hτ
  | succ n =>
      apply (feedbackMarkedFirstReturnIndex_eq_succ_iff _ n).mpr
      simpa only [feedbackMarkedWithoutFirstWait_current] using
        (feedbackMarkedFirstReturnIndex_eq_succ_iff w n).mp hτ

/-- The actual initial holding time at zero has the exponential law of rate two. -/
theorem feedbackMarkedTrajectory_zero_hold_law (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map (fun w ↦ (w 1).1) = expMeasure 2 := by
  have h := congrArg (fun μ : Measure (ℝ × (ℕ → FeedbackMarkedStep)) ↦ μ.map Prod.fst)
    (feedbackMarkedTrajectory_zero_hold_remainder_product lam hlam0 hlam)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  let := Measure.isProbabilityMeasure_map
    (μ := feedbackMarkedTrajectory lam hlam0 hlam 0) measurable_feedbackMarkedWithoutFirstWait.aemeasurable
  simpa [Function.comp_def] using h

/-- The first zero hold is independent of all remaining waits, marks and currents. -/
theorem feedbackMarkedTrajectory_zero_hold_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun (fun w : ℕ → FeedbackMarkedStep ↦ (w 1).1) feedbackMarkedWithoutFirstWait
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  have hf : Measurable (fun w : ℕ → FeedbackMarkedStep ↦ (w 1).1) := by fun_prop
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable
    measurable_feedbackMarkedWithoutFirstWait.aemeasurable).mpr
  rw [feedbackMarkedTrajectory_zero_hold_law]
  exact feedbackMarkedTrajectory_zero_hold_remainder_product lam hlam0 hlam

/-- In particular, the initial zero hold is independent of the rest of its entire first return cell. -/
theorem feedbackMarkedTrajectory_zero_hold_cell_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun (fun w : ℕ → FeedbackMarkedStep ↦ (w 1).1)
      (fun w ↦ feedbackMarkedFirstCell (feedbackMarkedWithoutFirstWait w))
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  exact (feedbackMarkedTrajectory_zero_hold_indep lam hlam0 hlam).comp
    measurable_id measurable_feedbackMarkedFirstCell

end OTSelector.Limit
