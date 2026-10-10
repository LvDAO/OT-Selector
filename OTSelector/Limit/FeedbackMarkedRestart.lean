import OTSelector.Limit.FeedbackMarkedTrajectory

/-!
# Restart of the actual marked feedback process

Restart retains the current at the cutting index, but replaces coordinate zero by a virtual
zero wait and zero mark. Thus the arrival wait at the cut belongs only to the preceding cell.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- A virtual initial coordinate contains no arrival wait or arrival mark. -/
def feedbackMarkedVirtual (k : ℤ) : FeedbackMarkedStep := (0, ⟨0, by simp⟩, k)

/-- Restart just after coordinate `n`, retaining its current as the new virtual initial state. -/
def feedbackMarkedRestart (n : ℕ) (w : ℕ → FeedbackMarkedStep) (m : ℕ) : FeedbackMarkedStep :=
  if m = 0 then feedbackMarkedVirtual (w n).2.2 else w (n + m)

@[fun_prop]
theorem measurable_feedbackMarkedRestart (n : ℕ) : Measurable (feedbackMarkedRestart n) := by
  apply measurable_pi_lambda
  intro m
  by_cases h : m = 0 <;> simp only [feedbackMarkedRestart, h, ↓reduceIte]
  · unfold feedbackMarkedVirtual
    fun_prop
  · fun_prop

@[simp]
theorem feedbackMarkedRestart_zero (n : ℕ) (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedRestart n w 0 = feedbackMarkedVirtual (w n).2.2 := by
  simp [feedbackMarkedRestart]

@[simp]
theorem feedbackMarkedRestart_succ (n m : ℕ) (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedRestart n w (m + 1) = w (n + m + 1) := by
  simp [feedbackMarkedRestart, Nat.add_assoc]

/-- The same restart on finite histories. -/
def feedbackMarkedRestartHistory (n m : ℕ)
    (x : (i : Finset.Iic (n + m)) → FeedbackMarkedStep) (i : Finset.Iic m) : FeedbackMarkedStep :=
  if i.val = 0 then feedbackMarkedVirtual (x ⟨n, by simp⟩).2.2
    else x ⟨n + i.val, Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) n)⟩

@[fun_prop]
theorem measurable_feedbackMarkedRestartHistory (n m : ℕ) :
    Measurable (feedbackMarkedRestartHistory n m) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i.val = 0 <;> simp only [feedbackMarkedRestartHistory, h, ↓reduceIte]
  · unfold feedbackMarkedVirtual
    fun_prop
  · fun_prop

@[simp]
theorem feedbackMarkedRestartHistory_restrict (n m : ℕ) (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedRestartHistory n m (frestrictLe (n + m) w) =
      frestrictLe m (feedbackMarkedRestart n w) := rfl

@[simp]
theorem feedbackMarkedRestartHistory_current (n m : ℕ)
    (x : (i : Finset.Iic (n + m)) → FeedbackMarkedStep) :
    (feedbackMarkedRestartHistory n m x ⟨m, by simp⟩).2.2 =
      (x ⟨n + m, by simp⟩).2.2 := by
  by_cases h : m = 0
  · subst m
    simp [feedbackMarkedRestartHistory, feedbackMarkedVirtual]
  · simp [feedbackMarkedRestartHistory, h]

private theorem feedbackMarkedRestartHistory_snoc (n m : ℕ)
    (x : (i : Finset.Iic (n + m)) → FeedbackMarkedStep) (z : FeedbackMarkedStep) :
    feedbackMarkedRestartHistory n (m + 1)
      (TrajectoryProjection.snoc (n + m) (x, z)) =
    TrajectoryProjection.snoc m (feedbackMarkedRestartHistory n m x, z) := by
  funext i
  by_cases hi : i.val = 0
  · simp [feedbackMarkedRestartHistory, TrajectoryProjection.snoc, hi]
  · by_cases him : i.val ≤ m
    · simp [feedbackMarkedRestartHistory, TrajectoryProjection.snoc, hi, him,
        Nat.add_le_add_left him n]
    · simp [feedbackMarkedRestartHistory, TrajectoryProjection.snoc, hi, him,
        show ¬ n + i.val ≤ n + m by omega]

private theorem partialTraj_apply_succ (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n b : ℕ) (hnb : n ≤ b)
    (x : (i : Finset.Iic n) → FeedbackMarkedStep) :
    Kernel.partialTraj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n (b + 1) x =
      ((Kernel.partialTraj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n b x) ⊗ₘ
        feedbackMarkedHistoryKernel lam b).map (TrajectoryProjection.snoc b) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  rw [Kernel.partialTraj_compProd_eq_map_traj hnb,
    Measure.map_map (TrajectoryProjection.measurable_snoc b) (by fun_prop)]
  simp only [Function.comp_def, TrajectoryProjection.snoc_restrict]
  exact (Kernel.traj_map_frestrictLe_apply (X := fun _ ↦ FeedbackMarkedStep) n (b + 1) x).symm

/-- A trajectory started from a deterministic state is the corresponding row of the path kernel. -/
theorem feedbackMarkedTrajectory_eq_traj (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
    feedbackMarkedTrajectory lam hlam0 hlam k =
      Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) 0 (fun _ ↦ feedbackMarkedVirtual k) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackMarkedTrajectory Kernel.trajMeasure
  rw [Measure.map_dirac' (MeasurableEquiv.measurable _), Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Every restarted finite prefix has the real zero-wait initial law and the original transitions. -/
theorem feedbackMarkedRestartHistory_partialTraj (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n m : ℕ) (x : (i : Finset.Iic n) → FeedbackMarkedStep) :
    (Kernel.partialTraj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n (n + m) x).map
      (feedbackMarkedRestartHistory n m) =
    (feedbackMarkedTrajectory lam hlam0 hlam (x ⟨n, by simp⟩).2.2).map (frestrictLe m) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  induction m with
  | zero =>
      change (Kernel.partialTraj (X := fun _ ↦ FeedbackMarkedStep)
        (feedbackMarkedHistoryKernel lam) n n x).map (feedbackMarkedRestartHistory n 0) = _
      rw [Kernel.partialTraj_self (X := fun _ ↦ FeedbackMarkedStep), Kernel.id_apply,
        Measure.map_dirac' (measurable_feedbackMarkedRestartHistory n 0)]
      unfold feedbackMarkedTrajectory
      rw [TrajectoryProjection.trajMeasure_prefix_zero,
        Measure.map_dirac' (MeasurableEquiv.measurable _)]
      congr 1
      funext i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.2; omega
      simp [feedbackMarkedRestartHistory, hi, feedbackMarkedVirtual]
  | succ m ih =>
      change (Kernel.partialTraj (X := fun _ ↦ FeedbackMarkedStep)
        (feedbackMarkedHistoryKernel lam) n (n + m + 1) x).map
          (feedbackMarkedRestartHistory n (m + 1)) = _
      rw [partialTraj_apply_succ lam hlam0 hlam n (n + m) (by omega),
        Measure.map_map (measurable_feedbackMarkedRestartHistory n (m + 1))
          (TrajectoryProjection.measurable_snoc (n + m))]
      have hcomm : feedbackMarkedRestartHistory n (m + 1) ∘ TrajectoryProjection.snoc (n + m) =
          TrajectoryProjection.snoc m ∘ Prod.map (feedbackMarkedRestartHistory n m) id := by
        funext p
        exact feedbackMarkedRestartHistory_snoc n m p.1 p.2
      rw [hcomm, ← Measure.map_map (TrajectoryProjection.measurable_snoc m)
        ((measurable_feedbackMarkedRestartHistory n m).prodMap measurable_id),
        TrajectoryProjection.map_compProd _ _ (feedbackMarkedHistoryKernel lam m)
          (measurable_feedbackMarkedRestartHistory n m) measurable_id (fun y ↦ ?_), ih]
      · exact (TrajectoryProjection.trajMeasure_prefix_succ _ _ m).symm
      · rw [Measure.map_id]
        simp only [feedbackMarkedHistoryKernel, Kernel.comap_apply,
          feedbackMarkedRestartHistory_current]

/-- The entire future after a deterministic cut depends only on the current at that cut. -/
theorem feedbackMarkedRestart_map_traj (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) (x : (i : Finset.Iic n) → FeedbackMarkedStep) :
    let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
    (Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n x).map
      (feedbackMarkedRestart n) = feedbackMarkedTrajectory lam hlam0 hlam (x ⟨n, by simp⟩).2.2 := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  apply TrajectoryProjection.ext_prefix
  intro m
  rw [Measure.map_map (measurable_frestrictLe m) (measurable_feedbackMarkedRestart n)]
  change (Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n x).map
    (feedbackMarkedRestartHistory n m ∘ frestrictLe (n + m)) = _
  rw [← Measure.map_map (measurable_feedbackMarkedRestartHistory n m) (measurable_frestrictLe _),
    Kernel.traj_map_frestrictLe_apply]
  exact feedbackMarkedRestartHistory_partialTraj lam hlam0 hlam n m x

/-- The real restart law indexed by the terminal current of a finite history. -/
noncomputable def feedbackMarkedRestartKernel (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → FeedbackMarkedStep) (ℕ → FeedbackMarkedStep) where
  toFun x := feedbackMarkedTrajectory lam hlam0 hlam (x ⟨n, by simp⟩).2.2
  measurable' := (measurable_of_countable (feedbackMarkedTrajectory lam hlam0 hlam)).comp
    (show Measurable (fun x : (i : Finset.Iic n) → FeedbackMarkedStep ↦
      (x ⟨n, by simp⟩).2.2) from by fun_prop)

instance feedbackMarkedRestartKernel_isMarkov (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) : IsMarkovKernel (feedbackMarkedRestartKernel lam hlam0 hlam n) := by
  constructor
  intro x
  change IsProbabilityMeasure (feedbackMarkedTrajectory lam hlam0 hlam (x ⟨n, by simp⟩).2.2)
  infer_instance

/-- The finite past and the complete restarted future have the actual Markov product law. -/
theorem feedbackMarkedTrajectory_history_restart (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map
      (fun w ↦ (frestrictLe n w, feedbackMarkedRestart n w)) =
    (feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n) ⊗ₘ
      feedbackMarkedRestartKernel lam hlam0 hlam n := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hfull : (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ (frestrictLe n w, w)) =
      (feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n) ⊗ₘ
        Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n := by
    rw [feedbackMarkedTrajectory_eq_traj, Kernel.traj_map_frestrictLe_apply]
    exact (Kernel.partialTraj_compProd_traj (X := fun _ ↦ FeedbackMarkedStep)
      (κ := feedbackMarkedHistoryKernel lam)
      (Nat.zero_le n) (fun _ ↦ feedbackMarkedVirtual k)).symm
  have hfun : (fun w : ℕ → FeedbackMarkedStep ↦ (frestrictLe n w, feedbackMarkedRestart n w)) =
      (Prod.map id (feedbackMarkedRestart n)) ∘ (fun w ↦ (frestrictLe n w, w)) := rfl
  rw [hfun, ← Measure.map_map (measurable_id.prodMap (measurable_feedbackMarkedRestart n))
    (by fun_prop), hfull]
  simpa only [Measure.map_id] using TrajectoryProjection.map_compProd
    ((feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n))
    (Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) n)
    (feedbackMarkedRestartKernel lam hlam0 hlam n) measurable_id
    (measurable_feedbackMarkedRestart n) (feedbackMarkedRestart_map_traj lam hlam0 hlam n)

/-- The first strictly positive return index; nonreturning paths use the null fallback zero. -/
noncomputable def feedbackMarkedFirstReturnIndex (w : ℕ → FeedbackMarkedStep) : ℕ :=
  if h : ∃ j, (w (j + 1)).2.2 = 0 then Nat.find h + 1 else 0

theorem feedbackMarkedFirstReturnIndex_eq_find (w : ℕ → FeedbackMarkedStep)
    (h : ∃ j, (w (j + 1)).2.2 = 0) :
    feedbackMarkedFirstReturnIndex w = Nat.find h + 1 := by
  simp [feedbackMarkedFirstReturnIndex, h]

@[simp]
theorem feedbackMarkedFirstReturnIndex_eq_zero_iff (w : ℕ → FeedbackMarkedStep) :
    feedbackMarkedFirstReturnIndex w = 0 ↔ ¬ ∃ j, (w (j + 1)).2.2 = 0 := by
  classical
  unfold feedbackMarkedFirstReturnIndex
  split_ifs <;> simp_all

theorem feedbackMarkedFirstReturnIndex_eq_succ_iff (w : ℕ → FeedbackMarkedStep) (n : ℕ) :
    feedbackMarkedFirstReturnIndex w = n + 1 ↔
      (w (n + 1)).2.2 = 0 ∧ ∀ j < n, (w (j + 1)).2.2 ≠ 0 := by
  classical
  by_cases h : ∃ j, (w (j + 1)).2.2 = 0
  · rw [feedbackMarkedFirstReturnIndex_eq_find w h, Nat.add_right_cancel_iff, Nat.find_eq_iff]
  · simp only [feedbackMarkedFirstReturnIndex, dite_eq_right h]
    constructor
    · omega
    · intro hw
      exact (h ⟨n, hw.1⟩).elim

@[fun_prop]
theorem measurable_feedbackMarkedFirstReturnIndex : Measurable feedbackMarkedFirstReturnIndex := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {w | feedbackMarkedFirstReturnIndex w = n}
  cases n with
  | zero =>
      simp only [feedbackMarkedFirstReturnIndex_eq_zero_iff, not_exists, Set.ofPred_forall]
      exact MeasurableSet.iInter fun j ↦ (measurableSet_singleton (0 : ℤ)).preimage
        (by fun_prop) |>.compl
  | succ n =>
      simp only [feedbackMarkedFirstReturnIndex_eq_succ_iff,
        Set.ofPred_and, Set.ofPred_forall]
      refine ((measurableSet_singleton (0 : ℤ)).preimage (by fun_prop)).inter ?_
      exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
        (measurableSet_singleton (0 : ℤ)).preimage (by fun_prop) |>.compl

/-- The fallback branch has probability zero for the actual zero-start process. -/
theorem feedbackMarkedFirstReturnIndex_pos {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0, 0 < feedbackMarkedFirstReturnIndex w := by
  filter_upwards [feedbackMarkedTrajectory_returns_zero hlam0 hlam] with w hw
  obtain ⟨j, hj, hzero⟩ := hw
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [feedbackMarkedFirstReturnIndex_eq_find w ⟨i, hzero⟩]
  omega

/-- At the actual positive first return the terminal current equals zero. -/
theorem feedbackMarkedFirstReturnIndex_current (w : ℕ → FeedbackMarkedStep)
    (h : 0 < feedbackMarkedFirstReturnIndex w) :
    (w (feedbackMarkedFirstReturnIndex w)).2.2 = 0 := by
  have hex : ∃ j, (w (j + 1)).2.2 = 0 := by
    by_contra hn
    have := (feedbackMarkedFirstReturnIndex_eq_zero_iff w).mpr hn
    omega
  rw [feedbackMarkedFirstReturnIndex_eq_find w hex]
  exact Nat.find_spec hex

/-- Read the first cell as a full path padded after its right endpoint by virtual zeros. -/
noncomputable def feedbackMarkedFirstCell (w : ℕ → FeedbackMarkedStep) (j : ℕ) : FeedbackMarkedStep :=
  if j ≤ feedbackMarkedFirstReturnIndex w then w j else feedbackMarkedVirtual 0

@[fun_prop]
theorem measurable_feedbackMarkedFirstCell : Measurable feedbackMarkedFirstCell := by
  apply measurable_pi_lambda
  intro j
  exact Measurable.ite (measurableSet_le measurable_const measurable_feedbackMarkedFirstReturnIndex)
    (measurable_pi_apply j) measurable_const

/-- The full process restarted at its first strictly positive return. -/
noncomputable def feedbackMarkedFirstReturnRestart (w : ℕ → FeedbackMarkedStep) : ℕ → FeedbackMarkedStep :=
  feedbackMarkedRestart (feedbackMarkedFirstReturnIndex w) w

@[fun_prop]
theorem measurable_feedbackMarkedFirstReturnRestart : Measurable feedbackMarkedFirstReturnRestart := by
  have h : Measurable (fun p : ℕ × (ℕ → FeedbackMarkedStep) ↦ feedbackMarkedRestart p.1 p.2) :=
    measurable_from_prod_countable_right fun n ↦ measurable_feedbackMarkedRestart n
  exact h.comp (measurable_feedbackMarkedFirstReturnIndex.prodMk measurable_id)

/-- Pad a known finite cell without inspecting any future coordinate. -/
def feedbackMarkedCellHistory (n : ℕ) (x : (i : Finset.Iic n) → FeedbackMarkedStep)
    (j : ℕ) : FeedbackMarkedStep :=
  if hj : j ≤ n then x ⟨j, Finset.mem_Iic.mpr hj⟩ else feedbackMarkedVirtual 0

@[fun_prop]
theorem measurable_feedbackMarkedCellHistory (n : ℕ) : Measurable (feedbackMarkedCellHistory n) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j ≤ n <;> simp only [feedbackMarkedCellHistory, h, ↓reduceDIte] <;> fun_prop

theorem feedbackMarkedFirstCell_eq_history (w : ℕ → FeedbackMarkedStep) (n : ℕ)
    (h : feedbackMarkedFirstReturnIndex w = n) :
    feedbackMarkedFirstCell w = feedbackMarkedCellHistory n (frestrictLe n w) := by
  funext j
  simp only [feedbackMarkedFirstCell, h, feedbackMarkedCellHistory]
  split_ifs <;> rfl

/-- The finite history records its first positive zero precisely at its right endpoint. -/
def feedbackMarkedReturnHistory (n : ℕ) (x : (i : Finset.Iic (n + 1)) → FeedbackMarkedStep) : Prop :=
  (x ⟨n + 1, by simp⟩).2.2 = 0 ∧
    ∀ j : Fin n, (x ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩).2.2 ≠ 0

theorem measurableSet_feedbackMarkedReturnHistory (n : ℕ) :
    MeasurableSet {x | feedbackMarkedReturnHistory n x} := by
  unfold feedbackMarkedReturnHistory
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine ((measurableSet_singleton (0 : ℤ)).preimage (by fun_prop)).inter ?_
  exact MeasurableSet.iInter fun j ↦
    (measurableSet_singleton (0 : ℤ)).preimage (by fun_prop) |>.compl

theorem feedbackMarkedFirstReturnIndex_eq_iff_history (w : ℕ → FeedbackMarkedStep) (n : ℕ) :
    feedbackMarkedFirstReturnIndex w = n + 1 ↔
      feedbackMarkedReturnHistory n (frestrictLe (n + 1) w) := by
  rw [feedbackMarkedFirstReturnIndex_eq_succ_iff]
  constructor
  · rintro ⟨hzero, hprev⟩
    exact ⟨hzero, fun j ↦ hprev j.val j.isLt⟩
  · rintro ⟨hzero, hprev⟩
    exact ⟨hzero, fun j hj ↦ hprev ⟨j, hj⟩⟩

/-- On any finite-history event ending at zero, the complete restarted future has the zero-start law. -/
theorem feedbackMarkedTrajectory_restart_rectangle (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ)
    (E : Set ((i : Finset.Iic n) → FeedbackMarkedStep)) (hE : MeasurableSet E)
    (hzero : ∀ x ∈ E, (x ⟨n, by simp⟩).2.2 = 0)
    (B : Set (ℕ → FeedbackMarkedStep)) (hB : MeasurableSet B) :
    feedbackMarkedTrajectory lam hlam0 hlam k
      {w | frestrictLe n w ∈ E ∧ feedbackMarkedRestart n w ∈ B} =
    feedbackMarkedTrajectory lam hlam0 hlam k (frestrictLe n ⁻¹' E) *
      feedbackMarkedTrajectory lam hlam0 hlam 0 B := by
  change feedbackMarkedTrajectory lam hlam0 hlam k
    ((fun w ↦ (frestrictLe n w, feedbackMarkedRestart n w)) ⁻¹' (E ×ˢ B)) = _
  rw [← Measure.map_apply ((measurable_frestrictLe n).prodMk (measurable_feedbackMarkedRestart n))
    (hE.prod hB), feedbackMarkedTrajectory_history_restart,
    Measure.compProd_apply_prod hE hB]
  calc
    _ = ∫⁻ _ in E, feedbackMarkedTrajectory lam hlam0 hlam 0 B
        ∂(feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n) := by
      apply setLIntegral_congr_fun hE
      intro x hx
      change feedbackMarkedTrajectory lam hlam0 hlam (x ⟨n, by simp⟩).2.2 B = _
      rw [hzero x hx]
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ,
        Measure.map_apply (measurable_frestrictLe n) hE]
      exact mul_comm _ _

/-- Factorization on each possible value of the actual positive return index. -/
theorem feedbackMarkedTrajectory_firstReturn_rectangle_slice (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ)
    (A B : Set (ℕ → FeedbackMarkedStep)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    feedbackMarkedTrajectory lam hlam0 hlam 0
      {w | feedbackMarkedFirstReturnIndex w = n + 1 ∧ feedbackMarkedFirstCell w ∈ A ∧
        feedbackMarkedFirstReturnRestart w ∈ B} =
    feedbackMarkedTrajectory lam hlam0 hlam 0
      {w | feedbackMarkedFirstReturnIndex w = n + 1 ∧ feedbackMarkedFirstCell w ∈ A} *
      feedbackMarkedTrajectory lam hlam0 hlam 0 B := by
  let E : Set ((i : Finset.Iic (n + 1)) → FeedbackMarkedStep) :=
    {x | feedbackMarkedReturnHistory n x ∧ feedbackMarkedCellHistory (n + 1) x ∈ A}
  have hE : MeasurableSet E := (measurableSet_feedbackMarkedReturnHistory n).inter
    ((measurable_feedbackMarkedCellHistory (n + 1)) hA)
  have hzero : ∀ x ∈ E, (x ⟨n + 1, by simp⟩).2.2 = 0 := fun _ hx ↦ hx.1.1
  have hread (w : ℕ → FeedbackMarkedStep) :
      frestrictLe (n + 1) w ∈ E ↔
        feedbackMarkedFirstReturnIndex w = n + 1 ∧ feedbackMarkedFirstCell w ∈ A := by
    change (feedbackMarkedReturnHistory n (frestrictLe (n + 1) w) ∧ _) ↔ _
    rw [← feedbackMarkedFirstReturnIndex_eq_iff_history]
    constructor <;> rintro ⟨h, hx⟩ <;> refine ⟨h, ?_⟩
    · rwa [feedbackMarkedFirstCell_eq_history w (n + 1) h]
    · rwa [feedbackMarkedFirstCell_eq_history w (n + 1) h] at hx
  have hleft : {w : ℕ → FeedbackMarkedStep | frestrictLe (n + 1) w ∈ E ∧ feedbackMarkedRestart (n + 1) w ∈ B} =
      {w | feedbackMarkedFirstReturnIndex w = n + 1 ∧ feedbackMarkedFirstCell w ∈ A ∧
        feedbackMarkedFirstReturnRestart w ∈ B} := by
    ext w
    simp only [Set.mem_ofPred_eq, hread]
    constructor
    · rintro ⟨⟨h, ha⟩, hb⟩
      exact ⟨h, ha, by simpa [feedbackMarkedFirstReturnRestart, h] using hb⟩
    · rintro ⟨h, ha, hb⟩
      exact ⟨⟨h, ha⟩, by simpa [feedbackMarkedFirstReturnRestart, h] using hb⟩
  have hright : frestrictLe (π := fun _ ↦ FeedbackMarkedStep) (n + 1) ⁻¹' E =
      {w | feedbackMarkedFirstReturnIndex w = n + 1 ∧ feedbackMarkedFirstCell w ∈ A} :=
    Set.ext hread
  rw [← hleft, ← hright]
  exact feedbackMarkedTrajectory_restart_rectangle lam hlam0 hlam 0 (n + 1) E hE hzero B hB

/-- Disjoint positive return-index slices exhaust every measurable event up to a null set. -/
theorem feedbackMarkedTrajectory_measure_eq_tsum_return_slices (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (S : Set (ℕ → FeedbackMarkedStep)) (hS : MeasurableSet S) :
    feedbackMarkedTrajectory lam hlam0 hlam 0 S =
      ∑' n : ℕ, feedbackMarkedTrajectory lam hlam0 hlam 0
        ({w | feedbackMarkedFirstReturnIndex w = n + 1} ∩ S) := by
  have hset : S =ᵐ[feedbackMarkedTrajectory lam hlam0 hlam 0]
      ⋃ n : ℕ, {w | feedbackMarkedFirstReturnIndex w = n + 1} ∩ S := by
    filter_upwards [feedbackMarkedFirstReturnIndex_pos hlam0 hlam] with w hw
    apply propext
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
      exact Set.mem_iUnion.mpr ⟨n, hn, hs⟩
    · intro hw
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
      exact hn.2
  rw [measure_congr hset]
  apply measure_iUnion
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro w ⟨hi, _⟩ ⟨hj, _⟩
    exact hij (by dsimp only [Set.mem_ofPred_eq] at hi hj; omega)
  · intro n
    exact (measurable_feedbackMarkedFirstReturnIndex (measurableSet_singleton (n + 1))).inter hS

/-- The first actual cell and the complete process restarted at its endpoint are independent;
the restarted process has exactly the original zero-start law. -/
theorem feedbackMarkedTrajectory_firstCell_restart_product (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map
      (fun w ↦ (feedbackMarkedFirstCell w, feedbackMarkedFirstReturnRestart w)) =
    ((feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackMarkedFirstCell).prod
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (measurable_feedbackMarkedFirstCell.prodMk
    measurable_feedbackMarkedFirstReturnRestart) (hA.prod hB), Measure.prod_prod,
    Measure.map_apply measurable_feedbackMarkedFirstCell hA]
  change feedbackMarkedTrajectory lam hlam0 hlam 0
    (feedbackMarkedFirstCell ⁻¹' A ∩ feedbackMarkedFirstReturnRestart ⁻¹' B) = _
  rw [feedbackMarkedTrajectory_measure_eq_tsum_return_slices lam hlam0 hlam _
      ((measurable_feedbackMarkedFirstCell hA).inter (measurable_feedbackMarkedFirstReturnRestart hB)),
    feedbackMarkedTrajectory_measure_eq_tsum_return_slices lam hlam0 hlam _
      (measurable_feedbackMarkedFirstCell hA), ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro n
  exact feedbackMarkedTrajectory_firstReturn_rectangle_slice lam hlam0 hlam n A B hA hB

/-- The full post-return law is the original zero-start marked trajectory law. -/
theorem feedbackMarkedTrajectory_firstReturn_restart_law (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackMarkedFirstReturnRestart =
      feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  have h := congrArg (fun μ : Measure ((ℕ → FeedbackMarkedStep) × (ℕ → FeedbackMarkedStep)) ↦
    μ.map Prod.snd) (feedbackMarkedTrajectory_firstCell_restart_product lam hlam0 hlam)
  rw [Measure.map_map measurable_snd (measurable_feedbackMarkedFirstCell.prodMk
    measurable_feedbackMarkedFirstReturnRestart)] at h
  have : IsProbabilityMeasure ((feedbackMarkedTrajectory lam hlam0 hlam 0).map
      feedbackMarkedFirstCell) := Measure.isProbabilityMeasure_map
        measurable_feedbackMarkedFirstCell.aemeasurable
  simpa [Function.comp_def] using h

/-- Independence of the actual first return cell from the complete restarted path. -/
theorem feedbackMarkedTrajectory_firstCell_restart_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun feedbackMarkedFirstCell feedbackMarkedFirstReturnRestart
      (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_feedbackMarkedFirstCell.aemeasurable
    measurable_feedbackMarkedFirstReturnRestart.aemeasurable).mpr
  rw [feedbackMarkedTrajectory_firstReturn_restart_law]
  exact feedbackMarkedTrajectory_firstCell_restart_product lam hlam0 hlam

end OTSelector.Limit
