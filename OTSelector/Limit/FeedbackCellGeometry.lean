import OTSelector.Limit.FeedbackRegenerationCells
import OTSelector.Limit.FeedbackMarkedRestart

/-!
# Geometry of an actual marked return cell

The cell roof is the clock of the first positive return. Every jump is a nearest-neighbor
current change, clocks are strictly increasing, and the endpoint currents are zero.
-/

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators

namespace OTSelector.Limit

/-- Physical jump coordinates measured from the start of a return cell. -/
noncomputable def feedbackCellClock (w : FeedbackCellPath) (n : ℕ) : ℝ :=
  feedbackJumpTime n (feedbackMarkedTrajectoryProjection w)

@[fun_prop]
theorem measurable_feedbackCellClock (n : ℕ) :
    Measurable (fun w ↦ feedbackCellClock w n) :=
  (measurable_feedbackJumpTime n).comp measurable_feedbackMarkedTrajectoryProjection

@[simp]
theorem feedbackCellClock_zero (w : FeedbackCellPath) : feedbackCellClock w 0 = 0 :=
  feedbackJumpTime_zero _

theorem feedbackCellClock_succ (w : FeedbackCellPath) (n : ℕ) :
    feedbackCellClock w (n + 1) = feedbackCellClock w n + (w (n + 1)).1 :=
  feedbackJumpTime_succ n _

theorem feedbackCellClock_strictMono (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) : StrictMono (feedbackCellClock w) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [feedbackCellClock_succ]
  exact lt_add_of_pos_right _ (hw n)

/-- The roof used for spatial occupation is the actual first-return jump coordinate. -/
theorem feedbackCellLength_eq_clock (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) (ht : 0 < feedbackMarkedFirstReturnIndex w) :
    feedbackCellLength w = feedbackCellClock w (feedbackMarkedFirstReturnIndex w) := by
  have hex : ∃ j, (w (j + 1)).2.2 = 0 := by
    by_contra hn
    have := (feedbackMarkedFirstReturnIndex_eq_zero_iff w).mpr hn
    omega
  have hp : ∃ j, feedbackPostInitialCurrent (feedbackMarkedTrajectoryProjection w) j = 0 := hex
  unfold feedbackCellLength
  rw [feedbackReturnLength_eq_first_clock _ (fun i ↦ (hw i).le) hp,
    feedbackMarkedFirstReturnIndex_eq_find w hex]
  apply ENNReal.toReal_ofReal
  exact (feedbackCellClock_zero w).symm.trans_le
    ((feedbackCellClock_strictMono w hw).monotone (Nat.zero_le _))

theorem feedbackMarkedTrajectory_initial {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam k, w 0 = feedbackMarkedVirtual k := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hmap := TrajectoryProjection.trajMeasure_prefix_zero
    (Measure.dirac (feedbackMarkedVirtual k)) (feedbackMarkedHistoryKernel lam)
  have h : ∀ᵐ x ∂(feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe 0),
      x ⟨0, by simp⟩ = feedbackMarkedVirtual k := by
    change ∀ᵐ x ∂(Kernel.trajMeasure (X := fun _ ↦ FeedbackMarkedStep)
      (Measure.dirac (feedbackMarkedVirtual k)) (feedbackMarkedHistoryKernel lam)).map
      (frestrictLe 0), _
    rw [hmap, Measure.map_dirac' (MeasurableEquiv.measurable _)]
    simp
  exact ae_of_ae_map (measurable_frestrictLe 0).aemeasurable h

theorem feedbackMarkedHoldingKernel_map_current {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedHoldingKernel lam k).map (fun z ↦ z.2.2) = feedbackJumpKernel lam k := by
  rw [show (fun z : FeedbackMarkedStep ↦ z.2.2) =
    Prod.snd ∘ feedbackMarkedStepProjection from rfl,
    ← Measure.map_map measurable_snd measurable_feedbackMarkedStepProjection,
    feedbackMarkedHoldingKernel_map_step hlam0 hlam,
    feedbackHoldingJumpKernel_map_current hlam0 hlam]

/-- The true marked trajectory changes current by exactly one at every positive-index jump. -/
theorem feedbackMarkedTrajectory_neighbors {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam k, ∀ n,
      (w (n + 1)).2.2 = (w n).2.2 + 1 ∨ (w (n + 1)).2.2 = (w n).2.2 - 1 := by
  rw [ae_all_iff]
  intro n
  let μ := feedbackMarkedTrajectory lam hlam0 hlam k
  have hprod : ∀ᵐ p ∂μ.map (frestrictLe n) ⊗ₘ condDistrib
      (fun w : FeedbackCellPath ↦ w (n + 1)) (frestrictLe n) μ,
      p.2.2.2 = (p.1 ⟨n, by simp⟩).2.2 + 1 ∨
        p.2.2.2 = (p.1 ⟨n, by simp⟩).2.2 - 1 := by
    apply Measure.ae_compProd_of_ae_ae (by measurability)
    filter_upwards [feedbackMarkedTrajectory_condDistrib hlam0 hlam k n] with x hx
    rw [hx]
    change ∀ᵐ z ∂feedbackMarkedHoldingKernel lam (x ⟨n, by simp⟩).2.2, _
    let q := (x ⟨n, by simp⟩).2.2
    have hn : ∀ᵐ z ∂feedbackJumpKernel lam q, z ∈ ({q + 1, q - 1} : Set ℤ) := by
      let := feedbackJumpKernel_isMarkov hlam0 hlam
      exact (mem_ae_iff_prob_eq_one (by measurability)).mpr
        (feedbackJumpKernel_neighbors hlam0 hlam q)
    rw [← feedbackMarkedHoldingKernel_map_current hlam0 hlam q] at hn
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      ae_of_ae_map (show Measurable (fun z : FeedbackMarkedStep ↦ z.2.2) by fun_prop).aemeasurable hn
  rw [compProd_map_condDistrib (μ := μ) (X := frestrictLe n)
    (Y := fun w : FeedbackCellPath ↦ w (n + 1))
    (measurable_pi_apply (n + 1)).aemeasurable] at hprod
  exact ae_of_ae_map (show Measurable (fun w : FeedbackCellPath ↦
    (frestrictLe n w, w (n + 1))) by fun_prop).aemeasurable hprod

/-- Source jump indices in the first return cell; index `i` denotes arrival `i + 1`. -/
noncomputable def feedbackCellSourceJumps (w : FeedbackCellPath) : Finset ℕ :=
  (Finset.range (feedbackMarkedFirstReturnIndex w)).filter
    (fun i ↦ (w (i + 1)).2.2 = (w i).2.2 + 1)

/-- Target jump indices, using the same arrival convention as source jumps. -/
noncomputable def feedbackCellTargetJumps (w : FeedbackCellPath) : Finset ℕ :=
  (Finset.range (feedbackMarkedFirstReturnIndex w)).filter
    (fun i ↦ (w (i + 1)).2.2 = (w i).2.2 - 1)

/-- A returning nearest-neighbor cell has equal source and target event counts. -/
theorem feedbackCellJumps_balanced (w : FeedbackCellPath)
    (hstart : (w 0).2.2 = 0) (ht : 0 < feedbackMarkedFirstReturnIndex w)
    (hneigh : ∀ i, (w (i + 1)).2.2 = (w i).2.2 + 1 ∨
      (w (i + 1)).2.2 = (w i).2.2 - 1) :
    (feedbackCellSourceJumps w).card = (feedbackCellTargetJumps w).card := by
  classical
  have htel (n : ℕ) : (∑ i ∈ Finset.range n, ((w (i + 1)).2.2 - (w i).2.2)) =
      (w n).2.2 - (w 0).2.2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have heq (i : ℕ) : (w (i + 1)).2.2 - (w i).2.2 =
      (if (w (i + 1)).2.2 = (w i).2.2 + 1 then (1 : ℤ) else 0) -
        (if (w (i + 1)).2.2 = (w i).2.2 - 1 then (1 : ℤ) else 0) := by
    rcases hneigh i with h | h <;> simp [h] <;> omega
  have h := htel (feedbackMarkedFirstReturnIndex w)
  simp_rw [heq] at h
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hstart,
    feedbackMarkedFirstReturnIndex_current w ht] at h
  change ((feedbackCellSourceJumps w).card : ℤ) - (feedbackCellTargetJumps w).card = 0 - 0 at h
  exact_mod_cast (show ((feedbackCellSourceJumps w).card : ℤ) =
    (feedbackCellTargetJumps w).card by omega)

/-- The balance used in cellwise comparison matchings holds for the actual cell law. -/
theorem feedbackMarkedTrajectory_cell_balanced {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      (feedbackCellSourceJumps w).card = (feedbackCellTargetJumps w).card := by
  filter_upwards [feedbackMarkedTrajectory_initial hlam0 hlam 0,
    feedbackMarkedFirstReturnIndex_pos hlam0 hlam,
    feedbackMarkedTrajectory_neighbors hlam0 hlam 0] with w hw ht hn
  apply feedbackCellJumps_balanced w _ ht hn
  rw [hw]
  rfl

end OTSelector.Limit
