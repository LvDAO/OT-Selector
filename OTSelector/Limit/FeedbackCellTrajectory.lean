import OTSelector.Limit.FeedbackMarkedRestart
import OTSelector.Limit.FeedbackRegenerationCells

/-!
# Identification of the path obtained from independent actual return cells

Successive cells extracted from the real zero-start path have the independent first-cell law.
Concatenating their positive jump coordinates reconstructs that path. The resulting pushforward
identity identifies the path assembled from iid actual cells without assuming regeneration.
-/

open MeasureTheory ProbabilityTheory Preorder Function Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- The law of the actual first cell, padded after its first positive return. -/
noncomputable def feedbackFirstCellLaw (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    Measure FeedbackCellPath :=
  (feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackMarkedFirstCell

instance feedbackFirstCellLaw_isProbability (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    IsProbabilityMeasure (feedbackFirstCellLaw lam hlam0 hlam) :=
  Measure.isProbabilityMeasure_map measurable_feedbackMarkedFirstCell.aemeasurable

/-- Read the successive return cells from one actual trajectory. -/
noncomputable def feedbackExtractCells (w : FeedbackCellPath) (j : ℕ) : FeedbackCellPath :=
  feedbackMarkedFirstCell (feedbackMarkedFirstReturnRestart^[j] w)

@[fun_prop]
theorem measurable_feedbackExtractCells : Measurable feedbackExtractCells := by
  apply measurable_pi_lambda
  intro j
  exact measurable_feedbackMarkedFirstCell.comp (measurable_feedbackMarkedFirstReturnRestart.iterate j)

@[simp]
theorem feedbackExtractCells_zero (w : FeedbackCellPath) :
    feedbackExtractCells w 0 = feedbackMarkedFirstCell w := rfl

theorem feedbackExtractCells_succ (w : FeedbackCellPath) (j : ℕ) :
    feedbackExtractCells w (j + 1) = feedbackExtractCells (feedbackMarkedFirstReturnRestart w) j := by
  simp only [feedbackExtractCells, Function.iterate_succ_apply]

private def feedbackCellPrefixEvent (m : ℕ) (t : ℕ → Set FeedbackCellPath) : Set FeedbackCellPath :=
  {w | ∀ j < m, feedbackExtractCells w j ∈ t j}

private theorem measurableSet_feedbackCellPrefixEvent (m : ℕ) (t : ℕ → Set FeedbackCellPath)
    (ht : ∀ j, MeasurableSet (t j)) : MeasurableSet (feedbackCellPrefixEvent m t) := by
  unfold feedbackCellPrefixEvent
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    (measurable_feedbackExtractCells.eval) (ht j)

private theorem feedbackCellPrefixEvent_succ (m : ℕ) (t : ℕ → Set FeedbackCellPath) :
    feedbackCellPrefixEvent (m + 1) t =
      (fun w ↦ (feedbackMarkedFirstCell w, feedbackMarkedFirstReturnRestart w)) ⁻¹'
        (t 0 ×ˢ feedbackCellPrefixEvent m (fun j ↦ t (j + 1))) := by
  ext w
  change (∀ j < m + 1, feedbackExtractCells w j ∈ t j) ↔
    feedbackMarkedFirstCell w ∈ t 0 ∧
      ∀ j < m, feedbackExtractCells (feedbackMarkedFirstReturnRestart w) j ∈ t (j + 1)
  constructor
  · intro h
    exact ⟨h 0 (by omega), fun j hj ↦ by rw [← feedbackExtractCells_succ]; exact h _ (by omega)⟩
  · rintro ⟨hzero, hsucc⟩ j hj
    cases j with
    | zero => exact hzero
    | succ j => rw [feedbackExtractCells_succ]; exact hsucc j (by omega)

/-- Exact product probabilities for every finite sequence of extracted cells. -/
theorem feedbackExtractCells_prefix_probability (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (m : ℕ) (t : ℕ → Set FeedbackCellPath)
    (ht : ∀ j, MeasurableSet (t j)) :
    feedbackMarkedTrajectory lam hlam0 hlam 0 (feedbackCellPrefixEvent m t) =
      ∏ j ∈ Finset.range m, feedbackFirstCellLaw lam hlam0 hlam (t j) := by
  induction m generalizing t with
  | zero => simp [feedbackCellPrefixEvent]
  | succ m ih =>
      rw [feedbackCellPrefixEvent_succ, ← Measure.map_apply
        (measurable_feedbackMarkedFirstCell.prodMk measurable_feedbackMarkedFirstReturnRestart)
        ((ht 0).prod (measurableSet_feedbackCellPrefixEvent m _ (fun j ↦ ht (j + 1)))),
        feedbackMarkedTrajectory_firstCell_restart_product, Measure.prod_prod,
        ih _ (fun j ↦ ht (j + 1)), Finset.prod_range_succ']
      exact mul_comm _ _

/-- Successive actual first-return cells have precisely the iid product law. -/
theorem feedbackExtractCells_map_eq_infinitePi (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackMarkedTrajectory lam hlam0 hlam 0).map feedbackExtractCells =
      Measure.infinitePi (fun _ : ℕ ↦ feedbackFirstCellLaw lam hlam0 hlam) := by
  apply Measure.eq_infinitePi
  intro s t ht
  let M := s.sup id + 1
  let u (j : ℕ) : Set FeedbackCellPath := if j ∈ s then t j else Set.univ
  have hu : ∀ j, MeasurableSet (u j) := fun j ↦ by
    dsimp [u]; split_ifs <;> simp_all
  have hsM : s ⊆ Finset.range M := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  have hset : feedbackExtractCells ⁻¹' Set.pi s t = feedbackCellPrefixEvent M u := by
    ext w
    change (∀ j ∈ s, feedbackExtractCells w j ∈ t j) ↔
      ∀ j < M, feedbackExtractCells w j ∈ u j
    constructor
    · intro h j hj
      by_cases hjs : j ∈ s
      · simpa [u, hjs] using h j hjs
      · simp [u, hjs]
    · intro h j hj
      simpa [u, hj] using h j (Finset.mem_range.mp (hsM hj))
  rw [Measure.map_apply measurable_feedbackExtractCells (MeasurableSet.pi s.countable_toSet (fun i _ ↦ ht i)),
    hset, feedbackExtractCells_prefix_probability lam hlam0 hlam M u hu]
  have hprod := Finset.prod_subset hsM (f := fun j ↦ feedbackFirstCellLaw lam hlam0 hlam (u j))
    (fun j _ hjs ↦ by simp [u, hjs])
  rw [← hprod]
  apply Finset.prod_congr rfl
  intro j hj
  simp [u, hj]

/-- A positive integer cell size on every path; the fallback is used only on a null event. -/
noncomputable def feedbackCellJumpCount (w : FeedbackCellPath) : ℕ :=
  max 1 (feedbackMarkedFirstReturnIndex w)

@[fun_prop]
theorem measurable_feedbackCellJumpCount : Measurable feedbackCellJumpCount :=
  measurable_const.max measurable_feedbackMarkedFirstReturnIndex

/-- Number of jumps contained in the first `j` cells. -/
noncomputable def feedbackCellJumpOffset (ω : ℕ → FeedbackCellPath) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, feedbackCellJumpCount (ω i)

@[simp]
theorem feedbackCellJumpOffset_zero (ω : ℕ → FeedbackCellPath) : feedbackCellJumpOffset ω 0 = 0 := by
  simp [feedbackCellJumpOffset]

theorem feedbackCellJumpOffset_succ (ω : ℕ → FeedbackCellPath) (j : ℕ) :
    feedbackCellJumpOffset ω (j + 1) = feedbackCellJumpOffset ω j + feedbackCellJumpCount (ω j) :=
  Finset.sum_range_succ _ _

@[fun_prop]
theorem measurable_feedbackCellJumpOffset (j : ℕ) : Measurable (fun ω ↦ feedbackCellJumpOffset ω j) := by
  unfold feedbackCellJumpOffset
  exact Finset.measurable_sum _ (fun i _ ↦ measurable_feedbackCellJumpCount.comp (measurable_pi_apply i))

theorem feedbackCellJumpOffset_ge (ω : ℕ → FeedbackCellPath) (j : ℕ) : j ≤ feedbackCellJumpOffset ω j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [feedbackCellJumpOffset_succ]
      have : 1 ≤ feedbackCellJumpCount (ω j) := le_max_left _ _
      omega

theorem feedbackCellJumpOffset_strictMono (ω : ℕ → FeedbackCellPath) :
    StrictMono (feedbackCellJumpOffset ω) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [feedbackCellJumpOffset_succ]
  have : 1 ≤ feedbackCellJumpCount (ω j) := le_max_left _ _
  omega

private theorem feedbackCellJumpIndex_exists (ω : ℕ → FeedbackCellPath) (n : ℕ) :
    ∃ j, n < feedbackCellJumpOffset ω (j + 1) :=
  ⟨n, (Nat.lt_succ_self n).trans_le (feedbackCellJumpOffset_ge ω (n + 1))⟩

/-- Cell containing jump `n+1`; endpoints belong to the cell whose final jump they are. -/
noncomputable def feedbackCellJumpIndex (ω : ℕ → FeedbackCellPath) (n : ℕ) : ℕ :=
  Nat.find (feedbackCellJumpIndex_exists ω n)

@[fun_prop]
theorem measurable_feedbackCellJumpIndex (n : ℕ) : Measurable (fun ω ↦ feedbackCellJumpIndex ω n) :=
  measurable_find (fun ω ↦ feedbackCellJumpIndex_exists ω n)
    (fun j ↦ measurableSet_lt measurable_const (measurable_feedbackCellJumpOffset (j + 1)))

theorem feedbackCellJumpIndex_bounds (ω : ℕ → FeedbackCellPath) (n : ℕ) :
    feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n) ≤ n ∧
      n < feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n + 1) := by
  refine ⟨?_, Nat.find_spec (feedbackCellJumpIndex_exists ω n)⟩
  cases hj : feedbackCellJumpIndex ω n with
  | zero => simp
  | succ j =>
      have hmin := Nat.find_min (feedbackCellJumpIndex_exists ω n) (show j < feedbackCellJumpIndex ω n by omega)
      have hn : ¬ n < feedbackCellJumpOffset ω (j + 1) := hmin
      exact Nat.le_of_not_gt hn

/-- The jump coordinate inside the selected cell is positive and no larger than its cell length. -/
theorem feedbackCellJumpIndex_local_bounds (ω : ℕ → FeedbackCellPath) (n : ℕ) :
    0 < n + 1 - feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n) ∧
    n + 1 - feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n) ≤
      feedbackCellJumpCount (ω (feedbackCellJumpIndex ω n)) := by
  have h := feedbackCellJumpIndex_bounds ω n
  rw [feedbackCellJumpOffset_succ] at h
  omega

private theorem measurable_nat_eval {A : Type*} [MeasurableSpace A] :
    Measurable (fun p : (ℕ → A) × ℕ ↦ p.1 p.2) :=
  measurable_from_prod_countable_left fun n ↦ measurable_pi_apply n

/-- Concatenate positive jump coordinates of successive cells, inserting just one virtual origin. -/
noncomputable def feedbackConcatCellPaths (ω : ℕ → FeedbackCellPath) : FeedbackCellPath
  | 0 => feedbackMarkedVirtual 0
  | n + 1 => ω (feedbackCellJumpIndex ω n)
      (n + 1 - feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n))

@[fun_prop]
theorem measurable_feedbackConcatCellPaths : Measurable feedbackConcatCellPaths := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n =>
      have hc : Measurable (fun ω : ℕ → FeedbackCellPath ↦ ω (feedbackCellJumpIndex ω n)) :=
        measurable_nat_eval.comp (measurable_id.prodMk (measurable_feedbackCellJumpIndex n))
      have ho : Measurable (fun ω : ℕ → FeedbackCellPath ↦
          feedbackCellJumpOffset ω (feedbackCellJumpIndex ω n)) :=
        measurable_nat_eval.comp ((measurable_pi_lambda _ measurable_feedbackCellJumpOffset).prodMk
          (measurable_feedbackCellJumpIndex n))
      exact measurable_nat_eval.comp (hc.prodMk (measurable_const.sub ho))

/-- Truncating a returning path at its first return preserves the return index itself. -/
theorem feedbackMarkedFirstCell_returnIndex (w : FeedbackCellPath)
    (hw : 0 < feedbackMarkedFirstReturnIndex w) :
    feedbackMarkedFirstReturnIndex (feedbackMarkedFirstCell w) = feedbackMarkedFirstReturnIndex w := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  rw [hn, feedbackMarkedFirstReturnIndex_eq_succ_iff]
  have hfirst := (feedbackMarkedFirstReturnIndex_eq_succ_iff w n).mp hn
  constructor
  · simpa [feedbackMarkedFirstCell, hn] using hfirst.1
  · intro j hj
    simpa [feedbackMarkedFirstCell, hn, show j + 1 ≤ n + 1 by omega] using hfirst.2 j hj

/-- Restart preserves the actual zero-start probability measure. -/
theorem feedbackMarkedFirstReturnRestart_measurePreserving (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    MeasurePreserving feedbackMarkedFirstReturnRestart (feedbackMarkedTrajectory lam hlam0 hlam 0)
      (feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  ⟨measurable_feedbackMarkedFirstReturnRestart,
    feedbackMarkedTrajectory_firstReturn_restart_law lam hlam0 hlam⟩

/-- Every successive extracted cell has a genuine positive return index almost surely. -/
theorem feedbackMarkedTrajectory_all_returns (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      ∀ j : ℕ, 0 < feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w) := by
  rw [ae_all_iff]
  intro j
  have h := feedbackMarkedFirstReturnIndex_pos hlam0 hlam
  rw [← (feedbackMarkedFirstReturnRestart_measurePreserving lam hlam0 hlam).iterate j |>.map_eq] at h
  exact ae_of_ae_map (measurable_feedbackMarkedFirstReturnRestart.iterate j).aemeasurable h

private theorem feedbackExtractCells_jumpCount (w : FeedbackCellPath) (j : ℕ)
    (hw : 0 < feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w)) :
    feedbackCellJumpCount (feedbackExtractCells w j) =
      feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w) := by
  unfold feedbackCellJumpCount feedbackExtractCells
  rw [feedbackMarkedFirstCell_returnIndex _ hw, max_eq_right (Nat.succ_le_of_lt hw)]

/-- Iterated actual restart reads the original path after the accumulated cell jump counts. -/
theorem feedbackMarkedRestart_iterate_coordinate (w : FeedbackCellPath)
    (hw : ∀ j, 0 < feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w))
    (j n : ℕ) (hn : 0 < n) :
    (feedbackMarkedFirstReturnRestart^[j] w) n =
      w (feedbackCellJumpOffset (feedbackExtractCells w) j + n) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      change feedbackMarkedRestart (feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w))
        (feedbackMarkedFirstReturnRestart^[j] w) n = _
      rw [feedbackMarkedRestart, ite_eq_right (Nat.ne_of_gt hn), ih _ (by omega),
        feedbackCellJumpOffset_succ, feedbackExtractCells_jumpCount w j (hw j)]
      congr 1
      omega

/-- Pathwise reconstruction from the actual successive return cells. -/
theorem feedbackConcatCellPaths_extract (w : FeedbackCellPath)
    (hzero : w 0 = feedbackMarkedVirtual 0)
    (hw : ∀ j, 0 < feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w)) :
    feedbackConcatCellPaths (feedbackExtractCells w) = w := by
  funext n
  cases n with
  | zero => exact hzero.symm
  | succ n =>
      let j := feedbackCellJumpIndex (feedbackExtractCells w) n
      have hb := feedbackCellJumpIndex_local_bounds (feedbackExtractCells w) n
      have hoff := (feedbackCellJumpIndex_bounds (feedbackExtractCells w) n).1
      have hlocal : n + 1 - feedbackCellJumpOffset (feedbackExtractCells w) j ≤
          feedbackMarkedFirstReturnIndex (feedbackMarkedFirstReturnRestart^[j] w) := by
        rw [← feedbackExtractCells_jumpCount w j (hw j)]
        exact hb.2
      change feedbackMarkedFirstCell (feedbackMarkedFirstReturnRestart^[j] w)
        (n + 1 - feedbackCellJumpOffset (feedbackExtractCells w) j) = _
      rw [feedbackMarkedFirstCell, ite_eq_left hlocal,
        feedbackMarkedRestart_iterate_coordinate w hw j _ hb.1]
      congr 1
      dsimp [j] at *
      omega

/-- The virtual initial coordinate of the actual path is deterministic. -/
theorem feedbackMarkedTrajectory_map_zero (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ w 0) =
      Measure.dirac (feedbackMarkedVirtual k) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hp : (feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe 0) =
      Measure.dirac (fun _ : Finset.Iic 0 ↦ feedbackMarkedVirtual k) := by
    rw [feedbackMarkedTrajectory_eq_traj, Kernel.traj_map_frestrictLe_apply,
      Kernel.partialTraj_self, Kernel.id_apply]
  have h := congrArg (fun μ : Measure ((i : Finset.Iic 0) → FeedbackMarkedStep) ↦
    μ.map (fun x ↦ x ⟨0, by simp⟩)) hp
  have he : Measurable (fun x : (i : Finset.Iic (0 : ℕ)) → FeedbackMarkedStep ↦
      x ⟨0, by simp⟩) := measurable_pi_apply _
  have hr : Measurable (frestrictLe (π := fun _ : ℕ ↦ FeedbackMarkedStep) 0) :=
    measurable_frestrictLe 0
  rw [Measure.map_map he hr, Measure.map_dirac' he] at h
  exact h

/-- Concatenation reconstructs the actual trajectory outside a null event. -/
theorem feedbackConcatCellPaths_extract_ae (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (fun w ↦ feedbackConcatCellPaths (feedbackExtractCells w)) =ᵐ[
      feedbackMarkedTrajectory lam hlam0 hlam 0] id := by
  have hzero : ∀ᵐ z ∂(Measure.dirac (feedbackMarkedVirtual 0)), z = feedbackMarkedVirtual 0 := by simp
  rw [← feedbackMarkedTrajectory_map_zero lam hlam0 hlam 0] at hzero
  have hz := ae_of_ae_map (measurable_pi_apply 0).aemeasurable hzero
  filter_upwards [hz, feedbackMarkedTrajectory_all_returns lam hlam0 hlam] with w hw hreturns
  exact feedbackConcatCellPaths_extract w hw hreturns

/-- Independent actual first-return cells concatenate to the original marked trajectory law. -/
theorem feedbackConcatCellPaths_firstCellLaw_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (Measure.infinitePi (fun _ : ℕ ↦ feedbackFirstCellLaw lam hlam0 hlam)).map
      feedbackConcatCellPaths = feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  rw [← feedbackExtractCells_map_eq_infinitePi, Measure.map_map
    measurable_feedbackConcatCellPaths measurable_feedbackExtractCells]
  exact (Measure.map_congr (feedbackConcatCellPaths_extract_ae lam hlam0 hlam)).trans Measure.map_id

/-- Trimming cells after their first return does not alter their concatenation. -/
theorem feedbackConcatCellPaths_firstCell (ω : ℕ → FeedbackCellPath)
    (hω : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j)) :
    feedbackConcatCellPaths (fun j ↦ feedbackMarkedFirstCell (ω j)) =
      feedbackConcatCellPaths ω := by
  have hcount (j : ℕ) : feedbackCellJumpCount (feedbackMarkedFirstCell (ω j)) =
      feedbackCellJumpCount (ω j) := by
    unfold feedbackCellJumpCount
    rw [feedbackMarkedFirstCell_returnIndex _ (hω j)]
  have hoff (j : ℕ) :
      feedbackCellJumpOffset (fun j ↦ feedbackMarkedFirstCell (ω j)) j =
        feedbackCellJumpOffset ω j := by
    exact Finset.sum_congr rfl fun i _ ↦ hcount i
  have hindex (n : ℕ) :
      feedbackCellJumpIndex (fun j ↦ feedbackMarkedFirstCell (ω j)) n =
        feedbackCellJumpIndex ω n := by
    unfold feedbackCellJumpIndex
    exact Nat.find_congr' (by intro j; rw [hoff])
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [feedbackConcatCellPaths, hindex, hoff]
      apply ite_eq_left
      have h := (feedbackCellJumpIndex_local_bounds ω n).2
      simpa only [feedbackCellJumpCount, max_eq_right (Nat.succ_le_of_lt (hω _))] using h

/-- Independent full marked paths, each read only through its first return, recover the actual law. -/
theorem feedbackConcatCellPaths_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (Measure.infinitePi (fun _ : ℕ ↦ feedbackMarkedTrajectory lam hlam0 hlam 0)).map
      feedbackConcatCellPaths = feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  let μ := feedbackMarkedTrajectory lam hlam0 hlam 0
  let Q := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let trim : (ℕ → FeedbackCellPath) → ℕ → FeedbackCellPath :=
    fun ω j ↦ feedbackMarkedFirstCell (ω j)
  have htrim : Measurable trim := by
    exact measurable_pi_lambda _ fun j ↦
      measurable_feedbackMarkedFirstCell.comp (measurable_pi_apply j)
  have hreturns : ∀ᵐ ω ∂Q, ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j) := by
    rw [ae_all_iff]
    intro j
    have h := feedbackMarkedFirstReturnIndex_pos hlam0 hlam
    change ∀ᵐ w ∂μ, 0 < feedbackMarkedFirstReturnIndex w at h
    rw [← Measure.infinitePi_map_eval (fun _ : ℕ ↦ μ) j] at h
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable h
  have heq : feedbackConcatCellPaths =ᵐ[Q] feedbackConcatCellPaths ∘ trim := by
    filter_upwards [hreturns] with ω hω
    exact (feedbackConcatCellPaths_firstCell ω hω).symm
  have hmap : Q.map trim =
      Measure.infinitePi (fun _ : ℕ ↦ feedbackFirstCellLaw lam hlam0 hlam) :=
    Measure.infinitePi_map_pi _ (fun _ ↦ measurable_feedbackMarkedFirstCell)
  change Q.map feedbackConcatCellPaths = _
  rw [Measure.map_congr heq, ← Measure.map_map measurable_feedbackConcatCellPaths htrim, hmap]
  exact feedbackConcatCellPaths_firstCellLaw_map lam hlam0 hlam

/-- Read the positive half of the existing two-sided cell base in jump order. -/
noncomputable def feedbackConcatPositiveCellPaths (ω : FeedbackCellSequence) : FeedbackCellPath :=
  feedbackConcatCellPaths (fun j : ℕ ↦ ω (j : ℤ))

@[fun_prop]
theorem measurable_feedbackConcatPositiveCellPaths :
    Measurable feedbackConcatPositiveCellPaths :=
  measurable_feedbackConcatCellPaths.comp
    (measurable_pi_lambda _ fun j : ℕ ↦ measurable_pi_apply (j : ℤ))

/-- The positive-index restriction of the actual two-sided iid base is the one-sided iid base. -/
theorem feedbackCellBase_positive_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackCellBase lam hlam0 hlam).map (fun ω (j : ℕ) ↦ ω (j : ℤ)) =
      Measure.infinitePi (fun _ : ℕ ↦ feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  Measure.map_infinitePi_infinitePi_of_inj Int.ofNat_injective

/-- The positive path assembled from the existing actual iid cell base has exactly the original
marked trajectory law, including all waiting times and marks. -/
theorem feedbackConcatPositiveCellPaths_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackCellBase lam hlam0 hlam).map feedbackConcatPositiveCellPaths =
      feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  change (feedbackCellBase lam hlam0 hlam).map
    (feedbackConcatCellPaths ∘ (fun ω (j : ℕ) ↦ ω (j : ℤ))) = _
  rw [← Measure.map_map measurable_feedbackConcatCellPaths
      (measurable_pi_lambda _ fun j : ℕ ↦ measurable_pi_apply (j : ℤ)),
    feedbackCellBase_positive_map, feedbackConcatCellPaths_map]

end OTSelector.Limit
