import OTSelector.Limit.FeedbackMarkedFirstHold
import OTSelector.Limit.FeedbackRegenerationCells
import OTSelector.Limit.FeedbackCellGeometry
import OTSelector.Limit.FeedbackCellConcatenation

/-!
# Null mark fibers under the actual feedback path law

The mark at a specified jump has an absolutely continuous source or target rate density.
The complete continuation depends only on the post-jump current. Tonelli therefore eliminates
countable fibers even when the exceptional mark value depends on the entire remaining path.
No independence of the constructed marks is assumed.
-/

open MeasureTheory ProbabilityTheory Set Function Filter Preorder
open scoped ENNReal

set_option maxHeartbeats 600000

namespace OTSelector.Limit

/-- Change only one arrival mark, retaining every wait and every visited current. -/
def feedbackReplaceMark (n : ℕ) (w : FeedbackCellPath) (u : UnitMark) : FeedbackCellPath :=
  Function.update w n ((w n).1, u, (w n).2.2)

theorem measurable_feedbackReplaceMark (n : ℕ) :
    Measurable (fun p : FeedbackCellPath × UnitMark ↦ feedbackReplaceMark n p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = n
  · subst i
    simp only [feedbackReplaceMark, Function.update_self]
    fun_prop
  · simp only [feedbackReplaceMark, Function.update_of_ne hi]
    exact (measurable_pi_apply i).comp measurable_fst

@[simp]
theorem feedbackReplaceMark_self (n : ℕ) (w : FeedbackCellPath) :
    feedbackReplaceMark n w (w n).2.1 = w := by
  unfold feedbackReplaceMark
  simpa only [Prod.eta] using Function.update_eq_self n w

/-- Source marks have no atoms at every current, because their actual law has a density. -/
instance sourceMarkRateMeasure_noAtoms (lam : ℝ) (k : ℤ) :
    NullSingletonClass (sourceMarkRateMeasure lam k) := by
  unfold sourceMarkRateMeasure
  infer_instance

/-- Target marks have the same nonatomic property for their own actual density. -/
instance targetMarkRateMeasure_noAtoms (lam : ℝ) (k : ℤ) :
    NullSingletonClass (targetMarkRateMeasure lam k) := by
  unfold targetMarkRateMeasure
  infer_instance

private theorem mark_product_countable_fibres_null
    {Y : Type*} [MeasurableSpace Y] (ν : Measure UnitMark) [SFinite ν] [NullSingletonClass ν]
    (μ : Measure Y) [SFinite μ] {s : Set (UnitMark × Y)} (hs : MeasurableSet s)
    (hfibre : ∀ y, {u : UnitMark | (u, y) ∈ s}.Countable) : ν.prod μ s = 0 := by
  rw [Measure.prod_apply_symm hs]
  change (∫⁻ y, ν {u : UnitMark | (u, y) ∈ s} ∂μ) = 0
  have hz (y : Y) : ν {u : UnitMark | (u, y) ∈ s} = 0 :=
    (hfibre y).measure_zero ν
  simp only [hz, lintegral_zero]

/-- The genuine marked jump and its entire continuation give zero mass to countable mark
fibers. The future path is fixed inside each fiber, not integrated out of the hypothesis. -/
theorem feedbackMarkedJumpKernel_restart_countable_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ)
    {s : Set ((UnitMark × ℤ) × FeedbackCellPath)} (hs : MeasurableSet s)
    (hfibre : ∀ j y, {u : UnitMark | ((u, j), y) ∈ s}.Countable) :
    (feedbackMarkedJumpKernel lam k ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam) s = 0 := by
  let : IsFiniteMeasure (sourceMarkRateMeasure lam k) := ⟨by
    rw [sourceMarkRateMeasure_univ hlam0 hlam]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure (targetMarkRateMeasure lam k) := ⟨by
    rw [targetMarkRateMeasure_univ hlam0 hlam]
    exact ENNReal.ofReal_lt_top⟩
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  have hzero (ν : Measure UnitMark) [SFinite ν] [NullSingletonClass ν] (j : ℤ) :
      (∫⁻ u, feedbackMarkedTrajectory lam hlam0 hlam j
        {y | ((u, j), y) ∈ s} ∂ν) = 0 := by
    let t : Set (UnitMark × FeedbackCellPath) := {p | ((p.1, j), p.2) ∈ s}
    have ht : MeasurableSet t := hs.preimage
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have hz := mark_product_countable_fibres_null ν
      (feedbackMarkedTrajectory lam hlam0 hlam j) ht (hfibre j)
    rwa [Measure.prod_apply ht] at hz
  rw [Measure.compProd_apply hs]
  change (∫⁻ z, feedbackMarkedAfterJumpKernel lam hlam0 hlam z (Prod.mk z ⁻¹' s) ∂
    (ENNReal.ofReal (totalJumpRate lam k))⁻¹ •
      ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
        (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))) = 0
  rw [lintegral_smul_measure, lintegral_add_measure,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_prodMk_right,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_prodMk_right]
  change _ * ((∫⁻ u, feedbackMarkedTrajectory lam hlam0 hlam (k + 1)
    {y | ((u, k + 1), y) ∈ s} ∂sourceMarkRateMeasure lam k) +
    (∫⁻ u, feedbackMarkedTrajectory lam hlam0 hlam (k - 1)
    {y | ((u, k - 1), y) ∈ s} ∂targetMarkRateMeasure lam k)) = 0
  rw [hzero, hzero, zero_add, mul_zero]


/-- Reconstruct the full path from its first real step and its complete restarted future. -/
def feedbackMarkFirstAssemble (k : ℤ) (p : ℝ × (UnitMark × ℤ) × FeedbackCellPath) :
    FeedbackCellPath
  | 0 => feedbackMarkedVirtual k
  | 1 => (p.1, p.2.1)
  | n + 2 => p.2.2 (n + 1)

theorem measurable_feedbackMarkFirstAssemble (k : ℤ) : Measurable (feedbackMarkFirstAssemble k) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => cases n <;> dsimp [feedbackMarkFirstAssemble] <;> fun_prop

theorem feedbackMarkFirstAssemble_path (k : ℤ) (w : FeedbackCellPath)
    (hzero : w 0 = feedbackMarkedVirtual k) :
    feedbackMarkFirstAssemble k ((w 1).1, (w 1).2, feedbackMarkedRestart 1 w) = w := by
  funext n
  cases n with
  | zero => exact hzero.symm
  | succ n => cases n with
    | zero => rfl
    | succ n => simp [feedbackMarkFirstAssemble, feedbackMarkedRestart, Nat.add_comm]

theorem feedbackReplaceMark_firstAssemble (k : ℤ) (t : ℝ) (v u : UnitMark) (j : ℤ)
    (y : FeedbackCellPath) :
    feedbackReplaceMark 1 (feedbackMarkFirstAssemble k (t, (v, j), y)) u =
      feedbackMarkFirstAssemble k (t, (u, j), y) := by
  funext n
  cases n with
  | zero => simp [feedbackReplaceMark, feedbackMarkFirstAssemble]
  | succ n => cases n with
    | zero => simp [feedbackReplaceMark, feedbackMarkFirstAssemble]
    | succ n => simp [feedbackReplaceMark, feedbackMarkFirstAssemble]

/-- A countable fiber in the first real mark is null even after the complete rest of the path
is specified. This follows from the actual density and full future factorization. -/
theorem feedbackMarkedTrajectory_first_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ)
    {s : Set FeedbackCellPath} (hs : MeasurableSet s)
    (hfibre : ∀ w, {u : UnitMark | feedbackReplaceMark 1 w u ∈ s}.Countable) :
    feedbackMarkedTrajectory lam hlam0 hlam k s = 0 := by
  let t := feedbackMarkFirstAssemble k ⁻¹' s
  have ht : MeasurableSet t := hs.preimage (measurable_feedbackMarkFirstAssemble k)
  have hz : ((expMeasure (totalJumpRate lam k)).prod
      (feedbackMarkedJumpKernel lam k ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam)) t = 0 := by
    apply Measure.measure_prod_null_of_ae_null ht
    apply ae_of_all
    intro a
    apply feedbackMarkedJumpKernel_restart_countable_fibres_null hlam0 hlam k
      (ht.preimage measurable_prodMk_left)
    intro j y
    change Set.Countable {u : UnitMark | feedbackMarkFirstAssemble k (a, (u, j), y) ∈ s}
    simpa only [feedbackReplaceMark_firstAssemble] using
      hfibre (feedbackMarkFirstAssemble k (a, (⟨0, by simp⟩, j), y))
  have hp : ∀ᵐ p ∂(expMeasure (totalJumpRate lam k)).prod
      (feedbackMarkedJumpKernel lam k ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam),
      feedbackMarkFirstAssemble k p ∉ s := (measure_eq_zero_iff_ae_notMem).mp hz
  rw [← feedbackMarkedTrajectory_first_wait_product lam hlam0 hlam k] at hp
  have hpath := ae_of_ae_map
    (show Measurable (fun w : FeedbackCellPath ↦
      ((w 1).1, (w 1).2, feedbackMarkedRestart 1 w)) by fun_prop).aemeasurable hp
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hpath, feedbackMarkedTrajectory_initial hlam0 hlam k] with w hw hi
  rwa [feedbackMarkFirstAssemble_path k w hi] at hw


/-- A finite past followed by a restarted future, ignoring the future's virtual coordinate zero. -/
def feedbackMarkSplice (n : ℕ)
    (p : ((i : Finset.Iic n) → FeedbackMarkedStep) × FeedbackCellPath) : FeedbackCellPath :=
  fun i ↦ if h : i ≤ n then p.1 ⟨i, Finset.mem_Iic.mpr h⟩ else p.2 (i - n)

theorem measurable_feedbackMarkSplice (n : ℕ) : Measurable (feedbackMarkSplice n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ≤ n
  · simp only [feedbackMarkSplice, hi, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [feedbackMarkSplice, hi, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

theorem feedbackMarkSplice_path (n : ℕ) (w : FeedbackCellPath) :
    feedbackMarkSplice n (frestrictLe n w, feedbackMarkedRestart n w) = w := by
  funext i
  by_cases hi : i ≤ n
  · simp only [feedbackMarkSplice, hi, ↓reduceDIte, frestrictLe_apply]
  · have hpos : i - n ≠ 0 := by omega
    simp only [feedbackMarkSplice, hi, ↓reduceDIte, feedbackMarkedRestart,
      hpos, ↓reduceIte, Nat.add_sub_of_le (by omega : n ≤ i)]

theorem feedbackMarkSplice_replace (n : ℕ) (x : (i : Finset.Iic n) → FeedbackMarkedStep)
    (y : FeedbackCellPath) (u : UnitMark) :
    feedbackMarkSplice n (x, feedbackReplaceMark 1 y u) =
      feedbackReplaceMark (n + 1) (feedbackMarkSplice n (x, y)) u := by
  funext i
  by_cases hi : i ≤ n
  · have hne : i ≠ n + 1 := by omega
    simp only [feedbackMarkSplice, feedbackReplaceMark, Function.update_of_ne hne, hi, ↓reduceDIte]
  · by_cases heq : i = n + 1
    · subst i
      simp [feedbackMarkSplice, feedbackReplaceMark]
    · have hne : i - n ≠ 1 := by omega
      simp only [feedbackMarkSplice, feedbackReplaceMark, Function.update_of_ne heq,
        Function.update_of_ne hne, hi, ↓reduceDIte]

/-- At any fixed positive jump label, a measurable event with countable one-mark fibers has
zero probability under the actual infinite marked trajectory law. All other path coordinates,
including the whole future, may occur in the event and in the exceptional mark value. -/
theorem feedbackMarkedTrajectory_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ)
    {s : Set FeedbackCellPath} (hs : MeasurableSet s)
    (hfibre : ∀ w, {u : UnitMark | feedbackReplaceMark (n + 1) w u ∈ s}.Countable) :
    feedbackMarkedTrajectory lam hlam0 hlam k s = 0 := by
  let t := feedbackMarkSplice n ⁻¹' s
  have ht : MeasurableSet t := hs.preimage (measurable_feedbackMarkSplice n)
  have hz : ((feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n) ⊗ₘ
      feedbackMarkedRestartKernel lam hlam0 hlam n) t = 0 := by
    rw [Measure.compProd_apply ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro x
    apply feedbackMarkedTrajectory_first_mark_fibres_null hlam0 hlam
      (x ⟨n, by simp⟩).2.2 (ht.preimage measurable_prodMk_left)
    intro y
    change Set.Countable {u : UnitMark | feedbackMarkSplice n (x, feedbackReplaceMark 1 y u) ∈ s}
    simpa only [← feedbackMarkSplice_replace] using hfibre (feedbackMarkSplice n (x, y))
  rw [← feedbackMarkedTrajectory_history_restart lam hlam0 hlam k n,
    Measure.map_apply (show Measurable (fun w : FeedbackCellPath ↦
      (frestrictLe n w, feedbackMarkedRestart n w)) by fun_prop) ht] at hz
  simp only [t, Set.preimage_preimage, feedbackMarkSplice_path] at hz
  exact hz

/-- Finite fibers are the case used for finite alternating kinetic cost differences. -/
theorem feedbackMarkedTrajectory_finite_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ)
    {s : Set FeedbackCellPath} (hs : MeasurableSet s)
    (hfibre : ∀ w, {u : UnitMark | feedbackReplaceMark (n + 1) w u ∈ s}.Finite) :
    feedbackMarkedTrajectory lam hlam0 hlam k s = 0 :=
  feedbackMarkedTrajectory_mark_fibres_null hlam0 hlam k n hs (fun w ↦ (hfibre w).countable)

/-- Replacing one iid cell by a fresh actual path preserves the actual two-sided cell law. -/
theorem feedbackCellBase_map_update
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (j : ℤ) :
    ((feedbackCellBase lam hlam0 hlam).prod
      (feedbackMarkedTrajectory lam hlam0 hlam 0)).map
      (fun p : FeedbackCellSequence × FeedbackCellPath ↦ Function.update p.1 j p.2) =
        feedbackCellBase lam hlam0 hlam := by
  classical
  have hm : Measurable
      (fun p : FeedbackCellSequence × FeedbackCellPath ↦ Function.update p.1 j p.2) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_self] using measurable_snd
    · simp only [Function.update_of_ne hi]
      exact (measurable_pi_apply i).comp measurable_fst
  unfold feedbackCellBase
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply hm (.pi s.countable_toSet fun _ _ ↦ ht _)]
  by_cases hj : j ∈ s
  · have heq : (fun p : FeedbackCellSequence × FeedbackCellPath ↦
        Function.update p.1 j p.2) ⁻¹' Set.pi (s : Set ℤ) t =
        Set.pi (s.erase j : Set ℤ) t ×ˢ t j := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
        Finset.mem_erase]
      constructor
      · intro h
        exact ⟨fun i hi ↦ by simpa only [Function.update_of_ne hi.1] using h i hi.2,
          by simpa only [Function.update_self] using h j hj⟩
      · rintro ⟨hw, hy⟩ i hi
        by_cases hij : i = j
        · subst i
          simpa only [Function.update_self] using hy
        · simpa only [Function.update_of_ne hij] using hw i ⟨hij, hi⟩
    rw [heq, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ ↦ ht i)]
    exact Finset.prod_erase_mul s _ hj
  · have heq : (fun p : FeedbackCellSequence × FeedbackCellPath ↦
        Function.update p.1 j p.2) ⁻¹' Set.pi (s : Set ℤ) t =
        Set.pi (s : Set ℤ) t ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
        Set.mem_univ, and_true]
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      rw [Function.update_of_ne (show i ≠ j from fun h ↦ hj (h ▸ hi))]
    rw [heq, Measure.prod_prod, measure_univ, mul_one,
      Measure.infinitePi_pi _ (fun i _ ↦ ht i)]

/-- Change a specified positive jump mark in one specified cell of the actual iid field. -/
def feedbackCellReplaceMark (j : ℤ) (n : ℕ) (w : FeedbackCellSequence) (u : UnitMark) :
    FeedbackCellSequence :=
  Function.update w j (feedbackReplaceMark n (w j) u)

theorem measurable_feedbackCellReplaceMark (j : ℤ) (n : ℕ) :
    Measurable (fun p : FeedbackCellSequence × UnitMark ↦ feedbackCellReplaceMark j n p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = j
  · subst i
    simp only [feedbackCellReplaceMark, Function.update_self]
    exact Measurable.comp (f := fun p : FeedbackCellSequence × UnitMark ↦ (p.1 j, p.2))
      (measurable_feedbackReplaceMark n)
      (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd)
  · simp only [feedbackCellReplaceMark, Function.update_of_ne hi]
    exact (measurable_pi_apply i).comp measurable_fst

/-- A countable single-mark fiber is null under the actual two-sided iid return-cell base. -/
theorem feedbackCellBase_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (j : ℤ) (n : ℕ)
    {s : Set FeedbackCellSequence} (hs : MeasurableSet s)
    (hfibre : ∀ w, {u : UnitMark | feedbackCellReplaceMark j (n + 1) w u ∈ s}.Countable) :
    feedbackCellBase lam hlam0 hlam s = 0 := by
  classical
  rw [← feedbackCellBase_map_update hlam0 hlam j]
  have hm : Measurable
      (fun p : FeedbackCellSequence × FeedbackCellPath ↦ Function.update p.1 j p.2) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_self] using measurable_snd
    · simp only [Function.update_of_ne hi]
      exact (measurable_pi_apply i).comp measurable_fst
  rw [Measure.map_apply hm hs]
  apply Measure.measure_prod_null_of_ae_null (hs.preimage hm)
  apply ae_of_all
  intro w
  apply feedbackMarkedTrajectory_mark_fibres_null hlam0 hlam 0 n
    ((hs.preimage hm).preimage measurable_prodMk_left)
  intro y
  change Set.Countable {u : UnitMark | Function.update w j (feedbackReplaceMark (n + 1) y u) ∈ s}
  simpa only [feedbackCellReplaceMark, Function.update_self, Function.update_idem]
    using hfibre (Function.update w j y)

/-- In particular, the actual iid field satisfies the finite-fiber criterion. -/
theorem feedbackCellBase_finite_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (j : ℤ) (n : ℕ)
    {s : Set FeedbackCellSequence} (hs : MeasurableSet s)
    (hfibre : ∀ w, {u : UnitMark | feedbackCellReplaceMark j (n + 1) w u ∈ s}.Finite) :
    feedbackCellBase lam hlam0 hlam s = 0 :=
  feedbackCellBase_mark_fibres_null hlam0 hlam j n hs (fun w ↦ (hfibre w).countable)

@[simp]
theorem feedbackCellReplaceMark_mark_self (j : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) : ((feedbackCellReplaceMark j n w u) j n).2.1 = u := by
  simp [feedbackCellReplaceMark, feedbackReplaceMark]

/-- Every other mark is unchanged, including all marks in the whole future. -/
theorem feedbackCellReplaceMark_mark_of_ne (j k : ℤ) (n m : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) (h : (j, n) ≠ (k, m)) :
    ((feedbackCellReplaceMark j n w u) k m).2.1 = (w k m).2.1 := by
  classical
  by_cases hkj : k = j
  · subst k
    have hmn : m ≠ n := by intro heq; exact h (by simp [heq])
    simp [feedbackCellReplaceMark, feedbackReplaceMark, Function.update_of_ne hmn]
  · simp [feedbackCellReplaceMark, Function.update_of_ne hkj]

/-- Distinct positive jump labels have distinct marks almost surely, even across cells. -/
theorem feedbackCellBase_marks_injective
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      Function.Injective (fun p : ℤ × ℕ ↦ (w p.1 (p.2 + 1)).2.1) := by
  have hp (p q : ℤ × ℕ) (hpq : p ≠ q) :
      ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
        (w p.1 (p.2 + 1)).2.1 ≠ (w q.1 (q.2 + 1)).2.1 := by
    apply measure_eq_zero_iff_ae_notMem.mp
    apply feedbackCellBase_finite_mark_fibres_null hlam0 hlam p.1 p.2
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    intro w
    have hpq' : (p.1, p.2 + 1) ≠ (q.1, q.2 + 1) := by
      intro h
      apply hpq
      apply Prod.ext
      · have hfst := congrArg (fun z : ℤ × ℕ ↦ z.1) h
        exact hfst
      · have := congrArg Prod.snd h; simpa using this
    apply (Set.finite_singleton ((w q.1 (q.2 + 1)).2.1)).subset
    intro u hu
    change ((feedbackCellReplaceMark p.1 (p.2 + 1) w u) p.1 (p.2 + 1)).2.1 =
      ((feedbackCellReplaceMark p.1 (p.2 + 1) w u) q.1 (q.2 + 1)).2.1 at hu
    rw [feedbackCellReplaceMark_mark_self,
      feedbackCellReplaceMark_mark_of_ne _ _ _ _ _ _ hpq'] at hu
    exact hu
  have hall : ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ p q : ℤ × ℕ,
      p ≠ q → (w p.1 (p.2 + 1)).2.1 ≠ (w q.1 (q.2 + 1)).2.1 := by
    simp only [ae_all_iff]
    intro p q hpq
    exact hp p q hpq
  filter_upwards [hall] with w hw
  intro p q heq
  by_contra hne
  exact hw p q hne heq

/-- Resampling marks leaves the complete unmarked path exactly unchanged. -/
@[simp]
theorem feedbackMarkedTrajectoryProjection_replaceMark (n : ℕ) (w : FeedbackCellPath)
    (u : UnitMark) :
    feedbackMarkedTrajectoryProjection (feedbackReplaceMark n w u) =
      feedbackMarkedTrajectoryProjection w := by
  funext i
  by_cases hi : i = n
  · subst i
    simp [feedbackMarkedTrajectoryProjection, feedbackMarkedStepProjection, feedbackReplaceMark]
  · simp [feedbackMarkedTrajectoryProjection, feedbackReplaceMark, Function.update_of_ne hi]

@[simp]
theorem feedbackCellLength_replaceMark (n : ℕ) (w : FeedbackCellPath) (u : UnitMark) :
    feedbackCellLength (feedbackReplaceMark n w u) = feedbackCellLength w := by
  simp [feedbackCellLength]

@[simp]
theorem feedbackCellClock_replaceMark (n : ℕ) (w : FeedbackCellPath) (u : UnitMark) (i : ℕ) :
    feedbackCellClock (feedbackReplaceMark n w u) i = feedbackCellClock w i := by
  simp [feedbackCellClock]

/-- Every visited current is retained by a single-mark replacement. -/
@[simp]
theorem feedbackReplaceMark_current (n i : ℕ) (w : FeedbackCellPath) (u : UnitMark) :
    (feedbackReplaceMark n w u i).2.2 = (w i).2.2 := by
  by_cases hi : i = n
  · subst i
    simp [feedbackReplaceMark]
  · simp [feedbackReplaceMark, Function.update_of_ne hi]

@[simp]
theorem feedbackMarkedFirstReturnIndex_replaceMark (n : ℕ) (w : FeedbackCellPath) (u : UnitMark) :
    feedbackMarkedFirstReturnIndex (feedbackReplaceMark n w u) =
      feedbackMarkedFirstReturnIndex w := by
  classical
  let f : (ℕ → ℤ) → ℕ := fun v ↦
    if h : ∃ j, v (j + 1) = 0 then Nat.find h + 1 else 0
  have heq : (fun i ↦ (feedbackReplaceMark n w u i).2.2) = (fun i ↦ (w i).2.2) :=
    funext (fun i ↦ feedbackReplaceMark_current n i w u)
  exact congrArg f heq

@[simp]
theorem feedbackCellCurrent_replaceMark (n : ℕ) (w : FeedbackCellPath) (u : UnitMark) (x : ℝ) :
    feedbackCellCurrent (feedbackReplaceMark n w u) x = feedbackCellCurrent w x := by
  simp only [feedbackCellCurrent, feedbackMarkedFirstReturnIndex_replaceMark,
    feedbackCellClock_replaceMark, feedbackCellJump, feedbackReplaceMark_current]

@[simp]
theorem feedbackCellLength_cellReplaceMark (j k : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) :
    feedbackCellLength (feedbackCellReplaceMark j n w u k) = feedbackCellLength (w k) := by
  classical
  by_cases h : k = j
  · subst k
    simp [feedbackCellReplaceMark]
  · simp [feedbackCellReplaceMark, Function.update_of_ne h]

@[simp]
theorem feedbackCellCurrent_cellReplaceMark (j k : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) (x : ℝ) :
    feedbackCellCurrent (feedbackCellReplaceMark j n w u k) x = feedbackCellCurrent (w k) x := by
  classical
  by_cases h : k = j
  · subst k
    simp [feedbackCellReplaceMark]
  · simp [feedbackCellReplaceMark, Function.update_of_ne h]

/-- All physical return roots are fixed during single-mark disintegration. -/
@[simp]
theorem feedbackCellRoot_cellReplaceMark (j k : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) :
    feedbackCellRoot (feedbackCellReplaceMark j n w u) k = feedbackCellRoot w k := by
  cases k <;> simp [feedbackCellRoot]

@[simp]
theorem feedbackCellRootsGood_cellReplaceMark (j : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) :
    feedbackCellRootsGood (feedbackCellReplaceMark j n w u) ↔ feedbackCellRootsGood w := by
  simp only [feedbackCellRootsGood, feedbackCellLength_cellReplaceMark,
    feedbackCellRoot_cellReplaceMark]

@[simp]
theorem feedbackCellIndex_cellReplaceMark (j : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) (x : ℝ) :
    feedbackCellIndex (feedbackCellReplaceMark j n w u) x = feedbackCellIndex w x := by
  unfold feedbackCellIndex
  rw [feedbackCellRootsGood_cellReplaceMark]
  simp only [feedbackCellRoot_cellReplaceMark]

/-- The entire physical current is unchanged by resampling one mark. -/
@[simp]
theorem feedbackConcatenatedCurrent_cellReplaceMark (j : ℤ) (n : ℕ) (w : FeedbackCellSequence)
    (u : UnitMark) (x : ℝ) :
    feedbackConcatenatedCurrent (feedbackCellReplaceMark j n w u) x =
      feedbackConcatenatedCurrent w x := by
  simp only [feedbackConcatenatedCurrent, feedbackCellIndex_cellReplaceMark,
    feedbackCellRoot_cellReplaceMark, feedbackCellCurrent_cellReplaceMark]

/-- Consequently the actual feedback graph is fixed throughout the mark fiber. -/
@[simp]
theorem feedbackConcatenatedHeight_cellReplaceMark (lam : ℝ) (j : ℤ) (n : ℕ)
    (w : FeedbackCellSequence) (u : UnitMark) (x : ℝ) :
    feedbackConcatenatedHeight lam (feedbackCellReplaceMark j n w u) x =
      feedbackConcatenatedHeight lam w x := by
  simp only [feedbackConcatenatedHeight, feedbackConcatenatedVelocity,
    feedbackConcatenatedCurrent_cellReplaceMark]

/-- The finite-fiber criterion passes through the actual roof restriction, normalization,
and physical rerooting. Thus it applies to the original stationary environment law. -/
theorem feedbackStationaryEnvironmentLaw_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (j : ℤ) (n : ℕ)
    {s : Set PointProcess.FeedbackEnvironment} (hs : MeasurableSet s)
    (hfibre : ∀ (a : ℝ) (w : FeedbackCellSequence),
      {u : UnitMark | a +ᵥ feedbackConcatenatedEnvironment lam
        (feedbackCellReplaceMark j (n + 1) w u) ∈ s}.Countable) :
    feedbackStationaryEnvironmentLaw lam hlam0 hlam s = 0 := by
  let f : FeedbackCellSequence × ℝ → PointProcess.FeedbackEnvironment :=
    fun p ↦ p.2 +ᵥ feedbackConcatenatedEnvironment lam p.1
  have hf : Measurable f :=
    PointProcess.FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun p : FeedbackCellSequence × ℝ ↦
        (p.2, feedbackConcatenatedEnvironment lam p.1))
      (measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst))
  have hz : ((feedbackCellBase lam hlam0 hlam).prod volume) (f ⁻¹' s) = 0 := by
    rw [Measure.prod_apply_symm (hs.preimage hf)]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro a
    apply feedbackCellBase_mark_fibres_null hlam0 hlam j n
      ((hs.preimage hf).preimage measurable_prodMk_right)
    exact hfibre a
  have hr : renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun w ↦ feedbackCellLength (w 0)) (f ⁻¹' s) = 0 :=
    Measure.absolutelyContinuous_restrict hz
  change (_ • (renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
    (fun w ↦ feedbackCellLength (w 0))).map f) s = 0
  rw [Measure.smul_apply, Measure.map_apply hf hs, hr, smul_zero]

/-- Finite exceptional mark fibers are sufficient for the actual stationary environment. -/
theorem feedbackStationaryEnvironmentLaw_finite_mark_fibres_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (j : ℤ) (n : ℕ)
    {s : Set PointProcess.FeedbackEnvironment} (hs : MeasurableSet s)
    (hfibre : ∀ (a : ℝ) (w : FeedbackCellSequence),
      {u : UnitMark | a +ᵥ feedbackConcatenatedEnvironment lam
        (feedbackCellReplaceMark j (n + 1) w u) ∈ s}.Finite) :
    feedbackStationaryEnvironmentLaw lam hlam0 hlam s = 0 :=
  feedbackStationaryEnvironmentLaw_mark_fibres_null hlam0 hlam j n hs
    (fun a w ↦ (hfibre a w).countable)

end OTSelector.Limit
