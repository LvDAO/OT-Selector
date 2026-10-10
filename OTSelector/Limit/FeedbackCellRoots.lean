import OTSelector.Limit.FeedbackRegenerationCells
import OTSelector.Probability.IIDShiftErgodic
import Mathlib.Probability.StrongLaw
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Actual two-sided return-cell roots and their measurable index

The roots are signed finite sums of the actual iid return-cell lengths.  Positivity and the
strong law give strictly ordered roots unbounded in both directions almost surely.  Their
half-open intervals partition the line and determine a jointly measurable cell index.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology Classical

namespace OTSelector.Limit

/-- The left endpoint of cell `j`, with cell zero rooted at the spatial origin. -/
noncomputable def feedbackCellRoot (w : FeedbackCellSequence) : ℤ → ℝ
  | .ofNat n => ∑ i ∈ Finset.range n, feedbackCellLength (w (i : ℤ))
  | .negSucc n => -(∑ i ∈ Finset.range (n + 1), feedbackCellLength (w (-((i : ℤ) + 1))))

@[simp]
theorem feedbackCellRoot_natCast (w : FeedbackCellSequence) (n : ℕ) :
    feedbackCellRoot w (n : ℤ) = ∑ i ∈ Finset.range n, feedbackCellLength (w (i : ℤ)) := rfl

@[simp]
theorem feedbackCellRoot_zero (w : FeedbackCellSequence) : feedbackCellRoot w 0 = 0 := by
  simp [feedbackCellRoot]

@[simp]
theorem feedbackCellRoot_neg_natCast (w : FeedbackCellSequence) (n : ℕ) :
    feedbackCellRoot w (-(n : ℤ)) =
      -(∑ i ∈ Finset.range n, feedbackCellLength (w (-((i : ℤ) + 1)))) := by
  cases n with
  | zero => simp
  | succ n => rfl

/-- Consecutive root locations differ by exactly the length of the intervening actual cell. -/
theorem feedbackCellRoot_add_one (w : FeedbackCellSequence) (j : ℤ) :
    feedbackCellRoot w (j + 1) = feedbackCellRoot w j + feedbackCellLength (w j) := by
  cases j with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, ← Nat.cast_add_one, feedbackCellRoot_natCast] using
      (Finset.sum_range_succ (fun i ↦ feedbackCellLength (w (i : ℤ))) n)
  | negSucc n =>
      rw [Int.negSucc_eq]
      have h : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by omega
      rw [h, ← Nat.cast_add_one, feedbackCellRoot_neg_natCast,
        feedbackCellRoot_neg_natCast, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

@[fun_prop]
theorem measurable_feedbackCellRoot (j : ℤ) : Measurable (fun w ↦ feedbackCellRoot w j) := by
  cases j with
  | ofNat n => exact Finset.measurable_sum _ fun i _ ↦
      measurable_feedbackCellLength.comp (measurable_pi_apply _)
  | negSucc n => exact (Finset.measurable_sum _ fun i _ ↦
      measurable_feedbackCellLength.comp (measurable_pi_apply _)).neg

/-- Positive actual cell lengths imply strict ordering of all integer-indexed roots. -/
theorem strictMono_feedbackCellRoot {w : FeedbackCellSequence}
    (hw : ∀ j : ℤ, 0 < feedbackCellLength (w j)) : StrictMono (feedbackCellRoot w) := by
  apply strictMono_int_of_lt_succ
  intro j
  rw [feedbackCellRoot_add_one]
  exact lt_add_of_pos_right _ (hw j)

/-- Reindexing the actual iid cells shifts all roots by the old location of the new zero cell. -/
theorem feedbackCellRoot_shift (w : FeedbackCellSequence) (k j : ℤ) :
    feedbackCellRoot (IIDShift.shift k w) j =
      feedbackCellRoot w (j + k) - feedbackCellRoot w k := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n hn =>
      rw [feedbackCellRoot_add_one, hn]
      have hidx : (n : ℤ) + 1 + k = ((n : ℤ) + k) + 1 := by omega
      rw [hidx, feedbackCellRoot_add_one]
      simp only [IIDShift.shift]
      ring
  | pred n hn =>
      have hleft := feedbackCellRoot_add_one (IIDShift.shift k w) (-(n : ℤ) - 1)
      have hright := feedbackCellRoot_add_one w (-(n : ℤ) - 1 + k)
      have hi₁ : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      have hi₂ : -(n : ℤ) - 1 + k + 1 = -(n : ℤ) + k := by omega
      rw [hi₁, hn] at hleft
      rw [hi₂] at hright
      simp only [IIDShift.shift] at hleft
      linarith

/-- A pathwise condition ensuring positive cells and coverage of the whole spatial line. -/
def feedbackCellRootsGood (w : FeedbackCellSequence) : Prop :=
  (∀ j : ℤ, 0 < feedbackCellLength (w j)) ∧
  (∀ m : ℕ, ∃ j : ℤ, (m : ℝ) < feedbackCellRoot w j) ∧
  (∀ m : ℕ, ∃ j : ℤ, feedbackCellRoot w j < -(m : ℝ))

theorem measurableSet_feedbackCellRootsGood : MeasurableSet {w | feedbackCellRootsGood w} := by
  unfold feedbackCellRootsGood
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.iInter fun j ↦ ?_).inter
    ((MeasurableSet.iInter fun m ↦ MeasurableSet.iUnion fun j ↦ ?_).inter
      (MeasurableSet.iInter fun m ↦ MeasurableSet.iUnion fun j ↦ ?_))
  · exact measurableSet_lt measurable_const
      (measurable_feedbackCellLength.comp (measurable_pi_apply j))
  · exact measurableSet_lt measurable_const (measurable_feedbackCellRoot j)
  · exact measurableSet_lt (measurable_feedbackCellRoot j) measurable_const

private theorem feedbackCellRootsGood.exists_below_above {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (x : ℝ) :
    (∃ j, feedbackCellRoot w j ≤ x) ∧ ∃ j, x < feedbackCellRoot w j := by
  obtain ⟨m, hm⟩ := exists_nat_gt |x|
  obtain ⟨j, hj⟩ := hw.2.2 m
  obtain ⟨k, hk⟩ := hw.2.1 m
  exact ⟨⟨j, by linarith [neg_abs_le x]⟩, ⟨k, by linarith [le_abs_self x]⟩⟩

/-- The cell index on valid paths; outside the measurable full-measure good set it is zero. -/
noncomputable def feedbackCellIndex (w : FeedbackCellSequence) (x : ℝ) : ℤ :=
  if feedbackCellRootsGood w then sSup {j : ℤ | feedbackCellRoot w j ≤ x} else 0

/-- Exact half-open cell bounds, including the endpoint convention required for concatenation. -/
theorem feedbackCellIndex_bounds {w : FeedbackCellSequence} (hw : feedbackCellRootsGood w)
    (x : ℝ) : feedbackCellRoot w (feedbackCellIndex w x) ≤ x ∧
      x < feedbackCellRoot w (feedbackCellIndex w x + 1) := by
  obtain ⟨hne, k, hk⟩ := hw.exists_below_above x
  have hbdd : BddAbove {j : ℤ | feedbackCellRoot w j ≤ x} := by
    refine ⟨k, fun j hj ↦ ?_⟩
    by_contra h
    have hlt := (strictMono_feedbackCellRoot hw.1) (lt_of_not_ge h)
    exact (not_lt_of_ge hj) (hk.trans hlt)
  simp only [feedbackCellIndex, hw, ↓reduceIte]
  refine ⟨Int.csSup_mem hne hbdd, ?_⟩
  by_contra h
  have hle := le_csSup hbdd (le_of_not_gt h)
  omega

/-- At most one cell interval contains a fixed spatial point. -/
theorem feedbackCellRoot_interval_unique {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) {x : ℝ} {i j : ℤ}
    (hi : feedbackCellRoot w i ≤ x ∧ x < feedbackCellRoot w (i + 1))
    (hj : feedbackCellRoot w j ≤ x ∧ x < feedbackCellRoot w (j + 1)) : i = j := by
  have hmono := (strictMono_feedbackCellRoot hw.1).monotone
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · have hle := hmono (show i + 1 ≤ j by omega)
    linarith [hi.2, hj.1]
  · have hle := hmono (show j + 1 ≤ i by omega)
    linarith [hj.2, hi.1]

/-- Membership in the cell interval characterizes the chosen index exactly. -/
theorem feedbackCellIndex_eq_iff {w : FeedbackCellSequence} (hw : feedbackCellRootsGood w)
    (x : ℝ) (j : ℤ) : feedbackCellIndex w x = j ↔
      feedbackCellRoot w j ≤ x ∧ x < feedbackCellRoot w (j + 1) := by
  constructor
  · intro h
    simpa only [h] using feedbackCellIndex_bounds hw x
  · exact feedbackCellRoot_interval_unique hw (feedbackCellIndex_bounds hw x)

/-- The actual cell index is jointly measurable in the entire iid path sequence and the root. -/
@[fun_prop]
theorem measurable_feedbackCellIndex :
    Measurable (fun p : FeedbackCellSequence × ℝ ↦ feedbackCellIndex p.1 p.2) := by
  apply measurable_to_countable'
  intro j
  have heq : {p : FeedbackCellSequence × ℝ | feedbackCellIndex p.1 p.2 = j} =
      ({p | feedbackCellRootsGood p.1} ∩
        {p | feedbackCellRoot p.1 j ≤ p.2 ∧ p.2 < feedbackCellRoot p.1 (j + 1)}) ∪
      ({p | ¬feedbackCellRootsGood p.1} ∩ {p | (0 : ℤ) = j}) := by
    ext p
    by_cases hp : feedbackCellRootsGood p.1
    · simp [hp, feedbackCellIndex_eq_iff hp]
    · simp [feedbackCellIndex, hp]
  change MeasurableSet {p : FeedbackCellSequence × ℝ | feedbackCellIndex p.1 p.2 = j}
  rw [heq]
  have hgood : MeasurableSet {p : FeedbackCellSequence × ℝ | feedbackCellRootsGood p.1} :=
    measurableSet_feedbackCellRootsGood.preimage measurable_fst
  exact (hgood.inter ((measurableSet_le
    ((measurable_feedbackCellRoot j).comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd
        ((measurable_feedbackCellRoot (j + 1)).comp measurable_fst)))).union
    (hgood.compl.inter (MeasurableSet.const _))

/-- The half-open root intervals partition the whole line on each good path. -/
theorem existsUnique_feedbackCellInterval {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (x : ℝ) :
    ∃! j : ℤ, x ∈ Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1)) := by
  refine ⟨feedbackCellIndex w x, feedbackCellIndex_bounds hw x, ?_⟩
  intro j hj
  exact ((feedbackCellIndex_eq_iff hw x j).mpr hj).symm

/-- Moving the distinguished cell preserves the pathwise root geometry. -/
theorem feedbackCellRootsGood.shift {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (k : ℤ) : feedbackCellRootsGood (IIDShift.shift k w) := by
  refine ⟨fun j ↦ hw.1 (j + k), ?_, ?_⟩
  · intro m
    obtain ⟨j, hj⟩ := (hw.exists_below_above ((m : ℝ) + feedbackCellRoot w k)).2
    refine ⟨j - k, ?_⟩
    rw [feedbackCellRoot_shift, sub_add_cancel]
    linarith
  · intro m
    obtain ⟨j, hj⟩ := (hw.exists_below_above
      (-(m : ℝ) + feedbackCellRoot w k - 1)).1
    refine ⟨j - k, ?_⟩
    rw [feedbackCellRoot_shift, sub_add_cancel]
    linarith

/-- The cell index transforms exactly when the cell origin is moved. -/
theorem feedbackCellIndex_shift {w : FeedbackCellSequence} (hw : feedbackCellRootsGood w)
    (k : ℤ) (x : ℝ) :
    feedbackCellIndex (IIDShift.shift k w) (x - feedbackCellRoot w k) =
      feedbackCellIndex w x - k := by
  apply (feedbackCellIndex_eq_iff (hw.shift k) _ _).mpr
  have h := feedbackCellIndex_bounds hw x
  rw [feedbackCellRoot_shift, feedbackCellRoot_shift, sub_add_cancel]
  have hi : feedbackCellIndex w x - k + 1 + k = feedbackCellIndex w x + 1 := by omega
  rw [hi]
  constructor <;> linarith

/-- Only finitely many actual cell intervals can meet a bounded observation window. -/
theorem finite_feedbackCellIntervals_inter_Icc {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (a b : ℝ) :
    {j : ℤ | (Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1)) ∩ Icc a b).Nonempty}.Finite := by
  apply (Set.finite_Icc (feedbackCellIndex w a) (feedbackCellIndex w b)).subset
  rintro j ⟨x, hxcell, hxwin⟩
  have hmono := (strictMono_feedbackCellRoot hw.1).monotone
  have ha := feedbackCellIndex_bounds hw a
  have hb := feedbackCellIndex_bounds hw b
  constructor
  · by_contra h
    have hi : j + 1 ≤ feedbackCellIndex w a := by omega
    have hle := hmono hi
    linarith [hxcell.2, hxwin.1]
  · by_contra h
    have hi : feedbackCellIndex w b + 1 ≤ j := by omega
    have hle := hmono hi
    linarith [hxcell.1, hxwin.2]

private theorem feedbackCellBase_lengths_identDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (i j : ℤ) :
    IdentDistrib (fun w : FeedbackCellSequence ↦ feedbackCellLength (w i))
      (fun w : FeedbackCellSequence ↦ feedbackCellLength (w j))
      (feedbackCellBase lam hlam0 hlam) (feedbackCellBase lam hlam0 hlam) := by
  have h : IdentDistrib (fun w : FeedbackCellSequence ↦ w i) (fun w ↦ w j)
      (feedbackCellBase lam hlam0 hlam) (feedbackCellBase lam hlam0 hlam) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply j).aemeasurable,
      (feedbackCellBase_eval_measurePreserving hlam0 hlam i).map_eq.trans
        (feedbackCellBase_eval_measurePreserving hlam0 hlam j).map_eq.symm⟩
  exact h.comp measurable_feedbackCellLength

private theorem feedbackCellBase_sum_length_tendsto_atTop {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (index : ℕ → ℤ) (hindex : Injective index) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, feedbackCellLength (w (index i)))
        atTop atTop := by
  have hindep := (feedbackCellBase_lengths_iIndep hlam0 hlam).precomp hindex
  have hslln := strong_law_ae_real
    (fun i (w : FeedbackCellSequence) ↦ feedbackCellLength (w (index i)))
    (integrable_feedbackCellBase_length hlam0 hlam (index 0))
    (fun i j hij ↦ hindep.indepFun hij)
    (fun i ↦ feedbackCellBase_lengths_identDistrib hlam0 hlam (index i) (index 0))
  rw [integral_feedbackCellBase_length] at hslln
  filter_upwards [hslln] with w hw
  have h := hw.pos_mul_atTop (feedbackCellMean_pos hlam0 hlam)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

/-- Both directions of the actual root sequence diverge almost surely, by the strong law and
the proved positive finite mean of the actual return-cell length. -/
theorem feedbackCellBase_roots_diverge {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      Tendsto (fun n : ℕ ↦ feedbackCellRoot w (n : ℤ)) atTop atTop ∧
      Tendsto (fun n : ℕ ↦ feedbackCellRoot w (-(n : ℤ))) atTop atBot := by
  have hpos := feedbackCellBase_sum_length_tendsto_atTop hlam0 hlam
    (fun n ↦ (n : ℤ)) Nat.cast_injective
  have hneg := feedbackCellBase_sum_length_tendsto_atTop hlam0 hlam
    (fun n ↦ -((n : ℤ) + 1)) (by
      intro i j h
      have hij : (i : ℤ) = (j : ℤ) := by linarith
      exact_mod_cast hij)
  filter_upwards [hpos, hneg] with w hwpos hwneg
  refine ⟨by simpa only [feedbackCellRoot_natCast] using hwpos, ?_⟩
  simpa only [Function.comp_def, feedbackCellRoot_neg_natCast] using
    tendsto_neg_atTop_atBot.comp hwneg

/-- The measurable geometry domain used by the actual concatenation has full iid base measure. -/
theorem feedbackCellBase_roots_good {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, feedbackCellRootsGood w := by
  filter_upwards [feedbackCellBase_lengths_positive hlam0 hlam,
    feedbackCellBase_roots_diverge hlam0 hlam] with w hw hdiv
  refine ⟨hw, ?_, ?_⟩
  · intro m
    obtain ⟨n, hn⟩ := (hdiv.1.eventually_gt_atTop (m : ℝ)).exists
    exact ⟨n, hn⟩
  · intro m
    obtain ⟨n, hn⟩ := (hdiv.2.eventually_lt_atBot (-(m : ℝ))).exists
    exact ⟨-(n : ℤ), hn⟩

end OTSelector.Limit
