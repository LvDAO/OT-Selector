import OTSelector.Matching.ZeroCutSurgery
import OTSelector.Limit.FeedbackCellReward
import OTSelector.Limit.FeedbackCellConcatenation

/-!
# Actual return-cell comparison matchings

Balanced source and target arrivals admit a finite perfect matching inside each cell. Its
quadratic feedback cost is bounded by the actual excursion-only reward, so the long initial
zero hold does not enter the comparison energy.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector.Matching

open OTSelector.Limit OTSelector.PointProcess

/-- A genuine bijection between the two finite arrival populations of one return cell. -/
noncomputable def feedbackCellComparison (w : FeedbackCellPath)
    (h : (feedbackCellSourceJumps w).card = (feedbackCellTargetJumps w).card) :
    ↥(feedbackCellSourceJumps w) ≃ ↥(feedbackCellTargetJumps w) :=
  Fintype.equivOfCardEq (by simpa using h)

private theorem cell_event_clock_bounds (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) {i : ℕ}
    (hi : i < feedbackMarkedFirstReturnIndex w) :
    (w 1).1 ≤ feedbackCellClock w (i + 1) ∧
      feedbackCellClock w (i + 1) ≤ feedbackCellLength w := by
  have ht : 0 < feedbackMarkedFirstReturnIndex w := by omega
  have hm := (feedbackCellClock_strictMono w hw).monotone
  have hfirst : feedbackCellClock w 1 = (w 1).1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, feedbackCellClock_succ, feedbackCellClock_zero, zero_add]
  constructor
  · rw [← hfirst]
    exact hm (by omega)
  · rw [feedbackCellLength_eq_clock w hw ht]
    exact hm (by omega)

/-- Every comparison edge lies after the initial hold and has length at most the excursion. -/
theorem feedbackCellComparison_edge_length {w : FeedbackCellSequence} (j : ℤ)
    (hw : ∀ i, 0 < (w j (i + 1)).1)
    (hL : feedbackCellLength (w j) = (w j 1).1 + feedbackCellExcursionLength (w j))
    (i : ↥(feedbackCellSourceJumps (w j))) (k : ↥(feedbackCellTargetJumps (w j))) :
    |(feedbackCellEventPoint w (j, k)).1 - (feedbackCellEventPoint w (j, i)).1| ≤
      feedbackCellExcursionLength (w j) := by
  have hi := cell_event_clock_bounds (w j) hw
    (Finset.mem_range.mp (Finset.mem_filter.mp i.property).1)
  have hk := cell_event_clock_bounds (w j) hw
    (Finset.mem_range.mp (Finset.mem_filter.mp k.property).1)
  dsimp only [feedbackCellEventPoint]
  rw [abs_le]
  constructor <;> linarith

/-- The actual finite cell matching has the excursion-only quadratic reward bound. -/
theorem feedbackCellComparison_cost_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 8) (w : FeedbackCellSequence) (j : ℤ)
    (hw : ∀ i, 0 < (w j (i + 1)).1)
    (hL : feedbackCellLength (w j) = (w j 1).1 + feedbackCellExcursionLength (w j))
    (e : ↥(feedbackCellSourceJumps (w j)) ≃ ↥(feedbackCellTargetJumps (w j))) :
    (∑ i : ↥(feedbackCellSourceJumps (w j)),
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e i))) ≤
      feedbackCellReward (quadraticUpperConstant lam) (w j) := by
  have hC : 0 ≤ quadraticUpperConstant lam := by unfold quadraticUpperConstant; positivity
  have hLip : ScalarLipschitz lam (feedbackConcatenatedGraphHeight lam w) := by
    intro x y
    have h := (lipschitzWith_feedbackConcatenatedHeight lam w).dist_le_mul y x
    rw [Real.coe_toNNReal _ (abs_nonneg lam), abs_of_pos hlam0] at h
    exact h
  have hedge (i : ↥(feedbackCellSourceJumps (w j))) :
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e i)) ≤
        quadraticUpperConstant lam * feedbackCellExcursionLength (w j) ^ 2 := by
    have ha : 1 - ((feedbackCellEventPoint w (j, i)).2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [(feedbackCellEventPoint w (j, i)).2.property.1,
        (feedbackCellEventPoint w (j, i)).2.property.2]
    have hb : 1 + ((feedbackCellEventPoint w (j, e i)).2 : ℝ) ∈ Icc (1 : ℝ) 2 := by
      constructor <;> linarith [(feedbackCellEventPoint w (j, e i)).2.property.1,
        (feedbackCellEventPoint w (j, e i)).2.property.2]
    apply (quadraticCost_bounds (feedbackConcatenatedGraphHeight lam w).continuous
      hLip hlam0.le hlam ha hb).2.trans
    apply mul_le_mul_of_nonneg_left _ hC
    have h := feedbackCellComparison_edge_length j hw hL i (e i)
    have he := feedbackCellExcursionLength_nonneg (w j)
    nlinarith [sq_abs ((feedbackCellEventPoint w (j, e i)).1 -
      (feedbackCellEventPoint w (j, i)).1), abs_nonneg
        ((feedbackCellEventPoint w (j, e i)).1 - (feedbackCellEventPoint w (j, i)).1)]
  have hcount : (feedbackCellSourceJumps (w j)).card ≤ feedbackMarkedFirstReturnIndex (w j) :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  calc
    _ ≤ ∑ _i : ↥(feedbackCellSourceJumps (w j)),
        quadraticUpperConstant lam * feedbackCellExcursionLength (w j) ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ hedge i)
    _ = ((feedbackCellSourceJumps (w j)).card : ℝ) *
        (quadraticUpperConstant lam * feedbackCellExcursionLength (w j) ^ 2) := by simp
    _ ≤ (feedbackMarkedFirstReturnIndex (w j) : ℝ) *
        (quadraticUpperConstant lam * feedbackCellExcursionLength (w j) ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (mul_nonneg hC (sq_nonneg _))
    _ = _ := by unfold feedbackCellReward; ring

/-- On the actual iid cell base every cell admits the required finite-energy comparison.
No cell balance or excursion-length identity is assumed by this probabilistic conclusion. -/
theorem feedbackCellBase_exists_comparison {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith), ∀ j : ℤ,
      ∃ e : ↥(feedbackCellSourceJumps (w j)) ≃ ↥(feedbackCellTargetJumps (w j)),
        (∑ i : ↥(feedbackCellSourceJumps (w j)),
          markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
            (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e i))) ≤
          feedbackCellReward (quadraticUpperConstant lam) (w j) := by
  have hhalf : lam < 1 / 2 := by linarith
  rw [ae_all_iff]
  intro j
  have hdata : ∀ᵐ v ∂feedbackMarkedTrajectory lam hlam0 hhalf 0,
      (∀ i, 0 < (v (i + 1)).1) ∧
      feedbackCellLength v = (v 1).1 + feedbackCellExcursionLength v ∧
      (feedbackCellSourceJumps v).card = (feedbackCellTargetJumps v).card := by
    filter_upwards [feedbackMarkedTrajectory_waits_positive hlam0 hhalf 0,
      feedbackCellLength_eq_hold_add_excursion hlam0 hhalf,
      feedbackMarkedTrajectory_cell_balanced hlam0 hhalf] with v hv hL hb
    exact ⟨hv, hL, hb⟩
  rw [← (feedbackCellBase_eval_measurePreserving hlam0 hhalf j).map_eq] at hdata
  have h := ae_of_ae_map (measurable_pi_apply j).aemeasurable hdata
  filter_upwards [h] with w hw
  exact ⟨feedbackCellComparison (w j) hw.2.2,
    feedbackCellComparison_cost_le hlam0 hlam w j hw.1 hw.2.1 _⟩

end OTSelector.Matching
