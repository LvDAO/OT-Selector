import OTSelector.Matching.FeedbackCellComparison
import OTSelector.Matching.OneStepBootstrap
import OTSelector.Limit.FeedbackZeroHold

/-!
# Actual comparison matchings between regenerative zero cuts

Non-event zero cuts lie in initial zero holds. The retained events between two
such cuts are exactly a finite block of complete cells, whose actual comparison
bijections therefore glue into the interior competitor used by the bootstrap.
-/

open Function Set MeasureTheory
open scoped BigOperators Classical

namespace OTSelector.Matching

open OTSelector.Limit OTSelector.PointProcess

/-- A non-event zero cut of the actual concatenated path. -/
def FeedbackZeroCut (w : FeedbackCellSequence) (x : ℝ) : Prop :=
  feedbackConcatenatedCurrent w x = 0 ∧
    ∀ i : ℤ × ℕ, i.2 < feedbackMarkedFirstReturnIndex (w i.1) →
      (feedbackCellEventPoint w i).1 ≠ x

/-- A genuine non-event zero cut lies strictly inside its cell's initial idle hold. -/
theorem feedbackZeroCut_mem_hold {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {x : ℝ} (hx : FeedbackZeroCut w x) :
    feedbackCellRoot w (feedbackCellIndex w x) < x ∧
      x < feedbackCellRoot w (feedbackCellIndex w x) +
        (w (feedbackCellIndex w x) 1).1 := by
  let j := feedbackCellIndex w x
  have hb := feedbackCellIndex_bounds hw.1 x
  have hstrict : feedbackCellRoot w j < x := by
    apply lt_of_le_of_ne hb.1
    intro heq
    obtain ⟨n, hn, _, hp⟩ := exists_feedbackCellEventPoint_eq_root hw j
    exact hx.2 (j - 1, n) hn (hp.trans heq)
  have huL : x - feedbackCellRoot w j < feedbackCellLength (w j) := by
    rw [feedbackCellRoot_add_one] at hb
    linarith [hb.2]
  have hu0 : 0 ≤ x - feedbackCellRoot w j := by linarith [hb.1]
  have hz : feedbackCellCurrent (w j) (x - feedbackCellRoot w j) = 0 := hx.1
  have hhold := (feedbackCellCurrent_zero_iff_initial_hold (w j) (hstart j)
    (hw.2 j).1 (hw.2 j).2 _ hu0 huL).mp hz
  exact ⟨hstrict, by linarith⟩

/-- At a cut in an initial zero hold, all events in its own or a later cell are to the right. -/
theorem feedbackCellEvent_after_zeroCut_iff {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {x : ℝ} (hx : FeedbackZeroCut w x) {direction : ℤ} {i : ℤ × ℕ}
    (hi : feedbackCellEventActive w direction i) :
    x < (feedbackCellEventPoint w i).1 ↔ feedbackCellIndex w x ≤ i.1 := by
  let j := feedbackCellIndex w x
  have hhold := feedbackZeroCut_mem_hold hw hstart hx
  have hevent := feedbackCellEventPoint_mem_cell hi
  have hmono := (strictMono_feedbackCellRoot hw.1.1).monotone
  constructor
  · intro hafter
    by_contra h
    have hroot := hmono (show i.1 + 1 ≤ j by omega)
    linarith [hevent.2, hhold.1]
  · intro hj
    rcases eq_or_lt_of_le hj with heq | hlt
    · have hclock := (feedbackCellClock_strictMono (w i.1) (hw.2 i.1).1).monotone
        (show 1 ≤ i.2 + 1 by omega)
      have hfirst : feedbackCellClock (w i.1) 1 = (w i.1 1).1 := by
        simpa using feedbackCellClock_succ (w i.1) 0
      rw [hfirst] at hclock
      dsimp only [feedbackCellEventPoint]
      rw [heq] at hhold
      linarith [hhold.2]
    · have hroot := hmono (show j + 1 ≤ i.1 by omega)
      have hbound := (feedbackCellIndex_bounds hw.1 x).2
      linarith [hevent.1]

/-- Every event between two non-event zero cuts belongs to a complete indexed cell block. -/
theorem feedbackCellEvent_between_zeroCuts_iff {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right)
    {direction : ℤ} {i : ℤ × ℕ} (hi : feedbackCellEventActive w direction i) :
    (feedbackCellEventPoint w i).1 ∈ Ioo left right ↔
      i.1 ∈ Ico (feedbackCellIndex w left) (feedbackCellIndex w right) := by
  have hliff := feedbackCellEvent_after_zeroCut_iff hw hstart hl hi
  have hriff := feedbackCellEvent_after_zeroCut_iff hw hstart hr hi
  have hne := hr.2 i hi.2.1
  change (left < (feedbackCellEventPoint w i).1 ∧ (feedbackCellEventPoint w i).1 < right) ↔ _
  rw [hliff]
  have hright : (feedbackCellEventPoint w i).1 < right ↔ i.1 < feedbackCellIndex w right := by
    rw [← not_le (a := feedbackCellIndex w right) (b := i.1), ← hriff]
    exact ⟨fun h h' ↦ (not_lt_of_gt h) h',
      fun h ↦ lt_of_le_of_ne (not_lt.mp h) hne⟩
  exact and_congr_right fun _ ↦ hright

/-- Retained marked event labels of a prescribed direction. -/
abbrev FeedbackEventLabel (w : FeedbackCellSequence) (direction : ℤ) :=
  {i : ℤ × ℕ // feedbackCellEventActive w direction i}

/-- Actual retained events strictly between the two cuts. -/
abbrev FeedbackWindowLabel (w : FeedbackCellSequence) (direction : ℤ) (left right : ℝ) :=
  {i : FeedbackEventLabel w direction // (feedbackCellEventPoint w i).1 ∈ Ioo left right}

instance feedbackWindowLabel_finite (w : FeedbackCellSequence) (direction : ℤ) (left right : ℝ) :
    Finite (FeedbackWindowLabel w direction left right) := by
  let U := {i : ℤ × ℕ | feedbackCellEventActive w direction i ∧
    (feedbackCellEventPoint w i).1 ∈ Icc left right}
  have hU : U.Finite := finite_feedbackCellEvents_window w direction left right
  let : Fintype U := hU.fintype
  let f : FeedbackWindowLabel w direction left right → U :=
    fun i ↦ ⟨i.val.val, i.val.property, i.property.1.le, i.property.2.le⟩
  apply Finite.of_injective f
  intro i j h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : U ↦ z.val) h))

noncomputable instance feedbackWindowLabel_fintype
    (w : FeedbackCellSequence) (direction : ℤ) (left right : ℝ) :
    Fintype (FeedbackWindowLabel w direction left right) := Fintype.ofFinite _

/-- The finite block of cells selected by the two zero holds. -/
noncomputable def feedbackWindowCells (w : FeedbackCellSequence) (left right : ℝ) : Finset ℤ :=
  Finset.Ico (feedbackCellIndex w left) (feedbackCellIndex w right)

/-- A concrete equivalence from window event labels to the finite family of complete cells. -/
noncomputable def feedbackWindowLabelEquiv {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} {d : ℤ}
    (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right)
    (cell : ℤ → Finset ℕ)
    (hcell : ∀ j n, n ∈ cell j ↔ n < feedbackMarkedFirstReturnIndex (w j) ∧
      (w j (n + 1)).2.2 - (w j n).2.2 = d) :
    FeedbackWindowLabel w d left right ≃
      (j : feedbackWindowCells w left right) × ↥(cell j) where
  toFun i := ⟨⟨i.val.val.1, by
      apply Finset.mem_Ico.mpr
      exact (feedbackCellEvent_between_zeroCuts_iff hw hstart hl hr i.val.property).mp i.property⟩,
    ⟨i.val.val.2, (hcell _ _).mpr i.val.property.2⟩⟩
  invFun p := ⟨⟨(p.1.val, p.2.val), hw, (hcell _ _).mp p.2.property⟩, by
    apply (feedbackCellEvent_between_zeroCuts_iff hw hstart hl hr
      ⟨hw, (hcell _ _).mp p.2.property⟩).mpr
    exact Finset.mem_Ico.mp p.1.property⟩
  left_inv i := by rfl
  right_inv p := by rfl

theorem mem_feedbackCellSourceJumps_iff (w : FeedbackCellPath) (n : ℕ) :
    n ∈ feedbackCellSourceJumps w ↔ n < feedbackMarkedFirstReturnIndex w ∧
      (w (n + 1)).2.2 - (w n).2.2 = 1 := by
  simp only [feedbackCellSourceJumps, Finset.mem_filter, Finset.mem_range]
  omega

theorem mem_feedbackCellTargetJumps_iff (w : FeedbackCellPath) (n : ℕ) :
    n ∈ feedbackCellTargetJumps w ↔ n < feedbackMarkedFirstReturnIndex w ∧
      (w (n + 1)).2.2 - (w n).2.2 = -1 := by
  simp only [feedbackCellTargetJumps, Finset.mem_filter, Finset.mem_range]
  omega

noncomputable abbrev feedbackWindowSourceEquiv {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right) :=
  feedbackWindowLabelEquiv hw hstart hl hr (fun j ↦ feedbackCellSourceJumps (w j))
    (fun j ↦ mem_feedbackCellSourceJumps_iff (w j))

noncomputable abbrev feedbackWindowTargetEquiv {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right) :=
  feedbackWindowLabelEquiv hw hstart hl hr (fun j ↦ feedbackCellTargetJumps (w j))
    (fun j ↦ mem_feedbackCellTargetJumps_iff (w j))

/-- Glue the actual complete-cell bijections into the entire interior window. -/
noncomputable def feedbackWindowComparison {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right)
    (e : ∀ j : ℤ, ↥(feedbackCellSourceJumps (w j)) ≃ ↥(feedbackCellTargetJumps (w j))) :
    FeedbackWindowLabel w 1 left right ≃ FeedbackWindowLabel w (-1) left right :=
  (feedbackWindowSourceEquiv hw hstart hl hr).trans
    ((Equiv.sigmaCongrRight (fun j : feedbackWindowCells w left right ↦ e j)).trans
      (feedbackWindowTargetEquiv hw hstart hl hr).symm)

/-- The glued comparison uses each interior source once and retains the actual sampled marks. -/
theorem feedbackWindowComparison_cost_le {lam : ℝ} {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right)
    (e : ∀ j : ℤ, ↥(feedbackCellSourceJumps (w j)) ≃ ↥(feedbackCellTargetJumps (w j)))
    (he : ∀ j, (∑ i : ↥(feedbackCellSourceJumps (w j)),
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e j i))) ≤
      feedbackCellReward (quadraticUpperConstant lam) (w j)) :
    (∑ i : FeedbackWindowLabel w 1 left right,
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w i.val.val)
        (feedbackCellEventPoint w (feedbackWindowComparison hw hstart hl hr e i).val.val)) ≤
      ∑ j ∈ feedbackWindowCells w left right,
        feedbackCellReward (quadraticUpperConstant lam) (w j) := by
  rw [← (feedbackWindowSourceEquiv hw hstart hl hr).symm.sum_comp]
  rw [Fintype.sum_sigma]
  change (∑ j : feedbackWindowCells w left right, ∑ i : ↥(feedbackCellSourceJumps (w j)),
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e j i))) ≤ _
  rw [Finset.sum_subtype (feedbackWindowCells w left right)
    (p := fun j ↦ j ∈ feedbackWindowCells w left right) (F := inferInstance) (by simp)]
  exact Finset.sum_le_sum fun j _ ↦ he j

/-- Exact interior source count in terms of the complete-cell source populations. -/
theorem feedbackWindowSource_card {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right) :
    Fintype.card (FeedbackWindowLabel w 1 left right) =
      ∑ j ∈ feedbackWindowCells w left right, (feedbackCellSourceJumps (w j)).card := by
  rw [Fintype.card_congr (feedbackWindowSourceEquiv hw hstart hl hr), Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact Finset.sum_coe_sort (feedbackWindowCells w left right)
    (fun j ↦ (feedbackCellSourceJumps (w j)).card)

/-- Any bijection of the actual retained event labels gives the concrete spatial matching
needed by the finite surgery engine. -/
noncomputable def feedbackLabelMatching (w : FeedbackCellSequence)
    (assignment : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1)) :
    SpatialMatching (FeedbackEventLabel w 1) (FeedbackEventLabel w (-1)) where
  source i := (feedbackCellEventPoint w i).1
  target i := (feedbackCellEventPoint w i).1
  assignment := assignment

theorem feedbackLabelMatching_locallyFinite (w : FeedbackCellSequence)
    (assignment : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1)) :
    (feedbackLabelMatching w assignment).LocallyFinite := by
  have hfinite (d : ℤ) (a b : ℝ) :
      {i : FeedbackEventLabel w d | (feedbackCellEventPoint w i).1 ∈ Icc a b}.Finite := by
    apply Set.Finite.of_injOn (f := fun i : FeedbackEventLabel w d ↦ i.val)
      (t := {i : ℤ × ℕ | feedbackCellEventActive w d i ∧
        (feedbackCellEventPoint w i).1 ∈ Icc a b})
    · intro i hi
      exact ⟨i.property, hi⟩
    · exact Subtype.val_injective.injOn
    · exact finite_feedbackCellEvents_window w d a b
  exact ⟨hfinite 1, hfinite (-1)⟩

namespace SpatialMatching

variable {S T : Type*}

/-- The interior rows of the selected modification represent every interior source exactly once. -/
noncomputable def sourceWindowEquiv (M : SpatialMatching S T)
    {left right : ℝ} (rows : Finset S) (hrows : (rows : Set S) = M.edgesMeeting left right)
    (hne : ∀ i, M.source i ≠ left) :
    {i : rows // cutRegion left right (M.source i) = 1} ≃
      {i : S // M.source i ∈ Ioo left right} where
  toFun i := ⟨i.val.val, by
    have h := cutRegion_eq_one.mp i.property
    exact ⟨lt_of_le_of_ne (not_lt.mp h.1) (hne i.val).symm, h.2⟩⟩
  invFun i := ⟨⟨i.val, by
    have hmem : i.val ∈ M.edgesMeeting left right := ⟨Or.inl i.property.2, Or.inl i.property.1⟩
    rw [← hrows] at hmem
    exact hmem⟩, cutRegion_eq_one.mpr ⟨not_lt_of_gt i.property.1, i.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original assignment identifies interior target rows with every actual interior target. -/
noncomputable def targetWindowEquiv (M : SpatialMatching S T)
    {left right : ℝ} (rows : Finset S) (hrows : (rows : Set S) = M.edgesMeeting left right)
    (hne : ∀ i, M.target i ≠ left) :
    {i : rows // cutRegion left right (M.target (M.assignment i)) = 1} ≃
      {i : T // M.target i ∈ Ioo left right} where
  toFun i := ⟨M.assignment i.val, by
    have h := cutRegion_eq_one.mp i.property
    exact ⟨lt_of_le_of_ne (not_lt.mp h.1) (hne (M.assignment i.val)).symm, h.2⟩⟩
  invFun i := ⟨⟨M.assignment.symm i.val, by
    have hmem : M.assignment.symm i.val ∈ M.edgesMeeting left right := by
      exact ⟨Or.inr (by simpa using i.property.2), Or.inr (by simpa using i.property.1)⟩
    rw [← hrows] at hmem
    exact hmem⟩, by
      apply cutRegion_eq_one.mpr
      simpa using And.intro (not_lt_of_gt i.property.1) i.property.2⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; exact M.assignment.symm_apply_apply _
  right_inv i := by apply Subtype.ext; exact M.assignment.apply_symm_apply _

end SpatialMatching

/-- The genuine marked quadratic cost on the retained source and target labels. -/
noncomputable def feedbackLabelCost (lam : ℝ) (w : FeedbackCellSequence)
    (i : FeedbackEventLabel w 1) (j : FeedbackEventLabel w (-1)) : ℝ :=
  markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
    (feedbackCellEventPoint w i) (feedbackCellEventPoint w j)

noncomputable def feedbackWindowSourceCount (w : FeedbackCellSequence) (left right : ℝ) : ℝ :=
  ∑ j ∈ feedbackWindowCells w left right, ((feedbackCellSourceJumps (w j)).card : ℝ)

noncomputable def feedbackWindowReward (lam : ℝ) (w : FeedbackCellSequence)
    (left right : ℝ) : ℝ :=
  ∑ j ∈ feedbackWindowCells w left right,
    feedbackCellReward (quadraticUpperConstant lam) (w j)

/-- Every selected complete cell intersects the spatial window. -/
theorem feedbackWindowCells_mem_interval {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hr : FeedbackZeroCut w right)
    {j : ℤ} (hj : j ∈ feedbackWindowCells w left right) :
    feedbackCellRoot w j < right ∧ left < feedbackCellRoot w (j + 1) := by
  have hj' := Finset.mem_Ico.mp hj
  have hm := (strictMono_feedbackCellRoot hw.1.1).monotone
  have hlb := (feedbackCellIndex_bounds hw.1 left).2
  have hrb := (feedbackZeroCut_mem_hold hw hstart hr).1
  exact ⟨lt_of_le_of_lt (hm hj'.2.le) hrb,
    lt_of_lt_of_le hlb (hm (by omega))⟩

/-- Source populations are bounded by the actual number of retained jumps in each cell. -/
theorem feedbackWindowSourceCount_le_jumpCount (w : FeedbackCellSequence) (left right : ℝ) :
    feedbackWindowSourceCount w left right ≤
      ∑ j ∈ feedbackWindowCells w left right, (feedbackMarkedFirstReturnIndex (w j) : ℝ) := by
  apply Finset.sum_le_sum
  intro j _
  exact_mod_cast (Finset.card_filter_le (Finset.range (feedbackMarkedFirstReturnIndex (w j)))
    (fun n ↦ (w j (n + 1)).2.2 = (w j n).2.2 + 1)).trans_eq (Finset.card_range _)

/-- A containing index block controls the interior event count. -/
theorem feedbackWindowSourceCount_le_sum {w : FeedbackCellSequence} {left right : ℝ}
    {J : Finset ℤ} (hJ : feedbackWindowCells w left right ⊆ J) :
    feedbackWindowSourceCount w left right ≤
      ∑ j ∈ J, (feedbackMarkedFirstReturnIndex (w j) : ℝ) := by
  apply (feedbackWindowSourceCount_le_jumpCount w left right).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg hJ (by intros; positivity)

/-- A containing index block controls the genuine comparison reward. -/
theorem feedbackWindowReward_le_sum {lam : ℝ} (hlam : 0 ≤ lam) {w : FeedbackCellSequence}
    {left right : ℝ} {J : Finset ℤ} (hJ : feedbackWindowCells w left right ⊆ J) :
    feedbackWindowReward lam w left right ≤
      ∑ j ∈ J, feedbackCellReward (quadraticUpperConstant lam) (w j) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hJ
  intro j _ _
  exact feedbackCellReward_nonneg (by unfold quadraticUpperConstant; positivity) (w j)

/-- Increase only the two environmental budgets of an already constructed comparison. -/
def SpatialMatching.WindowComparison.enlargeBounds {S T : Type*}
    {M : SpatialMatching S T} {cost : S → T → ℝ} {left right N W N' W' : ℝ}
    (comparison : M.WindowComparison cost left right N W) (hN : N ≤ N') (hW : W ≤ W') :
    M.WindowComparison cost left right N' W' where
  rows := comparison.rows
  rows_eq := comparison.rows_eq
  middle := comparison.middle
  comparison_cost := comparison.comparison_cost.trans hW
  interior_count := comparison.interior_count.trans hN

/-- Construct the exact bootstrap comparison object from actual complete-cell bijections.
All affected rows are found from endpoint local finiteness and the two finite crossing
families. Interior source and target rows are identified with the actual event labels. -/
noncomputable def feedbackActualWindowComparison {lam : ℝ} {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    {left right : ℝ} (hl : FeedbackZeroCut w left) (hr : FeedbackZeroCut w right)
    (assignment : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1))
    (hfinite : ∀ cut ∈ ({left, right} : Set ℝ),
      {i : FeedbackEventLabel w 1 | Crosses cut (feedbackCellEventPoint w i).1
        (feedbackCellEventPoint w (assignment i)).1}.Finite)
    (e : ∀ j : ℤ, ↥(feedbackCellSourceJumps (w j)) ≃ ↥(feedbackCellTargetJumps (w j)))
    (he : ∀ j, (∑ i : ↥(feedbackCellSourceJumps (w j)),
      markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (j, i)) (feedbackCellEventPoint w (j, e j i))) ≤
      feedbackCellReward (quadraticUpperConstant lam) (w j)) :
    (feedbackLabelMatching w assignment).WindowComparison (feedbackLabelCost lam w)
      left right (feedbackWindowSourceCount w left right) (feedbackWindowReward lam w left right) := by
  let M := feedbackLabelMatching w assignment
  have hrowsFinite := M.finite_edgesMeeting (feedbackLabelMatching_locallyFinite w assignment)
    left right (hfinite left (by simp)) (hfinite right (by simp))
  let rows := hrowsFinite.toFinset
  have hrows : (rows : Set (FeedbackEventLabel w 1)) = M.edgesMeeting left right :=
    hrowsFinite.coe_toFinset
  have hsne (i : FeedbackEventLabel w 1) : M.source i ≠ left := hl.2 i.val i.property.2.1
  have htne (i : FeedbackEventLabel w (-1)) : M.target i ≠ left := hl.2 i.val i.property.2.1
  let es : {i : rows // cutRegion left right (M.source i) = 1} ≃
      FeedbackWindowLabel w 1 left right := M.sourceWindowEquiv rows hrows hsne
  let et : {i : rows // cutRegion left right (M.target (M.assignment i)) = 1} ≃
      FeedbackWindowLabel w (-1) left right := M.targetWindowEquiv rows hrows htne
  let ew := feedbackWindowComparison hw hstart hl hr e
  let middle := es.trans (ew.trans et.symm)
  refine ⟨rows, hrows, middle, ?_, ?_⟩
  · have hew := feedbackWindowComparison_cost_le hw hstart hl hr e he
    rw [← es.symm.sum_comp]
    change (∑ i : FeedbackWindowLabel w 1 left right,
      feedbackLabelCost lam w (es.symm i).val (assignment (middle (es.symm i)).val)) ≤ _
    have hterm (i : FeedbackWindowLabel w 1 left right) :
        feedbackLabelCost lam w (es.symm i).val (assignment (middle (es.symm i)).val) =
          markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
            (feedbackCellEventPoint w i.val.val) (feedbackCellEventPoint w (ew i).val.val) := by
      simp only [middle, Equiv.trans_apply, Equiv.apply_symm_apply]
      change feedbackLabelCost lam w i.val (assignment (assignment.symm (ew i).val)) = _
      rw [assignment.apply_symm_apply]
      rfl
    simp_rw [hterm]
    exact hew
  · have hcard := Fintype.card_congr es
    change (Fintype.card {i : rows // cutRegion left right (M.source i) = 1} : ℝ) ≤ _
    rw [hcard, feedbackWindowSource_card hw hstart hl hr]
    simp only [Nat.cast_sum, feedbackWindowSourceCount, le_refl]

/-- Under the actual iid marked cell law, every pair of non-event zero cuts has the
required comparison for every perfect matching with finite boundary crossing families.
Neither a cell balance identity nor a comparison-cost bound is assumed by this conclusion. -/
theorem feedbackCellBase_windowComparison {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith), ∀ left right : ℝ,
      FeedbackZeroCut w left → FeedbackZeroCut w right →
      ∀ assignment : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1),
      (∀ cut ∈ ({left, right} : Set ℝ),
        {i : FeedbackEventLabel w 1 | Crosses cut (feedbackCellEventPoint w i).1
          (feedbackCellEventPoint w (assignment i)).1}.Finite) →
      Nonempty ((feedbackLabelMatching w assignment).WindowComparison (feedbackLabelCost lam w)
        left right (feedbackWindowSourceCount w left right) (feedbackWindowReward lam w left right)) := by
  filter_upwards [feedbackCellBase_identification_good hlam0 (show lam < 1 / 2 by linarith),
    feedbackCellBase_exists_comparison hlam0 hlam] with w hw hc
  choose e he using hc
  intro left right hl hr assignment hfinite
  exact ⟨feedbackActualWindowComparison hw.1 hw.2.2.1 hl hr assignment hfinite e he⟩

end OTSelector.Matching
