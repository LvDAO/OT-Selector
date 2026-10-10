import OTSelector.Feedback.FeedbackRecursion

/-!
# The finite event-driven feedback curve

The recursion in `FeedbackRecursion` gives the knots of the graph.  This file turns those knots
into one real-valued curve.  A step absorbs every source and target label at the selected
coordinate, so simultaneous crossings are represented by one interval endpoint rather than by
an artificial ordering of equal events.
-/

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-! ## States, current, and knots -/

@[simp]
theorem feedbackState_current_eq_card_sub (lam x0 p0 : ℝ) (m : ℕ) :
    (feedbackState sample lam x0 p0 m).current =
      ((feedbackState sample lam x0 p0 m).seenSource.card : ℤ) -
        (feedbackState sample lam x0 p0 m).seenTarget.card := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [feedbackState_succ, FeedbackStepState.step_current, ih]
      change
        ((feedbackState sample lam x0 p0 m).seenSource.card : ℤ) -
              (feedbackState sample lam x0 p0 m).seenTarget.card +
            (FeedbackStepState.newSource sample lam
              (feedbackState sample lam x0 p0 m)).card -
          (FeedbackStepState.newTarget sample lam
            (feedbackState sample lam x0 p0 m)).card =
        (((feedbackState sample lam x0 p0 m).seenSource ∪
              FeedbackStepState.newSource sample lam
                (feedbackState sample lam x0 p0 m)).card : ℤ) -
          ((feedbackState sample lam x0 p0 m).seenTarget ∪
              FeedbackStepState.newTarget sample lam
                (feedbackState sample lam x0 p0 m)).card
      rw [Finset.card_union_of_disjoint
        (FeedbackStepState.newSource_disjoint_seenSource sample lam _).symm]
      rw [Finset.card_union_of_disjoint
        (FeedbackStepState.newTarget_disjoint_seenTarget sample lam _).symm]
      push_cast
      ring

@[simp]
theorem feedbackState_terminal_current (lam x0 p0 : ℝ) :
    (feedbackState sample lam x0 p0 (2 * n)).current = 0 := by
  have hdone := sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
  have hall := (FeedbackStepState.candidates_eq_empty_iff sample lam
    (feedbackState sample lam x0 p0 (2 * n))).mp hdone
  rw [sample.feedbackState_current_eq_card_sub, hall.1, hall.2]
  simp

@[simp]
theorem feedbackState_terminal_slope {lam : ℝ} (x0 p0 : ℝ) :
    (feedbackState sample lam x0 p0 (2 * n)).slope lam = 0 := by
  rw [FeedbackStepState.slope, sample.feedbackState_terminal_current]
  simp [feedbackSlope]

/-- The x-coordinate of the `m`-th recursive state. -/
noncomputable def feedbackKnot (lam x0 p0 : ℝ) (m : ℕ) : ℝ :=
  (feedbackState sample lam x0 p0 m).x

/-- The graph value at the `m`-th recursive state. -/
noncomputable def feedbackKnotValue (lam x0 p0 : ℝ) (m : ℕ) : ℝ :=
  (feedbackState sample lam x0 p0 m).p

@[simp]
theorem feedbackKnot_zero (lam x0 p0 : ℝ) :
    feedbackKnot sample lam x0 p0 0 = x0 := by
  simp [feedbackKnot, initialFeedbackState]

@[simp]
theorem feedbackKnotValue_zero (lam x0 p0 : ℝ) :
    feedbackKnotValue sample lam x0 p0 0 = p0 := by
  simp [feedbackKnotValue, initialFeedbackState]

theorem feedbackKnotValue_succ (lam x0 p0 : ℝ) (m : ℕ) :
    feedbackKnotValue sample lam x0 p0 (m + 1) =
      segmentCurve (feedbackKnot sample lam x0 p0 m)
        (feedbackKnotValue sample lam x0 p0 m)
        ((feedbackState sample lam x0 p0 m).slope lam)
        (feedbackKnot sample lam x0 p0 (m + 1)) := by
  rfl

theorem feedbackKnot_value_consistency (lam x0 p0 : ℝ) (m : ℕ) :
    segmentCurve (feedbackKnot sample lam x0 p0 m)
        (feedbackKnotValue sample lam x0 p0 m)
        ((feedbackState sample lam x0 p0 m).slope lam)
        (feedbackKnot sample lam x0 p0 (m + 1)) =
      feedbackKnotValue sample lam x0 p0 (m + 1) := by
  exact (sample.feedbackKnotValue_succ lam x0 p0 m).symm

theorem feedbackState_x_step_mono
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (m : ℕ) :
    feedbackKnot sample lam x0 p0 m ≤ feedbackKnot sample lam x0 p0 (m + 1) := by
  by_cases hcand :
      ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty
  · exact (sample.feedbackState_x_strictMono_step hlam0 hlamHalf x0 p0 m hcand).le
  · have hempty :
        (feedbackState sample lam x0 p0 m).candidates sample lam = ∅ := by
      by_contra hne
      exact hcand (Finset.nonempty_iff_ne_empty.mpr hne)
    change (feedbackState sample lam x0 p0 m).x ≤
      (feedbackState sample lam x0 p0 (m + 1)).x
    rw [sample.feedbackState_succ_eq_of_candidates_eq_empty lam x0 p0 m hempty]

theorem feedbackState_x_mono
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    Monotone (feedbackKnot sample lam x0 p0) := by
  intro m k hmk
  induction hmk with
  | refl => exact le_rfl
  | @step k hmk ih =>
      exact ih.trans (sample.feedbackState_x_step_mono hlam0 hlamHalf x0 p0 k)

/-! ## Lipschitz gluing -/

theorem realLipschitz_if_le_const
    {lam c : ℝ} (_hlam0 : 0 ≤ lam) {f g : ℝ → ℝ}
    (hf : RealLipschitz lam f) (hg : RealLipschitz lam g) (hfg : f c = g c) :
    RealLipschitz lam (fun x ↦ if x ≤ c then f x else g x) := by
  intro x y
  by_cases hx : x ≤ c
  · by_cases hy : y ≤ c
    · simp only [ite_eq_left hx, ite_eq_left hy]
      exact hf x y
    · have hyc : c ≤ y := le_of_not_ge hy
      have hxy : x ≤ y := hx.trans hyc
      have hleft : |f c - f x| ≤ lam * |c - x| := hf x c
      have hright : |g y - g c| ≤ lam * |y - c| := hg c y
      calc
        |(if y ≤ c then f y else g y) - (if x ≤ c then f x else g x)| =
            |g y - f x| := by simp only [ite_eq_right hy, ite_eq_left hx]
        _ = |(g y - g c) + (f c - f x)| := by rw [hfg]; ring_nf
        _ ≤ |g y - g c| + |f c - f x| := abs_add_le _ _
        _ ≤ lam * |y - c| + lam * |c - x| := add_le_add hright hleft
        _ = lam * |y - x| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hyc),
            abs_of_nonneg (sub_nonneg.mpr hx),
            abs_of_nonneg (sub_nonneg.mpr hxy)]
          rw [← mul_add]
          congr 1
          ring_nf
  · have hxc : c ≤ x := le_of_not_ge hx
    by_cases hy : y ≤ c
    · have hxy : y ≤ x := hy.trans hxc
      have hleft : |f y - f c| ≤ lam * |y - c| := hf c y
      have hright : |g c - g x| ≤ lam * |c - x| := hg x c
      calc
        |(if y ≤ c then f y else g y) - (if x ≤ c then f x else g x)| =
            |g x - f y| := by
              rw [ite_eq_left hy, ite_eq_right hx, abs_sub_comm]
        _ = |(g x - g c) + (f c - f y)| := by rw [hfg]; ring_nf
        _ ≤ |g x - g c| + |f c - f y| := abs_add_le _ _
        _ ≤ lam * |x - c| + lam * |c - y| := by
          exact add_le_add (by simpa only [abs_sub_comm] using hright) (by
            simpa only [abs_sub_comm] using hleft)
        _ = lam * |x - y| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hxc),
            abs_of_nonneg (sub_nonneg.mpr hy),
            abs_of_nonneg (sub_nonneg.mpr hxy)]
          rw [← mul_add]
          congr 1
          ring_nf
        _ = lam * |y - x| := by rw [abs_sub_comm]
    · simp only [ite_eq_right hx, ite_eq_right hy]
      exact hg x y

/-! ## Terminal state and the finite recursive curve -/

@[simp]
theorem feedbackKnotValue_terminal (lam x0 p0 : ℝ) :
    feedbackKnotValue sample lam x0 p0 (2 * n + 0) =
      feedbackKnotValue sample lam x0 p0 (2 * n) := by
  rfl

/- The branch at `m ≥ H` is deliberately `p_m`; along the recursion it is reached first at `m=H`.
   The stable-state theorem in `FeedbackRecursion` then identifies all later terminal values. -/
noncomputable def feedbackCurveAux (lam x0 p0 : ℝ) (H m : ℕ) (x : ℝ) : ℝ :=
  if h : m < H then
    if x ≤ feedbackKnot sample lam x0 p0 (m + 1) then
      segmentCurve (feedbackKnot sample lam x0 p0 m)
        (feedbackKnotValue sample lam x0 p0 m)
        ((feedbackState sample lam x0 p0 m).slope lam) x
    else feedbackCurveAux lam x0 p0 H (m + 1) x
  else feedbackKnotValue sample lam x0 p0 m
termination_by H - m
decreasing_by omega

theorem feedbackCurveAux_at_next_knot
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (H m : ℕ) (hm : m < H) :
    feedbackCurveAux sample lam x0 p0 H (m + 1)
        (feedbackKnot sample lam x0 p0 (m + 1)) =
      feedbackKnotValue sample lam x0 p0 (m + 1) := by
  by_cases hnext : m + 1 < H
  · have hmono := sample.feedbackState_x_step_mono
      hlam0 hlamHalf x0 p0 (m + 1)
    rw [feedbackCurveAux, dite_eq_left hnext, ite_eq_left hmono]
    simp [segmentCurve]
  · have hlast : H ≤ m + 1 := by omega
    have hnot : ¬m + 1 < H := not_lt_of_ge hlast
    rw [feedbackCurveAux, dite_eq_right hnot]

theorem feedbackCurveAux_realLipschitz
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (H m : ℕ) (x0 p0 : ℝ) :
    RealLipschitz lam (feedbackCurveAux sample lam x0 p0 H m) := by
  induction hdiff : H - m using Nat.strong_induction_on generalizing m with
  | h d ih =>
      by_cases hm : m < H
      · have hrec :
            RealLipschitz lam (feedbackCurveAux sample lam x0 p0 H (m + 1)) := by
          exact ih (H - (m + 1)) (by omega) (m + 1) rfl
        have hseg : RealLipschitz lam (fun x ↦
            segmentCurve (feedbackKnot sample lam x0 p0 m)
              (feedbackKnotValue sample lam x0 p0 m)
              ((feedbackState sample lam x0 p0 m).slope lam) x) := by
          intro x y
          have hdiff :
              segmentCurve (feedbackKnot sample lam x0 p0 m)
                  (feedbackKnotValue sample lam x0 p0 m)
                  ((feedbackState sample lam x0 p0 m).slope lam) y -
                segmentCurve (feedbackKnot sample lam x0 p0 m)
                  (feedbackKnotValue sample lam x0 p0 m)
                  ((feedbackState sample lam x0 p0 m).slope lam) x =
              ((feedbackState sample lam x0 p0 m).slope lam) * (y - x) := by
            dsimp [segmentCurve]
            ring
          calc
            |segmentCurve (feedbackKnot sample lam x0 p0 m)
                (feedbackKnotValue sample lam x0 p0 m)
                ((feedbackState sample lam x0 p0 m).slope lam) y -
                segmentCurve (feedbackKnot sample lam x0 p0 m)
                  (feedbackKnotValue sample lam x0 p0 m)
                  ((feedbackState sample lam x0 p0 m).slope lam) x| =
                |((feedbackState sample lam x0 p0 m).slope lam)| * |y - x| := by
                  rw [hdiff, abs_mul]
            _ ≤ lam * |y - x| := by
              exact mul_le_mul_of_nonneg_right
                (abs_feedbackSlope_le hlam0) (abs_nonneg _)
        have hglue := realLipschitz_if_le_const hlam0 hseg hrec
          (by
            exact (sample.feedbackCurveAux_at_next_knot hlam0 hlamHalf x0 p0 H m hm).symm)
        have haux_eq : feedbackCurveAux sample lam x0 p0 H m =
            (fun x ↦
              if x ≤ feedbackKnot sample lam x0 p0 (m + 1) then
                segmentCurve (feedbackKnot sample lam x0 p0 m)
                  (feedbackKnotValue sample lam x0 p0 m)
                  ((feedbackState sample lam x0 p0 m).slope lam) x
              else feedbackCurveAux sample lam x0 p0 H (m + 1) x) := by
          funext x
          rw [feedbackCurveAux, dite_eq_left hm]
        rw [haux_eq]
        exact hglue
      · intro x y
        simp [feedbackCurveAux, hm]
        exact mul_nonneg hlam0 (abs_nonneg _)

/-! ## Global curve -/

noncomputable def feedbackCurve (lam x0 p0 : ℝ) (x : ℝ) : ℝ :=
  if x ≤ x0 then p0 else
    feedbackCurveAux sample lam x0 p0 (2 * n) 0 x

theorem feedbackCurveAux_zero_at_x0
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    feedbackCurveAux sample lam x0 p0 (2 * n) 0 x0 = p0 := by
  by_cases hH : 0 < 2 * n
  · have hmono := sample.feedbackState_x_step_mono
      hlam0 hlamHalf x0 p0 0
    have hbound : x0 ≤ feedbackKnot sample lam x0 p0 (0 + 1) := by
      simpa only [feedbackKnot_zero] using hmono
    rw [feedbackCurveAux, dite_eq_left hH, ite_eq_left hbound]
    simp [feedbackKnot, feedbackKnotValue, segmentCurve, feedbackState_zero,
      initialFeedbackState]
  · have hH0 : 2 * n = 0 := Nat.eq_zero_of_not_pos hH
    rw [feedbackCurveAux, hH0]
    simp [feedbackKnotValue, feedbackState_zero, initialFeedbackState]

theorem feedbackCurve_realLipschitz
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    RealLipschitz lam (feedbackCurve sample lam x0 p0) := by
  have hconst : RealLipschitz lam (fun _ : ℝ ↦ p0) := by
    intro x y
    simp
    exact mul_nonneg hlam0 (abs_nonneg _)
  have haux := sample.feedbackCurveAux_realLipschitz hlam0 hlamHalf (2 * n) 0 x0 p0
  have hglue := realLipschitz_if_le_const hlam0 hconst haux
    (sample.feedbackCurveAux_zero_at_x0 hlam0 hlamHalf x0 p0).symm
  change RealLipschitz lam (fun x ↦
    if x ≤ x0 then p0 else feedbackCurveAux sample lam x0 p0 (2 * n) 0 x)
  exact hglue

theorem feedbackCurve_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    Continuous (feedbackCurve sample lam x0 p0) := by
  have hLip : LipschitzWith (Real.toNNReal lam) (feedbackCurve sample lam x0 p0) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    simpa only [Real.dist_eq, Real.toNNReal_of_nonneg hlam0, abs_sub_comm] using
      sample.feedbackCurve_realLipschitz hlam0 hlamHalf x0 p0 x y
  exact hLip.continuous

noncomputable def feedbackGraph
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) : FeedbackGraph lam :=
  { curve := feedbackCurve sample lam x0 p0
    lam_nonneg := hlam0
    lam_lt_half := hlamHalf
    lipschitz := sample.feedbackCurve_realLipschitz hlam0 hlamHalf x0 p0 }

@[simp]
theorem feedbackGraph_curve
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    (sample.feedbackGraph hlam0 hlamHalf x0 p0).curve =
      feedbackCurve sample lam x0 p0 :=
  rfl

end FiniteSample

end OTSelector
