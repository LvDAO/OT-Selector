import OTSelector.Feedback.FiniteHistoryHazardSection
import OTSelector.Feedback.FiniteHistoryProductSection
import OTSelector.Feedback.AdaptiveDeferredDecision

/-!
# Finite-product survival calculus on one affine feedback section

For a fixed terminal state and a fixed set of already revealed labels, this file records the
elementary finite-product calculation behind the survival loss on the remaining labels.  The
factors are the algebraic (unclipped) one-point masses, so the calculation is valid on a bulk
interval where the corresponding sections stay in the rank strip.  No compensator or intensity
claim is made here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-! ## One-point algebraic masses -/

/-- The unscaled source area along the affine continuation of `terminal`. -/
noncomputable def feedbackSourceRemainingAreaAt (lam : ℝ)
    (terminal : FeedbackStepState n) (x : ℝ) : ℝ :=
  sourceUnclippedRemainingMass n
    (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x

/-- The unscaled target area along the affine continuation of `terminal`. -/
noncomputable def feedbackTargetRemainingAreaAt (lam : ℝ)
    (terminal : FeedbackStepState n) (x : ℝ) : ℝ :=
  targetUnclippedRemainingMass n
    (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x

/-- The algebraic source one-point remaining real mass. -/
noncomputable def feedbackSourceRemainingRealMassAt (lam : ℝ)
    (terminal : FeedbackStepState n) (x : ℝ) : ℝ :=
  feedbackSourceRemainingAreaAt lam terminal x / (n : ℝ)

/-- The algebraic target one-point remaining real mass. -/
noncomputable def feedbackTargetRemainingRealMassAt (lam : ℝ)
    (terminal : FeedbackStepState n) (x : ℝ) : ℝ :=
  feedbackTargetRemainingAreaAt lam terminal x / (n : ℝ)

/-- The one-point mass attached to a feedback label. -/
noncomputable def feedbackLabelRemainingRealMassAt (lam : ℝ)
    (terminal : FeedbackStepState n) (x : ℝ) : FeedbackLabel n → ℝ
  | Sum.inl _ => feedbackSourceRemainingRealMassAt lam terminal x
  | Sum.inr _ => feedbackTargetRemainingRealMassAt lam terminal x

/-- The one-point mass attached to an unseen label. -/
noncomputable def feedbackUnseenLabelRemainingRealMassAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S) : ℝ :=
  feedbackLabelRemainingRealMassAt lam terminal x (label : FeedbackLabel n)

/-- Product survival mass of the unseen coordinates. -/
noncomputable def feedbackUnseenSurvivalMassAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : ℝ :=
  ∏ label ∈ feedbackUnseenFinset S,
    feedbackLabelRemainingRealMassAt lam terminal x label

/-! ## Derivatives of the one-point factors -/

private theorem hasDerivAt_feedbackSourceRemainingAreaAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => feedbackSourceRemainingAreaAt lam terminal y)
      (-(1 - terminal.slope lam / 2)) x := by
  have h := (hasDerivAt_mul_const (x := x)
      (terminal.slope lam / 2 - 1)).add_const
      ((n : ℝ) + terminal.p / 2 - terminal.slope lam * terminal.x / 2)
  have h' : HasDerivAt
      (fun y : ℝ => feedbackSourceRemainingAreaAt lam terminal y)
      (terminal.slope lam / 2 - 1) x := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with y
    simp [feedbackSourceRemainingAreaAt, sourceUnclippedRemainingMass, segmentCurve]
    ring
  have hderiv : terminal.slope lam / 2 - 1 =
      -(1 - terminal.slope lam / 2) := by ring
  exact h'.congr_deriv hderiv

private theorem hasDerivAt_feedbackTargetRemainingAreaAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => feedbackTargetRemainingAreaAt lam terminal y)
      (-(1 + 3 * terminal.slope lam / 2)) x := by
  have h := (hasDerivAt_mul_const (x := x)
      (-(1 + 3 * terminal.slope lam / 2))).add_const
      ((n : ℝ) - 3 * terminal.p / 2 + 3 * terminal.slope lam * terminal.x / 2)
  have h' : HasDerivAt
      (fun y : ℝ => feedbackTargetRemainingAreaAt lam terminal y)
      (-(1 + 3 * terminal.slope lam / 2)) x := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with y
    simp [feedbackTargetRemainingAreaAt, targetUnclippedRemainingMass, segmentCurve]
    ring
  exact h'

set_option linter.unusedVariables false in
theorem hasDerivAt_feedbackSourceRemainingRealMassAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => feedbackSourceRemainingRealMassAt lam terminal y)
      (-(1 - terminal.slope lam / 2) / (n : ℝ)) x := by
  have h := (hasDerivAt_feedbackSourceRemainingAreaAt lam terminal x).div_const (n : ℝ)
  simpa [feedbackSourceRemainingRealMassAt] using h

set_option linter.unusedVariables false in
theorem hasDerivAt_feedbackTargetRemainingRealMassAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => feedbackTargetRemainingRealMassAt lam terminal y)
      (-(1 + 3 * terminal.slope lam / 2) / (n : ℝ)) x := by
  have h := (hasDerivAt_feedbackTargetRemainingAreaAt lam terminal x).div_const (n : ℝ)
  simpa [feedbackTargetRemainingRealMassAt] using h

private noncomputable def feedbackUnseenLabelDerivativeAt
    (lam : ℝ) (terminal : FeedbackStepState n)
    (label : feedbackUnseenFinset S) : ℝ :=
  match label.1 with
  | Sum.inl _ => -(1 - terminal.slope lam / 2) / (n : ℝ)
  | Sum.inr _ => -(1 + 3 * terminal.slope lam / 2) / (n : ℝ)

theorem hasDerivAt_feedbackUnseenLabelRemainingRealMassAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) :
    HasDerivAt
      (fun y => feedbackUnseenLabelRemainingRealMassAt lam terminal y S label)
      (feedbackUnseenLabelDerivativeAt lam terminal label) x := by
  rcases label with ⟨label, hlabel⟩
  cases label with
  | inl i =>
      simpa [feedbackUnseenLabelRemainingRealMassAt,
        feedbackLabelRemainingRealMassAt, feedbackUnseenLabelDerivativeAt] using
        hasDerivAt_feedbackSourceRemainingRealMassAt hn lam terminal x
  | inr j =>
      simpa [feedbackUnseenLabelRemainingRealMassAt,
        feedbackLabelRemainingRealMassAt, feedbackUnseenLabelDerivativeAt] using
        hasDerivAt_feedbackTargetRemainingRealMassAt hn lam terminal x

/-! ## Finite product derivative and colour split -/

private noncomputable def feedbackUnseenDerivativeProductTerm
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (label : FeedbackLabel n) : ℝ :=
  (∏ label' ∈ (feedbackUnseenFinset S).erase label,
      feedbackLabelRemainingRealMassAt lam terminal x label') *
    (match label with
      | Sum.inl _ => -(1 - terminal.slope lam / 2) / (n : ℝ)
      | Sum.inr _ => -(1 + 3 * terminal.slope lam / 2) / (n : ℝ))

noncomputable def feedbackUnseenSourceLabels
    (S : Finset (FeedbackLabel n)) : Finset (FeedbackLabel n) :=
  (feedbackUnseenFinset S).filter fun label ↦
    ∃ i : Fin n, (label : FeedbackLabel n) = Sum.inl i

noncomputable def feedbackUnseenTargetLabels
    (S : Finset (FeedbackLabel n)) : Finset (FeedbackLabel n) :=
  (feedbackUnseenFinset S).filter fun label ↦
    ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j

noncomputable def feedbackUnseenSourceCount
    (S : Finset (FeedbackLabel n)) : ℕ :=
  (feedbackUnseenSourceLabels S).card

noncomputable def feedbackUnseenTargetCount
    (S : Finset (FeedbackLabel n)) : ℕ :=
  (feedbackUnseenTargetLabels S).card

noncomputable def feedbackSourceSurvivalFluxAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : ℝ :=
  ∑ label ∈ feedbackUnseenSourceLabels S,
    feedbackUnseenDerivativeProductTerm lam terminal x S label

noncomputable def feedbackTargetSurvivalFluxAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : ℝ :=
  ∑ label ∈ feedbackUnseenTargetLabels S,
    feedbackUnseenDerivativeProductTerm lam terminal x S label

private theorem continuous_feedbackLabelRemainingRealMassAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (label : FeedbackLabel n) :
    Continuous (fun y : ℝ => feedbackLabelRemainingRealMassAt lam terminal y label) := by
  cases label with
  | inl i =>
      simpa [feedbackLabelRemainingRealMassAt] using
        (continuous_iff_continuousAt.mpr fun y ↦
          (hasDerivAt_feedbackSourceRemainingRealMassAt hn lam terminal y).continuousAt)
  | inr j =>
      simpa [feedbackLabelRemainingRealMassAt] using
        (continuous_iff_continuousAt.mpr fun y ↦
          (hasDerivAt_feedbackTargetRemainingRealMassAt hn lam terminal y).continuousAt)

private theorem continuous_feedbackUnseenDerivativeProductTerm
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Continuous (fun y : ℝ =>
      feedbackUnseenDerivativeProductTerm lam terminal y S label) := by
  unfold feedbackUnseenDerivativeProductTerm
  apply Continuous.mul
  · apply continuous_finsetProd
    intro label' hlabel'
    exact continuous_feedbackLabelRemainingRealMassAt hn lam terminal label'
  · exact continuous_const

theorem continuous_feedbackSourceSurvivalFluxAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) :
    Continuous (fun y : ℝ => feedbackSourceSurvivalFluxAt lam terminal y S) := by
  unfold feedbackSourceSurvivalFluxAt
  apply continuous_finsetSum
  intro label hlabel
  exact continuous_feedbackUnseenDerivativeProductTerm hn lam terminal S label

theorem continuous_feedbackTargetSurvivalFluxAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) :
    Continuous (fun y : ℝ => feedbackTargetSurvivalFluxAt lam terminal y S) := by
  unfold feedbackTargetSurvivalFluxAt
  apply continuous_finsetSum
  intro label hlabel
  exact continuous_feedbackUnseenDerivativeProductTerm hn lam terminal S label

theorem hasDerivAt_feedbackUnseenSurvivalMassAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) :
    HasDerivAt (fun y => feedbackUnseenSurvivalMassAt lam terminal y S)
      (feedbackSourceSurvivalFluxAt lam terminal x S +
        feedbackTargetSurvivalFluxAt lam terminal x S) x := by
  let f : feedbackUnseenFinset S → ℝ → ℝ := fun label y ↦
    feedbackUnseenLabelRemainingRealMassAt lam terminal y S label
  let f' : feedbackUnseenFinset S → ℝ := fun label ↦
    feedbackUnseenLabelDerivativeAt lam terminal label
  have hprod := HasDerivAt.finsetProd (u := feedbackUnseenFinset S)
    (f := fun label : FeedbackLabel n ↦
      fun y : ℝ => feedbackLabelRemainingRealMassAt lam terminal y label)
    (f' := fun label : FeedbackLabel n ↦ match label with
      | Sum.inl _ => -(1 - terminal.slope lam / 2) / (n : ℝ)
      | Sum.inr _ => -(1 + 3 * terminal.slope lam / 2) / (n : ℝ))
    (x := x) (fun label _ ↦ by
      cases label with
      | inl i =>
          simpa [feedbackLabelRemainingRealMassAt] using
            hasDerivAt_feedbackSourceRemainingRealMassAt hn lam terminal x
      | inr j =>
          simpa [feedbackLabelRemainingRealMassAt] using
            hasDerivAt_feedbackTargetRemainingRealMassAt hn lam terminal x)
  have hprod_fun : (∏ label ∈ feedbackUnseenFinset S,
      (fun y : ℝ => feedbackLabelRemainingRealMassAt lam terminal y label)) =
      (fun y => ∏ label ∈ feedbackUnseenFinset S,
        feedbackLabelRemainingRealMassAt lam terminal y label) := by
    funext y
    rw [Finset.prod_apply]
  rw [hprod_fun] at hprod
  rw [show (fun y => ∏ label ∈ feedbackUnseenFinset S,
      feedbackLabelRemainingRealMassAt lam terminal y label) =
      (fun y => feedbackUnseenSurvivalMassAt lam terminal y S) by rfl] at hprod
  have hsplit :
      (∑ label ∈ feedbackUnseenFinset S,
        (∏ j ∈ (feedbackUnseenFinset S).erase label,
          feedbackLabelRemainingRealMassAt lam terminal x j) •
          (match label with
            | Sum.inl _ => -(1 - terminal.slope lam / 2) / (n : ℝ)
            | Sum.inr _ => -(1 + 3 * terminal.slope lam / 2) / (n : ℝ))) =
      feedbackSourceSurvivalFluxAt lam terminal x S +
        feedbackTargetSurvivalFluxAt lam terminal x S := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := feedbackUnseenFinset S)
      (p := fun label ↦ ∃ i : Fin n, (label : FeedbackLabel n) = Sum.inl i)]
    · simp only [feedbackSourceSurvivalFluxAt, feedbackTargetSurvivalFluxAt,
        feedbackUnseenDerivativeProductTerm, smul_eq_mul]
      have htargetFilter : feedbackUnseenTargetLabels S =
          (feedbackUnseenFinset S).filter
            (fun label ↦ ¬ ∃ i : Fin n, (label : FeedbackLabel n) = Sum.inl i) := by
        ext label
        cases label <;> simp [feedbackUnseenTargetLabels]
      rw [htargetFilter]
      rfl
  rw [hsplit] at hprod
  simpa [feedbackUnseenSurvivalMassAt] using hprod

/-! ## Flux form when the factors are positive -/

private theorem feedbackSourceSurvivalTerm_eq
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (hsource : 0 < feedbackSourceRemainingRealMassAt lam terminal x)
    (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenSourceLabels S) :
    feedbackUnseenDerivativeProductTerm lam terminal x S label =
      -feedbackUnseenSurvivalMassAt lam terminal x S *
        (1 / feedbackSourceRemainingAreaAt lam terminal x) *
          (1 - terminal.slope lam / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harea : feedbackSourceRemainingAreaAt lam terminal x ≠ 0 := by
    intro hzero
    have hmzero : feedbackSourceRemainingRealMassAt lam terminal x = 0 := by
      simp [feedbackSourceRemainingRealMassAt, hzero]
    linarith
  have hmem : label ∈ feedbackUnseenFinset S :=
    (Finset.mem_filter.mp hlabel).1
  have hprod := Finset.mul_prod_erase (feedbackUnseenFinset S)
    (fun z : FeedbackLabel n ↦ feedbackLabelRemainingRealMassAt lam terminal x z) hmem
  have hprod' :
      feedbackLabelRemainingRealMassAt lam terminal x label *
          (∏ z ∈ (feedbackUnseenFinset S).erase label,
            feedbackLabelRemainingRealMassAt lam terminal x z) =
        feedbackUnseenSurvivalMassAt lam terminal x S := by
    simpa [feedbackUnseenSurvivalMassAt] using hprod
  cases label with
  | inl i =>
      have hfactor : feedbackLabelRemainingRealMassAt lam terminal x (Sum.inl i) =
          feedbackSourceRemainingRealMassAt lam terminal x := rfl
      rw [hfactor] at hprod'
      rw [← hprod']
      simp only [feedbackUnseenDerivativeProductTerm]
      simp [feedbackSourceRemainingRealMassAt]
      field_simp [feedbackSourceRemainingAreaAt, hn0, harea]
      ring
  | inr j =>
      have hfalse : ¬(∃ i : Fin n, (Sum.inr j : FeedbackLabel n) = Sum.inl i) := by
        simp
      exact False.elim (hfalse ((Finset.mem_filter.mp hlabel).2))

private theorem feedbackTargetSurvivalTerm_eq
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (htarget : 0 < feedbackTargetRemainingRealMassAt lam terminal x)
    (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenTargetLabels S) :
    feedbackUnseenDerivativeProductTerm lam terminal x S label =
      -feedbackUnseenSurvivalMassAt lam terminal x S *
        (1 / feedbackTargetRemainingAreaAt lam terminal x) *
          (1 + 3 * terminal.slope lam / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harea : feedbackTargetRemainingAreaAt lam terminal x ≠ 0 := by
    intro hzero
    have hmzero : feedbackTargetRemainingRealMassAt lam terminal x = 0 := by
      simp [feedbackTargetRemainingRealMassAt, hzero]
    linarith
  have hmem : label ∈ feedbackUnseenFinset S :=
    (Finset.mem_filter.mp hlabel).1
  have hprod := Finset.mul_prod_erase (feedbackUnseenFinset S)
    (fun z : FeedbackLabel n ↦ feedbackLabelRemainingRealMassAt lam terminal x z) hmem
  have hprod' :
      feedbackLabelRemainingRealMassAt lam terminal x label *
          (∏ z ∈ (feedbackUnseenFinset S).erase label,
            feedbackLabelRemainingRealMassAt lam terminal x z) =
        feedbackUnseenSurvivalMassAt lam terminal x S := by
    simpa [feedbackUnseenSurvivalMassAt] using hprod
  cases label with
  | inl i =>
      have hfalse : ¬(∃ j : Fin n, (Sum.inl i : FeedbackLabel n) = Sum.inr j) := by
        simp
      exact False.elim (hfalse ((Finset.mem_filter.mp hlabel).2))
  | inr j =>
      have hfactor : feedbackLabelRemainingRealMassAt lam terminal x (Sum.inr j) =
          feedbackTargetRemainingRealMassAt lam terminal x := rfl
      rw [hfactor] at hprod'
      rw [← hprod']
      simp only [feedbackUnseenDerivativeProductTerm]
      simp [feedbackTargetRemainingRealMassAt]
      field_simp [feedbackTargetRemainingAreaAt, hn0, harea]
      ring

theorem feedbackSourceSurvivalFluxAt_eq
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (hsource : 0 < feedbackSourceRemainingRealMassAt lam terminal x) :
    feedbackSourceSurvivalFluxAt lam terminal x S =
      -feedbackUnseenSurvivalMassAt lam terminal x S *
        ((feedbackUnseenSourceCount S : ℝ) /
          feedbackSourceRemainingAreaAt lam terminal x) *
          (1 - terminal.slope lam / 2) := by
  classical
  calc
    feedbackSourceSurvivalFluxAt lam terminal x S =
        ∑ label ∈ feedbackUnseenSourceLabels S,
          (-feedbackUnseenSurvivalMassAt lam terminal x S *
            (1 / feedbackSourceRemainingAreaAt lam terminal x) *
              (1 - terminal.slope lam / 2)) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact feedbackSourceSurvivalTerm_eq hn lam terminal x S hsource label hlabel
    _ = -feedbackUnseenSurvivalMassAt lam terminal x S *
        ((feedbackUnseenSourceCount S : ℝ) /
          feedbackSourceRemainingAreaAt lam terminal x) *
          (1 - terminal.slope lam / 2) := by
      simp [feedbackUnseenSourceCount]
      ring

theorem feedbackTargetSurvivalFluxAt_eq
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (htarget : 0 < feedbackTargetRemainingRealMassAt lam terminal x) :
    feedbackTargetSurvivalFluxAt lam terminal x S =
      -feedbackUnseenSurvivalMassAt lam terminal x S *
        ((feedbackUnseenTargetCount S : ℝ) /
          feedbackTargetRemainingAreaAt lam terminal x) *
          (1 + 3 * terminal.slope lam / 2) := by
  classical
  calc
    feedbackTargetSurvivalFluxAt lam terminal x S =
        ∑ label ∈ feedbackUnseenTargetLabels S,
          (-feedbackUnseenSurvivalMassAt lam terminal x S *
            (1 / feedbackTargetRemainingAreaAt lam terminal x) *
              (1 + 3 * terminal.slope lam / 2)) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact feedbackTargetSurvivalTerm_eq hn lam terminal x S htarget label hlabel
    _ = -feedbackUnseenSurvivalMassAt lam terminal x S *
        ((feedbackUnseenTargetCount S : ℝ) /
          feedbackTargetRemainingAreaAt lam terminal x) *
          (1 + 3 * terminal.slope lam / 2) := by
      simp [feedbackUnseenTargetCount]
      ring

/-! ## Integral loss identities -/

/-- The nonnegative source contribution to survival loss (when the section is in bulk). -/
noncomputable def feedbackSourceSurvivalLossFluxAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : ℝ :=
  -feedbackSourceSurvivalFluxAt lam terminal x S

/-- The nonnegative target contribution to survival loss (when the section is in bulk). -/
noncomputable def feedbackTargetSurvivalLossFluxAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : ℝ :=
  -feedbackTargetSurvivalFluxAt lam terminal x S

/-- Source-only cumulative survival loss on an interval. -/
noncomputable def feedbackSourceCumulativeFlux
    (lam : ℝ) (terminal : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (a b : ℝ) : ℝ :=
  ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S

theorem feedbackUnseenSurvivalMassAt_loss_eq_intervalIntegral
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (a b : ℝ)
    (hsourceInt : IntervalIntegrable
      (fun y => feedbackSourceSurvivalFluxAt lam terminal y S) volume a b)
    (htargetInt : IntervalIntegrable
      (fun y => feedbackTargetSurvivalFluxAt lam terminal y S) volume a b) :
    feedbackUnseenSurvivalMassAt lam terminal a S -
        feedbackUnseenSurvivalMassAt lam terminal b S =
      ∫ y in a..b,
        (feedbackSourceSurvivalLossFluxAt lam terminal y S +
          feedbackTargetSurvivalLossFluxAt lam terminal y S) := by
  have hint : IntervalIntegrable
      (fun y => feedbackSourceSurvivalFluxAt lam terminal y S +
        feedbackTargetSurvivalFluxAt lam terminal y S) volume a b :=
    hsourceInt.add htargetInt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => feedbackUnseenSurvivalMassAt lam terminal y S)
    (f' := fun y => feedbackSourceSurvivalFluxAt lam terminal y S +
      feedbackTargetSurvivalFluxAt lam terminal y S)
    (a := a) (b := b)
    (fun y _ ↦ hasDerivAt_feedbackUnseenSurvivalMassAt hn lam terminal y S) hint
  calc
    feedbackUnseenSurvivalMassAt lam terminal a S -
        feedbackUnseenSurvivalMassAt lam terminal b S =
        -(feedbackUnseenSurvivalMassAt lam terminal b S -
          feedbackUnseenSurvivalMassAt lam terminal a S) := by ring
    _ = -(∫ y in a..b,
        (feedbackSourceSurvivalFluxAt lam terminal y S +
          feedbackTargetSurvivalFluxAt lam terminal y S)) := by rw [hFTC]
    _ = ∫ y in a..b,
        (feedbackSourceSurvivalLossFluxAt lam terminal y S +
          feedbackTargetSurvivalLossFluxAt lam terminal y S) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext y
      simp [feedbackSourceSurvivalLossFluxAt, feedbackTargetSurvivalLossFluxAt]
      ring

theorem intervalIntegrable_feedbackSourceSurvivalFluxAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (a b : ℝ) :
    IntervalIntegrable
      (fun y => feedbackSourceSurvivalFluxAt lam terminal y S) volume a b :=
  (continuous_feedbackSourceSurvivalFluxAt hn lam terminal S).continuousOn.intervalIntegrable

theorem intervalIntegrable_feedbackTargetSurvivalFluxAt
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (a b : ℝ) :
    IntervalIntegrable
      (fun y => feedbackTargetSurvivalFluxAt lam terminal y S) volume a b :=
  (continuous_feedbackTargetSurvivalFluxAt hn lam terminal S).continuousOn.intervalIntegrable

theorem feedbackUnseenSurvivalMassAt_loss_eq_intervalIntegral'
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (a b : ℝ) :
    feedbackUnseenSurvivalMassAt lam terminal a S -
        feedbackUnseenSurvivalMassAt lam terminal b S =
      ∫ y in a..b,
        (feedbackSourceSurvivalLossFluxAt lam terminal y S +
          feedbackTargetSurvivalLossFluxAt lam terminal y S) := by
  exact feedbackUnseenSurvivalMassAt_loss_eq_intervalIntegral hn lam terminal S a b
    (intervalIntegrable_feedbackSourceSurvivalFluxAt hn lam terminal S a b)
    (intervalIntegrable_feedbackTargetSurvivalFluxAt hn lam terminal S a b)

theorem feedbackSourceCumulativeFlux_eq_integral
    (lam : ℝ) (terminal : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (a b : ℝ) :
    feedbackSourceCumulativeFlux lam terminal S a b =
      ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S :=
  rfl

/-! ## Identification with the conditioned unseen product rectangle -/

theorem feedbackUnseenSurvivalMassAt_eq_feedbackUnseenTupleLaw_real
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (hbulk : ∀ label ∈ feedbackUnseenFinset S,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x u ∧
        sourceBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x v ∧
        targetBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x v ≤ n) :
    feedbackUnseenSurvivalMassAt lam terminal x S =
      (feedbackUnseenTupleLaw S).real
        (feedbackUnseenRectangularSetAt lam terminal x S) := by
  classical
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n)
  have hremaining : ∀ label, MeasurableSet (remaining label) := by
    intro label
    exact measurableSet_feedbackLabelRemainingSetAt lam terminal x
      (label : FeedbackLabel n)
  have hpi := OTSelector.Probability.measure_univ_pi
    (unitSquareUniform : Measure MarkedHeight) remaining hremaining
  have hpiReal :
      (feedbackUnseenTupleLaw S).real
        (feedbackUnseenRectangularSetAt lam terminal x S) =
        ∏ label : feedbackUnseenFinset S,
          (unitSquareUniform : Measure MarkedHeight).real (remaining label) := by
    simp only [Measure.real, feedbackUnseenTupleLaw,
      feedbackUnseenRectangularSetAt, remaining]
    rw [hpi, ENNReal.toReal_prod]
  rw [hpiReal]
  simp only [feedbackUnseenSurvivalMassAt]
  simp only [remaining]
  have hsubprod :
      (∏ label : feedbackUnseenFinset S,
        (unitSquareUniform : Measure MarkedHeight).real
          (feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n))) =
      ∏ label ∈ (feedbackUnseenFinset S).attach,
        (unitSquareUniform : Measure MarkedHeight).real
          (feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n)) := by
    rw [Finset.univ_eq_attach]
  rw [hsubprod, ← Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro label _hmem
  rcases label with ⟨label, hbase⟩
  cases label with
  | inl i =>
      simpa [feedbackLabelRemainingRealMassAt, feedbackLabelRemainingSetAt,
        feedbackSourceRemainingRealMassAt,
        feedbackSourceRemainingAreaAt] using
        (unitSquareUniform_sourceRawRemainingSetAt_mass terminal lam x hn
          (fun u ↦ (hbulk (Sum.inl i) hbase).1 u |>.1)
          (fun u ↦ (hbulk (Sum.inl i) hbase).1 u |>.2)).symm
  | inr j =>
      simpa [feedbackLabelRemainingRealMassAt, feedbackLabelRemainingSetAt,
        feedbackTargetRemainingRealMassAt,
        feedbackTargetRemainingAreaAt] using
        (unitSquareUniform_targetRawRemainingSetAt_mass terminal lam x hn
          (fun v ↦ (hbulk (Sum.inr j) hbase).2 v |>.1)
          (fun v ↦ (hbulk (Sum.inr j) hbase).2 v |>.2)).symm

/-! ## Pointwise identification with the product law -/

theorem feedbackLabelRemainingRealMassAt_eq_unitSquareUniform_real
    (hn : 0 < n) (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (label : FeedbackLabel n)
    (hbulk : (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x u ∧
        sourceBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x v ∧
        targetBoundary (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x v ≤ n) :
    feedbackLabelRemainingRealMassAt lam terminal x label =
      (unitSquareUniform : Measure MarkedHeight).real
        (feedbackLabelRemainingSetAt lam terminal x label) := by
  cases label with
  | inl i =>
      simpa [feedbackLabelRemainingRealMassAt, feedbackSourceRemainingRealMassAt,
        feedbackSourceRemainingAreaAt, feedbackLabelRemainingSetAt] using
        (unitSquareUniform_sourceRawRemainingSetAt_mass terminal lam x hn
          (fun u ↦ (hbulk.1 u).1) (fun u ↦ (hbulk.1 u).2)).symm
  | inr j =>
      simpa [feedbackLabelRemainingRealMassAt, feedbackTargetRemainingRealMassAt,
        feedbackTargetRemainingAreaAt, feedbackLabelRemainingSetAt] using
        (unitSquareUniform_targetRawRemainingSetAt_mass terminal lam x hn
          (fun v ↦ (hbulk.2 v).1) (fun v ↦ (hbulk.2 v).2)).symm

end OTSelector
