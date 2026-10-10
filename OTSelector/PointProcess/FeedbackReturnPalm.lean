import OTSelector.Limit.FeedbackReturnConfiguration
import OTSelector.Limit.FeedbackCellConcatenation
import OTSelector.Limit.FeedbackEnvironmentIdentification
import OTSelector.PointProcess.RootedCampbell
import OTSelector.Probability.RenewalStationary
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Direct Palm identification for the actual return-cell construction

The key identity sums observations over every actual return root while the observation origin
runs through cell zero.  Invariance of the iid cell sequence under integer shifts changes this
into integration over the disjoint cells of one fixed sequence, which partition the line.
The argument uses the actual root geometry and Tonelli, without a Palm or inversion assumption.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators Classical ENNReal

namespace OTSelector.PointProcess

open OTSelector.Limit

private theorem measurable_rootInterval_lintegral {F : FeedbackCellSequence × ℝ → ℝ≥0∞}
    (hF : Measurable F) (j : ℤ) : Measurable (fun w : FeedbackCellSequence ↦
      ∫⁻ x in Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1)), F (w, x)) := by
  have hA : MeasurableSet {p : FeedbackCellSequence × ℝ |
      feedbackCellRoot p.1 j ≤ p.2 ∧ p.2 < feedbackCellRoot p.1 (j + 1)} :=
    (measurableSet_le ((measurable_feedbackCellRoot j).comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_feedbackCellRoot (j + 1)).comp measurable_fst))
  have h := (hF.indicator hA).lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert h using 1
  funext w
  exact (lintegral_indicator measurableSet_Ico _).symm

private theorem lintegral_Ico_translate (f : ℝ → ℝ≥0∞) (hF : Measurable f)
    (L r : ℝ) :
    (∫⁻ t in Ico 0 L, f (r - t)) =
      ∫⁻ y in Ico (-r) (L - r), f (-y) := by
  have hm : Measurable ((Ico 0 L).indicator (fun t ↦ f (r - t))) :=
    (hF.comp (measurable_const.sub measurable_id)).indicator measurableSet_Ico
  rw [← lintegral_indicator measurableSet_Ico]
  rw [← (measurePreserving_add_right (volume : Measure ℝ) r).lintegral_comp hm]
  have heq : (fun y ↦ (Ico 0 L).indicator (fun t ↦ f (r - t)) (y + r)) =
      (Ico (-r) (L - r)).indicator (fun y ↦ f (-y)) := by
    funext y
    have hmem : y + r ∈ Ico 0 L ↔ y ∈ Ico (-r) (L - r) := by
      simp only [mem_Ico]
      constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
    simp only [Set.indicator_apply, hmem, show r - (y + r) = -y by ring]
  rw [heq, lintegral_indicator measurableSet_Ico]

private theorem feedbackRootSweep_term (w : FeedbackCellSequence) (j : ℤ)
    {F : FeedbackCellSequence × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
      F (IIDShift.shift j w, feedbackCellRoot w j - t)) =
      ∫⁻ y in Ico (feedbackCellRoot (IIDShift.shift j w) (-j))
        (feedbackCellRoot (IIDShift.shift j w) (-j + 1)), F (IIDShift.shift j w, -y) := by
  rw [lintegral_Ico_translate (fun x ↦ F (IIDShift.shift j w, x))
    (hF.comp measurable_prodMk_left),
    feedbackCellRoot_shift, feedbackCellRoot_shift]
  have hidx : -j + 1 + j = (1 : ℤ) := by omega
  have hroot : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
    simpa only [feedbackCellRoot_zero, zero_add] using feedbackCellRoot_add_one w 0
  simp only [neg_add_cancel, feedbackCellRoot_zero, zero_sub, hidx, hroot]

/-- Summing actual return-root observations over the initial cell gives Lebesgue occupation
of the iid rooted sequence. This is the direct, unnormalized Campbell calculation. -/
theorem tsum_lintegral_feedbackReturnRootSweep {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {F : FeedbackCellSequence × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∑' j : ℤ, ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
      F (IIDShift.shift j w, feedbackCellRoot w j - t)
        ∂volume ∂feedbackCellBase lam hlam0 hlam) =
      ∫⁻ w, ∫⁻ x, F (w, x) ∂volume ∂feedbackCellBase lam hlam0 hlam := by
  let G : FeedbackCellSequence × ℝ → ℝ≥0∞ := fun p ↦ F (p.1, -p.2)
  have hG : Measurable G := hF.comp (measurable_fst.prodMk measurable_snd.neg)
  have hterm (j : ℤ) :
      (∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
        F (IIDShift.shift j w, feedbackCellRoot w j - t)
          ∂volume ∂feedbackCellBase lam hlam0 hlam) =
      ∫⁻ w, ∫⁻ y in Ico (feedbackCellRoot w (-j)) (feedbackCellRoot w (-j + 1)),
        G (w, y) ∂volume ∂feedbackCellBase lam hlam0 hlam := by
    simp_rw [feedbackRootSweep_term _ _ hF]
    exact (IIDShift.measurePreserving_shift
      (feedbackMarkedTrajectory lam hlam0 hlam 0) j).lintegral_comp
      (measurable_rootInterval_lintegral hG (-j))
  simp_rw [hterm]
  have hreindex := (Equiv.neg ℤ).tsum_eq (fun j ↦ ∫⁻ w,
    ∫⁻ y in Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1)), G (w, y)
      ∂volume ∂feedbackCellBase lam hlam0 hlam)
  simp only [Equiv.neg_apply] at hreindex
  rw [hreindex]
  rw [← lintegral_tsum (fun j ↦ (measurable_rootInterval_lintegral hG j).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [feedbackCellBase_roots_good hlam0 hlam] with w hw
  rw [tsum_lintegral_feedbackCellRoot_intervals hw]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
    (hF.comp measurable_prodMk_left)

private theorem lintegral_feedbackRoof {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {F : FeedbackCellSequence × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun w ↦ feedbackCellLength (w 0))) =
      ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)), F (w, t)
        ∂volume ∂feedbackCellBase lam hlam0 hlam := by
  have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
  rw [renewalRoofMeasure, ← lintegral_indicator hroof,
    lintegral_prod _ (hF.indicator hroof).aemeasurable]
  apply lintegral_congr
  intro w
  exact lintegral_indicator (measurableSet_Ico (a := (0 : ℝ))
    (b := feedbackCellLength (w 0))) (fun t ↦ F (w, t))

/-- The iid cells and position inside their distinguished cell, normalized by the actual mean. -/
noncomputable def feedbackReturnRoofLaw (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    Measure (FeedbackCellSequence × ℝ) :=
  (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ •
    renewalRoofMeasure (feedbackCellBase lam hlam0 hlam) (fun w ↦ feedbackCellLength (w 0))

instance feedbackReturnRoofLaw_isProbability (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    IsProbabilityMeasure (feedbackReturnRoofLaw lam hlam0 hlam) := by
  constructor
  have hL : Measurable (fun w : FeedbackCellSequence ↦ feedbackCellLength (w 0)) :=
    measurable_feedbackCellLength.comp (measurable_pi_apply 0)
  rw [feedbackReturnRoofLaw, Measure.smul_apply, smul_eq_mul,
    renewalRoofMeasure_univ _ hL,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_feedbackCellBase_length hlam0 hlam 0)
      (ae_of_all _ fun w ↦ feedbackCellLength_nonneg (w 0)),
    integral_feedbackCellBase_length]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (feedbackCellMean_pos hlam0 hlam)) ENNReal.ofReal_ne_top

/-- At any counted return root, read the actual iid sequence with that cell distinguished. -/
noncomputable def feedbackReturnRootedSequence (p : (FeedbackCellSequence × ℝ) × ℝ) :
    FeedbackCellSequence :=
  IIDShift.shift (feedbackCellIndex p.1.1 (p.2 + p.1.2)) p.1.1

theorem measurable_feedbackReturnRootedSequence : Measurable feedbackReturnRootedSequence := by
  have hm : Measurable (fun p : ℤ × FeedbackCellSequence ↦ IIDShift.shift p.1 p.2) :=
    measurable_from_prod_countable_right fun k ↦ IIDShift.measurable_shift k
  have hi : Measurable (fun p : (FeedbackCellSequence × ℝ) × ℝ ↦
      feedbackCellIndex p.1.1 (p.2 + p.1.2)) :=
    measurable_feedbackCellIndex.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.add (measurable_snd.comp measurable_fst)))
  exact hm.comp (hi.prodMk (measurable_fst.comp measurable_fst))

theorem feedbackReturnRootedSequence_at_root {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (t : ℝ) (j : ℤ) :
    feedbackReturnRootedSequence ((w, t), feedbackCellRoot w j - t) = IIDShift.shift j w := by
  unfold feedbackReturnRootedSequence
  rw [sub_add_cancel]
  have hi : feedbackCellIndex w (feedbackCellRoot w j) = j :=
    (feedbackCellIndex_eq_iff hw _ j).mpr
      ⟨le_rfl, (strictMono_feedbackCellRoot hw.1) (by omega)⟩
  rw [hi]

/-- The actual return-root Campbell measure, with its complete sequence seen from each return. -/
noncomputable def feedbackReturnSequenceCampbell (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure (ℝ × FeedbackCellSequence) :=
  rootedCampbell (feedbackReturnRoofLaw lam hlam0 hlam) feedbackReturnCountingKernel
    feedbackReturnRootedSequence

/-- Direct Campbell testing identifies the return-root marks with the actual iid cell law. -/
theorem lintegral_feedbackReturnSequenceCampbell {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {f : ℝ × FeedbackCellSequence → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂feedbackReturnSequenceCampbell lam hlam0 hlam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
        ∫⁻ w, ∫⁻ x, f (x, w) ∂volume ∂feedbackCellBase lam hlam0 hlam := by
  let F : (FeedbackCellSequence × ℝ) × ℝ → ℝ≥0∞ :=
    fun p ↦ f (p.2, feedbackReturnRootedSequence p)
  have hF : Measurable F := hf.comp (measurable_snd.prodMk measurable_feedbackReturnRootedSequence)
  have hN : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      ∫⁻ x, F (p, x) ∂feedbackReturnCountingKernel p) :=
    hF.lintegral_kernel_prod_right' (κ := feedbackReturnCountingKernel)
  rw [feedbackReturnSequenceCampbell, lintegral_rootedCampbell _ _ _
    measurable_feedbackReturnRootedSequence hf, feedbackReturnRoofLaw, lintegral_smul_measure]
  change _ * (∫⁻ p, (∫⁻ x, F (p, x) ∂feedbackReturnCountingKernel p)
    ∂renewalRoofMeasure _ _) = _
  rw [lintegral_feedbackRoof hlam0 hlam hN]
  congr 1
  have hterm (j : ℤ) : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      f (feedbackCellRoot p.1 j - p.2, IIDShift.shift j p.1)) :=
    hf.comp ((((measurable_feedbackCellRoot j).comp measurable_fst).sub measurable_snd).prodMk
      ((IIDShift.measurable_shift j).comp measurable_fst))
  calc
    _ = ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
        ∑' j : ℤ, f (feedbackCellRoot w j - t, IIDShift.shift j w)
          ∂volume ∂feedbackCellBase lam hlam0 hlam := by
      apply lintegral_congr_ae
      filter_upwards [feedbackCellBase_roots_good hlam0 hlam] with w hw
      apply lintegral_congr
      intro t
      rw [feedbackReturnCountingKernel_apply, countingMeasure_feedbackReturnConfiguration_of_good hw,
        lintegral_sum_measure]
      apply tsum_congr
      intro j
      rw [lintegral_dirac]
      exact congrArg (fun v ↦ f (feedbackCellRoot w j - t, v))
        (feedbackReturnRootedSequence_at_root hw t j)
    _ = ∑' j : ℤ, ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength (w 0)),
        f (feedbackCellRoot w j - t, IIDShift.shift j w)
          ∂volume ∂feedbackCellBase lam hlam0 hlam := by
      rw [← lintegral_feedbackRoof hlam0 hlam (Measurable.tsum hterm),
        lintegral_tsum (fun j ↦ (hterm j).aemeasurable)]
      apply tsum_congr
      intro j
      exact lintegral_feedbackRoof hlam0 hlam (hterm j)
    _ = _ := tsum_lintegral_feedbackReturnRootSweep hlam0 hlam (hf.comp measurable_swap)

/-- The actual return Campbell measure is Lebesgue measure times the iid cell law divided by
the actual mean cell length. No stationary Campbell or renewal-inversion formula is assumed. -/
theorem feedbackReturnSequenceCampbell_eq {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    feedbackReturnSequenceCampbell lam hlam0 hlam =
      (volume : Measure ℝ).prod
        ((ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ • feedbackCellBase lam hlam0 hlam) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_feedbackReturnSequenceCampbell hlam0 hlam hf,
    lintegral_prod_symm f hf.aemeasurable, lintegral_smul_measure, smul_eq_mul]

/-- The unnormalized return Palm law is exactly the actual iid cell law divided by its mean. -/
theorem unitWindowPalm_feedbackReturnSequenceCampbell {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    unitWindowPalm (feedbackReturnSequenceCampbell lam hlam0 hlam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ • feedbackCellBase lam hlam0 hlam := by
  rw [feedbackReturnSequenceCampbell_eq hlam0 hlam]
  ext s hs
  rw [unitWindowPalm_apply _ hs, Measure.prod_prod]
  simp

/-- The expected actual return count in a unit interval is the reciprocal mean cell length. -/
theorem lintegral_feedbackReturn_count_unit {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (∫⁻ p, feedbackReturnCountingKernel p (Ioc 0 1)
      ∂feedbackReturnRoofLaw lam hlam0 hlam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ := by
  rw [← unitWindowPalm_rootedCampbell_univ _ _ _ measurable_feedbackReturnRootedSequence]
  change unitWindowPalm (feedbackReturnSequenceCampbell lam hlam0 hlam) univ = _
  rw [unitWindowPalm_feedbackReturnSequenceCampbell hlam0 hlam, Measure.smul_apply]
  simp

/-- Project the actual return-root sequence mark to its concatenated feedback environment. -/
noncomputable def feedbackReturnEnvironmentCampbell (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure (ℝ × FeedbackEnvironment) :=
  (feedbackReturnSequenceCampbell lam hlam0 hlam).map
    (fun p ↦ (p.1, feedbackConcatenatedEnvironment lam p.2))

/-- The return-root environment marks have exactly the rooted iid environment law. -/
theorem unitWindowPalm_feedbackReturnEnvironmentCampbell {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    unitWindowPalm (feedbackReturnEnvironmentCampbell lam hlam0 hlam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ •
        (feedbackCellBase lam hlam0 hlam).map (feedbackConcatenatedEnvironment lam) := by
  have hm : Measurable (fun p : ℝ × FeedbackCellSequence ↦
      (p.1, feedbackConcatenatedEnvironment lam p.2)) :=
    measurable_fst.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_snd)
  ext s hs
  rw [unitWindowPalm_apply _ hs, feedbackReturnEnvironmentCampbell,
    Measure.map_apply hm (measurableSet_Ioc.prod hs), feedbackReturnSequenceCampbell_eq hlam0 hlam]
  change ((volume : Measure ℝ).prod
    ((ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ • feedbackCellBase lam hlam0 hlam))
      (Ioc 0 1 ×ˢ (feedbackConcatenatedEnvironment lam ⁻¹' s)) = _
  rw [Measure.prod_prod, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_feedbackConcatenatedEnvironment lam) hs]
  simp

/-- Record both the actual return configuration and the physical environment at a spatial cut. -/
noncomputable def feedbackReturnEnvironmentObservation (lam : ℝ)
    (p : FeedbackCellSequence × ℝ) : LocalConfiguration (0 : ℝ) × FeedbackEnvironment :=
  (feedbackReturnConfiguration p.1 p.2,
    FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1))

theorem measurable_feedbackReturnEnvironmentObservation (lam : ℝ) :
    Measurable (feedbackReturnEnvironmentObservation lam) := by
  have hc : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      feedbackConcatenatedEnvironment lam p.1) := (measurable_feedbackConcatenatedEnvironment lam).comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ p.1) measurable_fst
  have hr : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1)) :=
    FeedbackEnvironment.measurable_uncurry_reroot.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ (p.2, feedbackConcatenatedEnvironment lam p.1))
    (measurable_snd.prodMk hc)
  exact measurable_feedbackReturnConfiguration.prodMk hr

/-- The actual occupation law jointly recording the return roots and feedback environment. -/
noncomputable def feedbackReturnEnvironmentLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure (LocalConfiguration (0 : ℝ) × FeedbackEnvironment) :=
  (feedbackReturnRoofLaw lam hlam0 hlam).map (feedbackReturnEnvironmentObservation lam)

instance feedbackReturnEnvironmentLaw_isProbability (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure (feedbackReturnEnvironmentLaw lam hlam0 hlam) :=
  Measure.isProbabilityMeasure_map (measurable_feedbackReturnEnvironmentObservation lam).aemeasurable

/-- The environment marginal of the actual root-decorated construction is precisely the proved
stationary feedback law. The return roots have not been assumed to be an environment observable. -/
theorem feedbackReturnEnvironmentLaw_map_environment {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackReturnEnvironmentLaw lam hlam0 hlam).map Prod.snd =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
  rw [feedbackReturnEnvironmentLaw, Measure.map_map measurable_snd
    (measurable_feedbackReturnEnvironmentObservation lam), feedbackReturnRoofLaw, Measure.map_smul,
    feedbackStationaryEnvironmentLaw, renewalStationaryLaw, integral_feedbackCellBase_length]
  rfl

/-- Count the recorded actual return configuration in a return-decorated environment. -/
noncomputable def feedbackReturnEnvironmentCountingKernel :
    Kernel (LocalConfiguration (0 : ℝ) × FeedbackEnvironment) ℝ :=
  LocalConfiguration.randomCountingKernel Prod.fst measurable_fst

instance : IsSFiniteKernel feedbackReturnEnvironmentCountingKernel := by
  unfold feedbackReturnEnvironmentCountingKernel
  infer_instance

/-- Physically reroot the recorded feedback environment at a counted return location. -/
noncomputable def feedbackReturnEnvironmentRooter
    (p : (LocalConfiguration (0 : ℝ) × FeedbackEnvironment) × ℝ) : FeedbackEnvironment :=
  FeedbackEnvironment.reroot p.2 p.1.2

theorem measurable_feedbackReturnEnvironmentRooter :
    Measurable feedbackReturnEnvironmentRooter :=
  FeedbackEnvironment.measurable_uncurry_reroot.comp
    (f := fun p : (LocalConfiguration (0 : ℝ) × FeedbackEnvironment) × ℝ ↦ (p.2, p.1.2))
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

private noncomputable def feedbackReturnRoofRooter (lam : ℝ)
    (p : (FeedbackCellSequence × ℝ) × ℝ) : FeedbackEnvironment :=
  feedbackReturnEnvironmentRooter (feedbackReturnEnvironmentObservation lam p.1, p.2)

private theorem measurable_feedbackReturnRoofRooter (lam : ℝ) :
    Measurable (feedbackReturnRoofRooter lam) := by
  have hm : Measurable (fun p : (FeedbackCellSequence × ℝ) × ℝ ↦
      (feedbackReturnEnvironmentObservation lam p.1, p.2)) :=
    ((measurable_feedbackReturnEnvironmentObservation lam).comp measurable_fst).prodMk measurable_snd
  exact measurable_feedbackReturnEnvironmentRooter.comp
    (f := fun p : (FeedbackCellSequence × ℝ) × ℝ ↦
      (feedbackReturnEnvironmentObservation lam p.1, p.2)) hm

private theorem feedbackReturnEnvironmentCampbell_eq_roof_of_covariant {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcov : ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ,
      feedbackConcatenatedEnvironment lam (IIDShift.shift j w) =
        FeedbackEnvironment.reroot (feedbackCellRoot w j) (feedbackConcatenatedEnvironment lam w)) :
    feedbackReturnEnvironmentCampbell lam hlam0 hlam =
      rootedCampbell (feedbackReturnRoofLaw lam hlam0 hlam) feedbackReturnCountingKernel
        (feedbackReturnRoofRooter lam) := by
  have hmark : Measurable (fun p : ℝ × FeedbackCellSequence ↦
      (p.1, feedbackConcatenatedEnvironment lam p.2)) :=
    measurable_fst.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_snd)
  rw [feedbackReturnEnvironmentCampbell, feedbackReturnSequenceCampbell, rootedCampbell,
    Measure.map_map hmark (measurable_snd.prodMk measurable_feedbackReturnRootedSequence)]
  unfold rootedCampbell
  apply Measure.map_congr
  have hbase : ∀ᵐ p ∂feedbackReturnRoofLaw lam hlam0 hlam,
      feedbackCellRootsGood p.1 ∧ ∀ j : ℤ,
        feedbackConcatenatedEnvironment lam (IIDShift.shift j p.1) =
          FeedbackEnvironment.reroot (feedbackCellRoot p.1 j)
            (feedbackConcatenatedEnvironment lam p.1) := by
    apply Measure.ae_smul_measure
    apply ae_restrict_of_ae
    exact Measure.quasiMeasurePreserving_fst.ae ((feedbackCellBase_roots_good hlam0 hlam).and hcov)
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_eq_fun
      (hmark.comp (measurable_snd.prodMk measurable_feedbackReturnRootedSequence))
      (measurable_snd.prodMk (measurable_feedbackReturnRoofRooter lam))
  filter_upwards [hbase] with p hp
  rw [feedbackReturnCountingKernel_apply, countingMeasure_feedbackReturnConfiguration_of_good hp.1,
    Measure.ae_sum_iff]
  intro j
  apply (ae_dirac_iff (measurableSet_eq_fun
    ((hmark.comp (measurable_snd.prodMk measurable_feedbackReturnRootedSequence)).comp
      measurable_prodMk_left)
    ((measurable_snd.prodMk (measurable_feedbackReturnRoofRooter lam)).comp
      measurable_prodMk_left))).mpr
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  change feedbackConcatenatedEnvironment lam
    (feedbackReturnRootedSequence ((p.1, p.2), feedbackCellRoot p.1 j - p.2)) =
      FeedbackEnvironment.reroot (feedbackCellRoot p.1 j - p.2)
        (FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1))
  rw [feedbackReturnRootedSequence_at_root hp.1, hp.2 j, FeedbackEnvironment.reroot_add]
  congr 1
  ring

private theorem feedbackReturnEnvironmentLawCampbell_eq_roof {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    rootedCampbell (feedbackReturnEnvironmentLaw lam hlam0 hlam)
      feedbackReturnEnvironmentCountingKernel feedbackReturnEnvironmentRooter =
      rootedCampbell (feedbackReturnRoofLaw lam hlam0 hlam) feedbackReturnCountingKernel
        (feedbackReturnRoofRooter lam) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_rootedCampbell _ _ _ measurable_feedbackReturnEnvironmentRooter hf,
    lintegral_rootedCampbell _ _ _ (measurable_feedbackReturnRoofRooter lam) hf,
    feedbackReturnEnvironmentLaw]
  have hF : Measurable (fun p : (LocalConfiguration (0 : ℝ) × FeedbackEnvironment) × ℝ ↦
      f (p.2, feedbackReturnEnvironmentRooter p)) :=
    hf.comp (measurable_snd.prodMk measurable_feedbackReturnEnvironmentRooter)
  rw [lintegral_map (hF.lintegral_kernel_prod_right'
    (κ := feedbackReturnEnvironmentCountingKernel)) (measurable_feedbackReturnEnvironmentObservation lam)]
  rfl

/-- Physically rooting the actual occupation process at its return points gives exactly the
Campbell measure computed from iid return-root environments. -/
theorem rootedCampbell_feedbackReturnEnvironmentLaw {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    rootedCampbell (feedbackReturnEnvironmentLaw lam hlam0 hlam)
      feedbackReturnEnvironmentCountingKernel feedbackReturnEnvironmentRooter =
      feedbackReturnEnvironmentCampbell lam hlam0 hlam := by
  rw [feedbackReturnEnvironmentLawCampbell_eq_roof hlam0 hlam]
  exact (feedbackReturnEnvironmentCampbell_eq_roof_of_covariant hlam0 hlam
    (ae_feedbackConcatenatedEnvironment_shift hlam0 hlam)).symm

/-- The actual return-point Palm environment law is the concatenated iid environment law
divided by the actual mean cell length. The counting kernel and spatial rerooting are concrete. -/
theorem unitWindowPalm_feedbackReturnEnvironmentLaw {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    unitWindowPalm (rootedCampbell (feedbackReturnEnvironmentLaw lam hlam0 hlam)
      feedbackReturnEnvironmentCountingKernel feedbackReturnEnvironmentRooter) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ •
        (feedbackCellBase lam hlam0 hlam).map (feedbackConcatenatedEnvironment lam) := by
  rw [rootedCampbell_feedbackReturnEnvironmentLaw hlam0 hlam,
    unitWindowPalm_feedbackReturnEnvironmentCampbell hlam0 hlam]

end OTSelector.PointProcess
