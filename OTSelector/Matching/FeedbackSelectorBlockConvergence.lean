import OTSelector.PointProcess.MatchingSceneSelectorLimit
import OTSelector.PointProcess.MatchingSceneGoodSubsequence
import OTSelector.Finite.OptimizerMeasurability
import OTSelector.Feedback.FeedbackEnvironmentResidualSelection
import OTSelector.PointProcess.MatchingSceneSelectedEnvironment

/-!
# Physical block convergence for the original Euclidean optimizer

Every actual selected optimizer limit has the same source Palm mark law as a stationary
finite-energy candidate. A persistent positive probability of a bad physical block would
therefore give actual bad samples whose block averages converge to the prescribed value.
-/

open MeasureTheory Filter Set Function Topology
open scoped BigOperators Classical ENNReal

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample

/-- The original physical block average is measurable up to a null set under the original iid
law, using the already proved measurability of the original optimizer's selected point. -/
theorem aemeasurable_sourceHeightBlockMarks_euclideanOptimizer {n : ℕ}
    (ψ : C(UnitMark × UnitMark, ℝ)) (u v : ℝ) :
    AEMeasurable (fun sample : FiniteSample n ↦
      sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  have hf : Measurable (fun p : PlanPoint ↦
      if (p.1.1 : ℝ) ∈ Ioc u v then ψ (p.1.2, p.2.2) else 0) :=
    (ψ.continuous.measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd)).ite
      ((measurable_subtype_coe.comp measurable_fst.fst) measurableSet_Ioc) measurable_const
  unfold sourceHeightBlockMarks
  apply AEMeasurable.const_mul
  exact Finset.aemeasurable_fun_sum _ fun i _ ↦
    hf.comp_aemeasurable (aemeasurable_euclideanMatchedPoint i)

/-- Thus each original optimizer block exceedance has a well-defined completed-law probability. -/
theorem nullMeasurableSet_sourceHeightBlockMarks_euclideanOptimizer {n : ℕ}
    (ψ : C(UnitMark × UnitMark, ℝ)) (u v value ε : ℝ) :
    NullMeasurableSet {sample : FiniteSample n |
      ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v-value|}
      (finiteSampleLaw n : Measure (FiniteSample n)) :=
  nullMeasurableSet_le aemeasurable_const
    (continuous_abs.measurable.comp_aemeasurable
      ((aemeasurable_sourceHeightBlockMarks_euclideanOptimizer ψ u v).sub aemeasurable_const))

end OTSelector.FiniteSample

namespace OTSelector.Matching
open PointProcess

/-- The physical block limit of actual good optimizer samples agrees with the projective law
of any already constructed stationary candidate. -/
theorem tendsto_sourceHeightBlockMarks_of_good_candidate
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hNpos : ∀ k, 0 < N k)
    (sample : ∀ k, FiniteSample (N k))
    {lam amplitude globalQ endpointQ C u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hamp : 0 < amplitude)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hgood : ∀ k, sample k ∈
      feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (N k))
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw
        ((sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)
        (sample k).euclideanOptimizer ((N k : ℝ) * u) ((N k : ℝ) * v))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    (henv : (ν : Measure MatchingScene).map feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)))
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (hPenv : P.map feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)))
    (hPstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hPcand : ∀ᵐ scene ∂P, FeedbackSceneEnergyCandidate lam scene)
    (hPcross : (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂P) < ∞)
    (ψ : C(UnitMark × UnitMark, ℝ)) :
    Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (sample k).euclideanOptimizer ψ u v)
      atTop (𝓝 (∫ m, ψ m ∂feedbackProjectiveLaw P)) := by
  obtain ⟨hstat, hcand, _, hcross, _, hblock⟩ :=
    MatchingScene.feedbackFGL2_selectorLimit_of_good
      hN hNpos sample hlam0 hlam hamp hu huv hv hgood hlaw hlim htight henv
  have hκ : feedbackProjectiveLaw (ν : Measure MatchingScene) = feedbackProjectiveLaw P := by
    apply feedbackProjectiveLaws_unique hlam0 (hlam.trans (by norm_num)) hlam
      (ν : Measure MatchingScene) P henv hPenv hstat hPstat
    · intro k
      fin_cases k
      · exact hcand
      · exact hPcand
    · intro k
      fin_cases k
      · exact hcross
      · exact hPcross
  simpa only [hκ] using hblock ψ

private theorem tendsto_nonneg_zero_of_no_frequently_ge
    {p : ℕ → ℝ} (hpos : ∀ n, 0 ≤ p n)
    (hbad : ∀ δ : ℝ, 0 < δ → ¬∃ᶠ n in atTop, δ ≤ p n) :
    Tendsto p atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (hpos n)
  · intro b hb
    simpa only [not_frequently, not_le] using hbad b hb

private theorem tendsto_row_bad_probability_zero_of_selected_limits
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (value : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hselect : ∀ δ : ℝ, 0 < δ →
      (∃ᶠ n in atTop, δ ≤ (P n).real {ω | ε ≤ |X n ω-value|}) →
      ∃ N : ℕ → ℕ, ∃ sample : ∀ k, Ω (N k),
        (∀ k, ε ≤ |X (N k) (sample k)-value|) ∧
        Tendsto (fun k ↦ X (N k) (sample k)) atTop (𝓝 value)) :
    Tendsto (fun n ↦ (P n).real {ω | ε ≤ |X n ω-value|}) atTop (𝓝 0) := by
  apply tendsto_nonneg_zero_of_no_frequently_ge (fun _ ↦ measureReal_nonneg)
  intro δ hδ hbad
  obtain ⟨N, sample, hsample, hlim⟩ := hselect δ hδ hbad
  obtain ⟨k, hk⟩ := (hlim.eventually (Metric.ball_mem_nhds value hε)).exists
  have hclose : |X (N k) (sample k)-value| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hk
  exact (hsample k).not_gt hclose

/-- Internal connection point for the actual selection and residual-identification theorems.
It retains the original good samples and their actual root-law limit. -/
private def ActualIdentifiedBlockSelection {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (u v : ℝ) (huv : u < v) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ bad : ∀ n, Set (FiniteSample (n + 1)),
    (∃ᶠ n in atTop,
      δ ≤ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real (bad n)) →
    ∃ amplitude globalQ endpointQ C : ℝ,
      ∃ residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ,
        ∃ data : FeedbackGoodSceneSubsequence
          hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad residual,
          0 < amplitude ∧ (data.limit : Measure MatchingScene).map feedbackSceneEnvironment =
            Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num))

private theorem block_probability_zero_of_actual_identified_selection
    {lam u v : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hselect : ActualIdentifiedBlockSelection hlam0 hlam u v huv)
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (hPenv : P.map feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)))
    (hPstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hPcand : ∀ᵐ scene ∂P, FeedbackSceneEnergyCandidate lam scene)
    (hPcross : (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂P) < ∞)
    (ψ : C(UnitMark × UnitMark, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
      {sample | ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v -
        ∫ m, ψ m ∂feedbackProjectiveLaw P|}) atTop (𝓝 0) := by
  apply tendsto_row_bad_probability_zero_of_selected_limits
    (fun n ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))))
    (fun _ sample ↦ sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v)
    (∫ m, ψ m ∂feedbackProjectiveLaw P) hε
  intro δ hδ hbad
  obtain ⟨A, q, qE, C, residual, data, hA, henv⟩ := hselect δ hδ _ hbad
  refine ⟨data.index, data.sample, fun k ↦ (data.good_bad k).2, ?_⟩
  exact tendsto_sourceHeightBlockMarks_of_good_candidate
    ((tendsto_add_atTop_nat 1).comp data.strictMono_index.tendsto_atTop)
    (fun _ ↦ Nat.succ_pos _) data.sample hlam0 hlam hA hu huv hv
    (fun k ↦ (data.good_bad k).1) (fun _ ↦ rfl) data.law_tendsto data.tight henv
    P hPenv hPstat hPcand hPcross ψ

private theorem exists_candidate_of_actual_identified_selection
    {lam u v : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hselect : ActualIdentifiedBlockSelection hlam0 hlam u v huv) :
    ∃ P : ProbabilityMeasure MatchingScene,
      (P : Measure MatchingScene).map feedbackSceneEnvironment =
        Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)) ∧
      (∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (P : Measure MatchingScene) P) ∧
      (∀ᵐ scene ∂(P : Measure MatchingScene), FeedbackSceneEnergyCandidate lam scene) ∧
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(P : Measure MatchingScene)) < ∞ := by
  have hbad : ∃ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real univ :=
    (Eventually.of_forall fun _ ↦ by rw [probReal_univ]; norm_num).frequently
  obtain ⟨A, q, qE, C, residual, data, hA, henv⟩ :=
    hselect (1 / 2) (by norm_num) (fun _ ↦ univ) hbad
  have hN := (tendsto_add_atTop_nat 1).comp data.strictMono_index.tendsto_atTop
  obtain ⟨hstat, hcand, _, hcross, _, _⟩ :=
    MatchingScene.feedbackFGL2_selectorLimit_of_good hN
      (fun _ ↦ Nat.succ_pos _) data.sample hlam0 hlam hA hu huv hv
      (fun k ↦ (data.good_bad k).1) (fun _ ↦ rfl) data.law_tendsto data.tight henv
  exact ⟨data.limit, henv, hstat, hcand, hcross⟩

private theorem exists_projective_blockLimit_of_actual_identified_selection
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hselect : ∀ (u v : ℝ), 0 < u → ∀ huv : u < v, v < 1 →
      ActualIdentifiedBlockSelection hlam0 hlam u v huv) :
    ∃ κ : ProbabilityMeasure (UnitMark × UnitMark),
      (κ : Measure (UnitMark × UnitMark)).map Prod.fst = (volume : Measure UnitMark) ∧
      (κ : Measure (UnitMark × UnitMark)).map Prod.snd = (volume : Measure UnitMark) ∧
      ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
        ∀ (ψ : C(UnitMark × UnitMark, ℝ)) (ε : ℝ), 0 < ε →
          Tendsto (fun n : ℕ ↦
            (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
              {sample | ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v -
                ∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))|}) atTop (𝓝 0) := by
  obtain ⟨P, hPenv, hPstat, hPcand, hPcross⟩ :=
    exists_candidate_of_actual_identified_selection hlam0 hlam
      (show (0 : ℝ) < 1 / 3 by norm_num) (show (1 / 3 : ℝ) < 2 / 3 by norm_num)
      (show (2 / 3 : ℝ) < 1 by norm_num)
      (hselect (1 / 3) (2 / 3) (by norm_num) (by norm_num) (by norm_num))
  have hperfect := hPcand.mono fun _ hc ↦ hc.perfect
  let κ : ProbabilityMeasure (UnitMark × UnitMark) :=
    ⟨feedbackProjectiveLaw (P : Measure MatchingScene),
      feedbackProjectiveLaw_isProbability hlam0 (hlam.trans (by norm_num))
        (P : Measure MatchingScene) hPenv hperfect⟩
  refine ⟨κ, ?_, ?_, ?_⟩
  · exact feedbackProjectiveLaw_source hlam0 (hlam.trans (by norm_num))
      (P : Measure MatchingScene) hPenv hperfect
  · exact feedbackProjectiveLaw_target hlam0 (hlam.trans (by norm_num))
      (P : Measure MatchingScene) hPenv hperfect hPstat
  · intro u v hu huv hv ψ ε hε
    exact block_probability_zero_of_actual_identified_selection hlam0 hlam hu huv hv
      (hselect u v hu huv hv) (P : Measure MatchingScene) hPenv hPstat hPcand hPcross ψ hε

/-- The original finite residual estimates supply the selection constraints, and the selected
countable identities identify its entire limiting environment. -/
private theorem actualIdentifiedBlockSelection {lam u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ActualIdentifiedBlockSelection hlam0 hlam u v huv := by
  intro δ hδ bad hbad
  obtain ⟨A, q, qE, C, hA, hq, _hqE, hcoef, _hC, hselect⟩ :=
    exists_feedbackSelectorGood_weak_subsequence_parameters hlam0 hlam hδ hu huv hv
  let residual := feedbackCountableSpatialResidual
    hlam0.le (hlam.trans (by norm_num)) A u v
  obtain ⟨data⟩ := hselect bad residual hbad
    (tendsto_feedbackCountableSpatialResidual_badProbability
      hlam0 hlam hA hq hcoef hu huv hv)
  exact ⟨A, q, qE, C, residual, data, hA,
    data.environmentLaw_eq hA hq hcoef hu hv⟩

/-- Actual finite Euclidean optimizers produce a stationary, locally minimizing, finite-energy
candidate with the constructed feedback environment law. -/
theorem exists_feedbackSelectorCandidate {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∃ P : ProbabilityMeasure MatchingScene,
      (P : Measure MatchingScene).map feedbackSceneEnvironment =
        Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)) ∧
      (∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (P : Measure MatchingScene) P) ∧
      (∀ᵐ scene ∂(P : Measure MatchingScene), FeedbackSceneEnergyCandidate lam scene) ∧
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(P : Measure MatchingScene)) < ∞ := by
  apply exists_candidate_of_actual_identified_selection hlam0 hlam
    (show (0 : ℝ) < 1 / 3 by norm_num) (show (1 / 3 : ℝ) < 2 / 3 by norm_num)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  exact actualIdentifiedBlockSelection hlam0 hlam (by norm_num) (by norm_num) (by norm_num)

/-- Every continuous physical block mark average of the original iid optimizer converges in
probability to the source Palm average of any stationary finite-energy candidate. -/
theorem feedback_sourceHeightBlockMarks_tendstoInProbability
    {lam u v : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (hPenv : P.map feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)))
    (hPstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hPcand : ∀ᵐ scene ∂P, FeedbackSceneEnergyCandidate lam scene)
    (hPcross : (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂P) < ∞)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (ψ : C(UnitMark × UnitMark, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
      {sample | ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v -
        ∫ m, ψ m ∂feedbackProjectiveLaw P|}) atTop (𝓝 0) :=
  block_probability_zero_of_actual_identified_selection hlam0 hlam hu huv hv
    (actualIdentifiedBlockSelection hlam0 hlam hu huv hv)
    P hPenv hPstat hPcand hPcross ψ hε

/-- There is one coupling of the uniform mark laws that governs every strict interior physical
block of the original iid Euclidean optimizer. The limit and its convergence are constructed
from actual good samples, without a limiting-environment or extraction hypothesis. -/
theorem exists_feedbackProjectiveBlockLimit {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∃ κ : ProbabilityMeasure (UnitMark × UnitMark),
      (κ : Measure (UnitMark × UnitMark)).map Prod.fst = (volume : Measure UnitMark) ∧
      (κ : Measure (UnitMark × UnitMark)).map Prod.snd = (volume : Measure UnitMark) ∧
      ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
        ∀ (ψ : C(UnitMark × UnitMark, ℝ)) (ε : ℝ), 0 < ε →
          Tendsto (fun n : ℕ ↦
            (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
              {sample | ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v -
                ∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))|}) atTop (𝓝 0) :=
  exists_projective_blockLimit_of_actual_identified_selection hlam0 hlam
    (fun _ _ hu huv hv ↦ actualIdentifiedBlockSelection hlam0 hlam hu huv hv)

end OTSelector.Matching
