import OTSelector.Feedback.FeedbackEnvironmentCountableTests
import OTSelector.PointProcess.MatchingSceneGoodSubsequence
import OTSelector.PointProcess.MatchingSceneResidualLimit

/-! # Actual countable residuals in good-sample selection and their weak limit -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096

namespace OTSelector
open PointProcess FiniteSample

/-- Finite past test data and a nonnegative rational time `a/(d+1)`. -/
abbrev ActualEnvironmentResidualIndex := EnvironmentResidualTestCode × ℕ × ℕ
noncomputable instance : Encodable ActualEnvironmentResidualIndex := Encodable.ofCountable _

noncomputable def countableEnvironmentResidualTime (i : ActualEnvironmentResidualIndex) : ℝ≥0 :=
  (i.2.2 : ℝ≥0)/(i.2.1+1 : ℕ)

/-- This countable family consists of the original scene observables used in the ENV proof. -/
noncomputable def countableEnvironmentResidual (lam : ℝ)
    (i : ActualEnvironmentResidualIndex) : MatchingScene → ℝ := by
  rcases i with ⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩
  exact MatchingScene.pastMarkedResidual lam
    (fun j ↦ countablePastTest (fs j)) (fun j ↦ countablePastTest (ft j))
    (Probability.countableBoundedTest (EnvironmentPastCoordinates ns nt) hi)
    b (countableEnvironmentMarkTest pi) ((a:ℝ≥0)/(d+1:ℕ))

/-- The genuine residual integral of the original finite optimizer root law. -/
noncomputable def feedbackEnvironmentSpatialResidual {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (amplitude u v : ℝ)
    (i : ActualEnvironmentResidualIndex) (sample : FiniteSample n) : ℝ :=
  ∫scene, countableEnvironmentResidual lam i scene ∂sample.rootedMatchingSceneLaw
    (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) sample.euclideanOptimizer
    ((n:ℝ)*u) ((n:ℝ)*v)

/-- Natural-number enumeration for the existing actual good-sample selection theorem. -/
noncomputable def feedbackCountableSpatialResidual {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (amplitude u v : ℝ)
    (m n : ℕ) (sample : FiniteSample (n+1)) : ℝ :=
  match Encodable.decode₂ ActualEnvironmentResidualIndex m with
  | none => 0
  | some i => feedbackEnvironmentSpatialResidual hlam0 hlamHalf amplitude u v i sample

/-- The actual original good-event mask has vanishing residual tails for each member of the
countable family. Survival and the shrinking VC drift are supplied by proved finite results. -/
theorem tendsto_feedbackEnvironmentSpatialResidual_badProbability
    {lam amplitude globalQ endpointQ C u v ε : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1/8) (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8*(globalQ+33) < amplitude) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (i : ActualEnvironmentResidualIndex) (hε : 0 < ε) :
    Tendsto (fun n ↦ (finiteSampleLaw n : Measure (FiniteSample n)).real
      (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C n ∩
        {sample | ε < |feedbackEnvironmentSpatialResidual hlam0.le (hlam.trans (by norm_num))
          amplitude u v i sample|})) atTop (𝓝 0) := by
  rcases i with ⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩
  let t : ℝ≥0 := (a:ℝ≥0)/(d+1:ℕ)
  let B (n : ℕ) := feedbackA2AsymptoticBuffer amplitude n
  let left (n : ℕ) := (n:ℝ)*u-B n
  let right (n : ℕ) := (n:ℝ)*v-B n
  have hwindow : ∀ᶠ n in atTop, 0 ≤ left n ∧ left n < right n ∧
      right n+(t:ℝ) < feedbackA2AsymptoticHorizon amplitude n := by
    filter_upwards [eventually_feedbackSelection_bulk_fit hamp hu hv (t:ℝ)] with n hn
    dsimp [left,right,B]
    have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn.1
    exact ⟨by linarith [hn.2.2.1,t.2], sub_lt_sub_right (mul_lt_mul_of_pos_left huv hn0) _,
      by linarith [hn.2.2.2]⟩
  have hwidth : Tendsto (fun n ↦ right n-left n) atTop atTop := by
    have heq : (fun n ↦ right n-left n) = (fun n : ℕ ↦ (n:ℝ)*(v-u)) := by funext n; dsimp [right,left]; ring
    rw [heq]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.mpr huv)
  have hbase := tendsto_measureReal_environmentPastMarkedResidualBadEvent_zero
    hlam0 hlam (feedbackA2AsymptoticEta_pos hlam0).le (feedbackA2AsymptoticEta_small hlam0)
    hamp hε (feedbackA2AsymptoticHorizon amplitude) t left right hwindow hwidth
    (fun j ↦ countablePastTest (fs j)) (fun j ↦ countablePastTest (ft j))
    (Probability.countableBoundedTest (EnvironmentPastCoordinates ns nt) hi)
    (fun j x w hx ↦ countablePastTest_eq_zero_of_nonneg (fs j) x w hx)
    (fun j x w hx ↦ countablePastTest_eq_zero_of_nonneg (ft j) x w hx)
    b (countableEnvironmentMarkTest pi)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hbase
  filter_upwards [eventually_feedbackSelectorGood_survival (C := C) (endpointQ := endpointQ)
    hlam0 hlam hglobalQ hcoefficient, hwindow] with n hn hw
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro sample hs
  refine ⟨feedbackSelectorGoodEvent.a1 hs.1, hn sample hs.1, ?_⟩
  have he := integral_pastMarkedResidual_rootedSceneLaw_eq hlam0.le (hlam.trans (by norm_num))
    (feedbackA2AsymptoticEta lam) (B n) (feedbackA2AsymptoticHorizon amplitude n)
    (fun j ↦ countablePastTest (fs j)) (fun j ↦ countablePastTest (ft j))
    (Probability.countableBoundedTest (EnvironmentPastCoordinates ns nt) hi)
    b (countableEnvironmentMarkTest pi) t hw.2.1.le sample
  simp only [left,right,←add_sub_assoc,add_sub_cancel_left] at he
  have hnorm : feedbackEnvironmentSpatialResidual hlam0.le (hlam.trans (by norm_num))
      amplitude u v (⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩) sample =
      environmentPastMarkedSpatialResidual hlam0.le (hlam.trans (by norm_num))
        (feedbackA2AsymptoticEta lam) (B n) (feedbackA2AsymptoticHorizon amplitude n)
        (fun j ↦ countablePastTest (fs j)) (fun j ↦ countablePastTest (ft j))
        (Probability.countableBoundedTest (EnvironmentPastCoordinates ns nt) hi)
        b (countableEnvironmentMarkTest pi) t (left n) (right n) sample := he
  have hsmall : ε < |feedbackEnvironmentSpatialResidual hlam0.le (hlam.trans (by norm_num))
      amplitude u v (⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩) sample| := hs.2
  rw [hnorm] at hsmall
  exact hsmall.le

/-- The exact residual hypothesis required by `exists_feedbackSelectorGood_weak_subsequence_parameters`. -/
theorem tendsto_feedbackCountableSpatialResidual_badProbability
    {lam amplitude globalQ endpointQ C u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1/8) (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8*(globalQ+33) < amplitude) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (finiteSampleLaw (n+1) : Measure (FiniteSample (n+1))).real
      (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (n+1) ∩
        {sample | ε < |feedbackCountableSpatialResidual hlam0.le (hlam.trans (by norm_num))
          amplitude u v m n sample|})) atTop (𝓝 0) := by
  cases hd : Encodable.decode₂ ActualEnvironmentResidualIndex m with
  | none =>
      simpa only [feedbackCountableSpatialResidual, hd, abs_zero, not_lt_of_ge hε.le,
        ofPred_false, inter_empty, measureReal_empty] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  | some i =>
      simpa only [feedbackCountableSpatialResidual, hd, Function.comp_def] using
        (tendsto_feedbackEnvironmentSpatialResidual_badProbability hlam0 hlam hamp hglobalQ
          hcoefficient hu huv hv i hε).comp (tendsto_add_atTop_nat 1)

namespace FeedbackGoodSceneSubsequence
open MatchingScene
variable {lam amplitude globalQ endpointQ C δ u v : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1/8} {huv : u < v}
    {bad : ∀n, Set (FiniteSample (n+1))}
    (data : FeedbackGoodSceneSubsequence hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad
      (feedbackCountableSpatialResidual hlam0.le (hlam.trans (by norm_num)) amplitude u v))

/-- Every selected countable residual is zero under the actual weak limit. The required
uniform integrability is derived from the selected genuine closed-window count-square bounds. -/
theorem countableResidual_zero (i : ActualEnvironmentResidualIndex) :
    (∫scene, countableEnvironmentResidual lam i scene ∂(data.limit : Measure MatchingScene)) = 0 := by
  let μ (k) := feedbackSelectionSceneLaw hlam0.le (hlam.trans (by norm_num)) amplitude u v huv (data.sample k)
  have hzero : Tendsto (fun k ↦ ∫scene, countableEnvironmentResidual lam i scene
      ∂(μ k : Measure MatchingScene)) atTop (𝓝 0) := by
    simpa only [feedbackCountableSpatialResidual, Encodable.decode₂_encode,
      feedbackEnvironmentSpatialResidual, μ, feedbackSelectionSceneLaw, ProbabilityMeasure.coe_mk] using
      data.residual_tendsto (Encodable.encode i)
  rcases i with ⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩
  let t : ℝ≥0 := (a:ℝ≥0)/(d+1:ℕ)
  obtain ⟨R,hR⟩ := exists_nat_ge (t:ℝ)
  obtain ⟨K,hK,hcount⟩ := data.count_bound R
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcount
  apply integral_pastMarkedResidual_eq_zero_of_closed_count_sq_bound
    (fun j ↦ μ (j+N)) (data.law_tendsto.comp (tendsto_add_atTop_nat N))
    (data.tight.subset (by rintro _ ⟨j,rfl⟩; exact ⟨j+N,rfl⟩)) hlam0.le (hlam.trans (by norm_num))
    (fun j ↦ countablePastTest (fs j)) (fun j ↦ countablePastTest (ft j))
    (Probability.countableBoundedTest (EnvironmentPastCoordinates ns nt) hi)
    b (countableEnvironmentMarkTest pi) t hR
    (by filter_upwards [data.vacantCut 0,data.vacantCut t] with scene h0 ht; exact ⟨h0,ht⟩)
    ENNReal.ofReal_ne_top
  · intro j
    exact hN (j+N) (by omega)
  · exact hzero.comp (tendsto_add_atTop_nat N)

end FeedbackGoodSceneSubsequence
end OTSelector
