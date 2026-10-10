import OTSelector.PointProcess.MatchingSceneGoodSampleSelection
import OTSelector.PointProcess.MatchingSceneGraphLimit

/-!
# Actual good-sample weak subsequences

Optimizer energy yields tightness of the actual macroscopic root laws. Extracting a further
weak subsequence retains all selected sample constraints. Fixed-cut vacancy, stationarity,
aggregate simplicity and the original rational graph equation then follow from these same laws.
-/

open MeasureTheory Filter Set Function
open scoped Classical BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096

namespace OTSelector

open FiniteSample PointProcess PointProcess.MatchingScene

/-- The original optimizer scene rooted uniformly in the physical interval `((n+1)u,(n+1)v]`. -/
noncomputable def feedbackSelectionSceneLaw {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude u v : ℝ) (huv : u < v)
    (sample : FiniteSample (n + 1)) : ProbabilityMeasure MatchingScene :=
  ⟨sample.rootedMatchingSceneLaw (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude)
    sample.euclideanOptimizer ((n + 1 : ℕ) * u) ((n + 1 : ℕ) * v),
    sample.rootedMatchingSceneLaw_isProbability _ _
      (mul_lt_mul_of_pos_left huv (by positivity))⟩

/-- All retained constraints concern actual finite samples, and the weak limit is the limit
of their original uniform-root laws. Tightness is derived below from their good-event energy. -/
structure FeedbackGoodSceneSubsequence {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (amplitude globalQ endpointQ C δ u v : ℝ) (huv : u < v)
    (bad : ∀ n, Set (FiniteSample (n + 1)))
    (residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ) where
  index : ℕ → ℕ
  strictMono_index : StrictMono index
  sample : ∀ k, FiniteSample (index k + 1)
  limit : ProbabilityMeasure MatchingScene
  good_bad : ∀ k, sample k ∈ feedbackSelectorGoodEvent
    hlam0 hlam amplitude globalQ endpointQ C (index k + 1) ∧ sample k ∈ bad (index k)
  residual_tendsto : ∀ m, Tendsto (fun k ↦ residual m (index k) (sample k)) atTop (𝓝 0)
  count_bound : ∀ R : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ k in atTop,
    feedbackSelectionClosedCountSq hlam0.le (hlam.trans (by norm_num))
      amplitude u v R (sample k) ≤ ENNReal.ofReal K
  collision_bound : ∀ R j : ℕ, ∀ᶠ k in atTop,
    feedbackSelectionCollisionGrid hlam0.le (hlam.trans (by norm_num))
      amplitude δ u v R j (sample k) ≤ ENNReal.ofReal (collisionSelectionThreshold j)
  law_tendsto : Tendsto (fun k ↦ feedbackSelectionSceneLaw
    hlam0.le (hlam.trans (by norm_num)) amplitude u v huv (sample k)) atTop (𝓝 limit)

private theorem macro_count_bound {u v : ℝ} (huv : u < v) (n : ℕ) :
    (n : ℝ) ≤ (v - u)⁻¹ * ((n : ℝ) * v - (n : ℝ) * u) := by
  have hw : v - u ≠ 0 := (sub_pos.mpr huv).ne'
  have heq : (v - u)⁻¹ * ((n : ℝ) * v - (n : ℝ) * u) = n := by field_simp
  rw [heq]

private theorem selection_laws_tight {lam amplitude globalQ endpointQ C u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (huv : u < v)
    (N : ℕ → ℕ) (sample : ∀ k, FiniteSample (N k + 1))
    (hgood : ∀ k, sample k ∈ feedbackSelectorGoodEvent
      hlam0 hlam amplitude globalQ endpointQ C (N k + 1)) :
    IsTightMeasureSet (range fun k ↦ ((feedbackSelectionSceneLaw
      hlam0.le (hlam.trans (by norm_num)) amplitude u v huv (sample k)) : Measure MatchingScene)) := by
  apply FiniteSample.isTightMeasureSet_rootedMatchingSceneLaw sample
    (fun k ↦ (sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)
    (fun k ↦ (sample k).euclideanOptimizer)
    (fun k ↦ ((N k + 1 : ℕ) : ℝ) * u) (fun k ↦ ((N k + 1 : ℕ) : ℝ) * v)
    (fun k ↦ mul_lt_mul_of_pos_left huv (by positivity))
    (fun k ↦ macro_count_bound huv (N k + 1))
    (C := C / (v - u))
  intro k
  have he := feedbackSelectorGoodEvent.energy (hgood k)
  have hw : v - u ≠ 0 := (sub_pos.mpr huv).ne'
  have heq : C / (v - u) * (((N k + 1 : ℕ) : ℝ) * v -
      ((N k + 1 : ℕ) : ℝ) * u) = C * (N k + 1 : ℕ) := by field_simp
  rw [heq]
  exact he

namespace FeedbackGoodSceneSubsequence

variable {lam amplitude globalQ endpointQ C δ u v : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {huv : u < v}
    {bad : ∀ n, Set (FiniteSample (n + 1))}
    {residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ}
    (data : FeedbackGoodSceneSubsequence hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad residual)

/-- Genuine tightness follows from the selected optimizer energy, including the current coordinate. -/
theorem tight : IsTightMeasureSet (range fun k ↦ ((feedbackSelectionSceneLaw
    hlam0.le (hlam.trans (by norm_num)) amplitude u v huv (data.sample k)) : Measure MatchingScene)) :=
  selection_laws_tight hlam0 hlam huv data.index data.sample (fun k ↦ (data.good_bad k).1)

/-- Each fixed real cut is vacant, independently of identifying the environment. -/
theorem vacantCut (x : ℝ) : ∀ᵐ scene ∂(data.limit : Measure MatchingScene), scene.VacantCut x := by
  exact ae_vacantCut_of_rootedMatchingSceneLaw_tendsto data.sample
    (fun k ↦ (data.sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)
    (fun k ↦ (data.sample k).euclideanOptimizer)
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * u)
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * v)
    (fun k ↦ mul_lt_mul_of_pos_left huv (by positivity))
    (fun _ ↦ rfl) data.law_tendsto
    (Eventually.of_forall fun k ↦ macro_count_bound huv (data.index k + 1)) x

/-- Translation invariance of the actual limit follows from growing uniform root intervals. -/
theorem stationary (t : ℝ) : MeasurePreserving (MatchingScene.reroot t)
    (data.limit : Measure MatchingScene) (data.limit : Measure MatchingScene) := by
  have hscale : Tendsto (fun k ↦ ((data.index k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp data.strictMono_index.tendsto_atTop)
  have hwindow : Tendsto (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * v -
      ((data.index k + 1 : ℕ) : ℝ) * u) atTop atTop := by
    simpa only [← mul_sub] using hscale.atTop_mul_const (sub_pos.mpr huv)
  exact measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto_of_count_bound data.sample
    (fun k ↦ (data.sample k).feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)
    (fun k ↦ (data.sample k).euclideanOptimizer)
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * u)
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * v)
    (fun k ↦ mul_lt_mul_of_pos_left huv (by positivity))
    (fun _ ↦ rfl) data.law_tendsto data.tight hwindow
    (Eventually.of_forall fun k ↦ macro_count_bound huv (data.index k + 1)) t

/-- The selected finite collision grids exclude all time collisions of the limiting scene. -/
theorem timeSimple : ∀ᵐ scene ∂(data.limit : Measure MatchingScene), TimeSimple scene := by
  let m (R j : ℕ) := collisionSelectionGridSize R (collisionSelectionThreshold j)
    (feedbackSelectionWeight δ (.inr (R, j)))
  let a (R j : ℕ) : Fin (m R j) → ℝ := collisionGridLeft R
  let b (R j : ℕ) : Fin (m R j) → ℝ := collisionGridRight R
  apply ae_timeSimple_of_grid_budgets data.law_tendsto data.tight m a b
    (fun R j x hx ↦ collisionGrid_covers (Nat.cast_nonneg R)
      (collisionSelectionGridSize_pos _ _ _) hx)
    (fun _ j ↦ ENNReal.ofReal (collisionSelectionThreshold j))
    (fun _ ↦ by simpa using ENNReal.tendsto_ofReal tendsto_collisionSelectionThreshold)
  intro R j
  simpa only [feedbackSelectionCollisionGrid, stoppedEmpiricalSelectedCollisionGrid,
    stoppedEmpiricalCollisionFraction, feedbackSelectionSceneLaw, ProbabilityMeasure.coe_mk,
    feedbackFGL2Graph, m, a, b] using
    data.collision_bound R j

/-- On the same actual surviving graphs, every rational primitive identity passes to the limit. -/
theorem graphODE (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hu : 0 < u) (hv : v < 1) :
    ∀ᵐ scene ∂(data.limit : Measure MatchingScene), ∀ q : ℚ, scene.path.graphHeight q =
      ∫ x in (0 : ℝ)..(q : ℝ), lam * Limit.currentSign (scene.currentAt x) := by
  have hindex := (tendsto_add_atTop_nat 1).comp data.strictMono_index.tendsto_atTop
  have hgood : ∀ᶠ k in atTop,
      (data.sample k).NoFeedbackTies lam (feedbackA2AsymptoticBuffer amplitude (data.index k + 1)) 0 ∧
      safeFeedbackA1StopTime hlam0.le (hlam.trans (by norm_num))
        (feedbackA2AsymptoticEta lam) (feedbackA2AsymptoticBuffer amplitude (data.index k + 1))
        (feedbackA2AsymptoticBuffer amplitude (data.index k + 1)) 0
        (feedbackA2AsymptoticHorizon amplitude (data.index k + 1)) (data.sample k) =
        (feedbackA2AsymptoticHorizon amplitude (data.index k + 1) : WithTop ℝ≥0) := by
    filter_upwards [hindex.eventually (eventually_feedbackSelectorGood_survival
      (C := C) (endpointQ := endpointQ) hlam0 hlam hglobalQ hcoefficient)] with k hk
    exact ⟨feedbackSelectorGoodEvent.noFeedbackTies (data.good_bad k).1,
      hk (data.sample k) (data.good_bad k).1⟩
  apply ae_forall_rat_graph_eq_integral_currentAt_of_stoppedRootLaw_tendsto
    hlam0.le (hlam.trans (by norm_num)) data.sample (fun _ ↦ feedbackA2AsymptoticEta lam)
    (fun k ↦ feedbackA2AsymptoticBuffer amplitude (data.index k + 1))
    (fun k ↦ feedbackA2AsymptoticHorizon amplitude (data.index k + 1))
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * u)
    (fun k ↦ ((data.index k + 1 : ℕ) : ℝ) * v)
    (fun k ↦ mul_lt_mul_of_pos_left huv (by positivity))
    (fun _ ↦ rfl) data.law_tendsto data.tight
    (Eventually.of_forall fun k ↦ macro_count_bound huv (data.index k + 1)) hgood
  intro q
  filter_upwards [hindex.eventually (eventually_feedbackSelection_bulk_fit hamp hu hv |(q : ℝ)|)]
    with k hk
  simp only [Function.comp_apply] at hk
  constructor
  · have hm : -|(q : ℝ)| ≤ min 0 (q : ℝ) := le_min (neg_nonpos.mpr (abs_nonneg _)) (neg_abs_le _)
    linarith [hk.2.2.1]
  · have hm : max 0 (q : ℝ) ≤ |(q : ℝ)| := max_le (abs_nonneg _) (le_abs_self _)
    linarith [hk.2.2.2]

end FeedbackGoodSceneSubsequence

/-- The actual factory and selected optimizer energy produce a genuine weak subsequence,
without any assumed compactness, tightness or limiting environment law. -/
theorem exists_feedbackSelectorGood_weak_subsequence_parameters {lam δ u v : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ∃ amplitude globalQ endpointQ C : ℝ,
      0 < amplitude ∧ 0 < globalQ ∧ 1 ≤ endpointQ ∧
      8 * (globalQ + 33) < amplitude ∧ 0 < C ∧
      ∀ (bad : ∀ n, Set (FiniteSample (n + 1)))
        (residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ),
        (∃ᶠ n in atTop, δ ≤ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real (bad n)) →
        (∀ m ε, 0 < ε → Tendsto (fun n ↦
          (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
            (feedbackSelectorGoodEvent hlam0 hlam amplitude globalQ endpointQ C (n + 1) ∩
              {sample | ε < |residual m n sample|})) atTop (𝓝 0)) →
        Nonempty (FeedbackGoodSceneSubsequence
          hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad residual) := by
  obtain ⟨A, q, qE, C, hA, hq, hqE, hcoef, hC, hselect⟩ :=
    exists_feedbackSelectorGood_sample_parameters hlam0 hlam hδ hu huv hv
  refine ⟨A, q, qE, C, hA, hq, hqE, hcoef, hC, ?_⟩
  intro bad residual hbad hres
  obtain ⟨φ, hφ, sample, hs, hr, hm, hc⟩ := hselect bad residual hbad hres
  let μ (k : ℕ) := feedbackSelectionSceneLaw hlam0.le (hlam.trans (by norm_num)) A u v huv (sample k)
  have htight := selection_laws_tight hlam0 hlam huv φ sample (fun k ↦ (hs k).1)
  obtain ⟨ν, ψ, hψ, hlim⟩ := exists_tendsto_subseq_of_isTightMeasureSet μ htight
  refine ⟨{
    index := φ ∘ ψ
    strictMono_index := hφ.comp hψ
    sample := fun k ↦ sample (ψ k)
    limit := ν
    good_bad := fun k ↦ hs (ψ k)
    residual_tendsto := fun m ↦ (hr m).comp hψ.tendsto_atTop
    count_bound := ?_
    collision_bound := fun R j ↦ hψ.tendsto_atTop.eventually (hc R j)
    law_tendsto := hlim }⟩
  intro R
  obtain ⟨K, hK, hbound⟩ := hm R
  exact ⟨K, hK, hψ.tendsto_atTop.eventually hbound⟩


namespace PointProcess.MatchingScene

private theorem point_eq_of_time_of_cut_mass_le_one
    (cfg : LocalConfiguration matchingPointBase)
    (hbound : ∀ x : ℝ, LocalConfiguration.countingMeasure cfg ({x} ×ˢ univ) ≤ 1)
    {p q : MatchingPoint} (hp : LocalConfiguration.multiplicity cfg p ≠ 0)
    (hq : LocalConfiguration.multiplicity cfg q ≠ 0) (htime : p.1 = q.1) : p = q := by
  by_contra hpq
  have hmass (r : MatchingPoint) (hr : LocalConfiguration.multiplicity cfg r ≠ 0) :
      (1 : ℝ≥0∞) ≤ LocalConfiguration.countingMeasure cfg {r} := by
    rw [LocalConfiguration.countingMeasure_singleton]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
  have hsub : ({p} : Set MatchingPoint) ∪ {q} ⊆ {p.1} ×ˢ univ := by
    rintro r (hr | hr)
    · rcases hr with rfl
      exact ⟨rfl, mem_univ _⟩
    · rcases hr with rfl
      exact ⟨htime.symm, mem_univ _⟩
  have hbad : (1 : ℝ≥0∞) + 1 ≤ 1 := by
    calc
      _ ≤ LocalConfiguration.countingMeasure cfg {p} +
          LocalConfiguration.countingMeasure cfg {q} := add_le_add (hmass p hp) (hmass q hq)
      _ = LocalConfiguration.countingMeasure cfg ({p} ∪ {q}) :=
        (measure_union (disjoint_singleton.mpr hpq) (measurableSet_singleton q)).symm
      _ ≤ LocalConfiguration.countingMeasure cfg ({p.1} ×ˢ univ) := measure_mono hsub
      _ ≤ 1 := hbound p.1
  norm_num at hbad

/-- Aggregate simplicity is precisely strong enough for the actual two-colour first-event API:
each occupied point has multiplicity one and its spatial time determines its mark and colour. -/
theorem TimeSimple.isTimeSimple_feedbackSceneEnvironment {scene : MatchingScene}
    (h : TimeSimple scene) : LocalConfiguration.IsTimeSimple
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) := by
  have hs (x : ℝ) : LocalConfiguration.countingMeasure scene.source ({x} ×ˢ univ) ≤ 1 :=
    (le_add_right le_rfl).trans (h x)
  have ht (x : ℝ) : LocalConfiguration.countingMeasure scene.target ({x} ×ˢ univ) ≤ 1 :=
    (le_add_left le_rfl).trans (h x)
  constructor
  · rintro ⟨b, p⟩ hp
    cases b
    · exact Nat.le_antisymm (h.target_multiplicity_le_one p) (Nat.one_le_iff_ne_zero.mpr hp)
    · exact Nat.le_antisymm (h.source_multiplicity_le_one p) (Nat.one_le_iff_ne_zero.mpr hp)
  · rintro ⟨bp, p⟩ ⟨bq, q⟩ hp hq htime
    cases bp <;> cases bq
    · exact congrArg (fun r ↦ (false, r))
        (point_eq_of_time_of_cut_mass_le_one scene.target ht hp hq htime)
    · exact False.elim (h.source_target_time_ne hq hp htime.symm)
    · exact False.elim (h.source_target_time_ne hp hq htime)
    · exact congrArg (fun r ↦ (true, r))
        (point_eq_of_time_of_cut_mass_le_one scene.source hs hp hq htime)

end PointProcess.MatchingScene

/-- The actual weak limit satisfies the two-colour simplicity hypothesis used by the marked
martingale-problem environment theorem. -/
theorem FeedbackGoodSceneSubsequence.environment_timeSimple
    {lam amplitude globalQ endpointQ C δ u v : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {huv : u < v}
    {bad : ∀ n, Set (FiniteSample (n + 1))}
    {residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ}
    (data : FeedbackGoodSceneSubsequence hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad residual) :
    ∀ᵐ scene ∂(data.limit : Measure MatchingScene), LocalConfiguration.IsTimeSimple
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) :=
  data.timeSimple.mono fun _ hs ↦ hs.isTimeSimple_feedbackSceneEnvironment

end OTSelector
