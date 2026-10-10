import OTSelector.PointProcess.MatchingSceneCollision

/-!
# Absence of aggregate time collisions in actual weak limits

Small-window collision budgets pass to the genuine scene topology through closed continuous-test
constraints. Both colours and their multiplicities enter the same bound. The input budgets concern
finite laws; the conclusion excludes coincident spatial positions in the limiting point processes.
-/

open MeasureTheory Set Filter Function Topology
open scoped Classical BigOperators ENNReal CompactlySupported
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.LocalConfiguration

/-- A nonnegative test bounded by one and supported in a spatial interval is bounded by its actual
integer point count, including multiplicity. -/
theorem testIntegral_le_spatialCount
    (config : LocalConfiguration matchingPointBase) (f : C_c(MatchingPoint, ℝ))
    {a b : ℝ} (_hf0 : ∀ p, 0 ≤ f p) (hf1 : ∀ p, f p ≤ 1)
    (hfzero : ∀ p, p.1 ∉ Ioo a b → f p = 0) :
    testIntegral config f ≤ (spatialCount config a b : ℝ) := by
  rw [← integral_countingMeasure, spatialCount_cast,
    ← integral_indicator_one (measurableSet_spatialIoc a b)]
  have hfinite := (countingMeasure_lt_top_of_isBounded config (isBounded_spatialIoc a b)).ne
  have hi : Integrable ((spatialIoc a b).indicator (fun _ ↦ (1 : ℝ)))
      (countingMeasure config) :=
    (integrable_indicator_iff (measurableSet_spatialIoc a b)).mpr
      (integrableOn_const (C := (1 : ℝ)) hfinite)
  apply integral_mono (integrable_countingMeasure config f) hi
  intro p
  by_cases hp : p ∈ spatialIoc a b
  · simpa only [indicator_of_mem hp] using hf1 p
  · have hz : f p = 0 := hfzero p (fun h ↦ hp ⟨h.1, h.2.le⟩)
    simp only [indicator_of_notMem hp, hz, le_refl]

/-- Counting mass of a compact set is bounded by any nonnegative test which is one on it. -/
theorem countingMeasure_real_le_testIntegral
    (config : LocalConfiguration matchingPointBase) (f : C_c(MatchingPoint, ℝ))
    {K : Set MatchingPoint} (hK : IsCompact K) (hf0 : ∀ p, 0 ≤ f p)
    (hfone : ∀ p ∈ K, f p = 1) :
    (countingMeasure config).real K ≤ testIntegral config f := by
  rw [← integral_countingMeasure]
  have heq : (∫ p in K, f p ∂countingMeasure config) = (countingMeasure config).real K := by
    rw [setIntegral_congr_fun hK.measurableSet hfone, setIntegral_const, smul_eq_mul, mul_one]
  rw [← heq]
  exact setIntegral_le_integral (integrable_countingMeasure config f) (Eventually.of_forall hf0)

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance collisionPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase

/-- Every continuous test inside this open window sees at most one point in the two colours
combined. This formulation is closed under vague limits, even when a boundary acquires an atom. -/
def CollisionFreeWindow (a b : ℝ) (scene : MatchingScene) : Prop :=
  ∀ f : C_c(MatchingPoint, ℝ), (∀ p, 0 ≤ f p) → (∀ p, f p ≤ 1) →
    (∀ p, p.1 ∉ Ioo a b → f p = 0) →
    LocalConfiguration.testIntegral scene.source f +
      LocalConfiguration.testIntegral scene.target f ≤ 1

theorem isClosed_collisionFreeWindow (a b : ℝ) :
    IsClosed {scene | CollisionFreeWindow a b scene} := by
  simp only [CollisionFreeWindow, ofPred_forall]
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_le
    (((LocalConfiguration.continuous_testIntegral f).comp continuous_source).add
      ((LocalConfiguration.continuous_testIntegral f).comp continuous_target)) continuous_const

theorem collisionFreeWindow_of_aggregateSpatialIocCount_le_one
    {scene : MatchingScene} {a b : ℝ} (h : aggregateSpatialIocCount scene a b ≤ 1) :
    CollisionFreeWindow a b scene := by
  intro f hf0 hf1 hfzero
  exact (add_le_add
    (LocalConfiguration.testIntegral_le_spatialCount scene.source f hf0 hf1 hfzero)
    (LocalConfiguration.testIntegral_le_spatialCount scene.target f hf0 hf1 hfzero)).trans h

/-- Failure of the closed test constraint implies two actual finite-window points. -/
theorem aggregateSpatialIocCount_ge_two_of_not_collisionFreeWindow
    {scene : MatchingScene} {a b : ℝ} (h : ¬ CollisionFreeWindow a b scene) :
    2 ≤ aggregateSpatialIocCount scene a b := by
  have hnot : ¬ aggregateSpatialIocCount scene a b ≤ 1 :=
    fun hc ↦ h (collisionFreeWindow_of_aggregateSpatialIocCount_le_one hc)
  unfold aggregateSpatialIocCount at *
  have hi : (1 : ℤ) < LocalConfiguration.spatialCount scene.source a b +
      LocalConfiguration.spatialCount scene.target a b := by exact_mod_cast lt_of_not_ge hnot
  exact_mod_cast (show (2 : ℤ) ≤ LocalConfiguration.spatialCount scene.source a b +
    LocalConfiguration.spatialCount scene.target a b by omega)

/-- At a fixed spatial position the total counting mass of both colours, over all marks. -/
noncomputable def aggregateCutMass (scene : MatchingScene) (x : ℝ) : ℝ≥0∞ :=
  LocalConfiguration.countingMeasure scene.source ({x} ×ˢ univ) +
    LocalConfiguration.countingMeasure scene.target ({x} ×ˢ univ)

/-- Aggregate spatial simplicity excludes both within-colour and cross-colour collisions. -/
def TimeSimple (scene : MatchingScene) : Prop := ∀ x : ℝ, aggregateCutMass scene x ≤ 1

theorem aggregateCutMass_le_one_of_collisionFreeWindow
    {scene : MatchingScene} {a b x : ℝ} (h : CollisionFreeWindow a b scene)
    (hx : x ∈ Ioo a b) : aggregateCutMass scene x ≤ 1 := by
  let K : Set MatchingPoint := {x} ×ˢ univ
  let U : Set MatchingPoint := Prod.fst ⁻¹' Ioo a b
  have hK : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hKU : K ⊆ U := by
    rintro p ⟨hp, _⟩
    change p.1 ∈ Ioo a b
    simpa only [mem_singleton_iff.mp hp] using hx
  obtain ⟨f, hfone, hfc, hfsupp, hf⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let test : C_c(MatchingPoint, ℝ) := ⟨f, hfc⟩
  have htest0 : ∀ p, 0 ≤ test p := fun p ↦ (hf p).1
  have htest1 : ∀ p, test p ≤ 1 := fun p ↦ (hf p).2
  have htestzero : ∀ p : MatchingPoint, p.1 ∉ Ioo a b → test p = 0 := by
    intro p hp
    exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hp (hfsupp hs))
  have hone : ∀ p ∈ K, test p = 1 := fun p hp ↦ hfone hp
  have hreal := (add_le_add
    (LocalConfiguration.countingMeasure_real_le_testIntegral scene.source test hK htest0 hone)
    (LocalConfiguration.countingMeasure_real_le_testIntegral scene.target test hK htest0 hone)).trans
      (h test htest0 htest1 htestzero)
  have hsfin := (LocalConfiguration.countingMeasure_lt_top_of_isBounded scene.source hK.isBounded).ne
  have htfin := (LocalConfiguration.countingMeasure_lt_top_of_isBounded scene.target hK.isBounded).ne
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hsfin, htfin⟩) (by norm_num)).mp
  simpa only [aggregateCutMass, ENNReal.toReal_add hsfin htfin, ENNReal.toReal_one,
    Measure.real] using hreal

/-- Aggregate time simplicity gives genuine source multiplicity one. -/
theorem TimeSimple.source_multiplicity_le_one {scene : MatchingScene} (h : TimeSimple scene)
    (p : MatchingPoint) : LocalConfiguration.multiplicity scene.source p ≤ 1 := by
  have hp : (LocalConfiguration.multiplicity scene.source p : ℝ≥0∞) ≤
      LocalConfiguration.countingMeasure scene.source ({p.1} ×ˢ univ) := by
    rw [← LocalConfiguration.countingMeasure_singleton]
    exact measure_mono (singleton_subset_iff.mpr ⟨rfl, mem_univ _⟩)
  have hbound : (LocalConfiguration.multiplicity scene.source p : ℝ≥0∞) ≤ 1 :=
    (hp.trans (le_add_right le_rfl)).trans (h p.1)
  exact_mod_cast hbound

/-- Aggregate time simplicity gives genuine target multiplicity one. -/
theorem TimeSimple.target_multiplicity_le_one {scene : MatchingScene} (h : TimeSimple scene)
    (p : MatchingPoint) : LocalConfiguration.multiplicity scene.target p ≤ 1 := by
  have hp : (LocalConfiguration.multiplicity scene.target p : ℝ≥0∞) ≤
      LocalConfiguration.countingMeasure scene.target ({p.1} ×ˢ univ) := by
    rw [← LocalConfiguration.countingMeasure_singleton]
    exact measure_mono (singleton_subset_iff.mpr ⟨rfl, mem_univ _⟩)
  have hbound : (LocalConfiguration.multiplicity scene.target p : ℝ≥0∞) ≤ 1 :=
    (hp.trans (le_add_left le_rfl)).trans (h p.1)
  exact_mod_cast hbound

/-- In particular a source and target atom cannot share a time, whatever their marks. -/
theorem TimeSimple.source_target_time_ne {scene : MatchingScene} (h : TimeSimple scene)
    {p q : MatchingPoint} (hp : LocalConfiguration.multiplicity scene.source p ≠ 0)
    (hq : LocalConfiguration.multiplicity scene.target q ≠ 0) : p.1 ≠ q.1 := by
  intro heq
  have hs : (1 : ℝ≥0∞) ≤ LocalConfiguration.countingMeasure scene.source ({p.1} ×ˢ univ) := by
    have hm : (1 : ℝ≥0∞) ≤ LocalConfiguration.multiplicity scene.source p := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    apply hm.trans
    rw [← LocalConfiguration.countingMeasure_singleton]
    exact measure_mono (singleton_subset_iff.mpr ⟨rfl, mem_univ _⟩)
  have ht : (1 : ℝ≥0∞) ≤ LocalConfiguration.countingMeasure scene.target ({p.1} ×ˢ univ) := by
    have hm : (1 : ℝ≥0∞) ≤ LocalConfiguration.multiplicity scene.target q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    apply hm.trans
    rw [← LocalConfiguration.countingMeasure_singleton]
    exact measure_mono (singleton_subset_iff.mpr ⟨heq.symm, mem_univ _⟩)
  have hbad : (1 : ℝ≥0∞) + 1 ≤ 1 := (add_le_add hs ht).trans (h p.1)
  norm_num at hbad

/-- A finite family of overlapping open windows supplies a closed good event. -/
def CollisionFreeGrid {m : ℕ} (a b : Fin m → ℝ) (scene : MatchingScene) : Prop :=
  ∀ k, CollisionFreeWindow (a k) (b k) scene

theorem isClosed_collisionFreeGrid {m : ℕ} (a b : Fin m → ℝ) :
    IsClosed {scene | CollisionFreeGrid a b scene} := by
  simp only [CollisionFreeGrid, ofPred_forall]
  exact isClosed_iInter fun k ↦ isClosed_collisionFreeWindow (a k) (b k)

theorem measure_not_collisionFreeGrid_le {m : ℕ} (a b : Fin m → ℝ)
    (μ : Measure MatchingScene) :
    μ {scene | ¬ CollisionFreeGrid a b scene} ≤
      ∑ k : Fin m, μ {scene | 2 ≤ aggregateSpatialIocCount scene (a k) (b k)} := by
  calc
    _ ≤ μ (⋃ k : Fin m, {scene | 2 ≤ aggregateSpatialIocCount scene (a k) (b k)}) := by
      apply measure_mono
      intro scene hscene
      change ¬ ∀ k, CollisionFreeWindow (a k) (b k) scene at hscene
      push Not at hscene
      obtain ⟨k, hk⟩ := hscene
      exact mem_iUnion.mpr ⟨k, aggregateSpatialIocCount_ge_two_of_not_collisionFreeWindow hk⟩
    _ ≤ _ := by
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := μ)
        (fun k : Fin m ↦ {scene | 2 ≤ aggregateSpatialIocCount scene (a k) (b k)}))

/-- Finite-law grid budgets pass to the closed event of the weak limit. No continuity of raw
counting observables or endpoint atomlessness is assumed. -/
theorem measure_not_collisionFreeGrid_le_of_tendsto
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    {m : ℕ} (a b : Fin m → ℝ) {ε : ℝ≥0∞}
    (hbudget : ∀ᶠ n in atTop,
      (∑ k : Fin m, (μ n : Measure MatchingScene)
        {scene | 2 ≤ aggregateSpatialIocCount scene (a k) (b k)}) ≤ ε) :
    (ν : Measure MatchingScene) {scene | ¬ CollisionFreeGrid a b scene} ≤ ε := by
  apply measure_compl_closed_le_of_tendsto_of_tight hμ htight (isClosed_collisionFreeGrid a b)
  filter_upwards [hbudget] with n hn
  exact (measure_not_collisionFreeGrid_le a b (μ n)).trans hn

/-- A vanishing sequence of finite-window budgets excludes every time collision on a bounded
observation interval. The budgets are observable constraints on the approximating finite laws. -/
theorem ae_aggregateCutMass_le_one_on_of_grid_budgets
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (A : ℝ) (m : ℕ → ℕ) (a b : (j : ℕ) → Fin (m j) → ℝ)
    (hcover : ∀ j x, x ∈ Icc (-A) A → ∃ k, x ∈ Ioo (a j k) (b j k))
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hbudget : ∀ j, ∀ᶠ n in atTop,
      (∑ k : Fin (m j), (μ n : Measure MatchingScene)
        {scene | 2 ≤ aggregateSpatialIocCount scene (a j k) (b j k)}) ≤ ε j) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene),
      ∀ x ∈ Icc (-A) A, aggregateCutMass scene x ≤ 1 := by
  rw [ae_iff]
  apply le_antisymm _ zero_le
  apply ge_of_tendsto hε
  apply Eventually.of_forall
  intro j
  apply (measure_mono (show {scene | ¬ (∀ x ∈ Icc (-A) A,
      aggregateCutMass scene x ≤ 1)} ⊆ {scene | ¬ CollisionFreeGrid (a j) (b j) scene} from ?_)).trans
    (measure_not_collisionFreeGrid_le_of_tendsto hμ htight (a j) (b j) (hbudget j))
  intro scene hscene hg
  apply hscene
  intro x hx
  obtain ⟨k, hk⟩ := hcover j x hx
  exact aggregateCutMass_le_one_of_collisionFreeWindow (hg k) hk

/-- Countably many bounded observation intervals yield aggregate time simplicity everywhere. -/
theorem ae_timeSimple_of_grid_budgets
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (m : ℕ → ℕ → ℕ) (a b : (A j : ℕ) → Fin (m A j) → ℝ)
    (hcover : ∀ (A j : ℕ) (x : ℝ), x ∈ Icc (-(A : ℝ)) A →
      ∃ k, x ∈ Ioo (a A j k) (b A j k))
    (ε : ℕ → ℕ → ℝ≥0∞) (hε : ∀ A, Tendsto (ε A) atTop (𝓝 0))
    (hbudget : ∀ A j, ∀ᶠ n in atTop,
      (∑ k : Fin (m A j), (μ n : Measure MatchingScene)
        {scene | 2 ≤ aggregateSpatialIocCount scene (a A j k) (b A j k)}) ≤ ε A j) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), TimeSimple scene := by
  have hall : ∀ A : ℕ, ∀ᵐ scene ∂(ν : Measure MatchingScene),
      ∀ x ∈ Icc (-(A : ℝ)) A, aggregateCutMass scene x ≤ 1 := fun A ↦
    ae_aggregateCutMass_le_one_on_of_grid_budgets hμ htight A (m A) (a A) (b A)
      (hcover A) (ε A) (hε A) (hbudget A)
  filter_upwards [ae_all_iff.mpr hall] with scene hscene
  intro x
  obtain ⟨A, hA⟩ := exists_nat_gt |x|
  exact hscene A x ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- Mesh for overlapping windows covering a bounded observation interval. -/
noncomputable def collisionGridMesh (A : ℝ) (m : ℕ) : ℝ := (2*A+2)/(m:ℝ)

noncomputable def collisionGridLeft (A : ℝ) {m : ℕ} (k : Fin m) : ℝ :=
  -A-1+((k.val:ℝ)-1)*collisionGridMesh A m

noncomputable def collisionGridRight (A : ℝ) {m : ℕ} (k : Fin m) : ℝ :=
  -A-1+((k.val:ℝ)+2)*collisionGridMesh A m

theorem collisionGridMesh_pos {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m) :
    0 < collisionGridMesh A m := div_pos (by linarith) (by exact_mod_cast hm)

theorem collisionGrid_width (A : ℝ) {m : ℕ} (k : Fin m) :
    collisionGridRight A k - collisionGridLeft A k = 3*collisionGridMesh A m := by
  unfold collisionGridRight collisionGridLeft
  ring

theorem collisionGrid_ordered {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m) (k : Fin m) :
    collisionGridLeft A k ≤ collisionGridRight A k := by
  have hmesh := collisionGridMesh_pos hA hm
  have hw := collisionGrid_width A k
  linarith

/-- Overlap on both sides of each mesh interval prevents any endpoint from escaping the grid. -/
theorem collisionGrid_covers {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Icc (-A) A) :
    ∃ k : Fin m, x ∈ Ioo (collisionGridLeft A k) (collisionGridRight A k) := by
  let δ := collisionGridMesh A m
  have hδ : 0 < δ := collisionGridMesh_pos hA hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmul : (m:ℝ)*δ = 2*A+2 := by dsimp [δ, collisionGridMesh]; field_simp
  let q := (x+A+1)/δ
  have hq0 : 0 ≤ q := div_nonneg (by linarith [hx.1]) hδ.le
  have hqm : q < m := (div_lt_iff₀ hδ).mpr (by linarith [hx.2])
  let k : Fin m := ⟨⌊q⌋₊, (Nat.floor_lt hq0).mpr hqm⟩
  have hlo : (k.val:ℝ)*δ ≤ x+A+1 := by
    have h := (Nat.floor_le hq0)
    change (k.val:ℝ) ≤ q at h
    exact (le_div_iff₀ hδ).mp h
  have hhi : x+A+1 < ((k.val:ℝ)+1)*δ := by
    have h := Nat.lt_floor_add_one q
    change q < (k.val:ℝ)+1 at h
    exact (div_lt_iff₀ hδ).mp h
  refine ⟨k, ?_, ?_⟩
  · change -A-1+((k.val:ℝ)-1)*δ < x
    nlinarith
  · change x < -A-1+((k.val:ℝ)+2)*δ
    nlinarith

/-- Uniform geometric width gives the explicit finite-grid quadratic budget. -/
theorem collisionGrid_quadratic_budget (A : ℝ) (m : ℕ) :
    (∑ k : Fin m, ENNReal.ofReal (36*(collisionGridRight A k-collisionGridLeft A k)^2)) =
      (m : ℝ≥0∞) * ENNReal.ofReal (324*(collisionGridMesh A m)^2) := by
  simp_rw [collisionGrid_width]
  have h : 36*(3*collisionGridMesh A m)^2 = 324*(collisionGridMesh A m)^2 := by ring
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Every resolution stays inside one fixed enlarged observation interval. Consequently all
countably many grids can use the same finite-model survival event and root window. -/
theorem collisionGrid_endpoint_bounds {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m)
    (k : Fin m) : -(3*A+3) ≤ collisionGridLeft A k ∧
      collisionGridRight A k ≤ 3*A+3 := by
  let δ := collisionGridMesh A m
  have hδ : 0 < δ := collisionGridMesh_pos hA hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmul : (m:ℝ)*δ = 2*A+2 := by dsimp [δ, collisionGridMesh]; field_simp
  have hδle : δ ≤ 2*A+2 := by nlinarith
  have hk0 : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
  have hkm : (k.val:ℝ)+1 ≤ m := by exact_mod_cast k.isLt
  change -(3*A+3) ≤ -A-1+((k.val:ℝ)-1)*δ ∧
    -A-1+((k.val:ℝ)+2)*δ ≤ 3*A+3
  constructor <;> nlinarith

end OTSelector.PointProcess.MatchingScene
