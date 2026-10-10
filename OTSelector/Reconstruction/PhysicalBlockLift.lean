import OTSelector.Reconstruction.DiagonalLift
import OTSelector.Assumptions.EFE2
import OTSelector.PointProcess.MatchingScenePhysicalHeightBlocks
import Mathlib.Order.Interval.Set.Union

/-!
# Physical source-height blocks determine the full empirical plan

A continuous function of height and both marks is approximated by its height slices on finitely
many interior intervals. The constant mark test controls the omitted endpoint strips. Thus the
actual block averages determine the joint height/mark law, without an assumed global empirical
limit. The diagonal embedding and the existing vertical-displacement lift complete reconstruction.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector

private abbrev HeightMarks := UnitMark × (UnitMark × UnitMark)

private noncomputable def heightBlockTest (ψ : C(UnitMark × UnitMark, ℝ))
    (u v : ℝ) (z : HeightMarks) : ℝ :=
  if (z.1 : ℝ) ∈ Ioc u v then ψ z.2 else 0

private theorem measurable_heightBlockTest (ψ : C(UnitMark × UnitMark, ℝ)) (u v : ℝ) :
    Measurable (heightBlockTest ψ u v) := by
  exact (ψ.continuous.measurable.comp measurable_snd).ite
    (measurableSet_Ioc.preimage (continuous_subtype_val.measurable.comp measurable_fst))
    measurable_const

private theorem integrable_heightBlockTest (μ : ProbabilityMeasure HeightMarks)
    (ψ : C(UnitMark × UnitMark, ℝ)) (u v : ℝ) :
    Integrable (heightBlockTest ψ u v) (μ : Measure HeightMarks) := by
  apply Integrable.of_bound (measurable_heightBlockTest ψ u v).aestronglyMeasurable ‖ψ‖
  exact ae_of_all _ fun z ↦ by
    unfold heightBlockTest
    split_ifs
    · exact ψ.norm_coe_le_norm z.2
    · simp

private theorem integral_heightBlockTest_prod (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (ψ : C(UnitMark × UnitMark, ℝ)) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (∫ z, heightBlockTest ψ u v z ∂(unitUniform.prod κ : Measure HeightMarks)) =
      (v - u) * ∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark)) := by
  let a : UnitMark := ⟨u, hu.le, (huv.trans hv).le⟩
  let b : UnitMark := ⟨v, (hu.trans huv).le, hv.le⟩
  have heq : heightBlockTest ψ u v =
      fun z : HeightMarks ↦ (Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * ψ z.2 := by
    funext z
    simp only [heightBlockTest, indicator_apply, mem_Ioc]
    change (if u < (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ v then ψ z.2 else 0) =
      (if u < (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ v then 1 else 0) * ψ z.2
    split_ifs <;> simp
  rw [heq, ProbabilityMeasure.toMeasure_prod, integral_prod_mul,
    integral_indicator_const (1 : ℝ) measurableSet_Ioc]
  simp only [smul_eq_mul, mul_one]
  change ((volume : Measure UnitMark) (Ioc a b)).toReal * _ = _
  rw [unitInterval.volume_Ioc, ENNReal.toReal_ofReal (show 0 ≤ (b : ℝ) - a from sub_nonneg.mpr huv.le)]

/-- A finite interior partition approximates a continuous height/mark observable. The only
uncontrolled points lie in endpoint strips of arbitrarily small total length. -/
private theorem exists_heightBlock_approximation (F : C(HeightMarks, ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ (m : ℕ) (u v : ℝ) (a b : Fin m → ℝ) (ψ : Fin m → C(UnitMark × UnitMark, ℝ)),
      0 < u ∧ u < v ∧ v < 1 ∧ 1 - (v - u) < 2 * η ∧
      (∀ i, 0 < a i ∧ a i < b i ∧ b i < 1) ∧
      ∀ z, |F z - ∑ i, heightBlockTest (ψ i) (a i) (b i) z| ≤
        η + ‖F‖ * (1 - heightBlockTest 1 u v z) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous F.continuous) η hη
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt (lt_min hδ hη)
  let m := q + 1
  let w : ℝ := 1 / ((m : ℝ) + 2)
  have hm : 0 < m := by dsimp [m]; omega
  have hw : 0 < w := by dsimp [w]; positivity
  have hwm : ((m : ℝ) + 2) * w = 1 := by dsimp [w]; field_simp
  have hwsmall : w < min δ η := by
    have hle : w ≤ 1 / ((q : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      dsimp [m]
      push_cast
      linarith
    exact hle.trans_lt hq
  let a : ℕ → ℝ := fun i ↦ ((i : ℝ) + 1) * w
  have ha : Monotone a := by
    intro i j hij
    dsimp [a]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hij) hw.le
  have ha0 : 0 < a 0 := by simpa [a] using hw
  have haend : a m < 1 := by dsimp [a]; nlinarith
  have ha_lt (i : ℕ) : a i < a (i + 1) := by dsimp [a]; push_cast; nlinarith
  have ham : a 0 < a m := by
    simp only [a, Nat.cast_zero, zero_add]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith
  have haunit (i : Fin m) : a i ∈ Icc (0 : ℝ) 1 :=
    ⟨ha0.le.trans (ha (Nat.zero_le _)), (ha (Nat.le_of_lt i.isLt)).trans haend.le⟩
  let ψ : Fin m → C(UnitMark × UnitMark, ℝ) := fun i ↦
    ⟨fun mark ↦ F (⟨a i, haunit i⟩, mark), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨m, a 0, a m, (fun i ↦ a i), (fun i ↦ a (i.val + 1)), ψ,
    ha0, ham, haend, ?_, ?_, ?_⟩
  · have hsmall := (lt_min_iff.mp hwsmall).2
    simp only [a, Nat.cast_zero, zero_add]
    nlinarith
  · intro i
    exact ⟨ha0.trans_le (ha (Nat.zero_le _)), ha_lt i,
      (ha (Nat.succ_le_of_lt i.isLt)).trans_lt haend⟩
  · intro z
    by_cases hz : (z.1 : ℝ) ∈ Ioc (a 0) (a m)
    · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc m a hz)
      have him : i < m := Finset.mem_range.mp hi
      let j : Fin m := ⟨i, him⟩
      have hsingle : (∑ k : Fin m, heightBlockTest (ψ k) (a k) (a (k.val + 1)) z) = ψ j z.2 := by
        rw [Finset.sum_eq_single j]
        · exact ite_eq_left hzi
        · intro k _ hkj
          apply ite_eq_right
          intro hzk
          have hne : k.val ≠ i := by intro h; apply hkj; exact Fin.ext h
          rcases lt_or_gt_of_ne hne with hki | hik
          · have hak : a (k.val + 1) ≤ a i := ha (Nat.succ_le_of_lt hki)
            exact (not_lt_of_ge (hzk.2.trans hak)) hzi.1
          · have hak : a (i + 1) ≤ a k := ha (Nat.succ_le_of_lt hik)
            exact (not_lt_of_ge (hzi.2.trans hak)) hzk.1
        · simp
      rw [hsingle, heightBlockTest, ite_eq_left hz]
      simp only [ContinuousMap.one_apply, sub_self, mul_zero, add_zero]
      apply le_of_lt
      change dist (F z) (F (⟨a i, haunit j⟩, z.2)) < η
      apply hclose
      have hd : dist z (⟨a i, haunit j⟩, z.2) < δ := by
        simp only [Prod.dist_eq, dist_self, Subtype.dist_eq, Real.dist_eq]
        rw [abs_of_nonneg (sub_nonneg.mpr hzi.1.le), max_eq_left (sub_nonneg.mpr hzi.1.le)]
        have hsmall := (lt_min_iff.mp hwsmall).1
        have hstep : a (i + 1) - a i = w := by dsimp [a]; push_cast; ring
        linarith [hzi.2]
      exact hd
    · have hzero : (∑ k : Fin m, heightBlockTest (ψ k) (a k) (a (k.val + 1)) z) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        apply ite_eq_right
        intro hzk
        exact hz ⟨(ha (Nat.zero_le _)).trans_lt hzk.1,
          hzk.2.trans (ha (Nat.succ_le_of_lt k.isLt))⟩
      rw [hzero, sub_zero, heightBlockTest, ite_eq_right hz, sub_zero, mul_one]
      exact (F.norm_coe_le_norm z).trans (by linarith)

private theorem integral_heightBlock_approximation_bound
    (μ : ProbabilityMeasure HeightMarks) (F : C(HeightMarks, ℝ)) {m : ℕ}
    (a b : Fin m → ℝ) (ψ : Fin m → C(UnitMark × UnitMark, ℝ)) (u v η : ℝ)
    (happrox : ∀ z, |F z - ∑ i, heightBlockTest (ψ i) (a i) (b i) z| ≤
      η + ‖F‖ * (1 - heightBlockTest 1 u v z)) :
    |(∫ z, F z ∂(μ : Measure HeightMarks)) -
        ∫ z, ∑ i, heightBlockTest (ψ i) (a i) (b i) z ∂(μ : Measure HeightMarks)| ≤
      η + ‖F‖ * (1 - ∫ z, heightBlockTest 1 u v z ∂(μ : Measure HeightMarks)) := by
  have hF : Integrable F (μ : Measure HeightMarks) :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hS : Integrable (fun z ↦ ∑ i, heightBlockTest (ψ i) (a i) (b i) z) (μ : Measure HeightMarks) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_heightBlockTest μ (ψ i) (a i) (b i))
  have hI := integrable_heightBlockTest μ (1 : C(UnitMark × UnitMark, ℝ)) u v
  rw [← integral_sub hF hS]
  calc
    |∫ z, F z - ∑ i, heightBlockTest (ψ i) (a i) (b i) z ∂(μ : Measure HeightMarks)| ≤
        ∫ z, |F z - ∑ i, heightBlockTest (ψ i) (a i) (b i) z| ∂(μ : Measure HeightMarks) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, η + ‖F‖ * (1 - heightBlockTest 1 u v z) ∂(μ : Measure HeightMarks) :=
      integral_mono (hF.sub hS).abs ((integrable_const _).add
        (((integrable_const _).sub hI).const_mul _)) happrox
    _ = _ := by
      have hsub : Integrable (fun z ↦ (1 : ℝ) - heightBlockTest 1 u v z)
          (μ : Measure HeightMarks) := (integrable_const _).sub hI
      have hmul : Integrable (fun z ↦ ‖F‖ * (1 - heightBlockTest 1 u v z))
          (μ : Measure HeightMarks) := hsub.const_mul _
      rw [integral_add (integrable_const η) hmul, integral_const_mul,
        integral_sub (integrable_const (1 : ℝ)) hI]
      simp

/-- Interior height-block tests suffice for joint weak convergence; no marginal convergence
or boundary mass assumption is needed separately. -/
private theorem tendsto_heightMarks_of_blocks
    {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure HeightMarks) (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ ∫ z, heightBlockTest ψ u v z ∂(μ k : Measure HeightMarks)) l
          (𝓝 ((v - u) * ∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))))) :
    Tendsto μ l (𝓝 (unitUniform.prod κ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  let F : C(HeightMarks, ℝ) := f.toContinuousMap
  change Tendsto (fun k ↦ ∫ z, F z ∂(μ k : Measure HeightMarks)) l
    (𝓝 (∫ z, F z ∂(unitUniform.prod κ : Measure HeightMarks)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (10 * (‖F‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : 10 * (‖F‖ + 1) * η = ε := by dsimp [η]; field_simp
  obtain ⟨m, u, v, a, b, ψ, hu, huv, hv, htail, hab, happrox⟩ :=
    exists_heightBlock_approximation F hη
  let S : HeightMarks → ℝ := fun z ↦ ∑ i, heightBlockTest (ψ i) (a i) (b i) z
  have hsum : Tendsto (fun k ↦ ∫ z, S z ∂(μ k : Measure HeightMarks)) l
      (𝓝 (∫ z, S z ∂(unitUniform.prod κ : Measure HeightMarks))) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ ↦ hblock (a i) (b i)
      (hab i).1 (hab i).2.1 (hab i).2.2 (ψ i))
    simpa only [S, integral_finsetSum _ (fun i _ ↦ integrable_heightBlockTest _ _ _ _),
      integral_heightBlockTest_prod κ _ (hab _).1 (hab _).2.1 (hab _).2.2] using hh
  have hcenter : Tendsto
      (fun k ↦ ∫ z, heightBlockTest 1 u v z ∂(μ k : Measure HeightMarks)) l
      (𝓝 (v - u)) := by
    simpa using hblock u v hu huv hv 1
  have hsum' := (Metric.tendsto_nhds.mp hsum) η hη
  have hcenter' := (Metric.tendsto_nhds.mp hcenter) η hη
  filter_upwards [hsum', hcenter'] with k hk hc
  simp only [Real.dist_eq] at hk hc ⊢
  have hn := integral_heightBlock_approximation_bound (μ k) F a b ψ u v η happrox
  have hl := integral_heightBlock_approximation_bound (unitUniform.prod κ) F a b ψ u v η happrox
  have hlc : (∫ z, heightBlockTest 1 u v z ∂(unitUniform.prod κ : Measure HeightMarks)) = v - u := by
    simpa using integral_heightBlockTest_prod κ (1 : C(UnitMark × UnitMark, ℝ)) hu huv hv
  rw [hlc] at hl
  have hnc := (abs_lt.mp hc).1
  have hboundN : |(∫ z, F z ∂(μ k : Measure HeightMarks)) -
      ∫ z, S z ∂(μ k : Measure HeightMarks)| ≤ η + ‖F‖ * (3 * η) := by
    exact hn.trans (by nlinarith [norm_nonneg F])
  have hboundL : |(∫ z, S z ∂(unitUniform.prod κ : Measure HeightMarks)) -
      ∫ z, F z ∂(unitUniform.prod κ : Measure HeightMarks)| ≤ η + ‖F‖ * (2 * η) := by
    rw [abs_sub_comm]
    exact hl.trans (by nlinarith [norm_nonneg F])
  have htri := abs_sub_le (∫ z, F z ∂(μ k : Measure HeightMarks))
    (∫ z, S z ∂(μ k : Measure HeightMarks))
    (∫ z, F z ∂(unitUniform.prod κ : Measure HeightMarks))
  have htri' := abs_sub_le (∫ z, S z ∂(μ k : Measure HeightMarks))
    (∫ z, S z ∂(unitUniform.prod κ : Measure HeightMarks))
    (∫ z, F z ∂(unitUniform.prod κ : Measure HeightMarks))
  nlinarith [norm_nonneg F, mul_nonneg (norm_nonneg F) hη.le]

namespace FiniteSample

/-- Original source heights with the source mark and its assigned target mark. -/
noncomputable def sourceHeightMarkPlan {n : ℕ} [NeZero n] (sample : FiniteSample n)
    (σ : Assignment n) : ProbabilityMeasure (UnitMark × (UnitMark × UnitMark)) :=
  empiricalProbabilityMeasure (fun i ↦
    (sample.sourceHeight i, sample.sourceMark i, sample.targetMark (σ i)))

private theorem integral_sourceHeightMarkPlan_block {n : ℕ} [NeZero n]
    (sample : FiniteSample n) (σ : Assignment n) (ψ : C(UnitMark × UnitMark, ℝ))
    {u v : ℝ} (huv : u < v) :
    (∫ z, heightBlockTest ψ u v z ∂(sample.sourceHeightMarkPlan σ : Measure HeightMarks)) =
      (v - u) * sample.sourceHeightBlockMarks σ ψ u v := by
  change (∫ z, heightBlockTest ψ u v z ∂empiricalMeasure _) = _
  rw [integral_empiricalMeasure _ (measurable_heightBlockTest ψ u v).stronglyMeasurable]
  simp only [heightBlockTest, sourceHeightBlockMarks, mul_inv_rev]
  have hcancel : (v - u) * ((v - u)⁻¹ * (n : ℝ)⁻¹) = (n : ℝ)⁻¹ := by
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr huv.ne'), one_mul]
  rw [← mul_assoc, hcancel]

/-- Physical source-height block convergence gives the complete joint height/mark law. -/
theorem tendsto_sourceHeightMarkPlan_of_sourceHeightBlockMarks
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} [∀ k, NeZero (N k)]
    (sample : ∀ k, FiniteSample (N k)) (σ : ∀ k, Assignment (N k))
    (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (σ k) ψ u v) l
          (𝓝 (∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))))) :
    Tendsto (fun k ↦ (sample k).sourceHeightMarkPlan (σ k)) l
      (𝓝 (unitUniform.prod κ)) := by
  apply tendsto_heightMarks_of_blocks
  intro u v hu huv hv ψ
  simpa only [integral_sourceHeightMarkPlan_block _ _ _ huv] using
    (hblock u v hu huv hv ψ).const_mul (v - u)

/-- Diagonal plans are genuine pushforwards of the original height/mark statistics. -/
theorem diagonalPlan_eq_map_sourceHeightMarkPlan {n : ℕ} [NeZero n]
    (sample : FiniteSample n) (σ : Assignment n) :
    sample.diagonalPlan σ = (sample.sourceHeightMarkPlan σ).map
      measurable_diagonalEmbedding.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  change empiricalMeasure (sample.diagonalMatchedPoint σ) = Measure.map diagonalEmbedding
    (empiricalMeasure (fun i ↦ (sample.sourceHeight i, sample.sourceMark i,
      sample.targetMark (σ i))))
  rw [map_empiricalMeasure _ _ measurable_diagonalEmbedding]
  rfl

/-- The actual block-average hypotheses imply diagonal-plan convergence. -/
theorem tendsto_diagonalPlan_of_sourceHeightBlockMarks
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} [∀ k, NeZero (N k)]
    (sample : ∀ k, FiniteSample (N k)) (σ : ∀ k, Assignment (N k))
    (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (σ k) ψ u v) l
          (𝓝 (∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))))) :
    Tendsto (fun k ↦ (sample k).diagonalPlan (σ k)) l (𝓝 (reconstructedPlan κ)) := by
  have hc : Continuous diagonalEmbedding := by unfold diagonalEmbedding; fun_prop
  simpa only [diagonalPlan_eq_map_sourceHeightMarkPlan, reconstructedPlan] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (tendsto_sourceHeightMarkPlan_of_sourceHeightBlockMarks sample σ κ hblock) hc

/-- Physical block identification and actual vertical concentration reconstruct the full plan. -/
theorem tendsto_empiricalPlan_of_sourceHeightBlockMarks
    {ι : Type*} {l : Filter ι} {N : ι → ℕ} [∀ k, NeZero (N k)]
    (sample : ∀ k, FiniteSample (N k)) (σ : ∀ k, Assignment (N k))
    (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (σ k) ψ u v) l
          (𝓝 (∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark)))))
    (hvd : Tendsto (fun k ↦ (sample k).meanVerticalDisplacement (σ k)) l (𝓝 0)) :
    Tendsto (fun k ↦ (sample k).empiricalPlan (σ k)) l (𝓝 (reconstructedPlan κ)) := by
  exact tendsto_empiricalPlan_of_diagonalPlan sample σ (reconstructedPlan κ)
    (tendsto_diagonalPlan_of_sourceHeightBlockMarks sample σ κ hblock) hvd

end FiniteSample
end OTSelector
