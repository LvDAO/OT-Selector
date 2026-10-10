import OTSelector.Feedback.FeedbackEnvironmentPast
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Countable actual environment tests

The bounded outer tests use compact-open convergence on each fixed bounded ball of functions.
They do not assert separability of the sup-norm space of all bounded continuous functions.
The past point tests have a common compact support at each stage, so their configuration
integrals converge on every actual locally finite configuration.
-/

open MeasureTheory Set Filter TopologicalSpace
open scoped Classical Topology CompactlySupported BoundedContinuousFunction NNReal BigOperators
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.Probability

section BoundedTests
variable (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]

/-- A fixed uniform bound, with the compact-open subspace topology. -/
abbrev BoundedTestBall (m : ℕ) := ↥({f : C(X, ℝ) | ∀x, ‖f x‖ ≤ (m:ℝ)} : Set C(X, ℝ))

instance (m : ℕ) : Nonempty (BoundedTestBall X m) :=
  ⟨⟨0, fun _ ↦ by simp⟩⟩

/-- One countable family suffices for all bounded continuous outer cylinder tests. -/
noncomputable def countableBoundedTest (i : ℕ × ℕ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound (denseSeq (BoundedTestBall X i.1) i.2).val (2*i.1)
    (fun x y ↦ (dist_le_norm_add_norm _ _).trans (by
      have hx := (denseSeq (BoundedTestBall X i.1) i.2).property x
      have hy := (denseSeq (BoundedTestBall X i.1) i.2).property y
      linarith))

theorem norm_countableBoundedTest_apply_le (i : ℕ × ℕ) (x : X) :
    ‖countableBoundedTest X i x‖ ≤ (i.1:ℝ) :=
  (denseSeq (BoundedTestBall X i.1) i.2).property x

/-- Every bounded continuous function is approximated in the compact-open topology by a
sequence from one uniformly bounded part of the fixed countable family. -/
theorem exists_countableBoundedTest_tendsto (f : X →ᵇ ℝ) :
    ∃m : ℕ, ∃u : ℕ → ℕ,
      Tendsto (fun k ↦ (countableBoundedTest X (m,u k)).toContinuousMap)
        atTop (𝓝 f.toContinuousMap) := by
  obtain ⟨m, hm⟩ := exists_nat_ge ‖f‖
  let g : BoundedTestBall X m := ⟨f.toContinuousMap, fun x ↦ (f.norm_coe_le_norm x).trans hm⟩
  have hg : g ∈ closure (range (denseSeq (BoundedTestBall X m))) :=
    (denseRange_denseSeq (BoundedTestBall X m)) g
  obtain ⟨v,hv,hvlim⟩ := mem_closure_iff_seq_limit.mp hg
  choose u hu using hv
  have hseq : Tendsto (fun k ↦ denseSeq (BoundedTestBall X m) (u k)) atTop (𝓝 g) :=
    hvlim.congr' (Eventually.of_forall fun k ↦ (hu k).symm)
  exact ⟨m,u,(continuous_subtype_val.tendsto g).comp hseq⟩

/-- On a compact domain, in particular the physical mark interval, the same countable
family approximates uniformly, while staying in a fixed bounded part. -/
theorem exists_countableBoundedTest_tendstoUniformly [CompactSpace X] (f : X →ᵇ ℝ) :
    ∃m : ℕ, ∃u : ℕ → ℕ,
      TendstoUniformly (fun k x ↦ countableBoundedTest X (m,u k) x) f atTop := by
  obtain ⟨m,u,hu⟩ := exists_countableBoundedTest_tendsto X f
  exact ⟨m,u,ContinuousMap.tendsto_iff_tendstoUniformly.mp hu⟩

end BoundedTests

/-- Countably many outer tests imply the original identity for every bounded continuous
test. Only integrability of the real residual is needed for this upgrade. -/
theorem integral_mul_bcf_eq_zero_of_countable_tests
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) {Y : Ω → X} (hY : Measurable Y) {R : Ω → ℝ} (hR : Integrable R μ)
    (h : ∀i : ℕ × ℕ, (∫ω, R ω * countableBoundedTest X i (Y ω) ∂μ) = 0)
    (f : X →ᵇ ℝ) : (∫ω, R ω * f (Y ω) ∂μ) = 0 := by
  obtain ⟨m,u,hu⟩ := exists_countableBoundedTest_tendsto X f
  have hlim := tendsto_integral_of_dominated_convergence
    (fun ω ↦ ‖R ω‖*(m:ℝ))
    (fun k ↦ hR.aestronglyMeasurable.mul
      (((countableBoundedTest X (m,u k)).continuous.measurable.comp hY).aestronglyMeasurable))
    (hR.norm.mul_const (m:ℝ))
    (fun k ↦ Eventually.of_forall fun ω ↦ by
      simp only [Pi.mul_apply, Function.comp_apply, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_countableBoundedTest_apply_le X (m,u k) (Y ω))
        (norm_nonneg _))
    (Eventually.of_forall fun ω ↦ tendsto_const_nhds.mul
      ((continuous_eval_const (Y ω)).tendsto f.toContinuousMap |>.comp hu))
  exact tendsto_nhds_unique hlim (by simpa only [Pi.mul_apply, Function.comp_apply, h] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0)))

end OTSelector.Probability

namespace OTSelector.PointProcess

/-- The fixed compact window containing a past point test. -/
def pastTestWindow (m : ℕ) : Set MatchingPoint := Icc (-(m:ℝ)) 0 ×ˢ univ

theorem isCompact_pastTestWindow (m : ℕ) : IsCompact (pastTestWindow m) :=
  isCompact_Icc.prod isCompact_univ

/-- Past tests with one common compact support, given the compact-open topology. -/
abbrev PastTestSpace (m : ℕ) := ↥({f : C(MatchingPoint, ℝ) |
  (∀p, p ∉ pastTestWindow m → f p = 0) ∧ (∀x v, 0 ≤ x → f (x,v) = 0)} :
    Set C(MatchingPoint, ℝ))

instance (m : ℕ) : Nonempty (PastTestSpace m) := ⟨⟨0, by simp⟩⟩

noncomputable def PastTestSpace.toCompactlySupported {m : ℕ} (f : PastTestSpace m) :
    C_c(MatchingPoint, ℝ) where
  toContinuousMap := f.val
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact (isCompact_pastTestWindow m)
    (fun p hp ↦ by by_contra hn; exact hp (f.property.1 p hn))

/-- A fixed countable family of genuine negative-half-line compact point tests. -/
noncomputable def countablePastTest (i : ℕ × ℕ) : C_c(MatchingPoint, ℝ) :=
  (denseSeq (PastTestSpace i.1) i.2).toCompactlySupported

theorem countablePastTest_eq_zero_of_nonneg (i : ℕ × ℕ) (x : ℝ) (v : UnitMark) (hx : 0 ≤ x) :
    countablePastTest i (x,v) = 0 := (denseSeq (PastTestSpace i.1) i.2).property.2 x v hx

theorem support_countablePastTest_subset (i : ℕ × ℕ) :
    Function.support (countablePastTest i) ⊆ pastTestWindow i.1 := by
  intro p hp
  by_contra hn
  exact hp ((denseSeq (PastTestSpace i.1) i.2).property.1 p hn)

/-- Every original admissible past test is approximated compact-open by this fixed family,
with all approximants supported in a single compact window. -/
theorem exists_countablePastTest_tendsto (f : C_c(MatchingPoint, ℝ))
    (hf : ∀x v, 0 ≤ x → f (x,v) = 0) :
    ∃m : ℕ, Function.support f ⊆ pastTestWindow m ∧ ∃u : ℕ → ℕ,
      Tendsto (fun k ↦ (countablePastTest (m,u k)).toContinuousMap) atTop (𝓝 f.toContinuousMap) := by
  obtain ⟨a,ha⟩ := (f.hasCompactSupport.image continuous_fst).bddBelow
  obtain ⟨m,hm⟩ := exists_nat_ge (-a)
  have hsupport : Function.support f ⊆ pastTestWindow m := by
    intro p hp
    have hp0 : p.1 < 0 := lt_of_not_ge (fun h ↦ hp (hf p.1 p.2 h))
    have hpa : a ≤ p.1 := ha (mem_image_of_mem Prod.fst (subset_tsupport _ hp))
    exact ⟨⟨by linarith, hp0.le⟩, mem_univ _⟩
  let g : PastTestSpace m := ⟨f.toContinuousMap,
    ⟨fun p hp ↦ by by_contra hn; exact hp (hsupport hn), hf⟩⟩
  have hg : g ∈ closure (range (denseSeq (PastTestSpace m))) :=
    (denseRange_denseSeq (PastTestSpace m)) g
  obtain ⟨v,hv,hvlim⟩ := mem_closure_iff_seq_limit.mp hg
  choose u hu using hv
  have hseq : Tendsto (fun k ↦ denseSeq (PastTestSpace m) (u k)) atTop (𝓝 g) :=
    hvlim.congr' (Eventually.of_forall fun k ↦ (hu k).symm)
  exact ⟨m,hsupport,u,(continuous_subtype_val.tendsto g).comp hseq⟩

/-- Integrals on every actual configuration converge along the common-support approximation.
No extra moment or continuity hypothesis on the configuration is required. -/
theorem tendsto_testIntegral_of_common_support
    (config : LocalConfiguration matchingPointBase) {m : ℕ}
    {f : C_c(MatchingPoint, ℝ)} {F : ℕ → C_c(MatchingPoint, ℝ)}
    (hf : Function.support f ⊆ pastTestWindow m)
    (hF : ∀k, Function.support (F k) ⊆ pastTestWindow m)
    (hlim : Tendsto (fun k ↦ (F k).toContinuousMap) atTop (𝓝 f.toContinuousMap)) :
    Tendsto (fun k ↦ LocalConfiguration.testIntegral config (F k)) atTop
      (𝓝 (LocalConfiguration.testIntegral config f)) := by
  let S := ((LocalConfiguration.locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact
    (isCompact_pastTestWindow m)).toFinset
  have hsum (g : C_c(MatchingPoint, ℝ)) (hg : Function.support g ⊆ pastTestWindow m) :
      LocalConfiguration.testIntegral config g =
        ∑p ∈ S, (LocalConfiguration.multiplicity config p : ℝ)*g p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    have hgp : g p ≠ 0 := by intro hz; exact hp (by simp [LocalConfiguration.testSummand,hz])
    have hcp : LocalConfiguration.multiplicity config p ≠ 0 := by
      intro hz; exact hp (by simp [LocalConfiguration.testSummand,hz])
    exact Set.Finite.mem_toFinset _ |>.mpr ⟨hg hgp,hcp⟩
  simp_rw [hsum _ hf, hsum _ (hF _)]
  apply tendsto_finsetSum
  intro p _
  exact tendsto_const_nhds.mul ((continuous_eval_const p).tendsto f.toContinuousMap |>.comp hlim)

/-- The countable point-test observations of the environment past. -/
noncomputable def countablePastTestCode (config : LocalConfiguration matchingPointBase)
    (i : ℕ × ℕ) : ℝ := LocalConfiguration.testIntegral config (countablePastTest i)

/-- Every original negative-half-line compact test is measurable in the sigma algebra of
the fixed countable observations. This is a determining statement, not an added assumption. -/
theorem measurable_pastTestIntegral_countableCode (f : C_c(MatchingPoint, ℝ))
    (hf : ∀x v, 0 ≤ x → f (x,v) = 0) :
    Measurable[MeasurableSpace.comap countablePastTestCode inferInstance]
      (fun config ↦ LocalConfiguration.testIntegral config f) := by
  let : MeasurableSpace (LocalConfiguration matchingPointBase) :=
    MeasurableSpace.comap countablePastTestCode inferInstance
  obtain ⟨m,hm,u,hu⟩ := exists_countablePastTest_tendsto f hf
  apply measurable_of_tendsto_metrizable (f := fun k config ↦
    LocalConfiguration.testIntegral config (countablePastTest (m,u k)))
  · intro k
    exact (measurable_pi_apply (X := fun _ : ℕ × ℕ ↦ ℝ) (m,u k)).comp
      (measurable_iff_comap_le.mpr le_rfl)
  · exact tendsto_pi_nhds.mpr fun config ↦ tendsto_testIntegral_of_common_support config hm
      (fun k ↦ support_countablePastTest_subset (m,u k)) hu

/-- Equality of the fixed countable past tests implies equality of every original compact
past-test observation, on every pair of actual locally finite configurations. -/
theorem pastTestIntegral_eq_of_countableCode_eq
    {config config' : LocalConfiguration matchingPointBase}
    (hcode : countablePastTestCode config = countablePastTestCode config')
    (f : C_c(MatchingPoint, ℝ)) (hf : ∀x v, 0 ≤ x → f (x,v) = 0) :
    LocalConfiguration.testIntegral config f = LocalConfiguration.testIntegral config' f := by
  obtain ⟨m,hm,u,hu⟩ := exists_countablePastTest_tendsto f hf
  have h1 := tendsto_testIntegral_of_common_support config hm
    (fun k ↦ support_countablePastTest_subset (m,u k)) hu
  have h2 := tendsto_testIntegral_of_common_support config' hm
    (fun k ↦ support_countablePastTest_subset (m,u k)) hu
  apply tendsto_nhds_unique h1
  exact h2.congr' (Eventually.of_forall fun k ↦ (congrFun hcode (m,u k)).symm)

/-- The full original class of admissible compact past tests. -/
abbrev AdmissiblePastTest := {f : C_c(MatchingPoint, ℝ) //
  ∀x v, 0 ≤ x → f (x,v) = 0}

noncomputable def allPastTestCode (config : LocalConfiguration matchingPointBase)
    (f : AdmissiblePastTest) : ℝ := LocalConfiguration.testIntegral config f.val

/-- The fixed countable observations generate exactly the same sigma algebra as all original
compactly supported past tests. This equality is valid before taking any probability law. -/
theorem comap_allPastTestCode_eq_countable :
    MeasurableSpace.comap allPastTestCode inferInstance =
      MeasurableSpace.comap countablePastTestCode inferInstance := by
  apply le_antisymm
  · have h : Measurable[MeasurableSpace.comap countablePastTestCode inferInstance] allPastTestCode := by
      let : MeasurableSpace (LocalConfiguration matchingPointBase) :=
        MeasurableSpace.comap countablePastTestCode inferInstance
      exact measurable_pi_lambda _ fun f ↦ measurable_pastTestIntegral_countableCode f.val f.property
    exact measurable_iff_comap_le.mp h
  · have h : Measurable[MeasurableSpace.comap allPastTestCode inferInstance] countablePastTestCode := by
      let : MeasurableSpace (LocalConfiguration matchingPointBase) :=
        MeasurableSpace.comap allPastTestCode inferInstance
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (X := fun _ : AdmissiblePastTest ↦ ℝ)
        ⟨countablePastTest i, countablePastTest_eq_zero_of_nonneg i⟩).comp
        (measurable_iff_comap_le.mpr le_rfl)
    exact measurable_iff_comap_le.mp h

/-- Marks use the same uniformly approximating countable family on their actual compact
physical interval. -/
noncomputable def countableEnvironmentMarkTest (i : ℕ × ℕ) : UnitMark →ᵇ ℝ :=
  Probability.countableBoundedTest UnitMark i

theorem exists_countableEnvironmentMarkTest_tendstoUniformly (ψ : UnitMark →ᵇ ℝ) :
    ∃m : ℕ, ∃u : ℕ → ℕ,
      TendstoUniformly (fun k v ↦ countableEnvironmentMarkTest (m,u k) v) ψ atTop :=
  Probability.exists_countableBoundedTest_tendstoUniformly UnitMark ψ

/-- Countable code for two finite past-coordinate families, an outer test, a mark test, and
a color. A further countable time index can be paired with this code in sample selection. -/
abbrev EnvironmentResidualTestCode := Σs t : ℕ,
  (Fin s → ℕ × ℕ) × (Fin t → ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × Bool

instance : Countable EnvironmentResidualTestCode := inferInstance

end OTSelector.PointProcess
