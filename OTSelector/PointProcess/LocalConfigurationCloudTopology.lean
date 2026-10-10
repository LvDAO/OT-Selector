import OTSelector.PointProcess.LocalConfigurationTestIntegral
import Mathlib.Topology.ContinuousOn

/-!
# A labeled-cloud topology used only to compare Borel structures

The padded finite-cloud code has its natural disjoint-option topology.  Its Borel structure is
the already established finite-cloud measurable structure.  The product of these labeled shell
clouds maps continuously to the actual vague configuration space, and the sorted code supplies a
measurable section.  Hence every vague Borel set is measurable in the shell encoding.  The
labeled product topology is an auxiliary proof device, not the vague topology on configurations.
-/

open MeasureTheory Set Topology
open scoped Classical CompactlySupported BigOperators

namespace OTSelector.PointProcess

namespace FinitePointCloud

variable {X : Type*} [TopologicalSpace X]

/-- An absent point is an isolated component, separate from the physical point space. -/
@[instance_reducible]
def optionTopology (X : Type*) [TopologicalSpace X] : TopologicalSpace (Option X) :=
  TopologicalSpace.induced (Option.elim' (Sum.inl ()) (Sum.inr : X → Unit ⊕ X)) inferInstance

local instance optionInst : TopologicalSpace (Option X) := optionTopology X

private instance [SecondCountableTopology X] : SecondCountableTopology (Option X) :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

private instance [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] :
    BorelSpace (Option X) := by
  constructor
  change MeasurableSpace.comap (Option.elim' (Sum.inl ()) (Sum.inr : X → Unit ⊕ X))
    inferInstance = @borel _ (TopologicalSpace.induced _ _)
  rw [borel_comap]
  exact congrArg (MeasurableSpace.comap _) (BorelSpace.measurable_eq (α := Unit ⊕ X))

/-- The topology of the cardinality and all padded cloud coordinates. -/
@[instance_reducible]
def cloudTopology (X : Type*) [TopologicalSpace X] : TopologicalSpace (FinitePointCloud X) :=
  TopologicalSpace.induced paddedCode inferInstance

local instance cloudInst : TopologicalSpace (FinitePointCloud X) := cloudTopology X

theorem cloudSecondCountableTopology [SecondCountableTopology X] :
    SecondCountableTopology (FinitePointCloud X) :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

/-- The auxiliary labeled topology has precisely the existing code Borel sets. -/
theorem cloudBorelSpace [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] :
    BorelSpace (FinitePointCloud X) := by
  constructor
  change MeasurableSpace.comap paddedCode inferInstance =
    @borel _ (TopologicalSpace.induced paddedCode _)
  rw [borel_comap]
  exact congrArg (MeasurableSpace.comap _) (BorelSpace.measurable_eq (α := PaddedCode X))

private theorem continuous_option_some : Continuous (some : X → Option X) := by
  unfold optionInst optionTopology
  apply continuous_induced_rng.mpr
  exact continuous_inr

/-- A fixed-length tuple varies continuously in the auxiliary labeled-cloud topology. -/
theorem continuous_ofTuple (n : ℕ) :
    Continuous (fun points : Fin n → X ↦ (⟨n, points⟩ : FinitePointCloud X)) := by
  unfold cloudInst cloudTopology
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk continuous_const
  apply continuous_pi
  intro k
  by_cases hk : k < n
  · simpa only [paddedCode, point?, hk, ↓reduceDIte, Function.comp_def] using
      continuous_option_some.comp (_root_.continuous_apply (⟨k, hk⟩ : Fin n))
  · simpa only [paddedCode, point?, hk, ↓reduceDIte, Function.comp_def] using
      (continuous_const : Continuous (fun _ : Fin n → X ↦ (none : Option X)))

/-- In a compact point space, all finite labeled clouds with at most `N` atoms form a compact set.
Applied to closed annuli, this is the finite-coordinate compactness input for local count bounds. -/
theorem isCompact_card_le [CompactSpace X] (N : ℕ) :
    IsCompact {cloud : FinitePointCloud X | cloud.card ≤ N} := by
  have hcompact : IsCompact (⋃ n ∈ Finset.range (N + 1),
      Set.range (fun points : Fin n → X ↦ (⟨n, points⟩ : FinitePointCloud X))) :=
    Finset.isCompact_biUnion _ (fun n _ ↦ isCompact_range (continuous_ofTuple n))
  convert hcompact using 1
  ext cloud
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_range]
  constructor
  · intro h
    exact ⟨cloud.card, by omega, cloud.point, by cases cloud; rfl⟩
  · rintro ⟨n, hn, points, rfl⟩
    simpa using Nat.le_of_lt_succ hn

private theorem continuous_option_elim {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun o : Option X ↦ o.elim 0 f) := by
  unfold optionInst optionTopology
  have h := ((continuous_const : Continuous (fun _ : Unit ↦ (0 : ℝ))).sumElim hf).comp
    (continuous_induced_dom : Continuous (Option.elim' (Sum.inl ()) (Sum.inr : X → Unit ⊕ X)))
  convert h using 1
  funext o
  cases o <;> rfl

/-- A continuous point observable has a continuous sum on finite labeled clouds. -/
theorem continuous_sum_toMultiset {f : X → ℝ} (hf : Continuous f) :
    Continuous (fun cloud : FinitePointCloud X ↦ (cloud.toMultiset.map f).sum) := by
  have hcode : Continuous (fun code : PaddedCode X ↦
      ∑ k ∈ Finset.range code.1, (code.2 k).elim 0 f) := by
    apply continuous_prod_of_discrete_left.mpr
    intro n
    change Continuous (fun code : ℕ → Option X ↦ ∑ k ∈ Finset.range n, (code k).elim 0 f)
    apply continuous_finsetSum
    intro k hk
    exact (continuous_option_elim hf).comp (_root_.continuous_apply k)
  have h : Continuous (fun cloud : FinitePointCloud X ↦
      ∑ k ∈ Finset.range cloud.card, (cloud.point? k).elim 0 f) := by
    unfold cloudInst cloudTopology
    exact hcode.comp (continuous_induced_dom : Continuous (paddedCode (X := X)))
  convert h using 1
  funext cloud
  rw [← Fin.sum_univ_eq_sum_range]
  simp [point?, toMultiset, toList, List.sum_ofFn]

end FinitePointCloud

namespace LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- The auxiliary carrier remembers an enumeration separately in each bounded shell. -/
abbrev LabeledShellClouds (base : X) := ∀ n, FinitePointCloud (Shell base n)

local instance (n : ℕ) : TopologicalSpace (FinitePointCloud (Shell base n)) :=
  FinitePointCloud.cloudTopology (Shell base n)

/-- Forget all shell enumerations while retaining their point multiplicities. -/
def forgetLabels (clouds : LabeledShellClouds base) : LocalConfiguration base :=
  fun n ↦ (clouds n).toMultiset

/-- A compactly supported test sees only finitely many labeled shells. -/
theorem continuous_forgetLabels :
    Continuous[inferInstance, vagueTopology base] (forgetLabels : LabeledShellClouds base → _) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  obtain ⟨N, hN⟩ := exists_testSupport_subset_ball f base
  have h : Continuous (fun clouds : LabeledShellClouds base ↦
      ∑ n ∈ Finset.range N, ((clouds n).toMultiset.map (fun x ↦ f x.val)).sum) := by
    apply continuous_finsetSum
    intro n hn
    exact (FinitePointCloud.continuous_sum_toMultiset
      (f.continuous.comp continuous_subtype_val)).comp (_root_.continuous_apply n)
  convert h using 1
  funext clouds
  exact (testIntegral_eq_sum_map_window (forgetLabels clouds) f hN).trans
    (sum_map_window (forgetLabels clouds) N (fun x ↦ f x))

section Borel

variable [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [SecondCountableTopology X]

local instance (n : ℕ) : SecondCountableTopology (FinitePointCloud (Shell base n)) :=
  FinitePointCloud.cloudSecondCountableTopology

local instance (n : ℕ) : BorelSpace (FinitePointCloud (Shell base n)) :=
  FinitePointCloud.cloudBorelSpace

/-- The canonical code chooses measurable labels; continuity of this choice is not needed. -/
noncomputable def chooseLabels (config : LocalConfiguration base) : LabeledShellClouds base :=
  fun n ↦ MultisetEncoding.toFinitePointCloud (config n)

omit [SecondCountableTopology X] in
theorem measurable_chooseLabels : Measurable (chooseLabels (base := base)) := by
  apply measurable_pi_lambda
  intro n
  exact MultisetEncoding.measurable_toFinitePointCloud.comp (measurable_shell n)

omit [SecondCountableTopology X] in
@[simp]
theorem forgetLabels_chooseLabels (config : LocalConfiguration base) :
    forgetLabels (chooseLabels config) = config := by
  funext n
  exact MultisetEncoding.toMultiset_toFinitePointCloud (config n)

/-- Every vague Borel set is measurable in the shell code.  This is one direction of compatibility,
proved through a continuous labeled representation and its measurable section. -/
theorem vagueBorel_le :
    @borel (LocalConfiguration base) (vagueTopology base) ≤
      (inferInstance : MeasurableSpace (LocalConfiguration base)) := by
  let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  have hlabels := measurable_chooseLabels (base := base)
  have hforget : @Measurable (LabeledShellClouds base) (LocalConfiguration base)
      inferInstance (borel (LocalConfiguration base)) forgetLabels := by
    let : MeasurableSpace (LocalConfiguration base) := borel (LocalConfiguration base)
    let : BorelSpace (LocalConfiguration base) := ⟨rfl⟩
    exact continuous_forgetLabels.measurable
  have h := hforget.comp hlabels
  intro s hs
  change @MeasurableSet (LocalConfiguration base) MeasurableSpace.pi s
  have hpre : (forgetLabels ∘ chooseLabels (base := base)) ⁻¹' s = s := by
    ext config
    simp
  have hhs := h hs
  rw [hpre] at hhs
  exact hhs

end Borel

end LocalConfiguration

end OTSelector.PointProcess
