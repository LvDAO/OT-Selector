import OTSelector.PointProcess.MultisetEncoding
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Finsupp.Multiset

/-!
# Countable shell codes for locally finite configurations

A configuration is encoded by one finite multiset in each disjoint distance shell around a
chosen base point.  Multiplicities are retained.  Every bounded window meets only finitely many
shells, so each code determines an actual locally finite natural-valued function.

The shell code supplies a standard Borel structure.  No product topology is assigned to the
configuration space: crossing a shell boundary must remain continuous for the later vague
topology, whereas the shell product topology would not have that property.
-/

open Filter Function Set Topology
open scoped BigOperators Classical

namespace OTSelector.PointProcess

namespace LocalConfiguration

variable {X : Type*} [MetricSpace X]

/-- The unique shell index of a point, computed from its distance to the base point. -/
noncomputable def shellIndex (base x : X) : ℕ :=
  ⌊dist x base⌋₊

/-- The half-open distance shell with radii `n` and `n + 1`. -/
abbrev Shell (base : X) (n : ℕ) :=
  {x : X // shellIndex base x = n}

theorem shellIndex_eq_iff (base x : X) (n : ℕ) :
    shellIndex base x = n ↔ (n : ℝ) ≤ dist x base ∧ dist x base < (n : ℝ) + 1 :=
  Nat.floor_eq_iff dist_nonneg

theorem shellIndex_lt_iff (base x : X) (n : ℕ) :
    shellIndex base x < n ↔ dist x base < (n : ℝ) :=
  Nat.floor_lt dist_nonneg

section MeasurableShell

variable [MeasurableSpace X] [BorelSpace X]

@[fun_prop]
theorem measurable_shellIndex (base : X) : Measurable (shellIndex base) :=
  (continuous_id.dist continuous_const).measurable.nat_floor

theorem measurableSet_shell (base : X) (n : ℕ) :
    MeasurableSet {x | shellIndex base x = n} :=
  measurableSet_eq_fun (measurable_shellIndex base) measurable_const

instance instStandardBorelSpaceShell [StandardBorelSpace X] (base : X) (n : ℕ) :
    StandardBorelSpace (Shell base n) :=
  (measurableSet_shell base n).standardBorel

end MeasurableShell

end LocalConfiguration

/-- One finite multiset in each disjoint bounded shell. -/
abbrev LocalConfiguration {X : Type*} [MetricSpace X] (base : X) :=
  ∀ n : ℕ, Multiset (LocalConfiguration.Shell base n)

namespace LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- The multiplicity of a point in its unique shell. -/
noncomputable def multiplicity (config : LocalConfiguration base) (x : X) : ℕ :=
  (config (shellIndex base x)).count ⟨x, rfl⟩

theorem multiplicity_shell (config : LocalConfiguration base) (n : ℕ) (x : Shell base n) :
    multiplicity config x = (config n).count x := by
  rcases x with ⟨x, hx⟩
  subst n
  rfl

/-- The finite set of occupied points in the first `N` shells. -/
noncomputable def windowSupport (config : LocalConfiguration base) (N : ℕ) : Finset X :=
  (Finset.range N).biUnion fun n ↦ (config n).toFinset.image Subtype.val

theorem mem_windowSupport_iff (config : LocalConfiguration base) (N : ℕ) (x : X) :
    x ∈ windowSupport config N ↔ shellIndex base x < N ∧ multiplicity config x ≠ 0 := by
  classical
  simp only [windowSupport, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Multiset.mem_toFinset]
  constructor
  · rintro ⟨n, hn, y, hy, rfl⟩
    exact ⟨by simpa only [y.property] using hn, by
      rw [multiplicity_shell]
      exact Multiset.count_ne_zero.mpr hy⟩
  · rintro ⟨hx, hcount⟩
    exact ⟨shellIndex base x, hx, ⟨x, rfl⟩, Multiset.count_ne_zero.mp hcount, rfl⟩

/-- Restriction to an integer-radius ball has exactly the finite support represented by the
first `N` shells. -/
theorem ball_inter_support_eq (config : LocalConfiguration base) (N : ℕ) :
    Metric.ball base (N : ℝ) ∩ Function.support (multiplicity config) =
      (windowSupport config N : Set X) := by
  ext x
  simp only [Set.mem_inter_iff, Metric.mem_ball, Function.mem_support, Finset.mem_coe,
    mem_windowSupport_iff, shellIndex_lt_iff]

/-- Local finiteness follows from finite shell data, without a separate certificate. -/
theorem locallyFiniteSupport_multiplicity (config : LocalConfiguration base) :
    LocallyFiniteSupport (multiplicity config) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (dist x base)
  refine ⟨Metric.ball base (N : ℝ), Metric.isOpen_ball.mem_nhds hN, ?_⟩
  rw [ball_inter_support_eq]
  exact (windowSupport config N).finite_toSet

/-- Decode the shell representation into an actual locally finite integer configuration. -/
noncomputable def toLocallyFinsupp (config : LocalConfiguration base) :
    Function.locallyFinsupp X ℕ where
  toFun := multiplicity config
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' x _ := locallyFiniteSupport_multiplicity config x

@[simp]
theorem toLocallyFinsupp_apply (config : LocalConfiguration base) (x : X) :
    toLocallyFinsupp config x = multiplicity config x :=
  rfl

/-- The shell code retains every point multiplicity and is therefore injective. -/
theorem toLocallyFinsupp_injective :
    Injective (toLocallyFinsupp : LocalConfiguration base → Function.locallyFinsupp X ℕ) := by
  classical
  intro config other heq
  funext n
  apply Multiset.ext.mpr
  intro x
  rw [← multiplicity_shell config n x, ← multiplicity_shell other n x]
  exact congrArg (fun f : Function.locallyFinsupp X ℕ ↦ f x) heq

section Proper

variable [ProperSpace X]

private theorem finite_support_on_shell (config : Function.locallyFinsupp X ℕ) (n : ℕ) :
    (Function.support (fun x : Shell base n ↦ config x)).Finite := by
  have hfinite := config.locallyFiniteSupport.finite_inter_support_of_isCompact
    (isCompact_closedBall base ((n : ℝ) + 1))
  apply (hfinite.preimage (f := (Subtype.val : Shell base n → X))
    Subtype.val_injective.injOn).subset
  intro x hx
  exact ⟨((shellIndex_eq_iff base x n).mp x.property).2.le, hx⟩

/-- Encode a locally finite integer configuration by its multiplicities in each bounded shell. -/
noncomputable def ofLocallyFinsupp (config : Function.locallyFinsupp X ℕ) :
    LocalConfiguration base :=
  fun n ↦ (Finsupp.ofSupportFinite (fun x : Shell base n ↦ config x)
    (finite_support_on_shell config n)).toMultiset

@[simp]
theorem multiplicity_ofLocallyFinsupp (config : Function.locallyFinsupp X ℕ) (x : X) :
    multiplicity (ofLocallyFinsupp (base := base) config) x = config x := by
  unfold multiplicity ofLocallyFinsupp
  rw [Finsupp.count_toMultiset]
  rfl

/-- Decoding the shell representation preserves the full locally finite configuration. -/
@[simp]
theorem toLocallyFinsupp_ofLocallyFinsupp (config : Function.locallyFinsupp X ℕ) :
    toLocallyFinsupp (ofLocallyFinsupp (base := base) config) = config := by
  ext x
  exact multiplicity_ofLocallyFinsupp config x

/-- Encoding after decoding returns the same shell multisets, including all multiplicities. -/
@[simp]
theorem ofLocallyFinsupp_toLocallyFinsupp (config : LocalConfiguration base) :
    ofLocallyFinsupp (toLocallyFinsupp config) = config := by
  apply toLocallyFinsupp_injective
  exact toLocallyFinsupp_ofLocallyFinsupp (toLocallyFinsupp config)

/-- Shell codes describe exactly the locally finite natural-valued functions on a proper metric
space.  This equivalence asserts no topology on either side. -/
noncomputable def equivLocallyFinsupp (base : X) :
    LocalConfiguration base ≃ Function.locallyFinsupp X ℕ where
  toFun := toLocallyFinsupp
  invFun := ofLocallyFinsupp
  left_inv := ofLocallyFinsupp_toLocallyFinsupp
  right_inv := toLocallyFinsupp_ofLocallyFinsupp

end Proper

section Measurable

variable [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]

/-- The shell code is a standard Borel space by countable products of the proved multiset code.
This is a measurable-space statement and does not choose a configuration topology. -/
theorem standardBorelSpace (base : X) : StandardBorelSpace (LocalConfiguration base) :=
  inferInstance

/-- Observing one shell is measurable in the configuration code. -/
@[fun_prop]
theorem measurable_shell (n : ℕ) :
    Measurable (fun config : LocalConfiguration base ↦ config n) :=
  measurable_pi_apply n

/-- The number of points in a shell, counted with multiplicity, is measurable. -/
@[fun_prop]
theorem measurable_shell_card (n : ℕ) :
    Measurable (fun config : LocalConfiguration base ↦ (config n).card) :=
  MultisetEncoding.measurable_card.comp (measurable_shell n)

end Measurable

end LocalConfiguration

end OTSelector.PointProcess
