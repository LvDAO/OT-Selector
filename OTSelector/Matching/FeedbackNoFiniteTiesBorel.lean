import OTSelector.Matching.FeedbackNoFiniteTies
import OTSelector.PointProcess.LocalConfigurationMultiset

/-!
# The measurable no-tie event under the actual stationary environment law

Canonical finite-shell codes turn quantification over all actual point families into countable
quantification. This proves measurability of the geometric no-tie property itself before
transporting the actual iid-cell result through the normalized occupation construction.
-/

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators ENNReal Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

private noncomputable def tieEnumeratedPoint (c : LocalConfiguration matchingPointBase)
    (i : ℕ × ℕ) : MatchingPoint :=
  ((MultisetEncoding.toFinitePointCloud (c i.1)).point? i.2).elim matchingPointBase Subtype.val

private theorem tieEnumeratedPoint_eq (c : LocalConfiguration matchingPointBase) (i : ℕ × ℕ)
    (hi : i.2 < (c i.1).card) : tieEnumeratedPoint c i =
      ((MultisetEncoding.toFinitePointCloud (c i.1)).point ⟨i.2, hi⟩).val := by
  simp only [tieEnumeratedPoint, FinitePointCloud.point?_of_lt
    (MultisetEncoding.toFinitePointCloud (c i.1)) hi, Option.elim_some]

private theorem measurable_tieEnumeratedPoint (i : ℕ × ℕ) :
    Measurable (fun c : LocalConfiguration matchingPointBase ↦ tieEnumeratedPoint c i) :=
  (MeasureTheory.Option.measurable_elim matchingPointBase measurable_subtype_coe).comp
    ((FinitePointCloud.measurable_point?_apply i.2).comp
      (MultisetEncoding.measurable_toFinitePointCloud.comp (LocalConfiguration.measurable_shell i.1)))

private theorem atom_iff_tieEnumeratedPoint (c : LocalConfiguration matchingPointBase)
    (p : MatchingPoint) : LocalConfiguration.countingMeasure c {p} ≠ 0 ↔
      ∃ i : ℕ × ℕ, i.2 < (c i.1).card ∧ tieEnumeratedPoint c i = p := by
  constructor
  · intro hp
    have hp' : LocalConfiguration.multiplicity c p ≠ 0 := by simpa using hp
    have hm : (⟨p, rfl⟩ : LocalConfiguration.Shell matchingPointBase
        (LocalConfiguration.shellIndex matchingPointBase p)) ∈
        c (LocalConfiguration.shellIndex matchingPointBase p) := by
      simpa only [LocalConfiguration.multiplicity, Multiset.count_ne_zero] using hp'
    rw [← MultisetEncoding.toMultiset_toFinitePointCloud
      (c (LocalConfiguration.shellIndex matchingPointBase p))] at hm
    simp only [FinitePointCloud.toMultiset, FinitePointCloud.toList,
      Multiset.mem_coe, List.mem_ofFn] at hm
    obtain ⟨k, hk⟩ := hm
    refine ⟨(LocalConfiguration.shellIndex matchingPointBase p, k.val), k.isLt, ?_⟩
    rw [tieEnumeratedPoint_eq c _ k.isLt]
    exact congrArg Subtype.val hk
  · rintro ⟨⟨n, k⟩, hk, hpoint⟩
    let x := (MultisetEncoding.toFinitePointCloud (c n)).point ⟨k, hk⟩
    have hmem : x ∈ c n := by
      rw [← MultisetEncoding.toMultiset_toFinitePointCloud (c n)]
      simp only [FinitePointCloud.toMultiset, FinitePointCloud.toList,
        Multiset.mem_coe, List.mem_ofFn]
      exact ⟨⟨k, hk⟩, rfl⟩
    have hx : LocalConfiguration.multiplicity c x.val ≠ 0 := by
      rw [LocalConfiguration.multiplicity_shell]
      simpa only [Multiset.count_ne_zero] using hmem
    have hxp : x.val = p := by
      rw [tieEnumeratedPoint_eq c _ hk] at hpoint
      exact hpoint
    rw [hxp] at hx
    simpa using hx

/-- Kinetic marked cost, with the original physical mark-to-slope conversion. -/
noncomputable def markedKineticCost (g : ℝ → ℝ) (s t : MatchingPoint) : ℝ :=
  kineticCost g s.1 t.1 (1 - s.2) (1 + t.2)

private theorem marked_cost_difference (g : GraphHeight) {m : ℕ}
    (s t : Fin m → MatchingPoint) (tau : Equiv.Perm (Fin m)) :
    (∑ i, markedQuadraticCost g (s i) (t i)) -
      (∑ i, markedQuadraticCost g (s i) (t (tau i))) =
    (∑ i, markedKineticCost g (s i) (t i)) -
      (∑ i, markedKineticCost g (s i) (t (tau i))) := by
  apply sum_quadraticCost_sub_eq_sum_kineticCost_sub g.continuous
    (fun i ↦ (s i).1) (fun i ↦ (t i).1)
    (fun i ↦ 1 - ((s i).2 : ℝ)) (fun i ↦ 1 + ((t i).2 : ℝ)) tau
  intro i j
  linarith [(s i).2.property.2, (t j).2.property.1]

private def KineticNoFiniteTies (e : FeedbackEnvironment) : Prop :=
  ∀ (m : ℕ) (s t : Fin m → MatchingPoint) (tau : Equiv.Perm (Fin m)),
    Injective s → Injective t →
    (∀ i, LocalConfiguration.countingMeasure e.source {s i} ≠ 0) →
    (∀ i, LocalConfiguration.countingMeasure e.target {t i} ≠ 0) →
    tau ≠ Equiv.refl _ →
    (∑ i, markedKineticCost e.path.graphHeight (s i) (t i)) ≠
      ∑ i, markedKineticCost e.path.graphHeight (s i) (t (tau i))

private theorem noFiniteTies_iff_kinetic (e : FeedbackEnvironment) :
    FeedbackNoFiniteTies e ↔ KineticNoFiniteTies e := by
  constructor
  · intro h m s t tau hs ht hsa hta htau heq
    apply h m s t tau hs ht hsa hta htau
    have hd := marked_cost_difference e.path.graphHeight s t tau
    rw [heq, sub_self] at hd
    exact sub_eq_zero.mp hd
  · intro h m s t tau hs ht hsa hta htau heq
    apply h m s t tau hs ht hsa hta htau
    have hd := marked_cost_difference e.path.graphHeight s t tau
    rw [heq, sub_self] at hd
    exact sub_eq_zero.mp hd.symm

private def EnumeratedNoFiniteTies (e : FeedbackEnvironment) : Prop :=
  ∀ (m : ℕ) (s t : Fin m → ℕ × ℕ) (tau : Equiv.Perm (Fin m)),
    Injective (fun i ↦ tieEnumeratedPoint e.source (s i)) →
    Injective (fun i ↦ tieEnumeratedPoint e.target (t i)) →
    (∀ i, (s i).2 < (e.source (s i).1).card) →
    (∀ i, (t i).2 < (e.target (t i).1).card) → tau ≠ Equiv.refl _ →
    (∑ i, markedKineticCost e.path.graphHeight
      (tieEnumeratedPoint e.source (s i)) (tieEnumeratedPoint e.target (t i))) ≠
    ∑ i, markedKineticCost e.path.graphHeight
      (tieEnumeratedPoint e.source (s i)) (tieEnumeratedPoint e.target (t (tau i)))

private theorem kinetic_iff_enumerated (e : FeedbackEnvironment) :
    KineticNoFiniteTies e ↔ EnumeratedNoFiniteTies e := by
  constructor
  · intro h m s t tau hs ht hsa hta htau
    exact h m _ _ tau hs ht
      (fun i ↦ (atom_iff_tieEnumeratedPoint _ _).mpr ⟨s i, hsa i, rfl⟩)
      (fun i ↦ (atom_iff_tieEnumeratedPoint _ _).mpr ⟨t i, hta i, rfl⟩) htau
  · intro h m s t tau hs ht hsa hta htau
    have hs' (i : Fin m) := (atom_iff_tieEnumeratedPoint e.source (s i)).mp (hsa i)
    have ht' (i : Fin m) := (atom_iff_tieEnumeratedPoint e.target (t i)).mp (hta i)
    choose S hS hSp using hs'
    choose T hT hTp using ht'
    have hSi : Injective (fun i ↦ tieEnumeratedPoint e.source (S i)) := by simpa only [hSp] using hs
    have hTi : Injective (fun i ↦ tieEnumeratedPoint e.target (T i)) := by simpa only [hTp] using ht
    simpa only [hSp, hTp] using h m S T tau hSi hTi hS hT htau

private theorem measurable_markedKineticCost {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → GraphHeight} {s t : Ω → MatchingPoint}
    (hg : Measurable g) (hs : Measurable s) (ht : Measurable t) :
    Measurable (fun w ↦ markedKineticCost (g w) (s w) (t w)) := by
  have hgs : Measurable (fun w ↦ g w (s w).1) :=
    (show Continuous (fun z : GraphHeight × ℝ ↦ z.1 z.2) from continuous_eval).measurable.comp
      (hg.prodMk hs.fst)
  have hgt : Measurable (fun w ↦ g w (t w).1) :=
    (show Continuous (fun z : GraphHeight × ℝ ↦ z.1 z.2) from continuous_eval).measurable.comp
      (hg.prodMk ht.fst)
  have hsm : Measurable (fun w ↦ ((s w).2 : ℝ)) := measurable_subtype_coe.comp hs.snd
  have htm : Measurable (fun w ↦ ((t w).2 : ℝ)) := measurable_subtype_coe.comp ht.snd
  unfold markedKineticCost kineticCost
  exact (((ht.fst.sub hs.fst).add ((measurable_const.sub hsm).mul hgs)).add
    ((measurable_const.add htm).mul hgt)).pow_const (2 : ℕ) |>.div
      (measurable_const.mul ((measurable_const.sub hsm).add (measurable_const.add htm)))

/-- The actual geometric no-tie property is Borel, by canonical enumeration of every finite shell. -/
theorem measurableSet_feedbackNoFiniteTies : MeasurableSet {e | FeedbackNoFiniteTies e} := by
  have heq : {e | FeedbackNoFiniteTies e} = {e | EnumeratedNoFiniteTies e} := by
    ext e
    exact (noFiniteTies_iff_kinetic e).trans (kinetic_iff_enumerated e)
  rw [heq]
  unfold EnumeratedNoFiniteTies
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro s
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro tau
  have hS (i : Fin m) : Measurable (fun e : FeedbackEnvironment ↦ tieEnumeratedPoint e.source (s i)) :=
    (measurable_tieEnumeratedPoint _).comp FeedbackEnvironment.measurable_source
  have hT (i : Fin m) : Measurable (fun e : FeedbackEnvironment ↦ tieEnumeratedPoint e.target (t i)) :=
    (measurable_tieEnumeratedPoint _).comp FeedbackEnvironment.measurable_target
  have hs : MeasurableSet {e : FeedbackEnvironment |
      Injective (fun i ↦ tieEnumeratedPoint e.source (s i))} := by
    simp only [Function.Injective, ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      (measurableSet_eq_fun (hS i) (hS j)).imp (MeasurableSet.const (i = j))
  have ht : MeasurableSet {e : FeedbackEnvironment |
      Injective (fun i ↦ tieEnumeratedPoint e.target (t i))} := by
    simp only [Function.Injective, ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      (measurableSet_eq_fun (hT i) (hT j)).imp (MeasurableSet.const (i = j))
  have hsa : MeasurableSet {e : FeedbackEnvironment | ∀ i, (s i).2 < (e.source (s i).1).card} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const
      ((LocalConfiguration.measurable_shell_card _).comp FeedbackEnvironment.measurable_source)
  have hta : MeasurableSet {e : FeedbackEnvironment | ∀ i, (t i).2 < (e.target (t i).1).card} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const
      ((LocalConfiguration.measurable_shell_card _).comp FeedbackEnvironment.measurable_target)
  have hcost : MeasurableSet {e : FeedbackEnvironment |
      (∑ i, markedKineticCost e.path.graphHeight (tieEnumeratedPoint e.source (s i))
        (tieEnumeratedPoint e.target (t i))) ≠
      ∑ i, markedKineticCost e.path.graphHeight (tieEnumeratedPoint e.source (s i))
        (tieEnumeratedPoint e.target (t (tau i)))} := by
    apply (measurableSet_eq_fun _ _).compl
    · exact Finset.measurable_sum _ (fun i _ ↦ measurable_markedKineticCost
        FeedbackEnvironment.measurable_graphHeight (hS i) (hT i))
    · exact Finset.measurable_sum _ (fun i _ ↦ measurable_markedKineticCost
        FeedbackEnvironment.measurable_graphHeight (hS i) (hT (tau i)))
  exact hs.imp (ht.imp (hsa.imp (hta.imp ((MeasurableSet.const (tau ≠ Equiv.refl _)).imp hcost))))

/-- The actual stationary feedback environment almost surely has no finite alternating ties.
The law is the original normalized occupation of actual iid first-return cells. -/
theorem feedbackStationaryEnvironmentLaw_no_finite_ties
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 (by linarith), FeedbackNoFiniteTies e := by
  let Q := feedbackCellBase lam hlam0 (by linarith : lam < 1 / 2)
  let f : FeedbackCellSequence × ℝ → FeedbackEnvironment :=
    fun p ↦ p.2 +ᵥ feedbackConcatenatedEnvironment lam p.1
  have hf : Measurable f :=
    FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun p : FeedbackCellSequence × ℝ ↦
        (p.2, feedbackConcatenatedEnvironment lam p.1))
      (measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst))
  have hb : MeasurableSet {e | ¬FeedbackNoFiniteTies e} := measurableSet_feedbackNoFiniteTies.compl
  have hz : (Q.prod volume) (f ⁻¹' {e | ¬FeedbackNoFiniteTies e}) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hb.preimage hf)
    filter_upwards [feedbackCellBase_no_finite_ties_all_reroots hlam0 hlam] with w hw
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact ae_of_all _ (fun r h ↦ h (hw r))
  have hr : renewalRoofMeasure Q (fun w ↦ feedbackCellLength (w 0))
      (f ⁻¹' {e | ¬FeedbackNoFiniteTies e}) = 0 := Measure.absolutelyContinuous_restrict hz
  have hbad : feedbackStationaryEnvironmentLaw lam hlam0 (by linarith)
      {e | ¬FeedbackNoFiniteTies e} = 0 := by
    change (_ • (renewalRoofMeasure Q (fun w ↦ feedbackCellLength (w 0))).map f)
      {e | ¬FeedbackNoFiniteTies e} = 0
    rw [Measure.smul_apply, Measure.map_apply hf hb, hr, smul_zero]
  have h := measure_eq_zero_iff_ae_notMem.mp hbad
  simpa only [Set.mem_ofPred_eq, not_not] using h

end OTSelector.Matching
