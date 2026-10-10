import OTSelector.Limit.FeedbackCellReward
import OTSelector.Limit.FeedbackCellConcatenation
import OTSelector.Limit.FeedbackEnvironmentIdentification
import OTSelector.Probability.ExponentialPalm

/-!
# The zero hold at a stationary spatial origin

The actual normalized roof measure is disintegrated over its initial zero hold. The remaining
cell field keeps its Palm law, while the age and residual are independent rate-two exponentials.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators

set_option maxHeartbeats 600000

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

private theorem indepFun_row_fields_infinitePi {ι Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : ι → Ω → A} {g : ι → Ω → B} (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i)) (hfg : ∀ i, IndepFun (f i) (g i) μ) :
    IndepFun (fun ω : ι → Ω ↦ fun i ↦ f i (ω i)) (fun ω ↦ fun i ↦ g i (ω i))
      (Measure.infinitePi (fun _ : ι ↦ μ)) := by
  classical
  let Q := Measure.infinitePi (fun _ : ι ↦ μ)
  let μf := fun i ↦ μ.map (f i)
  let μg := fun i ↦ μ.map (g i)
  let : ∀ i, IsProbabilityMeasure (μf i) := fun i ↦ Measure.isProbabilityMeasure_map (hf i).aemeasurable
  let : ∀ i, IsProbabilityMeasure (μg i) := fun i ↦ Measure.isProbabilityMeasure_map (hg i).aemeasurable
  have hfinite (S : Finset ι) :
      IndepFun (fun ω : ι → Ω ↦ fun i : S ↦ f i (ω i))
        (fun ω ↦ fun i : S ↦ g i (ω i)) Q := by
    have hind := (iIndepFun_infinitePi (P := fun _ : ι ↦ μ)
      (X := fun i ↦ fun w ↦ (f i w, g i w)) (fun i ↦ (hf i).prodMk (hg i))).restrict S
    change iIndepFun (fun (i : S) (ω : ι → Ω) ↦ (f i (ω i), g i (ω i))) Q at hind
    have hm (i : S) : AEMeasurable (fun ω : ι → Ω ↦ (f i (ω i), g i (ω i))) Q :=
      (((hf i).prodMk (hg i)).comp (measurable_pi_apply (i : ι))).aemeasurable
    have hmap := hind.map_fun_eq_pi_map hm
    have hrow (i : S) : Q.map (fun ω ↦ (f i (ω i), g i (ω i))) = (μf i).prod (μg i) := by
      rw [show (fun ω : ι → Ω ↦ (f i (ω i), g i (ω i))) =
          (fun w ↦ (f i w, g i w)) ∘ (fun ω ↦ ω (i : ι)) from rfl,
        ← Measure.map_map ((hf i).prodMk (hg i)) (measurable_pi_apply _),
        Measure.infinitePi_map_eval]
      exact (hfg i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
    change Q.map (fun ω (i : S) ↦ (f i (ω i), g i (ω i))) =
      Measure.pi (fun i : S ↦ Q.map (fun ω ↦ (f i (ω i), g i (ω i)))) at hmap
    simp_rw [hrow] at hmap
    have hp := congrArg (fun ν : Measure (S → A × B) ↦
      ν.map (MeasurableEquiv.arrowProdEquivProdArrow A B S)) hmap
    rw [Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop),
      (measurePreserving_arrowProdEquivProdArrow A B S (fun i : S ↦ μf i) (fun i : S ↦ μg i)).map_eq] at hp
    change Q.map (fun ω ↦ ((fun i : S ↦ f i (ω i)), (fun i : S ↦ g i (ω i)))) =
      (Measure.pi (fun i : S ↦ μf i)).prod (Measure.pi (fun i : S ↦ μg i)) at hp
    have hl := congrArg (fun ν : Measure ((S → A) × (S → B)) ↦ ν.map Prod.fst) hp
    have hr := congrArg (fun ν : Measure ((S → A) × (S → B)) ↦ ν.map Prod.snd) hp
    rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at hl
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod] at hr
    simp only [measure_univ, one_smul, Function.comp_def] at hl hr
    apply (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_lambda _ fun i : S ↦ (hf i).comp (measurable_pi_apply (i : ι))).aemeasurable
      (measurable_pi_lambda _ fun i : S ↦ (hg i).comp (measurable_pi_apply (i : ι))).aemeasurable).mpr
    simp only [Function.comp_def]
    rw [hl, hr]
    exact hp
  apply IndepFun.process_indepFun_process
    (fun i ↦ (hf i).comp (measurable_pi_apply i)) (fun i ↦ (hg i).comp (measurable_pi_apply i))
  intro I J
  have h := (hfinite (I ∪ J)).comp
    (show Measurable (fun v : ↥(I ∪ J) → A ↦ fun i : I ↦
      v ⟨i, Finset.mem_union_left J i.2⟩) from by fun_prop)
    (show Measurable (fun v : ↥(I ∪ J) → B ↦ fun i : J ↦
      v ⟨i, Finset.mem_union_right I i.2⟩) from by fun_prop)
  exact h

/-- All cell data with only the distinguished cell's initial hold erased. Other cells stay intact. -/
noncomputable def feedbackEraseZeroHold (ω : FeedbackCellSequence) : FeedbackCellSequence :=
  fun j ↦ if j = 0 then feedbackMarkedWithoutFirstWait (ω j) else ω j

@[fun_prop]
theorem measurable_feedbackEraseZeroHold : Measurable feedbackEraseZeroHold := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j = 0
  · simp only [feedbackEraseZeroHold, hj, ite_true]
    exact measurable_feedbackMarkedWithoutFirstWait.comp (measurable_pi_apply 0)
  · simp only [feedbackEraseZeroHold, hj, ite_false]
    exact measurable_pi_apply j

/-- The distinguished zero hold is independent of all other actual cell data simultaneously. -/
theorem feedbackCellBase_zero_hold_erased_indep (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IndepFun (fun ω : FeedbackCellSequence ↦ (ω 0 1).1) feedbackEraseZeroHold
      (feedbackCellBase lam hlam0 hlam) := by
  let f : ℤ → FeedbackCellPath → ℝ := fun j w ↦ if j = 0 then (w 1).1 else 0
  let g : ℤ → FeedbackCellPath → FeedbackCellPath := fun j w ↦
    if j = 0 then feedbackMarkedWithoutFirstWait w else w
  have hf (j : ℤ) : Measurable (f j) := by
    by_cases hj : j = 0 <;> simp only [f, hj, ite_true, ite_false] <;> fun_prop
  have hg (j : ℤ) : Measurable (g j) := by
    by_cases hj : j = 0 <;> simp only [g, hj, ite_true, ite_false] <;> fun_prop
  have hi (j : ℤ) : IndepFun (f j) (g j) (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
    by_cases hj : j = 0
    · simpa only [f, g, hj, ite_true] using feedbackMarkedTrajectory_zero_hold_indep lam hlam0 hlam
    · simp only [f, g, hj, ite_false]
      exact indepFun_const_left 0 id
  have h := (indepFun_row_fields_infinitePi _ hf hg hi).comp (measurable_pi_apply 0) measurable_id
  change IndepFun (fun ω : FeedbackCellSequence ↦ (ω 0 1).1)
    (fun ω j ↦ if j = 0 then feedbackMarkedWithoutFirstWait (ω j) else ω j)
    (Measure.infinitePi (fun _ : ℤ ↦ feedbackMarkedTrajectory lam hlam0 hlam 0))
  simpa only [Function.comp_def, f, ite_true, id_eq, g, feedbackEraseZeroHold, feedbackCellBase] using h

/-- Palm law of all data unaffected by changing the distinguished zero hold. -/
noncomputable def feedbackZeroHoldRemainderLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure FeedbackCellSequence :=
  (feedbackCellBase lam hlam0 hlam).map feedbackEraseZeroHold

instance feedbackZeroHoldRemainderLaw_isProbability (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure (feedbackZeroHoldRemainderLaw lam hlam0 hlam) :=
  Measure.isProbabilityMeasure_map measurable_feedbackEraseZeroHold.aemeasurable

/-- Exact actual Palm factorization into the distinguished hold and every remaining cell datum. -/
theorem feedbackCellBase_zero_hold_remainder_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackCellBase lam hlam0 hlam).map (fun ω ↦ ((ω 0 1).1, feedbackEraseZeroHold ω)) =
      (expMeasure 2).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  have hz : (feedbackCellBase lam hlam0 hlam).map (fun ω ↦ (ω 0 1).1) = expMeasure 2 := by
    have hf : Measurable (fun w : FeedbackCellPath ↦ (w 1).1) := by fun_prop
    change (feedbackCellBase lam hlam0 hlam).map
      ((fun w : FeedbackCellPath ↦ (w 1).1) ∘ (fun ω ↦ ω 0)) = _
    rw [← Measure.map_map hf (measurable_pi_apply 0),
      (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).map_eq,
      feedbackMarkedTrajectory_zero_hold_law]
  rw [(feedbackCellBase_zero_hold_erased_indep lam hlam0 hlam).map_prod_eq_prod_map_map
    (show Measurable (fun ω : FeedbackCellSequence ↦ (ω 0 1).1) by fun_prop).aemeasurable
    measurable_feedbackEraseZeroHold.aemeasurable, hz]
  rfl

/-- Unnormalized occupation inside the actual distinguished zero hold.
The closed upper endpoint is harmless for Lebesgue occupation. -/
noncomputable def feedbackZeroHoldOccupation (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure (FeedbackCellSequence × ℝ) :=
  ((feedbackCellBase lam hlam0 hlam).prod volume).restrict
    {p | 0 ≤ p.2 ∧ p.2 ≤ (p.1 0 1).1}

/-- Age, residual, and the complete unaffected cell data at a point of the zero hold. -/
noncomputable def feedbackZeroHoldReadout (p : FeedbackCellSequence × ℝ) :
    (ℝ × ℝ) × FeedbackCellSequence :=
  ((p.2, (p.1 0 1).1 - p.2), feedbackEraseZeroHold p.1)

@[fun_prop]
theorem measurable_feedbackZeroHoldReadout : Measurable feedbackZeroHoldReadout := by
  unfold feedbackZeroHoldReadout
  fun_prop

/-- Actual zero-hold occupation has the exponential age/residual law times the original remainder
law, with the correct unnormalized mass one half. -/
theorem feedbackZeroHoldOccupation_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackZeroHoldOccupation lam hlam0 hlam).map feedbackZeroHoldReadout =
      (ENNReal.ofReal 2)⁻¹ • ((expMeasure 2).prod (expMeasure 2)).prod
        (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  let Q := feedbackCellBase lam hlam0 hlam
  let ν := feedbackZeroHoldRemainderLaw lam hlam0 hlam
  let ρ := expMeasure 2
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 2)
  let : SFinite (exponentialOccupationMeasure 2) := by
    unfold exponentialOccupationMeasure
    infer_instance
  let T : FeedbackCellSequence × ℝ → (ℝ × ℝ) × FeedbackCellSequence :=
    fun p ↦ (((p.1 0 1).1, p.2), feedbackEraseZeroHold p.1)
  have hpair : MeasurePreserving (fun ω ↦ ((ω 0 1).1, feedbackEraseZeroHold ω)) Q (ρ.prod ν) :=
    ⟨by fun_prop, feedbackCellBase_zero_hold_remainder_map lam hlam0 hlam⟩
  have hswap : MeasurePreserving (fun p : (ℝ × FeedbackCellSequence) × ℝ ↦
      ((p.1.1, p.2), p.1.2)) ((ρ.prod ν).prod volume) ((ρ.prod volume).prod ν) := by
    exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ρ volume ν)).comp
        (((MeasurePreserving.id ρ).prod (Measure.measurePreserving_swap (μ := ν) (ν := volume))).comp
          (measurePreserving_prodAssoc ρ ν volume))
  have hT : MeasurePreserving T (Q.prod volume) ((ρ.prod volume).prod ν) :=
    hswap.comp (hpair.prod (MeasurePreserving.id volume))
  let S : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}
  have hS : MeasurableSet S := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hocc : (feedbackZeroHoldOccupation lam hlam0 hlam).map T =
      (exponentialOccupationMeasure 2).prod ν := by
    have heq : {p : FeedbackCellSequence × ℝ | 0 ≤ p.2 ∧ p.2 ≤ (p.1 0 1).1} =
        T ⁻¹' (S ×ˢ univ) := by ext p; simp [T, S]
    rw [feedbackZeroHoldOccupation, heq, ← Measure.restrict_map hT.measurable (hS.prod MeasurableSet.univ),
      hT.map_eq, ← Measure.restrict_prod_eq_prod_univ]
    rfl
  have hread : feedbackZeroHoldReadout =
      (fun p : (ℝ × ℝ) × FeedbackCellSequence ↦ ((p.1.2, p.1.1 - p.1.2), p.2)) ∘ T := rfl
  rw [hread, ← Measure.map_map (by fun_prop) hT.measurable, hocc]
  change ((exponentialOccupationMeasure 2).prod ν).map
    (Prod.map (fun p : ℝ × ℝ ↦ (p.2, p.1 - p.2)) id) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    exponentialOccupationMeasure_map_age_residual (by norm_num : (0 : ℝ) < 2),
    Measure.map_id, Measure.prod_smul_left]

/-- The actual zero-hold occupation normalized by its mass has the full product disintegration. -/
theorem feedbackZeroHoldOccupation_normalized_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (ENNReal.ofReal 2 • feedbackZeroHoldOccupation lam hlam0 hlam).map feedbackZeroHoldReadout =
      ((expMeasure 2).prod (expMeasure 2)).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  rw [Measure.map_smul, feedbackZeroHoldOccupation_map, smul_smul]
  rw [ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofReal_ne_top, one_smul]

/-- Inside a genuine first-return cell, current zero occurs exactly during its initial hold. -/
theorem feedbackCellCurrent_zero_iff_initial_hold (w : FeedbackCellPath)
    (hstart : (w 0).2.2 = 0) (hw : ∀ i, 0 < (w (i + 1)).1)
    (ht : 0 < feedbackMarkedFirstReturnIndex w) (u : ℝ)
    (hu0 : 0 ≤ u) (huL : u < feedbackCellLength w) :
    feedbackCellCurrent w u = 0 ↔ u < (w 1).1 := by
  have hclock := feedbackCellClock_strictMono w hw
  have hL := feedbackCellLength_eq_clock w hw ht
  have hfirst : feedbackCellClock w 1 = (w 1).1 := by
    simpa only [feedbackCellClock_zero, zero_add] using feedbackCellClock_succ w 0
  constructor
  · intro hzero
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    have hterminal : u < feedbackCellClock w (k + 1) := by simpa only [hk] using huL.trans_eq hL
    have hex : ∃ n : ℕ, u < feedbackCellClock w (n + 1) := ⟨k, hterminal⟩
    let n := Nat.find hex
    have hn : n ≤ k := Nat.find_min' hex hterminal
    have hhi : u < feedbackCellClock w (n + 1) := Nat.find_spec hex
    have hlo : feedbackCellClock w n ≤ u := by
      cases hn0 : n with
      | zero => simpa only [hn0, feedbackCellClock_zero] using hu0
      | succ m =>
          exact le_of_not_gt (Nat.find_min hex (show m < Nat.find hex by change m < n; omega))
    have hval := feedbackCellCurrent_eq_of_clock_bounds w n u (by omega) hstart hclock hlo hhi
    rw [hval] at hzero
    have hn0 : n = 0 := by
      by_contra hne
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hmin := ((feedbackMarkedFirstReturnIndex_eq_succ_iff w k).mp hk).2
      exact hmin j (by omega) (by simpa only [hj] using hzero)
    simpa only [hn0, zero_add, hfirst] using hhi
  · intro hu
    have hval := feedbackCellCurrent_eq_of_clock_bounds w 0 u (Nat.zero_le _) hstart hclock
      (by simpa only [feedbackCellClock_zero] using hu0) (by simpa only [hfirst] using hu)
    exact hval.trans hstart

/-- On the roof over cell zero, the concatenated current reads that very cell. -/
theorem feedbackConcatenatedCurrent_eq_cell_zero {ω : FeedbackCellSequence}
    (hω : feedbackCellRootsGood ω) (u : ℝ) (hu0 : 0 ≤ u)
    (huL : u < feedbackCellLength (ω 0)) :
    feedbackConcatenatedCurrent ω u = feedbackCellCurrent (ω 0) u := by
  have hi : feedbackCellIndex ω u = 0 := by
    apply (feedbackCellIndex_eq_iff hω u 0).mpr
    have hr : feedbackCellRoot ω 1 = feedbackCellLength (ω 0) := by
      simpa only [zero_add, feedbackCellRoot_zero] using feedbackCellRoot_add_one ω 0
    simpa only [feedbackCellRoot_zero, zero_add, hr] using And.intro hu0 huL
  simp only [feedbackConcatenatedCurrent, hi, feedbackCellRoot_zero, sub_zero]

/-- The exact zero-hold characterization holds for the actual iid cell field. -/
theorem feedbackCellBase_current_zero_iff_initial_hold {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam, ∀ u : ℝ,
      0 ≤ u → u < feedbackCellLength (ω 0) →
        (feedbackConcatenatedCurrent ω u = 0 ↔ u < (ω 0 1).1) := by
  have hz := feedbackMarkedTrajectory_initial hlam0 hlam 0
  have hw := feedbackMarkedTrajectory_waits_positive hlam0 hlam 0
  have ht := feedbackMarkedFirstReturnIndex_pos hlam0 hlam
  rw [← (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).map_eq] at hz hw ht
  filter_upwards [feedbackCellBase_roots_good hlam0 hlam,
    ae_of_ae_map (measurable_pi_apply 0).aemeasurable hz,
    ae_of_ae_map (measurable_pi_apply 0).aemeasurable hw,
    ae_of_ae_map (measurable_pi_apply 0).aemeasurable ht] with ω hroots hstart hwait hret
  intro u hu0 huL
  rw [feedbackConcatenatedCurrent_eq_cell_zero hroots u hu0 huL]
  exact feedbackCellCurrent_zero_iff_initial_hold (ω 0) (by rw [hstart]; rfl) hwait hret u hu0 huL

/-- Normalized actual suspension measure before reading out the environment. -/
noncomputable def feedbackStationaryRoofLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure (FeedbackCellSequence × ℝ) :=
  (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ •
    renewalRoofMeasure (feedbackCellBase lam hlam0 hlam) (fun ω ↦ feedbackCellLength (ω 0))

instance feedbackStationaryRoofLaw_isProbability (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure (feedbackStationaryRoofLaw lam hlam0 hlam) := by
  have hL : Measurable (fun ω : FeedbackCellSequence ↦ feedbackCellLength (ω 0)) :=
    measurable_feedbackCellLength.comp (measurable_pi_apply 0)
  constructor
  rw [feedbackStationaryRoofLaw, Measure.smul_apply, smul_eq_mul,
    renewalRoofMeasure_univ _ hL,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_feedbackCellBase_length hlam0 hlam 0)
      (ae_of_all _ fun ω ↦ feedbackCellLength_nonneg (ω 0)), integral_feedbackCellBase_length]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (feedbackCellMean_pos hlam0 hlam))
    ENNReal.ofReal_ne_top

/-- The actual feedback environment read at the spatial point selected by occupation. -/
noncomputable def feedbackRoofEnvironment (lam : ℝ) (p : FeedbackCellSequence × ℝ) :
    PointProcess.FeedbackEnvironment :=
  PointProcess.FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1)

theorem measurable_feedbackRoofEnvironment (lam : ℝ) : Measurable (feedbackRoofEnvironment lam) := by
  change Measurable (fun p : FeedbackCellSequence × ℝ ↦
    PointProcess.FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1))
  have hm : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      (p.2, feedbackConcatenatedEnvironment lam p.1)) :=
    measurable_snd.prodMk ((measurable_feedbackConcatenatedEnvironment lam).comp measurable_fst)
  exact PointProcess.FeedbackEnvironment.measurable_uncurry_reroot.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ (p.2, feedbackConcatenatedEnvironment lam p.1)) hm

/-- This roof readout is exactly the already constructed stationary environment law. -/
theorem feedbackStationaryRoofLaw_environment_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackStationaryRoofLaw lam hlam0 hlam).map (feedbackRoofEnvironment lam) =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
  rw [feedbackStationaryRoofLaw, Measure.map_smul, feedbackStationaryEnvironmentLaw,
    renewalStationaryLaw, integral_feedbackCellBase_length]
  rfl

/-- The event that the actual environment observed at the roof point has zero current. -/
def feedbackRoofCurrentZero (lam : ℝ) : Set (FeedbackCellSequence × ℝ) :=
  {p | (feedbackRoofEnvironment lam p).path.rootCurrent = 0}

theorem measurableSet_feedbackRoofCurrentZero (lam : ℝ) :
    MeasurableSet (feedbackRoofCurrentZero lam) :=
  measurableSet_eq_fun (PointProcess.FeedbackEnvironment.measurable_rootCurrent.comp
    (measurable_feedbackRoofEnvironment lam)) measurable_const

/-- Restricting the actual roof to observed current zero is exactly occupation of the initial
zero hold. This also removes the null departure endpoint. -/
theorem feedbackRoof_restrict_currentZero (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun ω ↦ feedbackCellLength (ω 0))).restrict (feedbackRoofCurrentZero lam) =
        feedbackZeroHoldOccupation lam hlam0 hlam := by
  let Q := feedbackCellBase lam hlam0 hlam
  let R : Set (FeedbackCellSequence × ℝ) := {p | 0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)}
  let Z : Set (FeedbackCellSequence × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ (p.1 0 1).1}
  have hR : MeasurableSet R := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_feedbackCellLength.comp
        ((measurable_pi_apply 0).comp measurable_fst)))
  have hZ : MeasurableSet Z := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  rw [renewalRoofMeasure, Measure.restrict_restrict (measurableSet_feedbackRoofCurrentZero lam)]
  apply Measure.restrict_congr_set
  change ∀ᵐ p ∂Q.prod volume, (p ∈ feedbackRoofCurrentZero lam ∩ R) = (p ∈ Z)
  have heq : ∀ᵐ p ∂Q.prod volume, (p ∈ feedbackRoofCurrentZero lam ∩ R) ↔ (p ∈ Z) := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_feedbackRoofCurrentZero lam).inter hR |>.iff hZ)).mpr
    have hlength := feedbackCellLength_eq_hold_add_excursion hlam0 hlam
    rw [← (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).map_eq] at hlength
    filter_upwards [feedbackCellBase_current_zero_iff_initial_hold hlam0 hlam,
      ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam,
      ae_of_ae_map (measurable_pi_apply 0).aemeasurable hlength] with ω hzero hid hL
    filter_upwards [volume.ae_ne (ω 0 1).1] with u hu
    have hobs : (feedbackRoofEnvironment lam (ω, u)).path.rootCurrent =
        feedbackConcatenatedCurrent ω u := hid u
    have hZL : (ω 0 1).1 ≤ feedbackCellLength (ω 0) := by
      rw [hL]
      exact le_add_of_nonneg_right (feedbackCellExcursionLength_nonneg _)
    change (((feedbackRoofEnvironment lam (ω, u)).path.rootCurrent = 0) ∧
      (0 ≤ u ∧ u < feedbackCellLength (ω 0))) ↔ (0 ≤ u ∧ u ≤ (ω 0 1).1)
    rw [hobs]
    constructor
    · rintro ⟨hc, hu0, huL⟩
      exact ⟨hu0, ((hzero u hu0 huL).mp hc).le⟩
    · rintro ⟨hu0, huZ⟩
      have huZ' := lt_of_le_of_ne huZ hu
      have huL := huZ'.trans_le hZL
      exact ⟨(hzero u hu0 huL).mpr huZ', hu0, huL⟩
  exact heq.mono fun _ h ↦ propext h

/-- Actual stationary zero-current restriction has an explicit product pushforward. -/
theorem feedbackStationaryRoofLaw_zero_readout (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ((feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofCurrentZero lam)).map
        feedbackZeroHoldReadout =
      ((ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ * (ENNReal.ofReal 2)⁻¹) •
        ((expMeasure 2).prod (expMeasure 2)).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  rw [feedbackStationaryRoofLaw, Measure.restrict_smul, feedbackRoof_restrict_currentZero,
    Measure.map_smul, feedbackZeroHoldOccupation_map, smul_smul]

/-- Stationary probability of observing current zero, with the true mean roof denominator. -/
theorem feedbackStationaryRoofLaw_currentZero_mass (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofCurrentZero lam) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ * (ENNReal.ofReal 2)⁻¹ := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 2)
  have h := congrArg (fun μ : Measure ((ℝ × ℝ) × FeedbackCellSequence) ↦ μ univ)
    (feedbackStationaryRoofLaw_zero_readout lam hlam0 hlam)
  rw [Measure.map_apply measurable_feedbackZeroHoldReadout MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply] at h
  simpa only [measure_univ, smul_eq_mul, mul_one] using h

/-- Conditioning the actual stationary roof on observed current zero gives independent age and
residual Exp(2) variables and the unchanged joint Palm law of every remaining cell datum. -/
theorem feedbackStationaryRoofLaw_conditional_zero_readout (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofCurrentZero lam))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofCurrentZero lam)).map
        feedbackZeroHoldReadout =
      ((expMeasure 2).prod (expMeasure 2)).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  rw [Measure.map_smul, feedbackStationaryRoofLaw_zero_readout,
    feedbackStationaryRoofLaw_currentZero_mass, smul_smul]
  rw [ENNReal.inv_mul_cancel, one_smul]
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (feedbackCellMean_pos hlam0 hlam))
    · exact ENNReal.inv_ne_top.mpr (by norm_num)

/-- The zero-current event has positive mass in the actual stationary roof law. -/
theorem feedbackStationaryRoofLaw_currentZero_pos (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    0 < feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofCurrentZero lam) := by
  rw [feedbackStationaryRoofLaw_currentZero_mass]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

/-- The same zero-current mass is observed in the actual stationary environment. -/
theorem feedbackStationaryEnvironmentLaw_currentZero_mass (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    feedbackStationaryEnvironmentLaw lam hlam0 hlam {e | e.path.rootCurrent = 0} =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ * (ENNReal.ofReal 2)⁻¹ := by
  rw [← feedbackStationaryRoofLaw_environment_map lam hlam0 hlam,
    Measure.map_apply (measurable_feedbackRoofEnvironment lam)
      (measurableSet_eq_fun PointProcess.FeedbackEnvironment.measurable_rootCurrent measurable_const)]
  exact feedbackStationaryRoofLaw_currentZero_mass lam hlam0 hlam

/-- Every nonnegative unit residual band has positive exponential probability. -/
theorem expMeasure_two_unitBand_pos (h : ℝ) (hh : 0 ≤ h) :
    0 < expMeasure 2 (Icc h (h + 1)) := by
  have hpdf : Measurable (exponentialPDF 2) := (measurable_exponentialPDFReal 2).ennreal_ofReal
  change 0 < (volume.withDensity (exponentialPDF 2)) (Icc h (h + 1))
  rw [withDensity_apply _ measurableSet_Icc, setLIntegral_pos_iff hpdf]
  have heq : Function.support (exponentialPDF 2) ∩ Icc h (h + 1) = Icc h (h + 1) := by
    apply inter_eq_right.mpr
    intro x hx
    change exponentialPDF 2 x ≠ 0
    rw [exponentialPDF_of_nonneg (hh.trans hx.1)]
    exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (Real.exp_pos _))).ne'
  rw [heq, Real.volume_Icc]
  norm_num

/-- Restrict current zero further by a specified unit band of the remaining waiting time. -/
def feedbackRoofHoldBand (lam h : ℝ) : Set (FeedbackCellSequence × ℝ) :=
  {p | h ≤ (p.1 0 1).1 - p.2 ∧ (p.1 0 1).1 - p.2 ≤ h + 1} ∩ feedbackRoofCurrentZero lam

theorem measurableSet_feedbackRoofHoldBand (lam h : ℝ) :
    MeasurableSet (feedbackRoofHoldBand lam h) := by
  have hm : Measurable (fun p : FeedbackCellSequence × ℝ ↦ (p.1 0 1).1 - p.2) := by fun_prop
  exact ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)).inter
    (measurableSet_feedbackRoofCurrentZero lam)

/-- All roof data remaining after discarding the residual of the distinguished zero hold. -/
noncomputable def feedbackZeroHoldRestReadout (p : FeedbackCellSequence × ℝ) :
    ℝ × FeedbackCellSequence := (p.2, feedbackEraseZeroHold p.1)

@[fun_prop]
theorem measurable_feedbackZeroHoldRestReadout : Measurable feedbackZeroHoldRestReadout :=
  measurable_snd.prodMk (measurable_feedbackEraseZeroHold.comp measurable_fst)

/-- Residual-band occupation factors into its scalar band probability and the unchanged
joint law of the age and all unaffected cell data. -/
theorem feedbackStationaryRoofLaw_band_rest_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) :
    ((feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
        feedbackZeroHoldRestReadout =
      ((ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ * (ENNReal.ofReal 2)⁻¹ *
        expMeasure 2 (Icc h (h + 1))) •
          (expMeasure 2).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 2)
  let B : Set ((ℝ × ℝ) × FeedbackCellSequence) := (univ ×ˢ Icc h (h + 1)) ×ˢ univ
  have hB : MeasurableSet B := (MeasurableSet.univ.prod measurableSet_Icc).prod MeasurableSet.univ
  let G : ((ℝ × ℝ) × FeedbackCellSequence) → ℝ × FeedbackCellSequence :=
    fun p ↦ (p.1.1, p.2)
  have hG : Measurable G := by fun_prop
  have hpre : feedbackZeroHoldReadout ⁻¹' B =
      {p : FeedbackCellSequence × ℝ | h ≤ (p.1 0 1).1 - p.2 ∧ (p.1 0 1).1 - p.2 ≤ h + 1} := by
    ext p
    simp only [B, feedbackZeroHoldReadout, mem_preimage, mem_prod, mem_univ,
      mem_Icc, true_and, and_true, Set.mem_ofPred_eq]
  have heq := congrArg (fun μ : Measure ((ℝ × ℝ) × FeedbackCellSequence) ↦ (μ.restrict B).map G)
    (feedbackStationaryRoofLaw_zero_readout lam hlam0 hlam)
  rw [Measure.restrict_map measurable_feedbackZeroHoldReadout hB, hpre,
    Measure.restrict_restrict (by measurability),
    Measure.map_map hG measurable_feedbackZeroHoldReadout,
    Measure.restrict_smul, Measure.map_smul] at heq
  change ((feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
    feedbackZeroHoldRestReadout = _ at heq
  rw [show B = (univ ×ˢ Icc h (h + 1)) ×ˢ (univ : Set FeedbackCellSequence) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_restrict,
    Measure.restrict_univ] at heq
  change ((feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
    feedbackZeroHoldRestReadout =
    _ • (((expMeasure 2).prod ((expMeasure 2).restrict (Icc h (h + 1)))).prod
      (feedbackZeroHoldRemainderLaw lam hlam0 hlam)).map (Prod.map Prod.fst id) at heq
  rw [← Measure.map_prod_map _ _ measurable_fst measurable_id,
    Measure.map_fst_prod, Measure.restrict_apply_univ, Measure.map_id,
    Measure.prod_smul_left, smul_smul] at heq
  exact heq

/-- Exact probability of the actual fixed-origin residual-band event. -/
theorem feedbackStationaryRoofLaw_band_mass (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) :
    feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ * (ENNReal.ofReal 2)⁻¹ *
        expMeasure 2 (Icc h (h + 1)) := by
  let := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 2)
  have heq := congrArg (fun μ : Measure (ℝ × FeedbackCellSequence) ↦ μ univ)
    (feedbackStationaryRoofLaw_band_rest_map lam hlam0 hlam h)
  rw [Measure.map_apply measurable_feedbackZeroHoldRestReadout MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply] at heq
  simpa only [measure_univ, smul_eq_mul, mul_one] using heq

theorem feedbackStationaryRoofLaw_band_pos (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    0 < feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h) := by
  rw [feedbackStationaryRoofLaw_band_mass]
  exact ENNReal.mul_pos
    (mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) (expMeasure_two_unitBand_pos h hh).ne'

/-- After conditioning on any nonnegative residual band and discarding that residual, the age
and complete remaining cell data have a law independent of the band location. -/
theorem feedbackStationaryRoofLaw_conditional_band_rest_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    (((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
        feedbackZeroHoldRestReadout =
      (expMeasure 2).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam) := by
  rw [Measure.map_smul, feedbackStationaryRoofLaw_band_rest_map, smul_smul,
    ← feedbackStationaryRoofLaw_band_mass]
  rw [ENNReal.inv_mul_cancel (ne_of_gt (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh))
    (measure_ne_top _ _), one_smul]

/-- Reinsert only the age into the erased distinguished hold. This removes its residual and
keeps every mark, current, later wait, and other cell unchanged. -/
noncomputable def feedbackCollapseZeroHoldAssemble (p : ℝ × FeedbackCellSequence) :
    FeedbackCellSequence := fun j n ↦
  if j = 0 ∧ n = 1 then (p.1, (p.2 j n).2) else p.2 j n

@[fun_prop]
theorem measurable_feedbackCollapseZeroHoldAssemble : Measurable feedbackCollapseZeroHoldAssemble := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro n
  by_cases h : j = 0 ∧ n = 1 <;>
    simp [feedbackCollapseZeroHoldAssemble, h] <;> fun_prop

/-- Actual cell sequence with the remaining distinguished hold collapsed to zero at the root. -/
noncomputable def feedbackCollapseZeroHold (p : FeedbackCellSequence × ℝ) : FeedbackCellSequence :=
  feedbackCollapseZeroHoldAssemble (feedbackZeroHoldRestReadout p)

@[fun_prop]
theorem measurable_feedbackCollapseZeroHold : Measurable feedbackCollapseZeroHold :=
  measurable_feedbackCollapseZeroHoldAssemble.comp measurable_feedbackZeroHoldRestReadout

theorem feedbackCollapseZeroHold_first_wait (p : FeedbackCellSequence × ℝ) :
    feedbackCollapseZeroHold p 0 1 = (p.2, (p.1 0 1).2) := by
  simp [feedbackCollapseZeroHold, feedbackCollapseZeroHoldAssemble,
    feedbackZeroHoldRestReadout, feedbackEraseZeroHold]

theorem feedbackCollapseZeroHold_other_cell (p : FeedbackCellSequence × ℝ) {j : ℤ} (hj : j ≠ 0) :
    feedbackCollapseZeroHold p j = p.1 j := by
  funext n
  simp [feedbackCollapseZeroHold, feedbackCollapseZeroHoldAssemble,
    feedbackZeroHoldRestReadout, feedbackEraseZeroHold, hj]

/-- The actual collapsed cell field has one law for every nonnegative residual band. -/
theorem feedbackStationaryRoofLaw_conditional_band_collapse_map (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    (((feedbackStationaryRoofLaw lam hlam0 hlam (feedbackRoofHoldBand lam h))⁻¹) •
      (feedbackStationaryRoofLaw lam hlam0 hlam).restrict (feedbackRoofHoldBand lam h)).map
        feedbackCollapseZeroHold =
      ((expMeasure 2).prod (feedbackZeroHoldRemainderLaw lam hlam0 hlam)).map
        feedbackCollapseZeroHoldAssemble := by
  change Measure.map (feedbackCollapseZeroHoldAssemble ∘ feedbackZeroHoldRestReadout) _ = _
  rw [← Measure.map_map measurable_feedbackCollapseZeroHoldAssemble measurable_feedbackZeroHoldRestReadout,
    feedbackStationaryRoofLaw_conditional_band_rest_map lam hlam0 hlam h hh]

end OTSelector.Limit
