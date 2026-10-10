import OTSelector.Basic.FiniteSampleLeaveOneOut
import OTSelector.Feedback.FeedbackLeftRateStopping
import OTSelector.Probability.IndependentFiberNull
import OTSelector.Probability.IndependentRandomRegion
import OTSelector.Probability.CountingProcess.ContinuousOpenHitting
import OTSelector.Probability.CountingProcess.FiniteEventRawIntensity
import OTSelector.Probability.CountingProcess.PredictableFiniteSupport
import OTSelector.Probability.CountingProcess.StoppingMasks

/-!
# Counting intensities on the left zero-shear segment

The physical left coordinate is `x = n h`.  This file assigns the boundary convention
`(0, B]` to the left segment: height zero is never a jump, while a label exactly at `B` is
counted here and must be excluded from the following bulk segment.

The canonical sample is almost surely free of zero heights and height ties.  We expose that
full-measure event at time zero, as is legitimate in the usual augmentation, and send all event
times to `top` on its null complement.  This makes both counting paths simple pathwise without
changing the ordinary left counts almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Physical event times and the full-measure no-tie event -/

/-- The two colors of left-boundary labels. -/
abbrev LeftHeightLabel (n : ℕ) := Fin 2 × Fin n

/-- Height coordinate selected by a colored left-boundary label. -/
def leftHeightCoordinate (label : LeftHeightLabel n) (sample : FiniteSample n) : UnitMark :=
  if label.1 = 0 then sample.sourceHeight label.2 else sample.targetHeight label.2

/-- The underlying scalar coordinate occupied by a colored height label. -/
def leftHeightCoordinateIndex (label : LeftHeightLabel n) : CoordinateIndex n :=
  (⟨2 * label.1.val + 1, by omega⟩, label.2)

theorem coordinate_leftHeightCoordinateIndex (label : LeftHeightLabel n)
    (sample : FiniteSample n) :
    coordinate (leftHeightCoordinateIndex label) sample = leftHeightCoordinate label sample := by
  rcases label with ⟨color, i⟩
  fin_cases color <;> rfl

theorem leftHeightCoordinateIndex_injective :
    Function.Injective (leftHeightCoordinateIndex : LeftHeightLabel n → CoordinateIndex n) := by
  intro label other h
  have hcolor : label.1 = other.1 := by
    apply Fin.ext
    have hval := congrArg (fun p : CoordinateIndex n ↦ p.1.val) h
    simpa [leftHeightCoordinateIndex] using hval
  have hindex : label.2 = other.2 := congrArg (fun p : CoordinateIndex n ↦ p.2) h
  exact Prod.ext hcolor hindex

/-- Restore the scalar height selected by one colored label. -/
def leftHeightRestore (selected : LeftHeightLabel n)
    (rest : FiniteSample n) (x : UnitMark) : FiniteSample n :=
  coordinateRestore (leftHeightCoordinateIndex selected) rest x

theorem measurable_leftHeightRestore (selected : LeftHeightLabel n) :
    Measurable (fun z : FiniteSample n × UnitMark ↦
      leftHeightRestore selected z.1 z.2) := by
  simpa only [leftHeightRestore] using
    measurable_coordinateRestore (leftHeightCoordinateIndex selected)

theorem leftHeightCoordinate_leftHeightRestore
    (selected label : LeftHeightLabel n) (rest : FiniteSample n) (x : UnitMark) :
    leftHeightCoordinate label (leftHeightRestore selected rest x) =
      if label = selected then x else leftHeightCoordinate label rest := by
  rw [← coordinate_leftHeightCoordinateIndex,
    ← coordinate_leftHeightCoordinateIndex label rest]
  by_cases h : label = selected
  · subst label
    simp [leftHeightRestore]
  · have hindex : leftHeightCoordinateIndex label ≠
        leftHeightCoordinateIndex selected :=
      fun heq ↦ h (leftHeightCoordinateIndex_injective heq)
    rw [ite_eq_right h, leftHeightRestore,
      coordinateRestore_coordinate_eq_of_ne _ _ hindex]

theorem leftHeightRestore_coordinateLeaveOneOut
    (selected : LeftHeightLabel n) (sample : FiniteSample n) :
    leftHeightRestore selected
      (coordinateLeaveOneOut (leftHeightCoordinateIndex selected) sample)
      (leftHeightCoordinate selected sample) = sample := by
  rw [leftHeightRestore, ← coordinate_leftHeightCoordinateIndex]
  exact coordinateRestore_coordinateLeaveOneOut _ _

theorem measurable_leftHeightCoordinate (label : LeftHeightLabel n) :
    Measurable (leftHeightCoordinate label : FiniteSample n → UnitMark) := by
  by_cases h : label.1 = 0
  · rw [show leftHeightCoordinate label =
        fun sample : FiniteSample n ↦ sample.sourceHeight label.2 by
      funext sample
      simp only [leftHeightCoordinate, h, ite_true]]
    exact FiniteSample.measurable_sourceHeight label.2
  · rw [show leftHeightCoordinate label =
        fun sample : FiniteSample n ↦ sample.targetHeight label.2 by
      funext sample
      simp only [leftHeightCoordinate, h, ite_false]]
    exact FiniteSample.measurable_targetHeight label.2

/-- All source and target heights are nonzero and pairwise distinct. -/
def leftHeightGenericEvent (n : ℕ) : Set (FiniteSample n) :=
  {sample | (∀ label : LeftHeightLabel n, leftHeightCoordinate label sample ≠ 0) ∧
    ∀ label other : LeftHeightLabel n,
      leftHeightCoordinate label sample = leftHeightCoordinate other sample → label = other}

theorem measurableSet_leftHeightGenericEvent (n : ℕ) :
    MeasurableSet (leftHeightGenericEvent n) := by
  rw [show leftHeightGenericEvent n =
    ((⋂ label : LeftHeightLabel n,
        {sample : FiniteSample n | leftHeightCoordinate label sample ≠ 0}) ∩
      ⋂ label : LeftHeightLabel n, ⋂ other : LeftHeightLabel n,
        {sample : FiniteSample n |
          leftHeightCoordinate label sample = leftHeightCoordinate other sample →
            label = other}) by
      ext sample
      simp [leftHeightGenericEvent]]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun label ↦
      (measurableSet_eq_fun (measurable_leftHeightCoordinate label) measurable_const).compl
  · apply MeasurableSet.iInter
    intro label
    apply MeasurableSet.iInter
    intro other
    by_cases h : label = other
    · subst other
      simp
    · have heq :
          {sample : FiniteSample n |
              leftHeightCoordinate label sample = leftHeightCoordinate other sample →
                label = other} =
            {sample : FiniteSample n |
              leftHeightCoordinate label sample ≠ leftHeightCoordinate other sample} := by
          ext sample
          simp [h]
      rw [heq]
      exact (measurableSet_eq_fun (measurable_leftHeightCoordinate label)
        (measurable_leftHeightCoordinate other)).compl

private theorem measure_leftHeightCoordinate_eq_zero
    (label : LeftHeightLabel n) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | leftHeightCoordinate label sample = 0} = 0 := by
  let p := leftHeightCoordinateIndex label
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  have hnull := measure_eq_comp_eq_zero_of_indepFun
    (left := coordinateLeaveOneOut p) (right := coordinate p)
    (value := fun _ : FiniteSample n ↦ (0 : UnitMark))
    (measurable_coordinateLeaveOneOut p) (measurable_coordinate p) measurable_const
    (coordinateLeaveOneOut_indepFun_coordinate p)
    (congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p))
  simpa [p, coordinate_leftHeightCoordinateIndex] using hnull

private theorem measure_leftHeightCoordinate_eq_leftHeightCoordinate_eq_zero
    (label other : LeftHeightLabel n) (hne : label ≠ other) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | leftHeightCoordinate label sample = leftHeightCoordinate other sample} = 0 := by
  let p := leftHeightCoordinateIndex label
  let q := leftHeightCoordinateIndex other
  have hqp : q ≠ p := fun h ↦ hne (leftHeightCoordinateIndex_injective h.symm)
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  have hnull := measure_eq_comp_eq_zero_of_indepFun
    (left := coordinateLeaveOneOut p) (right := coordinate p)
    (value := coordinate q)
    (measurable_coordinateLeaveOneOut p) (measurable_coordinate p)
    (measurable_coordinate q)
    (coordinateLeaveOneOut_indepFun_coordinate p)
    (congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p))
  have hset :
      {sample : FiniteSample n |
        leftHeightCoordinate label sample = leftHeightCoordinate other sample} =
        {sample : FiniteSample n |
          coordinate p sample = coordinate q (coordinateLeaveOneOut p sample)} := by
    ext sample
    change leftHeightCoordinate label sample = leftHeightCoordinate other sample ↔
      coordinate p sample = coordinate q (coordinateLeaveOneOut p sample)
    rw [coordinateLeaveOneOut_coordinate_eq_of_ne p q hqp]
    simp only [p, q, coordinate_leftHeightCoordinateIndex]
  rw [hset]
  exact hnull

/-- The exceptional zero-height and same/cross-color tie samples form an explicit finite union
of null coordinate events. -/
theorem measure_leftHeightGenericEvent_compl_eq_zero (n : ℕ) :
    (finiteSampleLaw n : Measure (FiniteSample n)) (leftHeightGenericEvent n)ᶜ = 0 := by
  rw [show (leftHeightGenericEvent n)ᶜ =
      (⋃ label : LeftHeightLabel n,
          {sample : FiniteSample n | leftHeightCoordinate label sample = 0}) ∪
        ⋃ label : LeftHeightLabel n, ⋃ other : {other : LeftHeightLabel n // label ≠ other},
          {sample : FiniteSample n |
            leftHeightCoordinate label sample = leftHeightCoordinate other.1 sample} by
    ext sample
    simp only [leftHeightGenericEvent, mem_compl_iff, mem_ofPred_eq, not_and_or,
      not_forall, not_not, mem_union, mem_iUnion]
    constructor
    · rintro (hzero | htie)
      · exact Or.inl hzero
      · obtain ⟨label, other, heq, hne⟩ := htie
        exact Or.inr ⟨label, ⟨⟨other, hne⟩, heq⟩⟩
    · rintro (hzero | htie)
      · exact Or.inl hzero
      · obtain ⟨label, other, heq⟩ := htie
        exact Or.inr ⟨label, other.1, heq, other.2⟩]
  rw [measure_union_null]
  · rw [measure_iUnion_null_iff]
    exact fun label ↦ measure_leftHeightCoordinate_eq_zero label
  · rw [measure_iUnion_null_iff]
    intro label
    rw [measure_iUnion_null_iff]
    intro other
    exact measure_leftHeightCoordinate_eq_leftHeightCoordinate_eq_zero
      label other.1 other.2

theorem ae_mem_leftHeightGenericEvent (n : ℕ) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample ∈ leftHeightGenericEvent n := by
  rw [ae_iff]
  exact measure_leftHeightGenericEvent_compl_eq_zero n

private theorem finite_bad_leftHeightRestore_fiber_of_exists_good
    (selected : LeftHeightLabel n) (rest : FiniteSample n)
    (hexists : ∃ x : UnitMark,
      leftHeightRestore selected rest x ∈ leftHeightGenericEvent n) :
    {x : UnitMark |
      leftHeightRestore selected rest x ∉ leftHeightGenericEvent n}.Finite := by
  obtain ⟨x0, hgood0⟩ := hexists
  let forbidden : Set UnitMark :=
    insert 0 (Set.range fun label : {label : LeftHeightLabel n // label ≠ selected} ↦
      leftHeightCoordinate label.1 rest)
  have hforbidden : forbidden.Finite := by
    exact (Set.finite_range fun label :
      {label : LeftHeightLabel n // label ≠ selected} ↦
        leftHeightCoordinate label.1 rest).insert 0
  apply hforbidden.subset
  intro x hbad
  by_contra hxForbidden
  have hx0 : x ≠ (0 : UnitMark) := by
    intro hx
    apply hxForbidden
    simp [forbidden, hx]
  have hxOther : ∀ label : LeftHeightLabel n, label ≠ selected →
      x ≠ leftHeightCoordinate label rest := by
    intro label hlabel hx
    apply hxForbidden
    apply Set.mem_insert_iff.mpr
    right
    exact ⟨⟨label, hlabel⟩, hx.symm⟩
  apply hbad
  constructor
  · intro label
    by_cases hlabel : label = selected
    · subst label
      simpa [leftHeightCoordinate_leftHeightRestore] using hx0
    · have hnonzero := hgood0.1 label
      simpa [leftHeightCoordinate_leftHeightRestore, hlabel] using hnonzero
  · intro label other heq
    by_cases hlabel : label = selected
    · subst label
      by_cases hother : other = selected
      · exact hother.symm
      · have : x = leftHeightCoordinate other rest := by
          simpa [leftHeightCoordinate_leftHeightRestore, hother] using heq
        exact (hxOther other hother this).elim
    · by_cases hother : other = selected
      · subst other
        have : x = leftHeightCoordinate label rest := by
          simpa [leftHeightCoordinate_leftHeightRestore, hlabel] using heq.symm
        exact (hxOther label hlabel this).elim
      · apply hgood0.2 label other
        simpa [leftHeightCoordinate_leftHeightRestore, hlabel, hother] using heq

/-- Raw physical event time, truncated after `B`.  The raw family may contain zero or tied
times; the safe family below removes them on the null exceptional event. -/
noncomputable def leftRawEventTime
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) :
    FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  let x : ℝ := n * (leftHeightCoordinate label sample : ℝ)
  if x ≤ B then ((Real.toNNReal x : ℝ≥0) : WithTop ℝ≥0) else ⊤

theorem measurable_leftRawEventTime
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) :
    Measurable (leftRawEventTime n B label) := by
  let x : FiniteSample n → ℝ := fun sample ↦
    n * (leftHeightCoordinate label sample : ℝ)
  have hx : Measurable x :=
    measurable_const.mul ((measurable_leftHeightCoordinate label).subtype_coe)
  have hbranch : Measurable fun sample : FiniteSample n ↦
      ((Real.toNNReal (x sample) : ℝ≥0) : WithTop ℝ≥0) :=
    Measurable.withTop_coe (measurable_real_toNNReal.comp hx)
  exact Measurable.ite (measurableSet_le hx measurable_const) hbranch measurable_const

/-- Safe event time.  The left segment owns `B`, hence the non-strict upper cutoff. -/
noncomputable def leftEventTime
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) :
    FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  if sample ∈ leftHeightGenericEvent n then leftRawEventTime n B label sample else ⊤

theorem measurable_leftEventTime
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) :
    Measurable (leftEventTime n B label) := by
  exact Measurable.ite (measurableSet_leftHeightGenericEvent n)
    (measurable_leftRawEventTime n B label) measurable_const

/-- Raw left history at time `t`: the generic-event bit is exposed at time zero and each raw
event time is censored until it occurs. -/
noncomputable def leftRawSnapshot
    (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) :
    Bool × (LeftHeightLabel n → WithTop ℝ≥0) :=
  (decide (sample ∈ leftHeightGenericEvent n), fun label ↦
    if leftRawEventTime n B label sample ≤ (t : WithTop ℝ≥0) then
      leftRawEventTime n B label sample else ⊤)

theorem measurable_leftRawSnapshot (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) :
    Measurable (leftRawSnapshot n B t) := by
  apply Measurable.prodMk
  · exact Measurable.ite (measurableSet_leftHeightGenericEvent n)
      measurable_const measurable_const
  · apply measurable_pi_lambda
    intro label
    exact Measurable.ite
      (measurableSet_le (measurable_leftRawEventTime n B label) measurable_const)
      (measurable_leftRawEventTime n B label) measurable_const

private theorem leftRawEventTime_restore_self_not_le_of_lt
    (n : ℕ) (B s : ℝ≥0) (selected : LeftHeightLabel n)
    (rest : FiniteSample n) (x : UnitMark)
    (hx : (s : ℝ) < (n : ℝ) * (x : ℝ))
    {u : ℝ≥0} (hus : u ≤ s) :
    ¬ leftRawEventTime n B selected (leftHeightRestore selected rest x) ≤
      (u : WithTop ℝ≥0) := by
  have hx0 : 0 ≤ (n : ℝ) * (x : ℝ) :=
    mul_nonneg (by positivity) x.property.1
  simp only [leftRawEventTime, leftHeightCoordinate_leftHeightRestore, ite_true]
  split_ifs with hxB
  · intro hle
    have hnn := WithTop.coe_le_coe.mp hle
    have hreal : (n : ℝ) * (x : ℝ) ≤ u := by
      have hcoe := NNReal.coe_le_coe.mpr hnn
      rwa [Real.coe_toNNReal _ hx0] at hcoe
    exact (not_lt_of_ge (hreal.trans (by exact_mod_cast hus))) hx
  · exact WithTop.not_top_le_coe u

private theorem leftRawSnapshot_path_eq_restore_of_future
    (n : ℕ) (B s : ℝ≥0) (selected : LeftHeightLabel n)
    (rest : FiniteSample n) (x y : UnitMark)
    (hx : (s : ℝ) < (n : ℝ) * (x : ℝ))
    (hy : (s : ℝ) < (n : ℝ) * (y : ℝ))
    (hgoodx : leftHeightRestore selected rest x ∈ leftHeightGenericEvent n)
    (hgoody : leftHeightRestore selected rest y ∈ leftHeightGenericEvent n) :
    (fun u : Set.Iic s ↦
        leftRawSnapshot n B u.1 (leftHeightRestore selected rest x)) =
      fun u : Set.Iic s ↦
        leftRawSnapshot n B u.1 (leftHeightRestore selected rest y) := by
  funext u
  apply Prod.ext
  · simp [leftRawSnapshot, hgoodx, hgoody]
  · funext label
    by_cases hlabel : label = selected
    · subst label
      have hnotx := leftRawEventTime_restore_self_not_le_of_lt
        n B s selected rest x hx u.2
      have hnoty := leftRawEventTime_restore_self_not_le_of_lt
        n B s selected rest y hy u.2
      simp only [leftRawSnapshot]
      rw [ite_eq_right hnotx, ite_eq_right hnoty]
    · have hcoord :
          leftHeightCoordinate label (leftHeightRestore selected rest x) =
            leftHeightCoordinate label (leftHeightRestore selected rest y) := by
        simp [leftHeightCoordinate_leftHeightRestore, hlabel]
      have hraw :
          leftRawEventTime n B label (leftHeightRestore selected rest x) =
            leftRawEventTime n B label (leftHeightRestore selected rest y) := by
        simp only [leftRawEventTime, hcoord]
      simp only [leftRawSnapshot]
      rw [hraw]

/-- Raw left-history filtration. -/
noncomputable def leftRawFiltration (n : ℕ) (B : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  Filtration.natural (leftRawSnapshot n B)
    (fun t ↦ (measurable_leftRawSnapshot n B t).stronglyMeasurable)

/-- Usual augmentation of the left-history filtration. -/
noncomputable def leftUsualFiltration (n : ℕ) (B : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  usualAugmentation (leftRawFiltration n B)
    (finiteSampleLaw n : Measure (FiniteSample n))

theorem leftRawEvent_mem_iff_restore_of_future
    (n : ℕ) (B s : ℝ≥0) (selected : LeftHeightLabel n)
    (rest : FiniteSample n) (x y : UnitMark)
    (hx : (s : ℝ) < (n : ℝ) * (x : ℝ))
    (hy : (s : ℝ) < (n : ℝ) * (y : ℝ))
    (hgoodx : leftHeightRestore selected rest x ∈ leftHeightGenericEvent n)
    (hgoody : leftHeightRestore selected rest y ∈ leftHeightGenericEvent n)
    (E : Set (FiniteSample n)) (hE : MeasurableSet[leftRawFiltration n B s] E) :
    leftHeightRestore selected rest x ∈ E ↔
      leftHeightRestore selected rest y ∈ E := by
  have hEcomap : MeasurableSet[
      (leftRawFiltration n B s : MeasurableSpace (FiniteSample n))] E := hE
  rw [leftRawFiltration, Filtration.natural_eq_comap] at hEcomap
  obtain ⟨A, hA, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hEcomap
  rw [← hpre]
  change (fun u : Set.Iic s ↦
      leftRawSnapshot n B u.1 (leftHeightRestore selected rest x)) ∈ A ↔
    (fun u : Set.Iic s ↦
      leftRawSnapshot n B u.1 (leftHeightRestore selected rest y)) ∈ A
  rw [leftRawSnapshot_path_eq_restore_of_future n B s selected rest x y
    hx hy hgoodx hgoody]

theorem leftUsualFiltration_isRightContinuous (n : ℕ) (B : ℝ≥0) :
    Filtration.IsRightContinuous (leftUsualFiltration n B) :=
  usualAugmentation_isRightContinuous (leftRawFiltration n B)
    (finiteSampleLaw n : Measure (FiniteSample n))

private theorem leftRawSnapshot_stronglyAdapted
    (n : ℕ) (B : ℝ≥0) :
    StronglyAdapted (leftRawFiltration n B) (leftRawSnapshot n B) :=
  Filtration.stronglyAdapted_natural
    (fun t ↦ (measurable_leftRawSnapshot n B t).stronglyMeasurable)

theorem measurableSet_leftHeightGenericEvent_at
    (n : ℕ) (B t : ℝ≥0) :
    MeasurableSet[leftUsualFiltration n B t] (leftHeightGenericEvent n) := by
  have hsnapshot := leftRawSnapshot_stronglyAdapted n B t
  have hraw : MeasurableSet[leftRawFiltration n B t] (leftHeightGenericEvent n) := by
    rw [show leftHeightGenericEvent n =
        (fun sample ↦ (leftRawSnapshot n B t sample).1) ⁻¹' {true} by
      ext sample
      simp [leftRawSnapshot]]
    exact (measurableSet_singleton true).preimage (measurable_fst.comp hsnapshot.measurable)
  exact (le_usualAugmentation (leftRawFiltration n B)
    (finiteSampleLaw n : Measure (FiniteSample n)) t) _ hraw

theorem leftEventTime_isStoppingTime
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) :
    IsStoppingTime (leftUsualFiltration n B) (leftEventTime n B label) := by
  have hraw : IsStoppingTime (leftRawFiltration n B) (leftEventTime n B label) := by
    intro t
    have hsnapshot := leftRawSnapshot_stronglyAdapted n B t
    let A : Set (Bool × (LeftHeightLabel n → WithTop ℝ≥0)) :=
      {z | z.1 = true ∧ z.2 label ≤ (t : WithTop ℝ≥0)}
    have hA : MeasurableSet A :=
      ((measurableSet_singleton true).preimage measurable_fst).inter
        (measurableSet_le ((measurable_pi_apply label).comp measurable_snd) measurable_const)
    have heq : {sample : FiniteSample n |
          leftEventTime n B label sample ≤ (t : WithTop ℝ≥0)} =
        (fun sample ↦ leftRawSnapshot n B t sample) ⁻¹' A := by
      ext sample
      by_cases hgood : sample ∈ leftHeightGenericEvent n
      · by_cases hle : leftRawEventTime n B label sample ≤ (t : WithTop ℝ≥0)
        · simp only [Set.mem_ofPred_eq, Set.mem_preimage, leftEventTime,
            leftRawSnapshot, A, hgood, decide_true, ite_true, hle, true_and]
        · simp only [Set.mem_ofPred_eq, Set.mem_preimage, leftEventTime,
            leftRawSnapshot, A, hgood, decide_true, ite_true, hle, ite_false, true_and]
          exact iff_of_false (by simp) (WithTop.not_top_le_coe t)
      · simp only [Set.mem_ofPred_eq, Set.mem_preimage, leftEventTime,
          leftRawSnapshot, A, hgood, decide_false, ite_false, Bool.false_eq_true,
          false_and]
        exact iff_of_false (WithTop.not_top_le_coe t) (by simp)
    rw [heq]
    exact hA.preimage hsnapshot.measurable
  intro t
  exact (le_usualAugmentation (leftRawFiltration n B)
    (finiteSampleLaw n : Measure (FiniteSample n)) t) _ (hraw t)

theorem leftEventTime_le_iff_of_good
    {B t : ℝ≥0} {label : LeftHeightLabel n} {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n) (htB : t ≤ B) :
    leftEventTime n B label sample ≤ (t : WithTop ℝ≥0) ↔
      (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t := by
  have hx0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ) :=
    mul_nonneg (by positivity) (leftHeightCoordinate label sample).property.1
  simp only [leftEventTime, hgood, ite_true, leftRawEventTime]
  split_ifs with hxB
  · rw [WithTop.coe_le_coe]
    change Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) ≤ t ↔ _
    constructor
    · intro h
      have h' := NNReal.coe_le_coe.mpr h
      rwa [Real.coe_toNNReal _ hx0] at h'
    · intro h
      apply NNReal.coe_le_coe.mp
      rwa [Real.coe_toNNReal _ hx0]
  · constructor
    · exact fun h ↦ (WithTop.not_top_le_coe t h).elim
    · exact fun h ↦ (hxB (h.trans (by exact_mod_cast htB))).elim

theorem leftEventTime_lt_iff_of_good
    {B t : ℝ≥0} {label : LeftHeightLabel n} {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n) (htB : t ≤ B) :
    leftEventTime n B label sample < (t : WithTop ℝ≥0) ↔
      (n : ℝ) * (leftHeightCoordinate label sample : ℝ) < t := by
  have hx0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ) :=
    mul_nonneg (by positivity) (leftHeightCoordinate label sample).property.1
  simp only [leftEventTime, hgood, ite_true, leftRawEventTime]
  split_ifs with hxB
  · rw [WithTop.coe_lt_coe]
    change Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) < t ↔ _
    constructor
    · intro h
      have h' := NNReal.coe_lt_coe.mpr h
      rwa [Real.coe_toNNReal _ hx0] at h'
    · intro h
      apply NNReal.coe_lt_coe.mp
      rwa [Real.coe_toNNReal _ hx0]
  · constructor
    · exact fun h ↦ (not_lt_of_ge le_top h).elim
    · exact fun h ↦ (hxB (h.le.trans (by exact_mod_cast htB))).elim

private theorem leftEventTime_le_iff_of_good_general
    {B t : ℝ≥0} {label : LeftHeightLabel n} {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n) :
    leftEventTime n B label sample ≤ (t : WithTop ℝ≥0) ↔
      (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ B ∧
        (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t := by
  have hx0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ) :=
    mul_nonneg (by positivity) (leftHeightCoordinate label sample).property.1
  simp only [leftEventTime, hgood, ite_true, leftRawEventTime]
  split_ifs with hxB
  · rw [WithTop.coe_le_coe]
    change Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) ≤ t ↔ _
    rw [show Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) ≤ t ↔
        (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t by
      constructor
      · intro h
        have h' := NNReal.coe_le_coe.mpr h
        rwa [Real.coe_toNNReal _ hx0] at h'
      · intro h
        apply NNReal.coe_le_coe.mp
        rwa [Real.coe_toNNReal _ hx0]]
    exact (and_iff_right hxB).symm
  · constructor
    · exact fun h ↦ (WithTop.not_top_le_coe t h).elim
    · exact fun h ↦ (hxB h.1).elim

private theorem integral_unitUniform_left_future_window
    (hn : 0 < n) {B s t : ℝ≥0} (hst : s ≤ t) (hsB : s < B)
    (hBn : (B : ℝ) < n) (c : ℝ) :
    (∫ x : UnitMark,
      if (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
          (n : ℝ) * (x : ℝ) ≤ t ∧
          (n : ℝ) * (x : ℝ) ≤ B then c else 0
        ∂(unitUniform : Measure UnitMark)) =
      c * ((min (t : ℝ) B - s) / n) := by
  let q : ℝ := min (t : ℝ) B
  let ps : UnitMark := leftBoundaryRankThreshold n s
  let pq : UnitMark := leftBoundaryRankThreshold n q
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsReal : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hsq : (s : ℝ) ≤ q := le_min hsReal hsB.le
  have hq0 : 0 ≤ q := le_trans (by exact_mod_cast s.2) hsq
  have hqn : q ≤ n := (min_le_right _ _).trans hBn.le
  have hps : (ps : ℝ) = (s : ℝ) / n :=
    leftBoundaryRankThreshold_coe_of_mem hn (by exact_mod_cast s.2) (hsq.trans hqn)
  have hpq : (pq : ℝ) = q / n :=
    leftBoundaryRankThreshold_coe_of_mem hn hq0 hqn
  let A : Set UnitMark :=
    {x | (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
      (n : ℝ) * (x : ℝ) ≤ t ∧
      (n : ℝ) * (x : ℝ) ≤ B}
  have hA : A = Ioc ps pq := by
    ext x
    change ((s : ℝ) < (n : ℝ) * (x : ℝ) ∧
      (n : ℝ) * (x : ℝ) ≤ t ∧
      (n : ℝ) * (x : ℝ) ≤ B) ↔ ps < x ∧ x ≤ pq
    change _ ↔ (ps : ℝ) < (x : ℝ) ∧ (x : ℝ) ≤ (pq : ℝ)
    rw [hps, hpq, div_lt_iff₀ hnreal, le_div_iff₀ hnreal]
    constructor
    · rintro ⟨hlow, ht, hB⟩
      exact ⟨by simpa [mul_comm] using hlow,
        by
          rw [le_min_iff]
          exact ⟨by simpa [mul_comm] using ht, by simpa [mul_comm] using hB⟩⟩
    · rintro ⟨hlow, hupp⟩
      have hupp' : (n : ℝ) * (x : ℝ) ≤ q := by simpa [mul_comm] using hupp
      exact ⟨by simpa [mul_comm] using hlow,
        hupp'.trans (min_le_left _ _), hupp'.trans (min_le_right _ _)⟩
  have hfun :
      (fun x : UnitMark ↦
        if (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
            (n : ℝ) * (x : ℝ) ≤ t ∧
            (n : ℝ) * (x : ℝ) ≤ B then c else 0) =
        A.indicator (fun _ ↦ c) := by
    funext x
    by_cases hx : x ∈ A
    · have hx' : (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
          (n : ℝ) * (x : ℝ) ≤ t ∧
          (n : ℝ) * (x : ℝ) ≤ B := hx
      rw [ite_eq_left hx', Set.indicator_of_mem hx]
    · have hx' : ¬ ((s : ℝ) < (n : ℝ) * (x : ℝ) ∧
          (n : ℝ) * (x : ℝ) ≤ t ∧
          (n : ℝ) * (x : ℝ) ≤ B) := hx
      rw [ite_eq_right hx', Set.indicator_of_notMem hx]
  rw [hfun, hA, integral_indicator_const c measurableSet_Ioc]
  change ENNReal.toReal (volume (Ioc ps pq)) * c =
    c * ((min (t : ℝ) B - s) / n)
  rw [unitInterval.volume_Ioc]
  have hdiff : 0 ≤ (pq : ℝ) - (ps : ℝ) := sub_nonneg.mpr (by
    rw [hps, hpq]
    exact div_le_div_of_nonneg_right hsq hnreal.le)
  rw [ENNReal.toReal_ofReal hdiff, hps, hpq]
  change (q / n - (s : ℝ) / n) * c = c * ((q - s) / n)
  field_simp

private theorem integral_unitUniform_left_survival_hazard
    (hn : 0 < n) {B u : ℝ≥0} (huB : u ≤ B) (hBn : (B : ℝ) < n) (c : ℝ) :
    (∫ x : UnitMark,
      if (u : ℝ) ≤ (n : ℝ) * (x : ℝ) then c / ((n : ℝ) - u) else 0
        ∂(unitUniform : Measure UnitMark)) = c / n := by
  let pu : UnitMark := leftBoundaryRankThreshold n u
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have huReal : (u : ℝ) ≤ B := by exact_mod_cast huB
  have hun : (u : ℝ) ≤ n := huReal.trans hBn.le
  have hpu : (pu : ℝ) = (u : ℝ) / n :=
    leftBoundaryRankThreshold_coe_of_mem hn (by exact_mod_cast u.2) hun
  let A : Set UnitMark := {x | (u : ℝ) ≤ (n : ℝ) * (x : ℝ)}
  have hA : A = Icc pu 1 := by
    ext x
    change ((u : ℝ) ≤ (n : ℝ) * (x : ℝ)) ↔ pu ≤ x ∧ x ≤ 1
    change _ ↔ (pu : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (1 : UnitMark)
    rw [hpu, div_le_iff₀ hnreal]
    exact ⟨fun h ↦ ⟨by simpa [mul_comm] using h, x.property.2⟩, fun h ↦ by
      simpa [mul_comm] using h.1⟩
  have hfun :
      (fun x : UnitMark ↦
        if (u : ℝ) ≤ (n : ℝ) * (x : ℝ) then
          c / ((n : ℝ) - u) else 0) =
        A.indicator (fun _ ↦ c / ((n : ℝ) - u)) := by
    funext x
    by_cases hx : x ∈ A
    · have hx' : (u : ℝ) ≤ (n : ℝ) * (x : ℝ) := hx
      rw [ite_eq_left hx', Set.indicator_of_mem hx]
    · have hx' : ¬ ((u : ℝ) ≤ (n : ℝ) * (x : ℝ)) := hx
      rw [ite_eq_right hx', Set.indicator_of_notMem hx]
  rw [hfun, hA, integral_indicator_const _ measurableSet_Icc]
  change ENNReal.toReal (volume (Icc pu 1)) * (c / ((n : ℝ) - u)) = c / n
  rw [unitInterval.volume_Icc]
  have hdiff : 0 ≤ ((1 : UnitMark) : ℝ) - (pu : ℝ) := by
    exact sub_nonneg.mpr pu.property.2
  rw [ENNReal.toReal_ofReal hdiff, hpu]
  have hden : (n : ℝ) - u ≠ 0 := ne_of_gt (sub_pos.mpr (huReal.trans_lt hBn))
  field_simp
  norm_num
  ring

private theorem integral_timeMeasure_left_hazard_window
    {B s t : ℝ≥0} (hst : s ≤ t) (hsB : s < B) (c : ℝ) :
    (∫ u in Ioc s t,
      if u ≤ B then c else 0 ∂CountingProcess.timeMeasure) =
      c * ((min (t : ℝ) B - s)) := by
  let q : ℝ≥0 := min t B
  have hsq : s ≤ q := le_min hst hsB.le
  have hfun :
      (Ioc s t).indicator (fun u : ℝ≥0 ↦ if u ≤ B then c else 0) =
        (Ioc s q).indicator (fun _ ↦ c) := by
    funext u
    by_cases hu : u ∈ Ioc s t
    · by_cases huB : u ≤ B
      · have huq : u ∈ Ioc s q := ⟨hu.1, le_min hu.2 huB⟩
        rw [Set.indicator_of_mem hu, ite_eq_left huB, Set.indicator_of_mem huq]
      · have huq : u ∉ Ioc s q := fun h ↦ huB (h.2.trans (min_le_right _ _))
        rw [Set.indicator_of_mem hu, ite_eq_right huB, Set.indicator_of_notMem huq]
    · have huq : u ∉ Ioc s q := fun h ↦ hu ⟨h.1, h.2.trans (min_le_left _ _)⟩
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem huq]
  rw [← integral_indicator measurableSet_Ioc, hfun, integral_indicator measurableSet_Ioc]
  rw [CountingProcess.integral_timeMeasure_eq_intervalIntegral _ s q hsq,
    intervalIntegral.integral_const]
  change ((q : ℝ) - s) * c = c * ((min (t : ℝ) B - s))
  simp only [q, NNReal.coe_min]
  ring

private theorem left_raw_event_fiber_hazard_integral
    (hn : 0 < n) {B s t : ℝ≥0} (hst : s ≤ t) (hsB : s < B)
    (hBn : (B : ℝ) < n) (selected : LeftHeightLabel n)
    (rest : FiniteSample n) (E : Set (FiniteSample n))
    (hE : MeasurableSet[leftRawFiltration n B s] E) :
    (∫ x : UnitMark,
      if leftHeightRestore selected rest x ∈ leftHeightGenericEvent n ∧
          leftHeightRestore selected rest x ∈ E ∧
          (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
          (n : ℝ) * (x : ℝ) ≤ t ∧
          (n : ℝ) * (x : ℝ) ≤ B then 1 else 0
        ∂(unitUniform : Measure UnitMark)) =
      ∫ x : UnitMark, ∫ u in Ioc s t,
        if leftHeightRestore selected rest x ∈ leftHeightGenericEvent n ∧
            leftHeightRestore selected rest x ∈ E ∧ u ≤ B ∧
            (u : ℝ) ≤ (n : ℝ) * (x : ℝ) then
          1 / ((n : ℝ) - u) else 0
        ∂CountingProcess.timeMeasure ∂(unitUniform : Measure UnitMark) := by
  by_cases hexists : ∃ x : UnitMark,
      leftHeightRestore selected rest x ∈ leftHeightGenericEvent n
  · let bad : Set UnitMark :=
      {x | leftHeightRestore selected rest x ∉ leftHeightGenericEvent n}
    let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
      change NullSingletonClass (volume : Measure UnitMark)
      infer_instance
    have hbad : bad.Finite :=
      finite_bad_leftHeightRestore_fiber_of_exists_good selected rest hexists
    have hbadNull : (unitUniform : Measure UnitMark) bad = 0 := by
      exact hbad.measure_zero (unitUniform : Measure UnitMark)
    have haeGood : ∀ᵐ x ∂(unitUniform : Measure UnitMark), x ∉ bad := by
      rw [ae_iff]
      simpa only [compl_ofPred, not_not, ofPred_mem_eq] using hbadNull
    let ps : UnitMark := leftBoundaryRankThreshold n s
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsBn : (s : ℝ) < n := by
      exact (by exact_mod_cast hsB : (s : ℝ) < B).trans hBn
    have hps : (ps : ℝ) = (s : ℝ) / n :=
      leftBoundaryRankThreshold_coe_of_mem hn (by exact_mod_cast s.2) hsBn.le
    have hps1 : ps < (1 : UnitMark) := by
      change (ps : ℝ) < ((1 : UnitMark) : ℝ)
      rw [hps]
      norm_num
      exact (div_lt_one hnreal).mpr hsBn
    have hnotSubset : ¬ Ioc ps (1 : UnitMark) ⊆ bad := by
      intro hsub
      exact (Set.Ioc_infinite hps1) (hbad.subset hsub)
    rw [Set.not_subset] at hnotSubset
    obtain ⟨y, hyFuture, hyGood⟩ := hnotSubset
    have hgoody : leftHeightRestore selected rest y ∈ leftHeightGenericEvent n := by
      simpa only [bad, mem_ofPred_eq, not_not] using hyGood
    have hyPhysical : (s : ℝ) < (n : ℝ) * (y : ℝ) := by
      have hy := hyFuture.1
      change (ps : ℝ) < (y : ℝ) at hy
      rw [hps, div_lt_iff₀ hnreal] at hy
      simpa only [mul_comm] using hy
    let c : ℝ := if leftHeightRestore selected rest y ∈ E then 1 else 0
    have hmemConstant : ∀ x : UnitMark,
        leftHeightRestore selected rest x ∈ leftHeightGenericEvent n →
        (s : ℝ) < (n : ℝ) * (x : ℝ) →
        (leftHeightRestore selected rest x ∈ E ↔ c = 1) := by
      intro x hgoodx hx
      have hiff := leftRawEvent_mem_iff_restore_of_future
        n B s selected rest x y hx hyPhysical hgoodx hgoody E hE
      change (leftHeightRestore selected rest x ∈ E ↔
        (if leftHeightRestore selected rest y ∈ E then (1 : ℝ) else 0) = 1)
      rw [hiff]
      by_cases hyE : leftHeightRestore selected rest y ∈ E
      · simp [hyE]
      · simp [hyE]
    have hleftAE :
        (fun x : UnitMark ↦
          if leftHeightRestore selected rest x ∈ leftHeightGenericEvent n ∧
              leftHeightRestore selected rest x ∈ E ∧
              (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
              (n : ℝ) * (x : ℝ) ≤ t ∧
              (n : ℝ) * (x : ℝ) ≤ B then 1 else 0) =ᵐ[
            (unitUniform : Measure UnitMark)]
          fun x ↦ if (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
              (n : ℝ) * (x : ℝ) ≤ t ∧
              (n : ℝ) * (x : ℝ) ≤ B then c else 0 := by
      filter_upwards [haeGood] with x hxGood
      have hgoodx : leftHeightRestore selected rest x ∈ leftHeightGenericEvent n := by
        simpa only [bad, mem_ofPred_eq, not_not] using hxGood
      by_cases hwindow : (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
          (n : ℝ) * (x : ℝ) ≤ t ∧
          (n : ℝ) * (x : ℝ) ≤ B
      · have hmem := hmemConstant x hgoodx hwindow.1
        by_cases hxE : leftHeightRestore selected rest x ∈ E
        · have hc : c = 1 := hmem.mp hxE
          simp [hgoodx, hxE, hwindow, hc]
        · have hc : c ≠ 1 := fun hc ↦ hxE (hmem.mpr hc)
          have hc0 : c = 0 := by
            by_cases hyE : leftHeightRestore selected rest y ∈ E
            · exact (hc (by simp [c, hyE])).elim
            · simp [c, hyE]
          simp [hgoodx, hxE, hwindow, hc0]
      · simp [hwindow]
    have hleft :
        (∫ x : UnitMark,
          if leftHeightRestore selected rest x ∈ leftHeightGenericEvent n ∧
              leftHeightRestore selected rest x ∈ E ∧
              (s : ℝ) < (n : ℝ) * (x : ℝ) ∧
              (n : ℝ) * (x : ℝ) ≤ t ∧
              (n : ℝ) * (x : ℝ) ≤ B then 1 else 0
            ∂(unitUniform : Measure UnitMark)) =
          c * ((min (t : ℝ) B - s) / n) := by
      rw [integral_congr_ae hleftAE]
      exact integral_unitUniform_left_future_window hn hst hsB hBn c
    let R : UnitMark × ℝ≥0 → ℝ := fun z ↦
      if leftHeightRestore selected rest z.1 ∈ leftHeightGenericEvent n ∧
          leftHeightRestore selected rest z.1 ∈ E ∧ z.2 ≤ B ∧
          (z.2 : ℝ) ≤ (n : ℝ) * (z.1 : ℝ) then
        1 / ((n : ℝ) - z.2) else 0
    have hEambient : MeasurableSet E :=
      (leftRawFiltration n B).le s E hE
    have hrestore : Measurable (fun z : UnitMark × ℝ≥0 ↦
        leftHeightRestore selected rest z.1) :=
      (measurable_leftHeightRestore selected).comp (measurable_const.prodMk measurable_fst)
    have hRmeas : Measurable R := by
      apply Measurable.ite
      · have hcond := ((measurableSet_leftHeightGenericEvent n).preimage hrestore |>.inter
            (hEambient.preimage hrestore) |>.inter
            (measurableSet_le measurable_snd
              (measurable_const : Measurable fun _ : UnitMark × ℝ≥0 ↦ B))) |>.inter
            (measurableSet_le measurable_snd.subtype_coe
              ((measurable_const : Measurable fun _ : UnitMark × ℝ≥0 ↦ (n : ℝ)).mul
                measurable_fst.subtype_coe))
        rw [show {z : UnitMark × ℝ≥0 |
            leftHeightRestore selected rest z.1 ∈ leftHeightGenericEvent n ∧
              leftHeightRestore selected rest z.1 ∈ E ∧ z.2 ≤ B ∧
              (z.2 : ℝ) ≤ (n : ℝ) * (z.1 : ℝ)} =
            ((fun z ↦ leftHeightRestore selected rest z.1) ⁻¹' leftHeightGenericEvent n ∩
              (fun z ↦ leftHeightRestore selected rest z.1) ⁻¹' E) ∩
              {z | z.2 ≤ B} ∩ {z | (z.2 : ℝ) ≤ (n : ℝ) * (z.1 : ℝ)} by
          ext z
          simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
          tauto]
        exact hcond
      · exact measurable_const.div (measurable_const.sub measurable_snd.subtype_coe)
      · exact measurable_const
    let _ : SFinite CountingProcess.timeMeasure := by
      unfold CountingProcess.timeMeasure
      infer_instance
    let _ : IsFiniteMeasure (CountingProcess.timeMeasure.restrict (Ioc s t)) :=
      IsFiniteMeasure.mk (by
        rw [Measure.restrict_apply_univ]
        exact CountingProcess.timeMeasure_Ioc_lt_top s t)
    have hRint : Integrable R
        ((unitUniform : Measure UnitMark).prod
          (CountingProcess.timeMeasure.restrict (Ioc s t))) := by
      have hfloor : 0 < (n : ℝ) - B := sub_pos.mpr hBn
      refine Integrable.of_bound hRmeas.aestronglyMeasurable (1 / ((n : ℝ) - B)) ?_
      filter_upwards [] with z
      by_cases hz : leftHeightRestore selected rest z.1 ∈ leftHeightGenericEvent n ∧
          leftHeightRestore selected rest z.1 ∈ E ∧ z.2 ≤ B ∧
          (z.2 : ℝ) ≤ (n : ℝ) * (z.1 : ℝ)
      · have hden : 0 < (n : ℝ) - z.2 :=
          sub_pos.mpr ((by exact_mod_cast hz.2.2.1 : (z.2 : ℝ) ≤ B).trans_lt hBn)
        rw [show R z = 1 / ((n : ℝ) - z.2) by simp [R, hz]]
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden)]
        exact one_div_le_one_div_of_le hfloor (sub_le_sub_left (by
          exact_mod_cast hz.2.2.1) _)
      · simp [R, hz, hfloor.le]
    have hinner : ∀ u ∈ Ioc s t,
        (∫ x : UnitMark, R (x, u) ∂(unitUniform : Measure UnitMark)) =
          if u ≤ B then c / n else 0 := by
      intro u hu
      by_cases huB : u ≤ B
      · have hAE : (fun x : UnitMark ↦ R (x, u)) =ᵐ[
            (unitUniform : Measure UnitMark)]
            fun x ↦ if (u : ℝ) ≤ (n : ℝ) * (x : ℝ) then
              c / ((n : ℝ) - u) else 0 := by
          filter_upwards [haeGood] with x hxGood
          have hgoodx : leftHeightRestore selected rest x ∈ leftHeightGenericEvent n := by
            simpa only [bad, mem_ofPred_eq, not_not] using hxGood
          by_cases hsurvive : (u : ℝ) ≤ (n : ℝ) * (x : ℝ)
          · have hxFuture : (s : ℝ) < (n : ℝ) * (x : ℝ) :=
              (show (s : ℝ) < (u : ℝ) by exact_mod_cast hu.1).trans_le hsurvive
            have hmem := hmemConstant x hgoodx hxFuture
            by_cases hxE : leftHeightRestore selected rest x ∈ E
            · have hc : c = 1 := hmem.mp hxE
              simp [R, hgoodx, hxE, huB, hsurvive, hc]
            · have hc0 : c = 0 := by
                simp only [c]
                split_ifs with hyE
                · exact (hxE (hmem.mpr (by simp [c, hyE]))).elim
                · rfl
              simp [R, hgoodx, hxE, huB, hsurvive, hc0]
          · simp [R, hsurvive]
        rw [integral_congr_ae hAE,
          integral_unitUniform_left_survival_hazard hn huB hBn c, ite_eq_left huB]
      · have hzero : ∀ x : UnitMark, R (x, u) = 0 := by
          intro x
          simp [R, huB]
        simp [hzero, huB]
    have hright :
        (∫ x : UnitMark, ∫ u in Ioc s t, R (x, u)
            ∂CountingProcess.timeMeasure ∂(unitUniform : Measure UnitMark)) =
          c * ((min (t : ℝ) B - s) / n) := by
      calc
        (∫ x : UnitMark, ∫ u in Ioc s t, R (x, u)
            ∂CountingProcess.timeMeasure ∂(unitUniform : Measure UnitMark)) =
            ∫ z, R z ∂((unitUniform : Measure UnitMark).prod
              (CountingProcess.timeMeasure.restrict (Ioc s t))) := by
              exact (integral_prod R hRint).symm
        _ = ∫ u in Ioc s t, ∫ x : UnitMark, R (x, u)
              ∂(unitUniform : Measure UnitMark) ∂CountingProcess.timeMeasure := by
              exact integral_prod_symm R hRint
        _ = ∫ u in Ioc s t, if u ≤ B then c / n else 0
              ∂CountingProcess.timeMeasure := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro u hu
              exact hinner u hu
        _ = (c / n) * (min (t : ℝ) B - s) :=
          integral_timeMeasure_left_hazard_window hst hsB (c / n)
        _ = c * ((min (t : ℝ) B - s) / n) := by field_simp
    rw [hleft, hright]
  · have hnone : ∀ x : UnitMark,
        leftHeightRestore selected rest x ∉ leftHeightGenericEvent n := by
      simpa only [not_exists] using hexists
    simp_rw [hnone]
    simp

private theorem left_raw_event_label_hazard_integral
    (hn : 0 < n) {B s t : ℝ≥0} (hst : s ≤ t) (hsB : s < B)
    (hBn : (B : ℝ) < n) (selected : LeftHeightLabel n)
    (E : Set (FiniteSample n)) (hE : MeasurableSet[leftRawFiltration n B s] E) :
    (∫ sample : FiniteSample n,
      if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧
          (s : ℝ) < (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ∧
          (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ≤ t ∧
          (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ≤ B then 1 else 0
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ∫ sample : FiniteSample n, ∫ u in Ioc s t,
        if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧ u ≤ B ∧
            (u : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) then
          1 / ((n : ℝ) - u) else 0
        ∂CountingProcess.timeMeasure ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  let p := leftHeightCoordinateIndex selected
  let X : FiniteSample n → FiniteSample n := coordinateLeaveOneOut p
  let Y : FiniteSample n → UnitMark := coordinate p
  let μ := (finiteSampleLaw n : Measure (FiniteSample n))
  let ν := Measure.map X μ
  let ρ := (unitUniform : Measure UnitMark)
  let P := ν.prod ρ
  let L : FiniteSample n × UnitMark → ℝ := fun z ↦
    if leftHeightRestore selected z.1 z.2 ∈ leftHeightGenericEvent n ∧
        leftHeightRestore selected z.1 z.2 ∈ E ∧
        (s : ℝ) < (n : ℝ) * (z.2 : ℝ) ∧
        (n : ℝ) * (z.2 : ℝ) ≤ t ∧
        (n : ℝ) * (z.2 : ℝ) ≤ B then 1 else 0
  let J : (FiniteSample n × UnitMark) × ℝ≥0 → ℝ := fun z ↦
    if leftHeightRestore selected z.1.1 z.1.2 ∈ leftHeightGenericEvent n ∧
        leftHeightRestore selected z.1.1 z.1.2 ∈ E ∧ z.2 ≤ B ∧
        (z.2 : ℝ) ≤ (n : ℝ) * (z.1.2 : ℝ) then
      1 / ((n : ℝ) - z.2) else 0
  let G : FiniteSample n × UnitMark → ℝ := fun z ↦
    ∫ u in Ioc s t, J (z, u) ∂CountingProcess.timeMeasure
  have hEambient : MeasurableSet E := (leftRawFiltration n B).le s E hE
  have hrestore : Measurable (fun z : FiniteSample n × UnitMark ↦
      leftHeightRestore selected z.1 z.2) := measurable_leftHeightRestore selected
  have hLmeas : Measurable L := by
    apply Measurable.ite
    · have hcond := (((measurableSet_leftHeightGenericEvent n).preimage hrestore).inter
      (hEambient.preimage hrestore)).inter
          ((measurableSet_lt
            (measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (s : ℝ))
            ((measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (n : ℝ)).mul
              measurable_snd.subtype_coe)).inter
            ((measurableSet_le
              ((measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (n : ℝ)).mul
                measurable_snd.subtype_coe)
              (measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (t : ℝ))).inter
              (measurableSet_le
                ((measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (n : ℝ)).mul
                  measurable_snd.subtype_coe)
                (measurable_const : Measurable fun _ : FiniteSample n × UnitMark ↦ (B : ℝ)))))
      rw [show {z : FiniteSample n × UnitMark |
          leftHeightRestore selected z.1 z.2 ∈ leftHeightGenericEvent n ∧
            leftHeightRestore selected z.1 z.2 ∈ E ∧
            (s : ℝ) < (n : ℝ) * (z.2 : ℝ) ∧
            (n : ℝ) * (z.2 : ℝ) ≤ t ∧
            (n : ℝ) * (z.2 : ℝ) ≤ B} =
          ((fun z ↦ leftHeightRestore selected z.1 z.2) ⁻¹' leftHeightGenericEvent n ∩
            (fun z ↦ leftHeightRestore selected z.1 z.2) ⁻¹' E) ∩
            ({z | (s : ℝ) < (n : ℝ) * (z.2 : ℝ)} ∩
              ({z | (n : ℝ) * (z.2 : ℝ) ≤ t} ∩
                {z | (n : ℝ) * (z.2 : ℝ) ≤ B})) by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
        tauto]
      exact hcond
    · exact measurable_const
    · exact measurable_const
  have hL : Integrable L P := by
    refine Integrable.of_bound hLmeas.aestronglyMeasurable 1 ?_
    filter_upwards [] with z
    simp only [L]
    split_ifs <;> norm_num
  have hJmeas : Measurable J := by
    have hrestore' : Measurable (fun z : (FiniteSample n × UnitMark) × ℝ≥0 ↦
        leftHeightRestore selected z.1.1 z.1.2) :=
      hrestore.comp measurable_fst
    apply Measurable.ite
    · have hcond := (((measurableSet_leftHeightGenericEvent n).preimage hrestore').inter
          (hEambient.preimage hrestore')).inter
          ((measurableSet_le measurable_snd
            (measurable_const : Measurable fun _ : (FiniteSample n × UnitMark) × ℝ≥0 ↦ B)).inter
            (measurableSet_le measurable_snd.subtype_coe
              ((measurable_const : Measurable fun _ : (FiniteSample n × UnitMark) × ℝ≥0 ↦
                  (n : ℝ)).mul (measurable_snd.comp measurable_fst).subtype_coe)))
      rw [show {z : (FiniteSample n × UnitMark) × ℝ≥0 |
          leftHeightRestore selected z.1.1 z.1.2 ∈ leftHeightGenericEvent n ∧
            leftHeightRestore selected z.1.1 z.1.2 ∈ E ∧ z.2 ≤ B ∧
            (z.2 : ℝ) ≤ (n : ℝ) * (z.1.2 : ℝ)} =
          ((fun z ↦ leftHeightRestore selected z.1.1 z.1.2) ⁻¹' leftHeightGenericEvent n ∩
            (fun z ↦ leftHeightRestore selected z.1.1 z.1.2) ⁻¹' E) ∩
            ({z | z.2 ≤ B} ∩ {z | (z.2 : ℝ) ≤ (n : ℝ) * (z.1.2 : ℝ)}) by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
        tauto]
      exact hcond
    · exact measurable_const.div (measurable_const.sub measurable_snd.subtype_coe)
    · exact measurable_const
  let _ : SFinite CountingProcess.timeMeasure := by
    unfold CountingProcess.timeMeasure
    infer_instance
  let τ := CountingProcess.timeMeasure.restrict (Ioc s t)
  let _ : IsFiniteMeasure τ := IsFiniteMeasure.mk (by
    rw [Measure.restrict_apply_univ]
    exact CountingProcess.timeMeasure_Ioc_lt_top s t)
  have hJ : Integrable J (P.prod τ) := by
    have hfloor : 0 < (n : ℝ) - B := sub_pos.mpr hBn
    refine Integrable.of_bound hJmeas.aestronglyMeasurable (1 / ((n : ℝ) - B)) ?_
    filter_upwards [] with z
    by_cases hz : leftHeightRestore selected z.1.1 z.1.2 ∈ leftHeightGenericEvent n ∧
        leftHeightRestore selected z.1.1 z.1.2 ∈ E ∧ z.2 ≤ B ∧
        (z.2 : ℝ) ≤ (n : ℝ) * (z.1.2 : ℝ)
    · have hden : 0 < (n : ℝ) - z.2 :=
        sub_pos.mpr ((by exact_mod_cast hz.2.2.1 : (z.2 : ℝ) ≤ B).trans_lt hBn)
      rw [show J z = 1 / ((n : ℝ) - z.2) by simp [J, hz]]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden)]
      exact one_div_le_one_div_of_le hfloor (sub_le_sub_left (by
        exact_mod_cast hz.2.2.1) _)
    · simp [J, hz, hfloor.le]
  have hG : Integrable G P := by
    simpa only [G, τ] using hJ.integral_prod_left
  have hXm : Measurable X := measurable_coordinateLeaveOneOut p
  have hYm : Measurable Y := measurable_coordinate p
  have hXY : IndepFun X Y μ := coordinateLeaveOneOut_indepFun_coordinate p
  have hYlaw : Measure.map Y μ = ρ := by
    change Measure.map (coordinate p) (finiteSampleLaw n : Measure (FiniteSample n)) =
      (unitUniform : Measure UnitMark)
    exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p)
  have hLmap : Integrable L ((Measure.map X μ).prod (Measure.map Y μ)) := by
    rw [hYlaw]
    simpa only [P, ν, ρ] using hL
  have hGmap : Integrable G ((Measure.map X μ).prod (Measure.map Y μ)) := by
    rw [hYlaw]
    simpa only [P, ν, ρ] using hG
  have hLtransport := Probability.integral_indepFun_pair_eq_integral_prod
    hXm hYm hXY hLmap
  have hGtransport := Probability.integral_indepFun_pair_eq_integral_prod
    hXm hYm hXY hGmap
  rw [hYlaw] at hLtransport hGtransport
  have hpair : ∀ sample : FiniteSample n,
      leftHeightRestore selected (X sample) (Y sample) = sample := by
    intro sample
    simpa only [X, Y, p, coordinate_leftHeightCoordinateIndex] using
      leftHeightRestore_coordinateLeaveOneOut selected sample
  have hfiber : ∀ rest : FiniteSample n,
      (∫ x : UnitMark, L (rest, x) ∂ρ) = ∫ x : UnitMark, G (rest, x) ∂ρ := by
    intro rest
    simpa only [L, G, J, ρ] using
      left_raw_event_fiber_hazard_integral hn hst hsB hBn selected rest E hE
  calc
    (∫ sample : FiniteSample n,
      if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧
          (s : ℝ) < (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ∧
          (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ≤ t ∧
          (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) ≤ B then 1 else 0 ∂μ) =
        ∫ sample, L (X sample, Y sample) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with sample
          change _ = if
            leftHeightRestore selected (X sample) (Y sample) ∈ leftHeightGenericEvent n ∧
              leftHeightRestore selected (X sample) (Y sample) ∈ E ∧
              (s : ℝ) < (n : ℝ) * (Y sample : ℝ) ∧
              (n : ℝ) * (Y sample : ℝ) ≤ t ∧
              (n : ℝ) * (Y sample : ℝ) ≤ B then 1 else 0
          rw [hpair sample]
          simp only [Y, p, coordinate_leftHeightCoordinateIndex]

    _ = ∫ z, L z ∂P := by simpa only [P, ν] using hLtransport
    _ = ∫ rest, ∫ x, L (rest, x) ∂ρ ∂ν := integral_prod L hL
    _ = ∫ rest, ∫ x, G (rest, x) ∂ρ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with rest
      exact hfiber rest
    _ = ∫ z, G z ∂P := (integral_prod G hG).symm
    _ = ∫ sample, G (X sample, Y sample) ∂μ := by
      simpa only [P, ν] using hGtransport.symm
    _ = ∫ sample : FiniteSample n, ∫ u in Ioc s t,
        if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧ u ≤ B ∧
            (u : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate selected sample : ℝ) then
          1 / ((n : ℝ) - u) else 0
        ∂CountingProcess.timeMeasure ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with sample
          simp only [G, J]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          change (if
            leftHeightRestore selected (X sample) (Y sample) ∈ leftHeightGenericEvent n ∧
              leftHeightRestore selected (X sample) (Y sample) ∈ E ∧ u ≤ B ∧
              (u : ℝ) ≤ (n : ℝ) * (Y sample : ℝ) then
                1 / ((n : ℝ) - u) else 0) = _
          rw [hpair sample]
          simp only [Y, p, coordinate_leftHeightCoordinateIndex]

private noncomputable def leftRawWindowLabel
    (n : ℕ) (B s t : ℝ≥0) (E : Set (FiniteSample n))
    (label : LeftHeightLabel n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧
      (s : ℝ) < (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ∧
      (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t ∧
      (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ B then 1 else 0

private noncomputable def leftRawHazardLabel
    (n : ℕ) (B u : ℝ≥0) (E : Set (FiniteSample n))
    (label : LeftHeightLabel n) (sample : FiniteSample n) : ℝ :=
  if sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧ u ≤ B ∧
      (u : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ) then
    1 / ((n : ℝ) - u) else 0

private theorem measurable_leftRawWindowLabel
    {B s t : ℝ≥0} {E : Set (FiniteSample n)} (hE : MeasurableSet E)
    (label : LeftHeightLabel n) :
    Measurable (leftRawWindowLabel n B s t E label) := by
  apply Measurable.ite
  · have hcoord : Measurable fun sample : FiniteSample n ↦
        (n : ℝ) * (leftHeightCoordinate label sample : ℝ) :=
      measurable_const.mul (measurable_leftHeightCoordinate label).subtype_coe
    have hcond := (((measurableSet_leftHeightGenericEvent n).inter hE).inter
      (measurableSet_lt
        (measurable_const : Measurable fun _ : FiniteSample n ↦ (s : ℝ)) hcoord)).inter
      ((measurableSet_le hcoord
        (measurable_const : Measurable fun _ : FiniteSample n ↦ (t : ℝ))).inter
        (measurableSet_le hcoord
          (measurable_const : Measurable fun _ : FiniteSample n ↦ (B : ℝ))))
    rw [show {sample : FiniteSample n |
        sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧
          (s : ℝ) < (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ∧
          (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t ∧
          (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ B} =
        ((leftHeightGenericEvent n ∩ E) ∩
          {sample | (s : ℝ) < (n : ℝ) * (leftHeightCoordinate label sample : ℝ)}) ∩
          ({sample | (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ t} ∩
            {sample | (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ B}) by
      ext sample
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto]
    exact hcond
  · exact measurable_const
  · exact measurable_const

private theorem integrable_leftRawWindowLabel
    {B s t : ℝ≥0} {E : Set (FiniteSample n)} (hE : MeasurableSet E)
    (label : LeftHeightLabel n) :
    Integrable (leftRawWindowLabel n B s t E label)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  refine Integrable.of_bound
    (measurable_leftRawWindowLabel hE label).aestronglyMeasurable 1 ?_
  filter_upwards [] with sample
  simp only [leftRawWindowLabel]
  split_ifs <;> norm_num

private theorem measurable_leftRawHazardLabel_uncurry
    {B : ℝ≥0} {E : Set (FiniteSample n)} (hE : MeasurableSet E)
    (label : LeftHeightLabel n) :
    Measurable (fun z : FiniteSample n × ℝ≥0 ↦
      leftRawHazardLabel n B z.2 E label z.1) := by
  apply Measurable.ite
  · have hcoord : Measurable fun z : FiniteSample n × ℝ≥0 ↦
        (n : ℝ) * (leftHeightCoordinate label z.1 : ℝ) :=
      measurable_const.mul
        ((measurable_leftHeightCoordinate label).comp measurable_fst).subtype_coe
    have hrest : MeasurableSet
        ((Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n) ⁻¹'
          leftHeightGenericEvent n ∩
          (Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n) ⁻¹' E) :=
      ((measurableSet_leftHeightGenericEvent n).preimage
        (measurable_fst : Measurable (Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n))).inter
      (hE.preimage
        (measurable_fst : Measurable (Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n)))
    have huBset := measurableSet_le measurable_snd
      (measurable_const : Measurable fun _ : FiniteSample n × ℝ≥0 ↦ B)
    have hsurvive := measurableSet_le measurable_snd.subtype_coe hcoord
    have hcond := (hrest.inter huBset).inter hsurvive
    rw [show {z : FiniteSample n × ℝ≥0 |
        z.1 ∈ leftHeightGenericEvent n ∧ z.1 ∈ E ∧ z.2 ≤ B ∧
          (z.2 : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate label z.1 : ℝ)} =
        (((Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n) ⁻¹'
            leftHeightGenericEvent n ∩
          (Prod.fst : FiniteSample n × ℝ≥0 → FiniteSample n) ⁻¹' E) ∩
          {z | z.2 ≤ B}) ∩
          {z | (z.2 : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate label z.1 : ℝ)} by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      tauto]
    exact hcond
  · exact measurable_const.div (measurable_const.sub measurable_snd.subtype_coe)
  · exact measurable_const

private theorem integrableOn_leftRawHazardLabel
    {B s t : ℝ≥0} (hBn : (B : ℝ) < n) {E : Set (FiniteSample n)}
    (hE : MeasurableSet E) (label : LeftHeightLabel n) (sample : FiniteSample n) :
    IntegrableOn (fun u ↦ leftRawHazardLabel n B u E label sample)
      (Ioc s t) CountingProcess.timeMeasure := by
  have hfloor : 0 < (n : ℝ) - B := sub_pos.mpr hBn
  refine IntegrableOn.of_bound (CountingProcess.timeMeasure_Ioc_lt_top s t)
    ((measurable_leftRawHazardLabel_uncurry hE label).comp
      (measurable_prodMk_left : Measurable fun u : ℝ≥0 ↦ (sample, u))).aestronglyMeasurable
    (1 / ((n : ℝ) - B)) ?_
  filter_upwards [] with u
  by_cases hcond : sample ∈ leftHeightGenericEvent n ∧ sample ∈ E ∧ u ≤ B ∧
      (u : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ)
  · have hden : 0 < (n : ℝ) - u :=
      sub_pos.mpr ((by exact_mod_cast hcond.2.2.1 : (u : ℝ) ≤ B).trans_lt hBn)
    rw [show leftRawHazardLabel n B u E label sample = 1 / ((n : ℝ) - u) by
      simp [leftRawHazardLabel, hcond]]
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden)]
    exact one_div_le_one_div_of_le hfloor (sub_le_sub_left (by
      exact_mod_cast hcond.2.2.1) _)
  · simp [leftRawHazardLabel, hcond, hfloor.le]

private theorem integrable_integral_leftRawHazardLabel
    {B s t : ℝ≥0} (hBn : (B : ℝ) < n) {E : Set (FiniteSample n)}
    (hE : MeasurableSet E) (label : LeftHeightLabel n) :
    Integrable (fun sample : FiniteSample n ↦
      ∫ u in Ioc s t, leftRawHazardLabel n B u E label sample
        ∂CountingProcess.timeMeasure)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let _ : SFinite CountingProcess.timeMeasure := by
    unfold CountingProcess.timeMeasure
    infer_instance
  let τ := CountingProcess.timeMeasure.restrict (Ioc s t)
  let _ : IsFiniteMeasure τ := IsFiniteMeasure.mk (by
    rw [Measure.restrict_apply_univ]
    exact CountingProcess.timeMeasure_Ioc_lt_top s t)
  let H : FiniteSample n × ℝ≥0 → ℝ := fun z ↦
    leftRawHazardLabel n B z.2 E label z.1
  have hHmeas : Measurable H := by
    simpa only [H] using measurable_leftRawHazardLabel_uncurry hE label
  have hH : Integrable H
      ((finiteSampleLaw n : Measure (FiniteSample n)).prod τ) := by
    have hfloor : 0 < (n : ℝ) - B := sub_pos.mpr hBn
    refine Integrable.of_bound hHmeas.aestronglyMeasurable (1 / ((n : ℝ) - B)) ?_
    filter_upwards [] with z
    by_cases hcond : z.1 ∈ leftHeightGenericEvent n ∧ z.1 ∈ E ∧ z.2 ≤ B ∧
        (z.2 : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate label z.1 : ℝ)
    · have hden : 0 < (n : ℝ) - z.2 :=
        sub_pos.mpr ((by exact_mod_cast hcond.2.2.1 : (z.2 : ℝ) ≤ B).trans_lt hBn)
      rw [show H z = 1 / ((n : ℝ) - z.2) by simp [H, leftRawHazardLabel, hcond]]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hden)]
      exact one_div_le_one_div_of_le hfloor (sub_le_sub_left (by
        exact_mod_cast hcond.2.2.1) _)
    · simp [H, leftRawHazardLabel, hcond, hfloor.le]
  simpa only [H, τ] using hH.integral_prod_left

/-! ## Counts and predictable rates -/

/-- Safe finite left count for a colored label family. -/
noncomputable def leftColorCount
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop
    (fun i : Fin n ↦ leftEventTime n B (color, i)) t

noncomputable def leftSourceCountingProcess
    (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) : FiniteSample n → ℕ :=
  leftColorCount n B 0 t

noncomputable def leftTargetCountingProcess
    (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) : FiniteSample n → ℕ :=
  leftColorCount n B 1 t

private theorem leftColorCount_sub_eq_sum_physical_window
    {B s t : ℝ≥0} (hst : s ≤ t) (hsB : s < B)
    (color : Fin 2) (sample : FiniteSample n) :
    ((leftColorCount n B color t sample : ℝ) -
        leftColorCount n B color s sample) =
      ∑ i : Fin n,
        if sample ∈ leftHeightGenericEvent n ∧
            (s : ℝ) < (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ t ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ B then
          1 else 0 := by
  classical
  rw [leftColorCount, CountingProcess.finiteEventCountTop_cast_eq_sum,
    leftColorCount, CountingProcess.finiteEventCountTop_cast_eq_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · simp only [leftEventTime_le_iff_of_good_general hgood]
    by_cases hwindow : (s : ℝ) <
        (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ∧
        (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ t ∧
        (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ B
    · have hnotS : ¬((n : ℝ) *
          (leftHeightCoordinate (color, i) sample : ℝ) ≤ s) := not_le.mpr hwindow.1
      simp [hgood, hwindow, hnotS]
    · by_cases hleS : (n : ℝ) *
          (leftHeightCoordinate (color, i) sample : ℝ) ≤ s
      · have hleB : (n : ℝ) *
            (leftHeightCoordinate (color, i) sample : ℝ) ≤ B :=
          hleS.trans (by exact_mod_cast hsB.le)
        have hleT : (n : ℝ) *
            (leftHeightCoordinate (color, i) sample : ℝ) ≤ t :=
          hleS.trans (by exact_mod_cast hst)
        simp [hgood, hleS, hleB, hleT]
      · have hnotFuture : ¬((n : ℝ) *
              (leftHeightCoordinate (color, i) sample : ℝ) ≤ t ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ B) := by
          intro h
          exact hwindow ⟨lt_of_not_ge hleS, h.1, h.2⟩
        have hnotTOfB : (n : ℝ) *
              (leftHeightCoordinate (color, i) sample : ℝ) ≤ B →
            ¬((n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ t) :=
          fun hleB hleT ↦ hnotFuture ⟨hleT, hleB⟩
        have hleft : ¬((n : ℝ) *
              (leftHeightCoordinate (color, i) sample : ℝ) ≤ B ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ t) :=
          fun h ↦ hnotTOfB h.1 h.2
        have hleftS : ¬((n : ℝ) *
              (leftHeightCoordinate (color, i) sample : ℝ) ≤ B ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ s) :=
          fun h ↦ hleS h.2
        have hright : ¬(sample ∈ leftHeightGenericEvent n ∧
            (s : ℝ) < (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ t ∧
            (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) ≤ B) :=
          fun h ↦ hwindow h.2
        rw [ite_eq_right hleft, ite_eq_right hleftS, ite_eq_right hright]
        norm_num
  · have htTop : ¬(⊤ ≤ (t : WithTop ℝ≥0)) := WithTop.not_top_le_coe t
    have hsTop : ¬(⊤ ≤ (s : WithTop ℝ≥0)) := WithTop.not_top_le_coe s
    simp only [leftEventTime, hgood, ite_false]
    rw [ite_eq_right htTop, ite_eq_right hsTop]
    norm_num

private theorem leftColorCount_eq_of_boundary_le
    {B s t : ℝ≥0} (hBs : B ≤ s) (hst : s ≤ t)
    (color : Fin 2) (sample : FiniteSample n) :
    leftColorCount n B color t sample = leftColorCount n B color s sample := by
  classical
  unfold leftColorCount CountingProcess.finiteEventCountTop
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · simp only [leftEventTime_le_iff_of_good_general hgood]
    constructor
    · intro h
      exact ⟨h.1, h.1.trans (by exact_mod_cast hBs)⟩
    · intro h
      exact ⟨h.1, h.2.trans (by exact_mod_cast hst)⟩
  · have htTop : ¬(⊤ ≤ (t : WithTop ℝ≥0)) := WithTop.not_top_le_coe t
    have hsTop : ¬(⊤ ≤ (s : WithTop ℝ≥0)) := WithTop.not_top_le_coe s
    simp only [leftEventTime, hgood, ite_false]
    exact iff_of_false htTop hsTop

theorem leftSourceCountingProcess_eq_leftSourceCountAt_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    leftSourceCountingProcess n B t sample =
      sample.leftSourceCountAt (leftBoundaryRankThreshold n t) := by
  classical
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htBreal : (t : ℝ) ≤ B := by exact_mod_cast htB
  have htn : (t : ℝ) ≤ n := htBreal.trans hBn
  have hthreshold : ((leftBoundaryRankThreshold n t : UnitMark) : ℝ) = t / n :=
    leftBoundaryRankThreshold_coe_of_mem hn t.2 htn
  unfold leftSourceCountingProcess leftColorCount CountingProcess.finiteEventCountTop
  rw [show Finset.univ.filter
      (fun i : Fin n ↦ leftEventTime n B (0, i) sample ≤ (t : WithTop ℝ≥0)) =
      Finset.univ.filter
        (fun i : Fin n ↦ sample.sourceHeight i ≤ leftBoundaryRankThreshold n t) by
    apply Finset.filter_congr
    intro i _
    rw [leftEventTime_le_iff_of_good hgood htB]
    change (n : ℝ) * (sample.sourceHeight i : ℝ) ≤ (t : ℝ) ↔ _
    change _ ↔ (sample.sourceHeight i : ℝ) ≤
      ((leftBoundaryRankThreshold n t : UnitMark) : ℝ)
    rw [hthreshold, le_div_iff₀ hnreal]
    simp only [mul_comm]]
  unfold leftSourceCountAt
  rw [Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext i
  simp

theorem leftTargetCountingProcess_eq_leftTargetCountAt_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    leftTargetCountingProcess n B t sample =
      sample.leftTargetCountAt (leftBoundaryRankThreshold n t) := by
  classical
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htBreal : (t : ℝ) ≤ B := by exact_mod_cast htB
  have htn : (t : ℝ) ≤ n := htBreal.trans hBn
  have hthreshold : ((leftBoundaryRankThreshold n t : UnitMark) : ℝ) = t / n :=
    leftBoundaryRankThreshold_coe_of_mem hn t.2 htn
  unfold leftTargetCountingProcess leftColorCount CountingProcess.finiteEventCountTop
  rw [show Finset.univ.filter
      (fun i : Fin n ↦ leftEventTime n B (1, i) sample ≤ (t : WithTop ℝ≥0)) =
      Finset.univ.filter
        (fun i : Fin n ↦ sample.targetHeight i ≤ leftBoundaryRankThreshold n t) by
    apply Finset.filter_congr
    intro i _
    rw [leftEventTime_le_iff_of_good hgood htB]
    change (n : ℝ) * (sample.targetHeight i : ℝ) ≤ (t : ℝ) ↔ _
    change _ ↔ (sample.targetHeight i : ℝ) ≤
      ((leftBoundaryRankThreshold n t : UnitMark) : ℝ)
    rw [hthreshold, le_div_iff₀ hnreal]
    simp only [mul_comm]]
  unfold leftTargetCountAt
  rw [Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext i
  simp

theorem countBefore_leftSourceCountingProcess_eq_leftSourceCountBeforeAt_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    CountingProcess.countBefore (leftSourceCountingProcess n B) t sample =
      sample.leftSourceCountBeforeAt (leftBoundaryRankThreshold n t) := by
  classical
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htBreal : (t : ℝ) ≤ B := by exact_mod_cast htB
  have htn : (t : ℝ) ≤ n := htBreal.trans hBn
  have hthreshold : ((leftBoundaryRankThreshold n t : UnitMark) : ℝ) = t / n :=
    leftBoundaryRankThreshold_coe_of_mem hn t.2 htn
  unfold leftSourceCountingProcess leftColorCount
  rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
  rw [show Finset.univ.filter
      (fun i : Fin n ↦ leftEventTime n B (0, i) sample < (t : WithTop ℝ≥0)) =
      Finset.univ.filter
        (fun i : Fin n ↦ sample.sourceHeight i < leftBoundaryRankThreshold n t) by
    apply Finset.filter_congr
    intro i _
    rw [leftEventTime_lt_iff_of_good hgood htB]
    change (n : ℝ) * (sample.sourceHeight i : ℝ) < (t : ℝ) ↔ _
    change _ ↔ (sample.sourceHeight i : ℝ) <
      ((leftBoundaryRankThreshold n t : UnitMark) : ℝ)
    rw [hthreshold, lt_div_iff₀ hnreal]
    simp only [mul_comm]]
  unfold leftSourceCountBeforeAt
  rw [Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext i
  simp

theorem countBefore_leftTargetCountingProcess_eq_leftTargetCountBeforeAt_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    CountingProcess.countBefore (leftTargetCountingProcess n B) t sample =
      sample.leftTargetCountBeforeAt (leftBoundaryRankThreshold n t) := by
  classical
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htBreal : (t : ℝ) ≤ B := by exact_mod_cast htB
  have htn : (t : ℝ) ≤ n := htBreal.trans hBn
  have hthreshold : ((leftBoundaryRankThreshold n t : UnitMark) : ℝ) = t / n :=
    leftBoundaryRankThreshold_coe_of_mem hn t.2 htn
  unfold leftTargetCountingProcess leftColorCount
  rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
  rw [show Finset.univ.filter
      (fun i : Fin n ↦ leftEventTime n B (1, i) sample < (t : WithTop ℝ≥0)) =
      Finset.univ.filter
        (fun i : Fin n ↦ sample.targetHeight i < leftBoundaryRankThreshold n t) by
    apply Finset.filter_congr
    intro i _
    rw [leftEventTime_lt_iff_of_good hgood htB]
    change (n : ℝ) * (sample.targetHeight i : ℝ) < (t : ℝ) ↔ _
    change _ ↔ (sample.targetHeight i : ℝ) <
      ((leftBoundaryRankThreshold n t : UnitMark) : ℝ)
    rw [hthreshold, lt_div_iff₀ hnreal]
    simp only [mul_comm]]
  unfold leftTargetCountBeforeAt
  rw [Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext i
  simp

theorem leftSourceCountingProcess_ae_eq_leftSourceCountAt
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n) :
    leftSourceCountingProcess n B t =ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦ sample.leftSourceCountAt (leftBoundaryRankThreshold n t) := by
  filter_upwards [ae_mem_leftHeightGenericEvent n] with sample hgood
  exact leftSourceCountingProcess_eq_leftSourceCountAt_of_good hn htB hBn hgood

theorem leftTargetCountingProcess_ae_eq_leftTargetCountAt
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n) :
    leftTargetCountingProcess n B t =ᵐ[(finiteSampleLaw n : Measure (FiniteSample n))]
      fun sample ↦ sample.leftTargetCountAt (leftBoundaryRankThreshold n t) := by
  filter_upwards [ae_mem_leftHeightGenericEvent n] with sample hgood
  exact leftTargetCountingProcess_eq_leftTargetCountAt_of_good hn htB hBn hgood

theorem leftEventTime_eq_top_or_pos
    (n : ℕ) (B : ℝ≥0) (label : LeftHeightLabel n) (sample : FiniteSample n) :
    leftEventTime n B label sample = ⊤ ∨
      (0 : WithTop ℝ≥0) < leftEventTime n B label sample := by
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · rw [leftEventTime, ite_eq_left hgood]
    unfold leftRawEventTime
    dsimp only
    split_ifs with hB
    · right
      rw [WithTop.coe_pos]
      have hn : 0 < n := Nat.zero_lt_of_lt label.2.isLt
      have hhne : (leftHeightCoordinate label sample : ℝ) ≠ 0 := by
        intro hh
        exact hgood.1 label (Subtype.ext hh)
      have hh : 0 < (leftHeightCoordinate label sample : ℝ) :=
        lt_of_le_of_ne (leftHeightCoordinate label sample).property.1 (Ne.symm hhne)
      exact Real.toNNReal_pos.mpr (mul_pos (by exact_mod_cast hn) hh)
    · exact Or.inl rfl
  · exact Or.inl (by simp [leftEventTime, hgood])

theorem leftEventTime_injective
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) :
    ∀ sample (i j : Fin n),
      leftEventTime n B (color, i) sample ≠ ⊤ →
      leftEventTime n B (color, j) sample ≠ ⊤ →
      leftEventTime n B (color, i) sample = leftEventTime n B (color, j) sample → i = j := by
  intro sample i j hi hj heq
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · have hiRaw : leftRawEventTime n B (color, i) sample ≠ ⊤ := by
      simpa [leftEventTime, hgood] using hi
    have hjRaw : leftRawEventTime n B (color, j) sample ≠ ⊤ := by
      simpa [leftEventTime, hgood] using hj
    have hraw := heq
    simp only [leftEventTime, hgood, ite_true] at hraw
    unfold leftRawEventTime at hraw
    dsimp only at hraw
    split_ifs at hraw with hiB hjB
    · have hreal :
          (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) =
            (n : ℝ) * (leftHeightCoordinate (color, j) sample : ℝ) := by
        have hnnI := WithTop.coe_eq_coe.mp hraw
        have hcoe := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hnnI
        have hi0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) :=
          mul_nonneg (by positivity) (leftHeightCoordinate (color, i) sample).property.1
        have hj0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate (color, j) sample : ℝ) :=
          mul_nonneg (by positivity) (leftHeightCoordinate (color, j) sample).property.1
        simpa [Real.coe_toNNReal _ hi0, Real.coe_toNNReal _ hj0] using hcoe
      have hh : leftHeightCoordinate (color, i) sample =
          leftHeightCoordinate (color, j) sample := by
        have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
        apply Subtype.ext
        exact (mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hn)) hreal)
      exact congrArg Prod.snd (hgood.2 (color, i) (color, j) hh)
    · exact (hjRaw (by simp [leftRawEventTime, hjB])).elim
    · exact (hiRaw (by simp [leftRawEventTime, hiB])).elim
    · exact (hiRaw (by simp [leftRawEventTime, hiB])).elim
  · exact (hi (by simp [leftEventTime, hgood])).elim

theorem leftColorCount_stronglyAdapted (n : ℕ) (B : ℝ≥0) (color : Fin 2) :
    StronglyAdapted (leftUsualFiltration n B)
      (fun t sample ↦ (leftColorCount n B color t sample : ℝ)) := by
  exact CountingProcess.finiteEventCountTop_stronglyAdapted
    (leftUsualFiltration n B) (fun i : Fin n ↦ leftEventTime n B (color, i))
    (fun i ↦ leftEventTime_isStoppingTime n B (color, i))

theorem leftColorCount_isSimpleCountingProcess
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) :
    CountingProcess.IsSimpleCountingProcess (leftUsualFiltration n B)
      (leftColorCount n B color) := by
  exact CountingProcess.IsSimpleCountingProcess.of_finiteEventCountTop
    (fun i : Fin n ↦ leftEventTime n B (color, i))
    (fun sample i ↦ leftEventTime_eq_top_or_pos n B (color, i) sample)
    (leftEventTime_injective n B color)
    (leftColorCount_stronglyAdapted n B color)

/-- Positive stabilized denominator.  It agrees with `n-t` through the left horizon. -/
noncomputable def leftRateDenominator (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) : ℝ :=
  max ((n : ℝ) - B) ((n : ℝ) - (t : ℝ))

theorem leftRateDenominator_eq_sub_of_le {B t : ℝ≥0} (htB : t ≤ B) :
    leftRateDenominator n B t = (n : ℝ) - t := by
  unfold leftRateDenominator
  rw [max_eq_right]
  exact sub_le_sub_left (by exact_mod_cast htB) _

theorem leftRateDenominator_pos {B : ℝ≥0}
    (hBn : (B : ℝ) < n) (t : ℝ≥0) :
    0 < leftRateDenominator n B t := by
  exact lt_of_lt_of_le (sub_pos.mpr hBn) (le_max_left _ _)

/-- Predictable safe rate of one color, supported on the right-closed left interval. -/
noncomputable def leftColorIntensity
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  CountingProcess.throughStopMask (fun _ : FiniteSample n ↦ (B : WithTop ℝ≥0)) t sample *
    (if sample ∈ leftHeightGenericEvent n then
      ((n : ℝ) - CountingProcess.countBefore (leftColorCount n B color) t sample) /
        leftRateDenominator n B t
    else 0)

noncomputable def leftSourceIntensity (n : ℕ) (B : ℝ≥0) :=
  leftColorIntensity n B 0

noncomputable def leftTargetIntensity (n : ℕ) (B : ℝ≥0) :=
  leftColorIntensity n B 1

private theorem leftColorIntensity_eq_sum_physical_hazards
    {B u : ℝ≥0} (color : Fin 2)
    (sample : FiniteSample n) :
    leftColorIntensity n B color u sample =
      ∑ i : Fin n,
        if sample ∈ leftHeightGenericEvent n ∧ u ≤ B ∧
            (u : ℝ) ≤ (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) then
          1 / ((n : ℝ) - u) else 0 := by
  classical
  by_cases huB : u ≤ B
  · by_cases hgood : sample ∈ leftHeightGenericEvent n
    · have hmask : CountingProcess.throughStopMask
          (fun _ : FiniteSample n ↦ (B : WithTop ℝ≥0)) u sample = 1 := by
        unfold CountingProcess.throughStopMask
        rw [ite_eq_left]
        exact WithTop.coe_le_coe.mpr huB
      have hcount :
          (CountingProcess.countBefore (leftColorCount n B color) u sample : ℝ) =
            ∑ i : Fin n,
              if (n : ℝ) * (leftHeightCoordinate (color, i) sample : ℝ) < u then
                1 else 0 := by
        unfold leftColorCount
        rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
        rw [Finset.natCast_card_filter]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [leftEventTime_lt_iff_of_good hgood huB]
      rw [leftColorIntensity, hmask, one_mul, ite_eq_left hgood,
        leftRateDenominator_eq_sub_of_le huB, hcount]
      have hnSum : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      rw [hnSum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hlt : (n : ℝ) *
          (leftHeightCoordinate (color, i) sample : ℝ) < u
      · have hnot : ¬((u : ℝ) ≤ (n : ℝ) *
            (leftHeightCoordinate (color, i) sample : ℝ)) := not_le.mpr hlt
        simp [hgood, huB, hlt, hnot]
      · have hle : (u : ℝ) ≤ (n : ℝ) *
            (leftHeightCoordinate (color, i) sample : ℝ) := le_of_not_gt hlt
        simp [hgood, huB, hlt, hle]
    · simp [leftColorIntensity, hgood]
  · have hmask : CountingProcess.throughStopMask
        (fun _ : FiniteSample n ↦ (B : WithTop ℝ≥0)) u sample = 0 := by
      simp only [CountingProcess.throughStopMask]
      rw [ite_eq_right]
      simpa only [WithTop.coe_le_coe] using huB
    rw [leftColorIntensity, hmask, zero_mul]
    simp [huB]

theorem leftColorIntensity_predictable
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) :
    IsStronglyPredictable (leftUsualFiltration n B) (leftColorIntensity n B color) := by
  let F := leftUsualFiltration n B
  have hgeneric : IsStronglyPredictable F
      (fun (_ : ℝ≥0) (sample : FiniteSample n) ↦
        if sample ∈ leftHeightGenericEvent n then (1 : ℝ) else 0) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · intro t
      exact (Measurable.ite (measurableSet_leftHeightGenericEvent_at n B t)
        measurable_const measurable_const).stronglyMeasurable
    · intro sample
      by_cases hsample : sample ∈ leftHeightGenericEvent n
      · simp only [hsample, ite_true]
        exact continuous_const
      · simp only [hsample, ite_false]
        exact continuous_const
  have hcount : StronglyMeasurable[F.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        (CountingProcess.countBefore (leftColorCount n B color) z.1 z.2 : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore
      (leftColorCount_isSimpleCountingProcess n B color).stronglyAdapted
      (leftColorCount_isSimpleCountingProcess n B color).monotone
  have hden : IsStronglyPredictable F
      (fun (t : ℝ≥0) (_ : FiniteSample n) ↦ leftRateDenominator n B t) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · exact fun _ ↦ stronglyMeasurable_const
    · intro sample
      unfold leftRateDenominator
      fun_prop
  have hratio : StronglyMeasurable[F.predictable]
      (Function.uncurry fun (t : ℝ≥0) (sample : FiniteSample n) ↦
        ((n : ℝ) - CountingProcess.countBefore (leftColorCount n B color) t sample) /
          leftRateDenominator n B t) := by
    exact (stronglyMeasurable_const.sub hcount).div hden
  have hstop : IsStronglyPredictable F
      (CountingProcess.throughStopMask
        (fun _ : FiniteSample n ↦ (B : WithTop ℝ≥0))) :=
    CountingProcess.throughStopMask_predictable
      (isStoppingTime_const F B)
      Set.finite_range_const
  change StronglyMeasurable[F.predictable] (Function.uncurry (leftColorIntensity n B color))
  have hprod := hstop.mul hgeneric |>.mul hratio
  convert hprod using 1
  funext z
  rcases z with ⟨t, sample⟩
  by_cases hsample : sample ∈ leftHeightGenericEvent n
  · simp [leftColorIntensity, hsample]
  · simp [leftColorIntensity, hsample]

theorem leftSourceIntensity_predictable (n : ℕ) (B : ℝ≥0) :
    IsStronglyPredictable (leftUsualFiltration n B) (leftSourceIntensity n B) :=
  leftColorIntensity_predictable n B 0

theorem leftTargetIntensity_predictable (n : ℕ) (B : ℝ≥0) :
    IsStronglyPredictable (leftUsualFiltration n B) (leftTargetIntensity n B) :=
  leftColorIntensity_predictable n B 1

private theorem countBefore_leftColorCount_le
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0) (sample : FiniteSample n) :
    CountingProcess.countBefore (leftColorCount n B color) t sample ≤
      leftColorCount n B color t sample := by
  have hmono := (leftColorCount_isSimpleCountingProcess n B color).monotone sample
  by_contra hle
  have hsucc : leftColorCount n B color t sample + 1 ≤
      CountingProcess.countBefore (leftColorCount n B color) t sample :=
    Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  rw [CountingProcess.countBefore_succ_le_iff hmono] at hsucc
  rcases hsucc with ⟨s, hst, hs⟩
  exact (Nat.not_lt_of_ge (hmono hst.le)) hs

theorem leftColorIntensity_nonneg
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (color : Fin 2)
    (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ leftColorIntensity n B color t sample := by
  have hcount := countBefore_leftColorCount_le n B color t sample
  have hcountN : CountingProcess.countBefore (leftColorCount n B color) t sample ≤ n :=
    hcount.trans (CountingProcess.finiteEventCountTop_le
      (fun i : Fin n ↦ leftEventTime n B (color, i)) t sample)
  have hcountNreal :
      (CountingProcess.countBefore (leftColorCount n B color) t sample : ℝ) ≤ n := by
    exact_mod_cast hcountN
  have hnum : 0 ≤ (n : ℝ) -
      CountingProcess.countBefore (leftColorCount n B color) t sample := by
    exact sub_nonneg.mpr hcountNreal
  have hden : 0 ≤ leftRateDenominator n B t :=
    (leftRateDenominator_pos hBn t).le
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · by_cases hmask : (t : WithTop ℝ≥0) ≤ (B : WithTop ℝ≥0)
    · simp only [leftColorIntensity, hgood, ite_true,
        CountingProcess.throughStopMask, hmask, one_mul]
      exact div_nonneg hnum hden
    · simp only [leftColorIntensity, hgood, ite_true,
        CountingProcess.throughStopMask, hmask, ite_false, zero_mul]
      norm_num
  · simp [leftColorIntensity, hgood]

theorem leftColorIntensity_le_two
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (hBquarter : 4 * (B : ℝ) ≤ n)
    (color : Fin 2)
    (t : ℝ≥0) (sample : FiniteSample n) :
    leftColorIntensity n B color t sample ≤ 2 := by
  by_cases htB : t ≤ B
  · by_cases hgood : sample ∈ leftHeightGenericEvent n
    · have hcountN : CountingProcess.countBefore (leftColorCount n B color) t sample ≤ n :=
        (countBefore_leftColorCount_le n B color t sample).trans
            (CountingProcess.finiteEventCountTop_le
              (fun i : Fin n ↦ leftEventTime n B (color, i)) t sample)
      have hcount0 : 0 ≤
          (CountingProcess.countBefore (leftColorCount n B color) t sample : ℝ) := by
        positivity
      have hden : 0 < (n : ℝ) - t := by
        have htReal : (t : ℝ) ≤ B := by exact_mod_cast htB
        exact sub_pos.mpr (htReal.trans_lt hBn)
      rw [leftColorIntensity, leftRateDenominator_eq_sub_of_le htB]
      simp only [CountingProcess.throughStopMask, WithTop.coe_le_coe, htB, ite_true, hgood]
      rw [one_mul]
      rw [div_le_iff₀ hden]
      have hcountNreal :
          (CountingProcess.countBefore (leftColorCount n B color) t sample : ℝ) ≤ n := by
        exact_mod_cast hcountN
      have htReal : (t : ℝ) ≤ B := by exact_mod_cast htB
      nlinarith
    · simp [leftColorIntensity, hgood]
  · have htBTop : ¬((t : WithTop ℝ≥0) ≤ (B : WithTop ℝ≥0)) := by
      simpa only [WithTop.coe_le_coe] using htB
    by_cases hgood : sample ∈ leftHeightGenericEvent n
    · simp only [leftColorIntensity, hgood, ite_true,
        CountingProcess.throughStopMask, htBTop, ite_false, zero_mul]
      norm_num
    · simp [leftColorIntensity, hgood]

theorem leftColorIntensity_integrableOn
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (hBquarter : 4 * (B : ℝ) ≤ n)
    (color : Fin 2) (T : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun t ↦ leftColorIntensity n B color t sample)
      (Ioc (0 : ℝ≥0) T) CountingProcess.timeMeasure := by
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry (leftColorIntensity n B color)) :=
    (leftColorIntensity_predictable n B color).mono
      (CountingProcess.predictable_le_ambient (leftUsualFiltration n B))
  have hsection : StronglyMeasurable (fun t ↦ leftColorIntensity n B color t sample) :=
    hambient.comp_measurable (measurable_id.prodMk measurable_const)
  apply Measure.integrableOn_of_bounded (CountingProcess.timeMeasure_Ioc_lt_top 0 T).ne
    hsection.aestronglyMeasurable (M := 2)
  exact ae_of_all _ fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (leftColorIntensity_nonneg hBn color t sample)]
    exact leftColorIntensity_le_two hBn hBquarter color t sample

theorem leftColorIntensity_product_integrable
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (hBquarter : 4 * (B : ℝ) ≤ n)
    (color : Fin 2) :
    Integrable (Function.uncurry (leftColorIntensity n B color))
      (CountingProcess.timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  apply CountingProcess.integrable_uncurry_of_predictable_bounded_finite_support
    (finiteSampleLaw n : Measure (FiniteSample n)) (leftUsualFiltration n B)
    (leftColorIntensity_predictable n B color)
    (leftColorIntensity_nonneg hBn color) (by norm_num : (0 : ℝ) ≤ 2)
    (leftColorIntensity_le_two hBn hBquarter color) B
  intro t sample hne
  by_contra htB
  have htBTop : ¬((t : WithTop ℝ≥0) ≤ (B : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_le_coe] using htB
  apply hne
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · simp only [leftColorIntensity, hgood, ite_true,
      CountingProcess.throughStopMask, htBTop, ite_false, zero_mul]
  · simp [leftColorIntensity, hgood]

/-! ## Raw rectangle identity and actual predictable intensities -/

theorem leftColorCount_sub_setIntegral_eq_rawRectangle
    (hn : 0 < n) {B : ℝ≥0} (hBn : (B : ℝ) < n) (color : Fin 2)
    {s t : ℝ≥0} (hst : s ≤ t) (E : Set (FiniteSample n))
    (hE : MeasurableSet[leftRawFiltration n B s] E) :
    (∫ sample in E,
      ((leftColorCount n B color t sample : ℝ) - leftColorCount n B color s sample)
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ∫ sample in E, ∫ u in Ioc s t, leftColorIntensity n B color u sample
        ∂CountingProcess.timeMeasure ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  classical
  have hEambient : MeasurableSet E := (leftRawFiltration n B).le s E hE
  by_cases hsB : s < B
  · let W : Fin n → FiniteSample n → ℝ := fun i ↦
      leftRawWindowLabel n B s t E (color, i)
    let H : Fin n → FiniteSample n → ℝ := fun i sample ↦
      ∫ u in Ioc s t, leftRawHazardLabel n B u E (color, i) sample
        ∂CountingProcess.timeMeasure
    have hWint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (W i) (finiteSampleLaw n : Measure (FiniteSample n)) := by
      intro i hi
      exact integrable_leftRawWindowLabel hEambient (color, i)
    have hHint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (H i) (finiteSampleLaw n : Measure (FiniteSample n)) := by
      intro i hi
      exact integrable_integral_leftRawHazardLabel hBn hEambient (color, i)
    have hlabel : ∀ i : Fin n,
        (∫ sample, W i sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
          ∫ sample, H i sample ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
      intro i
      simpa only [W, H, leftRawWindowLabel, leftRawHazardLabel] using
        left_raw_event_label_hazard_integral hn hst hsB hBn (color, i) E hE
    have hleftPoint : ∀ sample : FiniteSample n,
        E.indicator (fun sample ↦
          ((leftColorCount n B color t sample : ℝ) -
            leftColorCount n B color s sample)) sample =
          ∑ i : Fin n, W i sample := by
      intro sample
      by_cases hsampleE : sample ∈ E
      · rw [Set.indicator_of_mem hsampleE,
          leftColorCount_sub_eq_sum_physical_window hst hsB]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [W, leftRawWindowLabel, hsampleE, true_and]
      · rw [Set.indicator_of_notMem hsampleE]
        apply (Finset.sum_eq_zero fun i hi ↦ ?_).symm
        simp [W, leftRawWindowLabel, hsampleE]
    have hrightPoint : ∀ sample : FiniteSample n,
        ∑ i : Fin n, H i sample =
          E.indicator (fun sample ↦
            ∫ u in Ioc s t, leftColorIntensity n B color u sample
              ∂CountingProcess.timeMeasure) sample := by
      intro sample
      by_cases hsampleE : sample ∈ E
      · rw [Set.indicator_of_mem hsampleE]
        rw [show (fun u ↦ leftColorIntensity n B color u sample) =
            fun u ↦ ∑ i : Fin n,
              leftRawHazardLabel n B u E (color, i) sample by
          funext u
          rw [leftColorIntensity_eq_sum_physical_hazards color sample]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [leftRawHazardLabel, hsampleE, true_and]]
        exact (integral_finsetSum Finset.univ fun i hi ↦
          integrableOn_leftRawHazardLabel hBn hEambient (color, i) sample).symm
      · rw [Set.indicator_of_notMem hsampleE]
        apply Finset.sum_eq_zero
        intro i hi
        simp [H, leftRawHazardLabel, hsampleE]
    calc
      (∫ sample in E,
        ((leftColorCount n B color t sample : ℝ) - leftColorCount n B color s sample)
          ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
          ∫ sample, E.indicator (fun sample ↦
            ((leftColorCount n B color t sample : ℝ) -
              leftColorCount n B color s sample)) sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) :=
        (integral_indicator hEambient).symm
      _ = ∫ sample, ∑ i : Fin n, W i sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hleftPoint
      _ = ∑ i : Fin n, ∫ sample, W i sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) :=
        integral_finsetSum Finset.univ hWint
      _ = ∑ i : Fin n, ∫ sample, H i sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hlabel i
      _ = ∫ sample, ∑ i : Fin n, H i sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) :=
        (integral_finsetSum Finset.univ hHint).symm
      _ = ∫ sample, E.indicator (fun sample ↦
            ∫ u in Ioc s t, leftColorIntensity n B color u sample
              ∂CountingProcess.timeMeasure) sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hrightPoint
      _ = ∫ sample in E, ∫ u in Ioc s t, leftColorIntensity n B color u sample
            ∂CountingProcess.timeMeasure
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) :=
        integral_indicator hEambient
  · have hBs : B ≤ s := le_of_not_gt hsB
    have hcount : ∀ sample : FiniteSample n,
        ((leftColorCount n B color t sample : ℝ) -
          leftColorCount n B color s sample) = 0 := by
      intro sample
      rw [leftColorCount_eq_of_boundary_le hBs hst]
      norm_num
    have hrate : ∀ sample : FiniteSample n,
        (∫ u in Ioc s t, leftColorIntensity n B color u sample
          ∂CountingProcess.timeMeasure) = 0 := by
      intro sample
      calc
        (∫ u in Ioc s t, leftColorIntensity n B color u sample
            ∂CountingProcess.timeMeasure) =
            ∫ _u in Ioc s t, (0 : ℝ) ∂CountingProcess.timeMeasure := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          have huB : ¬ u ≤ B := not_le.mpr (hBs.trans_lt hu.1)
          change leftColorIntensity n B color u sample = 0
          rw [leftColorIntensity_eq_sum_physical_hazards color sample]
          simp [huB]
        _ = 0 := by simp
    simp_rw [hcount, hrate]

/-- The safe finite-event left count of either color has the genuine finite-population
hazard as predictable intensity. -/
theorem leftColorCount_hasPredictableIntensity
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n)
    (color : Fin 2) :
    CountingProcess.HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n))
      (leftUsualFiltration n B) (leftColorCount n B color)
      (leftColorIntensity n B color) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hBn : (B : ℝ) < n := by nlinarith
  exact CountingProcess.hasPredictableIntensity_of_finiteEvent_raw_countIncrement
    (finiteSampleLaw n : Measure (FiniteSample n))
    (leftRawFiltration n B)
    (fun i : Fin n ↦ leftEventTime n B (color, i))
    (fun i ↦ leftEventTime_isStoppingTime n B (color, i))
    (fun i sample ↦ leftEventTime_eq_top_or_pos n B (color, i) sample)
    (leftEventTime_injective n B color)
    (leftColorIntensity n B color)
    (leftColorIntensity_predictable n B color)
    (by norm_num : (0 : ℝ) ≤ 2)
    (leftColorIntensity_nonneg hBn color)
    (leftColorIntensity_le_two hBn hBquarter color)
    (leftColorIntensity_integrableOn hBn hBquarter color)
    (leftColorIntensity_product_integrable hBn hBquarter color)
    (fun hst E hE ↦
      leftColorCount_sub_setIntegral_eq_rawRectangle hn hBn color hst E hE)

theorem leftSourceCountingProcess_hasPredictableIntensity
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    CountingProcess.HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n))
      (leftUsualFiltration n B) (leftSourceCountingProcess n B)
      (leftSourceIntensity n B) :=
  leftColorCount_hasPredictableIntensity hn hB hBquarter 0

theorem leftTargetCountingProcess_hasPredictableIntensity
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    CountingProcess.HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n))
      (leftUsualFiltration n B) (leftTargetCountingProcess n B)
      (leftTargetIntensity n B) :=
  leftColorCount_hasPredictableIntensity hn hB hBquarter 1

/-! ## Capped post-jump path and first rate failure -/

/-- Strict-left stabilized rate.  On the physical interval it is the ordinary left rate. -/
noncomputable def leftColorStrictRate
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  if sample ∈ leftHeightGenericEvent n then
    ((n : ℝ) - CountingProcess.countBefore (leftColorCount n B color) t sample) /
      leftRateDenominator n B t
  else 0

noncomputable def leftStrictRatePath
    (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (leftColorStrictRate n B 0 t sample, leftColorStrictRate n B 1 t sample)

noncomputable def leftColorPostRate
    (n : ℕ) (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  if sample ∈ leftHeightGenericEvent n then
    ((n : ℝ) - leftColorCount n B color t sample) /
      leftRateDenominator n B t
  else 0

noncomputable def leftPostRatePath
    (n : ℕ) (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (leftColorPostRate n B 0 t sample, leftColorPostRate n B 1 t sample)

theorem leftPostRatePath_adapted (n : ℕ) (B : ℝ≥0) :
    Adapted (leftUsualFiltration n B) (leftPostRatePath n B) := by
  intro t
  have hgood := measurableSet_leftHeightGenericEvent_at n B t
  have hsCount := leftColorCount_stronglyAdapted n B 0 t
  have htCount := leftColorCount_stronglyAdapted n B 1 t
  have hden : StronglyMeasurable[leftUsualFiltration n B t]
      (fun _ : FiniteSample n ↦ leftRateDenominator n B t) :=
    stronglyMeasurable_const
  have hsRate : StronglyMeasurable[leftUsualFiltration n B t]
      (fun sample : FiniteSample n ↦
        ((n : ℝ) - leftColorCount n B 0 t sample) / leftRateDenominator n B t) :=
    (stronglyMeasurable_const.sub hsCount).div hden
  have htRate : StronglyMeasurable[leftUsualFiltration n B t]
      (fun sample : FiniteSample n ↦
        ((n : ℝ) - leftColorCount n B 1 t sample) / leftRateDenominator n B t) :=
    (stronglyMeasurable_const.sub htCount).div hden
  have hsSafe := hsRate.indicator hgood
  have htSafe := htRate.indicator hgood
  convert (hsSafe.prodMk htSafe).measurable using 1
  funext sample
  by_cases hsample : sample ∈ leftHeightGenericEvent n
  · simp [leftPostRatePath, leftColorPostRate, Set.indicator, hsample]
  · simp [leftPostRatePath, leftColorPostRate, Set.indicator, hsample]

theorem leftPostRatePath_rightContinuous
    {B : ℝ≥0} (hBn : (B : ℝ) < n)
    (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ leftPostRatePath n B s sample) (Ici t) t := by
  have hden : Continuous fun s : ℝ≥0 ↦ leftRateDenominator n B s := by
    unfold leftRateDenominator
    fun_prop
  have hden0 : leftRateDenominator n B t ≠ 0 :=
    ne_of_gt (leftRateDenominator_pos hBn t)
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · have hsCount := CountingProcess.finiteEventCountTop_rightContinuous
      (fun i : Fin n ↦ leftEventTime n B (0, i)) sample t
    have htCount := CountingProcess.finiteEventCountTop_rightContinuous
      (fun i : Fin n ↦ leftEventTime n B (1, i)) sample t
    have hsNum : ContinuousWithinAt
        (fun s : ℝ≥0 ↦ (n : ℝ) - leftColorCount n B 0 s sample) (Ici t) t :=
      continuousWithinAt_const.sub hsCount
    have htNum : ContinuousWithinAt
        (fun s : ℝ≥0 ↦ (n : ℝ) - leftColorCount n B 1 s sample) (Ici t) t :=
      continuousWithinAt_const.sub htCount
    have hsRate : ContinuousWithinAt
        (fun s : ℝ≥0 ↦ ((n : ℝ) - leftColorCount n B 0 s sample) /
          leftRateDenominator n B s) (Ici t) t :=
      hsNum.div hden.continuousAt.continuousWithinAt hden0
    have htRate : ContinuousWithinAt
        (fun s : ℝ≥0 ↦ ((n : ℝ) - leftColorCount n B 1 s sample) /
          leftRateDenominator n B s) (Ici t) t :=
      htNum.div hden.continuousAt.continuousWithinAt hden0
    simp only [leftPostRatePath, leftColorPostRate, hgood, ite_true]
    convert hsRate.prodMk_nhds htRate using 1
    all_goals rfl
  · simp only [leftPostRatePath, leftColorPostRate, hgood, ite_false]
    exact continuousWithinAt_const

private theorem leftColorPostRate_tendsto_strict
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (color : Fin 2)
    (sample : FiniteSample n) (t : ℝ≥0) :
    Tendsto (fun s ↦ leftColorPostRate n B color s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (leftColorStrictRate n B color t sample)) := by
  by_cases hgood : sample ∈ leftHeightGenericEvent n
  · have hcount : Tendsto
        (fun s ↦ (leftColorCount n B color s sample : ℝ))
        (nhdsWithin t (Iio t))
        (nhds (CountingProcess.countBefore (leftColorCount n B color) t sample : ℝ)) := by
      exact CountingProcess.finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio
        (fun i : Fin n ↦ leftEventTime n B (color, i)) sample t
    have hnum : Tendsto
        (fun s : ℝ≥0 ↦ (n : ℝ) - (leftColorCount n B color s sample : ℝ))
        (nhdsWithin t (Iio t))
        (nhds ((n : ℝ) -
          (CountingProcess.countBefore (leftColorCount n B color) t sample : ℝ))) :=
      tendsto_const_nhds.sub hcount
    have hden : Tendsto (fun s : ℝ≥0 ↦ leftRateDenominator n B s)
        (nhdsWithin t (Iio t)) (nhds (leftRateDenominator n B t)) := by
      exact (show Continuous fun s : ℝ≥0 ↦ leftRateDenominator n B s by
        unfold leftRateDenominator
        fun_prop).continuousAt.mono_left inf_le_left
    have hden0 : leftRateDenominator n B t ≠ 0 :=
      ne_of_gt (leftRateDenominator_pos hBn t)
    simp only [leftColorPostRate, leftColorStrictRate, hgood, ite_true]
    convert hnum.div hden hden0 using 1
    all_goals rfl
  · simp only [leftColorPostRate, leftColorStrictRate, hgood, ite_false]
    exact tendsto_const_nhds

theorem leftPostRatePath_tendsto_strict
    {B : ℝ≥0} (hBn : (B : ℝ) < n)
    (sample : FiniteSample n) (t : ℝ≥0) :
    Tendsto (fun s ↦ leftPostRatePath n B s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (leftStrictRatePath n B t sample)) :=
  (leftColorPostRate_tendsto_strict hBn 0 sample t).prodMk_nhds
    (leftColorPostRate_tendsto_strict hBn 1 sample t)

def leftRateRegion : Set (ℝ × ℝ) := Icc ((1 : ℝ) / 2) 2 ×ˢ Icc ((1 : ℝ) / 2) 2

def leftRateBadSet : Set (ℝ × ℝ) := leftRateRegionᶜ

theorem isOpen_leftRateBadSet : IsOpen leftRateBadSet :=
  (isClosed_Icc.prod isClosed_Icc).isOpen_compl

/-- First post-jump rate failure, capped at the deterministic boundary `B`. -/
noncomputable def leftRateExitTime (n : ℕ) (B : ℝ≥0) :
    FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  min (MeasureTheory.hittingAfter (leftPostRatePath n B) leftRateBadSet 0 sample)
    (B : WithTop ℝ≥0)

theorem leftRateExitTime_isStoppingTime
    {B : ℝ≥0} (hBn : (B : ℝ) < n) :
    IsStoppingTime (leftUsualFiltration n B) (leftRateExitTime n B) := by
  let _ : Filtration.IsRightContinuous (leftUsualFiltration n B) :=
    leftUsualFiltration_isRightContinuous n B
  have hhit :=
    CountingProcess.MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen_of_rightContinuous
      (leftPostRatePath_adapted n B)
      (leftPostRatePath_rightContinuous hBn)
      isOpen_leftRateBadSet
  intro t
  rw [show {sample | leftRateExitTime n B sample ≤ (t : WithTop ℝ≥0)} =
      {sample | MeasureTheory.hittingAfter
          (leftPostRatePath n B) leftRateBadSet 0 sample ≤ (t : WithTop ℝ≥0)} ∪
        {sample | (B : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} by
      ext sample
      simp only [leftRateExitTime, min_le_iff, mem_ofPred_eq, mem_union]]
  exact (hhit t).union (MeasurableSet.const ((B : WithTop ℝ≥0) ≤ t))

theorem leftStrictRatePath_mem_region_of_lt_exit
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) < leftRateExitTime n B sample) :
    leftStrictRatePath n B t sample ∈ leftRateRegion := by
  have htHit : (t : WithTop ℝ≥0) < MeasureTheory.hittingAfter
      (leftPostRatePath n B) leftRateBadSet 0 sample :=
    ht.trans_le (min_le_left _ _)
  by_cases ht0 : t = 0
  · subst t
    have hpost := CountingProcess.not_mem_of_lt_hittingAfter_zero htHit
    have heq : leftStrictRatePath n B 0 sample = leftPostRatePath n B 0 sample := by
      simp [leftStrictRatePath, leftPostRatePath, leftColorStrictRate,
        leftColorPostRate, leftColorCount, CountingProcess.finiteEventCountTop_zero,
        leftEventTime_eq_top_or_pos]
    rw [heq]
    simpa only [leftRateBadSet, mem_compl_iff, not_not] using hpost
  · have htpos : 0 < t := lt_of_le_of_ne t.2 (Ne.symm ht0)
    let _ : NeBot (nhdsWithin t (Iio t : Set ℝ≥0)) :=
      nhdsWithin_Iio_neBot' ⟨0, htpos⟩ le_rfl
    apply (isClosed_Icc.prod isClosed_Icc).mem_of_tendsto
      (leftPostRatePath_tendsto_strict hBn sample t)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsHit : (s : WithTop ℝ≥0) < MeasureTheory.hittingAfter
        (leftPostRatePath n B) leftRateBadSet 0 sample :=
      (WithTop.coe_lt_coe.mpr hs).trans htHit
    have hnot := CountingProcess.not_mem_of_lt_hittingAfter_zero hsHit
    simpa only [leftRateBadSet, leftRateRegion, mem_compl_iff, not_not] using hnot

theorem leftSourceStrictRate_eq_leftSourceRate_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    leftColorStrictRate n B 0 t sample = sample.leftSourceRate n t := by
  rw [leftColorStrictRate, ite_eq_left hgood,
    show leftColorCount n B 0 = leftSourceCountingProcess n B by rfl,
    countBefore_leftSourceCountingProcess_eq_leftSourceCountBeforeAt_of_good
      hn htB hBn hgood,
    leftRateDenominator_eq_sub_of_le htB]
  rfl

theorem leftTargetStrictRate_eq_leftTargetRate_of_good
    (hn : 0 < n) {B t : ℝ≥0} (htB : t ≤ B) (hBn : (B : ℝ) ≤ n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    leftColorStrictRate n B 1 t sample = sample.leftTargetRate n t := by
  rw [leftColorStrictRate, ite_eq_left hgood,
    show leftColorCount n B 1 = leftTargetCountingProcess n B by rfl,
    countBefore_leftTargetCountingProcess_eq_leftTargetCountBeforeAt_of_good
      hn htB hBn hgood,
    leftRateDenominator_eq_sub_of_le htB]
  rfl

/-- Before the first rate failure, both genuine strict-left rates remain in `[1/2,2]`. -/
theorem leftRates_mem_Icc_of_lt_exit
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n)
    (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) < leftRateExitTime n B sample) :
    sample.leftSourceRate n t ∈ Icc ((1 : ℝ) / 2) 2 ∧
      sample.leftTargetRate n t ∈ Icc ((1 : ℝ) / 2) 2 := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hBnStrict : (B : ℝ) < n := by nlinarith
  have htBTop : (t : WithTop ℝ≥0) < (B : WithTop ℝ≥0) :=
    ht.trans_le (min_le_right _ _)
  have htB : t ≤ B := (WithTop.coe_lt_coe.mp htBTop).le
  have hregion := leftStrictRatePath_mem_region_of_lt_exit hBnStrict t sample ht
  have hgood : sample ∈ leftHeightGenericEvent n := by
    by_contra hbad
    have hzero : leftStrictRatePath n B t sample = (0, 0) := by
      simp [leftStrictRatePath, leftColorStrictRate, hbad]
    rw [hzero, leftRateRegion, mem_prod] at hregion
    norm_num at hregion
  rw [leftRateRegion, mem_prod] at hregion
  rw [← leftSourceStrictRate_eq_leftSourceRate_of_good hn htB hBnStrict.le hgood,
    ← leftTargetStrictRate_eq_leftTargetRate_of_good hn htB hBnStrict.le hgood]
  exact hregion

end FiniteSample

end OTSelector
