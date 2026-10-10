import OTSelector.PointProcess.MatchingSceneReroot

/-!
# The first strictly positive event of two actual marked configurations

The Boolean coordinate retains the color (`true` for source and `false` for target).
Local finiteness and compactness of the mark space force the first positive time, when
there is any positive event, to be attained and strictly positive.
-/

open MeasureTheory Set
open scoped ENNReal Classical

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.PointProcess.LocalConfiguration

/-- Two actual configurations, with source color `true` and target color `false`. -/
abbrev TwoColor := Bool → LocalConfiguration matchingPointBase

/-- Actual occupied points after the root, retaining their color. -/
def positiveEvents (c : TwoColor) : Set (Bool × MatchingPoint) :=
  {q | 0 < q.2.1 ∧ multiplicity (c q.1) q.2 ≠ 0}

/-- The first strictly positive event time; it is infinite when there is no such event. -/
noncomputable def firstPositiveTime (c : TwoColor) : ℝ≥0∞ :=
  sInf {r | ∃ q ∈ positiveEvents c, r = ENNReal.ofReal q.2.1}

theorem finite_positiveEvents_le (c : TwoColor) (t : ℝ) :
    {q ∈ positiveEvents c | q.2.1 ≤ t}.Finite := by
  have hf (b : Bool) : {p : MatchingPoint | 0 < p.1 ∧ p.1 ≤ t ∧
      multiplicity (c b) p ≠ 0}.Finite := by
    apply ((locallyFiniteSupport_multiplicity (c b)).finite_inter_support_of_isCompact
      (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set UnitMark))
        : IsCompact (Icc (0 : ℝ) t ×ˢ (univ : Set UnitMark)))).subset
    intro p hp
    exact ⟨⟨⟨hp.1.le, hp.2.1⟩, mem_univ _⟩, hp.2.2⟩
  apply (finite_univ.biUnion fun b (_ : b ∈ (univ : Set Bool)) ↦
    (hf b).image (fun p : MatchingPoint ↦ (b, p))).subset
  rintro ⟨b, p⟩ ⟨⟨hp, hm⟩, ht⟩
  exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨mem_univ _, ⟨p, ⟨hp, ht, hm⟩, rfl⟩⟩⟩

theorem exists_min_positiveEvent (c : TwoColor) (hc : (positiveEvents c).Nonempty) :
    ∃ q ∈ positiveEvents c, ∀ p ∈ positiveEvents c, q.2.1 ≤ p.2.1 := by
  obtain ⟨p, hp⟩ := hc
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image
    {q ∈ positiveEvents c | q.2.1 ≤ p.2.1} (fun q ↦ q.2.1)
    (finite_positiveEvents_le c p.2.1) ⟨p, hp, le_rfl⟩
  refine ⟨q, hq.1, fun r hr ↦ ?_⟩
  by_cases h : r.2.1 ≤ p.2.1
  · exact hmin r ⟨hr, h⟩
  · exact hq.2.trans (le_of_not_ge h)

theorem firstPositiveTime_eq_of_min (c : TwoColor) {q : Bool × MatchingPoint}
    (hq : q ∈ positiveEvents c)
    (hmin : ∀ p ∈ positiveEvents c, q.2.1 ≤ p.2.1) :
    firstPositiveTime c = ENNReal.ofReal q.2.1 := by
  apply le_antisymm
  · exact sInf_le ⟨q, hq, rfl⟩
  · apply le_sInf
    rintro _ ⟨p, hp, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hmin p hp)

/-- Every nonempty positive configuration has an actual first colored point. -/
theorem exists_firstPositivePoint (c : TwoColor) (hc : (positiveEvents c).Nonempty) :
    ∃ q ∈ positiveEvents c, firstPositiveTime c = ENNReal.ofReal q.2.1 ∧
      ∀ p ∈ positiveEvents c, q.2.1 ≤ p.2.1 := by
  obtain ⟨q, hq, hm⟩ := exists_min_positiveEvent c hc
  exact ⟨q, hq, firstPositiveTime_eq_of_min c hq hm, hm⟩

theorem firstPositiveTime_eq_top_of_empty (c : TwoColor)
    (hc : ¬(positiveEvents c).Nonempty) : firstPositiveTime c = ∞ := by
  have he : {r | ∃ q ∈ positiveEvents c, r = ENNReal.ofReal q.2.1} = ∅ := by
    ext r
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨q, hq, _⟩
    exact hc ⟨q, hq⟩
  unfold firstPositiveTime
  rw [he, sInf_empty]

theorem firstPositiveTime_pos (c : TwoColor) : 0 < firstPositiveTime c := by
  by_cases hc : (positiveEvents c).Nonempty
  · obtain ⟨q, hq, heq, _⟩ := exists_firstPositivePoint c hc
    rw [heq]
    exact ENNReal.ofReal_pos.mpr hq.1
  · rw [firstPositiveTime_eq_top_of_empty c hc]
    exact ENNReal.zero_lt_top

theorem firstPositiveTime_le_iff_exists (c : TwoColor) {t : ℝ} (ht : 0 ≤ t) :
    firstPositiveTime c ≤ ENNReal.ofReal t ↔
      ∃ q ∈ positiveEvents c, q.2.1 ≤ t := by
  by_cases hc : (positiveEvents c).Nonempty
  · obtain ⟨q, hq, heq, hm⟩ := exists_firstPositivePoint c hc
    rw [heq, ENNReal.ofReal_le_ofReal_iff ht]
    exact ⟨fun h ↦ ⟨q, hq, h⟩, fun ⟨p, hp, ht⟩ ↦ (hm p hp).trans ht⟩
  · rw [firstPositiveTime_eq_top_of_empty c hc]
    constructor
    · intro h
      exact (ENNReal.ofReal_ne_top (top_le_iff.mp h)).elim
    · rintro ⟨q, hq, _⟩
      exact (hc ⟨q, hq⟩).elim

theorem countingMeasure_eq_zero_iff {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {base : X} (c : LocalConfiguration base) {s : Set X}
    (hs : MeasurableSet s) :
    countingMeasure c s = 0 ↔ ∀ p ∈ s, multiplicity c p = 0 := by
  constructor
  · intro h p hp
    have hm := measure_mono (singleton_subset_iff.mpr hp : {p} ⊆ s) (μ := countingMeasure c)
    rw [countingMeasure_singleton, h] at hm
    exact_mod_cast le_zero_iff.mp hm
  · intro h
    rw [countingMeasure_apply c hs, ENNReal.tsum_eq_zero]
    intro n
    rw [shellMeasure_apply c n hs]
    apply Multiset.sum_eq_zero
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hr
    apply indicator_of_notMem
    intro hps
    have hp' : multiplicity c p.val ≠ 0 := by
      rw [multiplicity_shell]
      exact Multiset.count_ne_zero.mpr hp
    exact hp' (h p.val hps)

theorem spatialCount_nonneg (c : LocalConfiguration matchingPointBase) (a b : ℝ) :
    0 ≤ spatialCount c a b := by
  have h := measureReal_nonneg (μ := countingMeasure c) (s := spatialIoc a b)
  rw [← spatialCount_cast] at h
  exact_mod_cast h

theorem spatialCount_pos_iff (c : LocalConfiguration matchingPointBase) (a b : ℝ) :
    0 < spatialCount c a b ↔
      ∃ p ∈ spatialIoc a b, multiplicity c p ≠ 0 := by
  have hm := countingMeasure_lt_top_of_isBounded c (isBounded_spatialIoc a b)
  have hz := countingMeasure_eq_zero_iff c (measurableSet_spatialIoc a b)
  have hc : (0 : ℝ) < (spatialCount c a b : ℝ) ↔
      countingMeasure c (spatialIoc a b) ≠ 0 := by
    rw [spatialCount_cast, Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨fun h ↦ ne_of_gt h.1, fun h ↦ ⟨pos_iff_ne_zero.mpr h, hm⟩⟩
  have hpos : 0 < spatialCount c a b ↔ countingMeasure c (spatialIoc a b) ≠ 0 := by
    exact_mod_cast hc
  rw [hpos, ne_eq, hz]
  push Not
  rfl

/-- The first-event stopping event is exactly the actual aggregate counting event. -/
theorem firstPositiveTime_le_iff (c : TwoColor) {t : ℝ} (ht : 0 ≤ t) :
    firstPositiveTime c ≤ ENNReal.ofReal t ↔
      1 ≤ spatialCount (c true) 0 t + spatialCount (c false) 0 t := by
  rw [firstPositiveTime_le_iff_exists c ht]
  have hc : 1 ≤ spatialCount (c true) 0 t + spatialCount (c false) 0 t ↔
      0 < spatialCount (c true) 0 t ∨ 0 < spatialCount (c false) 0 t := by
    have htrue := spatialCount_nonneg (c true) 0 t
    have hfalse := spatialCount_nonneg (c false) 0 t
    omega
  rw [hc, spatialCount_pos_iff, spatialCount_pos_iff]
  constructor
  · rintro ⟨⟨b, p⟩, ⟨hp, hm⟩, ht⟩
    cases b
    · exact Or.inr ⟨p, ⟨hp, ht⟩, hm⟩
    · exact Or.inl ⟨p, ⟨hp, ht⟩, hm⟩
  · rintro (⟨p, hp, hm⟩ | ⟨p, hp, hm⟩)
    · exact ⟨(true, p), ⟨hp.1, hm⟩, hp.2⟩
    · exact ⟨(false, p), ⟨hp.1, hm⟩, hp.2⟩

/-- The first positive time is measurable in the actual pair of shell-coded configurations. -/
@[fun_prop]
theorem measurable_firstPositiveTime : Measurable firstPositiveTime := by
  apply measurable_of_Iic
  intro t
  by_cases ht : t = ∞
  · simp [ht]
  have hinput (b : Bool) : Measurable (fun c : TwoColor ↦ (((0 : ℝ), t.toReal), c b)) :=
    measurable_const.prodMk (measurable_pi_apply b)
  have hm (b : Bool) : Measurable (fun c : TwoColor ↦ spatialCount (c b) 0 t.toReal) := by
    have hh := measurable_spatialCount.comp (hinput b)
    exact hh
  have heq : firstPositiveTime ⁻¹' Iic t = {c : TwoColor |
      1 ≤ spatialCount (c true) 0 t.toReal + spatialCount (c false) 0 t.toReal} := by
    ext c
    simpa only [mem_preimage, mem_Iic, mem_ofPred_eq, ENNReal.ofReal_toReal ht] using
      firstPositiveTime_le_iff c (t := t.toReal) ENNReal.toReal_nonneg
  rw [heq]
  exact measurableSet_le measurable_const ((hm true).add (hm false))

/-- A countable enumeration of all occupied colored points. Empty code slots return the
base point at time zero and therefore never qualify as positive events. -/
noncomputable def enumeratedPoint (c : TwoColor) (n : ℕ) : Bool × MatchingPoint :=
  match Encodable.decode (α := Bool × ℕ × ℕ) n with
  | none => (false, matchingPointBase)
  | some (b, j, k) => ((MultisetEncoding.paddedCode (c b j)).2 k).elim
      (false, matchingPointBase) (fun p ↦ (b, p.val))

@[fun_prop]
theorem measurable_enumeratedPoint (n : ℕ) : Measurable (fun c ↦ enumeratedPoint c n) := by
  unfold enumeratedPoint
  cases h : Encodable.decode (α := Bool × ℕ × ℕ) n with
  | none => exact measurable_const
  | some i =>
    rcases i with ⟨b, j, k⟩
    exact (MeasureTheory.Option.measurable_elim (false, matchingPointBase)
      (measurable_const.prodMk measurable_subtype_coe)).comp
        ((measurable_pi_apply k).comp (measurable_snd.comp
          (MultisetEncoding.measurable_paddedCode.comp
            ((measurable_pi_apply j).comp (measurable_pi_apply b)))))

theorem exists_enumeratedPoint (c : TwoColor) {q : Bool × MatchingPoint}
    (hq : multiplicity (c q.1) q.2 ≠ 0) : ∃ n, enumeratedPoint c n = q := by
  classical
  let : DecidableEq MatchingPoint := Classical.decEq _
  let j := shellIndex matchingPointBase q.2
  let p : Shell matchingPointBase j := ⟨q.2, rfl⟩
  have hp : p ∈ c q.1 j := Multiset.count_ne_zero.mp hq
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    ((Multiset.mem_sort (MultisetEncoding.codingLE _)).mpr hp)
  refine ⟨Encodable.encode (q.1, j, k), ?_⟩
  simp only [enumeratedPoint, Encodable.encodek, MultisetEncoding.paddedCode, hk,
    Option.elim_some]
  rfl

theorem enumeratedPoint_mem_of_pos (c : TwoColor) (n : ℕ)
    (hn : 0 < (enumeratedPoint c n).2.1) : enumeratedPoint c n ∈ positiveEvents c := by
  classical
  let : DecidableEq MatchingPoint := Classical.decEq _
  unfold enumeratedPoint at hn ⊢
  cases h : Encodable.decode (α := Bool × ℕ × ℕ) n with
  | none => simp [h, matchingPointBase] at hn
  | some i =>
    rcases i with ⟨b, j, k⟩
    simp only [h] at hn ⊢
    cases hp : (MultisetEncoding.paddedCode (c b j)).2 k with
    | none =>
      rw [hp] at hn
      exact (lt_irrefl (0 : ℝ) hn).elim
    | some p =>
      have hn' : 0 < p.val.1 := by
        simpa only [hp, Option.elim_some] using hn
      simp only [Option.elim_some]
      refine ⟨hn', ?_⟩
      rw [multiplicity_shell]
      exact Multiset.count_ne_zero.mpr ((Multiset.mem_sort (MultisetEncoding.codingLE _)).mp
        (List.mem_iff_getElem?.mpr ⟨k, hp⟩))

private def firstIndexPredicate (c : TwoColor) (n : ℕ) : Prop :=
  firstPositiveTime c = ∞ ∨
    (0 < (enumeratedPoint c n).2.1 ∧
      ENNReal.ofReal (enumeratedPoint c n).2.1 = firstPositiveTime c)

private theorem exists_firstIndex (c : TwoColor) : ∃ n, firstIndexPredicate c n := by
  by_cases ht : firstPositiveTime c = ∞
  · exact ⟨0, Or.inl ht⟩
  have hc : (positiveEvents c).Nonempty := by
    by_contra hc
    exact ht (firstPositiveTime_eq_top_of_empty c hc)
  obtain ⟨q, hq, heq, _⟩ := exists_firstPositivePoint c hc
  obtain ⟨n, hn⟩ := exists_enumeratedPoint c hq.2
  exact ⟨n, Or.inr (by simpa only [hn] using And.intro hq.1 heq.symm)⟩

private theorem measurableSet_firstIndexPredicate (n : ℕ) :
    MeasurableSet {c | firstIndexPredicate c n} := by
  exact (measurableSet_eq_fun measurable_firstPositiveTime measurable_const).union
    ((measurableSet_lt measurable_const (measurable_enumeratedPoint n).snd.fst).inter
      (measurableSet_eq_fun ((measurable_enumeratedPoint n).snd.fst.ennreal_ofReal)
        measurable_firstPositiveTime))

/-- A measurable first colored point. Coincident events are resolved by the fixed countable
shell code. If there is no positive event, the result is the target-colored base point. -/
noncomputable def firstPositiveEvent (c : TwoColor) : Bool × MatchingPoint :=
  if firstPositiveTime c = ∞ then (false, matchingPointBase)
  else enumeratedPoint c (Nat.find (exists_firstIndex c))

@[fun_prop]
theorem measurable_firstPositiveEvent : Measurable firstPositiveEvent := by
  exact Measurable.ite (measurableSet_eq_fun measurable_firstPositiveTime measurable_const)
    measurable_const (Measurable.find measurable_enumeratedPoint
      measurableSet_firstIndexPredicate exists_firstIndex)

/-- At every finite first time, the measurable selection is an actual point attaining it. -/
theorem firstPositiveEvent_spec (c : TwoColor) (ht : firstPositiveTime c ≠ ∞) :
    firstPositiveEvent c ∈ positiveEvents c ∧
      ENNReal.ofReal (firstPositiveEvent c).2.1 = firstPositiveTime c := by
  have h := Nat.find_spec (exists_firstIndex c)
  rcases h with h | h
  · exact (ht h).elim
  · simp only [firstPositiveEvent, ite_eq_right ht]
    exact ⟨enumeratedPoint_mem_of_pos c _ h.1, h.2⟩

/-- Every occupied marked point has multiplicity one, and no two colored points have the
same spatial time. This condition is imposed on the actual configurations. -/
def IsTimeSimple (c : TwoColor) : Prop :=
  (∀ q : Bool × MatchingPoint, multiplicity (c q.1) q.2 ≠ 0 →
    multiplicity (c q.1) q.2 = 1) ∧
  (∀ q r : Bool × MatchingPoint, multiplicity (c q.1) q.2 ≠ 0 →
    multiplicity (c r.1) r.2 ≠ 0 → q.2.1 = r.2.1 → q = r)

theorem firstPositiveTime_le_of_mem (c : TwoColor) {q : Bool × MatchingPoint}
    (hq : q ∈ positiveEvents c) : firstPositiveTime c ≤ ENNReal.ofReal q.2.1 :=
  sInf_le ⟨q, hq, rfl⟩

theorem firstPositiveEvent_eq_of_time (c : TwoColor) (hc : IsTimeSimple c)
    {q : Bool × MatchingPoint} (hq : q ∈ positiveEvents c)
    (ht : ENNReal.ofReal q.2.1 = firstPositiveTime c) : firstPositiveEvent c = q := by
  have hfinite : firstPositiveTime c ≠ ∞ := ht.symm ▸ ENNReal.ofReal_ne_top
  have hs := firstPositiveEvent_spec c hfinite
  apply hc.2 _ _ hs.1.2 hq.2
  have heq := hs.2.trans ht.symm
  exact le_antisymm ((ENNReal.ofReal_le_ofReal_iff hq.1.le).mp heq.le)
    ((ENNReal.ofReal_le_ofReal_iff hs.1.1.le).mp heq.ge)

/-- Before the first positive time every color has zero actual counting measure. -/
theorem countingMeasure_restrict_eq_zero_before_firstPositiveTime
    (c : TwoColor) (b : Bool) {t : ℝ}
    (ht : ENNReal.ofReal t < firstPositiveTime c) :
    (countingMeasure (c b)).restrict (spatialIoc 0 t) = 0 := by
  apply Measure.restrict_eq_zero.mpr
  apply (countingMeasure_eq_zero_iff (c b) (measurableSet_spatialIoc 0 t)).mpr
  intro p hp
  by_contra hm
  have hfirst := firstPositiveTime_le_of_mem c (q := (b, p)) ⟨hp.1, hm⟩
  exact (not_lt_of_ge (hfirst.trans (ENNReal.ofReal_le_ofReal hp.2))) ht

theorem spatialCount_eq_zero_before_firstPositiveTime (c : TwoColor) (b : Bool)
    {t : ℝ} (ht : ENNReal.ofReal t < firstPositiveTime c) :
    spatialCount (c b) 0 t = 0 := by
  have hz := Measure.restrict_eq_zero.mp
    (countingMeasure_restrict_eq_zero_before_firstPositiveTime c b ht)
  simp [spatialCount, Measure.real, hz]

/-- The entire strict pre-first-event region has zero actual counting measure. This also
covers an infinite first time, without converting infinity to a real endpoint. -/
theorem countingMeasure_restrict_lt_firstPositiveTime (c : TwoColor) (b : Bool) :
    (countingMeasure (c b)).restrict
      {p : MatchingPoint | 0 < p.1 ∧ ENNReal.ofReal p.1 < firstPositiveTime c} = 0 := by
  apply Measure.restrict_eq_zero.mpr
  apply (countingMeasure_eq_zero_iff (c b)
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst.ennreal_ofReal measurable_const))).mpr
  intro p hp
  by_contra hm
  exact (not_lt_of_ge (firstPositiveTime_le_of_mem c (q := (b, p)) ⟨hp.1, hm⟩)) hp.2

private theorem countingMeasure_restrict_eq_dirac_of_unique
    (c : LocalConfiguration matchingPointBase) {s : Set MatchingPoint}
    (hs : MeasurableSet s) {p : MatchingPoint} (hp : p ∈ s)
    (hm : multiplicity c p = 1)
    (hunique : ∀ q ∈ s, multiplicity c q ≠ 0 → q = p) :
    (countingMeasure c).restrict s = Measure.dirac p := by
  have hz : (countingMeasure c).restrict (s \ {p}) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    apply (countingMeasure_eq_zero_iff c (hs.diff (measurableSet_singleton p))).mpr
    intro q hq
    by_contra h
    exact hq.2 (hunique q hq.1 h)
  have heq : s = {p} ∪ (s \ {p}) := by
    ext q
    simp only [mem_union, mem_singleton_iff, mem_sdiff]
    constructor
    · intro hq
      by_cases h : q = p
      · exact Or.inl h
      · exact Or.inr ⟨hq, h⟩
    · rintro (rfl | ⟨hq, _⟩)
      · exact hp
      · exact hq
  rw [heq, Measure.restrict_union (disjoint_sdiff_right)
    (hs.diff (measurableSet_singleton p)), hz, add_zero, Measure.restrict_singleton,
    countingMeasure_singleton, hm]
  simp

private theorem firstPositiveEvent_eq_of_mem_stoppedWindow
    (c : TwoColor) (hc : IsTimeSimple c) (b : Bool) (t : ℝ)
    {p : MatchingPoint}
    (hp : p ∈ spatialIoc 0 (min (ENNReal.ofReal t) (firstPositiveTime c)).toReal)
    (hm : multiplicity (c b) p ≠ 0) :
    firstPositiveTime c ≤ ENNReal.ofReal t ∧ firstPositiveEvent c = (b, p) := by
  have hfirst := firstPositiveTime_le_of_mem c (q := (b, p)) ⟨hp.1, hm⟩
  have hmin : min (ENNReal.ofReal t) (firstPositiveTime c) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hptime : ENNReal.ofReal p.1 ≤ min (ENNReal.ofReal t) (firstPositiveTime c) := by
    have h := ENNReal.ofReal_le_ofReal hp.2
    rwa [ENNReal.ofReal_toReal hmin] at h
  refine ⟨hfirst.trans (hptime.trans (min_le_left _ _)), ?_⟩
  exact firstPositiveEvent_eq_of_time c hc ⟨hp.1, hm⟩
    (le_antisymm (hptime.trans (min_le_right _ _)) hfirst)

/-- Stopping either actual counting measure at the first positive event retains precisely
its selected point, when that color arrives by the observation time. -/
theorem countingMeasure_restrict_firstPositiveTime (c : TwoColor) (hc : IsTimeSimple c)
    (b : Bool) (t : ℝ) :
    (countingMeasure (c b)).restrict
        (spatialIoc 0 (min (ENNReal.ofReal t) (firstPositiveTime c)).toReal) =
      if firstPositiveTime c ≤ ENNReal.ofReal t ∧ (firstPositiveEvent c).1 = b
        then Measure.dirac (firstPositiveEvent c).2 else 0 := by
  by_cases h : firstPositiveTime c ≤ ENNReal.ofReal t ∧ (firstPositiveEvent c).1 = b
  · rw [ite_eq_left h]
    have hfinite : firstPositiveTime c ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.1
    have hspec := firstPositiveEvent_spec c hfinite
    apply countingMeasure_restrict_eq_dirac_of_unique (c b) (measurableSet_spatialIoc _ _)
    · change 0 < (firstPositiveEvent c).2.1 ∧
        (firstPositiveEvent c).2.1 ≤ (min (ENNReal.ofReal t) (firstPositiveTime c)).toReal
      rw [min_eq_right h.1, ← hspec.2, ENNReal.toReal_ofReal hspec.1.1.le]
      exact ⟨hspec.1.1, le_rfl⟩
    · rw [← h.2]
      exact hc.1 _ hspec.1.2
    · intro q hq hq'
      exact (congrArg Prod.snd
        (firstPositiveEvent_eq_of_mem_stoppedWindow c hc b t hq hq').2).symm
  · rw [ite_eq_right h]
    apply Measure.restrict_eq_zero.mpr
    apply (countingMeasure_eq_zero_iff (c b) (measurableSet_spatialIoc _ _)).mpr
    intro p hp
    by_contra hm
    have hfirst := firstPositiveEvent_eq_of_mem_stoppedWindow c hc b t hp hm
    exact h ⟨hfirst.1, congrArg Prod.fst hfirst.2⟩

end OTSelector.PointProcess.LocalConfiguration
