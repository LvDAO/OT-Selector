import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Order.Lattice
import OTSelector.Basic.FiniteSampleLaw
import OTSelector.Feedback.FeedbackCurve
import OTSelector.Feedback.FeedbackGeneric

/-!
# Measurability of the finite feedback recursion

`FeedbackStepState` is encoded as a finite Borel product.  Membership of each label in the
seen sets is a closed inequality, so the recursive state and the no-tie event are measurable
functions of the canonical sample.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

variable {n : ℕ}

namespace FeedbackStepState

/-- Encoding of a computational state as a Borel product. -/
def pack (state : FeedbackStepState n) :
    ℝ × ℝ × ℤ × Finset (Fin n) × Finset (Fin n) :=
  (state.x, state.p, state.current, state.seenSource, state.seenTarget)

def unpack :
    ℝ × ℝ × ℤ × Finset (Fin n) × Finset (Fin n) → FeedbackStepState n
  | (x, p, current, seenSource, seenTarget) =>
    { x, p, current, seenSource, seenTarget }

@[simp] theorem unpack_pack (state : FeedbackStepState n) :
    unpack (pack state) = state :=
  rfl

@[simp] theorem pack_unpack (z : ℝ × ℝ × ℤ × Finset (Fin n) × Finset (Fin n)) :
    pack (unpack z) = z := by
  rcases z with ⟨x, p, current, seenSource, seenTarget⟩
  rfl

def packEquiv : FeedbackStepState n ≃ ℝ × ℝ × ℤ × Finset (Fin n) × Finset (Fin n) where
  toFun := pack
  invFun := unpack
  left_inv := unpack_pack
  right_inv := pack_unpack

noncomputable instance instMeasurableSpace : MeasurableSpace (FeedbackStepState n) :=
  MeasurableSpace.comap pack inferInstance

theorem measurable_pack : Measurable (pack : FeedbackStepState n → _) :=
  comap_measurable _

theorem measurable_unpack : Measurable (unpack : _ → FeedbackStepState n) := by
  rw [measurable_comap_iff]
  convert measurable_id using 1
  funext z
  exact pack_unpack z

@[fun_prop] theorem measurable_x : Measurable fun s : FeedbackStepState n ↦ s.x :=
  measurable_fst.comp measurable_pack

@[fun_prop] theorem measurable_p : Measurable fun s : FeedbackStepState n ↦ s.p :=
  (measurable_fst.comp measurable_snd).comp measurable_pack

@[fun_prop] theorem measurable_current : Measurable fun s : FeedbackStepState n ↦ s.current :=
  (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp measurable_pack

@[fun_prop] theorem measurable_seenSource :
    Measurable fun s : FeedbackStepState n ↦ s.seenSource :=
  (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).comp
    measurable_pack

@[fun_prop] theorem measurable_seenTarget :
    Measurable fun s : FeedbackStepState n ↦ s.seenTarget :=
  (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).comp
    measurable_pack

@[fun_prop]
theorem measurable_slope (lam : ℝ) :
    Measurable fun s : FeedbackStepState n ↦ s.slope lam := by
  have hcoe : Measurable fun s : FeedbackStepState n ↦ (s.current : ℝ) :=
    (continuous_of_discreteTopology
      (f := fun k : ℤ ↦ (k : ℝ))).measurable.comp measurable_current
  simp only [slope, feedbackSlope]
  exact Measurable.ite (measurableSet_lt measurable_const hcoe) measurable_const
    (Measurable.ite (measurableSet_lt hcoe measurable_const) measurable_const measurable_const)

end FeedbackStepState

namespace FiniteSample

variable {n : ℕ}

theorem measurableSet_finset_eq {Ω : Type*} [MeasurableSpace Ω]
    {s : Ω → Finset (Fin n)} (h : ∀ i, MeasurableSet {ω | i ∈ s ω})
    (t : Finset (Fin n)) : MeasurableSet {ω | s ω = t} := by
  have hset : {ω | s ω = t} = ⋂ i : Fin n, {ω | i ∈ s ω ↔ i ∈ t} := by
    ext ω
    simp [Finset.ext_iff]
  have hiff (i : Fin n) : MeasurableSet {ω | i ∈ s ω ↔ i ∈ t} := by
    by_cases hit : i ∈ t
    · convert h i using 1
      ext ω
      simp [hit]
    · convert (h i).compl using 1
      ext ω
      simp [hit]
  rw [hset]
  exact MeasurableSet.iInter fun i ↦ hiff i

theorem measurable_finset_of_mem {Ω : Type*} [MeasurableSpace Ω]
    {s : Ω → Finset (Fin n)} (h : ∀ i, MeasurableSet {ω | i ∈ s ω}) :
    Measurable s := by
  intro t _
  have hunion : s ⁻¹' t = ⋃ u ∈ t, {ω | s ω = u} := by
    ext ω
    simp
  rw [hunion]
  exact MeasurableSet.biUnion (to_countable t) fun u _ ↦ measurableSet_finset_eq h u

@[fun_prop]
theorem measurable_sourceSlope (i : Fin n) :
    Measurable fun sample : FiniteSample n ↦ sample.sourceSlope i :=
  measurable_const.sub (measurable_subtype_coe.comp (measurable_sourceMark i))

@[fun_prop]
theorem measurable_targetSlope (j : Fin n) :
    Measurable fun sample : FiniteSample n ↦ sample.targetSlope j :=
  measurable_const.add (measurable_subtype_coe.comp (measurable_targetMark j))

theorem measurableSet_mem_initialSeenSource (x0 p0 : ℝ) (i : Fin n) :
    MeasurableSet {sample : FiniteSample n | i ∈ sample.initialSeenSource x0 p0} := by
  have hset :
      {sample : FiniteSample n | i ∈ sample.initialSeenSource x0 p0} =
        {sample | (n : ℝ) * (sample.sourceHeight i : ℝ) +
          sample.sourceSlope i * p0 ≤ x0} := by
    ext sample
    simp [initialSeenSource]
  rw [hset]
  exact measurableSet_le
    ((measurable_const.mul (measurable_subtype_coe.comp (measurable_sourceHeight i))).add
      ((measurable_sourceSlope i).mul measurable_const))
    measurable_const

theorem measurableSet_mem_initialSeenTarget (x0 p0 : ℝ) (j : Fin n) :
    MeasurableSet {sample : FiniteSample n | j ∈ sample.initialSeenTarget x0 p0} := by
  have hset :
      {sample : FiniteSample n | j ∈ sample.initialSeenTarget x0 p0} =
        {sample | (n : ℝ) * (sample.targetHeight j : ℝ) -
          sample.targetSlope j * p0 ≤ x0} := by
    ext sample
    simp [initialSeenTarget]
  rw [hset]
  exact measurableSet_le
    ((measurable_const.mul (measurable_subtype_coe.comp (measurable_targetHeight j))).sub
      ((measurable_targetSlope j).mul measurable_const))
    measurable_const

@[fun_prop]
theorem measurable_initialSeenSource (x0 p0 : ℝ) :
    Measurable fun sample : FiniteSample n ↦ sample.initialSeenSource x0 p0 :=
  measurable_finset_of_mem fun i ↦ measurableSet_mem_initialSeenSource x0 p0 i

@[fun_prop]
theorem measurable_initialSeenTarget (x0 p0 : ℝ) :
    Measurable fun sample : FiniteSample n ↦ sample.initialSeenTarget x0 p0 :=
  measurable_finset_of_mem fun j ↦ measurableSet_mem_initialSeenTarget x0 p0 j

@[fun_prop]
theorem measurable_initialFeedbackCurrent (x0 p0 : ℝ) :
    Measurable fun sample : FiniteSample n ↦ sample.initialFeedbackCurrent x0 p0 := by
  have hcard : Measurable (Finset.card : Finset (Fin n) → ℕ) :=
    measurable_of_countable _
  have hcoe : Measurable fun k : ℕ ↦ (k : ℤ) :=
    continuous_of_discreteTopology (f := fun k : ℕ ↦ (k : ℤ)) |>.measurable
  simp only [initialFeedbackCurrent]
  exact (hcoe.comp (hcard.comp (measurable_initialSeenSource x0 p0))).sub
    (hcoe.comp (hcard.comp (measurable_initialSeenTarget x0 p0)))

@[fun_prop]
theorem measurable_initialFeedbackState (x0 p0 : ℝ) :
    Measurable fun sample : FiniteSample n ↦ sample.initialFeedbackState x0 p0 := by
  have hpack :
      Measurable fun sample : FiniteSample n ↦
        FeedbackStepState.pack (sample.initialFeedbackState x0 p0) := by
    simp only [initialFeedbackState, FeedbackStepState.pack]
    exact measurable_const.prodMk <|
      measurable_const.prodMk <|
        (measurable_initialFeedbackCurrent x0 p0).prodMk <|
          (measurable_initialSeenSource x0 p0).prodMk (measurable_initialSeenTarget x0 p0)
  have hcomp := FeedbackStepState.measurable_unpack.comp hpack
  simpa [Function.comp_def, FeedbackStepState.unpack_pack] using hcomp

theorem measurable_sourceCoordinate (lam : ℝ) (i : Fin n) :
    Measurable fun p : FiniteSample n × FeedbackStepState n ↦
      p.2.sourceCoordinate p.1 lam i := by
  simp only [FeedbackStepState.sourceCoordinate, sourceSegmentCrossing]
  fun_prop

theorem measurable_targetCoordinate (lam : ℝ) (j : Fin n) :
    Measurable fun p : FiniteSample n × FeedbackStepState n ↦
      p.2.targetCoordinate p.1 lam j := by
  simp only [FeedbackStepState.targetCoordinate, targetSegmentCrossing]
  fun_prop

theorem measurableSet_mem_seenSource (i : Fin n) :
    MeasurableSet {p : FiniteSample n × FeedbackStepState n | i ∈ p.2.seenSource} := by
  have hset : MeasurableSet {S : Finset (Fin n) | i ∈ S} :=
    measurableSet_mem_finset i
  exact (FeedbackStepState.measurable_seenSource.comp measurable_snd) hset

theorem measurableSet_mem_seenTarget (j : Fin n) :
    MeasurableSet {p : FiniteSample n × FeedbackStepState n | j ∈ p.2.seenTarget} := by
  have hset : MeasurableSet {S : Finset (Fin n) | j ∈ S} :=
    measurableSet_mem_finset j
  exact (FeedbackStepState.measurable_seenTarget.comp measurable_snd) hset

/-- Evaluation of a countable family of measurable functions remains measurable. -/
theorem measurable_eval_countable {ι Ω α : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] [MeasurableSpace α]
    {f : ι → Ω → α} (hf : ∀ i, Measurable (f i))
    {g : Ω → ι} (hg : Measurable g) :
    Measurable fun ω ↦ f (g ω) ω := by
  intro t ht
  have hunion :
      (fun ω ↦ f (g ω) ω) ⁻¹' t = ⋃ i, g ⁻¹' {i} ∩ f i ⁻¹' t := by
    ext ω
    simp
  rw [hunion]
  exact MeasurableSet.iUnion fun i ↦ (hg (measurableSet_singleton i)).inter (hf i ht)

/-- Finite `inf'` of measurable functions is measurable. -/
theorem measurable_inf' {ι α Ω : Type*} [SemilatticeInf α]
    [MeasurableSpace α] [MeasurableInf₂ α] [MeasurableSpace Ω]
    {s : Finset ι} {f : ι → Ω → α}
    (hf : ∀ i, Measurable (f i)) (hs : s.Nonempty) :
    Measurable fun ω ↦ s.inf' hs (fun i ↦ f i ω) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro hs
    exact (Finset.not_nonempty_empty hs).elim
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · have hfun :
          (fun ω ↦ (insert a s).inf' (Finset.insert_nonempty a s)
            (fun i ↦ f i ω)) =
            fun ω ↦ f a ω ⊓ s.inf' hs' (fun i ↦ f i ω) := by
        ext ω
        exact Finset.inf'_insert (H := hs') (fun i ↦ f i ω)
      rw [hfun]
      exact (hf a).inf (ih hs')
    · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hsempty
      simpa using hf a

/-- Next coordinate computed as if the seen sets were the given pair. -/
noncomputable def nextCoordinateOfSeen (lam : ℝ) (S T : Finset (Fin n))
    (pair : FiniteSample n × FeedbackStepState n) : ℝ :=
  (FeedbackStepState.mk pair.2.x pair.2.p pair.2.current S T).nextCoordinate pair.1 lam

theorem nextCoordinate_eq_ofSeen (lam : ℝ)
    (pair : FiniteSample n × FeedbackStepState n) :
    pair.2.nextCoordinate pair.1 lam =
      nextCoordinateOfSeen lam pair.2.seenSource pair.2.seenTarget pair := by
  simp [nextCoordinateOfSeen]

noncomputable def unseenIndex (S T : Finset (Fin n)) : Finset (Fin n ⊕ Fin n) :=
  (Finset.univ \ S).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ \ T).map ⟨Sum.inr, Sum.inr_injective⟩

noncomputable def unseenCoord (lam : ℝ) (k : Fin n ⊕ Fin n)
    (pair : FiniteSample n × FeedbackStepState n) : ℝ :=
  match k with
  | .inl i => pair.2.sourceCoordinate pair.1 lam i
  | .inr j => pair.2.targetCoordinate pair.1 lam j

theorem measurable_unseenCoord (lam : ℝ) (k : Fin n ⊕ Fin n) :
    Measurable (unseenCoord lam k) := by
  cases k with
  | inl i => exact measurable_sourceCoordinate lam i
  | inr j => exact measurable_targetCoordinate lam j

theorem unseenIndex_nonempty {S T : Finset (Fin n)}
    (hST : ¬(S = Finset.univ ∧ T = Finset.univ)) :
    (unseenIndex S T).Nonempty := by
  by_contra hnone
  simp only [unseenIndex, Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty,
    Finset.map_eq_empty] at hnone
  have hS : Finset.univ \ S = ∅ := hnone.1
  have hT : Finset.univ \ T = ∅ := hnone.2
  rw [Finset.sdiff_eq_empty_iff_subset] at hS hT
  exact hST ⟨(Finset.univ_subset_iff.mp hS), (Finset.univ_subset_iff.mp hT)⟩

theorem candidates_eq_unseenIndex_image (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.candidates sample lam =
      (unseenIndex state.seenSource state.seenTarget).image
        (fun k ↦ unseenCoord lam k (sample, state)) := by
  classical
  ext z
  simp [FeedbackStepState.candidates, FeedbackStepState.sourceCandidates,
    FeedbackStepState.targetCandidates, unseenIndex, unseenCoord]

theorem nextCoordinateOfSeen_eq_inf' (lam : ℝ) (S T : Finset (Fin n))
    (hST : ¬(S = Finset.univ ∧ T = Finset.univ))
    (pair : FiniteSample n × FeedbackStepState n) :
    nextCoordinateOfSeen lam S T pair =
      (unseenIndex S T).inf' (unseenIndex_nonempty hST)
        (fun k ↦ unseenCoord lam k pair) := by
  classical
  let st := FeedbackStepState.mk pair.2.x pair.2.p pair.2.current S T
  have hne : (st.candidates pair.1 lam).Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro hempty
    exact hST ((st.candidates_eq_empty_iff pair.1 lam).mp hempty)
  have hcoord (k : Fin n ⊕ Fin n) :
      unseenCoord lam k (pair.1, st) = unseenCoord lam k pair := by
    cases k <;> simp [unseenCoord, st, FeedbackStepState.sourceCoordinate,
      FeedbackStepState.targetCoordinate, FeedbackStepState.slope]
  change st.nextCoordinate pair.1 lam = _
  rw [FeedbackStepState.nextCoordinate, dite_eq_left hne]
  rw [Finset.min'_eq_inf']
  have hcand := candidates_eq_unseenIndex_image pair.1 lam st
  simp only [hcand]
  rw [Finset.inf'_image]
  simp [st, hcoord]

theorem measurable_nextCoordinateOfSeen (lam : ℝ) (S T : Finset (Fin n)) :
    Measurable (nextCoordinateOfSeen lam S T) := by
  classical
  by_cases hST : S = Finset.univ ∧ T = Finset.univ
  · have hfun : nextCoordinateOfSeen lam S T = fun pair ↦ pair.2.x := by
      ext pair
      let st := FeedbackStepState.mk pair.2.x pair.2.p pair.2.current S T
      have hempty : st.candidates pair.1 lam = ∅ :=
        (st.candidates_eq_empty_iff pair.1 lam).2 hST
      simp [nextCoordinateOfSeen, FeedbackStepState.nextCoordinate, st, hempty]
    rw [hfun]
    exact FeedbackStepState.measurable_x.comp measurable_snd
  · have hfun :
        nextCoordinateOfSeen lam S T =
          fun pair ↦ (unseenIndex S T).inf' (unseenIndex_nonempty hST)
            (fun k ↦ unseenCoord lam k pair) := by
      ext pair
      exact nextCoordinateOfSeen_eq_inf' lam S T hST pair
    rw [hfun]
    exact measurable_inf' (fun k ↦ measurable_unseenCoord lam k) (unseenIndex_nonempty hST)

theorem measurable_nextCoordinate (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.nextCoordinate pair.1 lam := by
  let seen : FiniteSample n × FeedbackStepState n →
      Finset (Fin n) × Finset (Fin n) :=
    fun pair ↦ (pair.2.seenSource, pair.2.seenTarget)
  have hg : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      (pair.2.seenSource, pair.2.seenTarget) :=
    (FeedbackStepState.measurable_seenSource.comp measurable_snd).prodMk
      (FeedbackStepState.measurable_seenTarget.comp measurable_snd)
  have hseen : Measurable seen := by simpa only [seen] using hg
  have heval : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      nextCoordinateOfSeen lam (seen pair).1 (seen pair).2 pair :=
    measurable_eval_countable
      (ι := Finset (Fin n) × Finset (Fin n))
      (Ω := FiniteSample n × FeedbackStepState n) (α := ℝ)
      (fun ST ↦ measurable_nextCoordinateOfSeen lam ST.1 ST.2) hseen
  have hfun :
      (fun pair : FiniteSample n × FeedbackStepState n ↦
        pair.2.nextCoordinate pair.1 lam) =
      fun pair ↦ nextCoordinateOfSeen lam (seen pair).1 (seen pair).2 pair := by
    funext pair
    exact nextCoordinate_eq_ofSeen lam pair
  rw [hfun]
  exact heval

theorem measurableSet_mem_newSource (lam : ℝ) (i : Fin n) :
    MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
      i ∈ pair.2.newSource pair.1 lam} := by
  have hset :
      {pair : FiniteSample n × FeedbackStepState n |
          i ∈ pair.2.newSource pair.1 lam} =
        {pair | i ∉ pair.2.seenSource ∧
          pair.2.sourceCoordinate pair.1 lam i =
            pair.2.nextCoordinate pair.1 lam} := by
    ext pair
    simp [FeedbackStepState.newSource]
  rw [hset]
  exact (measurableSet_mem_seenSource i).compl.inter
    (measurableSet_eq_fun (measurable_sourceCoordinate lam i)
      (measurable_nextCoordinate lam))

theorem measurableSet_mem_newTarget (lam : ℝ) (j : Fin n) :
    MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
      j ∈ pair.2.newTarget pair.1 lam} := by
  have hset :
      {pair : FiniteSample n × FeedbackStepState n |
          j ∈ pair.2.newTarget pair.1 lam} =
        {pair | j ∉ pair.2.seenTarget ∧
          pair.2.targetCoordinate pair.1 lam j =
            pair.2.nextCoordinate pair.1 lam} := by
    ext pair
    simp [FeedbackStepState.newTarget]
  rw [hset]
  exact (measurableSet_mem_seenTarget j).compl.inter
    (measurableSet_eq_fun (measurable_targetCoordinate lam j)
      (measurable_nextCoordinate lam))

theorem measurable_newSource (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.newSource pair.1 lam :=
  measurable_finset_of_mem fun i ↦ measurableSet_mem_newSource lam i

theorem measurable_newTarget (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.newTarget pair.1 lam :=
  measurable_finset_of_mem fun j ↦ measurableSet_mem_newTarget lam j

theorem measurable_finset_card :
    Measurable (Finset.card : Finset (Fin n) → ℕ) :=
  measurable_of_countable _

theorem measurable_seenSource_union_newSource (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.seenSource ∪ pair.2.newSource pair.1 lam := by
  apply measurable_finset_of_mem
  intro i
  have hset :
      {pair : FiniteSample n × FeedbackStepState n |
          i ∈ pair.2.seenSource ∪ pair.2.newSource pair.1 lam} =
        {pair | i ∈ pair.2.seenSource} ∪
          {pair | i ∈ pair.2.newSource pair.1 lam} := by
    ext pair
    simp
  rw [hset]
  exact (measurableSet_mem_seenSource i).union (measurableSet_mem_newSource lam i)

theorem measurable_seenTarget_union_newTarget (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.seenTarget ∪ pair.2.newTarget pair.1 lam := by
  apply measurable_finset_of_mem
  intro j
  have hset :
      {pair : FiniteSample n × FeedbackStepState n |
          j ∈ pair.2.seenTarget ∪ pair.2.newTarget pair.1 lam} =
        {pair | j ∈ pair.2.seenTarget} ∪
          {pair | j ∈ pair.2.newTarget pair.1 lam} := by
    ext pair
    simp
  rw [hset]
  exact (measurableSet_mem_seenTarget j).union (measurableSet_mem_newTarget lam j)

theorem measurable_step (lam : ℝ) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.step pair.1 lam := by
  let next : FiniteSample n × FeedbackStepState n → ℝ :=
    fun pair ↦ pair.2.nextCoordinate pair.1 lam
  have hnext : Measurable next := measurable_nextCoordinate lam
  have hx : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.x :=
    FeedbackStepState.measurable_x.comp measurable_snd
  have hp : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.p :=
    FeedbackStepState.measurable_p.comp measurable_snd
  have hslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.slope lam :=
    (FeedbackStepState.measurable_slope lam).comp measurable_snd
  have hsegment : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      segmentCurve pair.2.x pair.2.p (pair.2.slope lam) (next pair) := by
    simp only [segmentCurve]
    exact hp.add (hslope.mul (hnext.sub hx))
  have hcurrent : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.current := FeedbackStepState.measurable_current.comp measurable_snd
  have hnatInt : Measurable fun k : ℕ ↦ (k : ℤ) := measurable_of_countable _
  have hsourceCard : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      ((pair.2.newSource pair.1 lam).card : ℤ) :=
    hnatInt.comp (measurable_finset_card.comp (measurable_newSource lam))
  have htargetCard : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      ((pair.2.newTarget pair.1 lam).card : ℤ) :=
    hnatInt.comp (measurable_finset_card.comp (measurable_newTarget lam))
  have hstepCurrent : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.current + (pair.2.newSource pair.1 lam).card -
        (pair.2.newTarget pair.1 lam).card :=
    hcurrent.add hsourceCard |>.sub htargetCard
  have hpack : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      FeedbackStepState.pack (pair.2.step pair.1 lam) := by
    simp only [FeedbackStepState.step, FeedbackStepState.pack]
    exact hnext.prodMk <| hsegment.prodMk <| hstepCurrent.prodMk <|
      (measurable_seenSource_union_newSource lam).prodMk
        (measurable_seenTarget_union_newTarget lam)
  have hcomp := FeedbackStepState.measurable_unpack.comp hpack
  simpa [Function.comp_def, FeedbackStepState.unpack_pack] using hcomp

theorem measurable_feedbackState (lam x0 p0 : ℝ) (m : ℕ) :
    Measurable fun sample : FiniteSample n ↦ feedbackState sample lam x0 p0 m := by
  induction m with
  | zero => exact measurable_initialFeedbackState x0 p0
  | succ m ih =>
      have hpair : Measurable fun sample : FiniteSample n ↦
          (sample, feedbackState sample lam x0 p0 m) :=
        measurable_id.prodMk ih
      (convert (measurable_step lam).comp hpair using 1; rfl)

theorem measurable_feedbackKnot (lam x0 p0 : ℝ) (m : ℕ) :
    Measurable fun sample : FiniteSample n ↦ sample.feedbackKnot lam x0 p0 m :=
  FeedbackStepState.measurable_x.comp (measurable_feedbackState lam x0 p0 m)

theorem measurable_feedbackKnotValue (lam x0 p0 : ℝ) (m : ℕ) :
    Measurable fun sample : FiniteSample n ↦ sample.feedbackKnotValue lam x0 p0 m :=
  FeedbackStepState.measurable_p.comp (measurable_feedbackState lam x0 p0 m)

theorem measurable_feedbackNewLabelCount (lam x0 p0 : ℝ) (m : ℕ) :
    Measurable fun sample : FiniteSample n ↦
      ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card := by
  have hpair : Measurable fun sample : FiniteSample n ↦
      (sample, feedbackState sample lam x0 p0 m) :=
    measurable_id.prodMk (measurable_feedbackState lam x0 p0 m)
  exact (measurable_finset_card.comp ((measurable_newSource lam).comp hpair)).add
    (measurable_finset_card.comp ((measurable_newTarget lam).comp hpair))

theorem measurableSet_noFeedbackTies (lam x0 p0 : ℝ) :
    MeasurableSet {sample : FiniteSample n | sample.NoFeedbackTies lam x0 p0} := by
  have hstep (m : ℕ) : MeasurableSet {sample : FiniteSample n |
      m < 2 * n →
        ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
          ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1} := by
    by_cases hm : m < 2 * n
    · simp only [hm, true_implies]
      exact measurableSet_le (measurable_feedbackNewLabelCount lam x0 p0 m) measurable_const
    · simp [hm]
  have hset : {sample : FiniteSample n | sample.NoFeedbackTies lam x0 p0} =
      ⋂ m : ℕ, {sample | m < 2 * n →
        ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
          ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1} := by
    ext sample
    simp [NoFeedbackTies]
  rw [hset]
  exact MeasurableSet.iInter hstep

theorem measurableSet_feedbackTieEvent (lam x0 p0 : ℝ) :
    MeasurableSet {sample : FiniteSample n | ¬sample.NoFeedbackTies lam x0 p0} :=
  (measurableSet_noFeedbackTies lam x0 p0).compl

end FiniteSample

end OTSelector
