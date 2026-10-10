import OTSelector.Feedback.FiniteHistoryFiber

/-!
# Measurability of finite-history fibres

For a fixed terminal state, the revealed-point equalities and the remaining-region constraints are
finite intersections of measurable conditions in the sample variable.  This file records those
measurability facts separately from the deterministic fibre identity.  In particular, no singleton
fibre is treated as a positive-measure atom.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

private theorem measurable_sourcePoint_fixed (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.sourcePoint i) :=
  (FiniteSample.measurable_sourceHeight i).prodMk (FiniteSample.measurable_sourceMark i)

private theorem measurable_targetPoint_fixed (j : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.targetPoint j) :=
  (FiniteSample.measurable_targetHeight j).prodMk (FiniteSample.measurable_targetMark j)

private theorem measurableSet_sourcePoint_eq (reference : FiniteSample n) (i : Fin n) :
    MeasurableSet {sample : FiniteSample n |
      reference.sourcePoint i = sample.sourcePoint i} := by
  exact measurableSet_eq_fun measurable_const (measurable_sourcePoint_fixed i)

private theorem measurableSet_targetPoint_eq (reference : FiniteSample n) (j : Fin n) :
    MeasurableSet {sample : FiniteSample n |
      reference.targetPoint j = sample.targetPoint j} := by
  exact measurableSet_eq_fun measurable_const (measurable_targetPoint_fixed j)

private theorem measurableSet_sourceRemainingMembership
    (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) :
    MeasurableSet {sample : FiniteSample n |
      rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
        sourceRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x} := by
  have hraw : MeasurableSet (sourceRawRemainingSet n state.p state.x) :=
    (isOpen_sourceRawRemainingSet n state.p state.x).measurableSet
  have hpoint : MeasurableSet {sample : FiniteSample n |
      sample.sourcePoint i ∈ sourceRawRemainingSet n state.p state.x} :=
    (measurable_sourcePoint_fixed i) hraw
  have hset :
      {sample : FiniteSample n |
          rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
            sourceRemainingSet (n : ℝ)
              (segmentCurve state.x state.p (state.slope lam)) state.x} =
        {sample : FiniteSample n |
          sample.sourcePoint i ∈ sourceRawRemainingSet n state.p state.x} := by
    ext sample
    exact (mem_sourceRawRemainingSet_iff sample state lam i).symm
  rw [hset]
  exact hpoint

private theorem measurableSet_targetRemainingMembership
    (lam : ℝ) (state : FeedbackStepState n) (j : Fin n) :
    MeasurableSet {sample : FiniteSample n |
      rankStripMap (n : ℝ) (sample.targetPoint j) ∈
        targetRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x} := by
  have hraw : MeasurableSet (targetRawRemainingSet n state.p state.x) :=
    (isOpen_targetRawRemainingSet n state.p state.x).measurableSet
  have hpoint : MeasurableSet {sample : FiniteSample n |
      sample.targetPoint j ∈ targetRawRemainingSet n state.p state.x} :=
    (measurable_targetPoint_fixed j) hraw
  have hset :
      {sample : FiniteSample n |
          rankStripMap (n : ℝ) (sample.targetPoint j) ∈
            targetRemainingSet (n : ℝ)
              (segmentCurve state.x state.p (state.slope lam)) state.x} =
        {sample : FiniteSample n |
          sample.targetPoint j ∈ targetRawRemainingSet n state.p state.x} := by
    ext sample
    exact (mem_targetRawRemainingSet_iff sample state lam j).symm
  rw [hset]
  exact hpoint

/-! ## Fixed-state revealed-point and remaining-region events -/

/-- Agreement with a fixed terminal state's revealed labelled points is measurable in the sample. -/
theorem measurableSet_agreesOnStateSeen
    (terminal : FeedbackStepState n) (reference : FiniteSample n) :
    MeasurableSet {sample : FiniteSample n |
      AgreesOnStateSeen terminal reference sample} := by
  classical
  have hsource (i : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        i ∈ terminal.seenSource → reference.sourcePoint i = sample.sourcePoint i} := by
    by_cases hi : i ∈ terminal.seenSource
    · simpa [hi] using measurableSet_sourcePoint_eq reference i
    · simp [hi]
  have htarget (j : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        j ∈ terminal.seenTarget → reference.targetPoint j = sample.targetPoint j} := by
    by_cases hj : j ∈ terminal.seenTarget
    · simpa [hj] using measurableSet_targetPoint_eq reference j
    · simp [hj]
  have hsource_all : MeasurableSet {sample : FiniteSample n |
      ∀ i, i ∈ terminal.seenSource → reference.sourcePoint i = sample.sourcePoint i} := by
    have hset :
        {sample : FiniteSample n |
            ∀ i, i ∈ terminal.seenSource → reference.sourcePoint i = sample.sourcePoint i} =
          ⋂ i : Fin n, {sample : FiniteSample n |
            i ∈ terminal.seenSource → reference.sourcePoint i = sample.sourcePoint i} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter hsource
  have htarget_all : MeasurableSet {sample : FiniteSample n |
      ∀ j, j ∈ terminal.seenTarget → reference.targetPoint j = sample.targetPoint j} := by
    have hset :
        {sample : FiniteSample n |
            ∀ j, j ∈ terminal.seenTarget → reference.targetPoint j = sample.targetPoint j} =
          ⋂ j : Fin n, {sample : FiniteSample n |
            j ∈ terminal.seenTarget → reference.targetPoint j = sample.targetPoint j} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter htarget
  change MeasurableSet ({sample : FiniteSample n |
      ∀ i, i ∈ terminal.seenSource → reference.sourcePoint i = sample.sourcePoint i} ∩
    {sample : FiniteSample n |
      ∀ j, j ∈ terminal.seenTarget → reference.targetPoint j = sample.targetPoint j})
  exact hsource_all.inter htarget_all

/-- The fixed-state source and target remaining-region constraints are measurable in the sample. -/
theorem measurableSet_liesInStateRemaining
    (lam : ℝ) (terminal : FeedbackStepState n) :
    MeasurableSet {sample : FiniteSample n |
      LiesInStateRemaining lam terminal sample} := by
  classical
  have hsource (i : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        i ∉ terminal.seenSource →
          rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
            sourceRemainingSet (n : ℝ)
              (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
    by_cases hi : i ∈ terminal.seenSource
    · simp [hi]
    · have hmem := measurableSet_sourceRemainingMembership lam terminal i
      have hset :
          {sample : FiniteSample n |
              i ∉ terminal.seenSource →
                rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
                  sourceRemainingSet (n : ℝ)
                    (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} =
            {sample : FiniteSample n |
              rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
                sourceRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
        ext sample
        simp [hi]
      rw [hset]
      exact hmem
  have htarget (j : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        j ∉ terminal.seenTarget →
          rankStripMap (n : ℝ) (sample.targetPoint j) ∈
            targetRemainingSet (n : ℝ)
              (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
    by_cases hj : j ∈ terminal.seenTarget
    · simp [hj]
    · have hmem := measurableSet_targetRemainingMembership lam terminal j
      have hset :
          {sample : FiniteSample n |
              j ∉ terminal.seenTarget →
                rankStripMap (n : ℝ) (sample.targetPoint j) ∈
                  targetRemainingSet (n : ℝ)
                    (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} =
            {sample : FiniteSample n |
              rankStripMap (n : ℝ) (sample.targetPoint j) ∈
                targetRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
        ext sample
        simp [hj]
      rw [hset]
      exact hmem
  have hsource_all : MeasurableSet {sample : FiniteSample n |
      ∀ i, i ∉ terminal.seenSource →
        rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
          sourceRemainingSet (n : ℝ)
            (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
    have hset :
        {sample : FiniteSample n |
            ∀ i, i ∉ terminal.seenSource →
              rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
                sourceRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} =
          ⋂ i : Fin n, {sample : FiniteSample n |
            i ∉ terminal.seenSource →
              rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
                sourceRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter hsource
  have htarget_all : MeasurableSet {sample : FiniteSample n |
      ∀ j, j ∉ terminal.seenTarget →
        rankStripMap (n : ℝ) (sample.targetPoint j) ∈
          targetRemainingSet (n : ℝ)
            (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
    have hset :
        {sample : FiniteSample n |
            ∀ j, j ∉ terminal.seenTarget →
              rankStripMap (n : ℝ) (sample.targetPoint j) ∈
                targetRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} =
          ⋂ j : Fin n, {sample : FiniteSample n |
            j ∉ terminal.seenTarget →
              rankStripMap (n : ℝ) (sample.targetPoint j) ∈
                targetRemainingSet (n : ℝ)
                  (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter htarget
  change MeasurableSet ({sample : FiniteSample n |
      ∀ i, i ∉ terminal.seenSource →
        rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
          sourceRemainingSet (n : ℝ)
            (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x} ∩
    {sample : FiniteSample n |
      ∀ j, j ∉ terminal.seenTarget →
        rankStripMap (n : ℝ) (sample.targetPoint j) ∈
          targetRemainingSet (n : ℝ)
            (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x})
  exact hsource_all.inter htarget_all

/-! ## Fixed-history realization events -/

private theorem measurableSet_labelStepRealizes
    (lam : ℝ) (stateFun : FiniteSample n → FeedbackStepState n)
    (hstate : Measurable stateFun) (label : FeedbackLabel n) :
    MeasurableSet {sample : FiniteSample n |
      FiniteSample.labelStepRealizes sample lam (stateFun sample) label} := by
  have hpair : Measurable fun sample : FiniteSample n ↦ (sample, stateFun sample) :=
    measurable_id.prodMk hstate
  have hsource_mem (i : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        i ∈ (stateFun sample).newSource sample lam} := by
    have h := hpair (FiniteSample.measurableSet_mem_newSource lam i)
    simpa using h
  have htarget_mem (j : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        j ∈ (stateFun sample).newTarget sample lam} := by
    have h := hpair (FiniteSample.measurableSet_mem_newTarget lam j)
    simpa using h
  have hsource_eq (s : Finset (Fin n)) :
      MeasurableSet {sample : FiniteSample n |
        (stateFun sample).newSource sample lam = s} :=
    FiniteSample.measurableSet_finset_eq hsource_mem s
  have htarget_eq (t : Finset (Fin n)) :
      MeasurableSet {sample : FiniteSample n |
        (stateFun sample).newTarget sample lam = t} :=
    FiniteSample.measurableSet_finset_eq htarget_mem t
  cases label with
  | inl i =>
      change MeasurableSet ({sample : FiniteSample n |
        (stateFun sample).newSource sample lam = {i}} ∩
        {sample : FiniteSample n |
          (stateFun sample).newTarget sample lam = ∅})
      exact (hsource_eq {i}).inter (htarget_eq ∅)
  | inr j =>
      change MeasurableSet ({sample : FiniteSample n |
        (stateFun sample).newSource sample lam = ∅} ∩
        {sample : FiniteSample n |
          (stateFun sample).newTarget sample lam = {j}})
      exact (hsource_eq ∅).inter (htarget_eq {j})

/-- Realization of a fixed finite forced history is measurable for every measurable state map. -/
theorem measurableSet_forcedHistoryRealizes
    (lam : ℝ) (stateFun : FiniteSample n → FeedbackStepState n)
    (hstate : Measurable stateFun) (history : List (FeedbackLabel n)) :
    MeasurableSet {sample : FiniteSample n |
      FiniteSample.ForcedHistoryRealizes sample lam (stateFun sample) history} := by
  induction history generalizing stateFun with
  | nil =>
      simp [FiniteSample.ForcedHistoryRealizes]
  | cons label history ih =>
      let next : FiniteSample n → FeedbackStepState n :=
        fun sample ↦ (stateFun sample).forcedLabelStep sample lam label
      have hpair : Measurable fun sample : FiniteSample n ↦ (sample, stateFun sample) :=
        measurable_id.prodMk hstate
      have hnext : Measurable next := by
        exact (FeedbackStepState.measurable_forcedLabelStep lam label).comp hpair
      have hhead := measurableSet_labelStepRealizes lam stateFun hstate label
      have htail := ih (stateFun := next) hnext
      have hset :
          {sample : FiniteSample n |
              FiniteSample.ForcedHistoryRealizes sample lam
                (stateFun sample) (label :: history)} =
            {sample : FiniteSample n |
              FiniteSample.labelStepRealizes sample lam (stateFun sample) label} ∩
              {sample : FiniteSample n |
                FiniteSample.ForcedHistoryRealizes sample lam (next sample) history} := by
        ext sample
        simp [FiniteSample.ForcedHistoryRealizes, next]
      rw [hset]
      exact hhead.inter htail

/-! ## The full fixed-history branch and fibre events -/

/-- A fixed initial pattern and forced history define a measurable branch event. -/
theorem measurableSet_historyBranch
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    MeasurableSet {sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} := by
  have hinit : Measurable fun sample : FiniteSample n ↦
      sample.initialFeedbackState x0 p0 :=
    FiniteSample.measurable_initialFeedbackState x0 p0
  have hpack : Measurable fun sample : FiniteSample n ↦
      FeedbackStepState.pack (sample.initialFeedbackState x0 p0) :=
    FeedbackStepState.measurable_pack.comp hinit
  have hpack_eq : MeasurableSet {sample : FiniteSample n |
      FeedbackStepState.pack (sample.initialFeedbackState x0 p0) =
        FeedbackStepState.pack
          (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)} :=
    measurableSet_eq_fun hpack measurable_const
  have hinit_eq : MeasurableSet {sample : FiniteSample n |
      sample.initialFeedbackState x0 p0 =
        FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern} := by
    have hset :
        {sample : FiniteSample n |
            sample.initialFeedbackState x0 p0 =
              FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern} =
          {sample : FiniteSample n |
            FeedbackStepState.pack (sample.initialFeedbackState x0 p0) =
              FeedbackStepState.pack
                (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)} := by
      ext sample
      constructor
      · intro h
        change FeedbackStepState.pack (sample.initialFeedbackState x0 p0) =
          FeedbackStepState.pack
            (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)
        exact congrArg FeedbackStepState.pack h
      · intro h
        change FeedbackStepState.pack (sample.initialFeedbackState x0 p0) =
          FeedbackStepState.pack
            (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) at h
        exact FeedbackStepState.packEquiv.injective h
    rw [hset]
    exact hpack_eq
  have hforced := measurableSet_forcedHistoryRealizes lam
    (fun _ : FiniteSample n ↦
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)
    measurable_const history
  change MeasurableSet ({sample : FiniteSample n |
      sample.initialFeedbackState x0 p0 =
        FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern} ∩
    {sample : FiniteSample n |
      FiniteSample.ForcedHistoryRealizes sample lam
        (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history})
  exact hinit_eq.inter hforced

/-- A fibre over fixed reference data and a fixed labelled history is measurable in the sample. -/
theorem measurableSet_finiteHistoryFibre
    (reference : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    MeasurableSet {sample : FiniteSample n |
      FiniteHistoryFibre reference sample lam x0 p0 sourcePattern targetPattern history} := by
  unfold FiniteHistoryFibre
  dsimp only
  exact (measurableSet_agreesOnStateSeen
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) reference).inter
    (measurableSet_liesInStateRemaining lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history))

end OTSelector
