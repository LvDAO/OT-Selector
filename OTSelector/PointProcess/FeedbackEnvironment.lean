import OTSelector.PointProcess.MatchingSceneReroot

/-!
# The actual marked feedback environment carrier

An environment stores its two point configurations and its normalized graph and current, with
no matching edges. Rerooting moves both point configurations and the graph and updates the
integer current by the actual source-minus-target count between the two cuts.
-/

open MeasureTheory Set Function

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.PointProcess

@[ext]
structure FeedbackEnvironment where
  source : LocalConfiguration matchingPointBase
  target : LocalConfiguration matchingPointBase
  path : FeedbackPath

namespace FeedbackEnvironment

abbrev Coordinates := LocalConfiguration matchingPointBase ×
  LocalConfiguration matchingPointBase × GraphHeight × ℤ

def equivCoordinates : FeedbackEnvironment ≃ Coordinates where
  toFun e := (e.source, e.target, e.path.graphHeight, e.path.rootCurrent)
  invFun p := ⟨p.1, p.2.1, ⟨p.2.2.1, p.2.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instMeasurableSpace : MeasurableSpace FeedbackEnvironment :=
  MeasurableSpace.comap equivCoordinates inferInstance

def measurableEquivCoordinates : FeedbackEnvironment ≃ᵐ Coordinates where
  toEquiv := equivCoordinates
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    rw [measurable_comap_iff]
    simpa using (measurable_id : Measurable (id : Coordinates → Coordinates))

noncomputable instance instStandardBorelSpace : StandardBorelSpace FeedbackEnvironment := by
  let _ := upgradeStandardBorel Coordinates
  let _ : TopologicalSpace FeedbackEnvironment :=
    TopologicalSpace.induced measurableEquivCoordinates inferInstance
  let _ : PolishSpace FeedbackEnvironment := measurableEquivCoordinates.toEquiv.polishSpace_induced
  let _ : BorelSpace FeedbackEnvironment :=
    measurableEquivCoordinates.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

theorem measurable_source : Measurable (source : FeedbackEnvironment → _) :=
  measurableEquivCoordinates.measurable.fst

theorem measurable_target : Measurable (target : FeedbackEnvironment → _) :=
  measurableEquivCoordinates.measurable.snd.fst

theorem measurable_graphHeight : Measurable (fun e : FeedbackEnvironment ↦ e.path.graphHeight) :=
  measurableEquivCoordinates.measurable.snd.snd.fst

theorem measurable_rootCurrent : Measurable (fun e : FeedbackEnvironment ↦ e.path.rootCurrent) :=
  measurableEquivCoordinates.measurable.snd.snd.snd

/-- Measurability of an actual environment is checked on the two configurations and path data. -/
theorem measurable_mk {Ω : Type*} [MeasurableSpace Ω]
    {s t : Ω → LocalConfiguration matchingPointBase} {g : Ω → GraphHeight} {k : Ω → ℤ}
    (hs : Measurable s) (ht : Measurable t) (hg : Measurable g) (hk : Measurable k) :
    Measurable (fun ω ↦ (⟨s ω, t ω, ⟨g ω, k ω⟩⟩ : FeedbackEnvironment)) :=
  measurableEquivCoordinates.symm.measurable.comp (hs.prodMk (ht.prodMk (hg.prodMk hk)))

/-- Integer current increments are read from the actual two counting configurations. -/
noncomputable def currentIncrement (e : FeedbackEnvironment) (x y : ℝ) : ℤ :=
  LocalConfiguration.orientedCount e.source x y - LocalConfiguration.orientedCount e.target x y

theorem currentIncrement_add (e : FeedbackEnvironment) :
    FeedbackPath.IsAdditiveIntegerIncrement e.currentIncrement := by
  intro x y z
  simp only [currentIncrement, LocalConfiguration.orientedCount_add _ x y z]
  ring

/-- View the actual environment from spatial location `a`. -/
noncomputable def reroot (a : ℝ) (e : FeedbackEnvironment) : FeedbackEnvironment where
  source := LocalConfiguration.reroot a e.source
  target := LocalConfiguration.reroot a e.target
  path := FeedbackPath.rerootWithIncrement e.currentIncrement a e.path

theorem currentIncrement_reroot (e : FeedbackEnvironment) (a x y : ℝ) :
    (reroot a e).currentIncrement x y = e.currentIncrement (x + a) (y + a) := by
  simp only [currentIncrement, reroot, LocalConfiguration.orientedCount_reroot]

@[simp]
theorem reroot_zero (e : FeedbackEnvironment) : reroot 0 e = e := by
  apply FeedbackEnvironment.ext
  · exact LocalConfiguration.reroot_zero _
  · exact LocalConfiguration.reroot_zero _
  · exact FeedbackPath.rerootWithIncrement_zero e.currentIncrement_add e.path

theorem reroot_add (a b : ℝ) (e : FeedbackEnvironment) :
    reroot b (reroot a e) = reroot (a + b) e := by
  apply FeedbackEnvironment.ext
  · exact LocalConfiguration.reroot_add a b e.source
  · exact LocalConfiguration.reroot_add a b e.target
  · change FeedbackPath.rerootWithIncrement (reroot a e).currentIncrement b
      (FeedbackPath.rerootWithIncrement e.currentIncrement a e.path) = _
    have hincr : (reroot a e).currentIncrement =
        FeedbackPath.shiftIncrement a e.currentIncrement := by
      funext x y
      exact currentIncrement_reroot e a x y
    rw [hincr]
    exact FeedbackPath.rerootWithIncrement_add e.currentIncrement_add a b e.path

/-- The real action has the convention that positive displacement moves the observation root. -/
noncomputable instance instAddAction : AddAction ℝ FeedbackEnvironment where
  vadd := reroot
  zero_vadd := reroot_zero
  add_vadd a b e := by
    change reroot (a + b) e = reroot a (reroot b e)
    rw [reroot_add, add_comm b a]

private theorem measurable_source_reroot :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦ LocalConfiguration.reroot p.1 p.2.source) :=
  LocalConfiguration.measurable_uncurry_reroot.comp
    (f := fun p : ℝ × FeedbackEnvironment ↦ (p.1, p.2.source))
    (measurable_fst.prodMk (measurable_source.comp measurable_snd))

private theorem measurable_target_reroot :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦ LocalConfiguration.reroot p.1 p.2.target) :=
  LocalConfiguration.measurable_uncurry_reroot.comp
    (f := fun p : ℝ × FeedbackEnvironment ↦ (p.1, p.2.target))
    (measurable_fst.prodMk (measurable_target.comp measurable_snd))

private theorem measurable_height_reroot :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦ p.2.path.graphHeight.reroot p.1) :=
  GraphHeight.continuous_uncurry_reroot.measurable.comp
    (f := fun p : ℝ × FeedbackEnvironment ↦ (p.1, p.2.path.graphHeight))
    (measurable_fst.prodMk (measurable_graphHeight.comp measurable_snd))

private theorem measurable_source_currentIncrement :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦
      LocalConfiguration.orientedCount p.2.source 0 p.1) :=
  LocalConfiguration.measurable_orientedCount.comp
    (f := fun p : ℝ × FeedbackEnvironment ↦ ((0, p.1), p.2.source))
    ((measurable_const.prodMk measurable_fst).prodMk (measurable_source.comp measurable_snd))

private theorem measurable_target_currentIncrement :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦
      LocalConfiguration.orientedCount p.2.target 0 p.1) :=
  LocalConfiguration.measurable_orientedCount.comp
    (f := fun p : ℝ × FeedbackEnvironment ↦ ((0, p.1), p.2.target))
    ((measurable_const.prodMk measurable_fst).prodMk (measurable_target.comp measurable_snd))

/-- Joint measurability includes the genuine integer count update at the moving cut. -/
theorem measurable_uncurry_reroot :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦ reroot p.1 p.2) :=
  measurable_mk measurable_source_reroot measurable_target_reroot measurable_height_reroot
    ((measurable_rootCurrent.comp measurable_snd).add
      (measurable_source_currentIncrement.sub measurable_target_currentIncrement))

end FeedbackEnvironment
end OTSelector.PointProcess
