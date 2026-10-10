import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.ContinuousMapZero
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Feedback paths with a normalized graph height

This file replaces unrestricted cocycle and current functions by the coordinates that are needed
for a probability law: a continuous graph height normalized at the origin and one integer current
value at the origin.  Graph increments are derived by subtraction.

Re-rooting the current additionally needs the integer increment across two cuts.  That increment is
an external argument, rather than a stored function-space coordinate.  Its additive law is an
ordinary proposition.  No matching/configuration construction of that increment is asserted here.
-/

open Function Set Topology

namespace OTSelector.PointProcess

/-! ## Normalized graph heights -/

/-- Continuous real graph heights normalized by `g 0 = 0`, with compact-open topology. -/
abbrev GraphHeight := ContinuousMapZero ℝ ℝ

namespace GraphHeight

/-- Forget the normalization and view a graph height as an ordinary continuous map. -/
def toContinuousMap (g : GraphHeight) : C(ℝ, ℝ) := g

@[simp]
theorem toContinuousMap_apply (g : GraphHeight) (x : ℝ) : g.toContinuousMap x = g x :=
  rfl

@[simp]
theorem apply_zero (g : GraphHeight) : g 0 = 0 :=
  map_zero g

/-- The graph cocycle derived from a normalized height. -/
def cocycle (g : GraphHeight) (x y : ℝ) : ℝ :=
  g y - g x

@[simp]
theorem cocycle_self (g : GraphHeight) (x : ℝ) : g.cocycle x x = 0 := by
  simp [cocycle]

@[simp]
theorem cocycle_zero_left (g : GraphHeight) (x : ℝ) : g.cocycle 0 x = g x := by
  simp [cocycle]

/-- Height differences satisfy the additive cocycle identity. -/
theorem cocycle_add (g : GraphHeight) (x y z : ℝ) :
    g.cocycle x z = g.cocycle x y + g.cocycle y z := by
  simp only [cocycle]
  ring

/-- Re-root `g` at the old spatial location `a`.

The new coordinate `x` represents the old coordinate `x + a`; subtracting `g a` restores the
normalization at zero.  In the old `Scene.translate` convention this corresponds to translating a
scene by `-a`.
-/
def reroot (a : ℝ) (g : GraphHeight) : GraphHeight where
  toContinuousMap :=
    ⟨fun x ↦ g (x + a) - g a,
      (map_continuous g).comp (continuous_id.add continuous_const) |>.sub
        ((map_continuous g).comp continuous_const)⟩
  map_zero' := by simp

@[simp]
theorem reroot_apply (a x : ℝ) (g : GraphHeight) : g.reroot a x = g (x + a) - g a :=
  rfl

@[simp]
theorem reroot_zero (g : GraphHeight) : g.reroot 0 = g := by
  ext x
  simp

/-- Successive re-rootings add their old-coordinate displacements. -/
theorem reroot_add (a b : ℝ) (g : GraphHeight) :
    (g.reroot a).reroot b = g.reroot (a + b) := by
  ext x
  simp only [reroot_apply]
  rw [show (x + b) + a = x + (a + b) by ring, show b + a = a + b by ring]
  ring

/-- Re-rooting shifts both endpoints of the derived cocycle. -/
theorem cocycle_reroot (a x y : ℝ) (g : GraphHeight) :
    (g.reroot a).cocycle x y = g.cocycle (x + a) (y + a) := by
  simp [cocycle]

/-- Translate a graph height in the same direction as `Scene.translate`.

Under this convention old points move from `x` to `x + a`, so the new height at `x` reads the
old height at `x - a` and is normalized by the old value at `-a`.
-/
def translate (a : ℝ) (g : GraphHeight) : GraphHeight :=
  g.reroot (-a)

@[simp]
theorem translate_apply (a x : ℝ) (g : GraphHeight) :
    g.translate a x = g (x - a) - g (-a) := by
  simp [translate, sub_eq_add_neg]

@[simp]
theorem translate_zero (g : GraphHeight) : g.translate 0 = g := by
  simp [translate]

/-- Successive height translations follow the existing `Scene.translate` action convention. -/
theorem translate_add (a b : ℝ) (g : GraphHeight) :
    translate a (translate b g) = translate (a + b) g := by
  change (g.reroot (-b)).reroot (-a) = g.reroot (-(a + b))
  rw [reroot_add]
  congr 1
  ring

/-- Translation pulls the derived cocycle back by the same displacement as `Scene.translate`. -/
theorem cocycle_translate (a x y : ℝ) (g : GraphHeight) :
    (g.translate a).cocycle x y = g.cocycle (x - a) (y - a) := by
  simp [translate, sub_eq_add_neg, cocycle_reroot]

/-- Evaluation at a fixed spatial point is continuous. -/
theorem continuous_apply (x : ℝ) : Continuous (fun g : GraphHeight ↦ g x) :=
  continuous_eval_const x

/-- Re-rooting at a fixed spatial point is continuous in compact-open topology. -/
theorem continuous_reroot (a : ℝ) : Continuous (reroot a : GraphHeight → GraphHeight) := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hshift : Continuous (fun p : GraphHeight × ℝ ↦ p.1 (p.2 + a)) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hbase : Continuous (fun p : GraphHeight × ℝ ↦ p.1 a) :=
    (continuous_eval_const a).comp continuous_fst
  exact hshift.sub hbase

/-- Translation by a fixed displacement is continuous in compact-open topology. -/
theorem continuous_translate (a : ℝ) : Continuous (translate a : GraphHeight → GraphHeight) :=
  continuous_reroot (-a)

end GraphHeight

/-! ## Minimal path coordinates -/

/-- A feedback path stores only a normalized continuous graph height and the current at the root. -/
@[ext]
structure FeedbackPath where
  graphHeight : GraphHeight
  rootCurrent : ℤ

namespace FeedbackPath

/-- Coordinate equivalence with the product of graph height and root current. -/
def equivCoordinates : FeedbackPath ≃ GraphHeight × ℤ where
  toFun path := (path.graphHeight, path.rootCurrent)
  invFun coordinates := ⟨coordinates.1, coordinates.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinate map used to transport the product topology. -/
def coordinates (path : FeedbackPath) : GraphHeight × ℤ :=
  equivCoordinates path

/-- Compact-open graph-height topology times the discrete topology on the root current. -/
noncomputable instance instTopologicalSpace : TopologicalSpace FeedbackPath :=
  TopologicalSpace.induced coordinates inferInstance

/-- The coordinate map is a topological embedding. -/
theorem isEmbedding_coordinates : IsEmbedding coordinates where
  eq_induced := rfl
  injective := equivCoordinates.injective

/-- The coordinate map is a closed embedding onto the whole product. -/
theorem isClosedEmbedding_coordinates : IsClosedEmbedding coordinates where
  toIsEmbedding := isEmbedding_coordinates
  isClosed_range := by
    have hsurjective : Surjective coordinates := equivCoordinates.surjective
    rw [hsurjective.range_eq]
    exact isClosed_univ

/-- The normalized graph-height space is Polish in compact-open topology. -/
noncomputable instance instPolishSpaceGraphHeight : PolishSpace GraphHeight :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace

/-- Minimal feedback paths form a Polish space. -/
noncomputable instance instPolishSpace : PolishSpace FeedbackPath :=
  isClosedEmbedding_coordinates.polishSpace

/-- The Borel measurable structure of the Polish path topology. -/
noncomputable instance instMeasurableSpace : MeasurableSpace FeedbackPath :=
  borel FeedbackPath

instance instBorelSpace : BorelSpace FeedbackPath :=
  ⟨rfl⟩

noncomputable instance instStandardBorelSpace : StandardBorelSpace FeedbackPath :=
  inferInstance

/-- The graph-height coordinate is continuous. -/
theorem continuous_graphHeight : Continuous (graphHeight : FeedbackPath → GraphHeight) :=
  continuous_fst.comp isEmbedding_coordinates.continuous

/-- The root-current coordinate is continuous. -/
theorem continuous_rootCurrent : Continuous (rootCurrent : FeedbackPath → ℤ) :=
  continuous_snd.comp isEmbedding_coordinates.continuous

/-- Evaluation of the stored height at a fixed point is continuous. -/
theorem continuous_graphHeight_apply (x : ℝ) :
    Continuous (fun path : FeedbackPath ↦ path.graphHeight x) :=
  (GraphHeight.continuous_apply x).comp continuous_graphHeight

/-- The graph cocycle is derived from the normalized height coordinate. -/
def graphCocycle (path : FeedbackPath) (x y : ℝ) : ℝ :=
  path.graphHeight.cocycle x y

@[simp]
theorem graphCocycle_self (path : FeedbackPath) (x : ℝ) : path.graphCocycle x x = 0 :=
  path.graphHeight.cocycle_self x

@[simp]
theorem graphCocycle_zero_left (path : FeedbackPath) (x : ℝ) :
    path.graphCocycle 0 x = path.graphHeight x :=
  path.graphHeight.cocycle_zero_left x

/-- The derived graph increments satisfy the additive cocycle identity. -/
theorem graphCocycle_add (path : FeedbackPath) (x y z : ℝ) :
    path.graphCocycle x z = path.graphCocycle x y + path.graphCocycle y z :=
  path.graphHeight.cocycle_add x y z

/-! ## Integer-current increments and honest re-rooting -/

/-- An external integer increment between two spatial cuts. -/
abbrev IntegerIncrement := ℝ → ℝ → ℤ

/-- The algebraic law required of a cut-current increment. -/
def IsAdditiveIntegerIncrement (increment : IntegerIncrement) : Prop :=
  ∀ x y z, increment x z = increment x y + increment y z

theorem IsAdditiveIntegerIncrement.self_eq_zero {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (x : ℝ) : increment x x = 0 := by
  have h := hincrement x x x
  omega

theorem IsAdditiveIntegerIncrement.antisymm {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (x y : ℝ) :
    increment y x = -increment x y := by
  have h := hincrement x y x
  rw [hincrement.self_eq_zero] at h
  omega

/-- Current at a cut, derived from the stored root value and an external increment. -/
def currentAt (increment : IntegerIncrement) (path : FeedbackPath) (x : ℝ) : ℤ :=
  path.rootCurrent + increment 0 x

@[simp]
theorem currentAt_zero {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (path : FeedbackPath) :
    currentAt increment path 0 = path.rootCurrent := by
  simp [currentAt, hincrement.self_eq_zero]

/-- Express a fixed increment in coordinates rooted at the old point `a`. -/
def shiftIncrement (a : ℝ) (increment : IntegerIncrement) : IntegerIncrement :=
  fun x y ↦ increment (x + a) (y + a)

@[simp]
theorem shiftIncrement_apply (a x y : ℝ) (increment : IntegerIncrement) :
    shiftIncrement a increment x y = increment (x + a) (y + a) :=
  rfl

/-- Shifting preserves additivity of integer increments. -/
theorem IsAdditiveIntegerIncrement.shift {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (a : ℝ) :
    IsAdditiveIntegerIncrement (shiftIncrement a increment) := by
  intro x y z
  exact hincrement (x + a) (y + a) (z + a)

/-- Re-root a feedback path using an externally supplied integer-current increment. -/
def rerootWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) : FeedbackPath where
  graphHeight := path.graphHeight.reroot a
  rootCurrent := currentAt increment path a

@[simp]
theorem graphHeight_rerootWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) :
    (rerootWithIncrement increment a path).graphHeight = path.graphHeight.reroot a :=
  rfl

@[simp]
theorem rootCurrent_rerootWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) :
    (rerootWithIncrement increment a path).rootCurrent = currentAt increment path a :=
  rfl

/-- Re-rooting shifts both endpoints of the derived real graph cocycle. -/
theorem graphCocycle_rerootWithIncrement (increment : IntegerIncrement) (a x y : ℝ)
    (path : FeedbackPath) :
    (rerootWithIncrement increment a path).graphCocycle x y =
      path.graphCocycle (x + a) (y + a) :=
  path.graphHeight.cocycle_reroot a x y

/-- Translate a path in the same direction as `Scene.translate`, using an external current
increment to update the value at the translated root. -/
def translateWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) : FeedbackPath :=
  rerootWithIncrement increment (-a) path

@[simp]
theorem graphHeight_translateWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) :
    (translateWithIncrement increment a path).graphHeight = path.graphHeight.translate a :=
  rfl

@[simp]
theorem rootCurrent_translateWithIncrement (increment : IntegerIncrement) (a : ℝ)
    (path : FeedbackPath) :
    (translateWithIncrement increment a path).rootCurrent = currentAt increment path (-a) :=
  rfl

/-- Path translation pulls the derived graph cocycle back by the spatial displacement. -/
theorem graphCocycle_translateWithIncrement (increment : IntegerIncrement) (a x y : ℝ)
    (path : FeedbackPath) :
    (translateWithIncrement increment a path).graphCocycle x y =
      path.graphCocycle (x - a) (y - a) := by
  simpa [translateWithIncrement, sub_eq_add_neg] using
    graphCocycle_rerootWithIncrement increment (-a) x y path

/-- Re-rooting at zero is the identity when the integer increment is additive. -/
@[simp]
theorem rerootWithIncrement_zero {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (path : FeedbackPath) :
    rerootWithIncrement increment 0 path = path := by
  apply FeedbackPath.ext
  · exact path.graphHeight.reroot_zero
  · exact currentAt_zero hincrement path

/-- Successive re-rootings compose after shifting the second increment to the first new frame. -/
theorem rerootWithIncrement_add {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (a b : ℝ) (path : FeedbackPath) :
    rerootWithIncrement (shiftIncrement a increment) b
        (rerootWithIncrement increment a path) =
      rerootWithIncrement increment (a + b) path := by
  apply FeedbackPath.ext
  · exact path.graphHeight.reroot_add a b
  · simp only [rootCurrent_rerootWithIncrement, currentAt, shiftIncrement_apply, zero_add]
    rw [show b + a = a + b by ring]
    rw [hincrement 0 a (a + b)]
    omega

/-- Translation at zero is the identity for an additive current increment. -/
@[simp]
theorem translateWithIncrement_zero {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (path : FeedbackPath) :
    translateWithIncrement increment 0 path = path := by
  simpa [translateWithIncrement] using rerootWithIncrement_zero hincrement path

/-- Successive path translations use the current increment expressed in the intermediate frame. -/
theorem translateWithIncrement_add {increment : IntegerIncrement}
    (hincrement : IsAdditiveIntegerIncrement increment) (a b : ℝ) (path : FeedbackPath) :
    translateWithIncrement (shiftIncrement (-b) increment) a
        (translateWithIncrement increment b path) =
      translateWithIncrement increment (a + b) path := by
  simpa only [translateWithIncrement, neg_add_rev] using
    rerootWithIncrement_add hincrement (-b) (-a) path

/-- For a fixed increment and root, re-rooting is continuous in the path coordinate. -/
theorem continuous_rerootWithIncrement (increment : IntegerIncrement) (a : ℝ) :
    Continuous (rerootWithIncrement increment a : FeedbackPath → FeedbackPath) := by
  rw [isEmbedding_coordinates.continuous_iff]
  exact ((GraphHeight.continuous_reroot a).comp continuous_graphHeight).prodMk
    (continuous_rootCurrent.add continuous_const)

/-- Fixed re-rooting is Borel measurable. -/
theorem measurable_rerootWithIncrement (increment : IntegerIncrement) (a : ℝ) :
    Measurable (rerootWithIncrement increment a : FeedbackPath → FeedbackPath) :=
  (continuous_rerootWithIncrement increment a).measurable

/-- Translation by a fixed displacement is continuous on minimal path coordinates. -/
theorem continuous_translateWithIncrement (increment : IntegerIncrement) (a : ℝ) :
    Continuous (translateWithIncrement increment a : FeedbackPath → FeedbackPath) :=
  continuous_rerootWithIncrement increment (-a)

/-- Translation by a fixed displacement is Borel measurable on minimal path coordinates. -/
theorem measurable_translateWithIncrement (increment : IntegerIncrement) (a : ℝ) :
    Measurable (translateWithIncrement increment a : FeedbackPath → FeedbackPath) :=
  (continuous_translateWithIncrement increment a).measurable

end FeedbackPath

end OTSelector.PointProcess
