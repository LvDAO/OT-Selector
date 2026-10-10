import OTSelector.Feedback.FeedbackBoundaryComparison
import OTSelector.Feedback.RelativeVC

/-!
# Left-boundary rate control

The zero-shear segment is parametrized by the rank coordinate `x`.  Its source and target
crossing densities are the remaining label counts divided by the remaining rank length.  This
file records the actual finite-sample formulas and the deterministic implication used by the
left part of the global stopping coordinate.

The probability of the terminal count event is kept separate from this pathwise layer.  In
particular, no eventual-survival or rate conclusion is supplied as an assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace OTSelector
namespace FiniteSample

variable {n : ℕ}

/-! ## Actual zero-shear rates -/

/-- Strict-left source count at a unit-interval threshold. -/
noncomputable def leftSourceCountBeforeAt (p : UnitMark)
    (sample : FiniteSample n) : ℕ :=
  Set.ncard {i : Fin n | sample.sourceHeight i < p}

/-- Strict-left target count at a unit-interval threshold. -/
noncomputable def leftTargetCountBeforeAt (p : UnitMark)
    (sample : FiniteSample n) : ℕ :=
  Set.ncard {i : Fin n | sample.targetHeight i < p}

theorem measurable_leftSourceCountBeforeAt (p : UnitMark) :
    Measurable (leftSourceCountBeforeAt p : FiniteSample n → ℕ) := by
  unfold leftSourceCountBeforeAt
  apply measurable_ncard.comp
  rw [measurable_set_iff]
  intro i
  exact measurableSet_setOfPred.mp
    (measurableSet_lt (FiniteSample.measurable_sourceHeight i) measurable_const)

theorem measurable_leftTargetCountBeforeAt (p : UnitMark) :
    Measurable (leftTargetCountBeforeAt p : FiniteSample n → ℕ) := by
  unfold leftTargetCountBeforeAt
  apply measurable_ncard.comp
  rw [measurable_set_iff]
  intro i
  exact measurableSet_setOfPred.mp
    (measurableSet_lt (FiniteSample.measurable_targetHeight i) measurable_const)

/-- Source crossing density on the left zero-shear segment. -/
noncomputable def leftSourceRate (n : ℕ) (x : ℝ) (sample : FiniteSample n) : ℝ :=
  ((n : ℝ) - sample.leftSourceCountBeforeAt (leftBoundaryRankThreshold n x)) / (n - x)

/-- Target crossing density on the left zero-shear segment. -/
noncomputable def leftTargetRate (n : ℕ) (x : ℝ) (sample : FiniteSample n) : ℝ :=
  ((n : ℝ) - sample.leftTargetCountBeforeAt (leftBoundaryRankThreshold n x)) / (n - x)

/-- At the right end of the left segment, both colors have seen at most `2B` labels. -/
def leftRateCountGoodEvent (n : ℕ) (B : ℝ) : Set (FiniteSample n) :=
  {sample | (sample.leftSourceCountAt (leftBoundaryRankThreshold n B) : ℝ) ≤ 2 * B ∧
    (sample.leftTargetCountAt (leftBoundaryRankThreshold n B) : ℝ) ≤ 2 * B}

theorem measurableSet_leftRateCountGoodEvent (n : ℕ) (B : ℝ) :
    MeasurableSet (leftRateCountGoodEvent n B) := by
  exact (measurableSet_le
    ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_leftSourceCountAt (leftBoundaryRankThreshold n B)))
    measurable_const).inter
    (measurableSet_le
      ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
        (measurable_leftTargetCountAt (leftBoundaryRankThreshold n B)))
      measurable_const)

/-! ## Monotonicity of the terminal counts -/

theorem leftSourceCountAt_mono {p q : UnitMark} (hpq : p ≤ q)
    (sample : FiniteSample n) :
    sample.leftSourceCountAt p ≤ sample.leftSourceCountAt q := by
  unfold leftSourceCountAt
  exact Set.ncard_le_ncard (fun _ hi ↦ hi.trans hpq) (by toFinite_tac)

theorem leftTargetCountAt_mono {p q : UnitMark} (hpq : p ≤ q)
    (sample : FiniteSample n) :
    sample.leftTargetCountAt p ≤ sample.leftTargetCountAt q := by
  unfold leftTargetCountAt
  exact Set.ncard_le_ncard (fun _ hi ↦ hi.trans hpq) (by toFinite_tac)

theorem leftBoundaryRankThreshold_mono_on
    (hn : 0 < n) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyn : y ≤ n) :
    leftBoundaryRankThreshold n x ≤ leftBoundaryRankThreshold n y := by
  change ((leftBoundaryRankThreshold n x : UnitMark) : ℝ) ≤
    ((leftBoundaryRankThreshold n y : UnitMark) : ℝ)
  rw [leftBoundaryRankThreshold_coe_of_mem hn hx0 (hxy.trans hyn),
    leftBoundaryRankThreshold_coe_of_mem hn (hx0.trans hxy) hyn]
  exact div_le_div_of_nonneg_right hxy (by positivity : (0 : ℝ) ≤ n)

theorem leftSourceCountAt_rank_le_terminal
    (hn : 0 < n) {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    sample.leftSourceCountAt (leftBoundaryRankThreshold n x) ≤
      sample.leftSourceCountAt (leftBoundaryRankThreshold n B) :=
  leftSourceCountAt_mono (leftBoundaryRankThreshold_mono_on hn hx0 hxB hBn) sample

theorem leftTargetCountAt_rank_le_terminal
    (hn : 0 < n) {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    sample.leftTargetCountAt (leftBoundaryRankThreshold n x) ≤
      sample.leftTargetCountAt (leftBoundaryRankThreshold n B) :=
  leftTargetCountAt_mono (leftBoundaryRankThreshold_mono_on hn hx0 hxB hBn) sample

theorem leftSourceCountBeforeAt_rank_le_terminal
    (hn : 0 < n) {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    sample.leftSourceCountBeforeAt (leftBoundaryRankThreshold n x) ≤
      sample.leftSourceCountAt (leftBoundaryRankThreshold n B) := by
  unfold leftSourceCountBeforeAt leftSourceCountAt
  apply Set.ncard_le_ncard
  · intro i hi
    exact hi.le.trans (leftBoundaryRankThreshold_mono_on hn hx0 hxB hBn)
  · toFinite_tac

theorem leftTargetCountBeforeAt_rank_le_terminal
    (hn : 0 < n) {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hBn : B ≤ n)
    (sample : FiniteSample n) :
    sample.leftTargetCountBeforeAt (leftBoundaryRankThreshold n x) ≤
      sample.leftTargetCountAt (leftBoundaryRankThreshold n B) := by
  unfold leftTargetCountBeforeAt leftTargetCountAt
  apply Set.ncard_le_ncard
  · intro i hi
    exact hi.le.trans (leftBoundaryRankThreshold_mono_on hn hx0 hxB hBn)
  · toFinite_tac

/-! ## Uniform rate bounds on the terminal-count event -/

theorem leftRate_mem_Icc_of_count_le
    (hn : 0 < n) {x B count : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    (hBquarter : 4 * B ≤ n) (hcount0 : 0 ≤ count) (hcount : count ≤ 2 * B) :
    ((n : ℝ) - count) / (n - x) ∈ Icc ((1 : ℝ) / 2) 2 := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - x := by nlinarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith

/-- On the terminal-count event, the source rate remains in `[1/2,2]` throughout `[0,B]`. -/
theorem leftSourceRate_mem_Icc_of_good
    (hn : 0 < n) {B x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    (hBquarter : 4 * B ≤ n) {sample : FiniteSample n}
    (hgood : sample ∈ leftRateCountGoodEvent n B) :
    sample.leftSourceRate n x ∈ Icc ((1 : ℝ) / 2) 2 := by
  have hBn : B ≤ n := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hmono := leftSourceCountBeforeAt_rank_le_terminal hn hx0 hxB hBn sample
  have hmono' :
      (sample.leftSourceCountBeforeAt (leftBoundaryRankThreshold n x) : ℝ) ≤
        sample.leftSourceCountAt (leftBoundaryRankThreshold n B) := by
    exact_mod_cast hmono
  have hcount :
      (sample.leftSourceCountBeforeAt (leftBoundaryRankThreshold n x) : ℝ) ≤ 2 * B := by
    exact hmono'.trans hgood.1
  exact leftRate_mem_Icc_of_count_le hn hx0 hxB hBquarter (by positivity) hcount

/-- On the terminal-count event, the target rate remains in `[1/2,2]` throughout `[0,B]`. -/
theorem leftTargetRate_mem_Icc_of_good
    (hn : 0 < n) {B x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    (hBquarter : 4 * B ≤ n) {sample : FiniteSample n}
    (hgood : sample ∈ leftRateCountGoodEvent n B) :
    sample.leftTargetRate n x ∈ Icc ((1 : ℝ) / 2) 2 := by
  have hBn : B ≤ n := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hmono := leftTargetCountBeforeAt_rank_le_terminal hn hx0 hxB hBn sample
  have hmono' :
      (sample.leftTargetCountBeforeAt (leftBoundaryRankThreshold n x) : ℝ) ≤
        sample.leftTargetCountAt (leftBoundaryRankThreshold n B) := by
    exact_mod_cast hmono
  have hcount :
      (sample.leftTargetCountBeforeAt (leftBoundaryRankThreshold n x) : ℝ) ≤ 2 * B := by
    exact hmono'.trans hgood.2
  exact leftRate_mem_Icc_of_count_le hn hx0 hxB hBquarter (by positivity) hcount

/-! ## Probability of the terminal-count event -/

private theorem unitUniform_real_Iic (p : UnitMark) :
    (unitUniform : Measure UnitMark).real (Iic p) = p := by
  change ENNReal.toReal (volume (Iic p)) = p
  rw [unitInterval.volume_Iic, ENNReal.toReal_ofReal p.2.1]

private theorem sum_sourceIndicator_Iic_eq_count (p : UnitMark)
    (sample : FiniteSample n) :
    (∑ i : Fin n, RelativeVC.indicatorReal (Iic p) (sample.sourceHeight i)) =
      sample.leftSourceCountAt p := by
  classical
  rw [show sample.leftSourceCountAt p =
      (Finset.univ.filter fun i : Fin n ↦ sample.sourceHeight i ≤ p).card by
    unfold leftSourceCountAt
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext i
    simp]
  simp only [RelativeVC.indicatorReal, Set.indicator_apply, Pi.one_apply, mem_Iic,
    Finset.sum_boole]

private theorem sum_targetIndicator_Iic_eq_count (p : UnitMark)
    (sample : FiniteSample n) :
    (∑ i : Fin n, RelativeVC.indicatorReal (Iic p) (sample.targetHeight i)) =
      sample.leftTargetCountAt p := by
  classical
  rw [show sample.leftTargetCountAt p =
      (Finset.univ.filter fun i : Fin n ↦ sample.targetHeight i ≤ p).card by
    unfold leftTargetCountAt
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext i
    simp]
  simp only [RelativeVC.indicatorReal, Set.indicator_apply, Pi.one_apply, mem_Iic,
    Finset.sum_boole]

private theorem sourceHeight_empiricalProcess_Iic_eq
    (hn : 0 < n) (p : UnitMark) (sample : FiniteSample n) :
    EmpiricalProcess.empiricalProcess (unitUniform : Measure UnitMark) n
        (fun i ↦ sample.sourceHeight i) (RelativeVC.indicatorReal (Iic p)) =
      ((sample.leftSourceCountAt p : ℝ) - n * p) / Real.sqrt n := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  rw [RelativeVC.empiricalProcess_indicator _ _ _ _ measurableSet_Iic]
  unfold RelativeVC.empiricalSetDeviation RelativeVC.empiricalSetMass
    EmpiricalProcess.empiricalAverage
  rw [sum_sourceIndicator_Iic_eq_count, unitUniform_real_Iic]
  field_simp
  rw [hsqrt_sq]

private theorem targetHeight_empiricalProcess_Iic_eq
    (hn : 0 < n) (p : UnitMark) (sample : FiniteSample n) :
    EmpiricalProcess.empiricalProcess (unitUniform : Measure UnitMark) n
        (fun i ↦ sample.targetHeight i) (RelativeVC.indicatorReal (Iic p)) =
      ((sample.leftTargetCountAt p : ℝ) - n * p) / Real.sqrt n := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  rw [RelativeVC.empiricalProcess_indicator _ _ _ _ measurableSet_Iic]
  unfold RelativeVC.empiricalSetDeviation RelativeVC.empiricalSetMass
    EmpiricalProcess.empiricalAverage
  rw [sum_targetIndicator_Iic_eq_count, unitUniform_real_Iic]
  field_simp
  rw [hsqrt_sq]

/-- Bernstein control of the source terminal count on the left segment. -/
theorem measure_leftSourceCountAt_gt_two_mul_le
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | 2 * B <
          (sample.leftSourceCountAt (leftBoundaryRankThreshold n B) : ℝ)} ≤
      ENNReal.ofReal
        (2 * Real.exp (-((B / Real.sqrt n) ^ 2) /
          (4 * ((B / n) + (B / Real.sqrt n) / Real.sqrt n)))) := by
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem hn hB.le hBn
  have hx : 0 < B / Real.sqrt n := div_pos hB (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hbern := RelativeVC.centeredIndicator_bernstein
    (unitUniform : Measure UnitMark) (Iic p) measurableSet_Iic n (by omega)
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (X := fun i sample ↦ sample.sourceHeight i)
    (fun i ↦ FiniteSample.measurable_sourceHeight i)
    (finiteSampleLaw_sourceHeight_iIndep n)
    (fun i ↦ by
      simpa only [ProbabilityMeasure.toMeasure_map] using
        congrArg ProbabilityMeasure.toMeasure (finiteSampleLaw_map_sourceHeight n i))
    hx
  rw [unitUniform_real_Iic, hp] at hbern
  refine (measure_mono ?_).trans hbern
  intro sample hsample
  change 2 * B <
    (sample.leftSourceCountAt (leftBoundaryRankThreshold n B) : ℝ) at hsample
  change B / Real.sqrt n <
    |EmpiricalProcess.empiricalProcess (unitUniform : Measure UnitMark) n
      (fun i ↦ sample.sourceHeight i) (RelativeVC.indicatorReal (Iic p))|
  rw [sourceHeight_empiricalProcess_Iic_eq hn p sample]
  have hnp : (n : ℝ) * (p : ℝ) = B := by
    rw [hp]
    field_simp
  rw [hnp]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [abs_of_pos (div_pos (by linarith) hsqrt)]
  exact div_lt_div_of_pos_right (by linarith) hsqrt

/-- Bernstein control of the target terminal count on the left segment. -/
theorem measure_leftTargetCountAt_gt_two_mul_le
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        {sample | 2 * B <
          (sample.leftTargetCountAt (leftBoundaryRankThreshold n B) : ℝ)} ≤
      ENNReal.ofReal
        (2 * Real.exp (-((B / Real.sqrt n) ^ 2) /
          (4 * ((B / n) + (B / Real.sqrt n) / Real.sqrt n)))) := by
  let p := leftBoundaryRankThreshold n B
  have hp : (p : ℝ) = B / n :=
    leftBoundaryRankThreshold_coe_of_mem hn hB.le hBn
  have hx : 0 < B / Real.sqrt n := div_pos hB (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hbern := RelativeVC.centeredIndicator_bernstein
    (unitUniform : Measure UnitMark) (Iic p) measurableSet_Iic n (by omega)
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (X := fun i sample ↦ sample.targetHeight i)
    (fun i ↦ FiniteSample.measurable_targetHeight i)
    (finiteSampleLaw_targetHeight_iIndep n)
    (fun i ↦ by
      simpa only [ProbabilityMeasure.toMeasure_map] using
        congrArg ProbabilityMeasure.toMeasure (finiteSampleLaw_map_targetHeight n i))
    hx
  rw [unitUniform_real_Iic, hp] at hbern
  refine (measure_mono ?_).trans hbern
  intro sample hsample
  change 2 * B <
    (sample.leftTargetCountAt (leftBoundaryRankThreshold n B) : ℝ) at hsample
  change B / Real.sqrt n <
    |EmpiricalProcess.empiricalProcess (unitUniform : Measure UnitMark) n
      (fun i ↦ sample.targetHeight i) (RelativeVC.indicatorReal (Iic p))|
  rw [targetHeight_empiricalProcess_Iic_eq hn p sample]
  have hnp : (n : ℝ) * (p : ℝ) = B := by
    rw [hp]
    field_simp
  rw [hnp]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [abs_of_pos (div_pos (by linarith) hsqrt)]
  exact div_lt_div_of_pos_right (by linarith) hsqrt

/-- The actual left-rate terminal event fails with an explicit two-color Bernstein bound. -/
theorem measure_leftRateCountGoodEvent_compl_le
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n)) (leftRateCountGoodEvent n B)ᶜ ≤
      2 * ENNReal.ofReal
        (2 * Real.exp (-((B / Real.sqrt n) ^ 2) /
          (4 * ((B / n) + (B / Real.sqrt n) / Real.sqrt n)))) := by
  have hcompl : (leftRateCountGoodEvent n B)ᶜ =
      {sample | 2 * B <
        (sample.leftSourceCountAt (leftBoundaryRankThreshold n B) : ℝ)} ∪
      {sample | 2 * B <
        (sample.leftTargetCountAt (leftBoundaryRankThreshold n B) : ℝ)} := by
    ext sample
    simp only [leftRateCountGoodEvent, mem_compl_iff, mem_ofPred_eq, mem_union, not_and_or,
      not_le]
  rw [hcompl]
  calc
    _ ≤ (finiteSampleLaw n : Measure (FiniteSample n))
          {sample | 2 * B <
            (sample.leftSourceCountAt (leftBoundaryRankThreshold n B) : ℝ)} +
        (finiteSampleLaw n : Measure (FiniteSample n))
          {sample | 2 * B <
            (sample.leftTargetCountAt (leftBoundaryRankThreshold n B) : ℝ)} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal
          (2 * Real.exp (-((B / Real.sqrt n) ^ 2) /
            (4 * ((B / n) + (B / Real.sqrt n) / Real.sqrt n)))) +
        ENNReal.ofReal
          (2 * Real.exp (-((B / Real.sqrt n) ^ 2) /
            (4 * ((B / n) + (B / Real.sqrt n) / Real.sqrt n)))) :=
      add_le_add (measure_leftSourceCountAt_gt_two_mul_le hn hB hBn)
        (measure_leftTargetCountAt_gt_two_mul_le hn hB hBn)
    _ = _ := by ring

private theorem leftRate_bernstein_exponent_eq
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) :
    (B / Real.sqrt n) ^ 2 /
        (4 * (B / n + (B / Real.sqrt n) / Real.sqrt n)) =
      B / 8 := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
  field_simp
  nlinarith [hsqrt_sq]

/-- Simplified form of the two-color left-rate failure probability. -/
theorem measure_leftRateCountGoodEvent_compl_le_exp
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) (hBn : B ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n)) (leftRateCountGoodEvent n B)ᶜ ≤
      2 * ENNReal.ofReal (2 * Real.exp (-B / 8)) := by
  have h := measure_leftRateCountGoodEvent_compl_le hn hB hBn
  have hneg :
      -((B / Real.sqrt n) ^ 2) /
          (4 * (B / n + (B / Real.sqrt n) / Real.sqrt n)) =
        -B / 8 := by
    calc
      _ = -((B / Real.sqrt n) ^ 2 /
          (4 * (B / n + (B / Real.sqrt n) / Real.sqrt n))) := by ring
      _ = -B / 8 := by
        rw [leftRate_bernstein_exponent_eq hn hB]
        ring
  rw [hneg] at h
  exact h

end FiniteSample
end OTSelector
