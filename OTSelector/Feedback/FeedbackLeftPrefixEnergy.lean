import OTSelector.Feedback.FeedbackStoppedGraphEnergyBridge
import OTSelector.Feedback.FeedbackLeftCountingIntensity
import OTSelector.Feedback.StoppedRankGapEnergy

/-!
# Left-prefix energy of the increasing graph matching

The finite left arrivals remain top-valued when absent. Rank gaps are censored at the genuine
left rate-exit time; no artificial event is inserted at the boundary.
-/

open Filter MeasureTheory Set
open scoped Classical NNReal ENNReal ProbabilityTheory
open OTSelector.CountingProcess
namespace OTSelector.FiniteSample
variable {n : ℕ} (sample : FiniteSample n)

theorem leftPrefix_sourceIntersection_horizon_min_left
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (i : Fin n) :
    min (sample.sourceIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i) B =
      min ((n : ℝ) * sample.sourceHeight i) B := by
  let g := sample.horizonFeedbackGraph hlam0 hlamHalf B T
  have hle : sample.sourceIntersection g i ≤ B ↔
      (n : ℝ) * sample.sourceHeight i ≤ B := by
    rw [sample.sourceIntersection_le_iff]
    simp [g, sourcePhase]
  by_cases hi : sample.sourceIntersection g i ≤ B
  · have hspec := sample.sourceIntersection_spec g i
    have hg : g.curve (sample.sourceIntersection g i) = 0 :=
      sample.horizonFeedbackGraph_curve_eq_left hlam0 hlamHalf B T hi
    rw [hg] at hspec
    simp only [sourcePhase, mul_zero, add_zero] at hspec
    rw [min_eq_left hi, min_eq_left (hle.mp hi)]
    exact hspec.symm
  · rw [min_eq_right (le_of_not_ge hi), min_eq_right (le_of_not_ge (hle.not.mp hi))]

theorem leftPrefix_targetIntersection_horizon_min_left
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (i : Fin n) :
    min (sample.targetIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i) B =
      min ((n : ℝ) * sample.targetHeight i) B := by
  let g := sample.horizonFeedbackGraph hlam0 hlamHalf B T
  have hle : sample.targetIntersection g i ≤ B ↔
      (n : ℝ) * sample.targetHeight i ≤ B := by
    rw [sample.targetIntersection_le_iff]
    simp [g, targetPhase]
  by_cases hi : sample.targetIntersection g i ≤ B
  · have hspec := sample.targetIntersection_spec g i
    have hg : g.curve (sample.targetIntersection g i) = 0 :=
      sample.horizonFeedbackGraph_curve_eq_left hlam0 hlamHalf B T hi
    rw [hg] at hspec
    simp only [targetPhase, mul_zero, sub_zero] at hspec
    rw [min_eq_left hi, min_eq_left (hle.mp hi)]
    exact hspec.symm
  · rw [min_eq_right (le_of_not_ge hi), min_eq_right (le_of_not_ge (hle.not.mp hi))]

theorem leftPrefix_tuple_sort_min_commutes (values : Fin n → ℝ) (B : ℝ) (r : Fin n) :
    min (values (Tuple.sort values r)) B =
      (fun i ↦ min (values i) B) (Tuple.sort (fun i ↦ min (values i) B) r) := by
  have hm : Monotone ((fun i ↦ min (values i) B) ∘ Tuple.sort values) := by
    intro i j hij
    exact min_le_min (Tuple.monotone_sort values hij) le_rfl
  exact congrFun (Tuple.unique_monotone hm (Tuple.monotone_sort (fun i ↦ min (values i) B))) r

theorem leftPrefix_rank_gap_sq_le_prefix_add_suffix (a b B : ℝ) :
    (b - a) ^ 2 ≤ 2 * (min b B - min a B) ^ 2 +
      2 * (max 0 (b - B) - max 0 (a - B)) ^ 2 := by
  have ha : min a B + max 0 (a - B) = a := by
    by_cases h : a ≤ B
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h), add_zero]
    · rw [min_eq_right (le_of_not_ge h), max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hb : min b B + max 0 (b - B) = b := by
    by_cases h : b ≤ B
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h), add_zero]
    · rw [min_eq_right (le_of_not_ge h), max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hdiff : b - a = (min b B - min a B) +
      (max 0 (b - B) - max 0 (a - B)) := by linarith
  rw [hdiff]
  nlinarith [sq_nonneg ((min b B - min a B) -
    (max 0 (b - B) - max 0 (a - B)))]

private theorem leftPrefix_countBefore_at_rank_eq
    {m : ℕ} {Omega : Type*} (tau : Fin m → Omega → WithTop ℝ≥0)
    (r : Fin m) (sample : Omega) (s : ℝ≥0)
    (hrank : CountingProcess.finiteRankEventTime tau r sample = (s : WithTop ℝ≥0))
    (hunique : ∀ i j : Fin m, tau i sample = (s : WithTop ℝ≥0) →
      tau j sample = (s : WithTop ℝ≥0) → i = j) :
    countBefore (fun u sample' ↦ finiteEventCountTop tau u sample') s sample = r.val := by
  classical
  let values : Fin m → WithTop ℝ≥0 := fun i ↦ tau i sample
  let sigma : Equiv.Perm (Fin m) := Tuple.sort values
  have hrank' : values (sigma r) = (s : WithTop ℝ≥0) := by
    simpa only [CountingProcess.finiteRankEventTime, values, sigma] using hrank
  have hmono : Monotone (values ∘ sigma) := Tuple.monotone_sort values
  have hlt : ∀ k : Fin m, values (sigma k) < (s : WithTop ℝ≥0) ↔ k < r := by
    intro k
    constructor
    · intro hk
      by_contra hkr
      have hrk : r ≤ k := le_of_not_gt hkr
      have hle := hmono hrk
      simp only [Function.comp_apply, hrank'] at hle
      exact (not_lt_of_ge hle) hk
    · intro hkr
      have hle := hmono hkr.le
      simp only [Function.comp_apply, hrank'] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hlabels : sigma k = sigma r := hunique (sigma k) (sigma r) heq hrank'
      exact hkr.ne (sigma.injective hlabels)
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  have hcard :
      (Finset.univ.filter fun k : Fin m ↦ values (sigma k) < (s : WithTop ℝ≥0)).card =
        (Finset.univ.filter fun i : Fin m ↦ values i < (s : WithTop ℝ≥0)).card := by
    apply Finset.card_equiv sigma
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hcard]
  have hfilter :
      (Finset.univ.filter fun k : Fin m ↦ values (sigma k) < (s : WithTop ℝ≥0)) =
        Finset.Iio r := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact hlt k
  rw [hfilter]
  simp

private theorem leftPrefix_sorted_count_eq {Ω : Type*}
    (ξ : Fin n → Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    finiteEventCountTop (finiteRankEventTime ξ) t ω = finiteEventCountTop ξ t ω := by
  unfold finiteEventCountTop finiteRankEventTime
  apply Finset.card_equiv (Tuple.sort (fun i ↦ ξ i ω))
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem leftPrefix_sorted_injective {Ω : Type*}
    (ξ : Fin n → Ω → WithTop ℝ≥0) (ω : Ω)
    (hinj : ∀ i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (i j : Fin n) (hi : finiteRankEventTime ξ i ω ≠ ⊤)
    (hj : finiteRankEventTime ξ j ω ≠ ⊤)
    (heq : finiteRankEventTime ξ i ω = finiteRankEventTime ξ j ω) : i = j := by
  exact (Tuple.sort (fun k ↦ ξ k ω)).injective (hinj _ _ hi hj heq)

/-- A genuine left arrival, indexed by its order among its own colour. -/
noncomputable def leftPrefixRankTime (B : ℝ≥0) (color : Fin 2) :
    Fin n → FiniteSample n → WithTop ℝ≥0 :=
  finiteRankEventTime (fun i ↦ leftEventTime n B (color, i))

/-- An oriented prefix stops at the opposite rank or the genuine left rate failure. -/
noncomputable def leftPrefixGap (B : ℝ≥0) (color other : Fin 2)
    (r : Fin n) (sample : FiniteSample n) : ℝ :=
  max 0 ((cappedStoppingValue B
      (fun ω ↦ min (leftPrefixRankTime B other r ω) (leftRateExitTime n B ω)) sample : ℝ) -
    (cappedStoppingValue B (leftPrefixRankTime B color r) sample : ℝ))

/-- Total squared prefixes, censored at the first left rate failure. -/
noncomputable def stoppedLeftPrefixEnergy (B : ℝ≥0) : FiniteSample n → ℝ :=
  stoppedRankGapEnergy (leftPrefixGap B 0 1) (leftPrefixGap B 1 0)

theorem leftPrefixRankTime_isStoppingTime (B : ℝ≥0) (color : Fin 2) (r : Fin n) :
    IsStoppingTime (leftUsualFiltration n B) (leftPrefixRankTime B color r) :=
  finiteRankEventTime_isStoppingTime _ _ _ (fun i ↦ leftEventTime_isStoppingTime n B (color, i))

theorem measurable_leftPrefixGap {B : ℝ≥0} (hBn : (B : ℝ) < n)
    (color other : Fin 2) (r : Fin n) : Measurable (leftPrefixGap B color other r) := by
  exact measurable_const.max
    ((measurable_coe_nnreal_real.comp (measurable_cappedStoppingValue _
      ((leftPrefixRankTime_isStoppingTime B other r).min
        (leftRateExitTime_isStoppingTime hBn)) B)).sub
      (measurable_coe_nnreal_real.comp (measurable_cappedStoppingValue _
        (leftPrefixRankTime_isStoppingTime B color r) B)))

private theorem leftPrefixGap_nonneg (B : ℝ≥0) (color other : Fin 2)
    (r : Fin n) (sample : FiniteSample n) : 0 ≤ leftPrefixGap B color other r sample :=
  le_max_left _ _

private theorem leftPrefixGap_retained (B : ℝ≥0) (color other : Fin 2)
    (r : Fin n) (sample : FiniteSample n)
    (h : sample ∉ retainedRankGapEvent B (leftRateExitTime n B)
      (leftPrefixRankTime B color r)) : leftPrefixGap B color other r sample = 0 := by
  have hstop : leftRateExitTime n B sample ≤ (B : WithTop ℝ≥0) := min_le_right _ _
  have hle : min (min (leftPrefixRankTime B other r sample) (leftRateExitTime n B sample))
      (B : WithTop ℝ≥0) ≤ min (leftPrefixRankTime B color r sample) (B : WithTop ℝ≥0) := by
    apply le_min
    · have hnot : ¬ leftPrefixRankTime B color r sample ≤ leftRateExitTime n B sample := by
        intro hx
        exact h ⟨hx.trans hstop, hx⟩
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (le_of_not_ge hnot))
    · exact min_le_right _ _
  have hcap : cappedStoppingValue B
      (fun ω ↦ min (leftPrefixRankTime B other r ω) (leftRateExitTime n B ω)) sample ≤
        cappedStoppingValue B (leftPrefixRankTime B color r) sample := by
    apply WithTop.coe_le_coe.mp
    simpa only [coe_cappedStoppingValue] using hle
  exact max_eq_left (sub_nonpos.mpr (by exact_mod_cast hcap))

private theorem leftPrefixGap_tail_subset (B : ℝ≥0) (color other : Fin 2)
    (r : Fin n) (q : ℝ≥0) (c : ℝ) :
    {sample : FiniteSample n | (q : ℝ) < leftPrefixGap B color other r sample} ⊆
      {sample | c * (q : ℝ) <
        |(countBefore (leftColorCount n B color)
            (cappedStoppingValue B (leftPrefixRankTime B color r) sample) sample : ℝ) -
          countBefore (leftColorCount n B other)
            (cappedStoppingValue B (leftPrefixRankTime B color r) sample) sample|} ∪
      stoppedLowerOccupationEvent (leftColorCount n B other)
        (cappedStoppingValue B (leftPrefixRankTime B color r)) (leftRateExitTime n B) c q := by
  intro ω hgap
  by_cases hback : c * (q : ℝ) <
      |(countBefore (leftColorCount n B color)
          (cappedStoppingValue B (leftPrefixRankTime B color r) ω) ω : ℝ) -
        countBefore (leftColorCount n B other)
          (cappedStoppingValue B (leftPrefixRankTime B color r) ω) ω|
  · exact Or.inl hback
  right
  let σ := cappedStoppingValue B (leftPrefixRankTime B color r) ω
  let ρ := cappedStoppingValue B
    (fun ω ↦ min (leftPrefixRankTime B other r ω) (leftRateExitTime n B ω)) ω
  have hdiff : (q : ℝ) < (ρ : ℝ) - σ := by
    exact (lt_max_iff.mp hgap).resolve_left (not_lt_of_ge q.2)
  have hsr : σ + q < ρ := by exact_mod_cast (show (σ : ℝ) + q < ρ by linarith)
  have hrOther : (ρ : WithTop ℝ≥0) ≤ leftPrefixRankTime B other r ω := by
    rw [coe_cappedStoppingValue]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hrStop : (ρ : WithTop ℝ≥0) ≤ leftRateExitTime n B ω := by
    rw [coe_cappedStoppingValue]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hstop : ((σ + q : ℝ≥0) : WithTop ℝ≥0) ≤ leftRateExitTime n B ω :=
    (WithTop.coe_lt_coe.mpr hsr).le.trans hrStop
  have hend : leftColorCount n B other (σ + q) ω ≤ r.val := by
    apply Nat.le_of_not_gt
    intro hh
    have hh' := (finiteRankEventTime_le_iff_lt_finiteEventCountTop
      (fun i ↦ leftEventTime n B (other, i)) r ω (σ + q)).mpr hh
    exact not_le_of_gt ((WithTop.coe_lt_coe.mpr hsr).trans_le hrOther) hh'
  have hσB : σ < B := (lt_of_le_of_lt (le_add_right le_rfl) hsr).trans_le
    (cappedStoppingValue_le B _ ω)
  have hσEq : leftPrefixRankTime B color r ω = (σ : WithTop ℝ≥0) := by
    have hh : min (leftPrefixRankTime B color r ω) (B : WithTop ℝ≥0) = (σ : WithTop ℝ≥0) :=
      (coe_cappedStoppingValue B (leftPrefixRankTime B color r) ω).symm
    have hx : leftPrefixRankTime B color r ω ≤ (B : WithTop ℝ≥0) := by
      by_contra hh'
      rw [min_eq_right (le_of_not_ge hh')] at hh
      exact (ne_of_lt (WithTop.coe_lt_coe.mpr hσB)) hh.symm
    rwa [min_eq_left hx] at hh
  have hbefore : countBefore (leftColorCount n B color) σ ω = r.val := by
    apply leftPrefix_countBefore_at_rank_eq
      (fun i ↦ leftEventTime n B (color, i)) r ω σ hσEq
    intro i j hi hj
    exact leftEventTime_injective n B color ω i j
      (by rw [hi]; exact WithTop.coe_ne_top)
      (by rw [hj]; exact WithTop.coe_ne_top) (hi.trans hj.symm)
  have hbeforeLe : countBefore (leftColorCount n B other) σ ω ≤
      leftColorCount n B other σ ω := by
    change countBefore (fun t ω ↦ finiteEventCountTop
      (fun i ↦ leftEventTime n B (other, i)) t ω) σ ω ≤ _
    rw [countBefore_finiteEventCountTop_eq_card_filter_lt, leftColorCount, finiteEventCountTop]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  refine ⟨?_, hstop⟩
  change (leftColorCount n B other (σ + q) ω : ℝ) - leftColorCount n B other σ ω ≤ c * q
  have hend' : (leftColorCount n B other (σ + q) ω : ℝ) ≤ r.val := by exact_mod_cast hend
  have hbeforeLe' : (countBefore (leftColorCount n B other) σ ω : ℝ) ≤
      leftColorCount n B other σ ω := by exact_mod_cast hbeforeLe
  change ¬ c * (q : ℝ) < |(countBefore (leftColorCount n B color) σ ω : ℝ) -
    countBefore (leftColorCount n B other) σ ω| at hback
  rw [hbefore] at hback
  have habs := le_abs_self ((r.val : ℝ) - countBefore (leftColorCount n B other) σ ω)
  have hbound := le_of_not_gt hback
  linarith

/-- The predictable strict-left discrepancy of the two actual left counting processes. -/
noncomputable def leftPrefixCurrent (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  (leftCurrentOfCounts (fun _ ↦ 0) (leftColorCount n B 0) (leftColorCount n B 1) t sample : ℝ)

private theorem leftPrefix_before_le (B : ℝ≥0) (color : Fin 2) (t : ℝ≥0)
    (sample : FiniteSample n) : countBefore (leftColorCount n B color) t sample ≤ n := by
  change countBefore (fun s ω ↦ finiteEventCountTop
    (fun i ↦ leftEventTime n B (color, i)) s ω) t sample ≤ n
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem abs_leftPrefixCurrent_le (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) :
    |leftPrefixCurrent B t sample| ≤ n := by
  have hp : (countBefore (leftColorCount n B 0) t sample : ℝ) ≤ n := by
    exact_mod_cast leftPrefix_before_le B 0 t sample
  have hm : (countBefore (leftColorCount n B 1) t sample : ℝ) ≤ n := by
    exact_mod_cast leftPrefix_before_le B 1 t sample
  have hp0 : (0 : ℝ) ≤ countBefore (leftColorCount n B 0) t sample := by positivity
  have hm0 : (0 : ℝ) ≤ countBefore (leftColorCount n B 1) t sample := by positivity
  simp only [leftPrefixCurrent, leftCurrentOfCounts, Int.cast_sub,
    Int.cast_natCast, zero_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem leftPrefixCurrent_predictable (B : ℝ≥0) :
    IsStronglyPredictable (leftUsualFiltration n B) (leftPrefixCurrent B) :=
  leftCurrentOfCounts_cast_predictable
    (leftColorCount_isSimpleCountingProcess n B 0)
    (leftColorCount_isSimpleCountingProcess n B 1) stronglyMeasurable_const

private theorem leftPrefix_clip_current (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) :
    integerClip n (leftCurrentOfCounts (fun _ ↦ 0)
      (leftColorCount n B 0) (leftColorCount n B 1) t sample) =
      leftCurrentOfCounts (fun _ ↦ 0) (leftColorCount n B 0) (leftColorCount n B 1) t sample := by
  apply integerClip_eq_self_of_mem
  rw [cutoffStates, Finset.mem_Icc]
  have hh := abs_le.mp (abs_leftPrefixCurrent_le B t sample)
  dsimp only [leftPrefixCurrent] at hh
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem leftPrefixExitMask_boundedSimplePredictable
    {B : ℝ≥0} (hBn : (B : ℝ) < n) :
    IsBoundedSimplePredictable (leftUsualFiltration n B)
      (throughStopMask (leftRateExitTime n B)) := by
  have hhit := throughStopMask_hittingAfter_zero_boundedSimplePredictable_of_rightContinuous
    (leftPostRatePath_adapted n B) (leftPostRatePath_rightContinuous hBn) isOpen_leftRateBadSet
  have hBmask := throughStopMask_boundedSimplePredictable
    (isStoppingTime_const (leftUsualFiltration n B) B) Set.finite_range_const
  convert hhit.mul_process hBmask using 1
  funext t sample
  simp only [leftRateExitTime, throughStopMask, le_min_iff]
  split_ifs <;> simp_all

theorem leftPrefixMomentCharge_boundedSimplePredictable
    {B : ℝ≥0} (hBn : (B : ℝ) < n) (c d : ℝ) :
    IsBoundedSimplePredictable (leftUsualFiltration n B)
      (stoppedRankGapMomentCharge (leftRateExitTime n B) (leftPrefixCurrent B) c d) := by
  let g : ℤ → ℝ := fun k ↦ ((k : ℝ) / c) ^ 2 + 2 / d ^ 2
  have hg : IsBoundedSimplePredictable (leftUsualFiltration n B)
      (fun s sample ↦ g (integerClip n (leftCurrentOfCounts (fun _ ↦ 0)
        (leftColorCount n B 0) (leftColorCount n B 1) s sample))) := by
    refine ⟨leftCurrentOfCounts_comp_predictable
      (leftColorCount_isSimpleCountingProcess n B 0)
      (leftColorCount_isSimpleCountingProcess n B 1) stronglyMeasurable_const
      (fun k ↦ g (integerClip n k)), ?_, clippedValueAbsBound n g,
      clippedValueAbsBound_nonneg n g, ?_⟩
    · apply ((cutoffStates n).finite_toSet.image g).subset
      rintro y ⟨⟨s, sample⟩, rfl⟩
      exact ⟨_, integerClip_mem_cutoffStates n _, rfl⟩
    · exact fun s sample ↦ abs_apply_integerClip_le_clippedValueAbsBound n g _
  change IsBoundedSimplePredictable _ (fun t ω ↦ throughStopMask (leftRateExitTime n B) t ω *
    (((leftCurrentOfCounts (fun _ ↦ 0) (leftColorCount n B 0)
      (leftColorCount n B 1) t ω : ℝ) / c) ^ 2 + 2 / d ^ 2))
  simpa only [leftPrefix_clip_current, g] using
    (leftPrefixExitMask_boundedSimplePredictable hBn).mul_process hg

theorem leftPrefixCurrent_at_capped_stopping_stronglyMeasurable
    (B : ℝ≥0) {ξ : FiniteSample n → WithTop ℝ≥0}
    (hξ : IsStoppingTime (leftUsualFiltration n B) ξ) :
    StronglyMeasurable[(cappedStoppingValue_isStoppingTime _ hξ B).measurableSpace]
      (fun sample ↦ |leftPrefixCurrent B (cappedStoppingValue B ξ sample) sample|) := by
  have hm : Measurable[(cappedStoppingValue_isStoppingTime _ hξ B).measurableSpace]
      (stoppedValue (leftPrefixCurrent (n := n) B)
        (fun sample ↦ (cappedStoppingValue B ξ sample : WithTop ℝ≥0))) :=
    measurable_stoppedValue (leftPrefixCurrent_predictable (n := n) B).isStronglyProgressive
      (cappedStoppingValue_isStoppingTime _ hξ B)
  have hs : StronglyMeasurable[(cappedStoppingValue_isStoppingTime _ hξ B).measurableSpace]
      (stoppedValue (leftPrefixCurrent (n := n) B)
        (fun sample ↦ (cappedStoppingValue B ξ sample : WithTop ℝ≥0))) :=
    hm.stronglyMeasurable
  have h := continuous_abs.comp_stronglyMeasurable hs
  simpa only [stoppedValue, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using h

theorem leftPrefixCurrent_at_capped_stopping_sq_integrable
    (B : ℝ≥0) {ξ : FiniteSample n → WithTop ℝ≥0}
    (hξ : IsStoppingTime (leftUsualFiltration n B) ξ) :
    Integrable (fun sample ↦ |leftPrefixCurrent B (cappedStoppingValue B ξ sample) sample| ^ 2)
      (finiteSampleLaw n) := by
  have hmeas := (leftPrefixCurrent_at_capped_stopping_stronglyMeasurable B hξ).mono
    (cappedStoppingValue_isStoppingTime _ hξ B).measurableSpace_le
  refine Integrable.of_bound (hmeas.pow 2).aestronglyMeasurable ((n : ℝ) ^ 2) (ae_of_all _ ?_)
  intro sample
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_leftPrefixCurrent_le B _ _) 2

private theorem leftPrefix_occupation_integrand_bound
    (B : ℝ≥0) (t : ℝ≥0) (sample : FiniteSample n) :
    ‖throughStopMask (leftRateExitTime n B) t sample *
      (1 + leftPrefixCurrent B t sample ^ 2)‖ ≤ 1 + (n : ℝ) ^ 2 := by
  have hs : leftPrefixCurrent B t sample ^ 2 ≤ (n : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_leftPrefixCurrent_le B t sample) 2
  unfold throughStopMask
  split_ifs
  · simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 + leftPrefixCurrent B t sample ^ 2)]
    linarith
  · simp only [zero_mul, norm_zero]
    positivity

theorem leftPrefix_occupation_integrableOn {B : ℝ≥0} (hBn : (B : ℝ) < n)
    (sample : FiniteSample n) : IntegrableOn
    (fun t ↦ throughStopMask (leftRateExitTime n B) t sample *
      (1 + leftPrefixCurrent B t sample ^ 2)) (Ioc 0 B) timeMeasure := by
  have hp : IsStronglyPredictable (leftUsualFiltration n B)
      (fun t sample ↦ throughStopMask (leftRateExitTime n B) t sample *
        (1 + leftPrefixCurrent B t sample ^ 2)) :=
    (leftPrefixExitMask_boundedSimplePredictable hBn).1.mul
      (stronglyMeasurable_const.add ((leftPrefixCurrent_predictable B).pow 2))
  have hm := (hp.mono (predictable_le_ambient (leftUsualFiltration n B))).comp_measurable
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ≥0 ↦ sample)))
  exact Measure.integrableOn_of_bounded (timeMeasure_Ioc_lt_top 0 B).ne
    hm.aestronglyMeasurable (ae_of_all _ fun t ↦ leftPrefix_occupation_integrand_bound B t sample)

theorem leftPrefix_occupation_integrable {B : ℝ≥0} (hBn : (B : ℝ) < n) :
    Integrable (stoppedCurrentOccupation (leftRateExitTime n B) (leftPrefixCurrent B) B)
      (finiteSampleLaw n) := by
  have hp : IsStronglyPredictable (leftUsualFiltration n B)
      (fun t sample ↦ throughStopMask (leftRateExitTime n B) t sample *
        (1 + leftPrefixCurrent B t sample ^ 2)) :=
    (leftPrefixExitMask_boundedSimplePredictable hBn).1.mul
      (stronglyMeasurable_const.add ((leftPrefixCurrent_predictable B).pow 2))
  have hm := hp.mono (predictable_le_ambient (leftUsualFiltration n B))
  let _ : IsFiniteMeasure (timeMeasure.restrict (Ioc (0 : ℝ≥0) B)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact timeMeasure_Ioc_lt_top 0 B⟩
  have hmeas : StronglyMeasurable
      (stoppedCurrentOccupation (leftRateExitTime n B) (leftPrefixCurrent B) B) :=
    hm.integral_prod_left'
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((1 + (n : ℝ) ^ 2) * B) (ae_of_all _ fun sample ↦ ?_)
  calc
    ‖stoppedCurrentOccupation (leftRateExitTime n B) (leftPrefixCurrent B) B sample‖ ≤
        ∫ _t in Ioc (0 : ℝ≥0) B, 1 + (n : ℝ) ^ 2 ∂timeMeasure := by
      exact norm_integral_le_of_norm_le
        (integrableOn_const (timeMeasure_Ioc_lt_top 0 B).ne)
        (ae_of_all _ fun t ↦ leftPrefix_occupation_integrand_bound B t sample)
    _ = (1 + (n : ℝ) ^ 2) * B := by
      rw [integral_timeMeasure_eq_intervalIntegral _ 0 B (by simp)]
      simp
      ring

private theorem leftPrefix_intensity_mem_Icc {B : ℝ≥0} (hBn : (B : ℝ) < n)
    (color : Fin 2) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) < leftRateExitTime n B sample) :
    leftColorIntensity n B color t sample ∈ Icc ((1 : ℝ) / 2) 2 := by
  have htB : (t : WithTop ℝ≥0) ≤ (B : WithTop ℝ≥0) := ht.le.trans (min_le_right _ _)
  have hh := leftStrictRatePath_mem_region_of_lt_exit hBn t sample ht
  change leftColorStrictRate n B 0 t sample ∈ Icc ((1 : ℝ) / 2) 2 ∧
    leftColorStrictRate n B 1 t sample ∈ Icc ((1 : ℝ) / 2) 2 at hh
  have heq : leftColorIntensity n B color t sample = leftColorStrictRate n B color t sample := by
    simp only [leftColorIntensity, throughStopMask, htB, ite_true, one_mul, leftColorStrictRate]
  rw [heq]
  fin_cases color
  · exact hh.1
  · exact hh.2

/-- Actual left-prefix energy is controlled by actual stopped left-current occupation. -/
theorem stoppedLeftPrefixEnergy_integrable_and_integral_le_occupation
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    Integrable (stoppedLeftPrefixEnergy (n := n) B) (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n, stoppedLeftPrefixEnergy B sample ∂(finiteSampleLaw n)) ≤
        (4 * (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2)) *
        ∫ sample, stoppedCurrentOccupation (leftRateExitTime n B)
          (leftPrefixCurrent B) B sample ∂(finiteSampleLaw n) := by
  have hBn : (B : ℝ) < n := by have hb : 0 < (B : ℝ) := hB; nlinarith
  have hcount (color : Fin 2) : finiteEventCountTop (leftPrefixRankTime (n := n) B color) =
      leftColorCount n B color := by
    funext t sample
    exact leftPrefix_sorted_count_eq _ t sample
  have hN (color : Fin 2) : IsSimpleCountingProcess (leftUsualFiltration n B)
      (finiteEventCountTop (leftPrefixRankTime (n := n) B color)) := by
    rw [hcount]
    exact leftColorCount_isSimpleCountingProcess n B color
  have hΛ (color : Fin 2) : HasPredictableIntensity (finiteSampleLaw n)
      (leftUsualFiltration n B) (finiteEventCountTop (leftPrefixRankTime B color))
      (leftColorIntensity n B color) := by
    rw [hcount]
    exact leftColorCount_hasPredictableIntensity hn hB hBquarter color
  have hA (color : Fin 2) (t : ℝ≥0) : Integrable
      (fun sample ↦ integratedIntensity (leftColorIntensity n B color)
        (fun _ _ ↦ (1 : ℝ)) t sample) (finiteSampleLaw n) :=
    integratedIntensity_one_integrable_of_bounded (by norm_num : (0 : ℝ) ≤ 2)
      (leftColorIntensity_le_two hBn hBquarter color) (hN color) (hΛ color) t
  have htailPlus (r : Fin n) (q : ℝ≥0) (_hq : 0 < q) :=
    leftPrefixGap_tail_subset (n := n) B 0 1 r q (lowerOccupationCountRate ((1 : ℝ) / 2))
  have htailMinus (r : Fin n) (q : ℝ≥0) (_hq : 0 < q) :=
    leftPrefixGap_tail_subset (n := n) B 1 0 r q (lowerOccupationCountRate ((1 : ℝ) / 2))
  have hcur (s : ℝ≥0) (sample : FiniteSample n) : leftPrefixCurrent B s sample =
      (countBefore (leftColorCount n B 0) s sample : ℝ) -
        countBefore (leftColorCount n B 1) s sample := by
    simp [leftPrefixCurrent, leftCurrentOfCounts]
  have hresult := stoppedRankGapEnergy_integrable_and_integral_le
    (mu := (finiteSampleLaw n : Measure (FiniteSample n)))
    (F := leftUsualFiltration n B)
    (sigmaPlus := leftPrefixRankTime B 0) (sigmaMinus := leftPrefixRankTime B 1)
    (Xplus := leftPrefixGap B 0 1) (Xminus := leftPrefixGap B 1 0)
    (K := leftPrefixCurrent B) (tau := leftRateExitTime n B)
    (c0 := (1 : ℝ) / 2) (Cglobal := 2) (C0 := 2) B
    (by norm_num) (by norm_num) (by norm_num) (hN 0) (hN 1) (hΛ 0) (hΛ 1)
    (leftColorIntensity_le_two hBn hBquarter 0) (leftColorIntensity_le_two hBn hBquarter 1)
    (leftPrefixRankTime_isStoppingTime B 0) (leftPrefixRankTime_isStoppingTime B 1)
    (fun sample ↦ leftPrefix_sorted_injective _ sample (leftEventTime_injective n B 0 sample))
    (fun sample ↦ leftPrefix_sorted_injective _ sample (leftEventTime_injective n B 1 sample))
    (leftRateExitTime_isStoppingTime hBn)
    (fun t sample ht ↦ (leftPrefix_intensity_mem_Icc hBn 0 t sample ht).1)
    (fun t sample ht ↦ (leftPrefix_intensity_mem_Icc hBn 1 t sample ht).1)
    (fun t sample ht ↦ (leftPrefix_intensity_mem_Icc hBn 0 t sample ht).2)
    (fun t sample ht ↦ (leftPrefix_intensity_mem_Icc hBn 1 t sample ht).2)
    (measurable_leftPrefixGap hBn 0 1) (measurable_leftPrefixGap hBn 1 0)
    (leftPrefixGap_nonneg B 0 1) (leftPrefixGap_nonneg B 1 0)
    (leftPrefixGap_retained B 0 1) (leftPrefixGap_retained B 1 0)
    (fun r ↦ leftPrefixCurrent_at_capped_stopping_stronglyMeasurable B
      (leftPrefixRankTime_isStoppingTime B 0 r))
    (fun r ↦ leftPrefixCurrent_at_capped_stopping_stronglyMeasurable B
      (leftPrefixRankTime_isStoppingTime B 1 r))
    (fun r ↦ leftPrefixCurrent_at_capped_stopping_sq_integrable B
      (leftPrefixRankTime_isStoppingTime B 0 r))
    (fun r ↦ leftPrefixCurrent_at_capped_stopping_sq_integrable B
      (leftPrefixRankTime_isStoppingTime B 1 r))
    (by simpa only [hcount, hcur] using htailPlus)
    (by simpa only [hcount, hcur, abs_sub_comm] using htailMinus)
    (leftPrefixMomentCharge_boundedSimplePredictable hBn _ _)
    (hA 0) (hA 1) (leftPrefix_occupation_integrable hBn)
    (leftPrefix_occupation_integrableOn hBn)
  simpa only [stoppedLeftPrefixEnergy, show (2 : ℝ) * 2 = 4 by norm_num] using hresult

private theorem leftPrefix_timeMeasure_singleton_zero (a : ℝ≥0) :
    timeMeasure ({a} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton a)]
  rw [Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton a))]
  have hpre : Real.toNNReal ⁻¹' ({a} : Set ℝ≥0) ∩ Ici (0 : ℝ) =
      ({(a : ℝ)} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hxa, hx0⟩
      have hxcoe : Real.toNNReal x = Real.toNNReal (a : ℝ) := by simpa using hxa
      exact (Real.toNNReal_eq_toNNReal_iff hx0 a.2).mp hxcoe
    · intro hxa
      subst x
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

private theorem leftPrefix_countBefore_ae_eq_count
    {m : ℕ} (ξ : Fin m → FiniteSample n → WithTop ℝ≥0) (sample : FiniteSample n) :
    ∀ᵐ t ∂timeMeasure, countBefore (finiteEventCountTop ξ) t sample =
      finiteEventCountTop ξ t sample := by
  have hi (i : Fin m) : ∀ᵐ t : ℝ≥0 ∂timeMeasure, ξ i sample ≠ (t : WithTop ℝ≥0) := by
    rcases eq_or_ne (ξ i sample) ⊤ with htop | hfin
    · exact ae_of_all _ fun t ↦ by rw [htop]; exact WithTop.top_ne_coe
    · lift ξ i sample to ℝ≥0 using hfin with s hs
      have h : ∀ᵐ t ∂timeMeasure, t ≠ s := by
        apply ae_iff.mpr
        simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
          leftPrefix_timeMeasure_singleton_zero s
      filter_upwards [h] with t ht
      intro heq
      exact ht (WithTop.coe_injective heq).symm
  filter_upwards [ae_all_iff.mpr hi] with t ht
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 1
  apply Finset.filter_congr
  intro i _
  exact lt_iff_le_and_ne.trans (and_iff_left (ht i))

private theorem leftPrefix_boundary_sq_bound (x : ℝ) (sample : FiniteSample n) :
    ‖leftBoundaryCurrent n x sample ^ 2‖ ≤ (n : ℝ) ^ 2 := by
  let p := leftBoundaryRankThreshold n x
  have hs : sample.leftSourceCountAt p ≤ n := by
    simpa [leftSourceCountAt] using Set.ncard_le_card {i : Fin n | sample.sourceHeight i ≤ p}
  have ht : sample.leftTargetCountAt p ≤ n := by
    simpa [leftTargetCountAt] using Set.ncard_le_card {i : Fin n | sample.targetHeight i ≤ p}
  have hs' : (sample.leftSourceCountAt p : ℝ) ≤ n := by exact_mod_cast hs
  have ht' : (sample.leftTargetCountAt p : ℝ) ≤ n := by exact_mod_cast ht
  have habs : |(sample.leftSourceCountAt p : ℝ) - sample.leftTargetCountAt p| ≤ (n : ℝ) :=
    abs_le.mpr ⟨by linarith [(show (0 : ℝ) ≤ sample.leftSourceCountAt p by positivity)],
      by linarith [(show (0 : ℝ) ≤ sample.leftTargetCountAt p by positivity)]⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [leftBoundaryCurrent, leftBoundaryCurrentAt, p, sq_abs] using
    pow_le_pow_left₀ (abs_nonneg _) habs 2

private theorem leftPrefix_boundary_area_integrable (B : ℝ≥0) :
    Integrable (fun sample : FiniteSample n ↦
      ∫ t in Ioc (0 : ℝ≥0) B, leftBoundaryCurrent n t sample ^ 2 ∂timeMeasure)
      (finiteSampleLaw n) := by
  have hm : StronglyMeasurable (fun p : ℝ≥0 × FiniteSample n ↦
      leftBoundaryCurrent n p.1 p.2 ^ 2) :=
    ((measurable_leftBoundaryCurrent.comp
      ((measurable_coe_nnreal_real.comp measurable_fst).prodMk measurable_snd)).pow measurable_const).stronglyMeasurable
  let _ : IsFiniteMeasure (timeMeasure.restrict (Ioc (0 : ℝ≥0) B)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact timeMeasure_Ioc_lt_top 0 B⟩
  refine Integrable.of_bound hm.integral_prod_left'.aestronglyMeasurable
    ((n : ℝ) ^ 2 * B) (ae_of_all _ fun sample ↦ ?_)
  calc
    ‖∫ t in Ioc (0 : ℝ≥0) B, leftBoundaryCurrent n t sample ^ 2 ∂timeMeasure‖ ≤
        ∫ _t in Ioc (0 : ℝ≥0) B, (n : ℝ) ^ 2 ∂timeMeasure :=
      norm_integral_le_of_norm_le (integrableOn_const (timeMeasure_Ioc_lt_top 0 B).ne)
        (ae_of_all _ fun t ↦ leftPrefix_boundary_sq_bound t sample)
    _ = (n : ℝ) ^ 2 * B := by
      rw [integral_timeMeasure_eq_intervalIntegral _ 0 B (by simp)]
      simp [mul_comm]

/-- The actual stopped left-current occupation is at most `B + B²` in expectation. -/
theorem integral_leftPrefix_occupation_le
    (hn : 0 < n) {B : ℝ≥0} (hBn : (B : ℝ) < n) :
    (∫ sample : FiniteSample n, stoppedCurrentOccupation (leftRateExitTime n B)
      (leftPrefixCurrent B) B sample ∂(finiteSampleLaw n)) ≤ (B : ℝ) + (B : ℝ) ^ 2 := by
  let area : FiniteSample n → ℝ := fun sample ↦
    ∫ t in Ioc (0 : ℝ≥0) B, leftBoundaryCurrent n t sample ^ 2 ∂timeMeasure
  have harea : Integrable area (finiteSampleLaw n) := leftPrefix_boundary_area_integrable B
  have hdom : ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      stoppedCurrentOccupation (leftRateExitTime n B) (leftPrefixCurrent B) B sample ≤
        (B : ℝ) + area sample := by
    filter_upwards [ae_mem_leftHeightGenericEvent n] with sample hgood
    have hbound : IntegrableOn (fun t : ℝ≥0 ↦ leftBoundaryCurrent n t sample ^ 2)
        (Ioc 0 B) timeMeasure := by
      have hm : StronglyMeasurable (fun t : ℝ≥0 ↦ leftBoundaryCurrent n t sample ^ 2) :=
        ((measurable_leftBoundaryCurrent.comp
        (measurable_coe_nnreal_real.prodMk (measurable_const : Measurable (fun _ : ℝ≥0 ↦ sample)))).pow measurable_const).stronglyMeasurable
      exact Measure.integrableOn_of_bounded (timeMeasure_Ioc_lt_top 0 B).ne
        hm.aestronglyMeasurable (ae_of_all _ fun t ↦ leftPrefix_boundary_sq_bound t sample)
    calc
      stoppedCurrentOccupation (leftRateExitTime n B) (leftPrefixCurrent B) B sample ≤
          ∫ t in Ioc (0 : ℝ≥0) B, 1 + leftBoundaryCurrent n t sample ^ 2 ∂timeMeasure := by
        apply integral_mono_ae (leftPrefix_occupation_integrableOn hBn sample)
          ((integrableOn_const (timeMeasure_Ioc_lt_top 0 B).ne).add hbound)
        filter_upwards [ae_restrict_mem measurableSet_Ioc,
          ae_restrict_of_ae (leftPrefix_countBefore_ae_eq_count
            (fun i ↦ leftEventTime n B (0, i)) sample),
          ae_restrict_of_ae (leftPrefix_countBefore_ae_eq_count
            (fun i ↦ leftEventTime n B (1, i)) sample)] with t ht hs htarg
        have hcur : leftPrefixCurrent B t sample = leftBoundaryCurrent n t sample := by
          change countBefore (leftColorCount n B 0) t sample = _ at hs
          change countBefore (leftColorCount n B 1) t sample = _ at htarg
          simp only [leftPrefixCurrent, leftCurrentOfCounts, zero_add, Int.cast_sub,
            Int.cast_natCast, hs, htarg]
          change (leftSourceCountingProcess n B t sample : ℝ) -
            leftTargetCountingProcess n B t sample = _
          rw [leftSourceCountingProcess_eq_leftSourceCountAt_of_good hn ht.2 hBn.le hgood,
            leftTargetCountingProcess_eq_leftTargetCountAt_of_good hn ht.2 hBn.le hgood]
          rfl
        rw [hcur]
        unfold throughStopMask
        split_ifs
        · simp
        · simp only [zero_mul]
          exact add_nonneg (by norm_num) (sq_nonneg _)
      _ = (B : ℝ) + area sample := by
        rw [integral_add (integrableOn_const (C := (1 : ℝ)) (timeMeasure_Ioc_lt_top 0 B).ne) hbound]
        congr 1
        rw [integral_timeMeasure_eq_intervalIntegral _ 0 B (by simp)]
        simp
  calc
    _ ≤ ∫ sample, (B : ℝ) + area sample ∂(finiteSampleLaw n) :=
      integral_mono_ae (leftPrefix_occupation_integrable hBn) ((integrable_const _).add harea) hdom
    _ = (B : ℝ) + ∫ sample, area sample ∂(finiteSampleLaw n) := by
      rw [integral_add (integrable_const _) harea]
      congr 1
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (B : ℝ) + (B : ℝ) ^ 2 := by
      apply add_le_add_right
      have heq (sample : FiniteSample n) : area sample =
          ∫ x : ℝ in Ioc 0 (B : ℝ), leftBoundaryCurrent n x sample ^ 2 := by
        dsimp [area]
        rw [integral_timeMeasure_eq_intervalIntegral _ 0 B (by simp)]
        simp only [NNReal.coe_zero]
        rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (B : ℝ) from B.2)]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simp [Real.toNNReal_of_nonneg hx.1.le]
      simp_rw [heq]
      exact expected_leftBoundaryArea_le hn B.2 hBn.le

/-- Genuine left-prefix estimate, with only the deterministic scale assumptions. -/
theorem stoppedLeftPrefixEnergy_integrable_and_integral_le
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    Integrable (stoppedLeftPrefixEnergy (n := n) B) (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n, stoppedLeftPrefixEnergy B sample ∂(finiteSampleLaw n)) ≤
        (4 * (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
          2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2)) *
          ((B : ℝ) + (B : ℝ) ^ 2) := by
  have hBn : (B : ℝ) < n := by have hb : 0 < (B : ℝ) := hB; nlinarith
  obtain ⟨hint, hbound⟩ := stoppedLeftPrefixEnergy_integrable_and_integral_le_occupation
    hn hB hBquarter
  exact ⟨hint, hbound.trans (mul_le_mul_of_nonneg_left
    (integral_leftPrefix_occupation_le hn hBn) (by positivity))⟩

private theorem leftPrefix_capped_event_eq_min (B : ℝ≥0) (label : LeftHeightLabel n)
    {sample : FiniteSample n} (hgood : sample ∈ leftHeightGenericEvent n) :
    (cappedStoppingValue B (leftEventTime n B label) sample : ℝ) =
      min ((n : ℝ) * leftHeightCoordinate label sample) B := by
  have hx0 : 0 ≤ (n : ℝ) * (leftHeightCoordinate label sample : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) (leftHeightCoordinate label sample).2.1
  by_cases hxB : (n : ℝ) * (leftHeightCoordinate label sample : ℝ) ≤ B
  · have hnn : Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) ≤ B :=
      (Real.toNNReal_le_iff_le_coe).mpr hxB
    have hcap : cappedStoppingValue B (leftEventTime n B label) sample =
        Real.toNNReal ((n : ℝ) * (leftHeightCoordinate label sample : ℝ)) := by
      apply WithTop.coe_injective
      rw [coe_cappedStoppingValue]
      simp only [leftEventTime, hgood, ite_true, leftRawEventTime, hxB, ite_true]
      exact min_eq_left (WithTop.coe_le_coe.mpr hnn)
    rw [hcap, min_eq_left hxB]
    exact Real.coe_toNNReal _ hx0
  · have hcap : cappedStoppingValue B (leftEventTime n B label) sample = B := by
      apply WithTop.coe_injective
      rw [coe_cappedStoppingValue]
      simp only [leftEventTime, hgood, ite_true, leftRawEventTime, hxB, ite_false]
      exact min_eq_right le_top
    rw [hcap, min_eq_right (le_of_not_ge hxB)]

private theorem leftPrefix_capped_rank_eq_sorted_capped (B : ℝ≥0) (color : Fin 2)
    (r : Fin n) (sample : FiniteSample n) :
    (cappedStoppingValue B (leftPrefixRankTime B color r) sample : ℝ) =
      (fun i ↦ (cappedStoppingValue B (leftEventTime n B (color, i)) sample : ℝ))
        (Tuple.sort (fun i ↦ (cappedStoppingValue B
          (leftEventTime n B (color, i)) sample : ℝ)) r) := by
  let values : Fin n → WithTop ℝ≥0 := fun i ↦ leftEventTime n B (color, i) sample
  let clipped : Fin n → ℝ := fun i ↦
    (cappedStoppingValue B (leftEventTime n B (color, i)) sample : ℝ)
  have hm : Monotone (clipped ∘ Tuple.sort values) := by
    intro i j hij
    apply NNReal.coe_le_coe.mpr
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min (Tuple.monotone_sort values hij) le_rfl
  exact congrFun (Tuple.unique_monotone hm (Tuple.monotone_sort clipped)) r

theorem leftPrefix_capped_source_rank_eq_graph_prefix
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B T : ℝ≥0) (r : Fin n) {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n) :
    (cappedStoppingValue B (leftPrefixRankTime B 0 r) sample : ℝ) =
      min (sample.graphSourceIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r) B := by
  rw [leftPrefix_capped_rank_eq_sorted_capped]
  have heq : (fun i ↦ (cappedStoppingValue B (leftEventTime n B (0, i)) sample : ℝ)) =
      (fun i ↦ min (sample.sourceIntersection
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i) (B : ℝ)) := by
    funext i
    rw [leftPrefix_capped_event_eq_min B (0, i) hgood,
      sample.leftPrefix_sourceIntersection_horizon_min_left hlam0 hlamHalf B T i]
    rfl
  rw [heq, ← leftPrefix_tuple_sort_min_commutes]
  rfl

theorem leftPrefix_capped_target_rank_eq_graph_prefix
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B T : ℝ≥0) (r : Fin n) {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n) :
    (cappedStoppingValue B (leftPrefixRankTime B 1 r) sample : ℝ) =
      min (sample.graphTargetIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r) B := by
  rw [leftPrefix_capped_rank_eq_sorted_capped]
  have heq : (fun i ↦ (cappedStoppingValue B (leftEventTime n B (1, i)) sample : ℝ)) =
      (fun i ↦ min (sample.targetIntersection
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i) (B : ℝ)) := by
    funext i
    rw [leftPrefix_capped_event_eq_min B (1, i) hgood,
      sample.leftPrefix_targetIntersection_horizon_min_left hlam0 hlamHalf B T i]
    rfl
  rw [heq, ← leftPrefix_tuple_sort_min_commutes]
  rfl

/-- If the left rate interval survives through `B`, the stopped energy is exactly the
prefix part of the increasing graph-matching energy. -/
theorem stoppedLeftPrefixEnergy_eq_graph_prefix_of_survival
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B T : ℝ≥0) {sample : FiniteSample n}
    (hgood : sample ∈ leftHeightGenericEvent n)
    (hsurvival : leftRateExitTime n B sample = (B : WithTop ℝ≥0)) :
    stoppedLeftPrefixEnergy B sample =
      ∑ r : Fin n,
        (min (sample.graphTargetIntersectionAtRank
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r) (B : ℝ) -
        min (sample.graphSourceIntersectionAtRank
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r) (B : ℝ)) ^ 2 := by
  have hcap (color : Fin 2) (r : Fin n) :
      cappedStoppingValue B
        (fun ω ↦ min (leftPrefixRankTime B color r ω) (leftRateExitTime n B ω)) sample =
      cappedStoppingValue B (leftPrefixRankTime B color r) sample := by
    apply WithTop.coe_injective
    simp only [coe_cappedStoppingValue, hsurvival, min_assoc, min_self]
  unfold stoppedLeftPrefixEnergy stoppedRankGapEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold leftPrefixGap
  rw [hcap 1 r, hcap 0 r,
    leftPrefix_capped_source_rank_eq_graph_prefix hlam0 hlamHalf B T r hgood,
    leftPrefix_capped_target_rank_eq_graph_prefix hlam0 hlamHalf B T r hgood]
  generalize min (sample.graphTargetIntersectionAtRank _ r) (B : ℝ) = b
  generalize min (sample.graphSourceIntersectionAtRank _ r) (B : ℝ) = a
  by_cases hab : a ≤ b
  · rw [max_eq_right (sub_nonneg.mpr hab), max_eq_left (sub_nonpos.mpr hab)]
    ring
  · have hba := le_of_not_ge hab
    rw [max_eq_left (sub_nonpos.mpr hba), max_eq_right (sub_nonneg.mpr hba)]
    ring

end OTSelector.FiniteSample
