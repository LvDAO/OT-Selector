import OTSelector.Feedback.FeedbackTerminalGraphGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite rank energy from interval density

An open-interval lower count controls each retained edge by current occupation. Summing over
increasing edges charges the current exactly once per crossing, giving its square. The argument
is deterministic and allows repeated endpoints.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector

private theorem sorted_below_card_le_rank {n : ℕ} (v : Fin n → ℝ) (r : Fin n) :
    (Finset.univ.filter fun i ↦ v i < v (Tuple.sort v r)).card ≤ r.val := by
  have heq : (Finset.univ.filter fun i ↦ v (Tuple.sort v i) < v (Tuple.sort v r)).card =
      (Finset.univ.filter fun i ↦ v i < v (Tuple.sort v r)).card := by
    apply Finset.card_equiv (Tuple.sort v)
    intro i
    simp
  have hiff := Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (j := r) (a := v (Tuple.sort v r)) (Tuple.monotone_sort v)
  simp only [Function.comp_apply, heq, lt_self_iff_false, iff_false] at hiff
  omega

/-- The count below an interior cut plus the open count up to rank `r` is at most `r`. -/
private theorem count_cut_add_open_le_rank {n : ℕ} (v : Fin n → ℝ) (r : Fin n)
    (x : ℝ) (hx : x < v (Tuple.sort v r)) :
    (Finset.univ.filter fun i ↦ v i ≤ x).card +
      (Finset.univ.filter fun i ↦ x < v i ∧ v i < v (Tuple.sort v r)).card ≤ r.val := by
  let s := Finset.univ.filter fun i ↦ v i ≤ x
  let t := Finset.univ.filter fun i ↦ x < v i ∧ v i < v (Tuple.sort v r)
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : v i ≤ x := (Finset.mem_filter.mp hi).2
    have hj' : x < v i := (Finset.mem_filter.mp hj).2.1
    exact (not_lt_of_ge hi') hj'
  have hsub : s ∪ t ⊆ Finset.univ.filter fun i ↦ v i < v (Tuple.sort v r) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ((Finset.mem_filter.mp hi).2).trans_lt hx
    · exact (Finset.mem_filter.mp hi).2.2
  have h := (Finset.card_le_card hsub).trans (sorted_below_card_le_rank v r)
  rw [Finset.card_union_of_disjoint hdis] at h
  exact h

namespace FiniteSample
variable {n : ℕ} (sample : FiniteSample n)

/-- Real-valued rank discrepancy of an arbitrary finite graph matching. -/
noncomputable def graphRankCurrent {lam : ℝ} (graph : FeedbackGraph lam) (x : ℝ) : ℝ :=
  (sample.graphSourceCutCount graph x : ℝ) - sample.graphTargetCutCount graph x

/-- Open-interval counts of physical source graph intersections. -/
noncomputable def graphSourceOpenIntervalCount {lam : ℝ} (graph : FeedbackGraph lam)
    (s t : ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ s < sample.sourceIntersection graph i ∧
    sample.sourceIntersection graph i < t).card

/-- Open-interval counts of physical target graph intersections. -/
noncomputable def graphTargetOpenIntervalCount {lam : ℝ} (graph : FeedbackGraph lam)
    (s t : ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ s < sample.targetIntersection graph i ∧
    sample.targetIntersection graph i < t).card

theorem graphCrossingRankCount_cast_eq_abs_current {lam : ℝ}
    (graph : FeedbackGraph lam) (x : ℝ) :
    (sample.graphCrossingRankCount graph x : ℝ) = |sample.graphRankCurrent graph x| := by
  rw [sample.graphCrossingRankCount_eq_rankCountDiscrepancy]
  simp only [graphRankCountDiscrepancy, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub,
    Int.cast_natCast, graphRankCurrent]

/-- At an interior point of a source-first edge, every target before its endpoint is part of
its positive crossing current. -/
theorem graphTargetOpenIntervalCount_le_current_of_source_first {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) (x : ℝ)
    (hs : sample.graphSourceIntersectionAtRank graph r ≤ x)
    (ht : x < sample.graphTargetIntersectionAtRank graph r) :
    (sample.graphTargetOpenIntervalCount graph x
      (sample.graphTargetIntersectionAtRank graph r) : ℝ) ≤ sample.graphRankCurrent graph x := by
  have hsource : r.val < sample.graphSourceCutCount graph x :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card
      (sample.sourceIntersection graph) r x).mp hs
  have htarget := count_cut_add_open_le_rank (sample.targetIntersection graph) r x ht
  change sample.graphTargetCutCount graph x +
    sample.graphTargetOpenIntervalCount graph x
      (sample.graphTargetIntersectionAtRank graph r) ≤ r.val at htarget
  have hsum : sample.graphTargetCutCount graph x +
      sample.graphTargetOpenIntervalCount graph x
        (sample.graphTargetIntersectionAtRank graph r) ≤ sample.graphSourceCutCount graph x :=
    htarget.trans hsource.le
  have hreal : (sample.graphTargetCutCount graph x : ℝ) +
      sample.graphTargetOpenIntervalCount graph x
        (sample.graphTargetIntersectionAtRank graph r) ≤ sample.graphSourceCutCount graph x := by
    exact_mod_cast hsum
  unfold graphRankCurrent
  linarith

/-- The symmetric bound for a target-first edge. -/
theorem graphSourceOpenIntervalCount_le_neg_current_of_target_first {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) (x : ℝ)
    (ht : sample.graphTargetIntersectionAtRank graph r ≤ x)
    (hs : x < sample.graphSourceIntersectionAtRank graph r) :
    (sample.graphSourceOpenIntervalCount graph x
      (sample.graphSourceIntersectionAtRank graph r) : ℝ) ≤ -sample.graphRankCurrent graph x := by
  have htarget : r.val < sample.graphTargetCutCount graph x :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card
      (sample.targetIntersection graph) r x).mp ht
  have hsource := count_cut_add_open_le_rank (sample.sourceIntersection graph) r x hs
  change sample.graphSourceCutCount graph x +
    sample.graphSourceOpenIntervalCount graph x
      (sample.graphSourceIntersectionAtRank graph r) ≤ r.val at hsource
  have hsum : sample.graphSourceCutCount graph x +
      sample.graphSourceOpenIntervalCount graph x
        (sample.graphSourceIntersectionAtRank graph r) ≤ sample.graphTargetCutCount graph x :=
    hsource.trans htarget.le
  have hreal : (sample.graphSourceCutCount graph x : ℝ) +
      sample.graphSourceOpenIntervalCount graph x
        (sample.graphSourceIntersectionAtRank graph r) ≤ sample.graphTargetCutCount graph x := by
    exact_mod_cast hsum
  unfold graphRankCurrent
  linarith

theorem measurable_graphRankCurrent {lam : ℝ} (graph : FeedbackGraph lam) :
    Measurable (sample.graphRankCurrent graph) := by
  have hm (v : Fin n → ℝ) : Measurable (fun x : ℝ ↦
      ((Finset.univ.filter fun i ↦ v i ≤ x).card : ℝ)) := by
    simp_rw [← Finset.sum_boole]
    exact Finset.measurable_sum _ fun i _ ↦
      Measurable.ite (measurableSet_le measurable_const measurable_id)
        measurable_const measurable_const
  exact (hm (sample.sourceIntersection graph)).sub (hm (sample.targetIntersection graph))

theorem abs_graphRankCurrent_le {lam : ℝ} (graph : FeedbackGraph lam) (x : ℝ) :
    |sample.graphRankCurrent graph x| ≤ n := by
  have hs : sample.graphSourceCutCount graph x ≤ n := by
    simpa [graphSourceCutCount] using Finset.card_filter_le
      (Finset.univ : Finset (Fin n)) (fun i ↦ sample.sourceIntersection graph i ≤ x)
  have ht : sample.graphTargetCutCount graph x ≤ n := by
    simpa [graphTargetCutCount] using Finset.card_filter_le
      (Finset.univ : Finset (Fin n)) (fun i ↦ sample.targetIntersection graph i ≤ x)
  have hs' : (sample.graphSourceCutCount graph x : ℝ) ≤ n := by exact_mod_cast hs
  have ht' : (sample.graphTargetCutCount graph x : ℝ) ≤ n := by exact_mod_cast ht
  unfold graphRankCurrent
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg' (α := ℝ) (sample.graphSourceCutCount graph x)],
    by linarith [Nat.cast_nonneg' (α := ℝ) (sample.graphTargetCutCount graph x)]⟩

theorem integrableOn_abs_graphRankCurrent {lam : ℝ} (graph : FeedbackGraph lam) (a b : ℝ) :
    IntegrableOn (fun x ↦ |sample.graphRankCurrent graph x|) (Icc a b) := by
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (sample.measurable_graphRankCurrent graph).abs.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by simpa using sample.abs_graphRankCurrent_le graph x

theorem integrableOn_sq_graphRankCurrent {lam : ℝ} (graph : FeedbackGraph lam) (a b : ℝ) :
    IntegrableOn (fun x ↦ sample.graphRankCurrent graph x ^ 2) (Icc a b) := by
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    ((sample.measurable_graphRankCurrent graph).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (sample.abs_graphRankCurrent_le graph x) 2

/-- Density hypothesis on physical intervals, including an additive discretization error. -/
def GraphIntervalLowerDensity {lam : ℝ} (graph : FeedbackGraph lam)
    (a b c error : ℝ) : Prop :=
  ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
    c * (t - s) - error ≤ (sample.graphSourceOpenIntervalCount graph s t : ℝ) ∧
    c * (t - s) - error ≤ (sample.graphTargetOpenIntervalCount graph s t : ℝ)

private theorem graphRankCurrent_abs_lower_of_intervalDensity {lam : ℝ}
    (graph : FeedbackGraph lam) {a b c error : ℝ} (herr : 0 ≤ error)
    (hdensity : sample.GraphIntervalLowerDensity graph a b c error)
    (r : Fin n) (hright : sample.graphRankRightEndpoint graph r ≤ b)
    (x : ℝ) (hx : x ∈ Icc (max a (sample.graphRankLeftEndpoint graph r))
      (sample.graphRankRightEndpoint graph r)) :
    c * (sample.graphRankRightEndpoint graph r - x) - error ≤
      |sample.graphRankCurrent graph x| := by
  have hax : a ≤ x := (le_max_left _ _).trans hx.1
  have hleft : sample.graphRankLeftEndpoint graph r ≤ x := (le_max_right _ _).trans hx.1
  rcases eq_or_lt_of_le hx.2 with heq | hstrict
  · rw [heq, sub_self, mul_zero, zero_sub]
    exact (neg_nonpos.mpr herr).trans (abs_nonneg _)
  · by_cases hs : sample.graphSourceIntersectionAtRank graph r ≤
        sample.graphTargetIntersectionAtRank graph r
    · have hsource : sample.graphSourceIntersectionAtRank graph r ≤ x := by
        simpa only [graphRankLeftEndpoint, min_eq_left hs] using hleft
      have htarget : x < sample.graphTargetIntersectionAtRank graph r := by
        simpa only [graphRankRightEndpoint, max_eq_right hs] using hstrict
      have hden := (hdensity x _ hax hx.2 hright).2
      rw [graphRankRightEndpoint, max_eq_right hs] at hden ⊢
      exact hden.trans ((sample.graphTargetOpenIntervalCount_le_current_of_source_first
        graph r x hsource htarget).trans (le_abs_self _))
    · have ht := le_of_not_ge hs
      have htarget : sample.graphTargetIntersectionAtRank graph r ≤ x := by
        simpa only [graphRankLeftEndpoint, min_eq_right ht] using hleft
      have hsource : x < sample.graphSourceIntersectionAtRank graph r := by
        simpa only [graphRankRightEndpoint, max_eq_left ht] using hstrict
      have hden := (hdensity x _ hax hx.2 hright).1
      rw [graphRankRightEndpoint, max_eq_left ht] at hden ⊢
      exact hden.trans ((sample.graphSourceOpenIntervalCount_le_neg_current_of_target_first
        graph r x htarget hsource).trans (neg_le_abs _))

private theorem integral_affine_distance (u v c error : ℝ) (huv : u ≤ v) :
    (∫ x in Icc u v, c * (v - x) - error) = c / 2 * (v - u) ^ 2 - error * (v - u) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- One retained suffix is controlled by current occupation on that suffix. -/
theorem graphRankSuffix_sq_le_occupation {lam : ℝ} (graph : FeedbackGraph lam)
    {a b c error : ℝ} (hc : 0 < c) (herr : 0 ≤ error)
    (hdensity : sample.GraphIntervalLowerDensity graph a b c error)
    (r : Fin n) (ha : a ≤ sample.graphRankRightEndpoint graph r)
    (hb : sample.graphRankRightEndpoint graph r ≤ b) :
    (sample.graphRankRightEndpoint graph r - max a (sample.graphRankLeftEndpoint graph r)) ^ 2 ≤
      (4 / c) * (∫ x in Icc (max a (sample.graphRankLeftEndpoint graph r))
        (sample.graphRankRightEndpoint graph r), |sample.graphRankCurrent graph x|) +
      4 * error ^ 2 / c ^ 2 := by
  let u := max a (sample.graphRankLeftEndpoint graph r)
  let v := sample.graphRankRightEndpoint graph r
  have huv : u ≤ v := max_le ha min_le_max
  have hint : c / 2 * (v - u) ^ 2 - error * (v - u) ≤
      ∫ x in Icc u v, |sample.graphRankCurrent graph x| := by
    rw [← integral_affine_distance u v c error huv]
    apply setIntegral_mono_on (Continuous.integrableOn_Icc (by fun_prop))
      (sample.integrableOn_abs_graphRankCurrent graph u v) measurableSet_Icc
    intro x hx
    exact sample.graphRankCurrent_abs_lower_of_intervalDensity graph herr hdensity r hb x hx
  have hscaled := mul_le_mul_of_nonneg_left hint hc.le
  have heq (I : ℝ) : (4 / c) * I + 4 * error ^ 2 / c ^ 2 =
      (4 * c * I + 4 * error ^ 2) / c ^ 2 := by field_simp
  change (v - u) ^ 2 ≤ _
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith [sq_nonneg (c * (v - u) / 2 - error)]

/-- Ranks with right endpoint in `(a,b]`; their portion left of `a` is not charged here. -/
noncomputable def graphRightRetainedRankSet {lam : ℝ} (graph : FeedbackGraph lam)
    (a b : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun r ↦ a < sample.graphRankRightEndpoint graph r ∧
    sample.graphRankRightEndpoint graph r ≤ b

noncomputable def graphRightRetainedSuffixEnergy {lam : ℝ} (graph : FeedbackGraph lam)
    (a b : ℝ) : ℝ :=
  ∑ r ∈ sample.graphRightRetainedRankSet graph a b,
    (sample.graphRankRightEndpoint graph r - max a (sample.graphRankLeftEndpoint graph r)) ^ 2

private theorem retained_suffix_interval_subset {lam : ℝ} (graph : FeedbackGraph lam)
    (a b : ℝ) (r : Fin n) (hr : r ∈ sample.graphRightRetainedRankSet graph a b) :
    Ico (max a (sample.graphRankLeftEndpoint graph r)) (sample.graphRankRightEndpoint graph r) ⊆
      Icc a b := by
  have hb := (Finset.mem_filter.mp hr).2.2
  intro x hx
  exact ⟨(le_max_left _ _).trans hx.1, hx.2.le.trans hb⟩

private theorem suffix_occupation_sum_integrand_le_sq {lam : ℝ}
    (graph : FeedbackGraph lam) (a b x : ℝ) :
    (∑ r ∈ sample.graphRightRetainedRankSet graph a b,
      (Ico (max a (sample.graphRankLeftEndpoint graph r))
        (sample.graphRankRightEndpoint graph r)).indicator
        (fun x ↦ |sample.graphRankCurrent graph x|) x) ≤ sample.graphRankCurrent graph x ^ 2 := by
  let s := (sample.graphRightRetainedRankSet graph a b).filter fun r ↦
    x ∈ Ico (max a (sample.graphRankLeftEndpoint graph r)) (sample.graphRankRightEndpoint graph r)
  have hsub : s ⊆ sample.graphCrossingRankSet graph x := by
    intro r hr
    have hx := (Finset.mem_filter.mp hr).2
    simp only [graphCrossingRankSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(le_max_right _ _).trans hx.1, hx.2⟩
  have hcard : (s.card : ℝ) ≤ sample.graphCrossingRankCount graph x := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    _ = (s.card : ℝ) * |sample.graphRankCurrent graph x| := by
      simp only [Set.indicator_apply]
      rw [← Finset.sum_filter]
      simp only [s, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (sample.graphCrossingRankCount graph x : ℝ) * |sample.graphRankCurrent graph x| :=
      mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
    _ = sample.graphRankCurrent graph x ^ 2 := by
      rw [sample.graphCrossingRankCount_cast_eq_abs_current]
      rw [← sq_abs (sample.graphRankCurrent graph x), pow_two]

/-- Summing the per-edge occupation charge is dominated by the square-current area. -/
theorem graphRightRetainedSuffix_occupation_sum_le {lam : ℝ}
    (graph : FeedbackGraph lam) (a b : ℝ) :
    (∑ r ∈ sample.graphRightRetainedRankSet graph a b,
      ∫ x in Icc (max a (sample.graphRankLeftEndpoint graph r))
        (sample.graphRankRightEndpoint graph r), |sample.graphRankCurrent graph x|) ≤
      ∫ x in Icc a b, sample.graphRankCurrent graph x ^ 2 := by
  let f : Fin n → ℝ → ℝ := fun r ↦
    (Ico (max a (sample.graphRankLeftEndpoint graph r))
      (sample.graphRankRightEndpoint graph r)).indicator
      (fun x ↦ |sample.graphRankCurrent graph x|)
  have hf (r : Fin n) : IntegrableOn (f r) (Icc a b) :=
    (sample.integrableOn_abs_graphRankCurrent graph a b).indicator measurableSet_Ico
  have heq (r : Fin n) (hr : r ∈ sample.graphRightRetainedRankSet graph a b) :
      (∫ x in Icc (max a (sample.graphRankLeftEndpoint graph r))
        (sample.graphRankRightEndpoint graph r), |sample.graphRankCurrent graph x|) =
        ∫ x in Icc a b, f r x := by
    rw [integral_Icc_eq_integral_Ico, setIntegral_indicator measurableSet_Ico,
      inter_eq_right.mpr (sample.retained_suffix_interval_subset graph a b r hr)]
  simp_rw [Finset.sum_congr rfl heq]
  rw [← integral_finsetSum _ (fun r _ ↦ hf r)]
  apply setIntegral_mono_on (integrable_finsetSum _ fun r _ ↦ hf r)
    (sample.integrableOn_sq_graphRankCurrent graph a b) measurableSet_Icc
  intro x _
  exact sample.suffix_occupation_sum_integrand_le_sq graph a b x

/-- Uniform interval lower density gives a genuine deterministic right-energy bound. -/
theorem graphRightRetainedSuffixEnergy_le_occupation {lam : ℝ}
    (graph : FeedbackGraph lam) {a b c error : ℝ} (hc : 0 < c) (herr : 0 ≤ error)
    (hdensity : sample.GraphIntervalLowerDensity graph a b c error) :
    sample.graphRightRetainedSuffixEnergy graph a b ≤
      (4 / c) * (∫ x in Icc a b, sample.graphRankCurrent graph x ^ 2) +
      (4 / c ^ 2) * (sample.graphTerminalRankCount graph a : ℝ) * error ^ 2 := by
  have hcard : (sample.graphRightRetainedRankSet graph a b).card ≤
      sample.graphTerminalRankCount graph a := by
    apply Finset.card_le_card
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.1⟩
  calc
    _ ≤ ∑ r ∈ sample.graphRightRetainedRankSet graph a b,
        ((4 / c) * (∫ x in Icc (max a (sample.graphRankLeftEndpoint graph r))
          (sample.graphRankRightEndpoint graph r), |sample.graphRankCurrent graph x|) +
          4 * error ^ 2 / c ^ 2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact sample.graphRankSuffix_sq_le_occupation graph hc herr hdensity r
        (Finset.mem_filter.mp hr).2.1.le (Finset.mem_filter.mp hr).2.2
    _ = (4 / c) * (∑ r ∈ sample.graphRightRetainedRankSet graph a b,
        ∫ x in Icc (max a (sample.graphRankLeftEndpoint graph r))
          (sample.graphRankRightEndpoint graph r), |sample.graphRankCurrent graph x|) +
          ((sample.graphRightRetainedRankSet graph a b).card : ℝ) * (4 * error ^ 2 / c ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 / c) * (∫ x in Icc a b, sample.graphRankCurrent graph x ^ 2) +
        (sample.graphTerminalRankCount graph a : ℝ) * (4 * error ^ 2 / c ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (sample.graphRightRetainedSuffix_occupation_sum_le graph a b) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

end FiniteSample
end OTSelector
