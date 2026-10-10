import OTSelector.Feedback.FeedbackTerminalAreaGeometry

/-!
# Actual right-boundary energy with the geometric difference bound discharged

The conditional expectation below is taken under the original finite-sample law.  The component
event restricts the resulting inequality, rather than changing that law.  All height assumptions
refer to the actual feedback height at the boundary.  The clipped-area geometry supplies the
constant `D = 8`, so the public results have no conditional-probability-difference premise.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace OTSelector
namespace FiniteSample

variable {n : ℕ}

/-- Actual-sample boundary scalar estimate with the area-difference premise proved from the
right-junction location and the small frozen shear. -/
theorem rightBoundaryScalarCandidate_frozenEnergy_le_of_right_boundary
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xEnd B c C L : ℝ)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd)
    (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (hsourceBounds :
      (rightBoundarySourceUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (htargetBounds :
      (rightBoundaryTargetUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (hgap :
      |(rightBoundaryTargetUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) -
        (rightBoundarySourceUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ)| ≤ L)
    (hq : |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤ L * Real.sqrt B)
    (hqSmall : |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤ B / 8) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd) sample ≤
      3 * (2 * C + (L * (1 + C * 8)) ^ 2) * B ^ 2 := by
  have hfrozen := rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
    hlam0 hlamHalf x0 p0 T sample hNoTie
  have hqFrozen : |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| ≤ L * Real.sqrt B := by
    rwa [hfrozen]
  apply rightBoundaryScalarCandidate_frozenEnergy_le
    hlam0 hlamHalf x0 p0 T xEnd B c C L 8 sample hNoTie
    hB hc hC hL (by norm_num) hxEnd hlength hsourceBounds htargetBounds hgap hqFrozen
  intro y hy
  have hsmall : |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| ≤ B / 8 := by
    rwa [hfrozen]
  exact rightBoundaryHistoryProbability_difference_le hn lam (x0 + (T : ℝ)) y B
    (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))
    hboundary (lt_of_lt_of_le zero_lt_one hB) hBn hsmall hy.1.le

/-- Equation (1.32) for the actual frozen continuation through `n + 2 B`.

The only component hypotheses are the paper's two remaining-count bounds, current bound,
height bound, and the small-shear bound already supplied by bulk survival. -/
theorem condExp_rightBoundaryFrozenEnergy_le_of_boundary_components
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T) (B c C L : ℝ)
    (G : Set (FiniteSample n)) (hG : MeasurableSet G)
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2)
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hsourceBounds : ∀ sample ∈ G,
      (rightBoundarySourceUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (htargetBounds : ∀ sample ∈ G,
      (rightBoundaryTargetUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (hgap : ∀ sample ∈ G,
      |(rightBoundaryTargetUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) -
        (rightBoundarySourceUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ)| ≤ L)
    (hq : ∀ sample ∈ G,
      |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤ L * Real.sqrt B)
    (hqSmall : ∀ sample ∈ G,
      |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤ B / 8) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        (fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) ((n : ℝ) + 2 * B)
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n)).restrict G]
      fun _sample ↦ 3 * (2 * C + (L * (1 + C * 8)) ^ 2) * B ^ 2 := by
  have hxEnd : x0 + (T : ℝ) ≤ (n : ℝ) + 2 * B := by
    rw [hboundary]
    linarith
  have hlength : (n : ℝ) + 2 * B - (x0 + (T : ℝ)) ≤ 3 * B := by
    rw [hboundary]
    linarith
  have hcond := condExp_rightBoundaryFrozenEnergy_le
    hn hlam0 hlamHalf x0 p0 T hT0 ((n : ℝ) + 2 * B) hxEnd
  have hcondG := ae_restrict_of_ae (s := G) hcond
  have hNoTieG := ae_restrict_of_ae (s := G)
    (FiniteSample.finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf)
  filter_upwards [hcondG, hNoTieG, ae_restrict_mem hG] with
    sample hconditional hNoTie hsample
  exact hconditional.trans
    (rightBoundaryScalarCandidate_frozenEnergy_le_of_right_boundary
      hn hlam0 hlamHalf x0 p0 T ((n : ℝ) + 2 * B) B c C L sample hNoTie
      hboundary hB hBn hc hC hL hxEnd hlength
      (hsourceBounds sample hsample) (htargetBounds sample hsample)
      (hgap sample hsample) (hq sample hsample) (hqSmall sample hsample))

end FiniteSample
end OTSelector
