import OTSelector.Feedback.Graph

/-!
# Spacelike swept sets

The two half-space families are the deterministic geometric input to predictable deferred
decisions.  Their monotonicity is proved here from the feedback Lipschitz bound and the mark ranges.
-/

namespace OTSelector

/-- Source points swept by the graph by coordinate `x`. -/
def sourceSwept (g : ℝ → ℝ) (x : ℝ) : Set (ℝ × UnitMark) :=
  {z | z.1 + g x * (1 - (z.2 : ℝ)) ≤ x}

/-- Target points swept by the graph by coordinate `x`. -/
def targetSwept (g : ℝ → ℝ) (x : ℝ) : Set (ℝ × UnitMark) :=
  {z | z.1 - g x * (1 + (z.2 : ℝ)) ≤ x}

theorem sourceSwept_mono {lam : ℝ} {g : ℝ → ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hg : RealLipschitz lam g) : Monotone (sourceSwept g) := by
  intro x y hxy z hz
  have hu0 : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
  have hu1 : 1 - (z.2 : ℝ) ≤ 1 := by linarith [z.2.property.1]
  have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
  have hgy : g y - g x ≤ lam * (y - x) := by
    calc
      g y - g x ≤ |g y - g x| := le_abs_self _
      _ ≤ lam * |y - x| := hg x y
      _ = lam * (y - x) := by rw [hdist]
  have hmul : (g y - g x) * (1 - (z.2 : ℝ)) ≤ lam * (y - x) := by
    calc
      (g y - g x) * (1 - (z.2 : ℝ)) ≤
          (lam * (y - x)) * (1 - (z.2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hgy hu0
      _ ≤ lam * (y - x) := by
        have hbase : 0 ≤ lam * (y - x) := mul_nonneg hlam0 (sub_nonneg.mpr hxy)
        nlinarith
  change z.1 + g y * (1 - (z.2 : ℝ)) ≤ y
  change z.1 + g x * (1 - (z.2 : ℝ)) ≤ x at hz
  nlinarith

theorem targetSwept_mono {lam : ℝ} {g : ℝ → ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : 2 * lam ≤ 1) (hg : RealLipschitz lam g) : Monotone (targetSwept g) := by
  intro x y hxy z hz
  have hv0 : 0 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  have hv2 : 1 + (z.2 : ℝ) ≤ 2 := by linarith [z.2.property.2]
  have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
  have hgdrop : g x - g y ≤ lam * (y - x) := by
    calc
      g x - g y ≤ |g y - g x| := by rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ lam * |y - x| := hg x y
      _ = lam * (y - x) := by rw [hdist]
  have hmul : (g x - g y) * (1 + (z.2 : ℝ)) ≤ y - x := by
    calc
      (g x - g y) * (1 + (z.2 : ℝ)) ≤
          (lam * (y - x)) * (1 + (z.2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hgdrop hv0
      _ ≤ y - x := by
        have hyx0 : 0 ≤ y - x := sub_nonneg.mpr hxy
        have hcoeff : lam * (1 + (z.2 : ℝ)) ≤ 1 :=
          (mul_le_mul_of_nonneg_left hv2 hlam0).trans (by simpa [mul_comm] using hlamHalf)
        have hscaled := mul_le_mul_of_nonneg_right hcoeff hyx0
        nlinarith
  change z.1 - g y * (1 + (z.2 : ℝ)) ≤ y
  change z.1 - g x * (1 + (z.2 : ℝ)) ≤ x at hz
  nlinarith

theorem FeedbackGraph.sourceSwept_monotone {lam : ℝ} (graph : FeedbackGraph lam) :
    Monotone (sourceSwept graph.curve) :=
  sourceSwept_mono graph.lam_nonneg (le_trans (le_of_lt graph.lam_lt_half) (by norm_num))
    graph.lipschitz

theorem FeedbackGraph.targetSwept_monotone {lam : ℝ} (graph : FeedbackGraph lam) :
    Monotone (targetSwept graph.curve) :=
  targetSwept_mono graph.lam_nonneg (by linarith [graph.lam_lt_half]) graph.lipschitz

end OTSelector
