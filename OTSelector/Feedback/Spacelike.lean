import OTSelector.Feedback.Graph

/-!
# A2/I4 deterministic spacelike consequences
-/

namespace OTSelector

/-- Macroscopic rescaling `γ(z)=g(nz)/n`. -/
noncomputable def rescaleGraph (g : ℝ → ℝ) (scale : ℝ) (z : ℝ) : ℝ :=
  g (scale * z) / scale

/-- Rescaling preserves the Lipschitz constant.  This is the deterministic part of I4. -/
theorem rescaleGraph_lipschitz {g : ℝ → ℝ} {lam scale : ℝ} (hscale : 0 < scale)
    (hg : RealLipschitz lam g) : RealLipschitz lam (rescaleGraph g scale) := by
  intro x y
  calc
    |rescaleGraph g scale y - rescaleGraph g scale x| =
        |g (scale * y) - g (scale * x)| / scale := by
          rw [rescaleGraph, rescaleGraph, ← sub_div, abs_div, abs_of_pos hscale]
    _ ≤ (lam * |scale * y - scale * x|) / scale :=
      div_le_div_of_nonneg_right (hg (scale * x) (scale * y)) (le_of_lt hscale)
    _ = lam * |y - x| := by
      rw [← mul_sub, abs_mul, abs_of_pos hscale]
      field_simp

end OTSelector
