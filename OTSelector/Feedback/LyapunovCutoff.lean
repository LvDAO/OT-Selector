import OTSelector.Feedback.Lyapunov

/-!
# Deterministic localization for integer Lyapunov increments

The cutoff in this file is purely algebraic.  It replaces an integer state by its projection to
`[-R, R]`, so arbitrary functions on `ℤ` have finite-valued one-step increments after localization.
No stochastic, predictability, martingale, or limiting statement is used here.
-/

namespace OTSelector

/-! ## Integer cutoff and localized increments -/

/-- Projection of an integer state to the interval `[-R, R]`. -/
noncomputable def integerClip (R : ℕ) (k : ℤ) : ℤ :=
  max (-(R : ℤ)) (min (R : ℤ) k)

/-- The upward one-step increment after clipping both endpoints. -/
noncomputable def clippedUpwardIncrement (R : ℕ) (f : ℤ → ℝ) (k : ℤ) : ℝ :=
  f (integerClip R (k + 1)) - f (integerClip R k)

/-- The downward one-step increment after clipping both endpoints. -/
noncomputable def clippedDownwardIncrement (R : ℕ) (f : ℤ → ℝ) (k : ℤ) : ℝ :=
  f (integerClip R (k - 1)) - f (integerClip R k)

/-- The finite set of integer states retained by the cutoff. -/
noncomputable def cutoffStates (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- A finite set containing every difference of two clipped values of `f`. -/
noncomputable def cutoffPairs (R : ℕ) : Finset (ℤ × ℤ) :=
  cutoffStates R ×ˢ cutoffStates R

/-- The finite set of all differences between two retained values of `f`. -/
noncomputable def cutoffDifferenceValues (R : ℕ) (f : ℤ → ℝ) : Set ℝ :=
  (fun p : ℤ × ℤ => f p.1 - f p.2) '' (↑(cutoffPairs R) : Set (ℤ × ℤ))

theorem cutoffStates_nonempty (R : ℕ) : (cutoffStates R).Nonempty := by
  apply Finset.nonempty_Icc.mpr
  omega

theorem cutoffPairs_nonempty (R : ℕ) : (cutoffPairs R).Nonempty := by
  exact (cutoffStates_nonempty R).product (cutoffStates_nonempty R)

theorem integerClip_lower (R : ℕ) (k : ℤ) :
    -(R : ℤ) ≤ integerClip R k := by
  exact le_max_left _ _

theorem integerClip_upper (R : ℕ) (k : ℤ) :
    integerClip R k ≤ (R : ℤ) := by
  apply max_le
  · omega
  · exact min_le_left _ _

theorem integerClip_mem_cutoffStates (R : ℕ) (k : ℤ) :
    integerClip R k ∈ cutoffStates R := by
  rw [cutoffStates, Finset.mem_Icc]
  exact ⟨integerClip_lower R k, integerClip_upper R k⟩

theorem integerClip_eq_self_of_mem {R : ℕ} {k : ℤ}
    (hk : k ∈ cutoffStates R) : integerClip R k = k := by
  rw [cutoffStates, Finset.mem_Icc] at hk
  dsimp [integerClip]
  rw [min_eq_right hk.2, max_eq_right hk.1]

private theorem integerClip_eq_lower_of_le {R : ℕ} {k : ℤ}
    (hk : k ≤ -(R : ℤ)) : integerClip R k = -(R : ℤ) := by
  have hR : -(R : ℤ) ≤ (R : ℤ) := by omega
  dsimp [integerClip]
  rw [min_eq_right (le_trans hk hR), max_eq_left hk]

private theorem integerClip_eq_upper_of_ge {R : ℕ} {k : ℤ}
    (hk : (R : ℤ) ≤ k) : integerClip R k = (R : ℤ) := by
  have hR : -(R : ℤ) ≤ (R : ℤ) := by omega
  dsimp [integerClip]
  rw [min_eq_left hk, max_eq_right hR]

/-! ## Finite values and finite maxima -/

theorem cutoffDifferenceValues_finite (R : ℕ) (f : ℤ → ℝ) :
    (cutoffDifferenceValues R f).Finite := by
  exact (Finset.finite_toSet (cutoffPairs R)).image
    (fun p : ℤ × ℤ => f p.1 - f p.2)

theorem clippedUpwardIncrement_mem_cutoffDifferenceValues
    (R : ℕ) (f : ℤ → ℝ) (k : ℤ) :
    clippedUpwardIncrement R f k ∈ cutoffDifferenceValues R f := by
  change clippedUpwardIncrement R f k ∈
    (fun p : ℤ × ℤ => f p.1 - f p.2) '' (↑(cutoffPairs R) : Set (ℤ × ℤ))
  refine ⟨(integerClip R (k + 1), integerClip R k), ?_, rfl⟩
  exact Finset.mem_coe.mpr <|
    Finset.mem_product.mpr ⟨integerClip_mem_cutoffStates R (k + 1),
      integerClip_mem_cutoffStates R k⟩

theorem clippedDownwardIncrement_mem_cutoffDifferenceValues
    (R : ℕ) (f : ℤ → ℝ) (k : ℤ) :
    clippedDownwardIncrement R f k ∈ cutoffDifferenceValues R f := by
  change clippedDownwardIncrement R f k ∈
    (fun p : ℤ × ℤ => f p.1 - f p.2) '' (↑(cutoffPairs R) : Set (ℤ × ℤ))
  refine ⟨(integerClip R (k - 1), integerClip R k), ?_, rfl⟩
  exact Finset.mem_coe.mpr <|
    Finset.mem_product.mpr ⟨integerClip_mem_cutoffStates R (k - 1),
      integerClip_mem_cutoffStates R k⟩

theorem clippedUpwardIncrement_range_finite (R : ℕ) (f : ℤ → ℝ) :
    (Set.range (clippedUpwardIncrement R f)).Finite := by
  apply (cutoffDifferenceValues_finite R f).subset
  rintro y ⟨k, rfl⟩
  exact clippedUpwardIncrement_mem_cutoffDifferenceValues R f k

theorem clippedDownwardIncrement_range_finite (R : ℕ) (f : ℤ → ℝ) :
    (Set.range (clippedDownwardIncrement R f)).Finite := by
  apply (cutoffDifferenceValues_finite R f).subset
  rintro y ⟨k, rfl⟩
  exact clippedDownwardIncrement_mem_cutoffDifferenceValues R f k

/-- Finite maximum of the absolute ordinary upward increments on the retained states. -/
noncomputable def clippedUpwardAbsBound (R : ℕ) (f : ℤ → ℝ) : ℝ :=
  (cutoffStates R).sup' (cutoffStates_nonempty R)
    (fun k => |f (k + 1) - f k|)

/-- Finite maximum of the absolute ordinary downward increments on the retained states. -/
noncomputable def clippedDownwardAbsBound (R : ℕ) (f : ℤ → ℝ) : ℝ :=
  (cutoffStates R).sup' (cutoffStates_nonempty R)
    (fun k => |f (k - 1) - f k|)

theorem integerClip_succ_eq_or_self (R : ℕ) (k : ℤ) :
    integerClip R (k + 1) = integerClip R k ∨
      integerClip R (k + 1) = integerClip R k + 1 := by
  by_cases hlow : k < -(R : ℤ)
  · have hlow' : k + 1 ≤ -(R : ℤ) := by omega
    left
    rw [integerClip_eq_lower_of_le (le_of_lt hlow),
      integerClip_eq_lower_of_le hlow']
  · by_cases hhigh : (R : ℤ) ≤ k
    · left
      rw [integerClip_eq_upper_of_ge hhigh,
        integerClip_eq_upper_of_ge (by omega : (R : ℤ) ≤ k + 1)]
    · have hlow' : -(R : ℤ) ≤ k := le_of_not_gt hlow
      have hupper' : k + 1 ≤ (R : ℤ) := by omega
      have hck : integerClip R k = k := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨hlow', by omega⟩
      have hck1 : integerClip R (k + 1) = k + 1 := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨by omega, hupper'⟩
      right
      rw [hck1, hck]

theorem integerClip_pred_eq_or_self (R : ℕ) (k : ℤ) :
    integerClip R (k - 1) = integerClip R k ∨
      integerClip R (k - 1) = integerClip R k - 1 := by
  by_cases hlow : k ≤ -(R : ℤ)
  · left
    rw [integerClip_eq_lower_of_le hlow,
      integerClip_eq_lower_of_le (by omega : k - 1 ≤ -(R : ℤ))]
  · by_cases hhigh : (R : ℤ) < k
    · left
      rw [integerClip_eq_upper_of_ge (by omega : (R : ℤ) ≤ k),
        integerClip_eq_upper_of_ge (by omega : (R : ℤ) ≤ k - 1)]
    · have hlow' : -(R : ℤ) ≤ k - 1 := by omega
      have hupper' : k ≤ (R : ℤ) := le_of_not_gt hhigh
      have hck : integerClip R k = k := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨by omega, hupper'⟩
      have hck1 : integerClip R (k - 1) = k - 1 := by
        apply integerClip_eq_self_of_mem
        rw [cutoffStates, Finset.mem_Icc]
        exact ⟨hlow', by omega⟩
      right
      rw [hck1, hck]

theorem clippedUpwardIncrement_abs_le_bound (R : ℕ) (f : ℤ → ℝ) (k : ℤ) :
    |clippedUpwardIncrement R f k| ≤ clippedUpwardAbsBound R f := by
  unfold clippedUpwardAbsBound
  rcases integerClip_succ_eq_or_self R k with hsame | hstep
  · rw [clippedUpwardIncrement, hsame]
    simp only [sub_self, abs_zero]
    calc
      (0 : ℝ) ≤ |f (0 + 1) - f 0| := abs_nonneg _
      _ ≤ (cutoffStates R).sup' (cutoffStates_nonempty R)
          (fun j => |f (j + 1) - f j|) :=
        Finset.le_sup' (fun j : ℤ => |f (j + 1) - f j|) (by
          rw [cutoffStates, Finset.mem_Icc]
          constructor <;> omega)
  · rw [clippedUpwardIncrement, hstep]
    exact Finset.le_sup' (fun j : ℤ => |f (j + 1) - f j|)
      (integerClip_mem_cutoffStates R k)

theorem clippedDownwardIncrement_abs_le_bound (R : ℕ) (f : ℤ → ℝ) (k : ℤ) :
    |clippedDownwardIncrement R f k| ≤ clippedDownwardAbsBound R f := by
  unfold clippedDownwardAbsBound
  rcases integerClip_pred_eq_or_self R k with hsame | hstep
  · rw [clippedDownwardIncrement, hsame]
    simp only [sub_self, abs_zero]
    calc
      (0 : ℝ) ≤ |f (0 - 1) - f 0| := abs_nonneg _
      _ ≤ (cutoffStates R).sup' (cutoffStates_nonempty R)
          (fun j => |f (j - 1) - f j|) :=
        Finset.le_sup' (fun j : ℤ => |f (j - 1) - f j|) (by
          rw [cutoffStates, Finset.mem_Icc]
          constructor <;> omega)
  · rw [clippedDownwardIncrement, hstep]
    exact Finset.le_sup' (fun j : ℤ => |f (j - 1) - f j|)
      (integerClip_mem_cutoffStates R k)

/-! ## A concrete cubic specialization -/

private theorem cubicLyapunov_nonneg (k : ℤ) : 0 ≤ cubicLyapunov k := by
  dsimp [cubicLyapunov]
  positivity

private theorem cubicLyapunov_le_cutoff_cube {R : ℕ} {k : ℤ}
    (hk : k ∈ cutoffStates R) : cubicLyapunov k ≤ (R : ℝ) ^ 3 := by
  rw [cutoffStates, Finset.mem_Icc] at hk
  have hkabs : |(k : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hk.1
    · exact_mod_cast hk.2
  dsimp [cubicLyapunov]
  exact pow_le_pow_left₀ (abs_nonneg _) hkabs 3

private theorem cubicLyapunov_le_plus_one_cube {R : ℕ} {k : ℤ}
    (hk : k ∈ cutoffStates R) :
    cubicLyapunov k ≤ ((R : ℝ) + 1) ^ 3 := by
  have hstate := cubicLyapunov_le_cutoff_cube hk
  have hR : 0 ≤ (R : ℝ) := by positivity
  nlinarith [sq_nonneg (R : ℝ)]

private theorem cubicLyapunov_succ_le_plus_one_cube {R : ℕ} {k : ℤ}
    (hk : k ∈ cutoffStates R) :
    cubicLyapunov (k + 1) ≤ ((R : ℝ) + 1) ^ 3 := by
  rw [cutoffStates, Finset.mem_Icc] at hk
  have hkabs : |((k + 1 : ℤ) : ℝ)| ≤ (R : ℝ) + 1 := by
    rw [abs_le]
    constructor
    · have hkR : -(R : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      norm_num [Int.cast_add]
      linarith
    · have hkR : (k : ℝ) ≤ (R : ℝ) := by exact_mod_cast hk.2
      norm_num [Int.cast_add]
      linarith
  dsimp [cubicLyapunov]
  exact pow_le_pow_left₀ (abs_nonneg _) hkabs 3

private theorem cubicLyapunov_pred_le_plus_one_cube {R : ℕ} {k : ℤ}
    (hk : k ∈ cutoffStates R) :
    cubicLyapunov (k - 1) ≤ ((R : ℝ) + 1) ^ 3 := by
  rw [cutoffStates, Finset.mem_Icc] at hk
  have hkabs : |((k - 1 : ℤ) : ℝ)| ≤ (R : ℝ) + 1 := by
    rw [abs_le]
    constructor
    · have hkR : -(R : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      norm_num [Int.cast_sub]
      linarith
    · have hkR : (k : ℝ) ≤ (R : ℝ) := by exact_mod_cast hk.2
      norm_num [Int.cast_sub]
      linarith
  dsimp [cubicLyapunov]
  exact pow_le_pow_left₀ (abs_nonneg _) hkabs 3

theorem cubicLyapunov_clippedUpwardIncrement_abs_le (R : ℕ) (k : ℤ) :
    |clippedUpwardIncrement R cubicLyapunov k| ≤ (R : ℝ) ^ 3 := by
  rw [clippedUpwardIncrement]
  apply (abs_sub_le_iff).2
  constructor
  · have hleft := cubicLyapunov_le_cutoff_cube
      (integerClip_mem_cutoffStates R (k + 1))
    have hright := cubicLyapunov_nonneg (integerClip R k)
    linarith
  · have hleft := cubicLyapunov_le_cutoff_cube
      (integerClip_mem_cutoffStates R k)
    have hright := cubicLyapunov_nonneg (integerClip R (k + 1))
    linarith

theorem cubicLyapunov_clippedDownwardIncrement_abs_le (R : ℕ) (k : ℤ) :
    |clippedDownwardIncrement R cubicLyapunov k| ≤ (R : ℝ) ^ 3 := by
  rw [clippedDownwardIncrement]
  apply (abs_sub_le_iff).2
  constructor
  · have hleft := cubicLyapunov_le_cutoff_cube
      (integerClip_mem_cutoffStates R (k - 1))
    have hright := cubicLyapunov_nonneg (integerClip R k)
    linarith
  · have hleft := cubicLyapunov_le_cutoff_cube
      (integerClip_mem_cutoffStates R k)
    have hright := cubicLyapunov_nonneg (integerClip R (k - 1))
    linarith

theorem clippedUpwardAbsBound_cubicLyapunov_le (R : ℕ) :
    clippedUpwardAbsBound R cubicLyapunov ≤ ((R : ℝ) + 1) ^ 3 := by
  unfold clippedUpwardAbsBound
  apply Finset.sup'_le (cutoffStates_nonempty R)
  intro k hk
  rw [abs_sub_le_iff]
  constructor
  · have hleft := cubicLyapunov_succ_le_plus_one_cube hk
    have hright := cubicLyapunov_le_plus_one_cube hk
    have hright_nonneg := cubicLyapunov_nonneg k
    linarith
  · have hleft := cubicLyapunov_le_plus_one_cube hk
    have hright := cubicLyapunov_succ_le_plus_one_cube hk
    have hleft_nonneg := cubicLyapunov_nonneg (k + 1)
    linarith

theorem clippedDownwardAbsBound_cubicLyapunov_le (R : ℕ) :
    clippedDownwardAbsBound R cubicLyapunov ≤ ((R : ℝ) + 1) ^ 3 := by
  unfold clippedDownwardAbsBound
  apply Finset.sup'_le (cutoffStates_nonempty R)
  intro k hk
  rw [abs_sub_le_iff]
  constructor
  · have hleft := cubicLyapunov_pred_le_plus_one_cube hk
    have hright := cubicLyapunov_le_plus_one_cube hk
    have hright_nonneg := cubicLyapunov_nonneg k
    linarith
  · have hleft := cubicLyapunov_le_plus_one_cube hk
    have hright := cubicLyapunov_pred_le_plus_one_cube hk
    have hleft_nonneg := cubicLyapunov_nonneg (k - 1)
    linarith

end OTSelector
