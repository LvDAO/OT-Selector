import OTSelector.Feedback.Spacelike
import OTSelector.Basic.Convergence
import OTSelector.Probability.TriangularArray

/-!
# Normalized feedback graphs and triangular-array scaling

The macroscopic graph is `γₙ z = gₙ (n z) / n`.  This file contains only the
deterministic rescaling identities and the probability bookkeeping needed to
turn a square-root tight unnormalised envelope into a vanishing normalized
envelope.  The stochastic feedback process itself is intentionally not
introduced here.
-/

open Filter MeasureTheory
open scoped Topology

namespace OTSelector

/-! ## Deterministic rescaling -/

/-- The normalized row-`n` feedback graph `γₙ z = gₙ (n z) / n`. -/
noncomputable def normalizedGraph (g : ℕ → ℝ → ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  rescaleGraph (g n) (n : ℝ) z

/-- Precomposition with a positive dilation multiplies a Lipschitz constant by the dilation. -/
theorem graph_comp_mul_lipschitz {g : ℝ → ℝ} {lam scale : ℝ} (hscale : 0 < scale)
    (hg : RealLipschitz lam g) :
    RealLipschitz (lam * scale) (fun z ↦ g (scale * z)) := by
  intro x y
  calc
    |g (scale * y) - g (scale * x)| ≤ lam * |scale * y - scale * x| :=
      hg (scale * x) (scale * y)
    _ = (lam * scale) * |y - x| := by
      rw [← mul_sub, abs_mul, abs_of_pos hscale]
      ring

/-- The normalized graph has exactly the same Lipschitz constant as its unnormalised row. -/
theorem normalizedGraph_lipschitz {g : ℕ → ℝ → ℝ} {n : ℕ} {lam : ℝ}
    (hn : 0 < n) (hg : RealLipschitz lam (g n)) :
    RealLipschitz lam (normalizedGraph g n) := by
  change RealLipschitz lam (rescaleGraph (g n) (n : ℝ))
  exact rescaleGraph_lipschitz (g := g n) (scale := (n : ℝ))
    (by exact_mod_cast hn) hg

/-! ## Supremum control -/

/-- The (possibly nonmeasurable) uniform absolute envelope of a real graph. -/
noncomputable def graphSupAbs (g : ℝ → ℝ) : ℝ :=
  sSup (Set.range fun z ↦ |g z|)

theorem normalizedGraph_abs_le_div_sup {g : ℕ → ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hbound : BddAbove (Set.range fun z ↦ |g n z|)) (z : ℝ) :
    |normalizedGraph g n z| ≤ graphSupAbs (g n) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpoint : |g n ((n : ℝ) * z)| ≤ graphSupAbs (g n) :=
    le_csSup hbound ⟨(n : ℝ) * z, rfl⟩
  rw [normalizedGraph, rescaleGraph, abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right hpoint hnR.le

/-- The normalized supremum is bounded by the unnormalised supremum divided by `n`. -/
theorem normalizedGraph_supAbs_le_div {g : ℕ → ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hbound : BddAbove (Set.range fun z ↦ |g n z|)) :
    graphSupAbs (normalizedGraph g n) ≤ graphSupAbs (g n) / (n : ℝ) := by
  refine csSup_le ⟨|normalizedGraph g n 0|, ⟨0, rfl⟩⟩ ?_
  rintro _ ⟨z, rfl⟩
  exact normalizedGraph_abs_le_div_sup hn hbound z

/-- A normalized graph for a row whose sample space may depend on `n`. -/
noncomputable def normalizedGraphArray
    {Ω : ℕ → Type*} (g : ∀ n, Ω n → ℝ → ℝ)
    (n : ℕ) (ω : Ω n) : ℝ → ℝ :=
  normalizedGraph (fun _ : ℕ ↦ g n ω) n

/-- The deterministic supremum bound applied pointwise to a varying-row graph array. -/
theorem normalizedGraphArray_supAbs_le_div
    {Ω : ℕ → Type*} (g : ∀ n, Ω n → ℝ → ℝ) {n : ℕ} (hn : 0 < n)
    (ω : Ω n) (hbound : BddAbove (Set.range fun z ↦ |g n ω z|)) :
    graphSupAbs (normalizedGraphArray g n ω) ≤ graphSupAbs (g n ω) / (n : ℝ) := by
  change graphSupAbs (normalizedGraph (fun _ : ℕ ↦ g n ω) n) ≤
    graphSupAbs (g n ω) / (n : ℝ)
  exact normalizedGraph_supAbs_le_div hn hbound

/-! ## Generic triangular-array probability bookkeeping -/

private theorem eventually_nat_sqrt_scale_lt {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * Real.sqrt (n : ℝ) < ε * (n : ℝ) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, C / ε < Real.sqrt (n : ℝ) :=
    hsqrt.eventually (eventually_gt_atTop (C / ε))
  filter_upwards [hev] with n hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    exact lt_of_lt_of_le (div_pos hC hε) hn.le
  have hn0 : 0 < (n : ℝ) := by
    have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = n :=
      Real.mul_self_sqrt (Nat.cast_nonneg n)
    nlinarith
  have hC_lt : C < Real.sqrt (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have hmul := mul_lt_mul_of_pos_right hC_lt hsqrt_pos
  calc
    C * Real.sqrt (n : ℝ) < (Real.sqrt (n : ℝ) * ε) * Real.sqrt (n : ℝ) := hmul
    _ = ε * (n : ℝ) := by
      calc
        (Real.sqrt (n : ℝ) * ε) * Real.sqrt (n : ℝ) =
            ε * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = ε * (n : ℝ) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]

/-- Varying-row-space form of the square-root `Oₚ` normalization step.

The event is written directly in the triangular-array measure notation because the project's
`TendstoInProbability` alias has one fixed measure space. -/
theorem eventually_div_nat_tail_of_isBigOInProbability_sqrt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ)
    (hX : Probability.IsBigOInProbability P X
      (fun n ↦ Real.sqrt (n : ℝ)))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (P n).real {ω | ε ≤ |X n ω / (n : ℝ)|} < δ := by
  obtain ⟨C, hC, htail⟩ := hX (δ / 2) (by linarith)
  have hscale := eventually_nat_sqrt_scale_lt hC hε
  filter_upwards [hscale, htail, eventually_gt_atTop (0 : ℕ)] with n hnScale hnTail hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsubset : {ω | ε ≤ |X n ω / (n : ℝ)|} ⊆
      {ω | C * Real.sqrt (n : ℝ) < |X n ω|} := by
    intro ω hω
    have hω' : ε ≤ |X n ω| / (n : ℝ) := by
      simpa [abs_div, abs_of_pos hnR] using hω
    have hmul : ε * (n : ℝ) ≤ |X n ω| := (le_div_iff₀ hnR).mp hω'
    exact lt_of_lt_of_le hnScale hmul
  have hmeasure : (P n).real {ω | ε ≤ |X n ω / (n : ℝ)|} ≤ δ / 2 :=
    (measureReal_mono hsubset).trans hnTail
  linarith

/-- `graphSupAbs` is nonnegative whenever its row is bounded above. -/
theorem graphSupAbs_nonneg_of_bddAbove {g : ℝ → ℝ}
    (hbound : BddAbove (Set.range fun z ↦ |g z|)) : 0 ≤ graphSupAbs g := by
  have hpoint : |g 0| ≤ graphSupAbs g := by
    exact le_csSup hbound ⟨0, rfl⟩
  exact (abs_nonneg _).trans hpoint

/-- A directly consumable varying-row I4 envelope tail for normalized graph arrays. -/
theorem eventually_normalizedGraphArray_supAbs_tail
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (g : ∀ n, Ω n → ℝ → ℝ)
    (hbound : ∀ n ω, BddAbove (Set.range fun z ↦ |g n ω z|))
    (hX : Probability.IsBigOInProbability P
      (fun n ω ↦ graphSupAbs (g n ω)) (fun n ↦ Real.sqrt (n : ℝ)))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (P n).real {ω | ε ≤ graphSupAbs (normalizedGraphArray g n ω)} < δ := by
  have htail := eventually_div_nat_tail_of_isBigOInProbability_sqrt
    P (fun n ω ↦ graphSupAbs (g n ω)) hX hε hδ
  filter_upwards [htail, eventually_gt_atTop (0 : ℕ)] with n hnTail hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsubset : {ω | ε ≤ graphSupAbs (normalizedGraphArray g n ω)} ⊆
      {ω | ε ≤ |graphSupAbs (g n ω) / (n : ℝ)|} := by
    intro ω hω
    have hsup := normalizedGraphArray_supAbs_le_div g hn ω (hbound n ω)
    have hG0 : 0 ≤ graphSupAbs (g n ω) :=
      graphSupAbs_nonneg_of_bddAbove (hbound n ω)
    have hquot0 : 0 ≤ graphSupAbs (g n ω) / (n : ℝ) :=
      div_nonneg hG0 hnR.le
    calc
      ε ≤ graphSupAbs (normalizedGraphArray g n ω) := hω
      _ ≤ graphSupAbs (g n ω) / (n : ℝ) := hsup
      _ = |graphSupAbs (g n ω) / (n : ℝ)| := (abs_of_nonneg hquot0).symm
  exact (measureReal_mono hsubset (measure_ne_top (P n) _)).trans_lt hnTail

/-- An `Oₚ` bound may be transferred to an eventually larger nonnegative scale. -/
theorem isBigOInProbability_mono_scale
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {X : ∀ n, Ω n → ℝ} {smallScale largeScale : ℕ → ℝ}
    (hX : Probability.IsBigOInProbability P X smallScale)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ C : ℝ, 0 < C → C * smallScale n ≤ C * largeScale n) :
    Probability.IsBigOInProbability P X largeScale := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hscale, htail] with n hnScale hnTail
  have hsubset : {ω | C * largeScale n < |X n ω|} ⊆
      {ω | C * smallScale n < |X n ω|} := by
    intro ω hω
    exact lt_of_le_of_lt (hnScale C hC) hω
  exact (measureReal_mono hsubset).trans hnTail

/-- The maximum of two absolute envelopes remains `Oₚ` on the common scale. -/
theorem isBigOInProbability_max_abs
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Ω n → ℝ} {scale : ℕ → ℝ}
    (hscale : ∀ n, 0 ≤ scale n)
    (hX : Probability.IsBigOInProbability P X scale)
    (hY : Probability.IsBigOInProbability P Y scale) :
    Probability.IsBigOInProbability P
      (fun n ω ↦ max |X n ω| |Y n ω|) scale := by
  intro ε hε
  obtain ⟨CX, hCX, hXtail⟩ := hX (ε / 2) (by linarith)
  obtain ⟨CY, hCY, hYtail⟩ := hY (ε / 2) (by linarith)
  let C := max CX CY
  have hC : 0 < C := lt_of_lt_of_le hCX (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hXtail, hYtail] with n hnX hnY
  let EX : Set (Ω n) := {ω | CX * scale n < |X n ω|}
  let EY : Set (Ω n) := {ω | CY * scale n < |Y n ω|}
  have hsubset : {ω | C * scale n < max |X n ω| |Y n ω|} ⊆ EX ∪ EY := by
    intro ω hω
    by_cases hx : CX * scale n < |X n ω|
    · exact Set.mem_union_left EY hx
    · right
      have hcx : |X n ω| ≤ CX * scale n := le_of_not_gt hx
      have hmaxX : CX * scale n ≤ C * scale n :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hscale n)
      have hmax : CY * scale n ≤ C * scale n :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (hscale n)
      have hcy : CY * scale n < |Y n ω| := by
        by_contra hnot
        have hy : |Y n ω| ≤ CY * scale n := le_of_not_gt hnot
        exact (not_lt_of_ge (max_le (hcx.trans hmaxX) (hy.trans hmax))) hω
      exact hcy
  have hunion := measureReal_union_le (μ := P n) EX EY
  have hmono : (P n).real {ω | C * scale n < max |X n ω| |Y n ω|} ≤
      (P n).real (EX ∪ EY) := measureReal_mono hsubset
  have hcalc : (P n).real {ω | C * scale n < max |X n ω| |Y n ω|} ≤ ε := by
    calc
    (P n).real {ω | C * scale n < max |X n ω| |Y n ω|} ≤
        (P n).real (EX ∪ EY) := hmono
    _ ≤ (P n).real EX + (P n).real EY := hunion
    _ ≤ ε / 2 + ε / 2 := add_le_add hnX hnY
    _ = ε := by ring
  have hset : {ω | C * scale n < abs (max (abs (X n ω)) (abs (Y n ω)))} =
      {ω | C * scale n < max |X n ω| |Y n ω|} := by
    ext ω
    have hmax0 : 0 ≤ max |X n ω| |Y n ω| :=
      (abs_nonneg _).trans (le_max_left _ _)
    change C * scale n < abs (max (abs (X n ω)) (abs (Y n ω))) ↔
      C * scale n < max (abs (X n ω)) (abs (Y n ω))
    rw [abs_of_nonneg hmax0]
  rw [hset]
  exact hcalc

/-- A square-root `Oₚ` envelope becomes a vanishing normalized envelope on a fixed probability
space.  This is the fixed-space form of the triangular-array calculation, expressed through the
project's `TendstoInProbability` alias. -/
theorem tendstoInProbability_div_nat_of_isBigOInProbability_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX : Probability.IsBigOInProbability (fun _ : ℕ ↦ P) X
      (fun n ↦ Real.sqrt (n : ℝ))) :
    TendstoInProbability P (fun n ω ↦ X n ω / (n : ℝ)) atTop (fun _ ↦ 0) := by
  rw [tendstoInProbability_iff_measureReal_dist]
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨C, hC, htail⟩ := hX (δ / 2) (by linarith)
  have hscale := eventually_nat_sqrt_scale_lt hC hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      dist ((P).real {ω | ε ≤ dist (X n ω / (n : ℝ)) 0}) 0 < δ := by
    filter_upwards [hscale, htail] with n hnScale hnTail
    have hn0 : 0 < n := by
      by_contra hn'
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn'
      subst n
      norm_num at hnScale
    have hsubset : {ω | ε ≤ dist (X n ω / (n : ℝ)) 0} ⊆
        {ω | C * Real.sqrt (n : ℝ) < |X n ω|} := by
      intro ω hω
      have hω' : ε ≤ |X n ω| / (n : ℝ) := by simpa [Real.dist_eq] using hω
      have hmul : ε * (n : ℝ) ≤ |X n ω| := (le_div_iff₀ (by exact_mod_cast hn0)).mp hω'
      exact lt_of_lt_of_le hnScale hmul
    have hmeasure : (P).real {ω | ε ≤ dist (X n ω / (n : ℝ)) 0} ≤ δ / 2 :=
      (measureReal_mono hsubset).trans hnTail
    have hlt' : (P).real {ω | ε ≤ dist (X n ω / (n : ℝ)) 0} < δ := by linarith
    have hlt : (P).real {ω | ε ≤ |X n ω| / (n : ℝ)} < δ := by
      simpa [Real.dist_eq] using hlt'
    have hnonneg : 0 ≤ (P).real {ω | ε ≤ |X n ω| / (n : ℝ)} := measureReal_nonneg
    simpa [Real.dist_eq, sub_zero, abs_div,
      abs_of_pos (show 0 < (n : ℝ) by exact_mod_cast hn0),
      abs_of_nonneg hnonneg] using hlt
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  exact ⟨N, hN⟩

end OTSelector
