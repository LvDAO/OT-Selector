import OTSelector.Probability.Bernstein
import LeanPool.FormalLearningTheory.Bridge
import LeanPool.FormalLearningTheory.Complexity.Symmetrization

/-!
# Relative VC concentration infrastructure

This module combines the VC/Sauer and measurability framework from the local `lean-pool` with the
scalar Bernstein inequality ported in `OTSelector.Probability.Bernstein`.  The first layer turns the
scalar theorem into a centered-indicator bound; later layers add relative shells and peeling.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- The real indicator of a measurable set. -/
noncomputable def indicatorReal (s : Set Ω) : Ω → ℝ :=
  s.indicator 1

/-- The empirical mass assigned to a set by a finite sample. -/
noncomputable def empiricalSetMass (n : ℕ) (X : Fin n → Ω) (s : Set Ω) : ℝ :=
  EmpiricalProcess.empiricalAverage (indicatorReal s) n X

/-- The centered empirical mass of a set. -/
noncomputable def empiricalSetDeviation
    (P : Measure Ω) (n : ℕ) (X : Fin n → Ω) (s : Set Ω) : ℝ :=
  empiricalSetMass n X s - P.real s

theorem empiricalProcess_indicator (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (s : Set Ω) (hs : MeasurableSet s) :
    EmpiricalProcess.empiricalProcess P n X (indicatorReal s) =
      Real.sqrt n * empiricalSetDeviation P n X s := by
  rw [EmpiricalProcess.empiricalProcess, empiricalSetDeviation, empiricalSetMass]
  congr 1
  rw [show ∫ x, indicatorReal s x ∂P = P.real s by
    simpa [indicatorReal] using integral_indicator_one (μ := P) hs]

/-- Bernstein's inequality specialized to a centered set indicator. -/
theorem centeredIndicator_bernstein
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n)
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : Fin n → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = P)
    {x : ℝ} (hx : 0 < x) :
    μ {ω : Ξ | x <
        |EmpiricalProcess.empiricalProcess P n (fun j : Fin n ↦ X j ω)
          (indicatorReal s)|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(x ^ 2) /
          (4 * (P.real s + x / Real.sqrt n)))) := by
  have hP_nonneg : 0 ≤ P.real s := ENNReal.toReal_nonneg
  have hmeas : Measurable (indicatorReal s) := by
    exact measurable_const.indicator hs
  have hbdd : ∀ ω, |indicatorReal s ω| ≤ (1 : ℝ) := by
    intro ω
    by_cases hω : ω ∈ s <;> simp [indicatorReal, hω]
  have hsecond : ∫ ω, (indicatorReal s ω) ^ 2 ∂P ≤ (Real.sqrt (P.real s)) ^ 2 := by
    rw [Real.sq_sqrt hP_nonneg]
    have hsq : (fun ω ↦ (indicatorReal s ω) ^ 2) = indicatorReal s := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [indicatorReal, hω]
    rw [hsq]
    simpa [indicatorReal] using integral_indicator_one (μ := P) hs |>.le
  simpa using EmpiricalProcess.bernstein_inequality P (indicatorReal s) hmeas
    (M := 1) (σ := Real.sqrt (P.real s)) zero_le_one (Real.sqrt_nonneg _)
    hbdd hsecond n hn hX_meas hX_iindep hX_law hx

/-- Centered-indicator Bernstein for the canonical finite product sample. -/
theorem centeredIndicator_bernstein_pi
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Measure.pi (fun _ : Fin n ↦ P)
        {sample : Fin n → Ω | x <
          |EmpiricalProcess.empiricalProcess P n sample (indicatorReal s)|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(x ^ 2) /
          (4 * (P.real s + x / Real.sqrt n)))) := by
  let μ := Measure.pi (fun _ : Fin n ↦ P)
  have hmeas : ∀ i : Fin n, Measurable (fun sample : Fin n → Ω ↦ sample i) :=
    fun i ↦ measurable_pi_apply i
  have hindep : iIndepFun (fun i (sample : Fin n → Ω) ↦ sample i) μ := by
    dsimp [μ]
    exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable
  have hlaw : ∀ i : Fin n, μ.map (fun sample : Fin n → Ω ↦ sample i) = P := by
    intro i
    exact (measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq
  exact centeredIndicator_bernstein P s hs n hn hmeas hindep hlaw hx

/-- Product-sample centered-indicator Bernstein with the unknown set mass replaced by a stated
upper bound.  This monotone form is the input used uniformly on one relative shell. -/
theorem centeredIndicator_bernstein_pi_of_mass_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n) {x massCap : ℝ} (hx : 0 < x)
    (hmass : P.real s ≤ massCap) :
    Measure.pi (fun _ : Fin n ↦ P)
        {sample : Fin n → Ω | x <
          |EmpiricalProcess.empiricalProcess P n sample (indicatorReal s)|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(x ^ 2) /
          (4 * (massCap + x / Real.sqrt n)))) := by
  have hbase := centeredIndicator_bernstein_pi P s hs n hn hx
  have hn_pos : 0 < n := by omega
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn_pos)
  have hP_nonneg : 0 ≤ P.real s := ENNReal.toReal_nonneg
  have hcap_nonneg : 0 ≤ massCap := hP_nonneg.trans hmass
  have hxdiv_pos : 0 < x / Real.sqrt n := div_pos hx hsqrt_pos
  have hdenP : 0 < 4 * (P.real s + x / Real.sqrt n) := by positivity
  have hdenCap : 0 < 4 * (massCap + x / Real.sqrt n) := by positivity
  have hfrac : x ^ 2 / (4 * (massCap + x / Real.sqrt n)) ≤
      x ^ 2 / (4 * (P.real s + x / Real.sqrt n)) := by
    rw [div_le_div_iff₀ hdenCap hdenP]
    nlinarith [sq_nonneg x]
  have hexp :
      2 * Real.exp (-(x ^ 2) / (4 * (P.real s + x / Real.sqrt n))) ≤
        2 * Real.exp (-(x ^ 2) / (4 * (massCap + x / Real.sqrt n))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hfrac
  exact hbase.trans (ENNReal.ofReal_le_ofReal hexp)

/-! ## Finite classes and dyadic shells -/

/-- A finite-class maximal Bernstein inequality, obtained by a finite union bound. -/
theorem finiteClass_centeredIndicator_bernstein
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Finset (Set Ω)) (hC_meas : ∀ s ∈ C, MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n)
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : Fin n → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = P)
    (threshold : Set Ω → ℝ) (hthreshold : ∀ s ∈ C, 0 < threshold s) :
    μ {ω : Ξ | ∃ s ∈ C, threshold s <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|} ≤
      ∑ s ∈ C, ENNReal.ofReal
        (2 * Real.exp (-((threshold s) ^ 2) /
          (4 * (P.real s + threshold s / Real.sqrt n)))) := by
  let event : Set Ω → Set Ξ := fun s ↦
    {ω | threshold s <
      |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|}
  have hsubset :
      {ω : Ξ | ∃ s ∈ C, threshold s <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|} ⊆
        ⋃ s ∈ C, event s := by
    rintro ω ⟨s, hsC, hs⟩
    exact Set.mem_iUnion₂.mpr ⟨s, hsC, hs⟩
  calc
    μ {ω : Ξ | ∃ s ∈ C, threshold s <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|}
        ≤ μ (⋃ s ∈ C, event s) := measure_mono hsubset
    _ ≤ ∑ s ∈ C, μ (event s) := measure_biUnion_finset_le C event
    _ ≤ ∑ s ∈ C, ENNReal.ofReal
          (2 * Real.exp (-((threshold s) ^ 2) /
            (4 * (P.real s + threshold s / Real.sqrt n)))) := by
      exact Finset.sum_le_sum fun s hsC ↦
        centeredIndicator_bernstein P s (hC_meas s hsC) n hn
          hX_meas hX_iindep hX_law (hthreshold s hsC)

/-- The dyadic scale `2⁻ᵏ`, represented without integer powers. -/
noncomputable def dyadicScale (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  exact inv_pos.mpr (pow_pos (by norm_num) k)

@[simp]
theorem dyadicScale_zero : dyadicScale 0 = 1 := by
  simp [dyadicScale]

theorem dyadicScale_succ (k : ℕ) : dyadicScale (k + 1) = dyadicScale k / 2 := by
  rw [dyadicScale, dyadicScale, pow_succ]
  field_simp

/-- The smaller of a set's probability and its complement's probability. -/
noncomputable def balancedMass (P : Measure Ω) (s : Set Ω) : ℝ :=
  min (P.real s) (P.real sᶜ)

theorem balancedMass_nonneg (P : Measure Ω) (s : Set Ω) : 0 ≤ balancedMass P s := by
  exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Dyadic shell according to the smaller of a set and its complement. -/
def relativeShell (P : Measure Ω) (k : ℕ) : Set (Set Ω) :=
  {s | dyadicScale (k + 1) < balancedMass P s ∧ balancedMass P s ≤ dyadicScale k}

theorem relativeShell_lower {P : Measure Ω} {k : ℕ} {s : Set Ω}
    (hs : s ∈ relativeShell P k) : dyadicScale (k + 1) < balancedMass P s :=
  hs.1

theorem relativeShell_upper {P : Measure Ω} {k : ℕ} {s : Set Ω}
    (hs : s ∈ relativeShell P k) : balancedMass P s ≤ dyadicScale k :=
  hs.2

/-- Finite dyadic peeling: sum the maximal-Bernstein bound over a finite list of shells. -/
theorem finiteRelativePeeling_bernstein
    (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} (shell : Fin K → Finset (Set Ω))
    (hshell_meas : ∀ k s, s ∈ shell k → MeasurableSet s)
    (n : ℕ) (hn : 1 ≤ n)
    {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : Fin n → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : iIndepFun X μ)
    (hX_law : ∀ i, μ.map (X i) = P)
    (threshold : Fin K → ℝ) (hthreshold : ∀ k, 0 < threshold k) :
    μ {ω : Ξ | ∃ k : Fin K, ∃ s ∈ shell k, threshold k <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|} ≤
      ∑ k : Fin K, ∑ s ∈ shell k, ENNReal.ofReal
        (2 * Real.exp (-((threshold k) ^ 2) /
          (4 * (P.real s + threshold k / Real.sqrt n)))) := by
  let event : Fin K → Set Ξ := fun k ↦
    {ω | ∃ s ∈ shell k, threshold k <
      |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|}
  have hsubset :
      {ω : Ξ | ∃ k : Fin K, ∃ s ∈ shell k, threshold k <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|} ⊆
        ⋃ k, event k := by
    rintro ω ⟨k, s, hs, hbad⟩
    exact Set.mem_iUnion.mpr ⟨k, s, hs, hbad⟩
  calc
    μ {ω : Ξ | ∃ k : Fin K, ∃ s ∈ shell k, threshold k <
        |EmpiricalProcess.empiricalProcess P n (fun i ↦ X i ω) (indicatorReal s)|}
        ≤ μ (⋃ k, event k) := measure_mono hsubset
    _ ≤ ∑ k : Fin K, μ (event k) := by
      simpa using measure_iUnion_le (μ := μ) event
    _ ≤ ∑ k : Fin K, ∑ s ∈ shell k, ENNReal.ofReal
          (2 * Real.exp (-((threshold k) ^ 2) /
            (4 * (P.real s + threshold k / Real.sqrt n)))) := by
      exact Finset.sum_le_sum fun k _ ↦
        finiteClass_centeredIndicator_bernstein P (shell k)
          (hshell_meas k) n hn hX_meas hX_iindep hX_law
          (fun _ ↦ threshold k) (fun _ _ ↦ hthreshold k)

/-! ## VC restriction patterns -/

/-- The finite set of binary loss patterns realized by a concept class on a sample. -/
noncomputable def restrictionPatterns
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (n : ℕ) (z : Fin n → Ω) :
    Finset (Fin n → Bool) :=
  (Set.toFinite
    {p : Fin n → Bool | ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i))}).toFinset

omit [MeasurableSpace Ω] in
theorem mem_restrictionPatterns_iff
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (n : ℕ) (z : Fin n → Ω)
    (p : Fin n → Bool) :
    p ∈ restrictionPatterns C c n z ↔
      ∃ h ∈ C, ∀ i, p i = decide (h (z i) ≠ c (z i)) := by
  simp [restrictionPatterns]

omit [MeasurableSpace Ω] in
/-- The imported restriction-pattern theorem, exposed as a `Finset.card` bound. -/
theorem restrictionPatterns_card_le_growth [Infinite Ω]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (n : ℕ) (z : Fin n → Ω) :
    (restrictionPatterns C c n z).card ≤ GrowthFunction Ω C n := by
  rw [restrictionPatterns, ← Set.ncard_eq_toFinset_card]
  exact restriction_pattern_count C c n z

omit [MeasurableSpace Ω] in
/-- VC finiteness plus Sauer--Shelah gives a uniform polynomial bound for every realized pattern
set.  This is the cardinality input consumed by the Bernstein peeling layer. -/
theorem restrictionPatterns_card_le_sauer [Infinite Ω]
    (C : ConceptClass Ω Bool) (hVC : VCDim Ω C < ⊤) :
    ∃ d : ℕ, ∀ n : ℕ, d ≤ n → ∀ (c : Concept Ω Bool) (z : Fin n → Ω),
      (restrictionPatterns C c n z).card ≤
        ∑ i ∈ Finset.range (d + 1), Nat.choose n i := by
  obtain ⟨d, hd⟩ := vcdim_finite_imp_growth_bounded Ω C hVC
  refine ⟨d, fun n hn c z ↦ ?_⟩
  exact (restrictionPatterns_card_le_growth C c n z).trans (hd n hn)

/-! ## Variance-sensitive Rademacher tails -/

/-- Exact-variance Rademacher MGF bound.  In contrast with a uniform `|aᵢ| ≤ c` bound, the
exponent retains `∑ i, aᵢ²`; for indicator patterns this is the observed shell mass. -/
theorem rademacher_mgf_sum_sq_bound {m : ℕ} (a : Fin m → ℝ) (t : ℝ) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m, Real.exp (t * ∑ i, a i * boolToSign (σ i)) ≤
      Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := by
  have hstep : ∀ σ : SignVector m,
      Real.exp (t * ∑ i, a i * boolToSign (σ i)) =
        ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  simp_rw [hstep]
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * a i * boolToSign (σ i)) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * a i * boolToSign b) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m ↦ Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) ↦ Real.exp (t * a i * boolToSign b))]
  have hcard : (Fintype.card (SignVector m) : ℝ) = (2 : ℝ) ^ m := by
    simp
  have hinv : (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = (1 / 2 : ℝ) ^ m := by
    rw [hcard, one_div, one_div, inv_pow]
  rw [hinv]
  have hprod_const : ((1 / 2 : ℝ) ^ m : ℝ) = ∏ _i : Fin m, (1 / 2 : ℝ) := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod_const, ← Finset.prod_mul_distrib]
  have hfactor : ∀ i : Fin m,
      (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b) ≤
        Real.exp ((t * a i) ^ 2 / 2) := by
    intro i
    have hsum : ∑ b : Bool, Real.exp (t * a i * boolToSign b) =
        Real.exp (t * a i) + Real.exp (-(t * a i)) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1 <;> ring_nf
    rw [hsum]
    rw [show (1 / 2 : ℝ) * (Real.exp (t * a i) + Real.exp (-(t * a i))) =
      Real.cosh (t * a i) by rw [Real.cosh_eq]; ring]
    exact cosh_le_exp_sq_half _
  have hnonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b) := by
    intro i _
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun b _ ↦ (Real.exp_pos _).le)
  calc
    ∏ i : Fin m, (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * a i * boolToSign b)
        ≤ ∏ i : Fin m, Real.exp ((t * a i) ^ 2 / 2) :=
          Finset.prod_le_prod hnonneg fun i _ ↦ hfactor i
    _ = Real.exp (∑ i : Fin m, (t * a i) ^ 2 / 2) :=
      (Real.exp_sum Finset.univ _).symm
    _ = Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := by
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- One-sided counting form of the variance-sensitive Rademacher tail. -/
theorem rademacher_sum_tail_card {m : ℕ} (a : Fin m → ℝ) {u : ℝ} (hu : 0 < u)
    (hvar : 0 < ∑ i, a i ^ 2) :
    ((Finset.univ.filter
      (fun σ : SignVector m ↦ u ≤ ∑ i, a i * boolToSign (σ i))).card : ℝ) ≤
      (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := by
  let variance : ℝ := ∑ i, a i ^ 2
  let t : ℝ := u / variance
  have ht : 0 < t := div_pos hu hvar
  let good := Finset.univ.filter
    (fun σ : SignVector m ↦ u ≤ ∑ i, a i * boolToSign (σ i))
  have hterm : ∀ σ ∈ good,
      Real.exp (t * u) ≤ Real.exp (t * ∑ i, a i * boolToSign (σ i)) := by
    intro σ hσ
    apply Real.exp_le_exp.mpr
    have hσ' : u ≤ ∑ i, a i * boolToSign (σ i) := (Finset.mem_filter.mp hσ).2
    exact mul_le_mul_of_nonneg_left hσ' ht.le
  have hfilter : (good.card : ℝ) * Real.exp (t * u) ≤
      ∑ σ ∈ good, Real.exp (t * ∑ i, a i * boolToSign (σ i)) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum good _ _ hterm
  have hsub : ∑ σ ∈ good, Real.exp (t * ∑ i, a i * boolToSign (σ i)) ≤
      ∑ σ : SignVector m, Real.exp (t * ∑ i, a i * boolToSign (σ i)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun σ _ _ ↦ (Real.exp_pos _).le)
  have hcard_pos : (0 : ℝ) < Fintype.card (SignVector m) := by positivity
  have hmgf := rademacher_mgf_sum_sq_bound a t
  have hall : ∑ σ : SignVector m, Real.exp (t * ∑ i, a i * boolToSign (σ i)) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t ^ 2 * variance / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hmgf hcard_pos.le
    calc
      ∑ σ : SignVector m, Real.exp (t * ∑ i, a i * boolToSign (σ i)) =
          (Fintype.card (SignVector m) : ℝ) *
            ((1 / (Fintype.card (SignVector m) : ℝ)) *
              ∑ σ : SignVector m, Real.exp (t * ∑ i, a i * boolToSign (σ i))) := by
        field_simp
      _ ≤ (Fintype.card (SignVector m) : ℝ) *
          Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := hmul
      _ = (Fintype.card (SignVector m) : ℝ) * Real.exp (t ^ 2 * variance / 2) := by
        rfl
  have hchain := (hfilter.trans hsub).trans hall
  have hexp_pos : 0 < Real.exp (t * u) := Real.exp_pos _
  have hdiv : (good.card : ℝ) ≤
      (Fintype.card (SignVector m) : ℝ) * Real.exp (t ^ 2 * variance / 2) /
        Real.exp (t * u) := (le_div_iff₀ hexp_pos).mpr hchain
  calc
    (good.card : ℝ) ≤
        (Fintype.card (SignVector m) : ℝ) * Real.exp (t ^ 2 * variance / 2) /
          Real.exp (t * u) := hdiv
    _ = (Fintype.card (SignVector m) : ℝ) *
        Real.exp (t ^ 2 * variance / 2 - t * u) := by
      rw [Real.exp_sub]
      ring
    _ = (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := by
      congr 2
      dsimp [t, variance]
      field_simp
      ring

/-- Two-sided variance-sensitive Rademacher tail in counting form. -/
theorem rademacher_abs_sum_tail_card {m : ℕ} (a : Fin m → ℝ) {u : ℝ} (hu : 0 < u)
    (hvar : 0 < ∑ i, a i ^ 2) :
    ((Finset.univ.filter
      (fun σ : SignVector m ↦ u ≤ |∑ i, a i * boolToSign (σ i)|)).card : ℝ) ≤
      2 * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := by
  let positive := Finset.univ.filter
    (fun σ : SignVector m ↦ u ≤ ∑ i, a i * boolToSign (σ i))
  let negative := Finset.univ.filter
    (fun σ : SignVector m ↦ u ≤ ∑ i, (-a i) * boolToSign (σ i))
  let bad := Finset.univ.filter
    (fun σ : SignVector m ↦ u ≤ |∑ i, a i * boolToSign (σ i)|)
  have hsubset : bad ⊆ positive ∪ negative := by
    intro σ hσ
    simp only [positive, negative, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [le_abs] at hσ
    rcases hσ with hσ | hσ
    · exact Or.inl hσ
    · right
      simpa [← Finset.sum_neg_distrib] using hσ
  have hpos := rademacher_sum_tail_card a hu hvar
  have hvar_neg : 0 < ∑ i, (-a i) ^ 2 := by
    simpa only [neg_sq] using hvar
  have hneg := rademacher_sum_tail_card (fun i ↦ -a i) hu hvar_neg
  have hneg' : (negative.card : ℝ) ≤
      (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := by
    simpa only [negative, neg_sq] using hneg
  calc
    (bad.card : ℝ) ≤ ((positive ∪ negative).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (positive.card : ℝ) + negative.card := by
      exact_mod_cast Finset.card_union_le positive negative
    _ ≤ (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) +
        (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := add_le_add hpos hneg'
    _ = 2 * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) := by ring

/-- Two-sided Rademacher tail with only an upper bound on the realized variance.  Patterns with
zero variance are discharged internally: their signed sum is identically zero, hence cannot cross
a positive threshold. -/
theorem rademacher_abs_sum_tail_card_of_variance_le {m : ℕ} (a : Fin m → ℝ)
    {u varianceCap : ℝ} (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hvar_le : ∑ i, a i ^ 2 ≤ varianceCap) :
    ((Finset.univ.filter
      (fun σ : SignVector m ↦ u ≤ |∑ i, a i * boolToSign (σ i)|)).card : ℝ) ≤
      2 * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
  classical
  have hvar_nonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rcases hvar_nonneg.eq_or_lt with hvar_zero | hvar_pos
  · have ha_zero : ∀ i, a i = 0 := by
      intro i
      have hai_sq : a i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp hvar_zero.symm i
          (Finset.mem_univ i)
      nlinarith [sq_nonneg (a i)]
    have hfilter : Finset.univ.filter
        (fun σ : SignVector m ↦ u ≤ |∑ i, a i * boolToSign (σ i)|) = ∅ := by
      ext σ
      simp [ha_zero, not_le_of_gt hu]
    rw [hfilter]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hbase := rademacher_abs_sum_tail_card a hu hvar_pos
    have hdenCap : 0 < 2 * varianceCap := mul_pos (by norm_num) hvarianceCap
    have hdenVar : 0 < 2 * ∑ i, a i ^ 2 := mul_pos (by norm_num) hvar_pos
    have hfrac : u ^ 2 / (2 * varianceCap) ≤ u ^ 2 / (2 * ∑ i, a i ^ 2) := by
      rw [div_le_div_iff₀ hdenCap hdenVar]
      nlinarith [sq_nonneg u]
    have hexp : Real.exp (-(u ^ 2) / (2 * ∑ i, a i ^ 2)) ≤
        Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hfrac
    exact hbase.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Union of the two-sided Rademacher tail over a finite family of coefficient patterns. -/
theorem rademacher_finitePattern_tail_card
    {ρ : Type*} {m : ℕ} (patterns : Finset ρ) (coeff : ρ → Fin m → ℝ)
    (threshold : ρ → ℝ)
    (hthreshold : ∀ p ∈ patterns, 0 < threshold p)
    (hvar : ∀ p ∈ patterns, 0 < ∑ i, coeff p i ^ 2) :
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ patterns, threshold p ≤
        |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
      ∑ p ∈ patterns,
        2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-((threshold p) ^ 2) / (2 * ∑ i, coeff p i ^ 2)) := by
  classical
  let bad : ρ → Finset (SignVector m) := fun p ↦
    Finset.univ.filter (fun σ ↦ threshold p ≤ |∑ i, coeff p i * boolToSign (σ i)|)
  let allBad : Finset (SignVector m) := Finset.univ.filter (fun σ ↦
    ∃ p ∈ patterns, threshold p ≤ |∑ i, coeff p i * boolToSign (σ i)|)
  have hsubset : allBad ⊆ patterns.biUnion bad := by
    intro σ hσ
    simp only [allBad, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨p, hp, hbad⟩ := hσ
    exact Finset.mem_biUnion.mpr ⟨p, hp, by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hbad⟩
  calc
    (allBad.card : ℝ) ≤ ((patterns.biUnion bad).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ patterns, ((bad p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p ∈ patterns,
        2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-((threshold p) ^ 2) / (2 * ∑ i, coeff p i ^ 2)) := by
      exact Finset.sum_le_sum fun p hp ↦ by
        simpa only [bad] using
          rademacher_abs_sum_tail_card (coeff p) (hthreshold p hp) (hvar p hp)

/-- Finite-pattern Rademacher union bound with a common variance cap.  This version is the one used
by the VC exchangeability layer because it includes constant restriction patterns. -/
theorem rademacher_finitePattern_tail_card_of_variance_le
    {ρ : Type*} {m : ℕ} (patterns : Finset ρ) (coeff : ρ → Fin m → ℝ)
    {u varianceCap : ℝ} (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hvar_le : ∀ p ∈ patterns, ∑ i, coeff p i ^ 2 ≤ varianceCap) :
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ patterns, u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
      (patterns.card : ℝ) *
        (2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap))) := by
  classical
  let bad : ρ → Finset (SignVector m) := fun p ↦
    Finset.univ.filter (fun σ ↦ u ≤ |∑ i, coeff p i * boolToSign (σ i)|)
  let allBad : Finset (SignVector m) := Finset.univ.filter (fun σ ↦
    ∃ p ∈ patterns, u ≤ |∑ i, coeff p i * boolToSign (σ i)|)
  have hsubset : allBad ⊆ patterns.biUnion bad := by
    intro σ hσ
    simp only [allBad, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨p, hp, hbad⟩ := hσ
    exact Finset.mem_biUnion.mpr ⟨p, hp, by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hbad⟩
  calc
    (allBad.card : ℝ) ≤ ((patterns.biUnion bad).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ patterns, ((bad p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ patterns,
        2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      exact Finset.sum_le_sum fun p hp ↦ by
        simpa only [bad] using rademacher_abs_sum_tail_card_of_variance_le
          (coeff p) hu hvarianceCap (hvar_le p hp)
    _ = (patterns.card : ℝ) *
        (2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap))) := by
      rw [Finset.sum_const, nsmul_eq_mul]

omit [MeasurableSpace Ω] in
/-- VC growth-function bound for variance-sensitive Rademacher patterns, including zero-variance
patterns.  The only sample-dependent hypothesis is the genuine quadratic-variation bound. -/
theorem rademacher_vc_pattern_tail_card_of_variance_le [Infinite Ω]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (q : ℕ) (z : Fin q → Ω)
    {m : ℕ} (coeff : (Fin q → Bool) → Fin m → ℝ)
    {u varianceCap : ℝ} (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hvar_le : ∀ p ∈ restrictionPatterns C c q z,
      ∑ i, coeff p i ^ 2 ≤ varianceCap) :
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
      2 * (GrowthFunction Ω C q : ℝ) * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
  let patterns := restrictionPatterns C c q z
  let common : ℝ := 2 * (Fintype.card (SignVector m) : ℝ) *
    Real.exp (-(u ^ 2) / (2 * varianceCap))
  have hfinite := rademacher_finitePattern_tail_card_of_variance_le
    patterns coeff hu hvarianceCap hvar_le
  calc
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ)
        ≤ (patterns.card : ℝ) * common := by
          simpa only [patterns, common] using hfinite
    _ ≤ (GrowthFunction Ω C q : ℝ) * common := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast restrictionPatterns_card_le_growth C c q z
      · dsimp [common]
        positivity
    _ = 2 * (GrowthFunction Ω C q : ℝ) *
        (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      dsimp [common]
      ring

omit [MeasurableSpace Ω] in
/-- VC/Sauer plus the variance-sensitive Rademacher tail.  This is the finite-pattern combination
theorem used after symmetrization: the only combinatorial factor left is `GrowthFunction`. -/
theorem rademacher_vc_pattern_tail_card [Infinite Ω]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (q : ℕ) (z : Fin q → Ω)
    {m : ℕ} (coeff : (Fin q → Bool) → Fin m → ℝ)
    {u varianceCap : ℝ} (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hvar_pos : ∀ p ∈ restrictionPatterns C c q z, 0 < ∑ i, coeff p i ^ 2)
    (hvar_le : ∀ p ∈ restrictionPatterns C c q z,
      ∑ i, coeff p i ^ 2 ≤ varianceCap) :
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
      2 * (GrowthFunction Ω C q : ℝ) * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
  let patterns := restrictionPatterns C c q z
  have hfinite := rademacher_finitePattern_tail_card patterns coeff (fun _ ↦ u)
    (fun p hp ↦ hu) hvar_pos
  let common : ℝ := 2 * (Fintype.card (SignVector m) : ℝ) *
    Real.exp (-(u ^ 2) / (2 * varianceCap))
  have hterm : ∀ p ∈ patterns,
      2 * (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * ∑ i, coeff p i ^ 2)) ≤ common := by
    intro p hp
    have hVpos := hvar_pos p hp
    have hVle := hvar_le p hp
    have hdenCap : 0 < 2 * varianceCap := mul_pos (by norm_num) hvarianceCap
    have hdenV : 0 < 2 * ∑ i, coeff p i ^ 2 := mul_pos (by norm_num) hVpos
    have hfrac : u ^ 2 / (2 * varianceCap) ≤
        u ^ 2 / (2 * ∑ i, coeff p i ^ 2) := by
      rw [div_le_div_iff₀ hdenCap hdenV]
      nlinarith [sq_nonneg u]
    dsimp [common]
    have hneg : -u ^ 2 / (2 * ∑ i, coeff p i ^ 2) ≤
        -u ^ 2 / (2 * varianceCap) := by
      simpa only [neg_div] using neg_le_neg hfrac
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hneg) (by positivity)
  calc
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ)
        ≤ ∑ p ∈ patterns,
            2 * (Fintype.card (SignVector m) : ℝ) *
              Real.exp (-(u ^ 2) / (2 * ∑ i, coeff p i ^ 2)) := hfinite
    _ ≤ ∑ _p ∈ patterns, common := Finset.sum_le_sum hterm
    _ = (patterns.card : ℝ) * common := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (GrowthFunction Ω C q : ℝ) * common := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast restrictionPatterns_card_le_growth C c q z
      · dsimp [common]
        positivity
    _ = 2 * (GrowthFunction Ω C q : ℝ) *
        (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      dsimp [common]
      ring

omit [MeasurableSpace Ω] in
/-- Fully combined VC/Sauer/variance-sensitive Rademacher bound.  The degree `d` is produced by
the imported finite-VC theorem; no extra combinatorial hypothesis remains in the interface. -/
theorem rademacher_vc_sauer_pattern_tail_card [Infinite Ω]
    (C : ConceptClass Ω Bool) (hVC : VCDim Ω C < ⊤) :
    ∃ d : ℕ, ∀ (q : ℕ), d ≤ q →
      ∀ (c : Concept Ω Bool) (z : Fin q → Ω) (m : ℕ)
        (coeff : (Fin q → Bool) → Fin m → ℝ) (u varianceCap : ℝ),
        0 < u → 0 < varianceCap →
        (∀ p ∈ restrictionPatterns C c q z, 0 < ∑ i, coeff p i ^ 2) →
        (∀ p ∈ restrictionPatterns C c q z, ∑ i, coeff p i ^ 2 ≤ varianceCap) →
        ((Finset.univ.filter (fun σ : SignVector m ↦
          ∃ p ∈ restrictionPatterns C c q z,
            u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
          2 * (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) *
            (Fintype.card (SignVector m) : ℝ) *
              Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
  obtain ⟨d, hd⟩ := vcdim_finite_imp_growth_bounded Ω C hVC
  refine ⟨d, ?_⟩
  intro q hq c z m coeff u varianceCap hu hvarianceCap hvar_pos hvar_le
  have hbase := rademacher_vc_pattern_tail_card C c q z coeff hu hvarianceCap
    hvar_pos hvar_le
  let factor : ℝ := 2 * (Fintype.card (SignVector m) : ℝ) *
    Real.exp (-(u ^ 2) / (2 * varianceCap))
  have hgrowth : (GrowthFunction Ω C q : ℝ) ≤
      (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) := by
    exact_mod_cast hd q hq
  calc
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ)
        ≤ 2 * (GrowthFunction Ω C q : ℝ) *
          (Fintype.card (SignVector m) : ℝ) *
            Real.exp (-(u ^ 2) / (2 * varianceCap)) := hbase
    _ = (GrowthFunction Ω C q : ℝ) * factor := by
      dsimp [factor]
      ring
    _ ≤ (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) * factor := by
      exact mul_le_mul_of_nonneg_right hgrowth (by dsimp [factor]; positivity)
    _ = 2 * (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) *
        (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      dsimp [factor]
      push_cast
      ring

omit [MeasurableSpace Ω] in
/-- Fully combined finite-VC/Sauer/variance-sensitive Rademacher bound without a nondegeneracy
side condition.  Constant patterns are handled by the theorem itself. -/
theorem rademacher_vc_sauer_pattern_tail_card_of_variance_le [Infinite Ω]
    (C : ConceptClass Ω Bool) (hVC : VCDim Ω C < ⊤) :
    ∃ d : ℕ, ∀ (q : ℕ), d ≤ q →
      ∀ (c : Concept Ω Bool) (z : Fin q → Ω) (m : ℕ)
        (coeff : (Fin q → Bool) → Fin m → ℝ) (u varianceCap : ℝ),
        0 < u → 0 < varianceCap →
        (∀ p ∈ restrictionPatterns C c q z,
          ∑ i, coeff p i ^ 2 ≤ varianceCap) →
        ((Finset.univ.filter (fun σ : SignVector m ↦
          ∃ p ∈ restrictionPatterns C c q z,
            u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) ≤
          2 * (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) *
            (Fintype.card (SignVector m) : ℝ) *
              Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
  obtain ⟨d, hd⟩ := vcdim_finite_imp_growth_bounded Ω C hVC
  refine ⟨d, ?_⟩
  intro q hq c z m coeff u varianceCap hu hvarianceCap hvar_le
  have hbase := rademacher_vc_pattern_tail_card_of_variance_le
    C c q z coeff hu hvarianceCap hvar_le
  let factor : ℝ := 2 * (Fintype.card (SignVector m) : ℝ) *
    Real.exp (-(u ^ 2) / (2 * varianceCap))
  have hgrowth : (GrowthFunction Ω C q : ℝ) ≤
      (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) := by
    exact_mod_cast hd q hq
  calc
    ((Finset.univ.filter (fun σ : SignVector m ↦
      ∃ p ∈ restrictionPatterns C c q z,
        u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ)
        ≤ 2 * (GrowthFunction Ω C q : ℝ) *
          (Fintype.card (SignVector m) : ℝ) *
            Real.exp (-(u ^ 2) / (2 * varianceCap)) := hbase
    _ = (GrowthFunction Ω C q : ℝ) * factor := by
      dsimp [factor]
      ring
    _ ≤ (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) * factor := by
      exact mul_le_mul_of_nonneg_right hgrowth (by dsimp [factor]; positivity)
    _ = 2 * (∑ i ∈ Finset.range (d + 1), Nat.choose q i : ℕ) *
        (Fintype.card (SignVector m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap)) := by
      dsimp [factor]
      push_cast
      ring

end OTSelector.RelativeVC
