import OTSelector.Feedback.EndpointRegularity
import OTSelector.Probability.ConditionalNestedCDF

/-!
# Finite-sample nested endpoint tails

This file turns the conditional empirical-CDF estimate into a count-scale estimate.  The sample
is conditioned on its complete membership pattern in the largest endpoint complement, and the
selected coordinates are reindexed increasingly.  No independence claim is made after
conditioning only on the total count.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

set_option linter.style.haveILetI false

open OTSelector.CountConditioning
open OTSelector.Probability.NestedCDF
open OTSelector.Probability.ConditionalNestedCDF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Number of selected coordinates lying in a set. -/
noncomputable def selectedSetCount {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card = k)
    (sample : Fin n → Ω) (s : Set Ω) : ℝ := by
  classical
  exact ∑ j : Fin k, if selectedCoordinates J hJ sample j ∈ s then 1 else 0

/-- Number of all sample coordinates lying in a set. -/
noncomputable def sampleSetCountReal {n : ℕ} (sample : Fin n → Ω) (s : Set Ω) : ℝ := by
  classical
  exact ∑ i : Fin n, if sample i ∈ s then 1 else 0

/-- Centered unnormalized set count. -/
noncomputable def centeredSetCount {n : ℕ} (P : Measure Ω) (sample : Fin n → Ω)
    (s : Set Ω) : ℝ :=
  sampleSetCountReal sample s - (n : ℝ) * P.real s

omit [MeasurableSpace Ω] in
/-- Reindexing a sum over a membership pattern by `Fin J.card`. -/
theorem sum_selectedCoordinates {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card = k)
    (sample : Fin n → Ω) (f : Ω → ℝ) :
    ∑ j : Fin k, f (selectedCoordinates J hJ sample j) = ∑ i ∈ J, f (sample i) := by
  calc
    ∑ j : Fin k, f (selectedCoordinates J hJ sample j) =
        ∑ y : J, f (sample y) := by
      simpa [selectedCoordinates] using
        ((J.orderIsoOfFin hJ).toEquiv.sum_comp (fun y : J ↦ f (sample y)))
    _ = ∑ i ∈ J, f (sample i) := Finset.sum_attach J (fun i ↦ f (sample i))

omit [MeasurableSpace Ω] in
/-- On its full membership pattern, a count in a subset of `A` is exactly the count over the
reindexed selected coordinates. -/
theorem sampleSetCountReal_eq_selectedSetCount_of_subset
    {n k : ℕ} {A s : Set Ω} (hsA : s ⊆ A)
    (J : Finset (Fin n)) (hJ : J.card = k) (sample : Fin n → Ω)
    (hsample : sample ∈ membershipPattern A J) :
    sampleSetCountReal sample s = selectedSetCount J hJ sample s := by
  classical
  have hsum :
      (∑ i ∈ J, if sample i ∈ s then (1 : ℝ) else 0) =
        ∑ i : Fin n, if sample i ∈ s then (1 : ℝ) else 0 := by
    apply Finset.sum_subset (Finset.subset_univ J)
    intro i _ hiJ
    have hnotA : sample i ∉ A := by
      intro hiA
      exact hiJ ((mem_membershipPattern_iff.mp hsample i).mp hiA)
    have hnots : sample i ∉ s := fun his ↦ hnotA (hsA his)
    simp [hnots]
  rw [sampleSetCountReal, selectedSetCount, ← hsum]
  symm
  simpa using sum_selectedCoordinates J hJ sample
    (fun z ↦ if z ∈ s then (1 : ℝ) else 0)

/-- Number of selected coordinates whose score lies in a strict upper half-line. -/
noncomputable def selectedUpperCount {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card = k)
    (sample : Fin n → Ω) (score : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin k, if t < score (selectedCoordinates J hJ sample j) then 1 else 0

/-- Count centered at the conditional probability inside the selected region. -/
noncomputable def selectedUpperResidual {n k : ℕ} (P : Measure Ω) (A : Set Ω)
    (J : Finset (Fin n)) (hJ : J.card = k) (sample : Fin n → Ω)
    (score : Ω → ℝ) (t : ℝ) : ℝ :=
  selectedUpperCount J hJ sample score t -
    (k : ℝ) * (P[|A]).real (score ⁻¹' Set.Ioi t)

omit [MeasurableSpace Ω] in theorem selectedUpperCount_eq_selectedSetCount_preimage
    {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card = k)
    (sample : Fin n → Ω) (score : Ω → ℝ) (t : ℝ) :
    selectedUpperCount J hJ sample score t =
      selectedSetCount J hJ sample (score ⁻¹' Set.Ioi t) := by
  classical
  simp [selectedUpperCount, selectedSetCount]

theorem selectedUpperResidual_eq_setResidual
    {n k : ℕ} (P : Measure Ω) (A : Set Ω)
    (J : Finset (Fin n)) (hJ : J.card = k) (sample : Fin n → Ω)
    (score : Ω → ℝ) (t : ℝ) :
    selectedUpperResidual P A J hJ sample score t =
      selectedSetCount J hJ sample (score ⁻¹' Set.Ioi t) -
        (k : ℝ) * (P[|A]).real (score ⁻¹' Set.Ioi t) := by
  rw [selectedUpperResidual, selectedUpperCount_eq_selectedSetCount_preimage]

/-- The upper-half-line selected residual is exactly `k` times the negative CDF discrepancy. -/
theorem selectedUpperResidual_eq_neg_mul_cdfGap
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (_hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (hk : 0 < k)
    (sample : Fin n → Ω) (score : Ω → ℝ) (hscore : Measurable score) (t : ℝ) :
    selectedUpperResidual P A J hJ sample score t =
      -(k : ℝ) *
        (empCDF
          (fun j : Fin k ↦ fun sample' ↦ score (selectedCoordinates J hJ sample' j))
          sample t - cdf ((P[|A]).map score) t) := by
  letI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hA0
  letI : IsProbabilityMeasure ((P[|A]).map score) :=
    Measure.isProbabilityMeasure_map hscore.aemeasurable
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hcount :
      selectedUpperCount J hJ sample score t =
        (k : ℝ) - (k : ℝ) *
          empCDF
            (fun j : Fin k ↦ fun sample' ↦ score (selectedCoordinates J hJ sample' j))
            sample t := by
    have hpartition :
        (∑ j : Fin k,
            if t < score (selectedCoordinates J hJ sample j) then (1 : ℝ) else 0) +
          ∑ j : Fin k,
            (if score (selectedCoordinates J hJ sample j) ≤ t then (1 : ℝ) else 0) = k := by
      rw [← Finset.sum_add_distrib]
      calc
        (∑ j : Fin k,
            ((if t < score (selectedCoordinates J hJ sample j) then (1 : ℝ) else 0) +
              if score (selectedCoordinates J hJ sample j) ≤ t then (1 : ℝ) else 0)) =
            ∑ _j : Fin k, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hle : score (selectedCoordinates J hJ sample j) ≤ t
              · simp [hle, not_lt_of_ge hle]
              · simp [hle, lt_of_not_ge hle]
        _ = k := by simp
    rw [selectedUpperCount, empCDF, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul]
    linarith
  have hcdf : cdf ((P[|A]).map score) t = (P[|A]).real (score ⁻¹' Set.Iic t) := by
    rw [cdf_eq_real, Measure.real, Measure.real, Measure.map_apply hscore measurableSet_Iic]
  have hcompl :
      (P[|A]).real (score ⁻¹' Set.Ioi t) =
        1 - (P[|A]).real (score ⁻¹' Set.Iic t) := by
    rw [show score ⁻¹' Set.Ioi t = (score ⁻¹' Set.Iic t)ᶜ by ext z; simp,
      measureReal_compl (measurableSet_Iic.preimage hscore), probReal_univ]
  rw [selectedUpperResidual, hcount, hcdf, hcompl]
  ring

/-- A Kolmogorov bound controls every selected upper-half-line count simultaneously. -/
theorem abs_selectedUpperResidual_le_mul_ksDist
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (hk : 0 < k)
    (sample : Fin n → Ω) (score : Ω → ℝ) (hscore : Measurable score) (t : ℝ) :
    |selectedUpperResidual P A J hJ sample score t| ≤
      (k : ℝ) *
        ksDist
          (fun j : Fin k ↦ fun sample' ↦ score (selectedCoordinates J hJ sample' j))
          ((P[|A]).map score) sample := by
  letI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hA0
  letI : IsProbabilityMeasure ((P[|A]).map score) :=
    Measure.isProbabilityMeasure_map hscore.aemeasurable
  rw [selectedUpperResidual_eq_neg_mul_cdfGap P A hA hA0 J hJ hk sample score hscore t,
    abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg k)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  rw [ksDist]
  have hbdd : BddAbove (Set.range fun u : ℝ ↦
      |empCDF
          (fun j : Fin k ↦ fun sample' ↦ score (selectedCoordinates J hJ sample' j))
          sample u - cdf ((P[|A]).map score) u|) := ⟨1, by
    rintro _ ⟨u, rfl⟩
    exact abs_empCDF_sub_cdf_le_one hk _ _ sample u⟩
  exact le_ciSup hbdd t

/-- Outside the mixed full-pattern Kolmogorov event, every nonempty selected pattern obeys the
natural `d * sqrt(k)` count bound. -/
theorem abs_selectedUpperResidual_lt_of_not_patternwiseEvent
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (hk : 0 < J.card)
    (sample : Fin n → Ω) (hsample : sample ∈ membershipPattern A J)
    (score : Ω → ℝ) (hscore : Measurable score) (d : ℝ)
    (hgood : sample ∉ patternwiseEvent A (patternKSEvent P A score d)) (t : ℝ) :
    |selectedUpperResidual P A J rfl sample score t| < d * Real.sqrt J.card := by
  have hnot : sample ∉ patternKSEvent P A score d J := by
    intro hbad
    exact hgood (Set.mem_iUnion.mpr ⟨J, hsample, hbad⟩)
  have hks :
      ksDist
          (fun j : Fin J.card ↦
            fun sample' ↦ score (selectedCoordinates J rfl sample' j))
          ((P[|A]).map score) sample < d / Real.sqrt J.card := by
    rw [patternKSEvent, dite_eq_left hk] at hnot
    exact lt_of_not_ge hnot
  have hbase := abs_selectedUpperResidual_le_mul_ksDist
    P A hA hA0 J rfl hk sample score hscore t
  have hkreal : 0 < (J.card : ℝ) := Nat.cast_pos.mpr hk
  have hsqrt : 0 < Real.sqrt (J.card : ℝ) := Real.sqrt_pos.2 hkreal
  calc
    |selectedUpperResidual P A J rfl sample score t|
        ≤ (J.card : ℝ) * ksDist
            (fun j : Fin J.card ↦
              fun sample' ↦ score (selectedCoordinates J rfl sample' j))
            ((P[|A]).map score) sample := hbase
    _ < (J.card : ℝ) * (d / Real.sqrt J.card) := mul_lt_mul_of_pos_left hks hkreal
    _ = d * Real.sqrt J.card := by
      have hsquare : Real.sqrt (J.card : ℝ) * Real.sqrt J.card = J.card :=
        Real.mul_self_sqrt hkreal.le
      have hdiv : (J.card : ℝ) / Real.sqrt J.card = Real.sqrt J.card := by
        rw [div_eq_iff hsqrt.ne']
        exact hsquare.symm
      calc
        (J.card : ℝ) * (d / Real.sqrt J.card) =
            d * ((J.card : ℝ) / Real.sqrt J.card) := by ring
        _ = d * Real.sqrt J.card := by rw [hdiv]

/-- The mixed bad event for a nested selected count has probability at most `4 / d`. -/
theorem measure_nestedSelectedBadEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score) {d : ℝ} (hd : 0 < d) :
    Measure.pi (fun _ : Fin n ↦ P)
        (patternwiseEvent A (patternKSEvent P A score d)) ≤ ENNReal.ofReal (4 / d) := by
  exact measure_patternKSEvent_le P A hA hA0 hAc0 score hscore hd

/-- Deterministic decomposition of a centered nested count into its conditional-CDF residual and
the centered count of the largest selecting set. -/
theorem centeredCount_decomposition {n k : ℕ} {countC massC massA : ℝ}
    (hmassA : massA ≠ 0) :
    countC - (n : ℝ) * massC =
      (countC - (k : ℝ) * (massC / massA)) +
        (massC / massA) * ((k : ℝ) - (n : ℝ) * massA) := by
  field_simp
  ring

/-- Conditional mass times the selecting-set mass is the mass of the intersection. -/
theorem condReal_mul_parentReal
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (s : Set Ω) :
    (P[|A]).real s * P.real A = P.real (A ∩ s) := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hA s P)
  simpa [Measure.real, ENNReal.toReal_mul] using h

/-- Exact selected-count decomposition, with no division and hence no hidden zero-mass branch. -/
theorem centeredSetCount_eq_selectedResidual_add
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A s : Set Ω) (hA : MeasurableSet A) (hsA : s ⊆ A)
    (J : Finset (Fin n)) (hJ : J.card = k) (sample : Fin n → Ω)
    (hsample : sample ∈ membershipPattern A J) :
    centeredSetCount P sample s =
      (selectedSetCount J hJ sample s - (k : ℝ) * (P[|A]).real s) +
        (P[|A]).real s * centeredSetCount P sample A := by
  have hcount := sampleSetCountReal_eq_selectedSetCount_of_subset hsA J hJ sample hsample
  have hcountA : sampleSetCountReal sample A = k := by
    have hselected := sampleSetCountReal_eq_selectedSetCount_of_subset
      (A := A) (s := A) (Set.Subset.rfl) J hJ sample hsample
    rw [hselected, selectedSetCount]
    have hmem : ∀ j : Fin k, selectedCoordinates J hJ sample j ∈ A := by
      intro j
      exact (mem_membershipPattern_iff.mp hsample _).mpr
        (Finset.orderEmbOfFin_mem J hJ j)
    simp [hmem]
  have hmass := condReal_mul_parentReal P A hA s
  have hinter : A ∩ s = s := Set.inter_eq_right.mpr hsA
  rw [hinter] at hmass
  rw [centeredSetCount, centeredSetCount, hcount, hcountA]
  nlinarith

omit [MeasurableSpace Ω] in
/-- The selecting-set count equals the cardinality of its full membership pattern. -/
theorem sampleSetCountReal_eq_card_of_mem_membershipPattern
    {n : ℕ} {A : Set Ω} (J : Finset (Fin n)) (sample : Fin n → Ω)
    (hsample : sample ∈ membershipPattern A J) :
    sampleSetCountReal sample A = J.card := by
  have hcount := sampleSetCountReal_eq_selectedSetCount_of_subset
    (A := A) (s := A) (Set.Subset.rfl) J rfl sample hsample
  rw [hcount, selectedSetCount]
  have hselected : ∀ j : Fin J.card, selectedCoordinates J rfl sample j ∈ A := by
    intro j
    exact (mem_membershipPattern_iff.mp hsample _).mpr (Finset.orderEmbOfFin_mem J rfl j)
  simp [hselected]

/-- A centered selecting-set count is the usual normalized indicator process in count scale. -/
theorem centeredSetCount_eq_sqrt_mul_empiricalProcess
    {n : ℕ} (P : Measure Ω) (hn : 0 < n) (sample : Fin n → Ω)
    (A : Set Ω) (hA : MeasurableSet A) :
    centeredSetCount P sample A = Real.sqrt n *
      EmpiricalProcess.empiricalProcess P n sample (indicatorReal A) := by
  classical
  have hproc := empiricalProcess_indicator P n sample A hA
  have hsqrt : Real.sqrt (n : ℝ) * Real.sqrt n = n :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  rw [centeredSetCount, sampleSetCountReal, hproc, ← mul_assoc, hsqrt]
  have hsum :
      (∑ i : Fin n, if sample i ∈ A then (1 : ℝ) else 0) =
        (n : ℝ) * empiricalSetMass n sample A := by
    rw [empiricalSetMass, EmpiricalProcess.empiricalAverage]
    simp only [indicatorReal, Set.indicator_apply]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    simp
  rw [hsum, empiricalSetDeviation]
  ring

/-- The existing Boolean error-count API agrees with the generic centered set count. -/
theorem centeredErrorSum_eq_centeredSetCount
    (P : Measure Ω) {n : ℕ} (h c : Concept Ω Bool) (sample : Fin n → Ω) :
    centeredErrorSum P h c sample = centeredSetCount P sample (errorSet h c) := by
  classical
  simp only [centeredErrorSum, centeredSetCount, sampleSetCountReal, sampleErrorSum,
    ← indicatorReal_errorSet]
  congr 2

/-- Pointwise assembly: a good nested-CDF event plus a good largest-set count controls every
nested centered count. -/
theorem abs_centeredSetCount_lt_of_nested_and_max_good
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (hk : 0 < J.card)
    (sample : Fin n → Ω) (hsample : sample ∈ membershipPattern A J)
    (score : Ω → ℝ) (hscore : Measurable score) (t d r : ℝ)
    (hsubset : score ⁻¹' Set.Ioi t ⊆ A)
    (hnested : sample ∉ patternwiseEvent A (patternKSEvent P A score d))
    (hmax : |centeredSetCount P sample A| ≤ r) (hr : 0 ≤ r) :
    |centeredSetCount P sample (score ⁻¹' Set.Ioi t)| <
      d * Real.sqrt J.card + r := by
  letI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hA0
  have hdecomp := centeredSetCount_eq_selectedResidual_add
    P A (score ⁻¹' Set.Ioi t) hA hsubset J rfl sample hsample
  have hnestedBound := abs_selectedUpperResidual_lt_of_not_patternwiseEvent
    P A hA hA0 J hk sample hsample score hscore d hnested t
  have hq0 : 0 ≤ (P[|A]).real (score ⁻¹' Set.Ioi t) := measureReal_nonneg
  have hq1 : (P[|A]).real (score ⁻¹' Set.Ioi t) ≤ 1 := measureReal_le_one
  have hscaled :
      |(P[|A]).real (score ⁻¹' Set.Ioi t) * centeredSetCount P sample A| ≤ r := by
    rw [abs_mul, abs_of_nonneg hq0]
    calc
      (P[|A]).real (score ⁻¹' Set.Ioi t) * |centeredSetCount P sample A|
          ≤ (P[|A]).real (score ⁻¹' Set.Ioi t) * r :=
        mul_le_mul_of_nonneg_left hmax hq0
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right hq1 hr
      _ = r := one_mul r
  calc
    |centeredSetCount P sample (score ⁻¹' Set.Ioi t)| =
        |(selectedSetCount J rfl sample (score ⁻¹' Set.Ioi t) -
            (J.card : ℝ) * (P[|A]).real (score ⁻¹' Set.Ioi t)) +
          (P[|A]).real (score ⁻¹' Set.Ioi t) * centeredSetCount P sample A| :=
      congrArg abs hdecomp
    _ ≤ |selectedSetCount J rfl sample (score ⁻¹' Set.Ioi t) -
          (J.card : ℝ) * (P[|A]).real (score ⁻¹' Set.Ioi t)| +
        |(P[|A]).real (score ⁻¹' Set.Ioi t) * centeredSetCount P sample A| :=
      abs_add_le _ _
    _ < d * Real.sqrt J.card + r := by
      exact add_lt_add_of_lt_of_le (by simpa [selectedUpperResidual_eq_setResidual]
        using hnestedBound) hscaled

/-- The union of the nested-CDF bad event and the selecting-set Bernstein event. -/
noncomputable def nestedAndMaxBadEvent {n : ℕ} (P : Measure Ω) (A : Set Ω)
    (score : Ω → ℝ) (d x : ℝ) : Set (Fin n → Ω) :=
  patternwiseEvent A (patternKSEvent P A score d) ∪
    {sample | x <
      |EmpiricalProcess.empiricalProcess P n sample (indicatorReal A)|}

/-- Actual finite-sample probability bound for the two ingredients of the endpoint estimate. -/
theorem measure_nestedAndMaxBadEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score)
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) (hn : 1 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ P) (nestedAndMaxBadEvent P A score d x) ≤
      ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) / (4 * (P.real A + x / Real.sqrt n)))) := by
  calc
    Measure.pi (fun _ : Fin n ↦ P) (nestedAndMaxBadEvent P A score d x) ≤
        Measure.pi (fun _ : Fin n ↦ P)
            (patternwiseEvent A (patternKSEvent P A score d)) +
          Measure.pi (fun _ : Fin n ↦ P)
            {sample | x <
              |EmpiricalProcess.empiricalProcess P n sample (indicatorReal A)|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) / (4 * (P.real A + x / Real.sqrt n)))) :=
      add_le_add
        (measure_nestedSelectedBadEvent_le P A hA hA0 hAc0 score hscore hd)
        (centeredIndicator_bernstein_pi P A hA n hn hx)

/-- Outside the combined bad event, the nested centered count is controlled at the deterministic
scale obtained from a population mass cap for the largest selecting set. -/
theorem abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (hk : 0 < J.card)
    (sample : Fin n → Ω) (hsample : sample ∈ membershipPattern A J)
    (score : Ω → ℝ) (hscore : Measurable score) (t d x massCap : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hx : 0 < x)
    (hmass : P.real A ≤ massCap)
    (hsubset : score ⁻¹' Set.Ioi t ⊆ A)
    (hgood : sample ∉ nestedAndMaxBadEvent P A score d x) :
    |centeredSetCount P sample (score ⁻¹' Set.Ioi t)| <
      d * Real.sqrt ((n : ℝ) * massCap + Real.sqrt n * x) + Real.sqrt n * x := by
  have hnested : sample ∉ patternwiseEvent A (patternKSEvent P A score d) := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hproc :
      |EmpiricalProcess.empiricalProcess P n sample (indicatorReal A)| ≤ x := by
    exact le_of_not_gt fun hbad ↦ hgood (Or.inr hbad)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hmax : |centeredSetCount P sample A| ≤ Real.sqrt n * x := by
    rw [centeredSetCount_eq_sqrt_mul_empiricalProcess P hn sample A hA, abs_mul,
      abs_of_nonneg hsqrt0]
    exact mul_le_mul_of_nonneg_left hproc hsqrt0
  have hbasic := abs_centeredSetCount_lt_of_nested_and_max_good
    P A hA hA0 J hk sample hsample score hscore t d (Real.sqrt n * x)
    hsubset hnested hmax (mul_nonneg hsqrt0 hx.le)
  have hcountA := sampleSetCountReal_eq_card_of_mem_membershipPattern J sample hsample
  have hcenterA : centeredSetCount P sample A =
      (J.card : ℝ) - (n : ℝ) * P.real A := by
    rw [centeredSetCount, hcountA]
  have hupper : centeredSetCount P sample A ≤ Real.sqrt n * x :=
    le_of_abs_le hmax
  have hkcap : (J.card : ℝ) ≤ (n : ℝ) * massCap + Real.sqrt n * x := by
    rw [hcenterA] at hupper
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmassmul := mul_le_mul_of_nonneg_left hmass hn0
    linarith
  have hsqrtle : Real.sqrt (J.card : ℝ) ≤
      Real.sqrt ((n : ℝ) * massCap + Real.sqrt n * x) := Real.sqrt_le_sqrt hkcap
  calc
    |centeredSetCount P sample (score ⁻¹' Set.Ioi t)|
        < d * Real.sqrt J.card + Real.sqrt n * x := hbasic
    _ ≤ d * Real.sqrt ((n : ℝ) * massCap + Real.sqrt n * x) + Real.sqrt n * x :=
      add_le_add (mul_le_mul_of_nonneg_left hsqrtle hd.le) le_rfl

/-! ### Source and target endpoint specializations -/

/-- The rank-strip law is the product of its scaled-rank and unit-mark marginals. -/
theorem rankStripLaw_eq_rankCoordinateLaw_prod (width : ℝ) :
    (rankStripLaw width : Measure (ℝ × UnitMark)) =
      (rankCoordinateLaw width : Measure ℝ).prod (unitUniform : Measure UnitMark) := by
  change Measure.map (rankStripMap width)
      ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) =
    (Measure.map (rankCoordinateMap width) (unitUniform : Measure UnitMark)).prod
      (unitUniform : Measure UnitMark)
  calc
    Measure.map (rankStripMap width)
        ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) =
      Measure.map (Prod.map (rankCoordinateMap width) id)
        ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) := by
          congr 1
    _ = (Measure.map (rankCoordinateMap width) (unitUniform : Measure UnitMark)).prod
        (Measure.map id (unitUniform : Measure UnitMark)) :=
      (Measure.map_prod_map _ _ (measurable_rankCoordinateMap width) measurable_id).symm
    _ = (Measure.map (rankCoordinateMap width) (unitUniform : Measure UnitMark)).prod
        (unitUniform : Measure UnitMark) := by rw [Measure.map_id]

/-- Rectangle masses under the rank-strip law factor into the two marginal masses. -/
theorem rankStripLaw_real_prod (width : ℝ) (s : Set ℝ) (t : Set UnitMark) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real (s ×ˢ t) =
      (rankCoordinateLaw width : Measure ℝ).real s *
        (unitUniform : Measure UnitMark).real t := by
  rw [rankStripLaw_eq_rankCoordinateLaw_prod, measureReal_prod_prod]

private noncomputable def endpointHalfMark : UnitMark :=
  ⟨1 / 2, by norm_num, by norm_num⟩

private theorem unitUniform_real_Iic_half :
    (unitUniform : Measure UnitMark).real (Set.Iic endpointHalfMark) = 1 / 2 := by
  change ENNReal.toReal (volume (Set.Iic endpointHalfMark)) = 1 / 2
  rw [unitInterval.volume_Iic, ENNReal.toReal_ofReal]
  · rfl
  · norm_num [endpointHalfMark]

private theorem unitUniform_real_Ici_half :
    (unitUniform : Measure UnitMark).real (Set.Ici endpointHalfMark) = 1 / 2 := by
  change ENNReal.toReal (volume (Set.Ici endpointHalfMark)) = 1 / 2
  rw [unitInterval.volume_Ici, ENNReal.toReal_ofReal]
  · norm_num [endpointHalfMark]
  · norm_num [endpointHalfMark]

private theorem measure_ne_zero_of_rectangle_real_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {r s : Set α} (hrs : r ⊆ s) (hr : 0 < μ.real r) : μ s ≠ 0 := by
  apply (measureReal_ne_zero_iff (μ := μ) (s := s)).mp
  exact ne_of_gt (hr.trans_le (measureReal_mono hrs))

/-- The largest source endpoint complement has positive rank-strip mass. -/
theorem rankStripLaw_sourceEndpointComplement_max_ne_zero
    {width buffer : ℝ} (hwidth : 0 < width) (hbuffer : 0 < buffer)
    (hfit : 9 * buffer / 8 ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8)) ≠ 0 := by
  let r : Set (ℝ × UnitMark) := Set.Ioi (width - buffer / 2) ×ˢ Set.univ
  have ha0 : 0 ≤ width - buffer / 2 := by nlinarith
  have haw : width - buffer / 2 ≤ width := by linarith
  have hrpos : 0 < (rankStripLaw width : Measure (ℝ × UnitMark)).real r := by
    rw [rankStripLaw_real_prod,
      rankCoordinateLaw_real_Ioi_of_mem width (width - buffer / 2) hwidth ha0 haw,
      probReal_univ, mul_one]
    rw [sub_pos, div_lt_one hwidth]
    linarith
  apply measure_ne_zero_of_rectangle_real_pos (r := r) (s :=
    sourceEndpointComplement width buffer (buffer / 8)) _ hrpos
  rintro z ⟨hz, -⟩
  change width - buffer / 2 < z.1 at hz
  have hu0 : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
  have hcoef : 0 ≤ buffer / 8 := by positivity
  change width - buffer < z.1 + buffer / 8 * (1 - (z.2 : ℝ))
  have hadd : 0 ≤ buffer / 8 * (1 - (z.2 : ℝ)) := mul_nonneg hcoef hu0
  linarith

/-- The complement of the largest source endpoint complement also has positive rank-strip mass. -/
theorem rankStripLaw_sourceEndpointComplement_max_compl_ne_zero
    {width buffer : ℝ} (hwidth : 0 < width) (hbuffer : 0 < buffer)
    (hfit : 9 * buffer / 8 ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8))ᶜ ≠ 0 := by
  let a := width - 17 * buffer / 16
  let r : Set (ℝ × UnitMark) := Set.Iic a ×ˢ Set.Ici endpointHalfMark
  have ha0 : 0 ≤ a := by dsimp [a]; nlinarith
  have haw : a ≤ width := by dsimp [a]; linarith
  have hapos : 0 < a := by dsimp [a]; nlinarith
  have hrpos : 0 < (rankStripLaw width : Measure (ℝ × UnitMark)).real r := by
    rw [rankStripLaw_real_prod,
      rankCoordinateLaw_real_Iic_of_mem width a hwidth ha0 haw,
      unitUniform_real_Ici_half]
    exact mul_pos (div_pos hapos hwidth) (by norm_num)
  apply measure_ne_zero_of_rectangle_real_pos (r := r) (s :=
    (sourceEndpointComplement width buffer (buffer / 8))ᶜ) _ hrpos
  rintro z ⟨hz, hu⟩
  change z.1 ≤ a at hz
  change ¬width - buffer < z.1 + buffer / 8 * (1 - (z.2 : ℝ))
  rw [not_lt]
  change (1 / 2 : ℝ) ≤ (z.2 : ℝ) at hu
  have huBound : 1 - (z.2 : ℝ) ≤ 1 / 2 := by linarith
  have hcoef : 0 ≤ buffer / 8 := by positivity
  have hmul : buffer / 8 * (1 - (z.2 : ℝ)) ≤ buffer / 16 := by
    have := mul_le_mul_of_nonneg_left huBound hcoef
    linarith
  dsimp [a] at hz
  linarith

/-- The largest target endpoint complement has positive rank-strip mass. -/
theorem rankStripLaw_targetEndpointComplement_max_ne_zero
    {width buffer : ℝ} (hwidth : 0 < width) (hbuffer : 0 < buffer)
    (hfit : 5 * buffer / 4 ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8)) ≠ 0 := by
  let r : Set (ℝ × UnitMark) := Set.Ioi (width - buffer / 2) ×ˢ Set.univ
  have ha0 : 0 ≤ width - buffer / 2 := by nlinarith
  have haw : width - buffer / 2 ≤ width := by linarith
  have hrpos : 0 < (rankStripLaw width : Measure (ℝ × UnitMark)).real r := by
    rw [rankStripLaw_real_prod,
      rankCoordinateLaw_real_Ioi_of_mem width (width - buffer / 2) hwidth ha0 haw,
      probReal_univ, mul_one]
    rw [sub_pos, div_lt_one hwidth]
    linarith
  apply measure_ne_zero_of_rectangle_real_pos (r := r) (s :=
    targetEndpointComplement width buffer (-buffer / 8)) _ hrpos
  rintro z ⟨hz, -⟩
  change width - buffer / 2 < z.1 at hz
  have hu0 : 0 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  have hcoef : 0 ≤ buffer / 8 := by positivity
  change width - buffer < z.1 - (-buffer / 8) * (1 + (z.2 : ℝ))
  have hadd : 0 ≤ buffer / 8 * (1 + (z.2 : ℝ)) := mul_nonneg hcoef hu0
  linarith

/-- The complement of the largest target endpoint complement has positive rank-strip mass. -/
theorem rankStripLaw_targetEndpointComplement_max_compl_ne_zero
    {width buffer : ℝ} (hwidth : 0 < width) (hbuffer : 0 < buffer)
    (hfit : 5 * buffer / 4 ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8))ᶜ ≠ 0 := by
  let a := width - 19 * buffer / 16
  let r : Set (ℝ × UnitMark) := Set.Iic a ×ˢ Set.Iic endpointHalfMark
  have ha0 : 0 ≤ a := by dsimp [a]; nlinarith
  have haw : a ≤ width := by dsimp [a]; linarith
  have hapos : 0 < a := by dsimp [a]; nlinarith
  have hrpos : 0 < (rankStripLaw width : Measure (ℝ × UnitMark)).real r := by
    rw [rankStripLaw_real_prod,
      rankCoordinateLaw_real_Iic_of_mem width a hwidth ha0 haw,
      unitUniform_real_Iic_half]
    exact mul_pos (div_pos hapos hwidth) (by norm_num)
  apply measure_ne_zero_of_rectangle_real_pos (r := r) (s :=
    (targetEndpointComplement width buffer (-buffer / 8))ᶜ) _ hrpos
  rintro z ⟨hz, hu⟩
  change z.1 ≤ a at hz
  change ¬width - buffer < z.1 - (-buffer / 8) * (1 + (z.2 : ℝ))
  rw [not_lt]
  change (z.2 : ℝ) ≤ 1 / 2 at hu
  have huBound : 1 + (z.2 : ℝ) ≤ 3 / 2 := by linarith
  have hcoef : 0 ≤ buffer / 8 := by positivity
  have hmul : buffer / 8 * (1 + (z.2 : ℝ)) ≤ 3 * buffer / 16 := by
    have := mul_le_mul_of_nonneg_left huBound hcoef
    nlinarith
  dsimp [a] at hz
  linarith

/-- Source complements become strict upper half-lines after negating the source score. -/
theorem sourceEndpointComplement_eq_negScore_preimage {width buffer p : ℝ}
    (hbuffer : 0 < buffer) (hp : |p| ≤ buffer / 8) :
    sourceEndpointComplement width buffer p =
      (fun z ↦ -sourceEndpointScore buffer (width - buffer) z) ⁻¹' Set.Ioi (-p) := by
  rw [sourceEndpointComplement_eq_score_preimage hbuffer hp]
  ext z
  simp

/-- The complement defect is the generic centered count of the source endpoint complement. -/
theorem sourceComplementDefect_eq_centeredSetCount
    (P : Measure (ℝ × UnitMark)) {n : ℕ} (sample : Fin n → ℝ × UnitMark)
    (width buffer p : ℝ) :
    sourceComplementDefect P sample p (width - buffer) =
      centeredSetCount P sample (sourceEndpointComplement width buffer p) := by
  rw [sourceComplementDefect, centeredErrorSum_eq_centeredSetCount,
    ← sourceCutComplementSet_eq_errorSet]
  rfl

/-- Target analogue of `sourceComplementDefect_eq_centeredSetCount`. -/
theorem targetComplementDefect_eq_centeredSetCount
    (P : Measure (ℝ × UnitMark)) {n : ℕ} (sample : Fin n → ℝ × UnitMark)
    (width buffer p : ℝ) :
    targetComplementDefect P sample p (width - buffer) =
      centeredSetCount P sample (targetEndpointComplement width buffer p) := by
  rw [targetComplementDefect, centeredErrorSum_eq_centeredSetCount,
    ← targetCutComplementSet_eq_errorSet]
  rfl

/-- Source endpoint finite-sample probability bound, combining conditional nested-CDF control and
Bernstein control of the largest complement. -/
theorem measure_sourceEndpointBadEvent_le
    {n : ℕ} {width buffer d x : ℝ}
    (hA0 : (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8)) ≠ 0)
    (hAc0 : (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8))ᶜ ≠ 0)
    (hd : 0 < d) (hx : 0 < x) (hn : 1 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ (rankStripLaw width : Measure (ℝ × UnitMark)))
        (nestedAndMaxBadEvent
          (rankStripLaw width : Measure (ℝ × UnitMark))
          (sourceEndpointComplement width buffer (buffer / 8))
          (fun z ↦ -sourceEndpointScore buffer (width - buffer) z) d x) ≤
      ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) /
            (4 * ((rankStripLaw width : Measure (ℝ × UnitMark)).real
              (sourceEndpointComplement width buffer (buffer / 8)) +
                x / Real.sqrt n)))) := by
  exact measure_nestedAndMaxBadEvent_le
    (rankStripLaw width : Measure (ℝ × UnitMark))
    (sourceEndpointComplement width buffer (buffer / 8))
    (measurableSet_sourceCutComplementSet _ _)
    hA0 hAc0 (fun z ↦ -sourceEndpointScore buffer (width - buffer) z)
    (measurable_sourceEndpointScore buffer (width - buffer)).neg hd hx hn

/-- Target endpoint analogue of `measure_sourceEndpointBadEvent_le`. -/
theorem measure_targetEndpointBadEvent_le
    {n : ℕ} {width buffer d x : ℝ}
    (hA0 : (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8)) ≠ 0)
    (hAc0 : (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8))ᶜ ≠ 0)
    (hd : 0 < d) (hx : 0 < x) (hn : 1 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ (rankStripLaw width : Measure (ℝ × UnitMark)))
        (nestedAndMaxBadEvent
          (rankStripLaw width : Measure (ℝ × UnitMark))
          (targetEndpointComplement width buffer (-buffer / 8))
          (targetEndpointScore (width - buffer)) d x) ≤
      ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) /
            (4 * ((rankStripLaw width : Measure (ℝ × UnitMark)).real
              (targetEndpointComplement width buffer (-buffer / 8)) +
                x / Real.sqrt n)))) := by
  exact measure_nestedAndMaxBadEvent_le
    (rankStripLaw width : Measure (ℝ × UnitMark))
    (targetEndpointComplement width buffer (-buffer / 8))
    (measurableSet_targetCutComplementSet _ _)
    hA0 hAc0 (targetEndpointScore (width - buffer))
    (measurable_targetEndpointScore (width - buffer)) hd hx hn

/-- Source endpoint probability bound with all conditional nondegeneracy discharged by the strip
geometry. -/
theorem measure_sourceEndpointBadEvent_le_of_geometry
    {n : ℕ} {width buffer d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 9 * buffer / 8 ≤ width)
    (hd : 0 < d) (hx : 0 < x) (hn : 1 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ (rankStripLaw width : Measure (ℝ × UnitMark)))
        (nestedAndMaxBadEvent
          (rankStripLaw width : Measure (ℝ × UnitMark))
          (sourceEndpointComplement width buffer (buffer / 8))
          (fun z ↦ -sourceEndpointScore buffer (width - buffer) z) d x) ≤
      ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) /
            (4 * ((rankStripLaw width : Measure (ℝ × UnitMark)).real
              (sourceEndpointComplement width buffer (buffer / 8)) +
                x / Real.sqrt n)))) := by
  exact measure_sourceEndpointBadEvent_le
    (rankStripLaw_sourceEndpointComplement_max_ne_zero hwidth hbuffer hfit)
    (rankStripLaw_sourceEndpointComplement_max_compl_ne_zero hwidth hbuffer hfit)
    hd hx hn

/-- Target endpoint probability bound with all conditional nondegeneracy discharged by the strip
geometry. -/
theorem measure_targetEndpointBadEvent_le_of_geometry
    {n : ℕ} {width buffer d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 5 * buffer / 4 ≤ width)
    (hd : 0 < d) (hx : 0 < x) (hn : 1 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ (rankStripLaw width : Measure (ℝ × UnitMark)))
        (nestedAndMaxBadEvent
          (rankStripLaw width : Measure (ℝ × UnitMark))
          (targetEndpointComplement width buffer (-buffer / 8))
          (targetEndpointScore (width - buffer)) d x) ≤
      ENNReal.ofReal (4 / d) +
        ENNReal.ofReal
          (2 * Real.exp (-(x ^ 2) /
            (4 * ((rankStripLaw width : Measure (ℝ × UnitMark)).real
              (targetEndpointComplement width buffer (-buffer / 8)) +
                x / Real.sqrt n)))) := by
  exact measure_targetEndpointBadEvent_le
    (rankStripLaw_targetEndpointComplement_max_ne_zero hwidth hbuffer hfit)
    (rankStripLaw_targetEndpointComplement_max_compl_ne_zero hwidth hbuffer hfit)
    hd hx hn

/-- Source endpoint cut defect at the natural finite-sample scale. -/
theorem abs_sourceEndpointCutDefect_lt_naturalScale
    {n : ℕ} {width buffer p d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 9 * buffer / 8 ≤ width)
    (hp : |p| ≤ buffer / 8) (hn : 0 < n) (hd : 0 < d) (hx : 0 < x)
    (J : Finset (Fin n)) (hJ : 0 < J.card)
    (sample : Fin n → ℝ × UnitMark)
    (hsample : sample ∈ membershipPattern
      (sourceEndpointComplement width buffer (buffer / 8)) J)
    (hgood : sample ∉ nestedAndMaxBadEvent
      (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8))
      (fun z ↦ -sourceEndpointScore buffer (width - buffer) z) d x) :
    |sourceCutDefect (rankStripLaw width : Measure (ℝ × UnitMark))
        sample p (width - buffer)| <
      d * Real.sqrt
          ((n : ℝ) * (9 * buffer / (8 * width)) + Real.sqrt n * x) +
        Real.sqrt n * x := by
  have hC := sourceEndpointComplement_eq_negScore_preimage
    (width := width) hbuffer hp
  have hsubset :
      (fun z ↦ -sourceEndpointScore buffer (width - buffer) z) ⁻¹' Set.Ioi (-p) ⊆
        sourceEndpointComplement width buffer (buffer / 8) := by
    rw [← hC]
    exact sourceEndpointComplement_subset_max hp
  have hmass :
      (rankStripLaw width : Measure (ℝ × UnitMark)).real
          (sourceEndpointComplement width buffer (buffer / 8)) ≤
        9 * buffer / (8 * width) := by
    exact rankStripLaw_real_sourceEndpointComplement_le hwidth hbuffer.le hfit
      (by simp [abs_of_nonneg (div_nonneg hbuffer.le (by norm_num : (0 : ℝ) ≤ 8))])
  have hA0 := rankStripLaw_sourceEndpointComplement_max_ne_zero hwidth hbuffer hfit
  have hbase := abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent
    (rankStripLaw width : Measure (ℝ × UnitMark))
    (sourceEndpointComplement width buffer (buffer / 8))
    (measurableSet_sourceCutComplementSet _ _) hA0 J hJ sample hsample
    (fun z ↦ -sourceEndpointScore buffer (width - buffer) z)
    (measurable_sourceEndpointScore buffer (width - buffer)).neg
    (-p) d x (9 * buffer / (8 * width)) hn hd hx hmass hsubset hgood
  rw [← hC, ← sourceComplementDefect_eq_centeredSetCount] at hbase
  rw [abs_sourceCutDefect_eq_abs_complementDefect]
  exact hbase

/-- Target endpoint cut defect at the natural finite-sample scale. -/
theorem abs_targetEndpointCutDefect_lt_naturalScale
    {n : ℕ} {width buffer p d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 5 * buffer / 4 ≤ width)
    (hp : |p| ≤ buffer / 8) (hn : 0 < n) (hd : 0 < d) (hx : 0 < x)
    (J : Finset (Fin n)) (hJ : 0 < J.card)
    (sample : Fin n → ℝ × UnitMark)
    (hsample : sample ∈ membershipPattern
      (targetEndpointComplement width buffer (-buffer / 8)) J)
    (hgood : sample ∉ nestedAndMaxBadEvent
      (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8))
      (targetEndpointScore (width - buffer)) d x) :
    |targetCutDefect (rankStripLaw width : Measure (ℝ × UnitMark))
        sample p (width - buffer)| <
      d * Real.sqrt
          ((n : ℝ) * (5 * buffer / (4 * width)) + Real.sqrt n * x) +
        Real.sqrt n * x := by
  have hC := targetEndpointComplement_eq_score_preimage width buffer p
  have hsubset :
      targetEndpointScore (width - buffer) ⁻¹' Set.Ioi p ⊆
        targetEndpointComplement width buffer (-buffer / 8) := by
    rw [← hC]
    exact targetEndpointComplement_subset_max hp
  have hmass :
      (rankStripLaw width : Measure (ℝ × UnitMark)).real
          (targetEndpointComplement width buffer (-buffer / 8)) ≤
        5 * buffer / (4 * width) := by
    exact rankStripLaw_real_targetEndpointComplement_le hwidth hbuffer.le hfit
      (by
        have hnonpos : -buffer / 8 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hbuffer.le) (by norm_num)
        rw [abs_of_nonpos hnonpos]
        linarith)
  have hA0 := rankStripLaw_targetEndpointComplement_max_ne_zero hwidth hbuffer hfit
  have hbase := abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent
    (rankStripLaw width : Measure (ℝ × UnitMark))
    (targetEndpointComplement width buffer (-buffer / 8))
    (measurableSet_targetCutComplementSet _ _) hA0 J hJ sample hsample
    (targetEndpointScore (width - buffer))
    (measurable_targetEndpointScore (width - buffer))
    p d x (5 * buffer / (4 * width)) hn hd hx hmass hsubset hgood
  rw [← hC, ← targetComplementDefect_eq_centeredSetCount] at hbase
  rw [abs_targetCutDefect_eq_abs_complementDefect]
  exact hbase

end OTSelector.RelativeVC
