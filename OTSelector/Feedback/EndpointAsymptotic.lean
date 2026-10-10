import OTSelector.Feedback.EndpointTail
import OTSelector.Probability.TriangularArray

/-!
# Endpoint regularity on the square-root buffer scale

This module packages the finite nested-endpoint estimate for strip width `n` and buffer
`Bₙ = amplitude * √n`.  The supremum variables are defined by `sSup`; their tail events are
controlled through the explicit source and target bad-event envelopes from `EndpointTail`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace OTSelector.RelativeVC

open OTSelector.CountConditioning
open OTSelector.Probability

/-- Buffer width `Bₙ = amplitude * √n`. -/
noncomputable def endpointBuffer (amplitude : ℝ) (n : ℕ) : ℝ :=
  amplitude * Real.sqrt n

/-- The endpoint fluctuation scale `√Bₙ`. -/
noncomputable def endpointScale (amplitude : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (endpointBuffer amplitude n)

/-- Source endpoint defect values over the prescribed shear window. -/
noncomputable def sourceEndpointValueSet (amplitude : ℝ) (n : ℕ)
    (sample : Fin n → ℝ × UnitMark) : Set ℝ :=
  {y | ∃ p, |p| ≤ endpointBuffer amplitude n / 8 ∧
    y = |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample p
      ((n : ℝ) - endpointBuffer amplitude n)|}

/-- Source endpoint supremum. -/
noncomputable def sourceEndpointSup (amplitude : ℝ) (n : ℕ)
    (sample : Fin n → ℝ × UnitMark) : ℝ :=
  sSup (sourceEndpointValueSet amplitude n sample)

/-- Target endpoint defect values over the prescribed shear window. -/
noncomputable def targetEndpointValueSet (amplitude : ℝ) (n : ℕ)
    (sample : Fin n → ℝ × UnitMark) : Set ℝ :=
  {y | ∃ p, |p| ≤ endpointBuffer amplitude n / 8 ∧
    y = |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample p
      ((n : ℝ) - endpointBuffer amplitude n)|}

/-- Target endpoint supremum. -/
noncomputable def targetEndpointSup (amplitude : ℝ) (n : ℕ)
    (sample : Fin n → ℝ × UnitMark) : ℝ :=
  sSup (targetEndpointValueSet amplitude n sample)

/-- Joint source/target endpoint envelope. -/
noncomputable def jointEndpointSup (amplitude : ℝ) (n : ℕ)
    (sample : Fin n → ℝ × UnitMark) : ℝ :=
  max (sourceEndpointSup amplitude n sample) (targetEndpointSup amplitude n sample)

/-- The product law in row `n` of the endpoint triangular array. -/
noncomputable def endpointRowLaw (n : ℕ) : Measure (Fin n → ℝ × UnitMark) :=
  Measure.pi (fun _ : Fin n ↦ (rankStripLaw n : Measure (ℝ × UnitMark)))

/-- Bernstein tuning at level `q` on the square-root buffer regime. -/
noncomputable def endpointTuning (amplitude q : ℝ) (n : ℕ) : ℝ :=
  q * Real.sqrt (endpointBuffer amplitude n / n)

/-- Source bad event for row `n`. -/
noncomputable def sourceEndpointBadEvent (amplitude q : ℝ) (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  nestedAndMaxBadEvent
    (rankStripLaw n : Measure (ℝ × UnitMark))
    (sourceEndpointComplement n (endpointBuffer amplitude n) (endpointBuffer amplitude n / 8))
    (fun z ↦ -sourceEndpointScore (endpointBuffer amplitude n)
      ((n : ℝ) - endpointBuffer amplitude n) z)
    q (endpointTuning amplitude q n)

/-- Target bad event for row `n`. -/
noncomputable def targetEndpointBadEvent (amplitude q : ℝ) (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  nestedAndMaxBadEvent
    (rankStripLaw n : Measure (ℝ × UnitMark))
    (targetEndpointComplement n (endpointBuffer amplitude n) (-endpointBuffer amplitude n / 8))
    (targetEndpointScore ((n : ℝ) - endpointBuffer amplitude n))
    q (endpointTuning amplitude q n)

/-- Joint source/target bad event. -/
noncomputable def jointEndpointBadEvent (amplitude q : ℝ) (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  sourceEndpointBadEvent amplitude q n ∪ targetEndpointBadEvent amplitude q n

/-- For positive amplitude, all endpoint geometry conditions and `Bₙ ≥ 1` hold eventually. -/
theorem eventually_endpointBuffer_geometry {amplitude : ℝ} (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < endpointBuffer amplitude n ∧
        9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ) ∧
        5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ) ∧
        1 ≤ endpointBuffer amplitude n := by
  let M : ℝ := max 1 (max (5 * amplitude / 4) (1 / amplitude))
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [(hsqrt.eventually (eventually_ge_atTop M))] with n hnM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMcoef : 5 * amplitude / 4 ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMinv : 1 / amplitude ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := hM1.trans hnM
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hsqrt1
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = n :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hcoef : 5 * amplitude / 4 ≤ Real.sqrt (n : ℝ) := hMcoef.trans hnM
  have hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hsqrt0
    rw [hsquare] at hmul
    dsimp [endpointBuffer]
    nlinarith [hmul]
  have hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ) := by
    have hcoeff : 9 * amplitude / 8 ≤ 5 * amplitude / 4 := by nlinarith
    have := (mul_le_mul_of_nonneg_right (hcoeff.trans hcoef) hsqrt0)
    rw [hsquare] at this
    dsimp [endpointBuffer]
    nlinarith [this]
  have hbuffer : 0 < endpointBuffer amplitude n := by
    exact mul_pos hamp (Real.sqrt_pos.2 (Nat.cast_pos.2 hnpos))
  have hbufferOne : 1 ≤ endpointBuffer amplitude n := by
    have hinv : 1 / amplitude ≤ Real.sqrt (n : ℝ) := hMinv.trans hnM
    have := mul_le_mul_of_nonneg_left hinv hamp.le
    field_simp at this
    simpa [endpointBuffer, mul_comm] using this
  exact ⟨hnpos, hbuffer, hfitSource, hfitTarget, hbufferOne⟩

/-- The natural-scale nested count estimate also covers the empty selecting pattern.  This closes
the only branch not present in the positive-cardinality finite-sample statement. -/
theorem abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent_allPatterns
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    (J : Finset (Fin n)) (sample : Fin n → Ω)
    (hsample : sample ∈ membershipPattern A J)
    (score : Ω → ℝ) (hscore : Measurable score) (t d x massCap : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hx : 0 < x) (hmassCap : 0 < massCap)
    (hmass : P.real A ≤ massCap)
    (hsubset : score ⁻¹' Set.Ioi t ⊆ A)
    (hgood : sample ∉ nestedAndMaxBadEvent P A score d x) :
    |centeredSetCount P sample (score ⁻¹' Set.Ioi t)| <
      d * Real.sqrt ((n : ℝ) * massCap + Real.sqrt n * x) + Real.sqrt n * x := by
  by_cases hk : 0 < J.card
  · exact abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent
      P A hA hA0 J hk sample hsample score hscore t d x massCap hn hd hx hmass hsubset hgood
  · have hk0 : J.card = 0 := Nat.eq_zero_of_not_pos hk
    have hproc :
        |EmpiricalProcess.empiricalProcess P n sample (indicatorReal A)| ≤ x := by
      exact le_of_not_gt fun hbad ↦ hgood (Or.inr hbad)
    have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hmax : |centeredSetCount P sample A| ≤ Real.sqrt n * x := by
      rw [centeredSetCount_eq_sqrt_mul_empiricalProcess P hn sample A hA, abs_mul,
        abs_of_nonneg hsqrt0]
      exact mul_le_mul_of_nonneg_left hproc hsqrt0
    have hdecomp := centeredSetCount_eq_selectedResidual_add (k := 0)
      P A (score ⁻¹' Set.Ioi t) hA hsubset J hk0 sample hsample
    simp [selectedSetCount] at hdecomp
    have hq0 : 0 ≤ (P[|A]).real (score ⁻¹' Set.Ioi t) := measureReal_nonneg
    have hq1 : (P[|A]).real (score ⁻¹' Set.Ioi t) ≤ 1 := measureReal_le_one
    have hscaled :
        |(P[|A]).real (score ⁻¹' Set.Ioi t) * centeredSetCount P sample A| ≤
          Real.sqrt n * x := by
      rw [abs_mul, abs_of_nonneg hq0]
      calc
        (P[|A]).real (score ⁻¹' Set.Ioi t) * |centeredSetCount P sample A| ≤
            (P[|A]).real (score ⁻¹' Set.Ioi t) * (Real.sqrt n * x) :=
          mul_le_mul_of_nonneg_left hmax hq0
        _ ≤ 1 * (Real.sqrt n * x) :=
          mul_le_mul_of_nonneg_right hq1 (mul_nonneg hsqrt0 hx.le)
        _ = Real.sqrt n * x := one_mul _
    have hinner : 0 < (n : ℝ) * massCap + Real.sqrt n * x := by
      exact add_pos (mul_pos (Nat.cast_pos.2 hn) hmassCap)
        (mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)) hx)
    rw [hdecomp]
    exact hscaled.trans_lt (by
      have : 0 < d * Real.sqrt ((n : ℝ) * massCap + Real.sqrt n * x) :=
        mul_pos hd (Real.sqrt_pos.2 hinner)
      linarith)

/-- Source endpoint natural-scale estimate for every full membership pattern, including the empty
pattern. -/
theorem abs_sourceEndpointCutDefect_lt_naturalScale_allPatterns
    {n : ℕ} {width buffer p d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 9 * buffer / 8 ≤ width)
    (hp : |p| ≤ buffer / 8) (hn : 0 < n) (hd : 0 < d) (hx : 0 < x)
    (J : Finset (Fin n)) (sample : Fin n → ℝ × UnitMark)
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
  have hmassCap : 0 < 9 * buffer / (8 * width) := by positivity
  have hA0 := rankStripLaw_sourceEndpointComplement_max_ne_zero hwidth hbuffer hfit
  have hbase :=
    abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent_allPatterns
      (rankStripLaw width : Measure (ℝ × UnitMark))
      (sourceEndpointComplement width buffer (buffer / 8))
      (measurableSet_sourceCutComplementSet _ _) hA0 J sample hsample
      (fun z ↦ -sourceEndpointScore buffer (width - buffer) z)
      (measurable_sourceEndpointScore buffer (width - buffer)).neg
      (-p) d x (9 * buffer / (8 * width)) hn hd hx hmassCap hmass hsubset hgood
  rw [← hC, ← sourceComplementDefect_eq_centeredSetCount] at hbase
  rw [abs_sourceCutDefect_eq_abs_complementDefect]
  exact hbase

/-- Target endpoint natural-scale estimate for every full membership pattern. -/
theorem abs_targetEndpointCutDefect_lt_naturalScale_allPatterns
    {n : ℕ} {width buffer p d x : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 < buffer) (hfit : 5 * buffer / 4 ≤ width)
    (hp : |p| ≤ buffer / 8) (hn : 0 < n) (hd : 0 < d) (hx : 0 < x)
    (J : Finset (Fin n)) (sample : Fin n → ℝ × UnitMark)
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
  have hmassCap : 0 < 5 * buffer / (4 * width) := by positivity
  have hA0 := rankStripLaw_targetEndpointComplement_max_ne_zero hwidth hbuffer hfit
  have hbase :=
    abs_centeredSetCount_lt_naturalScale_of_not_nestedAndMaxBadEvent_allPatterns
      (rankStripLaw width : Measure (ℝ × UnitMark))
      (targetEndpointComplement width buffer (-buffer / 8))
      (measurableSet_targetCutComplementSet _ _) hA0 J sample hsample
      (targetEndpointScore (width - buffer))
      (measurable_targetEndpointScore (width - buffer))
      p d x (5 * buffer / (4 * width)) hn hd hx hmassCap hmass hsubset hgood
  rw [← hC, ← targetComplementDefect_eq_centeredSetCount] at hbase
  rw [abs_targetCutDefect_eq_abs_complementDefect]
  exact hbase

/-- Indices selected by a set in a concrete sample. -/
noncomputable def sampleMembershipIndices {Ω : Type*} {n : ℕ}
    (A : Set Ω) (sample : Fin n → Ω) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ sample i ∈ A

/-- The concrete sample belongs to its full membership pattern. -/
theorem mem_membershipPattern_sampleMembershipIndices
    {Ω : Type*} {n : ℕ} (A : Set Ω) (sample : Fin n → Ω) :
    sample ∈ membershipPattern A (sampleMembershipIndices A sample) := by
  classical
  rw [mem_membershipPattern_iff]
  intro i
  simp [sampleMembershipIndices]

/-- Coefficient of the common source/target endpoint envelope at tail parameter `q`. -/
noncomputable def endpointEnvelopeCoefficient (q : ℝ) : ℝ :=
  q * (Real.sqrt (5 / 4 + q) + 1)

/-- The chosen Bernstein threshold, multiplied by `√n`, is exactly `q √Bₙ`. -/
theorem sqrt_mul_endpointTuning {amplitude q : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 ≤ endpointBuffer amplitude n) :
    Real.sqrt n * endpointTuning amplitude q n =
      q * Real.sqrt (endpointBuffer amplitude n) := by
  rw [endpointTuning, Real.sqrt_div hbuffer]
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  field_simp

/-- Algebraic envelope shared by the source coefficient `9/8` and target coefficient `5/4`. -/
theorem endpointNaturalEnvelope_le {B c q : ℝ}
    (hB : 1 ≤ B) (hc : c ≤ 5 / 4) (hq : 1 ≤ q) :
    q * Real.sqrt (c * B + q * Real.sqrt B) + q * Real.sqrt B ≤
      endpointEnvelopeCoefficient q * Real.sqrt B := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hsqrt0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
  have hsqrt_le : Real.sqrt B ≤ B := by
    nlinarith [sq_nonneg (Real.sqrt B - 1)]
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hcoef0 : 0 ≤ 5 / 4 + q := by positivity
  have hinner : c * B + q * Real.sqrt B ≤ (5 / 4 + q) * B := by
    have hcB := mul_le_mul_of_nonneg_right hc hB0
    have hqB := mul_le_mul_of_nonneg_left hsqrt_le hq0
    nlinarith
  have hsqrtInner :
      Real.sqrt (c * B + q * Real.sqrt B) ≤
        Real.sqrt ((5 / 4 + q) * B) := Real.sqrt_le_sqrt hinner
  have hsqrtMul : Real.sqrt ((5 / 4 + q) * B) =
      Real.sqrt (5 / 4 + q) * Real.sqrt B := by
    rw [Real.sqrt_mul hcoef0]
  rw [hsqrtMul] at hsqrtInner
  dsimp [endpointEnvelopeCoefficient]
  nlinarith

/-- Pointwise source endpoint envelope outside its row bad event. -/
theorem sourceEndpointValue_lt_envelope
    {amplitude q : ℝ} {n : ℕ} {sample : Fin n → ℝ × UnitMark} {p : ℝ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hp : |p| ≤ endpointBuffer amplitude n / 8)
    (hgood : sample ∉ sourceEndpointBadEvent amplitude q n) :
    |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample p
        ((n : ℝ) - endpointBuffer amplitude n)| <
      endpointEnvelopeCoefficient q * endpointScale amplitude n := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 < endpointTuning amplitude q n := by
    exact mul_pos hq0 (Real.sqrt_pos.2 (div_pos hbuffer (Nat.cast_pos.2 hn)))
  let J := sampleMembershipIndices
    (sourceEndpointComplement n (endpointBuffer amplitude n) (endpointBuffer amplitude n / 8))
    sample
  have hsample : sample ∈ membershipPattern
      (sourceEndpointComplement n (endpointBuffer amplitude n)
        (endpointBuffer amplitude n / 8)) J :=
    mem_membershipPattern_sampleMembershipIndices _ _
  have hnat := abs_sourceEndpointCutDefect_lt_naturalScale_allPatterns
    (width := (n : ℝ)) (buffer := endpointBuffer amplitude n)
    (p := p) (d := q) (x := endpointTuning amplitude q n)
    (Nat.cast_pos.2 hn) hbuffer hfit hp hn hq0 hx J sample hsample (by
      simpa [sourceEndpointBadEvent] using hgood)
  have hscale : Real.sqrt n * endpointTuning amplitude q n =
      q * Real.sqrt (endpointBuffer amplitude n) :=
    sqrt_mul_endpointTuning hn hbuffer.le
  have hcancel :
    (n : ℝ) * (9 * endpointBuffer amplitude n / (8 * (n : ℝ))) =
        (9 / 8 : ℝ) * endpointBuffer amplitude n := by
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  rw [hscale, hcancel] at hnat
  exact hnat.trans_le (by
    simpa [endpointScale] using
      (endpointNaturalEnvelope_le (B := endpointBuffer amplitude n)
        (c := (9 / 8 : ℝ)) hB (by norm_num) hq))

/-- Pointwise target endpoint envelope outside its row bad event. -/
theorem targetEndpointValue_lt_envelope
    {amplitude q : ℝ} {n : ℕ} {sample : Fin n → ℝ × UnitMark} {p : ℝ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hp : |p| ≤ endpointBuffer amplitude n / 8)
    (hgood : sample ∉ targetEndpointBadEvent amplitude q n) :
    |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample p
        ((n : ℝ) - endpointBuffer amplitude n)| <
      endpointEnvelopeCoefficient q * endpointScale amplitude n := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 < endpointTuning amplitude q n := by
    exact mul_pos hq0 (Real.sqrt_pos.2 (div_pos hbuffer (Nat.cast_pos.2 hn)))
  let J := sampleMembershipIndices
    (targetEndpointComplement n (endpointBuffer amplitude n) (-endpointBuffer amplitude n / 8))
    sample
  have hsample : sample ∈ membershipPattern
      (targetEndpointComplement n (endpointBuffer amplitude n)
        (-endpointBuffer amplitude n / 8)) J :=
    mem_membershipPattern_sampleMembershipIndices _ _
  have hnat := abs_targetEndpointCutDefect_lt_naturalScale_allPatterns
    (width := (n : ℝ)) (buffer := endpointBuffer amplitude n)
    (p := p) (d := q) (x := endpointTuning amplitude q n)
    (Nat.cast_pos.2 hn) hbuffer hfit hp hn hq0 hx J sample hsample (by
      simpa [targetEndpointBadEvent] using hgood)
  have hscale : Real.sqrt n * endpointTuning amplitude q n =
      q * Real.sqrt (endpointBuffer amplitude n) :=
    sqrt_mul_endpointTuning hn hbuffer.le
  have hcancel :
    (n : ℝ) * (5 * endpointBuffer amplitude n / (4 * (n : ℝ))) =
        (5 / 4 : ℝ) * endpointBuffer amplitude n := by
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  rw [hscale, hcancel] at hnat
  exact hnat.trans_le (by
    simpa [endpointScale] using
      (endpointNaturalEnvelope_le (B := endpointBuffer amplitude n)
        (c := (5 / 4 : ℝ)) hB (by norm_num) hq))

/-- The source endpoint value set is nonempty once the buffer is nonnegative. -/
theorem sourceEndpointValueSet_nonempty {amplitude : ℝ} {n : ℕ}
    (sample : Fin n → ℝ × UnitMark) (hbuffer : 0 ≤ endpointBuffer amplitude n) :
    (sourceEndpointValueSet amplitude n sample).Nonempty := by
  refine ⟨|sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample 0
      ((n : ℝ) - endpointBuffer amplitude n)|, 0, ?_, rfl⟩
  simp only [abs_zero]
  positivity

/-- The target endpoint value set is nonempty once the buffer is nonnegative. -/
theorem targetEndpointValueSet_nonempty {amplitude : ℝ} {n : ℕ}
    (sample : Fin n → ℝ × UnitMark) (hbuffer : 0 ≤ endpointBuffer amplitude n) :
    (targetEndpointValueSet amplitude n sample).Nonempty := by
  refine ⟨|targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample 0
      ((n : ℝ) - endpointBuffer amplitude n)|, 0, ?_, rfl⟩
  simp only [abs_zero]
  positivity

/-- Outside the source bad event, the source supremum is bounded by the common envelope. -/
theorem sourceEndpointSup_le_envelope
    {amplitude q : ℝ} {n : ℕ} {sample : Fin n → ℝ × UnitMark}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hgood : sample ∉ sourceEndpointBadEvent amplitude q n) :
    sourceEndpointSup amplitude n sample ≤
      endpointEnvelopeCoefficient q * endpointScale amplitude n := by
  apply csSup_le (sourceEndpointValueSet_nonempty sample hbuffer.le)
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  exact (sourceEndpointValue_lt_envelope hn hbuffer hfit hB hq hp hgood).le

/-- Outside the target bad event, the target supremum is bounded by the common envelope. -/
theorem targetEndpointSup_le_envelope
    {amplitude q : ℝ} {n : ℕ} {sample : Fin n → ℝ × UnitMark}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hgood : sample ∉ targetEndpointBadEvent amplitude q n) :
    targetEndpointSup amplitude n sample ≤
      endpointEnvelopeCoefficient q * endpointScale amplitude n := by
  apply csSup_le (targetEndpointValueSet_nonempty sample hbuffer.le)
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  exact (targetEndpointValue_lt_envelope hn hbuffer hfit hB hq hp hgood).le

/-- The joint supremum is nonnegative and obeys the common envelope away from the joint bad event.
The proof supplies the local boundedness needed for each `sSup`. -/
theorem jointEndpointSup_nonneg_and_le_envelope
    {amplitude q : ℝ} {n : ℕ} {sample : Fin n → ℝ × UnitMark}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hgood : sample ∉ jointEndpointBadEvent amplitude q n) :
    0 ≤ jointEndpointSup amplitude n sample ∧
      jointEndpointSup amplitude n sample ≤
        endpointEnvelopeCoefficient q * endpointScale amplitude n := by
  have hsourceGood : sample ∉ sourceEndpointBadEvent amplitude q n :=
    fun hs ↦ hgood (Or.inl hs)
  have htargetGood : sample ∉ targetEndpointBadEvent amplitude q n :=
    fun ht ↦ hgood (Or.inr ht)
  have hsource := sourceEndpointSup_le_envelope
    hn hbuffer hfitSource hB hq hsourceGood
  have htarget := targetEndpointSup_le_envelope
    hn hbuffer hfitTarget hB hq htargetGood
  have hsourceBdd : BddAbove (sourceEndpointValueSet amplitude n sample) := by
    refine ⟨endpointEnvelopeCoefficient q * endpointScale amplitude n, ?_⟩
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact (sourceEndpointValue_lt_envelope hn hbuffer hfitSource hB hq hp hsourceGood).le
  have hsource0 : 0 ≤ sourceEndpointSup amplitude n sample := by
    have hmem : |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) sample 0
        ((n : ℝ) - endpointBuffer amplitude n)| ∈
        sourceEndpointValueSet amplitude n sample := by
      exact ⟨0, by simpa using (div_nonneg hbuffer.le (by norm_num : (0 : ℝ) ≤ 8)), rfl⟩
    exact (abs_nonneg _).trans (le_csSup hsourceBdd hmem)
  refine ⟨hsource0.trans (le_max_left _ _), ?_⟩
  exact max_le hsource htarget

/-- The Bernstein exponent is at least `q/9` under the common endpoint mass cap. -/
theorem endpointBernstein_exponent_ge
    {n : ℕ} {B q mass : ℝ} (hn : 0 < n) (hB : 1 ≤ B) (hq : 1 ≤ q)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 5 * B / (4 * n)) :
    q / 9 ≤
      (q * Real.sqrt (B / n)) ^ 2 /
        (4 * (mass + (q * Real.sqrt (B / n)) / Real.sqrt n)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hB)
  have hsqrtN_sq : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hnR.le
  have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
  have hx : q * Real.sqrt (B / (n : ℝ)) =
      q * Real.sqrt B / Real.sqrt n := by
    rw [Real.sqrt_div hB0]
    ring
  have hxpos : 0 < q * Real.sqrt (B / (n : ℝ)) := by
    exact mul_pos hq0 (Real.sqrt_pos.2 (div_pos (lt_of_lt_of_le zero_lt_one hB) hnR))
  have hden : 0 < 4 *
      (mass + (q * Real.sqrt (B / n)) / Real.sqrt n) := by
    positivity
  apply (le_div_iff₀ hden).2
  have hnMass : (n : ℝ) * mass ≤ 5 * B / 4 := by
    have := mul_le_mul_of_nonneg_left hmass hnR.le
    calc
      (n : ℝ) * mass ≤ (n : ℝ) * (5 * B / (4 * n)) := this
      _ = 5 * B / 4 := by field_simp [hnR.ne']
  have hnXSqrt : (n : ℝ) *
      ((q * Real.sqrt (B / n)) / Real.sqrt n) = q * Real.sqrt B := by
    rw [hx]
    field_simp [hsqrtN.ne']
    nlinarith
  have hnXsq : (n : ℝ) * (q * Real.sqrt (B / n)) ^ 2 = q ^ 2 * B := by
    rw [hx]
    field_simp [hsqrtN.ne']
    nlinarith
  have hcore :
      q / 9 * (4 * (5 * B / 4 + q * Real.sqrt B)) ≤ q ^ 2 * B := by
    have hsqrtB_le : Real.sqrt B ≤ B := by
      nlinarith [sq_nonneg (Real.sqrt B - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hB),
      mul_nonneg (sub_nonneg.mpr hq) hsqrtB.le]
  have hsum : (n : ℝ) *
      (mass + (q * Real.sqrt (B / n)) / Real.sqrt n) ≤
        5 * B / 4 + q * Real.sqrt B := by
    rw [mul_add, hnXSqrt]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 4 * (q / 9) by positivity)
  apply (le_of_mul_le_mul_left _ hnR)
  rw [hnXsq]
  nlinarith [hscaled, hcore]

/-- Exponential remainder at exponent `q/9` is bounded by `9/q`. -/
theorem exp_neg_ninth_le_inv {q : ℝ} (hq : 0 < q) :
    Real.exp (-(q / 9)) ≤ 9 / q := by
  have hmul := Real.mul_exp_neg_le_exp_neg_one (q / 9)
  have hexpOne : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hkey : (q / 9) * Real.exp (-(q / 9)) ≤ 1 := hmul.trans hexpOne
  apply (le_div_iff₀ hq).2
  nlinarith

/-- Uniform inverse-`q` source bad-event tail in the square-root buffer regime. -/
theorem endpointRowLaw_real_sourceBadEvent_le
    {amplitude q : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q) :
    (endpointRowLaw n).real (sourceEndpointBadEvent amplitude q n) ≤ 22 / q := by
  have hn1 : 1 ≤ n := hn
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 < endpointTuning amplitude q n := by
    exact mul_pos hq0 (Real.sqrt_pos.2
      (div_pos hbuffer (Nat.cast_pos.2 hn)))
  have henn := measure_sourceEndpointBadEvent_le_of_geometry
    (n := n) (width := (n : ℝ)) (buffer := endpointBuffer amplitude n)
    (d := q) (x := endpointTuning amplitude q n)
    (Nat.cast_pos.2 hn) hbuffer hfit hq0 hx hn1
  have hmassSource :
      (rankStripLaw n : Measure (ℝ × UnitMark)).real
          (sourceEndpointComplement n (endpointBuffer amplitude n)
            (endpointBuffer amplitude n / 8)) ≤
        9 * endpointBuffer amplitude n / (8 * n) := by
    exact rankStripLaw_real_sourceEndpointComplement_le
      (Nat.cast_pos.2 hn) hbuffer.le hfit
      (by simp [abs_of_nonneg (div_nonneg hbuffer.le (by norm_num : (0 : ℝ) ≤ 8))])
  have hmass :
      (rankStripLaw n : Measure (ℝ × UnitMark)).real
          (sourceEndpointComplement n (endpointBuffer amplitude n)
            (endpointBuffer amplitude n / 8)) ≤
        5 * endpointBuffer amplitude n / (4 * n) := by
    refine hmassSource.trans ?_
    have hquot : 0 ≤ endpointBuffer amplitude n / (n : ℝ) :=
      div_nonneg hbuffer.le (Nat.cast_nonneg n)
    calc
      9 * endpointBuffer amplitude n / (8 * n) =
          (9 / 8 : ℝ) * (endpointBuffer amplitude n / n) := by ring
      _ ≤ (5 / 4 : ℝ) * (endpointBuffer amplitude n / n) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hquot
      _ = 5 * endpointBuffer amplitude n / (4 * n) := by ring
  have hexponent := endpointBernstein_exponent_ge hn hB hq measureReal_nonneg hmass
  have hexpMono :
      Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (sourceEndpointComplement n (endpointBuffer amplitude n)
              (endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤
        Real.exp (-(q / 9)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (by simpa [endpointTuning] using hexponent)
  have hrem :
      2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (sourceEndpointComplement n (endpointBuffer amplitude n)
              (endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤ 18 / q := by
    have hinv := exp_neg_ninth_le_inv hq0
    calc
      2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (sourceEndpointComplement n (endpointBuffer amplitude n)
              (endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤
          2 * Real.exp (-(q / 9)) := mul_le_mul_of_nonneg_left hexpMono (by norm_num)
      _ ≤ 2 * (9 / q) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 18 / q := by ring
  let R : ℝ := 2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
    (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
      (sourceEndpointComplement n (endpointBuffer amplitude n)
        (endpointBuffer amplitude n / 8)) +
        endpointTuning amplitude q n / Real.sqrt n))))
  have henn' :
      (endpointRowLaw n) (sourceEndpointBadEvent amplitude q n) ≤
        ENNReal.ofReal (4 / q) + ENNReal.ofReal R := by
    simpa [endpointRowLaw, sourceEndpointBadEvent, R, neg_div] using henn
  have hfinite : ENNReal.ofReal (4 / q) + ENNReal.ofReal R ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono hfinite henn'
  have hfour0 : 0 ≤ 4 / q := div_nonneg (by norm_num) hq0.le
  have hrem0 : 0 ≤ R := by simp [R]; positivity
  rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hfour0,
    ENNReal.toReal_ofReal hrem0] at hreal
  have hR : R ≤ 18 / q := by simpa [R] using hrem
  have hfinal : ((endpointRowLaw n) (sourceEndpointBadEvent amplitude q n)).toReal ≤
      22 / q := hreal.trans (by
    calc
      4 / q + R ≤ 4 / q + 18 / q := add_le_add (le_refl _) hR
      _ = 22 / q := by ring)
  simpa [Measure.real] using hfinal

/-- Uniform inverse-`q` target bad-event tail in the square-root buffer regime. -/
theorem endpointRowLaw_real_targetBadEvent_le
    {amplitude q : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfit : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q) :
    (endpointRowLaw n).real (targetEndpointBadEvent amplitude q n) ≤ 22 / q := by
  have hn1 : 1 ≤ n := hn
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 < endpointTuning amplitude q n := by
    exact mul_pos hq0 (Real.sqrt_pos.2
      (div_pos hbuffer (Nat.cast_pos.2 hn)))
  have henn := measure_targetEndpointBadEvent_le_of_geometry
    (n := n) (width := (n : ℝ)) (buffer := endpointBuffer amplitude n)
    (d := q) (x := endpointTuning amplitude q n)
    (Nat.cast_pos.2 hn) hbuffer hfit hq0 hx hn1
  have hmass :
      (rankStripLaw n : Measure (ℝ × UnitMark)).real
          (targetEndpointComplement n (endpointBuffer amplitude n)
            (-endpointBuffer amplitude n / 8)) ≤
        5 * endpointBuffer amplitude n / (4 * n) := by
    exact rankStripLaw_real_targetEndpointComplement_le
      (Nat.cast_pos.2 hn) hbuffer.le hfit
      (by
        have hnonpos : -endpointBuffer amplitude n / 8 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbuffer.le) (by norm_num)
        rw [abs_of_nonpos hnonpos]
        linarith)
  have hexponent := endpointBernstein_exponent_ge hn hB hq measureReal_nonneg hmass
  have hexpMono :
      Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (targetEndpointComplement n (endpointBuffer amplitude n)
              (-endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤
        Real.exp (-(q / 9)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (by simpa [endpointTuning] using hexponent)
  have hrem :
      2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (targetEndpointComplement n (endpointBuffer amplitude n)
              (-endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤ 18 / q := by
    have hinv := exp_neg_ninth_le_inv hq0
    calc
      2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
          (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
            (targetEndpointComplement n (endpointBuffer amplitude n)
              (-endpointBuffer amplitude n / 8)) +
              endpointTuning amplitude q n / Real.sqrt n)))) ≤
          2 * Real.exp (-(q / 9)) := mul_le_mul_of_nonneg_left hexpMono (by norm_num)
      _ ≤ 2 * (9 / q) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 18 / q := by ring
  let R : ℝ := 2 * Real.exp (-((endpointTuning amplitude q n) ^ 2 /
    (4 * ((rankStripLaw n : Measure (ℝ × UnitMark)).real
      (targetEndpointComplement n (endpointBuffer amplitude n)
        (-endpointBuffer amplitude n / 8)) +
        endpointTuning amplitude q n / Real.sqrt n))))
  have henn' :
      (endpointRowLaw n) (targetEndpointBadEvent amplitude q n) ≤
        ENNReal.ofReal (4 / q) + ENNReal.ofReal R := by
    simpa [endpointRowLaw, targetEndpointBadEvent, R, neg_div] using henn
  have hfinite : ENNReal.ofReal (4 / q) + ENNReal.ofReal R ≠ ⊤ := by simp
  have hreal := ENNReal.toReal_mono hfinite henn'
  have hfour0 : 0 ≤ 4 / q := div_nonneg (by norm_num) hq0.le
  have hrem0 : 0 ≤ R := by simp [R]; positivity
  rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hfour0,
    ENNReal.toReal_ofReal hrem0] at hreal
  have hR : R ≤ 18 / q := by simpa [R] using hrem
  have hfinal : ((endpointRowLaw n) (targetEndpointBadEvent amplitude q n)).toReal ≤
      22 / q := hreal.trans (by
    calc
      4 / q + R ≤ 4 / q + 18 / q := add_le_add (le_refl _) hR
      _ = 22 / q := by ring)
  simpa [Measure.real] using hfinal

/-- Uniform inverse-`q` tail for the union of source and target bad events. -/
theorem endpointRowLaw_real_jointBadEvent_le
    {amplitude q : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q) :
    (endpointRowLaw n).real (jointEndpointBadEvent amplitude q n) ≤ 44 / q := by
  have hunion := measureReal_union_le
    (μ := endpointRowLaw n) (sourceEndpointBadEvent amplitude q n)
      (targetEndpointBadEvent amplitude q n)
  calc
    (endpointRowLaw n).real (jointEndpointBadEvent amplitude q n) ≤
        (endpointRowLaw n).real (sourceEndpointBadEvent amplitude q n) +
          (endpointRowLaw n).real (targetEndpointBadEvent amplitude q n) := by
      simpa [jointEndpointBadEvent] using hunion
    _ ≤ 22 / q + 22 / q := add_le_add
      (endpointRowLaw_real_sourceBadEvent_le hn hbuffer hfitSource hB hq)
      (endpointRowLaw_real_targetBadEvent_le hn hbuffer hfitTarget hB hq)
    _ = 44 / q := by ring

/-- A joint endpoint excursion above any larger multiple of `√Bₙ` is contained in the explicit
joint bad event. -/
theorem jointEndpointSup_largeEvent_subset_badEvent
    {amplitude q C : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hC : endpointEnvelopeCoefficient q < C) :
    {sample | C * endpointScale amplitude n < |jointEndpointSup amplitude n sample|} ⊆
      jointEndpointBadEvent amplitude q n := by
  intro sample hlarge
  by_contra hgood
  have hbound := jointEndpointSup_nonneg_and_le_envelope
    hn hbuffer hfitSource hfitTarget hB hq hgood
  change C * endpointScale amplitude n < |jointEndpointSup amplitude n sample| at hlarge
  rw [abs_of_nonneg hbound.1] at hlarge
  have hscale0 : 0 ≤ endpointScale amplitude n := Real.sqrt_nonneg _
  have hthreshold :
      endpointEnvelopeCoefficient q * endpointScale amplitude n ≤
        C * endpointScale amplitude n :=
    mul_le_mul_of_nonneg_right hC.le hscale0
  linarith

/-- Eventual uniform inverse-`q` tail for the actual joint endpoint supremum. -/
theorem eventually_endpointRowLaw_real_jointEndpointSup_tail_le
    {amplitude q : ℝ} (hamp : 0 < amplitude) (hq : 1 ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      (endpointRowLaw n).real
          {sample | (endpointEnvelopeCoefficient q + 1) * endpointScale amplitude n <
            |jointEndpointSup amplitude n sample|} ≤ 44 / q := by
  filter_upwards [eventually_endpointBuffer_geometry hamp] with n hngeom
  rcases hngeom with ⟨hn, hbuffer, hfitSource, hfitTarget, hB⟩
  have hsubset := jointEndpointSup_largeEvent_subset_badEvent
    (amplitude := amplitude) (q := q) (C := endpointEnvelopeCoefficient q + 1) (n := n)
    hn hbuffer hfitSource hfitTarget hB hq (by linarith)
  have hfinite : (endpointRowLaw n) (jointEndpointBadEvent amplitude q n) ≠ ⊤ := by
    rw [endpointRowLaw]
    exact measure_ne_top _ _
  exact (measureReal_mono hsubset hfinite).trans
    (endpointRowLaw_real_jointBadEvent_le hn hbuffer hfitSource hfitTarget hB hq)

/-- The source/target endpoint supremum is tight on the natural `√Bₙ` scale. -/
theorem jointEndpointSup_isBigOInProbability
    {amplitude : ℝ} (hamp : 0 < amplitude) :
    IsBigOInProbability endpointRowLaw
      (fun n ↦ jointEndpointSup amplitude n) (endpointScale amplitude) := by
  intro ε hε
  let q : ℝ := max 1 (44 / ε + 1)
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let C : ℝ := endpointEnvelopeCoefficient q + 1
  have hC : 0 < C := by
    have hcoef0 : 0 ≤ endpointEnvelopeCoefficient q := by
      dsimp [endpointEnvelopeCoefficient]
      positivity
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  have htail := eventually_endpointRowLaw_real_jointEndpointSup_tail_le hamp hq
  filter_upwards [htail] with n hnTail
  have hqLower : 44 / ε + 1 ≤ q := le_max_right _ _
  have hratio : 44 / q < ε := by
    rw [div_lt_iff₀ hq0]
    have hmul := mul_le_mul_of_nonneg_left hqLower hε.le
    field_simp at hmul
    nlinarith
  simpa [C] using hnTail.trans hratio.le

end OTSelector.RelativeVC
