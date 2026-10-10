import OTSelector.Feedback.FeedbackI3BacklogSum

/-!
# Abstract stopped rank-gap energy

This file isolates the probabilistic summation step in the stopped increasing-matching
estimate `(1.40)`.  The geometric input is a pair of deterministic tail inclusions: an oriented
rank gap is large only if the predictable rank backlog at its random left endpoint is large, or
if the opposite counting process has an atypically small stopped occupation.  The latter event
is bounded by the strict-stop lower-occupation theorem.

The random left endpoints are then summed through their honest finite-event counting
integrals.  The final compensator comparison uses the rate bounds only strictly before the
stopping coordinate.  The retained endpoint itself causes no loss because a singleton has zero
`timeMeasure` mass.  The conclusion is an actual `L1` estimate rather than an `O_P` statement.
-/

open Filter Set MeasureTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace OTSelector.CountingProcess

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A label is charged only when it actually occurs by the deterministic horizon and no later
than the stopping coordinate.  In particular an unattained (`⊤`) label is never retained. -/
def retainedRankGapEvent (T : NNReal) (tau xi : Omega -> WithTop NNReal) : Set Omega :=
  {omega | xi omega <= (T : WithTop NNReal) ∧ xi omega <= tau omega}

/-- The retained-label event is measurable at the bounded coordinate used for conditioning.
Capping an unattained label supplies a conditioning time, but does not create an event. -/
theorem measurableSet_retainedRankGapEvent
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {tau xi : Omega -> WithTop NNReal}
    (hxi : IsStoppingTime F xi) (htau : IsStoppingTime F tau) (T : NNReal) :
    MeasurableSet[(cappedStoppingValue_isStoppingTime F hxi T).measurableSpace]
      (retainedRankGapEvent T tau xi) := by
  have hretained : MeasurableSet[(hxi.min_const T).measurableSpace]
      ({omega | xi omega <= tau omega} ∩ {omega | xi omega <= (T : WithTop NNReal)}) :=
    (hxi.measurableSet_inter_le_const_iff _ T).mp
      ((hxi.measurableSet_le_stopping_time htau).inter (hxi.measurableSet_le' T))
  rw [IsStoppingTime.measurableSet] at hretained ⊢
  simpa only [coe_cappedStoppingValue, retainedRankGapEvent, Set.ofPred_and,
    Set.inter_comm] using hretained

/-- The predictable charge used at a random left endpoint of a retained rank edge. -/
noncomputable def stoppedRankGapMomentCharge
    (tau : Omega -> WithTop NNReal) (K : NNReal -> Omega -> Real)
    (c d : Real) : NNReal -> Omega -> Real :=
  fun s omega => throughStopMask tau s omega * ((K s omega / c) ^ 2 + 2 / d ^ 2)

/-- The stopped current occupation appearing on the right-hand side of `(1.40)`. -/
noncomputable def stoppedCurrentOccupation
    (tau : Omega -> WithTop NNReal) (K : NNReal -> Omega -> Real)
    (T : NNReal) : Omega -> Real :=
  fun omega =>
    ∫ s in Ioc (0 : NNReal) T,
      throughStopMask tau s omega * (1 + K s omega ^ 2) ∂timeMeasure

/-- The two oriented finite-rank gap families, summed in square. -/
noncomputable def stoppedRankGapEnergy {m : Nat}
    (Xplus Xminus : Fin m -> Omega -> Real) : Omega -> Real :=
  fun omega =>
    (∑ i, Xplus i omega ^ 2) + ∑ i, Xminus i omega ^ 2

omit [MeasurableSpace Omega] in
private theorem condExp_indicator_le_indicator_add_of_subset_rankGap
    {m0 m : MeasurableSpace Omega} {mu : @Measure Omega m0}
    [IsFiniteMeasure mu] (hm : m <= m0) {E D O : Set Omega}
    (hE : MeasurableSet[m0] E) (hD : MeasurableSet[m] D)
    (hO : MeasurableSet[m0] O) (hsubset : E ⊆ D ∪ O) {a : Real}
    (hOcc : condExp m mu (O.indicator fun _ => (1 : Real)) ≤ᵐ[mu]
      fun _ => a) :
    condExp m mu (E.indicator fun _ => (1 : Real)) ≤ᵐ[mu]
      fun omega => D.indicator (fun _ => (1 : Real)) omega + a := by
  let IE : Omega -> Real := E.indicator fun _ => 1
  let ID : Omega -> Real := D.indicator fun _ => 1
  let IO : Omega -> Real := O.indicator fun _ => 1
  have hD0 : MeasurableSet[m0] D := hm D hD
  have hIEint : Integrable IE mu := (integrable_const (1 : Real)).indicator hE
  have hIDint : Integrable ID mu := (integrable_const (1 : Real)).indicator hD0
  have hIOint : Integrable IO mu := (integrable_const (1 : Real)).indicator hO
  have hpoint : IE <= fun omega => ID omega + IO omega := by
    intro omega
    by_cases he : omega ∈ E
    · by_cases hd : omega ∈ D
      · by_cases ho : omega ∈ O <;> simp [IE, ID, IO, he, hd, ho]
      · have ho : omega ∈ O := (hsubset he).resolve_left hd
        simp [IE, ID, IO, he, hd, ho]
    · by_cases hd : omega ∈ D <;> by_cases ho : omega ∈ O <;>
        simp [IE, ID, IO, he, hd, ho]
  have hmono : condExp m mu IE ≤ᵐ[mu]
      condExp m mu (fun omega => ID omega + IO omega) :=
    condExp_mono hIEint (hIDint.add hIOint) (Eventually.of_forall hpoint)
  have hadd : condExp m mu (fun omega => ID omega + IO omega) =ᵐ[mu]
      condExp m mu ID + condExp m mu IO := condExp_add hIDint hIOint m
  have hIDstrong : StronglyMeasurable[m] ID :=
    stronglyMeasurable_const.indicator hD
  have hIDce : condExp m mu ID = ID :=
    condExp_of_stronglyMeasurable hm hIDstrong hIDint
  filter_upwards [hmono, hadd, hOcc] with omega hmonoOmega haddOmega hOccOmega
  rw [haddOmega, hIDce] at hmonoOmega
  change condExp m mu IE omega <= ID omega + condExp m mu IO omega at hmonoOmega
  change condExp m mu IE omega <= ID omega + a
  change condExp m mu IO omega <= a at hOccOmega
  linarith

/-!
## One random left endpoint
-/

/-- A deterministic rank-gap tail inclusion and the strict stopped lower-occupation theorem
give a genuine conditional second moment at a bounded random left endpoint. -/
theorem rankGap_integrable_sq_and_condExp_sq_le_of_strict_stop
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {N : NNReal -> Omega -> Nat} {Lambda : NNReal -> Omega -> Real}
    {sigma : Omega -> NNReal} {tau : Omega -> WithTop NNReal}
    {X K : Omega -> Real} {c0 Cglobal : Real} {S : NNReal}
    (hc0 : 0 < c0) (hCglobal : 0 <= Cglobal)
    (hN : IsSimpleCountingProcess F N)
    (hLambda : HasPredictableIntensity mu F N Lambda)
    (hLambdaUpper : forall u omega, Lambda u omega <= Cglobal)
    (hsigma : IsStoppingTime F fun omega => (sigma omega : WithTop NNReal))
    (hsigmaS : forall omega, sigma omega <= S) (htau : IsStoppingTime F tau)
    (hLambdaLower : forall (u : NNReal) omega, (u : WithTop NNReal) < tau omega ->
      c0 <= Lambda u omega)
    (hXMeas : Measurable X) (hXNonneg : forall omega, 0 <= X omega)
    (hKMeas : StronglyMeasurable[hsigma.measurableSpace] K)
    (hKNonneg : forall omega, 0 <= K omega)
    (hKSqInt : Integrable (fun omega => K omega ^ 2) mu)
    (hTailSubset : forall q : NNReal, 0 < q ->
      {omega | (q : Real) < X omega} ⊆
        {omega | lowerOccupationCountRate c0 * (q : Real) < K omega} ∪
          stoppedLowerOccupationEvent N sigma tau
            (lowerOccupationCountRate c0) q) :
    Integrable (fun omega => X omega ^ 2) mu ∧
      condExp hsigma.measurableSpace mu (fun omega => X omega ^ 2) ≤ᵐ[mu]
        fun omega =>
          (K omega / lowerOccupationCountRate c0) ^ 2 +
            2 / lowerOccupationDecayRate c0 ^ 2 := by
  have hrates := lowerOccupation_rates_pos hc0
  have hActualTail : forall q : Real, 0 < q ->
      condExp hsigma.measurableSpace mu
          ({omega | q < X omega}.indicator fun _ => (1 : Real)) ≤ᵐ[mu]
        fun omega =>
          (if K omega > lowerOccupationCountRate c0 * q then 1 else 0) +
            Real.exp (-lowerOccupationDecayRate c0 * q) := by
    intro q hq
    let qnn : NNReal := Real.toNNReal q
    have hqnn : 0 < qnn := Real.toNNReal_pos.mpr hq
    have hqcoe : (qnn : Real) = q := Real.coe_toNNReal q hq.le
    let E : Set Omega := {omega | q < X omega}
    let D : Set Omega :=
      {omega | lowerOccupationCountRate c0 * q < K omega}
    let O : Set Omega := stoppedLowerOccupationEvent N sigma tau
      (lowerOccupationCountRate c0) qnn
    have hE : MeasurableSet E :=
      measurableSet_lt measurable_const hXMeas
    have hD : MeasurableSet[hsigma.measurableSpace] D :=
      measurableSet_lt measurable_const hKMeas.measurable
    have hO : MeasurableSet O :=
      measurableSet_stoppedLowerOccupationEvent_bounded hN hsigma hsigmaS htau
    have hsubset : E ⊆ D ∪ O := by
      simpa only [E, D, O, qnn, hqcoe] using hTailSubset qnn hqnn
    have hOcc := condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping_strict
      (mu := mu) (F := F) (N := N) (Lambda := Lambda)
      (sigma := sigma) (tau := tau) (c₀ := c0) (C₀ := Cglobal)
      (B := S) (r := qnn) hc0 hCglobal hqnn hN hLambda hLambdaUpper
      hsigma hsigmaS htau hLambdaLower
    have hout := condExp_indicator_le_indicator_add_of_subset_rankGap
      hsigma.measurableSpace_le hE hD hO hsubset hOcc
    simpa only [E, D, O, Set.indicator, Set.mem_ofPred, gt_iff_lt, hqcoe] using hout
  have hmoment := integrable_sq_and_condExp_sq_le_of_tail
    hsigma.measurableSpace_le X K hXMeas hXNonneg hKMeas hKNonneg hKSqInt
    hrates.1 (by norm_num : (0 : Real) <= 1) hrates.2
    (by simpa only [one_mul] using hActualTail)
  simpa only [mul_one] using hmoment

/-!
## Finite-event summation and the stopped compensator
-/

omit [MeasurableSpace Omega] in
/-- The honest finite-event counting integral evaluates the moment charge at all finite random
left endpoints.  The mask is right-closed, so a label at `tau` is retained. -/
theorem countingIntegral_stoppedRankGapMomentCharge_eq_sum
    {m : Nat} (xi : Fin m -> Omega -> WithTop NNReal)
    (tau : Omega -> WithTop NNReal) (K : NNReal -> Omega -> Real)
    (c d : Real) (T : NNReal)
    (hinj : forall omega i j, xi i omega ≠ ⊤ -> xi j omega ≠ ⊤ ->
      xi i omega = xi j omega -> i = j)
    (omega : Omega) :
    countingIntegral (finiteEventCountTop xi)
        (stoppedRankGapMomentCharge tau K c d) T omega =
      ∑ i, (retainedRankGapEvent T tau (xi i)).indicator
        (fun omega' =>
          (K (cappedStoppingValue T (xi i) omega') omega' / c) ^ 2 + 2 / d ^ 2) omega := by
  classical
  rw [countingIntegral_finiteEventCountTop_eq_sum
    xi (stoppedRankGapMomentCharge tau K c d) omega T (hinj omega)]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hle : xi i omega <= (T : WithTop NNReal)
  · have hfinite : xi i omega ≠ ⊤ := (lt_of_le_of_lt hle (WithTop.coe_lt_top T)).ne
    have htime : finiteEventTimeValue xi omega i = cappedStoppingValue T (xi i) omega := by
      apply WithTop.coe_eq_coe.mp
      rw [finiteEventTimeValue_coe xi omega i hfinite, coe_cappedStoppingValue,
        min_eq_left hle]
    have hcap : (cappedStoppingValue T (xi i) omega : WithTop NNReal) = xi i omega := by
      rw [coe_cappedStoppingValue, min_eq_left hle]
    simp only [htime, stoppedRankGapMomentCharge, throughStopMask, hcap,
      retainedRankGapEvent, Set.indicator, Set.mem_ofPred_eq, hle, true_and]
    split_ifs <;> simp
  · rw [ite_eq_right hle, Set.indicator_of_notMem]
    exact fun h => hle h.1

/-- Summing the two honest stopped compensators costs only the stopped occupation of `1 + K^2`.
The upper rate bound is needed strictly before `tau`; the right-closed endpoint is discarded only
inside the time integral, where its singleton is null. -/
theorem integral_two_stoppedRankGapMomentCharge_countingIntegrals_le
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [SigmaFiniteFiltration mu F]
    {Nplus Nminus : NNReal -> Omega -> Nat}
    {LambdaPlus LambdaMinus K : NNReal -> Omega -> Real}
    {tau : Omega -> WithTop NNReal} {c d C0 : Real} (T : NNReal)
    (hc : 0 < c) (hd : 0 < d) (hC0 : 0 <= C0)
    (hNplus : IsSimpleCountingProcess F Nplus)
    (hNminus : IsSimpleCountingProcess F Nminus)
    (hLambdaPlus : HasPredictableIntensity mu F Nplus LambdaPlus)
    (hLambdaMinus : HasPredictableIntensity mu F Nminus LambdaMinus)
    (hCharge : IsBoundedSimplePredictable F
      (stoppedRankGapMomentCharge tau K c d))
    (hAplus : forall t, Integrable (fun omega =>
      integratedIntensity LambdaPlus (fun _ _ => (1 : Real)) t omega) mu)
    (hAminus : forall t, Integrable (fun omega =>
      integratedIntensity LambdaMinus (fun _ _ => (1 : Real)) t omega) mu)
    (hUpperPlus : forall (u : NNReal) omega, (u : WithTop NNReal) < tau omega ->
      LambdaPlus u omega <= C0)
    (hUpperMinus : forall (u : NNReal) omega, (u : WithTop NNReal) < tau omega ->
      LambdaMinus u omega <= C0)
    (hOccupation : Integrable (stoppedCurrentOccupation tau K T) mu)
    (hOccupationTime : forall omega, IntegrableOn
      (fun u => throughStopMask tau u omega * (1 + K u omega ^ 2))
      (Ioc (0 : NNReal) T) timeMeasure) :
    (∫ omega,
        countingIntegral Nplus (stoppedRankGapMomentCharge tau K c d) T omega +
          countingIntegral Nminus (stoppedRankGapMomentCharge tau K c d) T omega ∂mu) <=
      (2 * C0 * (1 / c ^ 2 + 2 / d ^ 2)) *
        (∫ omega, stoppedCurrentOccupation tau K T omega ∂mu) := by
  let H := stoppedRankGapMomentCharge tau K c d
  have hCountPlus : Integrable (countingIntegral Nplus H T) mu :=
    countingIntegral_integrable_of_intensity hLambdaPlus hCharge hAplus T
  have hCountMinus : Integrable (countingIntegral Nminus H T) mu :=
    countingIntegral_integrable_of_intensity hLambdaMinus hCharge hAminus T
  have hIntensityPlus : Integrable
      (fun omega => integratedIntensity LambdaPlus H T omega) mu :=
    integratedIntensity_integrable_of_boundedPredictable
      hLambdaPlus hCharge.isBoundedPredictable hAplus T
  have hIntensityMinus : Integrable
      (fun omega => integratedIntensity LambdaMinus H T omega) mu :=
    integratedIntensity_integrable_of_boundedPredictable
      hLambdaMinus hCharge.isBoundedPredictable hAminus T
  have hplusTime : forall omega, IntegrableOn
      (fun u => H u omega * LambdaPlus u omega)
      (Ioc (0 : NNReal) T) timeMeasure := fun omega =>
    hCharge.isBoundedPredictable.integrableOn_mul_intensity hLambdaPlus T omega
  have hminusTime : forall omega, IntegrableOn
      (fun u => H u omega * LambdaMinus u omega)
      (Ioc (0 : NNReal) T) timeMeasure := fun omega =>
    hCharge.isBoundedPredictable.integrableOn_mul_intensity hLambdaMinus T omega
  let C : Real := 2 * C0 * (1 / c ^ 2 + 2 / d ^ 2)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hpath : forall omega,
      integratedIntensity LambdaPlus H T omega +
          integratedIntensity LambdaMinus H T omega <=
        C * stoppedCurrentOccupation tau K T omega := by
    intro omega
    have hendpoint := ae_coe_ne_stoppingCoordinate tau T omega
    have hpoint : ∀ᵐ (u : NNReal) ∂(timeMeasure.restrict (Ioc (0 : NNReal) T)),
        H u omega * LambdaPlus u omega + H u omega * LambdaMinus u omega <=
          C * (throughStopMask tau u omega * (1 + K u omega ^ 2)) := by
      filter_upwards [hendpoint] with u hune
      by_cases hule : (u : WithTop NNReal) <= tau omega
      · have hult : (u : WithTop NNReal) < tau omega :=
          lt_of_le_of_ne hule hune
        have hp := hUpperPlus u omega hult
        have hm := hUpperMinus u omega hult
        dsimp only [H, stoppedRankGapMomentCharge]
        simp only [throughStopMask, ite_eq_left hule, one_mul]
        have hcharge0 : 0 <= (K u omega / c) ^ 2 + 2 / d ^ 2 := by
          positivity
        have hsumRate : LambdaPlus u omega + LambdaMinus u omega <= 2 * C0 := by
          linarith
        calc
          (((K u omega / c) ^ 2 + 2 / d ^ 2) * LambdaPlus u omega +
              ((K u omega / c) ^ 2 + 2 / d ^ 2) * LambdaMinus u omega) =
              ((K u omega / c) ^ 2 + 2 / d ^ 2) *
                (LambdaPlus u omega + LambdaMinus u omega) := by ring
          _ <= ((K u omega / c) ^ 2 + 2 / d ^ 2) * (2 * C0) :=
            mul_le_mul_of_nonneg_left hsumRate hcharge0
          _ <= C * (1 + K u omega ^ 2) := by
            dsimp [C]
            have hcInv : 0 <= 1 / c ^ 2 := by positivity
            have hdInv : 0 <= 2 / d ^ 2 := by positivity
            have hbase :
                (K u omega / c) ^ 2 + 2 / d ^ 2 <=
                  (1 / c ^ 2 + 2 / d ^ 2) * (1 + K u omega ^ 2) := by
              calc
                (K u omega / c) ^ 2 + 2 / d ^ 2 =
                    (1 / c ^ 2) * K u omega ^ 2 + 2 / d ^ 2 := by ring
                _ <= (1 / c ^ 2) * K u omega ^ 2 + 2 / d ^ 2 +
                    ((1 / c ^ 2) + (2 / d ^ 2) * K u omega ^ 2) := by
                  exact le_add_of_nonneg_right
                    (add_nonneg hcInv (mul_nonneg hdInv (sq_nonneg (K u omega))))
                _ = (1 / c ^ 2 + 2 / d ^ 2) *
                    (1 + K u omega ^ 2) := by ring
            have htwoC : 0 <= 2 * C0 := by positivity
            calc
              ((K u omega / c) ^ 2 + 2 / d ^ 2) * (2 * C0) =
                  (2 * C0) * ((K u omega / c) ^ 2 + 2 / d ^ 2) := by ring
              _ <= (2 * C0) *
                  ((1 / c ^ 2 + 2 / d ^ 2) * (1 + K u omega ^ 2)) :=
                mul_le_mul_of_nonneg_left hbase htwoC
              _ = (2 * C0 * (1 / c ^ 2 + 2 / d ^ 2)) *
                  (1 + K u omega ^ 2) := by ring
      · dsimp only [H, stoppedRankGapMomentCharge]
        simp only [throughStopMask, ite_eq_right hule, zero_mul]
        norm_num
    have hleftInt : IntegrableOn
        (fun u => H u omega * LambdaPlus u omega +
          H u omega * LambdaMinus u omega)
        (Ioc (0 : NNReal) T) timeMeasure :=
      (hplusTime omega).add (hminusTime omega)
    have hrightInt : IntegrableOn
        (fun u => C *
          (throughStopMask tau u omega * (1 + K u omega ^ 2)))
        (Ioc (0 : NNReal) T) timeMeasure :=
      (hOccupationTime omega).const_mul C
    have hmono := integral_mono_ae hleftInt hrightInt hpoint
    rw [integratedIntensity, integratedIntensity,
      ← integral_add (hplusTime omega) (hminusTime omega)]
    rw [stoppedCurrentOccupation, ← integral_const_mul]
    exact hmono
  have hIntensityBound :
      (∫ omega, integratedIntensity LambdaPlus H T omega +
        integratedIntensity LambdaMinus H T omega ∂mu) <=
        C * (∫ omega, stoppedCurrentOccupation tau K T omega ∂mu) := by
    have hmono := integral_mono_ae (hIntensityPlus.add hIntensityMinus)
      (hOccupation.const_mul C) (ae_of_all _ hpath)
    simpa only [integral_const_mul, Pi.add_apply] using hmono
  rw [integral_add hCountPlus hCountMinus,
    integral_countingIntegral_eq_integratedIntensity
      hNplus hLambdaPlus hCharge hAplus T,
    integral_countingIntegral_eq_integratedIntensity
      hNminus hLambdaMinus hCharge hAminus T,
    ← integral_add hIntensityPlus hIntensityMinus]
  simpa only [C, H] using hIntensityBound

/-!
## Abstract stopped rank-gap energy
-/

/-- Abstract `(1.40)` for two finite simple counting paths.

`Xplus i` is the oriented rank gap charged when the `i`-th plus label is the random left
endpoint; `Xminus` is the symmetric family.  The two `hTail...` assumptions are deterministic
rank-count inclusions, not moment or energy assumptions.  They are the only matching-specific
inputs.  All probabilistic bounds are derived here from the two genuine predictable
intensities. -/
theorem stoppedRankGapEnergy_integrable_and_integral_le
    {m : Nat} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    {sigmaPlus sigmaMinus : Fin m -> Omega -> WithTop NNReal}
    {Xplus Xminus : Fin m -> Omega -> Real}
    {LambdaPlus LambdaMinus K : NNReal -> Omega -> Real}
    {tau : Omega -> WithTop NNReal} {c0 Cglobal C0 : Real} (T : NNReal)
    (hc0 : 0 < c0) (hCglobal : 0 <= Cglobal) (hC0 : 0 <= C0)
    (hNplus : IsSimpleCountingProcess F (finiteEventCountTop sigmaPlus))
    (hNminus : IsSimpleCountingProcess F (finiteEventCountTop sigmaMinus))
    (hLambdaPlus : HasPredictableIntensity mu F
      (finiteEventCountTop sigmaPlus) LambdaPlus)
    (hLambdaMinus : HasPredictableIntensity mu F
      (finiteEventCountTop sigmaMinus) LambdaMinus)
    (hLambdaPlusGlobal : forall u omega, LambdaPlus u omega <= Cglobal)
    (hLambdaMinusGlobal : forall u omega, LambdaMinus u omega <= Cglobal)
    (hsigmaPlus : forall i, IsStoppingTime F (sigmaPlus i))
    (hsigmaMinus : forall i, IsStoppingTime F (sigmaMinus i))
    (hinjPlus : forall omega i j, sigmaPlus i omega ≠ ⊤ -> sigmaPlus j omega ≠ ⊤ ->
      sigmaPlus i omega = sigmaPlus j omega -> i = j)
    (hinjMinus : forall omega i j, sigmaMinus i omega ≠ ⊤ -> sigmaMinus j omega ≠ ⊤ ->
      sigmaMinus i omega = sigmaMinus j omega -> i = j)
    (htau : IsStoppingTime F tau)
    (hLowerPlus : forall (u : NNReal) omega,
      (u : WithTop NNReal) < tau omega -> c0 <= LambdaPlus u omega)
    (hLowerMinus : forall (u : NNReal) omega,
      (u : WithTop NNReal) < tau omega -> c0 <= LambdaMinus u omega)
    (hUpperPlus : forall (u : NNReal) omega,
      (u : WithTop NNReal) < tau omega -> LambdaPlus u omega <= C0)
    (hUpperMinus : forall (u : NNReal) omega,
      (u : WithTop NNReal) < tau omega -> LambdaMinus u omega <= C0)
    (hXplusMeas : forall i, Measurable (Xplus i))
    (hXminusMeas : forall i, Measurable (Xminus i))
    (hXplusNonneg : forall i omega, 0 <= Xplus i omega)
    (hXminusNonneg : forall i omega, 0 <= Xminus i omega)
    (hXplusRetained : forall i omega,
      omega ∉ retainedRankGapEvent T tau (sigmaPlus i) ->
        Xplus i omega = 0)
    (hXminusRetained : forall i omega,
      omega ∉ retainedRankGapEvent T tau (sigmaMinus i) ->
        Xminus i omega = 0)
    (hKplusMeas : forall i,
      StronglyMeasurable[(cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace]
        (fun omega => abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega)))
    (hKminusMeas : forall i,
      StronglyMeasurable[(cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace]
        (fun omega => abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega)))
    (hKplusSqInt : forall i, Integrable
      (fun omega => abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega) ^ 2) mu)
    (hKminusSqInt : forall i, Integrable
      (fun omega => abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega) ^ 2) mu)
    (hTailPlus : forall (i : Fin m) (q : NNReal), 0 < q ->
      {omega | (q : Real) < Xplus i omega} ⊆
        {omega | lowerOccupationCountRate c0 * (q : Real) <
          abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega)} ∪
        stoppedLowerOccupationEvent (finiteEventCountTop sigmaMinus)
          (cappedStoppingValue T (sigmaPlus i)) tau (lowerOccupationCountRate c0) q)
    (hTailMinus : forall (i : Fin m) (q : NNReal), 0 < q ->
      {omega | (q : Real) < Xminus i omega} ⊆
        {omega | lowerOccupationCountRate c0 * (q : Real) <
          abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega)} ∪
        stoppedLowerOccupationEvent (finiteEventCountTop sigmaPlus)
          (cappedStoppingValue T (sigmaMinus i)) tau (lowerOccupationCountRate c0) q)
    (hCharge : IsBoundedSimplePredictable F
      (stoppedRankGapMomentCharge tau K
        (lowerOccupationCountRate c0) (lowerOccupationDecayRate c0)))
    (hAplus : forall t, Integrable (fun omega =>
      integratedIntensity LambdaPlus (fun _ _ => (1 : Real)) t omega) mu)
    (hAminus : forall t, Integrable (fun omega =>
      integratedIntensity LambdaMinus (fun _ _ => (1 : Real)) t omega) mu)
    (hOccupation : Integrable (stoppedCurrentOccupation tau K T) mu)
    (hOccupationTime : forall omega, IntegrableOn
      (fun u => throughStopMask tau u omega * (1 + K u omega ^ 2))
      (Ioc (0 : NNReal) T) timeMeasure) :
    Integrable (stoppedRankGapEnergy Xplus Xminus) mu ∧
      (∫ omega, stoppedRankGapEnergy Xplus Xminus omega ∂mu) <=
        (2 * C0 *
          (1 / lowerOccupationCountRate c0 ^ 2 +
            2 / lowerOccupationDecayRate c0 ^ 2)) *
          (∫ omega, stoppedCurrentOccupation tau K T omega ∂mu) := by
  let c := lowerOccupationCountRate c0
  let d := lowerOccupationDecayRate c0
  let Aplus : Fin m -> Set Omega := fun i =>
    retainedRankGapEvent T tau (sigmaPlus i)
  let Aminus : Fin m -> Set Omega := fun i =>
    retainedRankGapEvent T tau (sigmaMinus i)
  let Rplus : Fin m -> Omega -> Real := fun i omega =>
    (K (cappedStoppingValue T (sigmaPlus i) omega) omega / c) ^ 2 + 2 / d ^ 2
  let Rminus : Fin m -> Omega -> Real := fun i omega =>
    (K (cappedStoppingValue T (sigmaMinus i) omega) omega / c) ^ 2 + 2 / d ^ 2
  let Gplus : Fin m -> Omega -> Real := fun i => (Aplus i).indicator (Rplus i)
  let Gminus : Fin m -> Omega -> Real := fun i => (Aminus i).indicator (Rminus i)
  have hrates := lowerOccupation_rates_pos hc0
  have hAplusMeas : forall i,
      MeasurableSet[(cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace]
        (Aplus i) := by
    intro i
    exact measurableSet_retainedRankGapEvent (hsigmaPlus i) htau T
  have hAminusMeas : forall i,
      MeasurableSet[(cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace]
        (Aminus i) := by
    intro i
    exact measurableSet_retainedRankGapEvent (hsigmaMinus i) htau T
  have hAplusMeas0 : forall i, MeasurableSet (Aplus i) := fun i =>
    (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace_le _ (hAplusMeas i)
  have hAminusMeas0 : forall i, MeasurableSet (Aminus i) := fun i =>
    (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace_le _ (hAminusMeas i)
  have hKplusNonneg : forall i omega,
      0 <= abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega) := fun i omega => abs_nonneg _
  have hKminusNonneg : forall i omega,
      0 <= abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega) := fun i omega => abs_nonneg _
  have hLocalPlus : forall i,
      Integrable (fun omega => Xplus i omega ^ 2) mu ∧
        condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace mu
            (fun omega => Xplus i omega ^ 2) ≤ᵐ[mu]
          fun omega =>
            (abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega) / c) ^ 2 + 2 / d ^ 2 := by
    intro i
    simpa only [c, d] using
      rankGap_integrable_sq_and_condExp_sq_le_of_strict_stop
        hc0 hCglobal hNminus hLambdaMinus hLambdaMinusGlobal
        (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T)
        (cappedStoppingValue_le T (sigmaPlus i)) htau hLowerMinus
        (hXplusMeas i) (hXplusNonneg i) (hKplusMeas i)
        (hKplusNonneg i) (hKplusSqInt i) (hTailPlus i)
  have hLocalMinus : forall i,
      Integrable (fun omega => Xminus i omega ^ 2) mu ∧
        condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace mu
            (fun omega => Xminus i omega ^ 2) ≤ᵐ[mu]
          fun omega =>
            (abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega) / c) ^ 2 + 2 / d ^ 2 := by
    intro i
    simpa only [c, d] using
      rankGap_integrable_sq_and_condExp_sq_le_of_strict_stop
        hc0 hCglobal hNplus hLambdaPlus hLambdaPlusGlobal
        (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T)
        (cappedStoppingValue_le T (sigmaMinus i)) htau hLowerPlus
        (hXminusMeas i) (hXminusNonneg i) (hKminusMeas i)
        (hKminusNonneg i) (hKminusSqInt i) (hTailMinus i)
  have hRplusInt : forall i, Integrable (Rplus i) mu := by
    intro i
    have hscaled := (hKplusSqInt i).const_mul (c⁻¹ ^ 2)
    have hterm : Integrable
        (fun omega => (K (cappedStoppingValue T (sigmaPlus i) omega) omega / c) ^ 2) mu := by
      apply hscaled.congr
      filter_upwards with omega
      rw [sq_abs]
      ring
    exact hterm.add (integrable_const (2 / d ^ 2))
  have hRminusInt : forall i, Integrable (Rminus i) mu := by
    intro i
    have hscaled := (hKminusSqInt i).const_mul (c⁻¹ ^ 2)
    have hterm : Integrable
        (fun omega => (K (cappedStoppingValue T (sigmaMinus i) omega) omega / c) ^ 2) mu := by
      apply hscaled.congr
      filter_upwards with omega
      rw [sq_abs]
      ring
    exact hterm.add (integrable_const (2 / d ^ 2))
  have hGplusInt : forall i, Integrable (Gplus i) mu := fun i =>
    (hRplusInt i).indicator (hAplusMeas0 i)
  have hGminusInt : forall i, Integrable (Gminus i) mu := fun i =>
    (hRminusInt i).indicator (hAminusMeas0 i)
  have hOnePlus : forall i,
      (∫ omega, Xplus i omega ^ 2 ∂mu) <= ∫ omega, Gplus i omega ∂mu := by
    intro i
    have hzero : (Aplus i).indicator (fun omega => Xplus i omega ^ 2) =
        fun omega => Xplus i omega ^ 2 := by
      funext omega
      by_cases hactive : omega ∈ Aplus i
      · simp [Set.indicator_of_mem hactive]
      · rw [Set.indicator_of_notMem hactive, hXplusRetained i omega]
        · norm_num
        · simpa only [Aplus, Set.mem_ofPred] using hactive
    have hsetEq : (∫ omega, Xplus i omega ^ 2 ∂mu) =
        ∫ omega in Aplus i, Xplus i omega ^ 2 ∂mu := by
      rw [← integral_indicator (hAplusMeas0 i), hzero]
    rw [hsetEq, ← setIntegral_condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace_le
      (hLocalPlus i).1 (hAplusMeas i)]
    have hce : condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace mu
          (fun omega => Xplus i omega ^ 2) ≤ᵐ[mu] Rplus i := by
      filter_upwards [(hLocalPlus i).2] with omega homega
      calc
        condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace mu
            (fun omega => Xplus i omega ^ 2) omega <=
            (abs (K (cappedStoppingValue T (sigmaPlus i) omega) omega) / c) ^ 2 + 2 / d ^ 2 := homega
        _ = Rplus i omega := by
          dsimp only [Rplus]
          rw [div_pow, sq_abs]
          ring
    have hceInt : Integrable
        (condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace mu
          (fun omega => Xplus i omega ^ 2)) (mu.restrict (Aplus i)) :=
      integrable_condExp.mono_measure Measure.restrict_le_self
    have hRrestrict : Integrable (Rplus i) (mu.restrict (Aplus i)) :=
      (hRplusInt i).mono_measure Measure.restrict_le_self
    calc
      (∫ omega in Aplus i,
          condExp (cappedStoppingValue_isStoppingTime F (hsigmaPlus i) T).measurableSpace mu
            (fun omega => Xplus i omega ^ 2) omega ∂mu) <=
          ∫ omega in Aplus i, Rplus i omega ∂mu :=
        integral_mono_ae hceInt hRrestrict (ae_restrict_le hce)
      _ = ∫ omega, Gplus i omega ∂mu := by
        rw [← integral_indicator (hAplusMeas0 i)]
  have hOneMinus : forall i,
      (∫ omega, Xminus i omega ^ 2 ∂mu) <= ∫ omega, Gminus i omega ∂mu := by
    intro i
    have hzero : (Aminus i).indicator (fun omega => Xminus i omega ^ 2) =
        fun omega => Xminus i omega ^ 2 := by
      funext omega
      by_cases hactive : omega ∈ Aminus i
      · simp [Set.indicator_of_mem hactive]
      · rw [Set.indicator_of_notMem hactive, hXminusRetained i omega]
        · norm_num
        · simpa only [Aminus, Set.mem_ofPred] using hactive
    have hsetEq : (∫ omega, Xminus i omega ^ 2 ∂mu) =
        ∫ omega in Aminus i, Xminus i omega ^ 2 ∂mu := by
      rw [← integral_indicator (hAminusMeas0 i), hzero]
    rw [hsetEq, ← setIntegral_condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace_le
      (hLocalMinus i).1 (hAminusMeas i)]
    have hce : condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace mu
          (fun omega => Xminus i omega ^ 2) ≤ᵐ[mu] Rminus i := by
      filter_upwards [(hLocalMinus i).2] with omega homega
      calc
        condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace mu
            (fun omega => Xminus i omega ^ 2) omega <=
            (abs (K (cappedStoppingValue T (sigmaMinus i) omega) omega) / c) ^ 2 + 2 / d ^ 2 := homega
        _ = Rminus i omega := by
          dsimp only [Rminus]
          rw [div_pow, sq_abs]
          ring
    have hceInt : Integrable
        (condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace mu
          (fun omega => Xminus i omega ^ 2)) (mu.restrict (Aminus i)) :=
      integrable_condExp.mono_measure Measure.restrict_le_self
    have hRrestrict : Integrable (Rminus i) (mu.restrict (Aminus i)) :=
      (hRminusInt i).mono_measure Measure.restrict_le_self
    calc
      (∫ omega in Aminus i,
          condExp (cappedStoppingValue_isStoppingTime F (hsigmaMinus i) T).measurableSpace mu
            (fun omega => Xminus i omega ^ 2) omega ∂mu) <=
          ∫ omega in Aminus i, Rminus i omega ∂mu :=
        integral_mono_ae hceInt hRrestrict (ae_restrict_le hce)
      _ = ∫ omega, Gminus i omega ∂mu := by
        rw [← integral_indicator (hAminusMeas0 i)]
  have hXplusSumInt : Integrable
      (fun omega => ∑ i, Xplus i omega ^ 2) mu :=
    integrable_finsetSum _ fun i _ => (hLocalPlus i).1
  have hXminusSumInt : Integrable
      (fun omega => ∑ i, Xminus i omega ^ 2) mu :=
    integrable_finsetSum _ fun i _ => (hLocalMinus i).1
  have hEnergyInt : Integrable (stoppedRankGapEnergy Xplus Xminus) mu := by
    change Integrable
      (fun omega => (∑ i, Xplus i omega ^ 2) + ∑ i, Xminus i omega ^ 2) mu
    exact hXplusSumInt.add hXminusSumInt
  have hGplusSumInt : Integrable (fun omega => ∑ i, Gplus i omega) mu :=
    integrable_finsetSum _ fun i _ => hGplusInt i
  have hGminusSumInt : Integrable (fun omega => ∑ i, Gminus i omega) mu :=
    integrable_finsetSum _ fun i _ => hGminusInt i
  have hEnergyToCharge :
      (∫ omega, stoppedRankGapEnergy Xplus Xminus omega ∂mu) <=
        ∫ omega, (∑ i, Gplus i omega) + ∑ i, Gminus i omega ∂mu := by
    change (∫ omega,
      (∑ i, Xplus i omega ^ 2) + ∑ i, Xminus i omega ^ 2 ∂mu) <= _
    rw [integral_add hXplusSumInt hXminusSumInt,
      integral_add hGplusSumInt hGminusSumInt,
      integral_finsetSum _ (fun i _ => (hLocalPlus i).1),
      integral_finsetSum _ (fun i _ => (hLocalMinus i).1),
      integral_finsetSum _ (fun i _ => hGplusInt i),
      integral_finsetSum _ (fun i _ => hGminusInt i)]
    exact add_le_add
      (Finset.sum_le_sum fun i _ => hOnePlus i)
      (Finset.sum_le_sum fun i _ => hOneMinus i)
  have hChargeEq : (fun omega =>
      (∑ i, Gplus i omega) + ∑ i, Gminus i omega) =
      fun omega =>
        countingIntegral (finiteEventCountTop sigmaPlus)
            (stoppedRankGapMomentCharge tau K c d) T omega +
          countingIntegral (finiteEventCountTop sigmaMinus)
            (stoppedRankGapMomentCharge tau K c d) T omega := by
    funext omega
    have hp := countingIntegral_stoppedRankGapMomentCharge_eq_sum
      sigmaPlus tau K c d T hinjPlus omega
    have hm := countingIntegral_stoppedRankGapMomentCharge_eq_sum
      sigmaMinus tau K c d T hinjMinus omega
    change (∑ i, Gplus i omega) + ∑ i, Gminus i omega = _
    simpa only [Gplus, Gminus, Aplus, Aminus, Rplus, Rminus] using
      congrArg₂ (fun x y : Real => x + y) hp.symm hm.symm
  have hComp := integral_two_stoppedRankGapMomentCharge_countingIntegrals_le
    T hrates.1 hrates.2 hC0 hNplus hNminus hLambdaPlus hLambdaMinus
    hCharge hAplus hAminus hUpperPlus hUpperMinus hOccupation hOccupationTime
  refine ⟨hEnergyInt, hEnergyToCharge.trans ?_⟩
  rw [hChargeEq]
  simpa only [c, d] using hComp

end OTSelector.CountingProcess
