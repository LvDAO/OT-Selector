import OTSelector.Feedback.FeedbackCountWindowMoment

/-!
# Factorial moments of the actual two-colour count

Both colours are combined as one finite event family.  Actual cross-colour event separation
makes this a simple count; its intensity is the sum of the two proved physical intensities.
Consequently the stopped aggregate has the quadratic factorial bound needed to exclude
same-colour and cross-colour time collisions in spatial limits.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped BigOperators Classical NNReal Topology
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.CountingProcess

variable {Ω : Type*} {m n : ℕ}

/-- Concatenate two genuine finite event families without dropping either colour. -/
noncomputable def mergedEventTime (ξ : Fin m → Ω → WithTop ℝ≥0)
    (ζ : Fin n → Ω → WithTop ℝ≥0) : Fin (m+n) → Ω → WithTop ℝ≥0 :=
  Fin.addCases ξ ζ

@[simp]
theorem finiteEventCountTop_mergedEventTime
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ζ : Fin n → Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    finiteEventCountTop (mergedEventTime ξ ζ) t ω =
      finiteEventCountTop ξ t ω + finiteEventCountTop ζ t ω := by
  simp only [finiteEventCountTop_eq_sum, Fin.sum_univ_add, mergedEventTime,
    Fin.addCases_left, Fin.addCases_right]

/-- Finite distinctness is retained exactly when the two colours have disjoint finite times. -/
theorem mergedEventTime_injective
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ζ : Fin n → Ω → WithTop ℝ≥0)
    (hξ : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (hζ : ∀ ω i j, ζ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ζ i ω = ζ j ω → i = j)
    (hcross : ∀ ω i j, ξ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ξ i ω ≠ ζ j ω) :
    ∀ ω i j, mergedEventTime ξ ζ i ω ≠ ⊤ → mergedEventTime ξ ζ j ω ≠ ⊤ →
      mergedEventTime ξ ζ i ω = mergedEventTime ξ ζ j ω → i = j := by
  intro ω i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simpa only [mergedEventTime, Fin.addCases_left] using
        (fun hi hj hij ↦ congrArg (Fin.castAdd n) (hξ ω i j hi hj hij))
    | right j =>
      simp only [mergedEventTime, Fin.addCases_left, Fin.addCases_right]
      intro hi hj hij
      exact (hcross ω i j hi hj hij).elim
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [mergedEventTime, Fin.addCases_left, Fin.addCases_right]
      intro hi hj hij
      exact (hcross ω j i hj hi hij.symm).elim
    | right j =>
      simpa only [mergedEventTime, Fin.addCases_right] using
        (fun hi hj hij ↦ congrArg (Fin.natAdd m) (hζ ω i j hi hj hij))

/-- The merged pathwise counting integral is the sum of the two actual colour integrals. -/
theorem countingIntegral_mergedEventTime
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ζ : Fin n → Ω → WithTop ℝ≥0)
    (hξ : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (hζ : ∀ ω i j, ζ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ζ i ω = ζ j ω → i = j)
    (hcross : ∀ ω i j, ξ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ξ i ω ≠ ζ j ω)
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    countingIntegral (finiteEventCountTop (mergedEventTime ξ ζ)) H t ω =
      countingIntegral (finiteEventCountTop ξ) H t ω +
        countingIntegral (finiteEventCountTop ζ) H t ω := by
  rw [countingIntegral_finiteEventCountTop_eq_sum _ _ _ _
      (mergedEventTime_injective ξ ζ hξ hζ hcross ω),
    countingIntegral_finiteEventCountTop_eq_sum _ _ _ _ (hξ ω),
    countingIntegral_finiteEventCountTop_eq_sum _ _ _ _ (hζ ω)]
  simp only [Fin.sum_univ_add, mergedEventTime, Fin.addCases_left, Fin.addCases_right,
    finiteEventTimeValue]

variable [MeasurableSpace Ω]

/-- The sum of genuine colour intensities is the intensity of their merged finite simple count. -/
theorem hasPredictableIntensity_mergedEventTime
    {μ : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ζ : Fin n → Ω → WithTop ℝ≥0)
    (hξ : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (hζ : ∀ ω i j, ζ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ζ i ω = ζ j ω → i = j)
    (hcross : ∀ ω i j, ξ i ω ≠ ⊤ → ζ j ω ≠ ⊤ → ξ i ω ≠ ζ j ω)
    {Λξ Λζ : ℝ≥0 → Ω → ℝ}
    (hIξ : HasPredictableIntensity μ F (finiteEventCountTop ξ) Λξ)
    (hIζ : HasPredictableIntensity μ F (finiteEventCountTop ζ) Λζ) :
    HasPredictableIntensity μ F (finiteEventCountTop (mergedEventTime ξ ζ))
      (fun t ω ↦ Λξ t ω + Λζ t ω) := by
  refine ⟨hIξ.predictable.add hIζ.predictable,
    fun t ω ↦ add_nonneg (hIξ.nonneg t ω) (hIζ.nonneg t ω),
    fun t ω ↦ (hIξ.integrableOn t ω).add (hIζ.integrableOn t ω), ?_⟩
  intro H hH
  have h := (hIξ.martingale hH).add (hIζ.martingale hH)
  convert h using 1
  funext t ω
  simp only [Pi.add_apply, compensatedIntegral,
    countingIntegral_mergedEventTime ξ ζ hξ hζ hcross]
  unfold integratedIntensity
  simp_rw [mul_add]
  rw [integral_add (hH.isBoundedPredictable.integrableOn_mul_intensity hIξ t ω)
    (hH.isBoundedPredictable.integrableOn_mul_intensity hIζ t ω)]
  ring

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual bulk-thinned source and target times cannot coincide when finite. -/
theorem safeSourceBulkEventTime_ne_targetBulkEventTime
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ω : FiniteSample n) (i j : Fin n)
    (hi : safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i ω ≠ ⊤)
    (hj : safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j ω ≠ ⊤) :
    safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i ω ≠
      safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j ω := by
  intro hij
  by_cases hiacc : eventAccepted (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i) ω
  · by_cases hjacc : eventAccepted (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j) ω
    · apply sourceEventTime_ne_targetEventTime hlam0 hlamHalf x0 p0 ω i j hiacc.1 hjacc.1
      simpa only [safeSourceBulkEventTime, safeTargetBulkEventTime,
        thinnedEventTime_of_accepted hiacc, thinnedEventTime_of_accepted hjacc] using hij
    · exact hj (thinnedEventTime_of_not_accepted hjacc)
  · exact hi (thinnedEventTime_of_not_accepted hiacc)

/-- The actual aggregate count contains every retained source and target event. -/
noncomputable def safeAggregateBulkCount
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (t : ℝ≥0) (ω : FiniteSample n) : ℕ :=
  safeSourceBulkCount hlam0 hlamHalf B x0 p0 t ω +
    safeTargetBulkCount hlam0 hlamHalf B x0 p0 t ω

private theorem aggregate_eq_merged
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ) :
    safeAggregateBulkCount (n := n) hlam0 hlamHalf B x0 p0 =
      finiteEventCountTop (mergedEventTime
        (fun i ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
        (fun i ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i)) := by
  funext t ω
  rw [finiteEventCountTop_mergedEventTime]
  rfl

/-- Cross-colour separation makes the aggregate a genuine simple counting process. -/
theorem safeAggregateBulkCount_isSimpleCountingProcess
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ) :
    IsSimpleCountingProcess (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeAggregateBulkCount hlam0 hlamHalf B x0 p0) := by
  rw [aggregate_eq_merged]
  apply IsSimpleCountingProcess.of_finiteEventCountTop
  · intro ω i
    induction i using Fin.addCases with
    | left i => simpa only [mergedEventTime, Fin.addCases_left] using
        safeSourceBulkEventTime_eq_top_or_pos hlam0 hlamHalf B x0 p0 ω i
    | right i => simpa only [mergedEventTime, Fin.addCases_right] using
        safeTargetBulkEventTime_eq_top_or_pos hlam0 hlamHalf B x0 p0 ω i
  · exact mergedEventTime_injective _ _
      (safeSourceBulkEventTime_injective hlam0 hlamHalf B x0 p0)
      (safeTargetBulkEventTime_injective hlam0 hlamHalf B x0 p0)
      (safeSourceBulkEventTime_ne_targetBulkEventTime hlam0 hlamHalf B x0 p0)
  · have h := (safeSourceBulkCount_stronglyAdapted (n := n) hlam0 hlamHalf B x0 p0).add
      (safeTargetBulkCount_stronglyAdapted (n := n) hlam0 hlamHalf B x0 p0)
    convert h using 1
    funext t ω
    rw [finiteEventCountTop_mergedEventTime, Nat.cast_add]
    rfl

/-- The aggregate intensity is the sum of the two previously derived physical rates. -/
theorem safeAggregateBulkCount_hasPredictableIntensity
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) :
    HasPredictableIntensity (finiteSampleLaw n : Measure (FiniteSample n))
      (usualRevealedFiltration hlam0 hlamHalf x0 p0)
      (safeAggregateBulkCount hlam0 hlamHalf B x0 p0)
      (fun t ω ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t ω +
        safeTargetBulkRate hlam0 hlamHalf B x0 p0 t ω) := by
  rw [aggregate_eq_merged]
  exact hasPredictableIntensity_mergedEventTime _ _
    (safeSourceBulkEventTime_injective hlam0 hlamHalf B x0 p0)
    (safeTargetBulkEventTime_injective hlam0 hlamHalf B x0 p0)
    (safeSourceBulkEventTime_ne_targetBulkEventTime hlam0 hlamHalf B x0 p0)
    (safeSourceBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB)
    (safeTargetBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB)

/-- The original finite law has a uniform quadratic factorial bound for aggregate stopped windows.
It includes pairs of opposite colours, not just repetitions within one colour. -/
theorem integral_factorial_safeAggregateA1Count_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n,
      (stoppedProcess (fun u ω ↦
        (safeAggregateBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
       stoppedProcess (fun u ω ↦
        (safeAggregateBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)^2 -
      (stoppedProcess (fun u ω ↦
        (safeAggregateBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
       stoppedProcess (fun u ω ↦
        (safeAggregateBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω)
      ∂finiteSampleLaw n) ≤ 72 * ((t : ℝ) - s)^2 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have heq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0.le hlamHalf eta B x0 p0 T) := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [heq] at hmask
  have hbound (u : ℝ≥0) (ω : FiniteSample n) :
      safeAggregateBulkCount hlam0.le hlamHalf B x0 p0 u ω ≤ n + n := by
    rw [aggregate_eq_merged]
    exact finiteEventCountTop_le _ u ω
  have h := integral_factorial_stoppedCount_increment_le
    (safeAggregateBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0)
    (safeAggregateBulkCount_hasPredictableIntensity (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB)
    hbound (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T)
    hmask (by norm_num : (0 : ℝ) ≤ 6) (fun u ω hu ↦ by
      have hr := safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T u ω hu
      linarith [hr.1, hr.2]) hst
  convert h using 1; ring

/-- The actual real-valued count in a stopped elapsed-time window. -/
noncomputable def safeAggregateA1WindowCount
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T s t : ℝ≥0) (ω : FiniteSample n) : ℝ :=
  stoppedProcess (fun u ω ↦ (safeAggregateBulkCount hlam0 hlamHalf B x0 p0 u ω : ℝ))
    (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T) t ω -
  stoppedProcess (fun u ω ↦ (safeAggregateBulkCount hlam0 hlamHalf B x0 p0 u ω : ℝ))
    (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T) s ω

/-- Monotonicity supplies the nonnegative integer behind the real count increment. -/
theorem safeAggregateA1WindowCount_eq_nat
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ω : FiniteSample n) :
    ∃ q : ℕ, q ≤ n+n ∧ safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t ω = q := by
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  let N := safeAggregateBulkCount (n := n) hlam0 hlamHalf B x0 p0
  have hN := safeAggregateBulkCount_isSimpleCountingProcess (n := n) hlam0 hlamHalf B x0 p0
  have hle : N (cappedStoppingValue s τ ω) ω ≤ N (cappedStoppingValue t τ ω) ω := by
    apply hN.monotone ω
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr hst)
  have hb : N (cappedStoppingValue t τ ω) ω ≤ n+n := by
    rw [show N = finiteEventCountTop (mergedEventTime
      (fun i ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
      (fun i ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i)) from
        aggregate_eq_merged hlam0 hlamHalf B x0 p0]
    exact finiteEventCountTop_le _ _ _
  refine ⟨N (cappedStoppingValue t τ ω) ω - N (cappedStoppingValue s τ ω) ω,
    (Nat.sub_le _ _).trans hb, ?_⟩
  rw [safeAggregateA1WindowCount, Limit.stoppedProcess_eq_cappedStoppingValue,
    Nat.cast_sub hle]

/-- Every stopped window factorial is nonnegative, including windows with zero or one event. -/
theorem safeAggregateA1WindowCount_factorial_nonneg
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ω : FiniteSample n) :
    0 ≤ (safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t ω)^2 -
      safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t ω := by
  obtain ⟨q, _, hq⟩ := safeAggregateA1WindowCount_eq_nat hlam0 hlamHalf eta B x0 p0 T hst ω
  rw [hq]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith

/-- The factorial observable is integrable under the original sample law, from finite population. -/
theorem integrable_safeAggregateA1WindowCount_factorial
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta : ℝ) {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun ω : FiniteSample n ↦
      (safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t ω)^2 -
        safeAggregateA1WindowCount hlam0 hlamHalf eta B x0 p0 T s t ω) (finiteSampleLaw n) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  let N := safeAggregateBulkCount (n := n) hlam0 hlamHalf B x0 p0
  have hN := safeAggregateBulkCount_isSimpleCountingProcess (n := n) hlam0 hlamHalf B x0 p0
  have hQ : StronglyAdapted F (stoppedProcess (fun u ω ↦ (N u ω : ℝ)) τ) := by
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous hN.stronglyAdapted
      (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T) hN.rightContinuous
  have hm : StronglyMeasurable
      (safeAggregateA1WindowCount (n := n) hlam0 hlamHalf eta B x0 p0 T s t) :=
    ((hQ t).mono (F.le t)).sub ((hQ s).mono (F.le s))
  apply Integrable.of_bound ((hm.pow 2).sub hm).aestronglyMeasurable
    (((n+n : ℕ) : ℝ)^2 + (n+n : ℕ))
  filter_upwards with ω
  obtain ⟨q, hq, heq⟩ := safeAggregateA1WindowCount_eq_nat hlam0 hlamHalf eta B x0 p0 T hst ω
  simp only [Pi.sub_apply, Pi.pow_apply, heq, Real.norm_eq_abs]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hq) 2)
    (by exact_mod_cast hq)

/-- Two or more aggregate events in a stopped window have probability at most `36 Δ²`. -/
theorem measureReal_safeAggregateA1WindowCount_ge_two_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {ω | 2 ≤ safeAggregateA1WindowCount hlam0.le (by linarith) eta B x0 p0 T s t ω} ≤
        36 * ((t : ℝ)-s)^2 := by
  have hlamHalf : lam < 1/2 := by linarith
  let X := safeAggregateA1WindowCount (n := n) hlam0.le hlamHalf eta B x0 p0 T s t
  have hM := mul_meas_ge_le_integral_of_nonneg
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) (f := fun ω ↦ X ω ^ 2-X ω)
    (ae_of_all _ (safeAggregateA1WindowCount_factorial_nonneg
      hlam0.le hlamHalf eta B x0 p0 T hst))
    (integrable_safeAggregateA1WindowCount_factorial hlam0.le hlamHalf eta hB x0 p0 T hst) 2
  have hsub : {ω | 2 ≤ X ω} ⊆ {ω | 2 ≤ X ω ^ 2-X ω} := by
    intro ω hω
    change 2 ≤ X ω at hω
    change 2 ≤ X ω ^ 2-X ω
    nlinarith [sq_nonneg (X ω-2)]
  have hp := measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n))) hsub
  have hi := integral_factorial_safeAggregateA1Count_increment_le
    (x0 := x0) (p0 := p0) hlam0 hlam hn hB heta hetaSmall T hst
  change (∫ ω, X ω ^ 2-X ω ∂(finiteSampleLaw n)) ≤ _ at hi
  change (finiteSampleLaw n : Measure (FiniteSample n)).real {ω | 2 ≤ X ω} ≤ _
  linarith

end OTSelector.FiniteSample
