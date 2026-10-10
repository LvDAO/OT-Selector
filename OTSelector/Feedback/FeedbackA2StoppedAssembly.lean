import OTSelector.Feedback.FeedbackA2Assembly
import OTSelector.Feedback.FeedbackA1Excursion
import OTSelector.Feedback.FeedbackA1Survival
import OTSelector.Feedback.FeedbackCurrentRankBridge

/-!
# Actual stopped-current A2 assembly

The older A2 event uses a full-horizon rank-current excursion.  This file keeps that API intact
and assembles a separate event controlled by the actual A1-stopped bulk current.  The
deterministic inclusion uses the earliest closed shear-boundary hit, so the witness lies through
the right-closed A1 stop even when it coincides with the bulk exit.

All statements here are fixed at the actual initial condition `(x0, p0) = (B, 0)`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal Topology

namespace OTSelector

open FiniteSample RelativeVC

/-! ## The earliest closed shear-boundary hit -/

private theorem safeFeedbackHeightAtElapsed_zero_start_stoppedA2
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) :
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 0 sample = 0 := by
  by_cases hNoTie : sample.NoFeedbackTies lam B 0
  · rw [sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
      hlam0 hlamHalf B 0 0 hNoTie]
    simpa using sample.feedbackCurve_at_x0 hlam0 hlamHalf B 0
  · simp [safeFeedbackHeightAtElapsed, hNoTie]

/-- A closed boundary hit has an earliest witness.  Every strictly earlier time remains in the
open shear window; this is the property that an arbitrary intermediate-value witness lacks. -/
private theorem exists_least_safeFeedbackHeight_boundary
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (sample : FiniteSample n) {t : ℝ≥0}
    (htHeight :
      |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| = B / 8) :
    ∃ s : ℝ≥0,
      s ≤ t ∧
        |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 s sample| = B / 8 ∧
        ∀ u : ℝ≥0, u < s →
          |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 u sample| < B / 8 := by
  let height : ℝ≥0 → ℝ := fun u ↦
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 u sample
  let S : Set ℝ≥0 := {u | u ≤ t ∧ |height u| = B / 8}
  have hcont : Continuous height :=
    safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf B 0 sample
  have hclosed : IsClosed S := by
    change IsClosed (Iic t ∩ {u : ℝ≥0 | |height u| = B / 8})
    exact isClosed_Iic.inter (isClosed_eq hcont.abs continuous_const)
  have hnonempty : S.Nonempty := by
    exact ⟨t, le_rfl, htHeight⟩
  have hbdd : BddBelow S := OrderBot.bddBelow S
  let s : ℝ≥0 := sInf S
  have hleast : IsLeast S s := hclosed.isLeast_csInf hnonempty hbdd
  refine ⟨s, hleast.1.1, hleast.1.2, ?_⟩
  intro u hu
  by_contra hnot
  have hge : B / 8 ≤ |height u| := le_of_not_gt hnot
  have hheight0 : height 0 = 0 :=
    safeFeedbackHeightAtElapsed_zero_start_stoppedA2
      hlam0 hlamHalf B sample
  have htarget : B / 8 ∈ Set.Icc |height 0| |height u| := by
    rw [hheight0, abs_zero]
    exact ⟨div_nonneg hB.le (by norm_num), hge⟩
  obtain ⟨v, hv, hvHeight⟩ :=
    (intermediate_value_Icc (show (0 : ℝ≥0) ≤ u from bot_le)
      hcont.abs.continuousOn) htarget
  have hvS : v ∈ S := by
    refine ⟨hv.2.trans (hu.le.trans hleast.1.1), hvHeight⟩
  exact (not_lt_of_ge ((hleast.2 hvS).trans hv.2)) hu

/-! ## The stopped A2 event -/

/-- Actual A2 bad event with the A1-good complement and the measurable A1-stopped current tail.
The older full-horizon `feedbackA2BadEvent` remains a separate API. -/
noncomputable def feedbackA2StoppedBadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0) (R : ℕ) :
    Set (FiniteSample n) :=
  feedbackA2GlobalCutBadEvent globalQ n ∪
    (feedbackA2EndpointBadEvent amplitude endpointQ n ∪
      ((feedbackA1GoodEvent n lam B 0)ᶜ ∪
        safeFeedbackA1StoppedCurrentExcursionEvent
          (n := n) hlam0 hlamHalf eta B T R))

noncomputable def feedbackA2StoppedGoodEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0) (R : ℕ) :
    Set (FiniteSample n) :=
  (feedbackA2StoppedBadEvent
    (n := n) hlam0 hlamHalf eta amplitude globalQ endpointQ B T R)ᶜ

theorem measurableSet_feedbackA2StoppedBadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0) (R : ℕ) :
    MeasurableSet (feedbackA2StoppedBadEvent
      (n := n) hlam0 hlamHalf eta amplitude globalQ endpointQ B T R) := by
  exact (measurableSet_feedbackA2GlobalCutBadEvent globalQ n).union
    ((measurableSet_feedbackA2EndpointBadEvent amplitude endpointQ n).union
      ((measurableSet_feedbackA1GoodEvent n lam B 0).compl.union
        (measurableSet_safeFeedbackA1StoppedCurrentExcursionEvent
          (n := n) hlam0 hlamHalf eta B T R)))

theorem measurableSet_feedbackA2StoppedGoodEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0) (R : ℕ) :
    MeasurableSet (feedbackA2StoppedGoodEvent
      (n := n) hlam0 hlamHalf eta amplitude globalQ endpointQ B T R) :=
  (measurableSet_feedbackA2StoppedBadEvent
    hlam0 hlamHalf eta amplitude globalQ endpointQ B T R).compl

/-! ## First-hit inclusion into the stopped current event -/

private theorem feedbackA2_stopped_bulk_section_bounds
    {n : ℕ} {B p x : ℝ} (hB : 0 ≤ B)
    (hxLower : B ≤ x) (hxUpper : x ≤ (n : ℝ) - B)
    (hp : |p| = B / 8) :
    (∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ))) ∧
      (∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n) ∧
      (∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ))) ∧
      (∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n) := by
  have hB8 : 0 ≤ B / 8 := by positivity
  constructor
  · intro u
    have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
    have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
    have hterm : |p * (1 - (u : ℝ))| ≤ B / 8 := by
      rw [abs_mul, abs_of_nonneg hu0, hp]
      nlinarith
    nlinarith [le_abs_self (p * (1 - (u : ℝ)))]
  · constructor
    · intro u
      have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
      have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
      have hterm : |p * (1 - (u : ℝ))| ≤ B / 8 := by
        rw [abs_mul, abs_of_nonneg hu0, hp]
        nlinarith
      have hlow := neg_le_of_abs_le hterm
      nlinarith
    · constructor
      · intro v
        have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
        have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
        have hterm : |p * (1 + (v : ℝ))| ≤ B / 4 := by
          rw [abs_mul, abs_of_nonneg hv0, hp]
          nlinarith
        have hlow := neg_le_of_abs_le hterm
        nlinarith
      · intro v
        have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
        have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
        have hterm : |p * (1 + (v : ℝ))| ≤ B / 4 := by
          rw [abs_mul, abs_of_nonneg hv0, hp]
          nlinarith
        nlinarith [le_abs_self (p * (1 + (v : ℝ)))]

/-- A raw exact shear hit is caused by a global cut failure, an A1-good failure, or an actual
A1-stopped bulk-current excursion.  The earliest-hit construction is what permits the current
witness to occur at the closed bulk endpoint. -/
theorem feedbackA2ExactShearHitBeforeRaw_subset_globalCut_or_A1Bad_or_stoppedCurrent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B globalQ : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (_hBn : B ≤ n)
    (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4) :
    feedbackA2ExactShearHitBeforeRaw
        (n := n) hlam0.le (by linarith) B T ⊆
      feedbackA2GlobalCutBadEvent globalQ n ∪
        ((feedbackA1GoodEvent n lam B 0)ᶜ ∪
          safeFeedbackA1StoppedCurrentExcursionEvent
            (n := n) hlam0.le (by linarith) eta B T R) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  intro sample hhit
  by_cases hcut : sample ∈ feedbackA2GlobalCutBadEvent globalQ n
  · exact Or.inl hcut
  by_cases hA1 : sample ∈ feedbackA1GoodEvent n lam B 0
  · apply Or.inr
    apply Or.inr
    obtain ⟨t, ht, htHeight⟩ := hhit
    obtain ⟨s, hsLe, hsHeight, hbefore⟩ :=
      exists_least_safeFeedbackHeight_boundary
        hlam0.le hlamHalf hB sample htHeight
    have hsT : s < T := hsLe.trans_lt ht.2
    have hsBulk : (s : WithTop ℝ≥0) ≤
        safeFeedbackBulkExitTime hlam0.le hlamHalf B B 0 sample := by
      apply le_of_not_gt
      intro hExitLt
      rw [safeFeedbackBulkExitTime, MeasureTheory.hittingAfter_lt_iff] at hExitLt
      obtain ⟨u, hu, huBad⟩ := hExitLt
      have huHeight := hbefore u hu.2
      have huT : u < T := hu.2.trans hsT
      have huTReal : (u : ℝ) < (T : ℝ) := by exact_mod_cast huT
      have huRegion : feedbackBulkRegion n B
          (elapsedFeedbackCoordinate B u)
          (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 u sample) := by
        refine ⟨?_, ?_, huHeight.le⟩
        · simp [elapsedFeedbackCoordinate]
        · simp only [elapsedFeedbackCoordinate]
          linarith
      change ¬feedbackBulkRegion n B
        (elapsedFeedbackCoordinate B u)
        (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 u sample) at huBad
      exact huBad huRegion
    have hstopEq := safeFeedbackA1StopTime_eq_min_bulkExit_horizon_of_good
      hn hlam0.le hlamHalf heta hB B 0 T sample hA1 hsqrt hlinear
    have hsStop : (s : WithTop ℝ≥0) ≤
        safeFeedbackA1StopTime hlam0.le hlamHalf eta B B 0 T sample := by
      rw [hstopEq]
      exact le_min hsBulk (WithTop.coe_le_coe.mpr hsT.le)
    have hsLower : B ≤ B + (s : ℝ) := le_add_of_nonneg_right s.2
    have hsTReal : (s : ℝ) < (T : ℝ) := by exact_mod_cast hsT
    have hsUpper : B + (s : ℝ) ≤ (n : ℝ) - B := by linarith
    have hsections := feedbackA2_stopped_bulk_section_bounds
      hB.le hsLower hsUpper hsHeight
    have hcomponents := first_hit_cut_component_exceeds (show 0 < n by omega)
      (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
      hsections.1 hsections.2.1 hsections.2.2.1 hsections.2.2.2
      (p := safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 s sample)
      (x := B + (s : ℝ)) (hit := B / 4)
      (by rw [hsHeight]; ring)
      (sourceThreshold := (globalQ + 32) * Real.sqrt n)
      (targetThreshold := (globalQ + 32) * Real.sqrt n)
      (currentThreshold := 2 * (R : ℝ) + 2)
      (by nlinarith [hthreshold])
    have hglobalGood : sample ∈ feedbackA2GlobalCutGoodEvent globalQ n := hcut
    have hsourceSup := feedbackA2GlobalCutGoodEvent.source_bound hglobalGood
    have htargetSup := feedbackA2GlobalCutGoodEvent.target_bound hglobalGood
    rcases hcomponents with hsource | htarget | hcurrent
    · exact False.elim ((not_lt_of_ge
        ((abs_sourceCutDefect_le_globalSourceCutSup
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackSourceRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 s sample)
          (B + (s : ℝ))).trans hsourceSup)) hsource)
    · exact False.elim ((not_lt_of_ge
        ((abs_targetCutDefect_le_globalTargetCutSup
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 s sample)
          (B + (s : ℝ))).trans htargetSup)) htarget)
    · let rankK : ℝ := feedbackRankDiscrepancy
          (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0.le hlamHalf B 0 s sample)
          (elapsedFeedbackCoordinate B s)
      let leftK : ℝ :=
        (CountingProcess.leftCurrentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
          (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
          s sample : ℝ)
      let postK : ℝ :=
        (CountingProcess.currentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0.le hlamHalf B B 0)
          (safeTargetBulkCount (n := n) hlam0.le hlamHalf B B 0)
          s sample : ℝ)
      have hrankLeft : |rankK - leftK| ≤ 1 := by
        simpa only [rankK, leftK, elapsedFeedbackCoordinate] using
          abs_feedbackRankDiscrepancy_sub_leftCurrentOfSafeBulkCounts_le_one_of_le_exit
            hlam0.le hlamHalf B B 0 s sample
              (feedbackA1GoodEvent.noFeedbackTies hA1) hsBulk
      have hpostLeft : |postK - leftK| ≤ 1 := by
        simpa only [postK, leftK] using
          CountingProcess.abs_currentOfCounts_sub_leftCurrentOfCounts_le_one
            (safeSourceBulkCount_isSimpleCountingProcess
              (n := n) hlam0.le hlamHalf B B 0)
            (safeTargetBulkCount_isSimpleCountingProcess
              (n := n) hlam0.le hlamHalf B B 0)
            (safeBulkCounts_noSimultaneousJumpsOn
              (n := n) hlam0.le hlamHalf B B 0 s)
      have hleftPost : |leftK - postK| ≤ 1 := by
        simpa only [abs_sub_comm] using hpostLeft
      have hrankPost : |rankK - postK| ≤ 2 := by
        calc
          |rankK - postK| = |(rankK - leftK) + (leftK - postK)| := by ring_nf
          _ ≤ |rankK - leftK| + |leftK - postK| := abs_add_le _ _
          _ ≤ 2 := by linarith
      have hrankLe : |rankK| ≤ |rankK - postK| + |postK| := by
        calc
          |rankK| = |(rankK - postK) + postK| := by ring_nf
          _ ≤ |rankK - postK| + |postK| := abs_add_le _ _
      have hcurrent' : 2 * (R : ℝ) + 2 < |rankK| := by
        simpa only [rankK, elapsedFeedbackCoordinate] using hcurrent
      have hreaches : 2 * (R : ℝ) ≤ |postK| := by linarith
      apply safeFeedbackA1StoppedCurrentExcursionRaw_subset_event
        (n := n) hlam0.le hlamHalf eta B T R
      exact ⟨s, hsT.le, hsStop, by simpa only [postK] using hreaches⟩
  · exact Or.inr (Or.inl hA1)

/-- The same inclusion with the endpoint component inserted into the combined measurable bad
event. -/
theorem feedbackA2ExactShearHitBeforeRaw_subset_feedbackA2StoppedBadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n)
    (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4) :
    feedbackA2ExactShearHitBeforeRaw
        (n := n) hlam0.le (by linarith) B T ⊆
      feedbackA2StoppedBadEvent
        (n := n) hlam0.le (by linarith)
          eta amplitude globalQ endpointQ B T R := by
  intro sample hhit
  have hmain :=
    feedbackA2ExactShearHitBeforeRaw_subset_globalCut_or_A1Bad_or_stoppedCurrent
      hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hhit
  rcases hmain with hglobal | hA1 | hcurrent
  · exact Or.inl hglobal
  · exact Or.inr (Or.inr (Or.inl hA1))
  · exact Or.inr (Or.inr (Or.inr hcurrent))

/-- On the actual stopped A2 good event, the safe height stays strictly inside the closed shear
window throughout the deterministic horizon. -/
theorem feedbackA2StoppedGoodEvent.abs_safeFeedbackHeightAtElapsed_lt
    {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n)
    (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (by linarith) eta amplitude globalQ endpointQ B T R)
    {t : ℝ≥0} (ht : t < T) :
    |safeFeedbackHeightAtElapsed hlam0.le (by linarith) B 0 t sample| < B / 8 := by
  have hnoHit : sample ∉ feedbackA2ExactShearHitBeforeRaw
      hlam0.le (by linarith) B T := by
    intro hhit
    exact hgood
      (feedbackA2ExactShearHitBeforeRaw_subset_feedbackA2StoppedBadEvent
        hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hhit)
  exact abs_safeFeedbackHeightAtElapsed_lt_of_not_exactShearHit
    hlam0.le (by linarith) hB hnoHit ht

/-! ## Explicit probability bound -/

/-- The actual stopped A2 event has a fully explicit probability bound.  In particular, the
current term is discharged by the cubic A1-stopped tail rather than retained as a premise. -/
theorem finiteSampleLaw_real_feedbackA2StoppedBadEvent_le
    {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n)
    (heta : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (hglobalQ : 0 < globalQ)
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hbufferOne : 1 ≤ endpointBuffer amplitude n)
    (hendpointQ : 1 ≤ endpointQ) (hR : 0 < R) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2StoppedBadEvent
          (n := n) hlam0.le (by linarith)
            eta amplitude globalQ endpointQ B T R) ≤
      18832 / globalQ + 44 / endpointQ +
        ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
        (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 := by
  let hlamHalf : lam < 1 / 2 := by linarith
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let G := feedbackA2GlobalCutBadEvent globalQ n
  let E := feedbackA2EndpointBadEvent amplitude endpointQ n
  let A := (feedbackA1GoodEvent n lam B 0)ᶜ
  let K := safeFeedbackA1StoppedCurrentExcursionEvent
    (n := n) hlam0.le hlamHalf eta B T R
  have hn0 : 0 < n := by omega
  have hG : μ.real G ≤ 18832 / globalQ := by
    simpa only [μ, G] using
      finiteSampleLaw_real_feedbackA2GlobalCutBadEvent_le hn0 hglobalQ
  have hE : μ.real E ≤ 44 / endpointQ := by
    simpa only [μ, E] using
      finiteSampleLaw_real_feedbackA2EndpointBadEvent_le
        hn0 hbuffer hfitSource hfitTarget hbufferOne hendpointQ
  have hAENN :
      μ A ≤ 2 * RelativeVC.regularityPolynomialBadBound n := by
    simpa only [μ, A] using
      feedbackA1GoodEvent_compl_le n hn hlam0.le hlamHalf B 0
  have hA : μ.real A ≤
      ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) := by
    apply ENNReal.toReal_mono
    · apply ENNReal.mul_ne_top
      · norm_num
      · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (RelativeVC.regularityPolynomialBadBound_le_inv_pow n (by omega))
    · exact hAENN
  have hK : μ.real K ≤
      (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 := by
    simpa only [μ, K, hlamHalf] using
      finiteSampleLaw_real_safeFeedbackA1StoppedCurrentExcursion_le
        (n := n) hlam0 hlam hn0 hB hBn heta hetaSmall T hR
  have hAK := measureReal_union_le (μ := μ) A K
  have hEAK := measureReal_union_le (μ := μ) E (A ∪ K)
  have hAll := measureReal_union_le (μ := μ) G (E ∪ (A ∪ K))
  calc
    μ.real (feedbackA2StoppedBadEvent
        (n := n) hlam0.le hlamHalf
          eta amplitude globalQ endpointQ B T R) ≤
        μ.real G + μ.real (E ∪ (A ∪ K)) := by
      simpa only [feedbackA2StoppedBadEvent, G, E, A, K] using hAll
    _ ≤ μ.real G + (μ.real E + μ.real (A ∪ K)) :=
      add_le_add le_rfl hEAK
    _ ≤ μ.real G + (μ.real E + (μ.real A + μ.real K)) :=
      add_le_add le_rfl (add_le_add le_rfl hAK)
    _ ≤ 18832 / globalQ +
        (44 / endpointQ +
          (ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
            ((2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
              3 * (((2 * B + 5 * B * Real.sqrt B) +
                (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) /
                  (R : ℝ) ^ 3))) := by
      exact add_le_add hG (add_le_add hE (add_le_add hA hK))
    _ = 18832 / globalQ + 44 / endpointQ +
        ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
        (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
        3 * (((2 * B + 5 * B * Real.sqrt B) +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 := by
      ring

/-- End-to-end stopped A2 assembly: the full numerical hypotheses simultaneously give the
explicit bad-event probability and strict shear survival on its complement. -/
theorem feedbackA2StoppedAssembly
    {n : ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n)
    (heta : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (hglobalQ : 0 < globalQ)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hbufferOne : 1 ≤ endpointBuffer amplitude n)
    (hendpointQ : 1 ≤ endpointQ) (hR : 0 < R) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2StoppedBadEvent
          (n := n) hlam0.le (by linarith)
            eta amplitude globalQ endpointQ B T R) ≤
        18832 / globalQ + 44 / endpointQ +
          ENNReal.toReal (2 * RelativeVC.regularityPolynomialBadBound n) +
          (2 * B + 5 * B * Real.sqrt B) / (R : ℝ) ^ 3 +
          3 * (((2 * B + 5 * B * Real.sqrt B) +
            (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) / (R : ℝ) ^ 3 ∧
      ∀ sample : FiniteSample n,
        sample ∈ feedbackA2StoppedGoodEvent
          hlam0.le (by linarith) eta amplitude globalQ endpointQ B T R →
        ∀ t : ℝ≥0, t < T →
          |safeFeedbackHeightAtElapsed
            hlam0.le (by linarith) B 0 t sample| < B / 8 := by
  constructor
  · exact finiteSampleLaw_real_feedbackA2StoppedBadEvent_le
      hlam0 hlam hn hB hBn heta hetaSmall hglobalQ hbuffer
        hfitSource hfitTarget hbufferOne hendpointQ hR
  · intro sample hgood t ht
    exact feedbackA2StoppedGoodEvent.abs_safeFeedbackHeightAtElapsed_lt
      hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood ht

end OTSelector
