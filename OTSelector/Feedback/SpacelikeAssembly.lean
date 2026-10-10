import OTSelector.Feedback.CutMass
import OTSelector.Feedback.VCAsymptotic
import OTSelector.Feedback.EndpointAsymptotic

/-!
# Deterministic A2 assembly

This file contains the algebraic layer used by the spacelike argument.  It deliberately does not
introduce a feedback path, a stopping time, or a probability assumption beyond those already
needed by the exact cut-mass and envelope theorems.  The stochastic inputs are passed as
pointwise bounds, so the conclusions below are genuine deterministic inequalities and event
inclusions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

/-! ## The three-term deterministic inequality -/

/-- The absolute value of a parameter controlled by an exact three-term identity. -/
theorem abs_half_parameter_le_of_sub_sub
    {p a b k A B C : ℝ}
    (hidentity : 2 * p = a - b - k)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hk : |k| ≤ C) :
    |p| ≤ (A + B + C) / 2 := by
  have htri : |a - b - k| ≤ |a| + |b| + |k| := by
    calc
      |a - b - k| ≤ |a - b| + |k| := abs_sub _ _
      _ ≤ (|a| + |b|) + |k| := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (add_le_add_right (abs_sub a b) |k|)
      _ = |a| + |b| + |k| := by ring
  have habs : 2 * |p| = |a - b - k| := by
    calc
      2 * |p| = |2 * p| := by rw [abs_mul]; norm_num
      _ = |a - b - k| := congrArg abs hidentity
  nlinarith

/-- The exact rank-strip identity (1.29) gives a deterministic shear-height bound. -/
theorem abs_shear_parameter_le_of_exact_cut_identity
    {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark) {p x : ℝ}
    (hsource0 : ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ)))
    (hsourceN : ∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n)
    (htarget0 : ∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ)))
    (htargetN : ∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n)
    {sourceBound targetBound currentBound : ℝ}
    (hsourceBound :
      |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) source p x| ≤ sourceBound)
    (htargetBound :
      |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) target p x| ≤ targetBound)
    (hcurrentBound : |feedbackRankDiscrepancy source target p x| ≤ currentBound) :
    |p| ≤ (sourceBound + targetBound + currentBound) / 2 := by
  have hidentity := two_mul_eq_sourceDefect_sub_targetDefect_sub_feedbackRankDiscrepancy
    hn source target hsource0 hsourceN htarget0 htargetN
  exact abs_half_parameter_le_of_sub_sub hidentity hsourceBound htargetBound hcurrentBound

/-- The global VC envelopes supply the source and target bounds in (1.29). -/
theorem abs_shear_parameter_le_of_global_cut_envelopes
    {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark) {p x : ℝ}
    (hsource0 : ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ)))
    (hsourceN : ∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n)
    (htarget0 : ∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ)))
    (htargetN : ∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n)
    {sourceEnvelope targetEnvelope currentBound : ℝ}
    (hsourceEnvelope :
      globalSourceCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) source ≤ sourceEnvelope)
    (htargetEnvelope :
      globalTargetCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) target ≤ targetEnvelope)
    (hcurrentBound : |feedbackRankDiscrepancy source target p x| ≤ currentBound) :
    |p| ≤ (sourceEnvelope + targetEnvelope + currentBound) / 2 := by
  apply abs_shear_parameter_le_of_exact_cut_identity hn source target hsource0 hsourceN
    htarget0 htargetN
  · exact (abs_sourceCutDefect_le_globalSourceCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark)) source p x).trans hsourceEnvelope
  · exact (abs_targetCutDefect_le_globalTargetCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark)) target p x).trans htargetEnvelope
  · exact hcurrentBound

/-! ## First-hit component inclusions -/

/-- At a first hit, an exact three-term identity forces one component above any thresholds whose
sum is strictly smaller than the hit height. -/
theorem first_hit_component_exceeds_of_exact_identity
    {p a b k hit sourceThreshold targetThreshold currentThreshold : ℝ}
    (hidentity : 2 * p = a - b - k)
    (hhit : 2 * |p| = hit)
    (hthreshold :
      sourceThreshold + targetThreshold + currentThreshold < hit) :
    sourceThreshold < |a| ∨ targetThreshold < |b| ∨ currentThreshold < |k| := by
  by_contra hnot
  have ha : |a| ≤ sourceThreshold :=
    le_of_not_gt (fun h ↦ hnot (Or.inl h))
  have hb : |b| ≤ targetThreshold :=
    le_of_not_gt (fun h ↦ hnot (Or.inr (Or.inl h)))
  have hk : |k| ≤ currentThreshold :=
    le_of_not_gt (fun h ↦ hnot (Or.inr (Or.inr h)))
  have htri : |a - b - k| ≤ |a| + |b| + |k| := by
    calc
      |a - b - k| ≤ |a - b| + |k| := abs_sub _ _
      _ ≤ (|a| + |b|) + |k| := by
        simpa [add_assoc, add_left_comm, add_comm] using
          (add_le_add_right (abs_sub a b) |k|)
      _ = |a| + |b| + |k| := by ring
  have habs : 2 * |p| = |a - b - k| := by
    calc
      2 * |p| = |2 * p| := by rw [abs_mul]; norm_num
      _ = |a - b - k| := congrArg abs hidentity
  nlinarith

/-- A set-level form of the first-hit trichotomy.  This is purely logical and needs no
measurability of the displayed functions. -/
theorem first_hit_event_subset_component_events
    {Ω : Type*} (hitEvent : Set Ω)
    (a b k p : Ω → ℝ) (hit sourceThreshold targetThreshold currentThreshold : ℝ)
    (hidentity : ∀ ω, 2 * p ω = a ω - b ω - k ω)
    (hhit : ∀ ω ∈ hitEvent, 2 * |p ω| = hit)
    (hthreshold :
      sourceThreshold + targetThreshold + currentThreshold < hit) :
    hitEvent ⊆
      {ω | sourceThreshold < |a ω|} ∪
        {ω | targetThreshold < |b ω|} ∪
          {ω | currentThreshold < |k ω|} := by
  intro ω hω
  have hcomponent := first_hit_component_exceeds_of_exact_identity
    (hidentity ω) (hhit ω hω) hthreshold
  rcases hcomponent with ha | hb | hk
  · exact Set.mem_union_left (x := ω) _
      (Set.mem_union_left (x := ω) _ (show ω ∈ {ω | sourceThreshold < |a ω|} from ha))
  · exact Set.mem_union_left (x := ω) _
      (Set.mem_union_right (x := ω) _ (show ω ∈ {ω | targetThreshold < |b ω|} from hb))
  · exact Set.mem_union_right (x := ω) _ (show ω ∈ {ω | currentThreshold < |k ω|} from hk)

/-- First-hit component inclusion for the exact rank-strip identity (1.29). -/
theorem first_hit_cut_component_exceeds
    {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark) {p x hit : ℝ}
    (hsource0 : ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ)))
    (hsourceN : ∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n)
    (htarget0 : ∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ)))
    (htargetN : ∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n)
    (hhit : 2 * |p| = hit)
    {sourceThreshold targetThreshold currentThreshold : ℝ}
    (hthreshold :
      sourceThreshold + targetThreshold + currentThreshold < hit) :
    sourceThreshold <
        |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) source p x| ∨
      targetThreshold <
        |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) target p x| ∨
      currentThreshold < |feedbackRankDiscrepancy source target p x| := by
  have hidentity := two_mul_eq_sourceDefect_sub_targetDefect_sub_feedbackRankDiscrepancy
    hn source target hsource0 hsourceN htarget0 htargetN
  exact first_hit_component_exceeds_of_exact_identity hidentity hhit hthreshold

/-! ## Endpoint section geometry -/

/-- The source affine sections at `x = n - B` remain inside the rank strip on the shear window. -/
theorem endpoint_source_section_bounds
    {n : ℕ} {buffer p : ℝ}
    (hbuffer : 0 ≤ buffer) (hfit : 9 * buffer / 8 ≤ (n : ℝ))
    (hp : |p| ≤ buffer / 8) :
    (∀ u : UnitMark, 0 ≤ (n : ℝ) - buffer - p * (1 - (u : ℝ))) ∧
      (∀ u : UnitMark, (n : ℝ) - buffer - p * (1 - (u : ℝ)) ≤ n) := by
  have hpabs : 0 ≤ buffer / 8 := by positivity
  constructor
  · intro u
    have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
    have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
    have hterm : |p * (1 - (u : ℝ))| ≤ buffer / 8 := by
      rw [abs_mul, abs_of_nonneg hu0]
      calc
        |p| * (1 - (u : ℝ)) ≤ (buffer / 8) * (1 - (u : ℝ)) :=
          mul_le_mul_of_nonneg_right hp hu0
        _ ≤ (buffer / 8) * 1 := mul_le_mul_of_nonneg_left hu1 hpabs
        _ = buffer / 8 := by ring
    have hlow : -(buffer / 8) ≤ p * (1 - (u : ℝ)) :=
      neg_le_of_abs_le hterm
    have hbase : 0 ≤ (n : ℝ) - 9 * buffer / 8 := by
      nlinarith [hfit]
    have hbase' : 0 ≤ (n : ℝ) - buffer - buffer / 8 := by
      nlinarith [hbase]
    have hupp : p * (1 - (u : ℝ)) ≤ buffer / 8 := le_abs_self _ |>.trans hterm
    nlinarith [hbase', hupp]
  · intro u
    have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
    have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
    have hterm : |p * (1 - (u : ℝ))| ≤ buffer / 8 := by
      rw [abs_mul, abs_of_nonneg hu0]
      calc
        |p| * (1 - (u : ℝ)) ≤ (buffer / 8) * (1 - (u : ℝ)) :=
          mul_le_mul_of_nonneg_right hp hu0
        _ ≤ (buffer / 8) * 1 := mul_le_mul_of_nonneg_left hu1 hpabs
        _ = buffer / 8 := by ring
    have hlow : -(buffer / 8) ≤ p * (1 - (u : ℝ)) :=
      neg_le_of_abs_le hterm
    nlinarith [hbuffer, hlow]

/-- The target affine sections at `x = n - B` remain inside the rank strip on the shear window. -/
theorem endpoint_target_section_bounds
    {n : ℕ} {buffer p : ℝ}
    (hbuffer : 0 ≤ buffer) (hfit : 5 * buffer / 4 ≤ (n : ℝ))
    (hp : |p| ≤ buffer / 8) :
    (∀ v : UnitMark, 0 ≤ (n : ℝ) - buffer + p * (1 + (v : ℝ))) ∧
      (∀ v : UnitMark, (n : ℝ) - buffer + p * (1 + (v : ℝ)) ≤ n) := by
  have hpabs : 0 ≤ buffer / 8 := by positivity
  constructor
  · intro v
    have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
    have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
    have hterm : |p * (1 + (v : ℝ))| ≤ buffer / 4 := by
      rw [abs_mul, abs_of_nonneg hv0]
      calc
        |p| * (1 + (v : ℝ)) ≤ (buffer / 8) * (1 + (v : ℝ)) :=
          mul_le_mul_of_nonneg_right hp hv0
        _ ≤ (buffer / 8) * 2 := mul_le_mul_of_nonneg_left hv2 hpabs
        _ = buffer / 4 := by ring
    have hlow : -(buffer / 4) ≤ p * (1 + (v : ℝ)) :=
      neg_le_of_abs_le hterm
    have hbase : 0 ≤ (n : ℝ) - 5 * buffer / 4 := by
      nlinarith [hfit]
    have hbase' : 0 ≤ (n : ℝ) - buffer - buffer / 4 := by
      nlinarith [hbase]
    nlinarith [hbase', hlow]
  · intro v
    have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
    have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
    have hterm : |p * (1 + (v : ℝ))| ≤ buffer / 4 := by
      rw [abs_mul, abs_of_nonneg hv0]
      calc
        |p| * (1 + (v : ℝ)) ≤ (buffer / 8) * (1 + (v : ℝ)) :=
          mul_le_mul_of_nonneg_right hp hv0
        _ ≤ (buffer / 8) * 2 := mul_le_mul_of_nonneg_left hv2 hpabs
        _ = buffer / 4 := by ring
    have hupp : p * (1 + (v : ℝ)) ≤ buffer / 4 := le_abs_self _ |>.trans hterm
    nlinarith [hbuffer, hupp]

/-! ## Endpoint height and first-hit consequences -/

/-- The endpoint version of the deterministic height bound. -/
theorem abs_endpoint_shear_parameter_le_of_cut_bounds
    {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark) {buffer p : ℝ}
    (hbuffer : 0 ≤ buffer) (hfitSource : 9 * buffer / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * buffer / 4 ≤ (n : ℝ))
    (hp : |p| ≤ buffer / 8)
    {sourceBound targetBound currentBound : ℝ}
    (hsourceBound :
      |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) source p
          ((n : ℝ) - buffer)| ≤ sourceBound)
    (htargetBound :
      |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) target p
          ((n : ℝ) - buffer)| ≤ targetBound)
    (hcurrentBound :
      |feedbackRankDiscrepancy source target p ((n : ℝ) - buffer)| ≤ currentBound) :
    |p| ≤ (sourceBound + targetBound + currentBound) / 2 := by
  have hsource := endpoint_source_section_bounds hbuffer hfitSource hp
  have htarget := endpoint_target_section_bounds hbuffer hfitTarget hp
  exact abs_shear_parameter_le_of_exact_cut_identity hn source target
    hsource.1 hsource.2 htarget.1 htarget.2 hsourceBound htargetBound hcurrentBound

/-- Endpoint defects controlled by the nested source/target envelopes imply a height bound. -/
theorem abs_endpoint_shear_parameter_le_of_endpoint_good
    {amplitude q : ℝ} {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark)
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    {p : ℝ} (hp : |p| ≤ endpointBuffer amplitude n / 8)
    (hsourceGood : source ∉ sourceEndpointBadEvent amplitude q n)
    (htargetGood : target ∉ targetEndpointBadEvent amplitude q n)
    {currentBound : ℝ}
    (hcurrentBound :
      |feedbackRankDiscrepancy source target p
          ((n : ℝ) - endpointBuffer amplitude n)| ≤ currentBound) :
    |p| ≤ endpointEnvelopeCoefficient q * endpointScale amplitude n + currentBound / 2 := by
  have hsource := sourceEndpointValue_lt_envelope hn hbuffer hfitSource hB hq hp hsourceGood
  have htarget := targetEndpointValue_lt_envelope hn hbuffer hfitTarget hB hq hp htargetGood
  have hbound := abs_endpoint_shear_parameter_le_of_cut_bounds hn source target
    hbuffer.le hfitSource hfitTarget hp hsource.le htarget.le hcurrentBound
  nlinarith

/-- Endpoint first-hit trichotomy for source defect, target defect, and current. -/
theorem first_hit_endpoint_component_exceeds
    {amplitude : ℝ} {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark)
    (hbuffer : 0 ≤ endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    {p hit sourceThreshold targetThreshold currentThreshold : ℝ}
    (hp : |p| ≤ endpointBuffer amplitude n / 8)
    (hhit : 2 * |p| = hit)
    (hthreshold :
      sourceThreshold + targetThreshold + currentThreshold < hit) :
    sourceThreshold <
        |sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) source p
            ((n : ℝ) - endpointBuffer amplitude n)| ∨
      targetThreshold <
        |targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) target p
            ((n : ℝ) - endpointBuffer amplitude n)| ∨
      currentThreshold <
        |feedbackRankDiscrepancy source target p
            ((n : ℝ) - endpointBuffer amplitude n)| := by
  have hsource := endpoint_source_section_bounds hbuffer hfitSource hp
  have htarget := endpoint_target_section_bounds hbuffer hfitTarget hp
  exact first_hit_cut_component_exceeds hn source target hsource.1 hsource.2
    htarget.1 htarget.2 hhit hthreshold

end OTSelector.RelativeVC
