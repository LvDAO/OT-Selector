import OTSelector.Matching.FeedbackConditionalEnergyTail

/-!
# An occupied long zero hold forces quadratic window energy

The actual residual-band conditioning produces an event-free physical interval. Any matching
edge crossing its midpoint spans the whole interval, forcing the window energy to exceed its
squared length. Two energy tails then give a common empty cut without independence.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000

namespace SpatialMatching
variable {S T : Type*}

/-- A single crossing edge contributes its full length to the actual energy sum. -/
theorem edge_length_le_crossingEnergy (M : SpatialMatching S T) (x : ℝ)
    (hfinite : {i | Crosses x (M.source i) (M.target (M.assignment i))}.Finite)
    (hne : ∀ i, M.source i ≠ x ∧ M.target (M.assignment i) ≠ x)
    (i : S) (hi : Crosses x (M.source i) (M.target (M.assignment i))) :
    |M.target (M.assignment i) - M.source i| ≤ M.crossingEnergy x := by
  let rows := hfinite.toFinset
  have hcontains : ∀ j, Crosses x (M.source j) (M.target (M.assignment j)) → j ∈ rows := by
    intro j hj
    exact hfinite.mem_toFinset.mpr hj
  rw [M.crossingEnergy_selected_eq rows x hne hcontains]
  let j : rows := ⟨i, hcontains i hi⟩
  have hsum := Finset.single_le_sum
    (s := (Finset.univ : Finset rows))
    (f := fun k : rows ↦ |(crossingSign (M.source k) (M.target (M.assignment k)) x : ℝ)| *
      (1 + |M.target (M.assignment k) - M.source k|))
    (fun k _ ↦ mul_nonneg (abs_nonneg _) (by positivity)) (Finset.mem_univ j)
  have hsign : |(crossingSign (M.source i) (M.target (M.assignment i)) x : ℝ)| = 1 := by
    rw [abs_crossingSign_non_event (hne i).1 (hne i).2, ite_eq_left hi]
  change |(crossingSign (M.source i) (M.target (M.assignment i)) x : ℝ)| *
    (1 + |M.target (M.assignment i) - M.source i|) ≤ _ at hsum
  rw [hsign, one_mul] at hsum
  exact (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans hsum

/-- A midpoint crossing in an event-free interval crosses every interior cut and spans its length. -/
theorem crosses_gap (M : SpatialMatching S T) {a b cut : ℝ} (hcut : cut ∈ Ioo a b)
    (hgap : ∀ i, M.source i ∉ Ioo a b ∧ M.target (M.assignment i) ∉ Ioo a b)
    {i : S} (hi : Crosses cut (M.source i) (M.target (M.assignment i))) :
    b - a ≤ |M.target (M.assignment i) - M.source i| ∧
      ∀ x ∈ Ioo a b, Crosses x (M.source i) (M.target (M.assignment i)) := by
  rcases hi with hi | hi
  · have hs : M.source i ≤ a := by
      by_contra hn
      exact (hgap i).1 ⟨lt_of_not_ge hn, hi.1.trans hcut.2⟩
    have ht : b ≤ M.target (M.assignment i) := by
      by_contra hn
      exact (hgap i).2 ⟨hcut.1.trans hi.2, lt_of_not_ge hn⟩
    constructor
    · exact (by linarith : b - a ≤ M.target (M.assignment i) - M.source i).trans (le_abs_self _)
    · intro x hx
      exact Or.inl ⟨hs.trans_lt hx.1, hx.2.trans_le ht⟩
  · have ht : M.target (M.assignment i) ≤ a := by
      by_contra hn
      exact (hgap i).2 ⟨lt_of_not_ge hn, hi.1.trans hcut.2⟩
    have hs : b ≤ M.source i := by
      by_contra hn
      exact (hgap i).1 ⟨hcut.1.trans hi.2, lt_of_not_ge hn⟩
    constructor
    · exact (by linarith : b - a ≤ -(M.target (M.assignment i) - M.source i)).trans
        (neg_le_abs _)
    · intro x hx
      exact Or.inr ⟨ht.trans_lt hx.1, hx.2.trans_le hs⟩

/-- An occupied event-free gap costs at least its squared length in any surrounding window. -/
theorem gap_sq_le_integral_crossingEnergy (M : SpatialMatching S T)
    {a b cut : ℝ} {I : Set ℝ} (hcut : cut ∈ Ioo a b)
    (hgap : ∀ i, M.source i ∉ Ioo a b ∧ M.target (M.assignment i) ∉ Ioo a b)
    (hfinite : ∀ x, {i | Crosses x (M.source i) (M.target (M.assignment i))}.Finite)
    (hI : Ioo a b ⊆ I) (hint : IntegrableOn M.crossingEnergy I)
    {i : S} (hi : Crosses cut (M.source i) (M.target (M.assignment i))) :
    (b - a) ^ 2 ≤ ∫ x in I, M.crossingEnergy x := by
  have hb := M.crosses_gap hcut hgap hi
  have hpoint (x : ℝ) (hx : x ∈ Ioo a b) : b - a ≤ M.crossingEnergy x := by
    have hne : ∀ j, M.source j ≠ x ∧ M.target (M.assignment j) ≠ x := by
      intro j
      exact ⟨fun he ↦ (hgap j).1 (he.symm ▸ hx), fun he ↦ (hgap j).2 (he.symm ▸ hx)⟩
    exact hb.1.trans (M.edge_length_le_crossingEnergy x (hfinite x) hne i (hb.2 x hx))
  calc
    (b - a) ^ 2 = ∫ _x in Ioo a b, (b - a) := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ]
      change _ = volume.real (Ioo a b) • (b - a)
      rw [Real.volume_real_Ioo_of_le (hcut.1.trans hcut.2).le, smul_eq_mul]
      ring
    _ ≤ ∫ x in Ioo a b, M.crossingEnergy x :=
      setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hI)
        measurableSet_Ioo hpoint
    _ ≤ ∫ x in I, M.crossingEnergy x :=
      setIntegral_mono_set hint (ae_of_all _ M.crossingEnergy_nonneg) (ae_of_all _ hI)

end SpatialMatching

/-- Every actual event lies outside the initial zero hold of cell zero. -/
theorem feedbackCellEventPoint_notMem_initialHold {w : FeedbackCellSequence}
    {direction : ℤ} {i : ℤ × ℕ} (hi : feedbackCellEventActive w direction i) :
    (feedbackCellEventPoint w i).1 ∉ Ioo 0 (w 0 1).1 := by
  have hw := hi.1
  have hbound := feedbackCellEventPoint_mem_cell hi
  have hmono := (strictMono_feedbackCellRoot hw.1.1).monotone
  by_cases hj : i.1 < 0
  · have hroot := hmono (show i.1 + 1 ≤ 0 by omega)
    rw [feedbackCellRoot_zero] at hroot
    intro hx
    linarith [hbound.2, hx.1]
  · have hj0 : 0 ≤ i.1 := le_of_not_gt hj
    have hroot := hmono hj0
    rw [feedbackCellRoot_zero] at hroot
    rcases eq_or_lt_of_le hj0 with heq | hjpos
    · have hclock := (feedbackCellClock_strictMono (w i.1) (hw.2 i.1).1).monotone
        (show 1 ≤ i.2 + 1 by omega)
      have hfirst : feedbackCellClock (w i.1) 1 = (w i.1 1).1 := by
        simpa using feedbackCellClock_succ (w i.1) 0
      rw [hfirst, ← heq] at hclock
      intro hx
      dsimp only [feedbackCellEventPoint] at hx
      rw [← heq, feedbackCellRoot_zero, zero_add] at hx
      linarith [hx.2]
    · have hroot1 := hmono (show 1 ≤ i.1 by omega)
      have hhold := feedbackCell_initial_hold_le_length hw 0
      have heq : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
        simpa using feedbackCellRoot_add_one w 0
      rw [heq] at hroot1
      intro hx
      linarith [hx.2, hbound.1]

/-- The actual conditioned roof contains a source- and target-free interval of length `h`. -/
theorem feedbackConditionalRoofLaw_no_events {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) :
    ∀ᵐ p ∂feedbackConditionalRoofLaw lam hlam0 hlam h,
      ∀ direction : ℤ, ∀ i : FeedbackEventLabel p.1 direction,
        (feedbackCellEventPoint p.1 i).1 ∉ Ioo p.2 (p.2 + h) := by
  have hage : ∀ᵐ p ∂feedbackStationaryRoofLaw lam hlam0 hlam, 0 ≤ p.2 := by
    apply Measure.ae_smul_measure
    have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
        0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} := by
      exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd
          (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
    exact (ae_restrict_mem hroof).mono fun _ hp ↦ hp.1
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hage,
    ae_restrict_mem (measurableSet_feedbackRoofHoldBand lam h)] with p hp hband
  intro direction i hx
  exact feedbackCellEventPoint_notMem_initialHold i.property
    ⟨hp.trans_lt hx.1, by linarith [hband.1.1, hx.2]⟩

/-- Sufficiently small actual window energy makes the middle of the distinguished long gap
an empty cut for that matching. -/
theorem feedbackWindowEnergy_empty_cut (p : FeedbackCellSequence × ℝ)
    (assignment : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1))
    (hfinite : ∀ cut, {i : FeedbackEventLabel p.1 1 |
      Crosses cut (feedbackCellEventPoint p.1 i).1
        (feedbackCellEventPoint p.1 (assignment i)).1}.Finite)
    {h L r : ℝ} (hh : 0 < h) (hL : h ≤ L) (hsmall : r * L < h ^ 2)
    (hgap : ∀ direction : ℤ, ∀ i : FeedbackEventLabel p.1 direction,
      (feedbackCellEventPoint p.1 i).1 ∉ Ioo p.2 (p.2 + h))
    (henergy : feedbackWindowEnergy p assignment h L ≤ r * L) :
    ∀ i : FeedbackEventLabel p.1 1, ¬Crosses (p.2 + h / 2) (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (assignment i)).1 := by
  intro i hi
  have hbound := (feedbackLabelMatching p.1 assignment).gap_sq_le_integral_crossingEnergy
    (show p.2 + h / 2 ∈ Ioo p.2 (p.2 + h) by constructor <;> linarith)
    (fun j ↦ ⟨hgap 1 j, hgap (-1) (assignment j)⟩) hfinite
    (I := feedbackEnergyInterval p h L) (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
    (integrableOn_feedbackLabelEnergy p assignment hfinite h L) hi
  have heq : (p.2 + h - p.2) ^ 2 = h ^ 2 := by ring
  rw [heq] at hbound
  exact (not_le_of_gt hsmall) (hbound.trans henergy)

/-- The simultaneous bootstrap and empty-gap scale conditions have actual parameter-only
solutions. In particular the common-cut error can be made smaller than one. -/
theorem exists_feedbackConditionalEnergyGap_scales {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) :
    ∃ h L r : ℝ, 0 < h ∧ 0 < L ∧ 0 < r ∧
      2 * P.mesh ≤ L ∧ 32 * feedbackCellMean lam hlam0 hlam ≤ L ∧
      16 * (h + 1) ≤ L ∧ (16 / P.zeroCoefficient) * r ≤ L ∧
      2 * (feedbackComparisonCoefficient P / 2 + 1 +
        (3 / 2) * feedbackComparisonCoefficient P / quadraticLowerConstant' lam) ≤ r ∧
      (12 * quadraticUpperConstant lam / quadraticLowerConstant' lam) *
        ((16 / P.zeroCoefficient) * r) ^ 3 ≤ r * L / 2 ∧
      r * L < h ^ 2 ∧ 8 * P.tailCoefficient / (3 * L) < 1 := by
  let A := 2 * (feedbackComparisonCoefficient P / 2 + 1 +
    (3 / 2) * feedbackComparisonCoefficient P / quadraticLowerConstant' lam)
  let r := 1 + max 0 A
  have hr : 0 < r := by dsimp [r]; positivity
  have hAr : A ≤ r := by dsimp [r]; linarith [le_max_right 0 A]
  let theta := (16 / P.zeroCoefficient) * r
  let B := (12 * quadraticUpperConstant lam / quadraticLowerConstant' lam) * theta ^ 3
  let h := 1 + |2 * P.mesh| + |32 * feedbackCellMean lam hlam0 hlam| +
    |theta| + |2 * B / r| + |8 * P.tailCoefficient / 3| + 64 * r
  have hh1 : 1 < h := by
    dsimp [h]
    linarith [abs_nonneg (2 * P.mesh), abs_nonneg (32 * feedbackCellMean lam hlam0 hlam),
      abs_nonneg theta, abs_nonneg (2 * B / r), abs_nonneg (8 * P.tailCoefficient / 3)]
  have hmesh : 2 * P.mesh < h := by
    have := le_abs_self (2 * P.mesh)
    dsimp [h]
    have := abs_nonneg (32 * feedbackCellMean lam hlam0 hlam)
    have := abs_nonneg theta
    have := abs_nonneg (2 * B / r)
    have := abs_nonneg (8 * P.tailCoefficient / 3)
    linarith
  have hroof : 32 * feedbackCellMean lam hlam0 hlam < h := by
    have := le_abs_self (32 * feedbackCellMean lam hlam0 hlam)
    dsimp [h]
    have := abs_nonneg (2 * P.mesh)
    have := abs_nonneg theta
    have := abs_nonneg (2 * B / r)
    have := abs_nonneg (8 * P.tailCoefficient / 3)
    linarith
  have ht : theta < h := by
    have := le_abs_self theta
    dsimp [h]
    have := abs_nonneg (2 * P.mesh)
    have := abs_nonneg (32 * feedbackCellMean lam hlam0 hlam)
    have := abs_nonneg (2 * B / r)
    have := abs_nonneg (8 * P.tailCoefficient / 3)
    linarith
  have hB : 2 * B / r < h := by
    have := le_abs_self (2 * B / r)
    dsimp [h]
    have := abs_nonneg (2 * P.mesh)
    have := abs_nonneg (32 * feedbackCellMean lam hlam0 hlam)
    have := abs_nonneg theta
    have := abs_nonneg (8 * P.tailCoefficient / 3)
    linarith
  have htail : 8 * P.tailCoefficient / 3 < h := by
    have := le_abs_self (8 * P.tailCoefficient / 3)
    dsimp [h]
    have := abs_nonneg (2 * P.mesh)
    have := abs_nonneg (32 * feedbackCellMean lam hlam0 hlam)
    have := abs_nonneg theta
    have := abs_nonneg (2 * B / r)
    linarith
  have hrh : 64 * r < h := by
    dsimp [h]
    linarith [abs_nonneg (2 * P.mesh), abs_nonneg (32 * feedbackCellMean lam hlam0 hlam),
      abs_nonneg theta, abs_nonneg (2 * B / r), abs_nonneg (8 * P.tailCoefficient / 3)]
  let L := 16 * (h + 1)
  have hL : 0 < L := by dsimp [L]; linarith
  have hhL : h < L := by dsimp [L]; linarith
  refine ⟨h, L, r, by linarith, hL, hr, hmesh.le.trans hhL.le,
    hroof.le.trans hhL.le, le_rfl, ht.le.trans hhL.le, hAr, ?_, ?_, ?_⟩
  · have hBr := (div_lt_iff₀ hr).mp hB
    change B ≤ r * L / 2
    nlinarith [mul_le_mul_of_nonneg_left hhL.le hr.le]
  · dsimp [L]
    nlinarith [mul_pos (by linarith : 0 < h) (sub_pos.mpr hrh)]
  · apply (div_lt_one (by positivity : 0 < 3 * L)).mpr
    linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two actual matchings have a common empty midpoint except on the sum of their energy tails.
No independence of the matchings is required. -/
theorem feedbackConditional_commonEmptyCut_bad_le {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : Ω → FeedbackCellSequence × ℝ} (hp : Measurable p)
    (hmap : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam)
    (assignment : Fin 2 → (ω : Ω) →
      FeedbackEventLabel (p ω).1 1 ≃ FeedbackEventLabel (p ω).1 (-1))
    (hadmissible : ∀ k, ∀ᵐ ω ∂μ, FeedbackMatchingAdmissible (p ω) (assignment k ω) lam)
    {h L r : ℝ} (Cenergy : Fin 2 → ℝ) (hh : 0 < h) (hL : 0 < L) (hr : 0 < r)
    (hLmesh : 2 * P.mesh ≤ L) (hLroof : 32 * feedbackCellMean lam hlam0 hlam ≤ L)
    (hLhold : 16 * (h + 1) ≤ L)
    (htheta : (16 / P.zeroCoefficient) * r ≤ L)
    (hlevel : 2 * (feedbackComparisonCoefficient P / 2 + 1 +
      (3 / 2) * feedbackComparisonCoefficient P / quadraticLowerConstant' lam) ≤ r)
    (hcubic : (12 * quadraticUpperConstant lam / quadraticLowerConstant' lam) *
      ((16 / P.zeroCoefficient) * r) ^ 3 ≤ r * L / 2)
    (hsmall : r * L < h ^ 2)
    (henergyInt : ∀ k R, 0 < R →
      Integrable (fun ω ↦ feedbackWindowEnergy (p ω) (assignment k ω) h R) μ)
    (hmean : ∀ k R, 0 < R →
      (∫ ω, feedbackWindowEnergy (p ω) (assignment k ω) h R ∂μ) ≤ Cenergy k * R) :
    (ProbabilityTheory.cond μ (p ⁻¹' feedbackRoofHoldBand lam h)).real
      {ω | ¬∀ k : Fin 2, ∀ i : FeedbackEventLabel (p ω).1 1,
        ¬Crosses ((p ω).2 + h / 2) (feedbackCellEventPoint (p ω).1 i).1
          (feedbackCellEventPoint (p ω).1 (assignment k ω i)).1} ≤
      8 * P.tailCoefficient / (3 * L) := by
  let ν := ProbabilityTheory.cond μ (p ⁻¹' feedbackRoofHoldBand lam h)
  have hA0 : μ (p ⁻¹' feedbackRoofHoldBand lam h) ≠ 0 := by
    rw [← Measure.map_apply hp (measurableSet_feedbackRoofHoldBand lam h), hmap]
    exact (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh.le).ne'
  let : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hA0
  have hνmap := feedbackConditionalRoofLaw_map_joint μ hp hmap h
  have hgap : ∀ᵐ ω ∂ν, ∀ d : ℤ, ∀ i : FeedbackEventLabel (p ω).1 d,
      (feedbackCellEventPoint (p ω).1 i).1 ∉ Ioo (p ω).2 ((p ω).2 + h) := by
    have hg := feedbackConditionalRoofLaw_no_events hlam0 hlam h
    rw [← hνmap] at hg
    exact ae_of_ae_map hp.aemeasurable hg
  let bad (k : Fin 2) : Set Ω :=
    {ω | r * L < feedbackWindowEnergy (p ω) (assignment k ω) h L}
  have htail (k : Fin 2) : ν.real (bad k) ≤ 4 * P.tailCoefficient / (3 * L) :=
    feedbackConditionalEnergy_tail_le hlam8 P μ hp hmap (assignment k) (hadmissible k)
      hh.le hL hr hLmesh hLroof hLhold htheta hlevel hcubic (henergyInt k) (hmean k)
  have hsub : ∀ᵐ ω ∂ν,
      (¬∀ k : Fin 2, ∀ i : FeedbackEventLabel (p ω).1 1,
        ¬Crosses ((p ω).2 + h / 2) (feedbackCellEventPoint (p ω).1 i).1
          (feedbackCellEventPoint (p ω).1 (assignment k ω i)).1) →
      ω ∈ bad 0 ∪ bad 1 := by
    have ha : ∀ᵐ ω ∂ν, ∀ k : Fin 2,
        FeedbackMatchingAdmissible (p ω) (assignment k ω) lam := by
      rw [ae_all_iff]
      exact fun k ↦ ProbabilityTheory.cond_absolutelyContinuous.ae_le (hadmissible k)
    filter_upwards [hgap, ha] with ω hg had
    intro hbad
    by_contra hn
    have h0 : feedbackWindowEnergy (p ω) (assignment 0 ω) h L ≤ r * L :=
      le_of_not_gt (fun h ↦ hn (Or.inl h))
    have h1 : feedbackWindowEnergy (p ω) (assignment 1 ω) h L ≤ r * L :=
      le_of_not_gt (fun h ↦ hn (Or.inr h))
    apply hbad
    intro k
    have hE : feedbackWindowEnergy (p ω) (assignment k ω) h L ≤ r * L := by
      fin_cases k
      · exact h0
      · exact h1
    exact feedbackWindowEnergy_empty_cut (p ω) (assignment k ω) (had k).finite_crossings
      hh (by linarith) hsmall hg hE
  calc
    _ ≤ ν.real (bad 0 ∪ bad 1) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ν.real (bad 0) + ν.real (bad 1) := measureReal_union_le _ _
    _ ≤ 4 * P.tailCoefficient / (3 * L) + 4 * P.tailCoefficient / (3 * L) :=
      add_le_add (htail 0) (htail 1)
    _ = 8 * P.tailCoefficient / (3 * L) := by ring

/-- The actual conditioned joint law assigns positive probability to a common empty cut for
any two admissible matchings with unconditional linear energy means. All scale parameters are
chosen inside the proof from the proved environmental constants. -/
theorem exists_feedbackConditional_commonEmptyCut {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : Ω → FeedbackCellSequence × ℝ} (hp : Measurable p)
    (hmap : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam)
    (assignment : Fin 2 → (ω : Ω) →
      FeedbackEventLabel (p ω).1 1 ≃ FeedbackEventLabel (p ω).1 (-1))
    (hadmissible : ∀ k, ∀ᵐ ω ∂μ, FeedbackMatchingAdmissible (p ω) (assignment k ω) lam)
    (Cenergy : Fin 2 → ℝ)
    (henergyInt : ∀ k h R, 0 < R →
      Integrable (fun ω ↦ feedbackWindowEnergy (p ω) (assignment k ω) h R) μ)
    (hmean : ∀ k h R, 0 < R →
      (∫ ω, feedbackWindowEnergy (p ω) (assignment k ω) h R ∂μ) ≤ Cenergy k * R) :
    ∃ h > 0, 0 < (ProbabilityTheory.cond μ (p ⁻¹' feedbackRoofHoldBand lam h)).real
      {ω | ∀ k : Fin 2, ∀ i : FeedbackEventLabel (p ω).1 1,
        ¬Crosses ((p ω).2 + h / 2) (feedbackCellEventPoint (p ω).1 i).1
          (feedbackCellEventPoint (p ω).1 (assignment k ω i)).1} := by
  obtain ⟨h, L, r, hh, hL, hr, hmesh, hroof, hhold, htheta, hlevel, hcubic, hsmall, htail⟩ :=
    exists_feedbackConditionalEnergyGap_scales P
  refine ⟨h, hh, ?_⟩
  let ν := ProbabilityTheory.cond μ (p ⁻¹' feedbackRoofHoldBand lam h)
  have hA0 : μ (p ⁻¹' feedbackRoofHoldBand lam h) ≠ 0 := by
    rw [← Measure.map_apply hp (measurableSet_feedbackRoofHoldBand lam h), hmap]
    exact (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh.le).ne'
  let : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hA0
  let good := {ω | ∀ k : Fin 2, ∀ i : FeedbackEventLabel (p ω).1 1,
    ¬Crosses ((p ω).2 + h / 2) (feedbackCellEventPoint (p ω).1 i).1
      (feedbackCellEventPoint (p ω).1 (assignment k ω i)).1}
  have hbad : ν.real goodᶜ < 1 :=
    (feedbackConditional_commonEmptyCut_bad_le hlam8 P μ hp hmap assignment hadmissible
      Cenergy hh hL hr hmesh hroof hhold htheta hlevel hcubic hsmall
      (fun k R hR ↦ henergyInt k h R hR) (fun k R hR ↦ hmean k h R hR)).trans_lt htail
  have hsum : 1 ≤ ν.real goodᶜ + ν.real good := by
    simpa [Measure.real] using (measureReal_union_le (μ := ν) goodᶜ good)
  change 0 < ν.real good
  linarith

end OTSelector.Matching
