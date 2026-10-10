import OTSelector.Limit.FeedbackConditionalCollapse

/-!
# Conditional environmental windows with reciprocal-scale error

All constants depend only on the feedback parameter. A finite monotone grid of the actual iid
cells controls both search intervals and every comparison between their cuts under the original
conditioned stationary roof law.
-/

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped ENNReal BigOperators Classical

namespace OTSelector.Limit
open OTSelector.PointProcess OTSelector.Matching
set_option maxHeartbeats 800000

/-- A deterministic mesh and index box large enough for the fixed-origin search windows. -/
structure FeedbackConditionalRegularityParameters (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) where
  mesh : ℝ
  horizon : ℕ
  mesh_pos : 0 < mesh
  hold_mesh : 64 * (1 + feedbackCellMean lam hlam0 hlam) ≤ mesh
  occupation_mesh :
    8 * feedbackCellMean lam hlam0 hlam *
      (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1) ≤
    feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1 * mesh
  horizon_large : 8 * mesh < (horizon : ℝ) * feedbackCellMean lam hlam0 hlam -
    (1 + feedbackCellMean lam hlam0 hlam)

/-- The deterministic scale conditions have actual parameter-only solutions. -/
theorem exists_feedbackConditionalRegularityParameters {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Nonempty (FeedbackConditionalRegularityParameters lam hlam0 hlam) := by
  let l := feedbackCellMean lam hlam0 hlam
  let z := feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1
  have hl : 0 < l := feedbackCellMean_pos hlam0 hlam
  have hz : 0 < z := feedbackCellRegularityMean_hold_pos hlam0 hlam _
  let R := 1 + 64 * (1 + l) + 8 * l * (1 + z) / z
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 64 * (1 + l) ≤ R := by
    have hpos : 0 ≤ 8 * l * (1 + z) / z := by positivity
    dsimp [R]
    linarith
  have hR2 : 8 * l * (1 + z) ≤ z * R := by
    have heq : z * (8 * l * (1 + z) / z) = 8 * l * (1 + z) := by
      field_simp
    dsimp [R]
    nlinarith [mul_pos hz hl]
  obtain ⟨M, hM⟩ := exists_nat_gt ((8 * R + (1 + l)) / l)
  have hM' : 8 * R < M * l - (1 + l) := by
    have := (div_lt_iff₀ hl).mp hM
    linarith
  exact ⟨⟨R, M, hR, hR1, hR2, hM'⟩⟩

namespace FeedbackConditionalRegularityParameters

variable {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2}

noncomputable def sourceCoefficient (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) : ℝ :=
  (2 * P.horizon * feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 2 +
    2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 2)) / P.mesh

noncomputable def rewardCoefficient (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) : ℝ :=
  (2 * P.horizon * feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 3 +
    2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 3)) / P.mesh

noncomputable def zeroCoefficient (_P : FeedbackConditionalRegularityParameters lam hlam0 hlam) : ℝ :=
  feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1 /
    (2 * feedbackCellMean lam hlam0 hlam)

noncomputable def tailCoefficient (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) : ℝ :=
  2 * P.mesh * feedbackCellPrefixTailConstant lam hlam0 hlam (quadraticUpperConstant lam) P.horizon

theorem zeroCoefficient_pos (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) :
    0 < P.zeroCoefficient :=
  div_pos (feedbackCellRegularityMean_hold_pos hlam0 hlam _) (by
    have := feedbackCellMean_pos hlam0 hlam
    positivity)

theorem horizon_pos (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) :
    0 < P.horizon := by
  have h := P.horizon_large
  have hR := P.mesh_pos
  have hl := feedbackCellMean_pos hlam0 hlam
  by_contra hM
  have heq : P.horizon = 0 := by omega
  rw [heq, Nat.cast_zero, zero_mul] at h
  linarith

/-- The chosen real mesh gives all deterministic losses required by the spatial geometry. -/
theorem mesh_bounds (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    {L : ℝ} (hLmesh : 2 * P.mesh ≤ L) (hLroof : 32 * feedbackCellMean lam hlam0 hlam ≤ L) :
    0 < ⌊L / P.mesh⌋₊ ∧
    (⌊L / P.mesh⌋₊ : ℝ) * P.mesh ≤ L ∧
    4 * L < ((P.horizon : ℝ) * feedbackCellMean lam hlam0 hlam -
      (1 + feedbackCellMean lam hlam0 hlam)) * ⌊L / P.mesh⌋₊ ∧
    feedbackCellMean lam hlam0 hlam +
      2 * (1 + feedbackCellMean lam hlam0 hlam) * ⌊L / P.mesh⌋₊ ≤ L / 16 ∧
    2 * feedbackCellMean lam hlam0 hlam +
      6 * (1 + feedbackCellMean lam hlam0 hlam) * ⌊L / P.mesh⌋₊ ≤ L / 4 ∧
    2 * feedbackCellMean lam hlam0 hlam *
      (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1) *
        ⌊L / P.mesh⌋₊ ≤
      feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1 * L / 4 := by
  let k := ⌊L / P.mesh⌋₊
  let l := feedbackCellMean lam hlam0 hlam
  let z := feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) 1
  have hl : 0 < l := feedbackCellMean_pos hlam0 hlam
  have hz : 0 < z := feedbackCellRegularityMean_hold_pos hlam0 hlam _
  have hx : 2 ≤ L / P.mesh := (le_div_iff₀ P.mesh_pos).mpr hLmesh
  have hk : 0 < k := Nat.floor_pos.mpr (by linarith)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkR : (k : ℝ) * P.mesh ≤ L :=
    (le_div_iff₀ P.mesh_pos).mp (Nat.floor_le (by linarith))
  have hhalf : L / P.mesh / 2 ≤ (k : ℝ) := by
    have := Nat.lt_floor_add_one (L / P.mesh)
    change L / P.mesh < (k : ℝ) + 1 at this
    linarith
  have hhalfR := mul_le_mul_of_nonneg_right hhalf P.mesh_pos.le
  have heq : L / P.mesh / 2 * P.mesh = L / 2 := by field_simp [P.mesh_pos.ne']
  rw [heq] at hhalfR
  have hroot := mul_lt_mul_of_pos_right P.horizon_large hk0
  have h64 := mul_le_mul_of_nonneg_right P.hold_mesh hk0.le
  have h8 := mul_le_mul_of_nonneg_right P.occupation_mesh hk0.le
  have hzL := mul_le_mul_of_nonneg_left hkR hz.le
  refine ⟨hk, hkR, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · dsimp [z] at hzL
    nlinarith

/-- A linear box sum is a linear spatial budget after dividing by the mesh size. -/
theorem sum_budget_le (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (r : Fin 4) {k : ℕ} {L : ℝ} (hkL : (k : ℝ) * P.mesh ≤ L) :
    (2 * P.horizon * feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r +
      2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r)) * k ≤
    ((2 * P.horizon * feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r +
      2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r)) /
      P.mesh) * L := by
  have hC : 0 ≤ quadraticUpperConstant lam := by unfold quadraticUpperConstant; positivity
  have hm := feedbackCellRegularityMean_nonneg hlam0 hlam hC r
  have hA : 0 ≤ 2 * P.horizon *
      feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r +
      2 * (1 + feedbackCellRegularityMean lam hlam0 hlam (quadraticUpperConstant lam) r) := by positivity
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ P.mesh_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hkL hA]

end FeedbackConditionalRegularityParameters

/-- The actual two search intervals and all comparison budgets at the observed origin. -/
def feedbackConditionalWindowRegular {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2}
    (P : FeedbackConditionalRegularityParameters lam hlam0 hlam) (h L : ℝ)
    (p : FeedbackCellSequence × ℝ) : Prop :=
  (∀ a ∈ Icc (p.2 + h / 2 - 2 * L) (p.2 + h / 2 - L),
    ∀ b ∈ Icc (p.2 + h / 2 + L) (p.2 + h / 2 + 2 * L),
      feedbackWindowSourceCount p.1 a b ≤ P.sourceCoefficient * L ∧
      feedbackWindowReward lam p.1 a b ≤ P.rewardCoefficient * L) ∧
  P.zeroCoefficient * L ≤ volume.real {x |
    x ∈ Icc (p.2 + h / 2 - 2 * L) (p.2 + h / 2 - L) ∧ FeedbackZeroCut p.1 x} ∧
  P.zeroCoefficient * L ≤ volume.real {x |
    x ∈ Icc (p.2 + h / 2 + L) (p.2 + h / 2 + 2 * L) ∧ FeedbackZeroCut p.1 x}

/-- The proved iid prefix event implies the required windows in the original observed environment. -/
theorem feedbackConditionalWindowRegular_of_prefix {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    {h L : ℝ} (hh : 0 ≤ h) (hLmesh : 2 * P.mesh ≤ L)
    (hLroof : 32 * feedbackCellMean lam hlam0 hlam ≤ L) (hLhold : 16 * (h + 1) ≤ L)
    (p : FeedbackCellSequence × ℝ)
    (hw : feedbackCellConfigurationGood p.1)
    (hc : feedbackCellConfigurationGood (feedbackCollapseZeroHold p))
    (hstart : ∀ j, (feedbackCollapseZeroHold p j 0).2.2 = 0)
    (hlen : feedbackCellLength (p.1 0) = feedbackCellLength (feedbackCollapseZeroHold p 0) +
      ((p.1 0 1).1 - p.2))
    (hB0 : h ≤ (p.1 0 1).1 - p.2) (hB1 : (p.1 0 1).1 - p.2 ≤ h + 1)
    (hgood : feedbackCellPrefixGood lam hlam0 hlam (quadraticUpperConstant lam) P.horizon
      ⌊L / P.mesh⌋₊ (feedbackCollapseZeroHold p)) :
    feedbackConditionalWindowRegular P h L p := by
  let k := ⌊L / P.mesh⌋₊
  let B := (p.1 0 1).1 - p.2
  let H := ((P.horizon : ℝ) * feedbackCellMean lam hlam0 hlam -
    (1 + feedbackCellMean lam hlam0 hlam)) * k
  obtain ⟨hk, hkR, hroot, hsmall, hmeshL, hmeshZ⟩ := P.mesh_bounds hLmesh hLroof
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith [P.mesh_pos]) hLmesh
  have hC : 0 ≤ quadraticUpperConstant lam := by unfold quadraticUpperConstant; positivity
  have hNk : 0 < P.horizon * k := Nat.mul_pos P.horizon_pos hk
  have hcell : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ L / 16 := by
    have hi := hgood.int_cell_le 0 (j := 0) (by omega) (by exact_mod_cast hNk)
    have hi' : feedbackCellLength (feedbackCollapseZeroHold p 0) ≤
        feedbackCellMean lam hlam0 hlam +
          2 * (1 + feedbackCellMean lam hlam0 hlam) * k := by
      simpa only [feedbackCellRegularityMean_length, feedbackCellRegularityObservable,
        Matrix.cons_val_zero] using hi
    exact hi'.trans hsmall
  have hu0 : 0 ≤ p.2 := by
    have hu := (hc.2 0).1 0
    rw [feedbackCollapseZeroHold_first_wait] at hu
    exact hu.le
  have hu1 : p.2 ≤ L / 16 := by
    have hu := feedbackCell_initial_hold_le_length hc 0
    rw [feedbackCollapseZeroHold_first_wait] at hu
    exact hu.trans hcell
  have hB : 0 ≤ B ∧ B ≤ L / 16 := by
    dsimp [B]
    constructor <;> linarith
  have hleft (a : ℝ) (ha : a ∈ Icc (p.2 + h / 2 - 2 * L) (p.2 + h / 2 - L)) :
      a < 0 ∧ |a| < H := by
    have hHa : 4 * L < H := hroot
    refine ⟨by linarith [ha.2], abs_lt.mpr ⟨?_, ?_⟩⟩ <;> linarith [ha.1, ha.2]
  have hright (b : ℝ) (hb : b ∈ Icc (p.2 + h / 2 + L) (p.2 + h / 2 + 2 * L)) :
      feedbackCellLength (feedbackCollapseZeroHold p 0) ≤ b - B ∧ |b - B| < H := by
    have hHa : 4 * L < H := hroot
    refine ⟨by linarith [hb.1, hB.2], abs_lt.mpr ⟨?_, ?_⟩⟩ <;>
      linarith [hb.1, hb.2, hB.1, hB.2]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    have hal := hleft a ha
    have hbr := hright b hb
    have hsource := feedbackCollapseZeroHold_windowSourceCount_le p hw.1 hc.1 hlen hgood
      hal.1 hbr.1 hal.2 hbr.2
    have hreward := hgood.windowReward_le hc.1 hal.2 hbr.2
    have heq := feedbackCollapseZeroHold_windowReward lam p hw.1 hc.1 hlen hal.1 hbr.1
    change feedbackWindowReward lam p.1 a (b - B + B) = _ at heq
    rw [sub_add_cancel] at heq
    change feedbackWindowSourceCount p.1 a (b - B + B) ≤ _ at hsource
    rw [sub_add_cancel] at hsource
    constructor
    · exact hsource.trans (P.sum_budget_le 2 hkR)
    · rw [heq]
      exact hreward.trans (P.sum_budget_le 3 hkR)
  · have ha := hleft (p.2 + h / 2 - 2 * L) ⟨le_refl _, by linarith⟩
    have hb := hleft (p.2 + h / 2 - L) ⟨by linarith, le_refl _⟩
    rw [feedbackCollapseZeroHold_zeroCut_volume_neg p hw.1 hc.1 hlen hb.1]
    exact hgood.zeroCut_occupation_linear hC hc hstart (by linarith) ha.2 hb.2 hmeshL hmeshZ
  · have ha := hright (p.2 + h / 2 + L) ⟨le_refl _, by linarith⟩
    have hb := hright (p.2 + h / 2 + 2 * L) ⟨by linarith, le_refl _⟩
    have heq := feedbackCollapseZeroHold_zeroCut_volume_pos p hw.1 hc.1 hlen
      (b := p.2 + h / 2 + 2 * L - B) ha.1
    change volume.real {x | x ∈ Icc (p.2 + h / 2 + L - B + B)
      (p.2 + h / 2 + 2 * L - B + B) ∧ FeedbackZeroCut p.1 x} = _ at heq
    simp only [sub_add_cancel] at heq
    rw [heq]
    exact hgood.zeroCut_occupation_linear hC hc hstart (by linarith) ha.2 hb.2 hmeshL hmeshZ

/-- Conditioning on the positive-mass residual band is a genuine probability measure. -/
theorem feedbackConditionalRoofLaw_isProbability {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (h : ℝ) (hh : 0 ≤ h) :
    IsProbabilityMeasure (feedbackConditionalRoofLaw lam hlam0 hlam h) := by
  constructor
  rw [feedbackConditionalRoofLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh).ne' (measure_ne_top _ _)

/-- Conditional environmental regularity in the original fixed-origin windows, with constants
independent of the residual-band location. The reciprocal error is summable on geometric scales. -/
theorem feedbackConditionalWindowRegular_bad_le {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    {h L : ℝ} (hh : 0 ≤ h) (hLmesh : 2 * P.mesh ≤ L)
    (hLroof : 32 * feedbackCellMean lam hlam0 hlam ≤ L) (hLhold : 16 * (h + 1) ≤ L) :
    (feedbackConditionalRoofLaw lam hlam0 hlam h).real
      {p | ¬feedbackConditionalWindowRegular P h L p} ≤ P.tailCoefficient / L := by
  let ν := feedbackConditionalRoofLaw lam hlam0 hlam h
  let : IsProbabilityMeasure ν := feedbackConditionalRoofLaw_isProbability hlam0 hlam h hh
  have hsub : ∀ᵐ p ∂ν, (¬feedbackConditionalWindowRegular P h L p) →
      ¬feedbackCellPrefixGood lam hlam0 hlam (quadraticUpperConstant lam) P.horizon
        ⌊L / P.mesh⌋₊ (feedbackCollapseZeroHold p) := by
    filter_upwards [feedbackConditionalRoofLaw_geometry hlam0 hlam h hh] with p hp
    intro hbad hgood
    exact hbad (feedbackConditionalWindowRegular_of_prefix P hh hLmesh hLroof hLhold p
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hgood)
  have hmeasure : ν.real {p | ¬feedbackConditionalWindowRegular P h L p} ≤
      ν.real {p | ¬feedbackCellPrefixGood lam hlam0 hlam (quadraticUpperConstant lam) P.horizon
        ⌊L / P.mesh⌋₊ (feedbackCollapseZeroHold p)} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hC : 0 ≤ quadraticUpperConstant lam := by unfold quadraticUpperConstant; positivity
  exact hmeasure.trans
    (feedbackStationaryRoofLaw_conditional_prefix_bad_le_real hlam0 hlam hC P.horizon
      P.mesh_pos hLmesh h hh)

/-- The weaker reciprocal error has the exact geometric-scale sum required by the bootstrap. -/
theorem hasSum_feedbackConditionalWindow_errors {lam : ℝ} {hlam0 : 0 < lam}
    {hlam : lam < 1 / 2} (P : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (L : ℝ) : HasSum (fun n : ℕ ↦ P.tailCoefficient / ((4 : ℝ) ^ n * L))
      (4 * P.tailCoefficient / (3 * L)) := by
  have hg := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left
    (P.tailCoefficient / L)
  have hf (n : ℕ) : P.tailCoefficient / L * (1 / 4 : ℝ) ^ n =
      P.tailCoefficient / ((4 : ℝ) ^ n * L) := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [hf] at hg
  convert! hg using 1
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end OTSelector.Limit
