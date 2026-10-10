import OTSelector.Feedback.Regularity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-sample peeling bounds for half-space regularity

This module instantiates the balanced count-scale Bernstein bound with the numerical threshold
from (1.10).  A shell of count mass `a` uses population cap `a / m`, observed-count cap `a`,
and threshold `C * (sqrt (a * log n) + log n)`.  The source and target classes share the same
abstract shell construction and are combined into one finite bad event.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

private theorem ncard_restrictions_le_sum_choose_of_vcdim_le {X : Type*}
    (C : ConceptClass X Bool) (S : Finset X) (d : ℕ)
    (hvc : VCDim X C ≤ (d : WithTop ℕ)) :
    ({f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c x = f x} : Set (↥S → Bool)).ncard ≤
      ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i := by
  classical
  set R := {f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c x = f x}
  have hR_fin : R.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  rw [Set.ncard_eq_toFinset_card']
  set Rfin := R.toFinset
  set A := Rfin.image (fun f ↦ Finset.univ.filter (fun x ↦ f x = true)) with hAdef
  have hinj : Function.Injective
      (fun f : ↥S → Bool ↦ Finset.univ.filter (fun x ↦ f x = true)) := by
    intro f g hfg
    funext x
    have hx := Finset.ext_iff.mp hfg x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    cases hf : f x <;> cases hg : g x <;> simp_all
  have hcard : Rfin.card = A.card := by
    rw [hAdef]
    exact (Finset.card_image_of_injective _ hinj).symm
  have hshatterer : A.card ≤ A.shatterer.card := Finset.card_le_card_shatterer A
  have hsauer := @Finset.card_shatterer_le_sum_vcDim ↥S _ A
  have hvcdimA : A.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le
    intro T hT
    have hTshat : A.Shatters T := Finset.mem_shatterer.mp hT
    set Tval := T.map ⟨Subtype.val, Subtype.val_injective⟩ with hTvaldef
    have hTval_shat : Shatters X C Tval := by
      intro g
      let g' : ↥S → Bool := fun x ↦
        if hx : (x : X) ∈ Tval then g ⟨x, hx⟩ else false
      let t : Finset ↥S := T.filter (fun x ↦ g' x = true)
      have htT : t ⊆ T := Finset.filter_subset _ _
      obtain ⟨B, hBA, hTB⟩ := hTshat htT
      simp only [hAdef, Finset.mem_image] at hBA
      obtain ⟨f, hfR, rfl⟩ := hBA
      rw [Set.mem_toFinset] at hfR
      obtain ⟨c, hcC, hcf⟩ := hfR
      refine ⟨c, hcC, ?_⟩
      intro ⟨y, hyTval⟩
      have hy := hyTval
      rw [hTvaldef, Finset.mem_map] at hy
      obtain ⟨⟨y', hy'S⟩, hy'T, hy'eq⟩ := hy
      simp only [Function.Embedding.coeFn_mk] at hy'eq
      subst hy'eq
      have hcf_y := hcf ⟨y', hy'S⟩
      have hf_iff_g : f ⟨y', hy'S⟩ = true ↔ g' ⟨y', hy'S⟩ = true := by
        have hf : (⟨y', hy'S⟩ : ↥S) ∈
            T ∩ Finset.univ.filter (fun x ↦ f x = true) ↔
            f ⟨y', hy'S⟩ = true := by simp [hy'T]
        have hg : (⟨y', hy'S⟩ : ↥S) ∈ t ↔ g' ⟨y', hy'S⟩ = true := by
          simp [t, hy'T]
        simp_all
      have hg'_eq : g' ⟨y', hy'S⟩ = g ⟨y', hyTval⟩ := by
        simp only [g', dite_eq_left hyTval]
      simp_all
    have hTcard : Tval.card = T.card := Finset.card_map _
    have hTbound : (Tval.card : WithTop ℕ) ≤ d := by
      calc
        (Tval.card : WithTop ℕ) ≤ VCDim X C := by
          exact le_iSup_of_le Tval (le_iSup_of_le hTval_shat le_rfl)
        _ ≤ d := hvc
    exact hTcard ▸ WithTop.coe_le_coe.mp hTbound
  have hcardS : Fintype.card ↥S = S.card := Fintype.card_coe S
  calc
    R.toFinset.card = A.card := hcard
    _ ≤ A.shatterer.card := hshatterer
    _ ≤ ∑ k ∈ Finset.Iic A.vcDim, (Fintype.card ↥S).choose k := hsauer
    _ = ∑ k ∈ Finset.Iic A.vcDim, S.card.choose k := by rw [hcardS]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.Iic_subset_Iic.mpr hvcdimA
    _ = ∑ k ∈ Finset.range (d + 1), S.card.choose k := by
      rw [Nat.range_succ_eq_Iic]

/-- Sauer--Shelah with an upper bound on VC dimension rather than an exact dimension. -/
theorem growthFunction_le_sum_choose_of_vcdim_le {X : Type*}
    (C : ConceptClass X Bool) (d q : ℕ) (hvc : VCDim X C ≤ (d : WithTop ℕ)) :
    GrowthFunction X C q ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose q i := by
  unfold GrowthFunction
  apply csSup_le'
  intro r hr
  obtain ⟨⟨S, hSq⟩, rfl⟩ := hr
  change ({f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c x = f x} : Set _).ncard ≤ _
  calc
    ({f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c x = f x} : Set _).ncard
        ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose S.card i :=
      ncard_restrictions_le_sum_choose_of_vcdim_le C S d hvc
    _ = ∑ i ∈ Finset.range (d + 1), Nat.choose q i := by rw [hSq]

theorem growthFunction_le_cube_of_vcdim_le_three {X : Type*}
    (C : ConceptClass X Bool) (q : ℕ) (hq : 3 ≤ q)
    (hvc : VCDim X C ≤ (3 : WithTop ℕ)) :
    (GrowthFunction X C q : ℝ) ≤ (q : ℝ) ^ 3 := by
  have hgrowth := growthFunction_le_sum_choose_of_vcdim_le C 3 q hvc
  have hsauer := sum_choose_le_exp_pow 3 q (by norm_num) hq
  have hbase : Real.exp 1 * (q : ℝ) / 3 ≤ q := by
    have hq_nonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hexp : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    nlinarith
  calc
    (GrowthFunction X C q : ℝ) ≤
        (∑ i ∈ Finset.range 4, Nat.choose q i : ℕ) := by exact_mod_cast hgrowth
    _ = ∑ i ∈ Finset.range 4, (Nat.choose q i : ℝ) := by push_cast; rfl
    _ ≤ (Real.exp 1 * (q : ℝ) / 3) ^ 3 := hsauer
    _ ≤ (q : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hbase 3

theorem sourceCut_growth_cube (q : ℕ) (hq : 3 ≤ q) :
    (GrowthFunction (ℝ × UnitMark) sourceCutClass q : ℝ) ≤ (q : ℝ) ^ 3 :=
  growthFunction_le_cube_of_vcdim_le_three sourceCutClass q hq
    vcdim_sourceCutClass_le_three

theorem targetCut_growth_cube (q : ℕ) (hq : 3 ≤ q) :
    (GrowthFunction (ℝ × UnitMark) targetCutClass q : ℝ) ≤ (q : ℝ) ^ 3 :=
  growthFunction_le_cube_of_vcdim_le_three targetCutClass q hq
    vcdim_targetCutClass_le_three

theorem sourceCutComplement_growth_cube (q : ℕ) (hq : 3 ≤ q) :
    (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass q : ℝ) ≤ (q : ℝ) ^ 3 :=
  growthFunction_le_cube_of_vcdim_le_three sourceCutComplementClass q hq
    vcdim_sourceCutComplementClass_le_three

theorem targetCutComplement_growth_cube (q : ℕ) (hq : 3 ≤ q) :
    (GrowthFunction (ℝ × UnitMark) targetCutComplementClass q : ℝ) ≤ (q : ℝ) ^ 3 :=
  growthFunction_le_cube_of_vcdim_le_three targetCutComplementClass q hq
    vcdim_targetCutComplementClass_le_three

/-- The count-scale threshold appearing in (1.10), with an explicit constant. -/
noncomputable def regularityCountThreshold (n : ℕ) (constant massCount : ℝ) : ℝ :=
  constant * (Real.sqrt (massCount * Real.log n) + Real.log n)

/-- Canonical dyadic count cap for shell `k`. -/
noncomputable def dyadicMassCount (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- A balanced relative-VC shell in count scale. -/
noncomputable def regularityShellEvent
    (P : Measure (ℝ × UnitMark)) (C : ConceptClass (ℝ × UnitMark) Bool)
    (m n : ℕ) (constant massCount : ℝ) : Set (Fin m → ℝ × UnitMark) :=
  balancedLocalizedCutCountEvent P C
    (regularityCountThreshold n constant massCount) (massCount / m) massCount

/-- The explicit Bernstein upper bound attached to one balanced count shell. -/
noncomputable def regularityShellTail
    (C Ccompl : ConceptClass (ℝ × UnitMark) Bool)
    (m n : ℕ) (constant massCount : ℝ) : ENNReal :=
  let threshold := regularityCountThreshold n constant massCount
  2 * ENNReal.ofReal
      (2 * (GrowthFunction (ℝ × UnitMark) C (2 * m) : ℝ) *
        Real.exp (-((Real.sqrt m * (threshold / Real.sqrt m) / 2) ^ 2) /
          (2 * (massCount + (m : ℝ) * (massCount / m) +
            Real.sqrt m * ((threshold / Real.sqrt m) / 2))))) +
    2 * ENNReal.ofReal
      (2 * (GrowthFunction (ℝ × UnitMark) Ccompl (2 * m) : ℝ) *
        Real.exp (-((Real.sqrt m * (threshold / Real.sqrt m) / 2) ^ 2) /
          (2 * (massCount + (m : ℝ) * (massCount / m) +
            Real.sqrt m * ((threshold / Real.sqrt m) / 2)))))

theorem regularityCountThreshold_pos
    {n : ℕ} (hn : 1 < n) {constant massCount : ℝ}
    (hconstant : 0 < constant) :
    0 < regularityCountThreshold n constant massCount := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold regularityCountThreshold
  exact mul_pos hconstant (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hlog)

theorem regularityCountThreshold_mono_mass
    {n : ℕ} (hn : 1 ≤ n) {constant massCount massCap : ℝ}
    (hconstant : 0 ≤ constant) (hmass : massCount ≤ massCap) :
    regularityCountThreshold n constant massCount ≤
      regularityCountThreshold n constant massCap := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold regularityCountThreshold
  apply mul_le_mul_of_nonneg_left _ hconstant
  exact add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmass hlog)) le_rfl

@[simp] theorem dyadicMassCount_pos (k : ℕ) : 0 < dyadicMassCount k := by
  simp [dyadicMassCount]

@[simp] theorem dyadicMassCount_nonneg (k : ℕ) : 0 ≤ dyadicMassCount k :=
  (dyadicMassCount_pos k).le

private theorem regularity_variance_cap_pos
    {m n : ℕ} (hm : 0 < m) (hn : 1 < n)
    {constant massCount : ℝ} (hconstant : 0 < constant) (hmass : 0 ≤ massCount) :
    0 < massCount + (m : ℝ) * (massCount / m) +
      Real.sqrt m * ((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) := by
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have hthreshold := regularityCountThreshold_pos (massCount := massCount) hn hconstant
  have hfirst : 0 ≤ massCount + (m : ℝ) * (massCount / m) := by
    exact add_nonneg hmass (mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg hmass (Nat.cast_nonneg _)))
  have hlast : 0 < Real.sqrt (m : ℝ) *
      ((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) := by
    positivity
  linarith

private theorem normalized_ghost_ratio_eq
    {m : ℕ} (hm : 0 < m) {threshold massCount : ℝ}
    (hdenom : massCount + threshold / 2 ≠ 0) :
    (((threshold / Real.sqrt m) / 2) ^ 2) /
        (4 * (massCount / m + ((threshold / Real.sqrt m) / 2) / Real.sqrt m)) =
      threshold ^ 2 / (16 * (massCount + threshold / 2)) := by
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have hsqrt_ne : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hsqrt_sq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hdenom_two : 2 * massCount + threshold ≠ 0 := by
    intro hzero
    apply hdenom
    linarith
  have hactual :
      Real.sqrt (m : ℝ) ^ 2 * 2 * massCount + threshold * (m : ℝ) ≠ 0 := by
    calc
      Real.sqrt (m : ℝ) ^ 2 * 2 * massCount + threshold * (m : ℝ) =
          (m : ℝ) * (2 * massCount + threshold) := by rw [hsqrt_sq]; ring
      _ ≠ 0 := mul_ne_zero hm_ne hdenom_two
  field_simp [hsqrt_ne, hm_ne, hdenom, hdenom_two, hactual]
  rw [hsqrt_sq]
  ring

private theorem normalized_count_exponent_eq
    {m : ℕ} (hm : 0 < m) {threshold massCount : ℝ} :
    ((Real.sqrt m * (threshold / Real.sqrt m) / 2) ^ 2) /
        (2 * (massCount + (m : ℝ) * (massCount / m) +
          Real.sqrt m * ((threshold / Real.sqrt m) / 2))) =
      (threshold / 2) ^ 2 / (2 * (2 * massCount + threshold / 2)) := by
  have hsqrt_ne : Real.sqrt (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hsqrt_cancel : Real.sqrt (m : ℝ) * (threshold / Real.sqrt m) = threshold := by
    field_simp
  have hm_cancel : (m : ℝ) * (massCount / m) = massCount := by
    field_simp
  have hsqrt_half : Real.sqrt (m : ℝ) * ((threshold / Real.sqrt m) / 2) =
      threshold / 2 := by
    field_simp
  rw [hsqrt_cancel, hm_cancel, hsqrt_half]
  ring

/-- At constant `64`, the count-scale Bernstein exponent is at least `16 log n`, uniformly in
the shell mass. -/
theorem regularity_count_exponent_sixtyFour
    (m n : ℕ) (hm : 0 < m) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    16 * Real.log n ≤
      ((Real.sqrt m *
        (regularityCountThreshold n 64 massCount / Real.sqrt m) / 2) ^ 2) /
        (2 * (massCount + (m : ℝ) * (massCount / m) +
          Real.sqrt m *
            ((regularityCountThreshold n 64 massCount / Real.sqrt m) / 2))) := by
  have hn_one : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn_one)
  let s := Real.sqrt (massCount * Real.log n)
  let threshold := regularityCountThreshold n 64 massCount
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = massCount * Real.log n := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hmass hlog.le)
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    exact regularityCountThreshold_pos (massCount := massCount) hn_one (by norm_num)
  have hdenom : 0 < 2 * (2 * massCount + threshold / 2) := by positivity
  rw [normalized_count_exponent_eq hm]
  rw [le_div_iff₀ hdenom]
  dsimp [threshold, regularityCountThreshold]
  dsimp [s] at hs_nonneg hs_sq ⊢
  nlinarith

theorem regularity_count_exp_sixtyFour_le
    (m n : ℕ) (hm : 0 < m) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    Real.exp
        (-((Real.sqrt m *
          (regularityCountThreshold n 64 massCount / Real.sqrt m) / 2) ^ 2) /
          (2 * (massCount + (m : ℝ) * (massCount / m) +
            Real.sqrt m *
              ((regularityCountThreshold n 64 massCount / Real.sqrt m) / 2)))) ≤
      1 / (n : ℝ) ^ 16 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hexponent := regularity_count_exponent_sixtyFour m n hm hn massCount hmass
  calc
    Real.exp
        (-((Real.sqrt m *
          (regularityCountThreshold n 64 massCount / Real.sqrt m) / 2) ^ 2) /
          (2 * (massCount + (m : ℝ) * (massCount / m) +
            Real.sqrt m *
              ((regularityCountThreshold n 64 massCount / Real.sqrt m) / 2))))
        ≤ Real.exp (16 * (-Real.log n)) := by
          apply Real.exp_le_exp.mpr
          simpa only [neg_div, mul_neg] using neg_le_neg hexponent
    _ = (Real.exp (-Real.log n)) ^ 16 := Real.exp_nat_mul _ _
    _ = 1 / (n : ℝ) ^ 16 := by
      rw [Real.exp_neg, Real.exp_log hn_pos]
      simp [one_div, inv_pow]

/-- Polynomial envelope for one source or target shell at sample size `n`. -/
noncomputable def regularityPolynomialShellBound (n : ℕ) : ENNReal :=
  4 * ENNReal.ofReal
    (2 * (((2 * n : ℕ) : ℝ) ^ 3) * (1 / (n : ℝ) ^ 16))

theorem regularityShellTail_sixtyFour_le
    (C Ccompl : ConceptClass (ℝ × UnitMark) Bool)
    (n : ℕ) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount)
    (hC : (GrowthFunction (ℝ × UnitMark) C (2 * n) : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3)
    (hCcompl : (GrowthFunction (ℝ × UnitMark) Ccompl (2 * n) : ℝ) ≤
      ((2 * n : ℕ) : ℝ) ^ 3) :
    regularityShellTail C Ccompl n n 64 massCount ≤ regularityPolynomialShellBound n := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hexp := regularity_count_exp_sixtyFour_le n n hn_pos hn massCount hmass
  let exponent : ℝ :=
    Real.exp
      (-((Real.sqrt n *
        (regularityCountThreshold n 64 massCount / Real.sqrt n) / 2) ^ 2) /
        (2 * (massCount + (n : ℝ) * (massCount / n) +
          Real.sqrt n *
            ((regularityCountThreshold n 64 massCount / Real.sqrt n) / 2))))
  let base : ℝ := 2 * (((2 * n : ℕ) : ℝ) ^ 3) * (1 / (n : ℝ) ^ 16)
  have hexponent : exponent ≤ 1 / (n : ℝ) ^ 16 := hexp
  have hexponent_nonneg : 0 ≤ exponent := by dsimp [exponent]; positivity
  have hbase_nonneg : 0 ≤ 1 / (n : ℝ) ^ 16 := by positivity
  have hC_real :
      2 * (GrowthFunction (ℝ × UnitMark) C (2 * n) : ℝ) * exponent ≤ base := by
    dsimp [base]
    calc
      2 * (GrowthFunction (ℝ × UnitMark) C (2 * n) : ℝ) * exponent
          ≤ 2 * (((2 * n : ℕ) : ℝ) ^ 3) * exponent := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hC (by norm_num)) hexponent_nonneg
      _ ≤ 2 * (((2 * n : ℕ) : ℝ) ^ 3) * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_left hexponent
          (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
  have hCcompl_real :
      2 * (GrowthFunction (ℝ × UnitMark) Ccompl (2 * n) : ℝ) * exponent ≤ base := by
    dsimp [base]
    calc
      2 * (GrowthFunction (ℝ × UnitMark) Ccompl (2 * n) : ℝ) * exponent
          ≤ 2 * (((2 * n : ℕ) : ℝ) ^ 3) * exponent := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hCcompl (by norm_num)) hexponent_nonneg
      _ ≤ 2 * (((2 * n : ℕ) : ℝ) ^ 3) * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_left hexponent
          (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
  unfold regularityShellTail regularityPolynomialShellBound
  dsimp only
  change 2 * ENNReal.ofReal
      (2 * (GrowthFunction (ℝ × UnitMark) C (2 * n) : ℝ) * exponent) +
    2 * ENNReal.ofReal
      (2 * (GrowthFunction (ℝ × UnitMark) Ccompl (2 * n) : ℝ) * exponent) ≤
    4 * ENNReal.ofReal base
  calc
    2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) C (2 * n) : ℝ) * exponent) +
      2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) Ccompl (2 * n) : ℝ) * exponent)
        ≤ 2 * ENNReal.ofReal base + 2 * ENNReal.ofReal base :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hC_real) (by positivity))
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hCcompl_real) (by positivity))
    _ = 4 * ENNReal.ofReal base := by ring

theorem sourceCut_regularityShellTail_sixtyFour_le
    (n : ℕ) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    regularityShellTail sourceCutClass sourceCutComplementClass n n 64 massCount ≤
      regularityPolynomialShellBound n := by
  apply regularityShellTail_sixtyFour_le _ _ n hn massCount hmass
  · exact sourceCut_growth_cube (2 * n) (by omega)
  · exact sourceCutComplement_growth_cube (2 * n) (by omega)

theorem targetCut_regularityShellTail_sixtyFour_le
    (n : ℕ) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    regularityShellTail targetCutClass targetCutComplementClass n n 64 massCount ≤
      regularityPolynomialShellBound n := by
  apply regularityShellTail_sixtyFour_le _ _ n hn massCount hmass
  · exact targetCut_growth_cube (2 * n) (by omega)
  · exact targetCutComplement_growth_cube (2 * n) (by omega)

/-- The ghost-sample smallness condition is automatic at the explicit constant `64` once
`n ≥ 4`.  Thus the numerical peeling theorems below need no probabilistic witness input. -/
theorem regularity_ghost_bernstein_sixtyFour
    (m n : ℕ) (hm : 0 < m) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n 64 massCount / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m +
              ((regularityCountThreshold n 64 massCount / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤
      (1 : ENNReal) / 2 := by
  have hn_one : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn_one)
  let s := Real.sqrt (massCount * Real.log n)
  let threshold := regularityCountThreshold n 64 massCount
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = massCount * Real.log n := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hmass hlog.le)
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    exact regularityCountThreshold_pos (massCount := massCount) hn_one (by norm_num)
  have hdenom_pos : 0 < massCount + threshold / 2 := by positivity
  have hquad : 16 * Real.log n * (massCount + threshold / 2) ≤ threshold ^ 2 := by
    dsimp [threshold, regularityCountThreshold]
    dsimp [s] at hs_nonneg hs_sq ⊢
    nlinarith
  have hratio : Real.log n ≤ threshold ^ 2 / (16 * (massCount + threshold / 2)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hdenom_pos)]
    nlinarith
  have hratio_eq := normalized_ghost_ratio_eq hm (threshold := threshold)
    (massCount := massCount) (ne_of_gt hdenom_pos)
  have hratio_normalized :
      Real.log n ≤
        (((threshold / Real.sqrt m) / 2) ^ 2) /
          (4 * (massCount / m + ((threshold / Real.sqrt m) / 2) / Real.sqrt m)) := by
    rw [hratio_eq]
    exact hratio
  have hexp :
      Real.exp
          (-(((threshold / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m + ((threshold / Real.sqrt m) / 2) / Real.sqrt m))) ≤
        1 / (n : ℝ) := by
    calc
      Real.exp
          (-(((threshold / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m + ((threshold / Real.sqrt m) / 2) / Real.sqrt m)))
          ≤ Real.exp (-Real.log n) := by
            apply Real.exp_le_exp.mpr
            simpa only [neg_div] using neg_le_neg hratio_normalized
      _ = 1 / (n : ℝ) := by simp [Real.exp_neg, Real.exp_log hn_pos, one_div]
  have htwo_div : (2 : ℝ) * (1 / (n : ℝ)) ≤ 1 / 2 := by
    have hn_four : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : (2 : ℝ) / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hn_pos]
      nlinarith
    simpa [div_eq_mul_inv, one_div] using hdiv
  have hreal :
      2 * Real.exp
          (-(((threshold / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m + ((threshold / Real.sqrt m) / 2) / Real.sqrt m))) ≤
        1 / 2 :=
    (mul_le_mul_of_nonneg_left hexp (by norm_num)).trans htwo_div
  have hofReal := ENNReal.ofReal_le_ofReal hreal
  simpa [threshold] using hofReal

/-- Outside a shell bad event, every cut satisfying that shell's two mass caps obeys the
count-scale (1.10) threshold. -/
theorem centeredErrorSum_lt_regularityCountThreshold_of_not_mem
    (P : Measure (ℝ × UnitMark)) (C : ConceptClass (ℝ × UnitMark) Bool)
    {m n : ℕ} {constant massCount : ℝ} {xs : Fin m → ℝ × UnitMark}
    (hxs : xs ∉ regularityShellEvent P C m n constant massCount)
    {h : Concept (ℝ × UnitMark) Bool} (hhC : h ∈ C)
    (htrue : balancedMass P (errorSet h falseCutTarget) ≤ massCount / m)
    (hsample : populationOrientedSampleErrorSum P h xs ≤ massCount) :
    |centeredErrorSum P h falseCutTarget xs| <
      regularityCountThreshold n constant massCount := by
  rw [regularityShellEvent] at hxs
  by_contra hnot
  exact hxs ⟨h, hhC, htrue, le_of_not_gt hnot, hsample⟩

/-- The observed count selected by the smaller population orientation differs from the expected
smaller count by exactly the absolute centered error.  This is the deterministic identity used
to bootstrap an observed-count shell back to the population count in (1.10). -/
theorem abs_populationOrientedSampleErrorSum_sub_expected_balancedMass
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (C : ConceptClass (ℝ × UnitMark) Bool) {m : ℕ}
    (h : Concept (ℝ × UnitMark) Bool) (hhC : h ∈ C) (hh : Measurable h)
    (xs : Fin m → ℝ × UnitMark) :
    |populationOrientedSampleErrorSum P h xs -
        (m : ℝ) * balancedMass P (errorSet h falseCutTarget)| =
      |centeredErrorSum P h falseCutTarget xs| := by
  obtain ⟨g, _, hmass, hcentered, hsample⟩ :=
    exists_balanced_orientation P C h hhC hh xs
  rw [← hsample, ← hmass, ← hcentered]
  rfl

/-- Deterministic Bernstein bootstrap: a bound involving the observed cap `expected + defect`
implies a bound involving only the expected count.  This is the numerical step that removes the
observed-count localization after peeling. -/
theorem selfBoundedBernstein_of_expected_add
    {defect expected logTerm constant : ℝ}
    (hdefect : 0 ≤ defect) (hexpected : 0 ≤ expected) (hlog : 0 ≤ logTerm)
    (hconstant : 0 ≤ constant)
    (hbound : defect ≤
      constant * (Real.sqrt ((expected + defect) * logTerm) + logTerm)) :
    defect ≤
      2 * constant * Real.sqrt (expected * logTerm) +
        (constant ^ 2 + 2 * constant) * logTerm := by
  have hexpected_log : 0 ≤ expected * logTerm := mul_nonneg hexpected hlog
  have hdefect_log : 0 ≤ defect * logTerm := mul_nonneg hdefect hlog
  have hsqrt_add :
      Real.sqrt ((expected + defect) * logTerm) ≤
        Real.sqrt (expected * logTerm) + Real.sqrt (defect * logTerm) := by
    rw [show (expected + defect) * logTerm =
      expected * logTerm + defect * logTerm by ring]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hexpected_sq := Real.sq_sqrt hexpected_log
      have hdefect_sq := Real.sq_sqrt hdefect_log
      nlinarith [mul_nonneg (Real.sqrt_nonneg (expected * logTerm))
        (Real.sqrt_nonneg (defect * logTerm))]
  have hscaled_sqrt := mul_le_mul_of_nonneg_left hsqrt_add hconstant
  have hyoung :
      constant * Real.sqrt (defect * logTerm) ≤
        defect / 2 + constant ^ 2 * logTerm / 2 := by
    rw [Real.sqrt_mul hdefect]
    have hdefect_sq := Real.sq_sqrt hdefect
    have hlog_sq := Real.sq_sqrt hlog
    nlinarith [sq_nonneg (Real.sqrt defect - constant * Real.sqrt logTerm)]
  nlinarith

/-- The same bootstrap with one enlarged constant, matching the exact shape of (1.10). -/
theorem selfBoundedBernstein_uniform_constant
    {defect expected logTerm constant : ℝ}
    (hdefect : 0 ≤ defect) (hexpected : 0 ≤ expected) (hlog : 0 ≤ logTerm)
    (hconstant : 0 ≤ constant)
    (hbound : defect ≤
      constant * (Real.sqrt ((expected + defect) * logTerm) + logTerm)) :
    defect ≤ (constant ^ 2 + 2 * constant) *
      (Real.sqrt (expected * logTerm) + logTerm) := by
  have hbase := selfBoundedBernstein_of_expected_add hdefect hexpected hlog hconstant hbound
  have hsqrt : 0 ≤ Real.sqrt (expected * logTerm) := Real.sqrt_nonneg _
  have hextra : 0 ≤ constant ^ 2 * Real.sqrt (expected * logTerm) :=
    mul_nonneg (sq_nonneg _) hsqrt
  nlinarith

/-- Abstract source/target bootstrap in the paper's population-count notation. -/
theorem centeredErrorSum_expected_regularity_of_selfBounded
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (h : Concept (ℝ × UnitMark) Bool) (xs : Fin m → ℝ × UnitMark)
    {logTerm constant : ℝ} (hlog : 0 ≤ logTerm) (hconstant : 0 ≤ constant)
    (hbound : |centeredErrorSum P h falseCutTarget xs| ≤
      constant *
        (Real.sqrt (((m : ℝ) * balancedMass P (errorSet h falseCutTarget) +
          |centeredErrorSum P h falseCutTarget xs|) * logTerm) + logTerm)) :
    |centeredErrorSum P h falseCutTarget xs| ≤
      (constant ^ 2 + 2 * constant) *
        (Real.sqrt (((m : ℝ) * balancedMass P (errorSet h falseCutTarget)) * logTerm) +
          logTerm) := by
  exact selfBoundedBernstein_uniform_constant (abs_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (balancedMass_nonneg P _)) hlog hconstant hbound

/-- One source half-space shell with the numerical (1.10) threshold. -/
theorem sourceCut_regularity_shell_tail
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 0 < m) (hn : 1 < n)
    (constant massCount : ℝ) (hconstant : 0 < constant) (hmass : 0 ≤ massCount)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m +
              ((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤ (1 : ENNReal) / 2) :
    Measure.pi (fun _ : Fin m ↦ P)
        (regularityShellEvent P sourceCutClass m n constant massCount) ≤
      regularityShellTail sourceCutClass sourceCutComplementClass m n constant massCount := by
  simpa [regularityShellEvent, regularityShellTail] using
    sourceCut_balanced_count_bernstein P m hm
      (regularityCountThreshold n constant massCount) (massCount / m) massCount
      (regularityCountThreshold_pos hn hconstant) hghostBernstein
      (regularity_variance_cap_pos hm hn hconstant hmass)

/-- One target half-space shell with the same numerical threshold. -/
theorem targetCut_regularity_shell_tail
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 0 < m) (hn : 1 < n)
    (constant massCount : ℝ) (hconstant : 0 < constant) (hmass : 0 ≤ massCount)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) ^ 2) /
            (4 * (massCount / m +
              ((regularityCountThreshold n constant massCount / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤ (1 : ENNReal) / 2) :
    Measure.pi (fun _ : Fin m ↦ P)
        (regularityShellEvent P targetCutClass m n constant massCount) ≤
      regularityShellTail targetCutClass targetCutComplementClass m n constant massCount := by
  simpa [regularityShellEvent, regularityShellTail] using
    targetCut_balanced_count_bernstein P m hm
      (regularityCountThreshold n constant massCount) (massCount / m) massCount
      (regularityCountThreshold_pos hn hconstant) hghostBernstein
      (regularity_variance_cap_pos hm hn hconstant hmass)

/-- Source shell bound with the ghost condition discharged by the fixed numerical constant `64`. -/
theorem sourceCut_regularity_shell_tail_sixtyFour
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 0 < m) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    Measure.pi (fun _ : Fin m ↦ P)
        (regularityShellEvent P sourceCutClass m n 64 massCount) ≤
      regularityShellTail sourceCutClass sourceCutComplementClass m n 64 massCount :=
  sourceCut_regularity_shell_tail P m n hm (lt_of_lt_of_le (by norm_num) hn)
    64 massCount (by norm_num) hmass
    (regularity_ghost_bernstein_sixtyFour m n hm hn massCount hmass)

/-- Target shell bound with the ghost condition discharged by the fixed numerical constant `64`. -/
theorem targetCut_regularity_shell_tail_sixtyFour
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n : ℕ) (hm : 0 < m) (hn : 4 ≤ n) (massCount : ℝ) (hmass : 0 ≤ massCount) :
    Measure.pi (fun _ : Fin m ↦ P)
        (regularityShellEvent P targetCutClass m n 64 massCount) ≤
      regularityShellTail targetCutClass targetCutComplementClass m n 64 massCount :=
  targetCut_regularity_shell_tail P m n hm (lt_of_lt_of_le (by norm_num) hn)
    64 massCount (by norm_num) hmass
    (regularity_ghost_bernstein_sixtyFour m n hm hn massCount hmass)

/-- Union of the first `K` dyadic bad shells for a concept class. -/
noncomputable def finiteRegularityBadEvent
    (P : Measure (ℝ × UnitMark)) (C : ConceptClass (ℝ × UnitMark) Bool)
    (m n K : ℕ) (constant : ℝ) : Set (Fin m → ℝ × UnitMark) :=
  {xs | ∃ k : Fin K,
    xs ∈ regularityShellEvent P C m n constant (dyadicMassCount k)}

/-- The event on which all source and target dyadic shells are regular. -/
noncomputable def finiteHalfspaceRegularityGoodEvent
    (P : Measure (ℝ × UnitMark)) (m n K : ℕ) (constant : ℝ) :
    Set (Fin m → ℝ × UnitMark) :=
  (finiteRegularityBadEvent P sourceCutClass m n K constant ∪
    finiteRegularityBadEvent P targetCutClass m n K constant)ᶜ

/-- Abstract finite-shell union bound.  Source and target cuts differ only in the one-shell
estimate supplied to this theorem. -/
theorem finite_regularity_peeling_of_shell_tail
    (P : Measure (ℝ × UnitMark)) (C : ConceptClass (ℝ × UnitMark) Bool)
    (m n K : ℕ) (constant : ℝ) (tail : Fin K → ENNReal)
    (hshell : ∀ k : Fin K,
      Measure.pi (fun _ : Fin m ↦ P)
          (regularityShellEvent P C m n constant (dyadicMassCount k)) ≤ tail k) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteRegularityBadEvent P C m n K constant) ≤
      ∑ k : Fin K, tail k := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let event : Fin K → Set (Fin m → ℝ × UnitMark) := fun k ↦
    regularityShellEvent P C m n constant (dyadicMassCount k)
  have hsubset : finiteRegularityBadEvent P C m n K constant ⊆ ⋃ k, event k := by
    rintro xs ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc
    μ (finiteRegularityBadEvent P C m n K constant)
        ≤ μ (⋃ k, event k) := measure_mono hsubset
    _ ≤ ∑ k : Fin K, μ (event k) := by
      simpa using measure_iUnion_le (μ := μ) event
    _ ≤ ∑ k : Fin K, tail k := Finset.sum_le_sum fun k _ ↦ hshell k

theorem sourceCut_finite_regularity_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 1 < n)
    (constant : ℝ) (hconstant : 0 < constant)
    (hghostBernstein : ∀ k : Fin K,
      ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) ^ 2) /
            (4 * (dyadicMassCount k / m +
              ((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤ (1 : ENNReal) / 2) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteRegularityBadEvent P sourceCutClass m n K constant) ≤
      ∑ k : Fin K,
        regularityShellTail sourceCutClass sourceCutComplementClass
          m n constant (dyadicMassCount k) := by
  apply finite_regularity_peeling_of_shell_tail
  intro k
  exact sourceCut_regularity_shell_tail P m n hm hn constant (dyadicMassCount k)
    hconstant (dyadicMassCount_nonneg k) (hghostBernstein k)

theorem targetCut_finite_regularity_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 1 < n)
    (constant : ℝ) (hconstant : 0 < constant)
    (hghostBernstein : ∀ k : Fin K,
      ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) ^ 2) /
            (4 * (dyadicMassCount k / m +
              ((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤ (1 : ENNReal) / 2) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteRegularityBadEvent P targetCutClass m n K constant) ≤
      ∑ k : Fin K,
        regularityShellTail targetCutClass targetCutComplementClass
          m n constant (dyadicMassCount k) := by
  apply finite_regularity_peeling_of_shell_tail
  intro k
  exact targetCut_regularity_shell_tail P m n hm hn constant (dyadicMassCount k)
    hconstant (dyadicMassCount_nonneg k) (hghostBernstein k)

/-- Source dyadic peeling with all shell-level numerical hypotheses discharged. -/
theorem sourceCut_finite_regularity_peeling_sixtyFour
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 4 ≤ n) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteRegularityBadEvent P sourceCutClass m n K 64) ≤
      ∑ k : Fin K,
        regularityShellTail sourceCutClass sourceCutComplementClass
          m n 64 (dyadicMassCount k) := by
  exact sourceCut_finite_regularity_peeling P m n K hm
    (lt_of_lt_of_le (by norm_num) hn) 64 (by norm_num) fun k ↦
      regularity_ghost_bernstein_sixtyFour m n hm hn
        (dyadicMassCount k) (dyadicMassCount_nonneg k)

/-- Target dyadic peeling with all shell-level numerical hypotheses discharged. -/
theorem targetCut_finite_regularity_peeling_sixtyFour
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 4 ≤ n) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteRegularityBadEvent P targetCutClass m n K 64) ≤
      ∑ k : Fin K,
        regularityShellTail targetCutClass targetCutComplementClass
          m n 64 (dyadicMassCount k) := by
  exact targetCut_finite_regularity_peeling P m n K hm
    (lt_of_lt_of_le (by norm_num) hn) 64 (by norm_num) fun k ↦
      regularity_ghost_bernstein_sixtyFour m n hm hn
        (dyadicMassCount k) (dyadicMassCount_nonneg k)

/-- Combined source/target finite peeling estimate. -/
theorem finiteHalfspaceRegularityGoodEvent_compl_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 1 < n)
    (constant : ℝ) (hconstant : 0 < constant)
    (hghostBernstein : ∀ k : Fin K,
      ENNReal.ofReal
        (2 * Real.exp
          (-(((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) ^ 2) /
            (4 * (dyadicMassCount k / m +
              ((regularityCountThreshold n constant (dyadicMassCount k) / Real.sqrt m) / 2) /
                Real.sqrt m)))) ≤ (1 : ENNReal) / 2) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteHalfspaceRegularityGoodEvent P m n K constant)ᶜ ≤
      (∑ k : Fin K,
        regularityShellTail sourceCutClass sourceCutComplementClass
          m n constant (dyadicMassCount k)) +
      ∑ k : Fin K,
        regularityShellTail targetCutClass targetCutComplementClass
          m n constant (dyadicMassCount k) := by
  rw [finiteHalfspaceRegularityGoodEvent, compl_compl]
  exact (measure_union_le _ _).trans (add_le_add
    (sourceCut_finite_regularity_peeling P m n K hm hn constant hconstant hghostBernstein)
    (targetCut_finite_regularity_peeling P m n K hm hn constant hconstant hghostBernstein))

/-- Combined source/target bad-event estimate with the explicit constant `64` and no remaining
shell-level side conditions. -/
theorem finiteHalfspaceRegularityGoodEvent_sixtyFour_compl_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m n K : ℕ) (hm : 0 < m) (hn : 4 ≤ n) :
    Measure.pi (fun _ : Fin m ↦ P)
        (finiteHalfspaceRegularityGoodEvent P m n K 64)ᶜ ≤
      (∑ k : Fin K,
        regularityShellTail sourceCutClass sourceCutComplementClass
          m n 64 (dyadicMassCount k)) +
      ∑ k : Fin K,
        regularityShellTail targetCutClass targetCutComplementClass
          m n 64 (dyadicMassCount k) := by
  exact finiteHalfspaceRegularityGoodEvent_compl_le P m n K hm
    (lt_of_lt_of_le (by norm_num) hn) 64 (by norm_num) fun k ↦
      regularity_ghost_bernstein_sixtyFour m n hm hn
        (dyadicMassCount k) (dyadicMassCount_nonneg k)

/-- Explicit polynomial envelope for all `n + 1` source and target shells. -/
noncomputable def regularityPolynomialBadBound (n : ℕ) : ENNReal :=
  2 * ((n + 1 : ℕ) : ENNReal) * regularityPolynomialShellBound n

theorem finiteHalfspaceRegularityGoodEvent_compl_le_polynomial
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 4 ≤ n) :
    Measure.pi (fun _ : Fin n ↦ P)
        (finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)ᶜ ≤
      regularityPolynomialBadBound n := by
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  calc
    Measure.pi (fun _ : Fin n ↦ P)
        (finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)ᶜ
        ≤ (∑ k : Fin (n + 1),
            regularityShellTail sourceCutClass sourceCutComplementClass
              n n 64 (dyadicMassCount k)) +
          ∑ k : Fin (n + 1),
            regularityShellTail targetCutClass targetCutComplementClass
              n n 64 (dyadicMassCount k) :=
      finiteHalfspaceRegularityGoodEvent_sixtyFour_compl_le
        P n n (n + 1) hn_pos hn
    _ ≤ (∑ _k : Fin (n + 1), regularityPolynomialShellBound n) +
          ∑ _k : Fin (n + 1), regularityPolynomialShellBound n := by
      apply add_le_add <;> apply Finset.sum_le_sum <;> intro k _
      · exact sourceCut_regularityShellTail_sixtyFour_le
          n hn (dyadicMassCount k) (dyadicMassCount_nonneg k)
      · exact targetCut_regularityShellTail_sixtyFour_le
          n hn (dyadicMassCount k) (dyadicMassCount_nonneg k)
    _ = regularityPolynomialBadBound n := by
      simp [regularityPolynomialBadBound, Fintype.card_fin]
      ring

theorem regularityPolynomialBadBound_le_inv_pow
    (n : ℕ) (hn : 1 ≤ n) :
    regularityPolynomialBadBound n ≤
      ENNReal.ofReal (256 * ((n : ℝ)⁻¹) ^ 12) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn_nonneg : (0 : ℝ) ≤ n := hn_pos.le
  have hn_add_nat : n + 1 ≤ 2 * n := by omega
  have hn_add : ((n + 1 : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast hn_add_nat
  have hreal :
      128 * ((n + 1 : ℕ) : ℝ) * (n : ℝ) ^ 3 * (1 / (n : ℝ) ^ 16) ≤
        256 * ((n : ℝ)⁻¹) ^ 12 := by
    field_simp
    nlinarith [pow_pos hn_pos 12, pow_pos hn_pos 16]
  unfold regularityPolynomialBadBound regularityPolynomialShellBound
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  convert hreal using 1
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem tendsto_regularityPolynomialBadBound :
    Filter.Tendsto regularityPolynomialBadBound Filter.atTop (nhds 0) := by
  let upper : ℕ → ENNReal := fun n ↦ ENNReal.ofReal (256 * ((n : ℝ)⁻¹) ^ 12)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 12)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 12
  have hreal : Filter.Tendsto (fun n : ℕ ↦ 256 * ((n : ℝ)⁻¹) ^ 12)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  have hupper : Filter.Tendsto upper Filter.atTop (nhds 0) := by
    simpa [upper, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact regularityPolynomialBadBound_le_inv_pow n hn

theorem tendsto_finiteHalfspaceRegularity_bad_probability
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P] :
    Filter.Tendsto
      (fun n ↦ Measure.pi (fun _ : Fin n ↦ P)
        (finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)ᶜ)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_regularityPolynomialBadBound
  · exact Filter.Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact finiteHalfspaceRegularityGoodEvent_compl_le_polynomial P n hn

private theorem sampleErrorSum_nonneg {Ω : Type*} {m : ℕ}
    (h c : Concept Ω Bool) (xs : Fin m → Ω) : 0 ≤ sampleErrorSum h c xs := by
  apply Finset.sum_nonneg
  intro i _
  cases hxi : h (xs i) <;> cases cxi : c (xs i) <;> norm_num [zeroOneLoss]

private theorem sampleErrorSum_le_card {Ω : Type*} {m : ℕ}
    (h c : Concept Ω Bool) (xs : Fin m → Ω) : sampleErrorSum h c xs ≤ m := by
  calc
    sampleErrorSum h c xs ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases hxi : h (xs i) <;> cases cxi : c (xs i) <;> norm_num [zeroOneLoss]
    _ = m := by simp

theorem populationOrientedSampleErrorSum_nonneg
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (h : Concept (ℝ × UnitMark) Bool) (xs : Fin m → ℝ × UnitMark) :
    0 ≤ populationOrientedSampleErrorSum P h xs := by
  unfold populationOrientedSampleErrorSum
  split
  · exact sampleErrorSum_nonneg h falseCutTarget xs
  · linarith [sampleErrorSum_le_card h falseCutTarget xs]

theorem populationOrientedSampleErrorSum_le_card
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (h : Concept (ℝ × UnitMark) Bool) (xs : Fin m → ℝ × UnitMark) :
    populationOrientedSampleErrorSum P h xs ≤ m := by
  unfold populationOrientedSampleErrorSum
  split
  · exact sampleErrorSum_le_card h falseCutTarget xs
  · linarith [sampleErrorSum_nonneg h falseCutTarget xs]

theorem expectedBalancedMassCount_le_card
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (h : Concept (ℝ × UnitMark) Bool) :
    (m : ℝ) * balancedMass P (errorSet h falseCutTarget) ≤ m := by
  have hmass : balancedMass P (errorSet h falseCutTarget) ≤ 1 := by
    exact (min_le_left _ _).trans measureReal_le_one
  simpa using mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ m from Nat.cast_nonneg _)

/-- Every nonnegative count at most `n` has a dyadic cap among indices `0, ..., n`, and the
least such cap is smaller than twice `max 1 z`. -/
theorem exists_dyadicMassCount_cap
    {n : ℕ} {z : ℝ} (hzn : z ≤ n) :
    ∃ k : Fin (n + 1), z ≤ dyadicMassCount k ∧
      dyadicMassCount k < 2 * max 1 z := by
  have hn_pow : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hz_pow : z ≤ (2 : ℝ) ^ n := hzn.trans (by exact_mod_cast hn_pow)
  let hex : ∃ k : ℕ, z ≤ (2 : ℝ) ^ k := ⟨n, hz_pow⟩
  let k₀ := Nat.find hex
  have hk₀ : z ≤ (2 : ℝ) ^ k₀ := Nat.find_spec hex
  have hk₀n : k₀ ≤ n := Nat.find_min' hex hz_pow
  refine ⟨⟨k₀, Nat.lt_succ_of_le hk₀n⟩, ?_, ?_⟩
  · exact hk₀
  · change (2 : ℝ) ^ k₀ < 2 * max 1 z
    by_cases hkzero : k₀ = 0
    · rw [hkzero, pow_zero]
      have hmax : (1 : ℝ) ≤ max 1 z := le_max_left _ _
      nlinarith
    · have hkpos : 0 < k₀ := Nat.pos_of_ne_zero hkzero
      have hkpred : k₀ - 1 < k₀ := by omega
      have hnot := Nat.find_min hex hkpred
      have hprev : (2 : ℝ) ^ (k₀ - 1) < z := lt_of_not_ge hnot
      calc
        (2 : ℝ) ^ k₀ = (2 : ℝ) ^ (k₀ - 1 + 1) := by congr 1; omega
        _ = 2 * (2 : ℝ) ^ (k₀ - 1) := by rw [pow_succ]; ring
        _ < 2 * z := mul_lt_mul_of_pos_left hprev (by norm_num)
        _ ≤ 2 * max 1 z := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

private theorem threshold_sixtyFour_of_massCap_le_two
    {n : ℕ} (hn : 4 ≤ n) {massCap mass : ℝ}
    (_hmassCap : 0 ≤ massCap) (hmass : 0 ≤ mass)
    (hcap : massCap ≤ 2 * mass) :
    regularityCountThreshold n 64 massCap ≤
      128 * (Real.sqrt (mass * Real.log n) + Real.log n) := by
  have hn_one : 1 < n := lt_of_lt_of_le (by norm_num) hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast hn_one)).le
  have hprod : massCap * Real.log n ≤ 2 * (mass * Real.log n) := by
    nlinarith
  have hsqrt : Real.sqrt (massCap * Real.log n) ≤
      2 * Real.sqrt (mass * Real.log n) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsq := Real.sq_sqrt (mul_nonneg hmass hlog)
      nlinarith [Real.sqrt_nonneg (mass * Real.log n)]
  unfold regularityCountThreshold
  nlinarith

/-- On the combined good event, every source cut covered by shell `k` satisfies its explicit
count-scale regularity bound. -/
theorem sourceCut_regular_on_goodEvent
    (P : Measure (ℝ × UnitMark)) {m n K : ℕ} {constant : ℝ}
    {xs : Fin m → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P m n K constant)
    (k : Fin K) {h : Concept (ℝ × UnitMark) Bool} (hh : h ∈ sourceCutClass)
    (htrue : balancedMass P (errorSet h falseCutTarget) ≤ dyadicMassCount k / m)
    (hsample : populationOrientedSampleErrorSum P h xs ≤ dyadicMassCount k) :
    |centeredErrorSum P h falseCutTarget xs| <
      regularityCountThreshold n constant (dyadicMassCount k) := by
  have hnot : xs ∉ regularityShellEvent P sourceCutClass m n constant
      (dyadicMassCount k) := by
    intro hk
    exact hgood (Set.mem_union_left _ ⟨k, hk⟩)
  exact centeredErrorSum_lt_regularityCountThreshold_of_not_mem
    P sourceCutClass hnot hh htrue hsample

/-- Target counterpart of `sourceCut_regular_on_goodEvent`. -/
theorem targetCut_regular_on_goodEvent
    (P : Measure (ℝ × UnitMark)) {m n K : ℕ} {constant : ℝ}
    {xs : Fin m → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P m n K constant)
    (k : Fin K) {h : Concept (ℝ × UnitMark) Bool} (hh : h ∈ targetCutClass)
    (htrue : balancedMass P (errorSet h falseCutTarget) ≤ dyadicMassCount k / m)
    (hsample : populationOrientedSampleErrorSum P h xs ≤ dyadicMassCount k) :
    |centeredErrorSum P h falseCutTarget xs| <
      regularityCountThreshold n constant (dyadicMassCount k) := by
  have hnot : xs ∉ regularityShellEvent P targetCutClass m n constant
      (dyadicMassCount k) := by
    intro hk
    exact hgood (Set.mem_union_right _ ⟨k, hk⟩)
  exact centeredErrorSum_lt_regularityCountThreshold_of_not_mem
    P targetCutClass hnot hh htrue hsample

/-- A dyadic shell bound at constant `64` implies the population-count form of (1.10).
The numerical constant is explicit; the proof uses the exact observed/expected count identity
and the self-bounded Bernstein bootstrap above. -/
private theorem centeredErrorSum_uniform_of_dyadic_shell_regular
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (C : ConceptClass (ℝ × UnitMark) Bool) {n : ℕ} (hn : 4 ≤ n)
    (h : Concept (ℝ × UnitMark) Bool) (hhC : h ∈ C) (hh : Measurable h)
    (xs : Fin n → ℝ × UnitMark)
    (hshell : ∀ k : Fin (n + 1),
      balancedMass P (errorSet h falseCutTarget) ≤ dyadicMassCount k / n →
      populationOrientedSampleErrorSum P h xs ≤ dyadicMassCount k →
      |centeredErrorSum P h falseCutTarget xs| <
        regularityCountThreshold n 64 (dyadicMassCount k)) :
    |centeredErrorSum P h falseCutTarget xs| ≤
      33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P (errorSet h falseCutTarget)) *
          Real.log n) + Real.log n) := by
  let expected : ℝ := (n : ℝ) * balancedMass P (errorSet h falseCutTarget)
  let observed : ℝ := populationOrientedSampleErrorSum P h xs
  let defect : ℝ := |centeredErrorSum P h falseCutTarget xs|
  let logTerm : ℝ := Real.log n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.2 (lt_of_lt_of_le (by norm_num) hn)
  have hexpected_nonneg : 0 ≤ expected := by
    exact mul_nonneg (Nat.cast_nonneg _) (balancedMass_nonneg P _)
  have hexpected_le : expected ≤ n := by
    exact expectedBalancedMassCount_le_card P h
  have hobserved_nonneg : 0 ≤ observed := by
    exact populationOrientedSampleErrorSum_nonneg P h xs
  have hobserved_le : observed ≤ n := by
    exact populationOrientedSampleErrorSum_le_card P h xs
  have hdefect_nonneg : 0 ≤ defect := abs_nonneg _
  have hmax_le_n : max expected observed ≤ n := max_le hexpected_le hobserved_le
  obtain ⟨k, hmax_cap, hcap_close⟩ := exists_dyadicMassCount_cap hmax_le_n
  have hexpected_cap : expected ≤ dyadicMassCount k :=
    (le_max_left expected observed).trans hmax_cap
  have hobserved_cap : observed ≤ dyadicMassCount k :=
    (le_max_right expected observed).trans hmax_cap
  have htrue_cap :
      balancedMass P (errorSet h falseCutTarget) ≤ dyadicMassCount k / n := by
    rw [le_div_iff₀ hn_pos]
    simpa [expected, mul_comm] using hexpected_cap
  have hshell_bound :
      defect ≤ regularityCountThreshold n 64 (dyadicMassCount k) := by
    exact (hshell k htrue_cap (by simpa [observed] using hobserved_cap)).le
  have hcount_identity : |observed - expected| = defect := by
    simpa [observed, expected, defect] using
      abs_populationOrientedSampleErrorSum_sub_expected_balancedMass
        P C h hhC hh xs
  have hobserved_expected : observed ≤ expected + defect := by
    have hle := le_abs_self (observed - expected)
    rw [hcount_identity] at hle
    linarith
  have hmax_expected : max expected observed ≤ expected + defect := by
    exact max_le (by linarith) hobserved_expected
  have hmax_one : max 1 (max expected observed) ≤ 1 + expected + defect := by
    exact max_le (by linarith) (by linarith)
  have hcap_two : dyadicMassCount k ≤ 2 * (1 + expected + defect) := by
    exact hcap_close.le.trans
      (mul_le_mul_of_nonneg_left hmax_one (by norm_num))
  have hmass_nonneg : 0 ≤ 1 + expected + defect := by linarith
  have hthreshold :
      regularityCountThreshold n 64 (dyadicMassCount k) ≤
        128 *
          (Real.sqrt ((1 + expected + defect) * Real.log n) + Real.log n) :=
    threshold_sixtyFour_of_massCap_le_two hn (dyadicMassCount_nonneg k)
      hmass_nonneg hcap_two
  have hself_bound : defect ≤
      128 * (Real.sqrt (((expected + 1) + defect) * logTerm) + logTerm) := by
    calc
      defect ≤ regularityCountThreshold n 64 (dyadicMassCount k) := hshell_bound
      _ ≤ 128 *
          (Real.sqrt ((1 + expected + defect) * Real.log n) + Real.log n) := hthreshold
      _ = 128 * (Real.sqrt (((expected + 1) + defect) * logTerm) + logTerm) := by
        simp only [logTerm]
        congr 2
        ring_nf
  have hlog_nonneg : 0 ≤ logTerm := by
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn))).le
  have hbootstrap := selfBoundedBernstein_uniform_constant hdefect_nonneg
    (by linarith : 0 ≤ expected + 1) hlog_nonneg (by norm_num : (0 : ℝ) ≤ 128)
    hself_bound
  have hbootstrap' : defect ≤
      16640 * (Real.sqrt ((expected + 1) * logTerm) + logTerm) := by
    norm_num at hbootstrap ⊢
    exact hbootstrap
  have hexp_one_le : Real.exp 1 ≤ (n : ℝ) := by
    exact (le_of_lt Real.exp_one_lt_three).trans (by exact_mod_cast (show 3 ≤ n by omega))
  have hlog_one : 1 ≤ logTerm := by
    exact (Real.le_log_iff_exp_le hn_pos).2 hexp_one_le
  have hexpected_log : 0 ≤ expected * logTerm :=
    mul_nonneg hexpected_nonneg hlog_nonneg
  have hsqrt_add :
      Real.sqrt ((expected + 1) * logTerm) ≤
        Real.sqrt (expected * logTerm) + Real.sqrt logTerm := by
    rw [show (expected + 1) * logTerm =
      expected * logTerm + logTerm by ring]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hexpected_sq := Real.sq_sqrt hexpected_log
      have hlog_sq := Real.sq_sqrt hlog_nonneg
      nlinarith [mul_nonneg (Real.sqrt_nonneg (expected * logTerm))
        (Real.sqrt_nonneg logTerm)]
  have hsqrt_log_le : Real.sqrt logTerm ≤ logTerm :=
    (Real.sqrt_le_self_iff).2 (Or.inr hlog_one)
  have hshape :
      Real.sqrt ((expected + 1) * logTerm) + logTerm ≤
        2 * (Real.sqrt (expected * logTerm) + logTerm) := by
    nlinarith [Real.sqrt_nonneg (expected * logTerm)]
  calc
    defect ≤ 16640 *
        (Real.sqrt ((expected + 1) * logTerm) + logTerm) := hbootstrap'
    _ ≤ 16640 * (2 * (Real.sqrt (expected * logTerm) + logTerm)) :=
      mul_le_mul_of_nonneg_left hshape (by norm_num)
    _ = 33280 * (Real.sqrt (expected * logTerm) + logTerm) := by ring
    _ = 33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P (errorSet h falseCutTarget)) *
          Real.log n) + Real.log n) := by rfl

/-- Uniform source-cut version of (1.10) on the explicit finite-peeling good event. -/
theorem sourceCut_uniform_regularity_on_goodEvent
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) {xs : Fin n → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)
    {h : Concept (ℝ × UnitMark) Bool} (hh : h ∈ sourceCutClass) :
    |centeredErrorSum P h falseCutTarget xs| ≤
      33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P (errorSet h falseCutTarget)) *
          Real.log n) + Real.log n) := by
  apply centeredErrorSum_uniform_of_dyadic_shell_regular P sourceCutClass hn h hh
    (measurable_sourceCutClass h hh) xs
  intro k htrue hsample
  exact sourceCut_regular_on_goodEvent P hgood k hh htrue hsample

/-- Uniform target-cut version of (1.10) on the same finite-peeling good event. -/
theorem targetCut_uniform_regularity_on_goodEvent
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) {xs : Fin n → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)
    {h : Concept (ℝ × UnitMark) Bool} (hh : h ∈ targetCutClass) :
    |centeredErrorSum P h falseCutTarget xs| ≤
      33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P (errorSet h falseCutTarget)) *
          Real.log n) + Real.log n) := by
  apply centeredErrorSum_uniform_of_dyadic_shell_regular P targetCutClass hn h hh
    (measurable_targetCutClass h hh) xs
  intro k htrue hsample
  exact targetCut_regular_on_goodEvent P hgood k hh htrue hsample

/-- The source defect itself satisfies (1.10), with the same good event and explicit constant. -/
theorem sourceCutDefect_uniform_regularity_on_goodEvent
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) {xs : Fin n → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)
    (p x : ℝ) :
    |sourceCutDefect P xs p x| ≤
      33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P
          (errorSet (sourceCutEval (p, x)) falseCutTarget)) * Real.log n) +
          Real.log n) := by
  rw [sourceCutDefect_eq_centeredErrorSum]
  exact sourceCut_uniform_regularity_on_goodEvent P hn hgood ⟨p, x, rfl⟩

/-- The target defect itself satisfies (1.10), with the same good event and explicit constant. -/
theorem targetCutDefect_uniform_regularity_on_goodEvent
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) {xs : Fin n → ℝ × UnitMark}
    (hgood : xs ∈ finiteHalfspaceRegularityGoodEvent P n n (n + 1) 64)
    (p x : ℝ) :
    |targetCutDefect P xs p x| ≤
      33280 *
        (Real.sqrt (((n : ℝ) * balancedMass P
          (errorSet (targetCutEval (p, x)) falseCutTarget)) * Real.log n) +
          Real.log n) := by
  rw [targetCutDefect_eq_centeredErrorSum]
  exact targetCut_uniform_regularity_on_goodEvent P hn hgood ⟨p, x, rfl⟩

end OTSelector.RelativeVC
