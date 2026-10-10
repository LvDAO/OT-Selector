import OTSelector.Probability.CountingProcess.Occupation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite-horizon exponential counting martingale

This file proves the martingale input to `lem:occupation` of `main.tex`.  For a simple counting
process with predictable intensity `Λ` and a finite deterministic upper bound on `Λ`, the
exponential process

  `Z t = exp(-θ₀ · N t + (1 - exp(-θ₀)) · ∫₀ᵗ Λ)`

is a martingale for `θ₀ > 0`.  Conditional lower-occupation estimates and stopped intervals
are deliberately left to the subsequent tail module.

The central ingredient is the path identity

  `Z t = 1 + ∫₀ᵗ H dN - ∫₀ᵗ H Λ ds`,    `H s = (e^{-θ₀} - 1) · e^{-θ₀ · N(s-)} · e^{(1-e^{-θ₀}) ∫₀ˢ Λ}`,

where `N(s-)` is the left jump count `countBefore N s`.  The left weight `H` is bounded and
predictable (by `stronglyMeasurable_countBefore` and `of_continuous_adapted`), so the closure
theorem in `Closure.lean` turns the compensated integral into a martingale; the path identity then
transfers the martingale property to `Z`.

This file supplies the two missing pieces: the jump-time structure of simple counting paths and
the path identity (which needs a per-path fundamental theorem of calculus for the continuous part
of the compensator).
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Jump-time structure of simple counting paths -/

omit [MeasurableSpace Ω] in
/-- Jump times are monotone in the label. -/
theorem jumpTime_mono {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k l : ℕ} (hkl : k ≤ l) {t : ℝ≥0}
    (ht : l < N t ω) :
    jumpTime N k ω ≤ jumpTime N l ω := by
  unfold jumpTime
  refine csInf_le_csInf (OrderBot.bddBelow _) ⟨t, ht⟩ ?_
  intro s hs
  exact lt_of_le_of_lt hkl hs

omit [MeasurableSpace Ω] in
/-- If `k` jumps are attained by time `s`, the `(k+1)`-th jump time is no later than `s`. -/
theorem jumpTime_le_of_lt {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s : ℝ≥0}
    (hks : k < N s ω) :
    jumpTime N k ω ≤ s := by
  unfold jumpTime
  exact csInf_le (OrderBot.bddBelow _) hks

omit [MeasurableSpace Ω] in
/-- Once some time attains more than `k` jumps, a bound on the `(k+1)`-th jump time forces the
count past `k` at the bound itself (right continuity carries the attained count to the infimum). -/
theorem lt_of_jumpTime_le {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hne : ∃ t : ℝ≥0, k < N t ω) (hτs : jumpTime N k ω ≤ s) :
    k < N s ω := by
  by_contra hs
  have hS : ∀ u : ℝ≥0, jumpTime N k ω < u → k < N u ω := by
    intro u hτu
    by_contra hk
    have hu_le : ∀ v ∈ ({t : ℝ≥0 | k < N t ω}), u ≤ v := by
      intro v hv
      by_contra hvle
      have hvu : v < u := lt_of_not_ge hvle
      have hNv : N v ω ≤ N u ω := hmono (le_of_lt hvu)
      have hNu : N u ω ≤ k := Nat.le_of_not_gt hk
      exact Nat.not_le.mpr hv (hNv.trans hNu)
    have hle : u ≤ sInf ({t : ℝ≥0 | k < N t ω}) := le_csInf hne hu_le
    exact (not_le.mpr hτu) hle
  have hc : Tendsto (fun u ↦ (N u ω : ℝ)) (𝓝[>] s) (𝓝 ((N s ω : ℝ))) :=
    (hrc s).mono_left (nhdsWithin_mono s Ioi_subset_Ici_self)
  have hev : ∀ᶠ u in 𝓝[>] s, (k + 1 : ℝ) ≤ (N u ω : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with u hus
    exact_mod_cast (Nat.succ_le_iff.mpr (hS u (lt_of_le_of_lt hτs hus)))
  have hnear : ∀ᶠ u in 𝓝[>] s, (N u ω : ℝ) < (N s ω : ℝ) + 1 := by
    filter_upwards [hc (Metric.ball_mem_nhds (N s ω : ℝ) (by norm_num : (0 : ℝ) < 1))] with u hu
    change (N u ω : ℝ) ∈ Metric.ball (N s ω : ℝ) 1 at hu
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hu
    nlinarith [abs_lt.mp hu]
  rcases (hev.and hnear).exists with ⟨u, hlow, hup⟩
  have hNsle : (N s ω : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.le_of_not_gt hs)
  nlinarith

omit [MeasurableSpace Ω] in
/-- The `(k+1)`-th jump time is attained no later than `s` exactly when the count at `s` already
exceeds `k`; the nonemptiness assumption rules out the no-jump case where the jump time defaults
to the bottom element. -/
theorem jumpTime_le_iff {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hne : ∃ t : ℝ≥0, k < N t ω) :
    jumpTime N k ω ≤ s ↔ k < N s ω := by
  constructor
  · intro hτs
    exact lt_of_jumpTime_le hmono hrc hne hτs
  · intro hks
    exact jumpTime_le_of_lt hks

omit [MeasurableSpace Ω] in
/-- `s` strictly precedes the `(k+1)`-th jump time exactly when the count at `s` is at most `k`. -/
theorem jumpTime_lt_iff {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hne : ∃ t : ℝ≥0, k < N t ω) :
    s < jumpTime N k ω ↔ N s ω ≤ k := by
  rw [← not_iff_not, not_lt, Nat.not_le]
  exact jumpTime_le_iff hmono hrc hne

omit [MeasurableSpace Ω] in
/-- Consecutive attained jump labels have strictly increasing jump times. -/
theorem jumpTime_lt_jumpTime_succ {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {t : ℝ≥0}
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N t ω))) (hk : k + 1 < N t ω) :
    jumpTime N k ω < jumpTime N (k + 1) ω := by
  have hle : jumpTime N k ω ≤ jumpTime N (k + 1) ω :=
    jumpTime_mono (Nat.le_succ k) hk
  have hne : jumpTime N k ω ≠ jumpTime N (k + 1) ω := by
    exact (hinj.ne_iff (Nat.lt_of_succ_lt hk) hk).mpr (by omega)
  exact lt_of_le_of_ne hle hne

omit [MeasurableSpace Ω] in
/-- The count at the `(k+1)`-th jump time is exactly `k + 1`. -/
theorem N_jumpTime {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {t : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N t ω))) (hk : k + 1 < N t ω) :
    N (jumpTime N k ω) ω = k + 1 := by
  have hle : k + 1 ≤ N (jumpTime N k ω) ω :=
    Nat.succ_le_iff.mpr (lt_of_jumpTime_le hmono hrc ⟨t, Nat.lt_of_succ_lt hk⟩ le_rfl)
  have hge : N (jumpTime N k ω) ω ≤ k + 1 := by
    by_contra h
    have hk2 : k + 1 < N (jumpTime N k ω) ω := Nat.lt_of_not_ge h
    have hτk1 : jumpTime N (k + 1) ω ≤ jumpTime N k ω :=
      jumpTime_le_of_lt hk2
    have hτmono : jumpTime N k ω ≤ jumpTime N (k + 1) ω :=
      jumpTime_mono (Nat.le_succ k) hk
    have heq : jumpTime N k ω = jumpTime N (k + 1) ω := le_antisymm hτmono hτk1
    exact (hinj.ne_iff (Nat.lt_of_succ_lt hk) hk).mpr (by omega) heq
  exact le_antisymm hge hle

omit [MeasurableSpace Ω] in
/-- The count at every attained jump time is exactly one more than its label, including the
last jump attained by a fixed horizon. -/
theorem N_jumpTime_of_lt {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {t : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N t ω))) (hk : k < N t ω) :
    N (jumpTime N k ω) ω = k + 1 := by
  have hle : k + 1 ≤ N (jumpTime N k ω) ω :=
    Nat.succ_le_iff.mpr (lt_of_jumpTime_le hmono hrc ⟨t, hk⟩ le_rfl)
  have hge : N (jumpTime N k ω) ω ≤ k + 1 := by
    by_contra h
    have hk2 : k + 1 < N (jumpTime N k ω) ω := Nat.lt_of_not_ge h
    have hτ : jumpTime N k ω ≤ t := jumpTime_le_of_lt hk
    have hsucc : k + 1 < N t ω := Nat.lt_of_lt_of_le hk2 (hmono hτ)
    have hτk1 : jumpTime N (k + 1) ω ≤ jumpTime N k ω := jumpTime_le_of_lt hk2
    have hτmono : jumpTime N k ω ≤ jumpTime N (k + 1) ω :=
      jumpTime_mono (Nat.le_succ k) hsucc
    have heq : jumpTime N k ω = jumpTime N (k + 1) ω := le_antisymm hτmono hτk1
    exact (hinj.ne_iff hk hsucc).mpr (by omega) heq
  exact le_antisymm hge hle

omit [MeasurableSpace Ω] in
/-- On the cell `(τₖ, τₖ₊₁]` the left jump count is exactly `k + 1`. -/
theorem countBefore_eq_of_Ioc {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hne : ∃ t : ℝ≥0, k < N t ω)
    (hleft : jumpTime N k ω < s) (hright : s ≤ jumpTime N (k + 1) ω) :
    countBefore N s ω = k + 1 := by
  apply le_antisymm
  · by_contra h
    have hge : k + 2 ≤ countBefore N s ω :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    rw [countBefore_succ_le_iff hmono] at hge
    rcases hge with ⟨u, hus, hku⟩
    have hτu : jumpTime N (k + 1) ω ≤ u := jumpTime_le_of_lt hku
    exact (not_lt.mpr (hright.trans hτu)) hus
  · rw [countBefore_succ_le_iff hmono]
    exact ⟨jumpTime N k ω, hleft, lt_of_jumpTime_le hmono hrc hne le_rfl⟩

omit [MeasurableSpace Ω] in
/-- On `(τ_{m-1}, t]` the left jump count is exactly `N t`. -/
theorem countBefore_eq_of_lt {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {m : ℕ} {s t : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hNt : N t ω = m) (hprev : jumpTime N (m - 1) ω < s) (hst : s ≤ t) :
    countBefore N s ω = m := by
  apply le_antisymm
  · by_contra h
    have hge : m + 1 ≤ countBefore N s ω :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    rw [countBefore_succ_le_iff hmono] at hge
    rcases hge with ⟨u, hus, hmu⟩
    have hNu : N u ω ≤ m := by
      rw [← hNt]
      exact hmono (hus.le.trans hst)
    omega
  · cases m with
    | zero => simp
    | succ k =>
      rw [countBefore_succ_le_iff hmono]
      exact ⟨jumpTime N k ω, hprev,
        lt_of_jumpTime_le hmono hrc ⟨t, by rw [hNt]; exact Nat.lt_succ_self k⟩ le_rfl⟩

omit [MeasurableSpace Ω] in
/-- With no jump up to `s`, the left jump count at `s` vanishes. -/
theorem countBefore_eq_zero_of_le {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {s : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (_hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t) (hNs : N s ω = 0) :
    countBefore N s ω = 0 := by
  apply le_antisymm
  · by_contra h
    have hge : 0 + 1 ≤ countBefore N s ω :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    rw [countBefore_succ_le_iff hmono] at hge
    rcases hge with ⟨u, hus, h0u⟩
    have hNu : N u ω = 0 := le_antisymm (hmono hus.le |>.trans_eq hNs) (Nat.zero_le _)
    omega
  · exact Nat.zero_le _

/-! ## Interval FTC for the continuous part -/

omit [MeasurableSpace Ω] in
/-- Membership of `Real.toNNReal x` in a nonnegative interval is the same as membership of `x`
in the corresponding real interval. -/
theorem toNNReal_mem_Ioc_iff {u v : ℝ≥0} {x : ℝ} :
    Real.toNNReal x ∈ Ioc u v ↔ x ∈ Ioc (u : ℝ) (v : ℝ) := by
  constructor
  · intro h
    have hx0 : 0 ≤ x := by
      by_contra hneg
      have hnn : (Real.toNNReal x : ℝ) = 0 := by
        simpa using max_eq_left (le_of_not_ge hneg)
      have hu' : (u : ℝ) < 0 := by
        have : (u : ℝ) < (Real.toNNReal x : ℝ) := by exact_mod_cast h.1
        rw [hnn] at this
        exact this
      exact (not_lt_of_ge u.2) hu'
    have hx : (Real.toNNReal x : ℝ) = x := by
      simpa using max_eq_left hx0
    rw [Set.mem_Ioc]
    constructor
    · have : (u : ℝ) < x := by
        have : (u : ℝ) < (Real.toNNReal x : ℝ) := by exact_mod_cast h.1
        simpa [hx] using this
      exact this
    · have : x ≤ (v : ℝ) := by
        have : (Real.toNNReal x : ℝ) ≤ (v : ℝ) := by exact_mod_cast h.2
        simpa [hx] using this
      exact this
  · intro h
    rw [Set.mem_Ioc] at h
    have hx0 : 0 ≤ x := le_trans u.2 (le_of_lt h.1)
    have hx : (Real.toNNReal x : ℝ) = x := by
      simpa using max_eq_left hx0
    rw [Set.mem_Ioc]
    constructor
    · have : (u : ℝ) < (Real.toNNReal x : ℝ) := by
        simpa [hx] using h.1
      exact_mod_cast this
    · have : (Real.toNNReal x : ℝ) ≤ (v : ℝ) := by
        simpa [hx] using h.2
      exact_mod_cast this

omit [MeasurableSpace Ω] in
/-- Pushing the restricted time measure along the coercion to `ℝ` recovers real Lebesgue measure
restricted to the corresponding real interval. -/
theorem map_coe_timeMeasure_restrict (u v : ℝ≥0) :
    (timeMeasure.restrict (Ioc u v)).map (fun r : ℝ≥0 ↦ (r : ℝ)) =
      volume.restrict (Ioc (u : ℝ) (v : ℝ)) := by
  rw [timeMeasure]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Ioc]
  rw [Measure.map_map NNReal.continuous_coe.measurable continuous_real_toNNReal.measurable]
  have htoNNReal :
      (NNReal.toReal ∘ Real.toNNReal) =ᵐ[((volume.restrict (Ici (0 : ℝ))).restrict
        (Real.toNNReal ⁻¹' Ioc u v))] id := by
    filter_upwards [self_mem_ae_restrict (continuous_real_toNNReal.measurable measurableSet_Ioc)]
      with x hx
    have hx0 : 0 ≤ x := le_trans u.2 (le_of_lt ((toNNReal_mem_Ioc_iff).mp hx).1)
    change (Real.toNNReal x : ℝ) = x
    simpa using max_eq_left hx0
  rw [Measure.map_congr htoNNReal]
  change Measure.map (id : ℝ → ℝ) ((volume.restrict (Ici (0 : ℝ))).restrict
      (Real.toNNReal ⁻¹' Ioc u v)) = volume.restrict (Ioc (u : ℝ) (v : ℝ))
  rw [Measure.map_id]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Ioc)]
  congr 1
  ext x
  rw [Set.mem_inter_iff, Set.mem_preimage, toNNReal_mem_Ioc_iff]
  constructor
  · intro h
    exact h.1
  · intro hx
    exact ⟨hx, le_trans u.2 (le_of_lt hx.1)⟩

omit [MeasurableSpace Ω] in
/-- The time-measure integral over a bounded interval agrees with the real interval integral of
the function precomposed with `Real.toNNReal`. -/
theorem integral_timeMeasure_eq_intervalIntegral (g : ℝ≥0 → ℝ) (u v : ℝ≥0) (huv : u ≤ v) :
    ∫ s in Ioc u v, g s ∂timeMeasure = ∫ x in (u : ℝ)..(v : ℝ), g (Real.toNNReal x) := by
  rw [intervalIntegral.integral_of_le (by exact_mod_cast huv)]
  rw [← map_coe_timeMeasure_restrict u v]
  have hcoeEmb : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  rw [hcoeEmb.integral_map]
  rw [integral_congr_ae]
  filter_upwards with s
  congr 1
  exact Real.toNNReal_coe.symm

omit [MeasurableSpace Ω] in
/-- On `(-∞, U]` the exponential is Lipschitz with constant `exp U`. -/
theorem abs_exp_sub_exp_le_exp_U (x y U : ℝ) (hx : x ≤ U) (hy : y ≤ U) :
    |Real.exp x - Real.exp y| ≤ Real.exp U * |x - y| := by
  wlog hxy : x ≤ y generalizing x y U
  · simpa [abs_sub_comm] using (this y x U hy hx) (le_of_not_ge hxy)
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  obtain ⟨z, hzIoo, hz⟩ := exists_hasDerivAt_eq_slope (f := Real.exp) (f' := Real.exp) hxy
    (Real.continuous_exp.continuousOn.mono (subset_univ _)) (fun x _ ↦ Real.hasDerivAt_exp x)
  have hzu : z ≤ U := hzIoo.2.le.trans hy
  have hmono : Real.exp z ≤ Real.exp U := Real.exp_le_exp.mpr hzu
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy.le))]
  rw [neg_sub]
  rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)]
  rw [neg_sub]
  calc
    Real.exp y - Real.exp x = Real.exp z * (y - x) := by
      have hyx : y - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxy)
      field_simp [hyx] at hz ⊢
      exact hz.symm
    _ ≤ Real.exp U * (y - x) := mul_le_mul_of_nonneg_right hmono (sub_nonneg.mpr hxy.le)

omit [MeasurableSpace Ω] in
/-- Absolute continuity of the exponential of an affine image of an absolutely continuous
function. -/
theorem exp_comp_affine_absolutelyContinuousOnInterval {G : ℝ → ℝ} {a b c d : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (c * G x + d)) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨C, hC⟩ := hG.exists_bound
  have hleU : ∀ x ∈ uIcc a b, c * G x + d ≤ |c| * C + |d| := by
    intro x hx
    calc
      c * G x + d ≤ |c * G x| + |d| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = |c| * |G x| + |d| := by rw [abs_mul]
      _ ≤ |c| * C + |d| := by
        gcongr
        exact hC x hx
  have hexpU : 0 < Real.exp (|c| * C + |d|) := Real.exp_pos _
  let M : ℝ := Real.exp (|c| * C + |d|) * (|c| + 1)
  have hMpos : 0 < M := mul_pos hexpU (by positivity : 0 < |c| + 1)
  rw [absolutelyContinuousOnInterval_iff] at hG
  obtain ⟨δ', hδ'pos, hδ'⟩ := hG (ε / M) (div_pos hε hMpos)
  refine ⟨δ', hδ'pos, fun E hE hsum ↦ ?_⟩
  by_cases hc : c = 0
  · subst c
    simp
    exact hε
  · have hpos : 0 < Real.exp (|c| * C + |d|) * |c| :=
      mul_pos hexpU (abs_pos.mpr hc)
    calc
      ∑ i ∈ Finset.range E.1, dist (Real.exp (c * G (E.2 i).1 + d))
          (Real.exp (c * G (E.2 i).2 + d))
          ≤ ∑ i ∈ Finset.range E.1,
            Real.exp (|c| * C + |d|) *
              |c * G (E.2 i).1 + d - (c * G (E.2 i).2 + d)| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa [Real.dist_eq] using
          abs_exp_sub_exp_le_exp_U (c * G (E.2 i).1 + d) (c * G (E.2 i).2 + d)
            (|c| * C + |d|) (hleU _ (hE.left i hi).left) (hleU _ (hE.left i hi).right)
      _ = Real.exp (|c| * C + |d|) * |c| *
          ∑ i ∈ Finset.range E.1, dist (G (E.2 i).1) (G (E.2 i).2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr (M := ℝ) rfl (fun i hi ↦ by
          rw [mul_assoc, Real.dist_eq]
          have : |c * G (E.2 i).1 + d - (c * G (E.2 i).2 + d)| =
              |c| * |G (E.2 i).1 - G (E.2 i).2| := by
            calc
              |c * G (E.2 i).1 + d - (c * G (E.2 i).2 + d)|
                  = |c * G (E.2 i).1 - c * G (E.2 i).2| := by
                congr 1
                ring
              _ = |c * (G (E.2 i).1 - G (E.2 i).2)| := by
                rw [mul_sub]
              _ = |c| * |G (E.2 i).1 - G (E.2 i).2| := by
                rw [abs_mul]
          rw [this])
      _ < Real.exp (|c| * C + |d|) * |c| * (ε / M) := by
        exact mul_lt_mul_of_pos_left (hδ' E hE hsum) hpos
      _ ≤ ε := by
        calc
          Real.exp (|c| * C + |d|) * |c| * (ε / M)
              ≤ Real.exp (|c| * C + |d|) * (|c| + 1) * (ε / M) := by
            gcongr
            exact le_add_of_nonneg_right zero_le_one
          _ = ε := by
            calc
              Real.exp (|c| * C + |d|) * (|c| + 1) * (ε / M) = (ε / M) * M := by
                unfold M
                ring
              _ = ε := div_mul_cancel₀ ε (ne_of_gt hMpos)

omit [MeasurableSpace Ω] in
/-- The fundamental theorem of calculus for the exponential of an accumulated integral:
`exp (c * (G v - G u)) - 1 = ∫ x in u..v, c * g x * exp (c * (G x - G u))` where
`G x = ∫ t in 0..x, g t`. -/
theorem intervalIntegral_exp_comp_eq {g : ℝ → ℝ} {u v c : ℝ} (h0u : 0 ≤ u) (huv : u ≤ v)
    (hg : IntervalIntegrable g volume 0 v) :
    Real.exp (c * ((∫ x in (0:ℝ)..v, g x) - (∫ x in (0:ℝ)..u, g x))) - 1 =
      ∫ x in u..v, c * g x *
        Real.exp (c * ((∫ t in (0:ℝ)..x, g t) - (∫ t in (0:ℝ)..u, g t))) := by
  let G : ℝ → ℝ := fun x ↦ ∫ t in (0:ℝ)..x, g t
  change Real.exp (c * (G v - G u)) - 1 = ∫ x in u..v, c * g x * Real.exp (c * (G x - G u))
  have h0v : 0 ≤ v := le_trans h0u huv
  have hG : AbsolutelyContinuousOnInterval G 0 v :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by exact left_mem_uIcc)
  have hsubset : uIcc u v ⊆ uIcc 0 v := by
    intro x hx
    rw [uIcc_of_le huv] at hx
    rw [uIcc_of_le h0v]
    exact ⟨le_trans h0u hx.1, hx.2⟩
  have hGu : AbsolutelyContinuousOnInterval G u v := hG.mono hsubset
  set d : ℝ := -(c * G u) with hd
  have hFac : AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (c * G x + d)) u v :=
    exp_comp_affine_absolutelyContinuousOnInterval (G := G) (a := u) (b := v) (c := c) (d := d)
      hGu
  have hderiv : ∀ᵐ x, x ∈ uIcc u v →
      HasDerivAt (fun x ↦ Real.exp (c * G x + d)) (c * g x * Real.exp (c * G x + d)) x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hGderiv
    intro hxuIcc
    have hGderivx : HasDerivAt G (g x) x :=
      hGderiv (hsubset hxuIcc) 0 (by exact left_mem_uIcc)
    have hinner : HasDerivAt (fun y ↦ c * G y + d) (c * g x) x :=
      hGderivx.const_mul c |>.add_const d
    have hcomp : HasDerivAt (fun y ↦ Real.exp (c * G y + d))
        (Real.exp (c * G x + d) * (c * g x)) x := hinner.exp
    convert hcomp using 1
    ring
  have hFTC : ∫ x in u..v, deriv (fun x ↦ Real.exp (c * G x + d)) x =
      Real.exp (c * G v + d) - Real.exp (c * G u + d) :=
    hFac.integral_deriv_eq_sub
  have hcongr : ∫ x in u..v, deriv (fun x ↦ Real.exp (c * G x + d)) x =
      ∫ x in u..v, c * g x * Real.exp (c * G x + d) := by
    exact intervalIntegral.integral_congr_ae (μ := volume) (by
      filter_upwards [hderiv] with x hx
      intro hxuIoc
      exact (hx (uIoc_subset_uIcc hxuIoc)).deriv)
  calc
    Real.exp (c * (G v - G u)) - 1 = Real.exp (c * G v + d) - Real.exp (c * G u + d) := by
      congr 1
      · congr 1
        rw [hd]
        ring
      · rw [hd]
        simp
    _ = ∫ x in u..v, deriv (fun x ↦ Real.exp (c * G x + d)) x := by
      rw [← hFTC]
    _ = ∫ x in u..v, c * g x * Real.exp (c * G x + d) := hcongr
    _ = ∫ x in u..v, c * g x * Real.exp (c * (G x - G u)) := by
      exact intervalIntegral.integral_congr (μ := volume) (fun x _ ↦ by
        congr 1
        rw [hd]
        ring_nf)

/-! ## Compensator continuity and adaptedness -/

omit [MeasurableSpace Ω] in
/-- Integrability for the time measure over `Ioc 0 v` is the same as interval integrability of
the pullback along `Real.toNNReal`. -/
theorem integrableOn_timeMeasure_iff_intervalIntegrable {f : ℝ≥0 → ℝ} {v : ℝ≥0} :
    IntegrableOn f (Ioc (0 : ℝ≥0) v) timeMeasure ↔
      IntervalIntegrable (fun x ↦ f (Real.toNNReal x)) volume 0 (v : ℝ) := by
  have hcoeEmb : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  constructor
  · intro h
    have hmap : Integrable (fun x ↦ f (Real.toNNReal x))
        ((timeMeasure.restrict (Ioc (0 : ℝ≥0) v)).map ((↑) : ℝ≥0 → ℝ)) := by
      refine (hcoeEmb.integrable_map_iff).mpr ?_
      have h' : Integrable f (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)) := by
        change IntegrableOn f (Ioc (0 : ℝ≥0) v) timeMeasure
        exact h
      convert h' using 1
      funext r
      change f (Real.toNNReal (r : ℝ)) = f r
      rw [Real.toNNReal_coe]
    rw [IntervalIntegrable]
    rw [map_coe_timeMeasure_restrict (u := 0) (v := v)] at hmap
    constructor
    · change IntegrableOn (fun x ↦ f (Real.toNNReal x)) (Ioc (0 : ℝ) (v : ℝ)) volume
      exact hmap
    · rw [Ioc_eq_empty (not_lt.mpr (by positivity : (0 : ℝ) ≤ (v : ℝ)))]
      exact integrableOn_empty
  · intro h
    rw [IntervalIntegrable] at h
    have hmap : Integrable (fun x ↦ f (Real.toNNReal x))
        ((timeMeasure.restrict (Ioc (0 : ℝ≥0) v)).map ((↑) : ℝ≥0 → ℝ)) := by
      rw [map_coe_timeMeasure_restrict (u := 0) (v := v)]
      change IntegrableOn (fun x ↦ f (Real.toNNReal x)) (Ioc (0 : ℝ) (v : ℝ)) volume
      exact h.1
    have h1 : Integrable ((fun x ↦ f (Real.toNNReal x)) ∘ ((↑) : ℝ≥0 → ℝ))
        (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)) :=
      (hcoeEmb.integrable_map_iff (μ := timeMeasure.restrict (Ioc (0 : ℝ≥0) v))
        (g := fun x ↦ f (Real.toNNReal x))).mp hmap
    change Integrable (fun r : ℝ≥0 ↦ f (Real.toNNReal (r : ℝ)))
      (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)) at h1
    have hcomp : (fun r : ℝ≥0 ↦ f (Real.toNNReal (r : ℝ))) = f := by
      funext r
      rw [Real.toNNReal_coe]
    rw [hcomp] at h1
    change IntegrableOn f (Ioc (0 : ℝ≥0) v) timeMeasure
    exact h1

omit [MeasurableSpace Ω] in
/-- Lift continuity on every `Icc 0 T` to global continuity on `ℝ≥0`. -/
theorem continuous_of_continuousOn_Icc {f : ℝ≥0 → ℝ}
    (hf : ∀ T : ℝ≥0, ContinuousOn f (Icc 0 T)) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro t
  have hcont : ContinuousWithinAt f (Icc 0 (t + 1)) t :=
    (hf (t + 1)).continuousWithinAt (by simp)
  refine hcont.continuousAt ?_
  rw [Metric.mem_nhds_iff]
  refine ⟨1, by norm_num, ?_⟩
  intro s hs
  rw [Metric.mem_ball] at hs
  have hsd : dist (s : ℝ) (t : ℝ) < 1 := by
    have : |(s : ℝ) - (t : ℝ)| < 1 := by
      simpa [NNReal.dist_eq] using hs
    simpa [Real.dist_eq] using this
  have hle : (s : ℝ) ≤ (t : ℝ) + 1 := by
    rw [Real.dist_eq] at hsd
    nlinarith [abs_lt.mp hsd]
  exact ⟨s.2, by exact_mod_cast hle⟩

omit [MeasurableSpace Ω] in
/-- The accumulated intensity is continuous in time along every path. -/
theorem A_continuous {Λ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hΛint : ∀ t, IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure) :
    Continuous (fun t : ℝ≥0 ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
  refine continuous_of_continuousOn_Icc fun T ↦ ?_
  have hii (t : ℝ≥0) : IntervalIntegrable (fun x ↦ Λ (Real.toNNReal x) ω) volume 0 (t : ℝ) :=
    (integrableOn_timeMeasure_iff_intervalIntegrable (f := fun s ↦ Λ s ω) (v := t)).mp (hΛint t)
  have hAC : AbsolutelyContinuousOnInterval
      (fun x : ℝ ↦ ∫ r in (0:ℝ)..x, Λ (Real.toNNReal r) ω) 0 (T : ℝ) :=
    (hii T).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by exact left_mem_uIcc)
  have hcontReal : ContinuousOn (fun x : ℝ ↦ ∫ r in (0:ℝ)..x, Λ (Real.toNNReal r) ω)
      (uIcc 0 (T : ℝ)) :=
    hAC.uniformContinuousOn.continuousOn
  have hsub : MapsTo (fun t : ℝ≥0 ↦ (t : ℝ)) (Icc 0 T) (uIcc 0 (T : ℝ)) := by
    intro t ht
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ (T : ℝ))]
    exact_mod_cast ht
  have hbridge : ∀ t : ℝ≥0, integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω =
      ∫ x in (0:ℝ)..(t:ℝ), Λ (Real.toNNReal x) ω := by
    intro t
    rw [integratedIntensity]
    simpa using integral_timeMeasure_eq_intervalIntegral (fun s ↦ Λ s ω) 0 t (by simp)
  refine (hcontReal.comp NNReal.continuous_coe.continuousOn hsub).congr ?_
  intro t _
  exact hbridge t

/-- The accumulated intensity is adapted whenever the centred counting process is a martingale. -/
theorem A_stronglyAdapted {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    StronglyAdapted ℱ (fun t ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
  have hM : Martingale
      (fun t ω ↦ (N t ω : ℝ) - integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) ℱ μ :=
    hΛ.centered_martingale
  intro t
  have hNt : StronglyMeasurable[ℱ t] (fun ω ↦ (N t ω : ℝ)) := hN.stronglyAdapted t
  have hMt : StronglyMeasurable[ℱ t]
      (fun ω ↦ (N t ω : ℝ) - integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) :=
    hM.stronglyAdapted t
  have hdiff : StronglyMeasurable[ℱ t] (fun ω ↦ (N t ω : ℝ) -
      ((N t ω : ℝ) - integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω)) :=
    hNt.sub hMt
  convert hdiff using 1
  ext ω
  ring

/-! ## Finite-horizon compensator bounds -/

omit [MeasurableSpace Ω] in
/-- Bounded `Ioc` intervals have finite time measure. -/
theorem timeMeasure_Ioc_lt_top (u v : ℝ≥0) : timeMeasure (Ioc u v) < ∞ := by
  have hm : ((timeMeasure.restrict (Ioc u v)).map ((↑) : ℝ≥0 → ℝ)) Set.univ =
      (volume.restrict (Ioc (u : ℝ) (v : ℝ))) Set.univ :=
    congrArg (fun m : Measure ℝ ↦ m Set.univ) (map_coe_timeMeasure_restrict u v)
  rw [Measure.map_apply_of_aemeasurable (NNReal.continuous_coe.measurable.aemeasurable)
    MeasurableSet.univ, Set.preimage_univ] at hm
  have hrest : (timeMeasure.restrict (Ioc u v)) Set.univ = timeMeasure (Ioc u v) := by
    simp [Measure.restrict_apply]
  rw [hrest] at hm
  rw [hm]
  simp [Measure.restrict_apply]

/-- Under a nonnegative intensity bounded by `C₀`, the accumulated unit compensator satisfies
`0 ≤ A t ≤ C₀ t` pathwise. -/
theorem integratedIntensity_one_nonneg_le {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hΛupper : ∀ t ω, Λ t ω ≤ C₀) (t : ℝ≥0) (ω : Ω) :
    0 ≤ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ∧
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ≤ C₀ * (t : ℝ) := by
  have _hC₀ : 0 ≤ C₀ := hC₀
  have hnonneg : 0 ≤ ∫ s in Ioc (0 : ℝ≥0) t, Λ s ω ∂timeMeasure := by
    exact setIntegral_nonneg measurableSet_Ioc (fun s _ ↦ hΛ.nonneg s ω)
  have hmono : ∫ s in Ioc (0 : ℝ≥0) t, Λ s ω ∂timeMeasure ≤
      ∫ s in Ioc (0 : ℝ≥0) t, (fun _ ↦ C₀) s ∂timeMeasure := by
    refine setIntegral_mono_on (hΛ.integrableOn t ω) ?_ measurableSet_Ioc ?_
    · exact integrableOn_const (C := C₀) (timeMeasure_Ioc_lt_top 0 t).ne
    · intro s _
      exact hΛupper s ω
  have hconst : ∫ s in Ioc (0 : ℝ≥0) t, (fun _ ↦ C₀) s ∂timeMeasure = C₀ * (t : ℝ) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ ↦ C₀) 0 t (by simp)]
    rw [intervalIntegral.integral_const]
    simp
    ring
  simpa [integratedIntensity] using ⟨hnonneg, hmono.trans_eq hconst⟩

/-! A finite or probability base measure turns the pathwise bound above into the integrability
assumption required by the bounded-predictable closure. -/

theorem integratedIntensity_one_integrable_of_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hΛupper : ∀ t ω, Λ t ω ≤ C₀)
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ) (t : ℝ≥0) :
    Integrable (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ := by
  have hAadapt := A_stronglyAdapted hN hΛ
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ :=
    ((hAadapt t).mono (ℱ.le t)).measurable.aestronglyMeasurable
  refine Integrable.of_bound hmeas (C₀ * (t : ℝ)) ?_
  filter_upwards with ω
  have hbound := integratedIntensity_one_nonneg_le (μ := μ) (ℱ := ℱ) hC₀ hΛ hΛupper t ω
  rw [Real.norm_eq_abs, abs_of_nonneg hbound.1]
  exact hbound.2

/-! ## The exponential left weight -/

/-- The left weight in the exponential martingale path identity: with `η = exp(-θ₀)`,
`H s = (η - 1) η^{N(s-)} exp((1 - η) ∫₀ˢ Λ)`. -/
noncomputable def expWeight (N : ℝ≥0 → Ω → ℕ) (Λ : ℝ≥0 → Ω → ℝ) (θ₀ : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω ↦ (Real.exp (-θ₀) - 1) * (Real.exp (-θ₀) ^ (countBefore N s ω)) *
    Real.exp ((1 - Real.exp (-θ₀)) * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)

/-- The exponential left weight is strongly predictable. -/
theorem expWeight_stronglyPredictable {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ} {θ₀ : ℝ}
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    IsStronglyPredictable ℱ (expWeight N Λ θ₀) := by
  have hcbNat : Measurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦ countBefore N z.1 z.2) := by
    classical
    intro B hB
    have hpre : (fun z : ℝ≥0 × Ω ↦ countBefore N z.1 z.2) ⁻¹' B =
        ⋃ n : ℕ, {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = n ∧ n ∈ B} := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_iUnion]
        exact ⟨countBefore N z.1 z.2, rfl, hz⟩
      · intro h
        rw [Set.mem_iUnion] at h
        rcases h with ⟨n, hn, hnB⟩
        simpa [hn] using hnB
    rw [hpre]
    refine MeasurableSet.iUnion fun n ↦ ?_
    by_cases hn : n ∈ B
    · have hset : {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = n ∧ n ∈ B} =
          {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = n} := by
        ext z
        simp [hn]
      rw [hset]
      exact measurableSet_countBefore_eq hN.stronglyAdapted (fun ω ↦ hN.monotone ω) n
    · have hset : {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = n ∧ n ∈ B} = ∅ := by
        ext z
        simp [hn]
      rw [hset]
      exact @MeasurableSet.empty (ℝ≥0 × Ω) ℱ.predictable
  have hpow : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × Ω ↦ Real.exp (-θ₀) ^ (countBefore N z.1 z.2)) := by
    have hpowMeas : Measurable (fun n : ℕ ↦ Real.exp (-θ₀) ^ n) :=
      (continuous_of_discreteTopology (f := fun n : ℕ ↦ Real.exp (-θ₀) ^ n)).measurable
    exact (hpowMeas.comp hcbNat).stronglyMeasurable
  have hAstrong : IsStronglyPredictable ℱ
      (fun t ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) :=
    MeasureTheory.IsStronglyPredictable.of_continuous_adapted
      (A_stronglyAdapted hN hΛ)
      (fun ω ↦ A_continuous (fun t ↦ hΛ.integrableOn t ω))
  have hbase : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × Ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) z.1 z.2) := by
    exact hAstrong
  have hcont : Continuous (fun x : ℝ ↦ Real.exp ((1 - Real.exp (-θ₀)) * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hexpA : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × Ω ↦ Real.exp ((1 - Real.exp (-θ₀)) *
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) z.1 z.2)) :=
    hcont.comp_stronglyMeasurable hbase
  have hH : StronglyMeasurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦
      (Real.exp (-θ₀) - 1) * (Real.exp (-θ₀) ^ (countBefore N z.1 z.2)) *
        Real.exp ((1 - Real.exp (-θ₀)) *
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) z.1 z.2)) :=
    (hpow.const_mul (Real.exp (-θ₀) - 1)).mul hexpA
  exact hH

/-- The truncated exponential left weight is bounded and predictable. -/
theorem expWeight_boundedPredictable {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ} {θ₀ C₀ : ℝ} (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ t ω, Λ t ω ≤ C₀) {T : ℝ≥0}
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    IsBoundedPredictable ℱ (fun s ω ↦ if s ≤ T then expWeight N Λ θ₀ s ω else 0) := by
  let η : ℝ := Real.exp (-θ₀)
  have hηpos : 0 < η := by unfold η; exact Real.exp_pos _
  have hηlt1 : η < 1 := by
    unfold η
    have h : Real.exp (-θ₀) < Real.exp 0 := Real.exp_lt_exp.mpr (neg_lt_zero.mpr hθ0)
    simpa using h
  have hηle1 : η ≤ 1 := le_of_lt hηlt1
  have hcpos : 0 < 1 - η := sub_pos.mpr hηlt1
  have hpred : IsStronglyPredictable ℱ (fun s ω ↦ if s ≤ T then expWeight N Λ θ₀ s ω else 0) := by
    have hbase : StronglyMeasurable[ℱ.predictable] (Function.uncurry (expWeight N Λ θ₀)) :=
      expWeight_stronglyPredictable hN hΛ
    have hset : MeasurableSet[ℱ.predictable] {z : ℝ≥0 × Ω | z.1 ≤ T} := by
      have hset' : {z : ℝ≥0 × Ω | z.1 ≤ T} =
          ({0} : Set ℝ≥0) ×ˢ Set.univ ∪ (Ioc (0 : ℝ≥0) T) ×ˢ Set.univ := by
        ext z
        constructor
        · intro hz
          by_cases hz0 : z.1 = 0
          · left
            exact ⟨hz0, trivial⟩
          · right
            exact ⟨⟨pos_iff_ne_zero.2 hz0, hz⟩, trivial⟩
        · rintro (⟨hz0, _⟩ | ⟨hzIoc, _⟩)
          · change z.1 ≤ T
            rw [Set.mem_singleton_iff.mp hz0]
            exact zero_le
          · exact hzIoc.2
      rw [hset']
      exact (measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ) MeasurableSet.univ).union
        (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) (0 : ℝ≥0) T MeasurableSet.univ)
    have hind : StronglyMeasurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦
        ({z' : ℝ≥0 × Ω | z'.1 ≤ T}.indicator (fun _ ↦ (1 : ℝ)) z)) :=
      stronglyMeasurable_const.indicator hset
    have hcut : StronglyMeasurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦
        Function.uncurry (expWeight N Λ θ₀) z *
          ({z' : ℝ≥0 × Ω | z'.1 ≤ T}.indicator (fun _ ↦ (1 : ℝ)) z)) :=
      hbase.mul hind
    have hfun : (Function.uncurry (fun s ω ↦ if s ≤ T then expWeight N Λ θ₀ s ω else 0)) =
        (fun z : ℝ≥0 × Ω ↦ Function.uncurry (expWeight N Λ θ₀) z *
          ({z' : ℝ≥0 × Ω | z'.1 ≤ T}.indicator (fun _ ↦ (1 : ℝ)) z)) := by
      ext z
      change (if z.1 ≤ T then expWeight N Λ θ₀ z.1 z.2 else 0) =
        expWeight N Λ θ₀ z.1 z.2 *
          ({z' : ℝ≥0 × Ω | z'.1 ≤ T}.indicator (fun _ ↦ (1 : ℝ)) z)
      by_cases hz : z.1 ≤ T
      · simp [hz, Set.indicator]
      · simp [hz, Set.indicator]
    change StronglyMeasurable[ℱ.predictable]
      (Function.uncurry (fun s ω ↦ if s ≤ T then expWeight N Λ θ₀ s ω else 0))
    rw [hfun]
    exact hcut
  have hCnonneg : 0 ≤ (1 - η) * Real.exp ((1 - η) * C₀ * (T : ℝ)) :=
    mul_nonneg (le_of_lt hcpos) (le_of_lt (Real.exp_pos _))
  refine ⟨hpred, (1 - η) * Real.exp ((1 - η) * C₀ * (T : ℝ)), hCnonneg, ?_⟩
  intro s ω
  by_cases hs : s ≤ T
  · simp [hs]
    have hAsmono : ∫ (t : ℝ≥0) in Ioc (0 : ℝ≥0) s, Λ t ω ∂timeMeasure ≤
        ∫ (t : ℝ≥0) in Ioc (0 : ℝ≥0) s, (fun _ ↦ C₀) t ∂timeMeasure := by
      refine setIntegral_mono_on (hΛ.integrableOn s ω) ?_ measurableSet_Ioc ?_
      · exact integrableOn_const (C := C₀) (timeMeasure_Ioc_lt_top 0 s).ne
      · intro t ht
        exact hΛupper t ω
    have hconst : ∫ (t : ℝ≥0) in Ioc (0 : ℝ≥0) s, (fun _ ↦ C₀) t ∂timeMeasure = C₀ * (s : ℝ) := by
      rw [integral_timeMeasure_eq_intervalIntegral (fun _ ↦ C₀) 0 s (by simp)]
      rw [intervalIntegral.integral_const]
      simp
      ring
    have hAsI : ∫ (t : ℝ≥0) in Ioc (0 : ℝ≥0) s, Λ t ω ∂timeMeasure ≤ C₀ * (T : ℝ) := by
      rw [hconst] at hAsmono
      exact hAsmono.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hC₀)
    have hAs : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω ≤ C₀ * (T : ℝ) := by
      rw [integratedIntensity]
      simpa using hAsI
    have hH : expWeight N Λ θ₀ s ω =
        (η - 1) * (η ^ (countBefore N s ω) * Real.exp ((1 - η) *
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)) := by
      unfold expWeight
      change (η - 1) * (η ^ countBefore N s ω) *
          Real.exp ((1 - η) * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω) =
        (η - 1) * (η ^ countBefore N s ω * Real.exp ((1 - η) *
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω))
      ring
    calc
      |expWeight N Λ θ₀ s ω| =
          |(η - 1) * (η ^ (countBefore N s ω) * Real.exp ((1 - η) *
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω))| := by rw [hH]
      _ = (1 - η) * (η ^ (countBefore N s ω) * Real.exp ((1 - η) *
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)) := by
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hηle1), neg_sub]
        rw [abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hηpos) _)
          (le_of_lt (Real.exp_pos _)))]
      _ ≤ (1 - η) * (1 * Real.exp ((1 - η) * (C₀ * (T : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
        refine mul_le_mul (pow_le_one₀ (le_of_lt hηpos) hηle1) ?_
          (le_of_lt (Real.exp_pos _)) zero_le_one
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAs (le_of_lt hcpos))
      _ = (1 - η) * Real.exp ((1 - η) * C₀ * (T : ℝ)) := by ring_nf
  · simp [hs]
    exact hCnonneg

/-! A bounded predictable exponential weight has an integrable time-section on every finite
interval.  This is the analytic input for splitting the compensator at attained jumps. -/

theorem expWeight_cut_intervalIntegrable {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {θ₀ C₀ : ℝ} (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ t ω, Λ t ω ≤ C₀) {T v : ℝ≥0}
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ) (ω : Ω) :
    IntervalIntegrable
      (fun x : ℝ ↦ (if Real.toNNReal x ≤ T then expWeight N Λ θ₀ (Real.toNNReal x) ω else 0) *
        Λ (Real.toNNReal x) ω) volume 0 (v : ℝ) := by
  obtain ⟨hHpred, B, hB, hHbound⟩ :=
    expWeight_boundedPredictable hθ0 hC₀ hΛupper (T := T) hN hΛ
  have hHsec : Measurable
      (fun s : ℝ≥0 ↦ if s ≤ T then expWeight N Λ θ₀ s ω else 0) := by
    have hsm : StronglyMeasurable[Prod.instMeasurableSpace]
        (Function.uncurry (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0)) :=
      hHpred.mono (predictable_le_ambient ℱ)
    exact hsm.measurable.comp (measurable_id.prodMk measurable_const)
  have hres : Integrable (fun s : ℝ≥0 ↦ Λ s ω)
      (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)) := hΛ.integrableOn v ω
  have hprod : Integrable
      (fun s : ℝ≥0 ↦ (if s ≤ T then expWeight N Λ θ₀ s ω else 0) * Λ s ω)
      (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)) := by
    refine hres.bdd_mul (c := B) hHsec.aestronglyMeasurable ?_
    exact Eventually.of_forall (fun s ↦ hHbound s ω)
  have hprodOn : IntegrableOn
      (fun s : ℝ≥0 ↦ (if s ≤ T then expWeight N Λ θ₀ s ω else 0) * Λ s ω)
      (Ioc (0 : ℝ≥0) v) timeMeasure := hprod
  exact (integrableOn_timeMeasure_iff_intervalIntegrable (f := fun s ↦
    (if s ≤ T then expWeight N Λ θ₀ s ω else 0) * Λ s ω) (v := v)).mp hprodOn

/-! ## Path identity for the exponential martingale -/
omit [MeasurableSpace Ω] in
/-- The counting integral of a constant weight is the constant times the count. -/
theorem countingIntegral_const {N : ℝ≥0 → Ω → ℕ} (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    countingIntegral N (fun _ _ ↦ c) t ω = c * (N t ω : ℝ) := by
  rw [countingIntegral, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_range]
  ring

omit [MeasurableSpace Ω] in
/-- The counting exponential starts at one whenever the count starts at zero. -/
theorem countingExponential_zero_of_N0 {N : ℝ≥0 → Ω → ℕ} {Λ θ : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hN0 : N 0 ω = 0) :
    countingExponential N Λ θ 0 ω = 1 := by
  rw [countingExponential, jumpExponentialProduct, hN0]
  simp [integratedIntensity]

omit [MeasurableSpace Ω] in
/-- Additive-exponent form of the exponential with constant negative rate: `Z t` equals
`exp(-θ₀)^{N t}` times the compensator exponential. -/
theorem countingExponential_pow_exp (N : ℝ≥0 → Ω → ℕ) (Λ : ℝ≥0 → Ω → ℝ) (θ₀ : ℝ)
    (t : ℝ≥0) (ω : Ω)
    (hΛint : IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure) :
    countingExponential N Λ (fun _ _ ↦ -θ₀) t ω =
      Real.exp (-θ₀) ^ (N t ω) * Real.exp ((1 - Real.exp (-θ₀)) *
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
  have _hΛint : IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure := hΛint
  rw [countingExponential_eq_exp, countingIntegral_const, integratedIntensity]
  dsimp only [expSubOne]
  rw [integral_timeMeasure_eq_intervalIntegral (fun s ↦ (Real.exp (-θ₀) - 1) * Λ s ω) 0 t
    (by simp)]
  rw [intervalIntegral.integral_const_mul]
  have hb : (∫ x in ((0 : ℝ≥0) : ℝ)..((t : ℝ≥0) : ℝ), Λ (Real.toNNReal x) ω) =
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω := by
    rw [integratedIntensity]
    simpa using (integral_timeMeasure_eq_intervalIntegral (fun s ↦ (1 : ℝ) * Λ s ω) 0 t
      (by simp)).symm
  rw [hb]
  rw [sub_eq_add_neg, Real.exp_add]
  rw [← Real.exp_nat_mul]
  congr 1
  · ring_nf
  · ring_nf

omit [MeasurableSpace Ω] in
/-- Interval integrability of the real pullback follows from integrability for the time measure. -/
theorem intervalIntegrable_toReal_of_integrableOn {f : ℝ≥0 → ℝ} {v : ℝ≥0}
    (hf : IntegrableOn f (Ioc (0 : ℝ≥0) v) timeMeasure) :
    IntervalIntegrable (fun x : ℝ ↦ f (Real.toNNReal x)) volume 0 (v : ℝ) := by
  have hemb : MeasurableEmbedding (NNReal.toReal) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  constructor
  · change Integrable (fun x : ℝ ↦ f (Real.toNNReal x))
      (volume.restrict (Ioc (0 : ℝ) (v : ℝ)))
    have hmap : (timeMeasure.restrict (Ioc (0 : ℝ≥0) v)).map NNReal.toReal =
        volume.restrict (Ioc (0 : ℝ) (v : ℝ)) := by
      simpa using map_coe_timeMeasure_restrict 0 v
    rw [← hmap]
    refine (hemb.integrable_map_iff (μ := timeMeasure.restrict (Ioc (0 : ℝ≥0) v))
      (g := fun x : ℝ ↦ f (Real.toNNReal x))).2 ?_
    change Integrable (fun r : ℝ≥0 ↦ f (Real.toNNReal ((r : ℝ))))
      (timeMeasure.restrict (Ioc (0 : ℝ≥0) v))
    have hcomp : (fun r : ℝ≥0 ↦ f (Real.toNNReal ((r : ℝ)))) = fun r ↦ f r := by
      ext r
      rw [Real.toNNReal_coe]
    rw [hcomp]
    exact hf
  · change Integrable (fun x : ℝ ↦ f (Real.toNNReal x))
      (volume.restrict (Ioc (v : ℝ) (0 : ℝ)))
    rw [Ioc_eq_empty (not_lt.mpr (by exact_mod_cast (zero_le : 0 ≤ v)))]
    rw [Measure.restrict_empty]
    exact integrable_zero_measure

omit [MeasurableSpace Ω] in
/-- Additivity of the integrated intensity across two adjacent cells. -/
theorem integratedIntensity_add_Ioc {Λ H : ℝ≥0 → Ω → ℝ} {ω : Ω} {w v u : ℝ≥0}
    (hwv : w ≤ v) (hvu : v ≤ u)
    (hHI : IntervalIntegrable (fun x : ℝ ↦ H (Real.toNNReal x) ω * Λ (Real.toNNReal x) ω)
      volume 0 (u : ℝ)) :
    integratedIntensity Λ H u ω = integratedIntensity Λ H w ω +
        ∫ s in Ioc w v, H s ω * Λ s ω ∂timeMeasure +
        ∫ s in Ioc v u, H s ω * Λ s ω ∂timeMeasure := by
  let g : ℝ → ℝ := fun x ↦ H (Real.toNNReal x) ω * Λ (Real.toNNReal x) ω
  have hwu : w ≤ u := hwv.trans hvu
  have hIw : IntervalIntegrable g volume 0 (w : ℝ) :=
    hHI.mono_set (by
      rw [uIcc_of_le (by exact_mod_cast (zero_le : 0 ≤ w)), uIcc_of_le (by exact_mod_cast (zero_le : 0 ≤ u))]
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hwu))
  have hIwu : IntervalIntegrable g volume (w : ℝ) (u : ℝ) :=
    hHI.mono_set (by
      rw [uIcc_of_le (by exact_mod_cast hwu), uIcc_of_le (by exact_mod_cast (zero_le : 0 ≤ u))]
      exact Set.Icc_subset_Icc (by exact_mod_cast (zero_le : 0 ≤ w)) le_rfl)
  have hIwv : IntervalIntegrable g volume (w : ℝ) (v : ℝ) :=
    hIwu.mono_set (by
      rw [uIcc_of_le (by exact_mod_cast hwv), uIcc_of_le (by exact_mod_cast hwu)]
      exact Set.Icc_subset_Icc le_rfl (by exact_mod_cast hvu))
  have hIvu : IntervalIntegrable g volume (v : ℝ) (u : ℝ) :=
    hIwu.mono_set (by
      rw [uIcc_of_le (by exact_mod_cast hvu), uIcc_of_le (by exact_mod_cast hwu)]
      exact Set.Icc_subset_Icc (by exact_mod_cast hwv) le_rfl)
  have h1 : (∫ x in (0:ℝ)..(w:ℝ), g x) + (∫ x in (w:ℝ)..(u:ℝ), g x) =
      ∫ x in (0:ℝ)..(u:ℝ), g x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := g)
      (a := (0:ℝ)) (b := (w:ℝ)) (c := (u:ℝ)) hIw hIwu
  have h2 : (∫ x in (w:ℝ)..(v:ℝ), g x) + (∫ x in (v:ℝ)..(u:ℝ), g x) =
      ∫ x in (w:ℝ)..(u:ℝ), g x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := g)
      (a := (w:ℝ)) (b := (v:ℝ)) (c := (u:ℝ)) hIwv hIvu
  have hbw : ∫ x in (0:ℝ)..(w:ℝ), g x = integratedIntensity Λ H w ω := by
    dsimp [g]
    rw [integratedIntensity]
    exact (integral_timeMeasure_eq_intervalIntegral (fun s ↦ H s ω * Λ s ω) 0 w
      (by simp)).symm
  have hbwv : ∫ x in (w:ℝ)..(v:ℝ), g x = ∫ s in Ioc w v, H s ω * Λ s ω ∂timeMeasure := by
    dsimp [g]
    exact (integral_timeMeasure_eq_intervalIntegral (fun s ↦ H s ω * Λ s ω) w v
      (by exact_mod_cast hwv)).symm
  have hbvu : ∫ x in (v:ℝ)..(u:ℝ), g x = ∫ s in Ioc v u, H s ω * Λ s ω ∂timeMeasure := by
    dsimp [g]
    exact (integral_timeMeasure_eq_intervalIntegral (fun s ↦ H s ω * Λ s ω) v u
      (by exact_mod_cast hvu)).symm
  have hb0 : ∫ x in (0:ℝ)..(u:ℝ), g x = integratedIntensity Λ H u ω := by
    dsimp [g]
    rw [integratedIntensity]
    exact (integral_timeMeasure_eq_intervalIntegral (fun s ↦ H s ω * Λ s ω) 0 u
      (by simp)).symm
  rw [← hb0, ← hbw, ← hbwv, ← hbvu]
  nlinarith [h1, h2]

omit [MeasurableSpace Ω] in
/-- One more attained jump adds its weight to the counting integral. -/
theorem countingIntegral_add_jump {N : ℝ≥0 → Ω → ℕ} {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {w u : ℝ≥0} {m : ℕ} (hNw : N w ω = m) (hNu : N u ω = m + 1) :
    countingIntegral N H u ω = countingIntegral N H w ω + H (jumpTime N m ω) ω := by
  rw [countingIntegral, countingIntegral, hNw, hNu, Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
/-- On an interval on which the left count is constant, the exponential weight has the explicit
compensator integral `-η^m (exp(c A_v) - exp(c A_u))`. -/
theorem expWeight_integral_Ioc {Λ : ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {θ₀ : ℝ}
    {u v : ℝ≥0} {m : ℕ} (hθ0 : 0 < θ₀) (huv : u ≤ v)
    (hcount : ∀ s ∈ Ioc u v, countBefore N s ω = m)
    (hΛint : IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) v) timeMeasure) :
    ∫ s in Ioc u v, expWeight N Λ θ₀ s ω * Λ s ω ∂timeMeasure =
      -(Real.exp (-θ₀) ^ m) *
        (Real.exp ((1 - Real.exp (-θ₀)) *
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω) -
          Real.exp ((1 - Real.exp (-θ₀)) *
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)) := by
  let η : ℝ := Real.exp (-θ₀)
  let c : ℝ := 1 - η
  let g : ℝ → ℝ := fun x ↦ Λ (Real.toNNReal x) ω
  let G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hηpos : 0 < η := by
    dsimp [η]
    exact Real.exp_pos _
  have hηlt : η < 1 := by
    dsimp [η]
    simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hθ0)
  have hcpos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr hηlt
  have hinterval : IntervalIntegrable g volume 0 (v : ℝ) := by
    dsimp [g]
    exact intervalIntegrable_toReal_of_integrableOn hΛint
  have hFTC := intervalIntegral_exp_comp_eq (g := g) (u := (u : ℝ)) (v := (v : ℝ))
    (c := c) (by positivity) (by exact_mod_cast huv) hinterval
  have hAeq : ∀ x : ℝ, 0 ≤ x →
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (Real.toNNReal x) ω = G x := by
    intro x hx0
    have hxt : (Real.toNNReal x : ℝ) = x := by
      simpa using max_eq_left hx0
    dsimp [G, g]
    rw [integratedIntensity]
    simpa [hxt] using
      (integral_timeMeasure_eq_intervalIntegral (fun s ↦ Λ s ω) 0 (Real.toNNReal x)
        (by positivity))
  have hrewrite :
      (∫ s in Ioc u v, expWeight N Λ θ₀ s ω * Λ s ω ∂timeMeasure) =
        ∫ s in Ioc u v,
          (η - 1) * (η ^ m) * Real.exp (c *
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω) * Λ s ω ∂timeMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [expWeight, hcount s hs]
    simp [η, c]
  rw [hrewrite]
  rw [integral_timeMeasure_eq_intervalIntegral
    (fun s ↦ (η - 1) * (η ^ m) * Real.exp (c *
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω) * Λ s ω) u v huv]
  have hbridge_integrand :
      (∫ x in (u : ℝ)..(v : ℝ),
        (η - 1) * (η ^ m) * Real.exp (c *
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (Real.toNNReal x) ω) * g x) =
      ∫ x in (u : ℝ)..(v : ℝ), (η - 1) * (η ^ m) * Real.exp (c * G x) * g x := by
    apply intervalIntegral.integral_congr_ae
    refine Eventually.of_forall (fun x hxIoc ↦ ?_)
    have hxIoc' : x ∈ Ioc (u : ℝ) (v : ℝ) := by
      rw [uIoc_of_le (by exact_mod_cast huv)] at hxIoc
      exact hxIoc
    have hx0 : 0 ≤ x := le_trans (by exact_mod_cast u.2) (le_of_lt hxIoc'.1)
    rw [hAeq x hx0]
  rw [hbridge_integrand]
  have hscale :
      (∫ x in (u : ℝ)..(v : ℝ),
        (η - 1) * (η ^ m) * Real.exp (c * G x) * g x) =
      -η ^ m * Real.exp (c * G (u : ℝ)) *
        (∫ x in (u : ℝ)..(v : ℝ), c * g x * Real.exp (c * (G x - G (u : ℝ)))) := by
    calc
      (∫ x in (u : ℝ)..(v : ℝ),
          (η - 1) * (η ^ m) * Real.exp (c * G x) * g x) =
          ∫ x in (u : ℝ)..(v : ℝ),
            (-η ^ m * Real.exp (c * G (u : ℝ))) *
              (c * g x * Real.exp (c * (G x - G (u : ℝ)))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hexp : Real.exp (c * G x) = Real.exp (c * G (u : ℝ)) *
            Real.exp (c * (G x - G (u : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          ring
        change (η - 1) * η ^ m * Real.exp (c * G x) * g x =
          -η ^ m * Real.exp (c * G (u : ℝ)) *
            (c * g x * Real.exp (c * (G x - G (u : ℝ))))
        rw [hexp]
        dsimp [c]
        ring
      _ = -η ^ m * Real.exp (c * G (u : ℝ)) *
          (∫ x in (u : ℝ)..(v : ℝ), c * g x * Real.exp (c * (G x - G (u : ℝ)))) := by
        rw [intervalIntegral.integral_const_mul]
  rw [hscale, ← hFTC]
  have hAu : G (u : ℝ) = integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω := by
    rw [← hAeq (u : ℝ) (by positivity)]
    simp
  have hAv : G (v : ℝ) = integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω := by
    rw [← hAeq (v : ℝ) (by positivity)]
    simp
  have hGu : (∫ x in (0 : ℝ)..(u : ℝ), g x) =
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω := by
    simpa [G] using hAu
  have hGv : (∫ x in (0 : ℝ)..(v : ℝ), g x) =
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω := by
    simpa [G] using hAv
  rw [hAu]
  rw [hGu, hGv]
  rw [mul_sub]
  have hexp : Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω) *
      Real.exp (c * (integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)) =
      Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp' : (-η ^ m * Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)) *
      Real.exp (c * (integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)) =
      -η ^ m * Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω) := by
    rw [mul_assoc, hexp]
  rw [hexp']
  simp [η, c]
  ring

omit [MeasurableSpace Ω] in
/-- The left jump count at the `(k+1)`-th attained jump time is exactly `k`. -/
theorem countBefore_jumpTime {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {t : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N t ω))) (hk : k < N t ω) :
    countBefore N (jumpTime N k ω) ω = k := by
  cases k with
  | zero =>
    apply le_antisymm
    · by_contra h
      have hge : 0 + 1 ≤ countBefore N (jumpTime N 0 ω) ω :=
        Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
      rw [countBefore_succ_le_iff hmono] at hge
      rcases hge with ⟨u, hu, h0u⟩
      exact (not_lt.mpr (jumpTime_le_of_lt h0u)) hu
    · exact Nat.zero_le _
  | succ k' =>
    refine countBefore_eq_of_Ioc hmono hrc ⟨t, Nat.lt_of_succ_lt hk⟩ ?_ le_rfl
    exact jumpTime_lt_jumpTime_succ hinj (by omega)

theorem countingExponential_path_identity {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ} {θ₀ C₀ : ℝ} {T t : ℝ≥0}
    (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀) (hΛupper : ∀ s ω, Λ s ω ≤ C₀)
    (hN : IsSimpleCountingProcess ℱ N) (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (htT : t ≤ T) (ω : Ω) :
    countingExponential N Λ (fun _ _ ↦ -θ₀) t ω =
      1 + compensatedIntegral N Λ
        (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0) t ω := by
  let η : ℝ := Real.exp (-θ₀)
  let c : ℝ := 1 - η
  let H : ℝ≥0 → Ω → ℝ :=
    fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0
  have hmono : Monotone (fun r ↦ N r ω) := hN.monotone ω
  have hrc : ∀ r, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici r) r :=
    hN.rightContinuous ω
  have hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N t ω)) := hN.jumpTime_injOn ω t
  have hcell_cut : ∀ {u v : ℝ≥0} {m : ℕ}, u ≤ v → v ≤ T →
      (∀ s ∈ Ioc u v, countBefore N s ω = m) →
      ∫ s in Ioc u v, H s ω * Λ s ω ∂timeMeasure =
        -(η ^ m) *
          (Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) v ω) -
            Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)) := by
    intro u v m huv hvT hcount
    have heq : (∫ s in Ioc u v, H s ω * Λ s ω ∂timeMeasure) =
        ∫ s in Ioc u v, expWeight N Λ θ₀ s ω * Λ s ω ∂timeMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp [H, le_trans hs.2 hvT]
    rw [heq]
    simpa [H, η, c] using
      (expWeight_integral_Ioc (Λ := Λ) (N := N) (ω := ω) (θ₀ := θ₀)
        (u := u) (v := v) (m := m) hθ0 huv hcount (hΛ.integrableOn v ω))
  have hprefix : ∀ j : ℕ, j < N t ω →
      countingExponential N Λ (fun _ _ ↦ -θ₀) (jumpTime N j ω) ω =
        1 + compensatedIntegral N Λ H (jumpTime N j ω) ω := by
    intro j
    induction j with
    | zero =>
        intro hj
        have hτle : jumpTime N 0 ω ≤ t := jumpTime_le_of_lt hj
        have hτT : jumpTime N 0 ω ≤ T := hτle.trans htT
        have hNτ : N (jumpTime N 0 ω) ω = 1 :=
          N_jumpTime_of_lt hmono hrc hinj hj
        have hcount0 : ∀ s ∈ Ioc (0 : ℝ≥0) (jumpTime N 0 ω),
            countBefore N s ω = 0 := by
          intro s hs
          by_cases hseq : s = jumpTime N 0 ω
          · subst s
            exact countBefore_jumpTime hmono hrc hinj hj
          · have hslt : s < jumpTime N 0 ω := lt_of_le_of_ne hs.2 hseq
            have hNsle : N s ω ≤ 0 :=
              (jumpTime_lt_iff hmono hrc ⟨t, hj⟩).mp hslt
            have hNs : N s ω = 0 := Nat.eq_zero_of_le_zero hNsle
            exact countBefore_eq_zero_of_le hmono hrc hNs
        have hcell := hcell_cut (u := 0) (v := jumpTime N 0 ω) (m := 0)
          (by simp) hτT hcount0
        have hN0 : N 0 ω = 0 := congrFun hN.zero ω
        have hcountInt : countingIntegral N H (jumpTime N 0 ω) ω = H (jumpTime N 0 ω) ω := by
          rw [countingIntegral_add_jump (N := N) (H := H)
            hN0 hNτ]
          simp [countingIntegral, hN0]
        have hZ := countingExponential_pow_exp N Λ θ₀ (jumpTime N 0 ω)
          ω (hΛ.integrableOn (jumpTime N 0 ω) ω)
        rw [hNτ] at hZ
        rw [compensatedIntegral, hcountInt]
        have hAcut : integratedIntensity Λ H (jumpTime N 0 ω) ω =
            ∫ s in Ioc (0 : ℝ≥0) (jumpTime N 0 ω), H s ω * Λ s ω ∂timeMeasure := rfl
        have hA0 : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) 0 ω = 0 := by
          simp [integratedIntensity]
        have hcell' :
            (∫ s in Ioc (0 : ℝ≥0) (jumpTime N 0 ω), H s ω * Λ s ω ∂timeMeasure) =
              1 - Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ))
                (jumpTime N 0 ω) ω) := by
          rw [hcell, hA0]
          simp
        have hcb0 : countBefore N (jumpTime N 0 ω) ω = 0 :=
          countBefore_jumpTime hmono hrc hinj hj
        have hHjump : H (jumpTime N 0 ω) ω =
            (η - 1) * Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ))
              (jumpTime N 0 ω) ω) := by
          simp [H, expWeight, hcb0, η, c, hτT]
        rw [hAcut, hcell', hHjump]
        calc
          countingExponential N Λ (fun _ _ ↦ -θ₀) (jumpTime N 0 ω) ω =
              η * Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ))
                (jumpTime N 0 ω) ω) := by simpa [η, c] using hZ
          _ = 1 + ((η - 1) * Real.exp (c * integratedIntensity Λ
                (fun _ _ ↦ (1 : ℝ)) (jumpTime N 0 ω) ω) -
              (1 - Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ))
                (jumpTime N 0 ω) ω))) := by ring
    | succ j ih =>
        intro hj
        have hjprev : j < N t ω := by omega
        have hτprev : jumpTime N j ω ≤ t := jumpTime_le_of_lt hjprev
        have hτnext : jumpTime N (j + 1) ω ≤ t := jumpTime_le_of_lt hj
        have hτprevT : jumpTime N j ω ≤ T := hτprev.trans htT
        have hτnextT : jumpTime N (j + 1) ω ≤ T := hτnext.trans htT
        have hτle : jumpTime N j ω ≤ jumpTime N (j + 1) ω :=
          jumpTime_mono (Nat.le_succ j) hj
        have hτlt : jumpTime N j ω < jumpTime N (j + 1) ω :=
          jumpTime_lt_jumpTime_succ hinj hj
        have hNprev : N (jumpTime N j ω) ω = j + 1 :=
          N_jumpTime_of_lt hmono hrc hinj hjprev
        have hNnext : N (jumpTime N (j + 1) ω) ω = j + 2 := by
          have h := N_jumpTime_of_lt hmono hrc hinj hj
          simpa [Nat.add_assoc] using h
        have hcountCell : ∀ s ∈ Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
            countBefore N s ω = j + 1 := by
          intro s hs
          exact countBefore_eq_of_Ioc hmono hrc ⟨t, hjprev⟩ hs.1 hs.2
        have hcell := hcell_cut (u := jumpTime N j ω)
          (v := jumpTime N (j + 1) ω) (m := j + 1) hτle hτnextT hcountCell
        have hHI : IntervalIntegrable
            (fun x : ℝ ↦ H (Real.toNNReal x) ω * Λ (Real.toNNReal x) ω)
            volume 0 (jumpTime N (j + 1) ω : ℝ) := by
          simpa [H] using
            (expWeight_cut_intervalIntegrable (μ := μ) (ℱ := ℱ) (N := N) (Λ := Λ)
              hθ0 hC₀ hΛupper (T := T) (v := jumpTime N (j + 1) ω) hN hΛ ω)
        have hAadd := integratedIntensity_add_Ioc (Λ := Λ) (H := H) (ω := ω)
          (w := 0) (v := jumpTime N j ω) (u := jumpTime N (j + 1) ω)
          (by simp) hτle hHI
        have hA0H : integratedIntensity Λ H 0 ω = 0 := by
          simp [integratedIntensity]
        have hAadd' : integratedIntensity Λ H (jumpTime N (j + 1) ω) ω =
            integratedIntensity Λ H (jumpTime N j ω) ω +
              ∫ s in Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
                H s ω * Λ s ω ∂timeMeasure := by
          rw [hA0H] at hAadd
          simp only [zero_add] at hAadd
          change integratedIntensity Λ H (jumpTime N (j + 1) ω) ω =
            integratedIntensity Λ H (jumpTime N j ω) ω +
              ∫ s in Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
                H s ω * Λ s ω ∂timeMeasure at hAadd
          exact hAadd
        have hcountadd := countingIntegral_add_jump (N := N) (H := H)
          hNprev hNnext
        have hDadd : compensatedIntegral N Λ H (jumpTime N (j + 1) ω) ω =
            compensatedIntegral N Λ H (jumpTime N j ω) ω +
              H (jumpTime N (j + 1) ω) ω -
                ∫ s in Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
                  H s ω * Λ s ω ∂timeMeasure := by
          unfold compensatedIntegral
          rw [hcountadd, hAadd']
          ring
        have hcbnext : countBefore N (jumpTime N (j + 1) ω) ω = j + 1 :=
          countBefore_jumpTime hmono hrc hinj hj
        have hHjump : H (jumpTime N (j + 1) ω) ω =
            (η - 1) * (η ^ (j + 1)) *
              Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ))
                (jumpTime N (j + 1) ω) ω) := by
          simp [H, expWeight, hcbnext, η, c, hτnextT]
        have hZprev := countingExponential_pow_exp N Λ θ₀ (jumpTime N j ω)
          ω (hΛ.integrableOn (jumpTime N j ω) ω)
        rw [hNprev] at hZprev
        have hZnext := countingExponential_pow_exp N Λ θ₀
          (jumpTime N (j + 1) ω) ω
          (hΛ.integrableOn (jumpTime N (j + 1) ω) ω)
        rw [hNnext] at hZnext
        have hprev := ih hjprev
        calc
          countingExponential N Λ (fun _ _ ↦ -θ₀)
              (jumpTime N (j + 1) ω) ω =
              η ^ (j + 2) * Real.exp (c * integratedIntensity Λ
                (fun _ _ ↦ (1 : ℝ)) (jumpTime N (j + 1) ω) ω) := by
                simpa [η, c] using hZnext
          _ = η ^ (j + 1) * Real.exp (c * integratedIntensity Λ
                (fun _ _ ↦ (1 : ℝ)) (jumpTime N j ω) ω) +
              ((η - 1) * (η ^ (j + 1)) * Real.exp (c * integratedIntensity Λ
                (fun _ _ ↦ (1 : ℝ)) (jumpTime N (j + 1) ω) ω) -
                (-(η ^ (j + 1)) *
                  (Real.exp (c * integratedIntensity Λ
                    (fun _ _ ↦ (1 : ℝ)) (jumpTime N (j + 1) ω) ω) -
                    Real.exp (c * integratedIntensity Λ
                      (fun _ _ ↦ (1 : ℝ)) (jumpTime N j ω) ω)))) := by
                rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
                ring
          _ = countingExponential N Λ (fun _ _ ↦ -θ₀)
                (jumpTime N j ω) ω + H (jumpTime N (j + 1) ω) ω -
                ∫ s in Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
                  H s ω * Λ s ω ∂timeMeasure := by
                rw [hZprev, hHjump, hcell]
                ring
          _ = (1 + compensatedIntegral N Λ H (jumpTime N j ω) ω) +
                H (jumpTime N (j + 1) ω) ω -
                ∫ s in Ioc (jumpTime N j ω) (jumpTime N (j + 1) ω),
                  H s ω * Λ s ω ∂timeMeasure := by
                rw [hprev]
          _ = 1 + compensatedIntegral N Λ H (jumpTime N (j + 1) ω) ω := by
                rw [hDadd]
                ring

  by_cases hN0 : N t ω = 0
  · have hcount0final : ∀ s ∈ Ioc (0 : ℝ≥0) t, countBefore N s ω = 0 := by
      intro s hs
      have hNs : N s ω = 0 := by
        apply Nat.eq_zero_of_le_zero
        rw [← hN0]
        exact hmono hs.2
      exact countBefore_eq_zero_of_le hmono hrc hNs
    have hcell := hcell_cut (u := 0) (v := t) (m := 0) (by simp) htT hcount0final
    have hcountInt : countingIntegral N H t ω = 0 := by
      simp [countingIntegral, hN0]
    have hA0H : integratedIntensity Λ H 0 ω = 0 := by
      simp [integratedIntensity]
    have hA0 : integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) 0 ω = 0 := by
      simp [integratedIntensity]
    have hAcut : integratedIntensity Λ H t ω =
        ∫ s in Ioc (0 : ℝ≥0) t, H s ω * Λ s ω ∂timeMeasure := rfl
    have hcell' :
      (∫ s in Ioc (0 : ℝ≥0) t, H s ω * Λ s ω ∂timeMeasure) =
          1 - Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
      rw [hcell]
      rw [hA0]
      simp only [pow_zero, mul_zero, Real.exp_zero]
      ring
    have hZ := countingExponential_pow_exp N Λ θ₀ t ω (hΛ.integrableOn t ω)
    rw [hN0] at hZ
    rw [compensatedIntegral, hcountInt, hAcut, hcell']
    calc
      countingExponential N Λ (fun _ _ ↦ -θ₀) t ω =
          Real.exp (c * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) := by
            simpa [η, c] using hZ
      _ = 1 + (0 - (1 - Real.exp (c * integratedIntensity Λ
            (fun _ _ ↦ (1 : ℝ)) t ω))) := by ring
  · have hn : 0 < N t ω := Nat.pos_of_ne_zero hN0
    let n : ℕ := N t ω - 1
    have hnval : N t ω = n + 1 := by
      dsimp [n]
      omega
    have hlast : n < N t ω := by
      rw [hnval]
      exact Nat.lt_succ_self n
    have hprefixlast := hprefix n hlast
    have hτle : jumpTime N n ω ≤ t := jumpTime_le_of_lt hlast
    by_cases hτeq : jumpTime N n ω = t
    · simpa [hτeq] using hprefixlast
    · have hτlt : jumpTime N n ω < t := lt_of_le_of_ne hτle hτeq
      have hNlast : N (jumpTime N n ω) ω = n + 1 :=
        N_jumpTime_of_lt hmono hrc hinj hlast
      have hcountCell : ∀ s ∈ Ioc (jumpTime N n ω) t,
          countBefore N s ω = n + 1 := by
        intro s hs
        exact countBefore_eq_of_lt hmono hrc hnval
          hs.1 hs.2
      have hcell := hcell_cut (u := jumpTime N n ω) (v := t) (m := n + 1)
        hτle htT hcountCell
      have hHI : IntervalIntegrable
          (fun x : ℝ ↦ H (Real.toNNReal x) ω * Λ (Real.toNNReal x) ω)
          volume 0 (t : ℝ) := by
        simpa [H] using
          (expWeight_cut_intervalIntegrable (μ := μ) (ℱ := ℱ) (N := N) (Λ := Λ)
            hθ0 hC₀ hΛupper (T := T) (v := t) hN hΛ ω)
      have hAadd := integratedIntensity_add_Ioc (Λ := Λ) (H := H) (ω := ω)
        (w := 0) (v := jumpTime N n ω) (u := t) (by simp) hτle hHI
      have hA0H : integratedIntensity Λ H 0 ω = 0 := by
        simp [integratedIntensity]
      have hAadd' : integratedIntensity Λ H t ω =
          integratedIntensity Λ H (jumpTime N n ω) ω +
            ∫ s in Ioc (jumpTime N n ω) t, H s ω * Λ s ω ∂timeMeasure := by
        rw [hA0H] at hAadd
        simp only [zero_add] at hAadd
        change integratedIntensity Λ H t ω =
          integratedIntensity Λ H (jumpTime N n ω) ω +
            ∫ s in Ioc (jumpTime N n ω) t, H s ω * Λ s ω ∂timeMeasure at hAadd
        exact hAadd
      have hcountsame : countingIntegral N H t ω =
          countingIntegral N H (jumpTime N n ω) ω := by
        rw [countingIntegral, countingIntegral, hnval, hNlast]
      have hDadd : compensatedIntegral N Λ H t ω =
          compensatedIntegral N Λ H (jumpTime N n ω) ω -
            ∫ s in Ioc (jumpTime N n ω) t, H s ω * Λ s ω ∂timeMeasure := by
        unfold compensatedIntegral
        rw [hcountsame, hAadd']
        ring
      have hZlast := countingExponential_pow_exp N Λ θ₀ (jumpTime N n ω) ω
        (hΛ.integrableOn (jumpTime N n ω) ω)
      rw [hNlast] at hZlast
      have hZt := countingExponential_pow_exp N Λ θ₀ t ω (hΛ.integrableOn t ω)
      rw [hnval] at hZt
      have hprev := hprefixlast
      calc
        countingExponential N Λ (fun _ _ ↦ -θ₀) t ω =
            η ^ (n + 1) * Real.exp (c * integratedIntensity Λ
              (fun _ _ ↦ (1 : ℝ)) t ω) := by
              simpa [η, c] using hZt
        _ = η ^ (n + 1) * Real.exp (c * integratedIntensity Λ
              (fun _ _ ↦ (1 : ℝ)) (jumpTime N n ω) ω) -
            (-(η ^ (n + 1)) *
              (Real.exp (c * integratedIntensity Λ
                (fun _ _ ↦ (1 : ℝ)) t ω) -
                Real.exp (c * integratedIntensity Λ
                  (fun _ _ ↦ (1 : ℝ)) (jumpTime N n ω) ω))) := by
              ring
        _ = countingExponential N Λ (fun _ _ ↦ -θ₀)
              (jumpTime N n ω) ω -
            ∫ s in Ioc (jumpTime N n ω) t, H s ω * Λ s ω ∂timeMeasure := by
              rw [hZlast, hcell]
        _ = (1 + compensatedIntegral N Λ H (jumpTime N n ω) ω) -
            ∫ s in Ioc (jumpTime N n ω) t, H s ω * Λ s ω ∂timeMeasure := by
              rw [hprev]
        _ = 1 + compensatedIntegral N Λ H t ω := by
              rw [hDadd]
              ring

theorem compensatedIntegral_cutoff_eq_min {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {θ₀ C₀ : ℝ} {T t : ℝ≥0} (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ s ω, Λ s ω ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (ω : Ω) :
    compensatedIntegral N Λ
      (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0) t ω =
      compensatedIntegral N Λ
        (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0) (min t T) ω := by
  by_cases hlt : t ≤ T
  · simp [min_eq_left hlt]
  · have hTt : T ≤ t := le_of_not_ge hlt
    let H : ℝ≥0 → Ω → ℝ :=
      fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0
    have hmono : Monotone (fun r ↦ N r ω) := hN.monotone ω
    have hrc : ∀ r, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici r) r :=
      hN.rightContinuous ω
    have hNT : N T ω ≤ N t ω := hmono hTt
    have hcount : countingIntegral N H t ω = countingIntegral N H T ω := by
      unfold countingIntegral
      symm
      apply Finset.sum_subset
      · exact Finset.range_subset_range.mpr hNT
      · intro k hk hnot
        have hkt : k < N t ω := Finset.mem_range.mp hk
        have hkT : N T ω ≤ k := Nat.le_of_not_gt (by
          intro hklt
          exact hnot (Finset.mem_range.mpr hklt))
        have hτnot : ¬ jumpTime N k ω ≤ T := by
          intro hτ
          have hkltT : k < N T ω :=
            (jumpTime_le_iff hmono hrc ⟨t, hkt⟩).mp hτ
          exact (Nat.not_lt_of_ge hkT) hkltT
        have hτgt : T < jumpTime N k ω := lt_of_not_ge hτnot
        simp [H, not_le_of_gt hτgt]
    have hHI : IntervalIntegrable
        (fun x : ℝ ↦ H (Real.toNNReal x) ω * Λ (Real.toNNReal x) ω)
        volume 0 (t : ℝ) := by
      simpa [H] using
        (expWeight_cut_intervalIntegrable (μ := μ) (ℱ := ℱ) (N := N) (Λ := Λ)
          hθ0 hC₀ hΛupper (T := T) (v := t) hN hΛ ω)
    have hAadd := integratedIntensity_add_Ioc (Λ := Λ) (H := H) (ω := ω)
      (w := 0) (v := T) (u := t) (by simp) hTt hHI
    have hA0 : integratedIntensity Λ H 0 ω = 0 := by
      simp [integratedIntensity]
    have hcellzero :
        (∫ s in Ioc T t, H s ω * Λ s ω ∂timeMeasure) = 0 := by
      calc
        (∫ s in Ioc T t, H s ω * Λ s ω ∂timeMeasure) =
            ∫ s in Ioc T t, (0 : ℝ) ∂timeMeasure := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          simp [H, not_le_of_gt hs.1]
        _ = 0 := by simp
    rw [hA0] at hAadd
    simp only [zero_add] at hAadd
    change integratedIntensity Λ H t ω =
      integratedIntensity Λ H T ω + ∫ s in Ioc T t, H s ω * Λ s ω ∂timeMeasure at hAadd
    rw [hcellzero, add_zero] at hAadd
    have hD : compensatedIntegral N Λ H t ω = compensatedIntegral N Λ H T ω := by
      unfold compensatedIntegral
      rw [hcount, hAadd]
    simpa [H, min_eq_right hTt] using hD


noncomputable def finiteHorizonCountingExponential
    (N : ℝ≥0 → Ω → ℕ) (Λ : ℝ≥0 → Ω → ℝ) (θ₀ : ℝ) (T : ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  countingExponential N Λ (fun _ _ ↦ -θ₀) (min t T) ω

theorem finiteHorizonCountingExponential_eq_driver {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {θ₀ C₀ : ℝ} {T t : ℝ≥0} (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ s ω, Λ s ω ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (ω : Ω) :
    finiteHorizonCountingExponential N Λ θ₀ T t ω =
      1 + compensatedIntegral N Λ
        (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0) t ω := by
  let H : ℝ≥0 → Ω → ℝ :=
    fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0
  have hpath := countingExponential_path_identity (μ := μ) (ℱ := ℱ)
    (N := N) (Λ := Λ) (θ₀ := θ₀) (C₀ := C₀) (T := T) (t := min t T)
    hθ0 hC₀ hΛupper hN hΛ (min_le_right t T) ω
  have hcut := compensatedIntegral_cutoff_eq_min (μ := μ) (ℱ := ℱ)
    (N := N) (Λ := Λ) (θ₀ := θ₀) (C₀ := C₀) (T := T) (t := t)
    hθ0 hC₀ hΛupper hN hΛ ω
  calc
    finiteHorizonCountingExponential N Λ θ₀ T t ω =
        countingExponential N Λ (fun _ _ ↦ -θ₀) (min t T) ω := rfl
    _ = 1 + compensatedIntegral N Λ H (min t T) ω := by simpa [H] using hpath
    _ = 1 + compensatedIntegral N Λ H t ω := by rw [hcut]
    _ = 1 + compensatedIntegral N Λ
        (fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0) t ω := by rfl

theorem finiteHorizonCountingExponential_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    {θ₀ C₀ : ℝ} {T : ℝ≥0} (hθ0 : 0 < θ₀) (hC₀ : 0 ≤ C₀)
    (hΛupper : ∀ s ω, Λ s ω ≤ C₀) (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    Martingale (finiteHorizonCountingExponential N Λ θ₀ T) ℱ μ := by
  let H : ℝ≥0 → Ω → ℝ :=
    fun s ω' ↦ if s ≤ T then expWeight N Λ θ₀ s ω' else 0
  have hH : IsBoundedPredictable ℱ H := by
    simpa [H] using
      (expWeight_boundedPredictable (μ := μ) (ℱ := ℱ) (N := N) (Λ := Λ)
        hθ0 hC₀ hΛupper (T := T) hN hΛ)
  have hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ := by
    intro t
    exact integratedIntensity_one_integrable_of_bounded (μ := μ) (ℱ := ℱ)
      (N := N) (Λ := Λ) hC₀ hΛupper hN hΛ t
  have hD : Martingale (compensatedIntegral N Λ H) ℱ μ :=
    hΛ.martingale_of_boundedPredictable_of_isFiniteMeasure hH hAint
  have hOne : Martingale (fun _ (_ : Ω) ↦ (1 : ℝ)) ℱ μ :=
    martingale_const ℱ μ 1
  have hDriver : Martingale (fun t ω ↦ 1 + compensatedIntegral N Λ H t ω) ℱ μ := by
    convert hOne.add hD using 1
    funext t ω
    rfl
  have hfun : finiteHorizonCountingExponential N Λ θ₀ T =
      (fun t ω ↦ 1 + compensatedIntegral N Λ H t ω) := by
    funext t ω
    exact finiteHorizonCountingExponential_eq_driver (μ := μ) (ℱ := ℱ) (N := N) (Λ := Λ)
      (θ₀ := θ₀) (C₀ := C₀) (T := T) hθ0 hC₀ hΛupper hN hΛ ω
  rw [hfun]
  exact hDriver


end OTSelector.CountingProcess
