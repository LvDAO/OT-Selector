import OTSelector.Gauge.EuclideanCoercivity
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The actual Euclidean gauge on a bounded microscopic window

The macroscopic graph `h + g (n * z) / n` has common height `h` and microscopic
increments `g`.  Its Euclidean gauge, multiplied by `n²`, approaches the quadratic
gauge as `h → 0` and `n → ∞`.  The estimates below use the exact hinge identity;
convergence of the costs is a conclusion, not an input.
-/

open Set MeasureTheory Filter
open scoped Interval Topology

namespace OTSelector

/-- The actual graph after zooming out a microscopic graph by `n` and adding its
macroscopic common height.  A horizontal root translation can be absorbed into `g`. -/
noncomputable def localNormalizedGraph (n h : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  h + g (n * z) / n

/-- Actual Euclidean gauged cost in microscopic units. -/
noncomputable def localEuclideanCost (n h : ℝ) (g : ℝ → ℝ)
    (xi eta a b : ℝ) : ℝ :=
  n ^ 2 * euclideanGaugedCost (localNormalizedGraph n h g) (xi / n) (eta / n) a b

theorem euclideanGaugedCost_eq_hinge_integral_on
    {A B xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi ≤ eta) {g : ℝ → ℝ}
    (hg : Continuous g) (hrange : ∀ x ∈ Icc xi eta, g x ∈ Icc A B)
    (hq : fourPointQuotient g xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    euclideanGaugedCost g xi eta a b =
      ∫ t in A..B, euclideanResidualSecond t * hingeKernel g xi eta a b t := by
  apply gaugedFourPointCost_eq_hinge_integral hAB hxi hg hrange
  · exact fun y _ ↦ euclideanResidual_hasDerivAt y
  · exact fun y _ ↦ euclideanResidualDeriv_hasDerivAt y
  · exact euclideanResidualDeriv_continuous.continuousOn
  · exact euclideanResidualSecond_continuous.continuousOn
  · exact hq
  · exact ha
  · exact hb

/-- A curvature error gives a relative gauge error on the actual graph. -/
theorem euclideanGaugedCost_sub_quadratic_abs_le
    {A B eps lam xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi < eta)
    {g : ℝ → ℝ} (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ Icc xi eta, g x ∈ Icc A B)
    (hq : fourPointQuotient g xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2)
    (hcurv : ∀ t ∈ Icc A B, 1 - eps ≤ euclideanResidualSecond t) :
    |euclideanGaugedCost g xi eta a b - quadraticCost g xi eta a b| ≤
      eps * quadraticCost g xi eta a b := by
  let H := hingeKernel g xi eta a b
  have hH : IntervalIntegrable H volume A B :=
    hingeKernel_intervalIntegrable hAB hxi.le hg hrange
  have hEH := hH.continuousOn_mul euclideanResidualSecond_continuous.continuousOn
  have hH0 : ∀ t, 0 ≤ H t := hingeKernel_nonneg hxi hg hLip hlam0 hlam ha hb
  have hlo : (∫ t in A..B, (1 - eps) * H t) ≤
      ∫ t in A..B, euclideanResidualSecond t * H t := by
    apply intervalIntegral.integral_mono_on hAB (hH.const_mul _) hEH
    exact fun t ht ↦ mul_le_mul_of_nonneg_right (hcurv t ht) (hH0 t)
  have hhi : (∫ t in A..B, euclideanResidualSecond t * H t) ≤
      ∫ t in A..B, H t := by
    apply intervalIntegral.integral_mono_on hAB hEH hH
    intro t _
    simpa using mul_le_mul_of_nonneg_right (euclideanResidualSecond_le_one t) (hH0 t)
  have hE := euclideanGaugedCost_eq_hinge_integral_on hAB hxi.le hg hrange hq ha hb
  have hQ := quadraticCost_eq_hinge_integral hAB hxi.le hg hrange hq ha hb
  dsimp [H] at hlo hhi
  rw [← hE, intervalIntegral.integral_const_mul, ← hQ] at hlo
  rw [← hE, ← hQ] at hhi
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith

theorem localNormalizedGraph_continuous {n h : ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) : Continuous (localNormalizedGraph n h g) := by
  unfold localNormalizedGraph
  fun_prop

theorem fourPointQuotient_localNormalizedGraph
    {n h xi eta a b : ℝ} (hn : n ≠ 0) (hD : a + b ≠ 0) (g : ℝ → ℝ) :
    fourPointQuotient (localNormalizedGraph n h g) (xi / n) (eta / n) a b =
      h + fourPointQuotient g xi eta a b / n := by
  simp only [fourPointQuotient, fourPointGap, fourPointDenominator,
    fourPointSourceValue, fourPointTargetValue, localNormalizedGraph,
    mul_div_cancel₀ _ hn]
  field_simp
  ring

/-- Exact quadratic scaling, including cancellation of the common graph height. -/
theorem quadraticCost_localNormalizedGraph
    {n h xi eta a b : ℝ} (hn : n ≠ 0) (hD : a + b ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g) :
    n ^ 2 * quadraticCost (localNormalizedGraph n h g) (xi / n) (eta / n) a b =
      quadraticCost g xi eta a b := by
  have hgi : IntervalIntegrable (fun x ↦ g (n * x) / n) volume (xi / n) (eta / n) :=
    (hg.comp (continuous_const.mul continuous_id) |>.div_const n).intervalIntegrable _ _
  have hi : (∫ x in xi / n..eta / n, localNormalizedGraph n h g x) =
      (eta / n - xi / n) * h + (∫ x in xi..eta, g x) / n ^ 2 := by
    unfold localNormalizedGraph
    rw [intervalIntegral.integral_add intervalIntegrable_const hgi,
      intervalIntegral.integral_const, intervalIntegral.integral_div,
      intervalIntegral.integral_comp_mul_left _ hn]
    simp only [mul_div_cancel₀ _ hn, smul_eq_mul]
    field_simp
  unfold quadraticCost gaugedFourPointCost
  simp only [id_eq]
  rw [fourPointQuotient_localNormalizedGraph hn hD g, hi]
  simp only [fourPointDenominator, fourPointSourceValue, fourPointTargetValue,
    localNormalizedGraph, mul_div_cancel₀ _ hn]
  unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
    fourPointDenominator
  field_simp
  ring

theorem localNormalizedGraph_lipschitz {n h lam : ℝ} (hn : 0 < n)
    {g : ℝ → ℝ} (hg : ScalarLipschitz lam g) :
    ScalarLipschitz lam (localNormalizedGraph n h g) := by
  intro x y
  simp only [localNormalizedGraph, add_sub_add_left_eq_sub, ← sub_div, abs_div,
    abs_of_pos hn]
  apply (div_le_iff₀ hn).2
  have h := hg (n * x) (n * y)
  rw [← mul_sub, abs_mul, abs_of_pos hn] at h
  nlinarith

private theorem local_quotient_bound
    {W M xi eta a b : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hxi : xi ∈ Icc (-W) W) (heta : eta ∈ Icc (-W) W)
    {g : ℝ → ℝ} (hg : ∀ x ∈ Icc (-W) W, |g x| ≤ M)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    |fourPointQuotient g xi eta a b| ≤ 2 * W + 3 * M := by
  have hD : 0 < a + b := by linarith [ha.1, hb.1]
  have hgap : |eta - xi| ≤ 2 * W := by
    apply abs_le.2
    constructor <;> linarith [hxi.1, hxi.2, heta.1, heta.2]
  have hs : |a * g xi| ≤ a * M := by
    simpa [abs_mul, abs_of_nonneg ha.1] using mul_le_mul_of_nonneg_left (hg xi hxi) ha.1
  have ht : |b * g eta| ≤ b * M := by
    simpa [abs_mul, abs_of_nonneg (show 0 ≤ b by linarith [hb.1])] using
      mul_le_mul_of_nonneg_left (hg eta heta) (show 0 ≤ b by linarith [hb.1])
  unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
    fourPointDenominator
  rw [abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).2
  have htri := abs_add_three (eta - xi) (a * g xi) (b * g eta)
  nlinarith [mul_nonneg hM (show 0 ≤ 3 - (a + b) by linarith [ha.2, hb.2]),
    mul_nonneg (show 0 ≤ 2 * W + 3 * M by positivity)
      (show 0 ≤ a + b - 1 by linarith [ha.1, hb.1])]

/-- Curvature continuity supplies the small-window error required by the hinge estimate. -/
theorem exists_euclidean_curvature_radius {eps : ℝ} (heps : 0 < eps) :
    ∃ r > 0, ∀ t : ℝ, |t| ≤ r → 1 - eps ≤ euclideanResidualSecond t := by
  obtain ⟨d, hd, h⟩ := Metric.continuousAt_iff.1
    euclideanResidualSecond_continuous.continuousAt eps heps
  refine ⟨d / 2, by positivity, fun t ht ↦ ?_⟩
  have ht' : dist t 0 < d := by simpa [Real.dist_eq] using ht.trans_lt (by linarith)
  have h' := h ht'
  have hz : euclideanResidualSecond 0 = 1 := by norm_num [euclideanResidualSecond]
  rw [hz, Real.dist_eq] at h'
  linarith [(abs_lt.1 h').1]

/-- Quantitative forward-edge estimate for the actual rescaled Euclidean gauge. -/
theorem localEuclideanCost_sub_quadratic_abs_le_forward
    {n h W M r eps lam xi eta a b : ℝ}
    (hn : 0 < n) (hW : 0 ≤ W) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hxi : xi ∈ Icc (-W) W) (heta : eta ∈ Icc (-W) W) (horder : xi < eta)
    {g : ℝ → ℝ} (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hgM : ∀ x ∈ Icc (-W) W, |g x| ≤ M)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2)
    (hsmall : |h| + (2 * W + 3 * M) / n ≤ r)
    (hcurv : ∀ t : ℝ, |t| ≤ r → 1 - eps ≤ euclideanResidualSecond t) :
    |localEuclideanCost n h g xi eta a b - quadraticCost g xi eta a b| ≤
      eps * quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
  have hr : 0 ≤ r := (by positivity : 0 ≤ |h| + (2 * W + 3 * M) / n).trans hsmall
  have hbound (v : ℝ) (hv : |v| ≤ 2 * W + 3 * M) : |h + v / n| ≤ r := by
    calc
      _ ≤ |h| + |v / n| := abs_add_le _ _
      _ ≤ |h| + (2 * W + 3 * M) / n := by
        rw [abs_div, abs_of_pos hn]
        linarith [div_le_div_of_nonneg_right hv hn.le]
      _ ≤ r := hsmall
  have hrange : ∀ x ∈ Icc (xi / n) (eta / n),
      localNormalizedGraph n h g x ∈ Icc (-r) r := by
    intro x hx
    have hxW : n * x ∈ Icc (-W) W := by
      constructor
      · have hh := (div_le_iff₀ hn).1 hx.1
        nlinarith [hxi.1]
      · have hh := (le_div_iff₀ hn).1 hx.2
        nlinarith [heta.2]
    exact abs_le.1 (hbound _ ((hgM _ hxW).trans (by linarith)))
  have hq : fourPointQuotient (localNormalizedGraph n h g)
      (xi / n) (eta / n) a b ∈ Icc (-r) r := by
    rw [fourPointQuotient_localNormalizedGraph hn.ne' hD g]
    exact abs_le.1 (hbound _ (local_quotient_bound hW hM hxi heta hgM ha hb))
  have herr := euclideanGaugedCost_sub_quadratic_abs_le (show -r ≤ r by linarith)
    ((div_lt_div_iff_of_pos_right hn).2 horder) (localNormalizedGraph_continuous hg)
    (localNormalizedGraph_lipschitz hn hLip) hlam0 (hlam.trans (by norm_num))
    hrange hq ha hb (fun t ht ↦ hcurv t (abs_le.2 ht))
  have hscaled := mul_le_mul_of_nonneg_left herr (sq_nonneg n)
  have hQ := quadraticCost_localNormalizedGraph (h := h) hn.ne' hD hg
    (xi := xi) (eta := eta)
  have hupper := quadraticGauge_upper_bound horder hg hLip hlam0 hlam ha hb
  calc
    _ = n ^ 2 * |euclideanGaugedCost (localNormalizedGraph n h g)
        (xi / n) (eta / n) a b -
          quadraticCost (localNormalizedGraph n h g) (xi / n) (eta / n) a b| := by
      rw [← hQ, localEuclideanCost, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg n)]
    _ ≤ n ^ 2 * (eps * quadraticCost (localNormalizedGraph n h g)
        (xi / n) (eta / n) a b) := hscaled
    _ = eps * quadraticCost g xi eta a b := by rw [mul_left_comm, hQ]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hupper heps]

theorem quadraticCost_reflected (g : ℝ → ℝ) (xi eta a b : ℝ) :
    quadraticCost (reflectedGraph g) (-xi) (-eta) a b = quadraticCost g xi eta a b := by
  have hi : (∫ x in -xi..-eta, reflectedGraph g x) = ∫ x in xi..eta, g x := by
    simp only [reflectedGraph, intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_neg, neg_neg]
    rw [intervalIntegral.integral_symm]
    ring
  unfold quadraticCost gaugedFourPointCost
  simp only [id_eq, fourPointQuotient_reflectedGraph, even_two, Even.neg_pow,
    fourPointSourceValue, fourPointTargetValue, reflectedGraph, neg_neg]
  rw [show (∫ x in -xi..-eta, -g (-x)) = ∫ x in xi..eta, g x from hi]

theorem localEuclideanCost_reflected (n h : ℝ) (g : ℝ → ℝ) (xi eta a b : ℝ) :
    localEuclideanCost n (-h) (reflectedGraph g) (-xi) (-eta) a b =
      localEuclideanCost n h g xi eta a b := by
  have hg : localNormalizedGraph n (-h) (reflectedGraph g) =
      reflectedGraph (localNormalizedGraph n h g) := by
    funext x
    simp [localNormalizedGraph, reflectedGraph]
    ring
  unfold localEuclideanCost
  rw [hg, neg_div, neg_div, euclideanGaugedCost_reflected]

private theorem gaugedFourPointCost_self
    (f f' g : ℝ → ℝ) (xi a b : ℝ) (hD : a + b ≠ 0) :
    gaugedFourPointCost f f' g xi xi a b = 0 := by
  have hq : fourPointQuotient g xi xi a b = g xi := by
    unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
      fourPointDenominator
    field_simp
    ring
  simp [gaugedFourPointCost, hq, fourPointDenominator,
    fourPointSourceValue, fourPointTargetValue]
  ring

/-- The microscopic error bound includes forward, reverse and coincident endpoints. -/
theorem localEuclideanCost_sub_quadratic_abs_le
    {n h W M r eps lam xi eta a b : ℝ}
    (hn : 0 < n) (hW : 0 ≤ W) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hxi : xi ∈ Icc (-W) W) (heta : eta ∈ Icc (-W) W)
    {g : ℝ → ℝ} (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hgM : ∀ x ∈ Icc (-W) W, |g x| ≤ M)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2)
    (hsmall : |h| + (2 * W + 3 * M) / n ≤ r)
    (hcurv : ∀ t : ℝ, |t| ≤ r → 1 - eps ≤ euclideanResidualSecond t) :
    |localEuclideanCost n h g xi eta a b - quadraticCost g xi eta a b| ≤
      eps * quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  rcases lt_trichotomy xi eta with ho | rfl | ho
  · exact localEuclideanCost_sub_quadratic_abs_le_forward hn hW hM heps hxi heta ho
      hg hLip hlam0 hlam hgM ha hb hsmall hcurv
  · have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
    simp [localEuclideanCost, euclideanGaugedCost, quadraticCost,
      gaugedFourPointCost_self _ _ _ _ _ _ hD]
  · have hm (x : ℝ) (hx : x ∈ Icc (-W) W) : -x ∈ Icc (-W) W := by
      constructor <;> linarith [hx.1, hx.2]
    have h := localEuclideanCost_sub_quadratic_abs_le_forward
      (h := -h) hn hW hM heps (hm _ hxi) (hm _ heta) (by linarith)
      (reflectedGraph_continuous hg) (reflectedGraph_lipschitz hLip) hlam0 hlam
      (fun x hx ↦ by simpa [reflectedGraph] using hgM (-x) (hm x hx)) ha hb
      (by simpa using hsmall) hcurv
    rw [localEuclideanCost_reflected, quadraticCost_reflected] at h
    convert h using 1
    ring

/-- Endpoint/mark tuples used by the bounded-window uniform convergence statement. -/
def localCostWindow (W : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-W) W ∧ p.2.1 ∈ Icc (-W) W ∧
    p.2.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2.2 ∈ Icc (1 : ℝ) 2}

/-- Uniform vanishing of the actual Euclidean-to-quadratic error, allowing a varying
microscopic graph.  Only common height and horizontal scaling converge at this stage. -/
theorem tendstoUniformlyOn_localEuclideanCost_sub_quadratic
    {ι : Type*} {l : Filter ι} {n h : ι → ℝ} {g : ι → ℝ → ℝ} {W M lam : ℝ}
    (hn : Tendsto n l atTop) (hh : Tendsto h l (𝓝 0))
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hg : ∀ k, Continuous (g k)) (hLip : ∀ k, ScalarLipschitz lam (g k))
    (hgM : ∀ k x, x ∈ Icc (-W) W → |g k x| ≤ M) :
    TendstoUniformlyOn
      (fun k p ↦ localEuclideanCost (n k) (h k) (g k) p.1 p.2.1 p.2.2.1 p.2.2.2 -
        quadraticCost (g k) p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun _ ↦ 0) l (localCostWindow W) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro eps heps
  let C := quadraticUpperConstant lam * (2 * W) ^ 2
  have hQ0 : 0 ≤ quadraticUpperConstant lam := by
    unfold quadraticUpperConstant
    positivity
  have hC : 0 ≤ C := mul_nonneg hQ0 (sq_nonneg _)
  have hsmallEps : 0 < eps / (C + 1) := div_pos heps (by positivity)
  obtain ⟨r, hr, hcurv⟩ := exists_euclidean_curvature_radius hsmallEps
  have hsmall : Tendsto (fun k ↦ |h k| + (2 * W + 3 * M) / n k) l (𝓝 0) := by
    simpa using hh.abs.add (tendsto_const_nhds.div_atTop hn)
  filter_upwards [hn.eventually_gt_atTop 0, hsmall.eventually (gt_mem_nhds hr)] with k hnk hsk
  intro p hp
  obtain ⟨hxi, heta, ha, hb⟩ := hp
  have hgap : |p.2.1 - p.1| ≤ 2 * W := by
    apply abs_le.2
    constructor <;> linarith [hxi.1, hxi.2, heta.1, heta.2]
  have hsq : (p.2.1 - p.1) ^ 2 ≤ (2 * W) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hgap 2
  have hbound := localEuclideanCost_sub_quadratic_abs_le hnk hW hM hsmallEps.le
    hxi heta (hg k) (hLip k) hlam0 hlam (hgM k) ha hb hsk.le hcurv
  rw [Real.dist_eq, zero_sub, abs_neg]
  calc
    _ ≤ eps / (C + 1) * quadraticUpperConstant lam * (p.2.1 - p.1) ^ 2 := hbound
    _ ≤ eps / (C + 1) * C := by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_left hsq
        (mul_nonneg hsmallEps.le hQ0)]
    _ < eps := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ (show 0 < C + 1 by positivity)).2 (by nlinarith)

private theorem abs_sq_sub_sq_le {x y M d : ℝ} (_hM : 0 ≤ M) (hd : 0 ≤ d)
    (hx : |x| ≤ M) (hy : |y| ≤ M) (hxy : |x - y| ≤ d) :
    |x ^ 2 - y ^ 2| ≤ 2 * M * d := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  have hs : |x + y| ≤ M + M := (abs_add_le _ _).trans (add_le_add hx hy)
  nlinarith [mul_le_mul hxy hs (abs_nonneg _) hd]

private theorem quotient_sub_abs_le
    {xi eta a b d : ℝ} {f g : ℝ → ℝ} (_hd : 0 ≤ d)
    (hxi : |g xi - f xi| ≤ d) (heta : |g eta - f eta| ≤ d)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    |fourPointQuotient g xi eta a b - fourPointQuotient f xi eta a b| ≤ d := by
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hD : 0 < a + b := by linarith [ha.1, hb.1]
  have heq : fourPointQuotient g xi eta a b - fourPointQuotient f xi eta a b =
      (a * (g xi - f xi) + b * (g eta - f eta)) / (a + b) := by
    unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
      fourPointDenominator
    ring
  rw [heq, abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).2
  have hs := mul_le_mul_of_nonneg_left hxi ha.1
  have ht := mul_le_mul_of_nonneg_left heta hb0
  have h := abs_add_le (a * (g xi - f xi)) (b * (g eta - f eta))
  rw [abs_mul, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hb0] at h
  nlinarith

/-- A direct stability estimate for the quadratic gauge.  It includes all endpoint orders
and varies both marks over their whole admissible ranges. -/
theorem quadraticCost_sub_abs_le_of_graph_close
    {W M d xi eta a b : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hxi : xi ∈ Icc (-W) W) (heta : eta ∈ Icc (-W) W)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfM : ∀ x ∈ Icc (-W) W, |f x| ≤ M)
    (hgM : ∀ x ∈ Icc (-W) W, |g x| ≤ M)
    (hclose : ∀ x ∈ Icc (-W) W, |g x - f x| ≤ d)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    |quadraticCost g xi eta a b - quadraticCost f xi eta a b| ≤
      (8 * W + 12 * M) * d := by
  let K := 2 * W + 3 * M
  let qg := fourPointQuotient g xi eta a b
  let qf := fourPointQuotient f xi eta a b
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hD : 0 ≤ a + b := by linarith [ha.1, hb.1]
  have hq : |qg ^ 2 - qf ^ 2| ≤ 2 * K * d :=
    abs_sq_sub_sq_le hK hd (local_quotient_bound hW hM hxi heta hgM ha hb)
      (local_quotient_bound hW hM hxi heta hfM ha hb)
      (quotient_sub_abs_le hd (hclose xi hxi) (hclose eta heta) ha hb)
  have hs := abs_sq_sub_sq_le hM hd (hgM xi hxi) (hfM xi hxi) (hclose xi hxi)
  have ht := abs_sq_sub_sq_le hM hd (hgM eta heta) (hfM eta heta) (hclose eta heta)
  have hA : |(a + b) * (qg ^ 2 - qf ^ 2) / 2| ≤ 3 * K * d := by
    rw [abs_div, abs_mul, abs_of_nonneg hD]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hq hD,
      mul_nonneg (show 0 ≤ 3 - (a + b) by linarith [ha.2, hb.2]) (mul_nonneg hK hd)]
  have hB : |a * (g xi ^ 2 - f xi ^ 2) / 2| ≤ M * d := by
    rw [abs_div, abs_mul, abs_of_nonneg ha.1]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hs ha.1,
      mul_nonneg (show 0 ≤ 1 - a by linarith [ha.2]) (mul_nonneg hM hd)]
  have hC : |b * (g eta ^ 2 - f eta ^ 2) / 2| ≤ 2 * M * d := by
    rw [abs_div, abs_mul, abs_of_nonneg hb0]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left ht hb0,
      mul_nonneg (show 0 ≤ 2 - b by linarith [hb.2]) (mul_nonneg hM hd)]
  have hI : |∫ x in xi..eta, g x - f x| ≤ 2 * W * d := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx ↦ show ‖g x - f x‖ ≤ d from by
        rw [Real.norm_eq_abs]
        exact hclose x (uIcc_subset_Icc hxi heta (uIoc_subset_uIcc hx)))
    rw [Real.norm_eq_abs] at hh
    have hgap : |eta - xi| ≤ 2 * W := by
      apply abs_le.2
      constructor <;> linarith [hxi.1, hxi.2, heta.1, heta.2]
    nlinarith [mul_le_mul_of_nonneg_left hgap hd]
  have heq : quadraticCost g xi eta a b - quadraticCost f xi eta a b =
      (a + b) * (qg ^ 2 - qf ^ 2) / 2 - a * (g xi ^ 2 - f xi ^ 2) / 2 -
        b * (g eta ^ 2 - f eta ^ 2) / 2 - ∫ x in xi..eta, g x - f x := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    unfold quadraticCost gaugedFourPointCost
    simp only [fourPointSourceValue, fourPointTargetValue, fourPointDenominator, id_eq]
    dsimp [qg, qf]
    ring
  rw [heq]
  have htri := abs_add_three ((a + b) * (qg ^ 2 - qf ^ 2) / 2)
    (-(a * (g xi ^ 2 - f xi ^ 2) / 2)) (-(b * (g eta ^ 2 - f eta ^ 2) / 2))
  have htri' := abs_add_le
    ((a + b) * (qg ^ 2 - qf ^ 2) / 2 - a * (g xi ^ 2 - f xi ^ 2) / 2 -
      b * (g eta ^ 2 - f eta ^ 2) / 2) (-(∫ x in xi..eta, g x - f x))
  simp only [abs_neg, ← sub_eq_add_neg] at htri htri'
  dsimp [K] at hA
  linarith

/-- Uniform graph convergence implies uniform convergence of the quadratic gauges on
the whole endpoint/mark window. -/
theorem tendstoUniformlyOn_quadraticCost_of_graph
    {ι : Type*} {l : Filter ι} {g : ι → ℝ → ℝ} {G : ℝ → ℝ} {W M : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hg : ∀ k, Continuous (g k)) (hG : Continuous G)
    (hgM : ∀ k x, x ∈ Icc (-W) W → |g k x| ≤ M)
    (hGM : ∀ x ∈ Icc (-W) W, |G x| ≤ M)
    (hconv : TendstoUniformlyOn g G l (Icc (-W) W)) :
    TendstoUniformlyOn
      (fun k p ↦ quadraticCost (g k) p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p ↦ quadraticCost G p.1 p.2.1 p.2.2.1 p.2.2.2) l (localCostWindow W) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro eps heps
  let C := 8 * W + 12 * M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 < eps / (C + 1) := div_pos heps (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ hd] with k hk
  intro p hp
  obtain ⟨hxi, heta, ha, hb⟩ := hp
  have hclose : ∀ x ∈ Icc (-W) W, |g k x - G x| ≤ eps / (C + 1) := by
    intro x hx
    simpa [Real.dist_eq, abs_sub_comm] using (hk x hx).le
  have hbnd := quadraticCost_sub_abs_le_of_graph_close hW hM hd.le hxi heta
    hG (hg k) hGM (hgM k) hclose ha hb
  rw [Real.dist_eq, abs_sub_comm]
  calc
    _ ≤ C * (eps / (C + 1)) := hbnd
    _ < eps := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (show 0 < C + 1 by positivity)).2 (by nlinarith)

/-- Actual rescaled Euclidean gauges converge uniformly to the limiting quadratic gauge.
The only convergence hypotheses concern spatial scaling, common height, and graph increments;
marks and both endpoint orders are uniform throughout their compact windows. -/
theorem tendstoUniformlyOn_localEuclideanCost
    {ι : Type*} {l : Filter ι} {n h : ι → ℝ} {g : ι → ℝ → ℝ}
    {G : ℝ → ℝ} {W M lam : ℝ}
    (hn : Tendsto n l atTop) (hh : Tendsto h l (𝓝 0))
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hg : ∀ k, Continuous (g k)) (hG : Continuous G)
    (hLip : ∀ k, ScalarLipschitz lam (g k))
    (hgM : ∀ k x, x ∈ Icc (-W) W → |g k x| ≤ M)
    (hGM : ∀ x ∈ Icc (-W) W, |G x| ≤ M)
    (hconv : TendstoUniformlyOn g G l (Icc (-W) W)) :
    TendstoUniformlyOn
      (fun k p ↦ localEuclideanCost (n k) (h k) (g k) p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p ↦ quadraticCost G p.1 p.2.1 p.2.2.1 p.2.2.2) l (localCostWindow W) := by
  have hE := tendstoUniformlyOn_localEuclideanCost_sub_quadratic
    hn hh hW hM hlam0 hlam hg hLip hgM
  have hQ := tendstoUniformlyOn_quadraticCost_of_graph hW hM hg hG hgM hGM hconv
  apply Metric.tendstoUniformlyOn_iff.2
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hE (eps / 2) (by positivity),
    Metric.tendstoUniformlyOn_iff.1 hQ (eps / 2) (by positivity)] with k hkE hkQ
  intro p hp
  have hke := hkE p hp
  have hkq := hkQ p hp
  simp only [Real.dist_eq, zero_sub, abs_neg] at hke hkq ⊢
  have htri := abs_sub_le (quadraticCost G p.1 p.2.1 p.2.2.1 p.2.2.2)
    (quadraticCost (g k) p.1 p.2.1 p.2.2.1 p.2.2.2)
    (localEuclideanCost (n k) (h k) (g k) p.1 p.2.1 p.2.2.1 p.2.2.2)
  rw [abs_sub_comm (quadraticCost (g k) _ _ _ _)] at htri
  linarith

/-- Horizontal rerooting is an exact identity for the actual Euclidean gauge. -/
theorem euclideanGaugedCost_translate (g : ℝ → ℝ) (z xi eta a b : ℝ) :
    euclideanGaugedCost (fun x ↦ g (x + z)) xi eta a b =
      euclideanGaugedCost g (xi + z) (eta + z) a b := by
  have hq : fourPointQuotient (fun x ↦ g (x + z)) xi eta a b =
      fourPointQuotient g (xi + z) (eta + z) a b := by
    unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
    congr 1
    ring
  unfold euclideanGaugedCost gaugedFourPointCost
  simp only [hq, fourPointSourceValue, fourPointTargetValue]
  rw [intervalIntegral.integral_comp_add_right
    (fun x ↦ euclideanResidualDeriv (g x)) z]

/-- The cost used above is exactly the normalized finite-graph gauge at a physical root.
Thus the uniform limit applies to the original finite Euclidean gauge, with no surrogate cost. -/
theorem localEuclideanCost_eq_rooted_gauge
    {n : ℝ} (hn : n ≠ 0) (graph : ℝ → ℝ) (root xi eta a b : ℝ) :
    localEuclideanCost n (graph root / n) (fun x ↦ graph (root + x) - graph root)
        xi eta a b =
      n ^ 2 * euclideanGaugedCost (fun z ↦ graph (n * z) / n)
        ((root + xi) / n) ((root + eta) / n) a b := by
  have hg : localNormalizedGraph n (graph root / n)
      (fun x ↦ graph (root + x) - graph root) =
        (fun z ↦ graph (n * (z + root / n)) / n) := by
    funext z
    unfold localNormalizedGraph
    rw [show n * (z + root / n) = root + n * z by field_simp; ring]
    ring
  unfold localEuclideanCost
  rw [hg]
  have ht := euclideanGaugedCost_translate (fun z ↦ graph (n * z) / n)
    (root / n) (xi / n) (eta / n) a b
  rw [ht]
  congr 2 <;> ring

/-- Joint continuity in both vertices and marks, away from zero horizontal separation. -/
theorem continuousAt_quadraticCost {G : ℝ → ℝ} (hG : Continuous G)
    {p : ℝ × ℝ × ℝ × ℝ} (hD : p.2.2.1 + p.2.2.2 ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ ↦
      quadraticCost G q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  have hprim : Continuous (fun x ↦ ∫ y in (0 : ℝ)..x, G y) :=
    intervalIntegral.continuous_primitive (fun a b ↦ hG.intervalIntegrable a b) 0
  have hI : Continuous (fun q : ℝ × ℝ × ℝ × ℝ ↦ ∫ x in q.1..q.2.1, G x) := by
    have heq : (fun q : ℝ × ℝ × ℝ × ℝ ↦ ∫ x in q.1..q.2.1, G x) =
        (fun q ↦ (∫ x in (0 : ℝ)..q.2.1, G x) - ∫ x in (0 : ℝ)..q.1, G x) := by
      funext q
      have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hG.intervalIntegrable 0 q.1) (hG.intervalIntegrable q.1 q.2.1)
      linarith
    rw [heq]
    fun_prop
  unfold quadraticCost gaugedFourPointCost fourPointQuotient fourPointGap
    fourPointSourceValue fourPointTargetValue fourPointDenominator
  simp only [id_eq]
  apply ContinuousAt.sub _ hI.continuousAt
  fun_prop (disch := first | exact hD | norm_num)

/-- Direct moving-vertex/mark API for a local edge in a finite permutation replacement. -/
theorem tendsto_localEuclideanCost_of_vertices
    {ι : Type*} {l : Filter ι} {n h : ι → ℝ} {g : ι → ℝ → ℝ}
    {G : ℝ → ℝ} {W M lam : ℝ} {p : ι → ℝ × ℝ × ℝ × ℝ} {q : ℝ × ℝ × ℝ × ℝ}
    (hn : Tendsto n l atTop) (hh : Tendsto h l (𝓝 0))
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hg : ∀ k, Continuous (g k)) (hG : Continuous G)
    (hLip : ∀ k, ScalarLipschitz lam (g k))
    (hgM : ∀ k x, x ∈ Icc (-W) W → |g k x| ≤ M)
    (hGM : ∀ x ∈ Icc (-W) W, |G x| ≤ M)
    (hconv : TendstoUniformlyOn g G l (Icc (-W) W))
    (hq : q ∈ localCostWindow W) (hp : Tendsto p l (𝓝[localCostWindow W] q)) :
    Tendsto (fun k ↦ localEuclideanCost (n k) (h k) (g k)
      (p k).1 (p k).2.1 (p k).2.2.1 (p k).2.2.2)
      l (𝓝 (quadraticCost G q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
  apply (tendstoUniformlyOn_localEuclideanCost hn hh hW hM hlam0 hlam
    hg hG hLip hgM hGM hconv).tendsto_comp _ hp
  apply (continuousAt_quadraticCost hG ?_).continuousWithinAt
  obtain ⟨_, _, ha, hb⟩ := hq
  linarith [ha.1, hb.1]

end OTSelector
