import OTSelector.Matching.DisagreementEnds
import OTSelector.PointProcess.MassTransport
import Mathlib.Algebra.Order.Group.CompleteLattice

/-!+# Transport from a one-sided infinite partner orbit

Every source of an infinite orbit bounded below sends one unit to the infimum
of that orbit's source positions. This avoids choosing an extremal labelled
vertex. The transport is measurable, has outgoing mass bounded by source count,
and places infinite incoming mass at the orbit's common infimum.
-/

open Function Set MeasureTheory Filter
open scoped ENNReal Classical

namespace OTSelector.Matching

variable {S : Type*}

def partnerOrbitPositions (p : Equiv.Perm S) (source : S → ℝ) (i : S) (n : ℤ) : ℝ :=
  source ((p ^ n) i)

/-- Covariance of all orbit coordinates follows from covariance of one partner step. -/
theorem partnerOrbitPositions_covariant (p p' : Equiv.Perm S) (source source' : S → ℝ)
    (r : Equiv.Perm S) (a : ℝ)
    (hs : ∀ i, source' (r i) = a + source i) (hp : ∀ i, p' (r i) = r (p i))
    (i : S) (n : ℤ) :
    partnerOrbitPositions p' source' (r i) n = a + partnerOrbitPositions p source i n := by
  have heq : p' = r * p * r⁻¹ := by
    ext j
    obtain ⟨k, rfl⟩ := r.surjective j
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hp k
  unfold partnerOrbitPositions
  rw [heq, conj_zpow]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hs]

/-- The active orbits of the lower-anchor transport. -/
def LowerAnchoredOrbit (p : Equiv.Perm S) (source : S → ℝ) (i : S) : Prop :=
  Injective (partnerOrbitPositions p source i) ∧ BddBelow (range (partnerOrbitPositions p source i))

theorem LowerAnchoredOrbit.not_fixed {p : Equiv.Perm S} {source : S → ℝ} {i : S}
    (hi : LowerAnchoredOrbit p source i) : p i ≠ i := by
  intro hfix
  have hh : partnerOrbitPositions p source i 1 = partnerOrbitPositions p source i 0 := by
    simp only [partnerOrbitPositions, zpow_one, zpow_zero, Equiv.Perm.one_apply, hfix]
  have := hi.1 hh
  norm_num at this

noncomputable def partnerLowerAnchor (p : Equiv.Perm S) (source : S → ℝ) (i : S) : ℝ :=
  ⨅ n : ℤ, partnerOrbitPositions p source i n

theorem partnerOrbitPositions_shift (p : Equiv.Perm S) (source : S → ℝ) (i : S) (k n : ℤ) :
    partnerOrbitPositions p source ((p ^ k) i) n = partnerOrbitPositions p source i (n + k) := by
  simp only [partnerOrbitPositions, zpow_add, Equiv.Perm.mul_apply]

theorem partnerOrbitPositions_range_shift (p : Equiv.Perm S) (source : S → ℝ) (i : S) (k : ℤ) :
    range (partnerOrbitPositions p source ((p ^ k) i)) = range (partnerOrbitPositions p source i) := by
  change range (fun n ↦ partnerOrbitPositions p source ((p ^ k) i) n) = _
  simp_rw [partnerOrbitPositions_shift]
  exact (Equiv.addRight k).surjective.range_comp (partnerOrbitPositions p source i)

theorem LowerAnchoredOrbit.shift {p : Equiv.Perm S} {source : S → ℝ} {i : S}
    (h : LowerAnchoredOrbit p source i) (k : ℤ) : LowerAnchoredOrbit p source ((p ^ k) i) := by
  constructor
  · intro m n hmn
    simp only [partnerOrbitPositions_shift] at hmn
    have := h.1 hmn
    omega
  · rw [partnerOrbitPositions_range_shift]
    exact h.2

theorem partnerLowerAnchor_shift (p : Equiv.Perm S) (source : S → ℝ) (i : S) (k : ℤ) :
    partnerLowerAnchor p source ((p ^ k) i) = partnerLowerAnchor p source i := by
  exact congrArg sInf (partnerOrbitPositions_range_shift p source i k)

/-- The actual countable transport assembled from one Dirac mass per active source. -/
noncomputable def partnerLowerTransport (p : Equiv.Perm S) (source : S → ℝ) : Measure (ℝ × ℝ) :=
  Measure.sum fun i ↦ if LowerAnchoredOrbit p source i then
    Measure.dirac (source i, partnerLowerAnchor p source i) else 0

theorem partnerLowerTransport_outgoing_le (p : Equiv.Perm S) (source : S → ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    partnerLowerTransport p source (A ×ˢ univ) ≤ ∑' i, if source i ∈ A then (1 : ℝ≥0∞) else 0 := by
  rw [partnerLowerTransport, Measure.sum_apply _ (hA.prod MeasurableSet.univ)]
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : LowerAnchoredOrbit p source i
  · simp [hi, Measure.dirac_apply' _ (hA.prod MeasurableSet.univ), Set.indicator_apply]
  · simp [hi]

/-- Fixed inactive labels send no mass, so only genuine active sources are counted. -/
theorem partnerLowerTransport_outgoing_le_active (p : Equiv.Perm S) (source : S → ℝ)
    (active : S → Prop) (hfix : ∀ i, ¬ active i → p i = i)
    (A : Set ℝ) (hA : MeasurableSet A) :
    partnerLowerTransport p source (A ×ˢ univ) ≤
      ∑' i, if active i ∧ source i ∈ A then (1 : ℝ≥0∞) else 0 := by
  rw [partnerLowerTransport, Measure.sum_apply _ (hA.prod MeasurableSet.univ)]
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : LowerAnchoredOrbit p source i
  · have hactive : active i := by by_contra h; exact hi.not_fixed (hfix i h)
    simp [hi, hactive, Measure.dirac_apply' _ (hA.prod MeasurableSet.univ), Set.indicator_apply]
  · simp [hi]

/-- All integer translates of an active source send to its same anchor, producing
infinite incoming mass in every measurable set containing that anchor. -/
theorem partnerLowerTransport_incoming_eq_top (p : Equiv.Perm S) (source : S → ℝ)
    {i : S} (hi : LowerAnchoredOrbit p source i) (A : Set ℝ) (hA : MeasurableSet A)
    (ha : partnerLowerAnchor p source i ∈ A) :
    partnerLowerTransport p source (univ ×ˢ A) = ∞ := by
  let mass : S → ℝ≥0∞ := fun j ↦
    (if LowerAnchoredOrbit p source j then
      Measure.dirac (source j, partnerLowerAnchor p source j) else 0) (univ ×ˢ A)
  have hinj : Injective (fun n : ℤ ↦ (p ^ n) i) := fun _ _ h ↦ hi.1 (congrArg source h)
  have hmass (n : ℤ) : mass ((p ^ n) i) = 1 := by
    simp only [mass, ite_eq_left (hi.shift n), partnerLowerAnchor_shift]
    simp [Measure.dirac_apply' _ (MeasurableSet.univ.prod hA), ha]
  apply top_unique
  rw [partnerLowerTransport, Measure.sum_apply _ (MeasurableSet.univ.prod hA)]
  change ∞ ≤ ∑' j, mass j
  calc
    ∞ = ∑' _ : ℤ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ = ∑' n : ℤ, mass ((p ^ n) i) := tsum_congr (fun n ↦ (hmass n).symm)
    _ ≤ ∑' j, mass j := ENNReal.tsum_comp_le_tsum_of_injective hinj mass

private theorem injective_bddBelow_translate_iff (x : ℤ → ℝ) (a : ℝ) :
    (Injective (fun n ↦ a + x n) ∧ BddBelow (range (fun n ↦ a + x n))) ↔
      (Injective x ∧ BddBelow (range x)) := by
  constructor
  · rintro ⟨hinj, b, hb⟩
    refine ⟨fun m n h ↦ hinj (congrArg (fun z ↦ a + z) h), b - a, ?_⟩
    rintro y ⟨n, rfl⟩
    have := hb ⟨n, rfl⟩
    linarith
  · rintro ⟨hinj, b, hb⟩
    refine ⟨fun m n h ↦ hinj (by linarith), a + b, ?_⟩
    rintro y ⟨n, rfl⟩
    have := hb ⟨n, rfl⟩
    linarith

/-- Translation and relabelling of the actual integer orbit preserve the active event. -/
theorem lowerAnchoredOrbit_covariant (p p' : Equiv.Perm S) (source source' : S → ℝ)
    (r : Equiv.Perm S) (a : ℝ)
    (hcov : ∀ i n, partnerOrbitPositions p' source' (r i) n =
      a + partnerOrbitPositions p source i n) (i : S) :
    LowerAnchoredOrbit p' source' (r i) ↔ LowerAnchoredOrbit p source i := by
  unfold LowerAnchoredOrbit
  have hh : partnerOrbitPositions p' source' (r i) = fun n ↦ a + partnerOrbitPositions p source i n :=
    funext (hcov i)
  rw [hh]
  exact injective_bddBelow_translate_iff _ _

theorem partnerLowerAnchor_covariant (p p' : Equiv.Perm S) (source source' : S → ℝ)
    (r : Equiv.Perm S) (a : ℝ)
    (hcov : ∀ i n, partnerOrbitPositions p' source' (r i) n =
      a + partnerOrbitPositions p source i n) {i : S} (hi : LowerAnchoredOrbit p source i) :
    partnerLowerAnchor p' source' (r i) = a + partnerLowerAnchor p source i := by
  simp only [partnerLowerAnchor, hcov]
  exact (add_ciInf hi.2 a).symm

/-- The constructed measure, rather than a transport covariance assumption, transforms
correctly under translations and the actual source-label relabelling. -/
theorem partnerLowerTransport_covariant (p p' : Equiv.Perm S) (source source' : S → ℝ)
    (r : Equiv.Perm S) (a : ℝ)
    (hcov : ∀ i n, partnerOrbitPositions p' source' (r i) n =
      a + partnerOrbitPositions p source i n) :
    partnerLowerTransport p' source' =
      (partnerLowerTransport p source).map (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) := by
  have hmap : Measurable (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) := by fun_prop
  unfold partnerLowerTransport
  rw [← Measure.sum_comp_equiv r (fun i ↦ if LowerAnchoredOrbit p' source' i then
    Measure.dirac (source' i, partnerLowerAnchor p' source' i) else 0)]
  rw [Measure.map_sum hmap.aemeasurable]
  congr 1
  funext i
  have hiiff := lowerAnchoredOrbit_covariant p p' source source' r a hcov i
  have hs : source' (r i) = a + source i := by
    simpa only [partnerOrbitPositions, zpow_zero, Equiv.Perm.one_apply] using hcov i 0
  by_cases hi : LowerAnchoredOrbit p source i
  · simp only [Function.comp_apply, ite_eq_left hi, ite_eq_left (hiiff.mpr hi),
      Measure.map_dirac' hmap, hs,
      partnerLowerAnchor_covariant p p' source source' r a hcov hi]
  · simp only [Function.comp_apply, ite_eq_right hi, ite_eq_right (hiiff.not.mpr hi),
      Measure.map_zero]

/-- Active-label covariance needs no translation law for the arbitrary positions of
inactive fixed labels. Those labels contribute the zero measure on both sides. -/
theorem partnerLowerTransport_covariant_active
    (p p' : Equiv.Perm S) (source source' : S → ℝ) (active active' : S → Prop)
    (hfix : ∀ i, ¬ active i → p i = i) (hfix' : ∀ i, ¬ active' i → p' i = i)
    (r : Equiv.Perm S) (a : ℝ) (hr : ∀ i, active' (r i) ↔ active i)
    (hcov : ∀ i, active i → ∀ n, partnerOrbitPositions p' source' (r i) n =
      a + partnerOrbitPositions p source i n) :
    partnerLowerTransport p' source' =
      (partnerLowerTransport p source).map (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) := by
  have hmap : Measurable (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) := by fun_prop
  unfold partnerLowerTransport
  rw [← Measure.sum_comp_equiv r (fun i ↦ if LowerAnchoredOrbit p' source' i then
    Measure.dirac (source' i, partnerLowerAnchor p' source' i) else 0)]
  rw [Measure.map_sum hmap.aemeasurable]
  congr 1
  funext i
  by_cases hactive : active i
  · have hh : partnerOrbitPositions p' source' (r i) =
        fun n ↦ a + partnerOrbitPositions p source i n := funext (hcov i hactive)
    have hiiff : LowerAnchoredOrbit p' source' (r i) ↔ LowerAnchoredOrbit p source i := by
      unfold LowerAnchoredOrbit
      rw [hh]
      exact injective_bddBelow_translate_iff _ _
    have hs : source' (r i) = a + source i := by
      simpa only [partnerOrbitPositions, zpow_zero, Equiv.Perm.one_apply] using hcov i hactive 0
    by_cases hi : LowerAnchoredOrbit p source i
    · have ha : partnerLowerAnchor p' source' (r i) = a + partnerLowerAnchor p source i := by
        unfold partnerLowerAnchor
        rw [hh]
        exact (add_ciInf hi.2 a).symm
      simp only [Function.comp_apply, ite_eq_left hi, ite_eq_left (hiiff.mpr hi),
        Measure.map_dirac' hmap, hs, ha]
    · simp only [Function.comp_apply, ite_eq_right hi, ite_eq_right (hiiff.not.mpr hi), Measure.map_zero]
  · have hi : ¬ LowerAnchoredOrbit p source i := fun hi ↦ hi.not_fixed (hfix i hactive)
    have hi' : ¬ LowerAnchoredOrbit p' source' (r i) :=
      fun hi ↦ hi.not_fixed (hfix' _ ((hr i).not.mpr hactive))
    simp only [Function.comp_apply, ite_eq_right hi, ite_eq_right hi', Measure.map_zero]

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] [Countable S]
variable (p : Ω → Equiv.Perm S) (source : Ω → S → ℝ)
variable (horbit : ∀ i n, Measurable (fun ω ↦ partnerOrbitPositions (p ω) (source ω) i n))
include horbit

omit [Countable S] in
theorem measurableSet_lowerAnchoredOrbit (i : S) :
    MeasurableSet {ω | LowerAnchoredOrbit (p ω) (source ω) i} := by
  apply MeasurableSet.inter _ (measurableSet_bddBelow_range (fun n ↦ horbit i n))
  change MeasurableSet {ω | ∀ m n, partnerOrbitPositions (p ω) (source ω) i m =
    partnerOrbitPositions (p ω) (source ω) i n → m = n}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro n
  by_cases hmn : m = n
  · simp only [hmn, implies_true, Set.ofPred_true, MeasurableSet.univ]
  · simpa only [hmn, imp_false, Set.compl_ofPred] using
      (measurableSet_eq_fun (horbit i m) (horbit i n)).compl

omit [Countable S] in
theorem measurable_partnerLowerAnchor (i : S) :
    Measurable (fun ω ↦ partnerLowerAnchor (p ω) (source ω) i) :=
  Measurable.iInf (fun n ↦ horbit i n)

theorem measurable_partnerLowerTransport :
    Measurable (fun ω ↦ partnerLowerTransport (p ω) (source ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [partnerLowerTransport, Measure.sum_apply _ hA]
  apply Measurable.tsum
  intro i
  have hs : Measurable (fun ω ↦ source ω i) := by
    simpa only [partnerOrbitPositions, zpow_zero, Equiv.Perm.one_apply] using horbit i 0
  have hd := Measure.measurable_dirac.comp (hs.prodMk (measurable_partnerLowerAnchor p source horbit i))
  exact (Measure.measurable_coe hA).comp
    (hd.ite (measurableSet_lowerAnchoredOrbit p source horbit i) measurable_const)

private theorem ae_not_lowerAnchoredOrbit_of_transport (P : Measure Ω) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hTcov : ∀ a, ∀ᵐ ω ∂P,
      partnerLowerTransport (p (shift a ω)) (source (shift a ω)) =
        (partnerLowerTransport (p ω) (source ω)).map
          (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)))
    (hout : (∫⁻ ω, partnerLowerTransport (p ω) (source ω) (Ioc 0 1 ×ˢ univ) ∂P) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ¬ LowerAnchoredOrbit (p ω) (source ω) i := by
  let T := fun ω ↦ partnerLowerTransport (p ω) (source ω)
  have hT : Measurable T := measurable_partnerLowerTransport p source horbit
  have hunit := OTSelector.PointProcess.ae_incoming_unit_lt_top P T hT shift hshift hTcov hout
  have hwindow (k : ℤ) : ∀ᵐ ω ∂P, T ω (univ ×ˢ Ioc (k : ℝ) (k + 1)) < ∞ := by
    filter_upwards [(hshift (-(k : ℝ))).quasiMeasurePreserving.ae hunit, hTcov (-(k : ℝ))]
      with ω hfinite hc
    dsimp only [T] at hfinite
    rw [hc, Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod measurableSet_Ioc)] at hfinite
    convert hfinite using 2
    ext z
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
  filter_upwards [ae_all_iff.mpr hwindow] with ω hω
  intro i hi
  let a := partnerLowerAnchor (p ω) (source ω) i
  let k := Int.ceil a - 1
  have ha : a ∈ Ioc (k : ℝ) (k + 1) := by
    have hl := Int.ceil_lt_add_one a
    have hr := Int.le_ceil a
    dsimp only [k]
    simp only [Int.cast_sub, Int.cast_one, Set.mem_Ioc]
    constructor <;> linarith
  have htop := partnerLowerTransport_incoming_eq_top (p ω) (source ω) hi _ measurableSet_Ioc ha
  have hh := hω k
  rw [show T ω (univ ×ˢ Ioc (k : ℝ) (k + 1)) = ∞ from htop] at hh
  exact (lt_irrefl _) hh


/-- Stationarity and finite source intensity exclude every lower-bounded infinite
orbit. Covariance is required only for the actual source coordinates under a
source-label permutation; the transport and its incoming divergence are proved. -/
theorem ae_not_lowerAnchoredOrbit (P : Measure Ω) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S, ∀ i n,
      partnerOrbitPositions (p (shift a ω)) (source (shift a ω)) (r i) n =
        a + partnerOrbitPositions (p ω) (source ω) i n)
    (hintensity : (∫⁻ ω, ∑' i, if source ω i ∈ Ioc 0 1 then (1 : ℝ≥0∞) else 0 ∂P) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ¬ LowerAnchoredOrbit (p ω) (source ω) i := by
  let T := fun ω ↦ partnerLowerTransport (p ω) (source ω)
  have hTcov (a : ℝ) : ∀ᵐ ω ∂P,
      T (shift a ω) = (T ω).map (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) := by
    filter_upwards [hcov a] with ω hω
    obtain ⟨r, hr⟩ := hω
    exact partnerLowerTransport_covariant (p ω) (p (shift a ω)) (source ω) (source (shift a ω)) r a hr
  have hout : (∫⁻ ω, T ω (Ioc 0 1 ×ˢ univ) ∂P) < ∞ := by
    apply lt_of_le_of_lt _ hintensity
    apply lintegral_mono
    intro ω
    convert partnerLowerTransport_outgoing_le (p ω) (source ω) _ measurableSet_Ioc using 1
    simp
  exact ae_not_lowerAnchoredOrbit_of_transport p source horbit P shift hshift hTcov hout

/-- The active-label form counts only genuine sources and permits arbitrary ghost
coordinates. The partner permutation fixes every inactive label almost surely. -/
theorem ae_not_lowerAnchoredOrbit_active (active : Ω → S → Prop)
    (P : Measure Ω) (shift : ℝ → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hfix : ∀ᵐ ω ∂P, ∀ i, ¬ active ω i → p ω i = i)
    (hcov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S,
      (∀ i, active (shift a ω) (r i) ↔ active ω i) ∧
      ∀ i, active ω i → ∀ n,
        partnerOrbitPositions (p (shift a ω)) (source (shift a ω)) (r i) n =
          a + partnerOrbitPositions (p ω) (source ω) i n)
    (hintensity : (∫⁻ ω, ∑' i,
      if active ω i ∧ source ω i ∈ Ioc 0 1 then (1 : ℝ≥0∞) else 0 ∂P) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ¬ LowerAnchoredOrbit (p ω) (source ω) i := by
  apply ae_not_lowerAnchoredOrbit_of_transport p source horbit P shift hshift
  · intro a
    filter_upwards [hcov a, hfix, (hshift a).quasiMeasurePreserving.ae hfix] with ω hc hf hf'
    obtain ⟨r, hr, hp⟩ := hc
    exact partnerLowerTransport_covariant_active (p ω) (p (shift a ω))
      (source ω) (source (shift a ω)) (active ω) (active (shift a ω)) hf hf' r a hr hp
  · apply lt_of_le_of_lt _ hintensity
    apply lintegral_mono_ae
    filter_upwards [hfix] with ω hf
    convert partnerLowerTransport_outgoing_le_active (p ω) (source ω) (active ω) hf
      (Ioc 0 1) measurableSet_Ioc using 1
    simp

/-- Both one-sided infinite orbit types are absent with only active-source intensity.
This is the form for fixed raw event labels with inactive labels fixed by the partner map. -/
theorem ae_not_oneSidedAnchoredOrbit_active (active : Ω → S → Prop)
    (P : Measure Ω) (shift : ℝ → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hfix : ∀ᵐ ω ∂P, ∀ i, ¬ active ω i → p ω i = i)
    (hcov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S,
      (∀ i, active (shift a ω) (r i) ↔ active ω i) ∧
      ∀ i, active ω i → ∀ n,
        partnerOrbitPositions (p (shift a ω)) (source (shift a ω)) (r i) n =
          a + partnerOrbitPositions (p ω) (source ω) i n)
    (hintensity : (∫⁻ ω, ∑' i,
      if active ω i ∧ source ω i ∈ Icc (-1) 1 then (1 : ℝ≥0∞) else 0 ∂P) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ¬ LowerAnchoredOrbit (p ω) (source ω) i ∧
      ¬ LowerAnchoredOrbit (p ω) (fun j ↦ -source ω j) i := by
  have hcount (f : ℝ → ℝ) (hf : ∀ x, f x ∈ Ioc 0 1 → x ∈ Icc (-1) 1) :
      (∫⁻ ω, ∑' i, if active ω i ∧ f (source ω i) ∈ Ioc 0 1
        then (1 : ℝ≥0∞) else 0 ∂P) < ∞ := by
    apply lt_of_le_of_lt _ hintensity
    apply lintegral_mono
    intro ω
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hi : active ω i ∧ f (source ω i) ∈ Ioc 0 1
    · have hi' : active ω i ∧ source ω i ∈ Icc (-1) 1 := ⟨hi.1, hf _ hi.2⟩
      simp only [ite_eq_left hi, ite_eq_left hi', le_refl]
    · simp only [ite_eq_right hi, zero_le]
  have hpos := ae_not_lowerAnchoredOrbit_active p source horbit active P shift hshift hfix hcov
    (hcount id (fun _ h ↦ ⟨by dsimp at h; linarith [h.1], h.2⟩))
  have hnmeas : ∀ i n, Measurable (fun ω ↦ partnerOrbitPositions (p ω) (fun j ↦ -source ω j) i n) :=
    fun i n ↦ (horbit i n).neg
  have hncov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S,
      (∀ i, active (shift (-a) ω) (r i) ↔ active ω i) ∧
      ∀ i, active ω i → ∀ n,
        partnerOrbitPositions (p (shift (-a) ω)) (fun j ↦ -source (shift (-a) ω) j) (r i) n =
          a + partnerOrbitPositions (p ω) (fun j ↦ -source ω j) i n := by
    intro a
    filter_upwards [hcov (-a)] with ω hω
    obtain ⟨r, hr, hp⟩ := hω
    refine ⟨r, hr, fun i hi n ↦ ?_⟩
    change -partnerOrbitPositions (p (shift (-a) ω)) (source (shift (-a) ω)) (r i) n =
      a + -partnerOrbitPositions (p ω) (source ω) i n
    rw [hp i hi n]
    ring
  have hneg := ae_not_lowerAnchoredOrbit_active p (fun ω j ↦ -source ω j) hnmeas active P
    (fun a ↦ shift (-a)) (fun a ↦ hshift (-a)) hfix hncov
    (hcount Neg.neg (fun _ h ↦ ⟨by linarith [h.2], by linarith [h.1]⟩))
  filter_upwards [hpos, hneg] with ω hp hn
  exact fun i ↦ ⟨hp i, hn i⟩

/-- Finite source intensity in one bounded window excludes both kinds of one-sided
infinite orbit. Reflection reuses the same constructed lower-anchor transport. -/
theorem ae_not_oneSidedAnchoredOrbit (P : Measure Ω) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S, ∀ i n,
      partnerOrbitPositions (p (shift a ω)) (source (shift a ω)) (r i) n =
        a + partnerOrbitPositions (p ω) (source ω) i n)
    (hintensity : (∫⁻ ω, ∑' i, if source ω i ∈ Icc (-1) 1 then (1 : ℝ≥0∞) else 0 ∂P) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ¬ LowerAnchoredOrbit (p ω) (source ω) i ∧
      ¬ LowerAnchoredOrbit (p ω) (fun j ↦ -source ω j) i := by
  have hcount (f : ℝ → ℝ) (hf : ∀ x, f x ∈ Ioc 0 1 → x ∈ Icc (-1) 1) :
      (∫⁻ ω, ∑' i, if f (source ω i) ∈ Ioc 0 1 then (1 : ℝ≥0∞) else 0 ∂P) < ∞ := by
    apply lt_of_le_of_lt _ hintensity
    apply lintegral_mono
    intro ω
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hi : f (source ω i) ∈ Ioc 0 1
    · simp only [ite_eq_left hi, ite_eq_left (hf _ hi), le_refl]
    · simp only [ite_eq_right hi, zero_le]
  have hpos := ae_not_lowerAnchoredOrbit p source horbit P shift hshift hcov
    (hcount id (fun _ h ↦ ⟨by dsimp at h; linarith [h.1], h.2⟩))
  have hnmeas : ∀ i n, Measurable (fun ω ↦ partnerOrbitPositions (p ω) (fun j ↦ -source ω j) i n) :=
    fun i n ↦ (horbit i n).neg
  have hncov : ∀ a, ∀ᵐ ω ∂P, ∃ r : Equiv.Perm S, ∀ i n,
      partnerOrbitPositions (p (shift (-a) ω)) (fun j ↦ -source (shift (-a) ω) j) (r i) n =
        a + partnerOrbitPositions (p ω) (fun j ↦ -source ω j) i n := by
    intro a
    filter_upwards [hcov (-a)] with ω hω
    obtain ⟨r, hr⟩ := hω
    refine ⟨r, fun i n ↦ ?_⟩
    change -partnerOrbitPositions (p (shift (-a) ω)) (source (shift (-a) ω)) (r i) n =
      a + -partnerOrbitPositions (p ω) (source ω) i n
    rw [hr]
    ring
  have hneg := ae_not_lowerAnchoredOrbit p (fun ω j ↦ -source ω j) hnmeas P
    (fun a ↦ shift (-a)) (fun a ↦ hshift (-a)) hncov
    (hcount Neg.neg (fun _ h ↦ ⟨by linarith [h.2], by linarith [h.1]⟩))
  filter_upwards [hpos, hneg] with ω hp hn
  exact fun i ↦ ⟨hp i, hn i⟩

end Measurability

end OTSelector.Matching
