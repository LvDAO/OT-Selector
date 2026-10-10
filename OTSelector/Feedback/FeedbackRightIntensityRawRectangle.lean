import OTSelector.Feedback.FeedbackRightIntensityCompensator
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Raw rectangle compensation for independent frozen-tail lifetimes

The raw observation is the pair of attained counts for two fixed label groups.  Replacing a
label whose crossing is after the observation time leaves the entire observed past unchanged.
This permits one-point compensation on each coordinate fiber, followed by product Fubini.

The final two theorems specialize the result to the actual marked-square laws conditioned on
the strict source/target remaining regions at a fixed frozen boundary.  They identify the
integrated rates with the full remaining-before counts divided by physical remaining areas.
The separate transport through a random revealed boundary and the joined bulk filtration is
not part of these fixed-boundary theorems.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector

namespace RightTail

variable {A : Type*} [MeasurableSpace A] {m : ℕ}

/-- Count the labels in a fixed group that have crossed by physical coordinate `t`. -/
noncomputable def count {ι : Type*} (X : ι → A → ℝ) (J : Finset ι)
    (t : ℝ) (ω : ι → A) : ℝ :=
  ∑ i ∈ J, if X i (ω i) ≤ t then 1 else 0

theorem measurable_count {ι : Type*} (X : ι → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J : Finset ι) (t : ℝ) : Measurable (count X J t) := by
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite
    (measurableSet_le ((hX i).comp (measurable_pi_apply i)) measurable_const)
    measurable_const measurable_const

/-- The natural history consists of two counts, without future label identities. -/
noncomputable def rawFiltration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → A → ℝ) (hX : ∀ i, Measurable (X i)) (J : Finset ι) :
    Filtration ℝ (inferInstance : MeasurableSpace (ι → A)) :=
  Filtration.natural (fun t ω ↦ (count X J t ω, count X Jᶜ t ω))
    (fun t ↦ ((measurable_count X hX J t).prodMk
      (measurable_count X hX Jᶜ t)).stronglyMeasurable)

omit [MeasurableSpace A] in
theorem count_insertNth_eq_of_future
    (X : Fin (m + 1) → A → ℝ) (J : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) (rest : Fin m → A) (x y : A) {s u : ℝ}
    (hx : s < X i x) (hy : s < X i y) (hus : u ≤ s) :
    count X J u (i.insertNth x rest) = count X J u (i.insertNth y rest) := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [Fin.insertNth_apply_same,
      ite_eq_right (not_le.mpr (hus.trans_lt hx)),
      ite_eq_right (not_le.mpr (hus.trans_lt hy))]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp only [Fin.insertNth_apply_succAbove]

/-- Every raw-history event is constant on the fiber of one as-yet unobserved label. -/
theorem rawEvent_insertNth_mem_iff_of_future
    (X : Fin (m + 1) → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J : Finset (Fin (m + 1))) (i : Fin (m + 1)) (rest : Fin m → A)
    (x y : A) {s : ℝ} (hx : s < X i x) (hy : s < X i y)
    {E : Set (Fin (m + 1) → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    i.insertNth x rest ∈ E ↔ i.insertNth y rest ∈ E := by
  rw [rawFiltration, Filtration.natural_eq_comap] at hE
  obtain ⟨D, hD, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hE
  rw [← hpre]
  simp only [Set.mem_preimage]
  apply iff_of_eq
  congr 1
  funext u
  exact Prod.ext (count_insertNth_eq_of_future X J i rest x y hx hy u.2)
    (count_insertNth_eq_of_future X Jᶜ i rest x y hx hy u.2)

/-- Fubini with one selected coordinate placed in the inner integral. -/
theorem integral_pi_eq_integral_insertNth
    (P : Fin (m + 1) → Measure A) [∀ i, SigmaFinite (P i)] (i : Fin (m + 1))
    (f : (Fin (m + 1) → A) → ℝ) (hf : Integrable f (Measure.pi P)) :
    (∫ ω, f ω ∂Measure.pi P) =
      ∫ rest, ∫ x, f (i.insertNth x rest) ∂P i ∂Measure.pi (fun j ↦ P (i.succAbove j)) := by
  have hpres := (measurePreserving_piFinSuccAbove P i).symm
  have hint := hpres.integrable_comp_of_integrable hf
  rw [← hpres.integral_comp' f]
  exact integral_prod_symm _ hint

end RightTail

/-- A past event that is constant while a point is still unseen can be included in the
one-point Fubini identity. -/
theorem affineSurvival_onePoint_compensator_on_past_event
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (X : Ω → ℝ) (hX : Measurable X)
    {s t K D : ℝ} (hst : s ≤ t) (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ u ∈ Icc s t, ν.real {ω | u < X ω} = (K - u) / D)
    (E : Set Ω)
    (hpast : ∀ x y, s < X x → s < X y → (x ∈ E ↔ y ∈ E)) :
    (∫ ω, if ω ∈ E ∧ s < X ω ∧ X ω ≤ t then (1 : ℝ) else 0 ∂ν) =
      ∫ ω, ∫ u in Ioc s t,
        if ω ∈ E ∧ u < X ω then 1 / (K - u) else 0 ∂volume ∂ν := by
  by_cases hex : ∃ x, s < X x
  · obtain ⟨x, hx⟩ := hex
    let c : ℝ := if x ∈ E then 1 else 0
    have hbase := affineSurvival_onePoint_compensator ν X hX hst hfloor hD hsurvival c
    have hwindow : MeasurableSet {ω | s < X ω ∧ X ω ≤ t} :=
      (measurableSet_lt measurable_const hX).inter (measurableSet_le hX measurable_const)
    rw [← integral_indicator hwindow] at hbase
    calc
      (∫ ω, if ω ∈ E ∧ s < X ω ∧ X ω ≤ t then (1 : ℝ) else 0 ∂ν) =
          ∫ ω, {ω | s < X ω ∧ X ω ≤ t}.indicator (fun _ ↦ c) ω ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω ↦ by
          by_cases hω : s < X ω ∧ X ω ≤ t
          · have hmem := hpast ω x hω.1 hx
            rw [Set.indicator_of_mem (show ω ∈ {ω | s < X ω ∧ X ω ≤ t} from hω)]
            by_cases hE : x ∈ E
            · simp [c, hE, hmem.mpr hE, hω]
            · have hnot : ω ∉ E := fun h ↦ hE (hmem.mp h)
              simp [c, hE, hnot]
          · rw [Set.indicator_of_notMem (show ω ∉ {ω | s < X ω ∧ X ω ≤ t} from hω)]
            dsimp only
            rw [ite_eq_right]
            tauto
      _ = ∫ ω, ∫ u in Ioc s t, if u < X ω then c / (K - u) else 0 ∂volume ∂ν := hbase
      _ = ∫ ω, ∫ u in Ioc s t,
            if ω ∈ E ∧ u < X ω then 1 / (K - u) else 0 ∂volume ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω ↦ by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          by_cases huX : u < X ω
          · have hmem := hpast ω x (hu.1.trans huX) hx
            by_cases hE : x ∈ E
            · simp [c, hE, hmem.mpr hE, huX]
            · have hnot : ω ∉ E := fun h ↦ hE (hmem.mp h)
              simp [c, hE, hnot, huX]
          · simp [huX]
  · have hzero : ∀ ω, ¬s < X ω := fun ω h ↦ hex ⟨ω, h⟩
    have hleft : (∫ ω, if ω ∈ E ∧ s < X ω ∧ X ω ≤ t then (1 : ℝ) else 0 ∂ν) = 0 := by
      simp [hzero]
    rw [hleft]
    symm
    apply integral_eq_zero_of_ae
    exact ae_of_all _ fun ω ↦ by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro u hu
      have hnot : ¬u < X ω := fun h ↦ hzero ω (hu.1.trans h)
      simp [hnot]

namespace RightTail

variable {A : Type*} [MeasurableSpace A] {m : ℕ}

noncomputable def labelWindow (X : Fin m → A → ℝ) (i : Fin m)
    (E : Set (Fin m → A)) (s t : ℝ) (ω : Fin m → A) : ℝ :=
  if ω ∈ E ∧ s < X i (ω i) ∧ X i (ω i) ≤ t then 1 else 0

noncomputable def labelHazard (X : Fin m → A → ℝ) (i : Fin m)
    (E : Set (Fin m → A)) (K u : ℝ) (ω : Fin m → A) : ℝ :=
  if ω ∈ E ∧ u < X i (ω i) then 1 / (K - u) else 0

noncomputable def labelHazardIntegral (X : Fin m → A → ℝ) (i : Fin m)
    (E : Set (Fin m → A)) (K s t : ℝ) (ω : Fin m → A) : ℝ :=
  ∫ u in Ioc s t, labelHazard X i E K u ω

theorem integrable_labelWindow
    (P : Fin m → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin m → A → ℝ) (hX : ∀ i, Measurable (X i)) (i : Fin m)
    {E : Set (Fin m → A)} (hE : MeasurableSet E) (s t : ℝ) :
    Integrable (labelWindow X i E s t) (Measure.pi P) := by
  have hXi : Measurable fun ω : Fin m → A ↦ X i (ω i) :=
    (hX i).comp (measurable_pi_apply i)
  have hmeas : Measurable (labelWindow X i E s t) :=
    Measurable.ite (hE.inter ((measurableSet_lt measurable_const hXi).inter
      (measurableSet_le hXi measurable_const))) measurable_const measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  exact ae_of_all _ fun ω ↦ by unfold labelWindow; split_ifs <;> norm_num

theorem integrable_labelHazardIntegral
    (P : Fin m → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin m → A → ℝ) (hX : ∀ i, Measurable (X i)) (i : Fin m)
    {E : Set (Fin m → A)} (hE : MeasurableSet E) {K s t : ℝ} (hfloor : 0 < K - t) :
    Integrable (labelHazardIntegral X i E K s t) (Measure.pi P) := by
  let Z : (Fin m → A) × ℝ → ℝ := fun z ↦
    if z.2 ∈ Ioc s t ∧ z.1 ∈ E ∧ z.2 < X i (z.1 i) then 1 / (K - z.2) else 0
  have hXi : Measurable fun z : (Fin m → A) × ℝ ↦ X i (z.1 i) :=
    (hX i).comp ((measurable_pi_apply i).comp measurable_fst)
  have hZ : Measurable Z :=
    Measurable.ite ((measurable_snd measurableSet_Ioc).inter
      ((measurable_fst hE).inter (measurableSet_lt measurable_snd hXi)))
        (measurable_const.div (measurable_const.sub measurable_snd)) measurable_const
  have hZint : Integrable Z ((Measure.pi P).prod (volume.restrict (Ioc s t))) := by
    apply Integrable.of_bound hZ.aestronglyMeasurable (1 / (K - t))
    exact ae_of_all _ fun z ↦ by
      by_cases hz : z.2 ∈ Ioc s t ∧ z.1 ∈ E ∧ z.2 < X i (z.1 i)
      · have hden := hfloor.trans_le (sub_le_sub_left hz.1.2 K)
        simp only [Z, ite_eq_left hz, norm_div, norm_one, Real.norm_of_nonneg hden.le]
        exact one_div_le_one_div_of_le hfloor (sub_le_sub_left hz.1.2 K)
      · simp only [Z, ite_eq_right hz, norm_zero]
        exact one_div_nonneg.mpr hfloor.le
  apply hZint.integral_prod_left.congr
  exact ae_of_all _ fun ω ↦ by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    simp only [Z, hu, true_and, labelHazard]

/-- The count-window contribution of one independent label satisfies the raw rectangle
identity for every event measurable in the actual two-count observation history. -/
theorem label_rawRectangle_succ
    (P : Fin (m + 1) → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin (m + 1) → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J : Finset (Fin (m + 1))) (i : Fin (m + 1))
    {s t K D : ℝ} (hst : s ≤ t) (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ u ∈ Icc s t, (P i).real {x | u < X i x} = (K - u) / D)
    {E : Set (Fin (m + 1) → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    (∫ ω, labelWindow X i E s t ω ∂Measure.pi P) =
      ∫ ω, labelHazardIntegral X i E K s t ω ∂Measure.pi P := by
  have hEambient := (rawFiltration X hX J).le s E hE
  rw [integral_pi_eq_integral_insertNth P i _
    (integrable_labelWindow P X hX i hEambient s t),
    integral_pi_eq_integral_insertNth P i _
      (integrable_labelHazardIntegral P X hX i hEambient hfloor)]
  apply integral_congr_ae
  exact ae_of_all _ fun rest ↦ by
    let Efiber : Set A := {x : A | i.insertNth x rest ∈ E}
    have hpast : ∀ x y : A, s < X i x → s < X i y → (x ∈ Efiber ↔ y ∈ Efiber) := by
      intro x y hx hy
      exact rawEvent_insertNth_mem_iff_of_future X hX J i rest x y hx hy hE
    have hfiber := affineSurvival_onePoint_compensator_on_past_event
      (P i) (X i) (hX i) hst hfloor hD hsurvival Efiber hpast
    simpa only [labelWindow, labelHazardIntegral, labelHazard,
      Fin.insertNth_apply_same, Efiber, mem_ofPred_eq] using hfiber

theorem label_rawRectangle
    (P : Fin m → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin m → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J : Finset (Fin m)) (i : Fin m)
    {s t K D : ℝ} (hst : s ≤ t) (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ u ∈ Icc s t, (P i).real {x | u < X i x} = (K - u) / D)
    {E : Set (Fin m → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    (∫ ω, labelWindow X i E s t ω ∂Measure.pi P) =
      ∫ ω, labelHazardIntegral X i E K s t ω ∂Measure.pi P := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m => exact label_rawRectangle_succ P X hX J i hst hfloor hD hsurvival hE

omit [MeasurableSpace A] in
theorem integrableOn_labelHazard
    (X : Fin m → A → ℝ) (i : Fin m) (E : Set (Fin m → A))
    {K s t : ℝ} (hfloor : 0 < K - t) (ω : Fin m → A) :
    IntegrableOn (fun u ↦ labelHazard X i E K u ω) (Ioc s t) volume := by
  by_cases hω : ω ∈ E
  · have hmeas : Measurable fun u : ℝ ↦ labelHazard X i E K u ω := by
      simp only [labelHazard, hω, true_and]
      exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
        (measurable_const.div (measurable_const.sub measurable_id)) measurable_const
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hmeas.aestronglyMeasurable
      (M := 1 / (K - t))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    by_cases huX : u < X i (ω i)
    · have hden := hfloor.trans_le (sub_le_sub_left hu.2 K)
      simp only [labelHazard, hω, huX, and_self, ite_true, norm_div, norm_one,
        Real.norm_of_nonneg hden.le]
      exact one_div_le_one_div_of_le hfloor (sub_le_sub_left hu.2 K)
    · simp only [labelHazard, huX, and_false, ite_false, norm_zero]
      exact one_div_nonneg.mpr hfloor.le
  · simp only [labelHazard, hω, false_and, ite_false]
    exact integrableOn_zero

/-- Exact raw rectangle identity for a finite group of independent lifetimes with affine
survival laws.  Ties are permitted.  Both histories and counts are the concrete natural ones. -/
theorem count_rawRectangle
    (P : Fin m → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin m → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J L : Finset (Fin m)) (K D : Fin m → ℝ)
    {s t : ℝ} (hst : s ≤ t)
    (hfloor : ∀ i ∈ L, 0 < K i - t) (hD : ∀ i ∈ L, D i ≠ 0)
    (hsurvival : ∀ i ∈ L, ∀ u ∈ Icc s t,
      (P i).real {x | u < X i x} = (K i - u) / D i)
    {E : Set (Fin m → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    (∫ ω in E, count X L t ω - count X L s ω ∂Measure.pi P) =
      ∫ ω in E, ∫ u in Ioc s t,
        (∑ i ∈ L, if u < X i (ω i) then 1 / (K i - u) else 0) ∂volume ∂Measure.pi P := by
  have hEambient := (rawFiltration X hX J).le s E hE
  have hleft : ∀ ω, E.indicator (fun ω ↦ count X L t ω - count X L s ω) ω =
      ∑ i ∈ L, labelWindow X i E s t ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      unfold count
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases his : X i (ω i) ≤ s
      · have hit := his.trans hst
        simp only [his, hit, ite_true, sub_self, labelWindow, hω, true_and,
          not_lt.mpr his, false_and, ite_false]
      · have his' := lt_of_not_ge his
        by_cases hit : X i (ω i) ≤ t <;>
          simp only [his, his', hit, ite_false, ite_true, sub_zero, labelWindow,
            hω, true_and]
    · rw [Set.indicator_of_notMem hω]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp only [labelWindow, hω, false_and, ite_false]
  have hright : ∀ ω, (∑ i ∈ L, labelHazardIntegral X i E (K i) s t ω) =
      E.indicator (fun ω ↦ ∫ u in Ioc s t,
        ∑ i ∈ L, if u < X i (ω i) then 1 / (K i - u) else 0) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have hsum := integral_finsetSum L
        (fun i hi ↦ integrableOn_labelHazard X i E (s := s) (hfloor i hi) ω)
      simpa only [labelHazardIntegral, labelHazard, hω, true_and] using hsum.symm
    · rw [Set.indicator_of_notMem hω]
      apply Finset.sum_eq_zero
      intro i hi
      simp only [labelHazardIntegral, labelHazard, hω, false_and, ite_false, integral_zero]
  calc
    (∫ ω in E, count X L t ω - count X L s ω ∂Measure.pi P) =
        ∫ ω, ∑ i ∈ L, labelWindow X i E s t ω ∂Measure.pi P := by
      rw [← integral_indicator hEambient]
      exact integral_congr_ae (ae_of_all _ hleft)
    _ = ∑ i ∈ L, ∫ ω, labelWindow X i E s t ω ∂Measure.pi P :=
      integral_finsetSum L (fun i hi ↦ integrable_labelWindow P X hX i hEambient s t)
    _ = ∑ i ∈ L, ∫ ω, labelHazardIntegral X i E (K i) s t ω ∂Measure.pi P := by
      apply Finset.sum_congr rfl
      intro i hi
      exact label_rawRectangle P X hX J i hst (hfloor i hi) (hD i hi) (hsurvival i hi) hE
    _ = ∫ ω, ∑ i ∈ L, labelHazardIntegral X i E (K i) s t ω ∂Measure.pi P :=
      (integral_finsetSum L
        (fun i hi ↦ integrable_labelHazardIntegral P X hX i hEambient (hfloor i hi))).symm
    _ = ∫ ω in E, ∫ u in Ioc s t,
        (∑ i ∈ L, if u < X i (ω i) then 1 / (K i - u) else 0) ∂volume ∂Measure.pi P := by
      rw [← integral_indicator hEambient]
      exact integral_congr_ae (ae_of_all _ hright)

/-- Number of labels in a group that crossed strictly before the physical coordinate. -/
noncomputable def countBefore {ι : Type*} (X : ι → A → ℝ) (J : Finset ι)
    (t : ℝ) (ω : ι → A) : ℝ :=
  ∑ i ∈ J, if X i (ω i) < t then 1 else 0

omit [MeasurableSpace A] in
/-- Strict and non-strict survival differ at only finitely many times on every path.  Thus the
integrated one-label hazards sum to the full remaining-before population divided by area. -/
theorem integral_sum_survival_eq_remainingBefore
    (X : Fin m → A → ℝ) (J : Finset (Fin m)) (K s t : ℝ) (ω : Fin m → A) :
    (∫ u in Ioc s t, ∑ i ∈ J, if u < X i (ω i) then 1 / (K - u) else 0) =
      ∫ u in Ioc s t, ((J.card : ℝ) - countBefore X J u ω) / (K - u) := by
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ Set.range (fun i : Fin m ↦ X i (ω i)) :=
    measure_eq_zero_iff_ae_notMem.mp ((Set.finite_range _).measure_zero volume)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hae] with u hu
  calc
    (∑ i ∈ J, if u < X i (ω i) then 1 / (K - u) else 0) =
        ∑ i ∈ J, ((1 : ℝ) - if X i (ω i) < u then 1 else 0) / (K - u) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : u ≠ X i (ω i) := fun h ↦ hu ⟨i, h.symm⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [hlt, not_lt.mpr hlt.le]
      · simp [hgt, not_lt.mpr hgt.le]
    _ = ((J.card : ℝ) - countBefore X J u ω) / (K - u) := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, countBefore]

/-- When one group's affine survival intercept is common, its compensator is the full
remaining-before population divided by the common remaining area. -/
theorem count_rawRectangle_remainingBefore
    (P : Fin m → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : Fin m → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J L : Finset (Fin m)) {K D s t : ℝ} (hst : s ≤ t)
    (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ i ∈ L, ∀ u ∈ Icc s t,
      (P i).real {x | u < X i x} = (K - u) / D)
    {E : Set (Fin m → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    (∫ ω in E, count X L t ω - count X L s ω ∂Measure.pi P) =
      ∫ ω in E, ∫ u in Ioc s t,
        ((L.card : ℝ) - countBefore X L u ω) / (K - u) ∂volume ∂Measure.pi P := by
  rw [count_rawRectangle P X hX J L (fun _ ↦ K) (fun _ ↦ D) hst
    (fun _ _ ↦ hfloor) (fun _ _ ↦ hD) hsurvival hE]
  exact integral_congr_ae (ae_of_all _ fun ω ↦
    integral_sum_survival_eq_remainingBefore X L K s t ω)

/-- Frozen source phase for one marked point. -/
def sourcePhase (n : ℕ) (q : ℝ) (z : MarkedHeight) : ℝ :=
  (n : ℝ) * (z.1 : ℝ) + q * (1 - (z.2 : ℝ))

/-- Frozen target phase for one marked point. -/
def targetPhase (n : ℕ) (q : ℝ) (z : MarkedHeight) : ℝ :=
  (n : ℝ) * (z.1 : ℝ) - q * (1 + (z.2 : ℝ))

/-- A fixed partition of the unseen labels into source and target labels. -/
noncomputable def fixedPhase {ι : Type*} (n : ℕ) (q : ℝ) (J : Finset ι)
    (i : ι) : MarkedHeight → ℝ :=
  if i ∈ J then sourcePhase n q else targetPhase n q

theorem measurable_fixedPhase {ι : Type*} (n : ℕ) (q : ℝ) (J : Finset ι) :
    ∀ i, Measurable (fixedPhase n q J i) := by
  intro i
  unfold fixedPhase
  split_ifs
  · unfold sourcePhase
    fun_prop
  · unfold targetPhase
    fun_prop

/-- The actual product factors supplied by the deferred-decision law at a fixed boundary. -/
noncomputable def fixedLaw {ι : Type*} (n : ℕ) (q xR : ℝ) (J : Finset ι)
    (i : ι) : Measure MarkedHeight :=
  if i ∈ J then
    (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]
  else
    (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]

theorem remainingAreas_pos_of_unclippedRegion
    {n : ℕ} {q x : ℝ} (hx : (x, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
    0 < sourceUnclippedRemainingMass n q x ∧
      0 < targetUnclippedRemainingMass n q x := by
  rcases hx with ⟨hx, hs, ht, htt⟩
  constructor
  · unfold sourceUnclippedRemainingMass
    linarith [hx.2, hs.2]
  · unfold targetUnclippedRemainingMass
    linarith [ht.2, htt.2]

theorem fixedLaw_isProbabilityMeasure
    {ι : Type*} {n : ℕ} (hn : 0 < n) {q xR : ℝ} (J : Finset ι)
    (hR : (xR, q) ∈ FiniteSample.rightTailUnclippedRegion n) (i : ι) :
    IsProbabilityMeasure (fixedLaw n q xR J i) := by
  have hareas := remainingAreas_pos_of_unclippedRegion hR
  have hs := FiniteSample.sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have ht := FiniteSample.targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold fixedLaw
  split_ifs
  · apply cond_isProbabilityMeasure
    apply (measureReal_ne_zero_iff).mp
    rw [unitSquareUniform_sourceRawRemainingSet hn
      (fun u ↦ (hs u).1.le) (fun u ↦ (hs u).2.le)]
    exact ne_of_gt (div_pos hareas.1 hnreal)
  · apply cond_isProbabilityMeasure
    apply (measureReal_ne_zero_iff).mp
    rw [unitSquareUniform_targetRawRemainingSet hn
      (fun u ↦ (ht u).1.le) (fun u ↦ (ht u).2.le)]
    exact ne_of_gt (div_pos hareas.2 hnreal)

/-- Actual source raw-rectangle compensation under the iid marked-point law at a fixed
frozen boundary.  The past observes both aggregate source and target histories.  No
tie-free assumption is required for this integral identity. -/
theorem fixedBoundary_source_rawRectangle
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (J : Finset (Fin m))
    (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    {E : Set (Fin m → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration (fixedPhase n q J)
      (measurable_fixedPhase n q J) J s] E) :
    (∫ ω in E, count (fixedPhase n q J) J t ω - count (fixedPhase n q J) J s ω
      ∂Measure.pi (fixedLaw n q xR J)) =
      ∫ ω in E, ∫ u in Ioc s t,
        ((J.card : ℝ) - countBefore (fixedPhase n q J) J u ω) /
          sourceUnclippedRemainingMass n q u ∂volume ∂Measure.pi (fixedLaw n q xR J) := by
  have hR := hstrip xR ⟨le_rfl, hRs.trans hst⟩
  have ht := hstrip t ⟨hRs.trans hst, le_rfl⟩
  let : ∀ i, IsProbabilityMeasure (fixedLaw n q xR J i) :=
    fixedLaw_isProbabilityMeasure hn J hR
  have hK : ∀ u, (n : ℝ) + q / 2 - u = sourceUnclippedRemainingMass n q u := by
    intro u
    unfold sourceUnclippedRemainingMass
    ring
  have hfloor : 0 < (n : ℝ) + q / 2 - t := by
    rw [hK]
    exact (remainingAreas_pos_of_unclippedRegion ht).1
  have hD : sourceUnclippedRemainingMass n q xR ≠ 0 :=
    ne_of_gt (remainingAreas_pos_of_unclippedRegion hR).1
  have hsurvival : ∀ i ∈ J, ∀ u ∈ Icc s t,
      (fixedLaw n q xR J i).real {z | u < fixedPhase n q J i z} =
        ((n : ℝ) + q / 2 - u) / sourceUnclippedRemainingMass n q xR := by
    intro i hi u hu
    simp only [fixedLaw, fixedPhase, hi, ite_true, hK]
    exact rightFrozenSourceLaw_survival hn (hRs.trans hu.1) hR
      (hstrip u ⟨hRs.trans hu.1, hu.2⟩)
  have hbase := count_rawRectangle_remainingBefore (fixedLaw n q xR J)
    (fixedPhase n q J) (measurable_fixedPhase n q J) J J hst hfloor hD hsurvival hE
  simpa only [hK] using hbase

/-- Actual target raw-rectangle compensation under the same fixed-boundary product law. -/
theorem fixedBoundary_target_rawRectangle
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (J : Finset (Fin m))
    (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    {E : Set (Fin m → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration (fixedPhase n q J)
      (measurable_fixedPhase n q J) J s] E) :
    (∫ ω in E, count (fixedPhase n q J) Jᶜ t ω - count (fixedPhase n q J) Jᶜ s ω
      ∂Measure.pi (fixedLaw n q xR J)) =
      ∫ ω in E, ∫ u in Ioc s t,
        (((Jᶜ).card : ℝ) - countBefore (fixedPhase n q J) Jᶜ u ω) /
          targetUnclippedRemainingMass n q u ∂volume ∂Measure.pi (fixedLaw n q xR J) := by
  have hR := hstrip xR ⟨le_rfl, hRs.trans hst⟩
  have ht := hstrip t ⟨hRs.trans hst, le_rfl⟩
  let : ∀ i, IsProbabilityMeasure (fixedLaw n q xR J i) :=
    fixedLaw_isProbabilityMeasure hn J hR
  have hK : ∀ u, (n : ℝ) - 3 * q / 2 - u = targetUnclippedRemainingMass n q u := by
    intro u
    unfold targetUnclippedRemainingMass
    ring
  have hfloor : 0 < (n : ℝ) - 3 * q / 2 - t := by
    rw [hK]
    exact (remainingAreas_pos_of_unclippedRegion ht).2
  have hD : targetUnclippedRemainingMass n q xR ≠ 0 :=
    ne_of_gt (remainingAreas_pos_of_unclippedRegion hR).2
  have hsurvival : ∀ i ∈ Jᶜ, ∀ u ∈ Icc s t,
      (fixedLaw n q xR J i).real {z | u < fixedPhase n q J i z} =
        ((n : ℝ) - 3 * q / 2 - u) / targetUnclippedRemainingMass n q xR := by
    intro i hi u hu
    have hi' : i ∉ J := Finset.mem_compl.mp hi
    simp only [fixedLaw, fixedPhase, hi', ite_false, hK]
    exact rightFrozenTargetLaw_survival hn (hRs.trans hu.1) hR
      (hstrip u ⟨hRs.trans hu.1, hu.2⟩)
  have hbase := count_rawRectangle_remainingBefore (fixedLaw n q xR J)
    (fixedPhase n q J) (measurable_fixedPhase n q J) J Jᶜ hst hfloor hD hsurvival hE
  simpa only [hK] using hbase

end RightTail
end OTSelector
