import OTSelector.Gauge.KineticGauge
import OTSelector.Limit.FeedbackMarkDisintegration
import OTSelector.Limit.FeedbackEnvironmentIdentification
import OTSelector.PointProcess.MatchingLocalLimit

/-!
# No finite alternating ties in the actual feedback environment

The event labels are the actual retained positive jumps of the iid return cells. A moved
source mark has a finite kinetic tie fiber. The actual marked trajectory disintegration
therefore eliminates every finite label cycle, and the original quadratic gauge has exactly
the same alternating cost difference.
-/

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped BigOperators ENNReal Classical

set_option maxHeartbeats 800000

namespace OTSelector.Matching

open OTSelector.Limit OTSelector.PointProcess

private theorem label_succ_ne {p q : ℤ × ℕ} (h : p ≠ q) :
    (p.1, p.2 + 1) ≠ (q.1, q.2 + 1) := by
  intro heq
  apply h
  apply Prod.ext
  · have hfst := congrArg (fun z : ℤ × ℕ ↦ z.1) heq
    exact hfst
  · have hsnd := congrArg (fun z : ℤ × ℕ ↦ z.2) heq
    simpa using hsnd

/-- Physical arrival positions do not change in the single-mark fiber. -/
theorem feedbackCellEventPoint_fst_replaceMark (p q : ℤ × ℕ)
    (w : FeedbackCellSequence) (u : UnitMark) :
    (feedbackCellEventPoint (feedbackCellReplaceMark p.1 (p.2 + 1) w u) q).1 =
      (feedbackCellEventPoint w q).1 := by
  change feedbackCellRoot _ q.1 + feedbackCellClock _ (q.2 + 1) = _
  rw [feedbackCellRoot_cellReplaceMark]
  by_cases h : q.1 = p.1
  · simp [feedbackCellEventPoint, feedbackCellReplaceMark, h]
  · simp [feedbackCellEventPoint, feedbackCellReplaceMark, Function.update_of_ne h]

@[simp]
theorem feedbackCellEventPoint_snd_replaceMark_self (p : ℤ × ℕ)
    (w : FeedbackCellSequence) (u : UnitMark) :
    (feedbackCellEventPoint (feedbackCellReplaceMark p.1 (p.2 + 1) w u) p).2 = u :=
  feedbackCellReplaceMark_mark_self _ _ _ _

theorem feedbackCellEventPoint_snd_replaceMark_other (p q : ℤ × ℕ)
    (w : FeedbackCellSequence) (u : UnitMark) (hpq : p ≠ q) :
    (feedbackCellEventPoint (feedbackCellReplaceMark p.1 (p.2 + 1) w u) q).2 =
      (feedbackCellEventPoint w q).2 :=
  feedbackCellReplaceMark_mark_of_ne _ _ _ _ _ _ (label_succ_ne hpq)

private theorem height_lipschitz {lam : ℝ} (hlam : 0 ≤ lam) (w : FeedbackCellSequence) :
    RealLipschitz lam (feedbackConcatenatedHeight lam w) := by
  intro x y
  have h := (lipschitzWith_feedbackConcatenatedHeight lam w).dist_le_mul y x
  rw [Real.coe_toNNReal _ (abs_nonneg lam), abs_of_nonneg hlam] at h
  exact h

/-- The exact kinetic cost of two actual labeled arrivals. -/
noncomputable def feedbackLabelKineticCost (lam : ℝ) (w : FeedbackCellSequence)
    (p q : ℤ × ℕ) : ℝ :=
  kineticCost (feedbackConcatenatedHeight lam w)
    (feedbackCellEventPoint w p).1 (feedbackCellEventPoint w q).1
    (1 - ((feedbackCellEventPoint w p).2 : ℝ))
    (1 + ((feedbackCellEventPoint w q).2 : ℝ))

private theorem measurable_height_at_event (lam : ℝ) (p : ℤ × ℕ) :
    Measurable (fun w ↦ feedbackConcatenatedHeight lam w (feedbackCellEventPoint w p).1) := by
  have hm : Measurable (fun w : FeedbackCellSequence ↦
      (feedbackConcatenatedGraphHeight lam w, (feedbackCellEventPoint w p).1)) :=
    (measurable_feedbackConcatenatedGraphHeight lam).prodMk
      (measurable_feedbackCellEventPoint p).fst
  exact (show Continuous (fun z : GraphHeight × ℝ ↦ z.1 z.2) from continuous_eval).measurable.comp hm

@[fun_prop]
theorem measurable_feedbackLabelKineticCost (lam : ℝ) (p q : ℤ × ℕ) :
    Measurable (fun w ↦ feedbackLabelKineticCost lam w p q) := by
  have hp := measurable_feedbackCellEventPoint p
  have hq := measurable_feedbackCellEventPoint q
  have hgp := measurable_height_at_event lam p
  have hgq := measurable_height_at_event lam q
  unfold feedbackLabelKineticCost kineticCost
  fun_prop

private theorem source_marks_replace {m : ℕ} (s : Fin m → ℤ × ℕ)
    (hs : Injective s) (i : Fin m) (w : FeedbackCellSequence) (u : UnitMark) :
    (fun k ↦ 1 - ((feedbackCellEventPoint
      (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u) (s k)).2 : ℝ)) =
    Function.update (fun k ↦ 1 - ((feedbackCellEventPoint w (s k)).2 : ℝ)) i (1 - u) := by
  funext k
  by_cases h : k = i
  · subst k
    simp
  · rw [Function.update_of_ne h, feedbackCellEventPoint_snd_replaceMark_other]
    exact fun heq ↦ h (hs heq.symm)

private theorem target_marks_replace {m : ℕ} (s t : Fin m → ℤ × ℕ)
    (hst : ∀ i k, s i ≠ t k) (i : Fin m) (w : FeedbackCellSequence) (u : UnitMark) :
    (fun k ↦ 1 + ((feedbackCellEventPoint
      (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u) (t k)).2 : ℝ)) =
    (fun k ↦ 1 + ((feedbackCellEventPoint w (t k)).2 : ℝ)) := by
  funext k
  rw [feedbackCellEventPoint_snd_replaceMark_other _ _ _ _ (hst i k)]

/-- A guarded finite alternating tie has zero probability for the actual iid cell law. The
only guards are the nonzero pole residue and distinct target marks used by the algebra. -/
theorem feedbackCellBase_alternating_tie_null
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {m : ℕ} (s t : Fin m → ℤ × ℕ) (hs : Injective s)
    (hst : ∀ i k, s i ≠ t k) (tau : Equiv.Perm (Fin m)) (i : Fin m) :
    feedbackCellBase lam hlam0 (by linarith)
      {w | (feedbackCellEventPoint w (t i)).1 ≠ (feedbackCellEventPoint w (s i)).1 ∧
        (feedbackCellEventPoint w (t i)).2 ≠ (feedbackCellEventPoint w (t (tau i))).2 ∧
        (∑ k, feedbackLabelKineticCost lam w (s k) (t k)) =
          ∑ k, feedbackLabelKineticCost lam w (s k) (t (tau k))} = 0 := by
  let E : Set FeedbackCellSequence := {w |
    (feedbackCellEventPoint w (t i)).1 ≠ (feedbackCellEventPoint w (s i)).1 ∧
    (feedbackCellEventPoint w (t i)).2 ≠ (feedbackCellEventPoint w (t (tau i))).2 ∧
    (∑ k, feedbackLabelKineticCost lam w (s k) (t k)) =
      ∑ k, feedbackLabelKineticCost lam w (s k) (t (tau k))}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (measurable_feedbackCellEventPoint (t i)).fst
      (measurable_feedbackCellEventPoint (s i)).fst).compl.inter
    ((measurableSet_eq_fun (measurable_feedbackCellEventPoint (t i)).snd
      (measurable_feedbackCellEventPoint (t (tau i))).snd).compl.inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)))
  apply feedbackCellBase_finite_mark_fibres_null hlam0 (by linarith) (s i).1 (s i).2 hE
  intro w
  let xi := fun k ↦ (feedbackCellEventPoint w (s k)).1
  let eta := fun k ↦ (feedbackCellEventPoint w (t k)).1
  let a := fun k ↦ 1 - ((feedbackCellEventPoint w (s k)).2 : ℝ)
  let b := fun k ↦ 1 + ((feedbackCellEventPoint w (t k)).2 : ℝ)
  let F : Set UnitMark := {u | feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u ∈ E}
  by_cases hF : F.Nonempty
  · obtain ⟨v, hv⟩ := hF
    have hn : eta i ≠ xi i := by
      have h := hv.1
      simpa only [feedbackCellEventPoint_fst_replaceMark] using h
    have hmark : b i ≠ b (tau i) := by
      have h := hv.2.1
      simp only [feedbackCellEventPoint_snd_replaceMark_other _ _ _ _ (hst i _)] at h
      intro heq
      apply h
      apply Subtype.ext
      dsimp [b] at heq
      linarith
    have hb : ∀ k, 0 < b k := fun k ↦ by
      dsimp [b]
      linarith [(feedbackCellEventPoint w (t k)).2.property.1]
    have hsmall : b i * lam < 1 := by
      have hbhi : b i ≤ 2 := by
        dsimp [b]
        linarith [(feedbackCellEventPoint w (t i)).2.property.2]
      nlinarith
    have hfinite := finite_kinetic_alternating_tie_fibre (height_lipschitz hlam0.le w)
      xi eta a b tau i hb hsmall hn hmark
    have hinj : Injective (fun u : UnitMark ↦ (1 : ℝ) - u) := by
      intro u v h
      apply Subtype.ext
      linarith
    apply (hfinite.preimage hinj.injOn).subset
    intro u hu
    refine ⟨by linarith [u.property.2], ?_⟩
    have h := hu.2.2
    change (∑ k, kineticCost (feedbackConcatenatedHeight lam
      (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u))
      (feedbackCellEventPoint _ (s k)).1 (feedbackCellEventPoint _ (t k)).1
      (1 - ((feedbackCellEventPoint _ (s k)).2 : ℝ))
      (1 + ((feedbackCellEventPoint _ (t k)).2 : ℝ))) =
      ∑ k, kineticCost (feedbackConcatenatedHeight lam
        (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u))
        (feedbackCellEventPoint _ (s k)).1 (feedbackCellEventPoint _ (t (tau k))).1
        (1 - ((feedbackCellEventPoint _ (s k)).2 : ℝ))
        (1 + ((feedbackCellEventPoint _ (t (tau k))).2 : ℝ)) at h
    have hg : feedbackConcatenatedHeight lam
        (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u) =
        feedbackConcatenatedHeight lam w := funext (fun x ↦
          feedbackConcatenatedHeight_cellReplaceMark _ _ _ _ _ x)
    rw [hg] at h
    simp only [feedbackCellEventPoint_fst_replaceMark] at h
    have ha := source_marks_replace s hs i w u
    have hb' := target_marks_replace s t hst i w u
    have ha' (k : Fin m) :
        1 - ((feedbackCellEventPoint
          (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u) (s k)).2 : ℝ) =
        Function.update a i (1 - u) k := congrFun ha k
    have hb'' (k : Fin m) :
        1 + ((feedbackCellEventPoint
          (feedbackCellReplaceMark (s i).1 ((s i).2 + 1) w u) (t k)).2 : ℝ) = b k :=
      congrFun hb' k
    simp_rw [ha', hb''] at h
    exact h
  · change F.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hF]
    exact Set.finite_empty

private theorem source_target_labels_ne {w : FeedbackCellSequence} {p q : ℤ × ℕ}
    (hp : feedbackCellEventActive w 1 p) (hq : feedbackCellEventActive w (-1) q) : p ≠ q := by
  intro h
  subst q
  have h₁ := hp.2.2
  have h₂ := hq.2.2
  omega

/-- The entire countable collection of actual finite labeled cycles has no kinetic ties. -/
theorem feedbackCellBase_no_finite_kinetic_ties
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith),
      ∀ (m : ℕ) (s t : Fin m → ℤ × ℕ) (tau : Equiv.Perm (Fin m)),
      Injective s → Injective t → (∀ i, feedbackCellEventActive w 1 (s i)) →
      (∀ i, feedbackCellEventActive w (-1) (t i)) → tau ≠ Equiv.refl _ →
      (∑ i, feedbackLabelKineticCost lam w (s i) (t i)) ≠
        ∑ i, feedbackLabelKineticCost lam w (s i) (t (tau i)) := by
  have hfixed (m : ℕ) (s t : Fin m → ℤ × ℕ) (tau : Equiv.Perm (Fin m)) :
      ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith),
      Injective s → Injective t → (∀ i, feedbackCellEventActive w 1 (s i)) →
      (∀ i, feedbackCellEventActive w (-1) (t i)) → tau ≠ Equiv.refl _ →
      (∑ i, feedbackLabelKineticCost lam w (s i) (t i)) ≠
        ∑ i, feedbackLabelKineticCost lam w (s i) (t (tau i)) := by
    by_cases hs : Injective s
    swap
    · exact ae_of_all _ (fun _ h ↦ (hs h).elim)
    by_cases ht : Injective t
    swap
    · exact ae_of_all _ (fun _ _ h ↦ (ht h).elim)
    by_cases htau : tau = Equiv.refl _
    · exact ae_of_all _ (fun _ _ _ _ _ h ↦ (h htau).elim)
    by_cases hst : ∀ i k, s i ≠ t k
    swap
    · push Not at hst
      obtain ⟨i, k, hik⟩ := hst
      exact ae_of_all _ (fun _ _ _ hsa hta ↦
        (source_target_labels_ne (hsa i) (hta k) hik).elim)
    have hmoved : ∃ i, tau i ≠ i := by
      by_contra h
      push Not at h
      exact htau (Equiv.ext h)
    obtain ⟨i, hi⟩ := hmoved
    have hn := measure_eq_zero_iff_ae_notMem.mp
      (feedbackCellBase_alternating_tie_null hlam0 hlam s t hs hst tau i)
    filter_upwards [hn, feedbackCellBase_marks_injective hlam0 (by linarith)] with w hw hmarks
    intro _ _ hsa hta _ heq
    apply hw
    refine ⟨?_, ?_, heq⟩
    · intro hcoord
      exact hst i i (feedbackCellEventPoint_fst_injective (hsa i).1
        (hsa i).2.1 (hta i).2.1 hcoord.symm)
    · intro heqmark
      have hlabels := hmarks heqmark
      exact hi (ht hlabels.symm)
  simpa only [ae_all_iff] using hfixed

/-- The original quadratic gauge has the same strict finite comparisons as the kinetic cost. -/
theorem feedbackCellBase_no_finite_quadratic_ties
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith),
      ∀ (m : ℕ) (s t : Fin m → ℤ × ℕ) (tau : Equiv.Perm (Fin m)),
      Injective s → Injective t → (∀ i, feedbackCellEventActive w 1 (s i)) →
      (∀ i, feedbackCellEventActive w (-1) (t i)) → tau ≠ Equiv.refl _ →
      (∑ i, markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (s i)) (feedbackCellEventPoint w (t i))) ≠
        ∑ i, markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
          (feedbackCellEventPoint w (s i)) (feedbackCellEventPoint w (t (tau i))) := by
  filter_upwards [feedbackCellBase_no_finite_kinetic_ties hlam0 hlam] with w hw
  intro m s t tau hs ht hsa hta htau heq
  apply hw m s t tau hs ht hsa hta htau
  have hD (i j : Fin m) :
      (1 - ((feedbackCellEventPoint w (s i)).2 : ℝ)) +
        (1 + ((feedbackCellEventPoint w (t j)).2 : ℝ)) ≠ 0 := by
    linarith [(feedbackCellEventPoint w (s i)).2.property.2,
      (feedbackCellEventPoint w (t j)).2.property.1]
  have hdiff := sum_quadraticCost_sub_eq_sum_kineticCost_sub
    (feedbackConcatenatedGraphHeight lam w).continuous
    (fun i ↦ (feedbackCellEventPoint w (s i)).1)
    (fun i ↦ (feedbackCellEventPoint w (t i)).1)
    (fun i ↦ 1 - ((feedbackCellEventPoint w (s i)).2 : ℝ))
    (fun i ↦ 1 + ((feedbackCellEventPoint w (t i)).2 : ℝ)) tau hD
  change (∑ i, markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
    (feedbackCellEventPoint w (s i)) (feedbackCellEventPoint w (t i))) -
      (∑ i, markedQuadraticCost (feedbackConcatenatedGraphHeight lam w)
        (feedbackCellEventPoint w (s i)) (feedbackCellEventPoint w (t (tau i)))) =
    (∑ i, feedbackLabelKineticCost lam w (s i) (t i)) -
      (∑ i, feedbackLabelKineticCost lam w (s i) (t (tau i))) at hdiff
  rw [heq, sub_self] at hdiff
  exact sub_eq_zero.mp hdiff.symm

/-- Every atom of the actual cell configuration comes from a retained actual jump label. -/
theorem feedbackConcatenatedPoints_atom_iff (w : FeedbackCellSequence) (direction : ℤ)
    (p : MatchingPoint) :
    LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w) {p} ≠ 0 ↔
      ∃ i : ℤ × ℕ, feedbackCellEventActive w direction i ∧ feedbackCellEventPoint w i = p := by
  rw [countingMeasure_feedbackConcatenatedPoints, Measure.sum_apply _ (measurableSet_singleton p),
    ne_eq, ENNReal.tsum_eq_zero]
  simp only [not_forall]
  apply exists_congr
  intro i
  by_cases hi : feedbackCellEventActive w direction i
  · simp [hi, Measure.dirac_apply', Pi.single_apply, eq_comm]
  · simp [hi]

/-- No finite alternating cost ties for the actual points of an environment. Membership uses
its genuine integer counting measures; the cost is the original quadratic feedback gauge. -/
def FeedbackNoFiniteTies (e : FeedbackEnvironment) : Prop :=
  ∀ (m : ℕ) (s t : Fin m → MatchingPoint) (tau : Equiv.Perm (Fin m)),
    Injective s → Injective t →
    (∀ i, LocalConfiguration.countingMeasure e.source {s i} ≠ 0) →
    (∀ i, LocalConfiguration.countingMeasure e.target {t i} ≠ 0) →
    tau ≠ Equiv.refl _ →
    (∑ i, markedQuadraticCost e.path.graphHeight (s i) (t i)) ≠
      ∑ i, markedQuadraticCost e.path.graphHeight (s i) (t (tau i))

/-- Actual retained labels exhaust all finite point families in the concatenated environment. -/
theorem feedbackCellBase_no_finite_ties
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith),
      FeedbackNoFiniteTies (feedbackConcatenatedEnvironment lam w) := by
  filter_upwards [feedbackCellBase_no_finite_quadratic_ties hlam0 hlam] with w hw
  intro m s t tau hs ht hsa hta htau heq
  have hsl (i : Fin m) := (feedbackConcatenatedPoints_atom_iff w 1 (s i)).mp (hsa i)
  have htl (i : Fin m) := (feedbackConcatenatedPoints_atom_iff w (-1) (t i)).mp (hta i)
  choose S hS hSp using hsl
  choose T hT hTp using htl
  have hSi : Injective S := by
    intro i j h
    apply hs
    rw [← hSp i, ← hSp j, h]
  have hTi : Injective T := by
    intro i j h
    apply ht
    rw [← hTp i, ← hTp j, h]
  apply hw m S T tau hSi hTi hS hT htau
  simp only [hSp, hTp]
  exact heq

/-- The quadratic gauge is invariant under the actual horizontal reroot and height normalization. -/
theorem quadraticCost_reroot {g : ℝ → ℝ} (hg : Continuous g)
    (r xi eta a b : ℝ) (hD : a + b ≠ 0) :
    quadraticCost (fun x ↦ g (x + r) - g r) (xi - r) (eta - r) a b =
      quadraticCost g xi eta a b := by
  have hI : (∫ x in xi - r..eta - r, g (x + r) - g r) =
      (∫ x in xi..eta, g x) - (eta - xi) * g r := by
    have hgi : IntervalIntegrable (fun x ↦ g (x + r)) volume (xi - r) (eta - r) :=
      (show Continuous (fun x ↦ g (x + r)) from hg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hgi intervalIntegrable_const,
      intervalIntegral.integral_comp_add_right]
    simp only [sub_add_cancel, intervalIntegral.integral_const, smul_eq_mul]
    ring
  unfold quadraticCost gaugedFourPointCost fourPointQuotient fourPointGap
    fourPointDenominator fourPointSourceValue fourPointTargetValue
  simp only [sub_add_cancel, id_eq]
  rw [hI]
  field_simp
  ring

/-- Actual rerooting transports a point atom exactly to its old physical location. -/
theorem feedbackEnvironment_reroot_atom (c : LocalConfiguration matchingPointBase)
    (r : ℝ) (p : MatchingPoint) :
    LocalConfiguration.countingMeasure (LocalConfiguration.reroot r c) {p} =
      LocalConfiguration.countingMeasure c {(p.1 + r, p.2)} := by
  simp [LocalConfiguration.reroot, LocalConfiguration.multiplicity_translate]

/-- A pathwise no-tie environment retains the property at every real cut simultaneously. -/
theorem FeedbackNoFiniteTies.reroot {e : FeedbackEnvironment}
    (he : FeedbackNoFiniteTies e) (r : ℝ) : FeedbackNoFiniteTies (r +ᵥ e) := by
  intro m s t tau hs ht hsa hta htau heq
  let S : Fin m → MatchingPoint := fun i ↦ ((s i).1 + r, (s i).2)
  let T : Fin m → MatchingPoint := fun i ↦ ((t i).1 + r, (t i).2)
  have hSi : Injective S := by
    intro i j hij
    apply hs
    apply Prod.ext
    · have h := congrArg (fun p : MatchingPoint ↦ p.1) hij
      dsimp [S] at h
      linarith
    · have h := congrArg (fun p : MatchingPoint ↦ p.2) hij
      exact h
  have hTi : Injective T := by
    intro i j hij
    apply ht
    apply Prod.ext
    · have h := congrArg (fun p : MatchingPoint ↦ p.1) hij
      dsimp [T] at h
      linarith
    · have h := congrArg (fun p : MatchingPoint ↦ p.2) hij
      exact h
  have hSa (i : Fin m) : LocalConfiguration.countingMeasure e.source {S i} ≠ 0 := by
    have h := hsa i
    change LocalConfiguration.countingMeasure (LocalConfiguration.reroot r e.source) {s i} ≠ 0 at h
    rwa [feedbackEnvironment_reroot_atom] at h
  have hTa (i : Fin m) : LocalConfiguration.countingMeasure e.target {T i} ≠ 0 := by
    have h := hta i
    change LocalConfiguration.countingMeasure (LocalConfiguration.reroot r e.target) {t i} ≠ 0 at h
    rwa [feedbackEnvironment_reroot_atom] at h
  apply he m S T tau hSi hTi hSa hTa htau
  have hcost (i j : Fin m) :
      markedQuadraticCost (r +ᵥ e).path.graphHeight (s i) (t j) =
        markedQuadraticCost e.path.graphHeight (S i) (T j) := by
    have hD : (1 - ((s i).2 : ℝ)) + (1 + ((t j).2 : ℝ)) ≠ 0 := by
      linarith [(s i).2.property.2, (t j).2.property.1]
    have h := quadraticCost_reroot e.path.graphHeight.continuous r
      ((s i).1 + r) ((t j).1 + r) (1 - ((s i).2 : ℝ)) (1 + ((t j).2 : ℝ)) hD
    simp only [add_sub_cancel_right] at h
    exact h
  simpa only [hcost] using heq

/-- All cuts of an actual iid-cell sample have the no-tie property on one common full set. -/
theorem feedbackCellBase_no_finite_ties_all_reroots
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 (by linarith), ∀ r : ℝ,
      FeedbackNoFiniteTies (r +ᵥ feedbackConcatenatedEnvironment lam w) :=
  (feedbackCellBase_no_finite_ties hlam0 hlam).mono (fun _ hw r ↦ hw.reroot r)

end OTSelector.Matching
