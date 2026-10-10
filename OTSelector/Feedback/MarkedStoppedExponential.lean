import OTSelector.Feedback.MarkedStoppedOccupation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponentially weighted Dynkin formula through a stopping mask

The fixed-horizon integrating factor is applied to the clipped observable stopped at a
right-closed predictable coordinate.  The resulting estimate controls the terminal alive moment
without constructing a cemetery state.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem integral_exp_mul_const_timeMeasure
    (a c : ℝ) {u v : ℝ≥0} (huv : u ≤ v) :
    (∫ s in Ioc u v, a * Real.exp (a * (s : ℝ)) * c ∂timeMeasure) =
      Real.exp (a * (v : ℝ)) * c - Real.exp (a * (u : ℝ)) * c := by
  rw [integral_timeMeasure_eq_intervalIntegral
    (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) * c) u v huv]
  have hcongr :
      (∫ x in (u : ℝ)..(v : ℝ),
          a * Real.exp (a * (Real.toNNReal x : ℝ)) * c) =
        ∫ x in (u : ℝ)..(v : ℝ), a * Real.exp (a * x) * c := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by exact_mod_cast huv)] at hx
    have hx0 : 0 ≤ x := le_trans (by exact_mod_cast u.2) hx.1
    have hcoe : (Real.toNNReal x : ℝ) = x := Real.coe_toNNReal x hx0
    simp only [hcoe]
  rw [hcongr]
  let F : ℝ → ℝ := fun x ↦ Real.exp (a * x) * c
  let F' : ℝ → ℝ := fun x ↦ a * Real.exp (a * x) * c
  have hderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ ↦ a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (a * y))
        (Real.exp (a * x) * a) x :=
      (Real.hasDerivAt_exp (a * x)).comp x hinner
    simpa only [F, F', mul_comm, mul_left_comm, mul_assoc] using hexp.mul_const c
  have hcont : Continuous F' := by
    dsimp only [F']
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x) (hcont.intervalIntegrable (u : ℝ) (v : ℝ))

omit [MeasurableSpace Ω] in
private theorem integrableOn_exp_mul_const_timeMeasure
    (a c : ℝ) {u v : ℝ≥0} :
    IntegrableOn (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) * c)
      (Ioc u v) timeMeasure := by
  have hzero : IntegrableOn (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) * c)
      (Ioc 0 v) timeMeasure := by
    rw [integrableOn_timeMeasure_iff_intervalIntegrable]
    exact (show Continuous (fun x : ℝ ↦
      a * Real.exp (a * (Real.toNNReal x : ℝ)) * c) by fun_prop).intervalIntegrable
        (0 : ℝ) (v : ℝ) (μ := volume)
  exact hzero.mono_set (fun s hs ↦ ⟨lt_of_le_of_lt u.2 hs.1, hs.2⟩)

omit [MeasurableSpace Ω] in
private noncomputable def finiteJumpStateBefore {E : Type*}
    (events : Finset E) (time : E → ℝ≥0) (step : E → ℤ)
    (k0 : ℤ) (s : ℝ≥0) : ℤ := by
  classical
  exact k0 + ∑ e ∈ events.filter (fun e ↦ time e < s), step e

omit [MeasurableSpace Ω] in
/-- Deterministic integrating-factor identity for finitely many ordered integer jumps. -/
private theorem exp_mul_finiteJumpState_eq
    {E : Type*} [LinearOrder E]
    (events : Finset E) (time : E → ℝ≥0) (step : E → ℤ)
    (f : ℤ → ℝ) (a : ℝ) (u v : ℝ≥0) (k0 : ℤ)
    (huv : u ≤ v)
    (htime : ∀ e ∈ events, u < time e ∧ time e ≤ v)
    (horder : ∀ e ∈ events, ∀ x ∈ events, e < x ↔ time e < time x) :
    IntegrableOn
        (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) *
          f (finiteJumpStateBefore events time step k0 s))
        (Ioc u v) timeMeasure ∧
      Real.exp (a * (v : ℝ)) * f (k0 + ∑ e ∈ events, step e) -
          Real.exp (a * (u : ℝ)) * f k0 =
        ∑ e ∈ events,
            Real.exp (a * (time e : ℝ)) *
              (f (finiteJumpStateBefore events time step k0 (time e) + step e) -
                f (finiteJumpStateBefore events time step k0 (time e))) +
          ∫ s in Ioc u v,
            a * Real.exp (a * (s : ℝ)) *
              f (finiteJumpStateBefore events time step k0 s) ∂timeMeasure := by
  classical
  induction events using Finset.induction_on_min generalizing u k0 with
  | empty =>
      constructor
      · simpa only [Finset.filter_empty, Finset.sum_empty, add_zero,
          finiteJumpStateBefore] using integrableOn_exp_mul_const_timeMeasure a (f k0)
      · simp only [Finset.sum_empty, add_zero, Finset.filter_empty, finiteJumpStateBefore]
        rw [integral_exp_mul_const_timeMeasure a (f k0) huv]
        ring
  | @insert e events he_min ih =>
      have he_not_mem : e ∉ events := by
        intro he
        exact (lt_irrefl e) (he_min e he)
      have heBounds : u < time e ∧ time e ≤ v :=
        htime e (Finset.mem_insert_self e events)
      have htimeTail : ∀ x ∈ events, time e < time x ∧ time x ≤ v := by
        intro x hx
        have hex : e < x := he_min x hx
        exact ⟨(horder e (Finset.mem_insert_self e events) x
          (Finset.mem_insert_of_mem hx)).mp hex,
          (htime x (Finset.mem_insert_of_mem hx)).2⟩
      have horderTail : ∀ x ∈ events, ∀ y ∈ events,
          x < y ↔ time x < time y := by
        intro x hx y hy
        exact horder x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
      have hIH := ih (time e) (k0 + step e) heBounds.2 htimeTail horderTail
      have hstateAtFirst :
          finiteJumpStateBefore (insert e events) time step k0 (time e) = k0 := by
        unfold finiteJumpStateBefore
        have hfilter : (insert e events).filter (fun x ↦ time x < time e) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact lt_irrefl _
          · have hetx : time e < time x := (horder e
              (Finset.mem_insert_self e events) x (Finset.mem_insert_of_mem hx)).mp
                (he_min x hx)
            exact not_lt_of_ge hetx.le
        rw [hfilter]
        simp
      have hstateTail : ∀ x ∈ events,
          finiteJumpStateBefore (insert e events) time step k0 (time x) =
            finiteJumpStateBefore events time step (k0 + step e) (time x) := by
        intro x hx
        have hetx : time e < time x := (htimeTail x hx).1
        unfold finiteJumpStateBefore
        have hfilterInsert :
            (insert e events).filter (fun y ↦ time y < time x) =
              insert e (events.filter (fun y ↦ time y < time x)) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hyt⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hy, hyt⟩
          · rintro (rfl | ⟨hy, hyt⟩)
            · exact ⟨Or.inl rfl, hetx⟩
            · exact ⟨Or.inr hy, hyt⟩
        rw [hfilterInsert, Finset.sum_insert]
        · ring
        · exact fun hefilter ↦ he_not_mem (Finset.mem_filter.mp hefilter).1
      have hstateEarly : ∀ s ∈ Ioc u (time e),
          finiteJumpStateBefore (insert e events) time step k0 s = k0 := by
        intro s hs
        unfold finiteJumpStateBefore
        have hfilter : (insert e events).filter (fun x ↦ time x < s) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact not_lt_of_ge hs.2
          · have hetx : time e < time x := (htimeTail x hx).1
            exact not_lt_of_ge (hs.2.trans hetx.le)
        rw [hfilter]
        simp
      have hstateLate : ∀ s ∈ Ioc (time e) v,
          finiteJumpStateBefore (insert e events) time step k0 s =
            finiteJumpStateBefore events time step (k0 + step e) s := by
        intro s hs
        unfold finiteJumpStateBefore
        have hfilterInsert :
            (insert e events).filter (fun y ↦ time y < s) =
              insert e (events.filter (fun y ↦ time y < s)) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hys⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hy, hys⟩
          · rintro (rfl | ⟨hy, hys⟩)
            · exact ⟨Or.inl rfl, hs.1⟩
            · exact ⟨Or.inr hy, hys⟩
        rw [hfilterInsert, Finset.sum_insert]
        · ring
        · exact fun hefilter ↦ he_not_mem (Finset.mem_filter.mp hefilter).1
      have hEarlyIntegrable : IntegrableOn
          (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore (insert e events) time step k0 s))
          (Ioc u (time e)) timeMeasure := by
        refine (integrableOn_exp_mul_const_timeMeasure a (f k0)).congr_fun ?_
          measurableSet_Ioc
        intro s hs
        change a * Real.exp (a * (s : ℝ)) * f k0 =
          a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore (insert e events) time step k0 s)
        rw [hstateEarly s hs]
      have hLateIntegrable : IntegrableOn
          (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore (insert e events) time step k0 s))
          (Ioc (time e) v) timeMeasure := by
        refine hIH.1.congr_fun ?_ measurableSet_Ioc
        intro s hs
        change a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore events time step (k0 + step e) s) =
          a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore (insert e events) time step k0 s)
        rw [hstateLate s hs]
      have hAllIntegrable : IntegrableOn
          (fun s : ℝ≥0 ↦ a * Real.exp (a * (s : ℝ)) *
            f (finiteJumpStateBefore (insert e events) time step k0 s))
          (Ioc u v) timeMeasure := by
        rw [← Ioc_union_Ioc_eq_Ioc heBounds.1.le heBounds.2]
        exact hEarlyIntegrable.union hLateIntegrable
      have hIntegralSplit :
          (∫ s in Ioc u v,
              a * Real.exp (a * (s : ℝ)) *
                f (finiteJumpStateBefore (insert e events) time step k0 s) ∂timeMeasure) =
            (∫ s in Ioc u (time e),
              a * Real.exp (a * (s : ℝ)) * f k0 ∂timeMeasure) +
              ∫ s in Ioc (time e) v,
                a * Real.exp (a * (s : ℝ)) *
                  f (finiteJumpStateBefore events time step (k0 + step e) s)
                    ∂timeMeasure := by
        rw [← Ioc_union_Ioc_eq_Ioc heBounds.1.le heBounds.2,
          setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
            hEarlyIntegrable hLateIntegrable]
        congr 1
        · apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          change a * Real.exp (a * (s : ℝ)) *
              f (finiteJumpStateBefore (insert e events) time step k0 s) =
            a * Real.exp (a * (s : ℝ)) * f k0
          rw [hstateEarly s hs]
        · apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          change a * Real.exp (a * (s : ℝ)) *
              f (finiteJumpStateBefore (insert e events) time step k0 s) =
            a * Real.exp (a * (s : ℝ)) *
              f (finiteJumpStateBefore events time step (k0 + step e) s)
          rw [hstateLate s hs]
      have hInitialIntegral := integral_exp_mul_const_timeMeasure
        a (f k0) heBounds.1.le
      rw [Finset.sum_insert he_not_mem]
      rw [Finset.sum_insert he_not_mem]
      rw [hstateAtFirst]
      have hsumTail :
          (∑ x ∈ events,
              Real.exp (a * (time x : ℝ)) *
                (f (finiteJumpStateBefore (insert e events) time step k0 (time x) + step x) -
                  f (finiteJumpStateBefore (insert e events) time step k0 (time x)))) =
            ∑ x ∈ events,
              Real.exp (a * (time x : ℝ)) *
                (f (finiteJumpStateBefore events time step (k0 + step e) (time x) + step x) -
                  f (finiteJumpStateBefore events time step (k0 + step e) (time x))) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hstateTail x hx]
      rw [hsumTail, hIntegralSplit, hInitialIntegral]
      constructor
      · exact hAllIntegrable
      · simp only [add_assoc] at hIH ⊢
        linarith [hIH.2]

omit [MeasurableSpace Ω] in
private noncomputable def exponentialCutTime
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (T : WithTop ℝ≥0) (τ ω)).untopA

omit [MeasurableSpace Ω] in
private theorem coe_exponentialCutTime
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (exponentialCutTime T τ ω : WithTop ℝ≥0) =
      min (T : WithTop ℝ≥0) (τ ω) := by
  unfold exponentialCutTime
  have hne : min (T : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top T)).ne
  rw [WithTop.untopA_eq_untop hne]
  exact WithTop.coe_untop _ hne

omit [MeasurableSpace Ω] in
private theorem exponentialCutTime_le
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    exponentialCutTime T τ ω ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [coe_exponentialCutTime]
  exact min_le_left _ _

omit [MeasurableSpace Ω] in
private theorem integral_mul_throughStopMask_eq_cut
    (τ : Ω → WithTop ℝ≥0) (g : ℝ≥0 → ℝ) (T : ℝ≥0) (ω : Ω) :
    (∫ s in Ioc (0 : ℝ≥0) T, throughStopMask τ s ω * g s ∂timeMeasure) =
      ∫ s in Ioc (0 : ℝ≥0) (exponentialCutTime T τ ω), g s ∂timeMeasure := by
  let u := exponentialCutTime T τ ω
  have huT : u ≤ T := exponentialCutTime_le T τ ω
  calc
    (∫ s in Ioc (0 : ℝ≥0) T, throughStopMask τ s ω * g s ∂timeMeasure) =
        ∫ s in Ioc (0 : ℝ≥0) T, (Ioc (0 : ℝ≥0) u).indicator g s ∂timeMeasure := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          have hsT : (s : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) :=
            WithTop.coe_le_coe.mpr hs.2
          by_cases hsτ : (s : WithTop ℝ≥0) ≤ τ ω
          · have hsuTop : (s : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) := by
              rw [show (u : WithTop ℝ≥0) =
                min (T : WithTop ℝ≥0) (τ ω) by exact coe_exponentialCutTime T τ ω]
              exact le_min hsT hsτ
            have hsu : s ≤ u := WithTop.coe_le_coe.mp hsuTop
            have hsmem : s ∈ Ioc (0 : ℝ≥0) u := ⟨hs.1, hsu⟩
            simp only [throughStopMask, ite_eq_left hsτ, one_mul]
            rw [Set.indicator_of_mem hsmem]
          · have hsnu : ¬s ≤ u := by
              intro hsu
              apply hsτ
              have hsuTop : (s : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) :=
                WithTop.coe_le_coe.mpr hsu
              rw [coe_exponentialCutTime] at hsuTop
              exact hsuTop.trans (min_le_right _ _)
            simp only [throughStopMask, ite_eq_right hsτ, zero_mul]
            rw [Set.indicator_of_notMem]
            exact fun hsMem ↦ hsnu hsMem.2
    _ = ∫ s in Ioc (0 : ℝ≥0) T ∩ Ioc (0 : ℝ≥0) u, g s ∂timeMeasure :=
      setIntegral_indicator measurableSet_Ioc
    _ = ∫ s in Ioc (0 : ℝ≥0) u, g s ∂timeMeasure := by
      rw [inter_eq_right.mpr]
      intro s hs
      exact ⟨hs.1, hs.2.trans huT⟩

omit [MeasurableSpace Ω] in
private theorem sum_markedEventStep_before_time_eq
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T s : ℝ≥0} {ω : Ω}
    (hplusMono : Monotone fun t ↦ Nplus t ω)
    (hplusRC : ∀ t, ContinuousWithinAt (fun u ↦ (Nplus u ω : ℝ)) (Ici t) t)
    (hplusInj : Set.InjOn (fun i ↦ jumpTime Nplus i ω) (Iio (Nplus T ω)))
    (hminusMono : Monotone fun t ↦ Nminus t ω)
    (hminusRC : ∀ t, ContinuousWithinAt (fun u ↦ (Nminus u ω : ℝ)) (Ici t) t)
    (hminusInj : Set.InjOn (fun j ↦ jumpTime Nminus j ω) (Iio (Nminus T ω)))
    (hsT : s ≤ T) :
    (∑ e ∈ (markedEventSet Nplus Nminus T ω).filter
        (fun e ↦ markedEventTime Nplus Nminus ω e < s), markedEventStep e) =
      (countBefore Nplus s ω : ℤ) - (countBefore Nminus s ω : ℤ) := by
  classical
  let S := (markedEventSet Nplus Nminus T ω).filter
    (fun e ↦ markedEventTime Nplus Nminus ω e < s)
  have hleft : S.toLeft = (Finset.range (Nplus T ω)).filter
      (fun i ↦ jumpTime Nplus i ω < s) := by
    ext i
    rw [Finset.mem_toLeft]
    constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiS, hit⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inl_mem_disjSum.mp hiS
      · exact hit
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiR, hit⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inl_mem_disjSum.mpr hiR
      · exact hit
  have hright : S.toRight = (Finset.range (Nminus T ω)).filter
      (fun j ↦ jumpTime Nminus j ω < s) := by
    ext j
    rw [Finset.mem_toRight]
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjS, hjt⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inr_mem_disjSum.mp hjS
      · exact hjt
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjR, hjt⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inr_mem_disjSum.mpr hjR
      · exact hjt
  have hplusFilter := filter_jumpTime_lt_eq_range_countBefore
    hplusMono hplusRC hplusInj hsT
  have hminusFilter := filter_jumpTime_lt_eq_range_countBefore
    hminusMono hminusRC hminusInj hsT
  have hsumLeft : (∑ i ∈ S.toLeft, markedEventStep (Sum.inl i)) =
      (S.toLeft.card : ℤ) := by
    simp [markedEventStep]
  have hsumRight : (∑ j ∈ S.toRight, markedEventStep (Sum.inr j)) =
      -(S.toRight.card : ℤ) := by
    simp [markedEventStep]
  change (∑ e ∈ S, markedEventStep e) = _
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hsumLeft, hsumRight,
    hleft, hright, hplusFilter, hminusFilter]
  simp only [Finset.card_range]
  ring

omit [MeasurableSpace Ω] in
private theorem markedEventTime_pos
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {T : ℝ≥0} {ω : Ω} {e : ℕ ⊕ ℕ}
    (he : e ∈ markedEventSet Nplus Nminus T ω) :
    0 < markedEventTime Nplus Nminus ω e := by
  rw [mem_markedEventSet_iff] at he
  rcases he with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · change 0 < jumpTime Nplus i ω
    apply (jumpTime_lt_iff (hplus.monotone ω) (hplus.rightContinuous ω) ⟨T, hi⟩).mpr
    simp [hplus.zero]
  · change 0 < jumpTime Nminus j ω
    apply (jumpTime_lt_iff (hminus.monotone ω) (hminus.rightContinuous ω) ⟨T, hj⟩).mpr
    simp [hminus.zero]

/-- A deterministic exponential integrating factor, frozen after a fixed horizon so that it is
globally bounded and is therefore a legal predictable counting transform. -/
noncomputable def fixedHorizonExponentialWeight
    (a : ℝ) (T s : ℝ≥0) : ℝ :=
  Real.exp (a * (min s T : ℝ≥0))

omit [MeasurableSpace Ω] in
@[simp]
theorem fixedHorizonExponentialWeight_zero (a : ℝ) (T : ℝ≥0) :
    fixedHorizonExponentialWeight a T 0 = 1 := by
  simp [fixedHorizonExponentialWeight]

omit [MeasurableSpace Ω] in
theorem fixedHorizonExponentialWeight_eq_exp
    (a : ℝ) {T s : ℝ≥0} (hsT : s ≤ T) :
    fixedHorizonExponentialWeight a T s = Real.exp (a * (s : ℝ)) := by
  rw [fixedHorizonExponentialWeight, min_eq_left hsT]

/-- The frozen fixed-horizon exponential factor is bounded predictable. -/
theorem fixedHorizonExponentialWeight_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) :
    IsBoundedPredictable ℱ
      (fun s (_ω : Ω) ↦ fixedHorizonExponentialWeight a T s) := by
  refine ⟨MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ ?_),
      Real.exp (a * (T : ℝ)), Real.exp_pos _ |>.le, ?_⟩
  · unfold fixedHorizonExponentialWeight
    fun_prop
  · intro s ω
    change |Real.exp (a * (min s T : ℝ≥0))| ≤ Real.exp (a * (T : ℝ))
    rw [Real.abs_exp]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right s T) ha

omit [MeasurableSpace Ω] in
private theorem constant_boundedPredictable
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} (c : ℝ) :
    IsBoundedPredictable ℱ (fun _s (_ω : Ω) ↦ c) := by
  refine ⟨MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const),
      |c|, abs_nonneg c, ?_⟩
  intro s ω
  exact le_rfl

/-- Finite absolute bound for values of `f` retained by the integer cutoff. -/
noncomputable def clippedValueAbsBound (R : ℕ) (f : ℤ → ℝ) : ℝ :=
  (cutoffStates R).sup' (cutoffStates_nonempty R) (fun k ↦ |f k|)

omit [MeasurableSpace Ω] in
theorem clippedValueAbsBound_nonneg (R : ℕ) (f : ℤ → ℝ) :
    0 ≤ clippedValueAbsBound R f := by
  exact (abs_nonneg (f (integerClip R 0))).trans
    (Finset.le_sup' (fun k : ℤ ↦ |f k|) (integerClip_mem_cutoffStates R 0))

omit [MeasurableSpace Ω] in
theorem abs_apply_integerClip_le_clippedValueAbsBound
    (R : ℕ) (f : ℤ → ℝ) (k : ℤ) :
    |f (integerClip R k)| ≤ clippedValueAbsBound R f := by
  exact Finset.le_sup' (fun j : ℤ ↦ |f j|) (integerClip_mem_cutoffStates R k)

/-- A clipped value of the strict-left current is bounded predictable. -/
theorem clippedLeftValue_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ
      (fun s ω ↦ f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))) := by
  exact ⟨leftCurrentOfCounts_comp_predictable hplus hminus hK0
      (fun k ↦ f (integerClip R k)),
    clippedValueAbsBound R f, clippedValueAbsBound_nonneg R f,
    fun s ω ↦ abs_apply_integerClip_le_clippedValueAbsBound R f
      (leftCurrentOfCounts K0 Nplus Nminus s ω)⟩

/-- At time zero, clipping makes every real-valued observable integrable under a finite measure.
The initial current only needs to be measurable at time zero. -/
theorem clippedObservable_zero_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ) :
    Integrable (clippedObservable R f K0 Nplus Nminus 0) μ := by
  have hK : StronglyMeasurable (fun ω ↦ (K0 ω : ℝ)) :=
    hK0.mono (ℱ.le 0)
  have hgInt : Measurable (fun k : ℤ ↦ f (integerClip R k)) :=
    measurable_of_countable _
  have hg : Measurable (fun x : ℝ ↦ f (integerClip R (Int.floor x))) :=
    hgInt.comp Int.measurable_floor
  have hObs : StronglyMeasurable (clippedObservable R f K0 Nplus Nminus 0) := by
    have hcomp := (hg.comp hK.measurable).stronglyMeasurable
    convert hcomp using 1
    funext ω
    rw [clippedObservable_zero hplus hminus]
    simp
  refine Integrable.of_bound hObs.aestronglyMeasurable (clippedValueAbsBound R f) ?_
  exact ae_of_all _ fun ω ↦ by
    rw [clippedObservable_zero hplus hminus, Real.norm_eq_abs]
    exact abs_apply_integerClip_le_clippedValueAbsBound R f (K0 ω)

/-- A bounded predictable process is pathwise integrable on every bounded time interval. -/
theorem IsBoundedPredictable.integrableOn_timeMeasure
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedPredictable ℱ H) (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun s ↦ H s ω) (Ioc (0 : ℝ≥0) T) timeMeasure := by
  obtain ⟨hpred, C, hC, hbound⟩ := hH
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace] (Function.uncurry H) :=
    hpred.mono (predictable_le_ambient ℱ)
  have hsection : StronglyMeasurable (fun s ↦ H s ω) :=
    hambient.comp_measurable (measurable_id.prodMk measurable_const)
  apply Measure.integrableOn_of_bounded (timeMeasure_Ioc_lt_top 0 T).ne
    hsection.aestronglyMeasurable (M := C)
  exact ae_of_all _ fun s ↦ by simpa [Real.norm_eq_abs] using hbound s ω

/-- On a finite sample measure, the bounded-time integral of a bounded predictable process is an
integrable random variable. -/
theorem IsBoundedPredictable.setIntegral_timeMeasure_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedPredictable ℱ H) (T : ℝ≥0) :
    Integrable (fun ω ↦ ∫ s in Ioc (0 : ℝ≥0) T, H s ω ∂timeMeasure) μ := by
  obtain ⟨hpred, C, hC, hbound⟩ := hH
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace] (Function.uncurry H) :=
    hpred.mono (predictable_le_ambient ℱ)
  let G : ℝ≥0 × Ω → ℝ :=
    (Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (Function.uncurry H)
  have hG : StronglyMeasurable G :=
    hambient.indicator (measurableSet_Ioc.prod MeasurableSet.univ)
  let htimeSFinite : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hstrong : StronglyMeasurable
      (fun ω ↦ ∫ s in Ioc (0 : ℝ≥0) T, H s ω ∂timeMeasure) := by
    have hint : StronglyMeasurable (fun ω ↦ ∫ s, G (s, ω) ∂timeMeasure) :=
      @StronglyMeasurable.integral_prod_left' ℝ≥0 Ω ℝ
        (inferInstance : MeasurableSpace ℝ≥0) (inferInstance : MeasurableSpace Ω)
        timeMeasure _ _ htimeSFinite G hG
    convert hint using 1
    funext ω
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
    funext s
    simp only [G, Set.indicator, mem_prod, mem_Ioc, mem_univ, and_true,
      Function.uncurry_apply_pair]
  have hnorm : ∀ ω, ‖∫ s in Ioc (0 : ℝ≥0) T, H s ω ∂timeMeasure‖ ≤
      C * (T : ℝ) := by
    intro ω
    have hconst : IntegrableOn (fun _s : ℝ≥0 ↦ C)
        (Ioc (0 : ℝ≥0) T) timeMeasure :=
      integrableOn_const (timeMeasure_Ioc_lt_top 0 T).ne
    calc
      ‖∫ s in Ioc (0 : ℝ≥0) T, H s ω ∂timeMeasure‖ ≤
          ∫ _s in Ioc (0 : ℝ≥0) T, C ∂timeMeasure := by
            apply norm_integral_le_of_norm_le hconst
            exact ae_of_all _ fun s ↦ by simpa [Real.norm_eq_abs] using hbound s ω
      _ = C * (T : ℝ) := by
        rw [integral_timeMeasure_eq_intervalIntegral (fun _s : ℝ≥0 ↦ C) 0 T (by simp)]
        simp [mul_comm]
  exact Integrable.of_bound hstrong.aestronglyMeasurable (C * (T : ℝ))
    (ae_of_all _ hnorm)

/-- Exponentially weighted upward jump transform through a right-closed stopping mask. -/
noncomputable def throughStopExponentialUpwardIntegrand
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω ↦ throughStopMask τ s ω *
    (fixedHorizonExponentialWeight a T s *
      clippedUpwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω))

/-- Exponentially weighted downward jump transform through a right-closed stopping mask. -/
noncomputable def throughStopExponentialDownwardIntegrand
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω ↦ throughStopMask τ s ω *
    (fixedHorizonExponentialWeight a T s *
      clippedDownwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω))

/-- Continuous integrating-factor clock accumulated while the path is alive. -/
noncomputable def throughStopExponentialClock
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) T,
    throughStopMask τ s ω *
      (a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))) ∂timeMeasure

/-- Exponentially weighted marked compensator through the stopping mask. -/
noncomputable def throughStopExponentialGeneratorCompensator
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (Λplus Λminus : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  integratedIntensity Λplus
      (throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus) T ω +
    integratedIntensity Λminus
      (throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus) T ω

theorem throughStopExponentialUpwardIntegrand_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ
      (throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus) := by
  change IsBoundedPredictable ℱ (fun s ω ↦ throughStopMask τ s ω *
    (fixedHorizonExponentialWeight a T s * clippedUpwardIncrement R f
      (leftCurrentOfCounts K0 Nplus Nminus s ω)))
  exact hMask.isBoundedPredictable.mul_process
    ((fixedHorizonExponentialWeight_boundedPredictable ha T).mul_process
      (clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f))

theorem throughStopExponentialDownwardIntegrand_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ
      (throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus) := by
  change IsBoundedPredictable ℱ (fun s ω ↦ throughStopMask τ s ω *
    (fixedHorizonExponentialWeight a T s * clippedDownwardIncrement R f
      (leftCurrentOfCounts K0 Nplus Nminus s ω)))
  exact hMask.isBoundedPredictable.mul_process
    ((fixedHorizonExponentialWeight_boundedPredictable ha T).mul_process
      (clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f))

private theorem throughStopExponentialClockIntegrand_boundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    IsBoundedPredictable ℱ (fun s ω ↦ throughStopMask τ s ω *
      (a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)))) := by
  exact hMask.isBoundedPredictable.mul_process
    (((constant_boundedPredictable a).mul_process
      (fixedHorizonExponentialWeight_boundedPredictable ha T)).mul_process
        (clippedLeftValue_boundedPredictable hplus hminus hK0 R f))

theorem throughStopExponentialClock_integrableOn
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (ω : Ω) :
    IntegrableOn (fun s ↦ throughStopMask τ s ω *
      (a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))))
      (Ioc (0 : ℝ≥0) T) timeMeasure :=
  (throughStopExponentialClockIntegrand_boundedPredictable
    hplus hminus hK0 hMask ha T R f).integrableOn_timeMeasure T ω

theorem throughStopExponentialClock_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    Integrable (throughStopExponentialClock τ a T R f K0 Nplus Nminus) μ := by
  change Integrable (fun ω ↦ ∫ s in Ioc (0 : ℝ≥0) T,
    throughStopMask τ s ω *
      (a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))) ∂timeMeasure) μ
  exact (throughStopExponentialClockIntegrand_boundedPredictable
    hplus hminus hK0 hMask ha T R f).setIntegral_timeMeasure_integrable T

private theorem countingIntegral_integrable_of_boundedPredictable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hA : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (T : ℝ≥0) : Integrable (countingIntegral N H T) μ := by
  have hResidual := (hΛ.martingale_of_boundedPredictable hH hA).integrable T
  have hComp := integratedIntensity_integrable_of_boundedPredictable hΛ hH hA T
  have heq : countingIntegral N H T = fun ω ↦
      compensatedIntegral N Λ H T ω + integratedIntensity Λ H T ω := by
    funext ω
    simp only [compensatedIntegral]
    ring
  rw [heq]
  exact hResidual.add hComp

private theorem integral_countingIntegral_eq_integratedIntensity_of_boundedPredictable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hN : IsSimpleCountingProcess ℱ N)
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hA : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (T : ℝ≥0) :
    ∫ ω, countingIntegral N H T ω ∂μ =
      ∫ ω, integratedIntensity Λ H T ω ∂μ := by
  have hM := hΛ.martingale_of_boundedPredictable hH hA
  have hzero : ∫ ω, compensatedIntegral N Λ H T ω ∂μ = 0 := by
    have hzeroProcess : compensatedIntegral N Λ H 0 = 0 := by
      funext ω
      simp [compensatedIntegral, countingIntegral, integratedIntensity, hN.zero]
    have hEq := hM.setIntegral_eq (i := 0) (j := T) bot_le
      (s := Set.univ) MeasurableSet.univ
    rw [Measure.restrict_univ, hzeroProcess] at hEq
    simpa only [Pi.zero_apply, integral_zero] using hEq.symm
  have hCount := countingIntegral_integrable_of_boundedPredictable hΛ hH hA T
  have hComp := integratedIntensity_integrable_of_boundedPredictable hΛ hH hA T
  change (∫ ω, countingIntegral N H T ω - integratedIntensity Λ H T ω ∂μ) = 0
    at hzero
  rw [integral_sub hCount hComp] at hzero
  linarith

omit [MeasurableSpace Ω] in
private theorem timeMeasure_singleton_zero_exponential (s : ℝ≥0) :
    timeMeasure ({s} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton s)]
  rw [Measure.restrict_apply
    (continuous_real_toNNReal.measurable (measurableSet_singleton s))]
  have hpre : Real.toNNReal ⁻¹' ({s} : Set ℝ≥0) ∩ Ici (0 : ℝ) =
      ({(s : ℝ)} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hxs, hx0⟩
      have hxcoe : Real.toNNReal x = Real.toNNReal (s : ℝ) := by simpa using hxs
      exact Real.toNNReal_eq_toNNReal_iff hx0 s.2 |>.mp hxcoe
    · intro hxs
      subst x
      exact ⟨Real.toNNReal_coe, s.2⟩
  rw [hpre, Real.volume_singleton]

omit [MeasurableSpace Ω] in
private theorem ae_coe_ne_exponentialStop
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
      (s : WithTop ℝ≥0) ≠ τ ω := by
  cases hτ : τ ω with
  | top =>
      filter_upwards with s
      exact WithTop.coe_ne_top
  | coe u =>
      have hne : ∀ᵐ (s : ℝ≥0) ∂timeMeasure, s ≠ u := by
        apply MeasureTheory.ae_iff.mpr
        simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
          timeMeasure_singleton_zero_exponential u
      filter_upwards [ae_restrict_of_ae hne] with s hs
      simpa only [hτ, ne_eq, WithTop.coe_eq_coe] using hs

omit [MeasurableSpace Ω] in
theorem throughStopExponentialGeneratorCompensator_eq_integral_rate
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (Λplus Λminus : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s ↦ throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus s ω *
        Λplus s ω) (Ioc (0 : ℝ≥0) T) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s ↦ throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus s ω *
        Λminus s ω) (Ioc (0 : ℝ≥0) T) timeMeasure) :
    throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
        Λplus Λminus ω =
      ∫ s in Ioc (0 : ℝ≥0) T,
        throughStopMask τ s ω * fixedHorizonExponentialWeight a T s *
          clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
            (leftCurrentOfCounts K0 Nplus Nminus s ω) ∂timeMeasure := by
  rw [throughStopExponentialGeneratorCompensator, integratedIntensity, integratedIntensity,
    ← integral_add hplusInt hminusInt]
  congr 1
  funext s
  unfold throughStopExponentialUpwardIntegrand throughStopExponentialDownwardIntegrand
    clippedGeneratorRate
  ring

/-- A strict-before-stop generator drift gives the fixed-horizon weighted compensator bound.
The single retained endpoint of the right-closed mask is removed only inside the time integral. -/
theorem throughStopExponentialClock_add_compensator_le_of_rate_drift_ae
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (ω : Ω)
    (hDrift : ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
      (s : WithTop ℝ≥0) < τ ω →
        clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
            (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
          -a * f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)) + b) :
    throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
        throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
          Λplus Λminus ω ≤
      (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by
  let Hplus := throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus
  let Hminus := throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using throughStopExponentialUpwardIntegrand_boundedPredictable
      hplus hminus hK0 hMask ha.le T R f
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using throughStopExponentialDownwardIntegrand_boundedPredictable
      hplus hminus hK0 hMask ha.le T R f
  have hplusInt : IntegrableOn (fun s ↦ Hplus s ω * Λplus s ω)
      (Ioc (0 : ℝ≥0) T) timeMeasure := hHplus.integrableOn_mul_intensity hΛplus T ω
  have hminusInt : IntegrableOn (fun s ↦ Hminus s ω * Λminus s ω)
      (Ioc (0 : ℝ≥0) T) timeMeasure := hHminus.integrableOn_mul_intensity hΛminus T ω
  have hgenInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * fixedHorizonExponentialWeight a T s *
        clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω))
      (Ioc (0 : ℝ≥0) T) timeMeasure := by
    have heq : (fun s ↦ throughStopMask τ s ω * fixedHorizonExponentialWeight a T s *
        clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω)) =
      (fun s ↦ Hplus s ω * Λplus s ω) +
        fun s ↦ Hminus s ω * Λminus s ω := by
      funext s
      simp only [Hplus, Hminus, throughStopExponentialUpwardIntegrand,
        throughStopExponentialDownwardIntegrand, clippedGeneratorRate, Pi.add_apply]
      ring
    rw [heq]
    exact hplusInt.add hminusInt
  have hclockInt := throughStopExponentialClock_integrableOn
    hplus hminus hK0 hMask ha.le T R f ω
  let combined : ℝ≥0 → ℝ := fun s ↦
    throughStopMask τ s ω *
      (a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))) +
    throughStopMask τ s ω * fixedHorizonExponentialWeight a T s *
      clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
        (leftCurrentOfCounts K0 Nplus Nminus s ω)
  have hcombinedInt : IntegrableOn combined (Ioc (0 : ℝ≥0) T) timeMeasure :=
    hclockInt.add hgenInt
  let dom : ℝ≥0 → ℝ := fun s ↦
    a * fixedHorizonExponentialWeight a T s * (b / a)
  have hdomInt : IntegrableOn dom (Ioc (0 : ℝ≥0) T) timeMeasure := by
    refine (integrableOn_exp_mul_const_timeMeasure a (b / a)).congr_fun ?_ measurableSet_Ioc
    intro s hs
    dsimp only [dom]
    rw [fixedHorizonExponentialWeight_eq_exp a hs.2]
  have hendpoint := ae_coe_ne_exponentialStop τ T ω
  have hpoint : ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
      combined s ≤ dom s := by
    filter_upwards [hDrift, hendpoint] with s hsdrift hsne
    by_cases hsle : (s : WithTop ℝ≥0) ≤ τ ω
    · have hslt : (s : WithTop ℝ≥0) < τ ω := lt_of_le_of_ne hsle hsne
      have hdrift := hsdrift hslt
      have hweight : 0 ≤ fixedHorizonExponentialWeight a T s :=
        Real.exp_pos _ |>.le
      dsimp only [combined, dom]
      simp only [throughStopMask, ite_eq_left hsle, one_mul]
      have ha0 : a ≠ 0 := ne_of_gt ha
      calc
        a * fixedHorizonExponentialWeight a T s *
              f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)) +
            fixedHorizonExponentialWeight a T s *
              clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
                (leftCurrentOfCounts K0 Nplus Nminus s ω)
            = fixedHorizonExponentialWeight a T s *
              (a * f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)) +
                clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
                  (leftCurrentOfCounts K0 Nplus Nminus s ω)) := by ring
        _ ≤ fixedHorizonExponentialWeight a T s * b := by
          apply mul_le_mul_of_nonneg_left _ hweight
          linarith
        _ = a * fixedHorizonExponentialWeight a T s * (b / a) := by
          field_simp [ha0]
    · dsimp only [combined, dom]
      simp only [throughStopMask, ite_eq_right hsle, zero_mul, zero_add]
      exact mul_nonneg (mul_nonneg ha.le (Real.exp_pos _).le) (div_nonneg hb ha.le)
  have hmono : (∫ s in Ioc (0 : ℝ≥0) T, combined s ∂timeMeasure) ≤
      ∫ s in Ioc (0 : ℝ≥0) T, dom s ∂timeMeasure :=
    integral_mono_ae hcombinedInt hdomInt hpoint
  have hcompEq := throughStopExponentialGeneratorCompensator_eq_integral_rate
    τ a T R f K0 Nplus Nminus Λplus Λminus ω hplusInt hminusInt
  have hleftEq : throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
      throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
        Λplus Λminus ω =
      ∫ s in Ioc (0 : ℝ≥0) T, combined s ∂timeMeasure := by
    rw [throughStopExponentialClock, hcompEq, ← integral_add hclockInt hgenInt]
  have hdomEq : (∫ s in Ioc (0 : ℝ≥0) T, dom s ∂timeMeasure) =
      (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by
    calc
      (∫ s in Ioc (0 : ℝ≥0) T, dom s ∂timeMeasure) =
          ∫ s in Ioc (0 : ℝ≥0) T,
            a * Real.exp (a * (s : ℝ)) * (b / a) ∂timeMeasure := by
              apply setIntegral_congr_fun measurableSet_Ioc
              intro s hs
              dsimp only [dom]
              rw [fixedHorizonExponentialWeight_eq_exp a hs.2]
      _ = Real.exp (a * (T : ℝ)) * (b / a) - (b / a) := by
        simpa using integral_exp_mul_const_timeMeasure a (b / a) (u := 0) (v := T) (by simp)
      _ = (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by ring
  rw [hleftEq]
  exact hmono.trans_eq hdomEq

/-- The exponentially weighted clipped observable evaluated at the pathwise cut `T ∧ τ`. -/
noncomputable def fixedHorizonExponentialStoppedObservable
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) : ℝ :=
  MeasureTheory.stoppedProcess
    (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
      clippedObservable R f K0 Nplus Nminus s ω') τ T ω


/-- Fixed-horizon integrating-factor chain rule for the clipped current stopped through a
right-closed mask.  In particular, a jump at the stopping coordinate is retained. -/
theorem fixedHorizonExponential_clipped_chain_rule_throughStop
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ t, NoSimultaneousJumpsOn Nplus Nminus t)
    (τ : Ω → WithTop ℝ≥0) (a : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (ω : Ω) :
    MeasureTheory.stoppedProcess
          (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
            clippedObservable R f K0 Nplus Nminus s ω') τ T ω -
        clippedObservable R f K0 Nplus Nminus 0 ω =
      countingIntegral Nplus
          (throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus) T ω +
        countingIntegral Nminus
          (throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus) T ω +
        throughStopExponentialClock τ a T R f K0 Nplus Nminus ω := by
  classical
  let u := exponentialCutTime T τ ω
  let events := markedEventSet Nplus Nminus u ω
  let time := markedEventTime Nplus Nminus ω
  let key := markedEventKey Nplus Nminus ω
  let step := markedEventStep
  let F : ℤ → ℝ := fun k ↦ f (integerClip R k)
  have huT : u ≤ T := exponentialCutTime_le T τ ω
  have htimeInj : Set.InjOn time (events : Set (ℕ ⊕ ℕ)) := by
    exact markedEventTime_injOn (hplus.jumpTime_injOn ω u)
      (hminus.jumpTime_injOn ω u) (hNo u)
  let eventOrder : LinearOrder (ℕ ⊕ ℕ) :=
    LinearOrder.lift' key (markedEventKey_injective Nplus Nminus ω)
  have horder : ∀ e ∈ events, ∀ x ∈ events,
      @LT.lt (ℕ ⊕ ℕ) eventOrder.toLT e x ↔ time e < time x := by
    intro e he x hx
    change key e < key x ↔ time e < time x
    exact markedEventKey_lt_iff_time_lt htimeInj he hx
  have htime : ∀ e ∈ events, (0 : ℝ≥0) < time e ∧ time e ≤ u := by
    intro e he
    exact ⟨markedEventTime_pos hplus hminus he, markedEventTime_le_horizon he⟩
  have hformula := @exp_mul_finiteJumpState_eq (ℕ ⊕ ℕ) eventOrder events time step F
    a 0 u (K0 ω) (by simp) htime horder
  have htotal : (∑ e ∈ events, step e) =
      (Nplus u ω : ℤ) - (Nminus u ω : ℤ) := by
    dsimp only [events, step]
    unfold markedEventSet
    rw [Finset.sum_disjSum]
    simp [markedEventStep]
    ring
  have hstate : ∀ s ∈ Ioc (0 : ℝ≥0) u,
      finiteJumpStateBefore events time step (K0 ω) s =
        leftCurrentOfCounts K0 Nplus Nminus s ω := by
    intro s hs
    dsimp only [events, time, step]
    unfold finiteJumpStateBefore
    rw [sum_markedEventStep_before_time_eq
      (hplus.monotone ω) (hplus.rightContinuous ω) (hplus.jumpTime_injOn ω u)
      (hminus.monotone ω) (hminus.rightContinuous ω) (hminus.jumpTime_injOn ω u)
      hs.2]
    unfold leftCurrentOfCounts
    ring
  have hsum :
      (∑ e ∈ events,
          Real.exp (a * (time e : ℝ)) *
            (F (finiteJumpStateBefore events time step (K0 ω) (time e) + step e) -
              F (finiteJumpStateBefore events time step (K0 ω) (time e)))) =
        countingIntegral Nplus
            (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
              clippedUpwardIncrement R f
                (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω +
          countingIntegral Nminus
            (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
              clippedDownwardIncrement R f
                (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω := by
    dsimp only [events]
    unfold markedEventSet
    rw [Finset.sum_disjSum]
    unfold countingIntegral
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hei : Sum.inl i ∈ events := by simp [events, markedEventSet, hi]
      have heBounds := htime (Sum.inl i) hei
      have hsi := hstate (time (Sum.inl i)) heBounds
      have htimeT : jumpTime Nplus i ω ≤ T :=
        (jumpTime_le_of_lt (Finset.mem_range.mp hi)).trans huT
      dsimp only [events, time, step, markedEventTime, markedEventStep] at hsi ⊢
      unfold markedEventSet at hsi
      rw [hsi, fixedHorizonExponentialWeight_eq_exp a htimeT]
      rfl
    · apply Finset.sum_congr rfl
      intro j hj
      have hej : Sum.inr j ∈ events := by simp [events, markedEventSet, hj]
      have heBounds := htime (Sum.inr j) hej
      have hsj := hstate (time (Sum.inr j)) heBounds
      have htimeT : jumpTime Nminus j ω ≤ T :=
        (jumpTime_le_of_lt (Finset.mem_range.mp hj)).trans huT
      dsimp only [events, time, step, markedEventTime, markedEventStep] at hsj ⊢
      unfold markedEventSet at hsj
      rw [hsj, fixedHorizonExponentialWeight_eq_exp a htimeT]
      rfl
  have hplusStop := countingIntegral_mul_throughStopMask
    (fun ω' ↦ hplus.monotone ω') (fun ω' s ↦ hplus.rightContinuous ω' s)
    τ (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
      clippedUpwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω
  have hminusStop := countingIntegral_mul_throughStopMask
    (fun ω' ↦ hminus.monotone ω') (fun ω' s ↦ hminus.rightContinuous ω' s)
    τ (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
      clippedDownwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω
  change countingIntegral Nplus
      (fun s ω' ↦ throughStopMask τ s ω' *
        (fixedHorizonExponentialWeight a T s *
          clippedUpwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω'))) T ω =
    countingIntegral Nplus
      (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
        clippedUpwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω at hplusStop
  change countingIntegral Nminus
      (fun s ω' ↦ throughStopMask τ s ω' *
        (fixedHorizonExponentialWeight a T s *
          clippedDownwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω'))) T ω =
    countingIntegral Nminus
      (fun s ω' ↦ fixedHorizonExponentialWeight a T s *
        clippedDownwardIncrement R f (leftCurrentOfCounts K0 Nplus Nminus s ω')) u ω at hminusStop
  have hclock : throughStopExponentialClock τ a T R f K0 Nplus Nminus ω =
      ∫ s in Ioc (0 : ℝ≥0) u,
        a * Real.exp (a * (s : ℝ)) *
          F (finiteJumpStateBefore events time step (K0 ω) s) ∂timeMeasure := by
    rw [throughStopExponentialClock]
    have hcut := integral_mul_throughStopMask_eq_cut τ
      (fun s ↦ a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω))) T ω
    rw [hcut]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    change a * fixedHorizonExponentialWeight a T s *
        f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)) =
      a * Real.exp (a * (s : ℝ)) *
        F (finiteJumpStateBefore events time step (K0 ω) s)
    rw [fixedHorizonExponentialWeight_eq_exp a (hs.2.trans huT), hstate s hs]
  have hterminal : F (K0 ω + ∑ e ∈ events, step e) =
      clippedObservable R f K0 Nplus Nminus u ω := by
    rw [htotal]
    unfold F clippedObservable currentOfCounts
    congr 2
    ring
  have hinitial : F (K0 ω) = clippedObservable R f K0 Nplus Nminus 0 ω := by
    simpa only [F] using (clippedObservable_zero hplus hminus R f ω).symm
  change fixedHorizonExponentialWeight a T u *
        clippedObservable R f K0 Nplus Nminus u ω -
      clippedObservable R f K0 Nplus Nminus 0 ω = _
  rw [fixedHorizonExponentialWeight_eq_exp a huT, ← hterminal, ← hinitial]
  calc
    Real.exp (a * (u : ℝ)) * F (K0 ω + ∑ e ∈ events, step e) - F (K0 ω) =
        (∑ e ∈ events,
            Real.exp (a * (time e : ℝ)) *
              (F (finiteJumpStateBefore events time step (K0 ω) (time e) + step e) -
                F (finiteJumpStateBefore events time step (K0 ω) (time e)))) +
          ∫ s in Ioc (0 : ℝ≥0) u,
            a * Real.exp (a * (s : ℝ)) *
              F (finiteJumpStateBefore events time step (K0 ω) s) ∂timeMeasure := by
          simpa only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul] using hformula.2
    _ = _ := by
      rw [hsum, ← hplusStop, ← hminusStop, ← hclock]
      unfold throughStopExponentialUpwardIntegrand throughStopExponentialDownwardIntegrand
      abel

/-- Fixed-horizon exponential Lyapunov envelope for the alive part of a clipped two-colour
current.  Genuine predictable intensities supply the weighted Dynkin identity internally; no
conditional-expectation or Dynkin hypothesis is exposed. -/
theorem exponential_clipped_throughStop_moment_bound_of_rate_drift_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ t, NoSimultaneousJumpsOn Nplus Nminus t)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (hDrift : ∀ᵐ ω ∂μ, ∀ᵐ (s : ℝ≥0)
      ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
        (s : WithTop ℝ≥0) < τ ω →
          clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
              (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
            -a * f (integerClip R (leftCurrentOfCounts K0 Nplus Nminus s ω)) + b) :
    ∫ ω, throughStopMask τ T ω * clippedObservable R f K0 Nplus Nminus T ω ∂μ ≤
      Real.exp (-(a * (T : ℝ))) *
          (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
        (b / a) * (1 - Real.exp (-(a * (T : ℝ)))) := by
  let Hplus := throughStopExponentialUpwardIntegrand τ a T R f K0 Nplus Nminus
  let Hminus := throughStopExponentialDownwardIntegrand τ a T R f K0 Nplus Nminus
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using throughStopExponentialUpwardIntegrand_boundedPredictable
      hplus hminus hK0 hMask ha.le T R f
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using throughStopExponentialDownwardIntegrand_boundedPredictable
      hplus hminus hK0 hMask ha.le T R f
  have hCountPlus : Integrable (countingIntegral Nplus Hplus T) μ :=
    countingIntegral_integrable_of_boundedPredictable hΛplus hHplus hAplus T
  have hCountMinus : Integrable (countingIntegral Nminus Hminus T) μ :=
    countingIntegral_integrable_of_boundedPredictable hΛminus hHminus hAminus T
  have hIntPlus : Integrable (fun ω ↦ integratedIntensity Λplus Hplus T ω) μ :=
    integratedIntensity_integrable_of_boundedPredictable hΛplus hHplus hAplus T
  have hIntMinus : Integrable (fun ω ↦ integratedIntensity Λminus Hminus T ω) μ :=
    integratedIntensity_integrable_of_boundedPredictable hΛminus hHminus hAminus T
  have hCountPlusEq : ∫ ω, countingIntegral Nplus Hplus T ω ∂μ =
      ∫ ω, integratedIntensity Λplus Hplus T ω ∂μ :=
    integral_countingIntegral_eq_integratedIntensity_of_boundedPredictable
      hplus hΛplus hHplus hAplus T
  have hCountMinusEq : ∫ ω, countingIntegral Nminus Hminus T ω ∂μ =
      ∫ ω, integratedIntensity Λminus Hminus T ω ∂μ :=
    integral_countingIntegral_eq_integratedIntensity_of_boundedPredictable
      hminus hΛminus hHminus hAminus T
  have hClock : Integrable
      (throughStopExponentialClock τ a T R f K0 Nplus Nminus) μ :=
    throughStopExponentialClock_integrable hplus hminus hK0 hMask ha.le T R f
  have hComp : Integrable
      (throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
        Λplus Λminus) μ := by
    change Integrable (fun ω ↦ integratedIntensity Λplus Hplus T ω +
      integratedIntensity Λminus Hminus T ω) μ
    exact hIntPlus.add hIntMinus
  have hTerminalEq : fixedHorizonExponentialStoppedObservable
      τ a T R f K0 Nplus Nminus = fun ω ↦
        clippedObservable R f K0 Nplus Nminus 0 ω +
          countingIntegral Nplus Hplus T ω + countingIntegral Nminus Hminus T ω +
            throughStopExponentialClock τ a T R f K0 Nplus Nminus ω := by
    funext ω
    have hpath := fixedHorizonExponential_clipped_chain_rule_throughStop
      (K0 := K0) hplus hminus hNo τ a T R f ω
    change fixedHorizonExponentialStoppedObservable τ a T R f K0 Nplus Nminus ω -
        clippedObservable R f K0 Nplus Nminus 0 ω = _ at hpath
    change fixedHorizonExponentialStoppedObservable τ a T R f K0 Nplus Nminus ω = _
    dsimp only [Hplus, Hminus]
    linarith
  have hTerminal : Integrable
      (fixedHorizonExponentialStoppedObservable τ a T R f K0 Nplus Nminus) μ := by
    rw [hTerminalEq]
    exact ((hObs0.add hCountPlus).add hCountMinus).add hClock
  have hTerminalIntegral :
      (∫ ω, fixedHorizonExponentialStoppedObservable
        τ a T R f K0 Nplus Nminus ω ∂μ) =
      (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
        ∫ ω, throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
          throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
            Λplus Λminus ω ∂μ := by
    rw [hTerminalEq]
    have hsplitTerminal := integral_add
      ((hObs0.add hCountPlus).add hCountMinus) hClock
    have hsplitMiddle := integral_add (hObs0.add hCountPlus) hCountMinus
    have hsplitInitial := integral_add hObs0 hCountPlus
    simp only [Pi.add_apply] at hsplitTerminal hsplitMiddle hsplitInitial
    rw [hsplitTerminal, hsplitMiddle, hsplitInitial, hCountPlusEq, hCountMinusEq]
    change _ = _ + ∫ ω,
      throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
        (integratedIntensity Λplus Hplus T ω + integratedIntensity Λminus Hminus T ω) ∂μ
    have hsplitComp := integral_add hClock (hIntPlus.add hIntMinus)
    have hsplitIntensities := integral_add hIntPlus hIntMinus
    simp only [Pi.add_apply] at hsplitComp hsplitIntensities
    rw [hsplitComp, hsplitIntensities]
    ring
  have hCompBound : ∀ᵐ ω ∂μ,
      throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
          throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
            Λplus Λminus ω ≤
        (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by
    filter_upwards [hDrift] with ω hω
    exact throughStopExponentialClock_add_compensator_le_of_rate_drift_ae
      hplus hminus hΛplus hΛminus hK0 hMask ha hb T R f ω hω
  have hCompIntegralBound :
      (∫ ω, throughStopExponentialClock τ a T R f K0 Nplus Nminus ω +
        throughStopExponentialGeneratorCompensator τ a T R f K0 Nplus Nminus
          Λplus Λminus ω ∂μ) ≤
        (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by
    have hright : Integrable (fun _ω : Ω ↦
        (b / a) * (Real.exp (a * (T : ℝ)) - 1)) μ := integrable_const _
    have hmono := integral_mono_ae (hClock.add hComp) hright hCompBound
    simpa using hmono
  have hTerminalBound :
      (∫ ω, fixedHorizonExponentialStoppedObservable
        τ a T R f K0 Nplus Nminus ω ∂μ) ≤
      (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
        (b / a) * (Real.exp (a * (T : ℝ)) - 1) := by
    rw [hTerminalIntegral]
    simpa only [add_comm] using
      (add_le_add_left hCompIntegralBound
        (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ))
  have hOrdPlus := clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hOrdMinus := clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hOrdM := clippedDynkinProcess_martingale_of_initial_measurable
    hplus hminus hNo hΛplus hΛminus hK0 R f hAplus hAminus
  have hOrdComp := clippedGeneratorCompensator_integrable
    hΛplus hΛminus hOrdPlus hOrdMinus hAplus hAminus T
  have hObsT := clippedObservable_integrable_of_martingale hOrdM T hObs0 hOrdComp
  have hMaskSection : StronglyMeasurable (throughStopMask τ T) := by
    have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
        (Function.uncurry (throughStopMask τ)) :=
      hMask.1.mono (predictable_le_ambient ℱ)
    exact hambient.comp_measurable (measurable_const.prodMk measurable_id)
  have hKilled : Integrable (fun ω ↦
      throughStopMask τ T ω * clippedObservable R f K0 Nplus Nminus T ω) μ := by
    refine hObsT.bdd_mul (c := 1) hMaskSection.aestronglyMeasurable ?_
    exact ae_of_all _ fun ω ↦ by
      simp only [throughStopMask]
      split <;> norm_num
  have hExtract : ∀ ω,
      throughStopMask τ T ω * clippedObservable R f K0 Nplus Nminus T ω ≤
        Real.exp (-(a * (T : ℝ))) *
          fixedHorizonExponentialStoppedObservable τ a T R f K0 Nplus Nminus ω := by
    intro ω
    by_cases hTτ : (T : WithTop ℝ≥0) ≤ τ ω
    · have hmin : min (T : WithTop ℝ≥0) (τ ω) = T := min_eq_left hTτ
      have hmask : throughStopMask τ T ω = 1 := by
        unfold throughStopMask
        split
        · rfl
        · contradiction
      have hstop : fixedHorizonExponentialStoppedObservable
          τ a T R f K0 Nplus Nminus ω =
            fixedHorizonExponentialWeight a T T *
              clippedObservable R f K0 Nplus Nminus T ω := by
        unfold fixedHorizonExponentialStoppedObservable MeasureTheory.stoppedProcess
        rw [hmin]
        rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      rw [hmask, one_mul, hstop]
      change clippedObservable R f K0 Nplus Nminus T ω ≤
        Real.exp (-(a * (T : ℝ))) *
          (fixedHorizonExponentialWeight a T T *
            clippedObservable R f K0 Nplus Nminus T ω)
      rw [fixedHorizonExponentialWeight_eq_exp a le_rfl]
      have hexp : Real.exp (-(a * (T : ℝ))) * Real.exp (a * (T : ℝ)) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      rw [← mul_assoc, hexp, one_mul]
    · have hmask : throughStopMask τ T ω = 0 := by
        unfold throughStopMask
        split
        · contradiction
        · rfl
      rw [hmask, zero_mul]
      apply mul_nonneg (Real.exp_pos _).le
      unfold fixedHorizonExponentialStoppedObservable MeasureTheory.stoppedProcess
      exact mul_nonneg (Real.exp_pos _).le (hf _)
  have hScaledTerminal : Integrable (fun ω ↦ Real.exp (-(a * (T : ℝ))) *
      fixedHorizonExponentialStoppedObservable τ a T R f K0 Nplus Nminus ω) μ :=
    hTerminal.const_mul _
  have hKilledBound :
      (∫ ω, throughStopMask τ T ω *
        clippedObservable R f K0 Nplus Nminus T ω ∂μ) ≤
      Real.exp (-(a * (T : ℝ))) *
        (∫ ω, fixedHorizonExponentialStoppedObservable
          τ a T R f K0 Nplus Nminus ω ∂μ) := by
    have hmono := integral_mono hKilled hScaledTerminal hExtract
    simpa only [integral_const_mul] using hmono
  calc
    (∫ ω, throughStopMask τ T ω * clippedObservable R f K0 Nplus Nminus T ω ∂μ)
        ≤ Real.exp (-(a * (T : ℝ))) *
          (∫ ω, fixedHorizonExponentialStoppedObservable
            τ a T R f K0 Nplus Nminus ω ∂μ) := hKilledBound
    _ ≤ Real.exp (-(a * (T : ℝ))) *
        ((∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
          (b / a) * (Real.exp (a * (T : ℝ)) - 1)) :=
      mul_le_mul_of_nonneg_left hTerminalBound (Real.exp_pos _).le
    _ = Real.exp (-(a * (T : ℝ))) *
          (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
        (b / a) * (1 - Real.exp (-(a * (T : ℝ)))) := by
      have hexp : Real.exp (-(a * (T : ℝ))) * Real.exp (a * (T : ℝ)) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      calc
        _ = Real.exp (-(a * (T : ℝ))) *
              (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
            (b / a) *
              (Real.exp (-(a * (T : ℝ))) * Real.exp (a * (T : ℝ)) -
                Real.exp (-(a * (T : ℝ)))) := by ring
        _ = _ := by rw [hexp]

end OTSelector.CountingProcess
