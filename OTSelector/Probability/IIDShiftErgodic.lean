import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# Ergodicity of the actual two-sided iid shift

The product law on integer-indexed sequences is preserved by every integer shift.  For a
shift-invariant measurable event, finite-cylinder approximation and independence of sufficiently
separated coordinate blocks imply that its probability equals its square.  Thus the one-step
shift is ergodic.  No mixing or ergodicity premise is imposed on the base probability law.
-/

open Function Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology symmDiff

namespace OTSelector.IIDShift

variable {X : Type*} [MeasurableSpace X]

/-- Move the coordinate origin by the integer `k`. -/
def shift (k : ℤ) (ω : ℤ → X) (i : ℤ) : X := ω (i + k)

omit [MeasurableSpace X] in
@[simp]
theorem shift_zero (ω : ℤ → X) : shift 0 ω = ω := by ext i; simp [shift]

omit [MeasurableSpace X] in
@[simp]
theorem shift_add (k l : ℤ) (ω : ℤ → X) : shift (k + l) ω = shift k (shift l ω) := by
  ext i
  simp [shift, add_assoc]

@[fun_prop]
theorem measurable_shift (k : ℤ) : Measurable (shift (X := X) k) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i + k)

/-- Each integer shift preserves the actual iid product probability measure. -/
theorem measurePreserving_shift (μ : Measure X) [IsProbabilityMeasure μ] (k : ℤ) :
    MeasurePreserving (shift (X := X) k) (Measure.infinitePi (fun _ : ℤ ↦ μ))
      (Measure.infinitePi (fun _ : ℤ ↦ μ)) where
  measurable := measurable_shift k
  map_eq := Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h ↦ add_right_cancel h)

omit [MeasurableSpace X] in
theorem iterate_shift_one (k : ℕ) : (shift (X := X) 1)^[k] = shift (k : ℤ) := by
  induction k with
  | zero => ext ω i; simp [shift]
  | succ k hk =>
      ext ω i
      simp only [Function.iterate_succ_apply', hk, shift, Nat.cast_add, Nat.cast_one]
      congr 1
      omega

private theorem exists_disjoint_translate (s : Finset ℤ) :
    ∃ k : ℕ, Disjoint s (s.image fun i ↦ i + (k : ℤ)) := by
  classical
  let M := s.sup Int.natAbs
  have hbound {i : ℤ} (hi : i ∈ s) : -(M : ℤ) ≤ i ∧ i ≤ (M : ℤ) := by
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Finset.le_sup hi : i.natAbs ≤ M)
  refine ⟨2 * M + 1, Finset.disjoint_left.mpr ?_⟩
  intro i hi hi'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi'
  have h₁ := hbound hi
  have h₂ := hbound hj
  omega

variable (μ : Measure X) [IsProbabilityMeasure μ]

local notation "Q" => Measure.infinitePi (fun _ : ℤ ↦ μ)

private theorem exists_cylinder_approx {A : Set (ℤ → X)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ B : Set (s → X), MeasurableSet B ∧
      (Q).real (cylinder s B ∆ A) < ε := by
  have hring : IsSetRing (measurableCylinders (fun _ : ℤ ↦ X)) :=
    ⟨empty_mem_measurableCylinders _, fun {_ _} hs ht ↦ union_mem_measurableCylinders hs ht,
      fun {_ _} hs ht ↦ sdiff_mem_measurableCylinders hs ht⟩
  have hcover : ∃ D : Set (Set (ℤ → X)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ ↦ X) ∧ Q (⋃₀ D)ᶜ = 0 := by
    exact ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr
      (univ_mem_measurableCylinders _), by simp⟩
  obtain ⟨C, hC, happrox⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := Q) hring hcover generateFrom_measurableCylinders.symm hA
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨s, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  refine ⟨s, B, hB, ?_⟩
  have h := (ENNReal.toReal_lt_toReal (measure_ne_top Q _) ENNReal.ofReal_ne_top).mpr happrox
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using h

/-- A finite cylinder and its shift are independent whenever their coordinate blocks are disjoint. -/
theorem measure_inter_shift_cylinder (s : Finset ℤ) {B : Set (s → X)} (hB : MeasurableSet B)
    (k : ℤ) (hdis : Disjoint s (s.image fun i ↦ i + k)) :
    Q (cylinder s B ∩ shift k ⁻¹' cylinder s B) = Q (cylinder s B) ^ 2 := by
  classical
  let t := s.image fun i ↦ i + k
  let readShift : (t → X) → (s → X) := fun ω i ↦
    ω ⟨i.val + k, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  have hread : Measurable readShift := by
    exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  have hindep : iIndepFun (fun i : ℤ ↦ fun ω : ℤ → X ↦ ω i) Q :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hblocks := hindep.indepFun_finset s t hdis (fun i ↦ measurable_pi_apply i)
  have h := (hblocks.comp measurable_id hread).measure_inter_preimage_eq_mul B B hB hB
  have heq : Q (cylinder s B ∩ shift k ⁻¹' cylinder s B) =
      Q (cylinder s B) * Q (shift k ⁻¹' cylinder s B) := by
    exact h
  rw [heq, (measurePreserving_shift μ k).measure_preimage hB.cylinder.nullMeasurableSet,
    pow_two]

/-- The real-probability version of finite-cylinder shift independence. -/
theorem measureReal_inter_shift_cylinder (s : Finset ℤ) {B : Set (s → X)}
    (hB : MeasurableSet B) (k : ℤ) (hdis : Disjoint s (s.image fun i ↦ i + k)) :
    (Q).real (cylinder s B ∩ shift k ⁻¹' cylinder s B) = (Q).real (cylinder s B) ^ 2 := by
  have h := congrArg ENNReal.toReal (measure_inter_shift_cylinder μ s hB k hdis)
  simpa only [Measure.real, ENNReal.toReal_pow] using h

private theorem invariant_probability_error {A C : Set (ℤ → X)}
    (hA : MeasurableSet A) (hC : MeasurableSet C) (k : ℤ)
    (hfixed : shift k ⁻¹' A = A)
    (hindep : (Q).real (C ∩ shift k ⁻¹' C) = (Q).real C ^ 2) :
    |(Q).real A - (Q).real A ^ 2| ≤ 4 * (Q).real (C ∆ A) := by
  let p := (Q).real A
  let q := (Q).real C
  let d := (Q).real (C ∆ A)
  have hp : 0 ≤ p := measureReal_nonneg
  have hq : 0 ≤ q := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hq1 : q ≤ 1 := measureReal_le_one
  have hd : 0 ≤ d := measureReal_nonneg
  have hpq : |q - p| ≤ d :=
    abs_measureReal_sub_le_measureReal_symmDiff hC.nullMeasurableSet hA.nullMeasurableSet
  have hshiftC : MeasurableSet (shift k ⁻¹' C) := measurable_shift k hC
  have hshiftError : (Q).real ((shift k ⁻¹' C) ∆ A) = d := by
    nth_rw 1 [← hfixed]
    rw [← Set.preimage_symmDiff]
    exact (measurePreserving_shift μ k).measureReal_preimage
      (hC.symmDiff hA).nullMeasurableSet
  have hsub : A ∆ (C ∩ shift k ⁻¹' C) ⊆ (C ∆ A) ∪ ((shift k ⁻¹' C) ∆ A) := by
    intro ω
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union]
    tauto
  have herror : (Q).real (A ∆ (C ∩ shift k ⁻¹' C)) ≤ 2 * d := by
    have h := (measureReal_mono (μ := Q) hsub).trans
      (measureReal_union_le (μ := Q) (C ∆ A) ((shift k ⁻¹' C) ∆ A))
    rw [hshiftError] at h
    exact h.trans_eq (by dsimp [d]; ring)
  have hinter : |p - q ^ 2| ≤ 2 * d := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff
      (μ := Q) hA.nullMeasurableSet (hC.inter hshiftC).nullMeasurableSet
    rw [hindep] at h
    exact h.trans herror
  have hsquares : |q ^ 2 - p ^ 2| ≤ 2 * d := by
    calc
      _ = |q - p| * |q + p| := by rw [← abs_mul]; congr 1; ring
      _ ≤ d * 2 := mul_le_mul hpq (by rw [abs_of_nonneg (add_nonneg hq hp)]; linarith)
        (abs_nonneg _) hd
      _ = 2 * d := mul_comm _ _
  have htriangle := abs_sub_le p (q ^ 2) (p ^ 2)
  change |p - p ^ 2| ≤ 4 * d
  linarith

/-- Every measurable event invariant under the one-step shift has real probability equal to its
square, proved by finite-cylinder approximation and disjoint block independence. -/
theorem measureReal_eq_sq_of_shift_invariant {A : Set (ℤ → X)}
    (hA : MeasurableSet A) (hfixed : shift 1 ⁻¹' A = A) :
    (Q).real A = (Q).real A ^ 2 := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨s, B, hB, happrox⟩ := exists_cylinder_approx μ hA
    (show 0 < ε / 4 by positivity)
  obtain ⟨k, hk⟩ := exists_disjoint_translate s
  have hfixedk : shift (k : ℤ) ⁻¹' A = A := by
    rw [← iterate_shift_one]
    exact IsFixedPt.preimage_iterate hfixed k
  have h := invariant_probability_error μ hA hB.cylinder k hfixedk
    (measureReal_inter_shift_cylinder μ s hB k hk)
  rw [Real.dist_eq]
  linarith

/-- The one-step shift on the actual two-sided iid product law is ergodic.  This requires only
a measurable probability law on the coordinate space. -/
theorem ergodic_shift_one : Ergodic (shift (X := X) 1) Q where
  toMeasurePreserving := measurePreserving_shift μ 1
  aeconst_set A hA hfixed := by
    have h := measureReal_eq_sq_of_shift_invariant μ hA hfixed
    have hfactor : (Q).real A * ((Q).real A - 1) = 0 := by nlinarith
    simp only [eventuallyConst_set', ae_eq_empty, ae_eq_univ]
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top Q A)).mp hzero)
    · apply Or.inr
      apply (prob_compl_eq_zero_iff hA).mpr
      apply (ENNReal.toReal_eq_one_iff _).mp
      change (Q).real A = 1
      linarith

/-- The whole-action zero-one interface also allows almost invariance and null-measurable events.
One-step ergodicity already suffices when the event is invariant under every integer shift. -/
theorem aeconst_of_forall_shift_ae_eq {A : Set (ℤ → X)}
    (hA : NullMeasurableSet A Q) (hfixed : ∀ k : ℤ, shift k ⁻¹' A =ᵐ[Q] A) :
    EventuallyConst A (ae Q) :=
  (ergodic_shift_one μ).quasiErgodic.aeconst_set₀ hA (hfixed 1)

omit [MeasurableSpace X] in
/-- The integer shift action, available explicitly without assigning a global action instance
to all function spaces. -/
@[instance_reducible]
def shiftAction : AddAction ℤ (ℤ → X) where
  vadd := shift
  zero_vadd := shift_zero
  add_vadd := shift_add

section WholeAction

local instance : AddAction ℤ (ℤ → X) := shiftAction

/-- The full integer shift action on the iid law is ergodic. -/
theorem ergodicVAdd_shift : ErgodicVAdd ℤ (ℤ → X) Q where
  measure_preimage_vadd k _ hA := (measurePreserving_shift μ k).measure_preimage
    hA.nullMeasurableSet
  aeconst_of_forall_preimage_vadd_ae_eq hA hfixed :=
    aeconst_of_forall_shift_ae_eq μ hA.nullMeasurableSet hfixed

end WholeAction

end OTSelector.IIDShift
