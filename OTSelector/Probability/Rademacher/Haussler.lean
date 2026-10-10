/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Probability.Rademacher.VCCovering
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Finite Boolean projections for Haussler packing

This file develops the finite combinatorial layer of Haussler's packing argument.  A projection
is represented by restricting every Boolean pattern to a `Finset` of sample coordinates.  The
fibres of that projection retain their multiplicities; this is essential in the weighted
one-inclusion/double-counting step.
-/

open scoped BigOperators

namespace OTSelector.Probability.Rademacher

open Classical

/-- Restriction of a Boolean pattern to a finite set of sample coordinates. -/
def restrictPattern {m : ℕ} (A : Finset (Fin m)) (p : Fin m → Bool) : A → Bool :=
  fun i ↦ p i

/-- The set of distinct restrictions of `H` to `A`. -/
def patternProjection {m : ℕ} (H : Finset (Fin m → Bool)) (A : Finset (Fin m)) :
    Finset (A → Bool) :=
  H.image (restrictPattern A)

/-- The fibre over a projected Boolean pattern. -/
def projectionFiber {m : ℕ} (H : Finset (Fin m → Bool)) (A : Finset (Fin m))
    (q : A → Bool) : Finset (Fin m → Bool) :=
  H.filter fun p ↦ restrictPattern A p = q

@[simp]
theorem mem_patternProjection_iff {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) (q : A → Bool) :
    q ∈ patternProjection H A ↔ ∃ p ∈ H, restrictPattern A p = q := by
  simp [patternProjection]

@[simp]
theorem mem_projectionFiber_iff {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) (q : A → Bool) (p : Fin m → Bool) :
    p ∈ projectionFiber H A q ↔ p ∈ H ∧ restrictPattern A p = q := by
  simp [projectionFiber]

theorem projectionFiber_subset {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) (q : A → Bool) :
    projectionFiber H A q ⊆ H := by
  exact Finset.filter_subset _ _

theorem projectionFiber_nonempty_iff {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) (q : A → Bool) :
    (projectionFiber H A q).Nonempty ↔ q ∈ patternProjection H A := by
  constructor
  · rintro ⟨p, hp⟩
    exact (mem_patternProjection_iff H A q).2
      ⟨p, (mem_projectionFiber_iff H A q p).1 hp |>.1,
        (mem_projectionFiber_iff H A q p).1 hp |>.2⟩
  · intro hq
    obtain ⟨p, hpH, hpq⟩ := (mem_patternProjection_iff H A q).1 hq
    exact ⟨p, (mem_projectionFiber_iff H A q p).2 ⟨hpH, hpq⟩⟩

/-- Fibres over distinct projected patterns are disjoint. -/
theorem projectionFiber_disjoint {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) {q r : A → Bool} (hqr : q ≠ r) :
    Disjoint (projectionFiber H A q) (projectionFiber H A r) := by
  rw [Finset.disjoint_left]
  intro p hpq hpr
  have hpq' := ((mem_projectionFiber_iff H A q p).1 hpq).2
  have hpr' := ((mem_projectionFiber_iff H A r p).1 hpr).2
  exact hqr (hpq'.symm.trans hpr')

/-- The projection fibres partition the original family, with multiplicity retained by their
cardinalities. -/
theorem sum_projectionFiber_card {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) :
    ∑ q ∈ patternProjection H A, (projectionFiber H A q).card = H.card := by
  symm
  exact Finset.card_eq_sum_card_fiberwise fun p hp ↦
    Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- Restricting to fewer coordinates factors through the larger projection. -/
theorem restrictPattern_restrict {m : ℕ} {A B : Finset (Fin m)} (hAB : A ⊆ B)
    (p : Fin m → Bool) :
    restrictPattern A p = fun i : A ↦ restrictPattern B p ⟨i.1, hAB i.property⟩ := by
  rfl

/-- Coordinate projection cannot increase finite Boolean VC dimension. -/
theorem patternProjection_boolVCDim_le {m : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) :
    (patternProjection H A).boolVCDim ≤ H.boolVCDim := by
  unfold Finset.boolVCDim
  apply Finset.sup_le
  intro T hT
  have hTsh : (boolFamilyToFinsetFamily (patternProjection H A)).Shatters T :=
    Finset.mem_shatterer.mp hT
  let Tval : Finset (Fin m) := T.map ⟨Subtype.val, Subtype.val_injective⟩
  have hTval_card : Tval.card = T.card := Finset.card_map _
  have hTval_sh : (boolFamilyToFinsetFamily H).Shatters Tval := by
    intro U hUT
    let Usub : Finset A := U.preimage (fun i : A ↦ (i : Fin m))
      (Set.injOn_of_injective Subtype.val_injective)
    have hUsubT : Usub ⊆ T := by
      intro i hi
      have hiU : (i : Fin m) ∈ U := by
        simpa [Usub] using hi
      have hiTval : (i : Fin m) ∈ Tval := hUT hiU
      simpa [Tval] using hiTval
    obtain ⟨V, hVproj, hTV⟩ := hTsh hUsubT
    rw [boolFamilyToFinsetFamily, Finset.mem_image] at hVproj
    obtain ⟨q, hqproj, rfl⟩ := hVproj
    obtain ⟨p, hpH, hpq⟩ := (mem_patternProjection_iff H A q).1 hqproj
    refine ⟨Finset.univ.filter (fun i ↦ p i = true), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, hpH, rfl⟩
    · ext x
      constructor
      · intro hx
        have hxTval : x ∈ Tval := (Finset.mem_inter.1 hx).1
        simp only [Tval, Finset.mem_map] at hxTval
        obtain ⟨i, hiT, rfl⟩ := hxTval
        have hiTV : i ∈ T ∩ Finset.univ.filter (fun j ↦ q j = true) := by
          refine Finset.mem_inter.mpr ⟨hiT, ?_⟩
          have hip : p i = true := by simpa using (Finset.mem_inter.1 hx).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← congr_fun hpq i]
          exact hip
        have hiUsub : i ∈ Usub := by
          rw [← hTV]
          exact hiTV
        simpa [Usub] using hiUsub
      · intro hxU
        have hxTval : x ∈ Tval := hUT hxU
        simp only [Tval, Finset.mem_map] at hxTval
        obtain ⟨i, hiT, rfl⟩ := hxTval
        have hiUsub : i ∈ Usub := by simpa [Usub] using hxU
        have hiTV : i ∈ T ∩ Finset.univ.filter (fun j ↦ q j = true) := by
          rw [hTV]
          exact hiUsub
        refine Finset.mem_inter.mpr ⟨by simpa [Tval] using hiT, ?_⟩
        have hiq : q i = true := by simpa using (Finset.mem_inter.1 hiTV).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (congr_fun hpq i).trans hiq
  rw [← hTval_card]
  exact hTval_sh.card_le_vcDim

/-- Sauer--Shelah bound for the number of distinct coordinate projections. -/
theorem patternProjection_card_le_sauer {m v : ℕ} (H : Finset (Fin m → Bool))
    (A : Finset (Fin m)) (hVC : H.boolVCDim ≤ v) :
    (patternProjection H A).card ≤ ∑ i ∈ Finset.Iic v, A.card.choose i := by
  calc
    (patternProjection H A).card
        = (boolFamilyToFinsetFamily (patternProjection H A)).card := by
          symm
          apply Finset.card_image_of_injective
          intro f g hfg
          funext i
          have hi := Finset.ext_iff.mp hfg i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          cases hfi : f i <;> cases hgi : g i <;> simp_all
    _ ≤ (boolFamilyToFinsetFamily (patternProjection H A)).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ i ∈ Finset.Iic (patternProjection H A).boolVCDim,
        (Fintype.card A).choose i := Finset.card_shatterer_le_sum_vcDim
    _ = ∑ i ∈ Finset.Iic (patternProjection H A).boolVCDim, A.card.choose i := by
      rw [Fintype.card_coe]
    _ ≤ ∑ i ∈ Finset.Iic v, A.card.choose i := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.Iic_subset_Iic.mpr ((patternProjection_boolVCDim_le H A).trans hVC)

/-! ## One-inclusion edges -/

/-- Downward-oriented edges of a set family inside a finite coordinate set.  An element
`(s, a)` records the cube edge from `s` to `s.erase a`; hence every undirected unit edge is
represented exactly once. -/
def downEdges {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒜 : Finset (Finset α)) : Finset (Finset α × α) :=
  (𝒜 ×ˢ U).filter fun e ↦ e.2 ∈ e.1 ∧ e.1.erase e.2 ∈ 𝒜

@[simp]
theorem mem_downEdges_iff {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒜 : Finset (Finset α)) (s : Finset α) (a : α) :
    (s, a) ∈ downEdges U 𝒜 ↔ s ∈ 𝒜 ∧ a ∈ U ∧ a ∈ s ∧ s.erase a ∈ 𝒜 := by
  simp [downEdges, and_assoc]

theorem downEdges_mono {α : Type*} [DecidableEq α] {U V : Finset α}
    {𝒜 ℬ : Finset (Finset α)} (hUV : U ⊆ V) (h𝒜ℬ : 𝒜 ⊆ ℬ) :
    downEdges U 𝒜 ⊆ downEdges V ℬ := by
  intro e he
  obtain ⟨s, a⟩ := e
  rw [mem_downEdges_iff] at he ⊢
  exact ⟨h𝒜ℬ he.1, hUV he.2.1, he.2.2.1, h𝒜ℬ he.2.2.2⟩

theorem downEdges_inter {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒜 ℬ : Finset (Finset α)) :
    downEdges U (𝒜 ∩ ℬ) = downEdges U 𝒜 ∩ downEdges U ℬ := by
  ext e
  obtain ⟨s, a⟩ := e
  simp only [mem_downEdges_iff, Finset.mem_inter]
  aesop

theorem downEdges_union_superset {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒜 ℬ : Finset (Finset α)) :
    downEdges U 𝒜 ∪ downEdges U ℬ ⊆ downEdges U (𝒜 ∪ ℬ) := by
  intro e he
  obtain ⟨s, a⟩ := e
  simp only [Finset.mem_union, mem_downEdges_iff] at he ⊢
  rcases he with he | he
  · exact ⟨Or.inl he.1, he.2.1, he.2.2.1, Or.inl he.2.2.2⟩
  · exact ⟨Or.inr he.1, he.2.1, he.2.2.1, Or.inr he.2.2.2⟩

/-- Edge counts are submodular under union/intersection. -/
theorem card_downEdges_add_card_downEdges_le_union_add_inter {α : Type*}
    [DecidableEq α] (U : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    (downEdges U 𝒜).card + (downEdges U ℬ).card ≤
      (downEdges U (𝒜 ∪ ℬ)).card + (downEdges U (𝒜 ∩ ℬ)).card := by
  rw [downEdges_inter]
  rw [← Finset.card_union_add_card_inter]
  exact Nat.add_le_add_right
    (Finset.card_le_card (downEdges_union_superset U 𝒜 ℬ)) _

private def liftDownEdge {α : Type*} [DecidableEq α] (a : α) :
    Finset α × α → Finset α × α :=
  fun e ↦ (insert a e.1, e.2)

private def verticalDownEdge {α : Type*} [DecidableEq α] (a : α) :
    Finset α → Finset α × α :=
  fun s ↦ (insert a s, a)

/-- Edges in the layer not containing `a` are exactly the corresponding edges of the
non-member section. -/
private theorem downEdges_nonMemberSubfamily {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (_haU : a ∉ U) (𝒜 : Finset (Finset α)) :
    downEdges U (𝒜.nonMemberSubfamily a) =
      (downEdges (insert a U) 𝒜).filter (fun e ↦ a ∉ e.1) := by
  ext e
  obtain ⟨s, b⟩ := e
  simp only [mem_downEdges_iff, Finset.mem_nonMemberSubfamily, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hs𝒜, has⟩, hbU, hbs, ⟨herase, _⟩⟩
    exact ⟨⟨hs𝒜, by simp [hbU], hbs, herase⟩, has⟩
  · rintro ⟨⟨hs𝒜, hbU, hbs, herase⟩, has⟩
    have hba : b ≠ a := by
      intro hba
      subst b
      exact has hbs
    have hbU' : b ∈ U := by simpa [_haU, hba] using hbU
    exact ⟨⟨hs𝒜, has⟩, hbU', hbs, ⟨herase, by simp [Finset.mem_erase, has]⟩⟩

/-- Non-vertical edges in the layer containing `a` are the lifted edges of the member section. -/
private theorem image_downEdges_memberSubfamily {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (haU : a ∉ U) (𝒜 : Finset (Finset α)) :
    (downEdges U (𝒜.memberSubfamily a)).image (liftDownEdge a) =
      (downEdges (insert a U) 𝒜).filter (fun e ↦ a ∈ e.1 ∧ e.2 ≠ a) := by
  ext e
  obtain ⟨s, b⟩ := e
  rw [Finset.mem_image]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨r, c⟩, he, h⟩
    rw [mem_downEdges_iff] at he
    rw [Finset.mem_memberSubfamily] at he
    rw [Finset.mem_memberSubfamily] at he
    change (insert a r, c) = (s, b) at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨hr𝒜, har⟩, hcU, hcr, ⟨herase, haerase⟩⟩ := he
    have hca : c ≠ a := fun hca ↦ haU (hca ▸ hcU)
    refine ⟨?_, by simp [hca]⟩
    rw [mem_downEdges_iff]
    refine ⟨hr𝒜, by simp [hcU], by simp [hcr, hca], ?_⟩
    rw [Finset.erase_insert_of_ne hca.symm]
    exact herase
  · rintro ⟨hedge, has, hba⟩
    rw [mem_downEdges_iff] at hedge
    obtain ⟨hs𝒜, hbU, hbs, herase⟩ := hedge
    let r := s.erase a
    have har : a ∉ r := Finset.notMem_erase _ _
    have hsr : insert a r = s := Finset.insert_erase has
    have hbU' : b ∈ U := by simpa [haU, hba] using hbU
    have hbr : b ∈ r := by simp [r, Finset.mem_erase, hba, hbs]
    refine ⟨(r, b), ?_, ?_⟩
    · rw [mem_downEdges_iff]
      rw [Finset.mem_memberSubfamily]
      refine ⟨⟨by simpa [hsr] using hs𝒜, har⟩, hbU', hbr, ?_⟩
      rw [Finset.mem_memberSubfamily]
      refine ⟨?_, by simp [r, Finset.mem_erase]⟩
      rw [← Finset.erase_insert_of_ne hba.symm, hsr]
      exact herase
    · simp [liftDownEdge, hsr]

/-- Vertical `a`-edges are indexed by the intersection of the two sections. -/
private theorem image_inter_sections_vertical {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (𝒜 : Finset (Finset α)) :
    ((𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a).image (verticalDownEdge a)) =
      (downEdges (insert a U) 𝒜).filter (fun e ↦ e.2 = a) := by
  ext e
  obtain ⟨s, b⟩ := e
  rw [Finset.mem_image]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨r, hr, h⟩
    rw [Finset.mem_inter, Finset.mem_nonMemberSubfamily,
      Finset.mem_memberSubfamily] at hr
    change (insert a r, a) = (s, b) at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨hr𝒜, har⟩, hins𝒜, -⟩ := hr
    refine ⟨?_, rfl⟩
    rw [mem_downEdges_iff]
    exact ⟨hins𝒜, by simp, by simp,
      by simpa [Finset.erase_insert, har] using hr𝒜⟩
  · rintro ⟨hedge, hba⟩
    subst b
    rw [mem_downEdges_iff] at hedge
    obtain ⟨hs𝒜, -, has, herase⟩ := hedge
    refine ⟨s.erase a, ?_, ?_⟩
    · rw [Finset.mem_inter, Finset.mem_nonMemberSubfamily,
        Finset.mem_memberSubfamily]
      exact ⟨⟨herase, Finset.notMem_erase _ _⟩,
        by simpa [Finset.insert_erase has] using hs𝒜, Finset.notMem_erase _ _⟩
    · simp [verticalDownEdge, Finset.insert_erase has]

private theorem liftDownEdge_injOn_memberSection {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (liftDownEdge a) (downEdges U (𝒜.memberSubfamily a)) := by
  rintro ⟨s, b⟩ hs ⟨t, c⟩ ht h
  change (s, b) ∈ downEdges U (𝒜.memberSubfamily a) at hs
  change (t, c) ∈ downEdges U (𝒜.memberSubfamily a) at ht
  rw [mem_downEdges_iff] at hs ht
  have has : a ∉ s := (Finset.mem_memberSubfamily.1 hs.1).2
  have hat : a ∉ t := (Finset.mem_memberSubfamily.1 ht.1).2
  change (insert a s, b) = (insert a t, c) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hst, rfl⟩ := h
  have hst' : s = t := by
    have := congr_arg (fun r : Finset α ↦ r.erase a) hst
    simpa [Finset.erase_insert has, Finset.erase_insert hat] using this
  subst t
  rfl

private theorem verticalDownEdge_injOn_sections {α : Type*} [DecidableEq α]
    (a : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (verticalDownEdge a)
      (↑(𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a) : Set (Finset α)) := by
  intro s hs t ht h
  change s ∈ 𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a at hs
  change t ∈ 𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a at ht
  have has : a ∉ s := (Finset.mem_nonMemberSubfamily.1 (Finset.mem_inter.1 hs).1).2
  have hat : a ∉ t := (Finset.mem_nonMemberSubfamily.1 (Finset.mem_inter.1 ht).1).2
  change (insert a s, a) = (insert a t, a) at h
  have hst : insert a s = insert a t := congr_arg Prod.fst h
  have := congr_arg (fun r : Finset α ↦ r.erase a) hst
  simpa [Finset.erase_insert has, Finset.erase_insert hat] using this

/-- Exact coordinate-section recurrence for downward cube edges. -/
private theorem card_downEdges_insert_eq_sections {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (haU : a ∉ U) (𝒜 : Finset (Finset α)) :
    (downEdges (insert a U) 𝒜).card =
      (downEdges U (𝒜.nonMemberSubfamily a)).card +
        (downEdges U (𝒜.memberSubfamily a)).card +
          (𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a).card := by
  let E := downEdges (insert a U) 𝒜
  let E₀ := E.filter (fun e ↦ a ∉ e.1)
  let E₁ := E.filter (fun e ↦ a ∈ e.1 ∧ e.2 ≠ a)
  let Evertical := E.filter (fun e ↦ e.2 = a)
  have hpartition : E₀ ∪ E₁ ∪ Evertical = E := by
    ext e
    obtain ⟨s, b⟩ := e
    simp only [E₀, E₁, Evertical, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨he, -⟩ | ⟨he, -⟩) | ⟨he, -⟩) <;> exact he
    · intro he
      by_cases has : a ∈ s
      · by_cases hba : b = a
        · exact Or.inr ⟨he, hba⟩
        · exact Or.inl (Or.inr ⟨he, has, hba⟩)
      · exact Or.inl (Or.inl ⟨he, has⟩)
  have hdisjoint₀₁ : Disjoint E₀ E₁ := by
    rw [Finset.disjoint_left]
    rintro ⟨s, b⟩ hs ht
    exact (Finset.mem_filter.1 hs).2 (Finset.mem_filter.1 ht).2.1
  have hdisjoint_vertical : Disjoint (E₀ ∪ E₁) Evertical := by
    rw [Finset.disjoint_left]
    rintro ⟨s, b⟩ hs ht
    rcases Finset.mem_union.1 hs with hs | hs
    · have has : a ∈ s := by
        have he := (Finset.mem_filter.1 ht).1
        have hbs := (mem_downEdges_iff _ _ s b).1 he |>.2.2.1
        exact (Finset.mem_filter.1 ht).2 ▸ hbs
      exact (Finset.mem_filter.1 hs).2 has
    · exact (Finset.mem_filter.1 hs).2.2 (Finset.mem_filter.1 ht).2
  have hcard_partition : E.card = E₀.card + E₁.card + Evertical.card := by
    rw [← hpartition, Finset.card_union_of_disjoint hdisjoint_vertical,
      Finset.card_union_of_disjoint hdisjoint₀₁]
  have hcard₀ : E₀.card = (downEdges U (𝒜.nonMemberSubfamily a)).card := by
    rw [downEdges_nonMemberSubfamily U a haU 𝒜]
  have hcard₁ : E₁.card = (downEdges U (𝒜.memberSubfamily a)).card := by
    change ((downEdges (insert a U) 𝒜).filter
      (fun e ↦ a ∈ e.1 ∧ e.2 ≠ a)).card = _
    rw [← image_downEdges_memberSubfamily U a haU 𝒜,
      Finset.card_image_of_injOn (liftDownEdge_injOn_memberSection U a 𝒜)]
  have hcard_vertical : Evertical.card =
      (𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a).card := by
    change ((downEdges (insert a U) 𝒜).filter (fun e ↦ e.2 = a)).card = _
    rw [← image_inter_sections_vertical U a 𝒜,
      Finset.card_image_of_injOn (verticalDownEdge_injOn_sections a 𝒜)]
  rw [hcard₀, hcard₁, hcard_vertical] at hcard_partition
  simpa only [E] using hcard_partition

private theorem section_union_shatters_lift {α : Type*} [DecidableEq α]
    {U : Finset α} {a : α} (haU : a ∉ U) {𝒜 : Finset (Finset α)}
    (hsupport : ∀ s ∈ 𝒜, s ⊆ insert a U) {S : Finset α}
    (hS : (𝒜.nonMemberSubfamily a ∪ 𝒜.memberSubfamily a).Shatters S) :
    𝒜.Shatters S := by
  have hsection_support : ∀ r ∈ 𝒜.nonMemberSubfamily a ∪ 𝒜.memberSubfamily a, r ⊆ U := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have hr' := Finset.mem_nonMemberSubfamily.1 hr
      intro x hx
      have hx' := hsupport r hr'.1 hx
      have hxa : x ≠ a := fun hxa ↦ hr'.2 (hxa ▸ hx)
      simpa [haU, hxa] using hx'
    · have hr' := Finset.mem_memberSubfamily.1 hr
      intro x hx
      have hx' := hsupport (insert a r) hr'.1 (Finset.mem_insert_of_mem hx)
      have hxa : x ≠ a := fun hxa ↦ hr'.2 (hxa ▸ hx)
      simpa [haU, hxa] using hx'
  have hSU : S ⊆ U := by
    obtain ⟨r, hr, hSr⟩ := hS.exists_superset
    exact hSr.trans (hsection_support r hr)
  have haS : a ∉ S := fun haS ↦ haU (hSU haS)
  intro T hTS
  obtain ⟨r, hr, hSrT⟩ := hS hTS
  rcases Finset.mem_union.1 hr with hr | hr
  · exact ⟨r, (Finset.mem_nonMemberSubfamily.1 hr).1, hSrT⟩
  · have hr' := Finset.mem_memberSubfamily.1 hr
    refine ⟨insert a r, hr'.1, ?_⟩
    simpa [Finset.inter_insert_of_notMem haS] using hSrT

private theorem section_inter_shatters_insert {α : Type*} [DecidableEq α]
    {a : α} {𝒜 : Finset (Finset α)} {S : Finset α}
    (hS : (𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a).Shatters S) :
    𝒜.Shatters (insert a S) := by
  intro T hT
  let T₀ := T.erase a
  have hT₀S : T₀ ⊆ S := by
    intro x hx
    have hxT : x ∈ T := Finset.mem_of_mem_erase hx
    have hxinsert : x ∈ insert a S := hT hxT
    have hxa : x ≠ a := (Finset.mem_erase.1 hx).1
    simpa [hxa] using hxinsert
  obtain ⟨r, hr, hSr⟩ := hS hT₀S
  have hr₀ := Finset.mem_nonMemberSubfamily.1 (Finset.mem_inter.1 hr).1
  have hr₁ := Finset.mem_memberSubfamily.1 (Finset.mem_inter.1 hr).2
  by_cases haT : a ∈ T
  · refine ⟨insert a r, hr₁.1, ?_⟩
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haT]
    · have hxSr : x ∈ S ∩ r ↔ x ∈ T₀ := Finset.ext_iff.mp hSr x
      have hxT₀T : x ∈ T₀ ↔ x ∈ T := by simp [T₀, hxa]
      simpa [hxa] using hxSr.trans hxT₀T
  · refine ⟨r, hr₀.1, ?_⟩
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haT, hr₀.2]
    · have hxSr : x ∈ S ∩ r ↔ x ∈ T₀ := Finset.ext_iff.mp hSr x
      have hxT₀T : x ∈ T₀ ↔ x ∈ T := by simp [T₀, hxa]
      simpa [hxa] using hxSr.trans hxT₀T

/-- The one-inclusion graph of a VC-`v` set family has at most `v |𝒜|` undirected edges. -/
private theorem card_downEdges_le_mul_card_of_shatters {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (v : ℕ)
    (hsupport : ∀ s ∈ 𝒜, s ⊆ U)
    (hvc : ∀ S : Finset α, 𝒜.Shatters S → S.card ≤ v) :
    (downEdges U 𝒜).card ≤ v * 𝒜.card := by
  induction U using Finset.induction generalizing 𝒜 v with
  | empty => simp [downEdges]
  | @insert a U haU ih =>
      let 𝒜₀ := 𝒜.nonMemberSubfamily a
      let 𝒜₁ := 𝒜.memberSubfamily a
      let 𝒢 := 𝒜₀ ∪ 𝒜₁
      let ℐ := 𝒜₀ ∩ 𝒜₁
      have hsupport₀ : ∀ s ∈ 𝒜₀, s ⊆ U := by
        intro s hs x hx
        have hs' := Finset.mem_nonMemberSubfamily.1 hs
        have hx' := hsupport s hs'.1 hx
        have hxa : x ≠ a := fun hxa ↦ hs'.2 (hxa ▸ hx)
        simpa [haU, hxa] using hx'
      have hsupport₁ : ∀ s ∈ 𝒜₁, s ⊆ U := by
        intro s hs x hx
        have hs' := Finset.mem_memberSubfamily.1 hs
        have hx' := hsupport (insert a s) hs'.1 (Finset.mem_insert_of_mem hx)
        have hxa : x ≠ a := fun hxa ↦ hs'.2 (hxa ▸ hx)
        simpa [haU, hxa] using hx'
      have hsupport𝒢 : ∀ s ∈ 𝒢, s ⊆ U := by
        intro s hs
        rcases Finset.mem_union.1 hs with hs | hs
        · exact hsupport₀ s hs
        · exact hsupport₁ s hs
      have hsupportℐ : ∀ s ∈ ℐ, s ⊆ U := by
        intro s hs
        exact hsupport₀ s (Finset.mem_inter.1 hs).1
      have hvc𝒢 : ∀ S : Finset α, 𝒢.Shatters S → S.card ≤ v := by
        intro S hS
        exact hvc S (section_union_shatters_lift haU hsupport hS)
      have hedge_sections := card_downEdges_insert_eq_sections U a haU 𝒜
      have hedge_submod :=
        card_downEdges_add_card_downEdges_le_union_add_inter U 𝒜₀ 𝒜₁
      have hedge_submod' :
          (downEdges U 𝒜₀).card + (downEdges U 𝒜₁).card ≤
            (downEdges U 𝒢).card + (downEdges U ℐ).card := by
        simpa only [𝒢, ℐ] using hedge_submod
      have hcard_sections :=
        Finset.card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜
      have hcard_union_inter := Finset.card_union_add_card_inter 𝒜₀ 𝒜₁
      have hcard𝒢ℐ : 𝒢.card + ℐ.card = 𝒜.card := by
        calc
          𝒢.card + ℐ.card = 𝒜₀.card + 𝒜₁.card := hcard_union_inter
          _ = 𝒜₁.card + 𝒜₀.card := Nat.add_comm _ _
          _ = 𝒜.card := hcard_sections
      cases v with
      | zero =>
          have hℐempty : ℐ = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.2
            intro r hr
            have hℐnonempty : ℐ.Nonempty := ⟨r, hr⟩
            have hshEmpty : ℐ.Shatters ∅ := Finset.shatters_empty.2 hℐnonempty
            have hshSingleton : 𝒜.Shatters {a} := by
              simpa using section_inter_shatters_insert (a := a) (𝒜 := 𝒜)
                (S := ∅) hshEmpty
            have := hvc {a} hshSingleton
            simp at this
          have h𝒢 := ih 𝒢 0 hsupport𝒢 hvc𝒢
          have h𝒢zero : (downEdges U 𝒢).card = 0 := by omega
          have hℐzero : (downEdges U ℐ).card = 0 := by simp [hℐempty, downEdges]
          have hsumzero :
              (downEdges U 𝒜₀).card + (downEdges U 𝒜₁).card = 0 := by
            have : (downEdges U 𝒜₀).card + (downEdges U 𝒜₁).card ≤ 0 := by
              simpa [h𝒢zero, hℐzero] using hedge_submod'
            exact Nat.eq_zero_of_le_zero this
          calc
            (downEdges (insert a U) 𝒜).card =
                (downEdges U 𝒜₀).card + (downEdges U 𝒜₁).card + ℐ.card :=
              hedge_sections
            _ = 0 := by rw [hsumzero, hℐempty]; simp
            _ ≤ 0 * 𝒜.card := by simp
      | succ v =>
          have hvcℐ : ∀ S : Finset α, ℐ.Shatters S → S.card ≤ v := by
            intro S hS
            have hSU : S ⊆ U := by
              obtain ⟨r, hr, hSr⟩ := hS.exists_superset
              exact hSr.trans (hsupportℐ r hr)
            have haS : a ∉ S := fun haS ↦ haU (hSU haS)
            have hins := section_inter_shatters_insert (a := a) (𝒜 := 𝒜) hS
            have hbound := hvc (insert a S) hins
            rw [Finset.card_insert_of_notMem haS] at hbound
            omega
          have h𝒢 := ih 𝒢 (v + 1) hsupport𝒢 hvc𝒢
          have hℐ := ih ℐ v hsupportℐ hvcℐ
          calc
            (downEdges (insert a U) 𝒜).card =
                (downEdges U 𝒜₀).card + (downEdges U 𝒜₁).card + ℐ.card :=
              hedge_sections
            _ ≤ (downEdges U 𝒢).card + (downEdges U ℐ).card + ℐ.card :=
              Nat.add_le_add_right hedge_submod' _
            _ ≤ (v + 1) * 𝒢.card + v * ℐ.card + ℐ.card := by
              exact Nat.add_le_add (Nat.add_le_add h𝒢 hℐ) le_rfl
            _ = (v + 1) * (𝒢.card + ℐ.card) := by ring
            _ = (v + 1) * 𝒜.card := by rw [hcard𝒢ℐ]

/-- Standard VC-dimension form of the one-inclusion edge bound. -/
theorem card_downEdges_le_vcDim_mul_card {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α))
    (hsupport : ∀ s ∈ 𝒜, s ⊆ U) :
    (downEdges U 𝒜).card ≤ 𝒜.vcDim * 𝒜.card := by
  exact card_downEdges_le_mul_card_of_shatters U 𝒜 𝒜.vcDim hsupport
    (fun _ hS ↦ hS.card_le_vcDim)

/-! ## Weighted one-inclusion estimate -/

def edgeLower {α : Type*} [DecidableEq α] (e : Finset α × α) : Finset α :=
  e.1.erase e.2

private def incidentDownEdges {α : Type*} [DecidableEq α] (U : Finset α)
    (𝒜 : Finset (Finset α)) (s : Finset α) : Finset (Finset α × α) :=
  (downEdges U 𝒜).filter fun e ↦ e.1 = s ∨ edgeLower e = s

@[simp]
private theorem mem_incidentDownEdges_iff {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (s : Finset α) (e : Finset α × α) :
    e ∈ incidentDownEdges U 𝒜 s ↔
      e ∈ downEdges U 𝒜 ∧ (e.1 = s ∨ edgeLower e = s) := by
  simp [incidentDownEdges]

private theorem downEdge_endpoints_ne {α : Type*} [DecidableEq α]
    {U : Finset α} {𝒜 : Finset (Finset α)} {e : Finset α × α}
    (he : e ∈ downEdges U 𝒜) : e.1 ≠ edgeLower e := by
  intro h
  have hmem : e.2 ∈ e.1 := by
    obtain ⟨s, a⟩ := e
    exact ((mem_downEdges_iff U 𝒜 s a).1 he).2.2.1
  have hnot : e.2 ∉ edgeLower e := by simp [edgeLower]
  exact hnot (h ▸ hmem)

private theorem sum_card_incidentDownEdges {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) :
    ∑ s ∈ 𝒜, (incidentDownEdges U 𝒜 s).card = 2 * (downEdges U 𝒜).card := by
  classical
  simp only [incidentDownEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hrhs : 2 * ∑ _x ∈ downEdges U 𝒜, 1 = ∑ _x ∈ downEdges U 𝒜, 2 := by
    simp [Finset.sum_const, Nat.mul_comm]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨s, a⟩ := e
  have he' := (mem_downEdges_iff U 𝒜 s a).1 he
  have hlower : s.erase a ∈ 𝒜 := he'.2.2.2
  have hne : s ≠ s.erase a := downEdge_endpoints_ne he
  change (∑ x ∈ 𝒜, if s = x ∨ edgeLower (s, a) = x then 1 else 0) = 2
  rw [show edgeLower (s, a) = s.erase a by rfl]
  calc
    (∑ x ∈ 𝒜, if s = x ∨ s.erase a = x then 1 else 0) =
        ∑ x ∈ 𝒜, ((if s = x then 1 else 0) +
          (if s.erase a = x then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hsx : s = x
      · have hax : a ∈ x := hsx ▸ he'.2.2.1
        simp [hsx, hax]
      · by_cases hlx : s.erase a = x <;> simp [hsx, hlx]
    _ = (∑ x ∈ 𝒜, if s = x then 1 else 0) +
        (∑ x ∈ 𝒜, if s.erase a = x then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = 2 := by simp [he'.1, hlower]

private theorem exists_incidentDownEdges_card_le_two_mul {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) {v : ℕ} (h𝒜 : 𝒜.Nonempty)
    (hsupport : ∀ s ∈ 𝒜, s ⊆ U)
    (hvc : ∀ S : Finset α, 𝒜.Shatters S → S.card ≤ v) :
    ∃ s ∈ 𝒜, (incidentDownEdges U 𝒜 s).card ≤ 2 * v := by
  have hedge := card_downEdges_le_mul_card_of_shatters U 𝒜 v hsupport hvc
  have hsum :
      ∑ s ∈ 𝒜, (incidentDownEdges U 𝒜 s).card ≤ ∑ _s ∈ 𝒜, 2 * v := by
    rw [sum_card_incidentDownEdges]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      2 * (downEdges U 𝒜).card ≤ 2 * (v * 𝒜.card) := Nat.mul_le_mul_left 2 hedge
      _ = 𝒜.card * (2 * v) := by ring
  exact Finset.exists_le_of_sum_le h𝒜 hsum

private theorem downEdges_erase_eq_filter_not_incident {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    downEdges U (𝒜.erase s) =
      (downEdges U 𝒜).filter (fun e ↦ ¬(e.1 = s ∨ edgeLower e = s)) := by
  ext e
  obtain ⟨t, a⟩ := e
  rw [mem_downEdges_iff, Finset.mem_filter, mem_downEdges_iff]
  simp only [Finset.mem_erase, edgeLower]
  constructor
  · rintro ⟨⟨hts, ht𝒜⟩, haU, hat, ⟨hlowers, hlower𝒜⟩⟩
    exact ⟨⟨ht𝒜, haU, hat, hlower𝒜⟩, fun h ↦ h.elim hts hlowers⟩
  · rintro ⟨⟨ht𝒜, haU, hat, hlower𝒜⟩, hnot⟩
    have hts : t ≠ s := fun hts ↦ hnot (Or.inl hts)
    have hlowers : t.erase a ≠ s := fun hlowers ↦ hnot (Or.inr hlowers)
    exact ⟨⟨hts, ht𝒜⟩, haU, hat, ⟨hlowers, hlower𝒜⟩⟩

/-- Weighted one-inclusion inequality for a family whose shattered sets have size at most `v`.
The weight of an edge is the smaller weight of its endpoints, exactly as required for projection
fibres in Haussler's argument. -/
theorem weighted_downEdges_le_two_mul_vc {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (v : ℕ) (w : Finset α → ℕ)
    (hsupport : ∀ s ∈ 𝒜, s ⊆ U)
    (hvc : ∀ S : Finset α, 𝒜.Shatters S → S.card ≤ v) :
    (∑ e ∈ downEdges U 𝒜, min (w e.1) (w (edgeLower e))) ≤
      2 * v * ∑ s ∈ 𝒜, w s := by
  induction hcard : 𝒜.card using Nat.strong_induction_on generalizing 𝒜
  rename_i n ih
  by_cases h𝒜empty : 𝒜 = ∅
  · simp [h𝒜empty, downEdges]
  · have h𝒜nonempty : 𝒜.Nonempty := Finset.nonempty_iff_ne_empty.2 h𝒜empty
    obtain ⟨t, ht, hdegree⟩ := exists_incidentDownEdges_card_le_two_mul
      U 𝒜 h𝒜nonempty hsupport hvc
    let ℬ := 𝒜.erase t
    have hℬsubset : ℬ ⊆ 𝒜 := Finset.erase_subset _ _
    have hℬlt : ℬ.card < n := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem ht
    have hsupportℬ : ∀ r ∈ ℬ, r ⊆ U := by
      intro r hr
      exact hsupport r (hℬsubset hr)
    have hvcℬ : ∀ S : Finset α, ℬ.Shatters S → S.card ≤ v := by
      intro S hS
      exact hvc S (hS.mono_left hℬsubset)
    have hℬweight_sum : ∑ r ∈ 𝒜, w r = w t + ∑ r ∈ ℬ, w r := by
      rw [← Finset.sum_erase_add _ _ ht, add_comm]
    have hnonincident :
        ∑ e ∈ (downEdges U 𝒜).filter
            (fun e ↦ ¬(e.1 = t ∨ edgeLower e = t)),
            min (w e.1) (w (edgeLower e)) =
          ∑ e ∈ downEdges U ℬ, min (w e.1) (w (edgeLower e)) := by
      rw [downEdges_erase_eq_filter_not_incident]
    have hincident :
        ∑ e ∈ incidentDownEdges U 𝒜 t,
            min (w e.1) (w (edgeLower e)) ≤
          2 * v * w t := by
      calc
        (∑ e ∈ incidentDownEdges U 𝒜 t,
            min (w e.1) (w (edgeLower e))) ≤
            ∑ _e ∈ incidentDownEdges U 𝒜 t, w t := by
          apply Finset.sum_le_sum
          intro e he
          have hinc := (mem_incidentDownEdges_iff U 𝒜 t e).1 he |>.2
          rcases hinc with hupper | hlower
          · rw [hupper]
            exact min_le_left (w t) (w (edgeLower e))
          · rw [hlower]
            exact min_le_right (w e.1) (w t)
        _ = (incidentDownEdges U 𝒜 t).card * w t := by
          simp [Finset.sum_const]
        _ ≤ (2 * v) * w t := Nat.mul_le_mul_right _ hdegree
        _ = 2 * v * w t := rfl
    have hweightedℬ := ih ℬ.card hℬlt ℬ hsupportℬ hvcℬ rfl
    have hpartition :
        ∑ e ∈ downEdges U 𝒜, min (w e.1) (w (edgeLower e)) =
          (∑ e ∈ (downEdges U 𝒜).filter
              (fun e ↦ ¬(e.1 = t ∨ edgeLower e = t)),
              min (w e.1) (w (edgeLower e))) +
            ∑ e ∈ incidentDownEdges U 𝒜 t,
              min (w e.1) (w (edgeLower e)) := by
      have hfilter_incident :
          (downEdges U 𝒜).filter
              (fun e ↦ ¬¬(e.1 = t ∨ edgeLower e = t)) =
            incidentDownEdges U 𝒜 t := by
        ext e
        rw [Finset.mem_filter, mem_incidentDownEdges_iff]
        constructor
        · rintro ⟨he, hnn⟩
          exact ⟨he, Classical.byContradiction hnn⟩
        · rintro ⟨he, hp⟩
          exact ⟨he, fun hnp ↦ hnp hp⟩
      rw [← hfilter_incident]
      exact (Finset.sum_filter_add_sum_filter_not
        (downEdges U 𝒜) (fun e ↦ ¬(e.1 = t ∨ edgeLower e = t))
          (fun e ↦ min (w e.1) (w (edgeLower e)))).symm
    rw [hpartition, hnonincident]
    calc
      (∑ e ∈ downEdges U ℬ, min (w e.1) (w (edgeLower e))) +
          ∑ e ∈ incidentDownEdges U 𝒜 t,
            min (w e.1) (w (edgeLower e)) ≤
          2 * v * (∑ r ∈ ℬ, w r) + 2 * v * w t := Nat.add_le_add hweightedℬ hincident
      _ = 2 * v * ∑ r ∈ 𝒜, w r := by rw [hℬweight_sum]; ring

/-! ## Set-family traces and fibre weights -/

/-- Trace of a set family on a finite coordinate set. -/
def traceFamily {α : Type*} [DecidableEq α] (𝒜 : Finset (Finset α))
    (S : Finset α) : Finset (Finset α) :=
  𝒜.image fun A ↦ S ∩ A

/-- Multiplicity of a trace pattern. -/
def traceFiber {α : Type*} [DecidableEq α] (𝒜 : Finset (Finset α))
    (S q : Finset α) : Finset (Finset α) :=
  𝒜.filter fun A ↦ S ∩ A = q

@[simp]
theorem mem_traceFamily_iff {α : Type*} [DecidableEq α] (𝒜 : Finset (Finset α))
    (S q : Finset α) :
    q ∈ traceFamily 𝒜 S ↔ ∃ A ∈ 𝒜, S ∩ A = q := by
  simp [traceFamily]

@[simp]
theorem mem_traceFiber_iff {α : Type*} [DecidableEq α] (𝒜 : Finset (Finset α))
    (S q A : Finset α) :
    A ∈ traceFiber 𝒜 S q ↔ A ∈ 𝒜 ∧ S ∩ A = q := by
  simp [traceFiber]

theorem sum_traceFiber_card {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) :
    ∑ q ∈ traceFamily 𝒜 S, (traceFiber 𝒜 S q).card = 𝒜.card := by
  symm
  exact Finset.card_eq_sum_card_image (fun A ↦ S ∩ A) 𝒜

theorem traceFamily_support {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) :
    ∀ q ∈ traceFamily 𝒜 S, q ⊆ S := by
  intro q hq
  obtain ⟨A, hA, rfl⟩ := (mem_traceFamily_iff 𝒜 S q).1 hq
  exact Finset.inter_subset_left

/-- A trace cannot shatter a larger set than the original family. -/
theorem traceFamily_shatters_lift {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S T : Finset α)
    (hT : (traceFamily 𝒜 S).Shatters T) : 𝒜.Shatters T := by
  have hTS : T ⊆ S := by
    obtain ⟨q, hq, hTq⟩ := hT.exists_superset
    exact hTq.trans (traceFamily_support 𝒜 S q hq)
  intro U hUT
  obtain ⟨q, hq, hTq⟩ := hT hUT
  obtain ⟨A, hA, hSAq⟩ := (mem_traceFamily_iff 𝒜 S q).1 hq
  refine ⟨A, hA, ?_⟩
  calc
    T ∩ A = T ∩ (S ∩ A) := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hxT, hxA⟩
        exact ⟨hxT, hTS hxT, hxA⟩
      · rintro ⟨hxT, hxS, hxA⟩
        exact ⟨hxT, hxA⟩
    _ = T ∩ q := by rw [hSAq]
    _ = U := hTq

/-- Weighted one-inclusion upper bound for the fibres of any coordinate trace. -/
theorem weighted_trace_downEdges_le_two_mul_vc {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (v : ℕ)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    (∑ e ∈ downEdges S (traceFamily 𝒜 S),
        min (traceFiber 𝒜 S e.1).card (traceFiber 𝒜 S (edgeLower e)).card) ≤
      2 * v * 𝒜.card := by
  have h := weighted_downEdges_le_two_mul_vc S (traceFamily 𝒜 S) v
    (fun q ↦ (traceFiber 𝒜 S q).card) (traceFamily_support 𝒜 S)
    (fun T hT ↦ hvc T (traceFamily_shatters_lift 𝒜 S T hT))
  simpa only [sum_traceFiber_card] using h

/-! ## Ordered-pair Hamming double counting -/

/-- Hamming distance of two finite sets, restricted to a finite coordinate set. -/
def finsetHamming {α : Type*} [DecidableEq α]
    (U A B : Finset α) : ℕ :=
  (U.filter fun a ↦ (a ∈ A) ≠ (a ∈ B)).card

/-- Ordered pairs in `𝒜` that disagree at coordinate `a`. -/
def crossingPairs {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (a : α) : Finset (Finset α × Finset α) :=
  ((𝒜.filter fun A ↦ a ∈ A) ×ˢ (𝒜.filter fun A ↦ a ∉ A)) ∪
    ((𝒜.filter fun A ↦ a ∉ A) ×ˢ (𝒜.filter fun A ↦ a ∈ A))

@[simp]
theorem mem_crossingPairs_iff {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (a : α) (A B : Finset α) :
    (A, B) ∈ crossingPairs 𝒜 a ↔ A ∈ 𝒜 ∧ B ∈ 𝒜 ∧ ((a ∈ A) ≠ (a ∈ B)) := by
  simp only [crossingPairs, Finset.mem_union, Finset.mem_product, Finset.mem_filter]
  by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;> simp_all

theorem card_crossingPairs {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (a : α) :
    (crossingPairs 𝒜 a).card =
      2 * (𝒜.filter fun A ↦ a ∈ A).card * (𝒜.filter fun A ↦ a ∉ A).card := by
  let 𝒜₁ := 𝒜.filter fun A ↦ a ∈ A
  let 𝒜₀ := 𝒜.filter fun A ↦ a ∉ A
  have hdisjoint : Disjoint (𝒜₁ ×ˢ 𝒜₀) (𝒜₀ ×ˢ 𝒜₁) := by
    rw [Finset.disjoint_left]
    rintro ⟨A, B⟩ h10 h01
    have hA1 := (Finset.mem_filter.1 (Finset.mem_product.1 h10).1).2
    have hA0 := (Finset.mem_filter.1 (Finset.mem_product.1 h01).1).2
    exact hA0 hA1
  rw [crossingPairs, Finset.card_union_of_disjoint hdisjoint]
  simp only [Finset.card_product]
  dsimp [𝒜₁, 𝒜₀]
  ring

/-- Summing Hamming distances over ordered distinct pairs is the same as summing coordinate
crossing counts. -/
theorem sum_offDiag_finsetHamming {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) :
    ∑ e ∈ 𝒜.offDiag, finsetHamming U e.1 e.2 =
      ∑ a ∈ U, (crossingPairs 𝒜 a).card := by
  classical
  simp only [finsetHamming, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a haU
  rw [show (∑ e ∈ 𝒜.offDiag, if (a ∈ e.1) ≠ (a ∈ e.2) then 1 else 0) =
      (crossingPairs 𝒜 a).card by
    rw [← Finset.card_filter]
    congr 1
    ext e
    obtain ⟨A, B⟩ := e
    simp only [Finset.mem_filter, Finset.mem_offDiag, mem_crossingPairs_iff]
    constructor
    · rintro ⟨⟨hA, hB, hAB⟩, hdiff⟩
      exact ⟨hA, hB, hdiff⟩
    · rintro ⟨hA, hB, hdiff⟩
      exact ⟨⟨hA, hB, fun hAB ↦ by subst B; exact hdiff rfl⟩, hdiff⟩]
  simp

/-- A separated finite set family has large total split-min mass across coordinates. -/
theorem separated_family_splitMin_lower {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (δ : ℕ)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B) :
    δ * (𝒜.card - 1) ≤
      2 * ∑ a ∈ U,
        min (𝒜.filter fun A ↦ a ∈ A).card (𝒜.filter fun A ↦ a ∉ A).card := by
  by_cases h𝒜empty : 𝒜 = ∅
  · simp [h𝒜empty]
  have h𝒜pos : 0 < 𝒜.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.2 h𝒜empty)
  have hsepSum : 𝒜.offDiag.card * δ ≤
      ∑ e ∈ 𝒜.offDiag, finsetHamming U e.1 e.2 := by
    calc
      𝒜.offDiag.card * δ = ∑ _e ∈ 𝒜.offDiag, δ := by
        simp [Finset.sum_const]
      _ ≤ ∑ e ∈ 𝒜.offDiag, finsetHamming U e.1 e.2 := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨A, B⟩ := e
        have he' := Finset.mem_offDiag.1 he
        exact hsep A he'.1 B he'.2.1 he'.2.2
  have hcross_le :
      ∑ a ∈ U, (crossingPairs 𝒜 a).card ≤
        𝒜.card * (2 * ∑ a ∈ U,
          min (𝒜.filter fun A ↦ a ∈ A).card
            (𝒜.filter fun A ↦ a ∉ A).card) := by
    calc
      (∑ a ∈ U, (crossingPairs 𝒜 a).card) =
          ∑ a ∈ U, 2 * (𝒜.filter fun A ↦ a ∈ A).card *
            (𝒜.filter fun A ↦ a ∉ A).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact card_crossingPairs 𝒜 a
      _ ≤ ∑ a ∈ U, 2 * 𝒜.card *
          min (𝒜.filter fun A ↦ a ∈ A).card
            (𝒜.filter fun A ↦ a ∉ A).card := by
        apply Finset.sum_le_sum
        intro a ha
        let n₁ := (𝒜.filter fun A ↦ a ∈ A).card
        let n₀ := (𝒜.filter fun A ↦ a ∉ A).card
        have hn₁ : n₁ ≤ 𝒜.card := Finset.card_filter_le _ _
        have hn₀ : n₀ ≤ 𝒜.card := Finset.card_filter_le _ _
        by_cases hle : n₁ ≤ n₀
        · rw [min_eq_left hle]
          change 2 * n₁ * n₀ ≤ 2 * 𝒜.card * n₁
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (by
            calc
              n₁ * n₀ ≤ n₁ * 𝒜.card := Nat.mul_le_mul_left n₁ hn₀
              _ = 𝒜.card * n₁ := Nat.mul_comm _ _)
        · rw [min_eq_right (Nat.le_of_not_ge hle)]
          change 2 * n₁ * n₀ ≤ 2 * 𝒜.card * n₀
          simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (by
            calc
              n₁ * n₀ ≤ 𝒜.card * n₀ := Nat.mul_le_mul_right n₀ hn₁
              _ = 𝒜.card * n₀ := rfl)
      _ = 𝒜.card * (2 * ∑ a ∈ U,
          min (𝒜.filter fun A ↦ a ∈ A).card
            (𝒜.filter fun A ↦ a ∉ A).card) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
  have hmul : 𝒜.card * (δ * (𝒜.card - 1)) ≤
      𝒜.card * (2 * ∑ a ∈ U,
        min (𝒜.filter fun A ↦ a ∈ A).card
          (𝒜.filter fun A ↦ a ∉ A).card) := by
    calc
      𝒜.card * (δ * (𝒜.card - 1)) = 𝒜.offDiag.card * δ := by
        rw [Finset.offDiag_card]
        calc
          𝒜.card * (δ * (𝒜.card - 1)) =
              (𝒜.card * (𝒜.card - 1)) * δ := by ring
          _ = (𝒜.card * 𝒜.card - 𝒜.card) * δ := by
            rw [← Nat.pred_eq_sub_one, Nat.mul_pred]
      _ ≤ ∑ e ∈ 𝒜.offDiag, finsetHamming U e.1 e.2 := hsepSum
      _ = ∑ a ∈ U, (crossingPairs 𝒜 a).card := sum_offDiag_finsetHamming U 𝒜
      _ ≤ 𝒜.card * (2 * ∑ a ∈ U,
          min (𝒜.filter fun A ↦ a ∈ A).card
            (𝒜.filter fun A ↦ a ∉ A).card) := hcross_le
  have := Nat.le_of_mul_le_mul_left hmul h𝒜pos
  simpa [Nat.mul_comm] using this

/-- Total split-min mass of the fibres of the trace on `S` at coordinate `a`. -/
def traceSplitMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (a : α) : ℕ :=
  ∑ q ∈ traceFamily 𝒜 S,
    min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
      ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card

/-- Separation forces large aggregate fibre-splitting mass outside any fixed trace. -/
theorem traceSplitMass_lower {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (S : Finset α) (δ : ℕ)
    (_hSU : S ⊆ U)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B) :
    δ * (𝒜.card - (traceFamily 𝒜 S).card) ≤
      2 * ∑ a ∈ U \ S, traceSplitMass 𝒜 S a := by
  have hfiber_lower : ∀ q ∈ traceFamily 𝒜 S,
      δ * ((traceFiber 𝒜 S q).card - 1) ≤
        2 * ∑ a ∈ U \ S,
          min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
            ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card := by
    intro q hq
    apply separated_family_splitMin_lower (U \ S) (traceFiber 𝒜 S q) δ
    intro A hA B hB hAB
    have hA' := (mem_traceFiber_iff 𝒜 S q A).1 hA
    have hB' := (mem_traceFiber_iff 𝒜 S q B).1 hB
    rw [show finsetHamming (U \ S) A B = finsetHamming U A B by
      unfold finsetHamming
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxU, hxS⟩, hdiff⟩
        exact ⟨hxU, hdiff⟩
      · rintro ⟨hxU, hdiff⟩
        refine ⟨⟨hxU, ?_⟩, hdiff⟩
        intro hxS
        have hxAq := Finset.ext_iff.mp hA'.2 x
        have hxBq := Finset.ext_iff.mp hB'.2 x
        simp only [Finset.mem_inter, hxS, true_and] at hxAq hxBq
        exact hdiff (propext (hxAq.trans hxBq.symm))]
    exact hsep A hA'.1 B hB'.1 hAB
  have hsum_lower :
      ∑ q ∈ traceFamily 𝒜 S, δ * ((traceFiber 𝒜 S q).card - 1) ≤
        ∑ q ∈ traceFamily 𝒜 S,
          2 * ∑ a ∈ U \ S,
            min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
              ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card := by
    exact Finset.sum_le_sum hfiber_lower
  calc
    δ * (𝒜.card - (traceFamily 𝒜 S).card) =
        ∑ q ∈ traceFamily 𝒜 S, δ * ((traceFiber 𝒜 S q).card - 1) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_tsub_distrib]
      · simp [sum_traceFiber_card]
      · intro q hq
        obtain ⟨A, hA, hAS⟩ := (mem_traceFamily_iff 𝒜 S q).1 hq
        exact Finset.card_pos.mpr ⟨A, (mem_traceFiber_iff 𝒜 S q A).2 ⟨hA, hAS⟩⟩
    _ ≤ ∑ q ∈ traceFamily 𝒜 S,
        2 * ∑ a ∈ U \ S,
          min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
            ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card := hsum_lower
    _ = 2 * ∑ a ∈ U \ S, traceSplitMass 𝒜 S a := by
      simp only [Finset.mul_sum, traceSplitMass]
      rw [Finset.sum_comm]

private theorem traceFiber_insert_mem {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S q : Finset α) (a : α)
    (haS : a ∉ S) (hqS : q ⊆ S) :
    traceFiber 𝒜 (insert a S) (insert a q) =
      (traceFiber 𝒜 S q).filter fun A ↦ a ∈ A := by
  have haq : a ∉ q := fun haq ↦ haS (hqS haq)
  ext A
  simp only [mem_traceFiber_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hA, hinter⟩
    refine ⟨⟨hA, ?_⟩, ?_⟩
    · ext x
      have hx := Finset.ext_iff.mp hinter x
      by_cases hxa : x = a
      · subst x
        simp [haS, haq]
      · simpa [hxa] using hx
    · have hx := Finset.ext_iff.mp hinter a
      simpa [haq] using hx
  · rintro ⟨⟨hA, hinter⟩, haA⟩
    refine ⟨hA, ?_⟩
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haS, haq, haA]
    · have hx := Finset.ext_iff.mp hinter x
      simpa [hxa] using hx

private theorem traceFiber_insert_notMem {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S q : Finset α) (a : α)
    (haS : a ∉ S) (hqS : q ⊆ S) :
    traceFiber 𝒜 (insert a S) q =
      (traceFiber 𝒜 S q).filter fun A ↦ a ∉ A := by
  have haq : a ∉ q := fun haq ↦ haS (hqS haq)
  ext A
  simp only [mem_traceFiber_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hA, hinter⟩
    refine ⟨⟨hA, ?_⟩, ?_⟩
    · ext x
      have hx := Finset.ext_iff.mp hinter x
      by_cases hxa : x = a
      · subst x
        simp [haS, haq]
      · simpa [hxa] using hx
    · have hx := Finset.ext_iff.mp hinter a
      simpa [haq] using hx
  · rintro ⟨⟨hA, hinter⟩, haA⟩
    refine ⟨hA, ?_⟩
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haq, haA]
    · have hx := Finset.ext_iff.mp hinter x
      simpa [hxa] using hx

/-- A split of a trace fibre injects into the vertical one-inclusion edges after inserting the
split coordinate. -/
theorem traceSplitMass_le_weighted_insert {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (a : α) (haS : a ∉ S) :
    traceSplitMass 𝒜 S a ≤
      ∑ e ∈ downEdges (insert a S) (traceFamily 𝒜 (insert a S)),
        min (traceFiber 𝒜 (insert a S) e.1).card
          (traceFiber 𝒜 (insert a S) (edgeLower e)).card := by
  let active := (traceFamily 𝒜 S).filter fun q ↦
    ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).Nonempty ∧
      ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).Nonempty
  have hactive_sum : traceSplitMass 𝒜 S a =
      ∑ q ∈ active,
        min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
          ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card := by
    unfold traceSplitMass
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hqactive
    simp only [Finset.mem_filter, hq, true_and] at hqactive
    by_cases hmem : ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).Nonempty
    · by_cases hnot : ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).Nonempty
      · exact (hqactive ⟨hmem, hnot⟩).elim
      · rw [Finset.not_nonempty_iff_eq_empty.mp hnot]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hmem]
      simp
  rw [hactive_sum]
  apply Finset.sum_le_sum_of_injOn (fun q ↦ (insert a q, a))
  · intro q₁ hq₁ q₂ hq₂ heq
    change q₁ ∈ active at hq₁
    change q₂ ∈ active at hq₂
    simp only [active, Finset.mem_filter] at hq₁ hq₂
    have haq₁ : a ∉ q₁ := fun haq₁ ↦ haS (traceFamily_support 𝒜 S q₁ hq₁.1 haq₁)
    have haq₂ : a ∉ q₂ := fun haq₂ ↦ haS (traceFamily_support 𝒜 S q₂ hq₂.1 haq₂)
    have herase := congr_arg (fun q : Finset α ↦ q.erase a) (congr_arg Prod.fst heq)
    simpa [haq₁, haq₂] using herase
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨q, hq, rfl⟩ := he
    simp only [active, Finset.mem_filter] at hq
    have hqS := traceFamily_support 𝒜 S q hq.1
    have hupper : insert a q ∈ traceFamily 𝒜 (insert a S) := by
      obtain ⟨A, hA⟩ := hq.2.1
      exact (mem_traceFamily_iff 𝒜 (insert a S) (insert a q)).2
        ⟨A, (mem_traceFiber_iff 𝒜 S q A).1 (Finset.mem_filter.1 hA).1 |>.1,
          (mem_traceFiber_iff 𝒜 (insert a S) (insert a q) A).1
            (traceFiber_insert_mem 𝒜 S q a haS hqS ▸ hA) |>.2⟩
    have hlower : q ∈ traceFamily 𝒜 (insert a S) := by
      obtain ⟨A, hA⟩ := hq.2.2
      exact (mem_traceFamily_iff 𝒜 (insert a S) q).2
        ⟨A, (mem_traceFiber_iff 𝒜 S q A).1 (Finset.mem_filter.1 hA).1 |>.1,
          (mem_traceFiber_iff 𝒜 (insert a S) q A).1
            (traceFiber_insert_notMem 𝒜 S q a haS hqS ▸ hA) |>.2⟩
    rw [mem_downEdges_iff]
    have haq : a ∉ q := fun haq ↦ haS (hqS haq)
    exact ⟨hupper, by simp, by simp, by simpa [edgeLower, haq] using hlower⟩
  · intro q hq
    simp only [active, Finset.mem_filter] at hq
    have hqS := traceFamily_support 𝒜 S q hq.1
    have haq : a ∉ q := fun haq ↦ haS (hqS haq)
    rw [traceFiber_insert_mem 𝒜 S q a haS hqS]
    rw [show edgeLower (insert a q, a) = q by simp [edgeLower, haq]]
    rw [traceFiber_insert_notMem 𝒜 S q a haS hqS]
  · intro e he he_not
    exact Nat.zero_le _

private theorem traceFiber_nonempty_iff {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S q : Finset α) :
    (traceFiber 𝒜 S q).Nonempty ↔ q ∈ traceFamily 𝒜 S := by
  constructor
  · rintro ⟨A, hA⟩
    exact (mem_traceFamily_iff 𝒜 S q).2
      ⟨A, ((mem_traceFiber_iff 𝒜 S q A).1 hA).1,
        ((mem_traceFiber_iff 𝒜 S q A).1 hA).2⟩
  · intro hq
    obtain ⟨A, hA, hAS⟩ := (mem_traceFamily_iff 𝒜 S q).1 hq
    exact ⟨A, (mem_traceFiber_iff 𝒜 S q A).2 ⟨hA, hAS⟩⟩

/-- Exact vertical-edge form of the trace split mass.  This identity is the bridge that avoids
paying an extra factor equal to the projection size in Haussler's double count. -/
theorem traceSplitMass_eq_verticalDownEdges {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (a : α) (haS : a ∉ S) :
    traceSplitMass 𝒜 S a =
      ∑ e ∈ (downEdges (insert a S) (traceFamily 𝒜 (insert a S))).filter
          (fun e ↦ e.2 = a),
        min (traceFiber 𝒜 (insert a S) e.1).card
          (traceFiber 𝒜 (insert a S) (edgeLower e)).card := by
  let active := (traceFamily 𝒜 S).filter fun q ↦
    ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).Nonempty ∧
      ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).Nonempty
  have hactive_sum : traceSplitMass 𝒜 S a =
      ∑ q ∈ active,
        min ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).card
          ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).card := by
    unfold traceSplitMass
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hqactive
    simp only [Finset.mem_filter, hq, true_and] at hqactive
    by_cases hmem : ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).Nonempty
    · by_cases hnot : ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).Nonempty
      · exact (hqactive ⟨hmem, hnot⟩).elim
      · rw [Finset.not_nonempty_iff_eq_empty.mp hnot]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty.mp hmem]
      simp
  rw [hactive_sum]
  apply Finset.sum_bij (fun q _ ↦ (insert a q, a))
  · intro q hq
    simp only [active, Finset.mem_filter] at hq
    have hqS := traceFamily_support 𝒜 S q hq.1
    have hupper : insert a q ∈ traceFamily 𝒜 (insert a S) := by
      rw [← traceFiber_nonempty_iff]
      simpa only [traceFiber_insert_mem 𝒜 S q a haS hqS] using hq.2.1
    have hlower : q ∈ traceFamily 𝒜 (insert a S) := by
      rw [← traceFiber_nonempty_iff]
      simpa only [traceFiber_insert_notMem 𝒜 S q a haS hqS] using hq.2.2
    have haq : a ∉ q := fun haq ↦ haS (hqS haq)
    simp [mem_downEdges_iff, hupper, hlower, haq]
  · intro q₁ hq₁ q₂ hq₂ heq
    have hq₁' := (Finset.mem_filter.1 hq₁).1
    have hq₂' := (Finset.mem_filter.1 hq₂).1
    have haq₁ : a ∉ q₁ := fun haq₁ ↦ haS (traceFamily_support 𝒜 S q₁ hq₁' haq₁)
    have haq₂ : a ∉ q₂ := fun haq₂ ↦ haS (traceFamily_support 𝒜 S q₂ hq₂' haq₂)
    have herase := congr_arg (fun q : Finset α ↦ q.erase a) (congr_arg Prod.fst heq)
    simpa [haq₁, haq₂] using herase
  · intro e he
    obtain ⟨r, b⟩ := e
    simp only [Finset.mem_filter] at he
    have hba : b = a := he.2
    rw [hba] at he ⊢
    have hedge := (mem_downEdges_iff (insert a S)
      (traceFamily 𝒜 (insert a S)) r a).1 he.1
    let q := r.erase a
    have hr_eq : insert a q = r := by
      exact Finset.insert_erase hedge.2.2.1
    have hqS : q ⊆ S := by
      intro x hx
      have hxr : x ∈ r := Finset.mem_of_mem_erase hx
      have hxT := traceFamily_support 𝒜 (insert a S) r hedge.1 hxr
      have hxa : x ≠ a := (Finset.mem_erase.1 hx).1
      simpa [hxa] using hxT
    have hqtrace : q ∈ traceFamily 𝒜 S := by
      obtain ⟨A, hA, hTA⟩ :=
        (mem_traceFamily_iff 𝒜 (insert a S) q).1 hedge.2.2.2
      exact (mem_traceFamily_iff 𝒜 S q).2 ⟨A, hA, by
        calc
          S ∩ A = S ∩ ((insert a S) ∩ A) := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          _ = S ∩ q := by rw [hTA]
          _ = q := Finset.inter_eq_right.mpr hqS⟩
    have hupper : ((traceFiber 𝒜 S q).filter fun A ↦ a ∈ A).Nonempty := by
      rw [← traceFiber_insert_mem 𝒜 S q a haS hqS, hr_eq]
      exact (traceFiber_nonempty_iff 𝒜 (insert a S) r).2 hedge.1
    have hlower : ((traceFiber 𝒜 S q).filter fun A ↦ a ∉ A).Nonempty := by
      rw [← traceFiber_insert_notMem 𝒜 S q a haS hqS]
      exact (traceFiber_nonempty_iff 𝒜 (insert a S) q).2 hedge.2.2.2
    refine ⟨q, Finset.mem_filter.2 ⟨hqtrace, hupper, hlower⟩, ?_⟩
    exact Prod.ext hr_eq rfl
  · intro q hq
    have hq' := (Finset.mem_filter.1 hq).1
    have hqS := traceFamily_support 𝒜 S q hq'
    have haq : a ∉ q := fun haq ↦ haS (hqS haq)
    rw [traceFiber_insert_mem 𝒜 S q a haS hqS]
    rw [show edgeLower (insert a q, a) = q by simp [edgeLower, haq]]
    rw [traceFiber_insert_notMem 𝒜 S q a haS hqS]

/-- Weighted one-inclusion mass of a trace. -/
def traceEdgeMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) : ℕ :=
  ∑ e ∈ downEdges S (traceFamily 𝒜 S),
    min (traceFiber 𝒜 S e.1).card (traceFiber 𝒜 S (edgeLower e)).card

/-- Vertical edge classes partition the weighted one-inclusion mass. -/
theorem sum_verticalDownEdges_eq_traceEdgeMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) :
    (∑ a ∈ S,
      ∑ e ∈ (downEdges S (traceFamily 𝒜 S)).filter (fun e ↦ e.2 = a),
        min (traceFiber 𝒜 S e.1).card
          (traceFiber 𝒜 S (edgeLower e)).card) = traceEdgeMass 𝒜 S := by
  unfold traceEdgeMass
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have heS : e.2 ∈ S := by
    obtain ⟨q, a⟩ := e
    exact ((mem_downEdges_iff S (traceFamily 𝒜 S) q a).1 he).2.1
  simp [heS]

/-! ## Projection averaging -/

/-- The contribution of edges in a trace that point in one fixed coordinate. -/
def verticalTraceEdgeMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (a : α) : ℕ :=
  ∑ e ∈ (downEdges S (traceFamily 𝒜 S)).filter (fun e ↦ e.2 = a),
    min (traceFiber 𝒜 S e.1).card
      (traceFiber 𝒜 S (edgeLower e)).card

/-- Inserting a fresh coordinate turns fibre splitting into the vertical edge mass of the
enlarged trace. -/
theorem traceSplitMass_eq_verticalTraceEdgeMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (a : α) (haS : a ∉ S) :
    traceSplitMass 𝒜 S a = verticalTraceEdgeMass 𝒜 (insert a S) a := by
  exact traceSplitMass_eq_verticalDownEdges 𝒜 S a haS

/-- Summing the coordinate classes of a trace recovers its complete weighted edge mass. -/
theorem sum_verticalTraceEdgeMass_eq_traceEdgeMass {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) :
    ∑ a ∈ S, verticalTraceEdgeMass 𝒜 S a = traceEdgeMass 𝒜 S := by
  exact sum_verticalDownEdges_eq_traceEdgeMass 𝒜 S

/-- Pointing an `r`-subset by a fresh coordinate is equivalent to pointing an
`(r+1)`-subset by one of its coordinates.  The associated split mass is exactly the edge mass
of the enlarged trace. -/
theorem sum_traceSplitMass_powersetCard {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (r : ℕ) :
    (∑ S ∈ U.powersetCard r, ∑ a ∈ U \ S, traceSplitMass 𝒜 S a) =
      ∑ T ∈ U.powersetCard (r + 1), traceEdgeMass 𝒜 T := by
  calc
    (∑ S ∈ U.powersetCard r, ∑ a ∈ U \ S, traceSplitMass 𝒜 S a) =
        ∑ (S ∈ U.powersetCard r) (a ∈ U) with a ∉ S,
          traceSplitMass 𝒜 S a := by
      rw [← Finset.sum_finset_product']
      grind
    _ = ∑ (T ∈ U.powersetCard (r + 1)) (a ∈ U) with a ∈ T,
          verticalTraceEdgeMass 𝒜 T a := by
      apply Finset.sum_bij'
        (fun ⟨S, a⟩ _ ↦ ⟨insert a S, a⟩)
        (fun ⟨T, a⟩ _ ↦ ⟨T.erase a, a⟩)
      · rintro ⟨S, a⟩ hSa
        dsimp at hSa ⊢
        congr 1
        grind
      · rintro ⟨T, a⟩ hTa
        dsimp at hTa ⊢
        congr 1
        grind
      · rintro ⟨S, a⟩ hSa
        dsimp at hSa ⊢
        have haS : a ∉ S := (Finset.mem_filter.1 hSa).2
        exact traceSplitMass_eq_verticalTraceEdgeMass 𝒜 S a haS
      · rintro ⟨T, a⟩ hTa
        dsimp at hTa ⊢
        grind
      · rintro ⟨T, a⟩ hTa
        dsimp at hTa ⊢
        grind
    _ = ∑ T ∈ U.powersetCard (r + 1),
          ∑ a ∈ T, verticalTraceEdgeMass 𝒜 T a := by
      rw [← Finset.sum_finset_product']
      grind
    _ = ∑ T ∈ U.powersetCard (r + 1), traceEdgeMass 𝒜 T := by
      apply Finset.sum_congr rfl
      intro T hT
      exact sum_verticalTraceEdgeMass_eq_traceEdgeMass 𝒜 T

/-- Summed trace deficiencies are bounded by the weighted one-inclusion estimate on the next
projection level. -/
theorem sum_trace_defect_powersetCard_le {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (r δ v : ℕ)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    δ * ∑ S ∈ U.powersetCard r, (𝒜.card - (traceFamily 𝒜 S).card) ≤
      4 * v * 𝒜.card * (U.powersetCard (r + 1)).card := by
  calc
    δ * ∑ S ∈ U.powersetCard r, (𝒜.card - (traceFamily 𝒜 S).card) =
        ∑ S ∈ U.powersetCard r,
          δ * (𝒜.card - (traceFamily 𝒜 S).card) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ S ∈ U.powersetCard r,
        2 * ∑ a ∈ U \ S, traceSplitMass 𝒜 S a := by
      apply Finset.sum_le_sum
      intro S hS
      exact traceSplitMass_lower U 𝒜 S δ (Finset.mem_powersetCard.1 hS).1 hsep
    _ = 2 * ∑ T ∈ U.powersetCard (r + 1), traceEdgeMass 𝒜 T := by
      rw [← Finset.mul_sum, sum_traceSplitMass_powersetCard]
    _ ≤ 2 * ∑ _T ∈ U.powersetCard (r + 1), 2 * v * 𝒜.card := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro T hT
      exact weighted_trace_downEdges_le_two_mul_vc 𝒜 T v hvc
    _ = 4 * v * 𝒜.card * (U.powersetCard (r + 1)).card := by
      simp [Finset.sum_const]
      ring

/-- Sauer--Shelah bound for a trace on a prescribed finite coordinate set. -/
theorem traceFamily_card_le_sauer {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (S : Finset α) (v : ℕ)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    (traceFamily 𝒜 S).card ≤ ∑ i ∈ Finset.Iic v, S.card.choose i := by
  calc
    (traceFamily 𝒜 S).card ≤ (traceFamily 𝒜 S).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ((Finset.Iic v).biUnion fun i ↦ S.powersetCard i).card := by
      apply Finset.card_le_card
      intro T hT
      rw [Finset.mem_biUnion]
      refine ⟨T.card, Finset.mem_Iic.2 ?_, Finset.mem_powersetCard.2 ⟨?_, rfl⟩⟩
      · exact hvc T (traceFamily_shatters_lift 𝒜 S T (Finset.mem_shatterer.1 hT))
      · obtain ⟨q, hq, hTq⟩ := (Finset.mem_shatterer.1 hT).exists_superset
        exact hTq.trans (traceFamily_support 𝒜 S q hq)
    _ ≤ ∑ i ∈ Finset.Iic v, (S.powersetCard i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.Iic v, S.card.choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_powersetCard i S

/-- A projection level whose next-to-current binomial ratio is small captures at least half of
a separated VC family. -/
theorem setFamily_card_le_two_mul_sauer_of_projection_ratio
    {α : Type*} [DecidableEq α] (U : Finset α) (𝒜 : Finset (Finset α))
    (r δ v : ℕ) (hδ : 0 < δ) (hr : r ≤ U.card)
    (hratio : 8 * v * U.card.choose (r + 1) ≤ δ * U.card.choose r)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    𝒜.card ≤ 2 * ∑ i ∈ Finset.Iic v, r.choose i := by
  let C := U.card.choose r
  let Cnext := U.card.choose (r + 1)
  let P := ∑ S ∈ U.powersetCard r, (traceFamily 𝒜 S).card
  let B := ∑ i ∈ Finset.Iic v, r.choose i
  have hCpos : 0 < C := by
    exact Nat.choose_pos hr
  have htrace_le : ∀ S ∈ U.powersetCard r, (traceFamily 𝒜 S).card ≤ 𝒜.card := by
    intro S hS
    exact Finset.card_image_le
  have hsum_trace_le : P ≤ C * 𝒜.card := by
    calc
      P ≤ ∑ _S ∈ U.powersetCard r, 𝒜.card := Finset.sum_le_sum htrace_le
      _ = C * 𝒜.card := by simp [C, Finset.sum_const]
  have hsum_defect :
      ∑ S ∈ U.powersetCard r, (𝒜.card - (traceFamily 𝒜 S).card) =
        C * 𝒜.card - P := by
    rw [Finset.sum_tsub_distrib]
    · simp [C, P, Finset.sum_const]
    · exact htrace_le
  have hdefect : δ * (C * 𝒜.card - P) ≤ 4 * v * 𝒜.card * Cnext := by
    rw [← hsum_defect]
    simpa [Cnext] using sum_trace_defect_powersetCard_le U 𝒜 r δ v hsep hvc
  have htwice_defect : 2 * (C * 𝒜.card - P) ≤ C * 𝒜.card := by
    refine Nat.le_of_mul_le_mul_left ?_ hδ
    calc
      δ * (2 * (C * 𝒜.card - P)) =
          2 * (δ * (C * 𝒜.card - P)) := by ring
      _ ≤ 2 * (4 * v * 𝒜.card * Cnext) := Nat.mul_le_mul_left 2 hdefect
      _ = 𝒜.card * (8 * v * Cnext) := by ring
      _ ≤ 𝒜.card * (δ * C) := by
        exact Nat.mul_le_mul_left 𝒜.card (by simpa [C, Cnext] using hratio)
      _ = δ * (C * 𝒜.card) := by ring
  have hhalf : C * 𝒜.card ≤ 2 * P := by omega
  have htrace_sauer : ∀ S ∈ U.powersetCard r, (traceFamily 𝒜 S).card ≤ B := by
    intro S hS
    have hScard : S.card = r := (Finset.mem_powersetCard.1 hS).2
    simpa [B, hScard] using traceFamily_card_le_sauer 𝒜 S v hvc
  have hP_sauer : P ≤ C * B := by
    calc
      P ≤ ∑ _S ∈ U.powersetCard r, B := Finset.sum_le_sum htrace_sauer
      _ = C * B := by simp [C, Finset.sum_const]
  have hcancel : C * 𝒜.card ≤ C * (2 * B) := by
    calc
      C * 𝒜.card ≤ 2 * P := hhalf
      _ ≤ 2 * (C * B) := Nat.mul_le_mul_left 2 hP_sauer
      _ = C * (2 * B) := by ring
  have := Nat.le_of_mul_le_mul_left hcancel hCpos
  simpa [B] using this

/-! ## A canonical projection level -/

/-- Projection size used in the finite Haussler argument.  The minimum handles the regime where
the formal ceiling would exceed the ambient sample size. -/
def hausslerProjectionSize (m v δ : ℕ) : ℕ :=
  min m ((8 * v * m) ⌈/⌉ δ)

theorem hausslerProjectionSize_le (m v δ : ℕ) :
    hausslerProjectionSize m v δ ≤ m := by
  exact min_le_left _ _

/-- The canonical projection level satisfies the binomial ratio required by the averaging
argument. -/
theorem hausslerProjectionSize_ratio (m v δ : ℕ) (hδ : 0 < δ) :
    8 * v * m.choose (hausslerProjectionSize m v δ + 1) ≤
      δ * m.choose (hausslerProjectionSize m v δ) := by
  let q := 8 * v * m
  let c := q ⌈/⌉ δ
  by_cases hcm : c ≤ m
  · have hsize : hausslerProjectionSize m v δ = c := by
      simp [hausslerProjectionSize, c, q, hcm]
    rw [hsize]
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos c)
    have hceil : q ≤ δ * c := by
      exact (ceilDiv_le_iff_le_mul hδ).1 le_rfl
    calc
      (8 * v * m.choose (c + 1)) * (c + 1) =
          8 * v * (m.choose (c + 1) * (c + 1)) := by ring
      _ = 8 * v * (m.choose c * (m - c)) := by
        rw [Nat.choose_succ_right_eq]
      _ ≤ 8 * v * (m.choose c * m) := by
        gcongr
        exact Nat.sub_le _ _
      _ = m.choose c * q := by ring
      _ ≤ m.choose c * (δ * c) := Nat.mul_le_mul_left _ hceil
      _ ≤ m.choose c * (δ * (c + 1)) := by
        gcongr
        exact Nat.le_succ c
      _ = (δ * m.choose c) * (c + 1) := by ring
  · have hmc : m ≤ c := Nat.le_of_not_ge hcm
    have hsize : hausslerProjectionSize m v δ = m := by
      simp [hausslerProjectionSize, c, q, hmc]
    rw [hsize]
    simp

/-- Premise-free finite set-family Haussler bound, still in the exact Sauer-sum form needed
before the final real-valued entropy simplification. -/
theorem setFamily_card_le_two_mul_sauer {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (δ v : ℕ) (hδ : 0 < δ)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    𝒜.card ≤ 2 * ∑ i ∈ Finset.Iic v,
      (hausslerProjectionSize U.card v δ).choose i := by
  apply setFamily_card_le_two_mul_sauer_of_projection_ratio U 𝒜
    (hausslerProjectionSize U.card v δ) δ v hδ
    (hausslerProjectionSize_le U.card v δ)
    (hausslerProjectionSize_ratio U.card v δ hδ) hsep hvc

@[simp]
theorem boolFamilyToFinsetFamily_card {m : ℕ} (H : Finset (Fin m → Bool)) :
    (boolFamilyToFinsetFamily H).card = H.card := by
  unfold boolFamilyToFinsetFamily
  apply Finset.card_image_of_injective
  intro p q hpq
  funext i
  have hi := Finset.ext_iff.mp hpq i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  cases hpi : p i <;> cases hqi : q i <;> simp_all

/-- The set-system and Boolean-function presentations have identical Hamming distance. -/
theorem finsetHamming_boolSets_eq_hammingDist {m : ℕ} (p q : Fin m → Bool) :
    finsetHamming Finset.univ
        (Finset.univ.filter fun i ↦ p i = true)
        (Finset.univ.filter fun i ↦ q i = true) =
      hammingDist p q := by
  unfold finsetHamming hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hpi : p i <;> cases hqi : q i <;> simp_all

/-- Premise-free discrete Haussler bound for Boolean patterns on a fixed sample. -/
theorem boolFamily_card_le_two_mul_sauer {m : ℕ} (H : Finset (Fin m → Bool))
    (δ v : ℕ) (hδ : 0 < δ)
    (hsep : ∀ p ∈ H, ∀ q ∈ H, p ≠ q → δ ≤ hammingDist p q)
    (hVC : H.boolVCDim ≤ v) :
    H.card ≤ 2 * ∑ i ∈ Finset.Iic v,
      (hausslerProjectionSize m v δ).choose i := by
  have hset := setFamily_card_le_two_mul_sauer
    (Finset.univ : Finset (Fin m)) (boolFamilyToFinsetFamily H) δ v hδ
    (fun A hA B hB hAB ↦ by
      rw [boolFamilyToFinsetFamily, Finset.mem_image] at hA hB
      obtain ⟨p, hpH, rfl⟩ := hA
      obtain ⟨q, hqH, rfl⟩ := hB
      have hpq : p ≠ q := fun hpq ↦ by subst q; exact hAB rfl
      rw [finsetHamming_boolSets_eq_hammingDist]
      exact hsep p hpH q hqH hpq)
    (fun T hT ↦ hT.card_le_vcDim.trans (by simpa [Finset.boolVCDim] using hVC))
  simpa using hset

/-! ## Polynomial packing and covering bounds -/

/-- The finite Boolean VC dimension never exceeds the number of coordinates. -/
theorem boolVCDim_le_card {m : ℕ} (H : Finset (Fin m → Bool)) :
    H.boolVCDim ≤ m := by
  unfold Finset.boolVCDim Finset.vcDim
  apply Finset.sup_le
  intro T hT
  simpa using Finset.card_le_card (Finset.subset_univ T)

/-- The canonical projection size contains the VC dimension when the Hamming separation does not
exceed the ambient dimension. -/
theorem le_hausslerProjectionSize (m v δ : ℕ) (_hv : 0 < v) (hδ : 0 < δ)
    (hvm : v ≤ m) (hδm : δ ≤ m) :
    v ≤ hausslerProjectionSize m v δ := by
  let q := 8 * v * m
  let c := q ⌈/⌉ δ
  have hceil : q ≤ δ * c := (ceilDiv_le_iff_le_mul hδ).1 le_rfl
  have hδv : δ * v ≤ q := by
    calc
      δ * v ≤ m * v := Nat.mul_le_mul_right v hδm
      _ = 1 * (v * m) := by ring
      _ ≤ 8 * (v * m) := Nat.mul_le_mul_right (v * m) (by norm_num)
      _ = 8 * v * m := by ring
      _ = q := rfl
  have hvc : v ≤ c := Nat.le_of_mul_le_mul_left (hδv.trans hceil) hδ
  exact le_min hvm hvc

/-- The projection size has the real scale `O(v m / δ)` with an explicit integer-safe
constant. -/
theorem delta_mul_hausslerProjectionSize_le (m v δ : ℕ) (hv : 0 < v) (_hδ : 0 < δ)
    (hδm : δ ≤ m) :
    δ * hausslerProjectionSize m v δ ≤ 9 * v * m := by
  let q := 8 * v * m
  let c := q ⌈/⌉ δ
  have hsize_le : hausslerProjectionSize m v δ ≤ c := by
    exact min_le_right _ _
  have hceil_upper : δ * c ≤ q + δ := by
    calc
      δ * c = ((q + δ - 1) / δ) * δ := by
        rw [mul_comm, show c = (q + δ - 1) / δ by
          exact Nat.ceilDiv_eq_add_pred_div q δ]
      _ ≤ q + δ - 1 := Nat.div_mul_le_self _ _
      _ ≤ q + δ := Nat.sub_le _ _
  have hmvm : m ≤ v * m := by
    simpa using Nat.mul_le_mul_right m hv
  calc
    δ * hausslerProjectionSize m v δ ≤ δ * c := Nat.mul_le_mul_left δ hsize_le
    _ ≤ q + δ := hceil_upper
    _ ≤ 8 * v * m + v * m := Nat.add_le_add_left (hδm.trans hmvm) _
    _ = 9 * v * m := by ring

/-- Real-valued polynomial form of the set-family packing bound. -/
theorem setFamily_card_cast_le_polynomial {α : Type*} [DecidableEq α]
    (U : Finset α) (𝒜 : Finset (Finset α)) (δ v : ℕ)
    (hv : 0 < v) (hvm : v ≤ U.card) (hδ : 0 < δ) (hδm : δ ≤ U.card)
    (hsep : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → δ ≤ finsetHamming U A B)
    (hvc : ∀ T : Finset α, 𝒜.Shatters T → T.card ≤ v) :
    (𝒜.card : ℝ) ≤
      2 * (16 * Real.exp 1 * U.card / δ) ^ v := by
  let r := hausslerProjectionSize U.card v δ
  have hvr : v ≤ r := le_hausslerProjectionSize U.card v δ hv hδ hvm hδm
  have hdisc : 𝒜.card ≤ 2 * ∑ i ∈ Finset.Iic v, r.choose i := by
    simpa [r] using setFamily_card_le_two_mul_sauer U 𝒜 δ v hδ hsep hvc
  have hsauer := sum_choose_le_exp_pow v r hv hvr
  rw [Nat.range_succ_eq_Iic] at hsauer
  have hδr : δ * r ≤ 9 * v * U.card := by
    exact delta_mul_hausslerProjectionSize_le U.card v δ hv hδ hδm
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hratio : (r : ℝ) / v ≤ 9 * U.card / δ := by
    rw [div_le_div_iff₀ hvR hδR]
    have hδrR : (δ : ℝ) * r ≤ 9 * v * U.card := by exact_mod_cast hδr
    nlinarith
  have hbase : Real.exp 1 * r / v ≤ 16 * Real.exp 1 * U.card / δ := by
    calc
      Real.exp 1 * r / v = Real.exp 1 * ((r : ℝ) / v) := by ring
      _ ≤ Real.exp 1 * (9 * U.card / δ) :=
        mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
      _ ≤ Real.exp 1 * (16 * U.card / δ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg δ)
        exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg U.card)
      _ = 16 * Real.exp 1 * U.card / δ := by ring
  calc
    (𝒜.card : ℝ) ≤ 2 * (∑ i ∈ Finset.Iic v, r.choose i : ℕ) := by
      exact_mod_cast hdisc
    _ ≤ 2 * (Real.exp 1 * r / v) ^ v := by
      apply mul_le_mul_of_nonneg_left
      · simpa using hsauer
      · norm_num
    _ ≤ 2 * (16 * Real.exp 1 * U.card / δ) ^ v := by
      gcongr

/-- Polynomial packing bound for Boolean families, with the natural condition `v ≤ m`. -/
theorem boolFamily_card_cast_le_polynomial_of_le_card {m : ℕ}
    (H : Finset (Fin m → Bool)) (δ v : ℕ)
    (hv : 0 < v) (hvm : v ≤ m) (hδ : 0 < δ) (hδm : δ ≤ m)
    (hsep : ∀ p ∈ H, ∀ q ∈ H, p ≠ q → δ ≤ hammingDist p q)
    (hVC : H.boolVCDim ≤ v) :
    (H.card : ℝ) ≤ 2 * (16 * Real.exp 1 * m / δ) ^ v := by
  have hset := setFamily_card_cast_le_polynomial
    (Finset.univ : Finset (Fin m)) (boolFamilyToFinsetFamily H) δ v hv
    (by simpa using hvm) hδ (by simpa using hδm)
    (fun A hA B hB hAB ↦ by
      rw [boolFamilyToFinsetFamily, Finset.mem_image] at hA hB
      obtain ⟨p, hpH, rfl⟩ := hA
      obtain ⟨q, hqH, rfl⟩ := hB
      have hpq : p ≠ q := fun hpq ↦ by subst q; exact hAB rfl
      rw [finsetHamming_boolSets_eq_hammingDist]
      exact hsep p hpH q hqH hpq)
    (fun T hT ↦ hT.card_le_vcDim.trans (by simpa [Finset.boolVCDim] using hVC))
  simpa using hset

/-- Polynomial packing bound for an arbitrary stated VC upper bound.  Internally the proof uses
`min v m`, then raises the exponent to `v`; no `v ≤ m` premise remains. -/
theorem boolFamily_card_cast_le_polynomial {m : ℕ}
    (H : Finset (Fin m → Bool)) (δ v : ℕ)
    (hδ : 0 < δ) (hδm : δ ≤ m)
    (hsep : ∀ p ∈ H, ∀ q ∈ H, p ≠ q → δ ≤ hammingDist p q)
    (hVC : H.boolVCDim ≤ v) :
    (H.card : ℝ) ≤ 2 * (16 * Real.exp 1 * m / δ) ^ v := by
  by_cases hv0 : v = 0
  · subst v
    have hdisc := boolFamily_card_le_two_mul_sauer H δ 0 hδ hsep hVC
    have hIic : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
    rw [hIic] at hdisc
    simp at hdisc
    norm_num
    exact_mod_cast hdisc
  · let d := min v m
    have hm : 0 < m := hδ.trans_le hδm
    have hd : 0 < d := by
      exact lt_min (Nat.pos_of_ne_zero hv0) hm
    have hdvm : d ≤ m := min_le_right _ _
    have hVCd : H.boolVCDim ≤ d := by
      exact le_min hVC (boolVCDim_le_card H)
    have hd_bound := boolFamily_card_cast_le_polynomial_of_le_card
      H δ d hd hdvm hδ hδm hsep hVCd
    have hbase_one : (1 : ℝ) ≤ 16 * Real.exp 1 * m / δ := by
      have hmd : (1 : ℝ) ≤ (m : ℝ) / δ := by
        rw [le_div_iff₀ (by exact_mod_cast hδ)]
        simpa using (Nat.cast_le.mpr hδm : (δ : ℝ) ≤ m)
      have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h16exp : (1 : ℝ) ≤ 16 * Real.exp 1 :=
        one_le_mul_of_one_le_of_one_le (by norm_num) hexp
      simpa [mul_div_assoc] using one_le_mul_of_one_le_of_one_le h16exp hmd
    calc
      (H.card : ℝ) ≤ 2 * (16 * Real.exp 1 * m / δ) ^ d := hd_bound
      _ ≤ 2 * (16 * Real.exp 1 * m / δ) ^ v := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_right₀ hbase_one (min_le_left _ _)
        · norm_num

/-- A separated indicator family satisfies the log-free Euclidean polynomial packing bound. -/
theorem separated_indicator_card_cast_le_polynomial {m v : ℕ}
    (ε : NNReal) (H : Finset (Fin m → Bool))
    (hε : 0 < ε) (hεm : (ε : ℝ) ^ 2 ≤ m)
    (hVC : H.boolVCDim ≤ v)
    (hsep : Metric.IsSeparated ε (indicatorVectors H : Set (SampleVector m))) :
    (H.card : ℝ) ≤
      2 * (16 * Real.exp 1) ^ v * (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
  let δ : ℕ := ⌈(ε : ℝ) ^ 2⌉₊
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδ : 0 < δ := by
    exact Nat.ceil_pos.2 (sq_pos_of_pos hεR)
  have hδm : δ ≤ m := by
    exact Nat.ceil_le.2 hεm
  have hham := (indicatorVectors_isSeparated_iff ε H).1 hsep
  have hpack : (H.card : ℝ) ≤ 2 * (16 * Real.exp 1 * m / δ) ^ v := by
    apply boolFamily_card_cast_le_polynomial H δ v hδ hδm
    · intro p hp q hq hpq
      exact Nat.ceil_le.2 (hham p hp q hq hpq).le
    · exact hVC
  have hδ_lower : (ε : ℝ) ^ 2 ≤ δ := Nat.le_ceil _
  have hfrac : (m : ℝ) / δ ≤ (m : ℝ) / (ε : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg m) (sq_pos_of_pos hεR) hδ_lower
  have hsqrt : (Real.sqrt m / (ε : ℝ)) ^ 2 = (m : ℝ) / (ε : ℝ) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hbase : 16 * Real.exp 1 * m / δ ≤
      16 * Real.exp 1 * (Real.sqrt m / (ε : ℝ)) ^ 2 := by
    rw [hsqrt]
    calc
      16 * Real.exp 1 * m / δ = (16 * Real.exp 1) * ((m : ℝ) / δ) := by ring
      _ ≤ (16 * Real.exp 1) * ((m : ℝ) / (ε : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 16 * Real.exp 1 * ((m : ℝ) / (ε : ℝ) ^ 2) := by ring
  calc
    (H.card : ℝ) ≤ 2 * (16 * Real.exp 1 * m / δ) ^ v := hpack
    _ ≤ 2 * (16 * Real.exp 1 * (Real.sqrt m / (ε : ℝ)) ^ 2) ^ v := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase v) (by norm_num)
    _ = 2 * (16 * Real.exp 1) ^ v *
        (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- Premise-free indicator covering-number bound obtained by applying the packing theorem to
mathlib's canonical maximal separated subfamily. -/
theorem indicator_coveringCard_cast_le_polynomial {m v : ℕ}
    (ε : NNReal) (H : Finset (Fin m → Bool))
    (hε : 0 < ε) (hεm : (ε : ℝ) ^ 2 ≤ m)
    (hVC : H.boolVCDim ≤ v) :
    (coveringCard ε (indicatorVectors H) : ℝ) ≤
      2 * (16 * Real.exp 1) ^ v * (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
  obtain ⟨Q, hQH, hQsep, hcover⟩ :=
    exists_separated_indicator_subfamily_coveringCard_le ε H
  exact (Nat.cast_le.mpr hcover).trans
    (separated_indicator_card_cast_le_polynomial ε Q hε hεm
      ((boolVCDim_mono hQH).trans hVC) hQsep)

/-- Fixed-sample concept-class form of the premise-free VC covering bound. -/
theorem sampleIndicator_coveringCard_cast_le_polynomial
    {Ω : Type*} {m v : ℕ} (ε : NNReal) (C : Finset (Concept Ω Bool))
    (z : Fin m → Ω) (hε : 0 < ε) (hεm : (ε : ℝ) ^ 2 ≤ m)
    (hVC : (samplePatterns C z).boolVCDim ≤ v) :
    (coveringCard ε (sampleIndicatorVectors C z) : ℝ) ≤
      2 * (16 * Real.exp 1) ^ v * (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
  exact indicator_coveringCard_cast_le_polynomial ε (samplePatterns C z) hε hεm hVC

end OTSelector.Probability.Rademacher
