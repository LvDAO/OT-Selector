import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import OTSelector.PointProcess.FinitePointCloud

/-!
# Measurable encoding of finite multisets

This module constructs measurable multiset codes over an arbitrary standard Borel space. The
coding order on `X` is pulled back from `MeasureTheory.embeddingReal X`; it is an encoding
device only and imposes no topology or pre-existing order on `X`.  The measurable space on
`Multiset X` is the pullback of the sorted padded code, the code is a measurable embedding,
and the resulting multiset space is standard Borel.  The range, cardinality, and measurable
order predicates used by the code are proved here without compatibility hypotheses on `X`.

Sorting is measurable on each finite tuple space: finitely many permutation regions are
specified by measurable comparisons of the real codes.  Gluing over the cloud cardinality
proves that `FinitePointCloud.toMultiset` is measurable for every standard-Borel mark space,
including uncountable spaces.  No topology/order compatibility on `X`, certificate witness,
or local axiom is used.
-/


open Set
open MeasureTheory
namespace OTSelector.PointProcess
namespace MultisetEncoding
variable {X : Type*}

noncomputable def codingLE (X : Type*) [MeasurableSpace X] [StandardBorelSpace X] : X → X → Prop :=
  fun x y => embeddingReal X x ≤ embeddingReal X y

noncomputable instance instDecidableCodingLE [MeasurableSpace X] [StandardBorelSpace X] :
    DecidableRel (codingLE X) := fun _ _ => Classical.propDecidable _

instance instIsTransCodingLE [MeasurableSpace X] [StandardBorelSpace X] :
    IsTrans X (codingLE X) where
  trans a b c hab hbc := by
    change embeddingReal X a ≤ embeddingReal X b at hab
    change embeddingReal X b ≤ embeddingReal X c at hbc
    change embeddingReal X a ≤ embeddingReal X c
    exact hab.trans hbc

instance instAntisymmCodingLE [MeasurableSpace X] [StandardBorelSpace X] :
    Std.Antisymm (codingLE X) where
  antisymm a b hab hba := by
    apply (measurableEmbedding_embeddingReal X).injective
    apply le_antisymm <;> assumption

instance instTotalCodingLE [MeasurableSpace X] [StandardBorelSpace X] :
    Std.Total (codingLE X) where
  total a b := by
    change embeddingReal X a ≤ embeddingReal X b ∨ embeddingReal X b ≤ embeddingReal X a
    exact le_total _ _

def OpLe [MeasurableSpace X] [StandardBorelSpace X] (o p : Option X) : Prop :=
  o.elim (p = none) (fun a => p.elim True (fun b => codingLE X a b))

noncomputable def paddedCode [MeasurableSpace X] [StandardBorelSpace X] (m : Multiset X) :
    FinitePointCloud.PaddedCode X :=
  (m.card, fun k => (m.sort (codingLE X))[k]?)

/-- The canonical sorted and padded multiset code. -/
noncomputable def canonicalCode [MeasurableSpace X] [StandardBorelSpace X] :=
  paddedCode (X := X)

def IsSortedCode [MeasurableSpace X] [StandardBorelSpace X]
    (code : FinitePointCloud.PaddedCode X) : Prop :=
  FinitePointCloud.IsCanonical code ∧ ∀ k, OpLe (code.2 k) (code.2 (k + 1))

theorem sort_of_pairwise [MeasurableSpace X] [StandardBorelSpace X] (l : List X)
    (hl : List.Pairwise (codingLE X) l) :
    (l : Multiset X).sort (codingLE X) = l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := (List.pairwise_cons.mp hl).1
      have htail := (List.pairwise_cons.mp hl).2
      change (a ::ₘ (l : Multiset X)).sort (codingLE X) = a :: l
      rw [Multiset.sort_cons a (l : Multiset X) (codingLE X) ha]
      congr 1
      exact ih htail

theorem isCanonical_paddedCode [MeasurableSpace X] [StandardBorelSpace X]
    (m : Multiset X) : FinitePointCloud.IsCanonical (paddedCode m) := by
  intro k
  simp only [paddedCode]
  by_cases hk : k < m.card
  · have hlen : (m.sort (codingLE X)).length = m.card := by rw [Multiset.length_sort]
    rw [List.getElem?_eq_getElem (by simpa [hlen] using hk)]
    simp [hk]
  · have hlen : (m.sort (codingLE X)).length = m.card := by rw [Multiset.length_sort]
    have hnone : (m.sort (codingLE X))[k]? = none :=
      List.getElem?_eq_none (by simpa [hlen] using (Nat.not_lt.mp hk))
    simp [hk]

theorem sorted_paddedCode [MeasurableSpace X] [StandardBorelSpace X]
    (m : Multiset X) : ∀ k, OpLe (X := X) ((paddedCode m).2 k) ((paddedCode m).2 (k + 1)) := by
  have hsorted := Multiset.pairwise_sort m (codingLE X)
  intro k
  simp only [paddedCode]
  by_cases hk : k < m.card
  · have hlen : (m.sort (codingLE X)).length = m.card := by rw [Multiset.length_sort]
    have hx : (m.sort (codingLE X))[k]? = some ((m.sort (codingLE X)).get ⟨k, by simpa [hlen] using hk⟩) :=
      List.getElem?_eq_getElem (by simpa [hlen] using hk)
    by_cases hk' : k + 1 < m.card
    · have hx' : (m.sort (codingLE X))[k + 1]? =
          some ((m.sort (codingLE X)).get ⟨k + 1, by simpa [hlen] using hk'⟩) :=
        List.getElem?_eq_getElem (by simpa [hlen] using hk')
      rw [hx, hx']
      have hrel := (List.pairwise_iff_getElem.mp hsorted) k (k + 1)
        (by simpa [hlen] using hk) (by simpa [hlen] using hk') (by omega)
      simpa [OpLe] using hrel
    · have hx' : (m.sort (codingLE X))[k + 1]? = none :=
        List.getElem?_eq_none (by simpa [hlen] using (Nat.not_lt.mp hk'))
      rw [hx, hx']
      simp [OpLe]
  · have hlen : (m.sort (codingLE X)).length = m.card := by rw [Multiset.length_sort]
    have hx : (m.sort (codingLE X))[k]? = none :=
      List.getElem?_eq_none (by simpa [hlen] using (Nat.not_lt.mp hk))
    have hk1 : ¬ k + 1 < m.card := fun h => hk (lt_of_le_of_lt (Nat.le_succ k) h)
    have hx' : (m.sort (codingLE X))[k + 1]? = none :=
      List.getElem?_eq_none (by simpa [hlen] using (Nat.not_lt.mp hk1))
    rw [hx, hx']
    simp [OpLe]

theorem isSortedCode_paddedCode [MeasurableSpace X] [StandardBorelSpace X]
    (m : Multiset X) : IsSortedCode (paddedCode m) :=
  ⟨isCanonical_paddedCode m, sorted_paddedCode m⟩

private def codeValue [MeasurableSpace X] [StandardBorelSpace X]
    (code : FinitePointCloud.PaddedCode X) (hcode : IsSortedCode code) (i : Fin code.1) : X :=
  (code.2 i).get ((hcode.1 i).2 i.isLt)

theorem pairwise_of_sortedCode [MeasurableSpace X] [StandardBorelSpace X]
    {code : FinitePointCloud.PaddedCode X} (hcode : IsSortedCode code) :
    List.Pairwise (codingLE X)
      (List.ofFn (fun i : Fin code.1 => codeValue code hcode i)) := by
  let l : List X := List.ofFn (fun i : Fin code.1 => codeValue code hcode i)
  have hstep (n : ℕ) (hn : n + 1 < code.1) :
      codingLE X (codeValue code hcode ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_lt hn)⟩)
        (codeValue code hcode ⟨n + 1, hn⟩) := by
    have h1 : (code.2 n) = some (codeValue code hcode ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n)
        (Nat.le_of_lt hn)⟩) := Option.some_get ((hcode.1 n).2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
        (Nat.le_of_lt hn))) |>.symm
    have h2 : (code.2 (n + 1)) = some (codeValue code hcode ⟨n + 1, hn⟩) :=
      (Option.some_get ((hcode.1 (n + 1)).2 hn)).symm
    simpa [OpLe, h1, h2] using hcode.2 n
  rw [show List.ofFn (fun i : Fin code.1 => codeValue code hcode i) = l by rfl]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hle : i ≤ j := Nat.le_of_lt hij
  have hres := Nat.le_induction
    (P := fun n _ => ∀ hn : n < l.length,
      codingLE X (l.get ⟨i, hi⟩) (l.get ⟨n, hn⟩))
    (by
      intro hn
      change embeddingReal X (l.get ⟨i, hi⟩) ≤ embeddingReal X (l.get ⟨i, hn⟩)
      have heq : l.get ⟨i, hi⟩ = l.get ⟨i, hn⟩ := by congr
      rw [heq])
    (by
      intro n hmn ih hn1
      have hn : n < l.length := lt_of_le_of_lt (Nat.le_succ n) hn1
      have hn1' : n + 1 < code.1 := by simpa [l, List.length_ofFn] using hn1
      have hs := hstep n hn1'
      have hsn : codingLE X (l.get ⟨i, hi⟩) (l.get ⟨n, hn⟩) := ih hn
      have hs' : codingLE X (l.get ⟨n, hn⟩) (l.get ⟨n + 1, hn1⟩) := by
        simpa [l, List.get_ofFn] using hs
      exact IsTrans.trans _ _ _ hsn hs') j hle hj
  simpa using hres


theorem paddedCode_injective [MeasurableSpace X] [StandardBorelSpace X] :
    Function.Injective (paddedCode (X := X)) := by
  intro m₁ m₂ hcode
  have hcard : m₁.card = m₂.card := congr_arg Prod.fst hcode
  have hpoint :
      (fun k : ℕ => (m₁.sort (codingLE X))[k]?) =
        (fun k : ℕ => (m₂.sort (codingLE X))[k]?) := congr_arg Prod.snd hcode
  have hsort : m₁.sort (codingLE X) = m₂.sort (codingLE X) := by
    apply List.ext_get
    · simpa only [Multiset.length_sort] using hcard
    · intro k hk₁ hk₂
      have h₁ : (m₁.sort (codingLE X))[k]? =
          some ((m₁.sort (codingLE X)).get ⟨k, hk₁⟩) := List.getElem?_eq_getElem hk₁
      have h₂ : (m₂.sort (codingLE X))[k]? =
          some ((m₂.sort (codingLE X)).get ⟨k, hk₂⟩) := List.getElem?_eq_getElem hk₂
      have hk := congr_fun hpoint k
      rw [h₁, h₂] at hk
      exact Option.some.inj hk
  calc
    m₁ = (m₁.sort (codingLE X) : Multiset X) := (Multiset.sort_eq m₁ (codingLE X)).symm
    _ = (m₂.sort (codingLE X) : Multiset X) := congrArg (fun l : List X => (l : Multiset X)) hsort
    _ = m₂ := Multiset.sort_eq m₂ (codingLE X)

theorem range_paddedCode [MeasurableSpace X] [StandardBorelSpace X] :
    range (paddedCode (X := X)) = {code | IsSortedCode code} := by
  ext code
  constructor
  · rintro ⟨m, rfl⟩
    exact isSortedCode_paddedCode m
  · intro hcode
    let l : List X := List.ofFn (fun i : Fin code.1 => codeValue code hcode i)
    refine ⟨(l : Multiset X), ?_⟩
    apply Prod.ext
    · simp [paddedCode, l, Multiset.coe_card, List.length_ofFn]
    · have hl : (l : Multiset X).sort (codingLE X) = l :=
        sort_of_pairwise l (pairwise_of_sortedCode hcode)
      funext k
      simp only [paddedCode]
      by_cases hk : k < code.1
      · have hx : code.2 k = some (codeValue code hcode ⟨k, hk⟩) :=
          (Option.some_get ((hcode.1 k).2 hk)).symm
        have hlist : ((l : Multiset X).sort (codingLE X))[k]? = l[k]? :=
          congrArg (fun t : List X => t[k]?) hl
        have hlk : l[k]? = some (codeValue code hcode ⟨k, hk⟩) := by
          simp [l, hk]
        rw [hlist, hlk, hx]
      · have hx : code.2 k = none := by
          apply Option.not_isSome_iff_eq_none.1
          intro hs
          exact hk ((hcode.1 k).1 hs)
        have hlist : ((l : Multiset X).sort (codingLE X))[k]? = l[k]? :=
          congrArg (fun t : List X => t[k]?) hl
        have hlk : l[k]? = none :=
          List.getElem?_eq_none (by simpa [l] using Nat.not_lt.mp hk)
        rw [hlist, hlk, hx]

abbrev SortedCodes [MeasurableSpace X] [StandardBorelSpace X] :=
  {code : FinitePointCloud.PaddedCode X // IsSortedCode code}

noncomputable def sortedCodeEquiv [MeasurableSpace X] [StandardBorelSpace X] :
    Multiset X ≃ SortedCodes (X := X) where
  toFun m := ⟨paddedCode m, isSortedCode_paddedCode m⟩
  invFun c :=
    (List.ofFn (fun i : Fin c.1.1 => codeValue c.1 c.2 i) : Multiset X)
  left_inv m := by
    let l : List X := List.ofFn (fun i : Fin m.card => codeValue (paddedCode m)
      (isSortedCode_paddedCode m) i)
    have hl : l = m.sort (codingLE X) := by
      apply List.ext_get
      · simp [l, Multiset.length_sort]
      · intro k hk₁ hk₂
        simp [l, codeValue, paddedCode, Multiset.length_sort]
    change ((List.ofFn (fun i : Fin m.card => codeValue (paddedCode m)
      (isSortedCode_paddedCode m) i) : List X) : Multiset X) = m
    rw [show List.ofFn (fun i : Fin m.card => codeValue (paddedCode m)
      (isSortedCode_paddedCode m) i) = l by rfl, hl]
    exact Multiset.sort_eq m (codingLE X)
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · simp [paddedCode, Multiset.coe_card, List.length_ofFn]
    · let l : List X := List.ofFn (fun i : Fin c.1.1 => codeValue c.1 c.2 i)
      have hl : (l : Multiset X).sort (codingLE X) = l :=
        sort_of_pairwise l (pairwise_of_sortedCode c.2)
      funext k
      simp only [paddedCode]
      by_cases hk : k < c.1.1
      · have hx : c.1.2 k = some (codeValue c.1 c.2 ⟨k, hk⟩) :=
          (Option.some_get ((c.2.1 k).2 hk)).symm
        have hlist : ((l : Multiset X).sort (codingLE X))[k]? = l[k]? :=
          congrArg (fun t : List X => t[k]?) hl
        have hlk : l[k]? = some (codeValue c.1 c.2 ⟨k, hk⟩) := by
          simp [l, hk]
        rw [hlist, hlk, hx]
      · have hx : c.1.2 k = none := by
          apply Option.not_isSome_iff_eq_none.1
          intro hs
          exact hk ((c.2.1 k).1 hs)
        have hlist : ((l : Multiset X).sort (codingLE X))[k]? = l[k]? :=
          congrArg (fun t : List X => t[k]?) hl
        have hlk : l[k]? = none :=
          List.getElem?_eq_none (by simpa [l] using Nat.not_lt.mp hk)
        rw [hlist, hlk, hx]


theorem measurableSet_codingLE_prod [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableSet {p : X × X | codingLE X p.1 p.2} := by
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    (isClosed_le continuous_fst continuous_snd).measurableSet
  have he : Measurable (Prod.map (embeddingReal X) (embeddingReal X)) :=
    Measurable.prodMk ((measurable_embeddingReal X).comp measurable_fst)
      ((measurable_embeddingReal X).comp measurable_snd)
  have hset : {p : X × X | codingLE X p.1 p.2} =
      (Prod.map (embeddingReal X) (embeddingReal X)) ⁻¹'
        {p : ℝ × ℝ | p.1 ≤ p.2} := by
    rfl
  rw [hset]
  exact hle.preimage he


private theorem measurableEmbedding_some [MeasurableSpace X] :
    MeasurableEmbedding (some : X → Option X) := by
  refine ⟨Option.some_injective X, MeasureTheory.Option.measurable_some, ?_⟩
  intro s hs
  have himage : some '' s =
      (Option.elim' (Sum.inl ()) Sum.inr) ⁻¹' (Sum.inr '' s) := by
    ext o
    cases o <;> simp
  rw [himage, MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inr '' s, ?_, rfl⟩
  rw [measurableSet_sum_iff]
  exact ⟨by simp, by rwa [Sum.inr_injective.preimage_image]⟩

private theorem measurable_get_ne_none [MeasurableSpace X] :
    Measurable (fun o : {o : Option X // o ≠ none} =>
      o.1.get (Option.isSome_iff_ne_none.mpr o.2)) := by
  intro s hs
  have heq : (fun o : {o : Option X // o ≠ none} =>
      o.1.get (Option.isSome_iff_ne_none.mpr o.2)) ⁻¹' s =
      Subtype.val ⁻¹' (some '' s) := by
    ext o
    constructor
    · intro ho
      refine ⟨o.1.get (Option.isSome_iff_ne_none.mpr o.2), ho, ?_⟩
      exact Option.some_get (Option.isSome_iff_ne_none.mpr o.2)
    · rintro ⟨x, hx, hxo⟩
      have hxeq : x = o.1.get (Option.isSome_iff_ne_none.mpr o.2) :=
        Option.some.inj (hxo.trans (Option.some_get (Option.isSome_iff_ne_none.mpr o.2)).symm)
      simpa [hxeq] using hx
  rw [heq]
  exact measurable_subtype_coe (measurableEmbedding_some.measurableSet_image' hs)

private theorem coding_of_opLe [MeasurableSpace X] [StandardBorelSpace X]
    {o p : Option X} (ho : o ≠ none) (hp : p ≠ none)
    (h : OpLe (X := X) o p) :
    codingLE X (o.get (Option.isSome_iff_ne_none.mpr ho))
      (p.get (Option.isSome_iff_ne_none.mpr hp)) := by
  cases o with
  | none => exact (ho rfl).elim
  | some a =>
    cases p with
    | none => exact (hp rfl).elim
    | some b => simpa [OpLe] using h

private theorem opLe_of_coding [MeasurableSpace X] [StandardBorelSpace X]
    {o p : Option X} (ho : o ≠ none) (hp : p ≠ none)
    (h : codingLE X (o.get (Option.isSome_iff_ne_none.mpr ho))
      (p.get (Option.isSome_iff_ne_none.mpr hp))) : OpLe (X := X) o p := by
  cases o with
  | none => exact (ho rfl).elim
  | some a =>
    cases p with
    | none => exact (hp rfl).elim
    | some b => simpa [OpLe] using h

theorem measurableSet_opLe [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableSet {q : Option X × Option X | OpLe (X := X) q.1 q.2} := by
  let C : Set (Option X × Option X) := {q | q.1 ≠ none ∧ q.2 ≠ none}
  have hC : MeasurableSet C := by
    refine ((measurable_fst (measurableSet_singleton none)).compl).inter ?_
    exact (measurable_snd (measurableSet_singleton none)).compl
  let g : C → X × X := fun q =>
    (q.1.1.get (Option.isSome_iff_ne_none.mpr q.2.1),
      q.1.2.get (Option.isSome_iff_ne_none.mpr q.2.2))
  have hg : Measurable g := by
    refine Measurable.prodMk ?_ ?_
    · refine measurable_get_ne_none.comp (Measurable.subtype_mk
        (h := fun q : C => q.property.1)
        (measurable_fst.comp measurable_subtype_coe))
    · refine measurable_get_ne_none.comp (Measurable.subtype_mk
        (h := fun q : C => q.property.2)
        (measurable_snd.comp measurable_subtype_coe))
  have hdecomp : {q : Option X × Option X | OpLe (X := X) q.1 q.2} =
      {q : Option X × Option X | q.2 = none} ∪
        (Subtype.val '' (g ⁻¹' {r : X × X | codingLE X r.1 r.2})) := by
    ext q
    constructor
    · intro hq
      by_cases hq2 : q.2 = none
      · exact Or.inl hq2
      · right
        have hq1 : q.1 ≠ none := by
          intro hq1
          apply hq2
          change q.1.elim (q.2 = none) (fun a => q.2.elim True (fun b => codingLE X a b)) at hq
          rw [hq1] at hq
          exact hq
        refine ⟨⟨q, ⟨hq1, hq2⟩⟩, ?_, rfl⟩
        change codingLE X (g ⟨q, ⟨hq1, hq2⟩⟩).1 (g ⟨q, ⟨hq1, hq2⟩⟩).2
        exact coding_of_opLe hq1 hq2 hq
    · rintro (hq2 | ⟨q, hq, rfl⟩)
      · rcases q with ⟨q1, q2⟩
        change OpLe (X := X) q1 q2
        cases q1 <;> cases q2 <;> simp_all [OpLe]
      · change OpLe (X := X) q.1.1 q.1.2
        exact opLe_of_coding q.2.1 q.2.2 hq
  rw [hdecomp]
  refine (measurable_snd (measurableSet_singleton none)).union ?_
  exact (MeasurableEmbedding.subtype_coe hC).measurableSet_image'
    ((measurableSet_codingLE_prod (X := X)).preimage hg)

theorem measurable_opLe [MeasurableSpace X] [StandardBorelSpace X] :
    Measurable (fun q : Option X × Option X => OpLe (X := X) q.1 q.2) :=
  measurableSet_setOfPred.mp (measurableSet_opLe (X := X))

/-- The multiset measurable space is the pullback of its sorted padded code. -/
noncomputable instance instMeasurableSpace [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableSpace (Multiset X) :=
  MeasurableSpace.comap (paddedCode (X := X)) inferInstance

@[fun_prop]
theorem measurable_paddedCode [MeasurableSpace X] [StandardBorelSpace X] :
    Measurable (paddedCode (X := X)) :=
  comap_measurable _

/-- The sorted-code range is measurable without a topology or order on `X`. -/
theorem measurableSet_isSortedCode [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableSet {code : FinitePointCloud.PaddedCode X | IsSortedCode code} := by
  rw [show {code : FinitePointCloud.PaddedCode X | IsSortedCode code} =
      {code | FinitePointCloud.IsCanonical code} ∩
        {code | ∀ k, OpLe (X := X) (code.2 k) (code.2 (k + 1))} by
    ext code
    simp [IsSortedCode]]
  refine FinitePointCloud.measurableSet_isCanonical.inter ?_
  refine (Measurable.forall fun k => ?_).setOf
  exact (measurable_opLe (X := X)).comp
    (Measurable.prodMk ((measurable_pi_apply k).comp measurable_snd)
      ((measurable_pi_apply (k + 1)).comp measurable_snd))

/-- The sorted padded code is a measurable embedding. -/
theorem measurableEmbedding_paddedCode [MeasurableSpace X] [StandardBorelSpace X] :
    MeasurableEmbedding (paddedCode (X := X)) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  exact ⟨paddedCode_injective, rfl, by
    rw [range_paddedCode]
    exact measurableSet_isSortedCode (X := X)⟩

private theorem standardBorelSpace_of_measurableEquiv {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] (e : A ≃ᵐ B) :
    StandardBorelSpace A := by
  let _ := upgradeStandardBorel B
  let topologyA : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  let _ : TopologicalSpace A := topologyA
  let _ : PolishSpace A := e.toEquiv.polishSpace_induced
  let _ : BorelSpace A := e.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- Arbitrary standard-Borel mark spaces have a standard-Borel multiset code. -/
instance instStandardBorelSpace [MeasurableSpace X] [StandardBorelSpace X] :
    StandardBorelSpace (Multiset X) := by
  let e := measurableEmbedding_paddedCode (X := X)
  let _ : StandardBorelSpace (range (paddedCode (X := X))) := by
    rw [range_paddedCode]
    exact (measurableSet_isSortedCode (X := X)).standardBorel
  exact standardBorelSpace_of_measurableEquiv e.equivRange

@[fun_prop]
theorem measurable_card [MeasurableSpace X] [StandardBorelSpace X] :
    Measurable (fun m : Multiset X => m.card) :=
  measurable_fst.comp measurable_paddedCode



/-! ## Measurable sorting and the unordered projection -/

private def tupleCode {n : ℕ} (x : Fin n → X) : FinitePointCloud.PaddedCode X :=
  (n, fun k ↦ if hk : k < n then some (x ⟨k, hk⟩) else none)

private theorem measurable_tupleCode [MeasurableSpace X] {n : ℕ} :
    Measurable (tupleCode : (Fin n → X) → FinitePointCloud.PaddedCode X) := by
  refine Measurable.prodMk measurable_const (measurable_pi_iff.mpr fun k ↦ ?_)
  by_cases hk : k < n
  · simpa only [tupleCode, dite_eq_left hk, Function.comp_def] using
      MeasureTheory.Option.measurable_some.comp
        (measurable_pi_apply (X := fun _ : Fin n ↦ X) ⟨k, hk⟩)
  · simpa only [tupleCode, dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : Fin n → X ↦ (none : Option X)))

private theorem paddedCode_ofFn_eq_tupleCode [MeasurableSpace X] [StandardBorelSpace X]
    {n : ℕ} (x : Fin n → X) (p : Equiv.Perm (Fin n))
    (hsorted : ∀ i j, i < j → codingLE X (x (p i)) (x (p j))) :
    paddedCode (List.ofFn x : Multiset X) = tupleCode (x ∘ p) := by
  have hperm : (List.ofFn x : Multiset X) = (List.ofFn (x ∘ p) : Multiset X) :=
    Multiset.coe_eq_coe.mpr (p.ofFn_comp_perm x).symm
  have hsort : (List.ofFn x : Multiset X).sort (codingLE X) = List.ofFn (x ∘ p) := by
    rw [hperm]
    exact sort_of_pairwise _ (List.pairwise_ofFn.mpr fun i j hij ↦ hsorted i j hij)
  apply Prod.ext
  · simp [paddedCode, tupleCode]
  · funext k
    simp [paddedCode, tupleCode, hsort, List.getElem?_ofFn]

/-- Sorting a fixed finite tuple by its real coding order is measurable.  The sorting regions
are finite intersections of measurable comparisons, and ties need no additional choice rule. -/
@[fun_prop]
theorem measurable_paddedCode_ofFn [MeasurableSpace X] [StandardBorelSpace X] (n : ℕ) :
    Measurable (fun x : Fin n → X ↦ paddedCode (List.ofFn x : Multiset X)) := by
  classical
  let region : Equiv.Perm (Fin n) → Set (Fin n → X) := fun p ↦
    {x | ∀ i j, i < j → codingLE X (x (p i)) (x (p j))}
  have hregion : ∀ p, MeasurableSet (region p) := by
    intro p
    change MeasurableSet {x : Fin n → X | ∀ i j, i < j → _}
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _hij ↦ ?_
    exact (measurableSet_codingLE_prod (X := X)).preimage
      ((measurable_pi_apply (X := fun _ : Fin n ↦ X) (p i)).prodMk
        (measurable_pi_apply (X := fun _ : Fin n ↦ X) (p j)))
  have hpermCode : ∀ p : Equiv.Perm (Fin n), Measurable fun x : Fin n → X ↦
      tupleCode (x ∘ p) := fun p ↦
    measurable_tupleCode.comp (measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (p i))
  intro s hs
  have hpreimage : (fun x : Fin n → X ↦ paddedCode (List.ofFn x : Multiset X)) ⁻¹' s =
      ⋃ p : Equiv.Perm (Fin n), region p ∩ (fun x ↦ tupleCode (x ∘ p)) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      let p := Tuple.sort (embeddingReal X ∘ x)
      have hsorted : x ∈ region p := by
        intro i j hij
        exact Tuple.monotone_sort (embeddingReal X ∘ x) hij.le
      exact ⟨p, hsorted, (paddedCode_ofFn_eq_tupleCode x p hsorted) ▸ hx⟩
    · rintro ⟨p, hsorted, hx⟩
      rwa [paddedCode_ofFn_eq_tupleCode x p hsorted]
  rw [hpreimage]
  exact MeasurableSet.iUnion fun p ↦ (hregion p).inter (hpermCode p hs)

private def pointsOfCard (n : ℕ) (cloud : {c : FinitePointCloud X // c.card = n}) :
    Fin n → X :=
  fun i ↦ cloud.1.point ⟨i, by simpa only [cloud.2] using i.isLt⟩

private theorem measurable_pointsOfCard [MeasurableSpace X] (n : ℕ) :
    Measurable (pointsOfCard (X := X) n) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  have hp : Measurable fun cloud : {c : FinitePointCloud X // c.card = n} ↦
      cloud.1.point? i :=
    (FinitePointCloud.measurable_point?_apply i).comp measurable_subtype_coe
  have hsome : ∀ cloud : {c : FinitePointCloud X // c.card = n}, cloud.1.point? i ≠ none := by
    intro cloud
    rw [FinitePointCloud.point?_of_lt cloud.1 (by simpa only [cloud.2] using i.isLt)]
    exact Option.some_ne_none _
  have hg := measurable_get_ne_none.comp (hp.subtype_mk (h := hsome))
  convert hg using 1
  ext cloud
  simp [pointsOfCard, FinitePointCloud.point?, show (i : ℕ) < cloud.1.card by
    simpa only [cloud.2] using i.isLt]

private theorem toMultiset_eq_of_card {n : ℕ}
    (cloud : {c : FinitePointCloud X // c.card = n}) :
    cloud.1.toMultiset = (List.ofFn (pointsOfCard n cloud) : Multiset X) := by
  rcases cloud with ⟨⟨m, x⟩, hcard⟩
  change m = n at hcard
  subst n
  rfl

/-- The sorted padded code of a finite cloud is measurable, uniformly over its random size. -/
@[fun_prop]
theorem measurable_paddedCode_toMultiset [MeasurableSpace X] [StandardBorelSpace X] :
    Measurable (fun cloud : FinitePointCloud X ↦ paddedCode cloud.toMultiset) := by
  have hfiber : ∀ n : ℕ, Measurable
      (fun cloud : {c : FinitePointCloud X // c.card = n} ↦ paddedCode cloud.1.toMultiset) := by
    intro n
    simpa only [toMultiset_eq_of_card, Function.comp_def] using
      (measurable_paddedCode_ofFn (X := X) n).comp (measurable_pointsOfCard n)
  intro s hs
  have hpreimage : (fun cloud : FinitePointCloud X ↦ paddedCode cloud.toMultiset) ⁻¹' s =
      ⋃ n : ℕ, Subtype.val ''
        ((fun cloud : {c : FinitePointCloud X // c.card = n} ↦ paddedCode cloud.1.toMultiset) ⁻¹' s) := by
    ext cloud
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    exact ⟨fun h ↦ ⟨cloud.card, ⟨cloud, rfl⟩, h, rfl⟩,
      fun ⟨_, c, h, hc⟩ ↦ hc ▸ h⟩
  rw [hpreimage]
  exact MeasurableSet.iUnion fun n ↦
    (FinitePointCloud.measurable_card (measurableSet_singleton n)).subtype_image (hfiber n hs)

end MultisetEncoding

namespace FinitePointCloud

/-- Forgetting the enumeration of a finite cloud is measurable for arbitrary standard-Borel
mark spaces, with the multiset sigma algebra given by its canonical sorted code. -/
@[fun_prop]
theorem measurable_toMultiset [MeasurableSpace X] [StandardBorelSpace X] :
    Measurable (toMultiset : FinitePointCloud X → Multiset X) := by
  rw [measurable_comap_iff]
  exact MultisetEncoding.measurable_paddedCode_toMultiset

end FinitePointCloud
end OTSelector.PointProcess
