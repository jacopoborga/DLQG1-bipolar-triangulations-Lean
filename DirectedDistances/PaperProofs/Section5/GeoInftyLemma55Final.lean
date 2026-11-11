/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairFaceGraph
public import DirectedDistances.PaperProofs.Section5.GeoInftyLemma55Assembly12
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusCanonicalCodingMeasurable5
public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairIdentifications

/-! Measurable pair realization and final side independence assembly. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local instance : MeasurableSpace (Option (ℕ × Bool)) := ⊤

/-- Helper toward Lemma 5.5. Allocation of a raw vertex includes the
isolated prefix root at zero and every geometric vertex of the future blocks. -/
@[expose] noncomputable def lPlusPairRawVertexAllocated (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : LPlusPairRawVertex → Prop
  | .inl u => if k = 0 then u = 0 else
      ∃ hp : z.val.1.code.1 ∈ lPlusPrefixHitDomain k,
        u < (kmswStage z.val.1.code.1 (lPlusPrefixHitIndex k ⟨_, hp⟩ - 1)).nextVertex
  | .inr (.inl _) => True
  | .inr (.inr u) => u ∈ (lMinusCoherentLeftSide x
      (lPlusCertifiedCodingPairPath x z)).vertices

/-- Helper toward Lemma 5.5. Raw vertex allocation is measurable. -/
theorem measurableSet_lPlusPairRawVertexAllocated (x : XDP) (k : ℤ)
    (u : LPlusPairRawVertex) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairRawVertexAllocated x k z u} := by
  rcases u with u | (u | u)
  · by_cases hk : k = 0
    · simp only [lPlusPairRawVertexAllocated, hk, ↓reduceIte]
      exact MeasurableSet.const _
    · have hm : Measurable (fun p : ℕ → Fin 3 =>
          if hp : p ∈ lPlusPrefixHitDomain k then
            decide (u < (kmswStage p (lPlusPrefixHitIndex k ⟨p, hp⟩ - 1)).nextVertex)
          else false) :=
        (measurable_lPlusPrefixPreviousStage k (fun F => decide (u < F.nextVertex))).dite
          measurable_const (measurableSet_lPlusPrefixHitDomain k)
      have hc : Measurable (fun z : lPlusCertifiedCodingPairDomain x => z.val.1.code.1) :=
        (measurable_lPlusSidePresentation_code x).fst.comp
          (measurable_fst.comp measurable_subtype_coe)
      have hs := ((hm.comp hc).eq_const true).setOf
      convert hs using 1
      ext z
      simp only [lPlusPairRawVertexAllocated, hk, ↓reduceIte, Set.mem_ofPred_eq,
        Function.comp_apply]
      split
      · rename_i hp
        simp only [decide_eq_true_eq]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hp, h⟩⟩
      · rename_i hp
        exact ⟨fun ⟨h, _⟩ => (hp h).elim, fun h => Bool.noConfusion h⟩
  · exact MeasurableSet.univ
  · exact (measurableSet_lMinusCoherentLeftSide_vertices x u).preimage
      (measurable_lPlusCertifiedCodingPairPath x)

/-- Helper toward Lemma 5.5. The measurable full vertex carrier uses
only allocated raw vertices and their full gluing IDs. -/
@[expose] noncomputable def lPlusPairCanonicalVertices (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : Set ℕ :=
  {n | ∃ u, lPlusPairRawVertexAllocated x k z u ∧ lPlusPairFullVertexId x k z u = n}

/-- Helper toward Lemma 5.5. Every full vertex carrier coordinate is measurable. -/
theorem measurableSet_lPlusPairCanonicalVertices (x : XDP) (k : ℤ) (n : ℕ) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      n ∈ lPlusPairCanonicalVertices x k z} := by
  change MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
    ∃ u, lPlusPairRawVertexAllocated x k z u ∧ lPlusPairFullVertexId x k z u = n}
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun u =>
    (measurableSet_lPlusPairRawVertexAllocated x k u).inter
      ((measurable_lPlusPairFullVertexId x k u).eq_const n).setOf)

/-- Helper toward Lemma 5.5. The complete ten-field side in certified
pair coordinates, before passing to marked isomorphism classes. -/
@[expose] noncomputable def lPlusCanonicalSideOnCertifiedPair (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) : GeometricSideSubmap where
  vertices := lPlusPairCanonicalVertices x k z
  edges := lPlusPairCanonicalEdges x k z
  west e := lPlusPairEndpoint x k z (e, false)
  east e := lPlusPairEndpoint x k z (e, true)
  present := {e | lPlusPairPresent x k z e}
  rotation := lPlusPairCorrectedRotationGraph x k z
  faceNext := lPlusPairFaceNext x k z
  root := lPlusPairRoot x k z
  boundary i := (lPlusPairBoundaryOption x k z i).getD (0, false)
  seam := lPlusPairSeam x k z

/-- Helper toward Lemma 5.5. All ten geometric-side fields are jointly
measurable on the certified pair domain. -/
theorem measurable_lPlusCanonicalSideOnCertifiedPair_code (x : XDP) (k : ℤ) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      geometricSideCode (lPlusCanonicalSideOnCertifiedPair x k z)) := by
  have hBool (P : lPlusCertifiedCodingPairDomain x → Prop)
      (hP : MeasurableSet {z | P z}) : Measurable (fun z => decide (P z)) := by
    apply measurable_to_bool
    change MeasurableSet {z : lPlusCertifiedCodingPairDomain x | decide (P z) = true}
    simpa only [decide_eq_true_eq] using hP
  have hv (n : ℕ) := hBool _ (measurableSet_lPlusPairCanonicalVertices x k n)
  have he (n : ℕ) := hBool _ (measurableSet_lPlusPairCanonicalEdges x k n)
  have hp (n : ℕ) := hBool _ (measurableSet_lPlusPairPresent x k n)
  have hr (d e : ℕ × Bool) := hBool _
    (measurableSet_lPlusPairCorrectedRotationGraph x k d e)
  have hf (d e : ℕ × Bool) := hBool _ (measurableSet_lPlusPairFaceNext x k d e)
  have hb (i : ℕ) : Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      (lPlusPairBoundaryOption x k z i).getD (0, false)) :=
    (measurable_of_countable (fun o : Option (ℕ × Bool) => o.getD (0, false))).comp
      (measurable_lPlusPairBoundaryOption x k i)
  exact (measurable_pi_iff.mpr hv).prodMk
    ((measurable_pi_iff.mpr he).prodMk
    ((measurable_pi_iff.mpr (fun e => measurable_lPlusPairEndpoint x k (e, false))).prodMk
    ((measurable_pi_iff.mpr (fun e => measurable_lPlusPairEndpoint x k (e, true))).prodMk
    ((measurable_pi_iff.mpr hp).prodMk
    ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hr d))).prodMk
    ((measurable_pi_iff.mpr (fun d => measurable_pi_iff.mpr (hf d))).prodMk
    ((measurable_lPlusPairRoot x k).prodMk
    ((measurable_pi_iff.mpr hb).prodMk
      (measurable_pi_iff.mpr (measurable_lPlusPairSeam x k))))))))))

/-- Helper toward Lemma 5.5. The pair side is measurable for the sigma
algebra generated by its ten fields. -/
theorem measurable_lPlusCanonicalSideOnCertifiedPair (x : XDP) (k : ℤ) :
    Measurable (lPlusCanonicalSideOnCertifiedPair x k) :=
  measurable_comap_iff.mpr (measurable_lPlusCanonicalSideOnCertifiedPair_code x k)

/-- Helper toward Lemma 5.5. The certified pair class reader is measurable. -/
theorem measurable_lPlusCanonicalSideOnCertifiedPair_class (x : XDP) (k : ℤ) :
    Measurable (fun z => geometricSideClass (lPlusCanonicalSideOnCertifiedPair x k z)) :=
  measurable_geometricSideClass.comp (measurable_lPlusCanonicalSideOnCertifiedPair x k)


section Aligned

variable (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
  (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)

local notation "zₛ" => (Subtype.mk (r, boundaryFutureHattedPath k s.W)
  (LPlusSourceWitnessAligned.codingPair_mem_domain x k r s) :
    lPlusCertifiedCodingPairDomain x)
local notation "Cₛ" => lPlusCanonicalSideOnCertifiedPair x k zₛ
local notation "Vₛ" => lPlusPairGluedVertexId x k r s hk
local notation "Dₛ" => lPlusPairGluedDartId x k r s hk
local notation "Eₛ" => s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4 x k r hk

include hk

/-- Helper toward Lemma 5.5. Prefix vertex allocation agrees exactly
with the source deleted-prefix vertices, including the isolated zero root. -/
theorem lPlusPairRawVertexAllocated_prefix_iff (u : ℕ) :
    lPlusPairRawVertexAllocated x k zₛ (.inl u) ↔
      u ∈ boundaryGluingPrefixMinusVertices s.W s.h k := by
  by_cases hk0 : k = 0
  · subst k
    simp only [lPlusPairRawVertexAllocated, ↓reduceIte,
      boundaryGluingPrefixMinusVertices_zero, Set.mem_singleton_iff]
  · have hkpos : 0 < k := by omega
    rw [boundaryGluingPrefixMinusVertices_of_pos hkpos]
    change (if k = 0 then u = 0 else ∃ hp : r.code.1 ∈ lPlusPrefixHitDomain k,
      u < (kmswStage r.code.1 (lPlusPrefixHitIndex k ⟨_, hp⟩ - 1)).nextVertex) ↔ _
    rw [ite_eq_right hk0, ← s.prefixCode_eq]
    have hhit := boundaryPrefixCode_mem_lPlusPrefixHitDomain s.W s.h k hk
    simp only [lPlusPrefixHitIndex_boundaryPrefixCode s.W s.h k hk]
    have he : kmswStage (boundaryPrefixCode k s.W)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1) =
        kmswStage (shiftedStream s.W 0)
          (boundaryHitTime (shiftedStream s.W 0) s.h k - 1) :=
      kmswStage_congr (fun i hi =>
        lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt s.W s.h k (by omega))
    rw [he]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hhit, h⟩⟩

/-- Helper toward Lemma 5.5. Every source block vertex is allocated. -/
theorem lPlusPairRawVertexAllocated_of_block
    (a : LPlusBlockVertex s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusPairRawVertexAllocated x k zₛ (lPlusBlockVertexRawLabel a) := by
  rcases a with a | (a | a)
  · exact (lPlusPairRawVertexAllocated_prefix_iff x k r s hk a.val).mpr a.property
  · trivial
  · change a.val ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x zₛ)).vertices
    rw [lPlusPairHattedSide_eq_of_aligned x k r s]
    exact a.property

/-- Helper toward Lemma 5.5. Every allocated raw vertex has a source
block representative. -/
theorem exists_lPlusBlockVertex_of_allocated (u : LPlusPairRawVertex)
    (hu : lPlusPairRawVertexAllocated x k zₛ u) :
    ∃ a : LPlusBlockVertex s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode),
      lPlusBlockVertexRawLabel a = u := by
  rcases u with u | (u | u)
  · exact ⟨.inl ⟨u, (lPlusPairRawVertexAllocated_prefix_iff x k r s hk u).mp hu⟩, rfl⟩
  · exact ⟨.inr (.inl u), rfl⟩
  · change u ∈ (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x zₛ)).vertices at hu
    rw [lPlusPairHattedSide_eq_of_aligned x k r s] at hu
    exact ⟨.inr (.inr ⟨u, hu⟩), rfl⟩

/-- Helper toward Lemma 5.5. The vertex numbering has exactly the
allocated pair vertex carrier as its range. -/
theorem lPlusPairGluedVertexId_mem (v : LPlusGluedVertex s.longest s.hqMode s.hτ) :
    Vₛ v ∈ (Cₛ).vertices := by
  induction v using Quotient.inductionOn with
  | h a => exact ⟨lPlusBlockVertexRawLabel a,
      lPlusPairRawVertexAllocated_of_block x k r s hk a, rfl⟩

/-- Helper toward Lemma 5.5. The vertex quotient and pair vertex carrier
are equivalent without choosing a source realization. -/
@[expose] noncomputable def lPlusPairVertexEquiv :
    LPlusGluedVertex s.longest s.hqMode s.hτ ≃ (Cₛ).vertices :=
  Equiv.ofBijective (fun v => ⟨Vₛ v, lPlusPairGluedVertexId_mem x k r s hk v⟩)
    ⟨fun _ _ h => lPlusPairGluedVertexId_injective x k r s hk (congrArg Subtype.val h), by
      rintro ⟨n, u, hu, hn⟩
      obtain ⟨a, ha⟩ := exists_lPlusBlockVertex_of_allocated x k r s hk u hu
      refine ⟨⟦a⟧, Subtype.ext ?_⟩
      change lPlusPairFullVertexId x k zₛ (lPlusBlockVertexRawLabel a) = n
      rw [ha]
      exact hn⟩

/-- Helper toward Lemma 5.5. Both darts of every geometric block edge
land in the allocated pair edge carrier. -/
theorem lPlusPairGluedDartId_mem (d : LPlusGluedDart s.longest s.hqMode s.hτ) :
    (Dₛ d).1 ∈ (Cₛ).edges := by
  induction d using Quotient.inductionOn with
  | h a => exact ⟨(lPlusBlockDartRawLabel a).1,
      lPlusPairRawEdgeAllocated_of_block x k r s hk a, rfl⟩

/-- Helper toward Lemma 5.5. The dart quotient is equivalent to both
darts of every allocated geometric pair edge, preserving missing edges. -/
@[expose] noncomputable def lPlusPairDartEquiv :
    LPlusGluedDart s.longest s.hqMode s.hτ ≃
      {d : ℕ × Bool // d.1 ∈ (Cₛ).edges} :=
  Equiv.ofBijective (fun d => ⟨Dₛ d, lPlusPairGluedDartId_mem x k r s hk d⟩)
    ⟨fun _ _ h => lPlusPairGluedDartId_injective x k r s hk (congrArg Subtype.val h), by
      rintro ⟨⟨n, t⟩, a, ha, hn⟩
      obtain ⟨b, hb⟩ := exists_lPlusBlockDart_of_allocated x k r s hk (a, false) ha
      have he : (Dₛ ⟦b⟧).1 = n := by
        change (lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
          (lPlusBlockDartRawLabel b)).1 = n
        rw [hb]
        exact hn
      by_cases ht : (Dₛ ⟦b⟧).2 = t
      · exact ⟨⟦b⟧, Subtype.ext (Prod.ext he ht)⟩
      · refine ⟨lPlusSide4GluedOpposite ⟦b⟧, Subtype.ext ?_⟩
        change Dₛ (lPlusSide4GluedOpposite ⟦b⟧) = (n, t)
        rw [lPlusPairGluedDartId_opposite x k r s hk]
        apply Prod.ext he
        cases hbit : (Dₛ ⟦b⟧).2 <;> cases t <;> simp_all only [Bool.not_false,
          Bool.not_true, Bool.false_eq_true, Bool.true_eq_false]⟩

/-- Helper toward Lemma 5.5. The pair cell equivalence preserves the
vertex and dart branches of the source gluing quotient. -/
@[expose] noncomputable def lPlusPairCellEquiv :
    Sum (LPlusGluedVertex s.longest s.hqMode s.hτ)
      (LPlusGluedDart s.longest s.hqMode s.hτ) ≃ GeometricSideCell Cₛ :=
  Equiv.sumCongr (lPlusPairVertexEquiv x k r s hk) (lPlusPairDartEquiv x k r s hk)


/-- Helper toward Lemma 5.5. The complete pair side is marked-isomorphic
to the exact source code-block side; all ten relations are retained. -/
noncomputable def lPlusCanonicalSideOnCertifiedPair_markedIso :
    GeometricSideMarkedIso
      (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) Cₛ := by
  let Q := lPlusPairCellEquiv x k r s hk
  refine ⟨(Eₛ).symm.trans Q, ?_⟩
  intro t u v
  obtain ⟨a, rfl⟩ := (Eₛ).surjective u
  obtain ⟨b, rfl⟩ := (Eₛ).surjective v
  have hF (a) : ((Eₛ).symm.trans Q) (Eₛ a) = Q a := by
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [hF, hF]
  cases t with
  | vertex => cases a <;> cases b <;> rfl
  | target => cases a <;> cases b <;> rfl
  | root =>
    rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_root_iff x k r hk]
    cases a with
    | inl a =>
      change Sum.inl a = (Sum.inl ⟦Sum.inr (Sum.inl 1)⟧ : Sum _
        (LPlusGluedDart s.longest s.hqMode s.hτ)) ↔ Vₛ a = lPlusPairRoot x k zₛ
      rw [Sum.inl.inj_iff, lPlusPairRoot_eq_of_aligned x k r s hk]
      exact (lPlusPairGluedVertexId_injective x k r s hk).eq_iff.symm
    | inr a => cases b <;> constructor <;> intro h <;> cases h
  | incident =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      cases b with
      | inr b => rfl
      | inl b =>
        induction a using Quotient.inductionOn with
        | h a =>
          rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_incident_mk_iff
            x k r hk a b]
          change _ ↔ (if (Dₛ ⟦a⟧).2 then
            lPlusPairEndpoint x k zₛ ((Dₛ ⟦a⟧).1, true) else
            lPlusPairEndpoint x k zₛ ((Dₛ ⟦a⟧).1, false)) = Vₛ b
          have he : (if (Dₛ ⟦a⟧).2 then
              lPlusPairEndpoint x k zₛ ((Dₛ ⟦a⟧).1, true) else
              lPlusPairEndpoint x k zₛ ((Dₛ ⟦a⟧).1, false)) =
                lPlusPairEndpoint x k zₛ (Dₛ ⟦a⟧) := by
            generalize Dₛ ⟦a⟧ = d
            rcases d with ⟨n, t⟩
            cases t <;> rfl
          rw [he, lPlusPairEndpoint_eq_of_aligned x k r s hk a]
          exact (lPlusPairGluedVertexId_injective x k r s hk).eq_iff.symm
  | opposite =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      cases b with
      | inl b => rfl
      | inr b =>
        rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_opposite_iff
          x k r hk a b]
        change lPlusSide4GluedOpposite a = b ↔ ((Dₛ a).1, !(Dₛ a).2) = Dₛ b
        rw [← lPlusPairGluedDartId_opposite x k r s hk a]
        exact (lPlusPairGluedDartId_injective x k r s hk).eq_iff.symm
  | oriented =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      induction a using Quotient.inductionOn with
      | h a =>
        exact (lPlusPairOriented_identification x k hk r s a).symm
  | rotation =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      cases b with
      | inl b => rfl
      | inr b =>
        exact (lPlusPairCorrectedRotationGraph_iff_canonicalSide4 x k r s hk a b).symm
  | faceNext =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      cases b with
      | inl b => rfl
      | inr b => exact (lPlusPairFaceNext_iff_codeBlockSide4 x k r s hk a b).symm
  | seam i =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      rw [s.toLPlusSidePresentationSourceWitness.codeBlockCellEquiv4_seam_iff
        x k r hk i a b]
      change _ ↔ lPlusPairSeam x k zₛ i = Dₛ a
      rw [lPlusPairSeam_eq_of_aligned x k r s hk i]
      exact (lPlusPairGluedDartId_injective x k r s hk).eq_iff.symm
  | boundary i =>
    cases a with
    | inl a => cases b <;> rfl
    | inr a =>
      obtain ⟨d, hd, him⟩ := lPlusPairBoundaryRawOption_identification x k hk r s i
      have hpair : (Cₛ).boundary i = Dₛ ⟦d⟧ := by
        change ((lPlusPairBoundaryRawOption x k zₛ i).map
          (lPlusPairRawDartId x k (zₛ).val)).getD (0, false) = _
        rw [hd]
        rfl
      let D := lPlusGluedDartEquivNonneg s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk
      change m0GeodesicBoundaryDart (shiftedStream s.W 0) s.h k .left i =
        (D a).val ↔ (Cₛ).boundary i = Dₛ a
      rw [hpair, ← him]
      change (D ⟦d⟧).val = (D a).val ↔ Dₛ ⟦d⟧ = Dₛ a
      exact (Subtype.val_injective.eq_iff.trans D.injective.eq_iff).trans
        (lPlusPairGluedDartId_injective x k r s hk).eq_iff.symm

/-- Helper toward Lemma 5.5. The measurable pair realization has exactly
the source canonical marked class on every aligned pair. -/
theorem lPlusCanonicalSideOnCertifiedPair_class_eq :
    geometricSideClass Cₛ = geometricSideClass
      (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) := by
  rw [lPlusCanonicalSide4_class_eq_codeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath
    s.hfin s.hleft hk]
  exact ((geometricSideClass_eq_iff _ _).mpr
    ⟨lPlusCanonicalSideOnCertifiedPair_markedIso x k r s hk⟩).symm

end Aligned

/-- Helper toward Lemma 5.5. A complete measurable pair realization
recovers both the canonical and code-block source classes. -/
theorem exists_lPlusPairCanonicalSide (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ C : lPlusCertifiedCodingPairDomain x → GeometricSideSubmap,
      Measurable (fun z => geometricSideCode (C z)) ∧
      (∀ z, (C z).edges = lPlusPairCanonicalEdges x k z) ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        let z : lPlusCertifiedCodingPairDomain x :=
          ⟨(r, boundaryFutureHattedPath k s.W),
            LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
        geometricSideClass (C z) = geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) ∧
        geometricSideClass (C z) = geometricSideClass
          (lPlusCodeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) := by
  refine ⟨lPlusCanonicalSideOnCertifiedPair x k,
    measurable_lPlusCanonicalSideOnCertifiedPair_code x k, fun _ => rfl, ?_⟩
  intro r s
  exact ⟨lPlusCanonicalSideOnCertifiedPair_class_eq x k r s hk,
    (lPlusCanonicalSideOnCertifiedPair_class_eq x k r s hk).trans
      (lPlusCanonicalSide4_class_eq_codeBlockSide4 s.hτ s.hp s.P s.hqMode s.Tpath
        s.hfin s.hleft hk)⟩

/-- Helper toward Lemma 5.5. The certified-pair marked class has a
measurable realization agreeing with every aligned source witness. -/
theorem exists_measurable_lPlusCertifiedPairClass (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ f : lPlusCertifiedCodingPairDomain x → GeometricSideClass,
      Measurable f ∧
      ∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        f ⟨(r, boundaryFutureHattedPath k s.W),
          LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩ =
        geometricSideClass
          (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk) :=
  ⟨fun z => geometricSideClass (lPlusCanonicalSideOnCertifiedPair x k z),
    measurable_lPlusCanonicalSideOnCertifiedPair_class x k,
    fun r s => lPlusCanonicalSideOnCertifiedPair_class_eq x k r s hk⟩

/-- Helper toward Lemma 5.5. The raw optional pair class is present
exactly on the certified pair domain. -/
@[expose] noncomputable def lPlusRawPairCanonicalClassOption (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) : Option GeometricSideClass :=
  if hz : z ∈ lPlusCertifiedCodingPairDomain x then
    some (geometricSideClass (lPlusCanonicalSideOnCertifiedPair x k ⟨z, hz⟩))
  else none

/-- Helper toward Lemma 5.5. The guarded raw pair class is measurable. -/
theorem measurable_lPlusRawPairCanonicalClassOption (x : XDP) (k : ℤ) :
    Measurable (lPlusRawPairCanonicalClassOption x k) :=
  (measurable_some_geometricSideClass.comp
    (measurable_lPlusCanonicalSideOnCertifiedPair_class x k)).dite measurable_const
      (measurableSet_lPlusCertifiedCodingPairDomain x)

/-- Helper toward Lemma 5.5. Presence of the raw pair class is exactly
certification, without an assumed source realization. -/
theorem lPlusRawPairCanonicalClassOption_isSome_iff (x : XDP) (k : ℤ)
    (z : LPlusCodingPair x) :
    (lPlusRawPairCanonicalClassOption x k z).isSome ↔
      z ∈ lPlusCertifiedCodingPairDomain x := by
  unfold lPlusRawPairCanonicalClassOption
  split <;> simp_all only [Option.isSome_some, Option.isSome_none,
    Bool.false_eq_true, iff_self]

/-- Helper toward Lemma 5.5. The raw pair class returns the exact
canonical source class on every aligned nonnegative pair. -/
theorem lPlusRawPairCanonicalClassOption_eq_of_aligned
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) :
    lPlusRawPairCanonicalClassOption x k (r, boundaryFutureHattedPath k s.W) =
      some (geometricSideClass
        (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk)) := by
  rw [lPlusRawPairCanonicalClassOption,
    dite_eq_left (LPlusSourceWitnessAligned.codingPair_mem_domain x k r s),
    lPlusCanonicalSideOnCertifiedPair_class_eq x k r s hk]

/-- Helper toward Lemma 5.5. The measurable raw pair reader agrees
almost surely with the actual left-side observable at every nonnegative index. -/
theorem lemma55LeftSideClassOption_ae_eq_lPlusRawPairCanonicalClassOption
    (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
      lPlusRawPairCanonicalClassOption x k ∘ lPlusCodingPairObservation x k := by
  have hcross := lPlusCodeBlockSide4_class_eq_of_presentation_codes_eq
  filter_upwards
    [lemma55LeftSideClassOption_ae_eq_LPlusSidePresentation_classOptionAt5
      hcross x k hk, ae_LPlusSidePresentation_exists_alignedWitness x k]
    with W hactual hsource
  obtain ⟨s, hsW⟩ := hsource
  have hpair :
      (decodeLPlus x k (leftSideObsNonneg x k W), boundaryFutureHattedPath k s.W) =
        lPlusCodingPairObservation x k W := by
    rw [hsW]
    rfl
  change lemma55LeftSideClassOption x k W =
    lPlusRawPairCanonicalClassOption x k (lPlusCodingPairObservation x k W)
  rw [hactual, Function.comp_apply, LPlusSidePresentation.classOptionAt5_eq_canonical_of_aligned
    hcross x k _ s hk, ← hpair]
  exact (lPlusRawPairCanonicalClassOption_eq_of_aligned x k hk _ s).symm

/-- Helper toward Lemma 5.5. A measurable raw optional class exists,
is present precisely on certified pairs, and agrees a.s. with the actual side. -/
theorem exists_measurable_lPlusRawPairClassOption (x : XDP) (k : ℤ) (hk : 0 ≤ k) :
    ∃ f : LPlusCodingPair x → Option GeometricSideClass,
      Measurable f ∧
      (∀ z, (f z).isSome ↔ z ∈ lPlusCertifiedCodingPairDomain x) ∧
      (∀ (r : LPlusSidePresentation x) (s : LPlusSourceWitnessAligned x k r),
        f (r, boundaryFutureHattedPath k s.W) =
          some (geometricSideClass
            (lPlusCanonicalSide4 s.hτ s.hp s.P s.hqMode s.Tpath s.hfin s.hleft hk))) ∧
      lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        f ∘ lPlusCodingPairObservation x k :=
  ⟨lPlusRawPairCanonicalClassOption x k, measurable_lPlusRawPairCanonicalClassOption x k,
    lPlusRawPairCanonicalClassOption_isSome_iff x k,
    fun r s => lPlusRawPairCanonicalClassOption_eq_of_aligned x k hk r s,
    lemma55LeftSideClassOption_ae_eq_lPlusRawPairCanonicalClassOption x k hk⟩

/-- Helper toward Lemma 5.5. The actual left-side class is a.e.
measurable at every positive boundary index, with no reader premise. -/
theorem aemeasurable_lemma55LeftSideClassOption_pos (x : XDP) (k : ℤ) (hk : 0 < k) :
    AEMeasurable (lemma55LeftSideClassOption x k) wholePlaneIIDCodeMeasure :=
  ((measurable_lPlusRawPairCanonicalClassOption x k).comp_aemeasurable
    (aemeasurable_lPlusCodingPairObservation x k)).congr
      (lemma55LeftSideClassOption_ae_eq_lPlusRawPairCanonicalClassOption x k
        (le_of_lt hk)).symm

/-- Helper toward Lemma 5.5. The source-shaped unmarked side independence
and same-sign laws have no premises beyond the default class. -/
theorem lemma55_unmarked_sides
    (default : GeometricSideClass) :
    ∀ (x : XDP) (k : ℤ),
      IndepFun
        (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k)
        (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k)
        wholePlaneIIDCodeMeasure ∧
      (0 ≤ k →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55RightSideClassOption2 x 0)) ∧
      (k ≤ 0 →
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x k) =
        wholePlaneIIDCodeMeasure.map
          (forgetMarksOptionClassValue default ∘ lemma55LeftSideClassOption x 0)) :=
  lemma55_unmarked_sides_of_LplusPosMeas_RminusMeas default
    aemeasurable_lemma55LeftSideClassOption_pos aemeasurable_RMinusSidePresentation_classOption

/-- Helper toward Lemma 5.5. The five marked class-valued clauses have
no premises beyond the default class. -/
theorem lemma55_marked_sides
    (default : GeometricSideClass) :
    ∀ (x : XDP) (k : ℤ),
      (lemma55LeftSideClassOption x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))) ∧
      (lemma55RightSideClassOption2 x k =ᵐ[wholePlaneIIDCodeMeasure]
        fun W => some (lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W))) ∧
      IndepFun (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W))
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W)) wholePlaneIIDCodeMeasure ∧
      (0 ≤ k → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55RightSideClassOption2 x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55RightSideClassOption2 x 0 W))) ∧
      (k ≤ 0 → wholePlaneIIDCodeMeasure.map
        (fun W => lemma55OptionClassValue default
          (lemma55LeftSideClassOption x k W)) =
        wholePlaneIIDCodeMeasure.map
          (fun W => lemma55OptionClassValue default
            (lemma55LeftSideClassOption x 0 W))) :=
  lemma55_classValued_of_LplusPosMeas_RminusMeas default
    aemeasurable_lemma55LeftSideClassOption_pos aemeasurable_RMinusSidePresentation_classOption

end DirectedDistances.PaperProofs.Section5









