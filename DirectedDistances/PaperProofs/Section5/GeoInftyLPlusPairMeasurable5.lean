/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusPairMeasurable4

/-! Approach change: describe the six component pairs of the full vertex kernel
directly, including vertex-only root contacts. The predecessor's shared-edge
closure omits the isolated prefix root at zero. This avoids choosing a source
realization, evaluating the ambient canonical reader, or asserting measurable
descent of the set-theoretic class factor (the three earlier stalled routes). -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local instance : MeasurableSpace (Option ℕ) := ⊤

/-- Helper toward Lemma 5.5. Prefix/primed vertex contacts include the
isolated prefix root at zero and endpoints of allocated shared edges. -/
@[expose] noncomputable def lPlusPairPrefixPrimedVertexContact (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u v : ℕ) : Prop :=
  (k = 0 ∧ u = 0 ∧ v = 1) ∨ ∃ a b : ℕ, ∃ t : Bool,
    lPlusPairRawEdgeAllocated x k z (.inl a) ∧
    lPlusPrefixPrimedEdgeAttachment x k z.val.1 a b ∧
    lPlusStoppedPrefixEndpointOption k z.val.1.code.1 (a, t) = some u ∧
    kmswLimitDartVertex z.val.1.code.2.2
      (b, t ^^ lMinusCodePrimedSideFlip
        (decodeLMinus x 0 (z.val.1.code.2.2, z.val.1.code.2.1)) b) = v

/-- Helper toward Lemma 5.5. The stopped endpoint equals the permanent
source endpoint on each allocated prefix edge. -/
theorem lPlusStoppedPrefixEndpointOption_eq_endpoint_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (d : LPlusPrefixDart s.W s.h k) :
    lPlusStoppedPrefixEndpointOption k r.code.1 d.val =
      some (kmswLimitDartVertex (shiftedStream s.W 0) d.val) := by
  by_cases hpos : 0 < k
  · have he : d.val.1 < (kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1)).nextEdge :=
      (Set.ext_iff.mp (lPlusPrefixMinusEdges_eq_previousStage
        (W := s.W) (h := s.h) hpos) d.val.1).mp d.property
    rw [lPlusStoppedPrefixEndpointOption_of_aligned x k r s hk]
    have hs := edge_endpoints_eq (shiftedStream s.W 0) he
    cases hb : d.val.2
    · simpa only [kmswLimitDartVertex, hb, Bool.false_eq_true, ↓reduceIte] using
        congrArg some hs.1
    · simpa only [kmswLimitDartVertex, hb, ↓reduceIte] using congrArg some hs.2
  · have hk0 : k = 0 := by omega
    subst k
    exact ((Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_zero s.W s.h)
      d.val.1).mp d.property).elim

/-- Helper toward Lemma 5.5. Alignment identifies the primed endpoint
code and its orientation correction without any new premise. -/
theorem lPlusPairPrimedEndpoint_eq_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (e : ℕ) (t : Bool) :
    kmswLimitDartVertex r.code.2.2
      (e, t ^^ lMinusCodePrimedSideFlip
        (decodeLMinus x 0 (r.code.2.2, r.code.2.1)) e) =
    kmswLimitDartVertex
      (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
      (e, t ^^ primedLimitSideFlip (boundaryGluingFutureStream s.W s.h k) s.hτ e) := by
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hf := lMinusCodePrimedSideFlip_observation
    (longest := s.longest) s.hτ s.hfin e
  change decide (∃ i, lMinusPrimedBoundaryEdge
    (hatLawPrimedCodes (boundaryFutureCode k s.W)) i e) = _ at hf
  change kmswLimitDartVertex r.code.2.2
    (e, t ^^ decide (∃ i, lMinusPrimedBoundaryEdge r.code.2.2 i e)) = _
  rw [← s.primedCode_eq, hf, hc]

/-- Helper toward Lemma 5.5. Every code-only prefix/primed contact
preserves its geometric vertex image, even before restricting raw vertices. -/
theorem lPlusPairPrefixPrimedVertexContact_sound_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) (u v : ℕ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairPrefixPrimedVertexContact x k z u v →
      u = boundaryGluingPrimedVertexMap s.W s.h k s.hτ v := by
  dsimp only
  rintro (⟨hk0, hu, rfl⟩ | ⟨a, b, t, ha, hab, hu, hv⟩)
  · subst k
    exact hu.trans (lPlus_primed_root_starts_at_xk s.hτ).symm
  · have ha' := (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned
      x k r s hk a).mp ha
    let d : LPlusPrefixDart s.W s.h k := ⟨(a, t), ha'⟩
    have hd := lPlusStoppedPrefixEndpointOption_eq_endpoint_of_aligned x k r s hk d
    have hend : kmswLimitDartVertex (shiftedStream s.W 0) (a, t) = u :=
      Option.some.inj (hd.symm.trans hu)
    have hedge := (lPlusPrefixPrimedEdgeAttachment_iff_of_aligned
      x k r s hk a b ha').mp hab
    have hv' := (lPlusPairPrimedEndpoint_eq_of_aligned x k r s b t).symm.trans hv
    calc
      u = kmswLimitDartVertex (shiftedStream s.W 0) (a, t) := hend.symm
      _ = boundaryGluingPrimedVertexMap s.W s.h k s.hτ v := by
        rw [hedge, ← hv', ← lMinusPrimedDartImage_endpoint s.hτ]
        congr 1
        apply Prod.ext (by rfl)
        change t = ((t ^^ primedLimitSideFlip _ s.hτ b) ^^ primedLimitSideFlip _ s.hτ b)
        rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- Helper toward Lemma 5.5. The complete prefix/primed vertex kernel
has a code-only description, including the isolated prefix root at zero. -/
theorem lPlusPairPrefixPrimedVertexContact_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (u : LPlusPrefixVertex s.W s.h k) (v : ℕ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairPrefixPrimedVertexContact x k z u.val v ↔
      u.val = boundaryGluingPrimedVertexMap s.W s.h k s.hτ v := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath k s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
  constructor
  · exact lPlusPairPrefixPrimedVertexContact_sound_of_aligned x k r s hk u.val v
  · intro huv
    by_cases hpos : 0 < k
    · obtain ⟨du, hdu⟩ := lPlus_prefix_vertex_endpoint_exists hpos u
      let p := primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ
      obtain ⟨f, hf⟩ := geoInfty_vertex_endpoint p v
      have hv : ∃ dv : ℕ × Bool, kmswLimitDartVertex p dv = v := by
        rcases hf with hf | hf
        · exact ⟨(f, false), hf⟩
        · exact ⟨(f, true), hf⟩
      obtain ⟨dv, hdv⟩ := hv
      have hincident : kmswLimitDartVertex (shiftedStream s.W 0) du.val =
          kmswLimitDartVertex (shiftedStream s.W 0) (lMinusPrimedDartImage s.hτ dv) := by
        rw [lMinusPrimedDartImage_endpoint s.hτ, hdv, hdu]
        exact huv
      obtain ⟨a, ha, hend⟩ := lPlus_prefix_future_shared_endpoint s.hτ hk du
        (primedLimitDartMap (boundaryGluingFutureStream s.W s.h k) s.hτ dv) hincident
      have ha' : a ∈ boundaryGluingPrefixMinusEdges s.W s.h k :=
        ((Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_inter_primedEdges
          s.W s.h k s.hτ s.hfin hk) a).mpr ha).1
      obtain ⟨b, hb⟩ := boundaryGluingUpperLeftEdges_subset_primedEdges
        s.W s.h k s.hτ s.hfin ha
      have ht : ∃ t : Bool,
          kmswLimitDartVertex (shiftedStream s.W 0) (a, t) = u.val := by
        rcases hend with hw | he
        · exact ⟨false, hw.trans hdu⟩
        · exact ⟨true, he.trans hdu⟩
      obtain ⟨t, ht⟩ := ht
      refine Or.inr ⟨a, b, t,
        (lPlusPairRawEdgeAllocated_prefix_iff_of_aligned x k r s hk a).mpr ha',
        (lPlusPrefixPrimedEdgeAttachment_iff_of_aligned x k r s hk a b ha').mpr hb.symm,
        ?_, ?_⟩
      · exact (lPlusStoppedPrefixEndpointOption_eq_endpoint_of_aligned
          x k r s hk ⟨(a, t), ha'⟩).trans (congrArg some ht)
      · rw [lPlusPairPrimedEndpoint_eq_of_aligned x k r s b t]
        apply (show Function.Injective (boundaryGluingPrimedVertexMap s.W s.h k s.hτ)
          from lPlusPrimedVertexImage_injective s.hτ s.hqMode)
        rw [← lMinusPrimedDartImage_endpoint s.hτ]
        have hd : lMinusPrimedDartImage s.hτ
            (b, t ^^ primedLimitSideFlip _ s.hτ b) = (a, t) := by
          apply Prod.ext hb
          change ((t ^^ primedLimitSideFlip _ s.hτ b) ^^ primedLimitSideFlip _ s.hτ b) = t
          rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
        rw [hd, ht, huv]
    · have hk0 : k = 0 := by omega
      subst k
      have hu : u.val = 0 := (Set.ext_iff.mp
        (boundaryGluingPrefixMinusVertices_zero (W := s.W) (h := s.h)) u.val).mp u.property
      have hv : v = 1 := (show Function.Injective
        (boundaryGluingPrimedVertexMap s.W s.h 0 s.hτ) from
          lPlusPrimedVertexImage_injective s.hτ s.hqMode)
        (huv.symm.trans (hu.trans (lPlus_primed_root_starts_at_xk s.hτ).symm))
      exact Or.inl ⟨rfl, hu, hv⟩

/-- Helper toward Lemma 5.5. Prefix/primed vertex contacts are measurable
by countable allocated-edge endpoint tests, with the zero root added explicitly. -/
theorem measurableSet_lPlusPairPrefixPrimedVertexContact (x : XDP) (k : ℤ)
    (u v : ℕ) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairPrefixPrimedVertexContact x k z u v} := by
  unfold lPlusPairPrefixPrimedVertexContact
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter (MeasurableSet.const _)))
  refine MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b =>
    MeasurableSet.iUnion (fun t => ?_)))
  have hp : Measurable (fun z : lPlusCertifiedCodingPairDomain x => z.val.1.code.1) :=
    (measurable_lPlusSidePresentation_code x).fst.comp
      (measurable_fst.comp measurable_subtype_coe)
  have hprimed := (measurable_lMinusPrimedDartEndpoint x b t).comp
    (measurable_fst.comp
      (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairFuture x)))
  exact (measurableSet_lPlusPairRawEdgeAllocated x k (.inl a)).inter
    ((measurableSet_lPlusCertifiedCodingPair_prefixPrimedEdgeAttachment x k a b).inter
      (((((measurable_lPlusStoppedPrefixEndpointOption k (a, t)).comp hp).eq_const
        (some u)).setOf).inter ((hprimed.eq_const v).setOf)))

/-- Helper toward Lemma 5.5. The primed/hatted vertex kernel is read
from the root contact and east endpoints of indexed beta boundary edges. -/
@[expose] noncomputable def lPlusPairPrimedHattedVertexContact (x : XDP)
    (z : lPlusCertifiedCodingPairDomain x) (u v : ℕ) : Prop :=
  (u = 1 ∧ v = 0) ∨ ∃ a b : ℕ,
    lMinusRawCodeEdgeGluing
      (decodeLMinus x 0 (z.val.1.code.2.2, z.val.1.code.2.1)) z.val.2 a b ∧
    u = kmswLimitDartVertex z.val.1.code.2.2 (a, false) ∧
    v = (lMinusCoherentLeftSide x (lPlusCertifiedCodingPairPath x z)).east b

/-- Helper toward Lemma 5.5. The full primed/hatted contact formula is
measurable before a source realization is chosen. -/
theorem measurableSet_lPlusPairPrimedHattedVertexContact (x : XDP)
    (u v : ℕ) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairPrimedHattedVertexContact x z u v} := by
  unfold lPlusPairPrimedHattedVertexContact
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union ((MeasurableSet.const _).inter (MeasurableSet.const _))
  refine MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b => ?_))
  have hc := measurable_fst.comp
    (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairFuture x))
  have hr := (measurableSet_lMinusRawCodeEdgeGluing x a b).preimage
    (hc.prodMk (measurable_subtype_coe.comp (measurable_lPlusCertifiedCodingPairPath x)))
  have hfixed : Measurable (fun p : ℕ → Fin 3 => kmswLimitDartVertex p (a, false)) := by
    apply measurable_of_factors_prefix a
    intro p p' hp
    simp only [kmswLimitDartVertex, edgeWest, edgeEast, kmswStage_congr hp]
  have hp : Measurable (fun z : lPlusCertifiedCodingPairDomain x =>
      u = kmswLimitDartVertex z.val.1.code.2.2 (a, false)) := (hfixed.comp
    ((measurable_lPlusSidePresentation_code x).snd.snd.comp
      (measurable_fst.comp measurable_subtype_coe))).const_eq u
  have hh := (measurableSet_lMinusCoherentLeftSide_incident x (b, true) v).preimage
    (measurable_lPlusCertifiedCodingPairPath x)
  exact hr.inter (hp.setOf.inter (by simpa only [Set.preimage_ofPred_eq, ↓reduceIte, eq_comm] using hh))

/-- Helper toward Lemma 5.5. Every primed/hatted vertex equality is
exactly a code-only root or indexed-boundary contact. -/
theorem lPlusPairPrimedHattedVertexContact_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (u v : ℕ) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairPrimedHattedVertexContact x z u v ↔
      boundaryGluingPrimedVertexMap s.W s.h k s.hτ u =
        boundaryGluingHatVertexMap s.W s.h k s.hτ v := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath k s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
  have hc := lMinus_primed_observation_code (longest := s.longest) s.hτ
  change hatLawPrimedCodes (boundaryFutureCode k s.W) = _ at hc
  have hcode : r.code.2.2 =
      primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ :=
    s.primedCode_eq.symm.trans hc
  have heast (b : ℕ) : (lMinusCoherentLeftSide x
      (lPlusCertifiedCodingPairPath x z)).east b =
      edgeEast (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ) b := by
    change edgeEast (boltzmannKMSWStream
      (pathCode (boundaryFutureHattedPath k s.W))) b = _
    rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
  have hboundary (i : ℕ) : lMinusPrimedBoundaryEdge r.code.2.2 i
      (primedBeta0EdgeIndex (boundaryGluingFutureStream s.W s.h k) s.hτ s.hfin
        (hatBoundaryHitWitnesses _ s.hτ) s.hfin i) := by
    rw [← s.primedCode_eq]
    exact lMinusPrimedBoundaryEdge_observation (longest := s.longest) s.hτ s.hfin i
  rw [lPlus_primed_hatted_vertex_eq_iff_boundary s.hτ s.hqMode s.hfin]
  constructor
  · rintro (hroot | ⟨a, b, ⟨i, hi, hb⟩, hu, hv⟩)
    · exact Or.inl hroot
    · have ha := lMinusPrimedBoundaryEdge_unique _ i a _ hi (hboundary i)
      change kmswLeftBoundaryEdge
        (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) i = b at hb
      rw [boundaryGluing_decoded_stream s.W s.h k s.hτ] at hb
      exact Or.inr ⟨i, by rw [hcode, ha] at hu; exact hu,
        by rw [← hb, heast] at hv; exact hv⟩
  · rintro (hroot | ⟨i, hu, hv⟩)
    · exact Or.inl hroot
    · refine Or.inr ⟨_, kmswLeftBoundaryEdge
        (hatCodes (boundaryGluingFutureStream s.W s.h k) s.hτ) i,
        ⟨i, hboundary i, ?_⟩, ?_, ?_⟩
      · change kmswLeftBoundaryEdge
          (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) i = _
        rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
      · change u = kmswLimitDartVertex r.code.2.2 _
        rw [hcode]
        exact hu
      · rw [heast]
        exact hv

/-- Helper toward Lemma 5.5. Direct full vertex relation on raw block
labels. Mixed cases include every root contact, even when no prefix edge exists.
The geometric identification below is on the actual allocated source carrier. -/
@[expose] noncomputable def lPlusPairFullVertexKernel (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) :
    LPlusPairRawVertex → LPlusPairRawVertex → Prop
  | .inl u, .inl v => u = v
  | .inr (.inl u), .inr (.inl v) => u = v
  | .inr (.inr u), .inr (.inr v) => u = v
  | .inl u, .inr (.inl v) => lPlusPairPrefixPrimedVertexContact x k z u v
  | .inr (.inl u), .inl v => lPlusPairPrefixPrimedVertexContact x k z v u
  | .inr (.inl u), .inr (.inr v) => lPlusPairPrimedHattedVertexContact x z u v
  | .inr (.inr u), .inr (.inl v) => lPlusPairPrimedHattedVertexContact x z v u
  | .inl u, .inr (.inr v) => lPlusPairPrefixPrimedVertexContact x k z u 1 ∧ v = 0
  | .inr (.inr u), .inl v => lPlusPairPrefixPrimedVertexContact x k z v 1 ∧ u = 0

/-- Helper toward Lemma 5.5. Every coordinate of the direct full vertex
kernel is measurable by its six component formulas. -/
theorem measurableSet_lPlusPairFullVertexKernel (x : XDP) (k : ℤ)
    (u v : LPlusPairRawVertex) :
    MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      lPlusPairFullVertexKernel x k z u v} := by
  rcases u with u | (u | u) <;> rcases v with v | (v | v)
  · exact MeasurableSet.const _
  · exact measurableSet_lPlusPairPrefixPrimedVertexContact x k u v
  · exact (measurableSet_lPlusPairPrefixPrimedVertexContact x k u 1).inter
      (MeasurableSet.const _)
  · exact measurableSet_lPlusPairPrefixPrimedVertexContact x k v u
  · exact MeasurableSet.const _
  · exact measurableSet_lPlusPairPrimedHattedVertexContact x u v
  · exact (measurableSet_lPlusPairPrefixPrimedVertexContact x k v 1).inter
      (MeasurableSet.const _)
  · exact measurableSet_lPlusPairPrimedHattedVertexContact x v u
  · exact MeasurableSet.const _

/-- Helper toward Lemma 5.5. Forget only subtype certificates, keeping
the block tag and permanent local vertex identity. -/
@[expose] def lPlusBlockVertexRawLabel {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {M : GeometricSideSubmap} : LPlusBlockVertex W h k M → LPlusPairRawVertex
  | .inl u => .inl u.val
  | .inr (.inl u) => .inr (.inl u)
  | .inr (.inr u) => .inr (.inr u.val)

/-- Helper toward Lemma 5.5. The direct measurable relation is the full
geometric vertex kernel on all three source blocks. This includes every mixed
pair and the isolated prefix root at zero; alignment is a quantified source
witness, not a newly assumed existence or class-identity premise. -/
theorem lPlusPairFullVertexKernel_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusBlockVertex s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairFullVertexKernel x k z (lPlusBlockVertexRawLabel a)
      (lPlusBlockVertexRawLabel b) ↔
      lPlusBlockVertexImage s.hτ a = lPlusBlockVertexImage s.hτ b := by
  dsimp only
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact Iff.rfl
  · exact lPlusPairPrefixPrimedVertexContact_iff_of_aligned x k r s hk a b
  · exact (and_congr_left (fun _ =>
      lPlusPairPrefixPrimedVertexContact_iff_of_aligned x k r s hk a 1)).trans
      (lPlusSourceWitnessAligned_prefixHattedVertex_eq_iff_root x k r s hk a b.val).symm
  · exact (lPlusPairPrefixPrimedVertexContact_iff_of_aligned x k r s hk b a).trans eq_comm
  · exact (show Function.Injective (boundaryGluingPrimedVertexMap s.W s.h k s.hτ)
      from lPlusPrimedVertexImage_injective s.hτ s.hqMode).eq_iff.symm
  · exact lPlusPairPrimedHattedVertexContact_iff_of_aligned x k r s a b.val
  · exact ((and_congr_left (fun _ =>
      lPlusPairPrefixPrimedVertexContact_iff_of_aligned x k r s hk b 1)).trans
      (lPlusSourceWitnessAligned_prefixHattedVertex_eq_iff_root x k r s hk b a.val).symm).trans
      eq_comm
  · exact (lPlusPairPrimedHattedVertexContact_iff_of_aligned x k r s b a.val).trans eq_comm
  · exact (boundaryGluingHatVertexMap_injective s.W s.h k s.hτ).eq_iff.symm

/-- Helper toward Lemma 5.5. The raw ambient vertex map is used only in
proofs of geometric identification, never to define a measurable coordinate. -/
@[expose] noncomputable def lPlusPairRawVertexImage
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    LPlusPairRawVertex → ℕ
  | .inl u => u
  | .inr (.inl u) => boundaryGluingPrimedVertexMap W h k hτ u
  | .inr (.inr u) => boundaryGluingHatVertexMap W h k hτ u

/-- Helper toward Lemma 5.5. No contact in the full raw relation creates
an incorrect ambient vertex equality, even through unallocated raw labels. -/
theorem lPlusPairFullVertexKernel_sound_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusPairRawVertex) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairFullVertexKernel x k z a b →
      lPlusPairRawVertexImage s.hτ a = lPlusPairRawVertexImage s.hτ b := by
  dsimp only
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact fun h => h
  · exact lPlusPairPrefixPrimedVertexContact_sound_of_aligned x k r s hk a b
  · rintro ⟨ha, rfl⟩
    exact (lPlusPairPrefixPrimedVertexContact_sound_of_aligned x k r s hk a 1 ha).trans
      ((lPlus_primed_root_starts_at_xk s.hτ).trans
        (boundaryGluingHatVertexMap_zero s.hτ).symm)
  · exact fun h => (lPlusPairPrefixPrimedVertexContact_sound_of_aligned x k r s hk b a h).symm
  · exact fun h => congrArg (boundaryGluingPrimedVertexMap s.W s.h k s.hτ) h
  · exact (lPlusPairPrimedHattedVertexContact_iff_of_aligned x k r s a b).mp
  · rintro ⟨hb, rfl⟩
    exact ((lPlusPairPrefixPrimedVertexContact_sound_of_aligned x k r s hk b 1 hb).trans
      ((lPlus_primed_root_starts_at_xk s.hτ).trans
        (boundaryGluingHatVertexMap_zero s.hτ).symm)).symm
  · exact fun h => ((lPlusPairPrimedHattedVertexContact_iff_of_aligned x k r s b a).mp h).symm
  · exact fun h => congrArg (boundaryGluingHatVertexMap s.W s.h k s.hτ) h

/-- Helper toward Lemma 5.5. Taking the equivalence closure of the full
raw contact relation preserves the exact geometric kernel on source vertices.
Intermediate raw labels cannot introduce spurious geometric identifications. -/
theorem lPlusPairFullVertexEqvGen_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusBlockVertex s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    Relation.EqvGen (lPlusPairFullVertexKernel x k z)
      (lPlusBlockVertexRawLabel a) (lPlusBlockVertexRawLabel b) ↔
      lPlusBlockVertexImage s.hτ a = lPlusBlockVertexImage s.hτ b := by
  dsimp only
  constructor
  · intro hab
    have hs : ∀ u v : LPlusPairRawVertex,
        Relation.EqvGen (lPlusPairFullVertexKernel x k
          ⟨(r, boundaryFutureHattedPath k s.W),
            LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩) u v →
        lPlusPairRawVertexImage s.hτ u = lPlusPairRawVertexImage s.hτ v := by
      intro u v huv
      induction huv with
      | rel u v h => exact lPlusPairFullVertexKernel_sound_of_aligned x k r s hk u v h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have h := hs _ _ hab
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> exact h
  · intro hab
    exact Relation.EqvGen.rel _ _
      ((lPlusPairFullVertexKernel_iff_of_aligned x k r s hk a b).mpr hab)

/-- Helper toward Lemma 5.5. The full kernel closure has measurable
finite-chain certificates, without a bound on chain length. -/
theorem measurableSet_lPlusPairFullVertexEqvGen (x : XDP) (k : ℤ)
    (u v : LPlusPairRawVertex) : MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
      Relation.EqvGen (lPlusPairFullVertexKernel x k z) u v} := by
  have hc (l : List LPlusPairRawVertex) (u v : LPlusPairRawVertex) :
      MeasurableSet {z : lPlusCertifiedCodingPairDomain x |
        lMinusFiniteGluingChain (lPlusPairFullVertexKernel x k z) u l v} := by
    induction l generalizing u with
    | nil => exact MeasurableSet.const (u = v)
    | cons a l ih =>
      exact ((measurableSet_lPlusPairFullVertexKernel x k u a).union
        (measurableSet_lPlusPairFullVertexKernel x k a u)).inter (ih a)
  have he : {z : lPlusCertifiedCodingPairDomain x |
      Relation.EqvGen (lPlusPairFullVertexKernel x k z) u v} =
      ⋃ l : List LPlusPairRawVertex, {z |
        lMinusFiniteGluingChain (lPlusPairFullVertexKernel x k z) u l v} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion,
      lMinusEqvGen_iff_exists_finiteGluingChain]
  rw [he]
  exact MeasurableSet.iUnion (fun l => hc l u v)

/-- Helper toward Lemma 5.5. Candidate tokens in the full vertex kernel
closure retain block and local vertex identity. -/
@[expose] noncomputable def lPlusPairFullVertexCandidate (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) (n : ℕ) : Prop :=
  ∃ v : LPlusPairRawVertex, lPlusRawEdgeToken v = n ∧
    Relation.EqvGen (lPlusPairFullVertexKernel x k z) v u

/-- Helper toward Lemma 5.5. Each vertex has its own candidate, including
an isolated geometric vertex. -/
theorem lPlusPairFullVertexCandidate_exists (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) :
    ∃ n, lPlusPairFullVertexCandidate x k z u n :=
  ⟨lPlusRawEdgeToken u, u, rfl, Relation.EqvGen.refl u⟩

/-- Helper toward Lemma 5.5. Least-token numbering uses the full vertex
kernel rather than just the shared-edge endpoint relation. -/
@[expose] noncomputable def lPlusPairFullVertexId (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u : LPlusPairRawVertex) : ℕ :=
  Nat.find (lPlusPairFullVertexCandidate_exists x k z u)

/-- Helper toward Lemma 5.5. Every full vertex ID is measurable from the
raw pair, without any source-witness selection. -/
theorem measurable_lPlusPairFullVertexId (x : XDP) (k : ℤ) (u : LPlusPairRawVertex) :
    Measurable (fun z : lPlusCertifiedCodingPairDomain x => lPlusPairFullVertexId x k z u) := by
  apply measurable_find (fun z => lPlusPairFullVertexCandidate_exists x k z u)
  intro n
  unfold lPlusPairFullVertexCandidate
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion (fun v => (MeasurableSet.const (lPlusRawEdgeToken v = n)).inter
    (measurableSet_lPlusPairFullVertexEqvGen x k v u))

/-- Helper toward Lemma 5.5. Equal full vertex IDs characterize exactly
the full contact closure. -/
theorem lPlusPairFullVertexId_eq_iff (x : XDP) (k : ℤ)
    (z : lPlusCertifiedCodingPairDomain x) (u v : LPlusPairRawVertex) :
    lPlusPairFullVertexId x k z u = lPlusPairFullVertexId x k z v ↔
      Relation.EqvGen (lPlusPairFullVertexKernel x k z) u v := by
  constructor
  · intro huv
    obtain ⟨a, ha, hau⟩ := Nat.find_spec (lPlusPairFullVertexCandidate_exists x k z u)
    obtain ⟨b, hb, hbv⟩ := Nat.find_spec (lPlusPairFullVertexCandidate_exists x k z v)
    have hab := lPlusRawEdgeToken_injective (ha.trans (huv.trans hb.symm))
    subst b
    exact Relation.EqvGen.trans u a v hau.symm hbv
  · intro huv
    apply Nat.find_congr'
    intro n
    constructor
    · rintro ⟨a, ha, hau⟩
      exact ⟨a, ha, Relation.EqvGen.trans a u v hau huv⟩
    · rintro ⟨a, ha, hav⟩
      exact ⟨a, ha, Relation.EqvGen.trans a v u hav huv.symm⟩

/-- Helper toward Lemma 5.5. The measurable full vertex IDs have exactly
the geometric vertex kernel on the actual three-block source carrier. -/
theorem lPlusPairFullVertexId_eq_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusBlockVertex s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
    lPlusPairFullVertexId x k z (lPlusBlockVertexRawLabel a) =
        lPlusPairFullVertexId x k z (lPlusBlockVertexRawLabel b) ↔
      lPlusBlockVertexImage s.hτ a = lPlusBlockVertexImage s.hτ b := by
  dsimp only
  exact (lPlusPairFullVertexId_eq_iff x k _ _ _).trans
    (lPlusPairFullVertexEqvGen_iff_of_aligned x k r s hk a b)

/-- Helper toward Lemma 5.5. An intrinsic prefix attachment really is
an allocated geometric edge, rather than an accidental unused raw label. -/
theorem lPlusPrefixPrimedEdgeAttachment_allocated_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) (a b : ℕ)
    (hab : lPlusPrefixPrimedEdgeAttachment x k r a b) :
    a ∈ boundaryGluingPrefixMinusEdges s.W s.h k ∧
      a = boundaryGluingPrimedEdgeMap s.W s.h k s.hτ b := by
  obtain ⟨L, hL, m, hm, i, hi, hj⟩ := hab
  have hlist := lPlusStoppedPrefixStage_upperLeftList_of_aligned x k r s hk
  have hL' := Option.some.inj (hlist.symm.trans hL)
  have ha : a ∈ boundaryGluingUpperLeftEdges s.W s.h k := by
    have hmem := List.mem_of_getElem? hi
    rw [← hL'] at hmem
    exact List.mem_reverse.mp hmem
  have ha' := ((Set.ext_iff.mp (boundaryGluingPrefixMinusEdges_inter_primedEdges
    s.W s.h k s.hτ s.hfin hk) a).mpr ha).1
  exact ⟨ha', (lPlusPrefixPrimedEdgeAttachment_iff_of_aligned
    x k r s hk a b ha').mp ⟨L, hL, m, hm, i, hi, hj⟩⟩

/-- Helper toward Lemma 5.5. The raw primed/hatted edge test has exactly
the geometric edge kernel, retaining parallel and missing edge identities. -/
theorem lPlusPairPrimedHattedEdgeGluing_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (a b : ℕ) :
    lMinusRawCodeEdgeGluing (decodeLMinus x 0 (r.code.2.2, r.code.2.1))
      (boundaryFutureHattedPath k s.W) a b ↔
      boundaryGluingPrimedEdgeMap s.W s.h k s.hτ a =
        boundaryGluingHatEdgeMap s.W s.h k s.hτ b := by
  have hboundary (i : ℕ) : lMinusPrimedBoundaryEdge r.code.2.2 i
      (primedBeta0EdgeIndex (boundaryGluingFutureStream s.W s.h k) s.hτ s.hfin
        (hatBoundaryHitWitnesses _ s.hτ) s.hfin i) := by
    rw [← s.primedCode_eq]
    exact lMinusPrimedBoundaryEdge_observation (longest := s.longest) s.hτ s.hfin i
  rw [lMinus_cross_edge_eq_iff s.hτ s.hfin]
  constructor
  · rintro ⟨i, hi, hb⟩
    have ha := lMinusPrimedBoundaryEdge_unique _ i a _ hi (hboundary i)
    change kmswLeftBoundaryEdge
      (boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k s.W))) i = b at hb
    rw [boundaryGluing_decoded_stream s.W s.h k s.hτ] at hb
    exact ⟨i, ha, hb.symm⟩
  · rintro ⟨i, ha, hb⟩
    refine ⟨i, ha.symm ▸ hboundary i, ?_⟩
    rw [boundaryGluing_decoded_stream s.W s.h k s.hτ]
    exact hb.symm

/-- Helper toward Lemma 5.5. The raw edge image is a proof-only map
into source geometric edge labels. -/
@[expose] noncomputable def lPlusPairRawEdgeImage
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) : LPlusRawEdge → ℕ
  | .inl e => e
  | .inr (.inl e) => boundaryGluingPrimedEdgeMap W h k hτ e
  | .inr (.inr e) => boundaryGluingHatEdgeMap W h k hτ e

/-- Helper toward Lemma 5.5. Existing raw edge chains cannot identify
geometrically distinct edges, even through unused raw labels. -/
theorem lPlusRawEdgeEqvGen_sound_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusRawEdge)
    (hab : Relation.EqvGen (lPlusRawEdgeGenerator x k
      (r, boundaryFutureHattedPath k s.W)) a b) :
    lPlusPairRawEdgeImage s.hτ a = lPlusPairRawEdgeImage s.hτ b := by
  induction hab with
  | rel a b hab =>
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · exact hab.elim
    · exact (lPlusPrefixPrimedEdgeAttachment_allocated_of_aligned x k r s hk a b hab).2
    · exact hab.elim
    · exact hab.elim
    · exact hab.elim
    · exact (lPlusPairPrimedHattedEdgeGluing_iff_of_aligned x k r s a b).mp hab
    · exact hab.elim
    · exact hab.elim
    · exact hab.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Helper toward Lemma 5.5. Forget dart bits while retaining each block
and geometric edge identity. -/
@[expose] def lPlusBlockDartRawEdgeLabel {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {M : GeometricSideSubmap} : LPlusBlockDart W h k M → LPlusRawEdge
  | .inl d => .inl d.val.1
  | .inr (.inl d) => .inr (.inl d.1)
  | .inr (.inr d) => .inr (.inr d.val.1)

/-- Helper toward Lemma 5.5. The existing measurable least-token edge IDs
have the exact geometric edge kernel on the full source dart carrier. -/
theorem lPlusRawEdgeClosureId_eq_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusRawEdgeClosureId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawEdgeLabel a) =
      lPlusRawEdgeClosureId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawEdgeLabel b) ↔
      (lPlusBlockDartImage s.hτ a).1 = (lPlusBlockDartImage s.hτ b).1 := by
  rw [lPlusRawEdgeClosureId_eq_iff]
  constructor
  · intro hab
    have h := lPlusRawEdgeEqvGen_sound_of_aligned x k r s hk _ _ hab
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> exact h
  · intro hab
    have hPH (a : LPlusPrefixDart s.W s.h k) (b : ℕ × Bool)
        (hab : a.val.1 = boundaryGluingHatEdgeMap s.W s.h k s.hτ b.1) : False := by
      have hm : a.val.1 ∈ boundaryGluingPrefixMinusEdges s.W s.h k ∩
          Set.range (boundaryGluingHatEdgeMap s.W s.h k s.hτ) :=
        ⟨a.property, b.1, hab.symm⟩
      rw [boundaryGluingPrefixMinusEdges_inter_hatRange s.W s.h k s.hτ hk] at hm
      exact hm
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · change a.val.1 = b.val.1 at hab
      rw [show lPlusBlockDartRawEdgeLabel (.inl a) = .inl a.val.1 from rfl,
        show lPlusBlockDartRawEdgeLabel (.inl b) = .inl b.val.1 from rfl, hab]
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _
        ((lPlusPrefixPrimedEdgeAttachment_iff_of_aligned x k r s hk a.val.1 b.1 a.property).mpr hab)
    · exact (hPH a b.val hab).elim
    · apply Relation.EqvGen.symm
      exact Relation.EqvGen.rel _ _
        ((lPlusPrefixPrimedEdgeAttachment_iff_of_aligned x k r s hk b.val.1 a.1 b.property).mpr hab.symm)
    · have h := boundaryGluingPrimedEdgeMap_injective s.W s.h k s.hτ hab
      change Relation.EqvGen (lPlusRawEdgeGenerator x k (r, boundaryFutureHattedPath k s.W))
        (.inr (.inl a.1)) (.inr (.inl b.1))
      rw [h]
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _
        ((lPlusPairPrimedHattedEdgeGluing_iff_of_aligned x k r s a.1 b.val.1).mpr hab)
    · exact (hPH b a.val hab.symm).elim
    · apply Relation.EqvGen.symm
      exact Relation.EqvGen.rel _ _
        ((lPlusPairPrimedHattedEdgeGluing_iff_of_aligned x k r s b.1 a.val.1).mpr hab.symm)
    · have h := boundaryGluingHatEdgeMap_injective s.W s.h k s.hτ hab
      change Relation.EqvGen (lPlusRawEdgeGenerator x k (r, boundaryFutureHattedPath k s.W))
        (.inr (.inr a.val.1)) (.inr (.inr b.val.1))
      rw [h]
      exact Relation.EqvGen.refl _

/-- Helper toward Lemma 5.5. Raw block dart labels retain both edge
identity and the local endpoint bit before primed orientation correction. -/
@[expose] def lPlusBlockDartRawLabel {W : ℤ → Fin 3}
    {h : BoundaryHitWitnesses (shiftedStream W 0)} {k : ℤ}
    {M : GeometricSideSubmap} : LPlusBlockDart W h k M → LPlusRawEdge × Bool
  | .inl d => (.inl d.val.1, d.val.2)
  | .inr (.inl d) => (.inr (.inl d.1), d.2)
  | .inr (.inr d) => (.inr (.inr d.val.1), d.val.2)

/-- Helper toward Lemma 5.5. The existing measurable raw dart bit is
exactly the endpoint bit in the geometric glued side. -/
theorem lPlusPairRawDartBit_eq_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (a : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusPairRawDartBit x (r, boundaryFutureHattedPath k s.W)
      (lPlusBlockDartRawLabel a) = (lPlusBlockDartImage s.hτ a).2 := by
  rcases a with a | (a | a)
  · rfl
  · have hf := lMinusCodePrimedSideFlip_observation
      (longest := s.longest) s.hτ s.hfin a.1
    change decide (∃ i, lMinusPrimedBoundaryEdge
      (hatLawPrimedCodes (boundaryFutureCode k s.W)) i a.1) = _ at hf
    change (a.2 ^^ decide (∃ i, lMinusPrimedBoundaryEdge r.code.2.2 i a.1)) = _
    rw [← s.primedCode_eq, hf]
    rfl
  · rfl

/-- Helper toward Lemma 5.5. The predecessor's measurable dart IDs have
the full geometric dart kernel, including distinct parallel edges, missing
edges and corrected primed bits. No source-class identity is assumed. -/
theorem lPlusPairRawDartId_eq_iff_of_aligned
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k)
    (a b : LPlusBlockDart s.W s.h k
      (lPlusHattedSide (W := s.W) (h := s.h) (k := k) s.longest s.hqMode)) :
    lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawLabel a) =
      lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
        (lPlusBlockDartRawLabel b) ↔
      lPlusBlockDartImage s.hτ a = lPlusBlockDartImage s.hτ b := by
  rw [lPlusPairRawDartId, lPlusPairRawDartId, Prod.ext_iff]
  have ha : (lPlusBlockDartRawLabel a).1 = lPlusBlockDartRawEdgeLabel a := by
    rcases a with a | (a | a) <;> rfl
  have hb : (lPlusBlockDartRawLabel b).1 = lPlusBlockDartRawEdgeLabel b := by
    rcases b with b | (b | b) <;> rfl
  rw [ha, hb, lPlusRawEdgeClosureId_eq_iff_of_aligned x k r s hk a b,
    lPlusPairRawDartBit_eq_of_aligned x k r s a,
    lPlusPairRawDartBit_eq_of_aligned x k r s b]
  exact Prod.ext_iff.symm

/-- Helper toward Lemma 5.5. The full measurable vertex numbering
descends to the actual geometric gluing quotient by the proved kernel theorem. -/
@[expose] noncomputable def lPlusPairGluedVertexId
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    LPlusGluedVertex s.longest s.hqMode s.hτ → ℕ :=
  Quotient.lift
    (fun a => lPlusPairFullVertexId x k
      ⟨(r, boundaryFutureHattedPath k s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x k r s⟩
      (lPlusBlockVertexRawLabel a))
    (fun a b hab => (lPlusPairFullVertexId_eq_iff_of_aligned x k r s hk a b).mpr hab)

/-- Helper toward Lemma 5.5. The induced numbering is injective on the
entire geometric vertex quotient, rather than just shared-edge endpoints. -/
theorem lPlusPairGluedVertexId_injective
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    Function.Injective (lPlusPairGluedVertexId x k r s hk) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b hab
  exact Quotient.sound ((lPlusPairFullVertexId_eq_iff_of_aligned x k r s hk a b).mp hab)

/-- Helper toward Lemma 5.5. The predecessor's measurable dart numbering
descends to the actual geometric dart quotient, with primed bits corrected. -/
@[expose] noncomputable def lPlusPairGluedDartId
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    LPlusGluedDart s.longest s.hqMode s.hτ → ℕ × Bool :=
  Quotient.lift
    (fun a => lPlusPairRawDartId x k (r, boundaryFutureHattedPath k s.W)
      (lPlusBlockDartRawLabel a))
    (fun a b hab => (lPlusPairRawDartId_eq_iff_of_aligned x k r s hk a b).mpr hab)

/-- Helper toward Lemma 5.5. The geometric dart quotient embeds into the
measurable raw coordinates, retaining both darts of each geometric edge. -/
theorem lPlusPairGluedDartId_injective
    (x : XDP) (k : ℤ) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r) (hk : 0 ≤ k) :
    Function.Injective (lPlusPairGluedDartId x k r s hk) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b hab
  exact Quotient.sound ((lPlusPairRawDartId_eq_iff_of_aligned x k r s hk a b).mp hab)

/-- Helper toward Lemma 5.5. At zero the shared-edge-only vertex IDs
separate two representatives of the same source root, whereas the full IDs
identify them. This records the concrete obstruction to the earlier route. -/
theorem lPlusPairVertexId_zero_root_gap
    (x : XDP) (r : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x 0 r) :
    let z : lPlusCertifiedCodingPairDomain x :=
      ⟨(r, boundaryFutureHattedPath 0 s.W),
        LPlusSourceWitnessAligned.codingPair_mem_domain x 0 r s⟩
    lPlusPairRawVertexId x 0 z (.inl 0) ≠
        lPlusPairRawVertexId x 0 z (.inr (.inl 1)) ∧
      lPlusPairFullVertexId x 0 z (.inl 0) =
        lPlusPairFullVertexId x 0 z (.inr (.inl 1)) := by
  dsimp only
  let z : lPlusCertifiedCodingPairDomain x :=
    ⟨(r, boundaryFutureHattedPath 0 s.W),
      LPlusSourceWitnessAligned.codingPair_mem_domain x 0 r s⟩
  let f : LPlusPairRawVertex → Option ℕ :=
    fun v => match v with | .inl u => some u | .inr _ => none
  have hrel (u v : LPlusPairRawVertex)
      (huv : lPlusPairRawVertexGenerator x 0 z u v) : f u = f v := by
    rcases u with u | (u | u) <;> rcases v with v | (v | v)
    · exact huv.elim
    · obtain ⟨a, b, t, hab, _, _⟩ := huv
      have ha := (lPlusPrefixPrimedEdgeAttachment_allocated_of_aligned
        x 0 r s (le_refl 0) a b hab).1
      rw [boundaryGluingPrefixMinusEdges_zero] at ha
      exact ha.elim
    · exact huv.elim
    · exact huv.elim
    · rfl
    · rfl
    · exact huv.elim
    · rfl
    · rfl
  constructor
  · intro hid
    have heq := (lPlusPairRawVertexId_eq_iff x 0 z _ _).mp hid
    have hf : ∀ u v, Relation.EqvGen (lPlusPairRawVertexGenerator x 0 z) u v → f u = f v := by
      intro u v h
      induction h with
      | rel u v h => exact hrel u v h
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hbad : (some 0 : Option ℕ) = none := hf _ _ heq
    cases hbad
  · apply (lPlusPairFullVertexId_eq_iff x 0 z _ _).mpr
    exact Relation.EqvGen.rel _ _ (Or.inl ⟨rfl, rfl, rfl⟩)

end DirectedDistances.PaperProofs.Section5

























































/- all 37 declarations in this file (25 theorems and 12 definitions), compiled
[propext, Classical.choice, Quot.sound] for each declaration. No `sorryAx` or
custom axiom occurred in any transitive list. All probe commands were removed
before the final production compile. The production/probe command was:


One compile was run at a time. No build, dependency/cache change, separate
and axiom closure certify these helpers only; the complete marked-side and -/
