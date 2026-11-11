/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusCanonicalCoding

/-! Certified cylinder events and directly accessible canonical coordinates.
The hatted truncations are marked isomorphism classes, whereas the canonical
side uses ambient hatted labels. No reconstruction of those labels is assumed. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. The simultaneous certified-coordinate domain. -/
@[expose] def lMinusCertifiedPresentationDomain (x : XDP) :
    Set (LMinusSidePresentation x) :=
  {r | ∀ i : ℕ, r.code.2 i ∈ Set.range (halfTruncate .left i)}

/-- Helper toward Lemma 5.5. The simultaneous domain is measurable. -/
theorem measurableSet_lMinusCertifiedPresentationDomain (x : XDP) :
    MeasurableSet (lMinusCertifiedPresentationDomain x) := by
  unfold lMinusCertifiedPresentationDomain
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (show MeasurableSet (Set.range (halfTruncate .left i)) from trivial).preimage
      ((measurable_pi_apply i).comp (measurable_lMinusSidePresentation_code x).snd))

/-- Helper toward Lemma 5.5. The exact observed law gives this domain full measure. -/
theorem ae_mem_lMinusCertifiedPresentationDomain (x : XDP) (k : ℤ) (hk : k ≤ 0) :
    ∀ᵐ r ∂(wholePlaneIIDCodeMeasure.map
      (fun W => decodeLMinus x k (leftSideObsNonpos x k W))),
      r ∈ lMinusCertifiedPresentationDomain x :=
  ae_lMinusSidePresentation_hatted_mem_range x k hk

/-- Helper toward Lemma 5.5. A certified window also defines a cylinder
on the original presentation space, without a dependent domain parameter. -/
@[expose] def lMinusCertifiedCylinder (x : XDP) (N : ℕ)
    (c : LMinusFiniteTruncationWindow N) : Set (LMinusSidePresentation x) :=
  {r | lMinusFiniteCodeWindow N r = (c.1, fun i => (c.2 i).val)}

/-- Helper toward Lemma 5.5. Each certified cylinder is measurable globally. -/
theorem measurableSet_lMinusCertifiedCylinder (x : XDP) (N : ℕ)
    (c : LMinusFiniteTruncationWindow N) :
    MeasurableSet (lMinusCertifiedCylinder x N c) :=
  measurableSet_lMinusFiniteCodeWindow x N (c.1, fun i => (c.2 i).val)

/-- Helper toward Lemma 5.5. An arbitrary selection of certified windows
gives a measurable countable union of cylinders. This does not identify any
geometric relation with that union. -/
theorem measurableSet_iUnion_lMinusCertifiedCylinder (x : XDP)
    (A : (N : ℕ) → Set (LMinusFiniteTruncationWindow N)) :
    MeasurableSet (⋃ N, ⋃ c ∈ A N, lMinusCertifiedCylinder x N c) := by
  apply MeasurableSet.iUnion
  intro N
  let : Countable (LMinusFiniteTruncationWindow N) :=
    countable_lMinusFiniteTruncationWindow N
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion
    (fun _ => measurableSet_lMinusCertifiedCylinder x N c))

/-- Helper toward Lemma 5.5. The certified cylinders cover exactly the
finite coordinate-range domain, including unrealized presentations. -/
theorem iUnion_lMinusCertifiedCylinder (x : XDP) (N : ℕ) :
    (⋃ c : LMinusFiniteTruncationWindow N, lMinusCertifiedCylinder x N c) =
      {r : LMinusSidePresentation x |
        ∀ i : Fin N, r.code.2 i.val ∈ Set.range (halfTruncate .left i.val)} := by
  ext r
  constructor
  · intro hr
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hr
    have he := congrArg Prod.snd hc
    intro i
    have hi := congrFun he i
    change r.code.2 i.val = (c.2 i).val at hi
    rw [hi]
    exact (c.2 i).property
  · intro hr
    refine Set.mem_iUnion.mpr ⟨(fun i => r.code.1 i.val,
      fun i => ⟨r.code.2 i.val, hr i⟩), ?_⟩
    rfl

/-- Helper toward Lemma 5.5. Eventual truth of finite-window cylinder
tests is measurable too; eventual stability need not be finite determination. -/
theorem measurableSet_lMinusCertifiedCylinder_eventually (x : XDP)
    (A : (N : ℕ) → Set (LMinusFiniteTruncationWindow N)) :
    MeasurableSet (⋃ t : ℕ, ⋂ N : ℕ, ⋂ (_ : t ≤ N),
      ⋃ c ∈ A N, lMinusCertifiedCylinder x N c) := by
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iInter
  intro N
  apply MeasurableSet.iInter
  intro _
  let : Countable (LMinusFiniteTruncationWindow N) :=
    countable_lMinusFiniteTruncationWindow N
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion
    (fun _ => measurableSet_lMinusCertifiedCylinder x N c))

/-- Helper toward Lemma 5.5. The shared primed boundary relation is an
eventual finite-prefix test and is measurable on the primed code space. -/
theorem measurableSet_lMinusPrimedBoundaryEdge (i e : ℕ) :
    MeasurableSet {p : ℕ → Fin 3 | lMinusPrimedBoundaryEdge p i e} := by
  have hstage (n : ℕ) : Measurable
      (fun p : ℕ → Fin 3 => (kmswStage p n).UR.reverse[i]? = some e) := by
    apply measurable_of_factors_prefix n
    intro p p' hp
    rw [kmswStage_congr hp]
  apply measurableSet_setOfPred.mpr
  change Measurable (fun p : ℕ → Fin 3 =>
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (kmswStage p n).UR.reverse[i]? = some e)
  exact Measurable.exists (fun N => Measurable.forall (fun n =>
    measurable_const.imp (hstage n)))

/-- Helper toward Lemma 5.5. The exact primed orientation correction is
measurable on presentations, including unrealized presentations. -/
theorem measurable_lMinusCodePrimedSideFlip (x : XDP) (e : ℕ) :
    Measurable (fun r : LMinusSidePresentation x => lMinusCodePrimedSideFlip r e) := by
  have hboundary (i : ℕ) : MeasurableSet {r : LMinusSidePresentation x |
      lMinusPrimedBoundaryEdge r.code.1 i e} :=
    (measurableSet_lMinusPrimedBoundaryEdge i e).preimage
      (measurable_lMinusSidePresentation_code x).fst
  apply measurable_to_bool
  change MeasurableSet {r : LMinusSidePresentation x |
    decide (∃ i, lMinusPrimedBoundaryEdge r.code.1 i e) = true}
  simpa only [decide_eq_true_eq, Set.iUnion_ofPred] using
    MeasurableSet.iUnion hboundary

/-- Helper toward Lemma 5.5. Fixed primed dart endpoints are measurable
before any vertex quotient or canonical relabeling is applied. -/
theorem measurable_lMinusPrimedDartEndpoint (x : XDP) (e : ℕ) (s : Bool) :
    Measurable (fun r : LMinusSidePresentation x =>
      kmswLimitDartVertex r.code.1 (e, s ^^ lMinusCodePrimedSideFlip r e)) := by
  have hfixed (b : Bool) : Measurable (fun r : LMinusSidePresentation x =>
      kmswLimitDartVertex r.code.1 (e, b)) := by
    refine (measurable_of_factors_prefix e
      (fun p : ℕ → Fin 3 => kmswLimitDartVertex p (e, b)) ?_).comp
        (measurable_lMinusSidePresentation_code x).fst
    intro p p' hp
    simp only [kmswLimitDartVertex, edgeWest, edgeEast, kmswStage_congr hp]
  have hpair : Measurable (fun z : Bool × LMinusSidePresentation x =>
      kmswLimitDartVertex z.2.code.1 (e, z.1)) :=
    measurable_from_prod_countable_right hfixed
  exact hpair.comp (((measurable_of_finite (fun b : Bool => s ^^ b)).comp
    (measurable_lMinusCodePrimedSideFlip x e)).prodMk measurable_id)

/-- Helper toward Lemma 5.5. Missing-root stages retain finite-prefix dependence. -/
theorem lMinusMissingRootStage_eq_of_prefix (p p' : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, p i = p' i) :
    kmswMissingRootStage p n = kmswMissingRootStage p' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change kmswStep (kmswMissingRootStage p n) (p n) =
      kmswStep (kmswMissingRootStage p' n) (p' n)
    rw [ih (fun i hi => hp i (by omega)), hp n (by omega)]

/-- Helper toward Lemma 5.5. The primed directed-presence test used in
the canonical side is measurable and preserves the missing-root initialization. -/
theorem measurableSet_lMinusPrimedPresent (x : XDP) (e : ℕ) :
    MeasurableSet {r : LMinusSidePresentation x |
      ∃ n, e < (kmswMissingRootStage r.code.1 n).nextEdge ∧
        (kmswMissingRootStage r.code.1 n).present e = true} := by
  have hstage (n : ℕ) : MeasurableSet {r : LMinusSidePresentation x |
      e < (kmswMissingRootStage r.code.1 n).nextEdge ∧
        (kmswMissingRootStage r.code.1 n).present e = true} := by
    refine (measurableSet_of_factors_prefix n
      (fun p : ℕ → Fin 3 => e < (kmswMissingRootStage p n).nextEdge ∧
        (kmswMissingRootStage p n).present e = true) ?_).preimage
          (measurable_lMinusSidePresentation_code x).fst
    intro p p' hp
    rw [lMinusMissingRootStage_eq_of_prefix p p' n hp]
  simpa only [Set.iUnion_ofPred] using MeasurableSet.iUnion hstage

/-- Helper toward Lemma 5.5. Raw hatted vertex membership is measurable
on coherent paths. Descent to the truncation presentation is separate. -/
theorem measurableSet_lMinusCoherentLeftSide_vertices (x : XDP) (v : ℕ) :
    MeasurableSet {q : Coherent x | v ∈ (lMinusCoherentLeftSide x q).vertices} := by
  change MeasurableSet {q : Coherent x | v ∈ ⋃ s,
    geometricAncestorVertices x renewalTime renewalTime_positiveSuccessTime .left q s}
  simp only [Set.mem_iUnion, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun s => measurableSet_geometricAncestorVertices x .left s v)

/-- Helper toward Lemma 5.5. Raw hatted edge membership is measurable
on coherent paths, including missing geometric edges. -/
theorem measurableSet_lMinusCoherentLeftSide_edges (x : XDP) (e : ℕ) :
    MeasurableSet {q : Coherent x | e ∈ (lMinusCoherentLeftSide x q).edges} := by
  change MeasurableSet {q : Coherent x | e ∈ ⋃ s,
    geometricAncestorEdges x renewalTime renewalTime_positiveSuccessTime .left q s}
  simp only [Set.mem_iUnion, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun s => measurableSet_geometricAncestorEdges x .left s e)

/-- Helper toward Lemma 5.5. Raw hatted incidence is measurable on the
coherent-path domain with its inherited sigma algebra. -/
theorem measurableSet_lMinusCoherentLeftSide_incident (x : XDP)
    (d : ℕ × Bool) (v : ℕ) :
    MeasurableSet {q : Coherent x |
      (if d.2 then (lMinusCoherentLeftSide x q).east d.1
        else (lMinusCoherentLeftSide x q).west d.1) = v} := by
  have h : Measurable (fun q : Coherent x =>
      if d.2 then (lMinusCoherentLeftSide x q).east d.1
        else (lMinusCoherentLeftSide x q).west d.1) := by
    cases hd : d.2
    · exact measurable_geometricRightSide_west x d.1
    · exact measurable_geometricRightSide_east x d.1
  exact (h.eq_const v).setOf

section CoherentRelations

local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" => (fun (x : XDP) (q : Coherent x) =>
  sourceAncestor_finite_incidence x renewalTime renewalTime_positiveSuccessTime q)

/-- Helper toward Lemma 5.5. Raw hatted induced rotation is measurable
on coherent paths by the countable first-return test. This asserts no
finite deciding truncation for an ambient raw label. -/
theorem measurableSet_lMinusCoherentLeftSide_rotation (x : XDP)
    (d e : ℕ × Bool) :
    MeasurableSet {q : Coherent x | (lMinusCoherentLeftSide x q).rotation d e} := by
  have hedge (j : ℕ) : Measurable (fun q : Coherent x =>
      ((kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∈
        (lMinusCoherentLeftSide x q).edges) := by
    have hG : Measurable (fun z : ℕ × Coherent x =>
        z.1 ∈ (lMinusCoherentLeftSide x z.2).edges) :=
      measurable_from_prod_countable_right (fun n =>
        measurableSet_setOfPred.mp (measurableSet_lMinusCoherentLeftSide_edges x n))
    have hcomp := hG.comp
      ((measurable_coherentRotation_iterate x d j).fst.prodMk measurable_id)
    simpa only [Function.comp_def, id_eq] using hcomp
  apply measurableSet_setOfPred.mpr
  change Measurable (fun q : Coherent x => ∃ k : ℕ, 0 < k ∧
    (kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[k] d = e ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot (W q) (HF x q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉
          (lMinusCoherentLeftSide x q).edges)
  exact Measurable.exists (fun k => measurable_const.and
    (((measurable_coherentRotation_iterate x d k).eq_const e).and
      (Measurable.forall (fun j => measurable_const.imp
        (measurable_const.imp (hedge j).not)))))

/-- Helper toward Lemma 5.5. Raw hatted retained-face succession is
measurable on coherent paths through triangle-list certificates. Its
factorization through the truncation code is not used as a premise. -/
theorem measurableSet_lMinusCoherentLeftSide_faceNext (x : XDP)
    (d e : ℕ × Bool) :
    MeasurableSet {q : Coherent x | (lMinusCoherentLeftSide x q).faceNext d e} := by
  have hedges (l : List (ℕ × Bool)) : MeasurableSet {q : Coherent x |
      ∀ z ∈ l, z.1 ∈ (lMinusCoherentLeftSide x q).edges} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun z => MeasurableSet.imp
      (MeasurableSet.const (z ∈ l)) (measurableSet_lMinusCoherentLeftSide_edges x z.1))
  have hm : MeasurableSet {q : Coherent x | ∃ (j : ℕ) (l : List (ℕ × Bool)),
      (∃ h : (W q) j = 0 ∨ (W q) j = 1, stageTriangleDartList (W q) ⟨j, h⟩ = l) ∧
      d ∈ l ∧ ∀ z ∈ l, z.1 ∈ (lMinusCoherentLeftSide x q).edges} := by
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun l =>
      (measurableSet_coherentTriangleList x j l).inter
        ((MeasurableSet.const (d ∈ l)).inter (hedges l)))
  have he : {q : Coherent x | (lMinusCoherentLeftSide x q).faceNext d e} =
      {q : Coherent x | ∃ (j : ℕ) (l : List (ℕ × Bool)),
        (∃ h : (W q) j = 0 ∨ (W q) j = 1, stageTriangleDartList (W q) ⟨j, h⟩ = l) ∧
        d ∈ l ∧ ∀ z ∈ l, z.1 ∈ (lMinusCoherentLeftSide x q).edges} ∩
        {q : Coherent x | kmswInfFaceSucc (W q) (HF x q) d = e} := by
    ext q
    constructor
    · rintro ⟨⟨j, hd, hall⟩, he⟩
      exact ⟨⟨j.val, stageTriangleDartList (W q) j, ⟨j.property, rfl⟩, hd, hall⟩, he⟩
    · rintro ⟨⟨j, l, ⟨hj, hl⟩, hd, hall⟩, he⟩
      subst l
      exact ⟨⟨⟨j, hj⟩, hd, hall⟩, he⟩
  rw [he]
  exact hm.inter ((measurable_coherentFaceSucc x d).eq_const e).setOf

end CoherentRelations

/-- Helper toward Lemma 5.5. The primed root edge has canonical token zero. -/
theorem lMinusCanonicalEdgeId_primed_zero {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    lMinusCanonicalEdgeId r M (⟦Sum.inl 0⟧) = 0 := by
  have h := lMinusCanonicalEdgeId_le_token r M (Sum.inl 0)
  change lMinusCanonicalEdgeId r M (⟦Sum.inl 0⟧) ≤ 2 * 0 at h
  omega

/-- Helper toward Lemma 5.5. Hatted candidates reduce to their own odd
token and the even tokens of directly shared primed boundary edges. -/
theorem lMinusCanonicalEdgeCandidate_hatted_iff {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (e : (lMinusCoherentLeftSide x q).edges) (n : ℕ) :
    lMinusCanonicalEdgeCandidate r (lMinusCoherentLeftSide x q)
      (⟦Sum.inr e⟧) n ↔
      n = 2 * e.val + 1 ∨ ∃ a : ℕ, n = 2 * a ∧
        lMinusCodeEdgeGluing r (lMinusCoherentLeftSide x q) (.inl a) (.inr e) := by
  rw [lMinusCanonicalEdgeCandidate_normal_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    cases b with
    | inl a => exact Or.inr ⟨a, hb.symm, he⟩
    | inr b =>
      change b = e at he
      subst b
      exact Or.inl hb.symm
  · rintro (hn | ⟨a, hn, he⟩)
    · exact ⟨.inr e, hn.symm, rfl⟩
    · exact ⟨.inl a, hn.symm, he⟩

/-- Helper toward Lemma 5.5. Away from the hatted boundary the minimal
glued token remains the ambient hatted label's odd token. Thus minimizing
the glued quotient does not itself relabel the hatted interior intrinsically. -/
theorem lMinusCanonicalEdgeId_hatted_of_not_boundary {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x)
    (e : (lMinusCoherentLeftSide x q).edges)
    (he : ∀ i, ((lMinusCoherentLeftSide x q).boundary i).1 ≠ e.val) :
    lMinusCanonicalEdgeId r (lMinusCoherentLeftSide x q) (⟦Sum.inr e⟧) =
      2 * e.val + 1 := by
  apply (lMinusCanonicalEdgeId_eq_iff r _ _ _).mpr
  refine ⟨⟨Sum.inr e, rfl, rfl⟩, ?_⟩
  intro m hm hc
  rcases (lMinusCanonicalEdgeCandidate_hatted_iff r q e m).mp hc with
    hm' | ⟨a, _, hglue⟩
  · omega
  · obtain ⟨i, _, hi⟩ := hglue
    exact he i hi

/-- Helper toward Lemma 5.5. The entire zeroth canonical boundary dart is fixed. -/
theorem lMinusCanonicalSide_boundary_zero (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    (lMinusCanonicalSide x r q hf).boundary 0 = (0, true) := by
  apply Prod.ext
  · exact lMinusCanonicalEdgeId_primed_zero r _
  · rfl

/-- Helper toward Lemma 5.5. Every exterior dart keeps its reversed bit. -/
theorem lMinusCanonicalSide_boundary_snd (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (i : ℕ) :
    ((lMinusCanonicalSide x r q hf).boundary i).2 = true := rfl

/-- Helper toward Lemma 5.5. Every seam dart keeps its forward bit. -/
theorem lMinusCanonicalSide_seam_snd (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (i : ℕ) :
    ((lMinusCanonicalSide x r q hf).seam i).2 = false := rfl

/-- Helper toward Lemma 5.5. The zeroth edge coordinate of the complete code is fixed. -/
theorem lMinusCanonicalSide_zero_mem_edges (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    0 ∈ (lMinusCanonicalSide x r q hf).edges :=
  ⟨⟦Sum.inl 0⟧, lMinusCanonicalEdgeId_primed_zero r _⟩

/-- Helper toward Lemma 5.5. The allocated primed vertex zero also has
canonical token zero, independently of all vertex identifications. -/
theorem lMinusCanonicalVertexId_primed_zero {x : XDP}
    (r : LMinusSidePresentation x) (M : GeometricSideSubmap) :
    lMinusCanonicalVertexId r M
      ⟨⟦Sum.inl 0⟧, Or.inl ⟨0, rfl⟩⟩ = 0 := by
  apply (lMinusCanonicalVertexId_eq_iff r M _ 0).mpr
  refine ⟨⟨Sum.inl 0, rfl, rfl⟩, ?_⟩
  intro m hm
  omega

/-- Helper toward Lemma 5.5. Vertex zero is retained by the canonical side. -/
theorem lMinusCanonicalSide_zero_mem_vertices (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) :
    0 ∈ (lMinusCanonicalSide x r q hf).vertices :=
  ⟨⟨⟦Sum.inl 0⟧, Or.inl ⟨0, rfl⟩⟩,
    lMinusCanonicalVertexId_primed_zero r _⟩

/-- Helper toward Lemma 5.5. All canonical exterior orientation bits are
measurable, with no regularity premise on the chosen coherent preimage. -/
theorem measurable_lMinusCanonicalSide_boundary_snd {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) :
    Measurable (fun ω => fun i : ℕ =>
      ((lMinusCanonicalSide x (r ω) (q ω) (hf ω)).boundary i).2) := by
  simp only [lMinusCanonicalSide_boundary_snd]
  exact measurable_const

/-- Helper toward Lemma 5.5. All canonical seam orientation bits are measurable. -/
theorem measurable_lMinusCanonicalSide_seam_snd {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) :
    Measurable (fun ω => fun i : ℕ =>
      ((lMinusCanonicalSide x (r ω) (q ω) (hf ω)).seam i).2) := by
  simp only [lMinusCanonicalSide_seam_snd]
  exact measurable_const

/-- Helper toward Lemma 5.5. The full zeroth boundary coordinate is measurable. -/
theorem measurable_lMinusCanonicalSide_boundary_zero {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) :
    Measurable (fun ω => (lMinusCanonicalSide x (r ω) (q ω) (hf ω)).boundary 0) := by
  simp only [lMinusCanonicalSide_boundary_zero]
  exact measurable_const

/-- Helper toward Lemma 5.5. The zeroth vertex-membership code is measurable. -/
theorem measurable_lMinusCanonicalSide_vertices_zero {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) :
    Measurable (fun ω => decide
      (0 ∈ (lMinusCanonicalSide x (r ω) (q ω) (hf ω)).vertices)) := by
  simp only [lMinusCanonicalSide_zero_mem_vertices, decide_true]
  exact measurable_const

/-- Helper toward Lemma 5.5. The zeroth edge-membership code is measurable. -/
theorem measurable_lMinusCanonicalSide_edges_zero {Ω : Type*}
    [MeasurableSpace Ω] (x : XDP) (r : Ω → LMinusSidePresentation x)
    (q : Ω → Coherent x) (hf : ∀ ω, KMSWFiniteIncidence (r ω).code.1) :
    Measurable (fun ω => decide
      (0 ∈ (lMinusCanonicalSide x (r ω) (q ω) (hf ω)).edges)) := by
  simp only [lMinusCanonicalSide_zero_mem_edges, decide_true]
  exact measurable_const

/-- Helper toward Lemma 5.5. The finite-incidence certificate needed by
the canonical constructor follows from the original source preimage. -/
theorem lMinusPreimage_primed_finiteIncidence {x : XDP} (q : LMinusPreimage x) :
    KMSWFiniteIncidence (lMinusCodeOf q).1 := by
  simpa only [lMinusCodeOf, q.mode_eq] using
    (lMinus_primed_observation_finiteIncidence (longest := q.longest) q.hτ q.hfin)

/-- Helper toward Lemma 5.5. The canonical side under the original
source-preimage binders, with its incidence certificate proved above. -/
@[expose] noncomputable def lMinusPreimageCanonicalSide {x : XDP}
    (q : LMinusPreimage x) : GeometricSideSubmap :=
  lMinusCanonicalSide x (decodeLMinus x q.k (lMinusCodeOf q)) q.hattedCoherent
    (lMinusPreimage_primed_finiteIncidence q)

/-- Helper toward Lemma 5.5. The source-preimage canonical side has
exactly the corrected decoder's class. -/
theorem lMinusPreimageCanonicalSide_class_eq {x : XDP} (q : LMinusPreimage x) :
    geometricSideClass (lMinusPreimageCanonicalSide q) =
      geometricSideClass (lMinusDecodedSide4 (W := q.W) (h := q.h) (k := q.k)
        (longest := q.longest) q.hτ q.hqMode q.hfin) := by
  rcases q with ⟨W, h, H, hLL, longest, hmode, k, hk, hp, hτ, hq, hfin, P, T, hl⟩
  cases hmode
  exact lMinusCanonicalSide_class_eq_decodedSide4 hτ hq hfin

/-- Helper toward Lemma 5.5. The exact optional reader agrees with each
source-preimage canonical side, without a measurability assumption. -/
theorem LMinusSidePresentation.classOption4_eq_some_canonical {x : XDP}
    (r : LMinusSidePresentation x) (q : LMinusPreimage x)
    (hc : lMinusCodeOf q = r.code) :
    r.classOption4 = some (geometricSideClass (lMinusPreimageCanonicalSide q)) := by
  rw [lMinusPreimageCanonicalSide_class_eq]
  exact r.classOption4_eq_some q hc

/-- Helper toward Lemma 5.5. Equal presentation codes identify the
canonical classes, without asserting equality of their ambient numeric IDs. -/
theorem lMinusPreimageCanonicalSide_class_eq_of_code_eq {x : XDP}
    (q q' : LMinusPreimage x) (hc : lMinusCodeOf q = lMinusCodeOf q') :
    geometricSideClass (lMinusPreimageCanonicalSide q) =
      geometricSideClass (lMinusPreimageCanonicalSide q') := by
  rw [lMinusPreimageCanonicalSide_class_eq, lMinusPreimageCanonicalSide_class_eq]
  exact (geometricSideClass_eq_iff _ _).mpr
    (lMinusDecodedSide4_markedIso_of_code_eq q q' hc)







































































end DirectedDistances.PaperProofs.Section5
