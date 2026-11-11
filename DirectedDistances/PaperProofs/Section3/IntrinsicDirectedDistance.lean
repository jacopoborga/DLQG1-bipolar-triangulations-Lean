/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart2

/-! # Intrinsic directed distances on retained geometric edges

Helpers toward Proposition 3.9, with the directed-path convention of
The additional missing predicate describes the cut; ambient missing edges
are also excluded. No finite-distance or cut-identification claim is made. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open scoped Classical

/-- Helper toward Proposition 3.9: a directed edge-list path on the map's
own vertices, using its own oriented endpoints and only retained present edges.
The empty path is allowed at every ambient vertex. -/
inductive IntrinsicDirectedEdgeListPath (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) : A.V → A.V → List A.E → Prop
  | nil (u : A.V) : IntrinsicDirectedEdgeListPath A S missing u u []
  | snoc {u v : A.V} {es : List A.E}
      (p : IntrinsicDirectedEdgeListPath A S missing u v es)
      (e : {e : A.E // ¬ A.map.toPlaneMapWithMissing.missing e})
      (retained : e.val ∈ S) (present : ¬ missing e.val)
      (incident : A.map.tail e = v) :
      IntrinsicDirectedEdgeListPath A S missing u (A.map.head e) (es ++ [e.val])

/-- Helper toward Proposition 3.9: the length of an intrinsic path is the
number of individual edges in its ordered list. -/
@[expose] def intrinsicDirectedPathLength {A : D39DomainRootedMap.{0}}
    {S : Set A.E} {missing : A.E → Prop} {u v : A.V}
    (p : {es : List A.E // IntrinsicDirectedEdgeListPath A S missing u v es}) : ℕ :=
  p.val.length

/-- Helper toward Proposition 3.9: all realized finite lengths, including
zero exactly when the endpoint vertices agree. -/
@[expose] def intrinsicDirectedReachableLengths (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) (u v : A.V) : Set ℕ :=
  {n | ∃ es : List A.E, IntrinsicDirectedEdgeListPath A S missing u v es ∧ es.length = n}

/-- Helper toward Proposition 3.9: shortest directed distance is the
infimum of realized lengths in ℕ∞; the empty infimum is ⊤. -/
@[expose] def intrinsicDirectedSDP (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) (u v : A.V) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ (_ : n ∈ intrinsicDirectedReachableLengths A S missing u v), (n : ℕ∞)

/-- Helper toward Proposition 3.9: longest directed distance is the
supremum of realized lengths in WithBot ℕ∞; unreachable is ⊥ and unbounded is ⊤. -/
@[expose] def intrinsicDirectedLDP (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) (u v : A.V) : WithBot ℕ∞ :=
  ⨆ n : ℕ, ⨆ (_ : n ∈ intrinsicDirectedReachableLengths A S missing u v),
    ((n : ℕ∞) : WithBot ℕ∞)

section Transport
variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: directed tails commute with geometric
isomorphisms, including changes in stored endpoint order. -/
theorem intrinsicDirected_tail_map
    (e : {e : A.E // ¬ A.map.toPlaneMapWithMissing.missing e}) :
    I.vertexEquiv (A.map.tail e) =
      B.map.tail ⟨I.edgeEquiv e.val, fun hm => e.property ((I.missing_map e.val).mp hm)⟩ := by
  have ho := I.orientation_map e.val e.property
  have hs := I.src_map e.val
  have ht := I.tgt_map e.val
  cases hf : A.map.forward e <;> cases hb : I.edgeFlip e.val <;>
    simp only [hf, hb, Bool.xor_false, Bool.false_xor, Bool.true_xor,
      Bool.not_true] at ho hs ht <;>
    simp only [DirectedPlaneMapWithMissing.tail, hf, ho, Bool.false_eq_true,
      ↓reduceIte, hs, ht]

/-- Helper toward Proposition 3.9: directed heads commute with geometric
isomorphisms even when the stored endpoints are reversed. -/
theorem intrinsicDirected_head_map
    (e : {e : A.E // ¬ A.map.toPlaneMapWithMissing.missing e}) :
    I.vertexEquiv (A.map.head e) =
      B.map.head ⟨I.edgeEquiv e.val, fun hm => e.property ((I.missing_map e.val).mp hm)⟩ := by
  have ho := I.orientation_map e.val e.property
  have hs := I.src_map e.val
  have ht := I.tgt_map e.val
  cases hf : A.map.forward e <;> cases hb : I.edgeFlip e.val <;>
    simp only [hf, hb, Bool.xor_false, Bool.false_xor, Bool.true_xor,
      Bool.not_true] at ho hs ht <;>
    simp only [DirectedPlaneMapWithMissing.head, hf, ho, Bool.false_eq_true,
      ↓reduceIte, hs, ht]

/-- Helper toward Proposition 3.9: mapping every individual edge transports
a path whenever retained edges and missing tags are transported. -/
theorem intrinsicDirectedEdgeListPath_map
    {S : Set A.E} {T : Set B.E} {missing : A.E → Prop} {missing' : B.E → Prop}
    (hs : ∀ e, e ∈ S → I.edgeEquiv e ∈ T)
    (hm : ∀ e, missing' (I.edgeEquiv e) ↔ missing e)
    {u v : A.V} {es : List A.E}
    (p : IntrinsicDirectedEdgeListPath A S missing u v es) :
    IntrinsicDirectedEdgeListPath B T missing' (I.vertexEquiv u) (I.vertexEquiv v)
      (es.map I.edgeEquiv) := by
  induction p with
  | nil => exact .nil _
  | @snoc v es p e he hp hv ih =>
    rw [List.map_append, List.map_singleton, intrinsicDirected_head_map I e]
    exact ih.snoc ⟨I.edgeEquiv e.val, fun hn => e.property ((I.missing_map e.val).mp hn)⟩
      (hs e.val he) (fun hn => hp ((hm e.val).mp hn))
      ((intrinsicDirected_tail_map I e).symm.trans (congrArg I.vertexEquiv hv))

/-- Helper toward Proposition 3.9: the exact path property is preserved and
reflected along the image edge set and the transported missing predicate. -/
theorem intrinsicDirectedEdgeListPath_transport
    (S : Set A.E) (missing : A.E → Prop) (u v : A.V) (es : List A.E) :
    IntrinsicDirectedEdgeListPath A S missing u v es ↔
      IntrinsicDirectedEdgeListPath B (I.edgeEquiv '' S)
        (fun e => missing (I.edgeEquiv.symm e))
        (I.vertexEquiv u) (I.vertexEquiv v) (es.map I.edgeEquiv) := by
  constructor
  · exact intrinsicDirectedEdgeListPath_map I (T := I.edgeEquiv '' S)
      (missing' := fun e => missing (I.edgeEquiv.symm e)) (fun e he => ⟨e, he, rfl⟩)
      (fun e => by simp only [Equiv.symm_apply_apply])
  · intro p
    have q := intrinsicDirectedEdgeListPath_map I.symm (T := S) (missing' := missing)
      (fun e he => by
        obtain ⟨a, ha, rfl⟩ := he
        simpa only [D39GeomRootedMapIsoV2.symm, Equiv.symm_apply_apply] using ha)
      (fun _ => Iff.rfl) p
    have hlist : (es.map I.edgeEquiv).map I.edgeEquiv.symm = es := by
      clear p q
      induction es with
      | nil => rfl
      | cons a es ih => simp only [List.map_cons, Equiv.symm_apply_apply, ih]
    simpa only [D39GeomRootedMapIsoV2.symm, Equiv.symm_apply_apply, hlist] using q

/-- Helper toward Proposition 3.9: a bijection of actual edge-list paths,
with inverse given by the inverse edge equivalence. -/
@[expose] def intrinsicDirectedPathEquiv (S : Set A.E) (missing : A.E → Prop)
    (u v : A.V) :
    {es : List A.E // IntrinsicDirectedEdgeListPath A S missing u v es} ≃
      {es : List B.E // IntrinsicDirectedEdgeListPath B (I.edgeEquiv '' S)
        (fun e => missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) es} := by
  let e : List A.E ≃ List B.E := {
    toFun := List.map I.edgeEquiv
    invFun := List.map I.edgeEquiv.symm
    left_inv := by
      intro es
      induction es with
      | nil => rfl
      | cons a es ih => simp only [List.map_cons, Equiv.symm_apply_apply, ih]
    right_inv := by
      intro es
      induction es with
      | nil => rfl
      | cons a es ih => simp only [List.map_cons, Equiv.apply_symm_apply, ih] }
  exact e.subtypeEquiv (intrinsicDirectedEdgeListPath_transport I S missing u v)

/-- Helper toward Proposition 3.9: path transport retains the complete
edge list through the edge bijection and preserves its length. -/
theorem intrinsicDirectedPathEquiv_spec (S : Set A.E) (missing : A.E → Prop)
    (u v : A.V)
    (p : {es : List A.E // IntrinsicDirectedEdgeListPath A S missing u v es}) :
    (intrinsicDirectedPathEquiv I S missing u v p).val = p.val.map I.edgeEquiv ∧
      intrinsicDirectedPathLength (intrinsicDirectedPathEquiv I S missing u v p) =
        intrinsicDirectedPathLength p :=
  ⟨rfl, List.length_map _⟩

/-- Helper toward Proposition 3.9: the set of all reachable lengths is
unchanged by a geometric isomorphism. -/
theorem intrinsicDirectedReachableLengths_transport (S : Set A.E)
    (missing : A.E → Prop) (u v : A.V) :
    intrinsicDirectedReachableLengths A S missing u v =
      intrinsicDirectedReachableLengths B (I.edgeEquiv '' S)
        (fun e => missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) := by
  ext n
  constructor
  · rintro ⟨es, hp, hn⟩
    exact ⟨es.map I.edgeEquiv,
      (intrinsicDirectedEdgeListPath_transport I S missing u v es).mp hp,
      (List.length_map _).trans hn⟩
  · rintro ⟨es, hp, hn⟩
    let p := (intrinsicDirectedPathEquiv I S missing u v).symm ⟨es, hp⟩
    exact ⟨p.val, p.property, (List.length_map _).trans hn⟩

/-- Helper toward Proposition 3.9: both extended distances agree after
transport, preserving all infima and suprema including infinite values. -/
theorem intrinsicDirected_distances_transport (S : Set A.E) (missing : A.E → Prop)
    (u v : A.V) :
    intrinsicDirectedSDP A S missing u v =
        intrinsicDirectedSDP B (I.edgeEquiv '' S)
          (fun e => missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) ∧
      intrinsicDirectedLDP A S missing u v =
        intrinsicDirectedLDP B (I.edgeEquiv '' S)
          (fun e => missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) := by
  unfold intrinsicDirectedSDP intrinsicDirectedLDP
  rw [intrinsicDirectedReachableLengths_transport I S missing u v]
  exact ⟨rfl, rfl⟩

end Transport

/-- Helper toward Proposition 3.9: an unreachable pair has shortest
distance ⊤ and longest distance ⊥, without assigning either distance zero. -/
theorem intrinsicDirected_unreachable_values (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) (u v : A.V)
    (h : ¬ ∃ es, IntrinsicDirectedEdgeListPath A S missing u v es) :
    intrinsicDirectedSDP A S missing u v = ⊤ ∧
      intrinsicDirectedLDP A S missing u v = ⊥ := by
  have hempty : intrinsicDirectedReachableLengths A S missing u v = ∅ := by
    ext n
    simp only [intrinsicDirectedReachableLengths, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨es, hp, _⟩
    exact h ⟨es, hp⟩
  simp only [intrinsicDirectedSDP, intrinsicDirectedLDP, hempty, Set.mem_empty_iff_false,
    iInf_of_empty, iSup_of_empty, iInf_const, iSup_const, and_self]

section SourceComparison

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D : M0CutData W H)

/- Helper toward Proposition 3.9: on the source domain, the intrinsic -/
theorem intrinsicDirected_source_path_iff (u v : WholePlaneVertex W)
    (es : List (WholePlaneEdge W)) :
    IntrinsicDirectedEdgeListPath (uibotWholePlaneSourceDomain W H G hp)
      D.edges D.missing u v es ↔ UIBOTCutEdgeListPath W H u v es := by
  constructor
  · intro p
    exact IntrinsicDirectedEdgeListPath.rec
      (motive := fun v es _ => UIBOTCutEdgeListPath W H u v es)
      (UIBOTCutEdgeListPath.nil u)
      (fun {v es} p e he hm hv ih => by
      have hend := uibotWholePlaneSourceMap_endpoints W H G hp e.val
      have q := ih.snoc e.val he ⟨⟨Bool.false_ne_true, hp e.val⟩, hm⟩
        (hend.1.symm.trans hv)
      exact Eq.mpr (congrArg (fun v => UIBOTCutEdgeListPath W H u v (es ++ [e.val]))
        hend.2) q) p
  · intro p
    dsimp only [uibotWholePlaneSourceDomain]
    induction p with
    | nil => exact .nil _
    | @snoc v es p e he ht hv ih =>
      have hend := uibotWholePlaneSourceMap_endpoints W H G hp e
      rw [← hend.2]
      exact ih.snoc ⟨e, fun hn => hn (hp e)⟩ he ht.2 (hend.1.trans hv)

/-- Helper toward Proposition 3.9: all intrinsic realized lengths on the
source domain agree with the installed code-cut reachable-length relation. -/
theorem intrinsicDirected_source_lengths_iff (u v : WholePlaneVertex W) (n : ℕ) :
    n ∈ intrinsicDirectedReachableLengths (uibotWholePlaneSourceDomain W H G hp)
      D.edges D.missing u v ↔
      m0CutReachableLength (m0CutDirectedStep W H D.seam) n u v := by
  change (∃ es, IntrinsicDirectedEdgeListPath (uibotWholePlaneSourceDomain W H G hp)
    D.edges D.missing u v es ∧ es.length = n) ↔ _
  apply Iff.trans (b := ∃ es, UIBOTCutEdgeListPath W H u v es ∧ es.length = n)
    ?_ (uibotIntrinsicCut_edgeList_length_iff W H u v n)
  constructor
  · rintro ⟨es, hp, hn⟩
    exact ⟨es, (intrinsicDirected_source_path_iff W H G _ D u v es).mp hp, hn⟩
  · rintro ⟨es, hp, hn⟩
    exact ⟨es, (intrinsicDirected_source_path_iff W H G _ D u v es).mpr hp, hn⟩

/-- Helper toward Proposition 3.9: the intrinsic source distances agree
with m0CutSDP and m0CutLDP, including their unreachable and unbounded values. -/
theorem intrinsicDirected_source_distances (u v : WholePlaneVertex W) :
    intrinsicDirectedSDP (uibotWholePlaneSourceDomain W H G hp) D.edges D.missing u v =
        m0CutSDP W H D.seam u v ∧
      intrinsicDirectedLDP (uibotWholePlaneSourceDomain W H G hp) D.edges D.missing u v =
        m0CutLDP W H D.seam u v := by
  simp only [intrinsicDirectedSDP, intrinsicDirectedLDP, m0CutSDP, m0CutLDP,
    intrinsicDirected_source_lengths_iff W H G hp D]
  exact ⟨trivial, trivial⟩

/-- Helper toward Proposition 3.9: in any geometrically isomorphic domain
map, the image code-cut edges and missing tags have exactly the code distances.
This transports paths first and does not assert an intrinsic cut identification. -/
theorem intrinsicDirected_image_source_distances
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) (u v : WholePlaneVertex W) :
    intrinsicDirectedSDP A (I.edgeEquiv '' D.edges)
        (fun e => D.missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) =
        m0CutSDP W H D.seam u v ∧
      intrinsicDirectedLDP A (I.edgeEquiv '' D.edges)
        (fun e => D.missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) =
        m0CutLDP W H D.seam u v := by
  have ht := intrinsicDirected_distances_transport
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I D.edges D.missing u v
  have hs := intrinsicDirected_source_distances W H G hp D u v
  exact ⟨ht.1.symm.trans hs.1, ht.2.symm.trans hs.2⟩

end SourceComparison

end DirectedDistances.PaperProofs.Section3
end
