/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassReconstruction
public import DirectedDistances.PaperProofs.Section3.D39BallBridgePart4
import Mathlib.Order.KonigLemma

/-! # Compatible finite geometric observations and global combinatorial maps

The geometric domain only imposes graph local finiteness. The finite PL
ball bridges do not supply a global ambient plane homeomorphism. This file
separates the finite combinatorial compactness argument from that geometric -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open Set MeasureTheory Filter
open scoped ENNReal Topology

universe u

/-- Helper toward Proposition 3.9: the vertex carrier at positive radius `n+1`. -/
abbrev uibotSeparationBallV (A : D39DomainRootedMap.{u}) (n : ℕ) :=
  {v // v ∈ d39GeomBallVertices A.map A.root (n + 1)}

/-- Helper toward Proposition 3.9: the geometric edge carrier at radius `n+1`. -/
abbrev uibotSeparationBallE (A : D39DomainRootedMap.{u}) (n : ℕ) :=
  {e // e ∈ d39GeomBallEdges A.map A.root (n + 1)}

local instance uibotClassSeparationFiniteVertices (A : D39DomainRootedMap.{u}) (n : ℕ) :
    Finite (uibotSeparationBallV A n) := (A.domain.ballVertices_finite (n + 1)).to_subtype

local instance uibotClassSeparationFiniteEdges (A : D39DomainRootedMap.{u}) (n : ℕ) :
    Finite (uibotSeparationBallE A n) := (A.domain.ballEdges_finite (n + 1)).to_subtype

/-- Helper toward Proposition 3.9: the finite vertex, edge-identity and
endpoint-order trace of a geometric ball isomorphism. Realizability retains
all finite geometric, orientation and retained-face constraints. -/
@[ext] structure UIBOTBallTrace (A B : D39DomainRootedMap.{u}) (n : ℕ) where
  vertexEquiv : uibotSeparationBallV A n ≃ uibotSeparationBallV B n
  edgeEquiv : uibotSeparationBallE A n ≃ uibotSeparationBallE B n
  flip : uibotSeparationBallE A n → Bool
  realizable : ∃ J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root,
    J.vertexEquiv = vertexEquiv ∧ J.edgeEquiv = edgeEquiv ∧ J.edgeFlip = flip

namespace UIBOTBallTrace

variable {A B : D39DomainRootedMap.{u}} {n m k : ℕ}

/-- Helper toward Proposition 3.9: forget the infinite geometric choices
in one ball isomorphism, retaining its realizable finite trace. -/
@[expose] def ofGeom (J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root) :
    UIBOTBallTrace A B n :=
  ⟨J.vertexEquiv, J.edgeEquiv, J.edgeFlip, J, rfl, rfl, rfl⟩

/-- Helper toward Proposition 3.9: there are finitely many realizable traces at each radius. -/
theorem finite_traces : Finite (UIBOTBallTrace A B n) := by
  apply Finite.of_injective
    (fun x : UIBOTBallTrace A B n => (x.vertexEquiv, x.edgeEquiv, x.flip))
  intro x y h
  obtain ⟨hv, hrest⟩ := Prod.mk.inj h
  obtain ⟨he, hf⟩ := Prod.mk.inj hrest
  exact UIBOTBallTrace.ext hv he hf

/-- Helper toward Proposition 3.9: a geometric witness for a realizable trace. -/
@[expose] def geom (x : UIBOTBallTrace A B n) := Classical.choose x.realizable

/-- Helper toward Proposition 3.9: the witness has exactly the stored finite trace. -/
theorem geom_spec (x : UIBOTBallTrace A B n) :
    x.geom.vertexEquiv = x.vertexEquiv ∧ x.geom.edgeEquiv = x.edgeEquiv ∧
      x.geom.edgeFlip = x.flip := Classical.choose_spec x.realizable

/-- Helper toward Proposition 3.9: restrict a realizable finite trace;
the geometric witness is restricted with all its retained-face data. -/
@[expose] def restrict (h : n ≤ m) (x : UIBOTBallTrace A B m) :
    UIBOTBallTrace A B n :=
  ofGeom (x.geom.restrict (Nat.succ_pos n) (Nat.add_le_add_right h 1))

/-- Helper toward Proposition 3.9: restriction preserves vertex images. -/
theorem restrict_vertex (h : n ≤ m) (x : UIBOTBallTrace A B m)
    (v : uibotSeparationBallV A n) :
    ((x.restrict h).vertexEquiv v).val =
      (x.vertexEquiv ⟨v.val, D39GeomBallIsoV2.vertexBall_mono
        (Nat.add_le_add_right h 1) v.property⟩).val := by
  change (x.geom.restrictVertices (Nat.add_le_add_right h 1) v).val = _
  rw [D39GeomBallIsoV2.restrictVertices_val, x.geom_spec.1]

/-- Helper toward Proposition 3.9: restriction preserves edge images. -/
theorem restrict_edge (h : n ≤ m) (x : UIBOTBallTrace A B m)
    (e : uibotSeparationBallE A n) :
    ((x.restrict h).edgeEquiv e).val =
      (x.edgeEquiv ⟨e.val, D39GeomBallIsoV2.edgeBall_mono
        (Nat.add_le_add_right h 1) e.property⟩).val := by
  change (x.geom.restrictEdges (Nat.add_le_add_right h 1) e).val = _
  rw [D39GeomBallIsoV2.restrictEdges_val, x.geom_spec.2.1]

/-- Helper toward Proposition 3.9: restriction preserves endpoint-order bits. -/
theorem restrict_flip (h : n ≤ m) (x : UIBOTBallTrace A B m)
    (e : uibotSeparationBallE A n) :
    (x.restrict h).flip e = x.flip ⟨e.val, D39GeomBallIsoV2.edgeBall_mono
        (Nat.add_le_add_right h 1) e.property⟩ := by
  change x.geom.edgeFlip _ = _
  rw [x.geom_spec.2.2]

/-- Helper toward Proposition 3.9: restriction to the same radius is the identity. -/
theorem restrict_refl (x : UIBOTBallTrace A B n) : x.restrict le_rfl = x := by
  apply UIBOTBallTrace.ext
  · apply Equiv.ext
    intro v
    exact Subtype.ext (restrict_vertex le_rfl x v)
  · apply Equiv.ext
    intro e
    exact Subtype.ext (restrict_edge le_rfl x e)
  · funext e
    exact restrict_flip le_rfl x e

/-- Helper toward Proposition 3.9: finite trace restrictions compose. -/
theorem restrict_trans (h : n ≤ m) (h' : m ≤ k) (x : UIBOTBallTrace A B k) :
    (x.restrict h').restrict h = x.restrict (h.trans h') := by
  apply UIBOTBallTrace.ext
  · apply Equiv.ext
    intro v
    apply Subtype.ext
    rw [restrict_vertex, restrict_vertex, restrict_vertex]
  · apply Equiv.ext
    intro e
    apply Subtype.ext
    rw [restrict_edge, restrict_edge, restrict_edge]
  · funext e
    rw [restrict_flip, restrict_flip, restrict_flip]

end UIBOTBallTrace

local instance uibotClassSeparationFiniteTracesAtRadius
    (A B : D39DomainRootedMap.{u}) (n : ℕ) : Finite (UIBOTBallTrace A B n) :=
  UIBOTBallTrace.finite_traces

/-- Helper toward Proposition 3.9: König's lemma chooses finite traces
simultaneously at every positive radius, compatibly under restriction. -/
theorem uibotClassSeparation_compatible_traces (A B : D39DomainRootedMap.{u})
    (hballs : ∀ r : ℕ, 0 < r →
      Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root)) :
    ∃ f : ∀ n, UIBOTBallTrace A B n,
      ∀ ⦃n m⦄ (h : n ≤ m), (f m).restrict h = f n := by
  have uibotClassSeparationNonemptyTraces (n : ℕ) :
      Nonempty (UIBOTBallTrace A B n) :=
    (hballs (n + 1) (Nat.succ_pos n)).map UIBOTBallTrace.ofGeom
  exact exists_seq_forall_proj_of_forall_finite (α := UIBOTBallTrace A B)
    (fun h x => x.restrict h) (fun _ x => UIBOTBallTrace.restrict_refl x)
    (fun _ _ _ h h' x => UIBOTBallTrace.restrict_trans h h' x)
    (fun _ _ => Set.toFinite _)

private theorem extend_exhaustion {α β : Type*} (s : ℕ → Set α)
    (hmono : Monotone s) (hcover : ∀ a, ∃ n, a ∈ s n)
    (f : ∀ n, s n → β)
    (hc : ∀ n m (h : n ≤ m) (a : s n),
      f n a = f m ⟨a.val, hmono h a.property⟩) :
    ∃ g : α → β, ∀ n (a : s n), g a.val = f n a := by
  classical
  choose c hmem using hcover
  refine ⟨fun a => f (c a) ⟨a, hmem a⟩, ?_⟩
  intro n a
  exact (hc (c a.val) (max (c a.val) n) (le_max_left _ _)
    ⟨a.val, hmem a.val⟩).trans
    (hc n (max (c a.val) n) (le_max_right _ _) a).symm

private theorem equiv_exhaustion {α β : Type*} (s : ℕ → Set α) (t : ℕ → Set β)
    (hmono : Monotone s) (hcover : ∀ a, ∃ n, a ∈ s n)
    (hcover' : ∀ b, ∃ n, b ∈ t n) (e : ∀ n, s n ≃ t n)
    (hc : ∀ n m (h : n ≤ m) (a : s n),
      (e n a).val = (e m ⟨a.val, hmono h a.property⟩).val) :
    ∃ E : α ≃ β, ∀ n (a : s n), E a.val = (e n a).val := by
  obtain ⟨f, hf⟩ := extend_exhaustion s hmono hcover (fun n a => (e n a).val) hc
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨n, hn⟩ := hcover a
    obtain ⟨m, hm⟩ := hcover b
    let x : s (max n m) := ⟨a, hmono (le_max_left _ _) hn⟩
    let y : s (max n m) := ⟨b, hmono (le_max_right _ _) hm⟩
    exact congrArg Subtype.val ((e (max n m)).injective (Subtype.ext
      ((hf _ x).symm.trans (hab.trans (hf _ y)))))
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨n, hn⟩ := hcover' b
    refine ⟨((e n).symm ⟨b, hn⟩).val, ?_⟩
    exact (hf n _).trans (congrArg Subtype.val ((e n).apply_symm_apply ⟨b, hn⟩))
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

private theorem vertex_cover (A : D39DomainRootedMap.{u}) (v : A.V) :
    ∃ n : ℕ, v ∈ d39GeomBallVertices A.map A.root (n + 1) := by
  obtain ⟨p, hp⟩ :=
    (A.domain.connected (d39GeomRootVertex A.map A.root) v).exists_walk_length_eq_edist
  refine ⟨p.length, ?_⟩
  change (d39GeomGraph A.map).edist _ v ≤ _
  rw [← hp]
  exact_mod_cast Nat.le_succ p.length

private theorem edge_cover (A : D39DomainRootedMap.{u}) (e : A.E) :
    ∃ n : ℕ, e ∈ d39GeomBallEdges A.map A.root (n + 1) := by
  obtain ⟨n, hn⟩ := vertex_cover A (A.map.toPlaneMapWithMissing.src e)
  obtain ⟨m, hm⟩ := vertex_cover A (A.map.toPlaneMapWithMissing.tgt e)
  exact ⟨max n m,
    D39GeomBallIsoV2.vertexBall_mono (Nat.add_le_add_right (le_max_left n m) 1) hn,
    D39GeomBallIsoV2.vertexBall_mono (Nat.add_le_add_right (le_max_right n m) 1) hm⟩

/-- Helper toward Proposition 3.9: agreement of every finite geometric
ball gives a global rooted combinatorial isomorphism, with edge identities,
missing tags and directions preserved. Its restriction at every radius is
realized by an actual geometric ball isomorphism. No global plane
homeomorphism is asserted. -/
theorem uibotClassSeparation_global_combinatorial_iso (A B : D39DomainRootedMap.{u})
    (hballs : ∀ r : ℕ, 0 < r →
      Nonempty (D39GeomBallIsoV2 r A.map A.root B.map B.root)) :
    ∃ I : D39CombDartIso A.map A.root B.map B.root,
      ∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root,
        (∀ v : uibotSeparationBallV A n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE A n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE A n, I.flip e.val = J.edgeFlip e) := by
  obtain ⟨f, hf⟩ := uibotClassSeparation_compatible_traces A B hballs
  have hvmono : Monotone (fun n => d39GeomBallVertices A.map A.root (n + 1)) :=
    fun _ _ h _ hv => D39GeomBallIsoV2.vertexBall_mono (Nat.add_le_add_right h 1) hv
  have hemono : Monotone (fun n => d39GeomBallEdges A.map A.root (n + 1)) :=
    fun _ _ h _ he => D39GeomBallIsoV2.edgeBall_mono (Nat.add_le_add_right h 1) he
  obtain ⟨V, hV⟩ := equiv_exhaustion _ _ hvmono (vertex_cover A) (vertex_cover B)
    (fun n => (f n).vertexEquiv) (by
      intro n m h v
      rw [← hf h]
      exact UIBOTBallTrace.restrict_vertex h (f m) v)
  obtain ⟨E, hE⟩ := equiv_exhaustion _ _ hemono (edge_cover A) (edge_cover B)
    (fun n => (f n).edgeEquiv) (by
      intro n m h e
      rw [← hf h]
      exact UIBOTBallTrace.restrict_edge h (f m) e)
  obtain ⟨flip, hflip⟩ := extend_exhaustion _ hemono (edge_cover A)
    (fun n => (f n).flip) (by
      intro n m h e
      rw [← hf h]
      exact UIBOTBallTrace.restrict_flip h (f m) e)
  have hJ (n : ℕ) : ∃ J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root,
      (∀ v : uibotSeparationBallV A n, V v.val = (J.vertexEquiv v).val) ∧
      (∀ e : uibotSeparationBallE A n, E e.val = (J.edgeEquiv e).val) ∧
      (∀ e : uibotSeparationBallE A n, flip e.val = J.edgeFlip e) := by
    obtain ⟨J, hv, he, hb⟩ := (f n).realizable
    refine ⟨J, ?_, ?_, ?_⟩
    · rw [hv]; exact hV n
    · rw [he]; exact hE n
    · rw [hb]; exact hflip n
  have hsrc (e : A.E) : V (A.map.toPlaneMapWithMissing.src e) =
      if flip e then B.map.toPlaneMapWithMissing.tgt (E e)
      else B.map.toPlaneMapWithMissing.src (E e) := by
    obtain ⟨n, hn⟩ := edge_cover A e
    obtain ⟨J, hv, he, hb⟩ := hJ n
    rw [hv ⟨A.map.toPlaneMapWithMissing.src e, hn.1⟩, he ⟨e, hn⟩, hb ⟨e, hn⟩]
    exact J.src_map ⟨e, hn⟩
  have htgt (e : A.E) : V (A.map.toPlaneMapWithMissing.tgt e) =
      if flip e then B.map.toPlaneMapWithMissing.src (E e)
      else B.map.toPlaneMapWithMissing.tgt (E e) := by
    obtain ⟨n, hn⟩ := edge_cover A e
    obtain ⟨J, hv, he, hb⟩ := hJ n
    rw [hv ⟨A.map.toPlaneMapWithMissing.tgt e, hn.2⟩, he ⟨e, hn⟩, hb ⟨e, hn⟩]
    exact J.tgt_map ⟨e, hn⟩
  have hmissing (e : A.E) : B.map.toPlaneMapWithMissing.missing (E e) ↔
      A.map.toPlaneMapWithMissing.missing e := by
    obtain ⟨n, hn⟩ := edge_cover A e
    obtain ⟨J, _, he, _⟩ := hJ n
    rw [he ⟨e, hn⟩]
    exact J.missing_map ⟨e, hn⟩
  have hforward (e : A.E) (he : ¬ A.map.toPlaneMapWithMissing.missing e) :
      B.map.forward ⟨E e, (hmissing e).not.mpr he⟩ =
        Bool.xor (A.map.forward ⟨e, he⟩) (flip e) := by
    obtain ⟨n, hn⟩ := edge_cover A e
    obtain ⟨J, _, heq, hb⟩ := hJ n
    simp only [heq ⟨e, hn⟩, hb ⟨e, hn⟩]
    exact J.orientation_map ⟨e, hn⟩ he
  obtain ⟨J, _, heq, hb⟩ := hJ 0
  have hroot : E A.root.1 = B.root.1 :=
    (heq ⟨A.root.1, d39GeomRootEdge_mem A.map A.root (by omega)⟩).trans J.root_edge_map
  have hbool : B.root.2 = Bool.xor A.root.2 (flip A.root.1) := by
    rw [hb ⟨A.root.1, d39GeomRootEdge_mem A.map A.root (by omega)⟩]
    exact J.root_bool_map
  exact ⟨⟨V, E, flip, hsrc, htgt, hmissing, hforward, hroot, hbool⟩, hJ⟩

local instance uibotClassSeparationMeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}

local instance uibotClassSeparationBorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: for almost every iid code, every
representative at zero distance from its sampled geometric class admits
a global rooted combinatorial isomorphism to the source construction.
Every finite restriction is geometrically realized. This conclusion
does not identify the global geometric classes. -/
theorem uibotClassSeparation_ae_zero_source_combinatorial_iso :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        let B := uibotWholePlaneSourceDomain W H G hp
        uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
          Quotient.mk d39DomainSetoid B ∧
        ∀ A : D39DomainRootedMap.{0},
          edist (Quotient.mk d39DomainSetoid A)
            (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = 0 →
          ∃ I : D39CombDartIso A.map A.root B.map B.root,
            ∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root,
              (∀ v : uibotSeparationBallV A n,
                I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
              (∀ e : uibotSeparationBallE A n,
                I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
              (∀ e : uibotSeparationBallE A n, I.flip e.val = J.edgeFlip e) := by
  filter_upwards [uibotMeasurableWholePlaneClassMap_ae_source] with W hW
  obtain ⟨H, h0, hpast, hp, hclass, _, _⟩ := hW
  refine ⟨H, h0, hpast, hp, hclass, ?_⟩
  intro A hz
  apply uibotClassSeparation_global_combinatorial_iso
  intro r hr
  apply (d39ClassDistance_le_pow_iff_nonempty hr A
    (uibotWholePlaneSourceDomain W H
      (WholePlanePastGlueDrawing.glueDrawing W h0 hpast H) hp)).mp
  rw [← hclass, hz]
  exact bot_le

/-- Helper toward Proposition 3.9: almost every class has a global
rooted combinatorial isomorphism to the whole-plane source at its recovered
code. The same source witnesses work for every representative, and every
finite restriction is realized geometrically with all face constraints. -/
theorem uibotClassSeparation_ae_source_combinatorial_iso :
    ∀ᵐ x ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}),
      let W := uibotRecoveredCode x
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        let B := uibotWholePlaneSourceDomain W H G hp
        ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = x →
          ∃ I : D39CombDartIso A.map A.root B.map B.root,
            ∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) A.map A.root B.map B.root,
              (∀ v : uibotSeparationBallV A n,
                I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
              (∀ e : uibotSeparationBallE A n,
                I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
              (∀ e : uibotSeparationBallE A n, I.flip e.val = J.edgeFlip e) := by
  filter_upwards [uibotClassReconstruction_ae_source_balls] with x hx
  obtain ⟨H, h0, hpast, hp, hballs⟩ := hx
  refine ⟨H, h0, hpast, hp, ?_⟩
  dsimp only
  intro A hA
  exact uibotClassSeparation_global_combinatorial_iso A
    (uibotWholePlaneSourceDomain _ H
      (WholePlanePastGlueDrawing.glueDrawing _ h0 hpast H) hp) (hballs A hA)




























end DirectedDistances.PaperProofs.Section3
end
