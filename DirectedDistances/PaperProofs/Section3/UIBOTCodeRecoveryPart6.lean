/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTCodeRecoveryPart5
public import DirectedDistances.PaperProofs.Section5.Prop516StarRotationCommutation
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField

/-! # Geometric ball transport on chronological darts

All geometric isomorphisms below act on the actual whole-plane edge identities. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section5
open MeasureTheory Filter
open unitInterval
open scoped ENNReal Topology

section Transport

variable {W W' : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {H' : WholePlaneRotationHypothesis W'}
    {G : WholePlaneDrawing W H} {G' : WholePlaneDrawing W' H'}
    {hp : ∀ e, wholePlaneEdgePresent W e} {hp' : ∀ e, wholePlaneEdgePresent W' e}
    {r : ℕ}


/-- Helper toward Proposition 3.9: the dart equivalence of two geometric
balls, on the original chronological edge IDs. The Boolean records the actual
west/east incidence, independently of stored geometric endpoint order. -/
@[expose] def uibotRecovery_ballDartEquiv
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) :
    {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r} ≃
    {d : WholePlaneDart W' // d.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G') r} where
  toFun d := ⟨((e.edgeEquiv ⟨d.1.1, d.2⟩).1, d.1.2), (e.edgeEquiv _).2⟩
  invFun d := ⟨((e.edgeEquiv.symm ⟨d.1.1, d.2⟩).1, d.1.2), (e.edgeEquiv.symm _).2⟩
  left_inv := by
    intro d
    apply Subtype.ext
    exact Prod.ext
      (congrArg Subtype.val (e.edgeEquiv.symm_apply_apply ⟨d.1.1, d.2⟩)) rfl
  right_inv := by
    intro d
    apply Subtype.ext
    exact Prod.ext
      (congrArg Subtype.val (e.edgeEquiv.apply_symm_apply ⟨d.1.1, d.2⟩)) rfl

/-- Helper toward Proposition 3.9: ball dart transport preserves the
ordered chronological root. -/
theorem uibotRecovery_ballDartEquiv_root
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) :
    (uibotRecovery_ballDartEquiv e
      ⟨wholePlaneDartι W 0 (0, false), d39GeomRootEdge_mem _ _ e.radius_pos⟩).1 =
      wholePlaneDartι W' 0 (0, false) := by
  exact Prod.ext e.root_edge_map rfl

/-- Helper toward Proposition 3.9: ball dart transport commutes with
edge reversal, retaining both incidences of every individual edge. -/
theorem uibotRecovery_ballDartEquiv_flip
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
    (uibotRecovery_ballDartEquiv e ⟨wholePlaneDartFlip W d.1, d.2⟩).1 =
      wholePlaneDartFlip W' (uibotRecovery_ballDartEquiv e d).1 := rfl

/-- Helper toward Proposition 3.9: ball dart transport preserves actual
incoming/outgoing orientation; all edge-presence premises concern the existing
deterministic realization and are discharged on the iid conull event. -/
theorem uibotRecovery_ballDartEquiv_tail
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
    wholePlaneDartTail W' (uibotRecovery_ballDartEquiv e d).1 ↔
      wholePlaneDartTail W d.1 := by
  change (¬ d.1.2 = true ∧ wholePlaneEdgePresent W' _) ↔
    (¬ d.1.2 = true ∧ wholePlaneEdgePresent W _)
  exact ⟨fun h => ⟨h.1, hp _⟩, fun h => ⟨h.1, hp' _⟩⟩

private theorem flip_apply (d : WholePlaneDart W) :
    wholePlaneDartFlip W d = (d.1, !d.2) := rfl

/-- Helper toward Proposition 3.9: a dart of a retained geometric edge has
its initial vertex in the same ball. -/
theorem uibotRecovery_ballDart_vertex_mem (d : WholePlaneDart W)
    (hd : d.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r) :
    wholePlaneDartVertex W d ∈ d39GeomBallVertices (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r := by
  have ho := uibotWholePlaneSourceEdgeEquiv_out W H G d.1
  change wholePlaneDartVertex W (uibotWholePlaneSourceEdgeEquiv W H G d.1).out ∈ _ ∧
    wholePlaneDartVertex W (wholePlaneDartFlip W
      (uibotWholePlaneSourceEdgeEquiv W H G d.1).out) ∈ _ at hd
  simp only [flip_apply, wholePlaneDartVertex, ho] at hd
  cases hb : (uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2 <;> cases hdB : d.2
  all_goals simp only [hb, wholePlaneDartVertex, hdB, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true] at hd ⊢
  all_goals first | exact hd.1 | exact hd.2


/-- Helper toward Proposition 3.9: the geometric vertex equivalence
maps each raw dart's initial vertex to the initial vertex of its transported
raw dart. The orientation field resolves stored endpoint reversals. -/
theorem uibotRecovery_ballDartEquiv_vertex
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
    (e.vertexEquiv ⟨wholePlaneDartVertex W d.1, uibotRecovery_ballDart_vertex_mem d.1 d.2⟩).1 =
      wholePlaneDartVertex W' (uibotRecovery_ballDartEquiv e d).1 := by
  let a := uibotWholePlaneSourceEdgeEquiv W H G d.1.1
  let b := uibotWholePlaneSourceEdgeEquiv W' H' G' (e.edgeEquiv ⟨d.1.1, d.2⟩).1
  have ha : a.out.1 = d.1.1 := uibotWholePlaneSourceEdgeEquiv_out W H G _
  have hb : b.out.1 = (e.edgeEquiv ⟨d.1.1, d.2⟩).1 :=
    uibotWholePlaneSourceEdgeEquiv_out W' H' G' _
  have hf := e.orientation_map ⟨d.1.1, d.2⟩
    (uibotWholePlaneSourceMap_noMissing W H G hp _)
  change (!b.out.2) = Bool.xor (!a.out.2) (e.edgeFlip ⟨d.1.1, d.2⟩) at hf
  have hs := e.src_map ⟨d.1.1, d.2⟩
  have ht := e.tgt_map ⟨d.1.1, d.2⟩
  change (e.vertexEquiv ⟨wholePlaneDartVertex W a.out, _⟩).1 =
    (if e.edgeFlip ⟨d.1.1, d.2⟩ then wholePlaneDartVertex W' (wholePlaneDartFlip W' b.out)
      else wholePlaneDartVertex W' b.out) at hs
  change (e.vertexEquiv ⟨wholePlaneDartVertex W (wholePlaneDartFlip W a.out), _⟩).1 =
    (if e.edgeFlip ⟨d.1.1, d.2⟩ then wholePlaneDartVertex W' b.out
      else wholePlaneDartVertex W' (wholePlaneDartFlip W' b.out)) at ht
  cases hda : a.out.2 <;> cases hdb : b.out.2 <;>
    cases hflip : e.edgeFlip ⟨d.1.1, d.2⟩ <;>
    simp only [hda, hdb, hflip, Bool.not_false, Bool.not_true,
      Bool.xor_false, Bool.xor_true, Bool.false_eq_true, Bool.true_eq_false] at hf
  all_goals cases hd : d.1.2
  all_goals simp only [flip_apply, wholePlaneDartVertex,
    hda, hdb, hflip, Bool.not_false, Bool.not_true, Bool.false_eq_true, 
    ite_false, ite_true, ha, hb] at hs ht
  all_goals first
    | simpa only [wholePlaneDartVertex, uibotRecovery_ballDartEquiv, Equiv.coe_fn_mk,
        hd, Bool.false_eq_true,  ite_false, ite_true] using hs
    | simpa only [wholePlaneDartVertex, uibotRecovery_ballDartEquiv, Equiv.coe_fn_mk,
        hd, Bool.false_eq_true,  ite_false, ite_true] using ht

private theorem source_arc_range (d : WholePlaneDart W) :
    Set.range ((uibotWholePlaneSourceMap W H G hp).arc d.1) = (G.arc d).image := by
  change Set.range (G.toPlaneGraphDrawing.arc (Quotient.mk G.edgeSetoid (d.1, false))) = _
  apply (G.toPlaneGraphDrawing_arc_range (d.1, false)).trans
  rcases d with ⟨a, b⟩
  cases b
  · rfl
  · exact (G.arc_image_flip (a, false)).symm

/-- Helper toward Proposition 3.9: the ambient homeomorphism maps the
entire raw PL dart arc onto the transported raw dart arc. -/
theorem uibotRecovery_ballDartEquiv_arc_image
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
    e.h '' (G.arc d.1).image = (G'.arc (uibotRecovery_ballDartEquiv e d).1).image := by
  rw [← source_arc_range (hp := hp) d.1,
    ← source_arc_range (hp := hp') (uibotRecovery_ballDartEquiv e d).1]
  exact e.arc_range_map ⟨d.1.1, d.2⟩

/-- Helper toward Proposition 3.9: the geometric isomorphism transports
the actual raw dart paths by increasing interval homeomorphisms. This retains
their PL traversal schedules and does not identify reversal with a different
parameterization by definitional equality. -/
theorem uibotRecovery_ballDartEquiv_arc_param
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
    ∃ φ : I ≃ₜ I, StrictMono φ ∧ ∀ t : I,
      e.h ((G.arc d.1).toPath t) =
        (G'.arc (uibotRecovery_ballDartEquiv e d).1).toPath (φ t) := by
  let E := uibotRecovery_ballDartEquiv e
  have hpos (a : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
      e.h (G.pos (wholePlaneDartVertex W a.1)) =
        G'.pos (wholePlaneDartVertex W' (E a).1) := by
    have h := e.pos_map ⟨wholePlaneDartVertex W a.1, uibotRecovery_ballDart_vertex_mem a.1 a.2⟩
    change e.h (G.pos _) = G'.pos _ at h
    rw [uibotRecovery_ballDartEquiv_vertex e a] at h
    exact h
  have hs : e.h (G.arc d.1).start = (G'.arc (E d).1).start := by
    rw [G.arc_start, G'.arc_start]
    exact hpos d
  have ht : e.h (G.arc d.1).finish = (G'.arc (E d).1).finish := by
    rw [G.arc_finish, G'.arc_finish]
    have h := hpos ⟨wholePlaneDartFlip W d.1, d.2⟩
    rw [uibotRecovery_ballDartEquiv_flip] at h
    exact h
  let γ := (G'.arc (E d).1).toPath
  let δ : Path (G'.arc (E d).1).start (G'.arc (E d).1).finish :=
    ((G.arc d.1).toPath.map e.h.continuous).cast hs.symm ht.symm
  have hγ : Function.Injective γ :=
    (G'.arc (E d).1).toPath_injective (G'.arc_length _) (G'.arc_simple _)
  have hδ : Function.Injective δ :=
    e.h.injective.comp ((G.arc d.1).toPath_injective (G.arc_length _) (G.arc_simple _))
  have hrange : Set.range δ = Set.range γ := by
    calc
      Set.range δ = e.h '' Set.range (G.arc d.1).toPath := by
        ext z
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨_, ⟨t, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨t, rfl⟩, rfl⟩
          exact ⟨t, rfl⟩
      _ = e.h '' (G.arc d.1).image := congrArg (fun S => e.h '' S) (Polyline.range_toPath _)
      _ = (G'.arc (E d).1).image := uibotRecovery_ballDartEquiv_arc_image e d
      _ = Set.range γ := (Polyline.range_toPath _).symm
  obtain ⟨φ, h0, h1, hφ⟩ := exists_path_reparam_of_injective_range_eq γ δ hγ hδ hrange
  refine ⟨φ, φ.continuous.strictMono_of_inj_boundedOrder ?_ φ.injective, ?_⟩
  · change φ 0 ≤ φ 1
    rw [h0, h1]
    exact bot_le
  · intro t
    exact congrArg (fun p : Path (G'.arc (E d).1).start (G'.arc (E d).1).finish => p t) hφ

/-- Helper toward Proposition 3.9: if both endpoint stars are retained,
the geometric ball equivalence preserves the original whole-plane rotation.
No rotation-preservation premise is assumed; the proof uses the oriented
ambient homeomorphism and uniqueness of topological cyclic successors. -/
theorem uibotRecovery_ballDartEquiv_rotation
    (e : D39GeomBallIsoV2 r (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r})
    (hs : ∀ q : WholePlaneDart W, wholePlaneDartVertex W q = wholePlaneDartVertex W d.1 →
      q.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r)
    (ht : ∀ q : WholePlaneDart W',
      wholePlaneDartVertex W' q = wholePlaneDartVertex W' (uibotRecovery_ballDartEquiv e d).1 →
      q.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G') r) :
    (uibotRecovery_ballDartEquiv e
      ⟨wholePlaneRotation W H d.1, hs _ (wholePlaneRotation_preserves_dartVertex W H d.1)⟩).1 =
      wholePlaneRotation W' H' (uibotRecovery_ballDartEquiv e d).1 := by
  classical
  let E := uibotRecovery_ballDartEquiv e
  let b := (⟨wholePlaneRotation W H d.1,
    hs _ (wholePlaneRotation_preserves_dartVertex W H d.1)⟩ :
    {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r})
  let c := (⟨wholePlaneRotation W' H' (E d).1,
    ht _ (wholePlaneRotation_preserves_dartVertex W' H' (E d).1)⟩ :
    {d : WholePlaneDart W' // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G') r})
  have hv (a b : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r}) :
      wholePlaneDartVertex W' (E a).1 = wholePlaneDartVertex W' (E b).1 ↔
        wholePlaneDartVertex W a.1 = wholePlaneDartVertex W b.1 := by
    rw [← uibotRecovery_ballDartEquiv_vertex e a, ← uibotRecovery_ballDartEquiv_vertex e b]
    constructor
    · intro h
      exact congrArg Subtype.val (e.vertexEquiv.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun v => (e.vertexEquiv v).1) (Subtype.ext h)
  have hstar : E '' {a | wholePlaneDartVertex W a.1 = wholePlaneDartVertex W d.1} =
      {a | wholePlaneDartVertex W' a.1 = wholePlaneDartVertex W' (E d).1} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hv b d).2 hb
    · intro ha
      change wholePlaneDartVertex W' a.1 = wholePlaneDartVertex W' (E d).1 at ha
      refine ⟨E.symm a, ?_, E.apply_symm_apply a⟩
      apply (hv (E.symm a) d).1
      simpa only [E.apply_symm_apply] using ha
  have hsource := d39TopologicalCcwSuccessor_subtype
    (D := WholePlaneDart W)
    (star := {a | wholePlaneDartVertex W a = wholePlaneDartVertex W d.1})
    (S := {a : WholePlaneDart W | a.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r})
    (arc := fun a t => (G.arc a).toPath t) d b
    (plDrawing_toPath_rotation_topological_ccwSuccessor G d.1)
  have hmap := d39TopologicalCcwSuccessor_map_equiv E hsource
  change D39TopologicalCcwSuccessor
    (E '' {a | wholePlaneDartVertex W a.1 = wholePlaneDartVertex W d.1})
    (fun a t => (G.arc (E.symm a).1).toPath t) (E d) (E b) at hmap
  rw [hstar] at hmap
  let param := fun a => (uibotRecovery_ballDartEquiv_arc_param e (E.symm a)).choose
  have htransport := d39TopologicalCcwSuccessor_map_orientedHomeomorph
    {a | wholePlaneDartVertex W' a.1 = wholePlaneDartVertex W' (E d).1}
    (fun a t => (G.arc (E.symm a).1).toPath t)
    (fun a t => (G'.arc a.1).toPath t) param (E d) (E b) e.h e.orientationPreserving
    (fun a _ => (uibotRecovery_ballDartEquiv_arc_param e (E.symm a)).choose_spec.1)
    (by
      intro a _ t
      have h := (uibotRecovery_ballDartEquiv_arc_param e (E.symm a)).choose_spec.2 t
      change e.h ((G.arc (E.symm a).1).toPath t) =
        (G'.arc (E (E.symm a)).1).toPath (param a t) at h
      exact h.trans (congrArg (fun z => (G'.arc z.1).toPath (param a t))
        (E.apply_symm_apply a))) hmap
  have htarget := d39TopologicalCcwSuccessor_subtype
    (D := WholePlaneDart W')
    (star := {a | wholePlaneDartVertex W' a = wholePlaneDartVertex W' (E d).1})
    (S := {a : WholePlaneDart W' | a.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G') r})
    (arc := fun a t => (G'.arc a).toPath t) (E d) c
    (plDrawing_toPath_rotation_topological_ccwSuccessor G' (E d).1)
  exact congrArg Subtype.val (d39TopologicalCcwSuccessor_unique htransport htarget)

private theorem dart_incident (d : WholePlaneDart W) :
    (uibotWholePlaneSourceMap W H G hp).src d.1 = wholePlaneDartVertex W d ∨
      (uibotWholePlaneSourceMap W H G hp).tgt d.1 = wholePlaneDartVertex W d := by
  have ho := uibotWholePlaneSourceEdgeEquiv_out W H G d.1
  change wholePlaneDartVertex W (uibotWholePlaneSourceEdgeEquiv W H G d.1).out = _ ∨
    wholePlaneDartVertex W (wholePlaneDartFlip W
      (uibotWholePlaneSourceEdgeEquiv W H G d.1).out) = _
  simp only [flip_apply, wholePlaneDartVertex, ho]
  cases hb : (uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2 <;> cases hd : d.2 <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      true_or, or_true]

/-- Helper toward Proposition 3.9: every dart based at radius `r` has
its geometric edge retained at radius `r + 1`. -/
theorem uibotRecovery_dart_edge_mem_succ (d : WholePlaneDart W)
    (hd : wholePlaneDartVertex W d ∈ d39GeomBallVertices
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r) :
    d.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) (r + 1) :=
  uibotRecovery_star_enclosed _ _ r _ hd _ (dart_incident d)

/-- Helper toward Proposition 3.9: at an interior vertex, a geometric
ball isomorphism preserves whole-plane rotation with no extra star premise.
Distance preservation encloses the target star as well as the source star. -/
theorem uibotRecovery_ballDartEquiv_rotation_interior
    (e : D39GeomBallIsoV2 (r + 1)
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G'))
    (d : {d : WholePlaneDart W // d.1 ∈ d39GeomBallEdges
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) (r + 1)})
    (hd : wholePlaneDartVertex W d.1 ∈ d39GeomBallVertices
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r) :
    ∃ hrot : (wholePlaneRotation W H d.1).1 ∈ d39GeomBallEdges
        (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) (r + 1),
      (uibotRecovery_ballDartEquiv e ⟨wholePlaneRotation W H d.1, hrot⟩).1 =
        wholePlaneRotation W' H' (uibotRecovery_ballDartEquiv e d).1 := by
  have hs (q : WholePlaneDart W)
      (hq : wholePlaneDartVertex W q = wholePlaneDartVertex W d.1) :
      q.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) (r + 1) :=
    uibotRecovery_dart_edge_mem_succ q (hq ▸ hd)
  have hv : wholePlaneDartVertex W' (uibotRecovery_ballDartEquiv e d).1 ∈
      d39GeomBallVertices (uibotWholePlaneSourceMap W' H' G' hp')
        (uibotWholePlaneSourceRoot W' H' G') r := by
    have he := e.distance_preserving (wholePlaneDartVertex W d.1)
      (uibotRecovery_ballDart_vertex_mem d.1 d.2)
    rw [uibotRecovery_ballDartEquiv_vertex e d] at he
    change d39GeomGraphDistance _ _ _ ≤ (r : ℕ∞) at hd ⊢
    exact he ▸ hd
  have ht (q : WholePlaneDart W')
      (hq : wholePlaneDartVertex W' q =
        wholePlaneDartVertex W' (uibotRecovery_ballDartEquiv e d).1) :
      q.1 ∈ d39GeomBallEdges (uibotWholePlaneSourceMap W' H' G' hp')
        (uibotWholePlaneSourceRoot W' H' G') (r + 1) :=
    uibotRecovery_dart_edge_mem_succ q (hq ▸ hv)
  exact ⟨hs _ (wholePlaneRotation_preserves_dartVertex W H d.1),
    uibotRecovery_ballDartEquiv_rotation e d hs ht⟩

end Transport

/-- Helper toward Proposition 3.9: each code letter is recovered from one
finite geometric ball of its rooted whole-plane realization. The radius is
chosen before the comparison word and its drawing. -/
theorem uibotRecovery_codeLetter_of_ballIso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (hp : ∀ e, wholePlaneEdgePresent W e)
    (hh : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N)) (n : ℤ) :
    ∃ r : ℕ, ∀ (W' : ℤ → Fin 3) (H' : WholePlaneRotationHypothesis W')
      (G' : WholePlaneDrawing W' H') (hp' : ∀ e, wholePlaneEdgePresent W' e)
      (_hh' : ∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W' N)),
      Nonempty (D39GeomBallIsoV2 (r + 1)
        (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
        (uibotWholePlaneSourceMap W' H' G' hp') (uibotWholePlaneSourceRoot W' H' G')) →
      W n = W' n := by
  classical
  obtain ⟨S, hS⟩ := uibotCodeLetter_finite_rotation_support W H hp hh n
  obtain ⟨r, hr⟩ := uibotRecovery_finite_vertices_enclosed
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    (uibotWholePlaneSourceDomain W H G hp).domain (S.image (wholePlaneDartVertex W))
  refine ⟨r, ?_⟩
  intro W' H' G' hp' hh' ⟨e⟩
  let B := d39GeomBallEdges (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) (r + 1)
  let f : WholePlaneDart W → WholePlaneDart W' := fun d =>
    if hd : d.1 ∈ B then ((e.edgeEquiv ⟨d.1, hd⟩).1, d.2)
    else (wholePlaneEdgeι W' 0 0, d.2)
  have hf (d : WholePlaneDart W) (hd : d.1 ∈ B) :
      f d = (uibotRecovery_ballDartEquiv e ⟨d, hd⟩).1 := dite_eq_left hd
  have hv (d : WholePlaneDart W) (hd : d ∈ S) :
      wholePlaneDartVertex W d ∈ d39GeomBallVertices
        (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r :=
    hr _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  have hrot (d : WholePlaneDart W)
      (hd : wholePlaneDartVertex W d ∈ d39GeomBallVertices
        (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) r) :
      f (wholePlaneRotation W H d) = wholePlaneRotation W' H' (f d) := by
    have he := uibotRecovery_dart_edge_mem_succ d hd
    obtain ⟨hrot, h⟩ := uibotRecovery_ballDartEquiv_rotation_interior e ⟨d, he⟩ hd
    exact (hf _ hrot).trans (h.trans (congrArg (wholePlaneRotation W' H') (hf d he).symm))
  apply hS W' H' hp' hh' f
  · intro d hd
    have hdi : wholePlaneDartVertex W ((wholePlaneRotation W H).symm d) =
        wholePlaneDartVertex W d := by
      have h := wholePlaneRotation_preserves_dartVertex W H ((wholePlaneRotation W H).symm d)
      exact h.symm.trans (congrArg (wholePlaneDartVertex W) ((wholePlaneRotation W H).apply_symm_apply d))
    refine ⟨hrot d (hv d hd), ?_, ?_, ?_⟩
    · apply (wholePlaneRotation W' H').injective
      rw [(wholePlaneRotation W' H').apply_symm_apply]
      exact (hrot _ (hdi ▸ hv d hd)).symm.trans
        (congrArg f ((wholePlaneRotation W H).apply_symm_apply d))
    · have he := uibotRecovery_dart_edge_mem_succ d (hv d hd)
      exact (hf (wholePlaneDartFlip W d) he).trans ((uibotRecovery_ballDartEquiv_flip e ⟨d, he⟩).trans
        (congrArg (wholePlaneDartFlip W') (hf d he).symm))
    · have he := uibotRecovery_dart_edge_mem_succ d (hv d hd)
      rw [hf d he]
      exact uibotRecovery_ballDartEquiv_tail e ⟨d, he⟩
  · have he := d39GeomRootEdge_mem (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) (Nat.succ_pos r)
    exact (hf (wholePlaneDartι W 0 (0, false)) he).trans (uibotRecovery_ballDartEquiv_root e)

local instance uibotCodeRecoveryPart6MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotCodeRecoveryPart6BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

/-- Helper toward Proposition 3.9: on one conull set, each integer code
letter is determined by a finite geometric ball of the measurable whole-plane
class. The comparison ranges over the same conull set, and the radius is
chosen before the comparison word. -/
theorem uibotRecovery_conull_local :
    ∃ S : Set (ℤ → Fin 3), (∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ S) ∧
      ∀ W : ℤ → Fin 3, W ∈ S → ∀ n : ℤ, ∃ r : ℕ,
        ∀ W' : ℤ → Fin 3, W' ∈ S →
          d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap
            uibotDeterministicComparison_proved W') =
          d39GeomBallClassMap r (uibotMeasurableWholePlaneClassMap
            uibotDeterministicComparison_proved W) → W' n = W n := by
  let S : Set (ℤ → Fin 3) := {W |
    (∀ N : ℕ, BoundaryHitWitnesses (shiftedStream W N)) ∧
    ∃ (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
      (hp : ∀ e, wholePlaneEdgePresent W e),
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W =
        Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp)}
  have hS : ∀ᵐ W ∂wholePlaneIIDCodeMeasure, W ∈ S := by
    filter_upwards [uibotMeasurableWholePlaneClassMap_ae_source,
      wholePlaneIID_ae_runBoundaryDegree] with W h hh
    obtain ⟨H, h0, hpast, hp, heq, _⟩ := h
    exact ⟨fun N => (hh N).choose, H,
      WholePlanePastGlueDrawing.glueDrawing W h0 hpast H, hp, heq⟩
  refine ⟨S, hS, ?_⟩
  intro W hW n
  obtain ⟨hh, H, G, hp, heq⟩ := hW
  obtain ⟨r, hr⟩ := uibotRecovery_codeLetter_of_ballIso W H G hp hh n
  refine ⟨r, ?_⟩
  intro W' hW' hball
  obtain ⟨hh', H', G', hp', heq'⟩ := hW'
  rw [heq, heq'] at hball
  exact (hr W' H' G' hp' hh'
    ((d39GeomBallClassMap_mk_eq_iff r _ _).1 hball.symm)).symm

/-- Helper toward Proposition 3.9: the measurable whole-plane geometric
class has a Borel inverse on a conull set of iid codes. The construction uses
open neighborhoods that recover individual letters, so it does not assume
injectivity or a standard-Borel structure on the geometric class space. -/
theorem uibotRecovery_exists_borel_inverse :
    ∃ G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3), Measurable G ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        G (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = W := by
  classical
  let F := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
  obtain ⟨S, hS, hlocal⟩ := uibotRecovery_conull_local
  choose radius hradius using fun (W : S) (n : ℤ) => hlocal W.1 W.2 n
  let U : ℤ → Fin 3 → Set D39GeomRootedMapClass.{0} := fun n k =>
    ⋃ W : S, ⋃ (_ : W.1 n = k), Metric.eball (F W.1) ((1 / 2 : ℝ≥0∞) ^ radius W n)
  have hU (n : ℤ) (k : Fin 3) : IsOpen (U n k) := by
    apply isOpen_iUnion
    intro W
    apply isOpen_iUnion
    intro hk
    exact Metric.isOpen_eball
  have hmem (W : ℤ → Fin 3) (hW : W ∈ S) (n : ℤ) (k : Fin 3) :
      F W ∈ U n k ↔ W n = k := by
    constructor
    · intro h
      obtain ⟨V, hV⟩ := Set.mem_iUnion.mp h
      obtain ⟨hk, hb⟩ := Set.mem_iUnion.mp hV
      have hb' : d39GeomBallClassMap (radius V n) (F V.1) =
          d39GeomBallClassMap (radius V n) (F W) := by
        have h := d39GeomClass_openBall_eq_ballClass (radius V n) (F V.1)
        exact (Set.ext_iff.mp h (F W)).mp hb
      exact (hradius V n W hW hb'.symm).trans hk
    · intro hk
      apply Set.mem_iUnion.mpr
      refine ⟨⟨W, hW⟩, Set.mem_iUnion.mpr ⟨hk, ?_⟩⟩
      rw [d39GeomClass_openBall_eq_ballClass]
      rfl
  let G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3) := fun x n =>
    if x ∈ U n 0 then 0 else if x ∈ U n 1 then 1 else 2
  refine ⟨G, ?_, ?_⟩
  · apply Measurable.of_eval
    intro n
    exact Measurable.ite (hU n 0).measurableSet measurable_const
      (Measurable.ite (hU n 1).measurableSet measurable_const measurable_const)
  · filter_upwards [hS] with W hW
    funext n
    change (if F W ∈ U n 0 then 0 else if F W ∈ U n 1 then 1 else 2) = W n
    rw [hmem W hW n 0, hmem W hW n 1]
    split_ifs with h0 h1
    · exact h0.symm
    · exact h1.symm
    · omega

/-- Helper toward Proposition 3.9: every measurable code observable
factors almost surely through one Borel inverse of the geometric class map.
The same inverse works for every target measurable space and every observable. -/
theorem uibotRecovery_exists_borel_factorization :
    ∃ G : D39GeomRootedMapClass.{0} → (ℤ → Fin 3), Measurable G ∧
      (∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        G (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) = W) ∧
      ∀ (β : Type*) [MeasurableSpace β] (X : (ℤ → Fin 3) → β),
        Measurable X → Measurable (X ∘ G) ∧
          X =ᵐ[wholePlaneIIDCodeMeasure] (X ∘ G) ∘
            uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved := by
  obtain ⟨G, hG, hinv⟩ := uibotRecovery_exists_borel_inverse
  refine ⟨G, hG, hinv, ?_⟩
  intro β _ X hX
  refine ⟨hX.comp hG, ?_⟩
  filter_upwards [hinv] with W hW
  exact (congrArg X hW).symm

/-- Helper toward Proposition 3.9: every measurable predicate of the
raw code agrees almost surely with a Borel predicate of the geometric class.
All shared witnesses and simultaneous quantifiers inside the predicate are
preserved by the recovered equality of entire codes. -/
theorem uibotRecovery_predicate_factorization
    (Q : (ℤ → Fin 3) → Prop) (hQ : MeasurableSet {W | Q W}) :
    ∃ P : D39GeomRootedMapClass.{0} → Prop, MeasurableSet {x | P x} ∧
      ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
        Q W ↔ P (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W) := by
  obtain ⟨G, hG, hinv⟩ := uibotRecovery_exists_borel_inverse
  refine ⟨fun x => Q (G x), hQ.preimage hG, ?_⟩
  filter_upwards [hinv] with W hW
  exact (congrArg Q hW).symm.to_iff

end DirectedDistances.PaperProofs.Section3
end
