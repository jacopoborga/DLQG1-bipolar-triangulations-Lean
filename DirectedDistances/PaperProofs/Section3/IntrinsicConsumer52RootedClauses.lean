/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52
public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer51Submaps
import DirectedDistances.KMSW.ShiftInfRotFirstReturn
import DirectedDistances.KMSW.HatInducedExit

/-! # The actual drawing of the stopped hatted edge image

The stopped hatted vertices and individual edges are identified with a
restriction of the original run-zero drawing. Its faces below are actual open
complementary regions in the representative's plane. This does not identify
the independently constructed shifted drawing's face certificate with those
regions. The exact outstanding comparison is recorded below; no qualifier is -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open MeasureTheory
open scoped Topology

/-- Helper toward Proposition 3.9: the stopped compressed edge's individual
ID in the original future, before the whole-plane and representative maps. -/
@[expose] def intrinsicConsumer52RawHatEdge (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (e : ℕ) : ℕ :=
  shiftLimitEdge w t ⟨hatLimitEdgeMap (fun i => w (t + i)) hτ e,
    ((hatLimitEdgeMap_range_iff _ hτ _).mp ⟨e, rfl⟩).1⟩

/-- Helper toward Proposition 3.9: the stopped compressed vertex's ID in
the original future, before transport to a representative. -/
@[expose] def intrinsicConsumer52RawHatVertex (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (v : ℕ) : ℕ :=
  (shiftLimitVertex w t ⟨hatLimitVertexMap (fun i => w (t + i)) hτ v⟩).id

/-- Helper toward Proposition 3.9: both geometric dart incidences survive
the compressed and stopped embeddings, with the dart bit unchanged. -/
theorem intrinsicConsumer52RawHat_dart_vertex (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (d : ℕ × Bool) :
    kmswLimitDartVertex w (intrinsicConsumer52RawHatEdge w t hτ d.1, d.2) =
      intrinsicConsumer52RawHatVertex w t hτ
        (kmswLimitDartVertex (hatCodes (fun i => w (t + i)) hτ) d) := by
  obtain ⟨hw, he⟩ := shiftLimitEdge_incidence w t
    ⟨hatLimitEdgeMap _ hτ d.1, ((hatLimitEdgeMap_range_iff _ hτ _).mp ⟨d.1, rfl⟩).1⟩
  obtain ⟨hw', he'⟩ := hatLimitEdgeMap_endpoint_alignment _ hτ d.1
  rcases d with ⟨e, b⟩
  cases b
  · change edgeWest w (intrinsicConsumer52RawHatEdge w t hτ e) = _
    exact hw.trans (congrArg
      (fun v => (shiftLimitVertex w t ⟨v⟩).id) hw')
  · change edgeEast w (intrinsicConsumer52RawHatEdge w t hτ e) = _
    exact he.trans (congrArg
      (fun v => (shiftLimitVertex w t ⟨v⟩).id) he')

/-- Helper toward Proposition 3.9: the retained original drawing has
exactly the transported compressed vertices, including the root. -/
theorem intrinsicConsumer52RawHat_vertices (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i))) :
    intrinsicConsumer51RunVertices w (Set.range (intrinsicConsumer52RawHatEdge w t hτ)) =
      Set.range (intrinsicConsumer52RawHatVertex w t hτ) := by
  ext v
  constructor
  · rintro ⟨⟨e, b⟩, ⟨f, rfl⟩, rfl⟩
    exact ⟨kmswLimitDartVertex (hatCodes _ hτ) (f, b),
      (intrinsicConsumer52RawHat_dart_vertex w t hτ (f, b)).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨d, hd⟩ := kmswLimitDartVertex_surjective (hatCodes _ hτ)
      (hatCodes_finiteIncidence _ hτ hfin) v
    exact ⟨(intrinsicConsumer52RawHatEdge w t hτ d.1, d.2), ⟨d.1, rfl⟩,
      (intrinsicConsumer52RawHat_dart_vertex w t hτ d).trans
        (congrArg (intrinsicConsumer52RawHatVertex w t hτ) hd)⟩

/-- Helper toward Proposition 3.9: the stopped compressed rotation is
first return to its complete dart image in the original future. -/
theorem intrinsicConsumer52RawHat_firstReturn (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    let φ := fun x : ℕ × Bool => (intrinsicConsumer52RawHatEdge w t hτ x.1, x.2)
    ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfinW : _ → _)^[k] (φ d) =
        φ (kmswInfRot (hatCodes (fun i => w (t + i)) hτ)
          (hatCodes_finiteIncidence _ hτ hfin) d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswInfRot w hfinW : _ → _)^[j] (φ d) ∉ Set.range φ := by
  let u := fun i => w (t + i)
  let f := fun x : ℕ × Bool => (hatLimitEdgeMap u hτ x.1, x.2)
  let g := fun x : ℕ × Bool => (kmswShiftEdgeMapAll w t x.1 x.1, x.2)
  have hginj : Function.Injective g := by
    intro a b hab
    have hef := congrArg Prod.fst hab
    have hb := congrArg (fun x : ℕ × Bool => x.2) hab
    apply Prod.ext
    swap
    · exact hb
    let n := max a.1 b.1
    have ha := kmsw_edge_allocated_by_self u a.1
    have hb' := kmsw_edge_allocated_by_self u b.1
    have haN := kmswShiftEdgeMapAll_eq_of_le w t a.1 n a.1
      (Nat.le_max_left _ _) ha
    have hbN := kmswShiftEdgeMapAll_eq_of_le w t b.1 n b.1
      (Nat.le_max_right _ _) hb'
    apply (kmswShift_sim2_all w t n).sim.edge_injective a.1 b.1
      (ha.trans_le (kmswStage_nextEdge_mono u (Nat.le_max_left _ _)))
      (hb'.trans_le (kmswStage_nextEdge_mono u (Nat.le_max_right _ _)))
    exact haN.trans (hef.trans hbN.symm)
  have hcomp : g ∘ f = fun x : ℕ × Bool =>
      (intrinsicConsumer52RawHatEdge w t hτ x.1, x.2) := by
    funext x
    apply Prod.ext
    swap
    · rfl
    exact (shiftLimitEdge_eq w t (hatLimitEdgeMap u hτ x.1)
      ⟨_, ((hatLimitEdgeMap_range_iff _ hτ _).mp ⟨x.1, rfl⟩).1⟩
      (kmsw_edge_allocated_by_self u _)).symm
  have hr := hatExit_induced_rotation_comp
    (kmswInfRot (hatCodes u hτ) (hatCodes_finiteIncidence u hτ hfin))
    (kmswInfRot u hfin) (kmswInfRot w hfinW) f g hginj
    (hatInfRot_firstReturn u hτ hfin)
    (shiftInfRot_firstReturn w t hfin hfinW) d
  rw [hcomp] at hr
  exact hr

/-- Helper toward Proposition 3.9: the compressed rotation equals the
geometric rotation of the original drawing restricted to the stopped image. -/
theorem intrinsicConsumer52RawHat_rotation (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfinW (monotone_family_all w)
    let T := {a : ℕ × Bool | a.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)}
    let D := fun a : ℕ × Bool =>
      (⟨(intrinsicConsumer52RawHatEdge w t hτ a.1, a.2), ⟨a.1, rfl⟩⟩ : T)
    D (kmswInfRot (hatCodes (fun i => w (t + i)) hτ)
      (hatCodes_finiteIncidence _ hτ hfin) d) = drawingFirstReturnPerm P T (D d) := by
  intro P T D
  let σ := kmswInfRot w hfinW
  obtain ⟨k, hk, hreturn, hgap⟩ :=
    intrinsicConsumer52RawHat_firstReturn w t hτ hfin hfinW d
  have hset : Set.range (fun a : ℕ × Bool =>
      (intrinsicConsumer52RawHatEdge w t hτ a.1, a.2)) = T := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, rfl⟩
    · rintro ⟨b, hb⟩
      exact ⟨(b, a.2), Prod.ext hb rfl⟩
  rw [hset] at hgap
  have hmem : (σ : _ → _)^[k] (D d).val ∈ T := by
    rw [hreturn]
    exact ⟨_, rfl⟩
  have htime : subsetFirstReturnTime σ T (drawingPositiveReturn P T) (D d) = k := by
    apply Nat.le_antisymm
    · by_contra hn
      have hs := subsetFirstReturnTime_spec σ T (drawingPositiveReturn P T) (D d)
      exact hs.2.2 k hk (by omega) hmem
    · by_contra hn
      have hs := subsetFirstReturnTime_spec σ T (drawingPositiveReturn P T) (D d)
      exact hgap _ hs.1 (by omega) hs.2.1
  apply Subtype.ext
  change _ = (subsetFirstReturnPerm σ T (drawingPositiveReturn P T)
    (drawingPositiveReturnInv P T) (D d)).val
  rw [subsetFirstReturnPerm_apply, htime]
  exact hreturn.symm




theorem intrinsicConsumer52RawHat_faceSuccessor (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfinW (monotone_family_all w)
    let T := {a : ℕ × Bool | a.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)}
    let D := fun a : ℕ × Bool =>
      (⟨(intrinsicConsumer52RawHatEdge w t hτ a.1, a.2), ⟨a.1, rfl⟩⟩ : T)
    D (kmswInfFaceSucc (hatCodes (fun i => w (t + i)) hτ)
      (hatCodes_finiteIncidence _ hτ hfin) d) =
      (drawingFirstReturnPerm P T).symm
        (restrictedFlip P T (fun _ => Iff.rfl) (D d)) := by
  intro P T D
  let ρ := kmswInfRot (hatCodes (fun i => w (t + i)) hτ)
    (hatCodes_finiteIncidence _ hτ hfin)
  let τ := drawingFirstReturnPerm P T
  change D (ρ.symm (futureMapEdgeInv d)) =
    τ.symm (restrictedFlip P T (fun _ => Iff.rfl) (D d))
  apply τ.injective
  rw [Equiv.apply_symm_apply]
  change τ (D (ρ.symm (futureMapEdgeInv d))) = D (futureMapEdgeInv d)
  have hr := intrinsicConsumer52RawHat_rotation w t hτ hfin hfinW
    (ρ.symm (futureMapEdgeInv d))
  change D (ρ (ρ.symm (futureMapEdgeInv d))) =
    τ (D (ρ.symm (futureMapEdgeInv d))) at hr
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

section Representative
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "w" => shiftedStream W 0
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "C" => uibotCut2SourceDartEquiv W H h hpast hp
local notation "P" => monotoneFamilyDrawing w ((And.left H) 0) (monotone_family_all w)

variable (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
    (uibotWholePlaneSourceRoot W H
      (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)

/-- Helper toward Proposition 3.9: a stopped hatted geometric dart in the
representative, including both changes of stored edge orientation. -/
@[expose] def intrinsicConsumer52HatDart (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (d : ℕ × Bool) : A.E × Bool :=
  intrinsicFutureDartEquiv (A := S) I
    (C (wholePlaneDartι W 0 (intrinsicConsumer52RawHatEdge w t hτ d.1, d.2)))

/-- Helper toward Proposition 3.9: each transported dart lies on exactly
the individual stopped hatted edge already exported by the consumer. -/
theorem intrinsicConsumer52HatDart_edge (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (d : ℕ × Bool) :
    (intrinsicConsumer52HatDart W H h hpast hp A I t hτ d).1 =
      intrinsicConsumer52HatEdge W H G hp A I t hτ d.1 := rfl

/-- Helper toward Proposition 3.9: parallel edges and the two incidences
of each individual edge remain distinct in the stopped dart embedding. -/
theorem intrinsicConsumer52HatDart_injective (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) :
    Function.Injective (intrinsicConsumer52HatDart W H h hpast hp A I t hτ) := by
  intro d e hde
  have hd := (C).injective ((intrinsicFutureDartEquiv I).injective hde)
  apply Prod.ext
  · exact intrinsicConsumer52HatEdge_injective W H G hp A I t hτ
      (congrArg Prod.fst hde)
  · exact congrArg (fun q : WholePlaneDart W => q.2) hd

/-- Helper toward Proposition 3.9: geometric incidence reversal commutes
with the stopped dart embedding, including both storage flips. -/
theorem intrinsicConsumer52HatDart_flip (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (d : ℕ × Bool) :
    intrinsicConsumer52HatDart W H h hpast hp A I t hτ (d.1, !d.2) =
      ((intrinsicConsumer52HatDart W H h hpast hp A I t hτ d).1,
        !(intrinsicConsumer52HatDart W H h hpast hp A I t hτ d).2) := by
  unfold intrinsicConsumer52HatDart
  exact (congrArg (intrinsicFutureDartEquiv (A := S) I)
    (uibotCut2SourceDartEquiv_flip W H h hpast hp
      (wholePlaneDartι W 0 (intrinsicConsumer52RawHatEdge w t hτ d.1, d.2)))).trans
        (intrinsicFutureDartEquiv_flip (A := S) (B := A) I _)

/-- Helper toward Proposition 3.9: the transported geometric dart's
vertex is the exported stopped hatted vertex of the compressed incidence. -/
theorem intrinsicConsumer52HatDart_vertex (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) (d : ℕ × Bool) :
    d39GeomRootVertex A.map (intrinsicConsumer52HatDart W H h hpast hp A I t hτ d) =
      intrinsicConsumer52HatVertex W H G hp A I t hτ
        (kmswLimitDartVertex (hatCodes (fun i => w (t + i)) hτ) d) := by
  unfold intrinsicConsumer52HatDart
  erw [intrinsicFutureDartEquiv_vertex, uibotCut2SourceDartEquiv_vertex,
    wholePlaneDartVertex_ι]
  exact congrArg (fun v => I.vertexEquiv (wholePlaneVertexι W 0 v))
    (intrinsicConsumer52RawHat_dart_vertex w t hτ d)

/-- Helper toward Proposition 3.9: the actual stopped hatted edge set
equals the original drawing's retained edge image, with no edge quotient. -/
theorem intrinsicConsumer52Rooted_edges (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) :
    Set.range (intrinsicConsumer52HatEdge W H G hp A I t hτ) =
      I.edgeEquiv '' (wholePlaneEdgeι W 0 ''
        Set.range (intrinsicConsumer52RawHatEdge w t hτ)) := by
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩

/-- Helper toward Proposition 3.9: the actual stopped hatted vertex set
equals the incident vertices of the retained original drawing. -/
theorem intrinsicConsumer52Rooted_vertices (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i))) :
    Set.range (intrinsicConsumer52HatVertex W H G hp A I t hτ) =
      I.vertexEquiv '' (wholePlaneVertexι W 0 ''
        intrinsicConsumer51RunVertices w
          (Set.range (intrinsicConsumer52RawHatEdge w t hτ))) := by
  rw [intrinsicConsumer52RawHat_vertices w t hτ hfin]
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

/-- Helper toward Proposition 3.9: the hatted code's complete cyclic
rotation is the induced geometric rotation of the actual stopped submap. -/
theorem intrinsicConsumer52Rooted_rotation (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i))) (d : ℕ × Bool) :
    intrinsicFutureRotation A
      (Set.range (intrinsicConsumer52HatEdge W H G hp A I t hτ))
      (intrinsicConsumer52HatDart W H h hpast hp A I t hτ
        (kmswInfRot (hatCodes (fun i => w (t + i)) hτ)
          (hatCodes_finiteIncidence _ hτ hfin) d))
      (intrinsicConsumer52HatDart W H h hpast hp A I t hτ d) := by
  let K := Set.range (intrinsicConsumer52RawHatEdge w t hτ)
  let T := {a : ℕ × Bool | a.1 ∈ K}
  let D := fun a : ℕ × Bool =>
    (⟨(intrinsicConsumer52RawHatEdge w t hτ a.1, a.2), ⟨a.1, rfl⟩⟩ : T)
  have hrot := intrinsicConsumer52RawHat_rotation w t hτ hfin (H.1 0) d
  change D (kmswInfRot (hatCodes _ hτ) (hatCodes_finiteIncidence _ hτ hfin) d) =
    drawingFirstReturnPerm P T (D d) at hrot
  have hactual := intrinsicConsumer51_runZero_rotation W H h hpast hp A I K (D d)
  dsimp only at hactual
  rw [← hrot] at hactual
  rw [intrinsicConsumer52Rooted_edges W H h hpast hp A I t hτ]
  exact hactual

/-- Helper toward Proposition 3.9: all complementary regions of the
actual stopped hatted submap are open regions of the representative drawing.
The parametrization here uses the restricted original drawing. -/
theorem intrinsicConsumer52Rooted_geometry (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i))) :
    let K := Set.range (intrinsicConsumer52RawHatEdge w t hτ)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    let J := fun d => intrinsicFutureDartEquiv (A := S) I (C (wholePlaneDartι W 0 d))
    let R := fun F : Q.Face => I.h '' F.val
    Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A
          (Set.range (intrinsicConsumer52HatVertex W H G hp A I t hτ))
          (Set.range (intrinsicConsumer52HatEdge W H G hp A I t hτ))) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A
        (Set.range (intrinsicConsumer52HatEdge W H G hp A I t hτ))
        (J (drawingFirstReturnPerm P T d).val) (J d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (J d.val)) s) ↔
          Q.dartBorders d F) := by
  intro K T Q J R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F F' hFF
    apply Subtype.ext
    exact Set.image_injective.mpr I.h.injective hFF
  · rw [intrinsicConsumer52Rooted_vertices W H h hpast hp A I t hτ hfin,
      intrinsicConsumer52Rooted_edges W H h hpast hp A I t hτ]
    simpa only [Set.image_image, Function.comp_def] using
      (intrinsicConsumer51_runZero_faceRegions W H h hpast hp A I K).symm
  · exact intrinsicConsumer51_runZero_face_open W H h hpast hp A I K
  · exact intrinsicConsumer51_runZero_external W H h hpast hp A I K
  · intro d
    rw [intrinsicConsumer52Rooted_edges W H h hpast hp A I t hτ]
    exact intrinsicConsumer51_runZero_rotation W H h hpast hp A I K d
  · exact intrinsicConsumer51_runZero_face_side W H h hpast hp A I K

end Representative

/- On the common event of intrinsicConsumer52_sample, the remaining geometric
clauses, with all binders, are:

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
  ∀ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (k : ℤ),
    let t := boundaryHitTime (shiftedStream W 0) h k
    let u := fun i => shiftedStream W 0 (t + i)
    ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
    let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
    ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      (∀ q, IsOpen (R q)) ∧
      (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Quotient.mk _ d = q) ∧
      (∀ q, (¬ Bornology.IsBounded (R q)) ↔
        q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
        (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d)

The event must be intersected with that of intrinsicConsumer52_sample, keeping
its common witnesses. This is not a deterministic assertion off that event.
The precise missing comparison is between hatRealizedDrawing u hfin and
the original monotone drawing restricted to the range of
intrinsicConsumer52RawHatEdge (shiftedStream W 0) t hτ. Their rotation and
face-successor permutations are now identified. An equivalence of their
actual complementary regions preserving dart-side incidence and unboundedness
is still needed. intrinsicConsumer52Rooted_geometry supplies the actual
regions of the latter drawing, but does not establish this equivalence.
Combining that missing identification with intrinsicConsumer52_sample:229
is still required for the complete representative-level Lemma 5.2 statement. -/

end DirectedDistances.PaperProofs.Section3
