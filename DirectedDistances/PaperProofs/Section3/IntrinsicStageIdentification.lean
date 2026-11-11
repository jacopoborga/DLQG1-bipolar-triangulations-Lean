/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.BoundaryHitTauIdentification
public import DirectedDistances.PaperProofs.Section3.IntrinsicDirectedDistance
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart3
public import DirectedDistances.PaperProofs.Section5.DirectedContainIdentified
public import DirectedDistances.PaperProofs.Section7.LongPathIdentified








public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5 DirectedDistances.PaperProofs.Section7
open MeasureTheory Quiver
open scoped Classical

/-- Helper toward Proposition 3.9: the minimal active-edge carrier on an
ambient representative; each edge retains its identity and ambient orientation. -/
@[expose] def IntrinsicStageActiveEdges (A : D39DomainRootedMap.{0}) :=
  ℕ → {e : A.E // ¬ A.map.missing e}

/-- Helper toward Proposition 3.9: the initial vertices of the supplied
active edges are computed using the representative's directed tails. -/
@[expose] def intrinsicStageActiveInitial (A : D39DomainRootedMap.{0})
    (activeEdges : IntrinsicStageActiveEdges A) (n : ℕ) : A.V := A.map.tail (activeEdges n)

/-- Helper toward Proposition 3.9: an actual directed step in a retained
edge set, excluding both ambient missing edges and cut missing edges. -/
@[expose] def IntrinsicStageEdgeStep (A : D39DomainRootedMap.{0})
    (S : Set A.E) (missing : A.E → Prop) (e : A.E) (a b : A.V) : Prop :=
  ∃ he : ¬ A.map.missing e, e ∈ S ∧ ¬ missing e ∧
    A.map.tail ⟨e, he⟩ = a ∧ A.map.head ⟨e, he⟩ = b

/-- Helper toward Proposition 3.9: the vertices allocated by the stopped
KMSW stage, in a supplied vertex enumeration of the representative. -/
@[expose] def intrinsicStageAllocatedVertices (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (V : ℕ → A.V) (n : ℕ) : Set A.V :=
  {v | ∃ z, z < (kmswStage (shiftedStream W 0) n).nextVertex ∧ v = V z}

/-- Helper toward Proposition 3.9: all geometric edges allocated by a
stage, including edges deleted from its directed edge set. -/
@[expose] def intrinsicStageAllocatedEdges (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (E : ℕ → A.E) (n : ℕ) : Set A.E :=
  {e | ∃ j, j < (kmswStage (shiftedStream W 0) n).nextEdge ∧ e = E j}

/-- Helper toward Proposition 3.9: the stage's present directed edges;
the stage presence flag is retained separately from ambient presence. -/
@[expose] def intrinsicStagePresentEdges (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (E : ℕ → A.E) (n : ℕ) : Set A.E :=
  {e | ∃ j, j < (kmswStage (shiftedStream W 0) n).nextEdge ∧
    (kmswStage (shiftedStream W 0) n).present j = true ∧ e = E j}

/-- Helper toward Proposition 3.9: the complete allocated-vertex and
present-edge content of a path in a stopped stage, on the ambient carrier. -/
@[expose] def IntrinsicIdentifiedStagePath (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (V : ℕ → A.V) (E : ℕ → A.E)
    (n N : ℕ) (p : Fin (N + 1) → A.V) : Prop :=
  (∀ i, p i ∈ intrinsicStageAllocatedVertices W A V n) ∧
  (∀ i : Fin N, ∃ j, j < (kmswStage (shiftedStream W 0) n).nextEdge ∧
    (kmswStage (shiftedStream W 0) n).present j = true ∧
    ∃ he : ¬ A.map.missing (E j),
      A.map.tail ⟨E j, he⟩ = p i.castSucc ∧ A.map.head ⟨E j, he⟩ = p i.succ)

/-- Helper toward Proposition 3.9: full finite and infinite containment
on intrinsic vertex and edge carriers. Finite paths lift into one common
shifted stage with their exact length; infinite paths use one infinite lift. -/
@[expose] def IntrinsicStageShiftContainment (W : ℤ → Fin 3)
    (A : D39DomainRootedMap.{0}) (V : ℕ → A.V) (E : ℕ → A.E)
    (S : Set A.E) (missing : A.E → Prop) (x : A.V) (t : ℕ) : Prop :=
  let w := shiftedStream W 0
  (∀ n : ℕ, ∀ p : Fin (n + 1) → A.V, ∀ e : Fin n → A.E,
    p 0 = x →
    (∀ i, IntrinsicStageEdgeStep A S missing (e i) (p i.castSucc) (p i.succ)) →
    ∃ m, ∃ z : StagePresentVertex (fun i => w (t + i)) m,
      ∃ q : Path (⟨0⟩ : StagePresentVertex (fun i => w (t + i)) m) z,
        V ((kmswShiftStageToLimit w t m).obj ⟨0⟩).id = x ∧
        V ((kmswShiftStageToLimit w t m).obj z).id = p (Fin.last n) ∧
        (pathEdgeList ((kmswShiftStageToLimit w t m).mapPath q)).map E = List.ofFn e ∧
        q.length = n) ∧
  (∀ p : ℕ → A.V, ∀ e : ℕ → A.E, p 0 = x →
    (∀ n, IntrinsicStageEdgeStep A S missing (e n) (p n) (p (n + 1))) →
    ∃ Q : InfinitePresentPath (fun i => w (t + i)) ⟨0⟩,
      ∀ n, E (shiftLimitEdge w t
        ⟨Q.edge n, (Q.edge_outgoing_at_initial _ n).1⟩) = e n)

section Image

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)

/-- Helper toward Proposition 3.9: transport every active edge, using
its whole-plane identity and the representative's actual present-edge subtype. -/
@[expose] def intrinsicStageActiveEdges : IntrinsicStageActiveEdges A := fun n =>
  ⟨I.edgeEquiv (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n)),
    fun hm => ((I.missing_map _).mp hm) (hp _)⟩

/-- Helper toward Proposition 3.9: tails of transported active edges
are exactly the images of the original active initial vertices. -/
theorem intrinsicStageActiveInitial_eq (n : ℕ) :
    intrinsicStageActiveInitial A (intrinsicStageActiveEdges W H G hp A I) n =
      I.vertexEquiv (wholePlaneEdgeWest W
        (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n))) := by
  have ht := intrinsicDirected_tail_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
    ⟨wholePlaneEdgeι W 0 (act (shiftedStream W 0) n), fun hm => hm (hp _)⟩
  have hend := uibotWholePlaneSourceMap_endpoints W H G hp
    (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n))
  exact ht.symm.trans (congrArg I.vertexEquiv hend.1)

/-- Helper toward Proposition 3.9: a retained source step is equivalent
to the corresponding intrinsic step, with its individual edge identity. -/
theorem intrinsicStageEdgeStep_image_iff (D : M0CutData W H)
    (e : WholePlaneEdge W) (a b : WholePlaneVertex W) :
    IntrinsicStageEdgeStep A (I.edgeEquiv '' D.edges)
      (fun f => D.missing (I.edgeEquiv.symm f)) (I.edgeEquiv e)
      (I.vertexEquiv a) (I.vertexEquiv b) ↔
    e ∈ D.edges ∧ D.tail (e, false) ∧
      wholePlaneEdgeWest W e = a ∧ wholePlaneEdgeEast W e = b := by
  have he : ¬ (uibotWholePlaneSourceMap W H G hp).missing e := fun hm => hm (hp e)
  have ht := intrinsicDirected_tail_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I ⟨e, he⟩
  have hh := intrinsicDirected_head_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I ⟨e, he⟩
  have hend := uibotWholePlaneSourceMap_endpoints W H G hp e
  dsimp only [uibotWholePlaneSourceDomain] at ht hh
  rw [hend.1] at ht
  rw [hend.2] at hh
  constructor
  · rintro ⟨he', ⟨f, hf, hfe⟩, hm, ha, hb⟩
    have hfe' : f = e := I.edgeEquiv.injective hfe
    subst f
    have hm' : ¬ D.missing e := by simpa only [Equiv.symm_apply_apply] using hm
    exact ⟨hf, ⟨⟨Bool.false_ne_true, hp e⟩, hm'⟩,
      I.vertexEquiv.injective (ht.trans ha), I.vertexEquiv.injective (hh.trans hb)⟩
  · rintro ⟨hs, hd, ha, hb⟩
    refine ⟨fun hm => he ((I.missing_map e).mp hm), ⟨e, hs, rfl⟩, ?_,
      ht.symm.trans (congrArg I.vertexEquiv ha),
      hh.symm.trans (congrArg I.vertexEquiv hb)⟩
    change ¬ D.missing (I.edgeEquiv.symm (I.edgeEquiv e))
    rw [Equiv.symm_apply_apply]
    exact hd.2

/-- Helper toward Proposition 3.9: existential intrinsic steps are
exactly the source cut's directed steps, retaining the witnessing edge. -/
theorem intrinsicStageDirectedStep_image_iff (D : M0CutData W H)
    (a b : WholePlaneVertex W) :
    (∃ e : A.E, IntrinsicStageEdgeStep A (I.edgeEquiv '' D.edges)
      (fun f => D.missing (I.edgeEquiv.symm f)) e (I.vertexEquiv a) (I.vertexEquiv b)) ↔
      m0CutDirectedStep W H D.seam a b := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨f, rfl⟩ := I.edgeEquiv.surjective e
    obtain ⟨hf, ht, ha, hb⟩ :=
      (intrinsicStageEdgeStep_image_iff W H G hp A I D f a b).mp he
    exact ⟨(f, false), ht, hf, ha, hb⟩
  · rintro ⟨⟨e, bit⟩, ht, he, ha, hb⟩
    cases bit with
    | false => exact ⟨I.edgeEquiv e,
        (intrinsicStageEdgeStep_image_iff W H G hp A I D e a b).mpr ⟨he, ht, ha, hb⟩⟩
    | true => exact (ht.1.1 rfl).elim

/-- Helper toward Proposition 3.9: stage vertex, geometric-edge and
present-edge sets are exactly their images under the same isomorphism. -/
theorem intrinsicStage_sets_image (n : ℕ) :
    intrinsicStageAllocatedVertices W A (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j)) n =
      I.vertexEquiv '' intrinsicStageAllocatedVertices W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneVertexι W 0) n ∧
    intrinsicStageAllocatedEdges W A (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n =
      I.edgeEquiv '' intrinsicStageAllocatedEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n ∧
    intrinsicStagePresentEdges W A (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n =
      I.edgeEquiv '' intrinsicStagePresentEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n := by
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · ext e
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · ext e
    constructor
    · rintro ⟨j, hj, hpj, rfl⟩; exact ⟨_, ⟨j, hj, hpj, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨j, hj, hpj, rfl⟩, rfl⟩; exact ⟨j, hj, hpj, rfl⟩

/-- Helper toward Proposition 3.9: allocated and present status, and
hence stage deletion status, are preserved and reflected for every edge.
Ambient and cut missing tags are kept distinct from the stage deletion. -/
theorem intrinsicStage_status_image (D : M0CutData W H) (n : ℕ) (e : WholePlaneEdge W) :
    (I.edgeEquiv e ∈ intrinsicStageAllocatedEdges W A
        (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n ↔
      e ∈ intrinsicStageAllocatedEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n) ∧
    (I.edgeEquiv e ∈ intrinsicStagePresentEdges W A
        (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n ↔
      e ∈ intrinsicStagePresentEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n) ∧
    (I.edgeEquiv e ∈ intrinsicStageAllocatedEdges W A
        (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n ∧
      I.edgeEquiv e ∉ intrinsicStagePresentEdges W A
        (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n ↔
      e ∈ intrinsicStageAllocatedEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n ∧
      e ∉ intrinsicStagePresentEdges W
        (uibotWholePlaneSourceDomain W H G hp) (wholePlaneEdgeι W 0) n) ∧
    ¬ A.map.missing (I.edgeEquiv e) ∧
    ((fun f => D.missing (I.edgeEquiv.symm f)) (I.edgeEquiv e) ↔ D.missing e) := by
  have ha := (intrinsicStage_sets_image W H G hp A I n).2.1
  have hpresent := (intrinsicStage_sets_image W H G hp A I n).2.2
  dsimp only [uibotWholePlaneSourceDomain] at ha hpresent ⊢
  rw [ha, hpresent]
  have him (S : Set (WholePlaneEdge W)) : I.edgeEquiv e ∈ I.edgeEquiv '' S ↔ e ∈ S := by
    constructor
    · rintro ⟨f, hf, hfe⟩
      exact I.edgeEquiv.injective hfe ▸ hf
    · intro he
      exact ⟨e, he, rfl⟩
  rw [him, him]
  refine ⟨Iff.rfl, Iff.rfl, Iff.rfl,
    (fun hm => ((I.missing_map e).mp hm) (hp e)), ?_⟩
  rw [Equiv.symm_apply_apply]

/-- Helper toward Proposition 3.9: transporting the complete ordered
edge list preserves its length, including the empty path. -/
theorem intrinsicStage_edgeList_length (es : List (WholePlaneEdge W)) :
    (es.map I.edgeEquiv).length = es.length := List.length_map _

/-- Helper toward Proposition 3.9: a stopped-stage path transports in
both directions, preserving its stage, length, allocation and presence flags. -/
theorem intrinsicIdentifiedStagePath_image_iff (n N : ℕ)
    (p : Fin (N + 1) → WholePlaneVertex W) :
    IntrinsicIdentifiedStagePath W A
      (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
      (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)) n N
      (fun i => I.vertexEquiv (p i)) ↔
    IdentifiedStagePath W (wholePlaneVertexι W 0) n N p := by
  have hend (j : ℕ) := uibotWholePlaneSourceMap_endpoints W H G hp (wholePlaneEdgeι W 0 j)
  have ht (j : ℕ) := intrinsicDirected_tail_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
    ⟨wholePlaneEdgeι W 0 j, fun hm => hm (hp _)⟩
  have hh (j : ℕ) := intrinsicDirected_head_map
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
    ⟨wholePlaneEdgeι W 0 j, fun hm => hm (hp _)⟩
  constructor
  · rintro ⟨hv, he⟩
    constructor
    · intro i
      obtain ⟨j, hj, hij⟩ := hv i
      exact ⟨j, hj, I.vertexEquiv.injective hij⟩
    · intro i
      obtain ⟨j, hj, hpj, he, ha, hb⟩ := he i
      exact ⟨j, hj, hpj,
        I.vertexEquiv.injective ((congrArg I.vertexEquiv (hend j).1).symm.trans
          ((ht j).trans ha)),
        I.vertexEquiv.injective ((congrArg I.vertexEquiv (hend j).2).symm.trans
          ((hh j).trans hb))⟩
  · rintro ⟨hv, he⟩
    constructor
    · intro i
      obtain ⟨j, hj, hij⟩ := hv i
      exact ⟨j, hj, congrArg I.vertexEquiv hij⟩
    · intro i
      obtain ⟨j, hj, hpj, ha, hb⟩ := he i
      refine ⟨j, hj, hpj, fun hm => ((I.missing_map _).mp hm) (hp _), ?_, ?_⟩
      · exact (ht j).symm.trans (congrArg I.vertexEquiv ((hend j).1.trans ha))
      · exact (hh j).symm.trans (congrArg I.vertexEquiv ((hend j).2.trans hb))

end Image

section Boundary
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G) A.map A.root)

local notation "D" => m0CutData W H h hLL
local notation "activeEdges" => intrinsicStageActiveEdges W H G hp A I

/-- Helper toward Proposition 3.9: the image boundary label is visited
at its least active-initial time, simultaneously including index zero. -/
theorem intrinsicStage_boundaryHitTime_isLeast (k : ℤ) :
    IsLeast {n : ℕ | I.vertexEquiv ((D).x k) = intrinsicStageActiveInitial A activeEdges n}
      (boundaryHitTime (shiftedStream W 0) h k) := by
  have hs := m0Cut_boundaryHitTime_isLeast_visit W H h hLL k
  have heq (n : ℕ) : I.vertexEquiv ((D).x k) = intrinsicStageActiveInitial A activeEdges n ↔
      (D).x k = wholePlaneEdgeWest W (wholePlaneEdgeι W 0 (act (shiftedStream W 0) n)) := by
    rw [intrinsicStageActiveInitial_eq]
    exact I.vertexEquiv.injective.eq_iff
  exact ⟨(heq _).mpr hs.1, fun n hn => hs.2 ((heq n).mp hn)⟩

/-- Helper toward Proposition 3.9: the actual minimum of intrinsic
active-initial visits to an image boundary label; attainment is already proved. -/
@[expose] def intrinsicStageBoundaryTime (k : ℤ) : ℕ :=
  Nat.find (show ∃ n, I.vertexEquiv ((D).x k) = intrinsicStageActiveInitial A activeEdges n from
    ⟨_, (intrinsicStage_boundaryHitTime_isLeast W H h hLL G hp A I k).1⟩)

/-- Helper toward Proposition 3.9: the intrinsic minimum equals the
coordinate hitting time at every integer boundary index, including zero. -/
theorem intrinsicStageBoundaryTime_eq (k : ℤ) :
    intrinsicStageBoundaryTime W H h hLL G hp A I k =
      boundaryHitTime (shiftedStream W 0) h k := by
  apply le_antisymm
  · exact Nat.find_min' _ (intrinsicStage_boundaryHitTime_isLeast W H h hLL G hp A I k).1
  · exact (intrinsicStage_boundaryHitTime_isLeast W H h hLL G hp A I k).2
      (Nat.find_spec _)

/-- Helper toward Proposition 3.9: every intrinsic finite or infinite
image-cut path has the complete edge-preserving shifted lift from Lemma 5.2,
at the actual minimum of intrinsic active-initial visits. No hitting-time
or path-containment premise is added. -/
theorem intrinsicStageShiftContainment_image (k : ℤ) :
    IntrinsicStageShiftContainment W A
      (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
      (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j))
      (I.edgeEquiv '' (D).edges) (fun e => (D).missing (I.edgeEquiv.symm e))
      (I.vertexEquiv ((D).x k)) (intrinsicStageBoundaryTime W H h hLL G hp A I k) := by
  rw [intrinsicStageBoundaryTime_eq]
  have hc := m0Cut_shiftContainment W H h hLL k
  constructor
  · intro n p e hp0 hs
    let p' := fun i => I.vertexEquiv.symm (p i)
    let e' := fun i => I.edgeEquiv.symm (e i)
    have hstep (i : Fin n) : e' i ∈ (D).edges ∧ (D).tail (e' i, false) ∧
        wholePlaneEdgeWest W (e' i) = p' i.castSucc ∧
        wholePlaneEdgeEast W (e' i) = p' i.succ := by
      apply (intrinsicStageEdgeStep_image_iff W H G hp A I D _ _ _).mp
      simpa only [e', p', Equiv.apply_symm_apply] using hs i
    have hp0' : p' 0 = (D).x k := by
      dsimp only [p']; rw [hp0, Equiv.symm_apply_apply]
    obtain ⟨m, z, q, hroot, hend, hedges, hlen⟩ := hc.1 n p' e' hp0'
      (fun i => (hstep i).1) (fun i => (hstep i).2.1)
      (fun i => (hstep i).2.2.1) (fun i => (hstep i).2.2.2)
    refine ⟨m, z, q, congrArg I.vertexEquiv hroot, ?_, ?_, hlen⟩
    · simpa only [p', Equiv.apply_symm_apply] using congrArg I.vertexEquiv hend
    · simpa only [List.map_map, Function.comp_def, List.map_ofFn,
        e', Equiv.apply_symm_apply] using congrArg (List.map I.edgeEquiv) hedges
  · intro p e hp0 hs
    let p' := fun n => I.vertexEquiv.symm (p n)
    let e' := fun n => I.edgeEquiv.symm (e n)
    have hstep (n : ℕ) : e' n ∈ (D).edges ∧ (D).tail (e' n, false) ∧
        wholePlaneEdgeWest W (e' n) = p' n ∧
        wholePlaneEdgeEast W (e' n) = p' (n + 1) := by
      apply (intrinsicStageEdgeStep_image_iff W H G hp A I D _ _ _).mp
      simpa only [e', p', Equiv.apply_symm_apply] using hs n
    let P : M0CutInfinitePath W H D ((D).x k) := {
      edge := e'
      inCut := fun n => (hstep n).1
      directed := fun n => (hstep n).2.1
      start := (hstep 0).2.2.1.trans (by
        dsimp only [p']; rw [hp0, Equiv.symm_apply_apply])
      chain := fun n => (hstep n).2.2.2.trans (hstep (n + 1)).2.2.1.symm }
    obtain ⟨Q, hQ⟩ := hc.2 P
    refine ⟨Q, fun n => ?_⟩
    simpa only [P, e', Equiv.apply_symm_apply] using congrArg I.edgeEquiv (hQ n)

end Boundary

/-- Helper toward Proposition 3.9: on one iid probability-one event,
the same recovered cut and stopping times work for every representative of
the sampled class and every rooted geometric isomorphism to it. This includes
all finite and infinite containment paths, all stopped-stage path carriers,
and the actual Lemma 7.1 stage paths with their original length lower bound. -/
theorem ae_intrinsicStage_identification :
    ∀ᵐ U ∂RandomWalk.wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        let V := fun j => I.vertexEquiv (wholePlaneVertexι W 0 j)
        let E := fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j)
        let S := I.edgeEquiv '' D.edges
        let missing := fun e => D.missing (I.edgeEquiv.symm e)
        let t := intrinsicStageBoundaryTime W H h hLL G hp A I
        (∀ k : ℤ,
          IsLeast {n : ℕ | I.vertexEquiv (D.x k) = intrinsicStageActiveInitial A
            (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
          t k = boundaryHitTime (shiftedStream W 0) h k ∧
          IntrinsicStageShiftContainment W A V E S missing (I.vertexEquiv (D.x k)) (t k)) ∧
        (∀ n : ℕ,
          intrinsicStageAllocatedVertices W A V n = I.vertexEquiv ''
            intrinsicStageAllocatedVertices W (uibotWholePlaneSourceDomain W H G hp)
              (wholePlaneVertexι W 0) n ∧
          intrinsicStageAllocatedEdges W A E n = I.edgeEquiv ''
            intrinsicStageAllocatedEdges W (uibotWholePlaneSourceDomain W H G hp)
              (wholePlaneEdgeι W 0) n ∧
          intrinsicStagePresentEdges W A E n = I.edgeEquiv ''
            intrinsicStagePresentEdges W (uibotWholePlaneSourceDomain W H G hp)
              (wholePlaneEdgeι W 0) n) ∧
        (∀ (n N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
          IntrinsicIdentifiedStagePath W A V E n N (fun i => I.vertexEquiv (p i)) ↔
            IdentifiedStagePath W (wholePlaneVertexι W 0) n N p) ∧
        ∀ ell k : ℕ, 1 ≤ ell → ell < k →
          ∃ (N : ℕ) (p : Fin (N + 1) → A.V),
            (∀ i : Fin N, ∃ e : A.E,
              IntrinsicStageEdgeStep A S missing e (p i.castSucc) (p i.succ)) ∧
            IntrinsicIdentifiedStagePath W A V E (t (-(k : ℤ))) N p ∧
            (max (identifiedLDPBusemann W (-(ell : ℤ)) -
              identifiedLDPBusemann W (-(k : ℤ))) 0).toNat ≤ N := by
  filter_upwards [uibotIntrinsicCut_sample_realization, uibotRecoveredCode_ae,
    lem_long_path_identified] with U hreal hcode hlong
  dsimp only at hreal ⊢
  rw [hcode] at hreal ⊢
  obtain ⟨_, _, H, h, hpast, hp, hclass, hisos, _⟩ := hreal
  let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
    (wholePlaneEdgeι U 0 (kmswLLCreatedEdge (shiftedStream U 0)
      (boundaryHitTime (shiftedStream U 0) h (k - 1))))
  obtain ⟨H', h', hLL', _, hpaths⟩ := hlong
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  have hhl : hLL' = hLL := Subsingleton.elim _ _
  subst hLL'
  refine ⟨H, h, hpast, hp, hclass, ?_⟩
  intro A hA
  refine ⟨hisos A hA, ?_⟩
  intro I
  let G := WholePlanePastGlueDrawing.glueDrawing U h hpast H
  let D := m0CutData U H h hLL
  refine ⟨?_, intrinsicStage_sets_image U H G hp A I,
    intrinsicIdentifiedStagePath_image_iff U H G hp A I, ?_⟩
  · intro k
    refine ⟨?_, intrinsicStageBoundaryTime_eq U H h hLL G hp A I k,
      intrinsicStageShiftContainment_image U H h hLL G hp A I k⟩
    rw [intrinsicStageBoundaryTime_eq]
    exact intrinsicStage_boundaryHitTime_isLeast U H h hLL G hp A I k
  · intro ell k hell hk
    obtain ⟨N, p, hstep, hstage, hbound⟩ := hpaths ell k hell hk
    refine ⟨N, (fun i => I.vertexEquiv (p i)), ?_, ?_, hbound⟩
    · intro i
      exact (intrinsicStageDirectedStep_image_iff U H G hp A I D _ _).mpr (hstep i)
    · rw [intrinsicStageBoundaryTime_eq]
      exact (intrinsicIdentifiedStagePath_image_iff U H G hp A I _ _ p).mpr hstage

end DirectedDistances.PaperProofs.Section3
end
