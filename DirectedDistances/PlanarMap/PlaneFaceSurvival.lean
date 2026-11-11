module

public import DirectedDistances.KMSW.StageTriangleBoundedFace
public import DirectedDistances.PlanarMap.GraphRegion

public section

namespace DirectedDistances.PlanarMap

open DirectedDistances.KMSW

variable {D V D' V' : Type*}
variable {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V'}

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
An open bounded face survives deletion of drawing geometry when its entire frontier -/
theorem planeFace_survives
    (P : PLDrawing D V flip rot vert) (Q : PLDrawing D' V' flip' rot' vert')
    (F : PlaneFaces P) (hopen : IsOpen F.val.val)
    (hsub : Q.image ⊆ P.image) (hfront : frontier F.val.val ⊆ Q.image) :
    ∃ G : PlaneFaces Q, G.val.val = F.val.val := by
  obtain ⟨z, hz, hF⟩ := F.val.property
  have hzF : z ∈ F.val.val := by
    rw [hF]
    exact mem_connectedComponentIn hz
  have hconn : IsConnected F.val.val := by
    rw [hF]
    exact isConnected_connectedComponentIn_iff.mpr hz
  have hdisj : F.val.val ∩ Q.image = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact P.face_subset_compl F.val hx.1 (hsub hx.2)
  have hcomponent : connectedComponentIn Q.imageᶜ z = F.val.val :=
    connectedComponentIn_compl_eq_of_open_connected hopen hconn ⟨z, hzF⟩
      hdisj hfront hzF
  let G : Q.Face := ⟨F.val.val, z, (fun hzQ => hz (hsub hzQ)), hcomponent.symm⟩
  exact ⟨⟨G, F.property⟩, rfl⟩

/-- Helper toward Lemma 5.12 (lem-flow-line-times); not a paper result.
Equality of oriented polylines preserves the left-hand wedge defining a bordering
dart, whenever the face sets agree. Trace equality alone does not specify that wedge. -/
theorem dartBorders_transport
    (P : PLDrawing D V flip rot vert) (Q : PLDrawing D' V' flip' rot' vert')
    (F : P.Face) (G : Q.Face) (d : D) (d' : D')
    (hface : G.val = F.val) (harc : Q.arc d' = P.arc d)
    (hborder : P.dartBorders d F) : Q.dartBorders d' G := by
  unfold PLDrawing.dartBorders at hborder ⊢
  rw [harc, hface]
  exact hborder

end DirectedDistances.PlanarMap
