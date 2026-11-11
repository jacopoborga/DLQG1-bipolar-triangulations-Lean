module

public import DirectedDistances.KMSW.KMSWWindowPatchRotation
public import DirectedDistances.KMSW.KMSWWindowPatchVertex
public import DirectedDistances.KMSW.StageRotation

import DirectedDistances.KMSW.KMSWWindowFreshVertexStar
import DirectedDistances.KMSW.KMSWWindowFreshPresence
import DirectedDistances.KMSW.KMSWWindowFreshOuterRotation
import DirectedDistances.KMSW.KMSWWindowPatchInjective

/-! Helper toward prop-disk-bs-conv / Proposition 5.16
capture of the induced finite structure (darts, geometric edges with
present/missing status, rotation, faces) on any set of fresh window vertices
through the KMSW window maps; no ball, center, root marker or Definition 3.8 -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Every dart endpoint in a finite set of fresh window vertices is captured
bijectively by the global window dart map
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetDartCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v) :
    (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S →
      stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m d) ∈
        S.image (kmswWindowPatchVertexMap w s m)) ∧
    (∀ d₁ d₂ : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d₁ ∈ S →
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d₂ ∈ S →
      kmswWindowDartMap w s m d₁ = kmswWindowDartMap w s m d₂ → d₁ = d₂) ∧
    (∀ g : StageDart (kmswStage w (s + m)).nextEdge,
      stageEndpoint (kmswStage w (s + m)) g ∈
        S.image (kmswWindowPatchVertexMap w s m) →
      ∃ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S ∧
          kmswWindowDartMap w s m d = g) ∧
    (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage w (s + m)) (kmswWindowDartMap w s m d) =
        kmswWindowPatchVertexMap w s m
          (stageEndpoint (kmswStage (fun i => w (s + i)) m) d)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    have hvertex := kmswWindowDartMap_vertex w s m d
    change stageEndpoint (kmswStage w (s + m))
      (kmswWindowDartMap w s m d) = _ at hvertex
    rw [hvertex]
    exact Finset.mem_image.mpr
      ⟨stageEndpoint (kmswStage (fun i => w (s + i)) m) d, hd, rfl⟩
  · intro d₁ d₂ _ _ heq
    exact kmswWindowDartMap_injective w s m heq
  · intro g hg
    obtain ⟨v, hv, hvg⟩ := Finset.mem_image.mp hg
    obtain ⟨hvbound, hnew⟩ := hS v hv
    have hendpoint :
        stageEndpoint (kmswStage w (s + m)) g =
          kmswWindowPatchVertexMap w s m v := by
      rw [hvg]
    obtain ⟨d, ⟨hd, hmap⟩, _⟩ :=
      (kmswWindowDartMap_star_bijective_of_fresh w s m v hvbound hnew).2
        g hendpoint
    have hmem : stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S := by
      rw [hd]
      exact hv
    exact ⟨d, hmem, hmap⟩
  · intro d
    exact kmswWindowDartMap_vertex w s m d

/-- Rotation and inverse rotation are transported at every dart endpoint in
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetRotationCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S) :
    (kmswMap w (s + m)).rot (kmswWindowDartMap w s m d) =
        kmswWindowDartMap w s m ((kmswMap (fun i => w (s + i)) m).rot d) ∧
      (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m d) =
        kmswWindowDartMap w s m
          ((kmswMap (fun i => w (s + i)) m).rot.symm d) := by
  obtain ⟨hv, hnew⟩ := hS _ hd
  exact ⟨kmswWindowDartMap_rot_of_fresh w s m _ hv hnew d rfl,
    kmswWindowDartMap_rot_symm_of_fresh w s m _ hv hnew d rfl⟩

/-- Face successor is transported when the endpoint of the opposite dart lies
in the fresh set; this is the exact hypothesis used by
`faceSucc = rot.symm ∘ edgeFlip`
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetFaceSuccCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m)
      (edgeFlip _ d) ∈ S) :
    (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m
        ((kmswMap (fun i => w (s + i)) m).faceSucc d) := by
  obtain ⟨hv, hnew⟩ := hS _ hd
  change (kmswMap w (s + m)).rot.symm
      (edgeFlip _ (kmswWindowDartMap w s m d)) =
    kmswWindowDartMap w s m
      ((kmswMap (fun i => w (s + i)) m).rot.symm (edgeFlip _ d))
  rw [kmswWindowDartMap_edgeFlip w s m d]
  exact kmswWindowDartMap_rot_symm_of_fresh w s m _ hv hnew
    (edgeFlip _ d) rfl

/-- The window dart map preserves the underlying geometric edge involution;
this identity does not need freshness
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetEdgeFlipCapture
    (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    kmswWindowDartMap w s m (edgeFlip _ d) =
      edgeFlip _ (kmswWindowDartMap w s m d) :=
  (kmswWindowDartMap_edgeFlip w s m d).symm

/-- Present versus missing status is preserved on each captured edge; one
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetPresentCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hd : stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S) :
    (kmswStage (fun i => w (s + i)) m).present d.1.val =
      (kmswStage w (s + m)).present (kmswWindowDartMap w s m d).1.val := by
  obtain ⟨hv, hnew⟩ := hS _ hd
  have hiff := kmswWindowDartMap_present_iff_of_fresh w s m _ hv hnew d rfl
  cases hs : (kmswStage (fun i => w (s + i)) m).present d.1.val <;>
    cases hg : (kmswStage w (s + m)).present
      (kmswWindowDartMap w s m d).1.val <;> simp_all

/-- Edge IDs whose two endpoints lie in the chosen finite window-vertex set.
IDs are retained, so parallel geometric edges remain distinct
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
@[expose] def kmswWindowFreshSetSourceEdges
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) :
    Set (Fin (kmswStage (fun i => w (s + i)) m).nextEdge) :=
  {e | (kmswStage (fun i => w (s + i)) m).west e.val ∈ S ∧
    (kmswStage (fun i => w (s + i)) m).east e.val ∈ S}

/-- Global edge IDs whose endpoints lie in the image of the chosen finite
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
@[expose] def kmswWindowFreshSetTargetEdges
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) :
    Set (Fin (kmswStage w (s + m)).nextEdge) :=
  {e | (kmswStage w (s + m)).west e.val ∈
      S.image (kmswWindowPatchVertexMap w s m) ∧
    (kmswStage w (s + m)).east e.val ∈
      S.image (kmswWindowPatchVertexMap w s m)}

/-- The edge-ID component of the window dart map, using its west dart
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
@[expose] def kmswWindowFreshSetEdgeMap
    (w : ℕ → Fin 3) (s m : ℕ)
    (e : Fin (kmswStage (fun i => w (s + i)) m).nextEdge) :
    Fin (kmswStage w (s + m)).nextEdge :=
  (kmswWindowDartMap w s m (e, false)).1

/-- West endpoints commute with the induced edge-ID map
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetEdgeMap_west
    (w : ℕ → Fin 3) (s m : ℕ)
    (e : Fin (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (kmswStage w (s + m)).west
        (kmswWindowFreshSetEdgeMap w s m e).val =
      kmswWindowPatchVertexMap w s m
        ((kmswStage (fun i => w (s + i)) m).west e.val) := by
  have h := kmswWindowDartMap_vertex w s m (e, false)
  have hside : (kmswWindowDartMap w s m (e, false)).2 = false := rfl
  simpa [stageEndpoint, kmswWindowFreshSetEdgeMap, hside] using h

/-- East endpoints commute with the induced edge-ID map
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetEdgeMap_east
    (w : ℕ → Fin 3) (s m : ℕ)
    (e : Fin (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (kmswStage w (s + m)).east
        (kmswWindowFreshSetEdgeMap w s m e).val =
      kmswWindowPatchVertexMap w s m
        ((kmswStage (fun i => w (s + i)) m).east e.val) := by
  have h := kmswWindowDartMap_vertex w s m (e, true)
  have hside : (kmswWindowDartMap w s m (e, true)).2 = true := rfl
  have hid : (kmswWindowDartMap w s m (e, true)).1 =
      (kmswWindowDartMap w s m (e, false)).1 := rfl
  simpa [stageEndpoint, kmswWindowFreshSetEdgeMap, hside, hid] using h

/-- The edge-ID map restricted to induced geometric edges
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
@[expose] def kmswWindowFreshSetEdgeMapOn
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) :
    {e // e ∈ kmswWindowFreshSetSourceEdges w s m S} →
      {e // e ∈ kmswWindowFreshSetTargetEdges w s m S} :=
  fun e => ⟨kmswWindowFreshSetEdgeMap w s m e.val, by
    change (kmswStage w (s + m)).west
        (kmswWindowFreshSetEdgeMap w s m e.val).val ∈
          S.image (kmswWindowPatchVertexMap w s m) ∧
      (kmswStage w (s + m)).east
        (kmswWindowFreshSetEdgeMap w s m e.val).val ∈
          S.image (kmswWindowPatchVertexMap w s m)
    have hmem := e.property
    change (kmswStage (fun i => w (s + i)) m).west e.val ∈ S ∧
      (kmswStage (fun i => w (s + i)) m).east e.val ∈ S at hmem
    refine ⟨?_, ?_⟩
    · rw [kmswWindowFreshSetEdgeMap_west]
      exact Finset.mem_image.mpr ⟨_, hmem.1, rfl⟩
    · rw [kmswWindowFreshSetEdgeMap_east]
      exact Finset.mem_image.mpr ⟨_, hmem.2, rfl⟩⟩

/-- Present/missing status is retained by the edge-ID map on induced edges
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetEdgeMap_present
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (e : {e // e ∈ kmswWindowFreshSetSourceEdges w s m S}) :
    (kmswStage (fun i => w (s + i)) m).present e.1.val =
      (kmswStage w (s + m)).present
        (kmswWindowFreshSetEdgeMap w s m e.1).val := by
  have hmem := e.property
  change (kmswStage (fun i => w (s + i)) m).west e.1.val ∈ S ∧
    (kmswStage (fun i => w (s + i)) m).east e.1.val ∈ S at hmem
  have hp := kmswWindowFreshSetPresentCapture w s m S hS
    (e.1, false) hmem.1
  simpa [kmswWindowFreshSetEdgeMap] using hp

/-- Induced geometric edge IDs correspond bijectively, preserving edge
multiplicity, for any finite set of fresh window vertices
Helper toward Proposition 5.16, not the paper result.
No Definition 3.8 reading, ball, or centre is chosen. -/
theorem kmswWindowFreshSetEdgeMap_bijective
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v) :
    Function.Bijective (kmswWindowFreshSetEdgeMapOn w s m S) := by
  constructor
  · intro e f hef
    apply Subtype.ext
    have heq : kmswWindowFreshSetEdgeMap w s m e.1 =
        kmswWindowFreshSetEdgeMap w s m f.1 := congrArg Subtype.val hef
    have hdart : kmswWindowDartMap w s m (e.1, false) =
        kmswWindowDartMap w s m (f.1, false) := by
      exact Prod.ext heq rfl
    have hsource := kmswWindowDartMap_injective w s m hdart
    exact congrArg Prod.fst hsource
  · intro g
    obtain ⟨v, hvS, hw⟩ := Finset.mem_image.mp g.2.1
    obtain ⟨z, hzS, he⟩ := Finset.mem_image.mp g.2.2
    obtain ⟨hvbound, hnew⟩ := hS v hvS
    let q : StageDart (kmswStage w (s + m)).nextEdge := (g.1, false)
    have hq : stageEndpoint (kmswStage w (s + m)) q =
        kmswWindowPatchVertexMap w s m v := by
      simpa [q, stageEndpoint] using hw.symm
    obtain ⟨d, ⟨hd, hmap⟩, _⟩ :=
      (kmswWindowDartMap_star_bijective_of_fresh w s m v hvbound hnew).2
        q hq
    have hside : d.2 = false := by
      have hmapSide := congrArg Prod.snd hmap
      simpa only [kmswWindowDartMap, q] using hmapSide
    have hwest : (kmswStage (fun i => w (s + i)) m).west d.1.val = v := by
      simpa [stageEndpoint, hside] using hd
    have hIDEast : (kmswWindowDartMap w s m (d.1, true)).1 = g.1 := by
      calc
        _ = (kmswWindowDartMap w s m d).1 := by
          cases d with
          | mk e b => rfl
        _ = q.1 := congrArg Prod.fst hmap
        _ = g.1 := rfl
    have hsideEast : (kmswWindowDartMap w s m (d.1, true)).2 = true := rfl
    have hvertexEast : kmswWindowPatchVertexMap w s m
        ((kmswStage (fun i => w (s + i)) m).east d.1.val) =
          (kmswStage w (s + m)).east g.1.val := by
      have h := kmswWindowDartMap_vertex w s m (d.1, true)
      have h' : (kmswStage w (s + m)).east g.1.val =
          kmswWindowPatchVertexMap w s m
            ((kmswStage (fun i => w (s + i)) m).east d.1.val) := by
        simpa [hIDEast, hsideEast] using h
      exact h'.symm
    have hebound : (kmswStage (fun i => w (s + i)) m).east d.1.val <
        (kmswStage (fun i => w (s + i)) m).nextVertex :=
      (kmswStage_endpoints_lt_nextVertex (fun i => w (s + i)) m d.1.val
        d.1.isLt).2
    obtain ⟨hzbound, _⟩ := hS z hzS
    have hsourceEast : (kmswStage (fun i => w (s + i)) m).east d.1.val = z :=
      kmswWindowPatchVertexMap_injOn w s m hebound hzbound
        (hvertexEast.trans he.symm)
    have hsource : d.1 ∈ kmswWindowFreshSetSourceEdges w s m S := by
      change (kmswStage (fun i => w (s + i)) m).west d.1.val ∈ S ∧
        (kmswStage (fun i => w (s + i)) m).east d.1.val ∈ S
      exact ⟨hwest ▸ hvS, hsourceEast ▸ hzS⟩
    have hdprod : d = (d.1, false) := by
      cases d with
      | mk e b =>
        have hb : b = false := by simpa using hside
        subst b
        rfl
    have hID : kmswWindowFreshSetEdgeMap w s m d.1 = g.1 := by
      change (kmswWindowDartMap w s m (d.1, false)).1 = g.1
      rw [← hdprod]
      exact congrArg Prod.fst hmap
    refine ⟨⟨d.1, hsource⟩, ?_⟩
    apply Subtype.ext
    exact hID

end DirectedDistances.KMSW
