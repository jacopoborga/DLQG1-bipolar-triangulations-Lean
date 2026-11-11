module

public import DirectedDistances.KMSW.RunBoundaryVertexLabels
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.KMSWShift
import DirectedDistances.KMSW.KMSWWholePlaneColimit






public section
namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW






theorem rightBoundary_vertices_merge_of_edges (w : ℕ → Fin 3) (n σ0 σn : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hmerge : ∀ k : ℕ, 1 ≤ k →
      kmswRightBoundaryEdge w (k - 1 + σ0) =
        kmswWindowEdgeMapInf w n
          (kmswRightBoundaryEdge (fun i => w (n + i)) (k - 1 + σn))) :
    ∀ j : ℕ,
      boundaryVertex w h0 ((j + σ0 : ℕ) : ℤ) =
        kmswWindowVertexMapInf w n
          (boundaryVertex (fun i => w (n + i)) hn ((j + σn : ℕ) : ℤ)) := by
  intro j
  let u := fun i => w (n + i)
  have hidx0 : (j + 1) - 1 + σ0 = j + σ0 := by omega
  have hidxn : (j + 1) - 1 + σn = j + σn := by omega
  have hm := hmerge (j + 1) (by omega)
  rw [hidx0, hidxn] at hm
  calc
    boundaryVertex w h0 ((j + σ0 : ℕ) : ℤ) =
        edgeWest w (kmswRightBoundaryEdge w (j + σ0)) :=
      (kmswRightBoundaryEdge_hit_endpoints w h0 (j + σ0)).1.symm
    _ = edgeWest w (kmswWindowEdgeMapInf w n
        (kmswRightBoundaryEdge u (j + σn))) := congrArg (edgeWest w) hm
    _ = kmswWindowVertexMapInf w n
        (edgeWest u (kmswRightBoundaryEdge u (j + σn))) :=
      kmswWindowEdgeMapInf_edgeWest w n (kmswRightBoundaryEdge u (j + σn))
    _ = kmswWindowVertexMapInf w n
        (boundaryVertex u hn ((j + σn : ℕ) : ℤ)) := by
      rw [(kmswRightBoundaryEdge_hit_endpoints u hn (j + σn)).1]

end DirectedDistances.PaperProofs.Section7
