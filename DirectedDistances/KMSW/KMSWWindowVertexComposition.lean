module

public import DirectedDistances.KMSW.KMSWWindowPatchVertex
import DirectedDistances.KMSW.KMSWWindowPatchComposition
import DirectedDistances.KMSW.KMSWWindowPatchInjective
import DirectedDistances.KMSW.StageVertices

/-! Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
window patch VERTEX maps; does not construct the whole-plane carrier, β_0^{L,R},
the cut or the source identification (Q-F4c is an unanswered author question);
not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
window patch VERTEX maps; does not construct the whole-plane carrier, β_0^{L,R},
the cut or the source identification (Q-F4c is an unanswered author question);
not the paper result. Every allocated vertex has a geometric incident dart,
including both initial vertices and endpoints of missing edges. -/
theorem kmswWindowPatchVertexMap_comp (w : ℕ → Fin 3) (s t m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + (t + i))) m).nextVertex) :
    kmswWindowPatchVertexMap w s (t + m)
        (kmswWindowPatchVertexMap (fun i => w (s + i)) t m v) =
      kmswWindowPatchVertexMap w (s + t) m v := by
  obtain ⟨d, hd⟩ := stageEndpoint_exists (fun i => w (s + (t + i))) m v hv
  let d' : StageDart (kmswStage (fun i => w ((s + t) + i)) m).nextEdge :=
    (⟨d.1.val, by simpa only [Nat.add_assoc] using d.1.isLt⟩, d.2)
  let r := kmswWindowDartMap w (s + t) m d'
  have hi :
      stageEndpoint (kmswStage (fun i => w (s + i)) (t + m))
          (kmswWindowDartMap (fun i => w (s + i)) t m d) =
        kmswWindowPatchVertexMap (fun i => w (s + i)) t m v := by
    exact (kmswWindowDartMap_vertex (fun i => w (s + i)) t m d).trans
      (congrArg (kmswWindowPatchVertexMap (fun i => w (s + i)) t m) hd)
  have ho :
      stageEndpoint (kmswStage w (s + (t + m)))
          (kmswWindowDartMap w s (t + m)
            (kmswWindowDartMap (fun i => w (s + i)) t m d)) =
        kmswWindowPatchVertexMap w s (t + m)
          (kmswWindowPatchVertexMap (fun i => w (s + i)) t m v) :=
    (kmswWindowDartMap_vertex w s (t + m) _).trans
      (congrArg (kmswWindowPatchVertexMap w s (t + m)) hi)
  have hd' : stageEndpoint (kmswStage (fun i => w ((s + t) + i)) m) d' = v := by
    simpa only [d', stageEndpoint, Nat.add_assoc] using hd
  have hr : stageEndpoint (kmswStage w ((s + t) + m)) r =
      kmswWindowPatchVertexMap w (s + t) m v :=
    (kmswWindowDartMap_vertex w (s + t) m d').trans
      (congrArg (kmswWindowPatchVertexMap w (s + t) m) hd')
  have hc := congrArg (stageEndpoint (kmswStage w (s + (t + m))))
    (kmswWindowDartMap_comp w s t m d)
  apply ho.symm.trans
  apply hc.trans
  simpa only [stageEndpoint, r, Nat.add_assoc] using hr

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
allocated vertices, including stage zero. Does not construct the whole-plane
carrier, β_0^{L,R}, the cut or the source identification (Q-F4c is an unanswered
author question); not the paper result. -/
theorem kmswWindowPatchVertexMap_zero_start (w : ℕ → Fin 3) (m v : ℕ)
    (hv : v < (kmswStage w m).nextVertex) :
    kmswWindowPatchVertexMap w 0 m v = v := by
  have hcomp := kmswWindowPatchVertexMap_comp w 0 0 m v
    (by simpa only [Nat.zero_add] using hv)
  have hbound := (kmswWindowPatchVertexMap_rel w 0 m).vertex_bound v
    (by simpa only [Nat.zero_add] using hv)
  have hinj := kmswWindowPatchVertexMap_injOn w 0 m
  simp only [Nat.zero_add] at hcomp hbound hinj
  exact hinj hbound hv hcomp

end DirectedDistances.KMSW
