module

public import DirectedDistances.KMSW.KMSWWindowPatchVertex
import DirectedDistances.KMSW.KMSWWindowPatchComposition
import DirectedDistances.KMSW.KMSWWindowVertexComposition
import DirectedDistances.KMSW.KMSWWindowPatchInjective
import DirectedDistances.KMSW.InfiniteRotation

/-! Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
edge/vertex maps (transition maps of the directed system over start shifts) and
their cocycle; does not construct the whole-plane carrier, its rotation/faces,
β_0^{L,R}, the cut or the source identification (Q-F4c is an unanswered author
question); not the paper result.

The edge map is evaluated at depth `e`; the vertex map at depth `4 * v + 1`.
Both depths allocate their respective identifiers for every code sequence.
Missing geometric edges are included. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
map, evaluated at the canonical allocating depth `e`; not the paper result.
Does not construct the whole-plane carrier, its rotation/faces, β_0^{L,R},
the cut or the source identification (Q-F4c is an unanswered author question). -/
@[expose] def kmswWindowEdgeMapInf (w : ℕ → Fin 3) (s e : ℕ) : ℕ :=
  (kmswWindowPatchData w s e).φ e

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
map, evaluated at the canonical allocating depth `4 * v + 1`; not the paper result.
Does not construct the whole-plane carrier, its rotation/faces, β_0^{L,R},
the cut or the source identification (Q-F4c is an unanswered author question). -/
@[expose] def kmswWindowVertexMapInf (w : ℕ → Fin 3) (s v : ℕ) : ℕ :=
  kmswWindowPatchVertexMap w s (4 * v + 1) v

private theorem vertex_potential_step (F : State) (c : Fin 3) (n : ℕ)
    (h : n + F.UL.length + 2 * F.UR.length ≤ 4 * F.nextVertex) :
    n + 1 + (kmswStep F c).UL.length + 2 * (kmswStep F c).UR.length ≤
      4 * (kmswStep F c).nextVertex := by
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    cases hUR : F.UR with
    | nil =>
      have hlen := congrArg List.length hUR
      simp only [List.length_nil] at hlen
      simp only [kmswStepOfStep, hUR, State.addEdge, List.length_append,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUR
      simp only [List.length_cons] at hlen
      simp only [kmswStepOfStep, hUR, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | left =>
    cases hUL : F.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL, State.addEdge,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUL
      simp only [List.length_reverse, List.length_dropLast, List.length_cons] at hlen
      simp only [kmswStepOfStep, hUL, State.addEdge, List.length_append,
        List.length_reverse, List.length_cons, List.length_nil]
      omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.length_append,
      List.length_dropLast, List.length_cons, List.length_nil]
    omega

private theorem vertex_potential (u : ℕ → Fin 3) (n : ℕ) :
    n + (kmswStage u n).UL.length + 2 * (kmswStage u n).UR.length ≤
      4 * (kmswStage u n).nextVertex := by
  induction n with
  | zero =>
    change 1 ≤ 8
    decide
  | succ n ih => exact vertex_potential_step (kmswStage u n) (u n) n ih

private theorem vertex_allocated_at (u : ℕ → Fin 3) (v : ℕ) :
    v < (kmswStage u (4 * v + 1)).nextVertex := by
  have h := vertex_potential u (4 * v + 1)
  omega

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
with every finite window allocating its argument; not the paper result.
The whole-plane carrier, rotation/faces, β_0^{L,R}, cut and source identification
are not constructed (Q-F4c is an unanswered author question). -/
theorem kmswWindowEdgeMapInf_eq_stage (w : ℕ → Fin 3) (s m e : ℕ)
    (he : e < (kmswStage (fun i => w (s + i)) m).nextEdge) :
    kmswWindowEdgeMapInf w s e = (kmswWindowPatchData w s m).φ e := by
  unfold kmswWindowEdgeMapInf
  by_cases h : m ≤ e
  · exact kmswWindowPatchData_extends_le w s m e h e he
  · exact (kmswWindowPatchData_extends_le w s e m (by omega) e
      (kmsw_edge_allocated_by_self _ e)).symm

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
with every finite window allocating its argument; not the paper result.
The whole-plane carrier, rotation/faces, β_0^{L,R}, cut and source identification
are not constructed (Q-F4c is an unanswered author question). -/
theorem kmswWindowVertexMapInf_eq_stage (w : ℕ → Fin 3) (s m v : ℕ)
    (hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex) :
    kmswWindowVertexMapInf w s v = kmswWindowPatchVertexMap w s m v := by
  unfold kmswWindowVertexMapInf
  by_cases h : m ≤ 4 * v + 1
  · exact kmswWindowPatchVertexMap_extends_le w s m (4 * v + 1) h v hv
  · exact (kmswWindowPatchVertexMap_extends_le w s (4 * v + 1) m (by omega) v
      (vertex_allocated_at _ v)).symm

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
edge IDs, including missing edges; not the paper result. The whole-plane carrier,
rotation/faces, β_0^{L,R}, cut and source identification are not constructed
(Q-F4c is an unanswered author question). -/
theorem kmswWindowEdgeMapInf_injective (w : ℕ → Fin 3) (s : ℕ) :
    Function.Injective (kmswWindowEdgeMapInf w s) := by
  intro e f hef
  let m := max e f
  have he : e < (kmswStage (fun i => w (s + i)) m).nextEdge :=
    (kmsw_edge_allocated_by_self _ e).trans_le
      (kmswStage_nextEdge_mono _ (Nat.le_max_left e f))
  have hf : f < (kmswStage (fun i => w (s + i)) m).nextEdge :=
    (kmsw_edge_allocated_by_self _ f).trans_le
      (kmswStage_nextEdge_mono _ (Nat.le_max_right e f))
  rw [kmswWindowEdgeMapInf_eq_stage w s m e he,
    kmswWindowEdgeMapInf_eq_stage w s m f hf] at hef
  exact (kmswWindowPatchData_rel w s m).edge_injective e he f hf hef

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
not the paper result. The whole-plane carrier, rotation/faces, β_0^{L,R}, cut and
source identification are not constructed (Q-F4c is an unanswered author question). -/
theorem kmswWindowVertexMapInf_injective (w : ℕ → Fin 3) (s : ℕ) :
    Function.Injective (kmswWindowVertexMapInf w s) := by
  intro v z hvz
  let m := max (4 * v + 1) (4 * z + 1)
  have hv : v < (kmswStage (fun i => w (s + i)) m).nextVertex :=
    (vertex_allocated_at _ v).trans_le
      (CutConverse.nextVertex_mono _ (Nat.le_max_left (4 * v + 1) (4 * z + 1)))
  have hz : z < (kmswStage (fun i => w (s + i)) m).nextVertex :=
    (vertex_allocated_at _ z).trans_le
      (CutConverse.nextVertex_mono _ (Nat.le_max_right (4 * v + 1) (4 * z + 1)))
  rw [kmswWindowVertexMapInf_eq_stage w s m v hv,
    kmswWindowVertexMapInf_eq_stage w s m z hz] at hvz
  exact kmswWindowPatchVertexMap_injOn w s m hv hz hvz

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
by the infinite window maps at every allocating stage; not the paper result.
The whole-plane carrier, rotation/faces, β_0^{L,R}, cut and source identification
are not constructed (Q-F4c is an unanswered author question). -/
theorem kmswWindowEdgeMapInf_west (w : ℕ → Fin 3) (s m e : ℕ)
    (he : e < (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (kmswStage w (s + m)).west (kmswWindowEdgeMapInf w s e) =
      kmswWindowVertexMapInf w s ((kmswStage (fun i => w (s + i)) m).west e) := by
  rw [kmswWindowEdgeMapInf_eq_stage w s m e he,
    kmswWindowVertexMapInf_eq_stage w s m _
      (kmswStage_endpoints_lt_nextVertex _ m e he).1]
  exact ((kmswWindowPatchVertexMap_rel w s m).west_endpoint e he).symm

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
by the infinite window maps at every allocating stage; not the paper result.
The whole-plane carrier, rotation/faces, β_0^{L,R}, cut and source identification
are not constructed (Q-F4c is an unanswered author question). -/
theorem kmswWindowEdgeMapInf_east (w : ℕ → Fin 3) (s m e : ℕ)
    (he : e < (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (kmswStage w (s + m)).east (kmswWindowEdgeMapInf w s e) =
      kmswWindowVertexMapInf w s ((kmswStage (fun i => w (s + i)) m).east e) := by
  rw [kmswWindowEdgeMapInf_eq_stage w s m e he,
    kmswWindowVertexMapInf_eq_stage w s m _
      (kmswStage_endpoints_lt_nextVertex _ m e he).2]
  exact ((kmswWindowPatchVertexMap_rel w s m).east_endpoint e he).symm

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
of the directed system over start shifts; not the paper result. The whole-plane
carrier, rotation/faces, β_0^{L,R}, cut and source identification are not constructed
(Q-F4c is an unanswered author question). -/
theorem kmswWindowEdgeMapInf_comp (w : ℕ → Fin 3) (s t e : ℕ) :
    kmswWindowEdgeMapInf w s
        (kmswWindowEdgeMapInf (fun i => w (s + i)) t e) =
      kmswWindowEdgeMapInf w (s + t) e := by
  have he := kmsw_edge_allocated_by_self (fun i => w (s + (t + i))) e
  have hi := (kmswWindowPatchData_rel (fun i => w (s + i)) t e).edge_bound e he
  rw [kmswWindowEdgeMapInf_eq_stage (fun i => w (s + i)) t e e he,
    kmswWindowEdgeMapInf_eq_stage w s (t + e) _ hi,
    kmswWindowEdgeMapInf_eq_stage w (s + t) e e
      (by simpa only [Nat.add_assoc] using he)]
  exact kmswWindowPatchData_phi_comp w s t e e he

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
of the directed system over start shifts; not the paper result. The whole-plane
carrier, rotation/faces, β_0^{L,R}, cut and source identification are not constructed
(Q-F4c is an unanswered author question). -/
theorem kmswWindowVertexMapInf_comp (w : ℕ → Fin 3) (s t v : ℕ) :
    kmswWindowVertexMapInf w s
        (kmswWindowVertexMapInf (fun i => w (s + i)) t v) =
      kmswWindowVertexMapInf w (s + t) v := by
  let m := 4 * v + 1
  have hv := vertex_allocated_at (fun i => w (s + (t + i))) v
  have hi := (kmswWindowPatchVertexMap_rel (fun i => w (s + i)) t m).vertex_bound v hv
  rw [kmswWindowVertexMapInf_eq_stage (fun i => w (s + i)) t m v hv,
    kmswWindowVertexMapInf_eq_stage w s (t + m) _ hi,
    kmswWindowVertexMapInf_eq_stage w (s + t) m v
      (by simpa only [Nat.add_assoc] using hv)]
  exact kmswWindowPatchVertexMap_comp w s t m v hv

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
infinite vertex map; not the paper result. The whole-plane carrier, rotation/faces,
β_0^{L,R}, cut and source identification are not constructed
(Q-F4c is an unanswered author question). -/
theorem kmswWindowVertexMapInf_zero_start (w : ℕ → Fin 3) :
    kmswWindowVertexMapInf w 0 = id := by
  funext v
  rw [kmswWindowVertexMapInf_eq_stage w 0 (4 * v + 1) v
    (by simpa only [Nat.zero_add] using vertex_allocated_at w v)]
  exact kmswWindowPatchVertexMap_zero_start w (4 * v + 1) v (vertex_allocated_at w v)

end DirectedDistances.KMSW
