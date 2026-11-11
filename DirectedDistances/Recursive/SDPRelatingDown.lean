module

public import DirectedDistances.Recursive.SDPRelatingUp
public import DirectedDistances.Recursive.LDPRelatingDownLift
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.UIBOTBoundaryM0

/-! # Shortest path comparison for the down code step

Deterministic shortest path identities for the `(1,-1)` case of
identity applies away from the time-zero root edge. At the root, paths split
into those avoiding that edge and those using it first; the latter contribution
is one plus the shifted SDP, with `⊤` retained for unreachable pairs. These
are one-case distance statements only; no Busemann conclusion is proved. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

private theorem downSdp_vertex_ext {w : ℕ → Fin 3}
    {a b : PresentVertex w} (h : a.id = b.id) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem downSdp_pathEdge_present (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) : EdgePresent w e := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons x y p f ih =>
      rw [pathEdgeList] at he
      rcases List.mem_append.mp he with hp | hf
      · exact ih hp
      · have h : e = f.val := List.mem_singleton.mp hf
        subst e
        exact f.property.1

private theorem downSdp_path_source_mem (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) :
    (⟨edgeWest w e⟩ : PresentVertex w) ∈ p.vertices := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons x y p f ih =>
      rw [pathEdgeList] at he
      rcases List.mem_append.mp he with hp | hf
      · exact (Path.mem_vertices_cons p f).2 (Or.inl (ih hp))
      · have h : e = f.val := List.mem_singleton.mp hf
        subst e
        have hmid : (⟨edgeWest w f.val⟩ : PresentVertex w) = x := by
          cases y
          exact congrArg PresentVertex.mk f.property.2.1
        rw [hmid]
        exact (Path.mem_vertices_cons p f).2 (Or.inl p.end_mem_vertices)

private theorem downSdp_path_source_eq_start (w : ℕ → Fin 3)
    {a b x : PresentVertex w} (p : Path a b)
    (hsource : ∀ e, EdgePresent w e → edgeEast w e ≠ x.id)
    (hx : x ∈ p.vertices) : x = a := by
  induction p with
  | nil => simpa only [Path.vertices_nil, List.mem_singleton] using hx
  | @cons a' b' p e ih =>
      rcases (Path.mem_vertices_cons p e).mp hx with hprefix | hend
      · exact ih hprefix
      · have hid : x.id = edgeEast w e.val := by
          rw [hend]
          exact e.property.2.2.symm
        exact (hsource e.val e.property.1 hid.symm).elim

private theorem downSdp_globalRoot_edge (w : ℕ → Fin 3) :
    EdgePresent w 0 ∧ edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, (initial_edge_present w 0).1, (initial_edge_present w 0).2⟩
  · exact (initial_edge_endpoints w 0).1
  · exact (initial_edge_endpoints w 0).2

private theorem downSdp_path_avoids_root_of_source_ne_zero
    (w : ℕ → Fin 3) {a b : PresentVertex w} (p : Path a b)
    (ha : a.id ≠ 0) : 0 ∉ pathEdgeList p := by
  intro hroot
  have hsourceMem := downSdp_path_source_mem w p hroot
  have hstart := downSdp_path_source_eq_start w p
    (x := (⟨0⟩ : PresentVertex w))
    (fun e he => uibot_zero_no_incoming w e he) (by
      have hw := (downSdp_globalRoot_edge w).2.1
      rw [hw] at hsourceMem
      exact hsourceMem)
  exact ha (congrArg PresentVertex.id hstart.symm)

private def downSdp_globalRootArrow (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    (⟨boundaryVertex w h 0⟩ : PresentVertex w) ⟶
      ⟨boundaryVertex w h 1⟩ := by
  refine ⟨0, (downSdp_globalRoot_edge w).1, ?_, ?_⟩
  · rw [boundaryVertex_zero]
    exact (downSdp_globalRoot_edge w).2.1
  · rw [boundaryVertex_one]
    exact (downSdp_globalRoot_edge w).2.2

/-- For allocated shifted vertices whose global source is not the root,
global and shifted shortest directed distances agree. The source condition
excludes the only edge omitted by the late-path lift (`lem:SDP-relating-X1-X`, -/
theorem downShift_sdp_image_eq (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hsource : (shiftLimitVertex w 1 a).id ≠ 0) :
    sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) = sdp a b := by
  have hle : sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) ≤ sdp a b :=
    upShift_sdp_le w a b
  by_cases hreach : Reachable (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b)
  · obtain ⟨p, hp⟩ := exists_length_eq_sdp hreach
    have havoid := downSdp_path_avoids_root_of_source_ne_zero w p hsource
    have hlate := (downShift_path_avoids_root_iff_late w p).1 havoid
    obtain ⟨q, hq⟩ := downShift_late_path_lift w ha hb p hlate rfl
    apply le_antisymm
    · exact hle
    · calc
        sdp a b ≤ q.length := sdp_le_length q
        _ = p.length := by exact_mod_cast hq
        _ = sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := hp
  · have hshift : ¬ Reachable a b := by
      intro hr
      obtain ⟨q⟩ := hr
      have htop := hle.trans (sdp_le_length q)
      rw [sdp_eq_top_iff_not_reachable.mpr hreach] at htop
      simp at htop
    rw [sdp_eq_top_iff_not_reachable.mpr hreach,
      sdp_eq_top_iff_not_reachable.mpr hshift]

/-- At the global root `x⁰₀`, path lengths split into late paths avoiding edge
zero and paths beginning with that root edge. The first term is the infimum
over the late paths (and is `⊤` if there are none); the second is one plus the
shifted distance from `x¹₀ = x⁰₁`, with `1 + ⊤ = ⊤` -/
theorem downShift_root_sdp_decompose (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (hw : w 0 = 2)
    {b : PresentVertex (fun i => w (1 + i))}
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    sdp (⟨boundaryVertex w h0 0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      min
        (⨅ p : {p : Path (⟨boundaryVertex w h0 0⟩ : PresentVertex w)
            (shiftLimitVertex w 1 b) // 0 ∉ pathEdgeList p},
          (p.val.length : ℕ∞))
        (1 + sdp (⟨0⟩ : PresentVertex (fun i => w (1 + i))) b) := by
  let root : PresentVertex w := ⟨boundaryVertex w h0 0⟩
  let target : PresentVertex w := shiftLimitVertex w 1 b
  let shiftedRoot : PresentVertex (fun i => w (1 + i)) := ⟨0⟩
  have hrootImage : shiftLimitVertex w 1 shiftedRoot =
      (⟨boundaryVertex w h0 1⟩ : PresentVertex w) := by
    have hlt : 0 < (kmswStage (fun i => w (1 + i)) 0).nextVertex := by
      simp [kmswStage, kmswInit]
    rw [shiftLimitVertex_eq w 1 0 shiftedRoot hlt]
    exact congrArg (fun n : ℕ => (⟨n⟩ : PresentVertex w))
      (downShift_rootVertices_and_firstStageImage w h0 hw).1
  have hrootAllocated : kmswVertexAllocated (fun i => w (1 + i)) shiftedRoot := by
    refine ⟨0, ?_⟩
    simp [shiftedRoot, kmswStage, kmswInit]
  have hrootSource : (shiftLimitVertex w 1 shiftedRoot).id ≠ 0 := by
    rw [hrootImage]
    simp [boundaryVertex_one]
  have hglobalEastSdp :
      sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
          (shiftLimitVertex w 1 b) = sdp shiftedRoot b := by
    have h := downShift_sdp_image_eq w hrootAllocated hb hrootSource
    rw [hrootImage] at h
    exact h
  have hlateUpper : sdp root target ≤
      (⨅ p : {p : Path root target // 0 ∉ pathEdgeList p},
        (p.val.length : ℕ∞)) := by
    apply le_iInf
    intro p
    exact sdp_le_length p.val
  have hrootUpperGlobal :
      sdp root target ≤
        1 + sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w) target := by
    by_cases hreach : Reachable
        (⟨boundaryVertex w h0 1⟩ : PresentVertex w) target
    · obtain ⟨q, hq⟩ := exists_length_eq_sdp hreach
      let rootPath : Path root (⟨boundaryVertex w h0 1⟩ : PresentVertex w) :=
        (Path.nil : Path root root).cons (downSdp_globalRootArrow w h0)
      have hrootPathLength : rootPath.length = 1 := by
        simp [rootPath, Path.length_cons]
      calc
        sdp root target ≤ (rootPath.comp q).length :=
          sdp_le_length (rootPath.comp q)
        _ = 1 + sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w) target := by
          rw [Path.length_comp, ENat.natCast_add, hrootPathLength, hq]
          simp
    · rw [sdp_eq_top_iff_not_reachable.mpr hreach]
      simp
  have hrootUpper : sdp root target ≤ 1 + sdp shiftedRoot b := by
    rw [hglobalEastSdp] at hrootUpperGlobal
    exact hrootUpperGlobal
  apply le_antisymm
  · apply le_min hlateUpper hrootUpper
  · change min
      (⨅ p : {p : Path root target // 0 ∉ pathEdgeList p},
        (p.val.length : ℕ∞))
      (1 + sdp shiftedRoot b) ≤
        (⨅ p : Path root target, (p.length : ℕ∞))
    apply le_iInf
    intro p
    have hcases := downShift_boundary_path_root_cases w h0 0 p
    rcases hcases with havoid | ⟨hj, q, hpath, hlen⟩
    · have hlateP :
          (⨅ q : {q : Path root target // 0 ∉ pathEdgeList q},
            (q.val.length : ℕ∞)) ≤ (p.length : ℕ∞) := by
        exact iInf_le
          (fun q : {q : Path root target // 0 ∉ pathEdgeList q} =>
            (q.val.length : ℕ∞))
          (⟨p, havoid⟩ : {q : Path root target // 0 ∉ pathEdgeList q})
      exact (min_le_left _ _).trans hlateP
    · have hqbound : sdp shiftedRoot b ≤ q.length := by
        calc
          sdp shiftedRoot b =
              sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w) target :=
            hglobalEastSdp.symm
          _ ≤ q.length := sdp_le_length q
      have hrootBranch :
          1 + sdp shiftedRoot b ≤ (p.length : ℕ∞) := by
        calc
          1 + sdp shiftedRoot b ≤ 1 + (q.length : ℕ∞) :=
            by simpa [add_comm] using add_le_add_left hqbound 1
          _ = (p.length : ℕ∞) := by
            rw [hlen]
            simp [Nat.cast_add, add_comm]
      exact (min_le_right _ _).trans hrootBranch

end DirectedDistances.Recursive
