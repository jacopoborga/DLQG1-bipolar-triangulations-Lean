module

public import DirectedDistances.Recursive.SDPRelatingUp
public import DirectedDistances.Recursive.LDPRelatingLeftLift
import DirectedDistances.KMSW.UIBOTBoundaryM0











public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

private noncomputable def leftStepSDPLimitFunctor (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let f : {e : ℕ // EdgePresent (fun i => w (1 + i)) e} := ⟨e.val, e.property.1⟩
    have hi := shiftLimitEdge_incidence w 1 f
    have ha : a = ⟨edgeWest (fun i => w (1 + i)) e.val⟩ := by
      cases a
      exact congrArg PresentVertex.mk e.property.2.1.symm
    have hb : b = ⟨edgeEast (fun i => w (1 + i)) e.val⟩ := by
      cases b
      exact congrArg PresentVertex.mk e.property.2.2.symm
    refine ⟨shiftLimitEdge w 1 f, shiftLimitEdge_present w 1 f, ?_, ?_⟩
    · rw [ha]
      exact hi.1
    · rw [hb]
      exact hi.2

private theorem leftStep_globalRoot_edge (w : ℕ → Fin 3) :
    EdgePresent w 0 ∧ edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 ∧ act w 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨0, (initial_edge_present w 0).1, (initial_edge_present w 0).2⟩
  · exact (initial_edge_endpoints w 0).1
  · exact (initial_edge_endpoints w 0).2
  · simp [act, kmswStage, kmswInit]

private theorem leftStep_path_endpoint_ne_root {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) : b.id ≠ 0 := by
  induction p with
  | nil => exact ha
  | @cons mid final p e ih =>
      intro hfinal
      have heast0 : edgeEast w e.val = 0 := e.property.2.2.trans hfinal
      exact (uibot_zero_no_incoming w e.val e.property.1) heast0

private theorem leftStep_path_edges_avoid_root (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) :
    ∀ e ∈ pathEdgeList p, e ≠ 0 := by
  revert ha
  induction p with
  | nil => intro ha; simp [pathEdgeList]
  | @cons mid final p edge ih =>
      intro ha
      have hmid : mid.id ≠ 0 := leftStep_path_endpoint_ne_root p ha
      intro e he
      simp only [pathEdgeList, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact ih ha e he
      · subst e
        intro hz
        have hw0 := (leftStep_globalRoot_edge w).2.1
        have hmid0 : mid.id = 0 := by
          calc
            mid.id = edgeWest w edge.val := edge.property.2.1.symm
            _ = edgeWest w 0 := by rw [hz]
            _ = 0 := hw0
        exact hmid hmid0

private theorem leftStep_path_edges_late (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) :
    ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, 1 ≤ actTime w e he := by
  intro e hemem he
  have hne := leftStep_path_edges_avoid_root w p ha e hemem
  have htime : e = act w (actTime w e he) := actTime_spec w e he
  by_contra hn
  have hzero : actTime w e he = 0 := by omega
  rw [hzero] at htime
  have hact0 := (leftStep_globalRoot_edge w).2.2.2
  rw [hact0] at htime
  exact hne htime

/-- The shift embedding sends each shifted path to a global path with the same
length, so the global SDP is at most the shifted SDP, including unreachable -/
theorem leftStep_sdp_le (w : ℕ → Fin 3)
    (a b : PresentVertex (fun i => w (1 + i))) :
    sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) ≤ sdp a b :=
  upShift_sdp_le w a b

/-- For allocated shifted vertices whose image source is not the root, the
SDP between their images equals the shifted SDP. A global shortest path lifts
with its length unchanged; if no global path exists, the shift embedding also
rules out a shifted path. This proves the first and third deterministic
identities in the `(-1,0)` case of `eqn-sdp-relating2`
middle identity involving `x^0_0`, and the Busemann claims in `thm-busemann`,
are not proved here. -/
theorem leftStep_sdp_image_eq (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hsource : (shiftLimitVertex w 1 a).id ≠ 0) :
    sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) = sdp a b := by
  by_cases hreach : Reachable (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b)
  · obtain ⟨q, hq⟩ := exists_length_eq_sdp hreach
    have hlate := leftStep_path_edges_late w q hsource
    obtain ⟨r, hrlen⟩ := leftStep_late_path_lift w ha hb q hlate rfl
    apply le_antisymm
    · exact upShift_sdp_le w a b
    · calc
        sdp a b ≤ r.length := sdp_le_length r
        _ = (q.length : ℕ∞) := by exact_mod_cast hrlen
        _ = sdp (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) := hq
  · have hshift : ¬ Reachable a b := by
      intro hab
      obtain ⟨p⟩ := hab
      exact hreach ⟨(leftStepSDPLimitFunctor w).mapPath p⟩
    rw [sdp_eq_top_iff_not_reachable.mpr hreach,
      sdp_eq_top_iff_not_reachable.mpr hshift]

/-- For the `(-1,0)` first step, the distance from `x^0_{-1}` to an image
target equals the shifted distance from `x^1_0`. This is a deterministic
boundary identity in `eqn-sdp-relating2` (`lem:SDP-relating-X1-X`,
`x^0_0` or the Busemann existence statement `thm-busemann` is made here. -/
theorem leftStep_sdp_leftBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (_h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) :
    ∀ b : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) b →
      Reachable (⟨0⟩ : PresentVertex (fun i => w (1 + i))) b →
      sdp (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
        sdp (⟨0⟩ : PresentVertex (fun i => w (1 + i))) b := by
  intro b hb hreach
  have ha : kmswVertexAllocated (fun i => w (1 + i))
      (⟨0⟩ : PresentVertex (fun i => w (1 + i))) := by
    exact ⟨0, by simp [kmswStage, kmswInit]⟩
  have hrootMap : shiftLimitVertex w 1
      (⟨0⟩ : PresentVertex (fun i => w (1 + i))) =
      (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w) := by
    rw [shiftLimitVertex_eq w 1 0 ⟨0⟩ (by simp [kmswStage, kmswInit])]
    exact congrArg PresentVertex.mk
      (leftShift_rootVertices_and_firstStageImage w h0 hw).1
  have hsource : (shiftLimitVertex w 1
      (⟨0⟩ : PresentVertex (fun i => w (1 + i)))).id ≠ 0 := by
    rw [hrootMap]
    intro hz
    change boundaryVertex w h0 (-1) = 0 at hz
    have hzero := boundaryVertex_zero w h0
    have hidx := (boundaryVertex_injective w h0) (hz.trans hzero.symm)
    omega
  rw [← hrootMap]
  exact leftStep_sdp_image_eq w ha hb hsource

/-- For the `(-1,0)` first step, the distance from `x^0_1` to an image
target equals the shifted distance from `x^1_1`. This is the third
deterministic boundary identity in `eqn-sdp-relating2`
middle identity for `x^0_0` and the Busemann claims in `thm-busemann` remain
outside this result. -/
theorem leftStep_sdp_rightBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (_h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) :
    ∀ b : PresentVertex (fun i => w (1 + i)),
      kmswVertexAllocated (fun i => w (1 + i)) b →
      Reachable (⟨1⟩ : PresentVertex (fun i => w (1 + i))) b →
      sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
        sdp (⟨1⟩ : PresentVertex (fun i => w (1 + i))) b := by
  intro b hb hreach
  have ha : kmswVertexAllocated (fun i => w (1 + i))
      (⟨1⟩ : PresentVertex (fun i => w (1 + i))) := by
    exact ⟨0, by simp [kmswStage, kmswInit]⟩
  have hrootMap : shiftLimitVertex w 1
      (⟨1⟩ : PresentVertex (fun i => w (1 + i))) =
      (⟨boundaryVertex w h0 1⟩ : PresentVertex w) := by
    rw [shiftLimitVertex_eq w 1 0 ⟨1⟩ (by simp [kmswStage, kmswInit])]
    exact congrArg PresentVertex.mk
      (leftShift_rootVertices_and_firstStageImage w h0 hw).2.1
  have hsource : (shiftLimitVertex w 1
      (⟨1⟩ : PresentVertex (fun i => w (1 + i)))).id ≠ 0 := by
    rw [hrootMap]
    change boundaryVertex w h0 1 ≠ 0
    rw [boundaryVertex_one]
    omega
  rw [← hrootMap]
  exact leftStep_sdp_image_eq w ha hb hsource

end DirectedDistances.Recursive
