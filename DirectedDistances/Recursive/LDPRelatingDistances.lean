module

public import DirectedDistances.Recursive.OneStepTransport
public import DirectedDistances.KMSW.KMSWShiftAllTimes
public import DirectedDistances.KMSW.DirectedContainHat











public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- For the first step `(0,1)`, the shifted left boundary vertices map to the
same global boundary indices. This is the left-index clause of
`eqn-ldp-relating3` in `lem:LDP-relating-X1-X` -/
theorem upShift_boundaryVertex_left (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) (k : ℤ) (hk : k ≤ -1) :
    kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h1 k)
        (boundaryVertex (fun i => w (i + 1)) h1 k) =
      boundaryVertex w h0 k := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  have h1' : BoundaryHitWitnesses u := h1
  let t := boundaryHitTime u h1' k
  have htime := (firstStepHitTimes_up w h0 h1' hw).1 k hk
  have htimeT : t + 1 = boundaryHitTime w h0 k := by
    dsimp [t]
    exact htime
  have htime' : 1 + t = boundaryHitTime w h0 k := by
    omega
  have hactive : boundaryVertex u h1' k = edgeWest u (act u t) :=
    boundaryVertex_eq_edgeWest_hit u h1' k
  have he := kmswShift_active_present w 1 t
  have hmap := kmswShift_present_edge_maps w 1 t
    (act (fun i => w (1 + i)) t) he.1 he.2
  have hedge : edgeWest u (act u t) =
      edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t) :=
    congrArg (fun q => edgeWest q (act q t)) hseq.symm
  calc
    kmswShiftVertexMapAll w 1 t (boundaryVertex u h1' k) =
        kmswShiftVertexMapAll w 1 t (edgeWest u (act u t)) :=
      congrArg (kmswShiftVertexMapAll w 1 t) hactive
    _ = kmswShiftVertexMapAll w 1 t
        (edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t)) :=
      congrArg (kmswShiftVertexMapAll w 1 t) hedge
    _ = edgeWest w (kmswShiftEdgeMapAll w 1 t
        (act (fun i => w (1 + i)) t)) := hmap.2.1.symm
    _ = edgeWest w (act w (1 + t)) := by rw [kmswShift_active_edge_map]
    _ = edgeWest w (act w (boundaryHitTime w h0 k)) := by rw [htime']
    _ = boundaryVertex w h0 k :=
      (boundaryVertex_eq_edgeWest_hit w h0 k).symm

/-- For the first step `(0,1)`, shifted right boundary vertices with index at
least `2` map to the global vertex with index one less. This is the
right-index clause of `eqn-ldp-relating3` in `lem:LDP-relating-X1-X` -/
theorem upShift_boundaryVertex_right (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) (k : ℤ) (hk : 2 ≤ k) :
    kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h1 k)
        (boundaryVertex (fun i => w (i + 1)) h1 k) =
      boundaryVertex w h0 (k - 1) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  have h1' : BoundaryHitWitnesses u := h1
  let t := boundaryHitTime u h1' k
  have htime := (firstStepHitTimes_up w h0 h1' hw).2 k (by omega)
  have htimeT : t + 1 = boundaryHitTime w h0 (k - 1) := by
    dsimp [t]
    exact htime
  have htime' : 1 + t = boundaryHitTime w h0 (k - 1) := by
    omega
  have hactive : boundaryVertex u h1' k = edgeWest u (act u t) :=
    boundaryVertex_eq_edgeWest_hit u h1' k
  have he := kmswShift_active_present w 1 t
  have hmap := kmswShift_present_edge_maps w 1 t
    (act (fun i => w (1 + i)) t) he.1 he.2
  have hedge : edgeWest u (act u t) =
      edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t) :=
    congrArg (fun q => edgeWest q (act q t)) hseq.symm
  calc
    kmswShiftVertexMapAll w 1 t (boundaryVertex u h1' k) =
        kmswShiftVertexMapAll w 1 t (edgeWest u (act u t)) :=
      congrArg (kmswShiftVertexMapAll w 1 t) hactive
    _ = kmswShiftVertexMapAll w 1 t
        (edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t)) :=
      congrArg (kmswShiftVertexMapAll w 1 t) hedge
    _ = edgeWest w (kmswShiftEdgeMapAll w 1 t
        (act (fun i => w (1 + i)) t)) := hmap.2.1.symm
    _ = edgeWest w (act w (1 + t)) := by rw [kmswShift_active_edge_map]
    _ = edgeWest w (act w (boundaryHitTime w h0 (k - 1))) := by
      rw [htime']
    _ = boundaryVertex w h0 (k - 1) :=
      (boundaryVertex_eq_edgeWest_hit w h0 (k - 1)).symm

/-- In the first `(0,1)` step, the shifted root endpoints map to global
vertices `x^0_0 = 0` and `2`, respectively. The boundary correspondence
needed for `eqn-ldp-relating3` then identifies the shifted vertex `x^1_2`
with `x^0_1` (`lem:LDP-relating-X1-X`, -/
theorem upShift_rootVertices (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (hw : w 0 = 1) :
    kmswShiftVertexMapAll w 1 0 0 = boundaryVertex w h0 0 ∧
      kmswShiftVertexMapAll w 1 0 1 = 2 := by
  have hsim := shiftedRoot_simulates_firstStage w
  have hinc := hsim.incidence 0 (by simp [kmswInit])
  rcases firstStage_up w hw with
    ⟨_, _, hactive, _, _, _, _, _, hwest, heast, _, _⟩
  have hwest' : (kmswStage w 1).west (kmswStage w 1).active = 0 := by
    rw [hactive]
    exact hwest
  have heast' : (kmswStage w 1).east (kmswStage w 1).active = 2 := by
    rw [hactive]
    exact heast
  have hrootWest : kmswShiftRootVertexNatMap w 1 0 =
      (kmswStage w 1).west (kmswShiftRootEdgeNatMap w 1 0) := by
    simpa [kmswInit] using hinc.1.symm
  have hrootEast : kmswShiftRootVertexNatMap w 1 1 =
      (kmswStage w 1).east (kmswShiftRootEdgeNatMap w 1 0) := by
    simpa [kmswInit] using hinc.2.symm
  constructor
  · change kmswShiftRootVertexNatMap w 1 0 = boundaryVertex w h0 0
    rw [hrootWest, kmswShiftRootEdgeNatMap, act, hwest']
    simp [boundaryVertex_zero]
  · change kmswShiftRootVertexNatMap w 1 1 = 2
    rw [hrootEast, kmswShiftRootEdgeNatMap, act, heast']

/-- Every finite shifted-stage path embeds in the global map with exactly the
same length. This is the path inclusion part of the deterministic comparison -/
theorem upShiftStage_path_length (w : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex (fun i => w (1 + i)) m} (p : Path a b) :
    ((kmswShiftStageToLimit w 1 m).mapPath p).length = p.length :=
  kmswShiftStageToLimit_length w 1 m p

/-- The longest-path supremum in a finite shifted stage is at most the
longest-path supremum between its image vertices in the global limit. The
convention `⊥` for unreachable pairs is preserved. This is only the embedding
inequality from `lem:LDP-relating-X1-X`
path correspondence or the full distance identity. -/
theorem upShiftStage_ldpSup_le (w : ℕ → Fin 3)
    (hbound : PresentPathLengthsBounded (w := w)) (m : ℕ)
    (a b : StagePresentVertex (fun i => w (1 + i)) m) :
    ldpSup a b ≤
      ldpSup ((kmswShiftStageToLimit w 1 m).obj a)
        ((kmswShiftStageToLimit w 1 m).obj b) := by
  let F := kmswShiftStageToLimit w 1 m
  have hsubset : pathLengths a b ⊆ pathLengths (F.obj a) (F.obj b) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨F.mapPath p, kmswShiftStageToLimit_length w 1 m p⟩
  by_cases hr : Reachable a b
  · obtain ⟨p⟩ := hr
    have hr' : Reachable (F.obj a) (F.obj b) := ⟨F.mapPath p⟩
    have hb := hbound (F.obj a) (F.obj b) hr'
    apply csSup_le_csSup
    · obtain ⟨N, hN⟩ := hb
      refine ⟨(N : WithBot ℕ), ?_⟩
      rintro _ ⟨n, hn, rfl⟩
      exact WithBot.coe_le_coe.mpr (hN hn)
    · exact ⟨p.length, ⟨p.length, ⟨p, rfl⟩, rfl⟩⟩
    · exact Set.image_mono hsubset
  · rw [ldpSup_eq_bot_of_not_reachable hr]
    exact bot_le

end DirectedDistances.Recursive
