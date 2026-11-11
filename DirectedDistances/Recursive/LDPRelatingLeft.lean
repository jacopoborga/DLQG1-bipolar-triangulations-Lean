module

public import DirectedDistances.Recursive.LDPRelatingDistances











public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

private theorem leftStep_hitTime_negOne (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (hw : w 0 = 0) :
    boundaryHitTime w h (-1) = 1 := by
  have hL1 : L w 1 = -1 := by simp [L, hw]
  have hhit := boundaryHitTime_left_spec w h (by omega : (-1 : ℤ) ≤ -1)
  have hpos : 0 < boundaryHitTime w h (-1) := by
    by_contra hn
    have hn0 : boundaryHitTime w h (-1) = 0 := by omega
    rw [hn0] at hhit
    simp [L] at hhit
  have hle : boundaryHitTime w h (-1) ≤ 1 := by
    rw [boundaryHitTime_left_eq_find w h (by omega : (-1 : ℤ) ≤ -1)]
    exact Nat.find_min' (h.leftHit (-1) (by omega)) hL1
  omega

/-- Under a first `(-1,0)` step, a shifted left boundary vertex with index
`k ≤ -1` maps to global boundary index `k - 1`. This is the left boundary
identification used for `eqn-ldp-relating2` in `lem:LDP-relating-X1-X` -/
theorem leftShift_boundaryVertex_left (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (k : ℤ) (hk : k ≤ -1) :
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
  have htime := (firstStepHitTimes_left w h0 h1' hw).1 k hk
  have htime' : 1 + t = boundaryHitTime w h0 (k - 1) := by
    have htimeT : t + 1 = boundaryHitTime w h0 (k - 1) := by
      dsimp [t]
      exact htime
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
    _ = edgeWest w (act w (boundaryHitTime w h0 (k - 1))) := by rw [htime']
    _ = boundaryVertex w h0 (k - 1) :=
      (boundaryVertex_eq_edgeWest_hit w h0 (k - 1)).symm

/-- Under a first `(-1,0)` step, shifted right boundary vertices with index
`k ≥ 1` map to the global vertex with the same index. This is the right
boundary identification used for `eqn-ldp-relating2` in -/
theorem leftShift_boundaryVertex_right (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (k : ℤ) (hk : 1 ≤ k) :
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
  have htime := (firstStepHitTimes_left w h0 h1' hw).2 k hk
  have htime' : 1 + t = boundaryHitTime w h0 k := by
    have htimeT : t + 1 = boundaryHitTime w h0 k := by
      dsimp [t]
      exact htime
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

/-- For the `(-1,0)` first step, the shifted root vertices map to global
boundary vertices `x^0_{-1} = 2` and `x^0_1 = 1`. The initial shifted image
contains exactly these two vertices among the three vertices of global stage
one, so `x^0_0 = 0` is the omitted global stage-one vertex. The first-stage
triangle is `firstStage_left` (`lem:LDP-relating-X1-X`, -/
theorem leftShift_rootVertices_and_firstStageImage (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (hw : w 0 = 0) :
    kmswShiftVertexMapAll w 1 0 0 = boundaryVertex w h0 (-1) ∧
      kmswShiftVertexMapAll w 1 0 1 = boundaryVertex w h0 1 ∧
      (∀ v, v < (kmswStage (fun i => w (1 + i)) 0).nextVertex →
        kmswShiftVertexMapAll w 1 0 v = 2 ∨
          kmswShiftVertexMapAll w 1 0 v = 1) := by
  have hsim := shiftedRoot_simulates_firstStage w
  have hinc := hsim.incidence 0 (by simp [kmswInit])
  rcases firstStage_left w hw with
    ⟨_, _, hactive, _, _, _, _, _, hwest, heast⟩
  have hwest' : (kmswStage w 1).west (kmswStage w 1).active = 2 := by
    rw [hactive]
    exact hwest
  have heast' : (kmswStage w 1).east (kmswStage w 1).active = 1 := by
    rw [hactive]
    exact heast
  have hrootWest : kmswShiftRootVertexNatMap w 1 0 =
      (kmswStage w 1).west (kmswShiftRootEdgeNatMap w 1 0) := by
    simpa [kmswInit] using hinc.1.symm
  have hrootEast : kmswShiftRootVertexNatMap w 1 1 =
      (kmswStage w 1).east (kmswShiftRootEdgeNatMap w 1 0) := by
    simpa [kmswInit] using hinc.2.symm
  have hleftMap : kmswShiftVertexMapAll w 1 0 0 = 2 := by
    change kmswShiftRootVertexNatMap w 1 0 = 2
    rw [hrootWest, kmswShiftRootEdgeNatMap, act, hwest']
  have hrightMap : kmswShiftVertexMapAll w 1 0 1 = 1 := by
    change kmswShiftRootVertexNatMap w 1 1 = 1
    rw [hrootEast, kmswShiftRootEdgeNatMap, act, heast']
  have hleftBoundary : boundaryVertex w h0 (-1) = 2 := by
    have ht := leftStep_hitTime_negOne w h0 hw
    calc
      boundaryVertex w h0 (-1) = edgeWest w (act w (boundaryHitTime w h0 (-1))) :=
        boundaryVertex_eq_edgeWest_hit w h0 (-1)
      _ = edgeWest w (act w 1) := by rw [ht]
      _ = (kmswStage w 1).west (kmswStage w 1).active := by
        rw [act]
        exact (edge_endpoints_eq w
          (act_lt_nextEdge w (Nat.le_refl 1))).1.symm
      _ = 2 := hwest'
  constructor
  · exact hleftMap.trans hleftBoundary.symm
  constructor
  · rw [hrightMap, boundaryVertex_one]
  · intro v hv
    have hvCases : v = 0 ∨ v = 1 := by
      simp [kmswStage, kmswInit] at hv
      omega
    rcases hvCases with rfl | rfl
    · exact Or.inl hleftMap
    · exact Or.inr hrightMap

/-- The shifted finite-stage map for a first `(-1,0)` step preserves the
length of every directed path (`lem:LDP-relating-X1-X`, -/
theorem leftShiftStage_path_length (w : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex (fun i => w (1 + i)) m} (p : Path a b) :
    ((kmswShiftStageToLimit w 1 m).mapPath p).length = p.length :=
  kmswShiftStageToLimit_length w 1 m p

/-- Every longest-path length in a finite shifted stage is represented by a
path of the same length between the image vertices in the global limit. Thus
the shifted `ldpSup` is at most the global `ldpSup`; unreachable pairs retain
the convention `⊥` (`lem:LDP-relating-X1-X`, -/
theorem leftShiftStage_ldpSup_le (w : ℕ → Fin 3)
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
