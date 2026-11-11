module

public import DirectedDistances.Recursive.LDPRelatingDistances











public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- Under a first `(1,-1)` step, a shifted left boundary vertex with index
`k ≤ -2` maps to global boundary index `k + 1`. This is the left boundary
identification used in `lem:LDP-relating-X1-X` -/
theorem downShift_boundaryVertex_left (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) (k : ℤ) (hk : k ≤ -2) :
    kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h1 k)
        (boundaryVertex (fun i => w (i + 1)) h1 k) =
      boundaryVertex w h0 (k + 1) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  have h1' : BoundaryHitWitnesses u := h1
  let t := boundaryHitTime u h1' k
  have htime := (firstStepHitTimes_down w h0 h1' hw).1 k hk
  have htime' : 1 + t = boundaryHitTime w h0 (k + 1) := by
    have htimeT : t + 1 = boundaryHitTime w h0 (k + 1) := by
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
    _ = edgeWest w (act w (boundaryHitTime w h0 (k + 1))) := by
      rw [htime']
    _ = boundaryVertex w h0 (k + 1) :=
      (boundaryVertex_eq_edgeWest_hit w h0 (k + 1)).symm

/-- Under a first `(1,-1)` step, shifted right boundary vertices with index
`k ≥ 1` map to global boundary index `k + 1`. This is the right boundary
identification used in `lem:LDP-relating-X1-X` -/
theorem downShift_boundaryVertex_right (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) (k : ℤ) (hk : 1 ≤ k) :
    kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h1 k)
        (boundaryVertex (fun i => w (i + 1)) h1 k) =
      boundaryVertex w h0 (k + 1) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i
    simp [u, Nat.one_add]
  have h1' : BoundaryHitWitnesses u := h1
  let t := boundaryHitTime u h1' k
  have htime := (firstStepHitTimes_down w h0 h1' hw).2 k hk
  have htime' : 1 + t = boundaryHitTime w h0 (k + 1) := by
    have htimeT : t + 1 = boundaryHitTime w h0 (k + 1) := by
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
    _ = edgeWest w (act w (boundaryHitTime w h0 (k + 1))) := by
      rw [htime']
    _ = boundaryVertex w h0 (k + 1) :=
      (boundaryVertex_eq_edgeWest_hit w h0 (k + 1)).symm

/-- For a first `(1,-1)` step, the shifted root vertices map to global
vertices `1` and `2`. Among all three allocated vertices of the global
first stage, the initial shifted image is exactly `{1,2}`; vertex `0` is
outside that image. The active first-stage edge has endpoints `1,2` -/
theorem downShift_rootVertices_and_firstStageImage (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (hw : w 0 = 2) :
    kmswShiftVertexMapAll w 1 0 0 = boundaryVertex w h0 1 ∧
      kmswShiftVertexMapAll w 1 0 1 = 2 ∧
      (∀ v, v < (kmswStage w 1).nextVertex →
        ((∃ u, u < (kmswStage (fun i => w (1 + i)) 0).nextVertex ∧
            kmswShiftVertexMapAll w 1 0 u = v) ↔ v = 1 ∨ v = 2)) := by
  have hsim := shiftedRoot_simulates_firstStage w
  have hinc := hsim.incidence 0 (by simp [kmswInit])
  rcases firstStage_down w hw with
    ⟨hnextVertex, _, hactive, _, _, _, _, hwest, heast⟩
  have hwest' : (kmswStage w 1).west (kmswStage w 1).active = 1 := by
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
  have hleftMap : kmswShiftVertexMapAll w 1 0 0 = 1 := by
    change kmswShiftRootVertexNatMap w 1 0 = 1
    rw [hrootWest, kmswShiftRootEdgeNatMap, act, hwest']
  have hrightMap : kmswShiftVertexMapAll w 1 0 1 = 2 := by
    change kmswShiftRootVertexNatMap w 1 1 = 2
    rw [hrootEast, kmswShiftRootEdgeNatMap, act, heast']
  constructor
  · rw [hleftMap, boundaryVertex_one]
  constructor
  · exact hrightMap
  · intro v hv
    rw [hnextVertex] at hv
    constructor
    · rintro ⟨u, hu, hmap⟩
      have huCases : u = 0 ∨ u = 1 := by
        simp [kmswStage, kmswInit] at hu
        omega
      rcases huCases with rfl | rfl
      · exact Or.inl (hmap.symm.trans hleftMap)
      · exact Or.inr (hmap.symm.trans hrightMap)
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [kmswStage, kmswInit], hleftMap⟩
      · exact ⟨1, by simp [kmswStage, kmswInit], hrightMap⟩

/-- Every path in a finite shifted stage embeds in the global map with
unchanged length. This is a deterministic helper for -/
theorem downShiftStage_path_length (w : ℕ → Fin 3) (m : ℕ)
    {a b : StagePresentVertex (fun i => w (1 + i)) m} (p : Path a b) :
    ((kmswShiftStageToLimit w 1 m).mapPath p).length = p.length :=
  kmswShiftStageToLimit_length w 1 m p

/-- For every first code, the longest-path supremum in a finite shifted stage
is at most that between the global image vertices. This is the generic path
embedding inequality underlying the corresponding first-step statements in
not depend on a code assumption and does not prove the reverse correspondence.
Unreachable pairs retain the convention `⊥`. -/
theorem shiftStage_ldpSup_le (w : ℕ → Fin 3)
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
