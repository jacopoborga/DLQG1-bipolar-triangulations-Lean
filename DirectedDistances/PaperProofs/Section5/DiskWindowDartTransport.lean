module

public import DirectedDistances.PaperProofs.Section5.DiskWindowFramedIso

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

private theorem transport_window_valid {n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The captured endpoint and disk stages have the same induced dart structure,
without a cone condition at the sampled level. -/
theorem diskWindowDartTransport_stage_iso
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage w n) r
          (activeInitial w T) ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T),
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage w n) r (activeInitial w T) d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (T + N)) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T) d) =
        kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) ∧
      (∀ d, e ((kmswStageBallRot (fun _ _ => True) w n r
          (activeInitial w T)).symm d) =
        (kmswStageBallRot (fun _ _ => True) w (T + N) r
          (activeInitial w T)).symm (e d)) ∧
      (∀ d, (kmswStage w n).present d.1.1.val =
        (kmswStage w (T + N)).present (e d).1.1.val) ∧
      (∀ d, kmswStageBallMapMissing (fun _ _ => True) w n r
          (activeInitial w T) d ↔
        kmswStageBallMapMissing (fun _ _ => True) w (T + N) r
          (activeInitial w T) (e d)) := by
  classical
  dsimp only
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let t := T + N
  let P : KMSWStageEdgePredicate := fun _ _ => True
  let source := kmswStage w n
  let target := kmswStage w t
  let c := activeInitial w T
  have hvalid := transport_window_valid h
  have htn : T + N ≤ n := by
    dsimp only [T]
    exact hvalid.2
  obtain ⟨E, hE⟩ := diskWindowClass_stage_darts_equiv h hev hnd
  let e := E.symm
  have heId (d) : (e d).1.1.val = d.1.1.val := by
    have hd := (hE (e d)).1
    rw [Equiv.apply_symm_apply] at hd
    exact hd.symm
  have heSide (d) : (e d).1.2 = d.1.2 := by
    have hd := (hE (e d)).2
    rw [Equiv.apply_symm_apply] at hd
    exact hd.symm
  have hballs :
      kmswStageBallVertices P source r c = kmswStageBallVertices P target r c :=
    diskWindowClass_vertex_ball_stable h hev hnd
  let castD : StageDart target.nextEdge → StageDart source.nextEdge :=
    fun d => outerSucc_castDart (kmswStage_nextEdge_mono w htn) d
  have hendpoint (d : StageDart target.nextEdge) :
      stageEndpoint source (castD d) = stageEndpoint target d := by
    cases d with
    | mk edge side =>
      have hs := kmswStage_endpoints_stable w htn edge.isLt
      cases hb : side <;>
        simp only [stageEndpoint, castD, outerSucc_castDart,
          Bool.false_eq_true, ↓reduceIte, Fin.val_castLE]
      · exact hs.1
      · exact hs.2
  have hcastFlip (d : StageDart target.nextEdge) :
      castD (edgeFlip _ d) = edgeFlip _ (castD d) := by
    cases d with
    | mk edge side => cases side <;> rfl
  have hballmem (d : StageDart target.nextEdge) :
      d ∈ kmswStageBallDarts P target r c ↔
        castD d ∈ kmswStageBallDarts P source r c := by
    rw [kmswStageBallDarts_mem_iff, kmswStageBallDarts_mem_iff]
    rw [hendpoint d, ← hcastFlip d, hendpoint (edgeFlip _ d), hballs]
  let U : Set (StageDart target.nextEdge) :=
    {d | stageEndpoint target d ∈ kmswStageBallVertices P target r c}
  have hU : ∀ d, d ∈ U → stageRot w t d ∈ U := by
    intro d hd
    change stageEndpoint target d ∈ kmswStageBallVertices P target r c at hd
    change stageEndpoint target (stageRot w t d) ∈
      kmswStageBallVertices P target r c
    have hsame :=
      (stageRot_sameCycle_iff_endpoint_eq w t d (stageRot w t d)).mp
        ⟨1, rfl⟩
    exact hsame ▸ hd
  have hstageRot := diskWindowClass_stage_rotation h hev hnd
  dsimp only at hstageRot
  have hcomm : ∀ d, d ∈ U →
      castD (stageRot w t d) = stageRot w n (castD d) := by
    intro d hd
    have hd' : stageEndpoint target d ∈
        kmswStageBallVertices P target r c := by
      change stageEndpoint target d ∈ kmswStageBallVertices P target r c at hd
      exact hd
    simpa only [castD, source, target, t] using
      (hstageRot n htn d hd').symm
  have hmem : ∀ d, d ∈ U →
      (d ∈ kmswStageBallDarts P target r c ↔
        castD d ∈ kmswStageBallDarts P source r c) := by
    intro d _
    exact hballmem d
  have hrotFor (d : KMSWStageBallDart P target r c) :
      castD ((kmswStageBallRot P w t r c d).1) =
        (kmswStageBallRot P w n r c
          ⟨castD d.1, (hballmem d.1).mp d.2⟩).1 := by
    have hdU : d.1 ∈ U := by
      change stageEndpoint target d.1 ∈ kmswStageBallVertices P target r c
      exact ((kmswStageBallDarts_mem_iff P target r c d.1).mp d.2).1
    have h := firstReturn_map_congr_of_invariant
      (stageRot w t) (stageRot w n)
      (kmswStageBallDarts P target r c)
      (kmswStageBallDarts P source r c) U castD hU hcomm hmem d hdU
    simpa only [kmswStageBallRot] using h
  have hback (d : KMSWStageBallDart P source r c) :
      castD (e d).1 = d.1 := by
    apply Prod.ext
    · apply Fin.ext
      change (e d).1.1.val = d.1.1.val
      exact heId d
    · exact heSide d
  have hrotation : ∀ d, e (kmswStageBallRot P w n r c d) =
      kmswStageBallRot P w t r c (e d) := by
    intro d
    have hdU : (e d).1 ∈ U := by
      change stageEndpoint target (e d).1 ∈
        kmswStageBallVertices P target r c
      exact ((kmswStageBallDarts_mem_iff P target r c (e d).1).mp
        (e d).2).1
    have hret := hrotFor (e d)
    have hsub :
        (⟨castD (e d).1, (hballmem (e d).1).mp (e d).2⟩ :
          KMSWStageBallDart P source r c) = d := by
      apply Subtype.ext
      exact hback d
    rw [hsub] at hret
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hval := congrArg
        (fun z : StageDart source.nextEdge => z.1.val) hret
      simp only [castD, outerSucc_castDart, Fin.val_castLE] at hval
      calc
        (e (kmswStageBallRot P w n r c d)).1.1.val =
            (kmswStageBallRot P w n r c d).1.1.val := heId _
        _ = (kmswStageBallRot P w t r c (e d)).1.1.val := hval.symm
    · have hside := congrArg
        (fun z : StageDart source.nextEdge => z.2) hret
      simp only [castD, outerSucc_castDart] at hside
      calc
        (e (kmswStageBallRot P w n r c d)).1.2 =
            (kmswStageBallRot P w n r c d).1.2 := heSide _
        _ = (kmswStageBallRot P w t r c (e d)).1.2 := hside.symm
  have hinvRotation : ∀ d, e ((kmswStageBallRot P w n r c).symm d) =
      (kmswStageBallRot P w t r c).symm (e d) := by
    intro d
    have h := hrotation ((kmswStageBallRot P w n r c).symm d)
    simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      (congrArg (kmswStageBallRot P w t r c).symm h).symm
  have hflip : ∀ d, e (kmswStageBallDartFlip P source r c d) =
      kmswStageBallDartFlip P target r c (e d) := by
    intro d
    cases d with
    | mk d hd =>
      cases d with
      | mk edge side =>
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          calc
            (e (kmswStageBallDartFlip P source r c
              ⟨(edge, side), hd⟩)).1.1.val = edge.val := by
                simpa [kmswStageBallDartFlip, edgeFlip] using
                  heId (kmswStageBallDartFlip P source r c
                    ⟨(edge, side), hd⟩)
            _ = (e ⟨(edge, side), hd⟩).1.1.val := by
              exact (heId ⟨(edge, side), hd⟩).symm
        · calc
            (e (kmswStageBallDartFlip P source r c
              ⟨(edge, side), hd⟩)).1.2 = !side := by
                simpa [kmswStageBallDartFlip, edgeFlip] using
                  heSide (kmswStageBallDartFlip P source r c
                    ⟨(edge, side), hd⟩)
            _ = !(e ⟨(edge, side), hd⟩).1.2 := by
              simp [heSide ⟨(edge, side), hd⟩]
  have hpresent : ∀ d, source.present d.1.1.val =
      target.present (e d).1.1.val := by
    intro d
    have hp := diskWindowClass_stage_present h hev hnd
    dsimp only at hp
    have hstatus := hp n htn (e d).1
      ((kmswStageBallDarts_mem_iff P target r c (e d).1).mp (e d).2).1
    calc
      source.present d.1.1.val = source.present (e d).1.1.val := by
        rw [heId d]
      _ = target.present (e d).1.1.val := hstatus
  have hmissing : ∀ d,
      kmswStageBallMapMissing P w n r c d ↔
        kmswStageBallMapMissing P w t r c (e d) := by
    intro d
    change (source.present d.1.1.val = false) ↔
      (target.present (e d).1.1.val = false)
    rw [hpresent d]
  exact ⟨e, heId, heSide, hflip, hrotation, hinvRotation, hpresent, hmissing⟩


private theorem transport_structure
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let s := T - N
    let m := 2 * N
    let c := activeInitial u N
    let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
    And
        ((kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + m)) r
            (kmswWindowPatchVertexMap w s m c)) =
          (Finset.image (kmswWindowPatchVertexMap w s m) S))
        ((∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
            stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈
              kmswStageBallVertices (fun _ _ => True)
                (kmswStage (fun i => w (s + i)) m) r c →
              (kmswStage (fun i => w (s + i)) m).present d.1.val =
                (kmswStage w (s + m)).present
                  (kmswWindowDartMap w s m d).1.val) ∧
          (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
            stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈
              kmswStageBallVertices (fun _ _ => True)
                (kmswStage (fun i => w (s + i)) m) r c →
              (kmswMap w (s + m)).rot (kmswWindowDartMap w s m d) =
                kmswWindowDartMap w s m
                  ((kmswMap (fun i => w (s + i)) m).rot d) ∧
              (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m d) =
                kmswWindowDartMap w s m
                  ((kmswMap (fun i => w (s + i)) m).rot.symm d)) ∧
          (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
            stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈
              kmswStageBallVertices (fun _ _ => True)
                (kmswStage (fun i => w (s + i)) m) r c →
            stageEndpoint (kmswStage (fun i => w (s + i)) m)
                (edgeFlip _ d) ∈ kmswStageBallVertices (fun _ _ => True)
                  (kmswStage (fun i => w (s + i)) m) r c →
              (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m d) =
                kmswWindowDartMap w s m
                  ((kmswMap (fun i => w (s + i)) m).faceSucc d))) := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u m) r c
  have hcode : ∀ i < m, w (s + i) = u i := by
    intro i hi
    exact (windowCodeDecode_bridge h i hi).symm
  have hglob := kmswDiskSeam_hglob_of_noDip h r c K0 hev.2 hnd
  have hcenter : c < (kmswStage u m).nextVertex := hev.1.1.1
  have hstage : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hclosed : ∀ z,
      kmswStageDistanceLe (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c z →
        z ∈ (S : Set ℕ) := by
    intro z hz
    rw [hstage] at hz
    have hz' := (kmswStageBallVertices_mem_iff_distanceLe
      (fun _ _ => True) u m r c z hcenter).2 hz
    exact Finset.mem_coe.mpr hz'
  have hfresh : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    intro v hv
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    have hseam : ∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
        (kmswCodeStep (u k) = .left →
          (kmswStage u k).UL.dropLast.reverse ≠ [] ∨
            minL w (s + k) = L w (s + k)) := by
      intro k hk hcreate
      have hcap := hev.1.1.2.1 v hv
      refine ⟨hcap.2 k hk hcreate, ?_⟩
      intro hleft
      by_cases hnonseam : (kmswStage u k).UL.dropLast.reverse ≠ []
      · exact Or.inl hnonseam
      · have hmem : k ∈ kmswBallLeftSeamSet u m r c := by
          unfold kmswBallLeftSeamSet
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr hk, ?_⟩
          exact ⟨⟨v, hv, hcreate⟩, hleft, not_not.mp hnonseam⟩
        exact Or.inr (hglob k hmem)
    have hfresh' := kmswWindowPatchVertexMap_fresh_of_global_seams
      u m v hb (hev.1.1.2.1 v hv).1 w s hcode hseam
    rw [hstage]
    exact ⟨hb, hfresh'⟩
  have hstructure := kmswWindowBallDartStructureCapture
    (fun _ _ => True) w s m S r c hfresh hclosed
  have hn' : T + N ≤ s + m := by
    have hvalid := transport_window_valid h
    dsimp [s, m]
    omega
  have hvertices := diskBall_eq_image_of_eventK_noDip h hev hnd (s + m) hn'
  have hvertices' := by
    simpa [u, w, T, s, m, c, S] using hvertices
  have hcodeN : ∀ i < N, w (s + i) = u i :=
    fun i hi => hcode i (by omega)
  have hsN : s + N = T := by
    have hvalid := transport_window_valid h
    dsimp [s, T]
    omega
  have hstageN : kmswStage (fun i => w (s + i)) N = kmswStage u N :=
    kmswStage_congr hcodeN
  have hbound : activeInitial u N <
      (kmswStage (fun i => w (s + i)) N).nextVertex := by
    rw [CutConverse.activeInitial_eq, hstageN]
    exact (kmswStage_endpoints_lt_nextVertex u N (kmswStage u N).active
      (kmswStage_boundary_ids_lt_nextEdge u N).1).1
  have hpatch := kmswWindowPatchVertexMap_extends_le w s N (2 * N)
    (by omega) (activeInitial u N) hbound
  have hroot : kmswWindowPatchVertexMap w s (2 * N) (activeInitial u N) =
      activeInitial w T := by
    calc
      kmswWindowPatchVertexMap w s (2 * N) (activeInitial u N) =
          kmswWindowPatchVertexMap w s N (activeInitial u N) := hpatch
      _ = activeInitial w (s + N) :=
        kmswWindowPatchVertexMap_activeInitial u w s N hcodeN
      _ = activeInitial w T := by rw [hsN]
  rw [← hroot] at hvertices'
  exact ⟨hvertices', hstructure⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The window endpoint transport respects the indicated induced structure without
any cone condition at the sampled level. -/
theorem diskWindowDartTransport_endpoint_rotation
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let s := T - N
    let m := 2 * N
    let c := activeInitial u N
    ∃ e : KMSWStageBallDart (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) m) r c ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (s + m)) r
          (kmswWindowPatchVertexMap w s m c),
      (∀ d, (e d).1 = kmswWindowDartMap w s m d.1) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True)
          (fun i => w (s + i)) m r c d) =
        kmswStageBallRot (fun _ _ => True) w (s + m) r
          (kmswWindowPatchVertexMap w s m c) (e d)) := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  let source := kmswStage (fun i => w (s + i)) m
  let target := kmswStage w (s + m)
  let verts := kmswStageBallVertices (fun _ _ => True) source r c
  let darts := kmswStageBallDarts (fun _ _ => True) source r c
  let targetDarts := kmswStageBallDarts (fun _ _ => True) target r
    (kmswWindowPatchVertexMap w s m c)
  let targetVerts := kmswStageBallVertices (fun _ _ => True) target r
    (kmswWindowPatchVertexMap w s m c)
  let f := stageRot (fun i => w (s + i)) m
  let g := stageRot w (s + m)
  have hcode : ∀ i < m, w (s + i) = u i := by
    intro i hi
    exact (windowCodeDecode_bridge h i hi).symm
  have hstage : source = kmswStage u m := by
    dsimp [source]
    exact kmswStage_congr hcode
  have hstructure := transport_structure h hev hnd
  have hvertices : targetVerts = verts.image (kmswWindowPatchVertexMap w s m) := by
    dsimp [targetVerts, verts, target]
    rw [hstage]
    exact hstructure.1
  have hvertexMem : ∀ v, v < source.nextVertex →
      (v ∈ verts ↔ kmswWindowPatchVertexMap w s m v ∈ targetVerts) := by
    intro v hv
    rw [hvertices]
    constructor
    · intro hvS
      exact Finset.mem_image.mpr ⟨v, hvS, rfl⟩
    · intro hvS
      obtain ⟨z, hz, hmap⟩ := Finset.mem_image.mp hvS
      have hzBound := Finset.mem_range.mp (Finset.mem_filter.mp hz).1
      have hvz := kmswWindowPatchVertexMap_injOn w s m hv hzBound hmap.symm
      simpa [hvz] using hz
  have hball : ∀ d : StageDart source.nextEdge,
      stageEndpoint source d ∈ verts →
      (d ∈ darts ↔ kmswWindowDartMap w s m d ∈ targetDarts) := by
    intro d hd
    rw [kmswStageBallDarts_mem_iff, kmswStageBallDarts_mem_iff]
    have hstart := hvertexMem _ (stageEndpoint_lt_nextVertex
      (fun i => w (s + i)) m d)
    have hflip := hvertexMem _ (stageEndpoint_lt_nextVertex
      (fun i => w (s + i)) m (edgeFlip _ d))
    have hmapStart : stageEndpoint target (kmswWindowDartMap w s m d) =
        kmswWindowPatchVertexMap w s m (stageEndpoint source d) := by
      exact kmswWindowDartMap_vertex w s m d
    have hmapFlip : stageEndpoint target
        (kmswWindowDartMap w s m (edgeFlip _ d)) =
          kmswWindowPatchVertexMap w s m (stageEndpoint source (edgeFlip _ d)) := by
      exact kmswWindowDartMap_vertex w s m (edgeFlip _ d)
    change (stageEndpoint source d ∈ verts ∧
      stageEndpoint source (edgeFlip _ d) ∈ verts) ↔
      (stageEndpoint target (kmswWindowDartMap w s m d) ∈ targetVerts ∧
        stageEndpoint target (edgeFlip _ (kmswWindowDartMap w s m d)) ∈
          targetVerts)
    rw [kmswWindowDartMap_edgeFlip, hmapStart, hmapFlip]
    exact and_congr hstart hflip
  let U : Set (StageDart source.nextEdge) :=
    {d | stageEndpoint source d ∈ verts}
  have hU : ∀ d, d ∈ U → f d ∈ U := by
    intro d hd
    change stageEndpoint source d ∈ verts at hd
    change stageEndpoint source (f d) ∈ verts
    have hsame : f.SameCycle d (f d) := ⟨1, rfl⟩
    have hend := (stageRot_sameCycle_iff_endpoint_eq
      (fun i => w (s + i)) m d (f d)).mp hsame
    exact hend ▸ hd
  have hcomm : ∀ d, d ∈ U →
      kmswWindowDartMap w s m (f d) = g (kmswWindowDartMap w s m d) := by
    intro d hd
    change stageEndpoint source d ∈ verts at hd
    have hrot := hstructure.2.2.1 d hd
    simpa [f, g, source, target, kmswMap_rot] using hrot.1.symm
  have hmem : ∀ d, d ∈ U →
      (d ∈ darts ↔ kmswWindowDartMap w s m d ∈ targetDarts) := by
    intro d hd
    change stageEndpoint source d ∈ verts at hd
    exact hball d hd
  obtain ⟨e, hemap⟩ := diskWindowClass_endpoint_darts_equiv h hev hnd
  refine ⟨e, hemap, ?_⟩
  intro d
  let xball : darts := d
  have hstart : stageEndpoint source d.1 ∈ verts :=
    (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2 |>.1
  have hrot := firstReturn_map_congr_of_invariant f g darts targetDarts U
    (kmswWindowDartMap w s m) hU hcomm hmem d hstart
  have htarget : e d =
      ⟨kmswWindowDartMap w s m d.1,
        (hball d.1 hstart).mp d.2⟩ := by
    apply Subtype.ext
    exact hemap d
  apply Subtype.ext
  calc
    (e (kmswStageBallRot (fun _ _ => True)
      (fun i => w (s + i)) m r c d)).1 =
        kmswWindowDartMap w s m
          (kmswStageBallRot (fun _ _ => True)
            (fun i => w (s + i)) m r c d).1 := hemap _
    _ = (kmswStageBallRot (fun _ _ => True) w (s + m) r
        (kmswWindowPatchVertexMap w s m c)
        ⟨kmswWindowDartMap w s m d.1, (hball d.1 hstart).mp d.2⟩).1 := hrot
    _ = (kmswStageBallRot (fun _ _ => True) w (s + m) r
        (kmswWindowPatchVertexMap w s m c) (e d)).1 := by rw [htarget]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The window endpoint transport respects the indicated induced structure without
any cone condition at the sampled level. -/
theorem diskWindowDartTransport_endpoint_tags
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
    let s := T - N
    let m := 2 * N
    let c := activeInitial u N
    ∃ e : KMSWStageBallDart (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) m) r c ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (s + m)) r
          (kmswWindowPatchVertexMap w s m c),
      (∀ d, (e d).1 = kmswWindowDartMap w s m d.1) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) m) r c d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (s + m)) r
          (kmswWindowPatchVertexMap w s m c) (e d)) ∧
      (∀ d, (kmswStage (fun i => w (s + i)) m).present d.1.1.val =
        (kmswStage w (s + m)).present (e d).1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  obtain ⟨e, he⟩ := diskWindowClass_endpoint_darts_equiv h hev hnd
  have hstructure := transport_structure h hev hnd
  refine ⟨e, he, ?_, ?_, ?_⟩
  · intro d
    apply Subtype.ext
    calc
      (e (kmswStageBallDartFlip (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c d)).1 =
          kmswWindowDartMap w s m
            (edgeFlip _ d.1) := he _
      _ = edgeFlip _ (kmswWindowDartMap w s m d.1) :=
        (kmswWindowDartMap_edgeFlip w s m d.1).symm
      _ = edgeFlip _ (e d).1 := by rw [he d]
  · intro d
    have hball := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2
    have hp := hstructure.2.1 d.1 hball.1
    rw [he d]
    simpa [u, w, T, s, m, c] using hp
  · intro d
    rw [he d]
    rfl


private theorem transport_directed_heq {s t : State} (hs : s = t)
    (M : DirectedMapWithMissing (StageDart s.nextEdge))
    (T : DirectedMapWithMissing (StageDart t.nextEdge))
    (I : DirectedMapWithMissingIso M T)
    (hI : ∀ d, (I.toEquiv d).1.val = d.1.val ∧ (I.toEquiv d).2 = d.2)
    (ho : HEq M.outer T.outer) : HEq M T := by
  cases hs
  have hi : I.toEquiv = Equiv.refl _ := by
    apply Equiv.ext
    intro d
    apply Prod.ext
    · exact Fin.ext (hI d).1
    · exact (hI d).2
  have hr : M.rot = T.rot := by
    apply Equiv.ext
    intro d
    simpa only [hi, Equiv.refl_apply] using I.rot_comm d
  have he : M.edgeInv = T.edgeInv := by
    apply Equiv.ext
    intro d
    simpa only [hi, Equiv.refl_apply] using I.edgeInv_comm d
  have hm : M.missing = T.missing := by
    funext d
    exact propext (by simpa only [hi, Equiv.refl_apply] using (I.missing_iff d).symm)
  have ht : M.tail = T.tail := by
    funext d
    exact propext (by simpa only [hi, Equiv.refl_apply] using (I.tail_iff d).symm)
  have ho' : M.outer = T.outer := eq_of_heq ho
  have hcomb (A B : CombinatorialMap (StageDart s.nextEdge))
      (he : A.edgeInv = B.edgeInv) (hr : A.rot = B.rot) : A = B := by
    cases A
    cases B
    cases he
    cases hr
    rfl
  have hc := hcomb _ _ he hr
  cases M
  cases T
  cases hc
  cases hm
  cases ht
  cases ho'
  rfl

private theorem transport_stage_data_eq (u v : ℕ → Fin 3) (m : ℕ)
    (h : ∀ i < m, u i = v i) :
    (⟨kmswStage u m, kmswStageDirectedMap u m⟩ :
      Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge)) =
        ⟨kmswStage v m, kmswStageDirectedMap v m⟩ := by
  have hs := kmswStage_congr h
  apply Sigma.ext hs
  apply transport_directed_heq hs _ _ (kmswStageDirectedMapIsoOfPrefix u v m h)
  · exact kmswStageDirectedMapIsoOfPrefix_val u v m h
  · change HEq (stageULHeadDart u m) (stageULHeadDart v m)
    have hhead {s t : State} (h : s = t) (hn : s.UL ≠ []) (hn' : t.UL ≠ [])
        (hb : s.UL.head hn < s.nextEdge) (hb' : t.UL.head hn' < t.nextEdge) :
        HEq ((⟨s.UL.head hn, hb⟩, false) : StageDart s.nextEdge)
          ((⟨t.UL.head hn', hb'⟩, false) : StageDart t.nextEdge) := by
      cases h
      rfl
    exact hhead hs _ _ _ _

private theorem transport_ball_data_eq {s t : State}
    (M : DirectedMapWithMissing (StageDart s.nextEdge))
    (Q : DirectedMapWithMissing (StageDart t.nextEdge))
    (h : (⟨s, M⟩ : Σ s : State, DirectedMapWithMissing (StageDart s.nextEdge)) =
      ⟨t, Q⟩) (r c : ℕ) :
    ∃ e : KMSWStageBallDart (fun _ _ => True) s r c ≃
        KMSWStageBallDart (fun _ _ => True) t r c,
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (cyclicFirstReturn M.rot _ (finitePermutationReturn M.rot _) d) =
        cyclicFirstReturn Q.rot _ (finitePermutationReturn Q.rot _) (e d)) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True) s r c d) =
        kmswStageBallDartFlip (fun _ _ => True) t r c (e d)) ∧
      (∀ d, Q.missing (e d).1 ↔ M.missing d.1) ∧
      (∀ d, Q.tail (e d).1 ↔ M.tail d.1) := by
  have hs : s = t := congrArg Sigma.fst h
  cases hs
  have hM : M = Q := eq_of_heq (Sigma.mk.inj h).2
  cases hM
  exact ⟨Equiv.refl _, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem transport_prefix_ball (u v : ℕ → Fin 3) (m r c : ℕ)
    (h : ∀ i < m, u i = v i) :
    ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage u m) r c ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage v m) r c,
      (∀ d, (e d).1.1.val = d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True) u m r c d) =
        kmswStageBallRot (fun _ _ => True) v m r c (e d)) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True) (kmswStage u m) r c d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage v m) r c (e d)) ∧
      (∀ d, (kmswStageDirectedMap v m).missing (e d).1 ↔
        (kmswStageDirectedMap u m).missing d.1) ∧
      (∀ d, (kmswStageDirectedMap v m).tail (e d).1 ↔
        (kmswStageDirectedMap u m).tail d.1) := by
  exact transport_ball_data_eq _ _ (transport_stage_data_eq u v m h) r c

private theorem transport_record {ell n N : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (c : KMSWLeftWalkClass (ell + 1) n)
    (hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1))
    (k : Fin ell) (hk : k.val + 1 = p.2)
    (h : bridgeOptionWindow n N p = some x) :
    ∀ j < N, L (windowCodeDecode N x) N < L (windowCodeDecode N x) j := by
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let v := finiteCodeExtend (n := n + 1) c.val
  let u := windowCodeDecode N x
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  have hT := kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c
    hc k hk
  have hvalid : N ≤ T ∧ T + N ≤ n := by
    unfold bridgeOptionWindow at h
    split at h
    · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
    · contradiction
  have hsN : s + N = T := by dsimp [s]; omega
  have hcode (i : ℕ) (hi : i < 2 * N) : v (s + i) = u i := by
    have hin : s + i < n := by dsimp [s]; omega
    change (if ht : s + i < n + 1 - 1 then c.val ⟨s + i, ht⟩ else 0) = _
    rw [dite_eq_left (by omega : s + i < n + 1 - 1)]
    rw [hc ⟨s + i, hin⟩]
    exact (windowCodeDecode_bridge h i hi).symm
  have hshift (j : ℕ) (hj : j ≤ 2 * N) : L v (s + j) = L v s + L u j := by
    induction j with
    | zero => simp only [L, Finset.range_zero, Finset.sum_empty, add_zero]
    | succ j ih =>
      have hg : L v (s + j + 1) = L v (s + j) +
          (lazyTwoDimensionalStep (v (s + j))).1 := Finset.sum_range_succ _ _
      have hu : L u (j + 1) = L u j +
          (lazyTwoDimensionalStep (u j)).1 := Finset.sum_range_succ _ _
      rw [Nat.add_succ, hg, hu, ih (by omega), hcode j (by omega), add_assoc]
  have hs := kmswDiskFirstHit_spec c kc
  have hrecord : ∀ j < T, L v T < L v j := by
    change kmswDiskFirstHit c kc = T at hT
    rw [← hT]
    intro j hj
    rw [hs.2.2.2.1]
    exact hs.2.2.2.2.1 j hj
  intro j hj
  have hlt := hrecord (s + j) (by omega)
  rw [← hsN, hshift N (by omega), hshift j (by omega)] at hlt
  exact (add_lt_add_iff_left (L v s)).mp hlt

private theorem transport_patch_prefix (u v : ℕ → Fin 3) (s m : ℕ)
    (h : ∀ i < s + m, u i = v i) :
    kmswWindowPatchData u s m = kmswWindowPatchData v s m := by
  induction m with
  | zero =>
    have hs : kmswStage u s = kmswStage v s :=
      kmswStage_congr (by simpa only [Nat.add_zero] using h)
    simp only [kmswWindowPatchData, hs]
  | succ m ih =>
    have hs : kmswStage u (s + m) = kmswStage v (s + m) :=
      kmswStage_congr (fun i hi => h i (by omega))
    have hl : kmswStage (fun i => u (s + i)) m =
        kmswStage (fun i => v (s + i)) m :=
      kmswStage_congr (fun i hi => h (s + i) (by omega))
    simp only [kmswWindowPatchData, hs, hl, h (s + m) (by omega),
      ih (fun i hi => h i (by omega))]

private theorem transport_endpoint_iso {n N r K0 : ℕ}
    {p : (ℕ → Fin 3) × ℕ} {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hnd : ¬ DiskDip N K0 p) :
    let u := windowCodeDecode N x
    let w := fun i => p.1 (i + 1)
    let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
    let c := activeInitial u N
    ∃ e : KMSWStageBallDart (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) (2 * N)) r c ≃
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (s + 2 * N)) r
          (kmswWindowPatchVertexMap w s (2 * N) c),
      (∀ d, (e d).1.1.val = (kmswWindowPatchData w s (2 * N)).φ d.1.1.val) ∧
      (∀ d, (e d).1.2 = d.1.2) ∧
      (∀ d, e (kmswStageBallRot (fun _ _ => True)
          (fun i => w (s + i)) (2 * N) r c d) =
        kmswStageBallRot (fun _ _ => True) w (s + 2 * N) r
          (kmswWindowPatchVertexMap w s (2 * N) c) (e d)) ∧
      (∀ d, e (kmswStageBallDartFlip (fun _ _ => True)
          (kmswStage (fun i => w (s + i)) (2 * N)) r c d) =
        kmswStageBallDartFlip (fun _ _ => True) (kmswStage w (s + 2 * N)) r
          (kmswWindowPatchVertexMap w s (2 * N) c) (e d)) ∧
      (∀ d, (kmswStageDirectedMap w (s + 2 * N)).missing (e d).1 ↔
        (kmswStageDirectedMap (fun i => w (s + i)) (2 * N)).missing d.1) ∧
      (∀ d, (kmswStageDirectedMap w (s + 2 * N)).tail (e d).1 ↔
        (kmswStageDirectedMap (fun i => w (s + i)) (2 * N)).tail d.1) := by
  classical
  dsimp only
  let w := fun i => p.1 (i + 1)
  let s := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat - N
  obtain ⟨e, he, hr⟩ := diskWindowDartTransport_endpoint_rotation h hev hnd
  have hstructure := transport_structure h hev hnd
  have hside (d) : (e d).1.2 = d.1.2 := by rw [he d]; rfl
  have hpresent (d) : (kmswStage w (s + 2 * N)).present (e d).1.1.val =
      (kmswStage (fun i => w (s + i)) (2 * N)).present d.1.1.val := by
    have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2
    have hp := hstructure.2.1 d.1 hd.1
    rw [he d]
    exact hp.symm
  refine ⟨e, ?_, hside, hr, ?_, ?_, ?_⟩
  · intro d
    rw [he d]
    rfl
  · intro d
    apply Subtype.ext
    calc
      (e (kmswStageBallDartFlip _ _ _ _ d)).1 =
          kmswWindowDartMap w s (2 * N) (edgeFlip _ d.1) := he _
      _ = edgeFlip _ (kmswWindowDartMap w s (2 * N) d.1) :=
        (kmswWindowDartMap_edgeFlip w s (2 * N) d.1).symm
      _ = edgeFlip _ (e d).1 := by rw [he d]
  · intro d
    change (_ = false) ↔ (_ = false)
    rw [hpresent d]
  · intro d
    change (_ = true ∧ _ = false) ↔ (_ = true ∧ _ = false)
    rw [hpresent d, hside d]

private theorem transport_inverse_comm {A B : Type} (e : A ≃ B)
    (f : Equiv.Perm A) (g : Equiv.Perm B)
    (h : ∀ x, e (f x) = g (e x)) (y : B) :
    e.symm (g y) = f (e.symm y) := by
  apply e.injective
  rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The captured window and finite disk have equivalent induced darts preserving
patch edge identities, sides, rotation, reversal, missing status and orientation. -/
theorem diskWindowFramedDartTransport_holds : DiskWindowFramedDartTransport := by
  intro n ell N K0 r hr p c hc k hk x h hev hnd d hde hdb hm
  dsimp only
  let u := windowCodeDecode N x
  let v := finiteCodeExtend (n := n + 1) c.val
  let w := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let a := activeInitial u N
  let b := activeInitial w T
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  have hvalid : N ≤ T ∧ T + N ≤ n := transport_window_valid h
  have hsm : s + m = T + N := by dsimp only [s, m]; omega
  have hsN : s + N = T := by dsimp only [s]; omega
  have hprefix (i : ℕ) (hi : i < n) : v i = w i := by
    change (if ht : i < n + 1 - 1 then c.val ⟨i, ht⟩ else 0) = _
    rw [dite_eq_left (by omega : i < n + 1 - 1)]
    exact hc ⟨i, hi⟩
  have hcode (i : ℕ) (hi : i < m) : w (s + i) = u i :=
    (windowCodeDecode_bridge h i hi).symm
  have hT : kmswDiskFirstHit c kc = T :=
    kmswDiskFirstHit_eq_codeFstFirstHit_toNat ell n p c hc k hk
  have hrec := transport_record c hc k hk h
  have hCcenter : stageEndpoint (kmswStage u m) (edgeFlip _ d) = a := by
    obtain ⟨d', he', hb', _, _, hcenter⟩ := framedRootData_of_record u N m
      (framedCapture_window_pos hev) (by dsimp only [m]; omega) hrec
    have hd : d = d' := by
      apply Prod.ext
      · exact Fin.ext (hde.trans he'.symm)
      · exact hdb.trans hb'.symm
    rw [hd]
    exact hcenter
  have hBcenter : stageEndpoint (kmswStage v n)
      (edgeFlip _ (kmswDiskRootDart c kc)) = b := by
    change (kmswStage v n).west (kmswLLCreatedEdge v (kmswDiskFirstHit c kc)) = b
    rw [(kmswDiskRootEdge_endpoints c kc).1, hT]
    exact activeInitial_congr (fun i hi => hprefix i (by omega))
  have hroot : kmswWindowPatchVertexMap w s m a = b := by
    have hstageN : kmswStage (fun i => w (s + i)) N = kmswStage u N :=
      kmswStage_congr (fun i hi => hcode i (by dsimp only [m]; omega))
    have hbound : a < (kmswStage (fun i => w (s + i)) N).nextVertex := by
      rw [hstageN]
      change activeInitial u N < _
      rw [CutConverse.activeInitial_eq]
      exact (kmswStage_endpoints_lt_nextVertex u N (kmswStage u N).active
        (kmswStage_boundary_ids_lt_nextEdge u N).1).1
    calc
      kmswWindowPatchVertexMap w s m a = kmswWindowPatchVertexMap w s N a :=
        kmswWindowPatchVertexMap_extends_le w s N m (by dsimp only [m]; omega) a hbound
      _ = activeInitial w (s + N) := kmswWindowPatchVertexMap_activeInitial u w s N
        (fun i hi => hcode i (by dsimp only [m]; omega))
      _ = b := by rw [hsN]
  change ∃ e : KMSWStageBallDart (fun _ _ => True) (kmswStage u m) r
        (stageEndpoint (kmswStage u m) (edgeFlip _ d)) ≃
      KMSWStageBallDart (fun _ _ => True) (kmswStage v n) r
        (stageEndpoint (kmswStage v n) (edgeFlip _ (kmswDiskRootDart c kc))),
    (∀ z, (e z).1.1.val = (kmswWindowPatchData v s m).φ z.1.1.val) ∧
    (∀ z, (e z).1.2 = z.1.2) ∧
    (∀ z, e (kmswStageBallRot (fun _ _ => True) u m r _ z) =
      kmswStageBallRot (fun _ _ => True) v n r _ (e z)) ∧
    (∀ z, e (kmswStageBallDartFlip (fun _ _ => True) (kmswStage u m) r _ z) =
      kmswStageBallDartFlip (fun _ _ => True) (kmswStage v n) r _ (e z)) ∧
    (∀ z, (kmswStageDirectedMap v n).missing (e z).1 ↔
      (kmswStageDirectedMap u m).missing z.1) ∧
    (∀ z, (kmswStageDirectedMap v n).tail (e z).1 ↔
      (kmswStageDirectedMap u m).tail z.1)
  rw [hCcenter, hBcenter]
  obtain ⟨e0, h0id, h0side, h0rot, h0flip, h0missing, h0tail⟩ :=
    transport_prefix_ball u (fun i => w (s + i)) m r a (fun i hi => (hcode i hi).symm)
  have he1 := transport_endpoint_iso h hev hnd
  dsimp only at he1
  rw [hsm, hroot] at he1
  obtain ⟨e1, h1id, h1side, h1rot, h1flip, h1missing, h1tail⟩ := he1
  obtain ⟨e2, h2id, h2side, h2flip, h2rot, _, h2present, h2missing⟩ :=
    diskWindowDartTransport_stage_iso h hev hnd
  obtain ⟨e3, h3id, h3side, h3rot, h3flip, h3missing, h3tail⟩ :=
    transport_prefix_ball v w n r b hprefix
  have h2id' (z) : (e2.symm z).1.1.val = z.1.1.val := by
    have hz := h2id (e2.symm z)
    rw [Equiv.apply_symm_apply] at hz
    exact hz.symm
  have h2side' (z) : (e2.symm z).1.2 = z.1.2 := by
    have hz := h2side (e2.symm z)
    rw [Equiv.apply_symm_apply] at hz
    exact hz.symm
  have h3id' (z) : (e3.symm z).1.1.val = z.1.1.val := by
    have hz := h3id (e3.symm z)
    rw [Equiv.apply_symm_apply] at hz
    exact hz.symm
  have h3side' (z) : (e3.symm z).1.2 = z.1.2 := by
    have hz := h3side (e3.symm z)
    rw [Equiv.apply_symm_apply] at hz
    exact hz.symm
  have h2tail (z) : (kmswStageDirectedMap w (T + N)).tail (e2 z).1 ↔
      (kmswStageDirectedMap w n).tail z.1 := by
    change (_ = true ∧ _ = false) ↔ (_ = true ∧ _ = false)
    rw [← h2present z, h2side z]
  let e := e0.trans (e1.trans (e2.symm.trans e3.symm))
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change (e3.symm (e2.symm (e1 (e0 z)))).1.1.val = _
    rw [h3id', h2id', h1id, h0id]
    have hp := transport_patch_prefix v w s m
      (fun i hi => hprefix i (by omega))
    rw [hp]
  · intro z
    change (e3.symm (e2.symm (e1 (e0 z)))).1.2 = _
    rw [h3side', h2side', h1side, h0side]
  · intro z
    dsimp only [e, Equiv.trans_apply]
    rw [h0rot, h1rot, transport_inverse_comm e2 _ _ h2rot,
      transport_inverse_comm e3 _ _ h3rot]
  · intro z
    dsimp only [e, Equiv.trans_apply]
    rw [h0flip, h1flip, transport_inverse_comm e2 _ _ h2flip,
      transport_inverse_comm e3 _ _ h3flip]
  · intro z
    dsimp only [e, Equiv.trans_apply]
    have h3 := h3missing (e3.symm (e2.symm (e1 (e0 z))))
    rw [Equiv.apply_symm_apply] at h3
    have h2 := h2missing (e2.symm (e1 (e0 z)))
    rw [Equiv.apply_symm_apply] at h2
    exact h3.symm.trans (h2.trans ((h1missing _).trans (h0missing _)))
  · intro z
    dsimp only [e, Equiv.trans_apply]
    have h3 := h3tail (e3.symm (e2.symm (e1 (e0 z))))
    rw [Equiv.apply_symm_apply] at h3
    have h2 := h2tail (e2.symm (e1 (e0 z)))
    rw [Equiv.apply_symm_apply] at h2
    exact h3.symm.trans (h2.symm.trans ((h1tail _).trans (h0tail _)))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The exact assembly comparison, with no residual geometric premise. -/
theorem diskWindowDartTransport_classComparison : DiskWindowClassComparison :=
  diskWindowClassComparison_of_framedDartTransport diskWindowFramedDartTransport_holds

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The exact almost-everywhere equality field of the assembly comparison. -/
theorem diskWindowDartTransport_class_eq_on_capture
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (N K0 r : ℕ) (hr : 0 < r) :
    ∀ᵐ p ∂bridgeLevelLaw n ell, ∀ x,
      bridgeOptionWindow n N p = some x →
      kmswWindowCaptureEventK N r K0 (windowCodeDecode N x) →
      ¬ DiskDip N K0 p →
      diskBSBallClass n ell hell r hr (diskBridgeDecoder ell n hell hle hmod p) =
        uibhbotDecodedWindowBallClass N r x :=
  diskWindowDartTransport_classComparison.class_eq_on_capture
    n ell hell hle hmod N K0 r hr

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The unconditional helper with exactly the convergence conclusion of the assembly
theorem, on its admissible S3 sequence domain and at every positive radius. -/
theorem diskWindowDartTransport_limit
    (A : ℝ) (hA : 1 < A) (ell : ℕ → ℕ)
    (hadm : ∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
      ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q)
    (hlo : ∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ))
    (hhi : ∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    letI : TopologicalSpace FramedBallClass := ⊥
    letI : OpensMeasurableSpace FramedBallClass := ⟨le_top⟩
    ∀ r : ℕ, ∀ hr : 0 < r,
      Tendsto (fun k => diskBSBallLaw (k + 1) (ell k)
        (hadm k).1 (hadm k).2.1 (hadm k).2.2 r hr)
        atTop (𝓝 (uibhbotBSBallLaw r hr)) := by
  exact prop516_of_diskWindowClassComparison diskWindowDartTransport_classComparison
    A hA ell hadm hlo hhi

end DirectedDistances.PaperProofs.Section5
