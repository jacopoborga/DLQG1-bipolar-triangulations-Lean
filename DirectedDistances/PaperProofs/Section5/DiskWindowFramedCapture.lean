module

public import DirectedDistances.KMSW.KMSWDiskBallCapture
public import DirectedDistances.KMSW.KMSWStageBallDartsStage
public import DirectedDistances.KMSW.KMSWWindowBallCapture
public import DirectedDistances.KMSW.KMSWStageBallMap
public import DirectedDistances.KMSW.KMSWLeftWalkCut
public import DirectedDistances.PaperProofs.Section5.DiskBallIdentification
public import DirectedDistances.PlanarMap.CyclicRestriction

/-! Helper toward Proposition 5.16 (local topology ruling); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.PlanarMap

private theorem diskWindow_capture_valid {n N : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x) :
    N ≤ (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat ∧
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat + N ≤ n := by
  unfold bridgeOptionWindow at h
  split at h
  · exact ⟨‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2⟩
  · contradiction

private theorem diskWindowPrefix_admissible (n : ℕ)
    (p : (ℕ → Fin 3) × ℕ)
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) :
    KMSWLeftWalkAdmissible (p.2 + 1) n (fun i => p.1 (i.val + 1)) := by
  have hwalk (j : ℕ) (hj : j ≤ n) :
      integrateCodes
          (finiteCodeExtend (n := n + 1) (fun i => p.1 (i.val + 1))) j =
        codeWalk p.1 j := by
    rw [codeWalk_eq_integrateCodes]
    unfold integrateCodes
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    simp [finiteCodeExtend, hin]
  change (∀ j ≤ n,
      0 ≤ (((p.2 : ℤ), (0 : ℤ)) + codeWalk p.1 j).1 ∧
        0 ≤ (((p.2 : ℤ), (0 : ℤ)) + codeWalk p.1 j).2) ∧
      ((p.2 : ℤ), (0 : ℤ)) + codeWalk p.1 n = (0, 0) at hcone
  unfold KMSWLeftWalkAdmissible
  rw [show ((p.2 + 1 : ℕ) : ℤ) - 1 = (p.2 : ℤ) by omega]
  refine ⟨?_, ?_⟩
  · have hend := hcone.2
    rw [← hwalk n le_rfl] at hend
    exact hend
  · intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    have hquadrant := hcone.1 j hjn
    rw [← hwalk j hjn] at hquadrant
    exact hquadrant

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The cone and positive-mark support holds almost surely under the disk bridge
law by `ae_diskBridge_support` (`DiskBridgeDecoderLaw.lean:151–171`). -/
theorem diskWindowWalkClassAndIndex {n : ℕ} (p : (ℕ → Fin 3) × ℕ)
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2) :
    ∃ c : KMSWLeftWalkClass (p.2 + 1) n,
      c.val = (fun i => p.1 (i.val + 1)) ∧
        ∃ k : Fin ((p.2 + 1) - 1), k.val + 1 = p.2 := by
  refine ⟨⟨(fun i => p.1 (i.val + 1)),
    diskWindowPrefix_admissible n p hcone⟩, rfl, ?_⟩
  refine ⟨⟨p.2 - 1, by omega⟩, ?_⟩
  simp
  omega

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
On the disk capture and no-prefix-dip events, the disk vertex ball is the
window-ball image, and dart status, rotation, inverse rotation, and face
The disk-law support witness is `ae_diskBridge_support` in
`DiskBridgeDecoderLaw.lean:151–171`. -/
theorem diskWindowBallDartStructureCapture
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
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
  have hclass : KMSWLeftWalkClass (p.2 + 1) n :=
    ⟨(fun i => p.1 (i.val + 1)), diskWindowPrefix_admissible n p hcone⟩
  let k : Fin ((p.2 + 1) - 1) := ⟨p.2 - 1, by omega⟩
  have hmark : 1 ≤ k.val + 1 := by
    simp only [k]
    omega
  have _ : KMSWLeftWalkClass (p.2 + 1) n := hclass
  have _ : 1 ≤ k.val + 1 := hmark
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
    have hvalid := diskWindow_capture_valid h
    dsimp [s, m]
    omega
  have hvertices := diskBall_eq_image_of_eventK_noDip h hev hnd (s + m) hn'
  have hvertices' := by
    simpa [u, w, T, s, m, c, S] using hvertices
  have hcodeN : ∀ i < N, w (s + i) = u i :=
    fun i hi => hcode i (by omega)
  have hsN : s + N = T := by
    have hvalid := diskWindow_capture_valid h
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

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
For a fresh window vertex set whose image is the target ball, the window dart
map restricts to a bijection of the induced ball dart sets -/
theorem kmswWindowBallDartMap_bijective_of_fresh_image
    (w : ℕ → Fin 3) (s m r c : ℕ)
    (hS : ∀ v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (himage : (kmswStageBallVertices (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c).image
          (kmswWindowPatchVertexMap w s m) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c)) :
    Function.Bijective (fun d : KMSWStageBallDart (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c =>
      (⟨kmswWindowDartMap w s m d.1, by
        rw [kmswStageBallDarts_mem_iff]
        have hd := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp d.2
        have hstart := kmswWindowDartMap_vertex w s m d.1
        have hend := kmswWindowDartMap_vertex w s m (edgeFlip _ d.1)
        have hflip := kmswWindowDartMap_edgeFlip w s m d.1
        have hstart' : stageEndpoint (kmswStage w (s + m))
            (kmswWindowDartMap w s m d.1) =
          kmswWindowPatchVertexMap w s m
            (stageEndpoint (kmswStage (fun i => w (s + i)) m) d.1) := by
          simpa only [stageEndpoint] using hstart
        have hend' : stageEndpoint (kmswStage w (s + m))
            (kmswWindowDartMap w s m (edgeFlip _ d.1)) =
          kmswWindowPatchVertexMap w s m
            (stageEndpoint (kmswStage (fun i => w (s + i)) m)
              (edgeFlip _ d.1)) := by
          simpa only [stageEndpoint] using hend
        constructor
        · rw [← himage]
          rw [hstart']
          exact Finset.mem_image.mpr ⟨_, hd.1, rfl⟩
        · rw [← himage]
          rw [hflip, hend']
          exact Finset.mem_image.mpr ⟨_, hd.2, rfl⟩⟩ :
        KMSWStageBallDart (fun _ _ => True) (kmswStage w (s + m)) r
          (kmswWindowPatchVertexMap w s m c))) := by
  classical
  let Sball := kmswStageBallVertices (fun _ _ => True)
    (kmswStage (fun i => w (s + i)) m) r c
  have hedge := kmswWindowFreshSetEdgeMap_bijective w s m Sball hS
  constructor
  · intro d e hde
    apply Subtype.ext
    exact kmswWindowDartMap_injective w s m
      (congrArg Subtype.val hde)
  · intro g
    have hg := (kmswStageBallDarts_mem_iff _ _ _ _ _).mp g.2
    have htargetEnds :
        (kmswStage w (s + m)).west g.1.1.val ∈
            kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + m)) r
              (kmswWindowPatchVertexMap w s m c) ∧
          (kmswStage w (s + m)).east g.1.1.val ∈
            kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + m)) r
              (kmswWindowPatchVertexMap w s m c) := by
      cases hb : g.1.2 <;>
        simpa [stageEndpoint, edgeFlip, hb, and_comm] using hg
    have hgtarget : g.1.1 ∈ kmswWindowFreshSetTargetEdges w s m Sball := by
      change (kmswStage w (s + m)).west g.1.1.val ∈
          Sball.image (kmswWindowPatchVertexMap w s m) ∧
        (kmswStage w (s + m)).east g.1.1.val ∈
          Sball.image (kmswWindowPatchVertexMap w s m)
      exact ⟨by rw [himage]; exact htargetEnds.1,
        by rw [himage]; exact htargetEnds.2⟩
    let gEdge : {e : Fin (kmswStage w (s + m)).nextEdge //
        e ∈ kmswWindowFreshSetTargetEdges w s m Sball} := ⟨g.1.1, hgtarget⟩
    let e := Classical.choose (hedge.2 gEdge)
    have hmap : kmswWindowFreshSetEdgeMapOn w s m Sball e = gEdge :=
      Classical.choose_spec (hedge.2 gEdge)
    have heS := e.property
    have hsource : (e.1, g.1.2) ∈ kmswStageBallDarts (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c := by
      rw [kmswStageBallDarts_mem_iff]
      change stageEndpoint (kmswStage (fun i => w (s + i)) m)
          (e.1, g.1.2) ∈ Sball ∧
        stageEndpoint (kmswStage (fun i => w (s + i)) m)
          (edgeFlip _ (e.1, g.1.2)) ∈ Sball
      change (kmswStage (fun i => w (s + i)) m).west e.1.val ∈ Sball ∧
        (kmswStage (fun i => w (s + i)) m).east e.1.val ∈ Sball at heS
      cases hb : g.1.2
      · exact ⟨by simpa only [stageEndpoint, hb, Bool.false_eq_true,
            ite_false] using heS.1,
          by simpa only [stageEndpoint, edgeFlip_apply, hb, Bool.not_false,
            Bool.false_eq_true, ite_false, ite_true] using heS.2⟩
      · exact ⟨by simpa only [stageEndpoint, hb, ite_true] using heS.2,
          by simpa only [stageEndpoint, edgeFlip_apply, hb, Bool.not_true,
            Bool.false_eq_true, ite_false, ite_true] using heS.1⟩
    refine ⟨⟨(e.1, g.1.2), hsource⟩, ?_⟩
    apply Subtype.ext
    change kmswWindowDartMap w s m (e.1, g.1.2) = g.1
    apply Prod.ext
    · have hEdge : kmswWindowFreshSetEdgeMap w s m e.1 = g.1.1 :=
        congrArg Subtype.val hmap
      simpa only [kmswWindowDartMap, kmswWindowFreshSetEdgeMap] using hEdge
    · rfl

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
On the disk capture and no-prefix-dip events, the window dart map restricts
to a bijection between the decoded-window and disk-stage ball darts -/
theorem diskWindowBallDartsEquiv
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
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
      ∀ d, (e d).1 = kmswWindowDartMap w s m d.1 := by
  classical
  let u := windowCodeDecode N x
  let w : ℕ → Fin 3 := fun i => p.1 (i + 1)
  let T := (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat
  let s := T - N
  let m := 2 * N
  let c := activeInitial u N
  have hcode : ∀ i < m, w (s + i) = u i := by
    intro i hi
    exact (windowCodeDecode_bridge h i hi).symm
  have hstage : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hvertices := (diskWindowBallDartStructureCapture h hev hcone hpos hnd).1
  have himage : (kmswStageBallVertices (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) r c).image
        (kmswWindowPatchVertexMap w s m) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) := by
    simpa only [hstage] using hvertices.symm
  have hglob := kmswDiskSeam_hglob_of_noDip h r c K0 hev.2 hnd
  have hfresh : ∀ v ∈ kmswStageBallVertices (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    intro v hv
    have hv' : v ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) r c := by simpa only [hstage] using hv
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hv').1
    have hseam : ∀ k < m, v = (kmswStage u k).nextVertex →
        (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
        (kmswCodeStep (u k) = .left →
          (kmswStage u k).UL.dropLast.reverse ≠ [] ∨
            minL w (s + k) = L w (s + k)) := by
      intro k hk hcreate
      have hcap := hev.1.1.2.1 v hv'
      refine ⟨hcap.2 k hk hcreate, ?_⟩
      intro hleft
      by_cases hnonseam : (kmswStage u k).UL.dropLast.reverse ≠ []
      · exact Or.inl hnonseam
      · have hmem : k ∈ kmswBallLeftSeamSet u m r c := by
          unfold kmswBallLeftSeamSet
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr hk, ?_⟩
          exact ⟨⟨v, hv', hcreate⟩, hleft, not_not.mp hnonseam⟩
        exact Or.inr (hglob k hmem)
    have hpatch := kmswWindowPatchVertexMap_fresh_of_global_seams
      u m v hb (hev.1.1.2.1 v hv').1 w s hcode hseam
    rw [hstage]
    exact ⟨hb, hpatch⟩
  have hbij := kmswWindowBallDartMap_bijective_of_fresh_image
    w s m r c hfresh himage
  let e := Equiv.ofBijective _ hbij
  refine ⟨e, ?_⟩
  intro d
  rfl

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
First-return maps commute with a map that conjugates the ambient permutations
on an invariant set and carries the return subset exactly -/
theorem firstReturn_map_congr_of_invariant
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : Equiv.Perm α) (g : Equiv.Perm β) (S : Finset α) (T : Finset β)
    (U : Set α) (e : α → β)
    (hU : ∀ x, x ∈ U → f x ∈ U)
    (hcomm : ∀ x, x ∈ U → e (f x) = g (e x))
    (hmem : ∀ x, x ∈ U → (x ∈ S ↔ e x ∈ T))
    (x : S) (hxU : x.1 ∈ U) :
    e ((cyclicFirstReturn f S (finitePermutationReturn f S) x).1) =
      (cyclicFirstReturn g T (finitePermutationReturn g T)
        ⟨e x.1, (hmem x.1 hxU).mp x.2⟩).1 := by
  classical
  let hf := finitePermutationReturn f S
  let hg := finitePermutationReturn g T
  let y : T := ⟨e x.1, (hmem x.1 hxU).mp x.2⟩
  have hiterU : ∀ j, (f ^ j) x.1 ∈ U := by
    intro j
    induction j with
    | zero => simpa using hxU
    | succ j ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hU _ ih
  have hiter : ∀ j, e ((f ^ j) x.1) = (g ^ j) y.1 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply]
        rw [hcomm _ (hiterU j), ih]
  let kf := cyclicFirstReturnTime f S hf x
  let kg := cyclicFirstReturnTime g T hg y
  have htime : kf = kg := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : kg < kf := by omega
      have hspec := cyclicFirstReturnTime_spec g T hg y
      have hreturn : (f ^ kg) x.1 ∈ S := by
        apply (hmem _ (hiterU kg)).mpr
        rw [hiter kg]
        exact hspec.2.1
      exact (cyclicFirstReturnTime_spec f S hf x).2.2 kg hspec.1 hlt hreturn
    · by_contra hnot
      have hlt : kf < kg := by omega
      have hspec := cyclicFirstReturnTime_spec f S hf x
      have hreturn : (g ^ kf) y.1 ∈ T := by
        have h := (hmem _ (hiterU kf)).mp hspec.2.1
        rw [hiter kf] at h
        exact h
      exact (cyclicFirstReturnTime_spec g T hg y).2.2 kf hspec.1 hlt hreturn
  calc
    e ((cyclicFirstReturn f S hf x).1) = e ((f ^ kf) x.1) := by
      rw [(firstReturn_spec f S hf x).1]
    _ = (g ^ kf) y.1 := hiter kf
    _ = (g ^ kg) y.1 := by rw [htime]
    _ = (cyclicFirstReturn g T hg y).1 := (firstReturn_spec g T hg y).1.symm

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The restricted first-return rotations correspond under the disk-window dart -/
theorem diskWindowBallDartsEquiv_rotation
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
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
  have hstructure := diskWindowBallDartStructureCapture h hev hcone hpos hnd
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
  obtain ⟨e, hemap⟩ := diskWindowBallDartsEquiv h hev hcone hpos hnd
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

/-- Helper toward Proposition 5.16 (local topology ruling); not a paper result.
The ball dart equivalence preserves edge identity and reversal, stage presence, -/
theorem diskWindowBallDartsEquiv_edge_tags_orientation
    {n N r K0 : ℕ} {p : (ℕ → Fin 3) × ℕ}
    {x : Fin (2 * N + 1) → ℤ × ℤ}
    (h : bridgeOptionWindow n N p = some x)
    (hev : kmswWindowCaptureEventK N r K0 (windowCodeDecode N x))
    (hcone : p.1 ∈ coneEvent (p.2 : ℤ) 0 n) (hpos : 1 ≤ p.2)
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
  obtain ⟨e, he⟩ := diskWindowBallDartsEquiv h hev hcone hpos hnd
  have hstructure := diskWindowBallDartStructureCapture h hev hcone hpos hnd
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

end DirectedDistances.PaperProofs.Section5
