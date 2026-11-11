module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableCloseSdp2

/- Measurable finite-ball SDP candidate events and intrinsic reflection.
Unreachable shortest distances remain infinity throughout the comparisons.
A measurable, conull, mirror-closed sub-event replaces the larger intrinsic data event. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW DirectedMapWithMissing
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite directed dart walks used only for the finite-distance comparison. -/
private def closeSdp3Walk {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) : List D → MapVertex M → MapVertex M → Prop
  | [], s, t => s = t
  | d :: ds, s, t => ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      closeSdp3Walk M ds (dartHeadVertex M d) t

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Prepending outside the existing vertex list preserves simplicity. -/
private def closeSdp3Prepend
    (M : DirectedMapWithMissing D) {s y t : MapVertex M} {n : ℕ}
    (d : D) (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = s) (hhy : dartHeadVertex M d = y)
    (P : SimpleDirectedDartPath M y t n) (hs : s ∉ P.vertices) :
    SimpleDirectedDartPath M s t (n + 1) := by
  refine {
    darts := d :: P.darts
    vertices := s :: P.vertices
    darts_length := by simp [P.darts_length]
    vertices_length := by simp [P.vertices_length]
    vertices_nodup := by simp [List.nodup_cons, hs, P.vertices_nodup]
    start_vertex := by simp
    end_vertex := by simpa [List.get_eq_getElem] using P.end_vertex
    edge_step := by
      intro i
      have hi : i.val ≤ n := by
        have h := i.isLt
        simp only [List.length_cons, P.darts_length] at h
        omega
      by_cases hi0 : i.val = 0
      · have hifin : i = ⟨0, by simp [List.length_cons, P.darts_length]⟩ := Fin.ext hi0
        subst i
        have hstart : P.vertices.get ⟨0, by simp [P.vertices_length]⟩ = y := P.start_vertex
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [List.get_eq_getElem] using hmiss
        · simpa [List.get_eq_getElem] using htail
        · simpa [List.get_eq_getElem] using hty.symm
        · simpa [List.get_eq_getElem] using hstart.trans hhy.symm
      · have hpos : 0 < i.val := by omega
        have hdlen := P.darts_length
        have hvlen := P.vertices_length
        let j : Fin P.darts.length := ⟨i.val - 1, by omega⟩
        let jv : Fin P.vertices.length := ⟨i.val - 1, by omega⟩
        let jv' : Fin P.vertices.length := ⟨i.val, by omega⟩
        have hidx : i.val = j.val + 1 := by dsimp [j]; omega
        have hsP := P.edge_step j
        have hgetD : (d :: P.darts).get i = P.darts.get j := by
          simp only [List.get_eq_getElem]
          simp [hidx]
        have hgetV : (s :: P.vertices).get ⟨i.val, by
            simp [List.length_cons, P.vertices_length]; omega⟩ =
            P.vertices.get jv := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv]
        have hgetV' : (s :: P.vertices).get ⟨i.val + 1, by
            simp [List.length_cons, P.vertices_length]; omega⟩ =
            P.vertices.get jv' := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv']
        rw [hgetD, hgetV, hgetV']
        simpa [jv, jv', hidx] using hsP
  }


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite walk contains a simple directed path of no greater length. -/
private theorem closeSdp3Walk_simple (M : DirectedMapWithMissing D)
    (ds : List D) (s t : MapVertex M) (hw : closeSdp3Walk M ds s t) :
    ∃ n : ℕ, n ≤ ds.length ∧ Nonempty (SimpleDirectedDartPath M s t n) := by
  classical
  induction ds generalizing s with
  | nil =>
    have he : s = t := hw
    subst t
    exact ⟨0, le_rfl, ⟨{
      darts := []
      vertices := [s]
      darts_length := rfl
      vertices_length := rfl
      vertices_nodup := List.nodup_singleton s
      start_vertex := rfl
      end_vertex := rfl
      edge_step := fun i => Fin.elim0 i }⟩⟩
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := hw
    obtain ⟨n, hn, ⟨P⟩⟩ := ih _ hw
    by_cases hmem : s ∈ P.vertices
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
      let j : Fin (n + 1) := ⟨i.val, by
        have h := i.isLt
        have hl := P.vertices_length
        omega⟩
      have he : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = s := hi
      have Q := P.suffix j
      rw [he] at Q
      exact ⟨n - j.val, by simp only [List.length_cons]; omega, ⟨Q⟩⟩
    · exact ⟨n + 1, by simp only [List.length_cons]; omega,
        ⟨closeSdp3Prepend M d hm ht hs rfl P hmem⟩⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A simple directed path gives the corresponding finite directed walk. -/
private theorem closeSdp3Simple_walk (M : DirectedMapWithMissing D)
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    ∃ ds : List D, closeSdp3Walk M ds s t ∧ ds.length = n := by
  induction n generalizing s t with
  | zero => exact ⟨[], P.start_vertex.symm.trans P.end_vertex, rfl⟩
  | succ n ih =>
    let i : Fin P.darts.length := ⟨0, by rw [P.darts_length]; omega⟩
    let j : Fin (n + 1 + 1) := ⟨1, by omega⟩
    have hs := P.edge_step i
    obtain ⟨ds, hw, hl⟩ := ih (P.suffix j)
    refine ⟨P.darts.get i :: ds, ⟨hs.1, hs.2.1, ?_, ?_⟩, by simp [hl]⟩
    · exact hs.2.2.1.symm.trans P.start_vertex
    · rw [← hs.2.2.2]
      exact hw

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite simple SDP is the infimum over all finite directed walks. -/
private theorem closeSdp3Finite_inf (M : DirectedMapWithMissing D)
    (s t : MapVertex M) :
    (show ℕ∞ from simpleDirectedPathSDPLength M s t) =
      ⨅ ds : List D, ⨅ (_ : closeSdp3Walk M ds s t), (ds.length : ℕ∞) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro ds
    apply le_iInf
    intro hw
    obtain ⟨n, hn, ⟨P⟩⟩ := closeSdp3Walk_simple M ds s t hw
    exact (Finset.min_le ((mem_simpleDirectedPathLengthSet M s t n).2
      ⟨P, trivial⟩)).trans (ENat.natCast_le_natCast.mpr hn)
  · unfold simpleDirectedPathSDPLength
    apply Finset.le_min
    intro n hn
    obtain ⟨P, _⟩ := (mem_simpleDirectedPathLengthSet M s t n).1 hn
    obtain ⟨ds, hw, hl⟩ := closeSdp3Simple_walk M P
    exact iInf_le_of_le ds (iInf_le_of_le hw (by rw [hl]; exact le_rfl))


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite set of intrinsic vertices is captured by one geometric radius. -/
private theorem closeSdp3_vertexFinset_captured (M : RootedLocallyFiniteMap)
    (T : Finset (RootedLocallyFiniteVertex M.D M.rot)) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ t ∈ T, rootedLocallyFiniteWithinRadius M R t := by
  classical
  obtain ⟨R, hR, hd⟩ := incrementDartList_captured M r₀ (T.toList.map Quotient.out)
  refine ⟨R, hR, fun t ht => ?_⟩
  have hmem : Quotient.out t ∈ T.toList.map Quotient.out :=
    List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩
  have hr := ((mem_rootedLocallyFiniteBallDarts M R _).mp (hd _ hmem)).1
  have he : rootedLocallyFiniteVertexClassOf M (Quotient.out t) = t :=
    Quotient.out_eq' t
  rw [he] at hr
  exact (mem_rootedLocallyFiniteRadiusVertices M R t).mp hr

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The difference is formed only when both shortest distances are finite. -/
private def closeSdp3Difference (a b : ℕ∞) : Option ℤ :=
  match a, b with
  | some x, some y => some ((x : ℤ) - (y : ℤ))
  | _, _ => none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite difference certifies reachability of both ambient sources. -/
private theorem closeSdp3Difference_reachable (M : RootedLocallyFiniteMap)
    (s0 s1 t : RootedLocallyFiniteVertex M.D M.rot)
    (h : (closeSdp3Difference (intrinsicIncrementSdp M s0 t)
      (intrinsicIncrementSdp M s1 t)).isSome) :
    (∃ ds, incrementSdpDartWalk M ds s0 t) ∧
      (∃ ds, incrementSdpDartWalk M ds s1 t) := by
  have ha : intrinsicIncrementSdp M s0 t ≠ ⊤ := by
    intro he
    rw [he] at h
    change (none : Option ℤ).isSome = true at h
    cases h
  have hb : intrinsicIncrementSdp M s1 t ≠ ⊤ := by
    intro he
    rw [he] at h
    cases hval : intrinsicIncrementSdp M s0 t <;>
      rw [hval] at h <;> change (none : Option ℤ).isSome = true at h <;> cases h
  exact ⟨not_not.mp (mt (intrinsicIncrementSdp_eq_top_iff M s0 t).2 ha),
    not_not.mp (mt (intrinsicIncrementSdp_eq_top_iff M s1 t).2 hb)⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Boundary-source identification transports the finite-ball difference exactly. -/
private theorem closeSdp3At_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (k : ℤ)
    (h0 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ k)
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
    (h1 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ (k - 1))
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
    (d : (rootedLocallyFiniteFramedBall M r hr).D) :
    finiteBallSdpIncrementAt (rootedLocallyFiniteFramedBall M r hr) k d =
      closeSdp3Difference
        (incrementCloseSdp_ballDistance M.toRootedLocallyFiniteMap r
          (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
          (rootedLocallyFiniteVertexClass M.rot d.1))
        (incrementCloseSdp_ballDistance M.toRootedLocallyFiniteMap r
          (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
          (rootedLocallyFiniteVertexClass M.rot d.1)) := by
  let B := rootedLocallyFiniteFramedBall M r hr
  have ha := FiniteBallSdpDistanceIdentification_proved M r hr
    (((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart) d
  have hb := FiniteBallSdpDistanceIdentification_proved M r hr
    (((B.map.rot * B.map.edgeInv) ^ (k - 1)) B.frameEdgeDart) d
  rw [h0] at ha
  rw [h1] at hb
  change closeSdp3Difference _ _ = _
  rw [← ha, ← hb]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The inverse framed vertex map cancels the forward map. -/
private theorem closeSdp3Iso_inverse {B C : FramedBall} (I : FramedBallIso B C)
    (v : MapVertex B.map) :
    framedBallVertexMap I.symm (framedBallVertexMap I v) = v := by
  induction v using Quotient.inductionOn with | h d =>
    change vertexClass _ (I.mapIso.toEquiv.symm (I.mapIso.toEquiv d)) = _
    rw [Equiv.symm_apply_apply]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite directed walks transport along framed isomorphisms. -/
private theorem closeSdp3Walk_iso {B C : FramedBall} (I : FramedBallIso B C)
    (ds : List B.D) (s t : MapVertex B.map) (h : closeSdp3Walk B.map ds s t) :
    closeSdp3Walk C.map (ds.map I.mapIso.toEquiv)
      (framedBallVertexMap I s) (framedBallVertexMap I t) := by
  induction ds generalizing s with
  | nil => exact congrArg (framedBallVertexMap I) h
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := h
    refine ⟨fun hc => hm ((I.mapIso.missing_iff d).1 hc),
      (I.mapIso.tail_iff d).2 ht, congrArg (framedBallVertexMap I) hs, ?_⟩
    have hi := ih _ hw
    have he : framedBallVertexMap I (dartHeadVertex B.map d) =
        dartHeadVertex C.map (I.mapIso.toEquiv d) := by
      change vertexClass _ (I.mapIso.toEquiv (B.map.edgeInv d)) = _
      rw [I.mapIso.edgeInv_comm]
      rfl
    rw [he] at hi
    exact hi

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Isomorphisms cannot increase finite simple shortest distance. -/
private theorem closeSdp3Distance_iso_le {B C : FramedBall} (I : FramedBallIso B C)
    (s t : MapVertex B.map) :
    (show ℕ∞ from simpleDirectedPathSDPLength C.map
      (framedBallVertexMap I s) (framedBallVertexMap I t)) ≤
      (show ℕ∞ from simpleDirectedPathSDPLength B.map s t) := by
  rw [closeSdp3Finite_inf, closeSdp3Finite_inf]
  apply le_iInf
  intro ds
  apply le_iInf
  intro hw
  exact iInf_le_of_le (ds.map I.mapIso.toEquiv)
    (iInf_le_of_le (closeSdp3Walk_iso I ds s t hw)
      (le_of_eq (congrArg (fun n : ℕ => (n : ℕ∞)) (List.length_map _))))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Framed isomorphisms preserve the complete finite SDP, including infinity. -/
private theorem closeSdp3Distance_iso {B C : FramedBall} (I : FramedBallIso B C)
    (s t : MapVertex B.map) :
    (show ℕ∞ from simpleDirectedPathSDPLength C.map
      (framedBallVertexMap I s) (framedBallVertexMap I t)) =
      (show ℕ∞ from simpleDirectedPathSDPLength B.map s t) := by
  apply le_antisymm (closeSdp3Distance_iso_le I s t)
  have h := closeSdp3Distance_iso_le I.symm (framedBallVertexMap I s)
    (framedBallVertexMap I t)
  simpa only [closeSdp3Iso_inverse] using h

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The ordered boundary sources transport at every integer index. -/
private theorem closeSdp3Source_iso {B C : FramedBall} (I : FramedBallIso B C) (k : ℤ) :
    framedBallVertexMap I (finiteBallSdpIncrementSource B k) =
      finiteBallSdpIncrementSource C k := by
  let e := I.mapIso.toEquiv
  let F := B.map.rot * B.map.edgeInv
  let G := C.map.rot * C.map.edgeInv
  have hg : G = e.permCongr F := by
    ext d
    change C.map.rot (C.map.edgeInv d) = e (B.map.rot (B.map.edgeInv (e.symm d)))
    rw [I.mapIso.rot_comm, I.mapIso.edgeInv_comm, Equiv.apply_symm_apply]
  have hp : e.permCongr (F ^ k) = (e.permCongr F) ^ k :=
    map_zpow e.permCongrHom F k
  change vertexClass _ (e ((F ^ k) B.frameEdgeDart)) =
    vertexClass _ ((G ^ k) C.frameEdgeDart)
  apply congrArg (vertexClass C.map.toCombinatorialMap)
  rw [hg, ← hp]
  change e ((F ^ k) B.frameEdgeDart) =
    e ((F ^ k) (e.symm C.frameEdgeDart))
  rw [← I.frameEdge_comm, Equiv.symm_apply_apply]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The integer difference at corresponding finite targets is isomorphism invariant. -/
private theorem closeSdp3At_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (d : B.D) :
    finiteBallSdpIncrementAt C k (I.mapIso.toEquiv d) = finiteBallSdpIncrementAt B k d := by
  have ha := closeSdp3Distance_iso I (finiteBallSdpIncrementSource B k) (vertexClass _ d)
  have hb := closeSdp3Distance_iso I (finiteBallSdpIncrementSource B (k - 1))
    (vertexClass _ d)
  rw [closeSdp3Source_iso] at ha hb
  change closeSdp3Difference _ _ = closeSdp3Difference _ _
  exact congrArg₂ closeSdp3Difference ha hb

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shell membership transports with the root vertex and every edge identity. -/
private theorem closeSdp3Shell_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (d : B.D) :
    finiteBallSdpIncrementShell B k m d ↔
      finiteBallSdpIncrementShell C k m (I.mapIso.toEquiv d) := by
  have hroot : framedBallVertexMap I (vertexClass _ B.rootDart) =
      vertexClass _ C.rootDart := Quotient.sound I.root_vertex
  have h0 := framedBallWithinRadius_iso_iff I m (vertexClass _ B.rootDart)
    (vertexClass _ d)
  have h1 := framedBallWithinRadius_iso_iff I (m + 1) (vertexClass _ B.rootDart)
    (vertexClass _ d)
  rw [hroot] at h0 h1
  change (_ ∧ ¬ _ ∧ _) ↔ (_ ∧ ¬ _ ∧ _)
  rw [h0, h1, closeSdp3At_iso I k d]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Nonempty shell consensus transports across arbitrary framed-ball isomorphisms. -/
private theorem closeSdp3Consensus_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (z : ℤ) (h : FiniteBallSdpIncrementConsensus B k m z) :
    FiniteBallSdpIncrementConsensus C k m z := by
  constructor
  · obtain ⟨d, hd⟩ := h.1
    exact ⟨I.mapIso.toEquiv d, (closeSdp3Shell_iso I k m d).1 hd⟩
  · intro c hc
    let d := I.mapIso.toEquiv.symm c
    have he : I.mapIso.toEquiv d = c := I.mapIso.toEquiv.apply_symm_apply c
    have hd : finiteBallSdpIncrementShell B k m d :=
      (closeSdp3Shell_iso I k m d).2 (he.symm ▸ hc)
    exact (he ▸ closeSdp3At_iso I k d).trans (h.2 d hd)


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The representative kernel has exactly the concrete finite-ball consensus. -/
private theorem closeSdp3_kernel_concrete (M : RootedLocallyFinitePlanarMap)
    (k : ℤ) (m r : ℕ) (z : ℤ) :
    finiteBallSdpIncrementKernel k m (rootedLocallyFiniteFacedBallClass r M) = some z ↔
      FiniteBallSdpIncrementConsensus
        (rootedLocallyFiniteFramedBall M (r + 1) (Nat.succ_pos r)) k m z := by
  rw [finiteBallSdpIncrementKernel_eq_some_iff]
  let q := rootedLocallyFiniteFacedBallClass r M
  obtain ⟨J⟩ : Nonempty (FacedFramedBallIso q.out
      (rootedLocallyFiniteFacedBall M (r + 1) (Nat.succ_pos r))) :=
    Quotient.exact q.out_eq
  exact ⟨closeSdp3Consensus_iso J.toFramedBallIso k m z,
    closeSdp3Consensus_iso J.toFramedBallIso.symm k m z⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
For a fixed target radius, one enclosing radius identifies every finite difference
with its ambient intrinsic difference, including the failure of reachability. -/
private theorem closeSdp3At_uniform (M : RootedLocallyFinitePlanarMap)
    (k : ℤ) (m : ℕ) :
    ∃ R : ℕ, m + 1 ≤ R ∧ ∀ r ≥ R, ∀ hr : 0 < r,
      ∀ d : (rootedLocallyFiniteFramedBall M r hr).D,
      rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap (m + 1)
        (rootedLocallyFiniteVertexClass M.rot d.1) →
      finiteBallSdpIncrementAt (rootedLocallyFiniteFramedBall M r hr) k d =
        closeSdp3Difference
          (intrinsicIncrementSdp M.toRootedLocallyFiniteMap
            (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
            (rootedLocallyFiniteVertexClass M.rot d.1))
          (intrinsicIncrementSdp M.toRootedLocallyFiniteMap
            (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
            (rootedLocallyFiniteVertexClass M.rot d.1)) := by
  obtain ⟨S0, hS0⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M k
  obtain ⟨S1, hS1⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M (k - 1)
  obtain ⟨R, hR, he⟩ := incrementCloseSdp_ballDistance_stabilizes_on_radius
    M.toRootedLocallyFiniteMap
    (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
    (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
    (m + 1) (max (max S0 S1) (m + 1))
  refine ⟨R, by omega, fun r hr hpos d hd => ?_⟩
  obtain ⟨he0, he1⟩ := he r hr _
    ((mem_rootedLocallyFiniteRadiusVertices _ _ _).2 hd)
  rw [closeSdp3At_transport M r hpos k
    (hS0 r (by omega) hpos) (hS1 r (by omega) hpos) d, he0, he1]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every vertex outside a ball belongs to a later exact geometric shell. -/
private theorem closeSdp3_vertex_shell (M : RootedLocallyFiniteMap)
    (t : RootedLocallyFiniteVertex M.D M.rot) (N : ℕ)
    (ht : ¬ rootedLocallyFiniteWithinRadius M N t) :
    ∃ m ≥ N, rootedLocallyFiniteWithinRadius M (m + 1) t ∧
      ¬ rootedLocallyFiniteWithinRadius M m t := by
  classical
  have hex : ∃ r, rootedLocallyFiniteWithinRadius M r t := by
    obtain ⟨R, _, hR⟩ := closeSdp3_vertexFinset_captured M {t} 0
    exact ⟨R, hR t (Finset.mem_singleton_self _)⟩
  have hmin := Nat.find_spec hex
  have hlow : N < Nat.find hex := by
    by_contra! hn
    exact ht ((mem_rootedLocallyFiniteRadiusVertices M N t).1
      (rootedLocallyFiniteRadiusVertices_mono M hn
        ((mem_rootedLocallyFiniteRadiusVertices M (Nat.find hex) t).2 hmin)))
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using hmin
  · exact Nat.find_min hex (by omega)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite candidate differences certify the exact two finite ambient distances. -/
private theorem closeSdp3Difference_eq_some (a b : ℕ∞) (z : ℤ) :
    closeSdp3Difference a b = some z ↔
      ∃ x y : ℕ, a = (x : ℕ∞) ∧ b = (y : ℕ∞) ∧ z = (x : ℤ) - (y : ℤ) := by
  constructor
  · intro h
    cases a using Option.rec with
    | none =>
      change (none : Option ℤ) = some z at h
      cases h
    | some x =>
      cases b using Option.rec with
      | none =>
        change (none : Option ℤ) = some z at h
        cases h
      | some y =>
        change some ((x : ℤ) - (y : ℤ)) = some z at h
        exact ⟨x, y, rfl, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨x, y, rfl, rfl, rfl⟩
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite candidate at every index is a countably specified event. -/
private def closeSdp3CandidateEvent (M : RootedLocallyFinitePlanarMap) : Prop :=
  ∀ k : ℤ, ∃ z : ℤ, finiteBallSdpIncrementCandidate k M = some z

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite candidate supplies both clauses of the intrinsic characterization. -/
private theorem closeSdp3ObservableData_of_candidateEvent (M : RootedLocallyFinitePlanarMap)
    (h : closeSdp3CandidateEvent M) : closeSdp2ObservableData M := by
  classical
  let A := M.toRootedLocallyFiniteMap
  constructor
  · intro k
    obtain ⟨z, hz⟩ := h k
    have hobs : finiteBallSdpIncrementObservable k M = z := by
      simp only [finiteBallSdpIncrementObservable, hz, Option.getD_some]
    obtain ⟨N, hN⟩ := (finiteBallSdpIncrementCandidate_eq_some_iff k M z).1 hz
    refine ⟨N, fun t ht h0 h1 => ?_⟩
    obtain ⟨m, hm, hnear, hfar⟩ := closeSdp3_vertex_shell A t N ht
    obtain ⟨R0, hR0⟩ := hN m hm
    obtain ⟨R1, hR1low, hR1⟩ := closeSdp3At_uniform M k m
    obtain ⟨R2, hR2low, hR2⟩ := incrementSdpDartList_captured A
      (max R0 R1) [Quotient.out t]
    let r := R2 + 1
    let hr : 0 < r := Nat.succ_pos R2
    let d : (rootedLocallyFiniteFramedBall M r hr).D :=
      ⟨Quotient.out t, rootedLocallyFiniteBallDarts_mono A (by omega)
        (hR2 _ (List.mem_singleton_self _))⟩
    have hd : rootedLocallyFiniteVertexClass M.rot d.1 = t := Quotient.out_eq' t
    have hc := (closeSdp3_kernel_concrete M k m R2 z).1 (hR0 R2 (by omega))
    have he := hR1 r (by omega) hr d (hd.symm ▸ hnear)
    have hdiff : closeSdp3Difference
        (intrinsicIncrementSdp A (intrinsicSdpIncrementSource A k) t)
        (intrinsicIncrementSdp A (intrinsicSdpIncrementSource A (k - 1)) t) = some z := by
      rw [← hd, ← he]
      apply hc.2 d
      refine ⟨?_, ?_, ?_⟩
      · apply (rootedLocallyFiniteFramedBall_withinRadius_iff M hr (by omega) d).2
        have hdn : rootedLocallyFiniteWithinRadius A (m + 1)
            (rootedLocallyFiniteVertexClass M.rot d.1) := hd.symm ▸ hnear
        exact hdn
      · intro hh
        exact hfar (hd ▸
          (rootedLocallyFiniteFramedBall_withinRadius_iff M hr (by omega) d).1 hh)
      · rw [he, hd]
        obtain ⟨ds0, _, ha⟩ := intrinsicIncrementSdp_attained A _ t h0
        obtain ⟨ds1, _, hb⟩ := intrinsicIncrementSdp_attained A _ t h1
        rw [← ha, ← hb]
        rfl
    obtain ⟨a, b, ha, hb, hi⟩ := (closeSdp3Difference_eq_some _ _ _).1 hdiff
    exact ⟨a, b, ha, hb, hobs.trans hi⟩
  · intro k T
    obtain ⟨z, hz⟩ := h k
    obtain ⟨N, hN⟩ := (finiteBallSdpIncrementCandidate_eq_some_iff k M z).1 hz
    obtain ⟨S, _, hS⟩ := closeSdp3_vertexFinset_captured A T 0
    let m := max N S
    obtain ⟨R0, hR0⟩ := hN m (le_max_left _ _)
    obtain ⟨R1, hR1low, hR1⟩ := closeSdp3At_uniform M k m
    let r := max R0 R1 + 1
    let hr : 0 < r := Nat.succ_pos _
    have hc := (closeSdp3_kernel_concrete M k m (max R0 R1) z).1
      (hR0 _ (le_max_left _ _))
    obtain ⟨d, hdnear, hdfar, hfinite⟩ := hc.1
    let t := rootedLocallyFiniteVertexClass M.rot d.1
    have hnear : rootedLocallyFiniteWithinRadius A (m + 1) t :=
      (rootedLocallyFiniteFramedBall_withinRadius_iff M hr (by omega) d).1 hdnear
    have hfar : ¬ rootedLocallyFiniteWithinRadius A m t := by
      intro ht
      exact hdfar
        ((rootedLocallyFiniteFramedBall_withinRadius_iff M hr (by omega) d).2 ht)
    have he := hR1 r (by omega) hr d hnear
    have hfinite' : (closeSdp3Difference
        (intrinsicIncrementSdp A (intrinsicSdpIncrementSource A k) t)
        (intrinsicIncrementSdp A (intrinsicSdpIncrementSource A (k - 1)) t)).isSome := by
      rw [← he]
      exact hfinite
    obtain ⟨h0, h1⟩ := closeSdp3Difference_reachable A _ _ t hfinite'
    refine ⟨t, ?_, h0, h1⟩
    intro ht
    exact hfar ((mem_rootedLocallyFiniteRadiusVertices A m t).1
      (rootedLocallyFiniteRadiusVertices_mono A (le_max_right N S)
        ((mem_rootedLocallyFiniteRadiusVertices A S t).2 (hS t ht))))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The faced-ball topology underlying all measurable events in this module. -/
noncomputable local instance closeSdp3Topology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The Borel measurable structure of the faced-ball topology. -/
noncomputable local instance closeSdp3Measurable :
    MeasurableSpace RootedLocallyFinitePlanarMap := borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The discrete measurable space for finite-increment options. -/
local instance closeSdp3OptionMeasurable : MeasurableSpace (Option ℤ) := ⊤

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite-increment singleton sets are measurable. -/
local instance closeSdp3OptionSingleton : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Countably many candidate fibers make the replacement data event measurable. -/
private theorem measurableSet_closeSdp3CandidateEvent :
    MeasurableSet {M : RootedLocallyFinitePlanarMap | closeSdp3CandidateEvent M} := by
  exact (Measurable.forall fun k : ℤ => Measurable.exists fun z : ℤ =>
    (measurable_finiteBallSdpIncrementCandidate k).eq_const (some z)).setOf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The proved shell stabilization realizes finite candidates simultaneously at all indices. -/
private theorem closeSdp3_ae_code_candidateEvent :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      closeSdp3CandidateEvent (uibhbotRootedPlanarMapOfCode W) := by
  have hstab : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
        finiteBallSdpIncrementKernel k m
          (rootedLocallyFiniteFacedBallClass r (uibhbotRootedPlanarMapOfCode W)) =
            some (uibhbotMirrorSdpCodeIncrement k W) := by
    exact ae_all_iff.mpr uibhbotSdpIncrementBallShellStabilizationAt_proved
  filter_upwards [hstab] with W hW k
  exact ⟨uibhbotMirrorSdpCodeIncrement k W,
    (finiteBallSdpIncrementCandidate_eq_some_iff k _ _).2 (hW k)⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The measurable candidate event is conull for the existing rooted-map law. -/
private theorem ae_closeSdp3CandidateEvent :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      closeSdp3CandidateEvent M := by
  change ∀ᵐ M ∂((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode), closeSdp3CandidateEvent M
  exact (ae_map_iff measurable_uibhbotRootedPlanarMapOfCode.aemeasurable
    measurableSet_closeSdp3CandidateEvent).2 closeSdp3_ae_code_candidateEvent

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intersect all forward mirror preimages to obtain a literally mirror-closed event.
This avoids identifying twice-reflected root dart representatives. -/
private def closeSdp3MirrorClosedCandidateEvent (M : RootedLocallyFinitePlanarMap) : Prop :=
  ∀ n : ℕ, closeSdp3CandidateEvent (mirrorRootedLocallyFinitePlanarMap^[n] M)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Countable intersections preserve measurability of the mirror-closed event. -/
private theorem measurableSet_closeSdp3MirrorClosedCandidateEvent :
    MeasurableSet {M : RootedLocallyFinitePlanarMap |
      closeSdp3MirrorClosedCandidateEvent M} := by
  exact (Measurable.forall fun n : ℕ =>
    (measurableSet_setOfPred.1 (measurableSet_closeSdp3CandidateEvent.preimage
      (measurable_mirrorRootedLocallyFinitePlanarMap.iterate n)))).setOf

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The replacement event is closed under the actual mirror map. -/
private theorem closeSdp3MirrorClosedCandidateEvent_mirror (M : RootedLocallyFinitePlanarMap)
    (h : closeSdp3MirrorClosedCandidateEvent M) :
    closeSdp3MirrorClosedCandidateEvent (mirrorRootedLocallyFinitePlanarMap M) := by
  intro n
  simpa only [Function.iterate_succ_apply] using h (n + 1)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Mirror-law invariance makes the countable mirror-closed event conull. -/
private theorem ae_closeSdp3MirrorClosedCandidateEvent :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      closeSdp3MirrorClosedCandidateEvent M := by
  apply ae_all_iff.mpr
  intro n
  induction n with
  | zero => exact ae_closeSdp3CandidateEvent
  | succ n ih =>
    have hmap : ∀ᵐ M ∂((uibhbotRootedPlanarMapLaw :
        Measure RootedLocallyFinitePlanarMap).map mirrorRootedLocallyFinitePlanarMap),
        closeSdp3CandidateEvent (mirrorRootedLocallyFinitePlanarMap^[n] M) := by
      rw [uibhbotLaw_mirror_invariant
        DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed]
      exact ih
    have hm := ae_of_ae_map
      measurable_mirrorRootedLocallyFinitePlanarMap.aemeasurable hmap
    simpa only [Function.iterate_succ_apply] using hm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic characterization forces reflection with the ordered-root shift two. -/
private theorem closeSdp3_reflection_of_data (M : RootedLocallyFinitePlanarMap)
    (h : closeSdp2ObservableData M)
    (hm : closeSdp2ObservableData (mirrorRootedLocallyFinitePlanarMap M)) :
    finiteBallSdpIncrementObservable 0 (mirrorRootedLocallyFinitePlanarMap M) =
      -finiteBallSdpIncrementObservable 2 M := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let B := mirrorRootedLocallyFiniteMap A
  let e := incrementSdpMirrorVertexEquiv A
  obtain ⟨N, hN⟩ := h.1 2
  obtain ⟨R, hR⟩ := hm.1 0
  let T := rootedLocallyFiniteRadiusVertices A N ∪
    (rootedLocallyFiniteRadiusVertices B R).image e.symm
  obtain ⟨t, ht, h0, h1⟩ := h.2 2 T
  have htN : ¬ rootedLocallyFiniteWithinRadius A N t := by
    intro hn
    exact ht (Finset.mem_union_left _
      ((mem_rootedLocallyFiniteRadiusVertices A N t).2 hn))
  have htR : ¬ rootedLocallyFiniteWithinRadius B R (e t) := by
    intro hr
    apply ht
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨e t, (mem_rootedLocallyFiniteRadiusVertices B R (e t)).2 hr,
        e.symm_apply_apply t⟩
  obtain ⟨a, b, ha, hb, hi⟩ := hN t htN h0 h1
  have hm0 : ∃ ds, incrementSdpDartWalk B ds (intrinsicSdpIncrementSource B 0) (e t) := by
    obtain ⟨ds, hd⟩ := h1
    have hx := (incrementSdpDartWalk_mirror A ds
      (intrinsicSdpIncrementSource A (2 - 1)) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicSdpIncrementSource_mirror, sub_zero,
      show (2 : ℤ) - 1 = 1 from rfl, e, B] using hx
  have hm1 : ∃ ds, incrementSdpDartWalk B ds
      (intrinsicSdpIncrementSource B (0 - 1)) (e t) := by
    obtain ⟨ds, hd⟩ := h0
    have hx := (incrementSdpDartWalk_mirror A ds
      (intrinsicSdpIncrementSource A 2) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicSdpIncrementSource_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl, e, B] using hx
  obtain ⟨c, d, hc, hd, hj⟩ := hR (e t) htR hm0 hm1
  change intrinsicIncrementSdp B (intrinsicSdpIncrementSource B 0) (e t) = (c : ℕ∞) at hc
  change intrinsicIncrementSdp B (intrinsicSdpIncrementSource B (0 - 1)) (e t) =
    (d : ℕ∞) at hd
  have hc' : intrinsicIncrementSdp A (intrinsicSdpIncrementSource A (2 - 1)) t =
      (c : ℕ∞) := by
    simpa only [B, e, intrinsicSdpIncrementSource_mirror, intrinsicIncrementSdp_mirror,
      sub_zero, show (2 : ℤ) - 1 = 1 from rfl] using hc
  have hd' : intrinsicIncrementSdp A (intrinsicSdpIncrementSource A 2) t = (d : ℕ∞) := by
    simpa only [B, e, intrinsicSdpIncrementSource_mirror, intrinsicIncrementSdp_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl] using hd
  have hcb : c = b := by exact_mod_cast hc'.symm.trans hb
  have hda : d = a := by exact_mod_cast hd'.symm.trans ha
  rw [hcb, hda] at hj
  omega

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The measurable, conull, mirror-closed candidate event forces scalar reflection.
No measurability of the larger intrinsic data event is required. -/
theorem uibhbotSdpIncrementObservableReflection_unconditional :
    UIBHBOTSdpIncrementObservableReflection finiteBallSdpIncrementObservable := by
  filter_upwards [ae_closeSdp3MirrorClosedCandidateEvent] with M hM
  apply closeSdp3_reflection_of_data M
  · exact closeSdp3ObservableData_of_candidateEvent M (hM 0)
  · exact closeSdp3ObservableData_of_candidateEvent _
      ((closeSdp3MirrorClosedCandidateEvent_mirror M hM) 0)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Unconditional symmetry of the measurable one-sided SDP increment at zero.
The finite-ball realization and the conull intrinsic reflection are proved inputs. -/
theorem hsymSdp_unconditional :
    iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) := by
  exact hsymSdp_of_remaining_ballShell_and_reflection
    (uibhbotSdpIncrementBallShellStabilizationAt_proved 0)
    (uibhbotSdpIncrementBallShellStabilizationAt_proved 2)
    uibhbotSdpIncrementObservableReflection_unconditional

end DirectedDistances.PaperProofs.Section5
