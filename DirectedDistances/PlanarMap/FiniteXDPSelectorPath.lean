/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPGeodesicDart

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- A vertex on an LDP geodesic has longest source and sink distances summing
to the LDP length (`lem-lr-ind`,
leftmost-geodesic cut; the leftmost selector from rotation order is a later
step. -/
theorem distance_sum_of_mem_LDPGeodesic_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsLDPGeodesicBase B P ∧ v ∈ P.vertices) →
      ldpSourceDistanceNatBase B v + ldpSinkDistanceNatBase B v = ldpLengthBase B := by
  rintro ⟨n, P, hP, hv⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hiBound : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
  let j : Fin (n + 1) := ⟨i.val, hiBound⟩
  have hdist := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP j
  have hlen := (isLDPGeodesicBase_iff_length_eq B P).mp hP
  have hvertex : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = v := by
    have hji : (⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ :
        Fin P.vertices.length) = i := by
      apply Fin.ext
      rfl
    simpa only [hji] using hi
  have hdist' : ldpSourceDistanceNatBase B v = j.val ∧
      ldpSinkDistanceNatBase B v = n - j.val := by
    simpa only [hvertex] using hdist
  omega

/-- A vertex on an SDP geodesic has shortest source and sink distances summing
to the SDP length (`lem-lr-ind`,
leftmost-geodesic cut; the leftmost selector from rotation order is a later
step. -/
theorem distance_sum_of_mem_SDPGeodesic_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsSDPGeodesicBase B P ∧ v ∈ P.vertices) →
      sdpSourceDistanceNatBase B v + sdpSinkDistanceNatBase B v = sdpLengthBase B := by
  rintro ⟨n, P, hP, hv⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hiBound : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
  let j : Fin (n + 1) := ⟨i.val, hiBound⟩
  have hdist := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP j
  have hlen := (isSDPGeodesicBase_iff_length_eq B P).mp hP
  have hvertex : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = v := by
    have hji : (⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ :
        Fin P.vertices.length) = i := by
      apply Fin.ext
      rfl
    simpa only [hji] using hi
  have hdist' : sdpSourceDistanceNatBase B v = j.val ∧
      sdpSinkDistanceNatBase B v = n - j.val := by
    simpa only [hvertex] using hdist
  omega

/-- The head of a geodesic dart is a vertex on an XDP geodesic
supports the leftmost-geodesic cut; the leftmost selector from rotation order
is a later step. -/
theorem exists_XDPGeodesic_vertex_at_head
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) (d : D)
    (hd : IsXDPGeodesicDart B x d) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ dartHeadVertex B.map d ∈ P.vertices := by
  obtain ⟨n, P, hP, hv⟩ := hd
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hstep := P.edge_step i
  rw [hi] at hstep
  have hiBound : i.val < n := by simpa [P.darts_length] using i.isLt
  let j : Fin P.vertices.length := ⟨i.val + 1, by rw [P.vertices_length]; omega⟩
  have hmem : dartHeadVertex B.map d ∈ P.vertices :=
    List.mem_iff_get.mpr ⟨j, hstep.2.2.2⟩
  exact ⟨n, P, hP, hmem⟩

/-- A non-sink vertex on an XDP geodesic has an outgoing geodesic dart
supports the leftmost-geodesic cut; the leftmost selector from rotation order
is a later step. -/
theorem exists_outgoingXDPGeodesicDart_of_geodesic_vertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {v : MapVertex B.map}
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink) :
    ∃ d, dartTailVertex B.map d = v ∧ IsXDPGeodesicDart B x d := by
  obtain ⟨n, P, hP, hvP⟩ := hv
  obtain ⟨d, _, htail, hd⟩ :=
    exists_outgoingXDPGeodesicDart_of_mem_vertices B x P hP hvP hvs
  exact ⟨d, htail, hd⟩

/-- The next vertex selected from `v`, with the sink as a fixed point -/
@[expose] noncomputable def selectorStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : MapVertex B.map → D) (v : MapVertex B.map) : MapVertex B.map := by
  classical
  exact if v = B.sink then B.sink else dartHeadVertex B.map (sel v)

/-- The finite LDP or SDP length selected by `x` (`lem-lr-ind`, -/
@[expose] noncomputable def xdpLengthBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) : ℕ :=
  match x with
  | .ldp => ldpLengthBase B
  | .sdp => sdpLengthBase B

/-- The natural valued source distance selected by `x` (`lem-lr-ind`, -/
@[expose] noncomputable def xdpSourceDistanceNatBase
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) : ℕ :=
  match x with
  | .ldp => ldpSourceDistanceNatBase B v
  | .sdp => sdpSourceDistanceNatBase B v

/-- Iteration of a chosen outgoing geodesic dart, stopped at the sink. The
leftmost selector from rotation order is a later step (`lem-lr-ind`, -/
@[expose] noncomputable def selectorVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : MapVertex B.map → D) : ℕ → MapVertex B.map := by
  classical
  exact Nat.rec B.source
    (fun _ v => selectorStep B sel v)

/-- One selector iteration either remains at the sink or follows the
selected dart (`lem-lr-ind`, -/
theorem selectorVertex_succ
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : MapVertex B.map → D) (i : ℕ) :
    selectorVertex B sel (i + 1) = selectorStep B sel (selectorVertex B sel i) := by
  rfl

private theorem xdpSourceDistanceNatBase_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    (match x with
     | .ldp => ldpSourceDistanceNatBase B B.source
     | .sdp => sdpSourceDistanceNatBase B B.source) = 0 := by
  cases x with
  | ldp =>
      obtain ⟨n, P, hP⟩ := exists_isLDPGeodesicBase B
      let i : Fin (n + 1) := ⟨0, by omega⟩
      have hdist := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP i
      have hstart : P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ = B.source := by
        simpa [i] using P.start_vertex
      rw [← hstart]
      simpa [i] using hdist.1
  | sdp =>
      obtain ⟨n, P, hP⟩ := exists_isSDPGeodesicBase B
      let i : Fin (n + 1) := ⟨0, by omega⟩
      have hdist := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP i
      have hstart : P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ = B.source := by
        simpa [i] using P.start_vertex
      rw [← hstart]
      simpa [i] using hdist.1

private theorem ldpSourceDistanceNatBase_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ldpSourceDistanceNatBase B B.sink = ldpLengthBase B := by
  obtain ⟨n, P, hP⟩ := exists_isLDPGeodesicBase B
  have hlen := (isLDPGeodesicBase_iff_length_eq B P).mp hP
  let i : Fin (n + 1) := ⟨n, by omega⟩
  have hdist := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP i
  have hend : P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ = B.sink := by
    simpa [i] using P.end_vertex
  calc
    ldpSourceDistanceNatBase B B.sink =
        ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) :=
      congrArg (ldpSourceDistanceNatBase B) hend.symm
    _ = i.val := hdist.1
    _ = ldpLengthBase B := by simpa [i] using hlen

private theorem sdpSourceDistanceNatBase_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    sdpSourceDistanceNatBase B B.sink = sdpLengthBase B := by
  obtain ⟨n, P, hP⟩ := exists_isSDPGeodesicBase B
  have hlen := (isSDPGeodesicBase_iff_length_eq B P).mp hP
  let i : Fin (n + 1) := ⟨n, by omega⟩
  have hdist := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP i
  have hend : P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ = B.sink := by
    simpa [i] using P.end_vertex
  calc
    sdpSourceDistanceNatBase B B.sink =
        sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) :=
      congrArg (sdpSourceDistanceNatBase B) hend.symm
    _ = i.val := hdist.1
    _ = sdpLengthBase B := by simpa [i] using hlen

/-- A geodesic vertex whose source distance is the full geodesic length is
the sink (`lem-lr-ind`, -/
private theorem geodesic_vertex_eq_sink_of_sourceDistance_eq_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {v : MapVertex B.map}
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hdist : xdpSourceDistanceNatBase B x v = xdpLengthBase B x) :
    v = B.sink := by
  cases x with
  | ldp =>
      obtain ⟨n, P, hP, hvP⟩ := hv
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvP
      have hiBound : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
      let j : Fin (n + 1) := ⟨i.val, hiBound⟩
      have hdistP := IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP j
      have hlen := (isLDPGeodesicBase_iff_length_eq B P).mp hP
      have hvertex : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = v := by
        have hji : (⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ : Fin P.vertices.length) = i := by
          apply Fin.ext
          rfl
        simpa only [hji] using hi
      have hdistV : ldpSourceDistanceNatBase B v = j.val := by
        simpa only [hvertex] using hdistP.1
      change ldpSourceDistanceNatBase B v = ldpLengthBase B at hdist
      have hlast : j.val = n := by
        change ldpSourceDistanceNatBase B v = ldpLengthBase B at hdist
        omega
      calc
        v = P.vertices.get i := hi.symm
        _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
          congr 1
          exact Fin.ext (by simpa [j] using hlast)
        _ = B.sink := P.end_vertex
  | sdp =>
      obtain ⟨n, P, hP, hvP⟩ := hv
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hvP
      have hiBound : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
      let j : Fin (n + 1) := ⟨i.val, hiBound⟩
      have hdistP := IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP j
      have hlen := (isSDPGeodesicBase_iff_length_eq B P).mp hP
      have hvertex : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = v := by
        have hji : (⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ : Fin P.vertices.length) = i := by
          apply Fin.ext
          rfl
        simpa only [hji] using hi
      have hdistV : sdpSourceDistanceNatBase B v = j.val := by
        simpa only [hvertex] using hdistP.1
      change sdpSourceDistanceNatBase B v = sdpLengthBase B at hdist
      have hlast : j.val = n := by
        change sdpSourceDistanceNatBase B v = sdpLengthBase B at hdist
        omega
      calc
        v = P.vertices.get i := hi.symm
        _ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
          congr 1
          exact Fin.ext (by simpa [j] using hlast)
        _ = B.sink := P.end_vertex

/-- Every selector iterate is a vertex of an XDP geodesic (`lem-lr-ind`, -/
theorem selectorVertex_mem_XDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v))
    (i : ℕ) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ selectorVertex B sel i ∈ P.vertices := by
  induction i with
  | zero =>
      cases x with
      | ldp =>
          obtain ⟨n, P, hP⟩ := exists_isLDPGeodesicBase B
          refine ⟨n, P, hP, ?_⟩
          apply List.mem_iff_get.mpr
          refine ⟨⟨0, by rw [P.vertices_length]; omega⟩, ?_⟩
          simpa [selectorVertex] using P.start_vertex
      | sdp =>
          obtain ⟨n, P, hP⟩ := exists_isSDPGeodesicBase B
          refine ⟨n, P, hP, ?_⟩
          apply List.mem_iff_get.mpr
          refine ⟨⟨0, by rw [P.vertices_length]; omega⟩, ?_⟩
          simpa [selectorVertex] using P.start_vertex
  | succ i ih =>
      rw [selectorVertex_succ]
      by_cases hsink : selectorVertex B sel i = B.sink
      · simpa [selectorStep, hsink] using ih
      · obtain ⟨n, P, hP, hv⟩ := ih
        obtain ⟨_, hd⟩ := hsel (selectorVertex B sel i) ⟨n, P, hP, hv⟩ hsink
        obtain ⟨n', P', hP', hv'⟩ :=
          exists_XDPGeodesic_vertex_at_head B x (sel (selectorVertex B sel i)) hd
        simpa [selectorStep, hsink] using (show
          ∃ n', ∃ P' : SimpleDirectedDartPath B.map B.source B.sink n',
            IsXDPGeodesicBase B x P' ∧
              dartHeadVertex B.map (sel (selectorVertex B sel i)) ∈ P'.vertices
          from ⟨n', P', hP', hv'⟩)

private theorem selectorVertex_sourceDistanceNat_ldp
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsLDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .ldp (sel v))
    (i : ℕ) (hi : i ≤ ldpLengthBase B) :
    ldpSourceDistanceNatBase B (selectorVertex B sel i) = i := by
  induction i with
  | zero =>
      have hzero : selectorVertex B sel 0 = B.source := by simp [selectorVertex]
      rw [hzero]
      exact xdpSourceDistanceNatBase_source B .ldp
  | succ i ih =>
      have hi' : i ≤ ldpLengthBase B := by omega
      have hprev := ih hi'
      have hv := selectorVertex_mem_XDPGeodesic B .ldp sel hsel i
      have hnot : selectorVertex B sel i ≠ B.sink := by
        intro hs
        rw [hs, ldpSourceDistanceNatBase_sink B] at hprev
        omega
      obtain ⟨htail, hd⟩ := hsel _ hv hnot
      obtain ⟨_, _, _, _, hinc⟩ :=
        IsXDPGeodesicDart.headVertex_sourceDistanceNat B .ldp
          (sel (selectorVertex B sel i)) (selectorVertex B sel i) hd htail
      have hhead : ldpSourceDistanceNatBase B
          (dartHeadVertex B.map (sel (selectorVertex B sel i))) =
        ldpSourceDistanceNatBase B (selectorVertex B sel i) + 1 := by
        simpa using hinc
      rw [selectorVertex_succ]
      simp [selectorStep, hnot, hhead, hprev]

private theorem selectorVertex_sourceDistanceNat_sdp
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsSDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .sdp (sel v))
    (i : ℕ) (hi : i ≤ sdpLengthBase B) :
    sdpSourceDistanceNatBase B (selectorVertex B sel i) = i := by
  induction i with
  | zero =>
      have hzero : selectorVertex B sel 0 = B.source := by simp [selectorVertex]
      rw [hzero]
      exact xdpSourceDistanceNatBase_source B .sdp
  | succ i ih =>
      have hi' : i ≤ sdpLengthBase B := by omega
      have hprev := ih hi'
      have hv := selectorVertex_mem_XDPGeodesic B .sdp sel hsel i
      have hnot : selectorVertex B sel i ≠ B.sink := by
        intro hs
        rw [hs, sdpSourceDistanceNatBase_sink B] at hprev
        omega
      obtain ⟨htail, hd⟩ := hsel _ hv hnot
      obtain ⟨_, _, _, _, hinc⟩ :=
        IsXDPGeodesicDart.headVertex_sourceDistanceNat B .sdp
          (sel (selectorVertex B sel i)) (selectorVertex B sel i) hd htail
      have hhead : sdpSourceDistanceNatBase B
          (dartHeadVertex B.map (sel (selectorVertex B sel i))) =
        sdpSourceDistanceNatBase B (selectorVertex B sel i) + 1 := by
        simpa using hinc
      rw [selectorVertex_succ]
      simp [selectorStep, hnot, hhead, hprev]

/-- The selected source distance equals the iteration index through the
geodesic length (`lem-lr-ind`, -/
theorem selectorVertex_sourceDistanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v))
    (i : ℕ)
    (hi : i ≤ xdpLengthBase B x) :
    xdpSourceDistanceNatBase B x (selectorVertex B sel i) = i := by
  cases x with
  | ldp =>
      change i ≤ ldpLengthBase B at hi
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsLDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .ldp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      simpa [xdpSourceDistanceNatBase] using selectorVertex_sourceDistanceNat_ldp B sel hs i hi
  | sdp =>
      change i ≤ sdpLengthBase B at hi
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsSDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .sdp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      simpa [xdpSourceDistanceNatBase] using selectorVertex_sourceDistanceNat_sdp B sel hs i hi

/-- The selector reaches the sink exactly at the geodesic length -/
theorem selectorVertex_eq_sink_at_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v)) :
    selectorVertex B sel (xdpLengthBase B x) = B.sink := by
  cases x with
  | ldp =>
      change selectorVertex B sel (ldpLengthBase B) = B.sink
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsLDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .ldp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      have hgeo := selectorVertex_mem_XDPGeodesic B .ldp sel hs (ldpLengthBase B)
      have hdist := selectorVertex_sourceDistanceNat_ldp B sel hs
        (ldpLengthBase B) (Nat.le_refl _)
      exact geodesic_vertex_eq_sink_of_sourceDistance_eq_length B .ldp hgeo hdist
  | sdp =>
      change selectorVertex B sel (sdpLengthBase B) = B.sink
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsSDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .sdp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      have hgeo := selectorVertex_mem_XDPGeodesic B .sdp sel hs (sdpLengthBase B)
      have hdist := selectorVertex_sourceDistanceNat_sdp B sel hs
        (sdpLengthBase B) (Nat.le_refl _)
      exact geodesic_vertex_eq_sink_of_sourceDistance_eq_length B .sdp hgeo hdist

/-- No selector iterate before the geodesic length is the sink
(`lem-lr-ind`, -/
theorem selectorVertex_ne_sink_of_lt_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v))
    (i : ℕ)
    (hi : i < xdpLengthBase B x) :
    selectorVertex B sel i ≠ B.sink := by
  cases x with
  | ldp =>
      have hi' : i < ldpLengthBase B := by simpa [xdpLengthBase] using hi
      intro hsink
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsLDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .ldp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      have hdist := selectorVertex_sourceDistanceNat_ldp B sel hs i (Nat.le_of_lt hi')
      rw [hsink, ldpSourceDistanceNatBase_sink B] at hdist
      omega
  | sdp =>
      have hi' : i < sdpLengthBase B := by simpa [xdpLengthBase] using hi
      intro hsink
      have hs : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
          IsSDPGeodesicBase B P ∧ v ∈ P.vertices) → v ≠ B.sink →
          dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B .sdp (sel v) := by
        intro v hv hvs
        apply hsel v
        · simpa [IsXDPGeodesicBase] using hv
        · exact hvs
      have hdist := selectorVertex_sourceDistanceNat_sdp B sel hs i (Nat.le_of_lt hi')
      rw [hsink, sdpSourceDistanceNatBase_sink B] at hdist
      omega

/-- At every index below the geodesic length, the selector chooses a
geodesic dart from the current vertex to the next iterate (`lem-lr-ind`, -/
theorem selectorVertex_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v))
    (i : ℕ)
    (hi : i < xdpLengthBase B x) :
    dartTailVertex B.map (sel (selectorVertex B sel i)) = selectorVertex B sel i ∧
      IsXDPGeodesicDart B x (sel (selectorVertex B sel i)) ∧
      dartHeadVertex B.map (sel (selectorVertex B sel i)) =
        selectorVertex B sel (i + 1) := by
  have hgeo := selectorVertex_mem_XDPGeodesic B x sel hsel i
  have hnot := selectorVertex_ne_sink_of_lt_length B x sel hsel i hi
  obtain ⟨htail, hd⟩ := hsel _ hgeo hnot
  refine ⟨htail, hd, ?_⟩
  rw [selectorVertex_succ]
  simp [selectorStep, hnot]

/-- The selected darts form a simple directed path whose length is the XDP
geodesic length (`lem-lr-ind`,
leftmost-geodesic cut; selecting the leftmost dart by rotation order is a
later step. -/
theorem exists_selector_XDPGeodesic_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (sel : MapVertex B.map → D)
    (hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v)) :
    ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
      IsXDPGeodesicBase B x P ∧
        ∀ i : Fin (xdpLengthBase B x),
          P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ =
            sel (selectorVertex B sel i.val) := by
  classical
  let L := xdpLengthBase B x
  let V : Fin (L + 1) → MapVertex B.map := fun i => selectorVertex B sel i.val
  let E : Fin L → D := fun i => sel (selectorVertex B sel i.val)
  let P : SimpleDirectedDartPath B.map B.source B.sink L := {
    darts := List.ofFn E
    vertices := List.ofFn V
    darts_length := by simp
    vertices_length := by simp
    vertices_nodup := by
      apply List.nodup_ofFn.mpr
      intro i j hij
      have hEq : xdpSourceDistanceNatBase B x (selectorVertex B sel i.val) =
          xdpSourceDistanceNatBase B x (selectorVertex B sel j.val) :=
        congrArg (xdpSourceDistanceNatBase B x) hij
      have hdi := selectorVertex_sourceDistanceNat B x sel hsel i.val (by omega)
      have hdj := selectorVertex_sourceDistanceNat B x sel hsel j.val (by omega)
      rw [hdi, hdj] at hEq
      exact Fin.ext hEq
    start_vertex := by
      simp [V, selectorVertex]
    end_vertex := by
      have hend := selectorVertex_eq_sink_at_length B x sel hsel
      rw [List.get_ofFn]
      simpa only [V, Fin.val_cast] using hend
    edge_step := by
      intro i
      have hi : i.val < L := by simpa using i.isLt
      let j : Fin L := ⟨i.val, hi⟩
      obtain ⟨htail, hd, hhead⟩ := selectorVertex_step B x sel hsel j.val (by simp [L])
      have hdart : (List.ofFn E).get i = sel (selectorVertex B sel j.val) := by
        simp [E, j]
      have hvertex : (List.ofFn V).get ⟨i.val, by simp; omega⟩ = selectorVertex B sel j.val := by
        rw [List.get_ofFn]
        simp only [V, Fin.val_cast, j]
      have hvertex' : (List.ofFn V).get ⟨i.val + 1, by simp; omega⟩ =
          selectorVertex B sel (j.val + 1) := by
        rw [List.get_ofFn]
        simp only [V, Fin.val_cast, j]
      rw [hdart, hvertex, hvertex']
      exact ⟨B.noMissingDarts _, (IsXDPGeodesicDart.present_tail B x _ hd).2,
        htail.symm, hhead.symm⟩
  }
  refine ⟨P, ?_, ?_⟩
  · cases x with
    | ldp =>
        change IsLDPGeodesicBase B P
        apply (isLDPGeodesicBase_iff_length_eq B P).2
        rfl
    | sdp =>
        change IsSDPGeodesicBase B P
        apply (isSDPGeodesicBase_iff_length_eq B P).2
        rfl
  · intro i
    have hiL : i.val < L := by simp [L]
    have hidx : i.val < (List.ofFn E).length := by simpa using hiL
    change (List.ofFn E).get ⟨i.val, hidx⟩ = sel (selectorVertex B sel i.val)
    rw [List.get_ofFn]
    simp only [E, Fin.val_cast]

/-! The distance-sum converses below choose extremal simple paths from the
source to a vertex and from that vertex to the sink, then join them using the
finite acyclic path split/join helper. They support the leftmost-geodesic cut -/

private theorem path_end_not_mem_take_selector
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) : t ∉ P.vertices.take n := by
  intro ht
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  have hi_lt : i.val < n := by
    have h := i.isLt
    simp [List.length_take, P.vertices_length] at h
    omega
  let iP : Fin P.vertices.length := ⟨i.val, by
    have hlen := P.vertices_length
    omega⟩
  let nP : Fin P.vertices.length := ⟨n, by
    have hlen := P.vertices_length
    omega⟩
  have htake : (P.vertices.take n).get i = P.vertices.get iP := by
    change (P.vertices.take n)[i.val]'i.isLt = P.vertices[i.val]'(by
      have hlen := P.vertices_length
      omega)
    exact (List.getElem_take' (xs := P.vertices) (i := i.val) (j := n)
      (by have hlen := P.vertices_length; omega) hi_lt).symm
  have hEq : P.vertices.get iP = P.vertices.get nP := by
    calc
      P.vertices.get iP = (P.vertices.take n).get i := htake.symm
      _ = t := hi
      _ = P.vertices.get nP := P.end_vertex.symm
  have hfin := P.vertices_nodup.get_inj_iff.mp hEq
  have hval := congrArg Fin.val hfin
  have : i.val = n := by simpa [iP, nP] using hval
  omega

private theorem exists_simplePath_concat_at_vertex
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n)
    (Q : SimpleDirectedDartPath M x t m) :
    ∃ R : SimpleDirectedDartPath M s t (n + m), x ∈ R.vertices := by
  have hcross : ∀ a ∈ P.vertices.take n, ∀ b ∈ Q.vertices, a ≠ b := by
    intro a ha b hb hab
    have haP : a ∈ P.vertices := List.mem_of_mem_take ha
    have hbP : a ∈ Q.vertices := hab ▸ hb
    have hax : a = x := path_common_vertex_eq_join M hacyclic P Q haP hbP
    have hxmem : x ∈ P.vertices.take n := hax ▸ ha
    exact path_end_not_mem_take_selector M P hxmem
  let R : SimpleDirectedDartPath M s t (n + m) := {
    darts := P.darts ++ Q.darts
    vertices := P.vertices.take n ++ Q.vertices
    darts_length := by
      simp only [List.length_append, P.darts_length, Q.darts_length]
    vertices_length := by
      simp only [List.length_append, List.length_take, P.vertices_length,
        Q.vertices_length]
      omega
    vertices_nodup := by
      rw [List.nodup_append]
      exact ⟨P.vertices_nodup.take, Q.vertices_nodup, hcross⟩
    start_vertex := by
      by_cases hn : n = 0
      · subst n
        have hsx : s = x := by
          have hstart : P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ = s := by
            simpa using P.start_vertex
          have hend : P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ = x := by
            simpa using P.end_vertex
          exact hstart.symm.trans hend
        have hstart : Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ = x :=
          Q.start_vertex
        change (P.vertices.take 0 ++ Q.vertices).get ⟨0, by
          simp [Q.vertices_length]⟩ = s
        simpa [List.get_eq_getElem] using hstart.trans hsx.symm
      · have htakeLen : (P.vertices.take n).length = n := by
          simp [List.length_take, P.vertices_length]
        have hzero : 0 < (P.vertices.take n).length := by omega
        have hstart : (P.vertices.take n).get ⟨0, hzero⟩ = s := by
          change (P.vertices.take n)[0]'hzero = s
          exact (List.getElem_take' (xs := P.vertices) (i := 0) (j := n)
            (by rw [P.vertices_length]; omega) (by omega)).symm.trans
            (by simpa using P.start_vertex)
        change (P.vertices.take n ++ Q.vertices)[0]'(by
          simp [List.length_append, htakeLen, Q.vertices_length]) = s
        rw [List.getElem_append_left hzero]
        exact hstart
    end_vertex := by
      have htakeLen : (P.vertices.take n).length = n := by
        simp [List.length_take, P.vertices_length]
      have hidx : n + m - (P.vertices.take n).length = m := by omega
      change (P.vertices.take n ++ Q.vertices)[n + m]'(by
        simp [List.length_append, htakeLen, Q.vertices_length]) = t
      rw [List.getElem_append_right (by omega)]
      simp only [hidx]
      exact Q.end_vertex
    edge_step := by
      intro i
      have hiBound : i.val < n + m := by
        have h := i.isLt
        simp only [List.length_append, P.darts_length, Q.darts_length] at h
        omega
      by_cases hin : i.val < n
      · let jD : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hin⟩
        let jV0 : Fin (P.vertices.take n).length := ⟨i.val, by
          simp [List.length_take, P.vertices_length]
          omega⟩
        let jV0P : Fin P.vertices.length := ⟨i.val, by
          rw [P.vertices_length]
          omega⟩
        let jV1 : Fin P.vertices.length := ⟨i.val + 1, by
          rw [P.vertices_length]
          omega⟩
        have hD : (P.darts ++ Q.darts).get i = P.darts.get jD := by
          change (P.darts ++ Q.darts)[i.val]'i.isLt = P.darts[i.val]'jD.isLt
          exact List.getElem_append_left (by rw [P.darts_length]; exact hin)
        have hV0 : (P.vertices.take n ++ Q.vertices).get ⟨i.val, by
            simp [List.length_append, List.length_take, P.vertices_length,
              Q.vertices_length]
            omega⟩ = (P.vertices.take n).get jV0 := by
          change (P.vertices.take n ++ Q.vertices)[i.val]'_ =
            (P.vertices.take n)[i.val]'jV0.isLt
          exact List.getElem_append_left jV0.isLt
        have hV1 : (P.vertices.take n ++ Q.vertices).get ⟨i.val + 1, by
            simp [List.length_append, List.length_take, P.vertices_length,
              Q.vertices_length]
            omega⟩ = P.vertices.get jV1 := by
          by_cases hlt : i.val + 1 < n
          · change (P.vertices.take n ++ Q.vertices)[i.val + 1]'_ =
              P.vertices[i.val + 1]'jV1.isLt
            rw [List.getElem_append_left (by
              simp [List.length_take, P.vertices_length]
              omega)]
            exact (List.getElem_take' (xs := P.vertices) (i := i.val + 1)
              (j := n) (by rw [P.vertices_length]; omega) hlt).symm
          · have hieq : i.val + 1 = n := by omega
            have htakeLen : (P.vertices.take n).length = n := by
              simp [List.length_take, P.vertices_length]
            have hjoin : (P.vertices.take n ++ Q.vertices)[n]'(by
                simp [List.length_append, htakeLen, Q.vertices_length]) =
                P.vertices[n]'(by rw [P.vertices_length]; omega) := by
              rw [List.getElem_append_right (by omega)]
              have hidx : n - (P.vertices.take n).length = 0 := by omega
              simp only [hidx]
              have hq : Q.vertices[0]'(by rw [Q.vertices_length]; omega) = x := by
                simpa using Q.start_vertex
              have hp : P.vertices[n]'(by rw [P.vertices_length]; omega) = x := by
                simpa using P.end_vertex
              exact hq.trans hp.symm
            simpa [hieq, jV1] using hjoin
        rw [hD, hV0, hV1]
        have hV0' : (P.vertices.take n).get jV0 = P.vertices.get jV0P := by
          change (P.vertices.take n)[i.val]'jV0.isLt = P.vertices[i.val]'jV0P.isLt
          exact (List.getElem_take' (xs := P.vertices) (i := i.val) (j := n)
            (by rw [P.vertices_length]; omega) (by omega)).symm
        rw [hV0']
        simpa [jD, jV0P, jV1] using P.edge_step jD
      · let k : ℕ := i.val - n
        have hk : k < m := by dsimp [k]; omega
        let jD : Fin Q.darts.length := ⟨k, by rw [Q.darts_length]; exact hk⟩
        let jV0 : Fin Q.vertices.length := ⟨k, by
          rw [Q.vertices_length]
          omega⟩
        let jV1 : Fin Q.vertices.length := ⟨k + 1, by
          rw [Q.vertices_length]
          omega⟩
        have hD : (P.darts ++ Q.darts).get i = Q.darts.get jD := by
          change (P.darts ++ Q.darts)[i.val]'i.isLt = Q.darts[k]'jD.isLt
          rw [List.getElem_append_right (by rw [P.darts_length]; omega)]
          have hidx : i.val - P.darts.length = k := by
            rw [P.darts_length]
          simp only [hidx]
        have hV0 : (P.vertices.take n ++ Q.vertices).get ⟨i.val, by
            simp [List.length_append, List.length_take, P.vertices_length,
              Q.vertices_length]
            omega⟩ = Q.vertices.get jV0 := by
          change (P.vertices.take n ++ Q.vertices)[i.val]'_ = Q.vertices[k]'jV0.isLt
          rw [List.getElem_append_right (by
            simp [List.length_take, P.vertices_length]
            omega)]
          have hidx : i.val - (P.vertices.take n).length = k := by
            simp [List.length_take, P.vertices_length]
            dsimp [k]
          simp only [hidx]
        have hV1 : (P.vertices.take n ++ Q.vertices).get ⟨i.val + 1, by
            simp [List.length_append, List.length_take, P.vertices_length,
              Q.vertices_length]
            omega⟩ = Q.vertices.get jV1 := by
          change (P.vertices.take n ++ Q.vertices)[i.val + 1]'_ =
            Q.vertices[k + 1]'jV1.isLt
          rw [List.getElem_append_right (by
            simp [List.length_take, P.vertices_length]
            omega)]
          have hidx : i.val + 1 - (P.vertices.take n).length = k + 1 := by
            simp [List.length_take, P.vertices_length]
            dsimp [k]
            omega
          simp only [hidx]
        rw [hD, hV0, hV1]
        exact Q.edge_step jD
  }
  have hjoin : R.vertices.get ⟨n, by
      simp [R, List.length_append, List.length_take, P.vertices_length,
        Q.vertices_length]⟩ = x := by
    have htakeLen : (P.vertices.take n).length = n := by
      simp [List.length_take, P.vertices_length]
    change (P.vertices.take n ++ Q.vertices)[n]'_ = x
    rw [List.getElem_append_right (by omega)]
    simp only [show n - (P.vertices.take n).length = 0 by omega]
    simpa using Q.start_vertex
  exact ⟨R, List.mem_iff_get.mpr ⟨⟨n, by
    have hlen := R.vertices_length
    omega⟩, hjoin⟩⟩

/-- A vertex whose longest source and sink distances sum to the LDP length
lies on an LDP geodesic (`lem-lr-ind`, -/
theorem exists_LDPGeodesic_through_vertex_of_distance_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hsum : ldpSourceDistanceNatBase B v + ldpSinkDistanceNatBase B v =
      ldpLengthBase B) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsLDPGeodesicBase B P ∧ v ∈ P.vertices := by
  let n := ldpSourceDistanceNatBase B v
  let m := ldpSinkDistanceNatBase B v
  have hn : n ∈ sourceVertexPathLengthsBase B v := by
    dsimp [n, ldpSourceDistanceNatBase]
    exact Finset.max'_mem _ _
  have hm : m ∈ vertexSinkPathLengthsBase B v := by
    dsimp [m, ldpSinkDistanceNatBase]
    exact Finset.max'_mem _ _
  obtain ⟨P, _⟩ := (mem_sourceVertexPathLengthsBase B v n).mp hn
  obtain ⟨Q, _⟩ := (mem_vertexSinkPathLengthsBase B v m).mp hm
  obtain ⟨R, hmem⟩ := exists_simplePath_concat_at_vertex B.map B.acyclic P Q
  have hlen : n + m = ldpLengthBase B := by simpa [n, m] using hsum
  have hgeo : IsLDPGeodesicBase B R := by
    apply (isLDPGeodesicBase_iff_length_eq B R).mpr
    exact hlen
  exact ⟨n + m, R, hgeo, hmem⟩

/-- A vertex whose shortest source and sink distances sum to the SDP length
lies on an SDP geodesic (`lem-lr-ind`, -/
theorem exists_SDPGeodesic_through_vertex_of_distance_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map)
    (hsum : sdpSourceDistanceNatBase B v + sdpSinkDistanceNatBase B v =
      sdpLengthBase B) :
    ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsSDPGeodesicBase B P ∧ v ∈ P.vertices := by
  let n := sdpSourceDistanceNatBase B v
  let m := sdpSinkDistanceNatBase B v
  have hn : n ∈ sourceVertexPathLengthsBase B v := by
    dsimp [n, sdpSourceDistanceNatBase]
    exact Finset.min'_mem _ _
  have hm : m ∈ vertexSinkPathLengthsBase B v := by
    dsimp [m, sdpSinkDistanceNatBase]
    exact Finset.min'_mem _ _
  obtain ⟨P, _⟩ := (mem_sourceVertexPathLengthsBase B v n).mp hn
  obtain ⟨Q, _⟩ := (mem_vertexSinkPathLengthsBase B v m).mp hm
  obtain ⟨R, hmem⟩ := exists_simplePath_concat_at_vertex B.map B.acyclic P Q
  have hlen : n + m = sdpLengthBase B := by simpa [n, m] using hsum
  have hgeo : IsSDPGeodesicBase B R := by
    apply (isSDPGeodesicBase_iff_length_eq B R).mpr
    exact hlen
  exact ⟨n + m, R, hgeo, hmem⟩

private noncomputable def chooseXDPGeodesicDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) : D := by
  classical
  exact if h : ∃ d, dartTailVertex B.map d = v ∧ IsXDPGeodesicDart B x d then
    Classical.choose h
  else Classical.choose (exists_outgoingXDPGeodesicDart_at_source B x)

private theorem chooseXDPGeodesicDart_spec
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (h : ∃ d, dartTailVertex B.map d = v ∧ IsXDPGeodesicDart B x d) :
    dartTailVertex B.map (chooseXDPGeodesicDart B x v) = v ∧
      IsXDPGeodesicDart B x (chooseXDPGeodesicDart B x v) := by
  classical
  unfold chooseXDPGeodesicDart
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- There is a selector choosing an outgoing XDP-geodesic dart at every
non-sink vertex on an XDP geodesic (`lem-lr-ind`, -/
theorem exists_XDPGeodesicDart_selector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ sel : MapVertex B.map → D,
      ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
        IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
        dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v) := by
  let sel : MapVertex B.map → D := fun v => chooseXDPGeodesicDart B x v
  refine ⟨sel, ?_⟩
  intro v hv hvs
  apply chooseXDPGeodesicDart_spec
  exact exists_outgoingXDPGeodesicDart_of_geodesic_vertex B x hv hvs

/-- Unconditionally, an XDP geodesic can be built by iterating a chosen
outgoing geodesic dart at each non-sink geodesic vertex -/
theorem exists_selector_XDPGeodesic_path_unconditionally
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ sel : MapVertex B.map → D,
      ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
        IsXDPGeodesicBase B x P ∧
          ∀ i : Fin (xdpLengthBase B x),
            P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ =
              sel (selectorVertex B sel i.val) := by
  obtain ⟨sel, hsel⟩ := exists_XDPGeodesicDart_selector B x
  obtain ⟨P, hP, hget⟩ := exists_selector_XDPGeodesic_path B x sel hsel
  exact ⟨sel, P, hP, hget⟩

end DirectedDistances.PlanarMap
