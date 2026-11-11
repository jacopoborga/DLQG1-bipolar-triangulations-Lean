/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section4.UIQBOTExternalFaceGeometry
public import DirectedDistances.PlanarMap.UIQBOTQuotientDartDrawingTransport

/-! # UIQBOT external-face geometry transport

Helpers toward Definition 3.2. The generic dart-carrier transport preserves
the complete piecewise-linear drawing data. The UIQBOT boundary-vertex bridge
is kept explicit below if it cannot be derived from the current map definitions. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap Filter

/-- Helper toward Definition 3.2: counterclockwise successor data transports
along a dart equivalence that preserves stars and initial directions. -/
private theorem ccwSuccessor_equiv
    {D D' : Type*} {star : Set D} {star' : Set D'}
    {dir : D → ℂ} {dir' : D' → ℂ} {d r : D} {d' r' : D'}
    (e : D ≃ D')
    (hstar : ∀ x, e x ∈ star' ↔ x ∈ star)
    (hdir : ∀ x, dir' (e x) = dir x)
    (hd : d' = e d) (hr : r' = e r)
    (h : CcwSuccessor star dir d r) : CcwSuccessor star' dir' d' r' := by
  have hset : star' = e '' star := by
    ext y
    constructor
    · intro hy
      have hy' : e (e.symm y) ∈ star' := by simpa using hy
      exact ⟨e.symm y, (hstar _).mp hy', e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hstar x).mpr hx
  rcases h with ⟨hfinite, hdmem, hrmem, hcase⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact hfinite.image e
  · rw [hset]
    exact ⟨d, hdmem, hd.symm⟩
  · rw [hset]
    exact ⟨r, hrmem, hr.symm⟩
  · rcases hcase with ⟨heq, hsingleton⟩ | ⟨hne, hmin⟩
    · left
      refine ⟨?_, ?_⟩
      · calc r' = e r := hr
          _ = e d := congrArg e heq
          _ = d' := hd.symm
      · ext y
        constructor
        · intro hy
          rw [hset] at hy
          rcases hy with ⟨x, hx, hxy⟩
          rw [hsingleton] at hx
          subst x
          exact hxy.symm.trans hd.symm
        · intro hy
          rw [hset]
          refine ⟨d, ?_, ?_⟩
          · rw [hsingleton]
            rfl
          · have hy' : y = d' := by simpa using hy
            exact hd.symm.trans hy'.symm
    · right
      refine ⟨?_, ?_⟩
      · intro heq
        apply hne
        apply e.injective
        calc e r = r' := hr.symm
          _ = d' := heq
          _ = e d := hd
      · intro f hf hfd
        rw [hset] at hf
        rcases hf with ⟨x, hx, hxf⟩
        have hxd : x ≠ d := by
          intro hxd
          apply hfd
          calc f = e x := hxf.symm
            _ = e d := congrArg e hxd
            _ = d' := hd.symm
        have hsource := hmin x hx hxd
        calc
          ccwTurn (dir' d') (dir' r') ≤ ccwTurn (dir' d') (dir' f) := by
            rw [hd, hr, ← hxf, hdir d, hdir r, hdir x]
            exact hsource

/-- Helper toward Definition 3.2: a PL drawing transports across an
equivalence of dart carriers that commutes with reversal, rotation and vertex
incidence. The drawing image and face point-sets are unchanged. -/
theorem plDrawing_transport
    {D D' V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : D' → D'} {rot' : Equiv.Perm D'} {vert' : D' → V}
    (e : D ≃ D')
    (hflip : ∀ d, flip' (e d) = e (flip d))
    (hrot : ∀ d, rot' (e d) = e (rot d))
    (hvert : ∀ d, vert' (e d) = vert d)
    (P : PLDrawing D V flip rot vert) :
    ∃ Q : PLDrawing D' V flip' rot' vert',
      Q.image = P.image ∧
      ∀ F : P.Face, ∃ F' : Q.Face,
        F'.val = F.val ∧
        ∀ d, Q.dartBorders (e d) F' ↔ P.dartBorders d F := by
  let Q : PLDrawing D' V flip' rot' vert' := {
    flip_involutive := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      calc
        flip' (flip' d') = flip' (flip' (e d)) := by rw [hd]
        _ = flip' (e (flip d)) := by rw [hflip]
        _ = e (flip (flip d)) := hflip _
        _ = e d := congrArg e (P.flip_involutive d)
        _ = d' := hd
    flip_ne := by
      intro d' h
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      have heq : e (flip d) = e d := by rw [← hflip, hd, h]
      exact P.flip_ne d (e.injective heq)
    vert_rotation := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      calc
        vert' (rot' d') = vert' (e (rot d)) := congrArg vert' (by rw [← hd, hrot])
        _ = vert (rot d) := hvert (rot d)
        _ = vert d := P.vert_rotation d
        _ = vert' (e d) := (hvert d).symm
        _ = vert' d' := congrArg vert' hd
    pos := P.pos
    pos_injective := P.pos_injective
    arc := fun d' => P.arc (e.symm d')
    arc_simple := fun d' => P.arc_simple (e.symm d')
    arc_length := fun d' => P.arc_length (e.symm d')
    arc_start := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change (P.arc (e.symm d')).start = P.pos (vert' d')
      rw [← hd, Equiv.symm_apply_apply, P.arc_start, ← hvert, hd]
    arc_finish := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change (P.arc (e.symm d')).finish = P.pos (vert' (flip' d'))
      rw [← hd, Equiv.symm_apply_apply, P.arc_finish, hflip, ← hvert]
    arc_flip := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      change P.arc (e.symm (flip' d')) = (P.arc d).reverse
      rw [← hd, hflip, e.symm_apply_apply, P.arc_flip]
    interior_disjoint := by
      intro d' e' hne hneflip
      let d := e.symm d'
      let f := e.symm e'
      have hd : e d = d' := e.apply_symm_apply d'
      have he : e f = e' := e.apply_symm_apply e'
      have hne' : f ≠ d := by
        intro h
        apply hne
        calc e' = e f := he.symm
          _ = e d := congrArg e h
          _ = d' := hd
      have hneflip' : f ≠ flip d := by
        intro h
        apply hneflip
        calc e' = e f := he.symm
          _ = e (flip d) := congrArg e h
          _ = flip' (e d) := (hflip d).symm
          _ = flip' d' := congrArg flip' hd
      simpa [d, f] using P.interior_disjoint d f hne' hneflip'
    interior_avoids_vertices := by
      intro d' v hz
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      exact P.interior_avoids_vertices d v (by simpa [d, hd] using hz)
    locally_finite := by
      intro K hK
      have hset : {d' | (K ∩ (P.arc (e.symm d')).image).Nonempty} =
          e '' {d | (K ∩ (P.arc d).image).Nonempty} := by
        ext d'
        constructor
        · intro hd'
          refine ⟨e.symm d', ?_, e.apply_symm_apply d'⟩
          simpa using hd'
        · rintro ⟨d, hd, rfl⟩
          simpa using hd
      rw [hset]
      exact (P.locally_finite K hK).image e
    initial_nonzero := fun d' => P.initial_nonzero (e.symm d')
    initial_arg_injective := by
      intro d' e' hv harg
      let d := e.symm d'
      let f := e.symm e'
      have hd : e d = d' := e.apply_symm_apply d'
      have he : e f = e' := e.apply_symm_apply e'
      have hv' : vert d = vert f := by
        calc vert d = vert' (e d) := (hvert d).symm
          _ = vert' d' := congrArg vert' hd
          _ = vert' e' := hv
          _ = vert' (e f) := congrArg vert' he.symm
          _ = vert f := hvert f
      have hdf : d = f := P.initial_arg_injective d f hv' harg
      calc d' = e d := hd.symm
        _ = e f := congrArg e hdf
        _ = e' := he
    rotation_agreement := by
      intro d'
      let d := e.symm d'
      have hd : e d = d' := e.apply_symm_apply d'
      have hr : rot' d' = e (rot d) := by rw [← hd, hrot]
      exact ccwSuccessor_equiv e
        (star := {x | vert x = vert d})
        (star' := {x | vert' x = vert' d'})
        (dir := fun x => (P.arc x).initialDirection)
        (dir' := fun x => (P.arc (e.symm x)).initialDirection)
        (d := d) (r := rot d) (d' := d') (r' := rot' d')
        (by
          intro x
          change vert' (e x) = vert' d' ↔ vert x = vert d
          rw [← hd, hvert x, hvert d])
        (by intro x; simp)
        hd.symm hr (P.rotation_agreement d)
  }
  have himage : Q.image = P.image := by
    ext z
    simp only [PLDrawing.image, Set.mem_union, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro (hz | ⟨d', hd⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨e.symm d', by simpa [Q] using hd⟩
    · rintro (hz | ⟨d, hd⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨e d, by simpa [Q] using hd⟩
  refine ⟨Q, himage, ?_⟩
  intro F
  obtain ⟨z, hz, hF⟩ := F.property
  have hzQ : z ∉ Q.image := by simpa [himage] using hz
  have hFQ : F.val = connectedComponentIn Q.imageᶜ z := by
    rw [hF, himage]
  let F' : Q.Face := ⟨F.val, z, hzQ, hFQ⟩
  refine ⟨F', rfl, ?_⟩
  intro d
  have hval : F'.val = F.val := rfl
  simp only [PLDrawing.dartBorders, Q, Equiv.symm_apply_apply, hval]

/-- Helper toward Definition 3.2: the canonical KMSW and UIQBOT dart
carriers are equivalent, with the quotient representative's bit adjustment. -/
noncomputable def uiqbotCanonicalBoundaryDartEquiv
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    ℕ × Bool ≃ (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool := by
  let P := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin P
  exact (uiqbotKMSWQuotientDartEquiv P iota).symm

/-- Helper toward Definition 3.2: the canonical dart equivalence commutes
with reversal on the two carrier conventions. -/
theorem uiqbotCanonicalBoundaryDartEquiv_flip
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    uiqbotCanonicalBoundaryDartEquiv w hfin (d.1, !d.2) =
      ((uiqbotCanonicalBoundaryDartEquiv w hfin d).1,
        !(uiqbotCanonicalBoundaryDartEquiv w hfin d).2) := by
  let P := uiqbotPresentationDrawing w hfin
  let iota := kmswGeometricEdgeEquiv w hfin P
  let f := uiqbotKMSWQuotientDartEquiv P iota
  apply f.injective
  simpa [uiqbotCanonicalBoundaryDartEquiv, P, iota, f] using
    (uiqbotKMSWQuotientDartEquiv_flip P iota
      (uiqbotCanonicalBoundaryDartEquiv w hfin d)).symm

/-- Helper toward Definition 3.2: conjugating the KMSW rotation along the
canonical dart equivalence gives the required rotation on UIQBOT darts. -/
theorem uiqbotCanonicalBoundaryDartEquiv_rotation
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    uiqbotTransportRotation (uiqbotCanonicalBoundaryDartEquiv w hfin).symm
      (kmswInfRot w hfin) (uiqbotCanonicalBoundaryDartEquiv w hfin d) =
        uiqbotCanonicalBoundaryDartEquiv w hfin (kmswInfRot w hfin d) := by
  simp [uiqbotTransportRotation]

/-- Helper toward Definition 3.2: representative-adjusted darts preserve
their initial vertex on the canonical UIQBOT map. -/
theorem uiqbotCanonicalBoundaryDartEquiv_initialVertex
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    boundaryDartInitial
        (uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin))
        (uiqbotCanonicalBoundaryDartEquiv w hfin d) = kmswLimitDartVertex w d := by
  let P := uiqbotPresentationDrawing w hfin
  let M0 := uiqbotPresentationDirectedMapX w hfin
  let M := uiqbotMapWithNoMissing M0
  let iota := kmswGeometricEdgeEquiv w hfin P
  let f := uiqbotKMSWQuotientDartEquiv P iota
  rcases d with ⟨k, b⟩
  let q := (uiqbotCanonicalBoundaryDartEquiv w hfin (k, b)).1
  let c := (uiqbotCanonicalBoundaryDartEquiv w hfin (k, b)).2
  have hqdef : q = iota k := by
    change ((uiqbotKMSWQuotientDartEquiv P iota).symm (k, b)).1 = iota k
    rfl
  have hcompat (n : ℕ) : M0.tail (iota n) = edgeWest w n ∧
      M0.head (iota n) = edgeEast w n := by
    have hiota : iota n = Quotient.mk P.edgeSetoid (n, false) :=
      kmswGeometricEdgeEquiv_apply w hfin P n
    have htail (q : P.GeometricEdge) :
        M0.tail q = (if !q.out.2 then kmswLimitDartVertex w q.out
          else kmswLimitDartVertex w (q.out.1, !q.out.2)) := by rfl
    have hhead (q : P.GeometricEdge) :
        M0.head q = (if !q.out.2 then kmswLimitDartVertex w (q.out.1, !q.out.2)
          else kmswLimitDartVertex w q.out) := by rfl
    rw [hiota, htail, hhead]
    obtain hout | hout := P.geometricEdge_out_mk (n, false)
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
    · rw [hout]
      simp [kmswLimitDartVertex, edgeWest, edgeEast]
  have htailq : M0.tail q = edgeWest w (iota.symm q) := by
    rw [← iota.apply_symm_apply q]
    simpa using (hcompat (iota.symm q)).1
  have hheadq : M0.head q = edgeEast w (iota.symm q) := by
    rw [← iota.apply_symm_apply q]
    simpa using (hcompat (iota.symm q)).2
  have hsrc : M0.src q = if M0.forward q then edgeWest w (iota.symm q)
      else edgeEast w (iota.symm q) := by
    by_cases hf : M0.forward q
    · simpa [DirectedPlaneMap.tail, hf] using htailq
    · simpa [DirectedPlaneMap.head, hf] using hheadq
  have htgt : M0.tgt q = if M0.forward q then edgeEast w (iota.symm q)
      else edgeWest w (iota.symm q) := by
    by_cases hf : M0.forward q
    · simpa [DirectedPlaneMap.head, hf] using hheadq
    · simpa [DirectedPlaneMap.tail, hf] using htailq
  have hqedge : iota.symm q = k := by
    rw [hqdef]
    exact iota.symm_apply_apply k
  have hcb : c = uiqbotQuotientDartBit q.out.2 b := by
    have hcdef : c = uiqbotQuotientDartBit (iota k).out.2 b := by
      change ((uiqbotKMSWQuotientDartEquiv P iota).symm (k, b)).2 =
        uiqbotQuotientDartBit (iota k).out.2 b
      rfl
    simpa [hqdef] using hcdef
  change boundaryDartInitial M (q, c) = kmswLimitDartVertex w (k, b)
  rw [boundaryDartInitial_eq]
  change (if c then M0.src q else M0.tgt q) = kmswLimitDartVertex w (k, b)
  rw [hsrc, htgt]
  cases hc : q.out.2 <;> cases b <;>
    simp [hcb, uiqbotQuotientDartBit, M0, uiqbotPresentationDirectedMapX,
      hqedge, hc, kmswLimitDartVertex, edgeWest, edgeEast]

/-- Helper toward Definition 3.2: the canonical dart carrier transport has
the reversal and boundary-vertex equations required by the source bridge. -/
theorem uiqbotCanonicalBoundaryDartTransport
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
    ∃ e : ℕ × Bool ≃ (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool,
      (∀ d, e (d.1, !d.2) = ((e d).1, !(e d).2)) ∧
      (∀ d, boundaryDartInitial M (e d) = kmswLimitDartVertex w d) := by
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  refine ⟨e, ?_, ?_⟩
  · intro d
    exact uiqbotCanonicalBoundaryDartEquiv_flip w hfin d
  · intro d
    exact uiqbotCanonicalBoundaryDartEquiv_initialVertex w hfin d

/-- Helper toward Definition 3.2: transport the KMSW unbounded face,
external-dart classification and geometric successor to the UIQBOT carrier. -/
theorem uiqbotCanonicalQuotientDrawing_externalFace
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    let e := uiqbotCanonicalBoundaryDartEquiv w hfin
    let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
    ∃ G : PLDrawing ((uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
        ℕ (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (uiqbotMapWithNoMissing
          (uiqbotPresentationDirectedMapX w hfin))),
      ∃ U : G.Face,
        G.IsUnbounded U ∧
        (∀ d, G.dartBorders d U ↔ limitExternalDart w (e.symm d)) ∧
        IsGeometricExternalFaceSucc G U
          (fun d => e (kmswInfFaceSucc w hfin (e.symm d))) := by
  let e := uiqbotCanonicalBoundaryDartEquiv w hfin
  let rot := uiqbotTransportRotation e.symm (kmswInfRot w hfin)
  let G₀ : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
      (kmswInfRot w hfin) (kmswLimitDartVertex w) :=
    uiqbotPresentationDrawing w hfin
  let M := uiqbotMapWithNoMissing (uiqbotPresentationDirectedMapX w hfin)
  obtain ⟨U₀, hUnbounded₀, _hUnique₀, hBorder₀, hSucc₀⟩ :=
    uiqbotKMSWPresentation_geometricExternalFaceSucc
      w hfin htrans hR hL0
  have hflip (d : ℕ × Bool) : ((e d).1, !(e d).2) =
      e (d.1, !d.2) := by
    exact (uiqbotCanonicalBoundaryDartEquiv_flip w hfin d).symm
  have hrotation (d : ℕ × Bool) : rot (e d) = e (kmswInfRot w hfin d) :=
    uiqbotCanonicalBoundaryDartEquiv_rotation w hfin d
  obtain ⟨G, _himage, hface⟩ := plDrawing_transport
    (D := ℕ × Bool)
    (D' := (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool)
    (V := ℕ)
    (flip := fun d : ℕ × Bool => (d.1, !d.2))
    (rot := kmswInfRot w hfin) (vert := kmswLimitDartVertex w)
    (flip' := fun d : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool =>
      (d.1, !d.2)) (rot' := rot) (vert' := boundaryDartInitial M)
    e hflip hrotation
    (uiqbotCanonicalBoundaryDartEquiv_initialVertex w hfin) G₀
  obtain ⟨U, hUval, hBorders⟩ := hface U₀
  have hUnbounded : G.IsUnbounded U := by
    intro R
    obtain ⟨z, hz, hr⟩ := hUnbounded₀ R
    exact ⟨z, hUval ▸ hz, hr⟩
  have hBorder (d : (uiqbotPresentationDrawing w hfin).GeometricEdge × Bool) :
      G.dartBorders d U ↔ limitExternalDart w (e.symm d) := by
    simpa only [Equiv.apply_symm_apply] using
      (hBorders (e.symm d)).trans (hBorder₀ (e.symm d))
  have hSucc : IsGeometricExternalFaceSucc G U
      (fun d => e (kmswInfFaceSucc w hfin (e.symm d))) := by
    refine ⟨hUnbounded, ?_⟩
    intro d hd
    let d₀ := e.symm d
    have hd₀ : G₀.dartBorders d₀ U₀ := by
      have hd' : G.dartBorders (e d₀) U := by simpa [d₀] using hd
      exact (hBorders d₀).mp hd'
    obtain ⟨hsucc, hnext⟩ := hSucc₀.2 d₀ hd₀
    refine ⟨?_, ?_⟩
    · change e (kmswInfFaceSucc w hfin d₀) = rot.symm (d.1, !d.2)
      rw [hsucc]
      have hflip' : (d.1, !d.2) = e (d₀.1, !d₀.2) := by
        have hd₀ : e d₀ = d := by
          dsimp [d₀]
          exact e.apply_symm_apply d
        calc
          (d.1, !d.2) = ((e d₀).1, !(e d₀).2) := by rw [← hd₀]
          _ = e (d₀.1, !d₀.2) := hflip d₀
      rw [hflip']
      simp [rot, uiqbotTransportRotation]
    · have hnext' : G.dartBorders (e (kmswInfFaceSucc w hfin d₀)) U :=
        (hBorders (kmswInfFaceSucc w hfin d₀)).2 hnext
      simpa [d₀] using hnext'
  exact ⟨G, U, hUnbounded, hBorder, hSucc⟩

end DirectedDistances.PaperProofs.Section4

end
