module

public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallFramed
import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem

noncomputable section

public section
namespace DirectedDistances.PlanarMap

open Equiv CombinatorialMap

private def ballVertexToAmbient (M : RootedLocallyFinitePlanarMap)
    (s : ℕ) (hs : 0 < s) :
    VertexQuotient (rootedLocallyFiniteFramedBall M s hs).map.toCombinatorialMap →
      RootedLocallyFiniteVertex M.D M.rot := by
  classical
  exact Quotient.map Subtype.val (fun x y h =>
    (rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap s x y).1 h)

private theorem ambientRadius_mono (M : RootedLocallyFiniteMap) {r s : ℕ}
    (hrs : r ≤ s) {v} (h : rootedLocallyFiniteWithinRadius M r v) :
    rootedLocallyFiniteWithinRadius M s v :=
  (mem_rootedLocallyFiniteRadiusVertices M s v).1
    (rootedLocallyFiniteRadiusVertices_mono M hrs
      ((mem_rootedLocallyFiniteRadiusVertices M r v).2 h))

private theorem ballPath_toAmbient (M : RootedLocallyFinitePlanarMap)
    (s : ℕ) (hs : 0 < s) {v w n}
    (h : framedBallGeometricPath (rootedLocallyFiniteFramedBall M s hs) v n w) :
    rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap 0
      (ballVertexToAmbient M s hs v) →
    rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap n
      (ballVertexToAmbient M s hs w) := by
  intro hv
  induction h with
  | nil => exact hv
  | snoc hp he ih =>
    obtain ⟨d, hd, hd'⟩ := he
    apply rootedLocallyFiniteWithinRadius.edge ih
    exact ⟨d.1, congrArg (ballVertexToAmbient M s hs) hd,
      congrArg (ballVertexToAmbient M s hs) hd'⟩

private theorem ambientRadius_toBall (M : RootedLocallyFinitePlanarMap)
    (s : ℕ) (hs : 0 < s) {n v}
    (h : rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap n v)
    (hn : n ≤ s)
    (d : (rootedLocallyFiniteFramedBall M s hs).D)
    (hd : rootedLocallyFiniteVertexClassOf M.toRootedLocallyFiniteMap d.1 = v) :
    framedBallWithinRadius (rootedLocallyFiniteFramedBall M s hs) n
      (vertexClass _ (rootedLocallyFiniteFramedBall M s hs).rootDart)
      (vertexClass _ d) := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let B := rootedLocallyFiniteFramedBall M s hs
  induction h generalizing d with
  | root =>
    have hc : B.map.rot.SameCycle B.rootDart d :=
      (rootedLocallyFiniteBall_rot_sameCycle_iff A s _ _).2
        (Quotient.exact hd).symm
    change framedBallWithinRadius B 0 (vertexClass _ B.rootDart) (vertexClass _ d)
    have heq : vertexClass B.map.toCombinatorialMap B.rootDart =
        vertexClass B.map.toCombinatorialMap d := Quotient.sound hc
    exact ⟨0, Nat.le_refl _, heq ▸ framedBallGeometricPath.nil _⟩
  | @stay n v hp ih =>
    obtain ⟨k, hk, hpath⟩ := ih (by omega) d hd
    exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hpath⟩
  | @edge n v w hp he ih =>
    obtain ⟨e, hev, hew⟩ := he
    have heS : e ∈ rootedLocallyFiniteBallDarts A s := by
      rw [mem_rootedLocallyFiniteBallDarts]
      constructor
      · exact (mem_rootedLocallyFiniteRadiusVertices A s _).2
          (ambientRadius_mono A (by omega) (hev.symm ▸ hp))
      · exact (mem_rootedLocallyFiniteRadiusVertices A s _).2
          (ambientRadius_mono A hn
            (rootedLocallyFiniteWithinRadius.edge hp ⟨e, hev, rfl⟩))
    let e' : B.D := ⟨e, heS⟩
    obtain ⟨k, hk, hpath⟩ := ih (by omega) e' hev
    have hc : B.map.rot.SameCycle (B.map.edgeInv e') d :=
      (rootedLocallyFiniteBall_rot_sameCycle_iff A s _ _).2
        (Quotient.exact (hew.trans hd.symm))
    refine ⟨k + 1, Nat.succ_le_succ hk, .snoc hpath ?_⟩
    exact ⟨e', rfl, Quotient.sound hc⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Intrinsic and ambient root distance agree up to the enclosing positive radius. -/
theorem rootedLocallyFiniteFramedBall_withinRadius_iff
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hs : 0 < s) (hrs : r ≤ s)
    (d : (rootedLocallyFiniteFramedBall M s hs).D) :
    framedBallWithinRadius (rootedLocallyFiniteFramedBall M s hs) r
        (vertexClass _ (rootedLocallyFiniteFramedBall M s hs).rootDart)
        (vertexClass _ d) ↔
      rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap r
        (rootedLocallyFiniteVertexClassOf M.toRootedLocallyFiniteMap d.1) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ambientRadius_mono M.toRootedLocallyFiniteMap hn
      (ballPath_toAmbient M s hs hp .root)
  · intro h
    exact ambientRadius_toBall M s hs h hrs d rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Every path of length at most r stays in the enclosing s-ball, so intrinsic
radius restriction recovers exactly the ambient r-ball dart set. -/
theorem rootedLocallyFiniteFramedBallRadiusExact_proved
    (M : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    rootedLocallyFiniteFramedBallRadiusExact M hr hrs := by
  classical
  unfold rootedLocallyFiniteFramedBallRadiusExact
  let B := rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)
  have hnest (z : {d : M.D //
      d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap s}) :
      z ∈ rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s ↔
        rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap r
            (rootedLocallyFiniteVertexClassOf M.toRootedLocallyFiniteMap z.1) ∧
          rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap r
            (rootedLocallyFiniteVertexClassOf M.toRootedLocallyFiniteMap
              (M.edgeInv z.1)) := by
    simp only [rootedLocallyFiniteNestedBallDarts, firstReturnSubset,
      Finset.mem_filter, Finset.mem_univ, true_and, mem_rootedLocallyFiniteBallDarts,
      mem_rootedLocallyFiniteRadiusVertices]
  apply Finset.ext
  intro d
  exact (framedBallRadiusDarts_mem_iff B r d).trans
    ((and_congr
      (rootedLocallyFiniteFramedBall_withinRadius_iff M (hr.trans_le hrs) hrs d)
      (rootedLocallyFiniteFramedBall_withinRadius_iff M (hr.trans_le hrs) hrs
        (B.map.edgeInv d))).trans (hnest d).symm)

private theorem nestedDarts_iso_iff
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs)))
    (d : (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)).D) :
    d ∈ rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s ↔
      I.mapIso.toEquiv d ∈
        rootedLocallyFiniteNestedBallDarts N.toRootedLocallyFiniteMap r s := by
  have hM := rootedLocallyFiniteFramedBallRadiusExact_proved M hr hrs
  have hN := rootedLocallyFiniteFramedBallRadiusExact_proved N hr hrs
  exact (Iff.of_eq (congrArg (fun S => d ∈ S) hM)).symm.trans
    ((framedBallRadiusDarts_mem_iso_iff I r d).symm.trans
      (Iff.of_eq (congrArg (fun S => I.mapIso.toEquiv d ∈ S) hN)))

private def nestedDartsIsoEquiv
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs))) :
    (rootedLocallyFiniteNestedFramedBall M hr hrs).D ≃
      (rootedLocallyFiniteNestedFramedBall N hr hrs).D :=
  I.mapIso.toEquiv.subtypeEquiv (nestedDarts_iso_iff M N hr hrs I)

private theorem iso_face_comm {B C : FramedBall} (e : B.D ≃ C.D)
    (hr : ∀ d, e (B.map.rot d) = C.map.rot (e d))
    (he : ∀ d, e (B.map.edgeInv d) = C.map.edgeInv (e d)) (d : B.D) :
    e (B.map.faceSucc d) = C.map.faceSucc (e d) := by
  change e (B.map.rot.symm (B.map.edgeInv d)) =
    C.map.rot.symm (C.map.edgeInv (e d))
  apply C.map.rot.injective
  rw [← hr, B.map.rot.apply_symm_apply, C.map.rot.apply_symm_apply, he]

private theorem iso_other_none_iff {B C : FramedBall} (I : FramedBallIso B C) :
    B.frameOtherDart = none ↔ C.frameOtherDart = none := by
  cases hb : B.frameOtherDart <;> cases hc : C.frameOtherDart
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rcases I.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
    · have hf := h.2
      rw [hc] at hf
      cases hf
    · simp only [hb, Option.map_none, reduceCtorEq] at hx
  · rcases I.frameOther_comm with h | ⟨x, y, hx, hy, hxy⟩
    · have hf := h.1
      simp only [hb, Option.map_some, reduceCtorEq] at hf
    · simp only [hc, reduceCtorEq] at hy
  · simp only [reduceCtorEq]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
An isomorphism of enclosing balls restricts to the ambient nested radius sets.
Only the existing framed-map data are claimed; original-face selection remains -/
private noncomputable def rootedLocallyFiniteNestedFramedBallIso_of_iso
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs))) :
    FramedBallIso (rootedLocallyFiniteNestedFramedBall M hr hrs)
      (rootedLocallyFiniteNestedFramedBall N hr hrs) := by
  classical
  let A := rootedLocallyFiniteFramedBall M s (hr.trans_le hrs)
  let B := rootedLocallyFiniteFramedBall N s (hr.trans_le hrs)
  let X := rootedLocallyFiniteNestedFramedBall M hr hrs
  let Y := rootedLocallyFiniteNestedFramedBall N hr hrs
  let S := rootedLocallyFiniteNestedBallDarts M.toRootedLocallyFiniteMap r s
  let T := rootedLocallyFiniteNestedBallDarts N.toRootedLocallyFiniteMap r s
  let e : X.D ≃ Y.D := nestedDartsIsoEquiv M N hr hrs I
  have hrot (d : X.D) : e (X.map.rot d) = Y.map.rot (e d) := by
    apply Subtype.ext
    exact DirectedDistances.PaperProofs.Section3.cyclicFirstReturn_map_of_equiv
      A.map.rot B.map.rot S T I.mapIso.toEquiv
      (nestedDarts_iso_iff M N hr hrs I) I.mapIso.rot_comm
      (finitePermutationReturn A.map.rot S) (finitePermutationReturn B.map.rot T) d
  have hedge (d : X.D) : e (X.map.edgeInv d) = Y.map.edgeInv (e d) := by
    apply Subtype.ext
    exact I.mapIso.edgeInv_comm d.1
  have hface := framedBall_sameCycle_iff_of_equiv e X.map.faceSucc Y.map.faceSucc
    (iso_face_comm e hrot hedge)
  have houter : Y.map.faceSucc.SameCycle Y.map.outer (e X.map.outer) := by
    exact inducedCombinatorialMap_face_sameCycle_of_connected_planar
      B.map.toCombinatorialMap (N.ball_isPlanar s (hr.trans_le hrs)) T
      (rootedLocallyFiniteNestedBallDarts_edgeInv_closed N.toRootedLocallyFiniteMap r s)
      (rootedLocallyFiniteNestedBallCombinatorialMap_connected
        N.toRootedLocallyFiniteMap hr hrs)
      Y.map.outer (e X.map.outer)
      ((I.mapIso.outer_iff A.map.outer).2 Equiv.Perm.SameCycle.rfl)
  refine {
    mapIso := {
      toEquiv := e
      rot_comm := hrot
      edgeInv_comm := hedge
      missing_iff := fun d => I.mapIso.missing_iff d.1
      tail_iff := fun d => I.mapIso.tail_iff d.1
      outer_iff := ?_ }
    root_vertex := ?_
    frameEdge_comm := ?_
    frameOther_comm := ?_ }
  · intro d
    exact ⟨fun h => (hface _ _).2 (houter.symm.trans h),
      fun h => houter.trans ((hface _ _).1 h)⟩
  · exact (inducedCombinatorialMap_rot_sameCycle_iff B.map.toCombinatorialMap T
      (rootedLocallyFiniteNestedBallDarts_edgeInv_closed N.toRootedLocallyFiniteMap r s)
      (e X.rootDart) Y.rootDart).2 I.root_vertex
  · apply Subtype.ext
    exact I.frameEdge_comm
  · have hnone := iso_other_none_iff I
    have hstatus : M.frameOtherDart = none ↔ N.frameOtherDart = none := by
      simpa only [rootedLocallyFiniteFramedBall, Option.map_eq_none_iff] using hnone
    cases hm : M.frameOtherDart <;> cases hn : N.frameOtherDart
    · exact Or.inl ⟨by
        simp only [rootedLocallyFiniteNestedFramedBall,
          rootedLocallyFiniteFramedBall, hm, Option.map_none], by
        simp only [rootedLocallyFiniteNestedFramedBall,
          rootedLocallyFiniteFramedBall, hn, Option.map_none]⟩
    · have h := hstatus.mp hm
      simp only [hn, reduceCtorEq] at h
    · have h := hstatus.mpr hn
      simp only [hm, reduceCtorEq] at h
    · right
      refine ⟨e (X.map.edgeInv X.frameEdgeDart),
        Y.map.edgeInv Y.frameEdgeDart, ?_, ?_, ?_⟩
      · simp only [X, rootedLocallyFiniteNestedFramedBall,
          rootedLocallyFiniteFramedBall, hm, Option.map_some]
        rfl
      · simp only [Y, rootedLocallyFiniteNestedFramedBall,
          rootedLocallyFiniteFramedBall, hn, Option.map_some]
        rfl
      · have hf : e X.frameEdgeDart = Y.frameEdgeDart := by
          apply Subtype.ext
          exact I.frameEdge_comm
        rw [hedge, hf]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Every enclosing-ball isomorphism induces a smaller positive-radius isomorphism. -/
theorem rootedLocallyFiniteFramedBallIso_restrict_exists
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs))) :
    ∃ J : FramedBallIso (rootedLocallyFiniteFramedBall M r hr)
      (rootedLocallyFiniteFramedBall N r hr),
      ∀ d, (J.mapIso.toEquiv d).1 =
        (I.mapIso.toEquiv ⟨d.1,
          rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs d.2⟩).1 := by
  refine ⟨((rootedLocallyFiniteNestedFramedBallIso M hr hrs).symm.trans
    (rootedLocallyFiniteNestedFramedBallIso_of_iso M N hr hrs I)).trans
    (rootedLocallyFiniteNestedFramedBallIso N hr hrs), ?_⟩
  intro d
  rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
Select the proved restriction isomorphism, without any existence premise. -/
@[expose] noncomputable def rootedLocallyFiniteFramedBallIso_restrict
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs))) :
    FramedBallIso (rootedLocallyFiniteFramedBall M r hr)
      (rootedLocallyFiniteFramedBall N r hr) :=
  Classical.choose (rootedLocallyFiniteFramedBallIso_restrict_exists M N hr hrs I)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The selected smaller-ball isomorphism is the restriction of the supplied map -/
theorem rootedLocallyFiniteFramedBallIso_restrict_apply
    (M N : RootedLocallyFinitePlanarMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : FramedBallIso (rootedLocallyFiniteFramedBall M s (hr.trans_le hrs))
      (rootedLocallyFiniteFramedBall N s (hr.trans_le hrs)))
    (d : (rootedLocallyFiniteFramedBall M r hr).D) :
    ((rootedLocallyFiniteFramedBallIso_restrict M N hr hrs I).mapIso.toEquiv d).1 =
      (I.mapIso.toEquiv ⟨d.1,
        rootedLocallyFiniteBallDarts_mono M.toRootedLocallyFiniteMap hrs d.2⟩).1 :=
  Classical.choose_spec (rootedLocallyFiniteFramedBallIso_restrict_exists M N hr hrs I) d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology); not a paper result.
The provider's index r is source radius r+1, including index zero (radius one).
No source radius-zero convention is introduced. -/
theorem rootedLocallyFiniteFramedBallRestrictionCompatible_proved :
    rootedLocallyFiniteFramedBallRestrictionCompatible := by
  intro r M N h
  obtain ⟨I⟩ := Quotient.exact h
  exact Quotient.sound ⟨rootedLocallyFiniteFramedBallIso_restrict M N
    (Nat.succ_pos r) (Nat.le_succ (r + 1)) I⟩

end DirectedDistances.PlanarMap
end
end
