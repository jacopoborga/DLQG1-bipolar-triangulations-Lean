/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization10







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

private def stageBallForFaces (w : ℕ → Fin 3) (n : ℕ) : D39FiniteBall where
  D := StageDart (kmswStage w n).nextEdge
  map := kmswMap w n
  missing := (kmswStageDirectedMap w n).missing
  tail := (kmswStageDirectedMap w n).tail
  rootDart := (kmswRootedStage w n).root
  original := Set.univ
  original_closed := fun _ => Iff.rfl

private theorem stageBallForFaces_connected (w : ℕ → Fin 3) (n : ℕ) :
    ∀ d e : (stageBallForFaces w n).D, Relation.EqvGen
      (fun x y => (stageBallForFaces w n).map.rot x = y ∨
        (stageBallForFaces w n).map.edgeInv x = y) d e := by
  intro d e
  have h := kmswMap_isConnected w n d e
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    apply ih.trans
    rcases hbc with h | h | h | h
    · exact Relation.EqvGen.rel _ _ (Or.inl h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      exact Or.inl ((congrArg (kmswMap w n).rot h).trans
        ((kmswMap w n).rot.apply_symm_apply _))
    · exact Relation.EqvGen.rel _ _ (Or.inr h.symm)
    · apply Relation.EqvGen.symm
      apply Relation.EqvGen.rel
      exact Or.inr ((congrArg (kmswMap w n).edgeInv h).trans
        ((kmswMap w n).edgeInv.apply_symm_apply _))

private theorem triangle_sameCycle_iff {D : Type*} [Finite D]
    (f : Equiv.Perm D) (a b c : D) (hc : FaceSucc3Cycle f a b c) (d e : D)
    (hd : d = a ∨ d = b ∨ d = c) :
    f.SameCycle d e ↔ e = a ∨ e = b ∨ e = c := by
  have hab : f.SameCycle a b := ⟨1, by simpa only [zpow_one] using hc.1⟩
  have hbc : f.SameCycle b c := ⟨1, by simpa only [zpow_one] using hc.2.1⟩
  have had : f.SameCycle a d := by
    rcases hd with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact hab
    · exact hab.trans hbc
  constructor
  · intro hde
    obtain ⟨k, rfl⟩ := (had.trans hde).exists_nat_pow_eq
    clear hde
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with ha | hb | hd
      · exact Or.inr (Or.inl ((congrArg f ha).trans hc.1))
      · exact Or.inr (Or.inr ((congrArg f hb).trans hc.2.1))
      · exact Or.inl ((congrArg f hd).trans hc.2.2.1)
  · rintro (rfl | rfl | rfl)
    · exact had.symm
    · exact had.symm.trans hab
    · exact had.symm.trans (hab.trans hbc)

private theorem typed_triangle_mem (w : ℕ → Fin 3) (n : ℕ)
    (j : TriangleCreationTime w) (hj : j.val < n)
    (d : StageDart (kmswStage w n).nextEdge) :
    (d.1.val, d.2) ∈ stageTriangleDartList w j ↔
      d = stageTriangleDart₁ w n j hj ∨ d = stageTriangleDart₂ w n j hj ∨
        d = stageTriangleDart₃ w n j hj := by
  rcases d with ⟨⟨e, he⟩, b⟩
  simp [stageTriangleDart₁, stageTriangleDart₂, stageTriangleDart₃,
    stageTriangleDartAt, stageTriangleDartList, Prod.ext_iff]

/-- Helper toward Proposition 3.9: each nonexterior original face of
every exterior-certified finite drawing has exactly one chronological
triangle label, with an iff for all of its actual oriented bordering darts. -/
theorem uibotFiniteStage_nonexteriorFace_triangle
    {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n)
    (U : P.Face)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (F : P.Face) (hFU : F ≠ U) :
    ∃! k : TriangleCreationTime w, k.val < n ∧
      ∀ d : StageDart (kmswStage w n).nextEdge,
        P.dartBorders d F ↔ (d.1.val, d.2) ∈ stageTriangleDartList w k := by
  let B := stageBallForFaces w n
  have hv := kmswStageDrawing_vertex_surjective w n
  have hc := stageBallForFaces_connected w n
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart hv (kmswRootedStage w n).root F
  have hout : d ∉ stageOuterWord w n := by
    intro ho
    have ho' : (kmswStageDirectedMap w n).IsOuter d := by
      rw [kmswStage_isOuter_iff_boundary]
      have h := (stageOuterWord_mem_iff w n d).mp ho
      simpa only [List.mem_append, or_comm] using h
    exact hFU (P.dartBorders_face_unique d F U hd ((hborder d).mpr ho'))
  obtain ⟨k, ⟨hkn, hdk⟩, hkuniq⟩ := (stage_dart_partition w n d).resolve_left hout
  have hface (e : StageDart (kmswStage w n).nextEdge) :
      P.dartBorders e F ↔ (kmswMap w n).faceSucc.SameCycle d e := by
    have hdF : B.plDartFace (stageVertex w n) P hv d = F :=
      (B.plDartFace_eq_iff (stageVertex w n) P hv d F).mpr hd
    constructor
    · intro he
      apply B.plDartFace_sameCycle_of_eq (stageVertex w n) P hv hc d e
      exact hdF.trans ((B.plDartFace_eq_iff (stageVertex w n) P hv e F).mpr he).symm
    · intro he
      apply (B.plDartFace_eq_iff (stageVertex w n) P hv e F).mp
      exact (B.plDartFace_eq_of_sameCycle (stageVertex w n) P hv d e he).symm.trans hdF
  have hchar (e : StageDart (kmswStage w n).nextEdge) :
      P.dartBorders e F ↔ (e.1.val, e.2) ∈ stageTriangleDartList w k := by
    rw [hface, typed_triangle_mem w n k hkn e]
    exact triangle_sameCycle_iff _ _ _ _ (stageTriangle_isFace w k n hkn) d e
      ((typed_triangle_mem w n k hkn d).mp hdk)
  refine ⟨k, ⟨hkn, hchar⟩, ?_⟩
  intro k' hk'
  exact hkuniq k' ⟨hk'.1, (hk'.2 d).mp hd⟩

/-- Helper toward Proposition 3.9: every retained original finite face
has a unique chronological triangle label under exactly hwindow and hcap.
The statement identifies all bordering darts, not just a selected one. -/
theorem uibotFiniteRootWindow_retainedFace_triangle {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    ∃! k : TriangleCreationTime (finiteCodeExtend w), k.val < n - 1 ∧
      ∀ d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          (d.1.val, d.2) ∈ stageTriangleDartList (finiteCodeExtend w) k := by
  apply uibotFiniteStage_nonexteriorFace_triangle P U hborder
  intro he
  have he' : F = P.toPlaneGraphDrawingFaceEquiv.symm U :=
    (Equiv.eq_symm_apply _).mpr he
  exact uibotFiniteRootWindow_exterior_not_retained w j u P U hU hborder
    hwindow hcap (he' ▸ hF)

/-- Helper toward Proposition 3.9: the unique triangle of every retained
original finite face was created inside the agreeing centered window.
Both chronological bounds and the complete bordering-dart characterization
hold for every exterior-certified P. -/
theorem uibotFiniteRootWindow_retainedFace_triangle_in_window {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    ∃! k : TriangleCreationTime (finiteCodeExtend w),
      j.val - N ≤ k.val ∧ k.val < j.val - N + 2 * N ∧
      ∀ d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          (d.1.val, d.2) ∈ stageTriangleDartList (finiteCodeExtend w) k := by
  classical
  obtain ⟨hv, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hn : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  let S := kmswStageBallVertices (fun _ _ => True)
    (kmswStage (finiteCodeExtend w) (n - 1)) r
    (activeInitial (finiteCodeExtend w) j.val)
  have hfresh (v : ℕ) (hvm : v ∈ S) :
      (kmswStage (finiteCodeExtend w) (j.val - N)).nextVertex ≤ v := by
    change v ∈ kmswStageBallVertices _ _ _ _ at hvm
    rw [← uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap] at hvm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvm
    exact kmswWindowPatchVertexMap_fresh_for_every_prefix u (2 * N) a
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (hcap.1.2.1 a ha).1 (hcap.1.2.1 a ha).2 (finiteCodeExtend w) (j.val - N) hcode
  have hends (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge)
      (hd : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F)) :
      (kmswStage (finiteCodeExtend w) (n - 1)).west d.1.val ∈ S ∧
      (kmswStage (finiteCodeExtend w) (n - 1)).east d.1.val ∈ S := by
    obtain ⟨hs, ht⟩ := (uibotFiniteStage_face_retained_iff_borderEndpoints P U hU hborder
      j.val (by have := j.isLt; omega) r F).mp hF d hd
    rw [uibotFiniteStageExteriorBallVertices_iff] at hs ht
    rcases d with ⟨e, b⟩
    cases b
    · exact ⟨hs, ht⟩
    · exact ⟨ht, hs⟩
  have hedge (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge)
      (hd : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F)) :
      d.1.val < (kmswStage (finiteCodeExtend w) (j.val - N + 2 * N)).nextEdge := by
    obtain ⟨a, _, ha⟩ := (uibotFiniteRootWindow_rootBallEdges_bijOn w j u hwindow hcap).2.2
      ⟨d.1.isLt, hends d hd⟩
    exact ha ▸ (kmswWindowFreshSetEdgeMap (finiteCodeExtend w) (j.val - N) (2 * N) a).isLt
  obtain ⟨k, ⟨hkn, hchar⟩, hkuniq⟩ :=
    uibotFiniteRootWindow_retainedFace_triangle w j u P U hU hborder hwindow hcap F hF
  have hklo : j.val - N ≤ k.val := by
    by_contra hnot
    have hks : k.val + 1 ≤ j.val - N := by omega
    let d := stageTriangleDart₁ (finiteCodeExtend w) (n - 1) k hkn
    have hdm : (d.1.val, d.2) ∈ stageTriangleDartList (finiteCodeExtend w) k := by
      simp only [d, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
        List.mem_cons, List.not_mem_nil, or_false, true_or]
    have hds : d.1.val < (kmswStage (finiteCodeExtend w) (j.val - N)).nextEdge :=
      (stageTriangleDartList_lt (finiteCodeExtend w) (k.val + 1) k
        (Nat.lt_succ_self _) _ hdm).trans_le (kmswStage_nextEdge_mono _ hks)
    have hnew := hfresh _ (hends d ((hchar d).mpr hdm)).1
    have hold := (kmswStage_endpoints_lt_nextVertex (finiteCodeExtend w) (j.val - N)
      d.1.val hds).1
    rw [(kmswStage_endpoints_stable (finiteCodeExtend w)
      (show j.val - N ≤ n - 1 by omega) hds).1] at hnew
    omega
  have hkhi : k.val < j.val - N + 2 * N := by
    have hnew : ((kmswStage (finiteCodeExtend w) k.val).nextEdge, true) ∈
        stageTriangleDartList (finiteCodeExtend w) k := by
      by_cases hc : finiteCodeExtend w k.val = 0
      · cases hUL : (kmswStage (finiteCodeExtend w) k.val).UL.dropLast.reverse <;>
          simp [stageTriangleDartList, stageTriangleDartTriple, hc, hUL]
      · simp [stageTriangleDartList, stageTriangleDartTriple, hc]
    let d := stageTriangleDartAt (finiteCodeExtend w) (n - 1) k hkn _ hnew
    have hd : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) :=
      (hchar d).mpr hnew
    have he := hedge d hd
    change (kmswStage (finiteCodeExtend w) k.val).nextEdge < _ at he
    by_contra hnot
    have hm := kmswStage_nextEdge_mono (finiteCodeExtend w)
      (show j.val - N + 2 * N ≤ k.val by omega)
    omega
  refine ⟨k, ⟨hklo, hkhi, hchar⟩, ?_⟩
  intro k' hk'
  exact hkuniq k' ⟨lt_of_lt_of_le hk'.2.1 hn, hk'.2.2⟩

private theorem window_triangle_mem_iff (w u : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i)
    (q : TriangleCreationTime u) (hq : q.val < m)
    (hc : w (s + q.val) = 0 ∨ w (s + q.val) = 1) (d : ℕ × Bool) :
    d ∈ stageTriangleDartList w ⟨s + q.val, hc⟩ ↔
      ∃ a, a ∈ stageTriangleDartList u q ∧
        (kmswWindowEdgeMapInf w s a.1, a.2) = d := by
  have hs : kmswStage (fun i => w (s + i)) q.val = kmswStage u q.val :=
    kmswStage_congr (fun i hi => hcode i (hi.trans hq))
  have hsfull : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hl : stageTriangleDartList (fun i => w (s + i)) ⟨q.val, hc⟩ =
      stageTriangleDartList u q := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, hs, hcode q.val hq]
  have hr := kmswWindowPatchData_triangle_rotated w s m q.val hq hc
  rw [hl] at hr
  have hm (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList u q) :
      ((kmswWindowPatchData w s m).φ a.1, a.2) =
        (kmswWindowEdgeMapInf w s a.1, a.2) := by
    apply Prod.ext
    · symm
      apply kmswWindowEdgeMapInf_eq_stage
      rw [hsfull]
      exact stageTriangleDartList_lt u m q hq a ha
    · rfl
  constructor
  · intro hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (hr.mem_iff.mpr hd)
    exact ⟨a, ha, (hm a ha).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact hr.mem_iff.mp (List.mem_map.mpr ⟨a, ha, (hm a ha).trans he⟩)

/-- Helper toward Proposition 3.9: every retained original finite face
has a unique triangle label in the centered window's own code. Its actual
bordering darts are exactly the infinite-window images of that triple. -/
theorem uibotFiniteRootWindow_retainedFace_windowTriangle {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    ∃! q : TriangleCreationTime u, q.val < 2 * N ∧
      ∀ d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          ∃ a, a ∈ stageTriangleDartList u q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2) := by
  obtain ⟨_, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  obtain ⟨k, ⟨hlo, hhi, hk⟩, huniq⟩ :=
    uibotFiniteRootWindow_retainedFace_triangle_in_window
      w j u P U hU hborder hwindow hcap F hF
  let t := k.val - (j.val - N)
  have ht : t < 2 * N := by dsimp [t]; omega
  have hst : j.val - N + t = k.val := by dsimp [t]; omega
  have hc : finiteCodeExtend w (j.val - N + t) = 0 ∨
      finiteCodeExtend w (j.val - N + t) = 1 := hst.symm ▸ k.property
  have hu : u t = 0 ∨ u t = 1 := by rwa [hcode t ht] at hc
  let q : TriangleCreationTime u := ⟨t, hu⟩
  have hqk : (⟨j.val - N + q.val, hc⟩ : TriangleCreationTime (finiteCodeExtend w)) = k :=
    Subtype.ext hst
  have hchar (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge) :
      P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList u q ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2) := by
    rw [hk, ← hqk]
    exact window_triangle_mem_iff (finiteCodeExtend w) u (j.val - N) (2 * N)
      hcode q ht hc _
  refine ⟨q, ⟨ht, hchar⟩, ?_⟩
  intro q' hq'
  have hc' : finiteCodeExtend w (j.val - N + q'.val) = 0 ∨
      finiteCodeExtend w (j.val - N + q'.val) = 1 := by
    rw [hcode q'.val hq'.1]
    exact q'.property
  have he := huniq ⟨j.val - N + q'.val, hc'⟩
    ⟨by change j.val - N ≤ j.val - N + q'.val; omega,
      by change j.val - N + q'.val < j.val - N + 2 * N; omega,
      fun d => (hq'.2 d).trans
      (window_triangle_mem_iff (finiteCodeExtend w) u (j.val - N) (2 * N)
        hcode q' hq'.1 hc' _).symm⟩
  apply Subtype.ext
  have hev := congrArg Subtype.val he
  change j.val - N + q'.val = k.val at hev
  change q'.val = t
  omega

/-- Helper toward Proposition 3.9: retained original finite faces inject
into the triangle labels created inside the captured window, preserving
the complete original bordering-dart relation for every face. -/
theorem uibotFiniteRootWindow_retainedFaces_windowTriangleEmbedding {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    ∃ f : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ↪
        {q : TriangleCreationTime u // q.val < 2 * N},
      ∀ F d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
        ∃ a, a ∈ stageTriangleDartList u (f F).val ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2) := by
  let A := {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
    (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r}
  have hex (F : A) : ∃ q : {q : TriangleCreationTime u // q.val < 2 * N},
      ∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
        ∃ a, a ∈ stageTriangleDartList u q.val ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2) := by
    obtain ⟨q, ⟨hq, hchar⟩, _⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
      w j u P U hU hborder hwindow hcap F.val F.property
    exact ⟨⟨q, hq⟩, hchar⟩
  choose f hf using hex
  refine ⟨⟨f, ?_⟩, hf⟩
  intro F K he
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart
    (kmswStageDrawing_vertex_surjective _ _) (kmswRootedStage (finiteCodeExtend w) (n - 1)).root
    (P.toPlaneGraphDrawingFaceEquiv F.val)
  have hdK : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv K.val) := by
    apply (hf K d).mpr
    rw [← he]
    exact (hf F d).mp hd
  apply Subtype.ext
  apply P.toPlaneGraphDrawingFaceEquiv.injective
  exact P.dartBorders_face_unique d _ _ hd hdK

/-- Helper toward Proposition 3.9: retained original faces of an arbitrary
exterior-certified finite drawing are in bijection with exactly the canonical
caps whose complete boundary vertices satisfy the finite ball test. One
orientation-preserving ambient homeomorphism realizes all these faces. -/
theorem uibotFiniteRootWindow_retainedFaces_canonicalCapEquiv {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    let C := familyQ (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)
    let Q := familyG (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v, h (C.pos v) = P.pos v) ∧
      (∀ d, ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
        ∀ t, h ((C.arc d).toPath t) = (P.arc d).toPath (φ t)) ∧
      ∃ E : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ≃
        {i : Fin (kmswStage (finiteCodeExtend w) (n - 1)).triangles.length //
          ∀ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
            C.pos v ∈ closure (Q.cap i).region →
            v.val ∈ kmswStageBallVertices (fun _ _ => True)
              (kmswStage (finiteCodeExtend w) (n - 1)) r
              (activeInitial (finiteCodeExtend w) j.val)},
        ∀ F, F.val.val = h '' (Q.cap (E F).val).region := by
  dsimp only
  let C := familyQ (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)
  let Q := familyG (finiteCodeExtend w) (monotone_family_all (finiteCodeExtend w)) (n - 1)
  obtain ⟨Uc, hUc, _, hbc⟩ := uibotCanonicalStage_exterior (finiteCodeExtend w) (n - 1)
  obtain ⟨h, ho, hp, ha⟩ :=
    uibotFiniteStageDrawing_ambient_homeomorph C P Uc U hUc hU hbc hborder
  choose φ hφ hpath using ha
  let I : D39GeomRootedMapIsoV2
      (uibotFiniteStageExteriorMap C Uc hUc hbc)
      (uibotFiniteStageExteriorRoot C j.val (by have := j.isLt; omega))
      (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) := {
    h := h
    orientationPreserving := ho
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    edgeFlip := fun _ => false
    edgeParam := fun e => φ e.out
    edgeParam_mono := fun e _ => hφ e.out
    edgeParam_anti := by intro e he; cases he
    pos_map := hp
    arc_map := fun e t => hpath e.out t
    src_map := fun _ => rfl
    tgt_map := fun _ => rfl
    missing_map := fun _ => Iff.rfl
    orientation_map := by intro e he; exact (Bool.xor_false _).symm
    root_edge_map := rfl
    root_bool_map := (Bool.xor_false _).symm }
  let M := uibotFiniteStageExteriorMap C Uc hUc hbc
  let root := uibotFiniteStageExteriorRoot C j.val (by have := j.isLt; omega)
  let A := {F // F ∈ d39GeomRetainedFaces M root r}
  let J := {i : Fin (kmswStage (finiteCodeExtend w) (n - 1)).triangles.length //
    ∀ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
      C.pos v ∈ closure (Q.cap i).region →
      v.val ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage (finiteCodeExtend w) (n - 1)) r
        (activeInitial (finiteCodeExtend w) j.val)}
  choose capFace hface using Q.face_partition.1
  let f : J → A := fun i => ⟨C.toPlaneGraphDrawingFaceEquiv.symm (capFace i.val), by
    intro v hv
    apply (uibotFiniteStageExteriorBallVertices_iff C Uc hUc hbc
      j.val (by have := j.isLt; omega) r v).mpr
    apply i.property v
    exact (hface i.val) ▸ hv⟩
  have hfval (i : J) : (f i).val.val = (Q.cap i.val).region := hface i.val
  have hfi : Function.Injective f := by
    intro i k hik
    apply Subtype.ext
    by_contra hne
    have hreg : (Q.cap i.val).region = (Q.cap k.val).region :=
      (hfval i).symm.trans ((congrArg (fun a : A => a.val.val) hik).trans (hfval k))
    obtain ⟨z, hz, he⟩ := (capFace i.val).property
    have hzF : z ∈ (capFace i.val).val := he.symm ▸ mem_connectedComponentIn hz
    have hzcap : z ∈ (Q.cap i.val).region := hface i.val ▸ hzF
    exact Set.disjoint_left.mp (Q.cap_disjoint i.val k.val hne) hzcap (hreg ▸ hzcap)
  have hfs : Function.Surjective f := by
    intro F
    have hb := uibotFiniteRootWindow_retainedFace_bounded w j u C Uc hUc hbc
      hwindow hcap F.val F.property
    have hn : ¬ C.IsUnbounded (C.toPlaneGraphDrawingFaceEquiv F.val) := by
      intro hu
      exact (C.isUnbounded_iff_not_isBounded _).mp hu hb
    obtain ⟨i, hi⟩ := uibotCanonicalStage_boundedFace_is_cap (finiteCodeExtend w) (n - 1)
      (C.toPlaneGraphDrawingFaceEquiv F.val) hn
    have hip : ∀ v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex,
        C.pos v ∈ closure (Q.cap i).region →
        v.val ∈ kmswStageBallVertices (fun _ _ => True)
          (kmswStage (finiteCodeExtend w) (n - 1)) r
          (activeInitial (finiteCodeExtend w) j.val) := by
      intro v hv
      apply (uibotFiniteStageExteriorBallVertices_iff C Uc hUc hbc
        j.val (by have := j.isLt; omega) r v).mp
      apply F.property v
      exact hi.symm ▸ hv
    refine ⟨⟨i, hip⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (hfval ⟨i, hip⟩).trans hi.symm
  let e : J ≃ A := Equiv.ofBijective f ⟨hfi, hfs⟩
  let t := I.faceEquiv.subtypeEquiv (I.retainedFaces_map r)
  let E := t.symm.trans e.symm
  refine ⟨I.h, I.orientationPreserving, hp, fun d => ⟨φ d, hφ d, hpath d⟩, E, ?_⟩
  intro F
  have he : f (E F) = t.symm F := e.apply_symm_apply (t.symm F)
  have ht : (I.faceEquiv (t.symm F).val) = F.val :=
    congrArg Subtype.val (t.apply_symm_apply F)
  calc
    F.val.val = (I.faceEquiv (t.symm F).val).val := congrArg Subtype.val ht.symm
    _ = I.h '' (t.symm F).val.val := I.faceEquiv_val _
    _ = I.h '' (Q.cap (E F).val).region :=
      congrArg (fun s : Set ℂ => I.h '' s)
        ((congrArg (fun a : A => a.val.val) he).symm.trans (hfval (E F)))

/- OPEN (DC, with every binder retained):

∀ (n N r : ℕ) (hr : 0 < r)
  (w : Fin (n - 1) → Fin 3) (j : Fin n)
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H)
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (P : StageDrawing (finiteCodeExtend w) (n - 1))
  (U : P.Face) (hU : P.IsUnbounded U)
  (hborder : ∀ d, P.dartBorders d U ↔
    (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
  (hwindow : uibotFiniteRootWindow N w j =
    some (fun i => shiftedStream W N i.val))
  (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r),
  Nonempty (D39GeomBallIsoV2 r
    (uibotFiniteStageExteriorMap P U hU hborder)
    (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega))
    (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G))

Specific remaining fields: identify the whole-plane original faces with
the finite faces carrying the same window triangle labels, prove retention
and bijectivity, and construct one orientation-preserving ambient map with
compatible vertex positions, arc parameters and original-face images.
The canonical-cap equivalence here transports arbitrary finite drawings;
it does not supply the finite-to-whole-plane ambient map. No open field is
for the sole coordinator. -/

end DirectedDistances.PaperProofs.Section3
end
