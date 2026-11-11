/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization
public import DirectedDistances.PaperProofs.Section5.Prop516StageDrawingBaseRepresentation

/-! # Finite geometric root balls toward Proposition 3.9

The sampled chronological root, geometric vertex ball and individual induced
edge identities are related to the captured code window. These are components
of the geometric comparison; retained faces and an ambient orientation-preserving
homeomorphism are still required. No local-limit identification is asserted. -/

public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 3.9: the exact induced-edge bijection for a
successful sampled root window, with all finite-stage edge identities retained. -/
theorem uibotFiniteRootWindow_rootBallEdges_bijOn {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N)
    Set.BijOn
      (fun e => (kmswWindowFreshSetEdgeMap (finiteCodeExtend w)
        (j.val - N) (2 * N) e).val)
      (kmswWindowFreshSetSourceEdges (finiteCodeExtend w) (j.val - N) (2 * N) S)
      {e : ℕ | e < (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge ∧
        (kmswStage (finiteCodeExtend w) (n - 1)).west e ∈
          kmswStageBallVertices (fun _ _ => True)
            (kmswStage (finiteCodeExtend w) (n - 1)) r
            (activeInitial (finiteCodeExtend w) j.val) ∧
        (kmswStage (finiteCodeExtend w) (n - 1)).east e ∈
          kmswStageBallVertices (fun _ _ => True)
            (kmswStage (finiteCodeExtend w) (n - 1)) r
            (activeInitial (finiteCodeExtend w) j.val)} := by
  obtain ⟨hv, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hn : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  have h := kmswWindowCaptureEventStrong_edge_bijOn_future u (finiteCodeExtend w)
    (2 * N) r (activeInitial u N) (j.val - N) hcap hcode (n - 1) hn
  dsimp only at h ⊢
  rwa [uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap] at h

noncomputable section

variable {w : ℕ → Fin 3} {n : ℕ} (P : StageDrawing w n) (Q : StageGeom w n P)

/-- Helper toward Proposition 3.9: the finite geometric mark at chronological
time `k`, stored with the Boolean selecting the west endpoint as its initial vertex. -/
@[expose] def uibotFiniteStageGeometricRoot (k : ℕ) (hk : k ≤ n) :
    P.GeometricEdge × Bool :=
  let d : StageDart (kmswStage w n).nextEdge :=
    (⟨act w k, act_lt_nextEdge w hk⟩, false)
  let e := Quotient.mk P.edgeSetoid d
  (e, !e.out.2)

/-- Helper toward Proposition 3.9: the finite drawing mark has the same
initial vertex as the chronological active edge, including earlier root times. -/
theorem uibotFiniteStageGeometricRoot_initial (k : ℕ) (hk : k ≤ n) :
    (d39GeomRootVertex (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P k hk)).val = activeInitial w k := by
  let d : StageDart (kmswStage w n).nextEdge :=
    (⟨act w k, act_lt_nextEdge w hk⟩, false)
  let e := Quotient.mk P.edgeSetoid d
  change Fin.val (if !e.out.2 then stageVertex w n e.out
    else stageVertex w n (edgeFlip _ e.out)) = _
  have hs : (kmswStage w n).west (act w k) = activeInitial w k := by
    rw [(kmswStage_endpoints_stable w hk (act_lt_nextEdge w le_rfl)).1]
    rw [CutConverse.activeInitial_eq]
  rcases P.geometricEdge_out_mk d with ho | ho
  · change e.out = d at ho
    rw [ho]
    exact hs
  · change e.out = edgeFlip _ d at ho
    rw [ho]
    exact hs

/-- Helper toward Proposition 3.9: every chronological active edge remains
present in the finite drawing at every later stage. -/
theorem uibotFiniteStageGeometricRoot_present (k : ℕ) (hk : k ≤ n) :
    ¬ (kmswStageDrawingDirectedPlaneMap P Q).missing
      (uibotFiniteStageGeometricRoot P k hk).1 := by
  change ¬ (kmswStageDrawingDirectedPlaneMap P Q).missing
    (Quotient.mk P.edgeSetoid
      ((⟨act w k, act_lt_nextEdge w hk⟩, false) : StageDart (kmswStage w n).nextEdge))
  rw [kmswStageDrawing_missing_mk]
  change ¬ (kmswStage w n).present (act w k) = false
  have hp := (present_mono w (act_lt_nextEdge w le_rfl)
    (kmswStage_active_present w k) n hk).2
  change (kmswStage w n).present (act w k) = true at hp
  rw [hp]
  exact Bool.noConfusion

/-- Helper toward Proposition 3.9: the finite geometric map with any earlier
chronological edge as its root lies in the local topology domain, with a present root. -/
theorem uibotFiniteStageGeometricMap_domain (k : ℕ) (hk : k ≤ n) :
    D39GeomDomain (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P k hk) := by
  refine ⟨kmswStageDrawing_geometricGraph_connected P Q, fun _ => Set.toFinite _, ?_⟩
  exact Or.inr ⟨uibotFiniteStageGeometricRoot_present P Q k hk, rfl⟩

/-- Helper toward Proposition 3.9: geometric adjacency in the finite drawing
is exactly distinct-vertex adjacency through a stage dart; multiedges remain
individual edges before taking graph distance. -/
theorem uibotFiniteStageGeometricMap_adj_iff
    (v z : Fin (kmswStage w n).nextVertex) :
    (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).Adj v z ↔
      v ≠ z ∧ kmswStageAdjacent (fun _ _ => True) (kmswStage w n) v.val z.val := by
  constructor
  · rintro ⟨hne, e, he⟩
    refine ⟨hne, ?_⟩
    change (stageVertex w n e.out = v ∧ stageVertex w n (edgeFlip _ e.out) = z) ∨
      (stageVertex w n e.out = z ∧ stageVertex w n (edgeFlip _ e.out) = v) at he
    rcases he with ⟨hv, hz⟩ | ⟨hz, hv⟩
    · exact ⟨e.out, trivial, congrArg Fin.val hv, congrArg Fin.val hz⟩
    · refine ⟨edgeFlip _ e.out, trivial, congrArg Fin.val hv, ?_⟩
      simpa [stageVertex, edgeFlip] using congrArg Fin.val hz
  · rintro ⟨hne, d, _, hv, hz⟩
    let e := Quotient.mk P.edgeSetoid d
    refine ⟨hne, e, ?_⟩
    change (stageVertex w n e.out = v ∧ stageVertex w n (edgeFlip _ e.out) = z) ∨
      (stageVertex w n e.out = z ∧ stageVertex w n (edgeFlip _ e.out) = v)
    rcases P.geometricEdge_out_mk d with ho | ho
    · change e.out = d at ho
      rw [ho]
      exact Or.inl ⟨Fin.ext hv, Fin.ext hz⟩
    · change e.out = edgeFlip _ d at ho
      rw [ho]
      right
      refine ⟨Fin.ext hz, ?_⟩
      apply Fin.ext
      simpa [stageVertex, edgeFlip] using hv

private theorem uibotFiniteGeometricWalk_stagePath
    {v z : Fin (kmswStage w n).nextVertex}
    (p : (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).Walk v z) :
    KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ v.val p.length z.val := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => exact .nil (Set.mem_univ _)
  | Hconcat p h ih =>
      rw [SimpleGraph.Walk.length_concat]
      exact .snoc ih (Set.mem_univ _) (Set.mem_univ _)
        ((uibotFiniteStageGeometricMap_adj_iff P Q _ _).mp h).2

private theorem uibotStagePath_finiteGeometricDistanceLe
    {x y k : ℕ}
    (p : KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ x k y)
    (hx : x < (kmswStage w n).nextVertex) (hy : y < (kmswStage w n).nextVertex) :
    (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).edist ⟨x, hx⟩ ⟨y, hy⟩ ≤
      (k : ℕ∞) := by
  induction p with
  | nil => exact le_of_eq SimpleGraph.edist_self
  | @snoc k y z p _ _ hadj ih =>
      obtain ⟨d, hdP, hd, hz⟩ := hadj
      have hy' : y < (kmswStage w n).nextVertex :=
        hd ▸ stageEndpoint_lt_nextVertex w n d
      have hi := ih hy'
      by_cases heq : y = z
      · cases heq
        exact hi.trans (show (k : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) by
          exact_mod_cast Nat.le_succ k)
      · have ha := (uibotFiniteStageGeometricMap_adj_iff P Q ⟨y, hy'⟩ ⟨z, hy⟩).mpr
          ⟨fun he => heq (congrArg Fin.val he), d, hdP, hd, hz⟩
        calc
          _ ≤ (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).edist
                ⟨x, hx⟩ ⟨y, hy'⟩ +
              (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).edist
                ⟨y, hy'⟩ ⟨z, hy⟩ := SimpleGraph.edist_triangle
          _ ≤ (k : ℕ∞) + 1 := add_le_add hi
            (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr ha))
          _ = ((k + 1 : ℕ) : ℕ∞) := by simp only [Nat.cast_add, Nat.cast_one]

/-- Helper toward Proposition 3.9: the finite geometric local topology vertex ball
equals the stage ball at the sampled chronological root, at the same radius. -/
theorem uibotFiniteStageGeometricBallVertices_iff (k : ℕ) (hk : k ≤ n)
    (r : ℕ) (v : Fin (kmswStage w n).nextVertex) :
    v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P k hk) r ↔
      v.val ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
        (activeInitial w k) := by
  classical
  rw [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range,
    and_iff_right v.isLt]
  let root := d39GeomRootVertex (kmswStageDrawingDirectedPlaneMap P Q)
    (uibotFiniteStageGeometricRoot P k hk)
  have hroot : root.val = activeInitial w k := uibotFiniteStageGeometricRoot_initial P Q k hk
  change (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).edist root v ≤
    (r : ℕ∞) ↔ _
  constructor
  · intro hv
    have ht : (d39GeomGraph (kmswStageDrawingDirectedPlaneMap P Q)).edist root v ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hv
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top ht
    have hlen : p.length ≤ r := by exact_mod_cast hp.trans_le hv
    have hpath := uibotFiniteGeometricWalk_stagePath P Q p
    rw [hroot] at hpath
    exact ⟨p.length, hlen, hpath⟩
  · rintro ⟨m, hm, hpath⟩
    rw [← hroot] at hpath
    exact (uibotStagePath_finiteGeometricDistanceLe P Q hpath root.isLt v.isLt).trans
      (by exact_mod_cast hm)

/-- Helper toward Proposition 3.9: a successful captured window identifies
exactly which vertices lie in the finite geometric ball at the sampled root. -/
theorem uibotFiniteRootWindow_geometricBallVertices_iff {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex) :
    v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
      (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r ↔
      ∃ x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
        (activeInitial u N),
        kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N) x = v.val := by
  rw [uibotFiniteStageGeometricBallVertices_iff,
    ← uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap,
    Finset.mem_image]

/-- Helper toward Proposition 3.9: the captured window's vertex carrier is
in bijection with the actual finite geometric ball. The displayed map is the
KMSW window patch map, so vertex identity is retained. -/
theorem uibotFiniteRootWindow_geometricVertex_bijective {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    ∃ f : {x // x ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u (2 * N)) r (activeInitial u N)} →
      {v // v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
        (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r},
      Function.Bijective f ∧ ∀ x,
        (f x).val.val = kmswWindowPatchVertexMap (finiteCodeExtend w)
          (j.val - N) (2 * N) x.val := by
  classical
  let S := kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
    (activeInitial u N)
  let φ := kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N)
  have hb (x : {x // x ∈ S}) : φ x.val <
      (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex := by
    have hm : φ x.val ∈ S.image φ := Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩
    rw [uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap] at hm
    exact Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  let f (x : {x // x ∈ S}) :
      {v // v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
        (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r} :=
    ⟨⟨φ x.val, hb x⟩,
      (uibotFiniteRootWindow_geometricBallVertices_iff w j u P Q hwindow hcap _).mpr
        ⟨x.val, x.property, rfl⟩⟩
  refine ⟨f, ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro x y hxy
    obtain ⟨_, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
    have hs : kmswStage (fun i => finiteCodeExtend w (j.val - N + i)) (2 * N) =
        kmswStage u (2 * N) := kmswStage_congr hcode
    apply Subtype.ext
    apply kmswWindowPatchVertexMap_injOn (finiteCodeExtend w) (j.val - N) (2 * N)
    · rw [hs]
      exact Finset.mem_range.mp (Finset.mem_filter.mp x.property).1
    · rw [hs]
      exact Finset.mem_range.mp (Finset.mem_filter.mp y.property).1
    · exact congrArg (fun z => z.val.val) hxy
  · intro v
    obtain ⟨x, hx, hφ⟩ :=
      (uibotFiniteRootWindow_geometricBallVertices_iff w j u P Q hwindow hcap v.val).mp
        v.property
    exact ⟨⟨x, hx⟩, Subtype.ext (Fin.ext hφ)⟩

/-- Helper toward Proposition 3.9: agreeing captured windows give an actual
equivalence of the finite and whole-plane geometric vertex balls, with its
action specified on every window vertex. This supplies the vertex field of
the desired local topology isomorphism, without asserting its edge or face fields. -/
theorem uibotFiniteRootWindow_geometricVertexEquiv {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ E : {v // v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
        (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r} ≃
      {v // v ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ (x : ℕ)
        (_hx : x ∈ kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N))
        (v : {v // v ∈ d39GeomBallVertices (kmswStageDrawingDirectedPlaneMap P Q)
          (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega)) r}),
        v.val.val = kmswWindowPatchVertexMap (finiteCodeExtend w)
          (j.val - N) (2 * N) x → (E v).val = wholePlaneVertexι W N x := by
  classical
  let S := kmswStageBallVertices (fun _ _ => True)
    (kmswStage (shiftedStream W N) (2 * N)) r (activeInitial (shiftedStream W N) N)
  obtain ⟨f, hf, hfid⟩ := uibotFiniteRootWindow_geometricVertex_bijective
    w j (shiftedStream W N) P Q hwindow hcap
  let g (x : {x // x ∈ S}) :
      {v // v ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r} :=
    ⟨wholePlaneVertexι W N x.val, by
      rw [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap]
      exact ⟨x.val, x.property, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact Subtype.ext (wholePlaneVertexι_injective W N (congrArg Subtype.val hxy))
    · intro v
      have hv := v.property
      simp only [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap] at hv
      obtain ⟨x, hx, he⟩ := hv
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let F := Equiv.ofBijective f hf
  let E := F.symm.trans (Equiv.ofBijective g hg)
  refine ⟨E, ?_⟩
  intro x hx v hv
  have hfv : f ⟨x, hx⟩ = v := Subtype.ext (Fin.ext ((hfid ⟨x, hx⟩).trans hv.symm))
  have hinv : F.symm v = ⟨x, hx⟩ := F.symm_apply_eq.mpr hfv.symm
  change (g (F.symm v)).val = _
  rw [hinv]

/- OPEN geometric comparison, with every binder (not an asserted declaration):

∀ (n N r : ℕ) (hr : 0 < r)
  (w : Fin (n - 1) → Fin 3) (j : Fin n)
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H)
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (P : StageDrawing (finiteCodeExtend w) (n - 1))
  (Q : StageGeom (finiteCodeExtend w) (n - 1) P)
  (hwindow : uibotFiniteRootWindow N w j =
    some (fun i => shiftedStream W N i.val))
  (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r),
  Nonempty (D39GeomBallIsoV2 r
    (kmswStageDrawingDirectedPlaneMap P Q)
    (uibotFiniteStageGeometricRoot P j.val (by have := j.isLt; omega))
    (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G)).

The vertex-equivalence field is supplied above, with its exact window action.
The finite and whole-plane induced-edge bijections are available separately;
transport these to the drawings' geometric edge quotients, then prove missing
tags, orientations, the ordered root and original retained-face correspondence.
One ambient orientation-preserving homeomorphism with compatible edge-arc
reparameterizations is still required. Finite stages must also be identified
with every actual Peano-rooted representative of kmswProcedureEquiv. -/

end

end DirectedDistances.PaperProofs.Section3
