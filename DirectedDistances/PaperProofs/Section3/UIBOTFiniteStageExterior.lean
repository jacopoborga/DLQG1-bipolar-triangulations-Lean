/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization2
public import DirectedDistances.PaperProofs.Section5.Prop516OriginalIffDirect9








public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5

noncomputable section

variable {w : ℕ → Fin 3} {n : ℕ}

/-- Helper toward Proposition 3.9: the finite directed geometric map built
from the drawing's certified exterior face and its outer boundary. -/
@[expose] def uibotFiniteStageExteriorMap
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d) :
    DirectedPlaneMapWithMissing (Fin (kmswStage w n).nextVertex) P.GeometricEdge := by
  let missing : P.GeometricEdge → Prop := fun e =>
    (kmswStageDirectedMap w n).missing e.out
  let forward : {e : P.GeometricEdge // ¬ missing e} → Bool :=
    fun e => !e.val.out.2
  exact finitePLDrawingDirectedMap P missing forward
    (kmswStageDrawing_missingEdges_external_of_exteriorFace P U hU hborder)

/-- Helper toward Proposition 3.9: under a `StageGeom` witness, the
exterior-face map is the same directed map as the existing geometric map. -/
theorem uibotFiniteStageExteriorMap_eq_stageGeomMap
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (G : StageGeom w n P) :
    uibotFiniteStageExteriorMap P U hU hborder =
      kmswStageDrawingDirectedPlaneMap P G := by
  rfl

/-- Helper toward Proposition 3.9: the chronological edge at time `k` is
marked by its geometric edge identity and by the side selecting its west
endpoint as the initial vertex. -/
@[expose] def uibotFiniteStageExteriorRoot
    (P : StageDrawing w n) (k : ℕ) (hk : k ≤ n) :
    P.GeometricEdge × Bool :=
  let d : StageDart (kmswStage w n).nextEdge :=
    (⟨act w k, act_lt_nextEdge w hk⟩, false)
  let e := Quotient.mk P.edgeSetoid d
  (e, !e.out.2)

/-- Helper toward Proposition 3.9: the exterior-face rooted map's root mark
has the chronological active initial vertex, also at earlier root times. -/
theorem uibotFiniteStageExteriorRoot_initial
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (k : ℕ) (hk : k ≤ n) :
    (d39GeomRootVertex (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P k hk)).val = activeInitial w k := by
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

/-- Helper toward Proposition 3.9: every chronological edge remains present
in the exterior-face map at every later finite stage. -/
theorem uibotFiniteStageExteriorRoot_present
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (k : ℕ) (hk : k ≤ n) :
    ¬ (uibotFiniteStageExteriorMap P U hU hborder).missing
      (uibotFiniteStageExteriorRoot P k hk).1 := by
  let d : StageDart (kmswStage w n).nextEdge :=
    (⟨act w k, act_lt_nextEdge w hk⟩, false)
  change ¬ (kmswStageDirectedMap w n).missing (Quotient.mk P.edgeSetoid d).out
  rcases P.geometricEdge_out_mk d with ho | ho
  · rw [ho]
    change ¬ (kmswStage w n).present (act w k) = false
    have hp := (present_mono w (act_lt_nextEdge w le_rfl)
      (kmswStage_active_present w k) n hk).2
    change (kmswStage w n).present (act w k) = true at hp
    rw [hp]
    exact Bool.noConfusion
  · rw [ho]
    intro hflip
    have hm' : (kmswStage w n).present (act w k) = false := by
      exact ((kmswStageDirectedMap w n).missing_edgeInv d).mp hflip
    have hp := (present_mono w (act_lt_nextEdge w le_rfl)
      (kmswStage_active_present w k) n hk).2
    change (kmswStage w n).present (act w k) = true at hp
    rw [hp] at hm'
    exact Bool.noConfusion hm'

/-- Helper toward Proposition 3.9: the stage map with an arbitrary
chronological root belongs to the local topology geometric domain. -/
theorem uibotFiniteStageExteriorMap_domain
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (k : ℕ) (hk : k ≤ n) :
    D39GeomDomain (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P k hk) := by
  refine ⟨?_, fun _ => Set.toFinite _, ?_⟩
  · simpa [uibotFiniteStageExteriorMap] using
      (kmswStageDrawing_geometricGraph_connected_of_external P
        (kmswStageDrawing_missingEdges_external_of_exteriorFace P U hU hborder))
  exact Or.inr ⟨uibotFiniteStageExteriorRoot_present P U hU hborder k hk, rfl⟩

/-- Helper toward Proposition 3.9: adjacency in the exterior-face drawing
is exactly distinct-vertex adjacency by a stage dart, retaining edge identity. -/
theorem uibotFiniteStageExteriorMap_adj_iff
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (v z : Fin (kmswStage w n).nextVertex) :
    (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).Adj v z ↔
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

private theorem uibotExteriorWalk_stagePath
    {P : StageDrawing w n} {U : P.Face} {hU : P.IsUnbounded U}
    {hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d}
    {v z : Fin (kmswStage w n).nextVertex}
    (p : (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).Walk v z) :
    KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ v.val p.length z.val := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => exact .nil (Set.mem_univ _)
  | Hconcat p hadj ih =>
      rw [SimpleGraph.Walk.length_concat]
      exact .snoc ih (Set.mem_univ _) (Set.mem_univ _)
        ((uibotFiniteStageExteriorMap_adj_iff P U hU hborder _ _).mp hadj).2

private theorem uibotStagePath_exteriorGeometricDistanceLe
    {P : StageDrawing w n} {U : P.Face} {hU : P.IsUnbounded U}
    {hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d}
    {x y k : ℕ}
    (p : KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ x k y)
    (hx : x < (kmswStage w n).nextVertex) (hy : y < (kmswStage w n).nextVertex) :
    (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).edist ⟨x, hx⟩ ⟨y, hy⟩ ≤
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
      · have ha := (uibotFiniteStageExteriorMap_adj_iff P U hU hborder ⟨y, hy'⟩ ⟨z, hy⟩).mpr
          ⟨fun he => heq (congrArg Fin.val he), d, hdP, hd, hz⟩
        calc
          _ ≤ (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).edist
                ⟨x, hx⟩ ⟨y, hy'⟩ +
              (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).edist
                ⟨y, hy'⟩ ⟨z, hy⟩ := SimpleGraph.edist_triangle
          _ ≤ (k : ℕ∞) + 1 := add_le_add hi
            (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr ha))
          _ = ((k + 1 : ℕ) : ℕ∞) := by simp only [Nat.cast_add, Nat.cast_one]

/-- Helper toward Proposition 3.9: the finite geometric vertex ball equals
the stage ball at the chronological root, without `StageGeom`. -/
theorem uibotFiniteStageExteriorBallVertices_iff
    (P : StageDrawing w n) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap w n).IsOuter d)
    (k : ℕ) (hk : k ≤ n) (r : ℕ) (v : Fin (kmswStage w n).nextVertex) :
    v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P k hk) r ↔
      v.val ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
        (activeInitial w k) := by
  classical
  rw [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range,
    and_iff_right v.isLt]
  let root := d39GeomRootVertex (uibotFiniteStageExteriorMap P U hU hborder)
    (uibotFiniteStageExteriorRoot P k hk)
  have hroot : root.val = activeInitial w k :=
    uibotFiniteStageExteriorRoot_initial P U hU hborder k hk
  change (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).edist root v ≤
    (r : ℕ∞) ↔ _
  constructor
  · intro hv
    have ht : (d39GeomGraph (uibotFiniteStageExteriorMap P U hU hborder)).edist root v ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hv
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top ht
    have hlen : p.length ≤ r := by exact_mod_cast hp.trans_le hv
    have hpath := uibotExteriorWalk_stagePath p
    rw [hroot] at hpath
    exact ⟨p.length, hlen, hpath⟩
  · rintro ⟨m, hm, hpath⟩
    rw [← hroot] at hpath
    exact (uibotStagePath_exteriorGeometricDistanceLe hpath root.isLt v.isLt).trans
      (by exact_mod_cast hm)

/-- Helper toward Proposition 3.9: a successful captured window identifies
the vertices in the finite exterior-face geometric ball. -/
theorem uibotFiniteRootWindow_exteriorBallVertices_iff
    {n N r : ℕ} (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r)
    (v : Fin (kmswStage (finiteCodeExtend w) (n - 1)).nextVertex) :
    v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r ↔
      ∃ x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
        (activeInitial u N),
        kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N) x = v.val := by
  rw [uibotFiniteStageExteriorBallVertices_iff,
    ← uibotFiniteRootWindow_rootBallVertices_eq_window w j u hwindow hcap,
    Finset.mem_image]

/-- Helper toward Proposition 3.9: the captured window vertex carrier is in
bijection with the finite exterior-face geometric ball. -/
theorem uibotFiniteRootWindow_exteriorVertex_bijective
    {n N r : ℕ} (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    ∃ f : {x // x ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u (2 * N)) r (activeInitial u N)} →
      {v // v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r},
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
      {v // v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} :=
    ⟨⟨φ x.val, hb x⟩,
      (uibotFiniteRootWindow_exteriorBallVertices_iff w j u P U hU hborder
        hwindow hcap _).mpr ⟨x.val, x.property, rfl⟩⟩
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
      (uibotFiniteRootWindow_exteriorBallVertices_iff w j u P U hU hborder
        hwindow hcap v.val).mp v.property
    exact ⟨⟨x, hx⟩, Subtype.ext (Fin.ext hφ)⟩

/-- Helper toward Proposition 3.9: agreeing captured windows give an
equivalence of the finite exterior-face and whole-plane vertex balls, with
its action specified on every window vertex. -/
theorem uibotFiniteRootWindow_exteriorVertexEquiv
    {n N r : ℕ} (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ E : {v // v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ≃
      {v // v ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ (x : ℕ)
        (_hx : x ∈ kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N))
        (v : {v // v ∈ d39GeomBallVertices (uibotFiniteStageExteriorMap P U hU hborder)
          (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r}),
        v.val.val = kmswWindowPatchVertexMap (finiteCodeExtend w)
          (j.val - N) (2 * N) x → (E v).val = wholePlaneVertexι W N x := by
  classical
  let S := kmswStageBallVertices (fun _ _ => True)
    (kmswStage (shiftedStream W N) (2 * N)) r (activeInitial (shiftedStream W N) N)
  obtain ⟨f, hf, hfid⟩ := uibotFiniteRootWindow_exteriorVertex_bijective
    w j (shiftedStream W N) P U hU hborder hwindow hcap
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


























/-- Helper toward Proposition 3.9: every finite code and stage has a drawing,
an unbounded face, and the exact outer-dart boundary characterization. -/
theorem uibotFiniteStageExterior_exists (w : ℕ → Fin 3) (n : ℕ) :
    ∃ (P : StageDrawing w n) (U : P.Face),
      P.IsUnbounded U ∧ ∀ d, P.dartBorders d U ↔
        (kmswStageDirectedMap w n).IsOuter d := by
  obtain ⟨P, U, hU, _, hborder⟩ :=
    kmswStageDrawing_uniqueExteriorFace_borders_iff_isOuter w n
  exact ⟨P, U, hU, hborder⟩


end

end DirectedDistances.PaperProofs.Section3
