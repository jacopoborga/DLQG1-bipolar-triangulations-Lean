/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization17

/-! # Exact canonical geometry under prefix agreement

These equalities concern the actual coordinates and full ordered polylines. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set

private theorem rank_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m, w i = u i) : kmswStageRank w m = kmswStageRank u m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hc0 : ∀ i < m, w i = u i := fun i hi => hc i (by omega)
    have hs := kmswStage_congr hc0
    funext v
    simp only [kmswStageRank, hs, hc m (by omega), ih hc0]

private theorem height_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m, w i = u i) : layoutHeight w m = layoutHeight u m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hc0 : ∀ i < m, w i = u i := fun i hi => hc i (by omega)
    have hs := kmswStage_congr hc0
    have hs' := kmswStage_congr hc
    funext v
    simp only [layoutHeight, hs, hs', ih hc0]

/-- Helper toward Proposition 3.9: agreeing code prefixes have literally
equal canonical vertex coordinates, including every allocated vertex. -/
theorem uibotLayoutPos_eq_of_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m, w i = u i) (v : ℕ) :
    layoutPos w m v = layoutPos u m v := by
  simp only [layoutPos, rank_prefix w u m hc, height_prefix w u m hc]

private theorem budget_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m + 1, w i = u i) : freshRampBudget w m = freshRampBudget u m := by
  have hs : kmswStage w m = kmswStage u m :=
    kmswStage_congr (fun i hi => hc i (by omega : i < m + 1))
  have hs' := kmswStage_congr hc
  simp only [freshRampBudget, freshEdges, hs, hs', rank_prefix w u (m + 1) hc]

private theorem slope_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m + 1, w i = u i) : rampSlope w m = rampSlope u m := by
  induction m with
  | zero => simp only [rampSlope, budget_prefix w u 0 hc]
  | succ m ih =>
    have hc0 : ∀ i < m + 1, w i = u i := fun i hi => hc i (by omega)
    simp only [rampSlope, ih hc0, budget_prefix w u (m + 1) hc]

/-- Helper toward Proposition 3.9: agreeing code prefixes have literally
equal canonical polylines; the equality includes the whole parameterization. -/
theorem uibotLayoutArc_eq_of_prefix (w u : ℕ → Fin 3) (m : ℕ)
    (hc : ∀ i < m, w i = u i) (e : ℕ) :
    layoutArc w m e = layoutArc u m e := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hc0 : ∀ i < m, w i = u i := fun i hi => hc i (by omega)
    have hs := kmswStage_congr hc0
    have hs' := kmswStage_congr hc
    simp only [layoutArc, hs, ih hc0, freshEdges, hs',
      uibotLayoutPos_eq_of_prefix w u (m + 1) hc, isFreshLeftMissing,
      hc m (by omega), slope_prefix w u m hc]
    rfl

/-- Helper toward Proposition 3.9: canonical stage positions are unchanged
by later sewing steps. The inclusion preserves the exact natural label. -/
theorem uibotCanonicalStage_pos_persistent (w : ℕ → Fin 3) {m t : ℕ}
    (hmt : m ≤ t) (v : Fin (kmswStage w m).nextVertex) :
    (familyQ w (monotone_family_all w) t).pos
        (v.castLE (CutConverse.nextVertex_mono w hmt)) =
      (familyQ w (monotone_family_all w) m).pos v := by
  change layoutPos w t v.val = layoutPos w m v.val
  induction t, hmt using Nat.le_induction with
  | base => rfl
  | succ t hmt ih =>
    exact (layoutPos_old_vertex w t v.val
      (v.isLt.trans_le (CutConverse.nextVertex_mono w hmt))).trans ih

/-- Helper toward Proposition 3.9: canonical stage polylines are unchanged
by later sewing steps, for both directions of every old geometric edge. -/
theorem uibotCanonicalStage_arc_persistent (w : ℕ → Fin 3) {m t : ℕ}
    (hmt : m ≤ t) (d : StageDart (kmswStage w m).nextEdge) :
    (familyQ w (monotone_family_all w) t).arc
        (d.1.castLE (kmswStage_nextEdge_mono w hmt), d.2) =
      (familyQ w (monotone_family_all w) m).arc d := by
  have he : layoutArc w t d.1.val = layoutArc w m d.1.val := by
    induction t, hmt using Nat.le_induction with
    | base => rfl
    | succ t hmt ih =>
      exact (layoutArc_old w t d.1.val
        (d.1.isLt.trans_le (kmswStage_nextEdge_mono w hmt))).trans ih
  change (if d.2 then (layoutArc w t d.1.val).reverse else layoutArc w t d.1.val) = _
  rw [he]
  rfl

/-- Helper toward Proposition 3.9: one ambient homeomorphism carries the
entire shifted window inside an arbitrary later finite drawing to its
canonical window drawing. Later sewing does not alter any selected arc. -/
theorem uibotFiniteWindow_final_ambient_canonical
    (w : ℕ → Fin 3) (s m t : ℕ) (hst : s + m ≤ t)
    (P : StageDrawing w t) (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w t).IsOuter d) :
    let C := familyQ (fun i => w (s + i)) (monotone_family_all (fun i => w (s + i))) m
    ∃ h : ℂ ≃ₜ ℂ, OrientationPreserving h ∧
      (∀ v : Fin (kmswStage (fun i => w (s + i)) m).nextVertex,
        h (P.pos ⟨kmswWindowPatchVertexMap w s m v.val,
          ((kmswWindowPatchVertexMap_rel w s m).vertex_bound v.val v.isLt).trans_le
            (CutConverse.nextVertex_mono w hst)⟩) = C.pos v) ∧
      ∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ z, h ((P.arc ((kmswWindowDartMap w s m d).1.castLE
              (kmswStage_nextEdge_mono w hst), d.2)).toPath z) =
            (C.arc d).toPath (φ z) := by
  let Ct := familyQ w (monotone_family_all w) t
  let Cs := familyQ w (monotone_family_all w) (s + m)
  obtain ⟨Ut, hUt, _, hbt⟩ := uibotCanonicalStage_exterior w t
  obtain ⟨Us, hUs, _, hbs⟩ := uibotCanonicalStage_exterior w (s + m)
  obtain ⟨a, hao, hap, haa⟩ :=
    uibotFiniteStageDrawing_ambient_homeomorph P Ct U Ut hU hUt hborder hbt
  obtain ⟨b, hbo, hbp, hba⟩ :=
    uibotFiniteWindowStageDrawing_ambient_canonical w s m Cs Us hUs hbs
  refine ⟨a.trans b, hao.trans hbo, ?_, ?_⟩
  · intro v
    change b (a (P.pos _)) = _
    rw [hap]
    have hs := uibotCanonicalStage_pos_persistent w hst
      (⟨kmswWindowPatchVertexMap w s m v.val,
        (kmswWindowPatchVertexMap_rel w s m).vertex_bound v.val v.isLt⟩ :
        Fin (kmswStage w (s + m)).nextVertex)
    change Ct.pos _ = Cs.pos _ at hs
    exact (congrArg b hs).trans (hbp v)
  · intro d
    let e := kmswWindowDartMap w s m d
    obtain ⟨φ, hφ, hpφ⟩ := haa (e.1.castLE (kmswStage_nextEdge_mono w hst), d.2)
    obtain ⟨ψ, hψ, hpψ⟩ := hba d
    refine ⟨φ.trans ψ, hψ.comp hφ, ?_⟩
    intro z
    change b (a ((P.arc _).toPath z)) = _
    rw [hpφ]
    have hs := uibotCanonicalStage_arc_persistent w hst e
    change Ct.arc (e.1.castLE (kmswStage_nextEdge_mono w hst), d.2) = Cs.arc e at hs
    rw [hs]
    exact hpψ (φ z)

end DirectedDistances.PaperProofs.Section3
end
