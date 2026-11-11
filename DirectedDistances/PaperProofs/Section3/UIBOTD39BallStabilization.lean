/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWWindowSeamLevel
public import DirectedDistances.KMSW.KMSWWindowActiveRoot
public import DirectedDistances.PaperProofs.Section3.UIBOTFiniteRootWindow
public import DirectedDistances.PaperProofs.Section3.D39GeometricDomain
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier
public import DirectedDistances.KMSW.WholePlaneRootedMapFields








public section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap

/-- Helper toward Proposition 3.9: infinite window transport preserves the
chronological active edge, including its edge identity. -/
theorem uibotWindowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) =
      act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

/-- Helper toward Proposition 3.9: a change of one-sided start preserves
the active edge at the same integer time. -/
theorem uibotWholePlaneEdgeTrans_act (W : ℤ → Fin 3) (N M : ℕ)
    (h : N ≤ M) (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    uibotWindowEdgeMapInf_act (shiftedStream W M) (M - N) k

/-- Helper toward Proposition 3.9: the transported initial vertex is the
initial vertex of the same chronological active edge. -/
theorem uibotWholePlaneVertexTrans_activeInitial (W : ℤ → Fin 3) (N M : ℕ)
    (h : N ≤ M) (k : ℕ) :
    wholePlaneVertexTrans W N M h (activeInitial (shiftedStream W N) k) =
      activeInitial (shiftedStream W M) (M - N + k) := by
  unfold activeInitial
  rw [← wholePlaneEdgeTrans_west, uibotWholePlaneEdgeTrans_act]

/-- Helper toward Proposition 3.9: the center-window active edge represents
the chronological edge `λ₀`, namely the initial edge of run zero. -/
theorem uibotWholePlane_centerRootEdge (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneEdgeι W N (act (shiftedStream W N) N) =
      wholePlaneEdgeι W 0 0 := by
  have ht := uibotWholePlaneEdgeTrans_act W 0 N (Nat.zero_le N) 0
  simp only [Nat.sub_zero, Nat.add_zero] at ht
  rw [← ht]
  exact congrFun (wholePlaneEdgeι_trans W 0 N (Nat.zero_le N)) 0

/-- Helper toward Proposition 3.9: the center of the captured ball is the
initial endpoint of `λ₀`, with no left-record or stopped-word hypothesis. -/
theorem uibotWholePlane_centerRootVertex (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneVertexι W N (activeInitial (shiftedStream W N) N) =
      wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0) := by
  rw [← uibotWholePlane_centerRootEdge W N, wholePlaneEdgeWest_ι]
  rfl

/-- Helper toward Proposition 3.9: a strong finite capture certificate at
the chronological midpoint of a window of `2*N` increments. -/
@[expose] def UIBOTRootWindowCapture (u : ℕ → Fin 3) (N r : ℕ) : Prop :=
  kmswWindowCaptureEventStrong u (2 * N) r (activeInitial u N)

/-- Helper toward Proposition 3.9: the root capture certificate depends
only on the `2*N` window letters, including its midpoint root choice. -/
theorem uibotRootWindowCapture_congr (u u' : ℕ → Fin 3) (N r : ℕ)
    (h : ∀ i < 2 * N, u i = u' i) :
    UIBOTRootWindowCapture u N r ↔ UIBOTRootWindowCapture u' N r := by
  have hc : activeInitial u N = activeInitial u' N :=
    activeInitial_congr (fun i hi => h i (by omega))
  unfold UIBOTRootWindowCapture
  rw [hc]
  exact kmswWindowCaptureEventStrong_congr u u' (2 * N) r _ h

/-- Helper toward Proposition 3.9: capture at the chronological midpoint
gives exactly the all-geometric-edge colimit vertex ball about `λ₀`. -/
theorem uibotWholePlane_rootBallVertices_eq_window (W : ℤ → Fin 3) (N r : ℕ)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) =
      wholePlaneVertexι W N ''
        (↑(kmswStageBallVertices (fun _ _ => True)
          (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N)) : Set ℕ) := by
  rw [← uibotWholePlane_centerRootVertex W N]
  exact wholePlaneBallVertices_eq_image_of_windowCaptureEvent
    W N (2 * N) r _ hcap.1

/-- Helper toward Proposition 3.9: window edges correspond bijectively to
the induced colimit root-ball edges; parallel and missing edge identities
are retained. This does not assert the geometric retained-face condition. -/
theorem uibotWholePlane_rootBallEdges_bijOn (W : ℤ → Fin 3) (N r : ℕ)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    let S := kmswStageBallVertices (fun _ _ => True)
      (kmswStage (shiftedStream W N) (2 * N)) r
      (activeInitial (shiftedStream W N) N)
    Set.BijOn (fun e : Fin (kmswStage (shiftedStream W N) (2 * N)).nextEdge =>
      wholePlaneEdgeι W N e.val)
      {e | (kmswStage (shiftedStream W N) (2 * N)).west e.val ∈ S ∧
        (kmswStage (shiftedStream W N) (2 * N)).east e.val ∈ S}
      {e | wholePlaneEdgeWest W e ∈
          wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) ∧
        wholePlaneEdgeEast W e ∈
          wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0))} := by
  dsimp only
  rw [← uibotWholePlane_centerRootVertex W N]
  exact kmswWindowCaptureEventStrong_wholePlaneEdge_bijOn W N (2 * N) r _ hcap

/-- Helper toward Proposition 3.9: the root at an interior time of a
window transports to the same chronological time in any compatible word. -/
theorem uibotWindowPatchVertexMap_activeInitial (u w : ℕ → Fin 3)
    (s m k : ℕ) (hk : k ≤ m) (hcode : ∀ i < m, w (s + i) = u i) :
    kmswWindowPatchVertexMap w s m (activeInitial u k) =
      activeInitial w (s + k) := by
  have hs : kmswStage (fun i => w (s + i)) k = kmswStage u k :=
    kmswStage_congr (fun i hi => hcode i (hi.trans_le hk))
  have hv : activeInitial u k <
      (kmswStage (fun i => w (s + i)) k).nextVertex := by
    rw [hs, CutConverse.activeInitial_eq]
    exact (kmswStage_endpoints_lt_nextVertex u k (act u k)
      (act_lt_nextEdge u le_rfl)).1
  rw [kmswWindowPatchVertexMap_extends_le w s k m hk _ hv]
  exact kmswWindowPatchVertexMap_activeInitial u w s k
    (fun i hi => hcode i (hi.trans_le hk))

/-- Helper toward Proposition 3.9: a captured centered window determines
the final finite-stage vertex ball at the chronological root, for every
compatible prefix and continuation. -/
theorem uibotFiniteStage_rootBallVertices_eq_window
    (u w : ℕ → Fin 3) (N r s n : ℕ)
    (hcap : UIBOTRootWindowCapture u N r)
    (hcode : ∀ i < 2 * N, w (s + i) = u i) (hn : s + 2 * N ≤ n) :
    (kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N)).image (kmswWindowPatchVertexMap w s (2 * N)) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
        (activeInitial w (s + N)) := by
  have h := kmswWindowCaptureEvent_ballVerticesImageEq_future u (2 * N) r
    (activeInitial u N) hcap.1 w s hcode n hn
  rw [uibotWindowPatchVertexMap_activeInitial u w s (2 * N) N (by omega) hcode] at h
  exact h

/-- Helper toward Proposition 3.9: a successful centered observation in
the actual finite word gives the precise code agreement needed by capture.
The cemetery outcome is excluded by the successful observation itself. -/
theorem uibotFiniteRootWindow_codeAgreement {n N : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val)) :
    UIBOTRootWindowValid N j ∧
      ∀ i < 2 * N, finiteCodeExtend w (j.val - N + i) = u i := by
  have hv : UIBOTRootWindowValid N j :=
    (uibotFiniteRootWindow_ne_none_iff w j).mp (by rw [hwindow]; simp only [ne_eq,
      reduceCtorEq, not_false_eq_true])
  refine ⟨hv, ?_⟩
  intro i hi
  have hindex := (uibotFiniteRootWindow_index j hv ⟨i, hi⟩).1
  rw [finiteCodeExtend, dite_eq_left hindex]
  exact (uibotFiniteRootWindow_letter w j hv (fun i => u i.val) hwindow ⟨i, hi⟩).symm

/-- Helper toward Proposition 3.9: a successful finite root-window sample
and its finite capture certificate determine the final stage root-ball
vertices. This applies directly to the inverse word sampled through
`kmswProcedureEquiv`; geometric realization remains a separate obligation. -/
theorem uibotFiniteRootWindow_rootBallVertices_eq_window {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n) (u : ℕ → Fin 3)
    (hwindow : uibotFiniteRootWindow N w j = some (fun i => u i.val))
    (hcap : UIBOTRootWindowCapture u N r) :
    (kmswStageBallVertices (fun _ _ => True) (kmswStage u (2 * N)) r
      (activeInitial u N)).image
        (kmswWindowPatchVertexMap (finiteCodeExtend w) (j.val - N) (2 * N)) =
      kmswStageBallVertices (fun _ _ => True)
        (kmswStage (finiteCodeExtend w) (n - 1)) r
        (activeInitial (finiteCodeExtend w) j.val) := by
  obtain ⟨hv, hcode⟩ := uibotFiniteRootWindow_codeAgreement w j u hwindow
  have hn : j.val - N + 2 * N ≤ n - 1 := by
    have := hv.1
    have := hv.2
    omega
  have h := uibotFiniteStage_rootBallVertices_eq_window u (finiteCodeExtend w)
    N r (j.val - N) (n - 1) hcap hcode hn
  rwa [Nat.sub_add_cancel hv.1] at h

noncomputable section

/-- Helper toward Proposition 3.9: a whole-plane drawing with every edge
present gives a directed geometric map, retaining the original geometric
edge quotient and its actual faces. The supplied presence proof is discharged
almost surely in `UIBOTLocalLimitIdentification`. -/
@[expose] def uibotWholePlaneGeometricMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    DirectedPlaneMapWithMissing (WholePlaneVertex W) G.GeometricEdge where
  toPlaneGraphDrawing := G.toPlaneGraphDrawing
  missing e := ¬ wholePlaneEdgePresent W e.out.1
  missing_on_external := by
    intro e he
    exact (he (hp e.out.1)).elim
  forward e := !e.val.out.2

/-- Helper toward Proposition 3.9: the geometric root mark for the
chronological edge `λ₀`; its Boolean compensates for endpoint storage. -/
@[expose] def uibotWholePlaneGeometricRoot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H) :
    G.GeometricEdge × Bool :=
  let e := Quotient.mk G.edgeSetoid (wholePlaneEdgeι W 0 0, false)
  (e, !e.out.2)

/-- Helper toward Proposition 3.9: the constructed map has exactly the
whole-plane presence tags, hence has no missing edge under its presence proof. -/
theorem uibotWholePlaneGeometricMap_noMissing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (e : G.GeometricEdge) :
    ¬ (uibotWholePlaneGeometricMap W H G hp).missing e := by
  exact fun he => he (hp e.out.1)

/-- Helper toward Proposition 3.9: each geometric present edge is oriented
from its whole-plane west endpoint to its whole-plane east endpoint. -/
theorem uibotWholePlaneGeometricMap_endpoints (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (e : G.GeometricEdge) :
    let M := uibotWholePlaneGeometricMap W H G hp
    M.tail ⟨e, uibotWholePlaneGeometricMap_noMissing W H G hp e⟩ =
        wholePlaneEdgeWest W e.out.1 ∧
      M.head ⟨e, uibotWholePlaneGeometricMap_noMissing W H G hp e⟩ =
        wholePlaneEdgeEast W e.out.1 := by
  change (if !e.out.2 then wholePlaneDartVertex W e.out
      else wholePlaneDartVertex W (wholePlaneDartFlip W e.out)) = _ ∧
    (if !e.out.2 then wholePlaneDartVertex W (wholePlaneDartFlip W e.out)
      else wholePlaneDartVertex W e.out) = _
  rcases he : e.out with ⟨a, b⟩
  cases b <;> exact ⟨rfl, rfl⟩

/-- Helper toward Proposition 3.9: the geometric mark has initial vertex
equal to the west endpoint of the chronological `λ₀` edge. -/
theorem uibotWholePlaneGeometricRoot_initial (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    d39GeomRootVertex (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) =
        wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0) := by
  let e := Quotient.mk G.edgeSetoid (wholePlaneEdgeι W 0 0, false)
  change (if !e.out.2 then wholePlaneDartVertex W e.out
    else wholePlaneDartVertex W (wholePlaneDartFlip W e.out)) = _
  rcases G.geometricEdge_out_mk (wholePlaneEdgeι W 0 0, false) with h | h
  · change e.out = _ at h
    rw [h]
    rfl
  · change e.out = _ at h
    rw [h]
    rfl

/-- Helper toward Proposition 3.9: the whole-plane geometric realization
belongs to the local topology domain. Connectedness uses the actual dart system;
local finiteness counts geometric edge identities, including parallel edges. -/
theorem uibotWholePlaneGeometricMap_domain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    D39GeomDomain (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) := by
  classical
  let M := uibotWholePlaneGeometricMap W H G hp
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    obtain ⟨d, rfl⟩ := uibhbot_faceOrbit_dartVertex_surjective W H v
    obtain ⟨e, rfl⟩ := uibhbot_faceOrbit_dartVertex_surjective W H w
    have hf (a : WholePlaneDart W) : (d39GeomGraph M).Reachable
        (wholePlaneDartVertex W a) (wholePlaneDartVertex W (wholePlaneDartFlip W a)) := by
      by_cases he : wholePlaneDartVertex W a =
          wholePlaneDartVertex W (wholePlaneDartFlip W a)
      · rw [he]
      · apply SimpleGraph.Adj.reachable
        refine ⟨he, Quotient.mk G.edgeSetoid a, ?_⟩
        rcases G.geometricEdge_out_mk a with hout | hout
        · left
          change wholePlaneDartVertex W (Quotient.mk G.edgeSetoid a).out = _ ∧
            wholePlaneDartVertex W (wholePlaneDartFlip W
              (Quotient.mk G.edgeSetoid a).out) = _
          rw [hout]
          exact ⟨rfl, rfl⟩
        · right
          change wholePlaneDartVertex W (Quotient.mk G.edgeSetoid a).out = _ ∧
            wholePlaneDartVertex W (wholePlaneDartFlip W
              (Quotient.mk G.edgeSetoid a).out) = _
          rw [hout, wholePlaneDartFlip_involutive]
          exact ⟨rfl, rfl⟩
    have hwalk := wholePlaneDart_connected W H d e
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => exact SimpleGraph.Reachable.refl _
    | @head a b hab _ ih =>
      have hs : (d39GeomGraph M).Reachable
          (wholePlaneDartVertex W a) (wholePlaneDartVertex W b) := by
        rcases hab with hr | hr | he | he
        · rw [hr, wholePlaneRotation_preserves_dartVertex]
        · rw [hr]
          have hh := wholePlaneRotation_preserves_dartVertex W H
            ((wholePlaneRotation W H).symm a)
          rw [Equiv.apply_symm_apply] at hh
          rw [← hh]
        · rw [he]
          exact hf a
        · have hi : (wholePlaneDartFlip W).symm a = wholePlaneDartFlip W a := by
            apply (wholePlaneDartFlip W).injective
            rw [Equiv.apply_symm_apply, wholePlaneDartFlip_involutive]
          rw [he, hi]
          exact hf a
      exact hs.trans ih
  · intro v
    apply ((wholePlaneStar_finite W H v).image (Quotient.mk G.edgeSetoid)).subset
    intro e he
    rcases he with hs | ht
    · exact ⟨e.out, hs, Quotient.out_eq e⟩
    · exact ⟨wholePlaneDartFlip W e.out, ht,
        (G.geometricEdge_flip e.out).trans (Quotient.out_eq e)⟩
  · right
    exact ⟨uibotWholePlaneGeometricMap_noMissing W H G hp _, rfl⟩

section GeometricBalls

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H)
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "M" => uibotWholePlaneGeometricMap W H G hp
local notation "rho" => uibotWholePlaneGeometricRoot W H G

/-- Helper toward Proposition 3.9: geometric adjacency is exactly
colimit adjacency between distinct vertices, with all edge identities
retained before passing to the distance graph. -/
theorem uibotWholePlaneGeometricMap_adj_iff (v w : WholePlaneVertex W) :
    (d39GeomGraph M).Adj v w ↔ v ≠ w ∧ wholePlaneAdjacent W v w := by
  constructor
  · rintro ⟨hne, e, he⟩
    refine ⟨hne, e.out.1, ?_⟩
    change (wholePlaneDartVertex W e.out = v ∧
        wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = w) ∨
      (wholePlaneDartVertex W e.out = w ∧
        wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = v) at he
    rcases ho : e.out with ⟨a, b⟩
    rw [ho] at he
    cases b
    · exact he
    · change (wholePlaneEdgeEast W a = v ∧ wholePlaneEdgeWest W a = w) ∨
        (wholePlaneEdgeEast W a = w ∧ wholePlaneEdgeWest W a = v) at he
      rcases he with ⟨hv, hw⟩ | ⟨hw, hv⟩
      · exact Or.inr ⟨hw, hv⟩
      · exact Or.inl ⟨hv, hw⟩
  · rintro ⟨hne, a, ha⟩
    let e : G.GeometricEdge := Quotient.mk G.edgeSetoid (a, false)
    refine ⟨hne, e, ?_⟩
    change (wholePlaneDartVertex W e.out = v ∧
        wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = w) ∨
      (wholePlaneDartVertex W e.out = w ∧
        wholePlaneDartVertex W (wholePlaneDartFlip W e.out) = v)
    rcases G.geometricEdge_out_mk (a, false) with ho | ho
    · change e.out = (a, false) at ho
      rw [ho]
      exact ha
    · change e.out = wholePlaneDartFlip W (a, false) at ho
      rw [ho]
      change (wholePlaneEdgeEast W a = v ∧ wholePlaneEdgeWest W a = w) ∨
        (wholePlaneEdgeEast W a = w ∧ wholePlaneEdgeWest W a = v)
      rcases ha with ⟨hv, hw⟩ | ⟨hw, hv⟩
      · exact Or.inr ⟨hw, hv⟩
      · exact Or.inl ⟨hv, hw⟩

private theorem uibotGeometricWalk_wholePlanePath {v w : WholePlaneVertex W}
    (p : (d39GeomGraph M).Walk v w) : WholePlanePath W Set.univ v p.length w := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => exact .nil (Set.mem_univ _)
  | Hconcat p h ih =>
      rw [SimpleGraph.Walk.length_concat]
      exact .snoc ih (Set.mem_univ _) (Set.mem_univ _)
        ((uibotWholePlaneGeometricMap_adj_iff W H G hp _ _).mp h).2

private theorem uibotWholePlanePath_geometricDistanceLe {v w : WholePlaneVertex W}
    {n : ℕ} (p : WholePlanePath W Set.univ v n w) :
    (d39GeomGraph M).edist v w ≤ (n : ℕ∞) := by
  induction p with
  | nil => exact le_of_eq SimpleGraph.edist_self
  | @snoc n y z p hy hz h ih =>
      by_cases heq : y = z
      · subst z
        exact ih.trans (by exact_mod_cast Nat.le_succ n)
      · have hadj := (uibotWholePlaneGeometricMap_adj_iff W H G hp y z).mpr ⟨heq, h⟩
        calc
          (d39GeomGraph M).edist v z ≤
              (d39GeomGraph M).edist v y + (d39GeomGraph M).edist y z :=
            SimpleGraph.edist_triangle
          _ ≤ (n : ℕ∞) + 1 := add_le_add ih
            (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hadj))
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp only [Nat.cast_add, Nat.cast_one]

/-- Helper toward Proposition 3.9: the actual geometric local topology vertex ball
has precisely the colimit vertices at the same radius and chronological
root. This includes radius zero without an index shift. -/
theorem uibotWholePlaneGeometricBallVertices_eq_colimit (r : ℕ) :
    d39GeomBallVertices M rho r =
      wholePlaneBallVertices W r (wholePlaneEdgeWest W (wholePlaneEdgeι W 0 0)) := by
  ext v
  constructor
  · intro hv
    change (d39GeomGraph M).edist (d39GeomRootVertex M rho) v ≤ (r : ℕ∞) at hv
    have hfinite : (d39GeomGraph M).edist (d39GeomRootVertex M rho) v ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hv
    obtain ⟨p, hp'⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
    have hlen : p.length ≤ r := by exact_mod_cast (hp'.trans_le hv)
    have hpath := uibotGeometricWalk_wholePlanePath W H G hp p
    exact ⟨p.length, hlen, Eq.mp
      (congrArg (fun z => WholePlanePath W Set.univ z p.length v)
        (uibotWholePlaneGeometricRoot_initial W H G hp)) hpath⟩
  · rintro ⟨n, hn, hpath⟩
    change (d39GeomGraph M).edist (d39GeomRootVertex M rho) v ≤ (r : ℕ∞)
    rw [uibotWholePlaneGeometricRoot_initial]
    exact (uibotWholePlanePath_geometricDistanceLe W H G hp hpath).trans
      (by exact_mod_cast hn)

/-- Helper toward Proposition 3.9: a finite chronological-root capture
certificate identifies the vertex set of the geometric local topology ball with the
finite window image. Retained-face and ambient-homeomorphism transport
are not inferred from this vertex equality. -/
theorem uibotWholePlaneGeometricBallVertices_eq_window (N r : ℕ)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    d39GeomBallVertices M rho r = wholePlaneVertexι W N ''
      (↑(kmswStageBallVertices (fun _ _ => True)
        (kmswStage (shiftedStream W N) (2 * N)) r
        (activeInitial (shiftedStream W N) N)) : Set ℕ) := by
  rw [uibotWholePlaneGeometricBallVertices_eq_colimit]
  exact uibotWholePlane_rootBallVertices_eq_window W N r hcap

end GeometricBalls

end

/- OPEN unit 3, exact next geometric comparison target (not a declaration).
The names `StageDrawing`, `StageGeom`, and `kmswStageDrawingDirectedPlaneMap`
are provided by PaperProofs/Section5/Prop516StageDrawingBaseRepresentation.

For all (ell right n N r : ℕ) (hn : 1 ≤ n) (hr : 0 < r),
  (c : KMSWWalkClass ell right n) (j : Fin n),
  (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W),
  (G : WholePlaneDrawing W H),
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
  (P : StageDrawing (codeExtend c) (n - 1)),
  (Q : StageGeom (codeExtend c) (n - 1) P),
  (hwindow : uibotFiniteRootWindow N c.val j =
    some (fun i => shiftedStream W N i.val)),
  (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r),
let d : StageDart (kmswStage (codeExtend c) (n - 1)).nextEdge :=
  (⟨act (codeExtend c) j.val,
    act_lt_nextEdge (codeExtend c) (by have := j.isLt; omega)⟩, false)
let e := Quotient.mk P.edgeSetoid d
the required conclusion is
  Nonempty (D39GeomBallIsoV2 r
    (kmswStageDrawingDirectedPlaneMap P Q) (e, !e.out.2)
    (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G)).

The code above proves chronological root transport, finite-stage vertex
capture, colimit edge-identity bijection, and geometric vertex capture.
It does not supply this isomorphism's single ambient orientation-preserving
homeomorphism, arc reparameterizations, or retained-original-face equivalence.
Then identify the finite geometric rooted stage with the Peano rooting of
`kmswProcedureEquiv ell right n hn c`, for every representative of that class.
This representative/root transport is also still required before law transport. -/

end DirectedDistances.PaperProofs.Section3
