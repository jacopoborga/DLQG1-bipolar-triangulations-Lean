/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.BoundaryEnumeration
public import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.OutgoingIntervalFreshLeft
import DirectedDistances.KMSW.AllocatedVertices
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.SDPIdentifyBdy

/-! # A corner-based outgoing path helper

Helper toward Lemma 5.12 (`lem-flow-line-times`), item (ii), along `β₀`
leftmost directed path in `M_{0,∞}` from `λ₀⁻` to infinity
using the incoming/outgoing cyclic order
corners with those source corners and does not prove the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- The geometric endpoint of a dart in the limiting rotation. The Boolean is
the endpoint tag in the rotation system; it is used to locate geometry, not to
turn a missing edge into a directed edge (`remark-kmsw-infinite`, -/
@[expose] def kmswDartEndpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

/-- A dart is eligible for a directed outgoing choice exactly when it is the
west dart of a present edge. Missing darts remain in the geometric rotation,
but are never eligible (`defn-planar-map-with-missing-edges`, -/
@[expose] def kmswPresentOutgoingDart (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  d.2 = false ∧ EdgePresent w d.1

/-- Some rotation iterate from a corner at `v` is a present outgoing dart
whenever `v` has one. Finite incidence supplies the geometric rotation;
outgoing existence is an explicit helper premise, discharged for the source
model by the no-sink clause of `lem-uibot-bdy` -/
theorem kmswFirstOutgoingAtCorner_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    ∃ n, kmswPresentOutgoingDart w ((kmswInfRot w hfin ^ n) corner) := by
  obtain ⟨e, he, hew⟩ := hout
  have hend :
      (if corner.2 then edgeEast w corner.1 else edgeWest w corner.1) =
        (if false then edgeEast w e else edgeWest w e) := by
    simpa [kmswDartEndpoint] using hcorner.trans hew.symm
  obtain ⟨n, hn⟩ :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin corner (e, false)).2 hend
  refine ⟨n, ?_⟩
  rw [hn]
  exact ⟨rfl, he⟩

/-- The first index at which the rotation from `corner` reaches a present
outgoing dart. All intervening geometric darts, including missing ones, are
still traversed in the cyclic order; only a present outgoing dart can satisfy
the predicate. `corner` must be chosen from the source's left boundary corner
before this is the paper's leftmost edge. Helper toward `lem-flow-line-times` -/
@[expose] noncomputable def kmswFirstOutgoingIndex (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) : ℕ := by
  classical
  exact Nat.find (kmswFirstOutgoingAtCorner_exists w hfin corner v hcorner hout)

/-- The edge reached at the first present outgoing dart after the supplied
geometric corner. This is a rotation-order selector; identifying its corner
with the paper's incoming-to-outgoing transition is a separate obligation -/
@[expose] noncomputable def kmswFirstOutgoingAfterCorner (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) : ℕ :=
  ((kmswInfRot w hfin ^ kmswFirstOutgoingIndex w hfin corner v hcorner hout) corner).1

/-- The corner selector returns a present edge directed out of `v`.
result. -/
theorem kmswFirstOutgoingAfterCorner_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    EdgePresent w (kmswFirstOutgoingAfterCorner w hfin corner v hcorner hout) ∧
      edgeWest w (kmswFirstOutgoingAfterCorner w hfin corner v hcorner hout) = v := by
  classical
  let hfirst := kmswFirstOutgoingAtCorner_exists w hfin corner v hcorner hout
  let n := Nat.find hfirst
  let d := (kmswInfRot w hfin ^ n) corner
  change EdgePresent w d.1 ∧ edgeWest w d.1 = v
  have hd := Nat.find_spec hfirst
  change kmswPresentOutgoingDart w d at hd
  refine ⟨hd.2, ?_⟩
  have heq := (kmswInfRot_exists_pow_iff_endpoint w hfin corner d).1 ⟨n, rfl⟩
  calc
    edgeWest w d.1 = kmswDartEndpoint w d := by
      simp [kmswDartEndpoint, hd.1]
    _ = kmswDartEndpoint w corner := heq.symm
    _ = v := hcorner

/-- The selected outgoing dart is first in the forward rotation scan from the
supplied corner: every earlier iterate fails to be a present outgoing dart.
This states leftmostness relative to that corner only; the paper's canonical
corner remains to be identified. Helper toward `lem-flow-line-times` (`β₀`); -/
theorem kmswFirstOutgoingIndex_min (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) (n : ℕ)
    (hn : kmswPresentOutgoingDart w ((kmswInfRot w hfin ^ n) corner)) :
    kmswFirstOutgoingIndex w hfin corner v hcorner hout ≤ n :=
  by
    classical
    exact Nat.find_min' (kmswFirstOutgoingAtCorner_exists w hfin corner v hcorner hout) hn

/-- In the one-sided KMSW map, the boundary witness's unbounded-below right
coordinate and finite incidence imply an outgoing present edge at every
vertex. This reuses the no-sink result from `lem-uibot-bdy`
toward `lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswM0_vertex_outgoing (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (v : ℕ) :
    ∃ e, EdgePresent w e ∧ edgeWest w e = v := by
  exact uibot_allocated_vertex_outgoing w h.R_unbounded_below v
    (kmsw_vertex_allocated_of_finite_incidence w hfin v)

/-- The vertex reached after `n` steps of the corner-first directed stream
from `λ₀⁻`, whose KMSW vertex ID is zero. `corner` and `hcorner` are explicit
geometric cut data; the identification with the canonical leftmost corners of
`M_{0,∞}` is not proved here (`eqn-north-flow-line`, -/
@[expose] noncomputable def kmswBeta0CandidateVertex (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (corner : ℕ → ℕ × Bool)
    (hcorner : ∀ v, kmswDartEndpoint w (corner v) = v) : ℕ → ℕ :=
  Nat.rec 0 (fun _ v => edgeEast w
    (kmswFirstOutgoingAfterCorner w hfin (corner v) v (hcorner v)
      (kmswM0_vertex_outgoing w hfin h v)))

/-- The edge stream obtained by iterating the corner-first selector from
a conditional helper stream, not the paper's `β₀`, until `corner` is proved to
be the source's geometric leftmost corner at every visited vertex. Helper
toward `lem-flow-line-times` (`β₀`); not the paper result -/
@[expose] noncomputable def kmswBeta0CandidateEdges (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (corner : ℕ → ℕ × Bool)
    (hcorner : ∀ v, kmswDartEndpoint w (corner v) = v) (n : ℕ) : ℕ :=
  kmswFirstOutgoingAfterCorner w hfin
    (corner (kmswBeta0CandidateVertex w hfin h corner hcorner n))
    (kmswBeta0CandidateVertex w hfin h corner hcorner n)
    (hcorner (kmswBeta0CandidateVertex w hfin h corner hcorner n))
    (kmswM0_vertex_outgoing w hfin h
      (kmswBeta0CandidateVertex w hfin h corner hcorner n))

/-- Every edge in the candidate stream is present and leaves its recursively
defined current vertex (`eqn-north-flow-line`, -/
theorem kmswBeta0CandidateEdges_present (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (corner : ℕ → ℕ × Bool)
    (hcorner : ∀ v, kmswDartEndpoint w (corner v) = v) (n : ℕ) :
    EdgePresent w (kmswBeta0CandidateEdges w hfin h corner hcorner n) ∧
      edgeWest w (kmswBeta0CandidateEdges w hfin h corner hcorner n) =
        kmswBeta0CandidateVertex w hfin h corner hcorner n := by
  exact (kmswFirstOutgoingAfterCorner_spec w hfin
    (corner (kmswBeta0CandidateVertex w hfin h corner hcorner n))
    (kmswBeta0CandidateVertex w hfin h corner hcorner n)
    (hcorner (kmswBeta0CandidateVertex w hfin h corner hcorner n))
    (kmswM0_vertex_outgoing w hfin h
      (kmswBeta0CandidateVertex w hfin h corner hcorner n)))

/-- The first candidate edge starts at `λ₀⁻` (ID zero)
`lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswBeta0CandidateEdges_start (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (corner : ℕ → ℕ × Bool)
    (hcorner : ∀ v, kmswDartEndpoint w (corner v) = v) :
    edgeWest w (kmswBeta0CandidateEdges w hfin h corner hcorner 0) = 0 := by
  exact (kmswFirstOutgoingAfterCorner_spec w hfin (corner 0) 0 (hcorner 0)
    (kmswM0_vertex_outgoing w hfin h 0)).2

/-- Consecutive candidate edges meet head-to-tail, so the stream is an actual
infinite directed path in the present-edge graph
`lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswBeta0CandidateEdges_chain (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (corner : ℕ → ℕ × Bool)
    (hcorner : ∀ v, kmswDartEndpoint w (corner v) = v) (n : ℕ) :
    edgeEast w (kmswBeta0CandidateEdges w hfin h corner hcorner n) =
      edgeWest w (kmswBeta0CandidateEdges w hfin h corner hcorner (n + 1)) := by
  let v := kmswBeta0CandidateVertex w hfin h corner hcorner n
  change edgeEast w
      (kmswFirstOutgoingAfterCorner w hfin (corner v) v (hcorner v)
        (kmswM0_vertex_outgoing w hfin h v)) =
    edgeWest w
      (kmswFirstOutgoingAfterCorner w hfin (corner (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1)))
        (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1))
        (hcorner (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1)))
        (kmswM0_vertex_outgoing w hfin h
          (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1))))
  rw [show kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1) =
      edgeEast w (kmswBeta0CandidateEdges w hfin h corner hcorner n) by rfl]
  exact (kmswFirstOutgoingAfterCorner_spec w hfin
    (corner (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1)))
    (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1))
    (hcorner (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1)))
    (kmswM0_vertex_outgoing w hfin h
      (kmswBeta0CandidateVertex w hfin h corner hcorner (n + 1)))).2.symm

/-! ### Reverse-rotation selectors

Forward counterclockwise rotation lists outgoing darts from rightmost to
leftmost (`LeftmostGeodesic.lean:26`,
`LeftmostGeodesicUIQBOT.lean:337`). Therefore the leftmost choice scans with
`(kmswInfRot w hfin).symm`, from the incoming dart at the end of the outgoing
block in forward order. These remain helpers toward `lem-flow-line-times`
(`β₀`); they are not the paper result. -/

private theorem perm_symm_pow_apply_pow {α : Type*} (σ : Equiv.Perm α)
    (n : ℕ) (x : α) : (σ.symm ^ n) ((σ ^ n) x) = x := by
  have hmul : σ.symm ^ n * σ ^ n = 1 := by
    change (σ⁻¹) ^ n * σ ^ n = 1
    rw [inv_pow]
    exact inv_mul_cancel _
  rw [← Equiv.Perm.mul_apply, hmul]
  rfl

private theorem perm_pow_apply_symm_pow {α : Type*} (σ : Equiv.Perm α)
    (n : ℕ) (x : α) : (σ ^ n) ((σ.symm ^ n) x) = x := by
  have hmul : σ ^ n * σ.symm ^ n = 1 := by
    change σ ^ n * (σ⁻¹) ^ n = 1
    rw [inv_pow]
    exact mul_inv_cancel _
  rw [← Equiv.Perm.mul_apply, hmul]
  rfl

private theorem perm_apply_symm_pow_succ {α : Type*} (σ : Equiv.Perm α)
    (n : ℕ) (x : α) : σ ((σ.symm ^ (n + 1)) x) = (σ.symm ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc
      σ ((σ.symm ^ ((n + 1) + 1)) x) =
          σ ((σ.symm ^ (n + 1)) (σ.symm x)) := by
            rw [pow_succ, Equiv.Perm.mul_apply]
      _ = (σ.symm ^ n) (σ.symm x) := ih _
      _ = (σ.symm ^ (n + 1)) x := by
            rw [pow_succ, Equiv.Perm.mul_apply]

/-- Some reverse-rotation iterate from a corner at `v` is a present outgoing
dart whenever `v` has one. Helper toward `lem-flow-line-times` (`β₀`); -/
theorem kmswFirstOutgoingAtCorner_symm_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    ∃ n, kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ n) corner) := by
  obtain ⟨e, he, hew⟩ := hout
  have hend :
      (if corner.2 then edgeEast w corner.1 else edgeWest w corner.1) =
        (if false then edgeEast w e else edgeWest w e) := by
    simpa [kmswDartEndpoint] using hcorner.trans hew.symm
  obtain ⟨n, hn⟩ :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin (e, false) corner).2 hend.symm
  refine ⟨n, ?_⟩
  rw [← hn, perm_symm_pow_apply_pow]
  exact ⟨rfl, he⟩

/-- The first index at which the reverse rotation from `corner` reaches a
present outgoing dart. Helper toward `lem-flow-line-times` (`β₀`); not the -/
@[expose] noncomputable def kmswFirstOutgoingIndex_symm (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) : ℕ := by
  classical
  exact Nat.find (kmswFirstOutgoingAtCorner_symm_exists w hfin corner v hcorner hout)

/-- The edge reached at the first present outgoing dart in the reverse
rotation scan. Helper toward `lem-flow-line-times` (`β₀`); not the paper result -/
@[expose] noncomputable def kmswFirstOutgoingAfterCorner_symm (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) : ℕ :=
  (((kmswInfRot w hfin).symm ^
    kmswFirstOutgoingIndex_symm w hfin corner v hcorner hout) corner).1

/-- The reverse-scan selector returns a present edge directed out of `v`.
Helper toward `lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswFirstOutgoingAfterCorner_symm_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    EdgePresent w (kmswFirstOutgoingAfterCorner_symm w hfin corner v hcorner hout) ∧
      edgeWest w (kmswFirstOutgoingAfterCorner_symm w hfin corner v hcorner hout) = v := by
  classical
  let hfirst := kmswFirstOutgoingAtCorner_symm_exists w hfin corner v hcorner hout
  let n := Nat.find hfirst
  let d := ((kmswInfRot w hfin).symm ^ n) corner
  change EdgePresent w d.1 ∧ edgeWest w d.1 = v
  have hd := Nat.find_spec hfirst
  change kmswPresentOutgoingDart w d at hd
  refine ⟨hd.2, ?_⟩
  have hforward : ∃ k, (kmswInfRot w hfin ^ k) d = corner := by
    refine ⟨n, ?_⟩
    change (kmswInfRot w hfin ^ n)
      (((kmswInfRot w hfin).symm ^ n) corner) = corner
    exact perm_pow_apply_symm_pow (kmswInfRot w hfin) n corner
  have heq := (kmswInfRot_exists_pow_iff_endpoint w hfin d corner).1 hforward
  change kmswDartEndpoint w d = kmswDartEndpoint w corner at heq
  calc
    edgeWest w d.1 = kmswDartEndpoint w d := by
      simp [kmswDartEndpoint, hd.1]
    _ = kmswDartEndpoint w corner := heq
    _ = v := hcorner

/-- The selected dart is first among present outgoing darts in the reverse
rotation scan: every earlier iterate fails to be present outgoing. The scan
orientation is the reverse of the documented counterclockwise order
(`LeftmostGeodesic.lean:26`, `LeftmostGeodesicUIQBOT.lean:337`). Helper toward
`lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswFirstOutgoingIndex_symm_min (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (corner : ℕ × Bool) (v : ℕ)
    (hcorner : kmswDartEndpoint w corner = v)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v) (n : ℕ)
    (hn : kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ n) corner)) :
    kmswFirstOutgoingIndex_symm w hfin corner v hcorner hout ≤ n := by
  classical
  exact Nat.find_min'
    (kmswFirstOutgoingAtCorner_symm_exists w hfin corner v hcorner hout) hn

private theorem kmswM0_not_present_has_LL_occurrence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (e : ℕ) (hne : ¬ EdgePresent w e) :
    ∃ n, e ∈ (kmswStage w n).LL := by
  have halloc := kmsw_edge_allocated_by_self w e
  have hfalse : (kmswStage w e).present e = false := by
    cases hp : (kmswStage w e).present e with
    | false => rfl
    | true => exact (hne ⟨e, halloc, hp⟩).elim
  have hstatus := ((kmswStage_status w e).1 e halloc).mp hfalse
  rcases hstatus with hUR | hLL
  · obtain ⟨m, hem, hpresent⟩ :=
      kmswStage_UR_edge_eventually_present_of_R_unbounded w h.R_unbounded_below e e hUR
    have hallocm : e < (kmswStage w m).nextEdge :=
      halloc.trans_le (kmswStage_nextEdge_mono w hem)
    exact (hne ⟨m, hallocm, hpresent⟩).elim
  · exact ⟨e, hLL⟩

private theorem kmswM0_not_present_endpoints_are_nonpos_boundary
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (e : ℕ)
    (hne : ¬ EdgePresent w e) :
    (∃ k : ℤ, k ≤ -1 ∧ edgeWest w e = boundaryVertex w h k) ∧
      (∃ k : ℤ, k ≤ 0 ∧ edgeEast w e = boundaryVertex w h k) := by
  obtain ⟨n, heLL⟩ := kmswM0_not_present_has_LL_occurrence w h e hne
  rw [kmswStage_LL_eq] at heLL
  obtain ⟨m, hm, hem⟩ := List.mem_map.mp heLL
  have hm' := List.mem_reverse.mp hm
  have hrecord : 0 < m ∧ ∀ j < m, L w m < L w j :=
    of_decide_eq_true (List.mem_filter.mp hm').2
  let k := L w m
  have hk : k ≤ -1 := by
    have hzero : L w 0 = 0 := by simp [L]
    have hlt := hrecord.2 0 (by omega)
    dsimp [k] at hlt ⊢
    omega
  have hfind : Nat.find (h.leftHit k hk) = m := by
    apply le_antisymm
    · exact Nat.find_min' (h.leftHit k hk) (show L w m = k by rfl)
    · by_contra hlt
      have hvalue := Nat.find_spec (h.leftHit k hk)
      have hstrict := hrecord.2 (Nat.find (h.leftHit k hk)) (by omega)
      change L w (Nat.find (h.leftHit k hk)) = k at hvalue
      dsimp [k] at hstrict hvalue
      omega
  have htime : boundaryHitTime w h k = m := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : k ≠ 0),
      dite_eq_right (by omega : ¬ 0 < k)]
    exact hfind
  have heq : e = kmswLLCreatedEdge w m := by simpa using hem.symm
  have hleft := boundaryVertex_left_missing_edge w h hk
  rw [htime] at hleft
  change (kmswStage w m).west (kmswLLCreatedEdge w m) = boundaryVertex w h k ∧
    (kmswStage w m).east (kmswLLCreatedEdge w m) = boundaryVertex w h (k + 1) ∧
    (kmswStage w m).present (kmswLLCreatedEdge w m) = false at hleft
  have hnext : 1 ≤ (kmswStage w m).nextEdge := by
    have hm := kmswStage_nextEdge_mono w (m := 0) (n := m) (Nat.zero_le _)
    simpa [kmswStage, kmswInit] using hm
  have hallocm : kmswLLCreatedEdge w m < (kmswStage w m).nextEdge := by
    simp only [kmswLLCreatedEdge]
    omega
  have hend := edge_endpoints_eq w hallocm
  refine ⟨⟨k, hk, ?_⟩, ⟨k + 1, by omega, ?_⟩⟩
  · rw [heq]
    exact hend.1.symm.trans hleft.1
  · rw [heq]
    exact hend.2.symm.trans hleft.2.1

private theorem kmswM0_incident_edges_present_of_incoming
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v)
    (d : ℕ × Bool)
    (hdv : kmswDartEndpoint w d = v) : EdgePresent w d.1 := by
  by_contra hmissing
  obtain ⟨⟨k, hk, hwest⟩, ⟨l, hl,heast⟩⟩ :=
    kmswM0_not_present_endpoints_are_nonpos_boundary w h d.1 hmissing
  have hnoWest := boundaryVertex_nonpos_no_incoming w h (k := k) (by omega)
  have hnoEast := boundaryVertex_nonpos_no_incoming w h (k := l) hl
  rcases hin with ⟨f, hf, hfv⟩
  by_cases htag : d.2
  · have hde : edgeEast w d.1 = v := by simpa [kmswDartEndpoint, htag] using hdv
    apply hnoEast f hf
    exact hfv.trans (hde.symm.trans heast)
  · have hdw : edgeWest w d.1 = v := by simpa [kmswDartEndpoint, htag] using hdv
    apply hnoWest f hf
    exact hfv.trans (hdw.symm.trans hwest)

/-- The least edge ID of an incoming present edge supplies a geometric corner
at `v`. Helper toward `lem-flow-line-times` (`β₀`); not the paper result -/
@[expose] noncomputable def kmswM0IncomingSeedCorner (w : ℕ → Fin 3)
    (v : ℕ) (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v) : ℕ × Bool := by
  classical
  exact (Nat.find hin, true)

/-- The seed corner is an incoming present dart based at `v`. Helper toward
`lem-flow-line-times` (`β₀`); not the paper result -/
theorem kmswM0IncomingSeedCorner_spec (w : ℕ → Fin 3) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v) :
    EdgePresent w (kmswM0IncomingSeedCorner w v hin).1 ∧
      edgeEast w (kmswM0IncomingSeedCorner w v hin).1 = v ∧
      kmswDartEndpoint w (kmswM0IncomingSeedCorner w v hin) = v := by
  classical
  have hs := Nat.find_spec hin
  refine ⟨hs.1, hs.2, ?_⟩
  change edgeEast w (Nat.find hin) = v
  exact hs.2

/-- The edge first reached by the reverse scan from the least incoming
present dart at `v`. Helper toward `lem-flow-line-times` (`β₀`); not the paper -/
@[expose] noncomputable def kmswM0LeftmostOutgoingEdge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v) : ℕ :=
  kmswFirstOutgoingAfterCorner_symm w hfin (kmswM0IncomingSeedCorner w v hin) v
    (kmswM0IncomingSeedCorner_spec w v hin).2.2
    (kmswM0_vertex_outgoing w hfin h v)

/-- For a vertex with an incoming present edge, reverse scanning from the
least incoming present dart selects the leftmost present outgoing edge. Its
forward successor is an incoming present dart, and every other present
outgoing dart precedes it through the outgoing interval. The reverse scan is
used because forward counterclockwise order lists outgoing darts rightmost to
leftmost (`LeftmostGeodesic.lean:26`, `LeftmostGeodesicUIQBOT.lean:337`;
`kmswInfRot_outgoing_interval_all`). Helper toward `lem-flow-line-times` -/
theorem kmswM0LeftmostOutgoingEdge_characterization (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hin : ∃ e, EdgePresent w e ∧ edgeEast w e = v) :
    let e := kmswM0LeftmostOutgoingEdge w hfin h v hin
    EdgePresent w e ∧ edgeWest w e = v ∧
      ∃ f, EdgePresent w f ∧ edgeEast w f = v ∧
        kmswInfRot w hfin (e, false) = (f, true) ∧
        ∀ g, EdgePresent w g → edgeWest w g = v →
          RotationArc (kmswInfRot w hfin)
            (fun d : ℕ × Bool => d.2 = false ∧ EdgePresent w d.1)
            (g, false) (e, false) := by
  classical
  let c := kmswM0IncomingSeedCorner w v hin
  let hout := kmswM0_vertex_outgoing w hfin h v
  let hfirst := kmswFirstOutgoingAtCorner_symm_exists w hfin c v
    (kmswM0IncomingSeedCorner_spec w v hin).2.2 hout
  let n := Nat.find hfirst
  let d := ((kmswInfRot w hfin).symm ^ n) c
  have hd := Nat.find_spec hfirst
  have hspec := kmswFirstOutgoingAfterCorner_symm_spec w hfin c v
    (kmswM0IncomingSeedCorner_spec w v hin).2.2 hout
  change EdgePresent w d.1 ∧ edgeWest w d.1 = v at hspec
  change kmswPresentOutgoingDart w d at hd
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hfalse : c.2 = false := by simpa [d, hn0] using hd.1
    simp [c, kmswM0IncomingSeedCorner] at hfalse
  have hdtag : d.2 = false := hd.1
  have hdepoint : kmswDartEndpoint w d = v := by
    simpa [kmswDartEndpoint, hdtag] using hspec.2
  let q := kmswInfRot w hfin d
  have hqpoint : kmswDartEndpoint w q = v := by
    have hrot : kmswDartEndpoint w d = kmswDartEndpoint w q := by
      have hex : ∃ k, (kmswInfRot w hfin ^ k) d = q := by
        refine ⟨1, ?_⟩
        simp [q]
      exact (kmswInfRot_exists_pow_iff_endpoint w hfin d q).1 hex
    exact hrot.symm.trans hdepoint
  have hqpresent := kmswM0_incident_edges_present_of_incoming w h v hin q hqpoint
  have hpredIndex : q = ((kmswInfRot w hfin).symm ^ (n - 1)) c := by
    dsimp [q, d]
    have hs : (n - 1) + 1 = n := by omega
    rw [← hs]
    exact perm_apply_symm_pow_succ (kmswInfRot w hfin) (n - 1) c
  have hnot := Nat.find_min hfirst (by omega : n - 1 < n)
  have hqtag : q.2 = true := by
    by_cases htag : q.2 = true
    · exact htag
    · have htag' : q.2 = false := by cases hb : q.2 <;> simp_all
      have hp : kmswPresentOutgoingDart w
          (((kmswInfRot w hfin).symm ^ (n - 1)) c) := by
        rw [← hpredIndex]
        exact ⟨htag', hqpresent⟩
      exact (hnot hp).elim
  have hqeast : edgeEast w q.1 = v := by
    simpa [kmswDartEndpoint, hqtag] using hqpoint
  have hdeq : d = (d.1, false) := Prod.ext rfl hdtag
  have hqeq : q = kmswInfRot w hfin (d.1, false) := by
    dsimp [q]
    rw [hdeq]
  have hleft (g : ℕ) (hg : EdgePresent w g) (hgv : edgeWest w g = v) :
      RotationArc (kmswInfRot w hfin)
        (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
        (g, false) (d.1, false) := by
    by_cases hge : g = d.1
    · subst g
      exact RotationArc.refl _ _ _ ⟨rfl, hspec.1⟩
    · have hinterval := kmswInfRot_outgoing_interval_all w hfin d.1 g
        (hspec.2.trans hgv.symm) hspec.1 hg
      rcases hinterval with hforward | hbackward
      · obtain ⟨k, hk, hall⟩ := hforward
        by_cases hk0 : k = 0
        · have heq : (d.1, false) = (g, false) := by
            simpa [hk0] using hk
          exact (hge (congrArg Prod.fst heq).symm).elim
        · have hstep := hall 1 (by omega)
          have hstep' : (kmswInfRot w hfin (d.1, false)).2 = false ∧
              EdgePresent w (kmswInfRot w hfin (d.1, false)).1 := by
            simpa only [pow_one] using hstep
          have hqout : kmswPresentOutgoingDart w q := by
            change q.2 = false ∧ EdgePresent w q.1
            rw [hqeq]
            exact hstep'
          have : q.2 = false := hqout.1
          simp [hqtag] at this
      · exact hbackward
  let e := kmswM0LeftmostOutgoingEdge w hfin h v hin
  change EdgePresent w d.1 ∧ edgeWest w d.1 = v ∧
      ∃ f, EdgePresent w f ∧ edgeEast w f = v ∧
        kmswInfRot w hfin (d.1, false) = (f, true) ∧
        ∀ g, EdgePresent w g → edgeWest w g = v →
          RotationArc (kmswInfRot w hfin)
            (fun x : ℕ × Bool => x.2 = false ∧ EdgePresent w x.1)
            (g, false) (d.1, false)
  refine ⟨hspec.1, hspec.2, ?_⟩
  refine ⟨q.1, hqpresent, hqeast, ?_, ?_⟩
  · calc
      kmswInfRot w hfin (d.1, false) = q := hqeq.symm
      _ = (q.1, true) := Prod.ext rfl hqtag
  · intro g hg hgv
    exact hleft g hg hgv

/-- The reverse dart of a present incoming edge is the corner at its head
from which the leftmost continuation is selected. Helper toward Lemma 5.12 -/
@[expose] def kmswBeta0IncomingCorner {w : ℕ → Fin 3}
    (e : {f : ℕ // EdgePresent w f}) : ℕ × Bool := (e.1, true)

/-- The incoming-corner endpoint is the head of its present edge. Helper
toward Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0IncomingCorner_spec {w : ℕ → Fin 3}
    (e : {f : ℕ // EdgePresent w f}) :
    kmswDartEndpoint w (kmswBeta0IncomingCorner e) = edgeEast w e.1 := by
  simp [kmswBeta0IncomingCorner, kmswDartEndpoint]

/-- The leftmost continuation of a present incoming edge, selected from its
reverse dart by scanning the inverse limiting rotation. Helper toward Lemma -/
@[expose] noncomputable def kmswBeta0Next (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (e : {f : ℕ // EdgePresent w f}) : {f : ℕ // EdgePresent w f} := by
  let c := kmswBeta0IncomingCorner e
  let v := edgeEast w e.1
  let hout := kmswM0_vertex_outgoing w hfin h v
  exact ⟨kmswFirstOutgoingAfterCorner_symm w hfin c v
    (kmswBeta0IncomingCorner_spec e) hout,
    (kmswFirstOutgoingAfterCorner_symm_spec w hfin c v
      (kmswBeta0IncomingCorner_spec e) hout).1⟩

/-- The continuation edge is present, leaves the incoming edge's head, and
is first in the inverse rotation scan among present outgoing darts. Helper
toward Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0Next_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (e : {f : ℕ // EdgePresent w f}) :
    EdgePresent w (kmswBeta0Next w hfin h e).1 ∧
      edgeWest w (kmswBeta0Next w hfin h e).1 = edgeEast w e.1 ∧
      ∀ n, n < kmswFirstOutgoingIndex_symm w hfin
          (kmswBeta0IncomingCorner e) (edgeEast w e.1)
          (kmswBeta0IncomingCorner_spec e)
          (kmswM0_vertex_outgoing w hfin h (edgeEast w e.1)) →
        ¬ kmswPresentOutgoingDart w
          (((kmswInfRot w hfin).symm ^ n) (kmswBeta0IncomingCorner e)) := by
  classical
  let c := kmswBeta0IncomingCorner e
  let v := edgeEast w e.1
  let hout := kmswM0_vertex_outgoing w hfin h v
  have hspec := kmswFirstOutgoingAfterCorner_symm_spec w hfin c v
    (kmswBeta0IncomingCorner_spec e) hout
  refine ⟨(kmswBeta0Next w hfin h e).2, ?_, ?_⟩
  · change edgeWest w
      (kmswFirstOutgoingAfterCorner_symm w hfin c v
        (kmswBeta0IncomingCorner_spec e) hout) = v
    exact hspec.2
  · intro n hn
    exact Nat.find_min
      (kmswFirstOutgoingAtCorner_symm_exists w hfin c v
        (kmswBeta0IncomingCorner_spec e) hout) hn

/-- Every distinct present outgoing edge at the head of `e` occurs strictly
later in the inverse rotation scan than `kmswBeta0Next e`. Helper toward
Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0Next_later (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (e : {f : ℕ // EdgePresent w f}) (g : ℕ)
    (hg : EdgePresent w g) (hgv : edgeWest w g = edgeEast w e.1)
    (hne : g ≠ (kmswBeta0Next w hfin h e).1) :
    ∃ m, kmswFirstOutgoingIndex_symm w hfin
        (kmswBeta0IncomingCorner e) (edgeEast w e.1)
        (kmswBeta0IncomingCorner_spec e)
        (kmswM0_vertex_outgoing w hfin h (edgeEast w e.1)) < m ∧
      ((kmswInfRot w hfin).symm ^ m) (kmswBeta0IncomingCorner e) = (g, false) := by
  classical
  let c := kmswBeta0IncomingCorner e
  let v := edgeEast w e.1
  let hout := kmswM0_vertex_outgoing w hfin h v
  let hcorner := kmswBeta0IncomingCorner_spec e
  let hfirst := kmswFirstOutgoingAtCorner_symm_exists w hfin c v hcorner hout
  let n := kmswFirstOutgoingIndex_symm w hfin c v hcorner hout
  have hc : kmswDartEndpoint w c = v := hcorner
  have hend : kmswDartEndpoint w (g, false) = kmswDartEndpoint w c := by
    change edgeWest w g = kmswDartEndpoint w c
    exact hgv.trans hc.symm
  obtain ⟨m, hm⟩ :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin (g, false) c).2 hend
  have hinv : ((kmswInfRot w hfin).symm ^ m) c = (g, false) := by
    have ht := congrArg ((kmswInfRot w hfin).symm ^ m) hm
    rw [perm_symm_pow_apply_pow] at ht
    exact ht.symm
  have hselected : ((kmswInfRot w hfin).symm ^ n) c =
      ((kmswBeta0Next w hfin h e).1, false) := by
    have htag : (((kmswInfRot w hfin).symm ^ n) c).2 = false := by
      have hs := Nat.find_spec hfirst
      change kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ n) c) at hs
      exact hs.1
    have hfst : (((kmswInfRot w hfin).symm ^ n) c).1 =
        (kmswBeta0Next w hfin h e).1 := by
      change (((kmswInfRot w hfin).symm ^ n) c).1 =
        kmswFirstOutgoingAfterCorner_symm w hfin c v hcorner hout
      rfl
    exact Prod.ext hfst htag
  have hlt : n < m := by
    by_contra hnot
    have hmle : m ≤ n := by omega
    by_cases hmn : m = n
    · have heq : (g, false) = ((kmswBeta0Next w hfin h e).1, false) := by
        calc
          (g, false) = ((kmswInfRot w hfin).symm ^ m) c := hinv.symm
          _ = ((kmswInfRot w hfin).symm ^ n) c := by rw [hmn]
          _ = ((kmswBeta0Next w hfin h e).1, false) := hselected
      exact hne (congrArg Prod.fst heq)
    · have hmn' : m < n := by omega
      have hbad := Nat.find_min hfirst hmn'
      have hp : kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ m) c) := by
        rw [hinv]
        exact ⟨rfl, hg⟩
      exact (hbad hp).elim
  exact ⟨m, hlt, hinv⟩

/-- The dart of the missing lower-left root edge based at vertex zero. The
edge remains geometric in the rotation system while carrying no directed
B3 (`β₀`); not the paper result. -/
@[expose] noncomputable def kmswBeta0RootCorner (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) : ℕ × Bool :=
  (kmswLLCreatedEdge w (boundaryHitTime w h (-1)), true)

/-- The missing lower-left edge dart is geometrically based at the root.
Helper toward Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0RootCorner_endpoint (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) :
    kmswDartEndpoint w (kmswBeta0RootCorner w h) = 0 := by
  have hroot := boundaryVertex_left_root_missing_edge w h
  have hnext : 0 < (kmswStage w (boundaryHitTime w h (-1))).nextEdge := by
    have hmono := kmswStage_nextEdge_mono w (Nat.zero_le (boundaryHitTime w h (-1)))
    simp [kmswStage, kmswInit] at hmono
    omega
  have halloc : kmswLLCreatedEdge w (boundaryHitTime w h (-1)) <
      (kmswStage w (boundaryHitTime w h (-1))).nextEdge := by
    dsimp [kmswLLCreatedEdge]
    omega
  have hend := edge_endpoints_eq w halloc
  change edgeEast w (kmswLLCreatedEdge w (boundaryHitTime w h (-1))) = 0
  rw [← hend.2]
  exact hroot.2.1

/-- The first present edge leaving vertex zero in the inverse rotation scan
from the missing lower-left root corner. Helper toward Lemma 5.12 B3 (`β₀`); -/
@[expose] noncomputable def kmswBeta0First (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) : {f : ℕ // EdgePresent w f} := by
  let c := kmswBeta0RootCorner w h
  let hc := kmswBeta0RootCorner_endpoint w h
  let hout := kmswM0_vertex_outgoing w hfin h 0
  exact ⟨kmswFirstOutgoingAfterCorner_symm w hfin c 0 hc hout,
    (kmswFirstOutgoingAfterCorner_symm_spec w hfin c 0 hc hout).1⟩

/-- The root first edge is present and leaves zero, and no earlier inverse
rotation iterate from the root corner is a present outgoing dart. Helper
toward Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0First_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    EdgePresent w (kmswBeta0First w hfin h).1 ∧
      edgeWest w (kmswBeta0First w hfin h).1 = 0 ∧
      ∀ n, n < kmswFirstOutgoingIndex_symm w hfin
          (kmswBeta0RootCorner w h) 0 (kmswBeta0RootCorner_endpoint w h)
          (kmswM0_vertex_outgoing w hfin h 0) →
        ¬ kmswPresentOutgoingDart w
          (((kmswInfRot w hfin).symm ^ n) (kmswBeta0RootCorner w h)) := by
  classical
  let c := kmswBeta0RootCorner w h
  let hc := kmswBeta0RootCorner_endpoint w h
  let hout := kmswM0_vertex_outgoing w hfin h 0
  let hfirst := kmswFirstOutgoingAtCorner_symm_exists w hfin c 0 hc hout
  have hspec := kmswFirstOutgoingAfterCorner_symm_spec w hfin c 0 hc hout
  refine ⟨(kmswBeta0First w hfin h).2, ?_, ?_⟩
  · change edgeWest w
      (kmswFirstOutgoingAfterCorner_symm w hfin c 0 hc hout) = 0
    exact hspec.2
  · intro n hn
    exact Nat.find_min hfirst hn

/-- Every distinct present outgoing edge at zero occurs strictly later in the
inverse rotation scan than `kmswBeta0First`. Helper toward Lemma 5.12 B3 -/
theorem kmswBeta0First_later (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (g : ℕ)
    (hg : EdgePresent w g) (hgv : edgeWest w g = 0)
    (hne : g ≠ (kmswBeta0First w hfin h).1) :
    ∃ m, kmswFirstOutgoingIndex_symm w hfin
        (kmswBeta0RootCorner w h) 0 (kmswBeta0RootCorner_endpoint w h)
        (kmswM0_vertex_outgoing w hfin h 0) < m ∧
      ((kmswInfRot w hfin).symm ^ m) (kmswBeta0RootCorner w h) = (g, false) := by
  classical
  let c := kmswBeta0RootCorner w h
  let hc := kmswBeta0RootCorner_endpoint w h
  let hout := kmswM0_vertex_outgoing w hfin h 0
  let hfirst := kmswFirstOutgoingAtCorner_symm_exists w hfin c 0 hc hout
  let n := kmswFirstOutgoingIndex_symm w hfin c 0 hc hout
  have hend : kmswDartEndpoint w (g, false) = kmswDartEndpoint w c := by
    change edgeWest w g = kmswDartEndpoint w c
    exact hgv.trans hc.symm
  obtain ⟨m, hm⟩ :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin (g, false) c).2 hend
  have hinv : ((kmswInfRot w hfin).symm ^ m) c = (g, false) := by
    have ht := congrArg ((kmswInfRot w hfin).symm ^ m) hm
    rw [perm_symm_pow_apply_pow] at ht
    exact ht.symm
  have hselected : ((kmswInfRot w hfin).symm ^ n) c =
      ((kmswBeta0First w hfin h).1, false) := by
    have htag : (((kmswInfRot w hfin).symm ^ n) c).2 = false := by
      have hs := Nat.find_spec hfirst
      change kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ n) c) at hs
      exact hs.1
    have hfst : (((kmswInfRot w hfin).symm ^ n) c).1 =
        (kmswBeta0First w hfin h).1 := by
      change (((kmswInfRot w hfin).symm ^ n) c).1 =
        kmswFirstOutgoingAfterCorner_symm w hfin c 0 hc hout
      rfl
    exact Prod.ext hfst htag
  have hlt : n < m := by
    by_contra hnot
    have hmle : m ≤ n := by omega
    by_cases hmn : m = n
    · have heq : (g, false) = ((kmswBeta0First w hfin h).1, false) := by
        calc
          (g, false) = ((kmswInfRot w hfin).symm ^ m) c := hinv.symm
          _ = ((kmswInfRot w hfin).symm ^ n) c := by rw [hmn]
          _ = ((kmswBeta0First w hfin h).1, false) := hselected
      exact hne (congrArg Prod.fst heq)
    · have hmn' : m < n := by omega
      have hbad := Nat.find_min hfirst hmn'
      have hp : kmswPresentOutgoingDart w (((kmswInfRot w hfin).symm ^ m) c) := by
        rw [hinv]
        exact ⟨rfl, hg⟩
      exact (hbad hp).elim
  exact ⟨m, hlt, hinv⟩

/-- The edge stream that starts with the first present outgoing edge at zero
and then takes the inverse-rotation leftmost continuation at every head.
Helper toward Lemma 5.12 B3 (`β₀`); not the paper result -/
@[expose] noncomputable def kmswBeta0Stream (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) : ℕ → {f : ℕ // EdgePresent w f} :=
  Nat.rec (kmswBeta0First w hfin h)
    (fun _ e => kmswBeta0Next w hfin h e)

/-- Every stream edge remains present. Helper toward Lemma 5.12 B3 (`β₀`); -/
theorem kmswBeta0Stream_present (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    EdgePresent w (kmswBeta0Stream w hfin h n).1 :=
  (kmswBeta0Stream w hfin h n).property

/-- The stream's first edge leaves the root vertex zero. Helper toward Lemma
5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0Stream_start (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    edgeWest w (kmswBeta0Stream w hfin h 0).1 = 0 := by
  exact (kmswBeta0First_spec w hfin h).2.1

/-- Consecutive stream edges meet head-to-tail. Helper toward Lemma 5.12 B3 -/
theorem kmswBeta0Stream_chain (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    edgeWest w (kmswBeta0Stream w hfin h (n + 1)).1 =
      edgeEast w (kmswBeta0Stream w hfin h n).1 := by
  exact (kmswBeta0Next_spec w hfin h (kmswBeta0Stream w hfin h n)).2.1

/-- Each continuation is the first present outgoing dart in the inverse
rotation scan from the preceding edge's head, and every distinct alternative
occurs strictly later. Helper toward Lemma 5.12 B3 (`β₀`); not the paper -/
theorem kmswBeta0Stream_leftmost (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    EdgePresent w (kmswBeta0Stream w hfin h (n + 1)).1 ∧
      edgeWest w (kmswBeta0Stream w hfin h (n + 1)).1 =
        edgeEast w (kmswBeta0Stream w hfin h n).1 ∧
      (∀ m, m < kmswFirstOutgoingIndex_symm w hfin
          (kmswBeta0IncomingCorner (kmswBeta0Stream w hfin h n))
          (edgeEast w (kmswBeta0Stream w hfin h n).1)
          (kmswBeta0IncomingCorner_spec (kmswBeta0Stream w hfin h n))
          (kmswM0_vertex_outgoing w hfin h
            (edgeEast w (kmswBeta0Stream w hfin h n).1)) →
        ¬ kmswPresentOutgoingDart w
          (((kmswInfRot w hfin).symm ^ m)
            (kmswBeta0IncomingCorner (kmswBeta0Stream w hfin h n)))) ∧
      (∀ g, EdgePresent w g →
        edgeWest w g = edgeEast w (kmswBeta0Stream w hfin h n).1 →
        g ≠ (kmswBeta0Stream w hfin h (n + 1)).1 →
        ∃ m, kmswFirstOutgoingIndex_symm w hfin
            (kmswBeta0IncomingCorner (kmswBeta0Stream w hfin h n))
            (edgeEast w (kmswBeta0Stream w hfin h n).1)
            (kmswBeta0IncomingCorner_spec (kmswBeta0Stream w hfin h n))
            (kmswM0_vertex_outgoing w hfin h
              (edgeEast w (kmswBeta0Stream w hfin h n).1)) < m ∧
          ((kmswInfRot w hfin).symm ^ m)
            (kmswBeta0IncomingCorner (kmswBeta0Stream w hfin h n)) = (g, false)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change EdgePresent w (kmswBeta0Next w hfin h
      (kmswBeta0Stream w hfin h n)).1
    exact (kmswBeta0Next_spec w hfin h
      (kmswBeta0Stream w hfin h n)).1
  · change edgeWest w (kmswBeta0Next w hfin h
      (kmswBeta0Stream w hfin h n)).1 = _
    exact (kmswBeta0Next_spec w hfin h
      (kmswBeta0Stream w hfin h n)).2.1
  · exact (kmswBeta0Next_spec w hfin h
      (kmswBeta0Stream w hfin h n)).2.2
  · intro g hg hgv hne
    exact kmswBeta0Next_later w hfin h (kmswBeta0Stream w hfin h n)
      g hg hgv hne

/-- The vertex sequence starts at zero and then records successive stream
heads. Helper toward Lemma 5.12 B3 (`β₀`); not the paper result -/
@[expose] noncomputable def kmswBeta0Vertices (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) : ℕ → ℕ :=
  Nat.rec 0 (fun n _ => edgeEast w (kmswBeta0Stream w hfin h n).1)

open Quiver

private theorem kmswBeta0VertexIdEq (w : ℕ → Fin 3) {u v : ℕ} (h : u = v) :
    (⟨u⟩ : PresentVertex w) = ⟨v⟩ :=
  congrArg (fun z => (⟨z⟩ : PresentVertex w)) h

private noncomputable def kmswBeta0PresentArrow (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (i : ℕ) :
    (⟨edgeWest w (kmswBeta0Stream w hfin h i).1⟩ : PresentVertex w) ⟶
      ⟨edgeEast w (kmswBeta0Stream w hfin h i).1⟩ :=
  ⟨(kmswBeta0Stream w hfin h i).1,
    (kmswBeta0Stream w hfin h i).property, rfl, rfl⟩

private theorem kmswBeta0PathCast_length {V : Type} [Quiver V] {a b c : V}
    (h : b = c) (p : Path a b) : (h ▸ p).length = p.length := by
  cases h
  rfl

private def kmswBeta0PathCast {V : Type} [Quiver V] {a b c d : V}
    (hs : a = c) (ht : b = d) (p : Path a b) : Path c d :=
  Eq.ndrec (motive := fun c' => Path c' d)
    (Eq.ndrec (motive := fun d' => Path a d') p ht) hs

private theorem kmswBeta0PathCast_length_both {V : Type} [Quiver V]
    {a b c d : V} (hs : a = c) (ht : b = d) (p : Path a b) :
    (kmswBeta0PathCast hs ht p).length = p.length := by
  cases hs
  cases ht
  rfl

private noncomputable def kmswBeta0EdgePath (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (i : ℕ) : (k : ℕ) →
      Path (⟨edgeWest w (kmswBeta0Stream w hfin h i).1⟩ : PresentVertex w)
        ⟨edgeEast w (kmswBeta0Stream w hfin h (i + k)).1⟩
  | 0 => (kmswBeta0PresentArrow w hfin h i).toPath
  | k + 1 => by
      simpa only [Nat.add_succ] using
        (kmswBeta0VertexIdEq w
          (kmswBeta0Stream_chain w hfin h (i + k)).symm ▸
          kmswBeta0EdgePath w hfin h i k).cons
          (kmswBeta0PresentArrow w hfin h (i + k + 1))

private theorem kmswBeta0EdgePath_length (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (i k : ℕ) :
    (kmswBeta0EdgePath w hfin h i k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((kmswBeta0VertexIdEq w
          (kmswBeta0Stream_chain w hfin h (i + k)).symm ▸
          kmswBeta0EdgePath w hfin h i k).cons
          (kmswBeta0PresentArrow w hfin h (i + k + 1))).length = (k + 1) + 1
      rw [Path.length_cons, kmswBeta0PathCast_length, ih]

private theorem kmswBeta0Vertices_eq_tail (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) (n : ℕ) :
    kmswBeta0Vertices w hfin h n = edgeWest w (kmswBeta0Stream w hfin h n).1 := by
  cases n with
  | zero => exact (kmswBeta0Stream_start w hfin h).symm
  | succ n => exact (kmswBeta0Stream_chain w hfin h n).symm

/-- The vertex sequence has no repeated vertex, by acyclicity of the limiting
Helper toward Lemma 5.12 B3 (`β₀`); not the paper result -/
theorem kmswBeta0Vertices_injective (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w) :
    Function.Injective (kmswBeta0Vertices w hfin h) := by
  intro i j hVertices
  have hnoRepeat {a b : ℕ} (hab : a < b)
      (heq : kmswBeta0Vertices w hfin h a = kmswBeta0Vertices w hfin h b) : False := by
    let k := b - (a + 1)
    have hidx : a + k + 1 = b := by dsimp [k]; omega
    let p := kmswBeta0EdgePath w hfin h a k
    have hlast : edgeEast w (kmswBeta0Stream w hfin h (a + k)).1 =
        edgeWest w (kmswBeta0Stream w hfin h b).1 := by
      rw [← hidx]
      exact (kmswBeta0Stream_chain w hfin h (a + k)).symm
    have hstartV :
        (⟨edgeWest w (kmswBeta0Stream w hfin h a).1⟩ : PresentVertex w) =
          ⟨kmswBeta0Vertices w hfin h a⟩ :=
      kmswBeta0VertexIdEq w (kmswBeta0Vertices_eq_tail w hfin h a).symm
    have hendV :
        (⟨edgeEast w (kmswBeta0Stream w hfin h (a + k)).1⟩ : PresentVertex w) =
          ⟨kmswBeta0Vertices w hfin h a⟩ :=
      kmswBeta0VertexIdEq w
        (hlast.trans ((kmswBeta0Vertices_eq_tail w hfin h b).symm.trans heq.symm))
    let cycle := kmswBeta0PathCast hstartV hendV p
    have hlenP : p.length = k + 1 := by
      simpa [p] using kmswBeta0EdgePath_length w hfin h a k
    have hcycleLen : cycle.length = p.length := by
      simpa [cycle, p] using kmswBeta0PathCast_length_both hstartV hendV p
    have hpos : 0 < cycle.length := by rw [hcycleLen, hlenP]; omega
    have hzero := presentVertex_acyclic w _ cycle
    omega
  rcases lt_trichotomy i j with hlt | hEq | hgt
  · exact False.elim (hnoRepeat hlt hVertices)
  · exact hEq
  · exact False.elim (hnoRepeat hgt hVertices.symm)

end DirectedDistances.KMSW
