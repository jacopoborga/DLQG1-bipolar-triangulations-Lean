/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperStoppedGeometry

public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.RandomWalk
open DirectedDistances.PlanarMap

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
Map a natural-indexed list lookup through a function. -/
private theorem stoppedIso_list_getD_map_nat {α β : Type*} (f : α → β)
    (xs : List α) (n : ℕ) (d : α) :
    (xs.map f).getD n (f d) = f (xs.getD n d) := by
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons x xs ih => cases n with
    | zero => rfl
    | succ n => exact ih n

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
Replace a valid natural-indexed lookup by its finite-indexed lookup. -/
private theorem stoppedIso_list_getD_eq_get_nat {α : Type*} (xs : List α)
    (i : Fin xs.length) (d : α) : xs.getD i.val d = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    cases i with
    | mk n hn =>
      cases n with
      | zero => rfl
      | succ n =>
        have hlen : n < xs.length := by simpa using hn
        let j : Fin xs.length := ⟨n, hlen⟩
        simpa [List.getD, j] using ih j

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
The boundary carrier built from the KMSW stage at the stopped prefix is
boundary-isomorphic to the quotient representative of its map class. -/
theorem stoppedStage_out_baseIso {r t ell : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) :
    Nonempty (BipolarBoundaryBaseIso (kmswWalkClassBase ht c)
      (kmswToMapIsoClass ht c).out.B) := by
  let B := kmswWalkClassBase ht c
  let D := StageDart (kmswStage (codeExtend c) (t - 1)).nextEdge
  let e := Fintype.equivFin D
  have htransport : BipolarBoundaryBaseIso B (kmswWalkClassRep ht c).B := by
    change BipolarBoundaryBaseIso B (B.transport e)
    exact B.transportIso e
  exact ⟨htransport.trans (kmswWalkClassRep_out_baseIso ht c).some⟩

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
On the stopped-value event, the stage at the pre-hit time has a
boundary-preserving isomorphism to the marked map's quotient representative.
The target index is the mark of `stoppedMarked`, i.e. the future-minimum index clamped
to the last allowed left-boundary index; this file does not prove that the clamp is
inactive almost surely. The marked arc is indexed by the suffix beginning at this
clamped mark. -/
theorem quadrantHatWalk_stoppedMarked_stageBaseIso (ω : ℕ → Fin 3)
    (r : ℕ) (hr : 1 ≤ r) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) :
    let q := stoppedMarked r hr (quadrantHatWalk ω)
    ∃ (ht : 1 ≤ hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr)
      (ell : ℕ)
      (c : KMSWWalkClass ell r
        (hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr)),
      q.1 = ⟨ell, ⟨hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr,
        kmswToMapIsoClass ht c⟩⟩ ∧
      Nonempty (BipolarBoundaryBaseIso (kmswWalkClassBase ht c)
        (kmswToMapIsoClass ht c).out.B) := by
  dsimp only
  obtain ⟨ht, ell, c, hvalue⟩ :=
    quadrantHatWalk_stoppedMarked_value ω r hr h hb
  refine ⟨ht, ell, c, hvalue, ?_⟩
  exact stoppedStage_out_baseIso ht c

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
The stopped KMSW stage has empty lower-left boundary, so its ordered left path
is the upper-left boundary. -/
theorem stoppedStage_LL_nil {r t ell : ℕ} (ht : 1 ≤ t)
    (c : KMSWWalkClass ell r t) :
    (kmswStage (codeExtend c) (t - 1)).LL = [] := by
  have h := kmswWalkClassMap_mem_sourceClass ht c
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hLL, _⟩
  exact hLL

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: stopped stage = marked Boltzmann
The boundary isomorphism carries each source-to-sink left-path vertex at
index `j` to the same indexed left vertex of the marked Boltzmann map. When
`j` is at least the mark, this is the corresponding vertex of the marked
suffix `J_r`. -/
theorem stoppedStage_leftVertex_index (r : ℕ)
    (q : RightVertexMarkedBoltzmannSpace r) (ht : 1 ≤ q.1.2.1)
    (c : KMSWWalkClass q.1.1 r q.1.2.1)
    (I : BipolarBoundaryBaseIso (kmswWalkClassBase ht c)
      q.1.2.2.out.B)
    (j : Fin (q.1.1 + 1)) (_hmark : q.2 ≤ j) :
    I.vertexEquiv ((kmswWalkClassBase ht c).leftPath.vertices.get
      ⟨j.val, by
        rw [(kmswWalkClassBase ht c).leftPath.vertices_length]
        exact j.isLt⟩) = boltzmannSdpUpper_leftVertex q j := by
  let B := kmswWalkClassBase ht c
  let B' := q.1.2.2.out.B
  have hp : I.mapPath B.leftPath = B'.leftPath :=
    SimpleDirectedDartPath.eq_of_darts_eq I.leftDarts
  have hv : B.leftPath.vertices.map I.vertexEquiv = B'.leftPath.vertices :=
    congrArg SimpleDirectedDartPath.vertices hp
  have hget := congrArg
    (fun xs : List (MapVertex B'.map) =>
      xs.getD j.val (I.vertexEquiv B.source)) hv
  rw [stoppedIso_list_getD_map_nat] at hget
  have hleft := stoppedIso_list_getD_eq_get_nat B.leftPath.vertices
    ⟨j.val, by rw [B.leftPath.vertices_length]; exact j.isLt⟩ B.source
  have hright := stoppedIso_list_getD_eq_get_nat B'.leftPath.vertices
    ⟨j.val, by rw [B'.leftPath.vertices_length]; exact j.isLt⟩
    (I.vertexEquiv B.source)
  rw [hleft, hright] at hget
  simpa [boltzmannSdpUpper_leftVertex, B, B'] using hget

end DirectedDistances.PaperProofs.Section7
