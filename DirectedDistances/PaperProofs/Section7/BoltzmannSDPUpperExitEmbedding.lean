/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperStoppedIso
public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperHatGeometry
import DirectedDistances.KMSW.HatInputAssembly
import DirectedDistances.KMSW.StageDirectedMapPathLengths
import DirectedDistances.PaperProofs.Section7.HitCoupling

public section

namespace DirectedDistances.PaperProofs.Section7

open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open Quiver

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
Extend the hatted vertex simulation injectively to the full natural-number vertex carriers. -/
@[expose] noncomputable def boltzmannSdpUpper_hatRawVertex (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m : ℕ) (v : ℕ) : ℕ :=
  let sh := kmswStage (hatCodes w h) m
  let gl := kmswStage w (quadrantRStageTime w h m)
  if v < sh.nextVertex then hatAllVertexMap w h m v else gl.nextVertex + v

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The hat stage maps by its incidence simulation into the raw stage at `S_m`, then into any
later raw stage. Edge identities are sent by the established hat-to-raw edge map. -/
@[expose] noncomputable def boltzmannSdpUpper_hatRawStagePrefunctor (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (m n : ℕ)
    (hn : quadrantRStageTime w h m ≤ n) :
    Prefunctor (StagePresentVertex (hatCodes w h) m) (StagePresentVertex w n) where
  obj v := ⟨boltzmannSdpUpper_hatRawVertex w h m v.id⟩
  map {a b} e := by
    let s := kmswStage (hatCodes w h) m
    let t := kmswStage w (quadrantRStageTime w h m)
    let hs := (hatAll_sim w h m).incidenceSim
    have he : e.val < s.nextEdge := e.property.1
    have hbound := hs.edge_bound e.val he
    have hpresent := hs.present e.val he e.property.2.1
    have hmono := present_mono w hbound hpresent n hn
    have hstable := kmswStage_endpoints_stable w hn hbound
    have hend := kmswStage_endpoints_lt_nextVertex (hatCodes w h) m e.val he
    have ha : a.id < s.nextVertex := by
      calc
        a.id = s.west e.val := e.property.2.2.1.symm
        _ < s.nextVertex := hend.1
    have hb : b.id < s.nextVertex := by
      calc
        b.id = s.east e.val := e.property.2.2.2.symm
        _ < s.nextVertex := hend.2
    refine ⟨hatAllEdgeMap w h m e.val, hmono.1, hmono.2, ?_, ?_⟩
    · calc
        (kmswStage w n).west (hatAllEdgeMap w h m e.val) =
            t.west (hatAllEdgeMap w h m e.val) := hstable.1
        _ = hatAllVertexMap w h m (s.west e.val) := hs.incidence e.val he |>.1
        _ = hatAllVertexMap w h m a.id := by rw [e.property.2.2.1]
        _ = boltzmannSdpUpper_hatRawVertex w h m a.id := by
          rw [boltzmannSdpUpper_hatRawVertex, ite_eq_left ha]
    · calc
        (kmswStage w n).east (hatAllEdgeMap w h m e.val) =
            t.east (hatAllEdgeMap w h m e.val) := hstable.2
        _ = hatAllVertexMap w h m (s.east e.val) := hs.incidence e.val he |>.2
        _ = hatAllVertexMap w h m b.id := by rw [e.property.2.2.2]
        _ = boltzmannSdpUpper_hatRawVertex w h m b.id := by
          rw [boltzmannSdpUpper_hatRawVertex, ite_eq_left hb]

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The extended object map is injective on the entire stage vertex carrier. -/
theorem boltzmannSdpUpper_hatRawStagePrefunctor_obj_injective
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m n : ℕ)
    (hn : quadrantRStageTime w h m ≤ n) :
    Function.Injective
      (boltzmannSdpUpper_hatRawStagePrefunctor w h m n hn).obj := by
  let s := kmswStage (hatCodes w h) m
  let t := kmswStage w (quadrantRStageTime w h m)
  let hs := (hatAll_sim w h m).incidenceSim
  intro a b hab
  have hv := congrArg StagePresentVertex.id hab
  by_cases ha : a.id < s.nextVertex
  · by_cases hb : b.id < s.nextVertex
    · have hids : hatAllVertexMap w h m a.id = hatAllVertexMap w h m b.id := by
        simpa [boltzmannSdpUpper_hatRawStagePrefunctor,
          boltzmannSdpUpper_hatRawVertex, s, t, ha, hb] using hv
      have hEq := hs.vertex_injective a.id b.id ha hb hids
      cases a
      cases b
      simp_all
    · have hsmall := hs.vertex_bound a.id ha
      simp [boltzmannSdpUpper_hatRawStagePrefunctor,
        boltzmannSdpUpper_hatRawVertex, s, ha, hb] at hv
      omega
  · by_cases hb : b.id < s.nextVertex
    · have hsmall := hs.vertex_bound b.id hb
      simp [boltzmannSdpUpper_hatRawStagePrefunctor,
        boltzmannSdpUpper_hatRawVertex, s, ha, hb] at hv
      omega
    · have hids : a.id = b.id := by
        simp [boltzmannSdpUpper_hatRawStagePrefunctor,
          boltzmannSdpUpper_hatRawVertex, s, ha, hb] at hv
        omega
      cases a
      cases b
      simp_all

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The root vertex is fixed by the stage embedding. -/
theorem boltzmannSdpUpper_hatRawStagePrefunctor_root
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m n : ℕ)
    (hn : quadrantRStageTime w h m ≤ n) :
    (boltzmannSdpUpper_hatRawStagePrefunctor w h m n hn).obj
      (⟨0⟩ : StagePresentVertex (hatCodes w h) m) = ⟨0⟩ := by
  have hzero : 0 < (kmswStage (hatCodes w h) m).nextVertex := by
    have hbase : 0 < (kmswStage (hatCodes w h) 0).nextVertex := by
      change 0 < 2
      omega
    exact hbase.trans_le (CutConverse.nextVertex_mono (hatCodes w h) (Nat.zero_le m))
  simp only [boltzmannSdpUpper_hatRawStagePrefunctor,
    boltzmannSdpUpper_hatRawVertex, ite_eq_left hzero]
  exact congrArg (StagePresentVertex.mk (w := w) (n := n))
    (hatAllVertexMap_root w h m)



theorem boltzmannSdpUpper_hatRawStagePrefunctor_edge_id
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m n : ℕ)
    (hn : quadrantRStageTime w h m ≤ n) {a b : StagePresentVertex (hatCodes w h) m}
    (e : a ⟶ b) :
    ((boltzmannSdpUpper_hatRawStagePrefunctor w h m n hn).map e).val =
      hatAllEdgeMap w h m e.val := rfl

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The active hat edge at index `m` maps to the active raw edge at time `S_m`. -/
theorem boltzmannSdpUpper_hatRawStagePrefunctor_active_edge
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m n : ℕ)
    (hn : quadrantRStageTime w h m ≤ n) :
    ∃ (a b : StagePresentVertex (hatCodes w h) m) (e : a ⟶ b),
      e.val = (kmswStage (hatCodes w h) m).active ∧
      ((boltzmannSdpUpper_hatRawStagePrefunctor w h m n hn).map e).val =
        (kmswStage w (quadrantRStageTime w h m)).active := by
  let s := kmswStage (hatCodes w h) m
  let a : StagePresentVertex (hatCodes w h) m := ⟨s.west s.active⟩
  let b : StagePresentVertex (hatCodes w h) m := ⟨s.east s.active⟩
  have he := act_lt_nextEdge (hatCodes w h) (Nat.le_refl m)
  have hp := kmswStage_active_present (hatCodes w h) m
  let e : a ⟶ b := ⟨s.active, he, hp, rfl, rfl⟩
  refine ⟨a, b, e, rfl, ?_⟩
  rw [boltzmannSdpUpper_hatRawStagePrefunctor_edge_id]
  exact (hatAll_sim w h m).incidenceSim.active

/-- Helper toward Lemma 7.13 (lem-boltzmann-sdp-upper, Step 1: embedding of the stopped map
The raw hit by time `n` puts the pre-hit hatted stage inside the raw stage at time `n`. -/
theorem boltzmannSdpUpper_stoppedStage_time_le_of_raw_hit (ω : ℕ → Fin 3)
    (r : ℕ) (hr : 1 ≤ r) (h : HasFlowLineHits (fun i => ω (i + 1)))
    (hb : BoundaryHitWitnesses (fun i => ω (i + 1))) (n : ℕ)
    (hhit : ∃ k ≤ n, R (fun i => ω (i + 1)) k = -(r : ℤ)) :
    quadrantRStageTime (fun i => ω (i + 1)) h
        (hattedRightVertexHitTime (fun i => ω (i + 1)) h hb r hr - 1) ≤ n := by
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let t := hattedRightVertexHitTime w h hb r hr
  rcases hhit with ⟨k, hkn, hk⟩
  have hrZ : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hfind : boundaryHitTime w hb (r : ℤ) =
      Nat.find (hb.rightHit (r : ℤ) hrZ) := by
    unfold boundaryHitTime
    simp only [dite_eq_right (by omega : (r : ℤ) ≠ 0),
      dite_eq_left (by omega : (0 : ℤ) < r)]
  have hfirst : boundaryHitTime w hb (r : ℤ) ≤ k := by
    rw [hfind]
    exact Nat.find_min' (hb.rightHit (r : ℤ) hrZ) hk
  have hsel := sourceHitTime_eq_selector_hattedRightHit w h hb r hr
  have ht : t = hattedRightHitTime w h r hr :=
    hattedRightVertexHitTime_eq_hattedRightHitTime w h hb r hr
  have hstage : quadrantRStageTime w h t = boundaryHitTime w hb (r : ℤ) := by
    rw [ht]
    exact
      (DirectedDistances.PaperProofs.Section5.quadrantRStageTime_eq_sourceQuadrantS
        w h (hattedRightHitTime w h r hr)).trans hsel.symm
  calc
    quadrantRStageTime w h (t - 1) ≤ quadrantRStageTime w h t :=
      quadrantRStageTime_mono w h (by omega)
    _ = boundaryHitTime w hb (r : ℤ) := hstage
    _ ≤ k := hfirst
    _ ≤ n := hkn

end DirectedDistances.PaperProofs.Section7
