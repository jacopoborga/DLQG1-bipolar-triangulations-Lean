/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatImageLimit
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # Coherent limits of stage-indexed KMSW maps

These generic limit-map helpers package coherent stage-indexed incidence maps
They are infrastructure for that argument, not a proof of `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Evaluate a stage-indexed map at the first stage where the identifier is
allocated, using zero for identifiers never allocated. The KMSW edge and
vertex limit maps specialize this construction for `lem-quad-kmsw` -/
@[expose] noncomputable def leastAllocatedStageMap
    (bound : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ m, i < bound m then F (Nat.find h) i else 0

private theorem coherentMap_eq_of_le
    (bound : ℕ → ℕ) (F : ℕ → ℕ → ℕ)
    (hmono : Monotone bound)
    (hcoh : ∀ m i, i < bound m → F (m + 1) i = F m i)
    {k m i : ℕ} (hkm : k ≤ m) (hi : i < bound k) :
    F m i = F k i := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
      exact (hcoh m i (hi.trans_le (hmono hkm))).trans ih

/-- A coherent stage map agrees with its first-allocation limit on every
allocated identifier (`lem-quad-kmsw`, -/
theorem leastAllocatedStageMap_eq_of_allocated
    (bound : ℕ → ℕ) (F : ℕ → ℕ → ℕ)
    (hmono : Monotone bound)
    (hcoh : ∀ m i, i < bound m → F (m + 1) i = F m i)
    (m i : ℕ) (hi : i < bound m) :
    leastAllocatedStageMap bound F i = F m i := by
  classical
  unfold leastAllocatedStageMap
  let halloc : ∃ n, i < bound n := ⟨m, hi⟩
  rw [dif_pos halloc]
  have hfirst : Nat.find halloc ≤ m := Nat.find_min' halloc hi
  have hbound : i < bound (Nat.find halloc) := Nat.find_spec halloc
  exact (coherentMap_eq_of_le bound F hmono hcoh hfirst hbound).symm

/-- The edge map induced by a coherent family of KMSW stage maps, using the
first stage where each edge ID is allocated (`lem-quad-kmsw`, -/
@[expose] noncomputable def limitEdgeMap
    (E : ℕ → ℕ → ℕ) (u : ℕ → Fin 3) : ℕ → ℕ :=
  leastAllocatedStageMap (fun m => (kmswStage u m).nextEdge) E

/-- The vertex map induced by a coherent family of KMSW stage maps, using the
first stage where each vertex ID is allocated (`lem-quad-kmsw`, -/
@[expose] noncomputable def limitVertexMap
    (V : ℕ → ℕ → ℕ) (u : ℕ → Fin 3) : ℕ → ℕ :=
  leastAllocatedStageMap (fun m => (kmswStage u m).nextVertex) V

/-- On an allocated edge, the first-allocation edge map equals the map at -/
theorem limitEdgeMap_eq_of_allocated
    {u : ℕ → Fin 3} (E : ℕ → ℕ → ℕ)
    (hcoh : ∀ m e, e < (kmswStage u m).nextEdge → E (m + 1) e = E m e)
    (m e : ℕ) (he : e < (kmswStage u m).nextEdge) :
    limitEdgeMap E u e = E m e := by
  exact leastAllocatedStageMap_eq_of_allocated
    (bound := fun n => (kmswStage u n).nextEdge) E
    (fun a b hab => kmswStage_nextEdge_mono u hab) hcoh m e he

/-- On an allocated vertex, the first-allocation vertex map equals the map at -/
theorem limitVertexMap_eq_of_allocated
    {u : ℕ → Fin 3} (V : ℕ → ℕ → ℕ)
    (hcoh : ∀ m v, v < (kmswStage u m).nextVertex → V (m + 1) v = V m v)
    (m v : ℕ) (hv : v < (kmswStage u m).nextVertex) :
    limitVertexMap V u v = V m v := by
  exact leastAllocatedStageMap_eq_of_allocated
    (bound := fun n => (kmswStage u n).nextVertex) V
    (fun a b hab => CutConverse.nextVertex_mono u hab) hcoh m v hv

/-- If every stage map fixes vertex zero, then the limit map fixes it too;
stage zero allocates that vertex (`lem-quad-kmsw`, -/
theorem limitVertexMap_root
    {u : ℕ → Fin 3} (V : ℕ → ℕ → ℕ)
    (hroot : ∀ m, V m 0 = 0) :
    limitVertexMap V u 0 = 0 := by
  classical
  change leastAllocatedStageMap (fun m => (kmswStage u m).nextVertex) V 0 = 0
  unfold leastAllocatedStageMap
  have hzero : 0 < (kmswStage u 0).nextVertex := by
    simp [kmswStage, kmswInit]
  let halloc : ∃ m, 0 < (kmswStage u m).nextVertex := ⟨0, hzero⟩
  rw [dif_pos halloc]
  exact hroot (Nat.find halloc)

/-- Coherent stagewise `HatIncidenceSim` data induces incidence simulation
for the limit maps (`lem-quad-kmsw`, -/
theorem hatIncidenceSim_limit_of_coherent
    {u w : ℕ → Fin 3} (T : ℕ → ℕ) (E V : ℕ → ℕ → ℕ)
    (hE : ∀ m e, e < (kmswStage u m).nextEdge → E (m + 1) e = E m e)
    (hV : ∀ m v, v < (kmswStage u m).nextVertex → V (m + 1) v = V m v)
    (hstage : ∀ m,
      HatIncidenceSim (kmswStage u m) (kmswStage w (T m)) (E m) (V m))
    (m : ℕ) :
    HatIncidenceSim (kmswStage u m) (kmswStage w (T m))
      (limitEdgeMap E u) (limitVertexMap V u) := by
  let hs := hstage m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [limitEdgeMap_eq_of_allocated E hE m e he]
    exact hs.edge_bound e he
  · intro e f he hf hef
    have hef' := hef
    rw [limitEdgeMap_eq_of_allocated E hE m e he,
      limitEdgeMap_eq_of_allocated E hE m f hf] at hef'
    exact hs.edge_injective e f he hf hef'
  · intro v hv
    rw [limitVertexMap_eq_of_allocated V hV m v hv]
    exact hs.vertex_bound v hv
  · intro v z hv hz hvz
    have hvz' := hvz
    rw [limitVertexMap_eq_of_allocated V hV m v hv,
      limitVertexMap_eq_of_allocated V hV m z hz] at hvz'
    exact hs.vertex_injective v z hv hz hvz'
  · have hactive := (kmswStage_boundary_ids_lt_nextEdge u m).1
    rw [limitEdgeMap_eq_of_allocated E hE m (kmswStage u m).active hactive]
    exact hs.active
  · intro e he
    have hend := kmswStage_endpoints_lt_nextVertex u m e he
    rw [limitEdgeMap_eq_of_allocated E hE m e he,
      limitVertexMap_eq_of_allocated V hV m _ hend.1,
      limitVertexMap_eq_of_allocated V hV m _ hend.2]
    exact hs.incidence e he
  · intro e he hp
    rw [limitEdgeMap_eq_of_allocated E hE m e he]
    exact hs.present e he hp
  · have hUR : ∀ e ∈ (kmswStage u m).UR, e < (kmswStage u m).nextEdge := by
      intro e he
      have hmem : e ∈ (kmswStage u m).UL ++ (kmswStage u m).UR ++
          (kmswStage u m).LL ++ (kmswStage u m).LR := by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr he))
      exact (kmswStage_boundary_ids_lt_nextEdge u m).2 e hmem
    have hmaps : List.map (limitEdgeMap E u) (kmswStage u m).UR =
        List.map (E m) (kmswStage u m).UR := by
      apply List.map_congr_left
      intro e he
      exact limitEdgeMap_eq_of_allocated E hE m e (hUR e he)
    rw [hmaps]
    exact hs.ur_prefix

/-- The exact present-edge image identity transfers from every stage family
to the limit edge map (`lem-quad-kmsw`, -/
theorem limitEdgeMap_image_eq
    {u w : ℕ → Fin 3} (T : ℕ → ℕ) (E : ℕ → ℕ → ℕ)
    (hcoh : ∀ m e, e < (kmswStage u m).nextEdge → E (m + 1) e = E m e)
    (m : ℕ)
    (himage : E m '' {e | e < (kmswStage u m).nextEdge ∧
      (kmswStage u m).present e = true} = stageReachablePresentEdges w (T m)) :
    limitEdgeMap E u '' {e | e < (kmswStage u m).nextEdge ∧
      (kmswStage u m).present e = true} = stageReachablePresentEdges w (T m) := by
  rw [← himage]
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨e, he, hEy⟩
    refine ⟨e, he, ?_⟩
    have heq := limitEdgeMap_eq_of_allocated E hcoh m e he.1
    rw [heq] at hEy
    exact hEy
  · rintro ⟨e, he, hEy⟩
    refine ⟨e, he, ?_⟩
    rw [limitEdgeMap_eq_of_allocated E hcoh m e he.1]
    exact hEy

/-- Package coherent stagewise incidence, edge-image and root data into the
generic input for `hatImageLimit`. This is limit-map infrastructure for -/
theorem hatImageLimitInput_of_coherent_stage_maps
    {u w : ℕ → Fin 3} (T : ℕ → ℕ) (E V : ℕ → ℕ → ℕ)
    (hTmono : Monotone T)
    (hTunbounded : ∀ n, ∃ m, n ≤ T m)
    (hE : ∀ m e, e < (kmswStage u m).nextEdge → E (m + 1) e = E m e)
    (hV : ∀ m v, v < (kmswStage u m).nextVertex → V (m + 1) v = V m v)
    (hstage : ∀ m,
      HatIncidenceSim (kmswStage u m) (kmswStage w (T m)) (E m) (V m))
    (himage : ∀ m, E m '' {e | e < (kmswStage u m).nextEdge ∧
      (kmswStage u m).present e = true} = stageReachablePresentEdges w (T m))
    (hroot : ∀ m, V m 0 = 0)
    (hincident : ∀ a : PresentVertex u,
      (∃ m, a.id < (kmswStage u m).nextVertex) → a.id ≠ 0 →
        ∃ e, EdgePresent u e ∧
          (edgeWest u e = a.id ∨ edgeEast u e = a.id) ∧
          Reachable (⟨0⟩ : PresentVertex u) ⟨edgeWest u e⟩ ∧
          Reachable (⟨0⟩ : PresentVertex u) ⟨edgeEast u e⟩) :
    HatImageLimitInput u w T (limitEdgeMap E u) (limitVertexMap V u) := by
  refine ⟨hTmono, hTunbounded, limitVertexMap_root V hroot, ?_, ?_, hincident⟩
  · intro m
    exact hatIncidenceSim_limit_of_coherent T E V hE hV hstage m
  · intro m
    exact limitEdgeMap_image_eq T E hE m (himage m)

end DirectedDistances.KMSW
