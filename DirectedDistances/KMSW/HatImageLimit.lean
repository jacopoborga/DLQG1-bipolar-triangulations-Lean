/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.QuadKMSWHatFlipped
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! # A generic limit argument for hatted KMSW stage simulations

This module turns a coherent, stage-independent vertex and edge map together
with stagewise incidence and an exact reachable-edge image into a limit map.
It supplies the path-lifting and range mechanism needed downstream for
limit lemma: it is not a proof of `lem-quad-kmsw`. -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Input data for the generic limit argument. The fixed maps are compared at
every local stage `m` and target stage `T m`. The final field is the local
structural condition needed for allocated non-root vertices: each is incident
to a local present edge whose endpoints are reachable from zero. This source
condition is not a conclusion about the target map. -/
structure HatImageLimitInput (u w : ℕ → Fin 3) (T eφ vφ : ℕ → ℕ) : Prop where
  time_mono : Monotone T
  time_unbounded : ∀ n, ∃ m, n ≤ T m
  root : vφ 0 = 0
  stage_sim : ∀ m,
    HatIncidenceSim (kmswStage u m) (kmswStage w (T m)) eφ vφ
  edge_image : ∀ m,
    eφ '' {e | e < (kmswStage u m).nextEdge ∧
      (kmswStage u m).present e = true} = stageReachablePresentEdges w (T m)
  allocated_nonroot_incident : ∀ a : PresentVertex u,
    (∃ m, a.id < (kmswStage u m).nextVertex) → a.id ≠ 0 →
      ∃ e, EdgePresent u e ∧
        (edgeWest u e = a.id ∨ edgeEast u e = a.id) ∧
        Reachable (⟨0⟩ : PresentVertex u) ⟨edgeWest u e⟩ ∧
        Reachable (⟨0⟩ : PresentVertex u) ⟨edgeEast u e⟩

private theorem allocated_image_injective
    {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u w T eφ vφ)
    {a b : PresentVertex u}
    (ha : ∃ m, a.id < (kmswStage u m).nextVertex)
    (hb : ∃ m, b.id < (kmswStage u m).nextVertex)
    (hab : (⟨vφ a.id⟩ : PresentVertex w) = ⟨vφ b.id⟩) : a = b := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  let k := max m n
  have ham : a.id < (kmswStage u k).nextVertex :=
    hm.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_left m n))
  have hbm : b.id < (kmswStage u k).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_right m n))
  have hval : vφ a.id = vφ b.id := congrArg PresentVertex.id hab
  have hid := (D.stage_sim k).vertex_injective a.id b.id ham hbm hval
  cases a
  cases b
  exact congrArg PresentVertex.mk hid

private theorem mapped_local_present_edge_reachable
    {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u w T eφ vφ)
    (m e : ℕ) (he : e < (kmswStage u m).nextEdge)
    (hp : (kmswStage u m).present e = true) :
    eφ e ∈ stageReachablePresentEdges w (T m) := by
  rw [← D.edge_image m]
  exact Set.mem_image_of_mem eφ ⟨he, hp⟩

private theorem allocated_maps_to_root_reachable
    {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u w T eφ vφ)
    (a : PresentVertex u)
    (ha : ∃ m, a.id < (kmswStage u m).nextVertex) :
    Reachable (⟨0⟩ : PresentVertex w) (⟨vφ a.id⟩ : PresentVertex w) := by
  by_cases hroot : a.id = 0
  · rw [hroot, D.root]
  · obtain ⟨e, he, hend, _hwestReach, _heastReach⟩ :=
      D.allocated_nonroot_incident a ha hroot
    obtain ⟨m, hem, hpm⟩ := he
    have himage := mapped_local_present_edge_reachable D m e hem hpm
    change eφ e < (kmswStage w (T m)).nextEdge ∧
      (kmswStage w (T m)).present (eφ e) = true ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (T m)).west (eφ e)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w)
        ⟨(kmswStage w (T m)).east (eφ e)⟩ at himage
    obtain ⟨heBound, _hePresent, hwestReach, heastReach⟩ := himage
    have hlocalEnds := edge_endpoints_eq u hem
    have hinc := (D.stage_sim m).incidence e hem
    have hwestMap : vφ (edgeWest u e) =
        (kmswStage w (T m)).west (eφ e) := by
      calc
        vφ (edgeWest u e) = vφ ((kmswStage u m).west e) :=
          congrArg vφ hlocalEnds.1.symm
        _ = (kmswStage w (T m)).west (eφ e) := hinc.1.symm
    have heastMap : vφ (edgeEast u e) =
        (kmswStage w (T m)).east (eφ e) := by
      calc
        vφ (edgeEast u e) = vφ ((kmswStage u m).east e) :=
          congrArg vφ hlocalEnds.2.symm
        _ = (kmswStage w (T m)).east (eφ e) := hinc.2.symm
    rcases hend with hwest | heast
    · have hfa : (⟨vφ a.id⟩ : PresentVertex w) =
          ⟨(kmswStage w (T m)).west (eφ e)⟩ := by
        apply congrArg PresentVertex.mk
        rw [← hwest]
        exact hwestMap
      rw [hfa]
      exact hwestReach
    · have hfa : (⟨vφ a.id⟩ : PresentVertex w) =
          ⟨(kmswStage w (T m)).east (eφ e)⟩ := by
        apply congrArg PresentVertex.mk
        rw [← heast]
        exact heastMap
      rw [hfa]
      exact heastReach

private theorem lift_path_from_allocated
    {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u w T eφ vφ)
    (f : PresentVertex u → PresentVertex w)
    (hf : ∀ a, f a = (⟨vφ a.id⟩ : PresentVertex w))
    {a : PresentVertex u}
    (ha : ∃ m, a.id < (kmswStage u m).nextVertex)
    {v : PresentVertex w} (q : Path (f a) v) :
    ∃ b : PresentVertex u,
      (∃ m, b.id < (kmswStage u m).nextVertex) ∧
      ∃ r : Path a b, f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices := by
  induction q with
  | nil =>
    refine ⟨a, ha, Path.nil, ?_, ?_⟩
    · exact rfl
    · intro y hy
      have hy' : y = a := by
        simpa only [Quiver.Path.vertices_nil, List.mem_singleton] using hy
      subst y
      simp
  | @cons x y q e ih =>
    obtain ⟨b, hb, r, hfb, hvertices⟩ := ih
    have hrootX : Reachable (⟨0⟩ : PresentVertex w) x := by
      have hrootB : Reachable (⟨0⟩ : PresentVertex w) (f b) := by
        simpa only [hf] using allocated_maps_to_root_reachable D b hb
      simpa only [hfb] using hrootB
    obtain ⟨qpath⟩ := hrootX
    have hrootY : Reachable (⟨0⟩ : PresentVertex w) y := ⟨qpath.cons e⟩
    obtain ⟨N, hN⟩ := e.property.1.eventually_present
    obtain ⟨m, hm⟩ := D.time_unbounded N
    obtain ⟨heBoundW, hePresentW⟩ := hN (T m) hm
    have hEndsW := edge_endpoints_eq w heBoundW
    have heReach : e.val ∈ stageReachablePresentEdges w (T m) := by
      change e.val < (kmswStage w (T m)).nextEdge ∧
        (kmswStage w (T m)).present e.val = true ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (T m)).west e.val⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w)
          ⟨(kmswStage w (T m)).east e.val⟩
      refine ⟨heBoundW, hePresentW, ?_, ?_⟩
      · rw [hEndsW.1, e.property.2.1]
        exact ⟨qpath⟩
      · rw [hEndsW.2, e.property.2.2]
        exact hrootY
    have himage : e.val ∈ eφ '' {j | j < (kmswStage u m).nextEdge ∧
        (kmswStage u m).present j = true} := by
      rw [D.edge_image m]
      exact heReach
    change ∃ j, (j < (kmswStage u m).nextEdge ∧
      (kmswStage u m).present j = true) ∧ eφ j = e.val at himage
    obtain ⟨j, hj, hje⟩ := himage
    obtain ⟨hjBound, hjPresent⟩ := hj
    have hEndsU := edge_endpoints_eq u hjBound
    have hEndsUAlloc := kmswStage_endpoints_lt_nextVertex u m j hjBound
    have hinc := (D.stage_sim m).incidence j hjBound
    have hsourceMap : vφ ((kmswStage u m).west j) = x.id := by
      calc
        vφ ((kmswStage u m).west j) =
            (kmswStage w (T m)).west (eφ j) := hinc.1.symm
        _ = (kmswStage w (T m)).west e.val := by rw [hje]
        _ = edgeWest w e.val := hEndsW.1
        _ = x.id := e.property.2.1
    have htargetMap : vφ ((kmswStage u m).east j) = y.id := by
      calc
        vφ ((kmswStage u m).east j) =
            (kmswStage w (T m)).east (eφ j) := hinc.2.symm
        _ = (kmswStage w (T m)).east e.val := by rw [hje]
        _ = edgeEast w e.val := hEndsW.2
        _ = y.id := e.property.2.2
    have hwestAlloc : ∃ n, (kmswStage u m).west j <
        (kmswStage u n).nextVertex := ⟨m, hEndsUAlloc.1⟩
    have hwestImage : f (⟨(kmswStage u m).west j⟩ : PresentVertex u) = x := by
      rw [hf]
      apply congrArg PresentVertex.mk
      exact hsourceMap
    have hwestImage' :
        (⟨vφ ((kmswStage u m).west j)⟩ : PresentVertex w) =
          ⟨vφ b.id⟩ := by
      simpa only [hf] using hwestImage.trans hfb.symm
    have hwestEq : (⟨(kmswStage u m).west j⟩ : PresentVertex u) = b :=
      allocated_image_injective D hwestAlloc hb hwestImage'
    let c : PresentVertex u := ⟨(kmswStage u m).east j⟩
    have hcAlloc : ∃ n, c.id < (kmswStage u n).nextVertex :=
      ⟨m, hEndsUAlloc.2⟩
    have heLocal : (⟨(kmswStage u m).west j⟩ : PresentVertex u) ⟶ c :=
      ⟨j, ⟨m, hjBound, hjPresent⟩,
        hEndsU.1.symm, hEndsU.2.symm⟩
    have heLocal' : b ⟶ c := hwestEq ▸ heLocal
    have hfc : f c = y := by
      rw [hf]
      apply congrArg PresentVertex.mk
      exact htargetMap
    refine ⟨c, hcAlloc, r.cons heLocal', hfc, ?_⟩
    intro z hz
    rcases (Quiver.Path.mem_vertices_cons r heLocal').1 hz with hz | hz
    · exact (Quiver.Path.mem_vertices_cons q e).2 (Or.inl (hvertices z hz))
    · subst z
      exact (Quiver.Path.mem_vertices_cons q e).2 (Or.inr hfc)

/-- From stagewise incidence and the exact reachable-present-edge image, the
limit vertex map induced by `vφ` is injective on allocated vertices, lifts
rooted paths, and has image exactly the root-reachable target vertices. The
source-side incidence condition in `HatImageLimitInput` is the explicit
structural obligation for allocated non-root vertices. This is a generic
limit argument for the use of `lem-quad-kmsw` in `lem-infty-cut`, not -/
theorem hatImageLimit
    {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}
    (D : HatImageLimitInput u w T eφ vφ) :
    ∃ f : PresentVertex u → PresentVertex w,
      (∀ a b, (∃ m, a.id < (kmswStage u m).nextVertex) →
        (∃ m, b.id < (kmswStage u m).nextVertex) → f a = f b → a = b) ∧
      f ⟨0⟩ = ⟨0⟩ ∧
      (∀ a, (∃ m, a.id < (kmswStage u m).nextVertex) →
        ∀ v (q : Path (f a) v),
          ∃ b, (∃ m, b.id < (kmswStage u m).nextVertex) ∧
            ∃ r : Path a b, f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices) ∧
      (∀ v, Reachable (⟨0⟩ : PresentVertex w) v →
        ∃ a, (∃ m, a.id < (kmswStage u m).nextVertex) ∧ f a = v) ∧
      (∀ a, (∃ m, a.id < (kmswStage u m).nextVertex) →
        Reachable (⟨0⟩ : PresentVertex w) (f a)) := by
  let f : PresentVertex u → PresentVertex w := fun a => ⟨vφ a.id⟩
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb hab
    exact allocated_image_injective D ha hb (by simpa [f] using hab)
  · change (⟨vφ 0⟩ : PresentVertex w) = ⟨0⟩
    exact congrArg PresentVertex.mk D.root
  · intro a ha v q
    exact lift_path_from_allocated D f (by intro a; rfl) ha q
  · intro v hv
    obtain ⟨q⟩ := hv
    have hrootAlloc : ∃ m, (⟨0⟩ : PresentVertex u).id <
        (kmswStage u m).nextVertex := by
      refine ⟨0, ?_⟩
      simp [kmswStage, kmswInit]
    have q' : Path (f (⟨0⟩ : PresentVertex u)) v := by
      simpa [f, D.root] using q
    obtain ⟨b, hb, r, hfb, _hvertices⟩ :=
      lift_path_from_allocated D f (by intro a; rfl) hrootAlloc q'
    exact ⟨b, hb, hfb⟩
  · intro a ha
    exact allocated_maps_to_root_reachable D a ha

end DirectedDistances.KMSW
