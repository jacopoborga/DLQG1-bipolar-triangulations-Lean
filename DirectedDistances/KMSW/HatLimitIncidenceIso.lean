/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.HatImageLimit
public import DirectedDistances.KMSW.BusemannM0Unconditional

/-! # Graph layer of the hatted half of `lem-quad-kmsw`

Explicit limit bijections between the allocated vertices and present edge IDs of
the hatted code `u` and the root-reachable vertices and edges of the global
walk `w`, from a `HatImageLimitInput`
identification remain; this is a helper, not `lem-quad-kmsw` itself. -/

public section
namespace DirectedDistances.KMSW

open Quiver

section Generic

variable {u w : ℕ → Fin 3} {T eφ vφ : ℕ → ℕ}

theorem edge_data
    (D : HatImageLimitInput u w T eφ vφ) {e : ℕ} (he : EdgePresent u e) :
    EdgePresent w (eφ e) ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w (eφ e)⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w (eφ e)⟩ ∧
      edgeWest w (eφ e) = vφ (edgeWest u e) ∧
      edgeEast w (eφ e) = vφ (edgeEast u e) := by
  obtain ⟨m, hem, hpm⟩ := he
  have hmem : eφ e ∈ stageReachablePresentEdges w (T m) := by
    rw [← D.edge_image m]
    exact ⟨e, ⟨hem, hpm⟩, rfl⟩
  change eφ e < (kmswStage w (T m)).nextEdge ∧
    (kmswStage w (T m)).present (eφ e) = true ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (T m)).west (eφ e)⟩ ∧
    Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (T m)).east (eφ e)⟩ at hmem
  obtain ⟨hb, hp, hr1, hr2⟩ := hmem
  have hW := edge_endpoints_eq w hb
  have hU := edge_endpoints_eq u hem
  have hinc := (D.stage_sim m).incidence e hem
  have h1 : edgeWest w (eφ e) = vφ (edgeWest u e) := by
    rw [← hW.1, hinc.1, hU.1]
  have h2 : edgeEast w (eφ e) = vφ (edgeEast u e) := by
    rw [← hW.2, hinc.2, hU.2]
  refine ⟨⟨T m, hb, hp⟩, ?_, ?_, h1, h2⟩
  · rw [← hW.1]; exact hr1
  · rw [← hW.2]; exact hr2

theorem edge_cover
    (D : HatImageLimitInput u w T eφ vφ) {e' : ℕ} (he : EdgePresent w e')
    (h1 : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e'⟩)
    (h2 : Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e'⟩) :
    ∃ j, EdgePresent u j ∧ eφ j = e' := by
  obtain ⟨N, hN⟩ := he.eventually_present
  obtain ⟨m, hm⟩ := D.time_unbounded N
  obtain ⟨hb, hp⟩ := hN (T m) hm
  have hW := edge_endpoints_eq w hb
  have hmem : e' ∈ stageReachablePresentEdges w (T m) := by
    change e' < (kmswStage w (T m)).nextEdge ∧
      (kmswStage w (T m)).present e' = true ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (T m)).west e'⟩ ∧
      Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w (T m)).east e'⟩
    refine ⟨hb, hp, ?_, ?_⟩
    · rw [hW.1]; exact h1
    · rw [hW.2]; exact h2
  rw [← D.edge_image m] at hmem
  obtain ⟨j, ⟨hj, hjp⟩, hje⟩ := hmem
  exact ⟨j, ⟨m, hj, hjp⟩, hje⟩

theorem edge_endpoints_alloc (u : ℕ → Fin 3) {j : ℕ} (hj : EdgePresent u j) :
    (∃ m, edgeWest u j < (kmswStage u m).nextVertex) ∧
      (∃ m, edgeEast u j < (kmswStage u m).nextVertex) := by
  obtain ⟨m, hem, _⟩ := hj
  have hU := edge_endpoints_eq u hem
  have hA := kmswStage_endpoints_lt_nextVertex u m j hem
  exact ⟨⟨m, hU.1 ▸ hA.1⟩, ⟨m, hU.2 ▸ hA.2⟩⟩

theorem vertex_inj
    (D : HatImageLimitInput u w T eφ vφ) {a b : ℕ}
    (ha : ∃ m, a < (kmswStage u m).nextVertex)
    (hb : ∃ m, b < (kmswStage u m).nextVertex) (h : vφ a = vφ b) : a = b := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  exact (D.stage_sim (max m n)).vertex_injective a b
    (hm.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_left m n)))
    (hn.trans_le (CutConverse.nextVertex_mono u (Nat.le_max_right m n))) h

/-- (H1) `eφ` is injective on present edges of the hatted code. -/
theorem hatLimit_edge_injOn (D : HatImageLimitInput u w T eφ vφ) :
    Set.InjOn eφ {e | EdgePresent u e} := by
  intro e he f hf h
  obtain ⟨m, hm, _⟩ := he
  obtain ⟨n, hn, _⟩ := hf
  exact (D.stage_sim (max m n)).edge_injective e f
    (hm.trans_le (kmswStage_nextEdge_mono u (Nat.le_max_left m n)))
    (hn.trans_le (kmswStage_nextEdge_mono u (Nat.le_max_right m n))) h

/-- (H2) Incidence of the limit edge map. -/
theorem hatLimit_edge_incidence (D : HatImageLimitInput u w T eφ vφ) {e : ℕ}
    (he : EdgePresent u e) :
    EdgePresent w (eφ e) ∧ edgeWest w (eφ e) = vφ (edgeWest u e) ∧
      edgeEast w (eφ e) = vφ (edgeEast u e) := by
  obtain ⟨h0, -, -, h1, h2⟩ := edge_data D he
  exact ⟨h0, h1, h2⟩

/-- (H3) Exact edge image. -/
theorem hatLimit_edge_image (D : HatImageLimitInput u w T eφ vφ) :
    eφ '' {e | EdgePresent u e} =
      {e' | EdgePresent w e' ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e'⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e'⟩} := by
  ext e'
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨h0, h1, h2, -, -⟩ := edge_data D he
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    obtain ⟨j, hj, hje⟩ := edge_cover D h0 h1 h2
    exact ⟨j, hj, hje⟩

theorem alloc_reachable (D : HatImageLimitInput u w T eφ vφ) {a : ℕ}
    (ha : ∃ m, a < (kmswStage u m).nextVertex) :
    Reachable (⟨0⟩ : PresentVertex w) ⟨vφ a⟩ := by
  by_cases h0 : a = 0
  · subst h0
    rw [D.root]
  · obtain ⟨e, he, hend, -, -⟩ :=
      D.allocated_nonroot_incident (⟨a⟩ : PresentVertex u) ha h0
    obtain ⟨-, h1, h2, h3, h4⟩ := edge_data D he
    rcases hend with h | h
    · have : vφ a = edgeWest w (eφ e) := by rw [h3, h]
      rw [this]; exact h1
    · have : vφ a = edgeEast w (eφ e) := by rw [h4, h]
      rw [this]; exact h2

theorem alloc_surj (D : HatImageLimitInput u w T eφ vφ)
    {v : PresentVertex w} (q : Path (⟨0⟩ : PresentVertex w) v) :
    ∃ a, (∃ m, a < (kmswStage u m).nextVertex) ∧ vφ a = v.id := by
  induction q with
  | nil =>
    exact ⟨0, ⟨0, by simp [kmswStage, kmswInit]⟩, D.root⟩
  | @cons x y q e ih =>
    have hx : Reachable (⟨0⟩ : PresentVertex w) x := ⟨q⟩
    have hy : Reachable (⟨0⟩ : PresentVertex w) y := ⟨q.cons e⟩
    obtain ⟨j, hj, hje⟩ := edge_cover D e.property.1
      (by rw [e.property.2.1]; exact hx) (by rw [e.property.2.2]; exact hy)
    obtain ⟨-, -, -, -, h4⟩ := edge_data D hj
    refine ⟨edgeEast u j, (edge_endpoints_alloc u hj).2, ?_⟩
    rw [← h4, hje, e.property.2.2]

/-- The vertex part of the graph isomorphism. -/
@[expose] noncomputable def hatLimitVertexEquiv
    (D : HatImageLimitInput u w T eφ vφ) :
    {a : PresentVertex u // ∃ m, a.id < (kmswStage u m).nextVertex} ≃
      {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v} :=
  Equiv.ofBijective
    (fun a => ⟨⟨vφ a.1.id⟩, alloc_reachable D a.2⟩)
    (by
      constructor
      · rintro ⟨⟨a⟩, ha⟩ ⟨⟨b⟩, hb⟩ h
        have h' : vφ a = vφ b := congrArg (fun x => x.1.id) h
        exact Subtype.ext (congrArg PresentVertex.mk (vertex_inj D ha hb h'))
      · rintro ⟨v, ⟨q⟩⟩
        obtain ⟨a, ha, hav⟩ := alloc_surj D q
        refine ⟨⟨⟨a⟩, ha⟩, Subtype.ext ?_⟩
        cases v
        exact congrArg PresentVertex.mk hav)

/-- The edge part of the graph isomorphism. -/
@[expose] noncomputable def hatLimitEdgeEquiv
    (D : HatImageLimitInput u w T eφ vφ) :
    {e : ℕ // EdgePresent u e} ≃
      {e' : ℕ // EdgePresent w e' ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e'⟩ ∧
        Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e'⟩} :=
  Equiv.ofBijective
    (fun e => ⟨eφ e.1, by
      obtain ⟨h0, h1, h2, -, -⟩ := edge_data D e.2
      exact ⟨h0, h1, h2⟩⟩)
    ⟨fun e f h => Subtype.ext
      (hatLimit_edge_injOn D e.2 f.2 (congrArg Subtype.val h)),
    by
      rintro ⟨e', h0, h1, h2⟩
      obtain ⟨j, hj, hje⟩ := edge_cover D h0 h1 h2
      exact ⟨⟨j, hj⟩, Subtype.ext hje⟩⟩

/-- Graph layer of the hatted half of `lem-quad-kmsw`
are given by `vφ` and `eφ`, and are compatible with ordered endpoints. Faces,
rotation and the planar identification remain; not counted. -/
theorem hatLimitIncidenceIso (D : HatImageLimitInput u w T eφ vφ) :
    ∃ (V : {a : PresentVertex u // ∃ m, a.id < (kmswStage u m).nextVertex} ≃
          {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v})
      (E : {e : ℕ // EdgePresent u e} ≃
          {e' : ℕ // EdgePresent w e' ∧
            Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e'⟩ ∧
            Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e'⟩}),
      (∀ a, (V a).1.id = vφ a.1.id) ∧ (∀ e, (E e).1 = eφ e.1) ∧
      (∀ e : {e : ℕ // EdgePresent u e},
        edgeWest w (E e).1 = vφ (edgeWest u e.1) ∧
        edgeEast w (E e).1 = vφ (edgeEast u e.1)) := by
  refine ⟨hatLimitVertexEquiv D, hatLimitEdgeEquiv D, fun a => rfl,
    fun e => rfl, fun e => ?_⟩
  obtain ⟨-, -, -, h3, h4⟩ := edge_data D e.2
  exact ⟨h3, h4⟩

end Generic

/-- Unconditional instance for the hatted code: for every `w` with flow-line
hits there are maps with the stagewise limit input and the graph-layer
remain; not counted. -/
theorem hatLimitIncidenceIso_unconditional (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∃ T eφ vφ : ℕ → ℕ,
      HatImageLimitInput (hatCodes w h) w T eφ vφ ∧
      ∃ (V : {a : PresentVertex (hatCodes w h) //
              ∃ m, a.id < (kmswStage (hatCodes w h) m).nextVertex} ≃
            {v : PresentVertex w // Reachable (⟨0⟩ : PresentVertex w) v})
        (E : {e : ℕ // EdgePresent (hatCodes w h) e} ≃
            {e' : ℕ // EdgePresent w e' ∧
              Reachable (⟨0⟩ : PresentVertex w) ⟨edgeWest w e'⟩ ∧
              Reachable (⟨0⟩ : PresentVertex w) ⟨edgeEast w e'⟩}),
        (∀ a, (V a).1.id = vφ a.1.id) ∧ (∀ e, (E e).1 = eφ e.1) ∧
        (∀ e : {e : ℕ // EdgePresent (hatCodes w h) e},
          edgeWest w (E e).1 = vφ (edgeWest (hatCodes w h) e.1) ∧
          edgeEast w (E e).1 = vφ (edgeEast (hatCodes w h) e.1)) := by
  obtain ⟨eφ, vφ, D⟩ := hatInputExists w h
  exact ⟨_, eφ, vφ, D, hatLimitIncidenceIso D⟩

end DirectedDistances.KMSW
