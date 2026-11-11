/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.CutVertexConverse
public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
import DirectedDistances.KMSW.UIQBOTOrientation
import DirectedDistances.KMSW.NoMissingEdgesAE

/-! # The link around a KMSW vertex

The finite rotation cycle at a vertex connects its present neighbors after -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open scoped Classical
open DirectedDistances.RandomWalk

private theorem finite_cycle_enumeration {D : Type*} [DecidableEq D]
    (σ : Equiv.Perm D) (s : Finset D) (hs : σ.IsCycleOn (s : Set D))
    (r : D) (hr : r ∈ s) :
    ∃ (l : D) (ds : List D), ds.Nodup ∧ ds.head? = some r ∧
      ds.getLast? = some l ∧ (∀ d, d ∈ ds ↔ d ∈ s) ∧
      ds.IsChain (fun d e => σ d = e) ∧ σ l = r ∧
      ds = List.ofFn (fun i : Fin s.card => (σ ^ i.val) r) := by
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨r, hr⟩
  let f : Fin s.card → D := fun i => (σ ^ i.val) r
  refine ⟨(σ ^ (s.card - 1)) r, List.ofFn f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_ofFn_ofInjective
    intro i j hij
    exact Fin.ext (hs.injOn_pow_apply hr i.isLt j.isLt hij)
  · simp only [List.head?_eq_getElem?, List.getElem?_ofFn, hpos,
      ↓reduceDIte]
    rfl
  · simp only [List.getLast?_eq_getElem?, List.length_ofFn,
      List.getElem?_ofFn, show s.card - 1 < s.card by omega,
      ↓reduceDIte, f]
  · intro d
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact hs.1.mapsTo.perm_pow i.val hr
    · intro hd
      obtain ⟨i, hi, hid⟩ := hs.exists_pow_eq hr hd
      exact ⟨⟨i, hi⟩, hid⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn, f]
    exact (congrArg (fun τ : Equiv.Perm D => τ r) (pow_succ' σ i)).symm
  · have htail : (σ ^ (s.card - 1)) r = σ.symm r := by
      apply σ.injective
      rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos,
        hs.pow_card_apply hr]
      exact (Equiv.apply_symm_apply σ r).symm
    simpa only [Equiv.apply_symm_apply] using congrArg σ htail
  · rfl

/-- The finite rotation cycle at a vertex can be listed from any chosen dart -/
private theorem kmsw_vertex_dart_cycle_enumeration (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) (d₀ : ℕ × Bool)
    (hd₀ : (if d₀.2 then edgeEast w d₀.1 else edgeWest w d₀.1) = v) :
    ∃ (l : ℕ × Bool) (ds : List (ℕ × Bool)), ds.Nodup ∧ ds.head? = some d₀ ∧
      ds.getLast? = some l ∧ (∀ d, d ∈ ds ↔
        (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v) ∧
      ds.IsChain (fun d e => kmswInfRot w hfin d = e) ∧
      kmswInfRot w hfin l = d₀ ∧
      ds = List.ofFn (fun i : Fin ((kmsw_darts_at_vertex_finite w hfin v).toFinset.card) =>
        (kmswInfRot w hfin ^ i.val) d₀) := by
  classical
  let S : Set (ℕ × Bool) :=
    {d | (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v}
  have hS : S.Finite := by
    simpa only [S] using kmsw_darts_at_vertex_finite w hfin v
  let s := hS.toFinset
  have hr : d₀ ∈ s := by
    rw [Set.Finite.mem_toFinset]
    exact hd₀
  have hc : (kmswInfRot w hfin).IsCycleOn (s : Set (ℕ × Bool)) := by
    simpa only [Set.Finite.coe_toFinset, s, S] using
      kmswInfRot_isCycleOn_vertex w hfin v
  obtain ⟨l, ds, hnd, hh, ht, hm, hchain, hlast, hform⟩ :=
    finite_cycle_enumeration (kmswInfRot w hfin) s hc d₀ hr
  refine ⟨l, ds, hnd, hh, ?_, ?_, hchain, hlast, ?_⟩
  · simpa [s] using ht
  · intro d
    rw [hm, Set.Finite.mem_toFinset]
    rfl
  · simpa [s] using hform

private def kmswDartEndpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private def kmswDartFarEndpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeWest w d.1 else edgeEast w d.1

private def kmswDartFlip (d : ℕ × Bool) : ℕ × Bool := (d.1, !d.2)

/-- The outer-face corner dart attached to a non-root boundary-corner index. -/
private noncomputable def kmswOuterCornerDart (w : ℕ → Fin 3) (k : Bool × ℕ) : ℕ × Bool :=
  if k.1 then (kmswRightBoundaryEdge w (k.2 + 1), true)
  else (kmswLeftBoundaryEdge w k.2, false)

private theorem kmsw_outerCornerDart_vertex (w : ℕ → Fin 3)
    (hL0 : ∀ j, 0 ≤ L w j) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (k : Bool × ℕ) :
    kmswDartEndpoint w (kmswDartFlip (kmswOuterCornerDart w k)) =
      kmswOuterCornerVertex w (some k) := by
  cases k with
  | mk right i =>
    cases right
    · simp [kmswDartEndpoint, kmswDartFlip, kmswOuterCornerDart,
        kmswOuterCornerVertex]
    · obtain ⟨_, hstep, _, _⟩ :=
        kmswRightBoundary_infinite_present_path w hL0 hR
      simp only [kmswDartEndpoint, kmswDartFlip, kmswOuterCornerDart,
        kmswOuterCornerVertex, ↓reduceIte]
      exact (hstep i).symm

private theorem kmsw_outerCorner_key_of_boundary (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hv0 : v ≠ 0)
    (hbdry : OnLeftBoundary w v ∨ OnRightBoundary w v) :
    ∃ k : Bool × ℕ, kmswOuterCornerVertex w (some k) = v := by
  rcases hbdry with hleft | hright
  · obtain ⟨e, he, hev⟩ := hleft
    obtain ⟨i, rfl⟩ := (isLeftBoundaryEdge_iff w htrans e).mp he
    rcases hev with hew | hee
    · obtain ⟨_, _, hzero, _⟩ :=
        kmswLeftBoundary_infinite_present_path w htrans hL0 hR
      cases i with
      | zero => exact (hv0 (hew.symm.trans hzero)).elim
      | succ i =>
          refine ⟨(false, i), ?_⟩
          change edgeEast w (kmswLeftBoundaryEdge w i) = v
          exact (kmswLeftBoundary_infinite_present_path w htrans hL0 hR).2.1 i |>.trans hew
    · exact ⟨(false, i), by simpa [kmswOuterCornerVertex] using hee⟩
  · obtain ⟨e, he, hev⟩ := hright
    obtain ⟨i, rfl⟩ := (isRightBoundaryEdge_iff w hR e).mp he
    rcases hev with hew | hee
    · obtain ⟨_, _, hzero, _⟩ :=
        kmswRightBoundary_infinite_present_path w hL0 hR
      cases i with
      | zero => exact (hv0 (hew.symm.trans hzero)).elim
      | succ i =>
          refine ⟨(true, i), ?_⟩
          change edgeEast w (kmswRightBoundaryEdge w i) = v
          exact (kmswRightBoundary_infinite_present_path w hL0 hR).2.1 i |>.trans hew
    · exact ⟨(true, i), by simpa [kmswOuterCornerVertex] using hee⟩

private theorem kmsw_boundary_corner_classify (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hv0 : v ≠ 0) {c : ℕ × Bool}
    (hc : (∃ i, c = (kmswLeftBoundaryEdge w i, false)) ∨
      (∃ i, c = (kmswRightBoundaryEdge w i, true)))
    (hcv : kmswDartEndpoint w (kmswDartFlip c) = v) :
    ∃ k : Bool × ℕ, kmswOuterCornerVertex w (some k) = v ∧
      kmswOuterCornerDart w k = c := by
  rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨(false, i), ?_, ?_⟩
    · simpa [kmswOuterCornerVertex, kmswDartEndpoint, kmswDartFlip] using hcv
    · simp [kmswOuterCornerDart]
  · obtain ⟨_, hstep, hzero, _⟩ :=
      kmswRightBoundary_infinite_present_path w hL0 hR
    cases i with
    | zero =>
        have hv : v = 0 := by
          exact hcv.symm.trans hzero
        exact (hv0 hv).elim
    | succ i =>
        have hcv' : edgeWest w (kmswRightBoundaryEdge w (i + 1)) = v := by
          simpa [kmswDartEndpoint, kmswDartFlip] using hcv
        refine ⟨(true, i), ?_, ?_⟩
        · change edgeEast w (kmswRightBoundaryEdge w i) = v
          exact (hstep i).trans hcv'
        · simp [kmswOuterCornerDart]

private theorem kmsw_linkStartDart (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hv0 : v ≠ 0) :
    ∃ d₀ : ℕ × Bool,
      kmswDartEndpoint w d₀ = v ∧
      ((OnLeftBoundary w v ∨ OnRightBoundary w v) → ∃ k : Bool × ℕ,
        kmswOuterCornerVertex w (some k) = v ∧
          d₀ = kmswDartFlip (kmswOuterCornerDart w k)) := by
  by_cases hbd : OnLeftBoundary w v ∨ OnRightBoundary w v
  · obtain ⟨k, hk⟩ := kmsw_outerCorner_key_of_boundary w htrans hR hL0 hv0 hbd
    refine ⟨kmswDartFlip (kmswOuterCornerDart w k), ?_, ?_⟩
    · exact (kmsw_outerCornerDart_vertex w hL0 hR k).trans hk
    · intro _
      exact ⟨k, hk, rfl⟩
  · obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
    obtain ⟨e, _, he⟩ := allocated_vertex_has_incoming_present_edge w hL0 v
      ⟨n, hn⟩ hv0
    refine ⟨(e, true), he, ?_⟩
    intro hb'
    exact (hbd hb').elim

private theorem kmsw_edgeWest_ne_edgeEast (w : ℕ → Fin 3) (e : ℕ) :
    edgeWest w e ≠ edgeEast w e := by
  have hstrict := kmswStageRank_strict w e e (kmsw_edge_allocated_by_self w e)
  have hend := edge_endpoints_eq w (kmsw_edge_allocated_by_self w e)
  rw [hend.1, hend.2] at hstrict
  intro he
  rw [he] at hstrict
  exact (lt_irrefl _ hstrict)

private theorem kmswDartFarEndpoint_ne_endpoint (w : ℕ → Fin 3)
    (d : ℕ × Bool) : kmswDartFarEndpoint w d ≠ kmswDartEndpoint w d := by
  cases d with
  | mk e b =>
      cases b
      · simpa [kmswDartFarEndpoint, kmswDartEndpoint] using
          (kmsw_edgeWest_ne_edgeEast w e).symm
      · simpa [kmswDartFarEndpoint, kmswDartEndpoint] using
          kmsw_edgeWest_ne_edgeEast w e

private theorem kmsw_neighborLinkStep_of_rotated_darts (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (v : ℕ) (d e : ℕ × Bool)
    (hd : kmswDartEndpoint w d = v) (he : kmswDartEndpoint w e = v)
    (hrot : kmswInfRot w hfin d = e)
    (hleft : ∀ i, (e.1, !e.2) ≠ (kmswLeftBoundaryEdge w i, false))
    (hright : ∀ i, (e.1, !e.2) ≠ (kmswRightBoundaryEdge w i, true)) :
    neighborLinkStep w v (kmswDartFarEndpoint w d)
      (kmswDartFarEndpoint w e) := by
  have hcorner : (e.1, !e.2) =
      ((kmswInfRot w hfin d).1, !(kmswInfRot w hfin d).2) := by
    rw [hrot]
  obtain ⟨c, _, hp, hs, _, _⟩ := kmswInfCorner_triangle_edge w hfin
    htrans hR hL0 d v hd (e.1, !e.2) hcorner hleft hright
  have hdfar : kmswDartFarEndpoint w d ≠ v := by
    intro huv
    exact kmswDartFarEndpoint_ne_endpoint w d
      (huv.trans hd.symm)
  have hefar : kmswDartFarEndpoint w e ≠ v := by
    intro huv
    exact kmswDartFarEndpoint_ne_endpoint w e
      (huv.trans he.symm)
  rw [hrot] at hs
  exact ⟨c.1, hp, hs, hdfar, hefar⟩

/-- If a non-root vertex does not lie on both outer boundaries, its present
neighbors are connected by triangle edges while avoiding it -/
theorem kmsw_nonzero_neighbors_connected (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hv0 : v ≠ 0)
    (hnotboth : ¬ (OnLeftBoundary w v ∧ OnRightBoundary w v))
    {u u' : ℕ} (hu : PresentUndirectedNeighbor w v u)
    (hu' : PresentUndirectedNeighbor w v u') :
    ∃ p : FiniteUndirectedEdgePath w u u',
      (∀ z ∈ p.vertices, z ≠ v) ∧
      ∀ e ∈ p.edgeIds, EdgePresent w e := by
  classical
  obtain ⟨d₀, hd₀, hstart⟩ :=
    kmsw_linkStartDart w hfin htrans hR hL0 hv0
  obtain ⟨l, ds, hnd, hh, hlast?, hdartCover, hdsChain, hrotLast, hform⟩ :=
    kmsw_vertex_dart_cycle_enumeration w hfin v d₀ hd₀
  cases ds with
  | nil => simp at hh
  | cons a tail =>
      have ha : a = d₀ := by simpa using hh
      subst a
      let far := kmswDartFarEndpoint w
      let head := far d₀
      let rest := tail.map far
      have hdart_mem (d : ℕ × Bool) : d ∈ d₀ :: tail ↔
          kmswDartEndpoint w d = v := by
        simpa [kmswDartEndpoint] using hdartCover d
      have hmap_mem (x : ℕ) : x ∈ head :: rest ↔
          ∃ d : ℕ × Bool, kmswDartEndpoint w d = v ∧ far d = x := by
        change x ∈ (d₀ :: tail).map far ↔ _
        rw [List.mem_map]
        constructor
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, (hdart_mem d).mp hd, rfl⟩
        · rintro ⟨d, hd, rfl⟩
          exact ⟨d, (hdart_mem d).mpr hd, rfl⟩
      have hcover (x : ℕ) : x ∈ head :: rest ↔
          PresentUndirectedNeighbor w v x := by
        rw [hmap_mem]
        constructor
        · rintro ⟨d, hd, hfar⟩
          have hne : x ≠ v := by
            intro hxv
            apply kmswDartFarEndpoint_ne_endpoint w d
            calc
              kmswDartFarEndpoint w d = x := hfar
              _ = v := hxv
              _ = kmswDartEndpoint w d := hd.symm
          cases hb : d.2
          · have hwest : edgeWest w d.1 = v := by
              simpa [kmswDartEndpoint, hb] using hd
            have heast : edgeEast w d.1 = x := by
              simpa [far, kmswDartFarEndpoint, hb] using hfar
            exact ⟨hne, d.1, edgePresent_of_nonneg_of_unbounded w hL0 hR d.1,
              Or.inl ⟨hwest, heast⟩⟩
          · have heast : edgeEast w d.1 = v := by
              simpa [kmswDartEndpoint, hb] using hd
            have hwest : edgeWest w d.1 = x := by
              simpa [far, kmswDartFarEndpoint, hb] using hfar
            exact ⟨hne, d.1, edgePresent_of_nonneg_of_unbounded w hL0 hR d.1,
              Or.inr ⟨heast, hwest⟩⟩
        · rintro ⟨hxv, e, hp, hstep⟩
          rcases hstep with ⟨hwest, heast⟩ | ⟨heast, hwest⟩
          · refine ⟨(e, false), ?_, ?_⟩
            · simpa [kmswDartEndpoint] using hwest
            · simpa [far, kmswDartFarEndpoint] using heast
          · refine ⟨(e, true), ?_, ?_⟩
            · simpa [kmswDartEndpoint] using heast
            · simpa [far, kmswDartFarEndpoint] using hwest
      have hchain : List.IsChain (neighborLinkStep w v) (head :: rest) := by
        rw [List.isChain_iff_getElem]
        intro i hi
        let d := (kmswInfRot w hfin ^ i) d₀
        let e := (kmswInfRot w hfin ^ (i + 1)) d₀
        have hformNeighbors : head :: rest = List.ofFn
            (fun j : Fin ((kmsw_darts_at_vertex_finite w hfin v).toFinset.card) =>
              far ((kmswInfRot w hfin ^ j.val) d₀)) := by
          change List.map far (d₀ :: tail) = _
          rw [hform, List.map_ofFn]
          rfl
        have hi' : i + 1 <
            (kmsw_darts_at_vertex_finite w hfin v).toFinset.card := by
          simpa [hformNeighbors] using hi
        have hgetD : (head :: rest)[i] = far d := by
          simp [hformNeighbors, d]
        have hgetE : (head :: rest)[i + 1] = far e := by
          simp [hformNeighbors, e]
        have hrot : kmswInfRot w hfin d = e := by
          dsimp [d, e]
          exact (congrArg (fun τ : Equiv.Perm (ℕ × Bool) => τ d₀)
            (pow_succ' (kmswInfRot w hfin) i)).symm
        have hdEq := (kmswInfRot_exists_pow_iff_endpoint w hfin d₀ d).1
          ⟨i, by rfl⟩
        have heEq := (kmswInfRot_exists_pow_iff_endpoint w hfin d₀ e).1
          ⟨i + 1, by rfl⟩
        have hd : kmswDartEndpoint w d = v := by
          exact hdEq.symm.trans hd₀
        have he : kmswDartEndpoint w e = v := by
          exact heEq.symm.trans hd₀
        have hflip : kmswDartFlip (e.1, !e.2) = e := by
          cases e with
          | mk edge b => cases b <;> rfl
        have hcornerVertex :
            kmswDartEndpoint w (kmswDartFlip (e.1, !e.2)) = v := by
          rw [hflip]
          exact he
        have hleft : ∀ j, (e.1, !e.2) ≠
            (kmswLeftBoundaryEdge w j, false) := by
          intro j hj
          by_cases hbd : OnLeftBoundary w v ∨ OnRightBoundary w v
          · obtain ⟨k, hk, hstartEq⟩ := hstart hbd
            obtain ⟨k', hk', hcorner⟩ := kmsw_boundary_corner_classify
              w hR hL0 hv0 (Or.inl ⟨j, hj⟩) hcornerVertex
            have hkey := kmswOuterCorner_vertex_injective w htrans hR hL0 v
              hv0 hnotboth (some k) (some k') hk hk'
            have hkeyEq : k = k' := Option.some.inj hkey
            have hcornerEq : kmswOuterCornerDart w k = (e.1, !e.2) := by
              rw [hkeyEq]
              exact hcorner
            have hlastEq : kmswDartFlip (e.1, !e.2) = d₀ := by
              rw [← hcornerEq]
              exact hstartEq.symm
            have heq : e = d₀ := hflip.symm.trans hlastEq
            have hS := kmsw_darts_at_vertex_finite w hfin v
            let hs := hS.toFinset
            have hr : d₀ ∈ hs := by
              change d₀ ∈ hS.toFinset
              rw [Set.Finite.mem_toFinset]
              exact hd₀
            have hcycle : (kmswInfRot w hfin).IsCycleOn (hs : Set (ℕ × Bool)) := by
              change (kmswInfRot w hfin).IsCycleOn
                (hS.toFinset : Set (ℕ × Bool))
              simpa only [Set.Finite.coe_toFinset] using
                kmswInfRot_isCycleOn_vertex w hfin v
            have hcard : 0 < hs.card := Finset.card_pos.mpr ⟨d₀, hr⟩
            have hiCard : i + 1 < hs.card := by
              change i + 1 < hS.toFinset.card
              exact hi'
            have hidx := hcycle.injOn_pow_apply hr hiCard hcard (by
              simpa [d, e] using heq)
            omega
          · have hleftV : OnLeftBoundary w v := by
              refine ⟨kmswLeftBoundaryEdge w j,
                (isLeftBoundaryEdge_iff w htrans _).2 ⟨j, rfl⟩, Or.inr ?_⟩
              have hcv := hcornerVertex
              rw [hj] at hcv
              simpa [kmswDartEndpoint, kmswDartFlip] using hcv
            exact (hbd (Or.inl hleftV)).elim
        have hright : ∀ j, (e.1, !e.2) ≠
            (kmswRightBoundaryEdge w j, true) := by
          intro j hj
          by_cases hbd : OnLeftBoundary w v ∨ OnRightBoundary w v
          · obtain ⟨k, hk, hstartEq⟩ := hstart hbd
            obtain ⟨k', hk', hcorner⟩ := kmsw_boundary_corner_classify
              w hR hL0 hv0 (Or.inr ⟨j, hj⟩) hcornerVertex
            have hkey := kmswOuterCorner_vertex_injective w htrans hR hL0 v
              hv0 hnotboth (some k) (some k') hk hk'
            have hkeyEq : k = k' := Option.some.inj hkey
            have hcornerEq : kmswOuterCornerDart w k = (e.1, !e.2) := by
              rw [hkeyEq]
              exact hcorner
            have hlastEq : kmswDartFlip (e.1, !e.2) = d₀ := by
              rw [← hcornerEq]
              exact hstartEq.symm
            have heq : e = d₀ := hflip.symm.trans hlastEq
            have hS := kmsw_darts_at_vertex_finite w hfin v
            let hs := hS.toFinset
            have hr : d₀ ∈ hs := by
              change d₀ ∈ hS.toFinset
              rw [Set.Finite.mem_toFinset]
              exact hd₀
            have hcycle : (kmswInfRot w hfin).IsCycleOn (hs : Set (ℕ × Bool)) := by
              change (kmswInfRot w hfin).IsCycleOn
                (hS.toFinset : Set (ℕ × Bool))
              simpa only [Set.Finite.coe_toFinset] using
                kmswInfRot_isCycleOn_vertex w hfin v
            have hcard : 0 < hs.card := Finset.card_pos.mpr ⟨d₀, hr⟩
            have hiCard : i + 1 < hs.card := by
              change i + 1 < hS.toFinset.card
              exact hi'
            have hidx := hcycle.injOn_pow_apply hr hiCard hcard (by
              simpa [d, e] using heq)
            omega
          · have hrightV : OnRightBoundary w v := by
              refine ⟨kmswRightBoundaryEdge w j,
                (isRightBoundaryEdge_iff w hR _).2 ⟨j, rfl⟩, Or.inl ?_⟩
              have hcv := hcornerVertex
              rw [hj] at hcv
              simpa [kmswDartEndpoint, kmswDartFlip] using hcv
            exact (hbd (Or.inr hrightV)).elim
        have hlink := kmsw_neighborLinkStep_of_rotated_darts w hfin
          htrans hR hL0 v d e hd he hrot hleft hright
        simpa [hgetD, hgetE] using hlink
      exact kmswNeighbors_connected_of_link_chain w v head rest hcover hchain hu hu'

private def kmswUndirectedAdj (w : ℕ → Fin 3) (x y : ℕ) : Prop :=
  ∃ e, EdgePresent w e ∧ UndirectedEdgeStep w x e y

private theorem kmswUndirectedAdj_symm (w : ℕ → Fin 3) {x y : ℕ}
    (h : kmswUndirectedAdj w x y) : kmswUndirectedAdj w y x := by
  obtain ⟨e, hp, hstep⟩ := h
  rcases hstep with hstep | hstep
  · exact ⟨e, hp, Or.inr ⟨hstep.2, hstep.1⟩⟩
  · exact ⟨e, hp, Or.inl ⟨hstep.2, hstep.1⟩⟩

private theorem kmswUndirectedAdj_no_loop (w : ℕ → Fin 3) {x : ℕ}
    (h : kmswUndirectedAdj w x x) : False := by
  obtain ⟨e, _, hstep⟩ := h
  rcases hstep with hstep | hstep
  · exact kmsw_edgeWest_ne_edgeEast w e (hstep.1.trans hstep.2.symm)
  · exact kmsw_edgeWest_ne_edgeEast w e (hstep.2.trans hstep.1.symm)

private theorem kmswUndirectedAdj_to_link (w : ℕ → Fin 3) (v x y : ℕ)
    (hx : x ≠ v) (hy : y ≠ v) (h : kmswUndirectedAdj w x y) :
    neighborLinkStep w v x y := by
  obtain ⟨e, hp, hstep⟩ := h
  exact ⟨e, hp, hstep, hx, hy⟩

private theorem kmsw_finitePath_to_linkReach (w : ℕ → Fin 3) (v : ℕ)
    {x y : ℕ} (p : FiniteUndirectedEdgePath w x y)
    (hAvoid : ∀ z ∈ p.vertices, z ≠ v)
    (hPresent : ∀ e ∈ p.edgeIds, EdgePresent w e) :
    Relation.ReflTransGen (neighborLinkStep w v) x y := by
  revert hAvoid hPresent
  induction p with
  | nil z =>
      intro hAvoid hPresent
      exact .refl
  | @cons a b c e hstep tail ih =>
      intro hAvoid hPresent
      have ha : a ≠ v := hAvoid a (by simp [FiniteUndirectedEdgePath.vertices])
      have hb : b ≠ v := by
        have hbmem : b ∈ tail.vertices := by
          induction tail with
          | nil z => simp [FiniteUndirectedEdgePath.vertices]
          | cons e' hstep' tail' ih' => simp [FiniteUndirectedEdgePath.vertices]
        exact hAvoid b (by simp [FiniteUndirectedEdgePath.vertices, hbmem])
      have he : EdgePresent w e := hPresent e (by simp [FiniteUndirectedEdgePath.edgeIds])
      have htailAvoid : ∀ z ∈ tail.vertices, z ≠ v := by
        intro z hz
        exact hAvoid z (by simp [FiniteUndirectedEdgePath.vertices, hz])
      have htailPresent : ∀ f ∈ tail.edgeIds, EdgePresent w f := by
        intro f hf
        exact hPresent f (by simp [FiniteUndirectedEdgePath.edgeIds, hf])
      exact .head ⟨e, he, hstep, ha, hb⟩ (ih htailAvoid htailPresent)

private theorem kmsw_adjacent_across_vertex_reaches (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v x y : ℕ} (hv : v ≠ 0)
    (hnotboth : ¬ (OnLeftBoundary w v ∧ OnRightBoundary w v))
    (hx : x ≠ v) (hy : y ≠ v)
    (hxv : kmswUndirectedAdj w x v) (hvy : kmswUndirectedAdj w v y) :
    Relation.ReflTransGen (neighborLinkStep w v) x y := by
  have hnx : PresentUndirectedNeighbor w v x := by
    obtain ⟨e, hp, hstep⟩ := kmswUndirectedAdj_symm w hxv
    exact ⟨hx, e, hp, hstep⟩
  have hny : PresentUndirectedNeighbor w v y := ⟨hy, hvy⟩
  obtain ⟨p, hpAvoid, hpresent⟩ := kmsw_nonzero_neighbors_connected
    w hfin htrans hR hL0 hv hnotboth hnx hny
  exact kmsw_finitePath_to_linkReach w v p hpAvoid hpresent

private theorem kmsw_chain_head_reaches_nonV (w : ℕ → Fin 3) (v : ℕ)
    (hbridge : ∀ {x y : ℕ}, x ≠ v → y ≠ v →
      kmswUndirectedAdj w x v → kmswUndirectedAdj w v y →
      Relation.ReflTransGen (neighborLinkStep w v) x y)
    (xs : List ℕ) (hne : xs ≠ [])
    (hchain : List.IsChain (kmswUndirectedAdj w) xs) :
    ∀ {head : ℕ}, xs.head? = some head → head ≠ v →
      ∀ {b : ℕ}, b ∈ xs → b ≠ v →
      Relation.ReflTransGen (neighborLinkStep w v) head b := by
  induction xs using List.twoStepInduction with
  | nil => simp at hne
  | singleton head =>
      intro head' hhead hh b hb hbv
      simp only [List.head?_singleton, Option.some.injEq] at hhead
      subst head'
      have : b = head := by simpa using hb
      subst b
      exact .refl
  | cons_cons head next tail ihTail ihNext =>
      intro head' hhead hh b hb hbv
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst head'
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact .refl
      · have hfirst : kmswUndirectedAdj w head next :=
          hchain.rel_head? (y := next) (by simp)
        by_cases hnext : next = v
        · rcases List.mem_cons.mp hb' with hbeq | hbtail
          · subst b
            exact (hbv hnext).elim
          · cases tail with
            | nil => simp at hbtail
            | cons next2 tail' =>
                have hsecond : kmswUndirectedAdj w next next2 :=
                  hchain.tail.rel_head? (y := next2) (by simp)
                rw [hnext] at hfirst hsecond
                have hnext2 : next2 ≠ v := by
                  intro heq
                  subst next2
                  apply kmswUndirectedAdj_no_loop w
                  exact hsecond
                have hbridge' := hbridge hh hnext2 hfirst hsecond
                have htailReach := ihTail (by simp) hchain.tail.tail rfl
                  hnext2 hbtail hbv
                exact hbridge'.trans htailReach
        · have hstep := kmswUndirectedAdj_to_link w v head next hh hnext hfirst
          have htailReach := ihNext next (by simp) hchain.tail rfl hnext hb' hbv
          exact (Relation.ReflTransGen.single hstep).trans htailReach

private theorem kmsw_neighborLinkStep_symm (w : ℕ → Fin 3) (v x y : ℕ)
    (h : neighborLinkStep w v x y) : neighborLinkStep w v y x := by
  obtain ⟨e, hp, hstep, hx, hy⟩ := h
  rcases hstep with hstep | hstep
  · exact ⟨e, hp, Or.inr ⟨hstep.2, hstep.1⟩, hy, hx⟩
  · exact ⟨e, hp, Or.inl ⟨hstep.2, hstep.1⟩, hy, hx⟩

private theorem kmsw_linkReach_symm (w : ℕ → Fin 3) (v : ℕ)
    {x y : ℕ} (h : Relation.ReflTransGen (neighborLinkStep w v) x y) :
    Relation.ReflTransGen (neighborLinkStep w v) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (kmsw_neighborLinkStep_symm w v _ _ hxy)

private theorem kmsw_path_source_mem_cons_toList {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Quiver.Path a b) :
    a ∈ b :: p.toList := by
  induction p with
  | nil => simp
  | cons p f ih => simp [Quiver.Path.toList, ih]

private theorem kmsw_directedPath_vertexList_chain (w : ℕ → Fin 3)
    {a b : PresentVertex w} (p : Quiver.Path a b) :
    List.IsChain (kmswUndirectedAdj w)
      ((b :: p.toList).map PresentVertex.id) := by
  apply (List.isChain_map PresentVertex.id).2
  apply p.isChain_cons_toList_nonempty.imp
  intro x y hxy
  obtain ⟨q⟩ := hxy
  rcases q with ⟨e, ⟨hp, hwest, heast⟩⟩
  exact ⟨e, hp, Or.inr ⟨heast, hwest⟩⟩

private theorem kmsw_allocated_vertices_link_connected (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v x y : ℕ} (hv : v ≠ 0)
    (hnotboth : ¬ (OnLeftBoundary w v ∧ OnRightBoundary w v))
    (hx : x ≠ v) (hy : y ≠ v)
    (hxalloc : ∃ n, x < (kmswStage w n).nextVertex)
    (hyalloc : ∃ n, y < (kmswStage w n).nextVertex) :
    Relation.ReflTransGen (neighborLinkStep w v) x y := by
  obtain ⟨px⟩ := allocated_vertex_reachable_from_zero w hL0 x hxalloc
  obtain ⟨py⟩ := allocated_vertex_reachable_from_zero w hL0 y hyalloc
  let vx := ((⟨x⟩ : PresentVertex w) :: px.toList).map PresentVertex.id
  let vy := ((⟨y⟩ : PresentVertex w) :: py.toList).map PresentVertex.id
  have hcross : ∀ {a b : ℕ}, a ≠ v → b ≠ v →
      kmswUndirectedAdj w a v → kmswUndirectedAdj w v b →
      Relation.ReflTransGen (neighborLinkStep w v) a b := by
    intro a b ha hb hav hvb
    exact kmsw_adjacent_across_vertex_reaches w hfin htrans hR hL0
      hv hnotboth ha hb hav hvb
  have hpxChain : List.IsChain (kmswUndirectedAdj w) vx := by
    simpa [vx] using kmsw_directedPath_vertexList_chain w px
  have hpxHead : vx.head? = some x := by simp [vx]
  have hpSource : (0 : ℕ) ∈ vx := by
    apply List.mem_map.mpr
    refine ⟨(⟨0⟩ : PresentVertex w), kmsw_path_source_mem_cons_toList px, ?_⟩
    rfl
  have hxToZero : Relation.ReflTransGen (neighborLinkStep w v) x 0 :=
    kmsw_chain_head_reaches_nonV w v hcross vx (by simp [vx]) hpxChain
      hpxHead hx hpSource (Ne.symm hv)
  have hpyChain : List.IsChain (kmswUndirectedAdj w) vy := by
    simpa [vy] using kmsw_directedPath_vertexList_chain w py
  have hpyHead : vy.head? = some y := by simp [vy]
  have hySource : (0 : ℕ) ∈ vy := by
    apply List.mem_map.mpr
    refine ⟨(⟨0⟩ : PresentVertex w), kmsw_path_source_mem_cons_toList py, ?_⟩
    rfl
  have hyToZero : Relation.ReflTransGen (neighborLinkStep w v) y 0 :=
    kmsw_chain_head_reaches_nonV w v hcross vy (by simp [vy]) hpyChain
      hpyHead hy hySource (Ne.symm hv)
  exact hxToZero.trans (kmsw_linkReach_symm w v hyToZero)

private theorem kmsw_finitePath_of_linkReach (w : ℕ → Fin 3) (v : ℕ)
    {x y : ℕ} (hxy : Relation.ReflTransGen (neighborLinkStep w v) x y)
    (hx : x ≠ v) :
    ∃ p : FiniteUndirectedEdgePath w x y,
      (∀ z ∈ p.vertices, z ≠ v) ∧
      ∀ e ∈ p.edgeIds, EdgePresent w e := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨.nil y, by simp [FiniteUndirectedEdgePath.vertices,
        FiniteUndirectedEdgePath.edgeIds, hx]⟩
  | @head a b hab hby ih =>
      obtain ⟨e, hp, hstep, ha, hb⟩ := hab
      obtain ⟨tail, htailAvoid, htailPresent⟩ := ih hb
      refine ⟨.cons e hstep tail, ?_⟩
      constructor
      · intro z hz
        simp only [FiniteUndirectedEdgePath.vertices, Set.mem_union] at hz
        rcases hz with hz | hz
        · subst z
          exact ha
        · exact htailAvoid z hz
      · intro e' he'
        simp only [FiniteUndirectedEdgePath.edgeIds, List.mem_cons] at he'
        rcases he' with he' | he'
        · subst e'
          exact hp
        · exact htailPresent e' he'

/-- If deleting a non-source vertex disconnects the present undirected graph,
then it belongs to both outer boundaries (`def-cut-vertex`, -/
theorem kmsw_removed_disconnected_implies_IsCutVertex (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hv : v ≠ 0)
    (hdisc : ∃ x y, x ≠ v ∧ y ≠ v ∧
      ∀ p : FiniteUndirectedEdgePath w x y, v ∈ p.vertices) :
    IsCutVertex w v := by
  by_contra hcut
  have hnotboth : ¬ (OnLeftBoundary w v ∧ OnRightBoundary w v) := hcut
  obtain ⟨x, y, hx, hy, hpaths⟩ := hdisc
  have hxalloc := kmsw_vertex_allocated_of_finite_incidence w hfin x
  have hyalloc := kmsw_vertex_allocated_of_finite_incidence w hfin y
  have hreach := kmsw_allocated_vertices_link_connected w hfin htrans hR hL0
    hv hnotboth hx hy hxalloc hyalloc
  obtain ⟨p, hpAvoid, _⟩ := kmsw_finitePath_of_linkReach w v hreach hx
  have hvMem : v ∈ p.vertices := hpaths p
  exact (hpAvoid v hvMem) rfl

end DirectedDistances.KMSW
