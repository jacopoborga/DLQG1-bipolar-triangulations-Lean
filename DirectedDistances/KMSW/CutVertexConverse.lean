/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.AllocatedVertices
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.InfiniteTriangulation
import DirectedDistances.KMSW.PathSpaceTransferCarrier

/-! # The source is a map-level cut vertex

The two outer boundary chains both start at the source, so the source belongs
to both orbit boundaries (`def-cut-vertex`, -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open Quiver
open DirectedDistances.RandomWalk

/-- The limiting rotation preserves the geometric endpoint carried by a dart -/
theorem kmswInfRot_endpoint_eq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    (if (kmswInfRot w hfin d).2 then edgeEast w (kmswInfRot w hfin d).1
      else edgeWest w (kmswInfRot w hfin d).1) =
    (if d.2 then edgeEast w d.1 else edgeWest w d.1) := by
  obtain ⟨N, hN⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, hrot⟩ := hN N le_rfl
  let x : StageDart (kmswStage w N).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := stageRot w N x
  have hxy : stageEndpoint (kmswStage w N) y =
      stageEndpoint (kmswStage w N) x :=
    ((stageRot_sameCycle_iff_endpoint_eq w N x y).1 ⟨1, rfl⟩).symm
  have hx : stageEndpoint (kmswStage w N) x =
      (if d.2 then edgeEast w d.1 else edgeWest w d.1) := by
    have he := edge_endpoints_eq w x.1.isLt
    cases hb : d.2 <;> simp [x, stageEndpoint, hb, he.1, he.2]
  have hy : stageEndpoint (kmswStage w N) y =
      (if y.2 then edgeEast w y.1.val else edgeWest w y.1.val) := by
    have he := edge_endpoints_eq w y.1.isLt
    cases hb : y.2 <;> simp [stageEndpoint, hb, he.1, he.2]
  have hrotVal : (kmswInfRot w hfin d).1 = y.1.val := by
    exact congrArg Prod.fst hrot
  have hrotBool : (kmswInfRot w hfin d).2 = y.2 := by
    exact congrArg Prod.snd hrot
  calc
    (if (kmswInfRot w hfin d).2 then edgeEast w (kmswInfRot w hfin d).1
      else edgeWest w (kmswInfRot w hfin d).1) =
        (if y.2 then edgeEast w y.1.val else edgeWest w y.1.val) := by
          rw [hrotVal, hrotBool]
    _ = stageEndpoint (kmswStage w N) y := hy.symm
    _ = stageEndpoint (kmswStage w N) x := hxy
    _ = (if d.2 then edgeEast w d.1 else edgeWest w d.1) := hx

/-- Every allocated geometric edge has distinct west and east endpoints -/
private theorem edgeWest_ne_edgeEast (w : ℕ → Fin 3) (e : ℕ) :
    edgeWest w e ≠ edgeEast w e := by
  have hstrict := kmswStageRank_strict w e e (kmsw_edge_allocated_by_self w e)
  have hend := edge_endpoints_eq w (kmsw_edge_allocated_by_self w e)
  rw [hend.1, hend.2] at hstrict
  intro he
  rw [he] at hstrict
  exact (lt_irrefl _ hstrict)

/-- A non-outer corner between consecutive darts has the third side of its
triangle as a present edge joining the two opposite endpoints. The face cycle
is ordered `flip (rot d)`, `d`, then the third dart (`def-uiqbot`, -/
theorem kmswInfCorner_triangle_edge (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (d : ℕ × Bool) (v : ℕ)
    (hv : (if d.2 then edgeEast w d.1 else edgeWest w d.1) = v)
    (corner : ℕ × Bool)
    (hcorner : corner = ((kmswInfRot w hfin d).1,
      !(kmswInfRot w hfin d).2))
    (hleft : ∀ i, corner ≠ (kmswLeftBoundaryEdge w i, false))
    (hright : ∀ i, corner ≠ (kmswRightBoundaryEdge w i, true)) :
    ∃ c : ℕ × Bool,
      FaceSucc3Cycle (kmswInfFaceSucc w hfin) corner d c ∧
      EdgePresent w c.1 ∧
      UndirectedEdgeStep w
        (if d.2 then edgeWest w d.1 else edgeEast w d.1) c.1
        (if (kmswInfRot w hfin d).2 then
          edgeWest w (kmswInfRot w hfin d).1
          else edgeEast w (kmswInfRot w hfin d).1) ∧
      edgeWest w c.1 ≠ v ∧ edgeEast w c.1 ≠ v := by
  let r := kmswInfRot w hfin d
  let f := kmswInfFaceSucc w hfin
  have hfc : f corner = d := by
    change (kmswInfRot w hfin).symm (corner.1, !corner.2) = d
    rw [hcorner]
    simp
  have htri := kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL0 corner hleft hright
  obtain ⟨j, ⟨hmem, hcycle⟩, _⟩ := htri
  let t := stageTriangleDartTriple w j
  have hmem' : corner = t.1 ∨ corner = t.2.1 ∨ corner = t.2.2 := by
    simpa [stageTriangleDartList, t] using hmem
  rcases hcycle with ⟨h12, h23, h31, hne12, hne23, hne31⟩
  have hfacecycle : ∃ c : ℕ × Bool, FaceSucc3Cycle f corner d c := by
    rcases hmem' with h1 | h2 | h3
    · have hd : d = t.2.1 := by
        calc
          d = f corner := hfc.symm
          _ = f t.1 := by rw [h1]
          _ = t.2.1 := h12
      refine ⟨t.2.2, ?_⟩
      rw [h1, hd]
      exact ⟨h12, h23, h31, hne12, hne23, hne31⟩
    · have hd : d = t.2.2 := by
        calc
          d = f corner := hfc.symm
          _ = f t.2.1 := by rw [h2]
          _ = t.2.2 := h23
      refine ⟨t.1, ?_⟩
      rw [h2, hd]
      exact ⟨h23, h31, h12, hne23, hne31, hne12⟩
    · have hd : d = t.1 := by
        calc
          d = f corner := hfc.symm
          _ = f t.2.2 := by rw [h3]
          _ = t.1 := h31
      refine ⟨t.2.1, ?_⟩
      rw [h3, hd]
      exact ⟨h31, h12, h23, hne31, hne12, hne23⟩
  obtain ⟨c, hcyc⟩ := hfacecycle
  have hcyc' : FaceSucc3Cycle (kmswInfFaceSucc w hfin) corner d c := by
    simpa [f] using hcyc
  rcases hcyc with ⟨hfd, hdc, hcf, _, _, _⟩
  have hdc' : (kmswInfRot w hfin).symm (d.1, !d.2) = c := by
    change f d = c at hdc
    exact hdc
  have hRotC : kmswInfRot w hfin c = (d.1, !d.2) := by
    have hh := congrArg (kmswInfRot w hfin) hdc'.symm
    simpa using hh
  have hcf' : (kmswInfRot w hfin).symm (c.1, !c.2) = corner := by
    change f c = corner at hcf
    exact hcf
  have hRotCorner : kmswInfRot w hfin corner = (c.1, !c.2) := by
    have hh := congrArg (kmswInfRot w hfin) hcf'.symm
    simpa using hh
  have hheadC : (if c.2 then edgeEast w c.1 else edgeWest w c.1) =
      (if d.2 then edgeWest w d.1 else edgeEast w d.1) := by
    have hc := (kmswInfRot_endpoint_eq w hfin c).symm
    have hfirst : (kmswInfRot w hfin c).1 = d.1 := by
      rw [hRotC]
    have hsecond : (kmswInfRot w hfin c).2 = !d.2 := by
      rw [hRotC]
    calc
      (if c.2 then edgeEast w c.1 else edgeWest w c.1) =
          (if (kmswInfRot w hfin c).2 then edgeEast w (kmswInfRot w hfin c).1
            else edgeWest w (kmswInfRot w hfin c).1) := hc
      _ = (if !d.2 then edgeEast w d.1 else edgeWest w d.1) := by
        rw [hfirst, hsecond]
      _ = (if d.2 then edgeWest w d.1 else edgeEast w d.1) := by
        cases d.2 <;> rfl
  have htailC : (if c.2 then edgeWest w c.1 else edgeEast w c.1) =
      (if r.2 then edgeWest w r.1 else edgeEast w r.1) := by
    have hc := kmswInfRot_endpoint_eq w hfin corner
    have hfirst : (kmswInfRot w hfin corner).1 = c.1 := by
      rw [hRotCorner]
    have hsecond : (kmswInfRot w hfin corner).2 = !c.2 := by
      rw [hRotCorner]
    calc
      (if c.2 then edgeWest w c.1 else edgeEast w c.1) =
          (if (kmswInfRot w hfin corner).2 then
            edgeEast w (kmswInfRot w hfin corner).1
            else edgeWest w (kmswInfRot w hfin corner).1) := by
              rw [hfirst, hsecond]
              cases c.2 <;> rfl
      _ = (if corner.2 then edgeEast w corner.1 else edgeWest w corner.1) := hc
      _ = (if r.2 then edgeWest w r.1 else edgeEast w r.1) := by
        rw [hcorner]
        cases r.2 <;> rfl
  have hheadR : (if r.2 then edgeEast w r.1 else edgeWest w r.1) = v := by
    calc
      _ = (if d.2 then edgeEast w d.1 else edgeWest w d.1) :=
        kmswInfRot_endpoint_eq w hfin d
      _ = v := hv
  have hfarD : (if d.2 then edgeWest w d.1 else edgeEast w d.1) ≠ v := by
    have hne : (if d.2 then edgeWest w d.1 else edgeEast w d.1) ≠
        (if d.2 then edgeEast w d.1 else edgeWest w d.1) := by
      cases hb : d.2
      · exact (edgeWest_ne_edgeEast w d.1).symm
      · exact edgeWest_ne_edgeEast w d.1
    intro h
    apply hne
    exact h.trans hv.symm
  have hfarR : (if r.2 then edgeWest w r.1 else edgeEast w r.1) ≠ v := by
    have hne : (if r.2 then edgeWest w r.1 else edgeEast w r.1) ≠
        (if r.2 then edgeEast w r.1 else edgeWest w r.1) := by
      cases hb : r.2
      · exact (edgeWest_ne_edgeEast w r.1).symm
      · exact edgeWest_ne_edgeEast w r.1
    intro h
    apply hne
    exact h.trans hheadR.symm
  have hwest : edgeWest w c.1 ≠ v := by
    cases hc : c.2
    · rw [show edgeWest w c.1 =
          (if d.2 then edgeWest w d.1 else edgeEast w d.1) from by
            simpa [hc] using hheadC]
      exact hfarD
    · rw [show edgeWest w c.1 =
          (if r.2 then edgeWest w r.1 else edgeEast w r.1) from by
            simpa [hc] using htailC]
      exact hfarR
  have heast : edgeEast w c.1 ≠ v := by
    cases hc : c.2
    · rw [show edgeEast w c.1 =
          (if r.2 then edgeWest w r.1 else edgeEast w r.1) from by
            simpa [hc] using htailC]
      exact hfarR
    · rw [show edgeEast w c.1 =
          (if d.2 then edgeWest w d.1 else edgeEast w d.1) from by
            simpa [hc] using hheadC]
      exact hfarD
  have hstep : UndirectedEdgeStep w
      (if d.2 then edgeWest w d.1 else edgeEast w d.1) c.1
      (if r.2 then edgeWest w r.1 else edgeEast w r.1) := by
    cases hc : c.2
    · apply Or.inl
      exact ⟨by simpa [hc] using hheadC, by simpa [hc] using htailC⟩
    · apply Or.inr
      exact ⟨by simpa [hc] using hheadC, by simpa [hc] using htailC⟩
  have hpresent : EdgePresent w c.1 := by
    obtain ⟨N, hN⟩ := eventually_present_of_nonneg_of_unbounded w hL0 hR c.1
    exact ⟨N, (hN N le_rfl).1, (hN N le_rfl).2⟩
  exact ⟨c, hcyc', hpresent, hstep, hwest, heast⟩

private def boundarySeqPath (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i : ℕ) : (k : ℕ) →
      Path (⟨edgeWest w (e i)⟩ : PresentVertex w)
        ⟨edgeEast w (e (i + k))⟩
  | 0 => Hom.toPath (⟨e i, hp i, rfl, rfl⟩ :
      (⟨edgeWest w (e i)⟩ : PresentVertex w) ⟶ ⟨edgeEast w (e i)⟩)
  | k + 1 => by
      simpa only [Nat.add_succ] using
        (congrArg (fun x => (⟨x⟩ : PresentVertex w)) (hpath (i + k)) ▸
          boundarySeqPath w e hp hpath i k).cons
          (⟨e (i + k + 1), hp (i + k + 1), rfl, rfl⟩)

private def boundaryPathCast {V : Type} [Quiver V] {a b c d : V}
    (hs : a = c) (ht : b = d) (p : Path a b) : Path c d :=
  Eq.ndrec (motive := fun c' => Path c' d)
    (Eq.ndrec (motive := fun d' => Path a d') p ht) hs

private theorem boundaryPathCast_length {V : Type} [Quiver V] {a b c d : V}
    (hs : a = c) (ht : b = d) (p : Path a b) :
    (boundaryPathCast hs ht p).length = p.length := by
  cases hs
  cases ht
  rfl

private theorem boundarySeqPath_pos (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    (i k : ℕ) : 0 < (boundarySeqPath w e hp hpath i k).length := by
  induction k with
  | zero => simp [boundarySeqPath, Path.length_toPath]
  | succ k ih =>
      change 0 < ((congrArg (fun x => (⟨x⟩ : PresentVertex w))
        (hpath (i + k)) ▸ boundarySeqPath w e hp hpath i k).cons _).length
      rw [Path.length_cons]
      omega

private theorem boundarySeqPath_no_repeat (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1)))
    {i j : ℕ} (hij : i < j)
    (heq : edgeEast w (e i) = edgeEast w (e j)) : False := by
  let k := j - (i + 1)
  have hsum : i + 1 + k = j := by dsimp [k]; omega
  let p := boundarySeqPath w e hp hpath (i + 1) k
  have hs : (⟨edgeWest w (e (i + 1))⟩ : PresentVertex w) =
      ⟨edgeEast w (e i)⟩ := by
    apply congrArg (fun x => (⟨x⟩ : PresentVertex w))
    exact (hpath i).symm
  have ht : (⟨edgeEast w (e (i + 1 + k))⟩ : PresentVertex w) =
      ⟨edgeEast w (e i)⟩ := by
    apply congrArg (fun x => (⟨x⟩ : PresentVertex w))
    rw [hsum]
    exact heq.symm
  let loop := boundaryPathCast hs ht p
  have hzero := presentVertex_acyclic w _ loop
  have hpos : 0 < p.length := by
    simpa [p] using boundarySeqPath_pos w e hp hpath (i + 1) k
  rw [boundaryPathCast_length hs ht p] at hzero
  omega

private theorem boundaryTerminal_injective (w : ℕ → Fin 3) (e : ℕ → ℕ)
    (hp : ∀ i, EdgePresent w (e i))
    (hpath : ∀ i, edgeEast w (e i) = edgeWest w (e (i + 1))) :
    Function.Injective (fun i => edgeEast w (e i)) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (boundarySeqPath_no_repeat w e hp hpath hij heq).elim
  · exact (boundarySeqPath_no_repeat w e hp hpath hji heq.symm).elim

/-- The non-root corners of the outer face are indexed along the two boundary
chains; `none` records their root junction (`def-uiqbot`, -/
@[expose] noncomputable def kmswOuterCornerVertex (w : ℕ → Fin 3) :
    Option (Bool × ℕ) → ℕ
  | none => 0
  | some (right, i) =>
      if right then edgeEast w (kmswRightBoundaryEdge w i)
      else edgeEast w (kmswLeftBoundaryEdge w i)

/-- Away from the root, the outer face visits a vertex in at most one corner
unless the vertex lies on both boundary chains. The chain vertex sequences are
injective because they are directed paths in the acyclic present graph -/
theorem kmswOuterCorner_vertex_injective (w : ℕ → Fin 3)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) (hv0 : v ≠ 0)
    (hnotboth : ¬ (OnLeftBoundary w v ∧ OnRightBoundary w v))
    (c₁ c₂ : Option (Bool × ℕ))
    (hc₁ : kmswOuterCornerVertex w c₁ = v)
    (hc₂ : kmswOuterCornerVertex w c₂ = v) : c₁ = c₂ := by
  obtain ⟨_, hleftStep, _, hleftPresent⟩ :=
    kmswLeftBoundary_infinite_present_path w htrans hL0 hR
  obtain ⟨_, hrightStep, _, hrightPresent⟩ :=
    kmswRightBoundary_infinite_present_path w hL0 hR
  have hleftInjective := boundaryTerminal_injective w
    (kmswLeftBoundaryEdge w) hleftPresent hleftStep
  have hrightInjective := boundaryTerminal_injective w
    (kmswRightBoundaryEdge w) hrightPresent hrightStep
  cases c₁ with
  | none =>
      cases c₂ with
      | none => rfl
      | some c₂ =>
          have hvzero : v = 0 := by simpa [kmswOuterCornerVertex] using hc₁.symm
          exact False.elim (hv0 hvzero)
  | some c₁ =>
      cases c₂ with
      | none =>
          have hvzero : v = 0 := by simpa [kmswOuterCornerVertex] using hc₂.symm
          exact False.elim (hv0 hvzero)
      | some c₂ =>
          have hside : c₁.1 = c₂.1 := by
            by_contra hne
            cases h₁ : c₁.1 <;> cases h₂ : c₂.1
            · exact hne (by rw [h₁, h₂])
            · have hleft : OnLeftBoundary w v := by
                refine ⟨kmswLeftBoundaryEdge w c₁.2,
                  (isLeftBoundaryEdge_iff w htrans _).mpr ⟨c₁.2, rfl⟩,
                  Or.inr ?_⟩
                simpa [kmswOuterCornerVertex, h₁] using hc₁
              have hright : OnRightBoundary w v := by
                refine ⟨kmswRightBoundaryEdge w c₂.2,
                  (isRightBoundaryEdge_iff w hR _).mpr ⟨c₂.2, rfl⟩,
                  Or.inr ?_⟩
                simpa [kmswOuterCornerVertex, h₂] using hc₂
              exact hnotboth ⟨hleft, hright⟩
            · have hright : OnRightBoundary w v := by
                refine ⟨kmswRightBoundaryEdge w c₁.2,
                  (isRightBoundaryEdge_iff w hR _).mpr ⟨c₁.2, rfl⟩,
                  Or.inr ?_⟩
                simpa [kmswOuterCornerVertex, h₁] using hc₁
              have hleft : OnLeftBoundary w v := by
                refine ⟨kmswLeftBoundaryEdge w c₂.2,
                  (isLeftBoundaryEdge_iff w htrans _).mpr ⟨c₂.2, rfl⟩,
                  Or.inr ?_⟩
                simpa [kmswOuterCornerVertex, h₂] using hc₂
              exact hnotboth ⟨hleft, hright⟩
            · exact hne (by rw [h₁, h₂])
          have hindex : c₁.2 = c₂.2 := by
            cases h₁ : c₁.1
            · have hv₁ : edgeEast w (kmswLeftBoundaryEdge w c₁.2) = v := by
                simpa [kmswOuterCornerVertex, h₁] using hc₁
              have h₂ : c₂.1 = false := hside.symm.trans h₁
              have hv₂ : edgeEast w (kmswLeftBoundaryEdge w c₂.2) = v := by
                simpa [kmswOuterCornerVertex, h₂] using hc₂
              exact hleftInjective (hv₁.trans hv₂.symm)
            · have hv₁ : edgeEast w (kmswRightBoundaryEdge w c₁.2) = v := by
                simpa [kmswOuterCornerVertex, h₁] using hc₁
              have h₂ : c₂.1 = true := hside.symm.trans h₁
              have hv₂ : edgeEast w (kmswRightBoundaryEdge w c₂.2) = v := by
                simpa [kmswOuterCornerVertex, h₂] using hc₂
              exact hrightInjective (hv₁.trans hv₂.symm)
          exact congrArg some (Prod.ext hside hindex)

/-- Edge IDs traversed by a finite undirected path, retaining parallel edges -/
@[expose] def FiniteUndirectedEdgePath.edgeIds {w : ℕ → Fin 3} {x y : ℕ} :
    FiniteUndirectedEdgePath w x y → List ℕ
  | .nil _ => []
  | .cons e _ tail => e :: tail.edgeIds

/-- A present neighbor of a vertex in the underlying undirected graph -/
@[expose] def PresentUndirectedNeighbor (w : ℕ → Fin 3) (v u : ℕ) : Prop :=
  u ≠ v ∧ ∃ e, EdgePresent w e ∧ UndirectedEdgeStep w v e u

/-- One step in the neighbor link: a present geometric edge joins two vertices
other than the removed center (`def-cut-vertex`, -/
@[expose] def neighborLinkStep (w : ℕ → Fin 3) (v x y : ℕ) : Prop :=
  ∃ e, EdgePresent w e ∧ UndirectedEdgeStep w x e y ∧ x ≠ v ∧ y ≠ v

private theorem neighborLinkStep_symm (w : ℕ → Fin 3) (v x y : ℕ)
    (h : neighborLinkStep w v x y) : neighborLinkStep w v y x := by
  obtain ⟨e, hp, hstep, hx, hy⟩ := h
  rcases hstep with hstep | hstep
  · exact ⟨e, hp, Or.inr ⟨hstep.2, hstep.1⟩, hy, hx⟩
  · exact ⟨e, hp, Or.inl ⟨hstep.2, hstep.1⟩, hy, hx⟩

private theorem neighborLink_reflTransGen_symm (w : ℕ → Fin 3) (v : ℕ)
    {x y : ℕ} (h : Relation.ReflTransGen (neighborLinkStep w v) x y) :
    Relation.ReflTransGen (neighborLinkStep w v) y x := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.head (neighborLinkStep_symm w v _ _ h)

private theorem finiteUndirectedPath_of_neighborLink (w : ℕ → Fin 3) (v : ℕ)
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

private theorem neighborLinkChain_head_reaches (w : ℕ → Fin 3) (v head : ℕ) :
    ∀ tail, List.IsChain (neighborLinkStep w v) (head :: tail) →
      ∀ u, u ∈ head :: tail →
        Relation.ReflTransGen (neighborLinkStep w v) head u
  | [], _, u, hu => by
      have hu' : u = head := by simpa using hu
      subst u
      exact .refl
  | next :: tail, hchain, u, hu => by
      have hnext : neighborLinkStep w v head next :=
        hchain.rel_head? (y := next) (by simp)
      have htail := hchain.tail
      rcases List.mem_cons.mp hu with rfl | hu
      · exact .refl
      · exact (Relation.ReflTransGen.single hnext).trans
          (neighborLinkChain_head_reaches w v next tail htail u hu)

private theorem neighborLinkChain_between (w : ℕ → Fin 3) (v head : ℕ)
    (tail : List ℕ)
    (hchain : List.IsChain (neighborLinkStep w v) (head :: tail))
    {x y : ℕ} (hx : x ∈ head :: tail) (hy : y ∈ head :: tail) :
    Relation.ReflTransGen (neighborLinkStep w v) x y := by
  have hheadX := neighborLinkChain_head_reaches w v head tail hchain x hx
  have hheadY := neighborLinkChain_head_reaches w v head tail hchain y hy
  exact (neighborLink_reflTransGen_symm w v hheadX).trans hheadY

/-- A certified linear ordering of all present neighbors, with a present
triangle edge across every consecutive pair, connects the neighbors while
avoiding the center vertex. This is the finite-list core of link connectivity -/
theorem kmswNeighbors_connected_of_link_chain (w : ℕ → Fin 3) (v head : ℕ)
    (tail : List ℕ)
    (hcover : ∀ u, u ∈ head :: tail ↔ PresentUndirectedNeighbor w v u)
    (hchain : List.IsChain (neighborLinkStep w v) (head :: tail))
    {u u' : ℕ} (hu : PresentUndirectedNeighbor w v u)
    (hu' : PresentUndirectedNeighbor w v u') :
    ∃ p : FiniteUndirectedEdgePath w u u',
      (∀ z ∈ p.vertices, z ≠ v) ∧
      ∀ e ∈ p.edgeIds, EdgePresent w e := by
  have huMem : u ∈ head :: tail := (hcover u).2 hu
  have hu'Mem : u' ∈ head :: tail := (hcover u').2 hu'
  have hreach := neighborLinkChain_between w v head tail hchain huMem hu'Mem
  exact finiteUndirectedPath_of_neighborLink w v hreach hu.1

/-- The source vertex belongs to both outer-face boundary orbits -/
theorem mapCutVertex_source (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (hL0 : ∀ j, 0 ≤ L w j) :
    mapCutVertex w hfin 0 := by
  rw [mapCutVertex_iff w hfin htrans hR hL0]
  obtain ⟨_, _, hleftZero, _⟩ :=
    kmswLeftBoundary_infinite_present_path w htrans hL0 hR
  obtain ⟨_, _, hrightZero, _⟩ :=
    kmswRightBoundary_infinite_present_path w hL0 hR
  constructor
  · exact ⟨kmswLeftBoundaryEdge w 0,
      (isLeftBoundaryEdge_iff w htrans _).mpr ⟨0, rfl⟩,
      Or.inl hleftZero⟩
  · exact ⟨kmswRightBoundaryEdge w 0,
      (isRightBoundaryEdge_iff w hR _).mpr ⟨0, rfl⟩,
      Or.inl hrightZero⟩

end DirectedDistances.KMSW
