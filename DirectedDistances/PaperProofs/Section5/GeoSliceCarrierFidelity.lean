/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceGeometricCarrier
public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination4
public import DirectedDistances.PaperProofs.Section5.GeoSliceLeftmostNonCrossing5
public import DirectedDistances.PaperProofs.Section5.GeometricSideClass

/-! # Carrier fidelity for the geodesic slice -/

public section
namespace DirectedDistances.PaperProofs.Section5

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hp : BoundaryHitWitnesses (kmswPastCode W)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

private theorem m0CutCodePath_initialId_injective {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    Function.Injective (fun n => ((P.codePath.initial n).1).id) := by
  have hw := infinitePresentPath_west_injective (H.1 0)
    (fun n => ⟨monotoneLayoutDrawing (shiftedStream W 0) n
      ((monotone_family_all (shiftedStream W 0)) n).choose,
      ((monotone_family_all (shiftedStream W 0)) n).choose_spec⟩) P.codePath
  intro i j hij
  apply hw
  calc
    edgeWest (shiftedStream W 0) (P.codePath.edge i) =
        ((P.codePath.initial i).1).id :=
      (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) i).2
    _ = ((P.codePath.initial j).1).id := hij
    _ = edgeWest (shiftedStream W 0) (P.codePath.edge j) :=
      (P.codePath.edge_outgoing_at_initial (shiftedStream W 0) j).2.symm





theorem m0CutGeodesicSlice_boundary_segments_mem
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (T : ∀ k : ℤ, InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (hleft : ∀ k, Xdp.CutLeftmostXdp W H h hp hLL longest k (P k) (T k))
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    (∀ n ≤ a, ((P (k - 1)).codePath.initial n).1.id ∈
        (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices) ∧
    (∀ i < a, (P (k - 1)).codePath.edge i ∈
        (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) ∧
    (∀ n ≤ b, ((P k).codePath.initial n).1.id ∈
        (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices) ∧
    (∀ i < b, (P k).codePath.edge i ∈
        (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) := by
  have hseg := m0CutAdjacentGeodesics_ordered_before_coalescence
    P T hleft k a b hab
  have hcoShift (t : ℕ) :
      M0CutEdgeTailsCoalesce (P (k - 1)) (P k) (a + t) (b + t) := by
    intro j
    simpa [Nat.add_assoc] using hab.1 (t + j)
  have hvertexShift (t : ℕ) :
      ((P (k - 1)).codePath.initial (a + t)).1 =
        ((P k).codePath.initial (b + t)).1 :=
    m0Cut_initial_vertex_eq_of_edge_tails_coalesce
      (P (k - 1)) (P k) (hcoShift t)
  have hvleft : ∀ n ≤ a,
      ((P (k - 1)).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P k) .left := by
    intro n hn
    cases n with
    | zero =>
        rw [m0Geodesic_initial_zero (P (k - 1))]
        exact m0Cut_previous_boundary_mem_left_side (P k)
    | succ n =>
        have hEdge := hseg.1 n (by omega)
        have hEnd := (m0GeodesicSide_endpoints hp (P k) .left
          ((P (k - 1)).codePath.edge n) hEdge).2
        change edgeEast (shiftedStream W 0) ((P (k - 1)).codePath.edge n) ∈
          m0GeodesicSideVertices hp (P k) .left at hEnd
        rw [((P (k - 1)).codePath.edge_incoming_at_succ
          (shiftedStream W 0) n).2] at hEnd
        exact hEnd
  have hvright : ∀ n ≤ b,
      ((P k).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P (k - 1)) .right := by
    intro n hn
    cases n with
    | zero =>
        rw [m0Geodesic_initial_zero (P k)]
        exact m0Cut_next_boundary_mem_right_side (P (k - 1))
    | succ n =>
        have hEdge := hseg.2 n (by omega)
        have hEnd := (m0GeodesicSide_endpoints hp (P (k - 1)) .right
          ((P k).codePath.edge n) hEdge).2
        change edgeEast (shiftedStream W 0) ((P k).codePath.edge n) ∈
          m0GeodesicSideVertices hp (P (k - 1)) .right at hEnd
        rw [((P k).codePath.edge_incoming_at_succ
          (shiftedStream W 0) n).2] at hEnd
        exact hEnd
  have hprefixV₁ : ∀ n ≤ a,
      ((P (k - 1)).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P (k - 1)) .right ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P (k - 1)) .left := by
    intro n hn
    have hv : ((P (k - 1)).codePath.initial n).1.id ∈
        m0GeodesicVertices (P (k - 1)) := ⟨n, rfl⟩
    rw [← m0GeodesicSideVertices_inter hp (P (k - 1))] at hv
    exact ⟨hv.2, hv.1⟩
  have hprefixV₂ : ∀ n ≤ b,
      ((P k).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P k) .left ∧
      ((P k).codePath.initial n).1.id ∈
        m0GeodesicSideVertices hp (P k) .right := by
    intro n hn
    have hv : ((P k).codePath.initial n).1.id ∈ m0GeodesicVertices (P k) :=
      ⟨n, rfl⟩
    rw [← m0GeodesicSideVertices_inter hp (P k)] at hv
    exact hv
  have htailV₁ : ∀ n ≤ a,
      ((P (k - 1)).codePath.initial n).1.id ∉
        ({v | ∃ m, a < m ∧ v = ((P (k - 1)).codePath.initial m).1.id} ∪
          {v | ∃ m, b < m ∧ v = ((P k).codePath.initial m).1.id}) := by
    intro n hn
    rintro (⟨m, hnm, hEq⟩ | ⟨m, hbm, hEq⟩)
    · have hinj := m0CutCodePath_initialId_injective (P (k - 1))
      have := hinj hEq
      omega
    · have htailMeet := hvertexShift (m - b)
      have hidx : b + (m - b) = m := by omega
      have hEq' : ((P (k - 1)).codePath.initial n).1.id =
          ((P (k - 1)).codePath.initial (a + (m - b))).1.id := by
        rw [hidx] at htailMeet
        exact hEq.trans (congrArg PresentVertex.id htailMeet).symm
      have hinj := m0CutCodePath_initialId_injective (P (k - 1))
      have hnm' := hinj hEq'
      omega
  have htailV₂ : ∀ n ≤ b,
      ((P k).codePath.initial n).1.id ∉
        ({v | ∃ m, a < m ∧ v = ((P (k - 1)).codePath.initial m).1.id} ∪
          {v | ∃ m, b < m ∧ v = ((P k).codePath.initial m).1.id}) := by
    intro n hn
    rintro (⟨m, ham, hEq⟩ | ⟨m, hnm, hEq⟩)
    · have htailMeet := hvertexShift (m - a)
      have hidx : a + (m - a) = m := by omega
      have hEq' : ((P k).codePath.initial n).1.id =
          ((P k).codePath.initial (b + (m - a))).1.id := by
        rw [hidx] at htailMeet
        exact hEq.trans (congrArg PresentVertex.id htailMeet)
      have hinj := m0CutCodePath_initialId_injective (P k)
      have hnm' := hinj hEq'
      omega
    · have hinj := m0CutCodePath_initialId_injective (P k)
      have := hinj hEq
      omega
  have hedgeTail₁ : ∀ i < a,
      (P (k - 1)).codePath.edge i ∉
        (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
          Set.range (fun n => (P k).codePath.edge (b + n))) := by
    intro i hi
    rintro (hmem | hmem)
    · obtain ⟨n, hn⟩ := Set.mem_range.mp hmem
      have hW := congrArg (wholePlaneEdgeι W 0) hn
      have hinj := m0Cut_geodesic_edge_injective (P (k - 1))
      have hidx := hinj hW
      omega
    · obtain ⟨n, hn⟩ := Set.mem_range.mp hmem
      have hco := hab.1 n
      have hW := hco.trans (congrArg (wholePlaneEdgeι W 0) hn)
      have hinj := m0Cut_geodesic_edge_injective (P (k - 1))
      have hidx := hinj hW
      omega
  have hedgeTail₂ : ∀ i < b,
      (P k).codePath.edge i ∉
        (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
          Set.range (fun n => (P k).codePath.edge (b + n))) := by
    intro i hi
    rintro (hmem | hmem)
    · obtain ⟨n, hn⟩ := Set.mem_range.mp hmem
      have hco := hab.1 n
      have hW := hco.symm.trans (congrArg (wholePlaneEdgeι W 0) hn)
      have hinj := m0Cut_geodesic_edge_injective (P k)
      have hidx := hinj hW
      omega
    · obtain ⟨n, hn⟩ := Set.mem_range.mp hmem
      have hW := congrArg (wholePlaneEdgeι W 0) hn
      have hinj := m0Cut_geodesic_edge_injective (P k)
      have hidx := hinj hW
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    change ((P (k - 1)).codePath.initial n).1.id ∈
      (m0GeodesicSideVertices hp (P (k - 1)) .right ∩
        m0GeodesicSideVertices hp (P k) .left) \
      ({v | ∃ m, a < m ∧ v = ((P (k - 1)).codePath.initial m).1.id} ∪
        {v | ∃ m, b < m ∧ v = ((P k).codePath.initial m).1.id})
    exact ⟨⟨(hprefixV₁ n hn).1, hvleft n hn⟩, htailV₁ n hn⟩
  · intro i hi
    change (P (k - 1)).codePath.edge i ∈
      (m0GeodesicSideEdges hp (P (k - 1)) .right ∩
        m0GeodesicSideEdges hp (P k) .left) \
      (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n)))
    have hown := (m0GeodesicEdges_subset_both hp (P (k - 1)) ⟨i, rfl⟩).2
    exact ⟨⟨hown, hseg.1 i hi⟩, hedgeTail₁ i hi⟩
  · intro n hn
    change ((P k).codePath.initial n).1.id ∈
      (m0GeodesicSideVertices hp (P (k - 1)) .right ∩
        m0GeodesicSideVertices hp (P k) .left) \
      ({v | ∃ m, a < m ∧ v = ((P (k - 1)).codePath.initial m).1.id} ∪
        {v | ∃ m, b < m ∧ v = ((P k).codePath.initial m).1.id})
    exact ⟨⟨hvright n hn, (hprefixV₂ n hn).1⟩, htailV₂ n hn⟩
  · intro i hi
    change (P k).codePath.edge i ∈
      (m0GeodesicSideEdges hp (P (k - 1)) .right ∩
        m0GeodesicSideEdges hp (P k) .left) \
      (Set.range (fun n => (P (k - 1)).codePath.edge (a + n)) ∪
        Set.range (fun n => (P k).codePath.edge (b + n)))
    have hown := (m0GeodesicEdges_subset_both hp (P k) ⟨i, rfl⟩).1
    exact ⟨⟨hseg.2 i hi, hown⟩, hedgeTail₂ i hi⟩




theorem m0CutGeodesicSlice_common_tails_not_mem
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    (∀ n, a < n → ((P (k - 1)).codePath.initial n).1.id ∉
      (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices) ∧
    (∀ n, b < n → ((P k).codePath.initial n).1.id ∉
      (m0CutGeodesicSlice (hp := hp) P k a b hab).vertices) ∧
    (∀ i, a ≤ i → (P (k - 1)).codePath.edge i ∉
      (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) ∧
    (∀ i, b ≤ i → (P k).codePath.edge i ∉
      (m0CutGeodesicSlice (hp := hp) P k a b hab).edges) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn hmem
    have hcarrier := (m0CutGeodesicSlice_mem_vertices_iff
      (hp := hp) P k a b hab ((P (k - 1)).codePath.initial n).1.id).mp hmem
    exact hcarrier.2 (Or.inl ⟨n, hn, rfl⟩)
  · intro n hn hmem
    have hcarrier := (m0CutGeodesicSlice_mem_vertices_iff
      (hp := hp) P k a b hab ((P k).codePath.initial n).1.id).mp hmem
    exact hcarrier.2 (Or.inr ⟨n, hn, rfl⟩)
  · intro i hi hmem
    have hcarrier := (m0CutGeodesicSlice_mem_edges_iff
      (hp := hp) P k a b hab ((P (k - 1)).codePath.edge i)).mp hmem
    refine hcarrier.2 (Or.inl ⟨i - a, ?_⟩)
    change (P (k - 1)).codePath.edge (a + (i - a)) =
      (P (k - 1)).codePath.edge i
    rw [Nat.add_sub_of_le hi]
  · intro i hi hmem
    have hcarrier := (m0CutGeodesicSlice_mem_edges_iff
      (hp := hp) P k a b hab ((P k).codePath.edge i)).mp hmem
    refine hcarrier.2 (Or.inr ⟨i - b, ?_⟩)
    change (P k).codePath.edge (b + (i - b)) = (P k).codePath.edge i
    rw [Nat.add_sub_of_le hi]




theorem m0CutGeodesicSlice_root_eq_previous_boundary
    {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest)
    (k : ℤ) (a b : ℕ)
    (hab : M0CutLeastEdgeCoalescence (P (k - 1)) (P k) a b) :
    (m0CutGeodesicSlice (hp := hp) P k a b hab).root =
      boundaryVertex (shiftedStream W 0) h (k - 1) := rfl

/-- Helper toward Lemma 5.6: the relation carrying a geometric submap without
its choice of root and without the formal indexed segment marks. The retained
structural relations are precisely the directed planar submap relations. -/
@[expose] def m0CutUnrootedRelation (M : GeometricSideSubmap)
    (t : TruncationRelation) (u v : GeometricSideCell M) : Prop :=
  match t with
  | .root | .target | .boundary _ | .seam _ => False
  | _ => geometricSideRelation M t u v

/-- Helper toward Lemma 5.6: isomorphism of the unrooted directed planar
submaps underlying two geometric-side carriers. -/
structure GeometricSideUnrootedIso (M N : GeometricSideSubmap) where
  equiv : GeometricSideCell M ≃ GeometricSideCell N
  relation_iff : ∀ t u v,
    m0CutUnrootedRelation M t u v ↔
      m0CutUnrootedRelation N t (equiv u) (equiv v)

/-- Helper toward Lemma 5.6: a rooted marked isomorphism induces the
corresponding unrooted isomorphism. -/
@[expose] def m0CutMarkedIsoToUnrooted
    {M N : GeometricSideSubmap} (I : GeometricSideMarkedIso M N) :
    GeometricSideUnrootedIso M N where
  equiv := I.equiv
  relation_iff := by
    intro t u v
    cases t with
    | vertex => simpa [m0CutUnrootedRelation] using I.relation_iff .vertex u v
    | root => simp [m0CutUnrootedRelation]
    | target => simp [m0CutUnrootedRelation]
    | incident => simpa [m0CutUnrootedRelation] using I.relation_iff .incident u v
    | opposite => simpa [m0CutUnrootedRelation] using I.relation_iff .opposite u v
    | oriented => simpa [m0CutUnrootedRelation] using I.relation_iff .oriented u v
    | rotation => simpa [m0CutUnrootedRelation] using I.relation_iff .rotation u v
    | faceNext => simpa [m0CutUnrootedRelation] using I.relation_iff .faceNext u v
    | boundary i => simp [m0CutUnrootedRelation]
    | seam i => simp [m0CutUnrootedRelation]

/-- Helper toward Lemma 5.6: the setoid of unrooted directed planar submaps. -/
@[expose] def m0CutUnrootedSetoid : Setoid GeometricSideSubmap where
  r M N := Nonempty (GeometricSideUnrootedIso M N)
  iseqv := ⟨
    fun M => ⟨{
      equiv := Equiv.refl _
      relation_iff := by intro t u v; rfl
    }⟩,
    fun h => h.elim fun I => ⟨{
      equiv := I.equiv.symm
      relation_iff := by
        intro t u v
        simpa using (I.relation_iff t (I.equiv.symm u) (I.equiv.symm v)).symm
    }⟩,
    fun h₁ h₂ => h₁.elim fun I => h₂.elim fun J => ⟨{
      equiv := I.equiv.trans J.equiv
      relation_iff := by
        intro t u v
        exact (I.relation_iff t u v).trans
          (J.relation_iff t (I.equiv u) (I.equiv v))
    }⟩⟩

/-- Helper toward Lemma 5.6: equivalence classes of unrooted directed planar
submaps. -/
@[expose] def GeometricSideUnrootedClass : Type := Quotient m0CutUnrootedSetoid

/-- Helper toward Lemma 5.6: the unrooted class of a geometric carrier. -/
@[expose] def geometricSideUnrootedClass (M : GeometricSideSubmap) :
    GeometricSideUnrootedClass := Quotient.mk m0CutUnrootedSetoid M

/-- Helper toward Lemma 5.6: the measurable structure on unrooted classes is
induced by the class map. -/
noncomputable instance : MeasurableSpace GeometricSideUnrootedClass :=
  MeasurableSpace.map geometricSideUnrootedClass inferInstance

/-- Helper toward Lemma 5.6: forget the root and formal indexed marks from a
rooted marked side class. This makes the source's unrooted class a well-defined
function of the rooted representation. -/
@[expose] def forgetRootAndMarks : GeometricSideClass → GeometricSideUnrootedClass :=
  Quotient.lift geometricSideUnrootedClass (by
    intro M N h
    exact h.elim fun I => Quotient.sound ⟨m0CutMarkedIsoToUnrooted I⟩)

/-- Helper toward Lemma 5.6: equality in law of rooted classes implies
equality in law after applying the unrooting function. -/
theorem map_forgetRootAndMarks_eq_of_rooted_law_eq
    {μ ν : Measure GeometricSideClass} (h : μ = ν) :
    μ.map forgetRootAndMarks = ν.map forgetRootAndMarks := congrArg
      (fun μ : Measure GeometricSideClass => μ.map forgetRootAndMarks) h






























end DirectedDistances.PaperProofs.Section5
