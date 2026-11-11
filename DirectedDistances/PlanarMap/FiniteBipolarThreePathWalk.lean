/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarThreePathRegion
public import DirectedDistances.PlanarMap.FiniteBoundaryDecomposition
public import DirectedDistances.PlanarMap.FiniteXDPGeodesicSplit
public import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft











public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Definition 3.13: concatenating endpoint-labelled geometric
walks requires only agreement at the common endpoint. -/
theorem isBoundaryDartWalk_append_three_path
    (M : DirectedMapWithMissing D) {xs ys : List D} {s t u : MapVertex M}
    (hx : IsBoundaryDartWalk M xs s t) (hy : IsBoundaryDartWalk M ys t u) :
    IsBoundaryDartWalk M (xs ++ ys) s u := by
  induction xs generalizing s with
  | nil =>
      have hst : s = t := hx
      subst s
      exact hy
  | cons d ds ih =>
      exact ⟨hx.1, ih hx.2⟩

/-- Helper toward Definition 3.13: reversing the order and the darts reverses
an endpoint-labelled geometric walk, including the empty walk. -/
theorem isBoundaryDartWalk_reverse_three_path
    (M : DirectedMapWithMissing D) {xs : List D} {s t : MapVertex M}
    (h : IsBoundaryDartWalk M xs s t) :
    IsBoundaryDartWalk M (xs.reverse.map M.edgeInv) t s := by
  induction xs generalizing s with
  | nil => exact Eq.symm h
  | cons d ds ih =>
      simp only [List.reverse_cons, List.map_append, List.map_singleton]
      apply isBoundaryDartWalk_append_three_path M (ih h.2)
      constructor
      · rfl
      · change dartHeadVertex M (M.edgeInv d) = s
        simpa only [dartHeadVertex, dartTailVertex, M.edgeInv_invol] using h.1.symm

/-- Helper toward Definition 3.13: indexed vertex incidences certify a
geometric dart walk without a distinctness or orientation hypothesis. -/
theorem isBoundaryDartWalk_of_indexed_vertices_three_path
    (M : DirectedMapWithMissing D) (xs : List D)
    (v : Fin (xs.length + 1) → MapVertex M)
    (h : ∀ i : Fin xs.length,
      v ⟨i.val, by omega⟩ = dartTailVertex M (xs.get i) ∧
      v ⟨i.val + 1, by omega⟩ = dartHeadVertex M (xs.get i)) :
    IsBoundaryDartWalk M xs (v ⟨0, by omega⟩) (v ⟨xs.length, by omega⟩) := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
      constructor
      · exact (h ⟨0, by simp⟩).1
      · have ht := ih (fun i => v ⟨i.val + 1, by have := i.isLt; simp only [List.length_cons]; omega⟩)
          (fun i => by
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, Nat.add_assoc]
              using h ⟨i.val + 1, by have := i.isLt; simp only [List.length_cons]; omega⟩)
        simpa only [(h ⟨0, by simp⟩).2, List.get_eq_getElem, List.getElem_cons_zero, List.length_cons] using ht


namespace SimpleDirectedDartPath

/-- Helper toward Definition 3.13: the geometric walk underlying a directed
path has its stated endpoints, also for a zero-length path. -/
theorem isBoundaryDartWalk_three_path {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    IsBoundaryDartWalk M P.darts s t := by
  have hw := isBoundaryDartWalk_of_indexed_vertices_three_path M P.darts
    (fun i => P.vertices.get ⟨i.val, by
      have := i.isLt
      rw [P.vertices_length]
      have hdlen := P.darts_length
      omega⟩)
    (fun i => ⟨(P.edge_step i).2.2.1, (P.edge_step i).2.2.2⟩)
  simpa only [P.darts_length, P.start_vertex, P.end_vertex] using hw

/-- Helper toward Definition 3.13: two meeting directed portions and the
reverse of any connector form a closed geometric walk. The meeting need
not be internal or transverse; shared darts are retained. -/
theorem three_path_closed_walk {M : DirectedMapWithMissing D}
    {x y u v : MapVertex M} {a b n : ℕ}
    (O : SimpleDirectedDartPath M x v a)
    (I : SimpleDirectedDartPath M u y b)
    (P : SimpleDirectedDartPath M x y n)
    (i : Fin O.vertices.length) (j : Fin I.vertices.length)
    (hij : O.vertices.get i = I.vertices.get j) :
    IsBoundaryDartWalk M
      (O.darts.take i.val ++ I.darts.drop j.val ++ P.darts.reverse.map M.edgeInv) x x := by
  have ho := (O.prefix ⟨i.val, by rw [← O.vertices_length]; exact i.isLt⟩).isBoundaryDartWalk_three_path
  have hi := (I.suffix ⟨j.val, by rw [← I.vertices_length]; exact j.isLt⟩).isBoundaryDartWalk_three_path
  rw [prefix_darts] at ho
  rw [suffix_darts] at hi
  rw [← hij] at hi
  exact isBoundaryDartWalk_append_three_path M
    (isBoundaryDartWalk_append_three_path M ho hi)
    (isBoundaryDartWalk_reverse_three_path M P.isBoundaryDartWalk_three_path)

end SimpleDirectedDartPath

namespace BipolarMapWithBoundaryBase

variable {ℓ r : ℕ}

/-- Helper toward Definition 3.13: the canonical outgoing and incoming paths
have a unique pair of first meeting indices. Existence uses the given
connector; neither disjointness nor positive lengths are required. -/
theorem exists_unique_threePathFirstMeeting
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    ∃! ij : Fin (B.rightmostOutPath x).2.vertices.length ×
        Fin (B.rightmostInPath y).2.vertices.length,
      (B.rightmostOutPath x).2.vertices.get ij.1 =
          (B.rightmostInPath y).2.vertices.get ij.2 ∧
        (∀ k : Fin (B.rightmostOutPath x).2.vertices.length, k.val < ij.1.val →
          (B.rightmostOutPath x).2.vertices.get k ∉ (B.rightmostInPath y).2.vertices) ∧
        (∀ k : Fin (B.rightmostInPath y).2.vertices.length, k.val < ij.2.val →
          (B.rightmostInPath y).2.vertices.get k ∉ (B.rightmostOutPath x).2.vertices) := by
  exact SimpleDirectedDartPath.exists_unique_first_common_pair_three_path B.acyclic
    (B.rightmostOutPath x).2 (B.rightmostInPath y).2
    (B.out_in_intersect_of_directed_path (B.rightmostOutPath x).2
      (B.rightmostInPath y).2 P (B.rightmostOutPath_out x) (B.rightmostInPath_in y))

/-- Helper toward Definition 3.13: the first meeting indices, chosen after
existence and uniqueness have been proved. -/
@[expose] noncomputable def threePathFirstMeeting
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    Fin (B.rightmostOutPath x).2.vertices.length ×
      Fin (B.rightmostInPath y).2.vertices.length :=
  Classical.choose (B.exists_unique_threePathFirstMeeting P)

/-- Helper toward Definition 3.13: complete characterization of the chosen
first pair, including minimality along both canonical paths. -/
theorem eq_threePathFirstMeeting_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (ij : Fin (B.rightmostOutPath x).2.vertices.length ×
      Fin (B.rightmostInPath y).2.vertices.length) :
    ij = B.threePathFirstMeeting P ↔
      (B.rightmostOutPath x).2.vertices.get ij.1 =
          (B.rightmostInPath y).2.vertices.get ij.2 ∧
        (∀ k : Fin (B.rightmostOutPath x).2.vertices.length, k.val < ij.1.val →
          (B.rightmostOutPath x).2.vertices.get k ∉ (B.rightmostInPath y).2.vertices) ∧
        (∀ k : Fin (B.rightmostInPath y).2.vertices.length, k.val < ij.2.val →
          (B.rightmostInPath y).2.vertices.get k ∉ (B.rightmostOutPath x).2.vertices) := by
  have h := Classical.choose_spec (B.exists_unique_threePathFirstMeeting P)
  constructor
  · rintro rfl
    exact h.1
  · exact h.2 ij

/-- Helper toward Definition 3.13: traverse the outgoing path to its first
meeting with the incoming path, then the incoming suffix to `y`, and finally
traverse `P` backwards to `x`. Repeated and oppositely traversed edges are
kept; no cancellation or simple-boundary assumption is made. -/
@[expose] noncomputable def threePathBoundaryWalk
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) : List D :=
  (B.rightmostOutPath x).2.darts.take (B.threePathFirstMeeting P).1.val ++
    (B.rightmostInPath y).2.darts.drop (B.threePathFirstMeeting P).2.val ++
      P.darts.reverse.map B.map.edgeInv

/-- Helper toward Definition 3.13: the canonical three-path boundary is a
closed geometric walk at `x`. The recursive walk predicate includes every
consecutive head-to-tail incidence and the closing incidence, with an empty
walk allowed. -/
theorem threePathBoundaryWalk_closed
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    IsBoundaryDartWalk B.map (B.threePathBoundaryWalk P) x x := by
  exact SimpleDirectedDartPath.three_path_closed_walk
    (B.rightmostOutPath x).2 (B.rightmostInPath y).2 P
    (B.threePathFirstMeeting P).1 (B.threePathFirstMeeting P).2
    ((B.eq_threePathFirstMeeting_iff P _).mp rfl).1


/-- Helper toward Definition 3.13: changing an endpoint by an equality
preserves the dart list. This is transport, not an additional premise on
the canonical three-path construction. -/
private theorem transport_start_darts
    {M : DirectedMapWithMissing D} {s s' t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (h : s = s') :
    (h ▸ P : SimpleDirectedDartPath M s' t n).darts = P.darts := by
  cases h
  rfl

/-- Helper toward Definition 3.13: the directed envelope from `x` to `y`
formed by the outgoing prefix and incoming suffix at the first meeting.
Acyclicity proves simplicity of their concatenation, with no disjointness
hypothesis. -/
@[expose] noncomputable def threePathEnvelope
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    SimpleDirectedDartPath B.map x y
      ((B.threePathFirstMeeting P).1.val +
        ((B.rightmostInPath y).1 - (B.threePathFirstMeeting P).2.val)) := by
  let O := (B.rightmostOutPath x).2
  let I := (B.rightmostInPath y).2
  let i := (B.threePathFirstMeeting P).1
  let j := (B.threePathFirstMeeting P).2
  have hij : O.vertices.get i = I.vertices.get j :=
    ((B.eq_threePathFirstMeeting_iff P _).mp rfl).1
  let A := O.prefix ⟨i.val, by rw [← O.vertices_length]; exact i.isLt⟩
  let C := I.suffix ⟨j.val, by rw [← I.vertices_length]; exact j.isLt⟩
  exact A.appendAcyclic B.map B.acyclic (hij.symm ▸ C)

/-- Helper toward Definition 3.13: the directed envelope retains precisely
the two forward portions of the boundary walk, even in degenerate cases. -/
theorem threePathEnvelope_darts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    (B.threePathEnvelope P).darts =
      (B.rightmostOutPath x).2.darts.take (B.threePathFirstMeeting P).1.val ++
        (B.rightmostInPath y).2.darts.drop (B.threePathFirstMeeting P).2.val := by
  unfold threePathEnvelope
  rw [SimpleDirectedDartPath.appendAcyclic_darts, transport_start_darts,
    SimpleDirectedDartPath.prefix_darts, SimpleDirectedDartPath.suffix_darts]

/-- Helper toward Definition 3.13: extend any connector by the canonical
incoming path to `x` and outgoing path from `y`. Acyclicity supplies the
simple source-to-sink cut before its face labels are used. -/
@[expose] noncomputable def threePathExtendedCut
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    SimpleDirectedDartPath B.map B.source B.sink
      (((B.rightmostInPath x).1 + n) + (B.rightmostOutPath y).1) :=
  ((B.rightmostInPath x).2.appendAcyclic B.map B.acyclic P).appendAcyclic
    B.map B.acyclic (B.rightmostOutPath y).2

/-- Helper toward Definition 3.13: the cut extension uses the same exterior
portions for every connector with the given endpoints. -/
theorem threePathExtendedCut_darts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    (B.threePathExtendedCut P).darts =
      (B.rightmostInPath x).2.darts ++ P.darts ++ (B.rightmostOutPath y).2.darts := by
  simp only [threePathExtendedCut, SimpleDirectedDartPath.appendAcyclic_darts]

/-- Helper toward Definition 3.13: internal faces between the connector and
its canonical envelope, specified by the global cut labels. Value zero is
the right side of the extended connector and value one the left side of the
extended envelope. Both cuts have the same incoming prefix and outgoing
suffix. The marked outer face is excluded by normalization. The geometric
identification with the source's filled region remains a separate obligation;
this definition does not assert that identification or a simple boundary. -/
@[expose] noncomputable def threePathRegion
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    Set (CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :=
  {f | ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) f = 0 ∧
    ThreePathFaceLabels.normalized B
      (B.threePathExtendedCut (B.threePathEnvelope P)) f = 1}

/-- Helper toward Definition 3.13: complete face-membership characterization
of the region defined by the two cuts. -/
theorem mem_threePathRegion_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    f ∈ B.threePathRegion P ↔
      ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) f = 0 ∧
        ThreePathFaceLabels.normalized B
          (B.threePathExtendedCut (B.threePathEnvelope P)) f = 1 := Iff.rfl

/-- Helper toward Definition 3.13: the marked outer face is not an internal
face of the cut-defined three-path region. -/
theorem outerFace_not_mem_threePathRegion
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    faceClass B.map.toCombinatorialMap B.map.outer ∉ B.threePathRegion P := by
  intro h
  have ho := ((ThreePathFaceLabels.eq_normalized_iff B
    (B.threePathExtendedCut (B.threePathEnvelope P)) _).mp rfl).2
  exact zero_ne_one (ho.symm.trans h.2)

/-- Helper toward Definition 3.13: the marked geometric boundary support,
including both darts of every walked edge. It retains slit edges traversed
in both directions, even when no internal face is incident to such an edge.
This is the support of the boundary walk; identifying it with the geometric
boundary of the filled region is not asserted by this definition. -/
@[expose] noncomputable def threePathBoundaryDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) : Set D :=
  {d | d ∈ B.threePathBoundaryWalk P ∨ B.map.edgeInv d ∈ B.threePathBoundaryWalk P}

/-- Helper toward Definition 3.13: every walked dart is in the marked
boundary support, including repeated darts and canceled slit edges. -/
theorem mem_threePathBoundaryDarts_of_mem_walk
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {d : D}
    (hd : d ∈ B.threePathBoundaryWalk P) : d ∈ B.threePathBoundaryDarts P :=
  Or.inl hd

/-- Helper toward Definition 3.13: marked boundary support is invariant
under reversal of the dart representing a geometric edge. -/
theorem edgeInv_mem_threePathBoundaryDarts_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    B.map.edgeInv d ∈ B.threePathBoundaryDarts P ↔ d ∈ B.threePathBoundaryDarts P := by
  simp only [threePathBoundaryDarts, Set.mem_ofPred_eq, B.map.edgeInv_invol, or_comm]


/-- Helper toward Definition 3.13: the recursive closed-walk certificate
implies both endpoint incidences and every consecutive head-to-tail
incidence. Empty walks are included by `BoundaryRunEndpoints`. -/
theorem threePathBoundaryWalk_endpoints_and_isChain
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    BoundaryRunEndpoints B.map (B.threePathBoundaryWalk P) x x ∧
      (B.threePathBoundaryWalk P).IsChain
        (fun d e => dartHeadVertex B.map d = dartTailVertex B.map e) :=
  (isBoundaryDartWalk_iff_endpoints_and_isChain B.map _ x x).mp
    (B.threePathBoundaryWalk_closed P)

/-- Helper toward Definition 3.13: in the nonempty case, the last dart ends
at the tail of the first dart. This does not require a simple boundary. -/
theorem threePathBoundaryWalk_last_head_eq_first_tail
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (hne : B.threePathBoundaryWalk P ≠ []) :
    dartHeadVertex B.map ((B.threePathBoundaryWalk P).getLast hne) =
      dartTailVertex B.map ((B.threePathBoundaryWalk P).head hne) := by
  have h := (B.threePathBoundaryWalk_endpoints_and_isChain P).1
  generalize hw : B.threePathBoundaryWalk P = xs at hne h ⊢
  cases xs with
  | nil => exact (hne rfl).elim
  | cons d ds => exact h.2.trans h.1

private theorem mem_reverse_edgeInv_iff_three_path
    (M : DirectedMapWithMissing D) (xs : List D) (d : D) :
    d ∈ xs.reverse.map M.edgeInv ↔ M.edgeInv d ∈ xs := by
  constructor
  · intro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    have heq : e = M.edgeInv d := by
      simpa only [M.edgeInv_invol] using congrArg M.edgeInv hed
    exact heq ▸ List.mem_reverse.mp he
  · intro h
    exact List.mem_map.mpr ⟨M.edgeInv d, List.mem_reverse.mpr h, M.edgeInv_invol d⟩

/-- Helper toward Definition 3.13: the marked boundary consists precisely
of the geometric edges of the three portions. Shared edges remain present;
reversal and cancellation in the walk do not remove their support. -/
theorem mem_threePathBoundaryDarts_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    d ∈ B.threePathBoundaryDarts P ↔
      (d ∈ (B.rightmostOutPath x).2.darts.take (B.threePathFirstMeeting P).1.val ∨
        B.map.edgeInv d ∈
          (B.rightmostOutPath x).2.darts.take (B.threePathFirstMeeting P).1.val) ∨
      (d ∈ (B.rightmostInPath y).2.darts.drop (B.threePathFirstMeeting P).2.val ∨
        B.map.edgeInv d ∈
          (B.rightmostInPath y).2.darts.drop (B.threePathFirstMeeting P).2.val) ∨
      (d ∈ P.darts ∨ B.map.edgeInv d ∈ P.darts) := by
  simp only [threePathBoundaryDarts, Set.mem_ofPred_eq, threePathBoundaryWalk,
    List.mem_append, mem_reverse_edgeInv_iff_three_path, B.map.edgeInv_invol]
  tauto

/-- Helper toward Definition 3.13: an outgoing dart whose reverse is on
the marked outer face is the outgoing right extreme. -/
private theorem out_eq_of_reverse_outer_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {v : MapVertex B.map}
    (ht : v ≠ B.sink) (d : D) (hdv : dartTailVertex B.map d = v)
    (hd : B.map.tail d) (ho : B.map.IsOuter (B.map.edgeInv d)) :
    d = B.out v ht := by
  rcases B.outerSplit with ⟨hcycle, hperm, _, _, _, _⟩
  have hm := (mem_iff_isOuter B.map B.outerWord hcycle _).mpr ho
  rw [hperm.mem_iff] at hm
  simp only [List.append_nil, List.mem_append] at hm
  rcases hm with hl | hr
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
    have hiTail := (B.leftPath.edge_step i).2.1
    rw [hi] at hiTail
    exact (((B.map.tail_iff d (B.noMissingDarts d)).mp hd) hiTail).elim
  · obtain ⟨e, he, hed⟩ := List.mem_map.mp hr
    have hed' : e = d := B.map.edgeInv.injective hed
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hed' ▸ List.mem_reverse.mp he)
    obtain ⟨ht', hs⟩ := B.out_rightPath i
    simpa only [hi, hdv] using hs

/-- Helper toward Definition 3.13: at a vertex of an arbitrary cut, a
distinct rightmost outgoing departure has the right label. The assertion
includes the source and does not require the cut itself to be selected. -/
theorem side_out_not_mem_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (ht : v ≠ B.sink) {b : D}
    (hb : b ∈ C.darts) (hbv : dartTailVertex B.map b = v)
    (hout : B.out v ht ∉ C.darts) :
    ThreePathFaceLabels.side B C (B.out v ht) = false := by
  have hbTail : B.map.tail b := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hb
    exact (C.edge_step i).2.1
  obtain ⟨k, hk, hmin, htail⟩ :=
    B.outgoing_clockwise_interval_three_path v ht b hbv hbTail
  have hpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    have hbo : b = B.out v ht := by
      simpa only [hz, pow_zero, Equiv.Perm.one_apply] using hk
    exact hout (hbo ▸ hb)
  have hvertex (j : ℕ) :
      dartTailVertex B.map ((B.map.rot.symm ^ j) b) = v := by
    apply Eq.trans _ hbv
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_inv.mp
      (Equiv.Perm.sameCycle_pow_right.mpr
        (Equiv.Perm.SameCycle.refl B.map.rot.symm b))).symm
  have havoid (j : ℕ) (hj : 0 < j) (hjk : j < k) :
      (B.map.rot.symm ^ j) b ≠ b := by
    intro he
    have hhit : (B.map.rot.symm ^ (k - j)) b = B.out v ht := by
      calc
        (B.map.rot.symm ^ (k - j)) b =
            (B.map.rot.symm ^ (k - j)) ((B.map.rot.symm ^ j) b) := by rw [he]
        _ = (B.map.rot.symm ^ k) b := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega : j ≤ k)]
        _ = B.out v ht := hk
    exact hmin (k - j) (by omega) hhit
  have hseq : ∀ j, 0 < j → j ≤ k →
      ThreePathFaceLabels.side B C ((B.map.rot.symm ^ j) b) = false := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
        intro _ hj
        let q := (B.map.rot.symm ^ j) b
        have hqt : B.map.tail q := htail j (by omega)
        have hqo : q ≠ B.out v ht := hmin j (by omega)
        have hinner : ¬ B.map.IsOuter (B.map.edgeInv q) := by
          intro ho
          exact hqo (B.out_eq_of_reverse_outer_walk_three_path ht q (hvertex j) hqt ho)
        have hf : B.map.toCombinatorialMap.faceSucc (B.map.edgeInv q) =
            B.map.rot.symm q := by
          change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv q)) = _
          rw [B.map.edgeInv_invol]
        have hstep := ThreePathFaceLabels.side_faceSucc_of_inner B C _ hinner
        rw [hf] at hstep
        by_cases hz : j = 0
        · subst j
          have hseed := ThreePathFaceLabels.side_reverse_path_dart B C hb
          simpa only [q, pow_zero, Equiv.Perm.one_apply, Nat.zero_add, pow_one] using
            hstep.trans hseed
        · have hqC : q ∉ C.darts := by
            intro hm
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
            obtain ⟨a, ha⟩ := List.mem_iff_get.mp hb
            have he : C.vertices.get ⟨i.val, by
                have := i.isLt
                have := C.darts_length
                rw [C.vertices_length]
                omega⟩ =
                C.vertices.get ⟨a.val, by
                  have := a.isLt
                  have := C.darts_length
                  rw [C.vertices_length]
                  omega⟩ :=
              calc
                _ = dartTailVertex B.map (C.darts.get i) := (C.edge_step i).2.2.1
                _ = dartTailVertex B.map q := congrArg (dartTailVertex B.map) hi
                _ = v := hvertex j
                _ = dartTailVertex B.map b := hbv.symm
                _ = dartTailVertex B.map (C.darts.get a) :=
                  congrArg (dartTailVertex B.map) ha.symm
                _ = _ := (C.edge_step a).2.2.1.symm
            have hia : i = a := by
              apply Fin.ext
              exact congrArg (fun z : Fin C.vertices.length => z.val)
                (C.vertices_nodup.get_inj_iff.mp he)
            exact havoid j (by omega) (by omega) (hi.symm.trans (hia ▸ ha))
          have hqiC : B.map.edgeInv q ∉ C.darts := by
            intro hm
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
            exact ((B.map.tail_iff q (B.noMissingDarts q)).mp hqt)
              (hi ▸ (C.edge_step i).2.1)
          have he := ThreePathFaceLabels.side_edgeInv_of_not_seam B C q hqC hqiC
          simpa only [q, pow_succ', Equiv.Perm.mul_apply] using
            hstep.trans (he.trans (ih (by omega) (by omega)))
  have hs := hseq k hpos le_rfl
  rw [hk] at hs
  exact hs

/-- Helper toward Definition 3.13: at a non-source boundary corner, the
incoming right extreme has the right label for every cut. -/
private theorem side_inc_of_reverse_out_outer_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (ho : B.map.IsOuter (B.map.edgeInv (B.out v ht))) :
    ThreePathFaceLabels.side B C (B.inc v hs) = false := by
  rcases B.outerSplit with ⟨hcycle, hperm, _, _, _, _⟩
  have hm := (mem_iff_isOuter B.map B.outerWord hcycle _).mpr ho
  rw [hperm.mem_iff] at hm
  simp only [List.append_nil, List.mem_append] at hm
  have hr : B.map.edgeInv (B.out v ht) ∈
      B.rightPath.darts.reverse.map B.map.edgeInv := by
    rcases hm with hl | hr
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
      exact (((B.map.tail_iff _ (B.noMissingDarts _)).mp (B.out_spec v ht).2.1)
        (hi ▸ (B.leftPath.edge_step i).2.1)).elim
    · exact hr
  obtain ⟨e, he, hed⟩ := List.mem_map.mp hr
  have heq : e = B.out v ht := B.map.edgeInv.injective hed
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (heq ▸ List.mem_reverse.mp he)
  have hip : 0 < i.val := by
    by_contra hn
    have hi0 : i = ⟨0, by rw [B.rightPath.darts_length]; exact B.right_length_pos⟩ :=
      Fin.ext (by change i.val = 0; omega)
    apply hs
    calc
      v = dartTailVertex B.map (B.out v ht) := (B.out_spec v ht).1.symm
      _ = dartTailVertex B.map (B.rightPath.darts.get i) :=
        congrArg (dartTailVertex B.map) hi.symm
      _ = B.rightPath.vertices.get _ := (B.rightPath.edge_step i).2.2.1.symm
      _ = B.source := by simpa only [hi0] using B.rightPath.start_vertex
  let j : Fin B.rightPath.darts.length := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hjv : dartHeadVertex B.map (B.rightPath.darts.get j) = v := by
    calc
      _ = B.rightPath.vertices.get _ := (B.rightPath.edge_step j).2.2.2.symm
      _ = B.rightPath.vertices.get
          ⟨i.val, by have := i.isLt; have := B.rightPath.darts_length
                     rw [B.rightPath.vertices_length]; omega⟩ :=
        congrArg B.rightPath.vertices.get (Fin.ext (by dsimp only [j]; omega))
      _ = dartTailVertex B.map (B.rightPath.darts.get i) :=
        (B.rightPath.edge_step i).2.2.1
      _ = v := (congrArg (dartTailVertex B.map) hi).trans (B.out_spec v ht).1
  obtain ⟨hs', hinc⟩ := B.in_rightPath j
  have hinc' : B.map.edgeInv (B.rightPath.darts.get j) = B.inc v hs := by
    simpa only [hjv] using hinc
  rw [← hinc']
  exact ThreePathFaceLabels.side_right_outer B C
    (List.mem_map.mpr ⟨_, List.mem_reverse.mpr (List.get_mem _ _), rfl⟩)

/-- Helper toward Definition 3.13: the incoming right extreme at a cut
vertex is always on its right side, even when the cut uses neither extreme. -/
theorem side_inc_at_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hs : v ≠ B.source) {b : D}
    (hb : b ∈ C.darts) (hbv : dartTailVertex B.map b = v) :
    ThreePathFaceLabels.side B C (B.inc v hs) = false := by
  classical
  by_cases ht : v = B.sink
  · exact B.side_inc_at_out_cut_three_path C hs (.inl ht)
  by_cases hout : B.out v ht ∈ C.darts
  · exact B.side_inc_at_out_cut_three_path C hs (.inr ⟨ht, hout⟩)
  have houtside := B.side_out_not_mem_cut_three_path C ht hb hbv hout
  by_cases ho : B.map.IsOuter (B.map.edgeInv (B.out v ht))
  · exact B.side_inc_of_reverse_out_outer_walk_three_path C hs ht ho
  have hrev : B.map.edgeInv (B.out v ht) ∉ C.darts := by
    intro hm
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact (((B.map.tail_iff _ (B.noMissingDarts _)).mp (B.out_spec v ht).2.1)
      (hi ▸ (C.edge_step i).2.1)).elim
  have he := ThreePathFaceLabels.side_edgeInv_of_not_seam B C (B.out v ht) hout hrev
  have hf := ThreePathFaceLabels.side_faceSucc_of_inner B C _ ho
  have hface : B.map.toCombinatorialMap.faceSucc (B.map.edgeInv (B.out v ht)) =
      B.inc v hs := by
    change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv (B.out v ht))) = _
    rw [B.map.edgeInv_invol, inc, dite_eq_right ht]
  rw [hface] at hf
  exact hf.trans (he.trans houtside)

/-- Helper toward Definition 3.13: a cut has an outgoing dart at every
listed vertex other than its sink. -/
private theorem exists_departure_cut_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ C.vertices) (ht : v ≠ B.sink) :
    ∃ b, b ∈ C.darts ∧ dartTailVertex B.map b = v := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have hjn : j.val < n := by
    have hjle : j.val ≤ n := by
      have := j.isLt
      have := C.vertices_length
      omega
    by_contra hn
    have hjeq : j = ⟨n, by rw [C.vertices_length]; omega⟩ :=
      Fin.ext (by change j.val = n; omega)
    exact ht (hj.symm.trans (by simpa only [hjeq] using C.end_vertex))
  let i : Fin C.darts.length := ⟨j.val, by rw [C.darts_length]; exact hjn⟩
  refine ⟨C.darts.get i, List.get_mem _ _, ?_⟩
  exact (C.edge_step i).2.2.1.symm.trans
    ((congrArg C.vertices.get (Fin.ext rfl)).trans hj)

/-- Helper toward Definition 3.13: a path following outgoing right
extremes, started on an arbitrary cut, has right-side label at every
off-cut vertex. Repeated contacts with the cut are allowed. -/
theorem offPathSide_out_path_from_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {a b : MapVertex B.map} (O : SimpleDirectedDartPath B.map a b m)
    (hO : B.Out O) (ha : a ∈ C.vertices)
    (i : Fin O.vertices.length) (hi : O.vertices.get i ∉ C.vertices) :
    ThreePathFaceLabels.offPathSide B C ⟨O.vertices.get i, hi⟩ = false := by
  have hmain : ∀ j : ℕ, ∀ hj : j < O.vertices.length,
      ∀ hoff : O.vertices.get ⟨j, hj⟩ ∉ C.vertices,
      ThreePathFaceLabels.offPathSide B C ⟨O.vertices.get ⟨j, hj⟩, hoff⟩ = false := by
    intro j
    induction j with
    | zero =>
        intro hj hoff
        exact (hoff (by simpa only [O.start_vertex] using ha)).elim
    | succ j ih =>
        intro hj hoff
        have hjd : j < O.darts.length := by
          have := O.vertices_length
          rw [O.darts_length]
          omega
        let d := O.darts.get ⟨j, hjd⟩
        let u := O.vertices.get ⟨j, by omega⟩
        let v := O.vertices.get ⟨j + 1, hj⟩
        have hdu : dartTailVertex B.map d = u := (O.edge_step ⟨j, hjd⟩).2.2.1.symm
        have hdv : dartHeadVertex B.map d = v := (O.edge_step ⟨j, hjd⟩).2.2.2.symm
        have hdt : B.map.tail d := (O.edge_step ⟨j, hjd⟩).2.1
        by_cases hu : u ∈ C.vertices
        · obtain ⟨ht, hsel⟩ := hO ⟨j, hjd⟩
          have hut : u ≠ B.sink := fun he => ht (hdu.trans he)
          have hsel' : d = B.out u hut := by
            change d = B.out (dartTailVertex B.map d) ht at hsel
            simpa only [hdu] using hsel
          obtain ⟨c, hc, hcu⟩ := B.exists_departure_cut_walk_three_path C hu hut
          have hdC : d ∉ C.darts := by
            intro hm
            obtain ⟨k, hk⟩ := List.mem_iff_get.mp hm
            apply hoff
            change v ∈ C.vertices
            rw [← hdv, ← hk, ← (C.edge_step k).2.2.2]
            exact List.get_mem _ _
          have hside : ThreePathFaceLabels.side B C d = false := by
            rw [hsel']
            exact B.side_out_not_mem_cut_three_path C hut hc hcu
              (by simpa only [← hsel'] using hdC)
          rw [ThreePathFaceLabels.offPathSide_eq B C ⟨v, hoff⟩
            (B.map.edgeInv d) hdv]
          exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C d
            (.inr (by rw [hdv]; exact hoff))).trans hside
        · have hstep : B.map.directedStep u v :=
            ⟨d, B.noMissingDarts d, hdt, hdu, hdv⟩
          exact (ThreePathFaceLabels.offPathSide_eq_of_directedStep B C
            ⟨u, hu⟩ ⟨v, hoff⟩ hstep).symm.trans (ih (by omega) hu)
  exact hmain i.val i.isLt hi

/-- Helper toward Definition 3.13: a path following incoming right
extremes, ended on an arbitrary cut, has right-side label at every off-cut
vertex. Contacts with the cut and zero-length paths are included. -/
theorem offPathSide_in_path_to_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {a b : MapVertex B.map} (I : SimpleDirectedDartPath B.map a b m)
    (hI : B.In I) (hb : b ∈ C.vertices)
    (i : Fin I.vertices.length) (hi : I.vertices.get i ∉ C.vertices) :
    ThreePathFaceLabels.offPathSide B C ⟨I.vertices.get i, hi⟩ = false := by
  have hmain : ∀ j : ℕ, ∀ k : Fin I.vertices.length, m - k.val = j →
      ∀ hoff : I.vertices.get k ∉ C.vertices,
      ThreePathFaceLabels.offPathSide B C ⟨I.vertices.get k, hoff⟩ = false := by
    intro j
    induction j with
    | zero =>
        intro k hk hoff
        have hkm : k.val = m := by have := k.isLt; have := I.vertices_length; omega
        have hkeq : k = ⟨m, by rw [I.vertices_length]; omega⟩ := Fin.ext hkm
        exact (hoff (by simpa only [hkeq, I.end_vertex] using hb)).elim
    | succ j ih =>
        intro k hk hoff
        have hkm : k.val < m := by omega
        let next : Fin I.vertices.length := ⟨k.val + 1, by have := I.vertices_length; omega⟩
        let idx : Fin I.darts.length := ⟨k.val, by rw [I.darts_length]; exact hkm⟩
        let d := I.darts.get idx
        let u := I.vertices.get k
        let v := I.vertices.get next
        have hdu : dartTailVertex B.map d = u :=
          (I.edge_step idx).2.2.1.symm.trans (congrArg I.vertices.get (Fin.ext rfl))
        have hdv : dartHeadVertex B.map d = v := (I.edge_step idx).2.2.2.symm
        have hdt : B.map.tail d := (I.edge_step idx).2.1
        by_cases hv : v ∈ C.vertices
        · obtain ⟨hs, hsel⟩ := hI idx
          have hvs : v ≠ B.source := fun he => hs (hdv.trans he)
          have hsel' : B.map.edgeInv d = B.inc v hvs := by
            change B.map.edgeInv d = B.inc (dartHeadVertex B.map d) hs at hsel
            simpa only [hdv] using hsel
          have hside : ThreePathFaceLabels.side B C (B.map.edgeInv d) = false := by
            rw [hsel']
            by_cases ht : v = B.sink
            · exact B.side_inc_at_out_cut_three_path C hvs (.inl ht)
            · obtain ⟨c, hc, hcv⟩ := B.exists_departure_cut_walk_three_path C hv ht
              exact B.side_inc_at_cut_three_path C hvs hc hcv
          rw [ThreePathFaceLabels.offPathSide_eq B C ⟨u, hoff⟩ d hdu]
          exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C d
            (.inl (by rw [hdu]; exact hoff))).symm.trans hside
        · have hstep : B.map.directedStep u v :=
            ⟨d, B.noMissingDarts d, hdt, hdu, hdv⟩
          exact (ThreePathFaceLabels.offPathSide_eq_of_directedStep B C
            ⟨u, hoff⟩ ⟨v, hv⟩ hstep).trans
              (ih next (by dsimp only [next]; omega) hv)
  exact hmain (m - i.val) i rfl hi

/-- Helper toward Definition 3.13: every reverse dart of an outgoing
selected path started on the cut has the right-side label. -/
theorem side_reverse_out_path_from_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {a b : MapVertex B.map} (O : SimpleDirectedDartPath B.map a b m)
    (hO : B.Out O) (ha : a ∈ C.vertices) {d : D} (hd : d ∈ O.darts) :
    ThreePathFaceLabels.side B C (B.map.edgeInv d) = false := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  obtain ⟨ht, hsel⟩ := hO i
  have ht' : dartTailVertex B.map d ≠ B.sink := by simpa only [hi] using ht
  have hsel' : d = B.out (dartTailVertex B.map d) ht' := by simpa only [hi] using hsel
  by_cases hv : dartTailVertex B.map d ∈ C.vertices
  · by_cases hm : d ∈ C.darts
    · exact ThreePathFaceLabels.side_reverse_path_dart B C hm
    · obtain ⟨c, hc, hcv⟩ := B.exists_departure_cut_walk_three_path C hv ht'
      have hside : ThreePathFaceLabels.side B C d = false := by
        rw [hsel']
        exact B.side_out_not_mem_cut_three_path C ht' hc hcv
          (by simpa only [← hsel'] using hm)
      have hrev : B.map.edgeInv d ∉ C.darts := by
        intro hr
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hr
        have hdt : B.map.tail d := hi ▸ (O.edge_step i).2.1
        exact (((B.map.tail_iff d (B.noMissingDarts d)).mp hdt)
          (hj ▸ (C.edge_step j).2.1)).elim
      exact (ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hm hrev).trans hside
  · let j : Fin O.vertices.length := ⟨i.val, by
      have := i.isLt
      have := O.darts_length
      have := O.vertices_length
      omega⟩
    have hj : O.vertices.get j = dartTailVertex B.map d :=
      (O.edge_step i).2.2.1.trans (congrArg (dartTailVertex B.map) hi)
    have hoff : O.vertices.get j ∉ C.vertices := fun hm => hv (hj ▸ hm)
    have hside := B.offPathSide_out_path_from_cut_three_path C O hO ha j hoff
    rw [ThreePathFaceLabels.offPathSide_eq B C ⟨O.vertices.get j, hoff⟩ d hj.symm] at hside
    exact (ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C d (.inl hv)).trans hside

/-- Helper toward Definition 3.13: every reverse dart of an incoming
selected path ended on the cut has the right-side label. -/
theorem side_reverse_in_path_to_cut_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {a b : MapVertex B.map} (I : SimpleDirectedDartPath B.map a b m)
    (hI : B.In I) (hb : b ∈ C.vertices) {d : D} (hd : d ∈ I.darts) :
    ThreePathFaceLabels.side B C (B.map.edgeInv d) = false := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  obtain ⟨hs, hsel⟩ := hI i
  have hs' : dartHeadVertex B.map d ≠ B.source := by simpa only [hi] using hs
  have hsel' : B.map.edgeInv d = B.inc (dartHeadVertex B.map d) hs' := by
    simpa only [hi] using hsel
  by_cases hv : dartHeadVertex B.map d ∈ C.vertices
  · rw [hsel']
    by_cases ht : dartHeadVertex B.map d = B.sink
    · exact B.side_inc_at_out_cut_three_path C hs' (.inl ht)
    · obtain ⟨c, hc, hcv⟩ := B.exists_departure_cut_walk_three_path C hv ht
      exact B.side_inc_at_cut_three_path C hs' hc hcv
  · let j : Fin I.vertices.length := ⟨i.val + 1, by
      have := i.isLt
      have := I.darts_length
      have := I.vertices_length
      omega⟩
    have hj : I.vertices.get j = dartHeadVertex B.map d :=
      (I.edge_step i).2.2.2.trans (congrArg (dartHeadVertex B.map) hi)
    have hoff : I.vertices.get j ∉ C.vertices := fun hm => hv (hj ▸ hm)
    have hside := B.offPathSide_in_path_to_cut_three_path C I hI hb j hoff
    rw [ThreePathFaceLabels.offPathSide_eq B C ⟨I.vertices.get j, hoff⟩
      (B.map.edgeInv d) hj.symm] at hside
    exact hside

/-- Helper toward Definition 3.13: membership in an acyclic concatenation
retains all vertices of both portions, including their shared endpoint. -/
private theorem mem_append_vertices_walk_three_path {M : DirectedMapWithMissing D}
    (hacyclic : M.IsAcyclic) {s v t : MapVertex M} {a b : ℕ}
    (P : SimpleDirectedDartPath M s v a) (Q : SimpleDirectedDartPath M v t b)
    (z : MapVertex M) :
    z ∈ (P.appendAcyclic M hacyclic Q).vertices ↔ z ∈ P.vertices ∨ z ∈ Q.vertices := by
  change z ∈ P.vertices.take a ++ Q.vertices ↔ _
  rw [List.mem_append]
  constructor
  · exact Or.imp List.mem_of_mem_take id
  · rintro (hP | hQ)
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
      by_cases hia : i.val < a
      · exact .inl (List.mem_iff_get.mpr
          ⟨⟨i.val, by simp only [List.length_take, P.vertices_length]; omega⟩,
            by simpa only [List.get_eq_getElem, List.getElem_take] using hi⟩)
      · have he : i = ⟨a, by rw [P.vertices_length]; omega⟩ :=
          Fin.ext (by have := i.isLt; have := P.vertices_length; change i.val = a; omega)
        have hz : z = v := hi.symm.trans (by rw [he]; exact P.end_vertex)
        exact .inr (hz ▸ Q.start_mem_vertices_three_path)
    · exact .inr hQ

/-- Helper toward Definition 3.13: every vertex of the connector remains
on its extended source-to-sink cut. -/
theorem mem_threePathExtendedCut_vertices
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {z : MapVertex B.map}
    (hz : z ∈ P.vertices) : z ∈ (B.threePathExtendedCut P).vertices := by
  exact (mem_append_vertices_walk_three_path B.acyclic _ _ z).mpr (.inl
    ((mem_append_vertices_walk_three_path B.acyclic _ _ z).mpr (.inr hz)))

/-- Helper toward Definition 3.13: the reverse of every dart of the
extended envelope has right-side label for the extended connector. The
canonical portions can overlap the connector or one another. This is a
dart-side conclusion; face-label nesting is still a separate assertion. -/
theorem side_reverse_threePathExtendedEnvelope
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {d : D}
    (hd : d ∈ (B.threePathExtendedCut (B.threePathEnvelope P)).darts) :
    ThreePathFaceLabels.side B (B.threePathExtendedCut P) (B.map.edgeInv d) = false := by
  rw [B.threePathExtendedCut_darts] at hd
  rcases List.mem_append.mp hd with hmid | hsuffix
  · rcases List.mem_append.mp hmid with hprefix | henvelope
    · apply ThreePathFaceLabels.side_reverse_path_dart
      rw [B.threePathExtendedCut_darts]
      exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hprefix)))
    · rw [B.threePathEnvelope_darts] at henvelope
      rcases List.mem_append.mp henvelope with hout | hin
      · exact B.side_reverse_out_path_from_cut_three_path (B.threePathExtendedCut P)
          (B.rightmostOutPath x).2 (B.rightmostOutPath_out x)
          (B.mem_threePathExtendedCut_vertices P P.start_mem_vertices_three_path)
          (List.mem_of_mem_take hout)
      · exact B.side_reverse_in_path_to_cut_three_path (B.threePathExtendedCut P)
          (B.rightmostInPath y).2 (B.rightmostInPath_in y)
          (B.mem_threePathExtendedCut_vertices P P.end_mem_vertices_three_path)
          (List.mem_of_mem_drop hin)
  · apply ThreePathFaceLabels.side_reverse_path_dart
    rw [B.threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inr hsuffix)

/-- Helper toward Definition 3.13: a mod-two cycle supported on the
geometric edges of a simple path is zero. -/
private theorem cycle_supported_on_path_eq_zero_walk_three_path
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (c : EdgeSpace M.toCombinatorialMap)
    (hc : vertexBoundary M.toCombinatorialMap c = 0)
    (hsupport : ∀ d, c (edgeClass M.toCombinatorialMap d) ≠ 0 →
      d ∈ P.darts ∨ M.edgeInv d ∈ P.darts) : c = 0 := by
  classical
  have hedge (d : D) : edgeClass M.toCombinatorialMap (M.edgeInv d) =
      edgeClass M.toCombinatorialMap d := by
    apply Quotient.sound
    exact (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap _ _).mpr
      (.inr (M.edgeInv_invol d).symm)
  funext e
  refine Quotient.inductionOn e ?_
  intro d
  by_contra hd
  change c (edgeClass M.toCombinatorialMap d) ≠ 0 at hd
  have hex : ∃ j : ℕ, ∃ hj : j < P.darts.length,
      c (edgeClass M.toCombinatorialMap (P.darts.get ⟨j, hj⟩)) ≠ 0 := by
    rcases hsupport d hd with hm | hm
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      exact ⟨j.val, j.isLt, by simpa only [hj] using hd⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      exact ⟨j.val, j.isLt, by simpa only [hj, hedge] using hd⟩
  let i := Nat.find hex
  obtain ⟨hi, hci⟩ := Nat.find_spec hex
  let a := P.darts.get ⟨i, hi⟩
  let v := vertexClass M.toCombinatorialMap a
  have hzero (q : D) (hqa : q ≠ a) :
      (if vertexClass M.toCombinatorialMap q = v then
        c (edgeClass M.toCombinatorialMap q) else 0) = 0 := by
    by_cases hqv : vertexClass M.toCombinatorialMap q = v
    · rw [ite_eq_left hqv]
      by_contra hq
      rcases hsupport q hq with hm | hm
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
        have he : P.vertices.get
            ⟨j.val, by have := j.isLt; have := P.darts_length; have := P.vertices_length; omega⟩ =
            P.vertices.get
            ⟨i, by have := P.darts_length; have := P.vertices_length; omega⟩ := by
          calc
            _ = dartTailVertex M (P.darts.get j) := (P.edge_step j).2.2.1
            _ = dartTailVertex M q := congrArg (dartTailVertex M) hj
            _ = dartTailVertex M a := hqv
            _ = _ := (P.edge_step ⟨i, hi⟩).2.2.1.symm
        have hji : j.val = i := congrArg
          (fun z : Fin P.vertices.length => z.val) (P.vertices_nodup.get_inj_iff.mp he)
        exact hqa (hj.symm.trans (congrArg P.darts.get (Fin.ext hji)))
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
        have he : P.vertices.get
            ⟨j.val + 1, by have := j.isLt; have := P.darts_length; have := P.vertices_length; omega⟩ =
            P.vertices.get
            ⟨i, by have := P.darts_length; have := P.vertices_length; omega⟩ := by
          calc
            _ = dartHeadVertex M (P.darts.get j) := (P.edge_step j).2.2.2
            _ = dartHeadVertex M (M.edgeInv q) := congrArg (dartHeadVertex M) hj
            _ = dartTailVertex M q := by simp only [dartHeadVertex, dartTailVertex, M.edgeInv_invol]
            _ = dartTailVertex M a := hqv
            _ = _ := (P.edge_step ⟨i, hi⟩).2.2.1.symm
        have hji : j.val + 1 = i := congrArg
          (fun z : Fin P.vertices.length => z.val) (P.vertices_nodup.get_inj_iff.mp he)
        exact Nat.find_min hex (by omega : j.val < i)
          ⟨j.isLt, by simpa only [hj, hedge] using hq⟩
    · exact ite_eq_right hqv
  have hsum := congrFun hc v
  change (∑ q : D, if vertexClass M.toCombinatorialMap q = v then
    c (edgeClass M.toCombinatorialMap q) else 0) = 0 at hsum
  rw [Finset.sum_eq_single a] at hsum
  · rw [ite_eq_left (show vertexClass M.toCombinatorialMap a = v from rfl)] at hsum
    exact hci hsum
  · intro q _ hqa
    exact hzero q hqa
  · intro h
    exact (h (Finset.mem_univ a)).elim

/-- Helper toward Definition 3.13: the two coefficients in the face field. -/
private theorem zmod_two_eq_zero_or_one_walk_three_path (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hz := ZMod.val_lt z
  have hval : z.val = 0 ∨ z.val = 1 := by omega
  rcases hval with h | h
  · left
    apply ZMod.val_injective 2
    simpa only [ZMod.val_zero] using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- Helper toward Definition 3.13: the face function measuring failure of
nesting agrees with the corresponding pair of dart-side labels. Both cuts
give the same label on each marked exterior arc, so the exterior case also
has value zero. -/
private theorem normalized_mul_complement_eq_side_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    (E : SimpleDirectedDartPath B.map B.source B.sink m) (d : D) :
    ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap d) *
        (1 - ThreePathFaceLabels.normalized B E (faceClass B.map.toCombinatorialMap d)) =
      if ThreePathFaceLabels.side B C d = true ∧ ThreePathFaceLabels.side B E d = false
        then 1 else 0 := by
  classical
  have houter (ho : B.map.IsOuter d) :
      ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap d) = 0 := by
    have hface : faceClass B.map.toCombinatorialMap d =
        faceClass B.map.toCombinatorialMap B.map.outer := Quotient.sound ho.symm
    rw [hface]
    exact ((ThreePathFaceLabels.eq_normalized_iff B C _).mp rfl).2
  by_cases hul : d ∈ B.map.ulDarts
  · simp only [houter hul.2.2, zero_mul, ThreePathFaceLabels.side,
      ite_eq_left hul, Bool.true_eq_false, and_false, ite_false]
  by_cases hlr : d ∈ B.map.lrDarts
  · simp only [houter hlr.2.2, zero_mul, ThreePathFaceLabels.side,
      ite_eq_right hul, ite_eq_left hlr, Bool.false_eq_true, false_and, ite_false]
  rcases zmod_two_eq_zero_or_one_walk_three_path
    (ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap d)) with hc | hc <;>
    rcases zmod_two_eq_zero_or_one_walk_three_path
      (ThreePathFaceLabels.normalized B E (faceClass B.map.toCombinatorialMap d)) with he | he <;>
    simp [ThreePathFaceLabels.side, hul, hlr, hc, he]

/-- Helper toward Definition 3.13: a cut whose reverse darts all have
right-side label for a second cut contains the latter cut's left face set.
The proof uses the fact that a simple path supports no nonzero mod-two cycle. -/
private theorem normalized_nesting_of_reverse_sides_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n m : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    (E : SimpleDirectedDartPath B.map B.source B.sink m)
    (hE : ∀ d, d ∈ E.darts → ThreePathFaceLabels.side B C (B.map.edgeInv d) = false)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    ThreePathFaceLabels.normalized B C f = 1 →
      ThreePathFaceLabels.normalized B E f = 1 := by
  classical
  let T : FaceSpace B.map.toCombinatorialMap := fun g =>
    ThreePathFaceLabels.normalized B C g * (1 - ThreePathFaceLabels.normalized B E g)
  have hboundary : faceBoundary B.map.toCombinatorialMap T = 0 := by
    apply cycle_supported_on_path_eq_zero_walk_three_path C
      (faceBoundary B.map.toCombinatorialMap T)
      (vertexBoundary_faceBoundary B.map.toCombinatorialMap T)
    intro d hcoeff
    by_cases hd : d ∈ C.darts
    · exact .inl hd
    by_cases hi : B.map.edgeInv d ∈ C.darts
    · exact .inr hi
    exfalso
    apply hcoeff
    rw [faceBoundary_apply]
    change
      ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap d) *
          (1 - ThreePathFaceLabels.normalized B E (faceClass B.map.toCombinatorialMap d)) +
        ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap (B.map.edgeInv d)) *
          (1 - ThreePathFaceLabels.normalized B E
            (faceClass B.map.toCombinatorialMap (B.map.edgeInv d))) = 0
    rw [normalized_mul_complement_eq_side_walk_three_path B C E d,
      normalized_mul_complement_eq_side_walk_three_path B C E (B.map.edgeInv d)]
    have hCflip := ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hd hi
    by_cases hdE : d ∈ E.darts
    · have hsi := hE d hdE
      have hsd := hCflip.symm.trans hsi
      simp only [hsd, hsi, Bool.false_eq_true, false_and, ite_false, zero_add]
    by_cases hiE : B.map.edgeInv d ∈ E.darts
    · have hsd : ThreePathFaceLabels.side B C d = false := by
        simpa only [B.map.edgeInv_invol] using hE (B.map.edgeInv d) hiE
      have hsi := hCflip.trans hsd
      simp only [hsd, hsi, Bool.false_eq_true, false_and, ite_false, zero_add]
    · rw [hCflip, ThreePathFaceLabels.side_edgeInv_of_not_seam B E d hdE hiE]
      exact CharTwo.add_self_eq_zero _
  have hTzero : T = 0 := by
    rcases (faceBoundary_eq_zero_iff_connected B.map.toCombinatorialMap B.planar.1 T).mp
      hboundary with hz | ho
    · exact hz
    · have he := congrFun ho (faceClass B.map.toCombinatorialMap B.map.outer)
      have hCouter := ((ThreePathFaceLabels.eq_normalized_iff B C _).mp rfl).2
      change ThreePathFaceLabels.normalized B C _ *
        (1 - ThreePathFaceLabels.normalized B E _) = 1 at he
      rw [hCouter, zero_mul] at he
      exact (zero_ne_one he).elim
  intro hCf
  rcases zmod_two_eq_zero_or_one_walk_three_path (ThreePathFaceLabels.normalized B E f)
    with hEf | hEf
  · have hf := congrFun hTzero f
    change ThreePathFaceLabels.normalized B C f *
      (1 - ThreePathFaceLabels.normalized B E f) = 0 at hf
    rw [hCf, hEf, sub_zero, mul_one] at hf
    exact (one_ne_zero hf).elim
  · exact hEf

/-- Helper toward Definition 3.13: the left face set of every extended
connector is contained in the left face set of its extended canonical
envelope, with arbitrary endpoints, shared portions and degeneracies. -/
theorem normalized_threePathExtendedCut_eq_one_imp_envelope
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) f = 1 →
      ThreePathFaceLabels.normalized B
        (B.threePathExtendedCut (B.threePathEnvelope P)) f = 1 :=
  B.normalized_nesting_of_reverse_sides_walk_three_path
    (B.threePathExtendedCut P) (B.threePathExtendedCut (B.threePathEnvelope P))
    (fun _ hd => B.side_reverse_threePathExtendedEnvelope P hd) f

/-- Helper toward Definition 3.13: the face indicator of the region is the
product of the envelope label and the complement of the connector label. -/
theorem mem_threePathRegion_iff_mul_eq_one
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    f ∈ B.threePathRegion P ↔
      ThreePathFaceLabels.normalized B
          (B.threePathExtendedCut (B.threePathEnvelope P)) f *
        (1 - ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) f) = 1 := by
  rw [B.mem_threePathRegion_iff]
  rcases zmod_two_eq_zero_or_one_walk_three_path
    (ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) f) with hc | hc <;>
    rcases zmod_two_eq_zero_or_one_walk_three_path
      (ThreePathFaceLabels.normalized B
        (B.threePathExtendedCut (B.threePathEnvelope P)) f) with he | he <;>
    simp [hc, he]

/-- Helper toward Definition 3.13: an envelope dart belongs to the marked
geometric boundary even when its edge is shared with the connector. -/
theorem mem_threePathBoundaryDarts_of_mem_envelope
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {d : D}
    (hd : d ∈ (B.threePathEnvelope P).darts) : d ∈ B.threePathBoundaryDarts P := by
  rw [B.threePathEnvelope_darts] at hd
  apply (B.mem_threePathBoundaryDarts_iff P d).mpr
  rcases List.mem_append.mp hd with ho | hi
  · exact .inl (.inl ho)
  · exact .inr (.inl (.inl hi))

/-- Helper toward Definition 3.13: crossing an edge absent from the
marked three-path walk preserves region membership. Faces are the actual
`faceSucc` cycles, with no restriction on their degrees. -/
theorem threePathRegion_face_edgeInv_iff_of_not_boundary
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D)
    (hd : d ∉ B.threePathBoundaryDarts P) :
    faceClass B.map.toCombinatorialMap d ∈ B.threePathRegion P ↔
      faceClass B.map.toCombinatorialMap (B.map.edgeInv d) ∈ B.threePathRegion P := by
  have hdi : B.map.edgeInv d ∉ B.threePathBoundaryDarts P :=
    fun hm => hd ((B.edgeInv_mem_threePathBoundaryDarts_iff P d).mp hm)
  have hP (e : D) (he : e ∉ B.threePathBoundaryDarts P) : e ∉ P.darts := by
    intro hm
    exact he ((B.mem_threePathBoundaryDarts_iff P e).mpr (.inr (.inr (.inl hm))))
  have henv (e : D) (he : e ∉ B.threePathBoundaryDarts P) :
      e ∉ (B.threePathEnvelope P).darts :=
    fun hm => he (B.mem_threePathBoundaryDarts_of_mem_envelope P hm)
  let C := B.threePathExtendedCut P
  let E := B.threePathExtendedCut (B.threePathEnvelope P)
  have hsame (e : D) (he : e ∉ B.threePathBoundaryDarts P) :
      e ∈ C.darts ↔ e ∈ E.darts := by
    simp only [C, E, B.threePathExtendedCut_darts, List.mem_append, hP e he, henv e he]
  have hprod :
      ThreePathFaceLabels.normalized B E (faceClass B.map.toCombinatorialMap d) *
          (1 - ThreePathFaceLabels.normalized B C (faceClass B.map.toCombinatorialMap d)) =
        ThreePathFaceLabels.normalized B E (faceClass B.map.toCombinatorialMap (B.map.edgeInv d)) *
          (1 - ThreePathFaceLabels.normalized B C
            (faceClass B.map.toCombinatorialMap (B.map.edgeInv d))) := by
    rw [normalized_mul_complement_eq_side_walk_three_path B E C d,
      normalized_mul_complement_eq_side_walk_three_path B E C (B.map.edgeInv d)]
    by_cases hm : d ∈ C.darts
    · have hmE := (hsame d hd).mp hm
      rw [ThreePathFaceLabels.side_path_dart B C hm,
        ThreePathFaceLabels.side_reverse_path_dart B E hmE]
      simp only [Bool.true_eq_false, and_false, Bool.false_eq_true, false_and, ite_false]
    by_cases hi : B.map.edgeInv d ∈ C.darts
    · have hiE := (hsame (B.map.edgeInv d) hdi).mp hi
      have hC : ThreePathFaceLabels.side B C d = false := by
        simpa only [B.map.edgeInv_invol] using
          ThreePathFaceLabels.side_reverse_path_dart B C hi
      have hE : ThreePathFaceLabels.side B E d = false := by
        simpa only [B.map.edgeInv_invol] using
          ThreePathFaceLabels.side_reverse_path_dart B E hiE
      rw [hE, ThreePathFaceLabels.side_path_dart B C hi]
      simp only [Bool.false_eq_true, false_and, Bool.true_eq_false, and_false, ite_false]
    · have hmE : d ∉ E.darts := fun h => hm ((hsame d hd).mpr h)
      have hiE : B.map.edgeInv d ∉ E.darts :=
        fun h => hi ((hsame (B.map.edgeInv d) hdi).mpr h)
      rw [ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hm hi,
        ThreePathFaceLabels.side_edgeInv_of_not_seam B E d hmE hiE]
  rw [B.mem_threePathRegion_iff_mul_eq_one, B.mem_threePathRegion_iff_mul_eq_one]
  exact iff_of_eq (congrArg (· = 1) hprod)

/-- Helper toward Definition 3.13: adjacency of face cycles through an
edge outside the marked boundary. Removing the geometric support retains
slit edges as barriers, even when they have the same face on both sides. -/
@[expose] def threePathFaceStep
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f g : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) : Prop :=
  ∃ d : D, d ∉ B.threePathBoundaryDarts P ∧
    faceClass B.map.toCombinatorialMap d = f ∧
    faceClass B.map.toCombinatorialMap (B.map.edgeInv d) = g

/-- Helper toward Definition 3.13: geometric face adjacency outside the
marked walk is symmetric, even when both incident faces coincide. -/
theorem threePathFaceStep_symm
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    {f g : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap}
    (h : B.threePathFaceStep P f g) : B.threePathFaceStep P g f := by
  obtain ⟨d, hd, hf, hg⟩ := h
  refine ⟨B.map.edgeInv d, ?_, hg, ?_⟩
  · exact fun hm => hd ((B.edgeInv_mem_threePathBoundaryDarts_iff P d).mp hm)
  · simpa only [B.map.edgeInv_invol] using hf

/-- Helper toward Definition 3.13: region membership is invariant under
every path of face adjacencies avoiding the geometric boundary support. -/
theorem mem_threePathRegion_iff_of_face_reaches
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    {f g : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap}
    (hfg : Relation.ReflTransGen (B.threePathFaceStep P) f g) :
    f ∈ B.threePathRegion P ↔ g ∈ B.threePathRegion P := by
  induction hfg with
  | refl => rfl
  | @tail g h _ hgh ih =>
      obtain ⟨d, hd, rfl, rfl⟩ := hgh
      exact ih.trans (B.threePathRegion_face_edgeInv_iff_of_not_boundary P d hd)

/-- Helper toward Definition 3.13: a region face cannot reach the marked
outer face without crossing the three-path boundary. The converse enclosure
identification remains a separate obligation. -/
theorem not_face_reaches_outer_of_mem_threePathRegion
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hf : f ∈ B.threePathRegion P) :
    ¬ Relation.ReflTransGen (B.threePathFaceStep P) f
      (faceClass B.map.toCombinatorialMap B.map.outer) := by
  intro h
  exact B.outerFace_not_mem_threePathRegion P
    ((B.mem_threePathRegion_iff_of_face_reaches P h).mp hf)

/-- Helper toward Definition 3.13: an exterior-zero face function whose
boundary is supported on a simple path vanishes. -/
private theorem face_function_eq_zero_of_path_support_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {s t : MapVertex B.map} {n : ℕ}
    (A : SimpleDirectedDartPath B.map s t n)
    (T : FaceSpace B.map.toCombinatorialMap)
    (ho : T (faceClass B.map.toCombinatorialMap B.map.outer) = 0)
    (hs : ∀ d, faceBoundary B.map.toCombinatorialMap T
      (edgeClass B.map.toCombinatorialMap d) ≠ 0 →
        d ∈ A.darts ∨ B.map.edgeInv d ∈ A.darts) : T = 0 := by
  have hz := cycle_supported_on_path_eq_zero_walk_three_path A
    (faceBoundary B.map.toCombinatorialMap T)
    (vertexBoundary_faceBoundary B.map.toCombinatorialMap T) hs
  rcases (faceBoundary_eq_zero_iff_connected B.map.toCombinatorialMap B.planar.1 T).mp hz
      with h | h
  · exact h
  · have he := congrFun h (faceClass B.map.toCombinatorialMap B.map.outer)
    exact (zero_ne_one (ho.symm.trans he)).elim

/-- Helper toward Definition 3.13: multiplication by an exterior-zero face
function removes the exceptional exterior corner labels. -/
private theorem mul_normalized_eq_side_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (A : SimpleDirectedDartPath B.map B.source B.sink n)
    (T : FaceSpace B.map.toCombinatorialMap)
    (ho : T (faceClass B.map.toCombinatorialMap B.map.outer) = 0) (d : D) :
    T (faceClass B.map.toCombinatorialMap d) *
        ThreePathFaceLabels.normalized B A (faceClass B.map.toCombinatorialMap d) =
      if ThreePathFaceLabels.side B A d = true
        then T (faceClass B.map.toCombinatorialMap d) else 0 := by
  classical
  have hzero (hd : B.map.IsOuter d) : T (faceClass B.map.toCombinatorialMap d) = 0 := by
    have he : faceClass B.map.toCombinatorialMap d =
        faceClass B.map.toCombinatorialMap B.map.outer := Quotient.sound hd.symm
    exact he ▸ ho
  by_cases hul : d ∈ B.map.ulDarts
  · simp only [hzero hul.2.2, zero_mul, ite_self]
  by_cases hlr : d ∈ B.map.lrDarts
  · simp only [hzero hlr.2.2, zero_mul, ite_self]
  rcases zmod_two_eq_zero_or_one_walk_three_path
    (ThreePathFaceLabels.normalized B A (faceClass B.map.toCombinatorialMap d)) with h | h <;>
    simp only [ThreePathFaceLabels.side, ite_eq_right hul, ite_eq_right hlr, h,
      zero_ne_one, decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true,
      mul_zero, mul_one]

/-- Helper toward Definition 3.13: the complementary cut label obeys the
same exterior-zero multiplication rule. -/
private theorem mul_complement_normalized_eq_side_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (A : SimpleDirectedDartPath B.map B.source B.sink n)
    (T : FaceSpace B.map.toCombinatorialMap)
    (ho : T (faceClass B.map.toCombinatorialMap B.map.outer) = 0) (d : D) :
    T (faceClass B.map.toCombinatorialMap d) *
        (1 - ThreePathFaceLabels.normalized B A (faceClass B.map.toCombinatorialMap d)) =
      if ThreePathFaceLabels.side B A d = true
        then 0 else T (faceClass B.map.toCombinatorialMap d) := by
  rw [mul_sub, mul_one, mul_normalized_eq_side_walk_three_path B A T ho d]
  split <;> simp only [sub_self, sub_zero]

/-- Helper toward Definition 3.13: nesting also holds for dart-side labels,
including the marked exterior corners. -/
private theorem side_threePathExtendedCut_imp_envelope_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    ThreePathFaceLabels.side B (B.threePathExtendedCut P) d = true →
      ThreePathFaceLabels.side B
        (B.threePathExtendedCut (B.threePathEnvelope P)) d = true := by
  classical
  by_cases hul : d ∈ B.map.ulDarts
  · simp only [ThreePathFaceLabels.side, ite_eq_left hul, implies_true]
  by_cases hlr : d ∈ B.map.lrDarts
  · simp only [ThreePathFaceLabels.side, ite_eq_right hul, ite_eq_left hlr,
      Bool.false_eq_true, false_implies]
  simp only [ThreePathFaceLabels.side, ite_eq_right hul, ite_eq_right hlr,
    decide_eq_true_eq]
  exact B.normalized_threePathExtendedCut_eq_one_imp_envelope P _

/-- Helper toward Definition 3.13: the geometric support is the union of
the connector and envelope supports, with no cancellation of shared edges. -/
theorem mem_threePathBoundaryDarts_iff_connector_or_envelope
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    d ∈ B.threePathBoundaryDarts P ↔
      (d ∈ P.darts ∨ B.map.edgeInv d ∈ P.darts) ∨
        (d ∈ (B.threePathEnvelope P).darts ∨
          B.map.edgeInv d ∈ (B.threePathEnvelope P).darts) := by
  rw [B.mem_threePathBoundaryDarts_iff, B.threePathEnvelope_darts]
  simp only [List.mem_append]
  tauto

/-- Helper toward Definition 3.13: every face separated from the marked
outer face by the full geometric walk support belongs to the cut-defined
region. Shared portions and slit edges require no additional premise. -/
theorem mem_threePathRegion_of_not_face_reaches_outer
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap)
    (hf : ¬ Relation.ReflTransGen (B.threePathFaceStep P) f
      (faceClass B.map.toCombinatorialMap B.map.outer)) :
    f ∈ B.threePathRegion P := by
  classical
  let C := B.threePathExtendedCut P
  let E := B.threePathExtendedCut (B.threePathEnvelope P)
  let T : FaceSpace B.map.toCombinatorialMap := fun g =>
    if Relation.ReflTransGen (B.threePathFaceStep P) g
      (faceClass B.map.toCombinatorialMap B.map.outer) then 0 else 1
  have ho : T (faceClass B.map.toCombinatorialMap B.map.outer) = 0 :=
    ite_eq_left Relation.ReflTransGen.refl
  have hTf : T f = 1 := ite_eq_right hf
  have hstep (d : D) (hd : d ∉ B.threePathBoundaryDarts P) :
      T (faceClass B.map.toCombinatorialMap d) =
        T (faceClass B.map.toCombinatorialMap (B.map.edgeInv d)) := by
    have hs : B.threePathFaceStep P (faceClass B.map.toCombinatorialMap d)
        (faceClass B.map.toCombinatorialMap (B.map.edgeInv d)) := ⟨d, hd, rfl, rfl⟩
    have hr : Relation.ReflTransGen (B.threePathFaceStep P)
        (faceClass B.map.toCombinatorialMap d)
        (faceClass B.map.toCombinatorialMap B.map.outer) ↔
      Relation.ReflTransGen (B.threePathFaceStep P)
        (faceClass B.map.toCombinatorialMap (B.map.edgeInv d))
        (faceClass B.map.toCombinatorialMap B.map.outer) :=
      ⟨fun h => h.head (B.threePathFaceStep_symm P hs), fun h => h.head hs⟩
    simp only [T, hr]
  have hCP (d : D) (hd : d ∈ P.darts) : d ∈ C.darts := by
    rw [threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hd)))
  have hEP (d : D) (hd : d ∈ (B.threePathEnvelope P).darts) : d ∈ E.darts := by
    rw [threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hd)))
  have hTC : (fun g => T g * ThreePathFaceLabels.normalized B C g) = 0 := by
    apply face_function_eq_zero_of_path_support_walk_three_path B C
      (fun g => T g * ThreePathFaceLabels.normalized B C g) (by rw [ho, zero_mul])
    intro d hcoeff
    by_cases hd : d ∈ C.darts
    · exact .inl hd
    by_cases hi : B.map.edgeInv d ∈ C.darts
    · exact .inr hi
    exfalso
    apply hcoeff
    rw [faceBoundary_apply]
    rw [mul_normalized_eq_side_walk_three_path B C T ho d,
      mul_normalized_eq_side_walk_three_path B C T ho (B.map.edgeInv d)]
    have hflip := ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hd hi
    by_cases hb : d ∈ B.threePathBoundaryDarts P
    · have hside : ThreePathFaceLabels.side B C d = false := by
        rcases (B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mp hb with
          hp | he
        · rcases hp with hp | hp
          · exact (hd (hCP d hp)).elim
          · exact (hi (hCP (B.map.edgeInv d) hp)).elim
        · rcases he with he | he
          · exact hflip.symm.trans (B.side_reverse_threePathExtendedEnvelope P (hEP d he))
          · simpa only [B.map.edgeInv_invol] using
              B.side_reverse_threePathExtendedEnvelope P (hEP (B.map.edgeInv d) he)
      rw [hflip, hside]
      simp only [Bool.false_eq_true, ite_false, zero_add]
    · rw [hflip, hstep d hb]
      exact CharTwo.add_self_eq_zero _
  have hTE : (fun g => T g * (1 - ThreePathFaceLabels.normalized B E g)) = 0 := by
    apply face_function_eq_zero_of_path_support_walk_three_path B E
      (fun g => T g * (1 - ThreePathFaceLabels.normalized B E g)) (by rw [ho, zero_mul])
    intro d hcoeff
    by_cases hd : d ∈ E.darts
    · exact .inl hd
    by_cases hi : B.map.edgeInv d ∈ E.darts
    · exact .inr hi
    exfalso
    apply hcoeff
    rw [faceBoundary_apply]
    rw [mul_complement_normalized_eq_side_walk_three_path B E T ho d,
      mul_complement_normalized_eq_side_walk_three_path B E T ho (B.map.edgeInv d)]
    have hflip := ThreePathFaceLabels.side_edgeInv_of_not_seam B E d hd hi
    by_cases hb : d ∈ B.threePathBoundaryDarts P
    · have hside : ThreePathFaceLabels.side B E d = true := by
        rcases (B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mp hb with
          hp | he
        · rcases hp with hp | hp
          · exact B.side_threePathExtendedCut_imp_envelope_walk_three_path P d
              (ThreePathFaceLabels.side_path_dart B C (hCP d hp))
          · exact hflip.symm.trans
              (B.side_threePathExtendedCut_imp_envelope_walk_three_path P (B.map.edgeInv d)
                (ThreePathFaceLabels.side_path_dart B C (hCP (B.map.edgeInv d) hp)))
        · rcases he with he | he
          · exact (hd (hEP d he)).elim
          · exact (hi (hEP (B.map.edgeInv d) he)).elim
      rw [hflip, hside]
      simp only [ite_true, zero_add]
    · rw [hflip, hstep d hb]
      exact CharTwo.add_self_eq_zero _
  have hCf := congrFun hTC f
  have hEf := congrFun hTE f
  change T f * ThreePathFaceLabels.normalized B C f = 0 at hCf
  change T f * (1 - ThreePathFaceLabels.normalized B E f) = 0 at hEf
  rw [hTf, one_mul] at hCf hEf
  exact ⟨hCf, (sub_eq_zero.mp hEf).symm⟩

/-- Helper toward Definition 3.13: the internal faces of the region are
exactly the faces enclosed by the closed three-path walk, where enclosure
means separation from the marked outer face after removing its edge support. -/
theorem mem_threePathRegion_iff_not_face_reaches_outer
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (f : CombinatorialMap.FaceQuotient B.map.toCombinatorialMap) :
    f ∈ B.threePathRegion P ↔
      ¬ Relation.ReflTransGen (B.threePathFaceStep P) f
        (faceClass B.map.toCombinatorialMap B.map.outer) :=
  ⟨B.not_face_reaches_outer_of_mem_threePathRegion P f,
    B.mem_threePathRegion_of_not_face_reaches_outer P f⟩

/-- Helper toward Definition 3.13: the geometric darts of the filled
three-path submap. Both sides of every edge incident to an enclosed face
are retained, together with all marked boundary edges, including slits. -/
@[expose] noncomputable def threePathFilledDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) : Set D :=
  {d | d ∈ B.threePathBoundaryDarts P ∨
    faceClass B.map.toCombinatorialMap d ∈ B.threePathRegion P ∨
    faceClass B.map.toCombinatorialMap (B.map.edgeInv d) ∈ B.threePathRegion P}

/-- Helper toward Definition 3.13: filled edge membership is independent
of the dart representing the geometric edge. -/
theorem edgeInv_mem_threePathFilledDarts_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    B.map.edgeInv d ∈ B.threePathFilledDarts P ↔ d ∈ B.threePathFilledDarts P := by
  simp only [threePathFilledDarts, Set.mem_ofPred_eq,
    B.edgeInv_mem_threePathBoundaryDarts_iff, B.map.edgeInv_invol, or_comm]

/-- Helper toward Definition 3.13: away from the marked boundary, a filled
edge has both incident face sides inside the region. -/
theorem mem_threePathFilledDarts_iff_of_not_boundary
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D)
    (hd : d ∉ B.threePathBoundaryDarts P) :
    d ∈ B.threePathFilledDarts P ↔
      faceClass B.map.toCombinatorialMap d ∈ B.threePathRegion P ∧
        faceClass B.map.toCombinatorialMap (B.map.edgeInv d) ∈ B.threePathRegion P := by
  have hi := B.threePathRegion_face_edgeInv_iff_of_not_boundary P d hd
  change (_ ∨ _ ∨ _) ↔ _
  rw [or_iff_right hd]
  exact ⟨fun h => h.elim (fun hf => ⟨hf, hi.mp hf⟩) (fun hg => ⟨hi.mpr hg, hg⟩),
    fun h => .inl h.1⟩

/-- Helper toward Definition 3.13: the filled edge set is the marked
walk support together with the edges incident to enclosed face cycles. -/
theorem mem_threePathFilledDarts_iff_enclosed
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    d ∈ B.threePathFilledDarts P ↔ d ∈ B.threePathBoundaryDarts P ∨
      ¬ Relation.ReflTransGen (B.threePathFaceStep P)
        (faceClass B.map.toCombinatorialMap d)
        (faceClass B.map.toCombinatorialMap B.map.outer) := by
  by_cases hd : d ∈ B.threePathBoundaryDarts P
  · exact ⟨fun _ => .inl hd, fun _ => .inl hd⟩
  · rw [B.mem_threePathFilledDarts_iff_of_not_boundary P d hd, or_iff_right hd,
      ← B.mem_threePathRegion_iff_not_face_reaches_outer P]
    exact ⟨And.left, fun hf =>
      ⟨hf, (B.threePathRegion_face_edgeInv_iff_of_not_boundary P d hd).mp hf⟩⟩

/-- Helper toward Definition 3.13: geometric edge orbits in the filled
submap. Parallel edges retain their distinct edge classes. -/
@[expose] noncomputable def threePathFilledEdges
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) :
    Set (CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap) :=
  {e | ∃ d ∈ B.threePathFilledDarts P, edgeClass B.map.toCombinatorialMap d = e}

/-- Helper toward Definition 3.13: membership of any edge representative
agrees with the filled geometric dart set. -/
theorem edgeClass_mem_threePathFilledEdges_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D) :
    edgeClass B.map.toCombinatorialMap d ∈ B.threePathFilledEdges P ↔
      d ∈ B.threePathFilledDarts P := by
  constructor
  · rintro ⟨e, he, hed⟩
    have h := Quotient.exact hed
    rcases (CombinatorialMap.edgeInv_sameCycle_iff B.map.toCombinatorialMap e d).mp h with
      h | h
    · exact h ▸ he
    · rw [h]
      exact (B.edgeInv_mem_threePathFilledDarts_iff P e).mpr he
  · exact fun h => ⟨d, h, rfl⟩

/-- Helper toward Definition 3.13: vertices of the filled submap are the
vertices on either forward boundary path and all vertices incident to an
enclosed face. The path clauses retain the single vertex of an empty walk. -/
@[expose] noncomputable def threePathFilledVertices
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) : Set (MapVertex B.map) :=
  {v | v ∈ P.vertices ∨ v ∈ (B.threePathEnvelope P).vertices ∨
    ∃ d, faceClass B.map.toCombinatorialMap d ∈ B.threePathRegion P ∧
      dartTailVertex B.map d = v}

/-- Helper toward Definition 3.13: away from the marked boundary vertices,
filled vertices are exactly the vertices incident to enclosed face cycles. -/
theorem mem_threePathFilledVertices_iff_of_not_boundary
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (v : MapVertex B.map)
    (hP : v ∉ P.vertices) (hE : v ∉ (B.threePathEnvelope P).vertices) :
    v ∈ B.threePathFilledVertices P ↔
      ∃ d, (¬ Relation.ReflTransGen (B.threePathFaceStep P)
        (faceClass B.map.toCombinatorialMap d)
        (faceClass B.map.toCombinatorialMap B.map.outer)) ∧ dartTailVertex B.map d = v := by
  simp only [threePathFilledVertices, Set.mem_ofPred_eq, hP, hE, false_or,
    B.mem_threePathRegion_iff_not_face_reaches_outer]

/-- Helper toward Definition 3.13: both endpoints of a path dart are
listed vertices, with edge identity retained. -/
private theorem dart_endpoints_mem_vertices_walk_three_path
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) {d : D} (hd : d ∈ P.darts) :
    dartTailVertex M d ∈ P.vertices ∧ dartHeadVertex M d ∈ P.vertices := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hd
  exact ⟨(P.edge_step i).2.2.1 ▸ List.get_mem _ _,
    (P.edge_step i).2.2.2 ▸ List.get_mem _ _⟩

/-- Helper toward Definition 3.13: every noninitial path vertex is incident
to a path dart, including the terminal vertex. -/
private theorem path_vertex_incidence_walk_three_path
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) {v : MapVertex M} (hv : v ∈ P.vertices) :
    v = s ∨ ∃ d ∈ P.darts, dartHeadVertex M d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  by_cases hz : i.val = 0
  · exact .inl (hi.symm.trans ((congrArg P.vertices.get (Fin.ext hz)).trans P.start_vertex))
  · have hj : i.val - 1 < P.darts.length := by
      have := i.isLt
      have := P.vertices_length
      rw [P.darts_length]
      omega
    let j : Fin P.darts.length := ⟨i.val - 1, hj⟩
    refine .inr ⟨P.darts.get j, List.get_mem _ _, ?_⟩
    exact (P.edge_step j).2.2.2.symm.trans
      ((congrArg P.vertices.get (Fin.ext (by dsimp only [j]; omega))).trans hi)

/-- Helper toward Definition 3.13: every filled edge endpoint is a filled
vertex. This verifies genuine incidence closure, beyond boundary inclusion. -/
theorem dartTail_mem_threePathFilledVertices
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {d : D}
    (hd : d ∈ B.threePathFilledDarts P) :
    dartTailVertex B.map d ∈ B.threePathFilledVertices P := by
  rcases hd with hb | hf | hf
  · rcases (B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mp hb with
      hp | he
    · rcases hp with hp | hp
      · exact .inl (dart_endpoints_mem_vertices_walk_three_path P hp).1
      · exact .inl (by simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol]
          using (dart_endpoints_mem_vertices_walk_three_path P hp).2)
    · rcases he with he | he
      · exact .inr (.inl (dart_endpoints_mem_vertices_walk_three_path (B.threePathEnvelope P) he).1)
      · exact .inr (.inl (by
          simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using
            (dart_endpoints_mem_vertices_walk_three_path (B.threePathEnvelope P) he).2))
  · exact .inr (.inr ⟨d, hf, rfl⟩)
  · refine .inr (.inr ⟨B.map.toCombinatorialMap.faceSucc (B.map.edgeInv d), ?_, ?_⟩)
    · have he : faceClass B.map.toCombinatorialMap (B.map.edgeInv d) =
          faceClass B.map.toCombinatorialMap
            (B.map.toCombinatorialMap.faceSucc (B.map.edgeInv d)) :=
        Quotient.sound (Equiv.Perm.SameCycle.apply_right Equiv.Perm.SameCycle.rfl)
      exact he ▸ hf
    · simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using
        (dartHeadVertex_eq_tailVertex_faceSucc B.map (B.map.edgeInv d)).symm

/-- Helper toward Definition 3.13: incidence closure includes the head
endpoint of every filled edge. -/
theorem dartHead_mem_threePathFilledVertices
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) {d : D}
    (hd : d ∈ B.threePathFilledDarts P) :
    dartHeadVertex B.map d ∈ B.threePathFilledVertices P :=
  B.dartTail_mem_threePathFilledVertices P
    ((B.edgeInv_mem_threePathFilledDarts_iff P d).mpr hd)

/-- Helper toward Definition 3.13: the filled vertex set is exactly the
edge-endpoint set together with the marked initial vertex. This last vertex
is retained even when all three boundary portions are empty. -/
theorem mem_threePathFilledVertices_iff_incident
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (v : MapVertex B.map) :
    v ∈ B.threePathFilledVertices P ↔ v = x ∨
      ∃ d ∈ B.threePathFilledDarts P, dartTailVertex B.map d = v := by
  constructor
  · rintro (hp | he | ⟨d, hf, hd⟩)
    · rcases path_vertex_incidence_walk_three_path P hp with h | ⟨d, hd, hv⟩
      · exact .inl h
      · refine .inr ⟨B.map.edgeInv d, ?_, hv⟩
        apply (B.edgeInv_mem_threePathFilledDarts_iff P d).mpr
        exact .inl ((B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mpr
          (.inl (.inl hd)))
    · rcases path_vertex_incidence_walk_three_path (B.threePathEnvelope P) he with
        h | ⟨d, hd, hv⟩
      · exact .inl h
      · refine .inr ⟨B.map.edgeInv d, ?_, hv⟩
        apply (B.edgeInv_mem_threePathFilledDarts_iff P d).mpr
        exact .inl (B.mem_threePathBoundaryDarts_of_mem_envelope P hd)
    · exact .inr ⟨d, .inr (.inl hf), hd⟩
  · rintro (rfl | ⟨d, hd, rfl⟩)
    · exact .inl P.start_mem_vertices_three_path
    · exact B.dartTail_mem_threePathFilledVertices P hd

/-- Helper toward Definition 3.13: if the connector follows outgoing right
extremes, its cut and the envelope cut have identical normalized face labels. -/
theorem normalized_threePathExtendedCut_eq_envelope_of_out
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) :
    ThreePathFaceLabels.normalized B (B.threePathExtendedCut P) =
      ThreePathFaceLabels.normalized B
        (B.threePathExtendedCut (B.threePathEnvelope P)) := by
  let C := B.threePathExtendedCut P
  let E := B.threePathExtendedCut (B.threePathEnvelope P)
  have hrev (d : D) (hd : d ∈ C.darts) :
      ThreePathFaceLabels.side B E (B.map.edgeInv d) = false := by
    rw [threePathExtendedCut_darts] at hd
    rcases List.mem_append.mp hd with hmid | hsuffix
    · rcases List.mem_append.mp hmid with hprefix | hp
      · apply ThreePathFaceLabels.side_reverse_path_dart
        rw [threePathExtendedCut_darts]
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hprefix)))
      · exact B.side_reverse_out_path_from_cut_three_path E P hP
          (B.mem_threePathExtendedCut_vertices (B.threePathEnvelope P)
            (B.threePathEnvelope P).start_mem_vertices_three_path) hp
    · apply ThreePathFaceLabels.side_reverse_path_dart
      rw [threePathExtendedCut_darts]
      exact List.mem_append.mpr (.inr hsuffix)
  funext f
  have hback := B.normalized_nesting_of_reverse_sides_walk_three_path E C hrev f
  have hforward := B.normalized_threePathExtendedCut_eq_one_imp_envelope P f
  rcases zmod_two_eq_zero_or_one_walk_three_path (ThreePathFaceLabels.normalized B C f)
      with hc | hc
  · rcases zmod_two_eq_zero_or_one_walk_three_path (ThreePathFaceLabels.normalized B E f)
        with he | he
    · exact hc.trans he.symm
    · exact (zero_ne_one (hc.symm.trans (hback he))).elim
  · exact hc.trans (hforward hc).symm

/-- Helper toward Definition 3.13: a rightmost outgoing connector encloses
no internal faces, including zero-length connectors. -/
theorem threePathRegion_eq_empty_of_out
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) :
    B.threePathRegion P = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  have he := congrFun (B.normalized_threePathExtendedCut_eq_envelope_of_out P hP) f
  exact zero_ne_one (hf.1.symm.trans (he.trans hf.2))

/-- Helper toward Definition 3.13: a simple directed path has no repeated
darts, as follows from its vertex simplicity. -/
private theorem darts_nodup_walk_three_path
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) : P.darts.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  have hv := (P.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hij).trans (P.edge_step j).2.2.1.symm)
  exact Fin.ext (congrArg (fun q : Fin P.vertices.length => q.val)
    (P.vertices_nodup.get_inj_iff.mp hv))

/-- Helper toward Definition 3.13: for an outgoing rightmost connector,
every envelope dart is already a connector dart. -/
theorem mem_connector_of_mem_threePathEnvelope_of_out
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) {d : D}
    (hd : d ∈ (B.threePathEnvelope P).darts) : d ∈ P.darts := by
  classical
  let C := B.threePathExtendedCut P
  let E := B.threePathExtendedCut (B.threePathEnvelope P)
  have hdE : d ∈ E.darts := by
    rw [threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hd)))
  have hs (e : D) : ThreePathFaceLabels.side B C e = ThreePathFaceLabels.side B E e := by
    have heq : ThreePathFaceLabels.normalized B C = ThreePathFaceLabels.normalized B E :=
      B.normalized_threePathExtendedCut_eq_envelope_of_out P hP
    simp only [ThreePathFaceLabels.side, heq]
  have hdC : d ∈ C.darts := by
    by_contra hn
    have hi : B.map.edgeInv d ∉ C.darts := by
      intro hm
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hdE
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      have ht : B.map.tail d := hi ▸ (E.edge_step i).2.1
      exact ((B.map.tail_iff d (B.noMissingDarts d)).mp ht)
        (hj ▸ (C.edge_step j).2.1)
    have he := ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hn hi
    rw [hs, hs, ThreePathFaceLabels.side_path_dart B E hdE,
      ThreePathFaceLabels.side_reverse_path_dart B E hdE] at he
    exact Bool.false_ne_true he
  have hnd := darts_nodup_walk_three_path E
  rw [threePathExtendedCut_darts] at hnd
  have hparts := List.nodup_append.mp hnd
  have hprefix := List.nodup_append.mp hparts.1
  rw [threePathExtendedCut_darts] at hdC
  rcases List.mem_append.mp hdC with hmid | hsuffix
  · rcases List.mem_append.mp hmid with hbefore | hp
    · exact (hprefix.2.2 d hbefore d hd rfl).elim
    · exact hp
  · exact (hparts.2.2 d (List.mem_append.mpr (.inr hd)) d hsuffix rfl).elim

/-- Helper toward Definition 3.13: when the connector is rightmost
outgoing, the filled region has precisely its geometric edge support. -/
theorem mem_threePathFilledDarts_iff_of_out
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) (d : D) :
    d ∈ B.threePathFilledDarts P ↔ d ∈ P.darts ∨ B.map.edgeInv d ∈ P.darts := by
  change (_ ∨ _ ∨ _) ↔ _
  rw [B.threePathRegion_eq_empty_of_out P hP]
  simp only [Set.mem_empty_iff_false, or_false]
  rw [B.mem_threePathBoundaryDarts_iff_connector_or_envelope]
  exact ⟨fun h => h.elim id (Or.imp
    (B.mem_connector_of_mem_threePathEnvelope_of_out P hP)
    (B.mem_connector_of_mem_threePathEnvelope_of_out P hP)), Or.inl⟩

/-- Helper toward Definition 3.13: the degenerate filled region retains
exactly the connector vertices, also for the empty connector. -/
theorem mem_threePathFilledVertices_iff_of_out
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (hP : B.Out P) (v : MapVertex B.map) :
    v ∈ B.threePathFilledVertices P ↔ v ∈ P.vertices := by
  rw [B.mem_threePathFilledVertices_iff_incident]
  constructor
  · rintro (rfl | ⟨d, hd, rfl⟩)
    · exact P.start_mem_vertices_three_path
    · rcases (B.mem_threePathFilledDarts_iff_of_out P hP d).mp hd with hd | hd
      · exact (dart_endpoints_mem_vertices_walk_three_path P hd).1
      · simpa only [dartHeadVertex, dartTailVertex, B.map.edgeInv_invol] using
          (dart_endpoints_mem_vertices_walk_three_path P hd).2
  · intro hv
    rcases path_vertex_incidence_walk_three_path P hv with h | ⟨d, hd, hv⟩
    · exact .inl h
    · exact .inr ⟨B.map.edgeInv d,
        (B.mem_threePathFilledDarts_iff_of_out P hP (B.map.edgeInv d)).mpr
          (.inr (by simpa only [B.map.edgeInv_invol] using hd)), hv⟩

/-- Helper toward Definition 3.13: a connector dart belongs to a second
extended cut exactly when it belongs to that cut's connector. The common
exterior portions cannot contain it, by simplicity of its own extended cut. -/
private theorem connector_mem_extendedCut_iff_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) {d : D} (hd : d ∈ Q.darts) :
    d ∈ (B.threePathExtendedCut P).darts ↔ d ∈ P.darts := by
  have hnd := darts_nodup_walk_three_path (B.threePathExtendedCut Q)
  rw [B.threePathExtendedCut_darts] at hnd
  have hparts := List.nodup_append.mp hnd
  have hprefix := List.nodup_append.mp hparts.1
  rw [B.threePathExtendedCut_darts]
  constructor
  · intro hc
    rcases List.mem_append.mp hc with hmid | hsuffix
    · rcases List.mem_append.mp hmid with hbefore | hp
      · exact (hprefix.2.2 d hbefore d hd rfl).elim
      · exact hp
    · exact (hparts.2.2 d (List.mem_append.mpr (.inr hd)) d hsuffix rfl).elim
  · intro hp
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hp)))

/-- Helper toward Definition 3.13: a dart incident to a region face has
right-side label for the extended connector. Exterior corners are included
using the normalized product identity. -/
private theorem side_false_of_face_mem_region_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (d : D)
    (hd : faceClass B.map.toCombinatorialMap d ∈ B.threePathRegion P) :
    ThreePathFaceLabels.side B (B.threePathExtendedCut P) d = false := by
  have h := (B.mem_threePathRegion_iff_mul_eq_one P _).mp hd
  rw [normalized_mul_complement_eq_side_walk_three_path] at h
  split at h
  · rename_i hs
    exact hs.2
  · exact (zero_ne_one h).elim

/-- Helper toward Definition 3.13: for a competing directed connector,
filled edge containment is precisely weak right-side membership relative to
the first connector's cut. This does not assume geodesicity or a local
rotation characterization. -/
theorem mem_threePathFilledDarts_iff_side_of_mem_connector
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) {d : D} (hd : d ∈ Q.darts) :
    d ∈ B.threePathFilledDarts P ↔ d ∈ P.darts ∨
      ThreePathFaceLabels.side B (B.threePathExtendedCut P) d = false := by
  let C := B.threePathExtendedCut P
  let E := B.threePathExtendedCut (B.threePathEnvelope P)
  have ht : B.map.tail d := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    exact hi ▸ (Q.edge_step i).2.1
  have hrev {s t : MapVertex B.map} {k : ℕ}
      (A : SimpleDirectedDartPath B.map s t k) : B.map.edgeInv d ∉ A.darts := by
    intro hm
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact ((B.map.tail_iff d (B.noMissingDarts d)).mp ht) (hi ▸ (A.edge_step i).2.1)
  constructor
  · intro hfilled
    by_cases hp : d ∈ P.darts
    · exact .inl hp
    right
    have hc : d ∉ C.darts :=
      fun h => hp ((B.connector_mem_extendedCut_iff_walk_three_path P Q hd).mp h)
    have hflip := ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hc (hrev C)
    rcases hfilled with hb | hf | hf
    · rcases (B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mp hb with
        hp' | he
      · exact (hp'.elim hp (hrev P)).elim
      · rcases he with he | he
        · have hdE : d ∈ E.darts := by
            rw [threePathExtendedCut_darts]
            exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr he)))
          exact hflip.symm.trans (B.side_reverse_threePathExtendedEnvelope P hdE)
        · exact (hrev (B.threePathEnvelope P) he).elim
    · exact B.side_false_of_face_mem_region_walk_three_path P d hf
    · exact hflip.symm.trans
        (B.side_false_of_face_mem_region_walk_three_path P (B.map.edgeInv d) hf)
  · rintro (hp | hs)
    · exact .inl ((B.mem_threePathBoundaryDarts_iff_connector_or_envelope P d).mpr
        (.inl (.inl hp)))
    · have hdQ : d ∈ (B.threePathExtendedCut Q).darts := by
        rw [threePathExtendedCut_darts]
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hd)))
      have hE : ThreePathFaceLabels.side B E d = true :=
        B.side_threePathExtendedCut_imp_envelope_walk_three_path Q d
          (ThreePathFaceLabels.side_path_dart B (B.threePathExtendedCut Q) hdQ)
      change ThreePathFaceLabels.side B
        (B.threePathExtendedCut (B.threePathEnvelope P)) d = true at hE
      refine .inr (.inl ((B.mem_threePathRegion_iff_mul_eq_one P _).mpr ?_))
      rw [normalized_mul_complement_eq_side_walk_three_path]
      simp only [hE, hs, and_self, ite_true]

/-- Helper toward Definition 3.13: endpoint transport preserves the
vertices of a directed path. -/
private theorem transport_start_vertices_walk_three_path
    {M : DirectedMapWithMissing D} {s s' t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (h : s = s') :
    (h ▸ P : SimpleDirectedDartPath M s' t n).vertices = P.vertices := by
  cases h
  rfl

/-- Helper toward Definition 3.13: the envelope vertices are exactly the
two forward portions, including the first meeting vertex in both portions. -/
theorem mem_threePathEnvelope_vertices_iff
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (v : MapVertex B.map) :
    v ∈ (B.threePathEnvelope P).vertices ↔
      v ∈ (B.rightmostOutPath x).2.vertices.take ((B.threePathFirstMeeting P).1.val + 1) ∨
        v ∈ (B.rightmostInPath y).2.vertices.drop (B.threePathFirstMeeting P).2.val := by
  unfold threePathEnvelope
  rw [mem_append_vertices_walk_three_path, transport_start_vertices_walk_three_path,
    SimpleDirectedDartPath.prefix_vertices, SimpleDirectedDartPath.suffix_vertices]

/-- Helper toward Definition 3.13: complete vertex description of the
closed three-path submap, in terms of all three boundary portions and the
vertices incident to enclosed face cycles. Empty portions retain endpoints. -/
theorem mem_threePathFilledVertices_iff_three_portions
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (v : MapVertex B.map) :
    v ∈ B.threePathFilledVertices P ↔
      v ∈ P.vertices ∨
      v ∈ (B.rightmostOutPath x).2.vertices.take ((B.threePathFirstMeeting P).1.val + 1) ∨
      v ∈ (B.rightmostInPath y).2.vertices.drop (B.threePathFirstMeeting P).2.val ∨
      ∃ d, (¬ Relation.ReflTransGen (B.threePathFaceStep P)
        (faceClass B.map.toCombinatorialMap d)
        (faceClass B.map.toCombinatorialMap B.map.outer)) ∧ dartTailVertex B.map d = v := by
  change (_ ∨ _ ∨ _) ↔ _
  rw [B.mem_threePathEnvelope_vertices_iff]
  simp_rw [B.mem_threePathRegion_iff_not_face_reaches_outer]
  tauto

/-- Helper toward Definition 3.13: among outgoing darts at a cut vertex,
the right side is exactly the clockwise sector after its cut dart and up
to the outgoing right extreme. This includes the source rotation. -/
theorem side_false_iff_clockwise_outgoing_sector_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {n : ℕ}
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {b : D} (hb : b ∈ C.darts) (q : D) (hq : B.map.tail q)
    (hqv : dartTailVertex B.map q = dartTailVertex B.map b)
    (ht : dartTailVertex B.map b ≠ B.sink) :
    ThreePathFaceLabels.side B C q = false ↔
      q ∈ openRotationInterval_three_path B.map.rot.symm b
        (B.out (dartTailVertex B.map b) ht) ∨
      (q = B.out (dartTailVertex B.map b) ht ∧ q ≠ b) := by
  let ρ := B.map.rot.symm
  let v := dartTailVertex B.map b
  let o := B.out v ht
  have hbt : B.map.tail b := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
    exact hi ▸ (C.edge_step i).2.1
  obtain ⟨k, hk, hkmin, hktail⟩ :=
    B.outgoing_clockwise_interval_three_path v ht b rfl hbt
  obtain ⟨l, hl, hlmin, hltail⟩ :=
    B.outgoing_clockwise_interval_three_path v ht q hqv hq
  change (ρ ^ k) b = o at hk
  change (ρ ^ l) q = o at hl
  have hvertex (a : D) (j : ℕ) :
      dartTailVertex B.map ((ρ ^ j) a) = dartTailVertex B.map a := by
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_inv.mp
      (Equiv.Perm.sameCycle_pow_right.mpr
        (Equiv.Perm.SameCycle.refl B.map.rot.symm a))).symm
  have hcut (d : D) (hd : d ∈ C.darts)
      (hdv : dartTailVertex B.map d = v) : d = b := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    obtain ⟨a, ha⟩ := List.mem_iff_get.mp hb
    have he := (C.edge_step i).2.2.1.trans
      ((congrArg (dartTailVertex B.map) hi).trans
        (hdv.trans ((congrArg (dartTailVertex B.map) ha).symm.trans
          (C.edge_step a).2.2.1.symm)))
    have hia : i = a := Fin.ext (congrArg (fun z : Fin C.vertices.length => z.val)
      (C.vertices_nodup.get_inj_iff.mp he))
    exact hi.symm.trans (hia ▸ ha)
  have hstep (d : D) (hdv : dartTailVertex B.map d = v)
      (hdt : B.map.tail d) (hdb : d ≠ b) (hdo : d ≠ o) :
      ThreePathFaceLabels.side B C (ρ d) = ThreePathFaceLabels.side B C d := by
    have hinner : ¬ B.map.IsOuter (B.map.edgeInv d) := fun ho =>
      hdo (B.out_eq_of_reverse_outer_walk_three_path ht d hdv hdt ho)
    have hdC : d ∉ C.darts := fun hd => hdb (hcut d hd hdv)
    have hiC : B.map.edgeInv d ∉ C.darts := by
      intro hi
      obtain ⟨i, he⟩ := List.mem_iff_get.mp hi
      exact ((B.map.tail_iff d (B.noMissingDarts d)).mp hdt)
        (he ▸ (C.edge_step i).2.1)
    have hf := ThreePathFaceLabels.side_faceSucc_of_inner B C _ hinner
    have he := ThreePathFaceLabels.side_edgeInv_of_not_seam B C d hdC hiC
    have hface : B.map.toCombinatorialMap.faceSucc (B.map.edgeInv d) = ρ d := by
      change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv d)) = _
      rw [B.map.edgeInv_invol]
    rw [hface] at hf
    exact hf.trans he
  have hbetween (a c : D) (r s : ℕ) (hrs : r ≤ s)
      (he : (ρ ^ r) a = (ρ ^ s) c) : a = (ρ ^ (s - r)) c := by
    apply (ρ ^ r).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hrs]
    exact he
  have havoid (j : ℕ) (hj : 0 < j) (hjk : j ≤ k) : (ρ ^ j) b ≠ b := by
    intro he
    have hhit : (ρ ^ (k - j)) b = o := by
      calc
        (ρ ^ (k - j)) b = (ρ ^ (k - j)) ((ρ ^ j) b) := by rw [he]
        _ = (ρ ^ k) b := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk]
        _ = o := hk
    exact hkmin (k - j) (by omega) hhit
  have hfalse : ∀ j, 0 < j → j ≤ k →
      ThreePathFaceLabels.side B C ((ρ ^ j) b) = false := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro _ hj
      by_cases hz : j = 0
      · subst j
        have hinner : ¬ B.map.IsOuter (B.map.edgeInv b) := by
          intro ho
          have hbo := B.out_eq_of_reverse_outer_walk_three_path ht b rfl hbt ho
          exact hkmin 0 (by omega) (by simpa only [pow_zero, Equiv.Perm.one_apply])
        have hf := ThreePathFaceLabels.side_faceSucc_of_inner B C _ hinner
        have hface : B.map.toCombinatorialMap.faceSucc (B.map.edgeInv b) = ρ b := by
          change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv b)) = _
          rw [B.map.edgeInv_invol]
        rw [hface] at hf
        simpa only [Nat.zero_add, pow_one] using hf.trans
          (ThreePathFaceLabels.side_reverse_path_dart B C hb)
      · have hs := hstep ((ρ ^ j) b) (hvertex b j) (hktail j (by omega))
          (havoid j (by omega) (by omega)) (hkmin j (by omega))
        simpa only [pow_succ', Equiv.Perm.mul_apply] using
          hs.trans (ih (by omega) (by omega))
  have htrue (hkl : k ≤ l) : ThreePathFaceLabels.side B C q = true := by
    have hqb : (ρ ^ (l - k)) q = b :=
      (hbetween b q k l hkl (hk.trans hl.symm)).symm
    have hseq : ∀ j, j ≤ l - k →
        ThreePathFaceLabels.side B C ((ρ ^ j) q) = ThreePathFaceLabels.side B C q := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hdb : (ρ ^ j) q ≠ b := by
          intro he
          have hhit : (ρ ^ (k + j)) q = o := by
            rw [pow_add, Equiv.Perm.mul_apply, he, hk]
          exact hlmin (k + j) (by omega) hhit
        have hs := hstep ((ρ ^ j) q) ((hvertex q j).trans hqv)
          (hltail j (by omega)) hdb (hlmin j (by omega))
        simpa only [pow_succ', Equiv.Perm.mul_apply] using hs.trans (ih (by omega))
    have he := hseq (l - k) le_rfl
    rw [hqb, ThreePathFaceLabels.side_path_dart B C hb] at he
    exact he.symm
  constructor
  · intro hs
    have hlk : l < k := by
      by_contra hn
      have he := htrue (by omega)
      rw [hs] at he
      cases he
    have hqeq := hbetween q b l k (by omega) (hl.trans hk.symm)
    by_cases hlzero : l = 0
    · right
      have hqo : q = o := by simpa only [hlzero, pow_zero, Equiv.Perm.one_apply] using hl
      exact ⟨hqo, fun he => by
        have hside := ThreePathFaceLabels.side_path_dart B C hb
        rw [← he, hs] at hside
        cases hside⟩
    · left
      exact ⟨k, hk, hkmin, k - l, by omega, by omega, hqeq.symm⟩
  · rintro (⟨k', hk', hkmin', j, hj, hjk, hjq⟩ | ⟨hqo, hqb⟩)
    · have hkeq : k' = k := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with hlt | hgt
        · exact hkmin k' hlt hk'
        · exact hkmin' k hgt hk
      subst k'
      exact hjq ▸ hfalse j hj (by omega)
    · have hkpos : 0 < k := by
        by_contra hn
        have hkzero : k = 0 := by omega
        have hbo : b = o := by simpa only [hkzero, pow_zero, Equiv.Perm.one_apply] using hk
        exact hqb (hqo.trans hbo.symm)
      change ThreePathFaceLabels.side B C q = false
      change q = o at hqo
      rw [hqo, ← hk]
      exact hfalse k hkpos le_rfl

/-- Helper toward Definition 3.13: the outgoing false-side sector at a
connector dart is the same sector for its canonical source-to-sink cut. -/
theorem side_false_iff_clockwise_sector_threePathExtendedCut
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map x y n) (i : Fin P.darts.length)
    (q : D) (hq : B.map.tail q)
    (hqv : dartTailVertex B.map q = dartTailVertex B.map (P.darts.get i))
    (ht : dartTailVertex B.map (P.darts.get i) ≠ B.sink) :
    ThreePathFaceLabels.side B (B.threePathExtendedCut P) q = false ↔
      q ∈ openRotationInterval_three_path B.map.rot.symm (P.darts.get i)
        (B.out (dartTailVertex B.map (P.darts.get i)) ht) ∨
      (q = B.out (dartTailVertex B.map (P.darts.get i)) ht ∧ q ≠ P.darts.get i) := by
  apply B.side_false_iff_clockwise_outgoing_sector_three_path
    (B.threePathExtendedCut P) ?_ q hq hqv ht
  rw [B.threePathExtendedCut_darts]
  exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr (List.get_mem _ i))))

/-- Helper toward Definition 3.13: a simple path has at most one departure
dart at any vertex, retaining the identities of parallel edges. -/
private theorem eq_of_mem_darts_same_tail_walk_three_path
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) {a b : D}
    (ha : a ∈ P.darts) (hb : b ∈ P.darts)
    (hv : dartTailVertex M a = dartTailVertex M b) : a = b := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have he := (P.edge_step i).2.2.1.trans
    ((congrArg (dartTailVertex M) hi).trans
      (hv.trans ((congrArg (dartTailVertex M) hj).symm.trans
        (P.edge_step j).2.2.1.symm)))
  have hij : i = j := Fin.ext (congrArg (fun z : Fin P.vertices.length => z.val)
    (P.vertices_nodup.get_inj_iff.mp he))
  exact hi.symm.trans (hij ▸ hj)

/-- Helper toward Definition 3.13: a competing connector cannot depart
from an exterior portion of the extended cut. Its shared departure vertex
has the first connector's own departure dart. -/
private theorem cut_departure_mem_connector_walk_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) {q b : D}
    (hq : q ∈ Q.darts) (hb : b ∈ (B.threePathExtendedCut P).darts)
    (hv : dartTailVertex B.map b = dartTailVertex B.map q) : b ∈ P.darts := by
  by_cases hp : b ∈ P.darts
  · exact hp
  have hbQ : b ∈ (B.threePathExtendedCut Q).darts := by
    rw [B.threePathExtendedCut_darts] at hb ⊢
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hb)))
      · exact (hp hb).elim
    · exact List.mem_append.mpr (.inr hb)
  have hqQ : q ∈ (B.threePathExtendedCut Q).darts := by
    rw [B.threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hq)))
  have he := eq_of_mem_darts_same_tail_walk_three_path
    (B.threePathExtendedCut Q) hbQ hqQ hv
  rw [he]
  exact (B.connector_mem_extendedCut_iff_walk_three_path P Q hq).mp (he ▸ hb)

/-- Helper toward Definition 3.13: a competing connector is wholly in
the closed three-path region exactly when all its departures at connector
vertices use the same dart or its clockwise outgoing right sector. Between
contacts, side consistency propagates containment without extra premises. -/
theorem connector_subset_threePathFilledDarts_iff_clockwise_departures
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) :
    (∀ q ∈ Q.darts, q ∈ B.threePathFilledDarts P) ↔
      ∀ (i : Fin P.darts.length) (q : D), q ∈ Q.darts →
        dartTailVertex B.map q = dartTailVertex B.map (P.darts.get i) →
        ∀ ht : dartTailVertex B.map (P.darts.get i) ≠ B.sink,
          q = P.darts.get i ∨
          q ∈ openRotationInterval_three_path B.map.rot.symm (P.darts.get i)
            (B.out (dartTailVertex B.map (P.darts.get i)) ht) ∨
          (q = B.out (dartTailVertex B.map (P.darts.get i)) ht ∧
            q ≠ P.darts.get i) := by
  let C := B.threePathExtendedCut P
  have htail {q : D} (hq : q ∈ Q.darts) : B.map.tail q := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    exact hi ▸ (Q.edge_step i).2.1
  constructor
  · intro h i q hq hqv ht
    rcases (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q hq).mp (h q hq) with
      hp | hs
    · exact .inl (eq_of_mem_darts_same_tail_walk_three_path P hp
        (List.get_mem _ i) hqv)
    · exact .inr ((B.side_false_iff_clockwise_sector_threePathExtendedCut
        P i q (htail hq) hqv ht).mp hs)
  · intro hright
    have hatcut (q : D) (hq : q ∈ Q.darts)
        (hv : dartTailVertex B.map q ∈ C.vertices) :
        q ∈ B.threePathFilledDarts P := by
      have ht : dartTailVertex B.map q ≠ B.sink := by
        intro he
        exact B.sink_rotation_all_incoming.1 q he (htail hq)
      obtain ⟨b, hb, hbv⟩ := B.exists_departure_cut_walk_three_path C hv ht
      have hbp := B.cut_departure_mem_connector_walk_three_path P Q hq hb hbv
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hbp
      have hqv : dartTailVertex B.map q = dartTailVertex B.map (P.darts.get i) :=
        hbv.symm.trans (congrArg (dartTailVertex B.map) hi.symm)
      have hti : dartTailVertex B.map (P.darts.get i) ≠ B.sink :=
        fun he => ht (hqv.trans he)
      apply (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q hq).mpr
      rcases hright i q hq hqv hti with he | hs
      · exact .inl (he ▸ List.get_mem _ i)
      · exact .inr ((B.side_false_iff_clockwise_sector_threePathExtendedCut
          P i q (htail hq) hqv hti).mpr hs)
    have hmain : ∀ j : ℕ, ∀ hj : j < Q.darts.length,
        Q.darts.get ⟨j, hj⟩ ∈ B.threePathFilledDarts P := by
      intro j
      induction j with
      | zero =>
        intro hj
        apply hatcut _ (List.get_mem _ _)
        have hv : dartTailVertex B.map (Q.darts.get ⟨0, hj⟩) = x :=
          (Q.edge_step ⟨0, hj⟩).2.2.1.symm.trans Q.start_vertex
        rw [hv]
        exact B.mem_threePathExtendedCut_vertices P
          (P.start_mem_vertices_three_path)
      | succ j ih =>
        intro hj
        let d := Q.darts.get ⟨j + 1, hj⟩
        have hd : d ∈ Q.darts := List.get_mem _ _
        by_cases hv : dartTailVertex B.map d ∈ C.vertices
        · exact hatcut d hd hv
        have hjprev : j < Q.darts.length := by omega
        let e := Q.darts.get ⟨j, hjprev⟩
        have he : e ∈ Q.darts := List.get_mem _ _
        have hev : dartHeadVertex B.map e = dartTailVertex B.map d :=
          (Q.edge_step ⟨j, hjprev⟩).2.2.2.symm.trans
            (Q.edge_step ⟨j + 1, hj⟩).2.2.1
        have heside : ThreePathFaceLabels.side B C e = false := by
          rcases (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q he).mp
            (ih hjprev) with hep | hs
          · have heC : e ∈ C.darts := by
              rw [B.threePathExtendedCut_darts]
              exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hep)))
            exact (hv (hev ▸ (dart_endpoints_mem_vertices_walk_three_path C heC).2)).elim
          · exact hs
        have hflip := ThreePathFaceLabels.side_edgeInv_of_endpoint_not_mem B C e
          (.inr (by rw [hev]; exact hv))
        have hs := ThreePathFaceLabels.side_eq_of_sameTail B C rfl hev hv
        have hdside : ThreePathFaceLabels.side B C d = false :=
          hs.trans (hflip.trans heside)
        exact (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q hd).mpr
          (.inr hdside)
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    exact hi ▸ hmain i.val i.isLt

/-- Helper toward Definition 3.13: the departure criterion describes the
entire connector submap, including its vertices and a zero-length path. -/
theorem connector_subset_threePathFilledSubmap_iff_clockwise_departures
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) :
    ((∀ q ∈ Q.darts, q ∈ B.threePathFilledDarts P) ∧
      (∀ v ∈ Q.vertices, v ∈ B.threePathFilledVertices P)) ↔
      ∀ (i : Fin P.darts.length) (q : D), q ∈ Q.darts →
        dartTailVertex B.map q = dartTailVertex B.map (P.darts.get i) →
        ∀ ht : dartTailVertex B.map (P.darts.get i) ≠ B.sink,
          q = P.darts.get i ∨
          q ∈ openRotationInterval_three_path B.map.rot.symm (P.darts.get i)
            (B.out (dartTailVertex B.map (P.darts.get i)) ht) ∨
          (q = B.out (dartTailVertex B.map (P.darts.get i)) ht ∧
            q ≠ P.darts.get i) := by
  rw [← B.connector_subset_threePathFilledDarts_iff_clockwise_departures P Q]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro v hv
    rcases path_vertex_incidence_walk_three_path Q hv with he | ⟨d, hd, he⟩
    · rw [he]
      exact (B.mem_threePathFilledVertices_iff_incident P x).mpr (.inl rfl)
    · rw [← he]
      exact B.dartHead_mem_threePathFilledVertices P (h d hd)

/-- Helper toward Definition 3.13: two distinct outgoing departures at
one vertex cannot both be strictly on the right of each other's extended
connector cuts. The common outgoing extreme cuts the cyclic order. -/
theorem not_mutually_right_departures_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m) {p q : D}
    (hp : p ∈ P.darts) (hq : q ∈ Q.darts)
    (hv : dartTailVertex B.map q = dartTailVertex B.map p)
    (hPq : ThreePathFaceLabels.side B (B.threePathExtendedCut P) q = false)
    (hQp : ThreePathFaceLabels.side B (B.threePathExtendedCut Q) p = false) : False := by
  have hpt : B.map.tail p := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    exact hi ▸ (P.edge_step i).2.1
  have hqt : B.map.tail q := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    exact hi ▸ (Q.edge_step i).2.1
  have ht : dartTailVertex B.map p ≠ B.sink :=
    fun he => B.sink_rotation_all_incoming.1 p he hpt
  have htq : dartTailVertex B.map q ≠ B.sink := fun he => ht (hv.symm.trans he)
  have hpC : p ∈ (B.threePathExtendedCut P).darts := by
    rw [B.threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hp)))
  have hqC : q ∈ (B.threePathExtendedCut Q).darts := by
    rw [B.threePathExtendedCut_darts]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hq)))
  have hqsector := (B.side_false_iff_clockwise_outgoing_sector_three_path
    (B.threePathExtendedCut P) hpC q hqt hv ht).mp hPq
  have hpsector := (B.side_false_iff_clockwise_outgoing_sector_three_path
    (B.threePathExtendedCut Q) hqC p hpt hv.symm htq).mp hQp
  let ρ := B.map.rot.symm
  let o := B.out (dartTailVertex B.map p) ht
  change q ∈ openRotationInterval_three_path ρ p o ∨ (q = o ∧ q ≠ p) at hqsector
  have hpsector' : p ∈ openRotationInterval_three_path ρ q o ∨ (p = o ∧ p ≠ q) := by
    simpa only [hv] using hpsector
  obtain ⟨k, hk, hkmin, _⟩ := B.outgoing_clockwise_interval_three_path
    (dartTailVertex B.map p) ht p rfl hpt
  obtain ⟨l, hl, hlmin, _⟩ := B.outgoing_clockwise_interval_three_path
    (dartTailVertex B.map p) ht q hv hqt
  have horder (a c : D) (k l : ℕ) (hk : (ρ ^ k) a = o)
      (hkmin : ∀ j < k, (ρ ^ j) a ≠ o) (hl : (ρ ^ l) c = o)
      (hlmin : ∀ j < l, (ρ ^ j) c ≠ o)
      (hs : c ∈ openRotationInterval_three_path ρ a o ∨ (c = o ∧ c ≠ a)) : l < k := by
    rcases hs with ⟨k', hk', hkmin', j, hj, hjk, hjc⟩ | ⟨hco, hca⟩
    · have hkeq : k' = k := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with hlt | hgt
        · exact hkmin k' hlt hk'
        · exact hkmin' k hgt hk
      subst k'
      have hhit : (ρ ^ (k - j)) c = o := by
        rw [← hjc, ← Equiv.Perm.mul_apply, ← pow_add,
          Nat.sub_add_cancel (by omega : j ≤ k), hk]
      have hle : l ≤ k - j := by
        by_contra hn
        exact hlmin (k - j) (by omega) hhit
      omega
    · have hlzero : l = 0 := by
        by_contra hn
        exact hlmin 0 (by omega) (by simpa only [pow_zero, Equiv.Perm.one_apply] using hco)
      have hkpos : 0 < k := by
        by_contra hn
        have hkzero : k = 0 := by omega
        have hao : a = o := by simpa only [hkzero, pow_zero, Equiv.Perm.one_apply] using hk
        exact hca (hco.trans hao.symm)
      omega
  have hfirst := horder p q k l hk hkmin hl hlmin hqsector
  have hsecond := horder q p l k hl hlmin hk hkmin hpsector'
  omega

/-- Helper toward Definition 3.13: weak-right containment of directed
connectors is antisymmetric, for arbitrary endpoints and lengths. -/
theorem darts_eq_of_mutual_threePathFilledDarts
    (B : BipolarMapWithBoundaryBase D ℓ r) {x y : MapVertex B.map} {n m : ℕ}
    (P : SimpleDirectedDartPath B.map x y n)
    (Q : SimpleDirectedDartPath B.map x y m)
    (hPQ : ∀ q ∈ Q.darts, q ∈ B.threePathFilledDarts P)
    (hQP : ∀ p ∈ P.darts, p ∈ B.threePathFilledDarts Q) : P.darts = Q.darts := by
  have hget : ∀ j : ℕ, ∀ (hjP : j < P.darts.length) (hjQ : j < Q.darts.length),
      P.darts.get ⟨j, hjP⟩ = Q.darts.get ⟨j, hjQ⟩ := by
    intro j
    induction j with
    | zero =>
      intro hjP hjQ
      have hv : dartTailVertex B.map (Q.darts.get ⟨0, hjQ⟩) =
          dartTailVertex B.map (P.darts.get ⟨0, hjP⟩) :=
        (Q.edge_step ⟨0, hjQ⟩).2.2.1.symm.trans
          (Q.start_vertex.trans (P.start_vertex.symm.trans (P.edge_step ⟨0, hjP⟩).2.2.1))
      by_contra hn
      have hp := List.get_mem P.darts ⟨0, hjP⟩
      have hq := List.get_mem Q.darts ⟨0, hjQ⟩
      have hsP := (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q hq).mp
        (hPQ _ hq)
      have hsQ := (B.mem_threePathFilledDarts_iff_side_of_mem_connector Q P hp).mp
        (hQP _ hp)
      have hsP' := hsP.resolve_left (fun hm => hn
        (eq_of_mem_darts_same_tail_walk_three_path P hm hp hv).symm)
      have hsQ' := hsQ.resolve_left (fun hm => hn
        (eq_of_mem_darts_same_tail_walk_three_path Q hm hq hv.symm))
      exact B.not_mutually_right_departures_three_path P Q hp hq hv hsP' hsQ'
    | succ j ih =>
      intro hjP hjQ
      have hjP' : j < P.darts.length := by omega
      have hjQ' : j < Q.darts.length := by omega
      have he := ih hjP' hjQ'
      have hv : dartTailVertex B.map (Q.darts.get ⟨j + 1, hjQ⟩) =
          dartTailVertex B.map (P.darts.get ⟨j + 1, hjP⟩) :=
        (Q.edge_step ⟨j + 1, hjQ⟩).2.2.1.symm.trans
          ((Q.edge_step ⟨j, hjQ'⟩).2.2.2.trans
            ((congrArg (dartHeadVertex B.map) he.symm).trans
              ((P.edge_step ⟨j, hjP'⟩).2.2.2.symm.trans
                (P.edge_step ⟨j + 1, hjP⟩).2.2.1)))
      by_contra hn
      have hp := List.get_mem P.darts ⟨j + 1, hjP⟩
      have hq := List.get_mem Q.darts ⟨j + 1, hjQ⟩
      have hsP := (B.mem_threePathFilledDarts_iff_side_of_mem_connector P Q hq).mp
        (hPQ _ hq)
      have hsQ := (B.mem_threePathFilledDarts_iff_side_of_mem_connector Q P hp).mp
        (hQP _ hp)
      have hsP' := hsP.resolve_left (fun hm => hn
        (eq_of_mem_darts_same_tail_walk_three_path P hm hp hv).symm)
      have hsQ' := hsQ.resolve_left (fun hm => hn
        (eq_of_mem_darts_same_tail_walk_three_path Q hm hq hv.symm))
      exact B.not_mutually_right_departures_three_path P Q hp hq hv hsP' hsQ'
  have hvertex : ∀ (i : ℕ) (_hiP : i ≤ n) (_hiQ : i ≤ m),
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ =
        Q.vertices.get ⟨i, by rw [Q.vertices_length]; omega⟩ := by
    intro i hiP hiQ
    cases i with
    | zero => exact P.start_vertex.trans Q.start_vertex.symm
    | succ i =>
      have hiPd : i < P.darts.length := by rw [P.darts_length]; omega
      have hiQd : i < Q.darts.length := by rw [Q.darts_length]; omega
      exact (P.edge_step ⟨i, hiPd⟩).2.2.2.trans
        ((congrArg (dartHeadVertex B.map) (hget i hiPd hiQd)).trans
          (Q.edge_step ⟨i, hiQd⟩).2.2.2.symm)
  have hnm : n = m := by
    rcases Nat.le_total n m with hle | hle
    · have he := (hvertex n le_rfl hle).symm.trans P.end_vertex
      have he' := Q.vertices_nodup.get_inj_iff.mp (he.trans Q.end_vertex.symm)
      exact congrArg (fun z : Fin Q.vertices.length => z.val) he'
    · have he := (hvertex m hle le_rfl).trans Q.end_vertex
      have he' := P.vertices_nodup.get_inj_iff.mp (he.trans P.end_vertex.symm)
      exact (congrArg (fun z : Fin P.vertices.length => z.val) he').symm
  apply List.ext_get_iff.mpr
  exact ⟨by rw [P.darts_length, Q.darts_length, hnm], hget⟩

/-- Helper toward Definition 3.13: equal-length extremal connectors visit
a common vertex at the same index. Both cross-splices are simple by
acyclicity, so different indices would improve one of the two lengths. -/
theorem extremal_connector_common_indices_eq_three_path
    (B : BipolarMapWithBoundaryBase D ℓ r) (choice : XDP)
    {x y : MapVertex B.map} {n : ℕ}
    (P Q : SimpleDirectedDartPath B.map x y n)
    (hP : match choice with
      | .ldp => ∀ {m : ℕ} (_R : SimpleDirectedDartPath B.map x y m), m ≤ n
      | .sdp => ∀ {m : ℕ} (_R : SimpleDirectedDartPath B.map x y m), n ≤ m)
    (i j : Fin (n + 1))
    (hv : P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩ =
      Q.vertices.get ⟨j.val, by rw [Q.vertices_length]; exact j.isLt⟩) : i = j := by
  let QS := Q.suffix j
  let S : SimpleDirectedDartPath B.map
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; exact i.isLt⟩) y (n - j.val) :=
    { QS with start_vertex := QS.start_vertex.trans hv.symm }
  let PS := P.suffix i
  let T : SimpleDirectedDartPath B.map
      (Q.vertices.get ⟨j.val, by rw [Q.vertices_length]; exact j.isLt⟩) y (n - i.val) :=
    { PS with start_vertex := PS.start_vertex.trans hv }
  let R := (P.prefix i).appendAcyclic B.map B.acyclic S
  let U := (Q.prefix j).appendAcyclic B.map B.acyclic T
  have hi : i.val ≤ n := by have := i.isLt; omega
  have hj : j.val ≤ n := by have := j.isLt; omega
  apply Fin.ext
  cases choice with
  | ldp =>
    have hR := hP R
    have hU := hP U
    change i.val + (n - j.val) ≤ n at hR
    change j.val + (n - i.val) ≤ n at hU
    omega
  | sdp =>
    have hR := hP R
    have hU := hP U
    change n ≤ i.val + (n - j.val) at hR
    change n ≤ j.val + (n - i.val) at hU
    omega









































































end BipolarMapWithBoundaryBase
end DirectedDistances.PlanarMap

