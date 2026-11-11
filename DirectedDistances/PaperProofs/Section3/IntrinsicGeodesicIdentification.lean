/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBusemannIdentification
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart3
public import DirectedDistances.PaperProofs.Section3.UIBOTQualifierPart1

/-! # Edge geodesics on geometric representatives

Helpers toward Proposition 3.9, with finite-segment conventions from
Every edge is retained as an individual geometric edge. The results about
image cuts do not remove the intrinsic-object qualifications. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open DirectedDistances.Paper.Section4
open DirectedDistances.RandomWalk MeasureTheory Filter
open scoped Classical

/-- Helper toward Proposition 3.9: a ray of retained present edges in the
representative itself, with its directed endpoints and starting vertex. -/
structure IntrinsicInfiniteDirectedPath (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (x : A.V) where
  /-- Helper toward Proposition 3.9: individual oriented geometric edges. -/
  edge : ℕ → {e : A.E // ¬ A.map.missing e}
  /-- Helper toward Proposition 3.9: every edge is retained by the cut. -/
  retained : ∀ n, (edge n).val ∈ S.edges
  /-- Helper toward Proposition 3.9: no edge has an additional missing tag. -/
  present : ∀ n, ¬ S.missing (edge n).val
  /-- Helper toward Proposition 3.9: the prescribed starting vertex. -/
  start : A.map.tail (edge 0) = x
  /-- Helper toward Proposition 3.9: the complete ordered edge chain. -/
  chain : ∀ n, A.map.head (edge n) = A.map.tail (edge (n + 1))

namespace IntrinsicInfiniteDirectedPath

variable {A : D39DomainRootedMap.{0}} {S : IntrinsicBusemannCut A} {x : A.V}

/-- Helper toward Proposition 3.9: the vertex after `n` traversed edges. -/
@[expose] def vertex (P : IntrinsicInfiniteDirectedPath A S x) (n : ℕ) : A.V :=
  A.map.tail (P.edge n)

/-- Helper toward Proposition 3.9: equality of edge streams determines a
ray, without identifying parallel edges with the same endpoints. -/
theorem edge_ext {P Q : IntrinsicInfiniteDirectedPath A S x}
    (he : ∀ n, (P.edge n).val = (Q.edge n).val) : P = Q := by
  have h : P.edge = Q.edge := funext (fun n => Subtype.ext (he n))
  cases P
  cases Q
  cases h
  rfl

/-- Helper toward Proposition 3.9: every finite consecutive segment is an
actual intrinsic edge-list path, of exactly its number of edges. -/
theorem segment_path (P : IntrinsicInfiniteDirectedPath A S x) (i n : ℕ) :
    IntrinsicDirectedEdgeListPath A S.edges S.missing
      (P.vertex i) (P.vertex (i + n))
      (List.ofFn (fun j : Fin n => (P.edge (i + j.val)).val)) := by
  induction n with
  | zero => simpa only [Nat.add_zero, List.ofFn_zero] using
      (IntrinsicDirectedEdgeListPath.nil (A := A) (S := S.edges)
        (missing := S.missing) (P.vertex i))
  | succ n ih =>
    rw [List.ofFn_succ']
    simpa only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append,
      Nat.add_assoc, IntrinsicInfiniteDirectedPath.vertex, P.chain] using
      (ih.snoc (P.edge (i + n)) (P.retained _) (P.present _) rfl)

/-- Helper toward Proposition 3.9: every finite segment realizes its
length in the representative's full set of reachable lengths. -/
theorem segment_length_mem (P : IntrinsicInfiniteDirectedPath A S x) (i n : ℕ) :
    n ∈ intrinsicDirectedReachableLengths A S.edges S.missing
      (P.vertex i) (P.vertex (i + n)) :=
  ⟨_, P.segment_path i n, List.length_ofFn⟩

/-- Helper toward Proposition 3.9: every nonempty segment is extremal
against all intrinsic finite edge-list competitors (Definition 4.5).
`true` denotes LDP and `false` denotes SDP. -/
@[expose] def HasOptimalSegments (P : IntrinsicInfiniteDirectedPath A S x)
    (longest : Bool) : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a ≤ b → ∀ n : ℕ,
    n ∈ intrinsicDirectedReachableLengths A S.edges S.missing
      (P.vertex (a - 1)) (P.vertex b) →
    if longest then n ≤ b + 1 - a else b + 1 - a ≤ n

/-- Helper toward Proposition 3.9: every nonempty SDP segment realizes
the finite intrinsic SDP between its own endpoints. -/
theorem sdp_segment_distance (P : IntrinsicInfiniteDirectedPath A S x)
    (hP : P.HasOptimalSegments false) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    intrinsicDirectedSDP A S.edges S.missing (P.vertex (a - 1)) (P.vertex b) =
      (b + 1 - a : ℕ) := by
  have he : a - 1 + (b + 1 - a) = b := by omega
  have hm := P.segment_length_mem (a - 1) (b + 1 - a)
  rw [he] at hm
  apply le_antisymm
  · exact iInf_le_of_le (b + 1 - a) (iInf_le_of_le hm le_rfl)
  · apply le_iInf
    intro n
    apply le_iInf
    intro hn
    exact_mod_cast hP a b ha hab n hn

/-- Helper toward Proposition 3.9: every nonempty LDP segment realizes
a finite intrinsic LDP, so neither unboundedness nor unreachable values are
silently converted to a natural distance. -/
theorem ldp_segment_distance (P : IntrinsicInfiniteDirectedPath A S x)
    (hP : P.HasOptimalSegments true) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    intrinsicDirectedLDP A S.edges S.missing (P.vertex (a - 1)) (P.vertex b) =
      (((b + 1 - a : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have he : a - 1 + (b + 1 - a) = b := by omega
  have hm := P.segment_length_mem (a - 1) (b + 1 - a)
  rw [he] at hm
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro hn
    exact_mod_cast hP a b ha hab n hn
  · exact le_iSup_of_le (b + 1 - a) (le_iSup_of_le hm le_rfl)

end IntrinsicInfiniteDirectedPath

/-- Helper toward Proposition 3.9: an intrinsic infinite XDP geodesic is
a ray whose actual finite edge segments are optimal in its image cut. -/
@[expose] def IntrinsicInfiniteXDPGeodesic (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (x : A.V) (longest : Bool) :=
  {P : IntrinsicInfiniteDirectedPath A S x // P.HasOptimalSegments longest}

/-- Helper toward Proposition 3.9: equality of complete edge tails at
specified offsets, retaining geometric edge identity. -/
@[expose] def IntrinsicEdgeTailsCoalesce {A : D39DomainRootedMap.{0}}
    {S : IntrinsicBusemannCut A} {x y : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (Q : IntrinsicInfiniteDirectedPath A S y)
    (a b : ℕ) : Prop := ∀ n, (P.edge (a + n)).val = (Q.edge (b + n)).val

/-- Helper toward Proposition 3.9: coordinatewise least edge-coalescence
offsets, with the same leastness quantifiers as `eqn-coalesce`. -/
@[expose] def IntrinsicLeastEdgeCoalescence {A : D39DomainRootedMap.{0}}
    {S : IntrinsicBusemannCut A} {x y : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (Q : IntrinsicInfiniteDirectedPath A S y)
    (a b : ℕ) : Prop :=
  IntrinsicEdgeTailsCoalesce P Q a b ∧
    ∀ i j, IntrinsicEdgeTailsCoalesce P Q i j → a ≤ i ∧ b ≤ j

/-- Helper toward Proposition 3.9: a least pair of intrinsic edge-tail
offsets is unique in both coordinates. -/
theorem intrinsicLeastEdgeCoalescence_unique {A : D39DomainRootedMap.{0}}
    {S : IntrinsicBusemannCut A} {x y : A.V}
    {P : IntrinsicInfiniteDirectedPath A S x} {Q : IntrinsicInfiniteDirectedPath A S y}
    {a b c d : ℕ} (hab : IntrinsicLeastEdgeCoalescence P Q a b)
    (hcd : IntrinsicLeastEdgeCoalescence P Q c d) : a = c ∧ b = d :=
  ⟨le_antisymm (hab.2 c d hcd.1).1 (hcd.2 a b hab.1).1,
    le_antisymm (hab.2 c d hcd.1).2 (hcd.2 a b hab.1).2⟩

/-- Helper toward Proposition 3.9: adjacent edge-tail coalescence of an
integer-indexed family implies coalescence of every pair of its rays. -/
theorem intrinsicEdgeTailsCoalesce_pairwise {A : D39DomainRootedMap.{0}}
    {S : IntrinsicBusemannCut A} {x : ℤ → A.V}
    (P : ∀ k : ℤ, IntrinsicInfiniteDirectedPath A S (x k))
    (hadj : ∀ k : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P (k - 1)) (P k) a b) :
    ∀ k k' : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k) (P k') a b := by
  let R (k j : ℤ) := ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k) (P j) a b
  have hr (k : ℤ) : R k k := ⟨0, 0, fun _ => rfl⟩
  have hs {k j : ℤ} : R k j → R j k := by
    rintro ⟨a, b, h⟩
    exact ⟨b, a, fun n => (h n).symm⟩
  have ht {k j l : ℤ} : R k j → R j l → R k l := by
    rintro ⟨a, b, hab⟩ ⟨c, d, hcd⟩
    refine ⟨a + c, d + b, fun n => ?_⟩
    have h₁ := hab (c + n)
    have h₂ := hcd (b + n)
    rw [Nat.add_left_comm c b n] at h₂
    simpa only [Nat.add_assoc] using h₁.trans h₂
  have hz (k : ℤ) : R 0 k := by
    induction k using Int.induction_on with
    | zero => exact hr 0
    | succ k hk =>
      apply ht hk
      have he : (k : ℤ) + 1 - 1 = (k : ℤ) := by omega
      exact (congrArg (fun j : ℤ => R j ((k : ℤ) + 1)) he).mp (hadj ((k : ℤ) + 1))
    | pred k hk => exact ht hk (hs (hadj (-(k : ℤ))))
  exact fun k k' => ht (hs (hz k)) (hz k')

/-- Helper toward Proposition 3.9: the complete geometric trace of an
edge ray, including every point on every traversed edge arc. -/
@[expose] def intrinsicEdgeRayTrace (A : D39DomainRootedMap.{0})
    (e : ℕ → A.E) : Set ℂ := ⋃ n, Set.range (A.map.arc (e n))

section Transport

variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: the image of specified cut data under
the actual vertex and edge bijections. -/
@[expose] def intrinsicGeodesicMapCut (S : IntrinsicBusemannCut A) :
    IntrinsicBusemannCut B where
  vertices := I.vertexEquiv '' S.vertices
  edges := I.edgeEquiv '' S.edges
  missing e := S.missing (I.edgeEquiv.symm e)

/-- Helper toward Proposition 3.9: transport an entire ray edge by edge,
preserving its directed chain and both sorts of missing tags. -/
@[expose] def intrinsicInfiniteDirectedPathMap {S : IntrinsicBusemannCut A} {x : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) :
    IntrinsicInfiniteDirectedPath B (intrinsicGeodesicMapCut I S) (I.vertexEquiv x) where
  edge n := ⟨I.edgeEquiv (P.edge n).val,
    fun hm => (P.edge n).property ((I.missing_map _).mp hm)⟩
  retained n := ⟨_, P.retained n, rfl⟩
  present n := by simpa only [intrinsicGeodesicMapCut, Equiv.symm_apply_apply]
    using P.present n
  start := (intrinsicDirected_tail_map I (P.edge 0)).symm.trans
    (congrArg I.vertexEquiv P.start)
  chain n := (intrinsicDirected_head_map I (P.edge n)).symm.trans
    ((congrArg I.vertexEquiv (P.chain n)).trans (intrinsicDirected_tail_map I _))

/-- Helper toward Proposition 3.9: ray transport also preserves every
vertex, as a consequence of preserving individual edges and oriented tails. -/
theorem intrinsicInfiniteDirectedPathMap_vertex {S : IntrinsicBusemannCut A} {x : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (n : ℕ) :
    (intrinsicInfiniteDirectedPathMap I P).vertex n = I.vertexEquiv (P.vertex n) :=
  (intrinsicDirected_tail_map I (P.edge n)).symm

/-- Helper toward Proposition 3.9: every intrinsic image ray pulls back
uniquely; competitors are transported in both directions. -/
@[expose] def intrinsicInfiniteDirectedPathEquiv (S : IntrinsicBusemannCut A) (x : A.V) :
    IntrinsicInfiniteDirectedPath A S x ≃
      IntrinsicInfiniteDirectedPath B (intrinsicGeodesicMapCut I S) (I.vertexEquiv x) where
  toFun := intrinsicInfiniteDirectedPathMap I
  invFun Q := {
    edge n := ⟨I.edgeEquiv.symm (Q.edge n).val,
      fun hm => (Q.edge n).property (by
        simpa only [Equiv.apply_symm_apply] using (I.missing_map _).mpr hm)⟩
    retained n := by
      obtain ⟨e, he, hq⟩ := Q.retained n
      change I.edgeEquiv.symm (Q.edge n).val ∈ S.edges
      rw [← hq, Equiv.symm_apply_apply]
      exact he
    present n := Q.present n
    start := by
      apply I.vertexEquiv.injective
      rw [intrinsicDirected_tail_map I]
      simpa only [Equiv.apply_symm_apply] using Q.start
    chain n := by
      apply I.vertexEquiv.injective
      rw [intrinsicDirected_head_map I, intrinsicDirected_tail_map I]
      simpa only [Equiv.apply_symm_apply] using Q.chain n }
  left_inv P := IntrinsicInfiniteDirectedPath.edge_ext (fun _ => I.edgeEquiv.symm_apply_apply _)
  right_inv Q := IntrinsicInfiniteDirectedPath.edge_ext (fun _ => I.edgeEquiv.apply_symm_apply _)

/-- Helper toward Proposition 3.9: all finite segment optimality tests
are preserved and reflected, including all competing realized lengths. -/
theorem intrinsicInfiniteDirectedPathMap_optimal_iff
    {S : IntrinsicBusemannCut A} {x : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (longest : Bool) :
    (intrinsicInfiniteDirectedPathMap I P).HasOptimalSegments longest ↔
      P.HasOptimalSegments longest := by
  unfold IntrinsicInfiniteDirectedPath.HasOptimalSegments
  simp only [intrinsicInfiniteDirectedPathMap_vertex]
  have hlen := intrinsicDirectedReachableLengths_transport I S.edges S.missing
  simp only [intrinsicGeodesicMapCut, ← hlen]

/-- Helper toward Proposition 3.9: the geodesic equivalence transports
every competitor, rather than a selected family of vertex sequences. -/
@[expose] def intrinsicInfiniteXDPGeodesicEquiv (S : IntrinsicBusemannCut A)
    (x : A.V) (longest : Bool) :
    IntrinsicInfiniteXDPGeodesic A S x longest ≃
      IntrinsicInfiniteXDPGeodesic B (intrinsicGeodesicMapCut I S)
        (I.vertexEquiv x) longest :=
  (intrinsicInfiniteDirectedPathEquiv I S x).subtypeEquiv (fun P => by
    change P.HasOptimalSegments longest ↔
      (intrinsicInfiniteDirectedPathMap I P).HasOptimalSegments longest
    exact (intrinsicInfiniteDirectedPathMap_optimal_iff I P longest).symm)

/-- Helper toward Proposition 3.9: arbitrary aligned edge tails agree
after transport exactly when they agreed before transport. -/
theorem intrinsicEdgeTailsCoalesce_map_iff {S : IntrinsicBusemannCut A} {x y : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (Q : IntrinsicInfiniteDirectedPath A S y)
    (a b : ℕ) :
    IntrinsicEdgeTailsCoalesce (intrinsicInfiniteDirectedPathMap I P)
      (intrinsicInfiniteDirectedPathMap I Q) a b ↔ IntrinsicEdgeTailsCoalesce P Q a b := by
  change (∀ n, I.edgeEquiv _ = I.edgeEquiv _) ↔ _
  simp only [I.edgeEquiv.injective.eq_iff, IntrinsicEdgeTailsCoalesce]

/-- Helper toward Proposition 3.9: the same pair of offsets is least
before and after transport, preserving both leastness coordinates. -/
theorem intrinsicLeastEdgeCoalescence_map_iff {S : IntrinsicBusemannCut A} {x y : A.V}
    (P : IntrinsicInfiniteDirectedPath A S x) (Q : IntrinsicInfiniteDirectedPath A S y)
    (a b : ℕ) :
    IntrinsicLeastEdgeCoalescence (intrinsicInfiniteDirectedPathMap I P)
      (intrinsicInfiniteDirectedPathMap I Q) a b ↔
      IntrinsicLeastEdgeCoalescence P Q a b := by
  simp only [IntrinsicLeastEdgeCoalescence, intrinsicEdgeTailsCoalesce_map_iff]

/-- Helper toward Proposition 3.9: a geometric isomorphism carries the
whole ray trace onto the image ray trace, including edge interiors. -/
theorem intrinsicEdgeRayTrace_map (e : ℕ → A.E) :
    intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (e n)) =
      I.h '' intrinsicEdgeRayTrace A e := by
  unfold intrinsicEdgeRayTrace
  rw [Set.image_iUnion]
  congr 1
  funext n
  exact (I.arc_range_map (e n)).symm

/-- Helper toward Proposition 3.9: containment of an entire ray trace
in a specified geometric region is preserved and reflected when that region
is transported by the same homeomorphism. -/
theorem intrinsicEdgeRayTrace_subset_image_iff (e : ℕ → A.E) (C : Set ℂ) :
    intrinsicEdgeRayTrace B (fun n => I.edgeEquiv (e n)) ⊆ I.h '' C ↔
      intrinsicEdgeRayTrace A e ⊆ C := by
  rw [intrinsicEdgeRayTrace_map]
  exact Set.image_subset_image_iff I.h.injective

end Transport

section SourceComparison

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D : M0CutData W H)

/-- Helper toward Proposition 3.9: the specified source cut as intrinsic
data on the source geometric domain. -/
@[expose] def intrinsicGeodesicSourceCut :
    IntrinsicBusemannCut (uibotWholePlaneSourceDomain W H G hp) where
  vertices := m0CutLeftVertices W H D.seam
  edges := D.edges
  missing := D.missing

/-- Helper toward Proposition 3.9: the source cut's entire edge-ray
carrier agrees with the intrinsic ray carrier, including every competitor. -/
@[expose] def intrinsicSourceInfinitePathEquiv (x : WholePlaneVertex W) :
    M0CutInfinitePath W H D x ≃
      IntrinsicInfiniteDirectedPath (uibotWholePlaneSourceDomain W H G hp)
        (intrinsicGeodesicSourceCut W H G hp D) x where
  toFun P := {
    edge n := ⟨P.edge n, fun hm => hm (hp _)⟩
    retained := P.inCut
    present n := (P.directed n).2
    start := (uibotWholePlaneSourceMap_endpoints W H G hp (P.edge 0)).1.trans P.start
    chain n := (uibotWholePlaneSourceMap_endpoints W H G hp (P.edge n)).2.trans
      ((P.chain n).trans (uibotWholePlaneSourceMap_endpoints W H G hp
        (P.edge (n + 1))).1.symm) }
  invFun P := {
    edge n := (P.edge n).val
    inCut := P.retained
    directed n := ⟨⟨Bool.false_ne_true, hp _⟩, P.present n⟩
    start := (uibotWholePlaneSourceMap_endpoints W H G hp (P.edge 0).val).1.symm.trans
      P.start
    chain n := (uibotWholePlaneSourceMap_endpoints W H G hp (P.edge n).val).2.symm.trans
      ((P.chain n).trans (uibotWholePlaneSourceMap_endpoints W H G hp
        (P.edge (n + 1)).val).1) }
  left_inv _P := M0CutInfinitePath.edge_ext rfl
  right_inv _P := IntrinsicInfiniteDirectedPath.edge_ext (fun _ => rfl)

/-- Helper toward Proposition 3.9: source-ray vertices are preserved by
the full edge-ray equivalence. -/
theorem intrinsicSourceInfinitePathEquiv_vertex (x : WholePlaneVertex W)
    (P : M0CutInfinitePath W H D x) (n : ℕ) :
    (intrinsicSourceInfinitePathEquiv W H G hp D x P).vertex n = P.vertex n :=
  (uibotWholePlaneSourceMap_endpoints W H G hp (P.edge n)).1

/-- Helper toward Proposition 3.9: the source and intrinsic segment
conditions coincide, in both modes and for all finite competitors. -/
theorem intrinsicSourceInfinitePathEquiv_optimal_iff (x : WholePlaneVertex W)
    (P : M0CutInfinitePath W H D x) (longest : Bool) :
    (intrinsicSourceInfinitePathEquiv W H G hp D x P).HasOptimalSegments longest ↔
      (if longest then P.HasLongestSegments else P.HasShortestSegments) := by
  unfold IntrinsicInfiniteDirectedPath.HasOptimalSegments
  simp only [intrinsicSourceInfinitePathEquiv_vertex]
  change (∀ a b : ℕ, 1 ≤ a → a ≤ b → ∀ n : ℕ,
    n ∈ intrinsicDirectedReachableLengths (uibotWholePlaneSourceDomain W H G hp)
      D.edges D.missing (P.vertex (a - 1)) (P.vertex b) →
      if longest then n ≤ b + 1 - a else b + 1 - a ≤ n) ↔ _
  simp only [intrinsicDirected_source_lengths_iff W H G hp D]
  cases longest <;> rfl

/-- Helper toward Proposition 3.9: every image-cut ray corresponds to
exactly one source-cut edge ray, without any extra geometric premise. -/
@[expose] def intrinsicImageInfinitePathEquiv (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) (x : WholePlaneVertex W) :
    M0CutInfinitePath W H D x ≃
      IntrinsicInfiniteDirectedPath A (intrinsicBusemannImageCut W H G hp D A I)
        (I.vertexEquiv x) :=
  (intrinsicSourceInfinitePathEquiv W H G hp D x).trans
    (intrinsicInfiniteDirectedPathEquiv (A := uibotWholePlaneSourceDomain W H G hp)
      (B := A) I (intrinsicGeodesicSourceCut W H G hp D) x)

/-- Helper toward Proposition 3.9: the image equivalence acts on every
individual geometric edge by the isomorphism's edge bijection. -/
theorem intrinsicImageInfinitePathEquiv_edge (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) (x : WholePlaneVertex W) (P : M0CutInfinitePath W H D x) (n : ℕ) :
    ((intrinsicImageInfinitePathEquiv W H G hp D A I x P).edge n).val =
      I.edgeEquiv (P.edge n) := rfl

/-- Helper toward Proposition 3.9: all image-cut segment-optimality
tests are exactly the source-cut tests. -/
theorem intrinsicImageInfinitePathEquiv_optimal_iff (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) (x : WholePlaneVertex W) (P : M0CutInfinitePath W H D x)
    (longest : Bool) :
    (intrinsicImageInfinitePathEquiv W H G hp D A I x P).HasOptimalSegments longest ↔
      (if longest then P.HasLongestSegments else P.HasShortestSegments) :=
  (intrinsicInfiniteDirectedPathMap_optimal_iff
    (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I
      (intrinsicSourceInfinitePathEquiv W H G hp D x P) longest).trans
    (intrinsicSourceInfinitePathEquiv_optimal_iff W H G hp D x P longest)

/-- Helper toward Proposition 3.9: the source trace uses the actual arc
of each edge, and equals the installed glued-drawing path trace. -/
theorem intrinsicGeodesicSource_trace (e : ℕ → WholePlaneEdge W) :
    intrinsicEdgeRayTrace (uibotWholePlaneSourceDomain W H G hp) e =
      pathTrace G (fun n => (e n, false)) := by
  unfold intrinsicEdgeRayTrace pathTrace
  congr 1
  funext n
  exact G.toPlaneGraphDrawing_arc_range (e n, false)

/-- Helper toward Proposition 3.9: every source cut competitor has its
entire geometric trace transported to the representative. -/
theorem intrinsicImageInfinitePathEquiv_trace (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root) (x : WholePlaneVertex W) (P : M0CutInfinitePath W H D x) :
    intrinsicEdgeRayTrace A
        (fun n => ((intrinsicImageInfinitePathEquiv W H G hp D A I x P).edge n).val) =
      I.h '' pathTrace G (fun n => (P.edge n, false)) := by
  change intrinsicEdgeRayTrace A (fun n => I.edgeEquiv (P.edge n)) = _
  exact (intrinsicEdgeRayTrace_map (A := uibotWholePlaneSourceDomain W H G hp)
    (B := A) I P.edge).trans (congrArg (fun C : Set ℂ => I.h '' C)
      (intrinsicGeodesicSource_trace W H G hp P.edge))

end SourceComparison

section IdentifiedGeodesics

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root)

local notation "D" => m0CutData W H h hLL
local notation "S" => intrinsicBusemannImageCut W H G hp D A I

/-- Helper toward Proposition 3.9: the installed identified geodesic
gives an intrinsic image-cut geodesic, retaining every edge and every finite
optimal segment. This assertion contains no planar leftmostness claim. -/
@[expose] def intrinsicGeodesicOfCode {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    IntrinsicInfiniteXDPGeodesic A S (I.vertexEquiv ((D).x k)) longest := by
  refine ⟨intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)
    (m0CutPathOfPresentPath W H h hLL k P.codePath), ?_⟩
  apply (intrinsicImageInfinitePathEquiv_optimal_iff W H G hp D A I _ _ longest).mpr
  cases longest with
  | false =>
    exact (Xdp.Sdp.m0Cut_hasShortestSegments_iff W H h hLL k P.codePath).mpr P.segments
  | true =>
    exact (m0Cut_hasLongestSegments_iff W H h hLL k P.codePath).mpr P.segments

/-- Helper toward Proposition 3.9: the intrinsic geodesic is the image
of each individual code edge, not merely the image of its vertices. -/
theorem intrinsicGeodesicOfCode_edge {k : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ) :
    (((intrinsicGeodesicOfCode W H h hLL G hp A I P).val.edge n).val) =
      I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)) := rfl

/-- Helper toward Proposition 3.9: least intrinsic offsets of code-image
geodesics agree exactly with the installed least edge-coalescence predicate. -/
theorem intrinsicGeodesicOfCode_least_iff {k k' : ℤ} {longest : Bool}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (Q : M0CutInfiniteGeodesic W H h hLL k' longest) (a b : ℕ) :
    IntrinsicLeastEdgeCoalescence
      (intrinsicGeodesicOfCode W H h hLL G hp A I P).val
      (intrinsicGeodesicOfCode W H h hLL G hp A I Q).val a b ↔
      M0CutLeastEdgeCoalescence P Q a b := by
  have ht (i j : ℕ) :
      IntrinsicEdgeTailsCoalesce (intrinsicGeodesicOfCode W H h hLL G hp A I P).val
        (intrinsicGeodesicOfCode W H h hLL G hp A I Q).val i j ↔
        M0CutEdgeTailsCoalesce P Q i j := by
    constructor
    · intro htail n
      exact I.edgeEquiv.injective (htail n)
    · intro htail n
      exact congrArg I.edgeEquiv (htail n)
  simp only [IntrinsicLeastEdgeCoalescence, M0CutLeastEdgeCoalescence, ht]

end IdentifiedGeodesics

section ImageRegion

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "D" => m0CutData W H h hLL

/-- Helper toward Proposition 3.9: the universal code leftmostness test
is equivalent to containment of every intrinsic optimal competitor in the
image of its code `closedBetween` region. The region here is explicitly an
image; this does not identify an independently defined intrinsic region. -/
theorem intrinsicImage_leftmost_image_region_iff
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root)
    (longest : Bool) (k : ℤ) (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (R : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k)) :
    (∀ Q : IntrinsicInfiniteDirectedPath A
        (intrinsicBusemannImageCut W H G hp D A I) (I.vertexEquiv ((D).x k)),
      Q.HasOptimalSegments longest →
        intrinsicEdgeRayTrace A (fun n => (Q.edge n).val) ⊆
          I.h '' closedBetween
            (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
            (pathTrace G (fun n => wholePlaneDartι W 0 (R.edge n, false)))) ↔
      Xdp.CutLeftmostXdp W H h hpast hLL longest k P R := by
  let e := intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)
  constructor
  · intro hleft Q hQ
    have ho := (intrinsicImageInfinitePathEquiv_optimal_iff W H G hp D A I
      ((D).x k) Q longest).mpr hQ
    have hc := hleft (e Q) ho
    have he := intrinsicImageInfinitePathEquiv_trace W H G hp D A I ((D).x k) Q
    change intrinsicEdgeRayTrace A (fun n => ((e Q).edge n).val) = _ at he
    rw [he] at hc
    exact (Set.image_subset_image_iff I.h.injective).mp hc
  · intro hleft Q hQ
    let q := e.symm Q
    have heq : e q = Q := e.apply_symm_apply Q
    have ho : (e q).HasOptimalSegments longest := by rw [heq]; exact hQ
    have hq := (intrinsicImageInfinitePathEquiv_optimal_iff W H G hp D A I
      ((D).x k) q longest).mp ho
    have hc := hleft q hq
    have he := intrinsicImageInfinitePathEquiv_trace W H G hp D A I ((D).x k) q
    change intrinsicEdgeRayTrace A (fun n => ((e q).edge n).val) = _ at he
    rw [heq] at he
    rw [he]
    exact (Set.image_subset_image_iff I.h.injective).mpr hc

end ImageRegion

/-- Helper toward Proposition 3.9: on one iid conull event, the images
of the actual slice-witness geodesics are intrinsic geodesics in every
representative and under every source isomorphism. Their least offsets
agree with the geometric offset factor, with the same witness for the slice
value and the identified Busemann increment. This does not identify an
intrinsic planar leftmostness region. -/
theorem intrinsicGeodesic_sample_offsets_ae :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      ∃ s : ∀ x : XDP, M0CutGeodesicSliceWitness W x,
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        ∀ x : XDP,
        (if x = XDP.ldp then
          IsIntrinsicBusemannLDP A (intrinsicBusemannImageCut W H G hp D A I)
            (fun k => I.vertexEquiv (D.x k)) (identifiedLDPBusemann W)
        else IsIntrinsicBusemannSDP A (intrinsicBusemannImageCut W H G hp D A I)
            (fun k => I.vertexEquiv (D.x k)) (identifiedSDPBusemann W)) ∧
        let P := fun j => intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P j)
        (∀ k k' : ℤ, ∃ a b : ℕ, IntrinsicEdgeTailsCoalesce (P k).val (P k').val a b) ∧
        ∀ k : ℤ,
        let X := if x = XDP.ldp then identifiedLDPBusemann W else identifiedSDPBusemann W
        IntrinsicLeastEdgeCoalescence (P (k - 1)).val (P k).val
          ((s x).thetaMinus k) ((s x).theta k) ∧
        uibotGeomCoalescenceOffsets z x k = ((s x).thetaMinus k, (s x).theta k) ∧
        uibotCodeCoalescenceOffsets W x k = ((s x).thetaMinus k, (s x).theta k) ∧
        (uibotGeomSideSliceObservables z x k).2 =
          some (geometricSideClass (m0CutGeodesicSlice (hp := (s x).hp) (s x).P k
            ((s x).thetaMinus k) ((s x).theta k) ((s x).least k))) ∧
        X k - X (k - 1) = (((s x).theta k : ℕ) : ℤ) -
          (((s x).thetaMinus k : ℕ) : ℤ) := by
  filter_upwards [uibotIntrinsicCut_sample_realization, uibotRecoveredCode_ae,
    uibotGeomCoalescenceOffsets_ae_slice_characterization,
    identifiedSDPBusemann_characterization_ae, identifiedLDPBusemann_characterization_ae,
    uibotGeomCoalescenceOffsets_ae]
    with U hreal hcode hslices hSDP hLDP hfactor
  dsimp only at hreal ⊢
  rw [hcode] at hreal ⊢
  obtain ⟨_, _, H, h, hpast, hp, hclass, hisos, _⟩ := hreal
  choose s hs using hslices
  refine ⟨H, h, hpast, hp, s, hclass, ?_⟩
  intro A hA
  refine ⟨hisos A hA, ?_⟩
  intro I x
  refine ⟨?_, ?_⟩
  · by_cases hx : x = XDP.ldp
    · simp only [hx, ite_true]
      exact (isIntrinsicBusemannLDP_image_iff U H h _ _ hp A I _).mpr (hLDP H h _)
    · simp only [hx, ite_false]
      exact (isIntrinsicBusemannSDP_image_iff U H h _ _ hp A I _).mpr (hSDP H h _)
  refine ⟨?_, ?_⟩
  · apply intrinsicEdgeTailsCoalesce_pairwise
    intro k
    refine ⟨(s x).thetaMinus k, (s x).theta k, ?_⟩
    exact ((intrinsicGeodesicOfCode_least_iff U H h _ _ hp A I
      ((s x).P (k - 1)) ((s x).P k) _ _).mpr ((s x).least k)).1
  intro k
  refine ⟨(intrinsicGeodesicOfCode_least_iff U H h _ _ hp A I
    ((s x).P (k - 1)) ((s x).P k) _ _).mpr ((s x).least k),
    (hs x k).1, (congrArg (fun f => f x k) hfactor).trans ((hs x k).1),
    (hs x k).2, ?_⟩
  have hco : M0CutLeastEdgeCoalescence ((s x).P k) ((s x).P (k - 1))
      ((s x).theta k) ((s x).thetaMinus k) := by
    refine ⟨fun n => ((s x).least k).1 n |>.symm, ?_⟩
    intro a b hab
    have hh := ((s x).least k).2 b a (fun n => (hab n).symm)
    exact ⟨hh.2, hh.1⟩
  apply m0Cut_busemann_cls_identity _ ((s x).P k) ((s x).P (k - 1)) _ _ hco
  by_cases hx : x = XDP.ldp
  · simpa only [hx, ite_true] using hLDP (s x).H (s x).h (s x).hLL
  · simpa only [hx, ite_false, Bool.false_eq_true] using hSDP (s x).H (s x).h (s x).hLL

/- REMAINING SPECIFICATIONS, not Lean declarations or assumptions.

The missing object is a region B A p r : Set ℂ defined from A's plane
orientation and the two actual edge rays p r : ℕ → A.E. It must express
"weakly to the right of p and to the left of r" in the source sense.
The existing coordinate-defined `closedBetween` cannot simply serve as B
on arbitrary representatives: its horizontal sections are not preserved by
an arbitrary orientation-preserving homeomorphism (even a half-turn).

The exact deterministic characterization still required has these binders:

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1))))
let D := m0CutData W H h hLL
let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
∀ (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root)
  (longest : Bool) (k : ℤ)
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (T : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
  (_ : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
  (_ : T.edge = R.edge),
B A (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (P.codePath.edge n)))
    (fun n => I.edgeEquiv (wholePlaneEdgeι W 0 (T.edge n))) =
  I.h '' closedBetween
    (pathTrace G (fun n => wholePlaneDartι W 0 (P.codePath.edge n, false)))
    (pathTrace G (fun n => wholePlaneDartι W 0 (T.edge n, false))).

With B independently defined and characterized, the missing literal
leftmost predicate would have the following full carrier and body:

L (A : D39DomainRootedMap.{0}) (S : IntrinsicBusemannCut A) (v : A.V)
  (longest : Bool) (P : IntrinsicInfiniteXDPGeodesic A S v longest)
  (T : IntrinsicInfiniteDirectedPath A S v) :=
∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
  intrinsicEdgeRayTrace A (fun n => (Q.val.edge n).val) ⊆
    B A (fun n => (P.val.edge n).val) (fun n => (T.edge n).val).

On the same conull event, with the existential W,H,h,hpast,hp,hLL,D,G,s,z
bound exactly as in `intrinsicGeodesic_sample_offsets_ae`, the missing
additional clause is:

∀ (A : D39DomainRootedMap.{0})
  (_ : Quotient.mk d39DomainSetoid A = z)
  (I : D39GeomRootedMapIsoV2
    (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
    A.map A.root) (x : XDP) (k : ℤ),
let S := intrinsicBusemannImageCut W H G hp D A I
let v := I.vertexEquiv (D.x k)
let longest := if x = XDP.ldp then true else false
∃ T : IntrinsicInfiniteDirectedPath A S v,
  RightmostInCut A S v T ∧
  ∀ Q : IntrinsicInfiniteXDPGeodesic A S v longest,
    L A S v longest Q T ↔ Q = intrinsicGeodesicOfCode W H h hLL G hp A I ((s x).P k).

Here RightmostInCut has full carrier
  (A : D39DomainRootedMap.{0}) (S : IntrinsicBusemannCut A) (v : A.V)
  (T : IntrinsicInfiniteDirectedPath A S v) : Prop
and means the rightmost directed ray for the cut's retained present edges
and restricted rotation, rather than the ambient map's unrestricted ray.

The existing image-region equivalence above proves neither this native
region characterization nor this intrinsic uniqueness clause. No B or L
interface is installed here, and neither missing statement is assumed. -/

end DirectedDistances.PaperProofs.Section3
end
