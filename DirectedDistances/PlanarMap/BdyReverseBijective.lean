module

public import DirectedDistances.PlanarMap.BdyReverseInverse
public import Mathlib.MeasureTheory.Measure.Count

/-! # Bijections and size invariants for restricted boundary reversal

use only the restricted simple-boundary carrier, are not counted in the paper
The source law concerns isomorphism classes; transport from this labelled
carrier to those classes is a separate obligation. -/

public section
namespace DirectedDistances.PlanarMap

universe u
variable {D : Type u} [Fintype D] [DecidableEq D] {ℓ r a b : ℕ}
open BipolarTriangulationWithBoundary
open scoped ENNReal

/-- Preimage with explicit length transport. Restricted helper for -/
private theorem leftReversal_preimage
    (B : BipolarTriangulationWithBoundary D a b) (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) (hkr : k < r) (hbc : B.IsBoundaryChanneled)
    (hℓ : a - k = ℓ) (hρ : b + k = r) :
    ∃ (C : BipolarTriangulationWithBoundary D ℓ r) (hc : C.IsBoundaryChanneled),
      HEq (rightPrefixReversal C k hk hkr hc) B := by
  subst ℓ
  subst r
  refine ⟨leftPrefixReversal B k hk hka hbc,
    leftPrefixReversal_isBoundaryChanneled B k hk hka hbc, ?_⟩
  have h := rightPrefixReversal_leftPrefixReversal B k hk hka hbc
  exact (heq_of_eq h).trans (cast_heq _ B)

/-- Right reversal is bijective when the initial left length is positive.
Restricted simple-boundary helper for `lem-bdy-reverse` -/
theorem rightPrefixReversalMbc_bijective (hℓ : 1 ≤ ℓ) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) :
    Function.Bijective
      (rightPrefixReversalMbc (D := D) (ℓ := ℓ) (r := r) k hk hkr) := by
  constructor
  · exact rightPrefixReversalMbc_injective k hk hkr
  · intro B
    obtain ⟨C, hc, h⟩ := leftReversal_preimage (ℓ := ℓ) (r := r)
      B.val k hk (by omega) hkr B.property (by omega) (by omega)
    refine ⟨⟨C, hc⟩, ?_⟩
    apply Subtype.ext
    exact eq_of_heq h

/-- Reflection preserves restricted membership (`lem-bdy-reverse`, -/
theorem InMbc_mirror {B : BipolarTriangulationWithBoundary D ℓ r}
    (hB : InMbc ℓ r B) : InMbc r ℓ B.mirror :=
  mirror_isBoundaryChanneled hB

/-- Converse reflection membership on the restricted carrier -/
theorem InMbc_of_mirror {B : BipolarTriangulationWithBoundary D ℓ r}
    (hB : InMbc r ℓ B.mirror) : InMbc ℓ r B := by
  have hhead (d : D) (hm : ¬ B.map.missing d) (ht : B.map.tail d) :
      DirectedMapWithMissing.mirrorVertexMap B.map (dartHeadVertex B.map d) =
        dartHeadVertex B.map.mirror d := by
    have hne : dartTailVertex B.map d ≠ dartHeadVertex B.map d := by
      intro he
      apply B.acyclic (dartTailVertex B.map d)
      exact Relation.TransGen.single ⟨d, hm, ht, rfl, he.symm⟩
    let P : SimpleDirectedDartPath B.map
        (dartTailVertex B.map d) (dartHeadVertex B.map d) 1 :=
      { darts := [d]
        vertices := [dartTailVertex B.map d, dartHeadVertex B.map d]
        darts_length := rfl
        vertices_length := rfl
        vertices_nodup := by simp [hne]
        start_vertex := rfl
        end_vertex := rfl
        edge_step := by
          intro i
          rcases i with ⟨i, hi⟩
          have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
          subst i
          exact ⟨hm, ht, rfl, rfl⟩ }
    have hh := (DirectedMapWithMissing.SimpleDirectedDartPath.mirror P).edge_step
      ⟨0, by simp [DirectedMapWithMissing.SimpleDirectedDartPath.mirror, P]⟩
    exact hh.2.2.2
  intro d hm ht hv hn
  apply (mirror_boundaryEdge_iff B d).mp
  apply hB d hm ht
  · change dartHeadVertex B.map.mirror d ∈ B.mirror.boundaryVertices
    rw [← hhead d hm ht]
    exact (mirror_mem_boundaryVertices_iff B _).mpr hv
  · intro he
    apply hn
    apply (DirectedMapWithMissing.mirrorVertexMap_bijective B.map).injective
    rw [hhead d hm ht]
    exact he

/-- Geometric edge classes survive restricted reversal (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_numEdges
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (rightPrefixReversal B k hk hkr hbc).map.toCombinatorialMap.numEdges =
      B.map.toCombinatorialMap.numEdges := by
  rw [rightPrefixReversal_map, flipRightPrefix_toCombinatorialMap]

/-- Reflection preserves geometric edge classes (`lem-bdy-reverse`, -/
@[simp] theorem mirror_numEdges (B : BipolarTriangulationWithBoundary D ℓ r) :
    B.mirror.map.toCombinatorialMap.numEdges = B.map.toCombinatorialMap.numEdges :=
  CombinatorialMap.numEdges_mirror B.map.toCombinatorialMap

/-- Inner-edge size on the restricted simple-boundary carrier: total geometric
edge classes minus its `ℓ + r` distinct boundary edges (`lem-bdy-reverse`,
This counts geometric edges, before any boundary edges are declared missing. -/
@[expose] noncomputable def innerEdgeCount
    (B : BipolarTriangulationWithBoundary D ℓ r) : ℕ :=
  B.map.toCombinatorialMap.numEdges - (ℓ + r)

/-- Restricted reversal preserves inner-edge size (`lem-bdy-reverse`, -/
@[simp] theorem rightPrefixReversal_innerEdgeCount
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    innerEdgeCount (rightPrefixReversal B k hk hkr hbc) = innerEdgeCount B := by
  unfold innerEdgeCount
  rw [rightPrefixReversal_numEdges]
  congr 1
  omega

/-- Reflection preserves inner-edge size (`lem-bdy-reverse`, -/
@[simp] theorem mirror_innerEdgeCount (B : BipolarTriangulationWithBoundary D ℓ r) :
    innerEdgeCount B.mirror = innerEdgeCount B := by
  simp only [innerEdgeCount, mirror_numEdges, Nat.add_comm]

/-- Right reversal on a fixed inner-edge size slice. Restricted helper for -/
@[expose] noncomputable def rightPrefixReversalSize (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (n : ℕ) :
    {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n} →
    {B : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) B ∧ innerEdgeCount B = n} :=
  fun B => ⟨rightPrefixReversal B.val k hk hkr B.property.1,
    rightPrefixReversal_InMbc B.val k hk hkr B.property.1,
    (rightPrefixReversal_innerEdgeCount B.val k hk hkr B.property.1).trans B.property.2⟩

/-- Fixed-size restricted reversal is bijective for positive initial left
No isomorphism-quotient or source uniform law is asserted. -/
theorem rightPrefixReversalSize_bijective (hℓ : 1 ≤ ℓ) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (n : ℕ) :
    Function.Bijective (rightPrefixReversalSize (D := D) (ℓ := ℓ) k hk hkr n) := by
  constructor
  · intro B C h
    apply Subtype.ext
    have hb : rightPrefixReversalMbc k hk hkr ⟨B.val, B.property.1⟩ =
        rightPrefixReversalMbc k hk hkr ⟨C.val, C.property.1⟩ := by
      apply Subtype.ext
      exact congrArg (fun x => x.val) h
    have he := (rightPrefixReversalMbc_injective k hk hkr) hb
    exact congrArg (fun x : {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B} => x.val) he
  · intro B
    obtain ⟨C, hC⟩ := (rightPrefixReversalMbc_bijective (D := D) hℓ k hk hkr).surjective
      ⟨B.val, B.property.1⟩
    have hv : rightPrefixReversal C.val k hk hkr C.property = B.val :=
      congrArg Subtype.val hC
    have hs : innerEdgeCount C.val = n := by
      rw [← rightPrefixReversal_innerEdgeCount C.val k hk hkr C.property, hv]
      exact B.property.2
    exact ⟨⟨C.val, C.property, hs⟩, Subtype.ext hv⟩

/-- Endpoint root-index transport before declaring boundary edges missing.
The first `r - 1` right edges are carried to the first `r - 1` left edges;
index `i` becomes `i.rev`, of value `r - 1 - (i + 1)`.
These are labelled index pairs, not source isomorphism classes. -/
@[expose] noncomputable def endpointMissingRootTransport (hr : 2 ≤ r) :
    ({B : BipolarTriangulationWithBoundary D 1 r // InMbc 1 r B} × Fin (r - 1)) →
    ({B : BipolarTriangulationWithBoundary D (1 + (r - 1)) (r - (r - 1)) //
      InMbc (1 + (r - 1)) (r - (r - 1)) B} × Fin (r - 1)) :=
  fun Bi => (rightPrefixReversalMbc (r - 1) (by omega) (by omega) Bi.1, Bi.2.rev)

/-- Endpoint reversal transports all choices of missing root bijectively,
with the explicit reversed index. Restricted helper for `lem-bdy-reverse` -/
theorem endpointMissingRootTransport_bijective (hr : 2 ≤ r) :
    Function.Bijective (endpointMissingRootTransport (D := D) hr) := by
  constructor
  · rintro ⟨B, i⟩ ⟨C, j⟩ h
    have hb := congrArg Prod.fst h
    have hi := congrArg (fun x => x.2.rev) h
    apply Prod.ext
    · exact (rightPrefixReversalMbc_endpoint_bijective hr).injective hb
    · simpa only [endpointMissingRootTransport, Fin.rev_rev] using hi
  · rintro ⟨B, j⟩
    obtain ⟨C, hC⟩ := (rightPrefixReversalMbc_endpoint_bijective (D := D) hr).surjective B
    refine ⟨(C, j.rev), ?_⟩
    exact Prod.ext hC (Fin.rev_rev j)

/-- The `i`th reversed right dart is the opposite dart at left index
`k - 1 - i`. Thus it represents the same geometric edge. -/
theorem rightPrefixReversal_index_dart
    (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) (i : Fin k) :
    (rightPrefixReversal B k hk hkr hbc).leftPath.darts[i.rev.val]'(by
      rw [(rightPrefixReversal B k hk hkr hbc).leftPath.darts_length]
      have := i.rev.isLt
      omega) =
      B.map.edgeInv (B.rightPath.darts[i.val]'(by rw [B.rightPath.darts_length]; omega)) := by
  simp only [rightPrefixReversal_leftPath_darts]
  have hlen : ((B.rightPath.darts.take k).reverse.map B.map.edgeInv).length = k := by
    simp only [List.length_map, List.length_reverse, List.length_take,
      B.rightPath.darts_length, Nat.min_eq_left (Nat.le_of_lt hkr)]
  rw [List.getElem_append_left (by rw [hlen]; exact i.rev.isLt)]
  simp only [List.getElem_map, List.getElem_reverse, List.getElem_take]
  have hi : (B.rightPath.darts.take k).length - 1 - i.rev.val = i.val := by
    simp only [List.length_take, B.rightPath.darts_length,
      Nat.min_eq_left (Nat.le_of_lt hkr), Fin.val_rev]
    omega
  simp only [hi]

/-- Distinct steps of a simple directed path represent distinct edge classes.
Restricted counting helper for `lem-bdy-reverse` -/
private theorem path_edgeOrbit_injective {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    Function.Injective (fun i : Fin P.darts.length =>
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgeInv) (P.darts.get i)) := by
  intro i j h
  have hi := P.edge_step i
  have hj := P.edge_step j
  rcases (CombinatorialMap.edgeInv_sameCycle_iff M.toCombinatorialMap _ _).mp
      (Quotient.exact h) with he | he
  · have hv := hj.2.2.1.trans ((congrArg (dartTailVertex M) he).trans hi.2.2.1.symm)
    have heq := List.nodup_iff_injective_get.mp P.vertices_nodup hv
    exact Fin.ext (congrArg Fin.val heq).symm
  · exact False.elim (((M.tail_iff _ hi.1).mp hi.2.1)
      (by rw [← he]; exact hj.2.1))

/-- The two disjoint simple boundary paths supply `ℓ + r` distinct geometric
edges. Restricted counting helper for `lem-bdy-reverse` -/
theorem boundaryLength_le_numEdges (B : BipolarTriangulationWithBoundary D ℓ r) :
    ℓ + r ≤ B.map.toCombinatorialMap.numEdges := by
  classical
  let f : Fin B.leftPath.darts.length ⊕ Fin B.rightPath.darts.length →
      CombinatorialMap.EdgeQuotient B.map.toCombinatorialMap :=
    Sum.elim
      (fun i => Quotient.mk _ (B.leftPath.darts.get i))
      (fun i => Quotient.mk _ (B.rightPath.darts.get i))
  have hf : Function.Injective f := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (path_edgeOrbit_injective B.leftPath h)
    · exact False.elim (B.paths_edge_disjoint _ (List.get_mem _ i) _
        (List.get_mem _ j) (Quotient.exact h))
    · exact False.elim (B.paths_edge_disjoint _ (List.get_mem _ j) _
        (List.get_mem _ i) (Quotient.exact h).symm)
    · exact congrArg Sum.inr (path_edgeOrbit_injective B.rightPath h)
  simpa only [Fintype.card_sum, Fintype.card_fin, B.leftPath.darts_length,
    B.rightPath.darts_length, CombinatorialMap.numEdges] using
    Fintype.card_le_of_injective f hf

/-- Total edges split into inner-edge size and `ℓ + r` boundary edges, with
no truncated-subtraction loss. Restricted helper for `lem-bdy-reverse` -/
theorem innerEdgeCount_add_boundaryLength
    (B : BipolarTriangulationWithBoundary D ℓ r) :
    innerEdgeCount B + (ℓ + r) = B.map.toCombinatorialMap.numEdges :=
  Nat.sub_add_cancel (boundaryLength_le_numEdges B)

/-- Counting-normalised uniform measure on a finite labelled carrier. It is
zero on the empty carrier. Restricted transport helper for `lem-bdy-reverse`
source isomorphism classes is a separate obligation. -/
@[expose] noncomputable def uniformCountingMeasure (α : Type*) [Fintype α]
    [MeasurableSpace α] : MeasureTheory.Measure α :=
  (Fintype.card α : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count

/-- A bijection transports finite counting-normalised uniform measure to
uniform measure. Generic helper for the restricted application of -/
theorem uniformCountingMeasure_map_of_bijective
    {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (hf : Function.Bijective f) :
    (uniformCountingMeasure α).map f = uniformCountingMeasure β := by
  have hm := measurable_of_countable f
  have hc : (MeasureTheory.Measure.count : MeasureTheory.Measure α).map f =
      MeasureTheory.Measure.count := by
    ext s hs
    rw [MeasureTheory.Measure.map_apply hm hs,
      ← MeasureTheory.Measure.count_injective_image hf.injective (f ⁻¹' s),
      Set.image_preimage_eq s hf.surjective]
  unfold uniformCountingMeasure
  rw [MeasureTheory.Measure.map_smul _ hm.aemeasurable, hc,
    Fintype.card_congr (Equiv.ofBijective f hf)]

/-- Uniform transport on a fixed-size restricted slice, with both finiteness
instances supplied explicitly. Helper for `lem-bdy-reverse`
labelled-carrier statement; source isomorphism-class transport remains separate. -/
theorem rightPrefixReversalSize_uniform (hℓ : 1 ≤ ℓ) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (n : ℕ)
    (sourceFintype : Fintype {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n})
    (targetFintype : Fintype {B : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) B ∧ innerEdgeCount B = n})
    [MeasurableSpace {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n}]
    [MeasurableSpace {B : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) B ∧ innerEdgeCount B = n}]
    [MeasurableSingletonClass {B : BipolarTriangulationWithBoundary D ℓ r //
      InMbc ℓ r B ∧ innerEdgeCount B = n}]
    [MeasurableSingletonClass {B : BipolarTriangulationWithBoundary D (ℓ + k) (r - k) //
      InMbc (ℓ + k) (r - k) B ∧ innerEdgeCount B = n}] :
    (@uniformCountingMeasure _ sourceFintype _).map (rightPrefixReversalSize k hk hkr n) =
      @uniformCountingMeasure _ targetFintype _ := by
  let _ := sourceFintype
  let _ := targetFintype
  exact uniformCountingMeasure_map_of_bijective _
    (rightPrefixReversalSize_bijective hℓ k hk hkr n)

/-- Uniform transport of endpoint map/root pairs, with finiteness supplied
explicitly. Restricted helper for `lem-bdy-reverse`
component is labelled, so this does not yet give the source equality in law. -/
theorem endpointMissingRootTransport_uniform (hr : 2 ≤ r) :
    let A := {B : BipolarTriangulationWithBoundary D 1 r // InMbc 1 r B} × Fin (r - 1)
    let C := {B : BipolarTriangulationWithBoundary D (1 + (r - 1)) (r - (r - 1)) //
      InMbc (1 + (r - 1)) (r - (r - 1)) B} × Fin (r - 1)
    ∀ (sourceFintype : Fintype A) (targetFintype : Fintype C)
      [mA : MeasurableSpace A] [mC : MeasurableSpace C]
      [MeasurableSingletonClass A] [MeasurableSingletonClass C],
      (@uniformCountingMeasure A sourceFintype mA).map
          (endpointMissingRootTransport hr) =
        @uniformCountingMeasure C targetFintype mC := by
  intro A C sourceFintype targetFintype mA mC hA hC
  let _ := sourceFintype
  let _ := targetFintype
  exact uniformCountingMeasure_map_of_bijective _
    (endpointMissingRootTransport_bijective hr)

/-- The endpoint root transport carries the original `i`th right edge to
exactly the same geometric edge, now listed at left index
`i.rev = r - 1 - (i + 1)`. Restricted helper for `lem-bdy-reverse`
The designation of these indexed edges as missing is performed afterwards,
so this statement does not equip a missing edge with an orientation. -/
theorem endpointMissingRootTransport_sameEdge (hr : 2 ≤ r)
    (B : {B : BipolarTriangulationWithBoundary D 1 r // InMbc 1 r B})
    (i : Fin (r - 1)) :
    let C := endpointMissingRootTransport hr (B, i)
    Equiv.Perm.SameCycle B.val.map.edgeInv
      (B.val.rightPath.darts[i.val]'(by rw [B.val.rightPath.darts_length]; omega))
      (C.1.val.leftPath.darts[C.2.val]'(by
        rw [C.1.val.leftPath.darts_length]
        have := C.2.isLt
        omega)) := by
  dsimp only [endpointMissingRootTransport, rightPrefixReversalMbc]
  apply (CombinatorialMap.edgeInv_sameCycle_iff B.val.map.toCombinatorialMap _ _).mpr
  exact Or.inr (rightPrefixReversal_index_dart B.val (r - 1)
    (by omega) (by omega) B.property i)

end DirectedDistances.PlanarMap
