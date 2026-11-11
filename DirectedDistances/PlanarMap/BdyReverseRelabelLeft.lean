/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseRelabelEquivariance
public import DirectedDistances.PlanarMap.MirrorMap

/-! # Relabelling equivariance for left boundary reversal -/

public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- Mirroring a relabelled directed map gives the relabelled mirror. The
outer dart is preserved by the equality because both sides mark the image
under relabelling of the original opposite outer dart. Helper toward
result. -/
theorem DirectedMapWithMissing.mirror_relabel (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) :
    (DirectedMapWithMissing.relabel σ M).mirror =
      DirectedMapWithMissing.relabel σ M.mirror := by
  cases M with
  | mk C missing hm tail ht htm outer ho =>
    cases C with
    | mk edgeInv hinv hne rot =>
      simp [DirectedMapWithMissing.mirror, DirectedMapWithMissing.relabel,
        CombinatorialMap.mirror, CombinatorialMap.relabel,
        relabelPerm]
      exact (mul_assoc σ rot⁻¹ σ⁻¹).symm

/-- The rotation permutations agree in the two orders of mirror and
relabel. Helper toward `lem-bdy-reverse` -/
theorem DirectedMapWithMissing.mirror_relabel_rot (σ : Equiv.Perm D)
    (M : DirectedMapWithMissing D) :
    (DirectedMapWithMissing.relabel σ M).mirror.toCombinatorialMap.rot =
      (DirectedMapWithMissing.relabel σ M.mirror).toCombinatorialMap.rot := by
  simp [DirectedMapWithMissing.mirror, DirectedMapWithMissing.relabel,
    CombinatorialMap.mirror, CombinatorialMap.relabel, relabelPerm_inv]

/-- The rotation-cycle vertices of the two directed maps in
`mirror_relabel` are identified by a quotient equivalence induced by the
identity on darts. Helper toward `lem-bdy-reverse` -/
@[expose] noncomputable def DirectedMapWithMissing.mirrorRelabelVertexEquiv
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) :
    MapVertex ((DirectedMapWithMissing.relabel σ M).mirror) ≃
      MapVertex (DirectedMapWithMissing.relabel σ M.mirror) := by
  apply Quotient.congr (Equiv.refl D)
  intro x y
  change Equiv.Perm.SameCycle
      ((DirectedMapWithMissing.relabel σ M).mirror.toCombinatorialMap.rot) x y ↔
    Equiv.Perm.SameCycle
      ((DirectedMapWithMissing.relabel σ M.mirror).toCombinatorialMap.rot) x y
  rw [DirectedMapWithMissing.mirror_relabel_rot σ M]

/-- The mirror/relabel quotient transport sends each dart representative to
the same dart representative. Helper toward `lem-bdy-reverse` -/
theorem DirectedMapWithMissing.mirrorRelabelVertexEquiv_dartTailVertex
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D) (d : D) :
    DirectedMapWithMissing.mirrorRelabelVertexEquiv σ M
      (dartTailVertex ((DirectedMapWithMissing.relabel σ M).mirror) d) =
    dartTailVertex (DirectedMapWithMissing.relabel σ M.mirror) d := by
  change Quotient.congr (Equiv.refl D) _ (Quotient.mk _ d) = Quotient.mk _ d
  exact Quotient.congr_mk (Equiv.refl D) _ d

/-- Relabelling vertex transport commutes with mirror vertex transport after
identifying the two mirror/relabel rotation quotients. Helper toward
result. -/
theorem DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D)
    (v : MapVertex M) :
    DirectedMapWithMissing.mirrorRelabelVertexEquiv σ M
      (DirectedMapWithMissing.mirrorVertexMap (DirectedMapWithMissing.relabel σ M)
        (DirectedMapWithMissing.relabelVertexEquiv σ M v)) =
      DirectedMapWithMissing.relabelVertexEquiv σ M.mirror
        (DirectedMapWithMissing.mirrorVertexMap M v) := by
  induction v using Quotient.inductionOn with
  | h d =>
    change DirectedMapWithMissing.mirrorRelabelVertexEquiv σ M
      (DirectedMapWithMissing.mirrorVertexMap (DirectedMapWithMissing.relabel σ M)
        (DirectedMapWithMissing.relabelVertexEquiv σ M (dartTailVertex M d))) =
      DirectedMapWithMissing.relabelVertexEquiv σ M.mirror
        (DirectedMapWithMissing.mirrorVertexMap M (dartTailVertex M d))
    rw [DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex]
    rw [mirrorVertexMap_eq, mirror_dartTailVertex]
    rw [DirectedMapWithMissing.mirrorRelabelVertexEquiv_dartTailVertex]
    rw [mirrorVertexMap_eq, mirror_dartTailVertex]
    rw [DirectedMapWithMissing.relabelVertexEquiv_dartTailVertex]

private theorem DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute_heq
    (σ : Equiv.Perm D) (M : DirectedMapWithMissing D)
    (v : MapVertex M) :
    HEq
      (DirectedMapWithMissing.mirrorVertexMap (DirectedMapWithMissing.relabel σ M)
        (DirectedMapWithMissing.relabelVertexEquiv σ M v))
      (DirectedMapWithMissing.relabelVertexEquiv σ M.mirror
        (DirectedMapWithMissing.mirrorVertexMap M v)) := by
  have htype :
      MapVertex ((DirectedMapWithMissing.relabel σ M).mirror) =
        MapVertex (DirectedMapWithMissing.relabel σ M.mirror) :=
    congrArg (fun N : DirectedMapWithMissing D => MapVertex N)
      (DirectedMapWithMissing.mirror_relabel σ M)
  cases htype
  have hid : ∀ x : MapVertex ((DirectedMapWithMissing.relabel σ M).mirror),
      DirectedMapWithMissing.mirrorRelabelVertexEquiv σ M x = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h d =>
      change Quotient.congr (Equiv.refl D) _ (Quotient.mk _ d) = _
      exact Quotient.congr_mk (Equiv.refl D) _ d
  have hcomm := DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute σ M v
  have h0 := hid
    (DirectedMapWithMissing.mirrorVertexMap (DirectedMapWithMissing.relabel σ M)
      (DirectedMapWithMissing.relabelVertexEquiv σ M v))
  exact heq_of_eq (h0.symm.trans hcomm)

private theorem simplePath_vertices_eq_of_darts_eq
    {M : DirectedMapWithMissing D} {s t s' t' : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n)
    (Q : SimpleDirectedDartPath M s' t' n)
    (hs : s = s') (hd : P.darts = Q.darts) : P.vertices = Q.vertices := by
  apply List.ext_getElem
  · rw [P.vertices_length, Q.vertices_length]
  · intro i hiP hiQ
    by_cases hzero : i = 0
    · subst i
      simpa only [List.get_eq_getElem] using
        P.start_vertex.trans (hs.trans Q.start_vertex.symm)
    · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
      have hin : i ≤ n := by rw [P.vertices_length] at hiP; omega
      have hdiP : i - 1 < P.darts.length := by rw [P.darts_length]; omega
      have hdiQ : i - 1 < Q.darts.length := by rw [Q.darts_length]; omega
      let jP : Fin P.darts.length := ⟨i - 1, hdiP⟩
      let jQ : Fin Q.darts.length := ⟨i - 1, hdiQ⟩
      have hP := P.edge_step jP
      have hQ := Q.edge_step jQ
      have hPhead : P.vertices[i]'hiP =
          dartHeadVertex M (P.darts[i - 1]'hdiP) := by
        have hidx : jP.val + 1 = i := by dsimp [jP]; omega
        simpa only [List.get_eq_getElem, jP, hidx] using hP.2.2.2
      have hQhead : Q.vertices[i]'hiQ =
          dartHeadVertex M (Q.darts[i - 1]'hdiQ) := by
        have hidx : jQ.val + 1 = i := by dsimp [jQ]; omega
        simpa only [List.get_eq_getElem, jQ, hidx] using hQ.2.2.2
      have hQhead' : Q.vertices[i]'hiQ =
          dartHeadVertex M (P.darts[i - 1]'hdiP) := by
        simpa only [hd] using hQhead
      exact hPhead.trans hQhead'.symm

private theorem simpleDirectedDartPath_hext
    {M N : DirectedMapWithMissing D} {s t : MapVertex M} {s' t' : MapVertex N}
    {n : ℕ} (P : SimpleDirectedDartPath M s t n)
    (Q : SimpleDirectedDartPath N s' t' n)
    (hM : M = N) (hs : HEq s s') (ht : HEq t t')
    (hd : P.darts = Q.darts) : HEq P Q := by
  subst N
  have hs' : s = s' := eq_of_heq hs
  subst s'
  have ht' : t = t' := eq_of_heq ht
  subst t'
  have hv : P.vertices = Q.vertices :=
    simplePath_vertices_eq_of_darts_eq P Q rfl hd
  cases P with
  | mk pd pv pdl pvl pnod pstart pend pstep =>
    cases Q with
    | mk qd qv qdl qvl qnod qstart qend qstep =>
      dsimp at hd hv
      subst qd
      subst qv
      rfl

/-- Mirroring a relabelled path is heterogeneously equal to relabelling its
not the paper result. -/
theorem SimpleDirectedDartPath.mirror_relabel
    (σ : Equiv.Perm D) {M : DirectedMapWithMissing D}
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    HEq
      (DirectedMapWithMissing.SimpleDirectedDartPath.mirror
        (SimpleDirectedDartPath.relabel σ P))
      (SimpleDirectedDartPath.relabel σ
        (DirectedMapWithMissing.SimpleDirectedDartPath.mirror P)) := by
  apply simpleDirectedDartPath_hext
  · exact DirectedMapWithMissing.mirror_relabel σ M
  · exact DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute_heq σ M s
  · exact DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute_heq σ M t
  · simp [DirectedMapWithMissing.SimpleDirectedDartPath.mirror,
      SimpleDirectedDartPath.relabel]

omit [Fintype D] [DecidableEq D] in
private theorem nonemptyWord_ext_of_letters {W W' : NonemptyWord D}
    (h : W.letters = W'.letters) : W = W' := by
  cases W with
  | mk letters nonempty nodup =>
    cases W' with
    | mk letters' nonempty' nodup' =>
      dsimp at h
      subst letters'
      rfl

/-- Mirroring a relabelled bipolar boundary carrier is equal to relabelling
its mirror. Helper toward `lem-bdy-reverse` -/
theorem BipolarTriangulationWithBoundary.mirror_relabel {ℓ r : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D ℓ r) :
    (B.relabel σ).mirror = (B.mirror).relabel σ := by
  apply BipolarTriangulationWithBoundary.hext_fields
  · change (DirectedMapWithMissing.relabel σ B.map).mirror =
      DirectedMapWithMissing.relabel σ B.map.mirror
    exact DirectedMapWithMissing.mirror_relabel σ B.map
  · exact DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute_heq
      σ B.map B.source
  · exact DirectedMapWithMissing.mirrorRelabelVertexEquiv_commute_heq
      σ B.map B.sink
  · apply nonemptyWord_ext_of_letters
    change (DirectedMapWithMissing.mirrorOuterWord
        (DirectedMapWithMissing.relabel σ B.map)
        (NonemptyWord.relabel σ B.outerWord)).letters =
      (NonemptyWord.relabel σ
        (DirectedMapWithMissing.mirrorOuterWord B.map B.outerWord)).letters
    simp [DirectedMapWithMissing.mirrorOuterWord, NonemptyWord.relabel,
      DirectedMapWithMissing.relabel, CombinatorialMap.relabel_edgeInv,
      relabelPerm_apply, List.map_reverse, List.map_map, Function.comp_def]
  · exact SimpleDirectedDartPath.mirror_relabel σ B.rightPath
  · exact SimpleDirectedDartPath.mirror_relabel σ B.leftPath

/-- Restricted left-prefix reversal commutes with dart relabelling. Helper
paper result. -/
theorem leftPrefixReversal_relabel {a b : ℕ}
    (σ : Equiv.Perm D) (B : BipolarTriangulationWithBoundary D a b)
    (k : ℕ) (hk : 1 ≤ k) (hka : k < a) (hbc : B.IsBoundaryChanneled) :
    leftPrefixReversal (B.relabel σ) k hk hka
      ((B.relabel_InMbc_iff σ).2 hbc) =
    (leftPrefixReversal B k hk hka hbc).relabel σ := by
  have hmirror := BipolarTriangulationWithBoundary.mirror_relabel σ B
  have hbcRelabel : (B.relabel σ).IsBoundaryChanneled :=
    (B.relabel_InMbc_iff σ).2 hbc
  have hbcMirror : B.mirror.IsBoundaryChanneled :=
    BipolarTriangulationWithBoundary.mirror_isBoundaryChanneled hbc
  have hbcMirrorRelabelLeft : (B.relabel σ).mirror.IsBoundaryChanneled :=
    BipolarTriangulationWithBoundary.mirror_isBoundaryChanneled hbcRelabel
  let C : BoundaryMbcClass D b a := ⟨B.mirror, hbcMirror⟩
  let C' : BoundaryMbcClass D b a := ⟨(B.relabel σ).mirror,
    hbcMirrorRelabelLeft⟩
  have hC : C' = relabelBoundaryMbcClass σ C := by
    apply Subtype.ext
    exact hmirror
  change
    (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C').val.mirror =
      ((rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C).val.mirror).relabel σ
  calc
    (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C').val.mirror =
        (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka
          (relabelBoundaryMbcClass σ C)).val.mirror :=
      congrArg (fun X : BoundaryMbcClass D b a =>
        (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka X).val.mirror) hC
    _ = (relabelBoundaryMbcClass σ
          (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C)).val.mirror :=
      congrArg (fun X : BoundaryMbcClass D (b + k) (a - k) => X.val.mirror)
        (rightPrefixReversalMbc_relabel σ k hk hka C)
    _ = (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C).val.mirror.relabel σ :=
      BipolarTriangulationWithBoundary.mirror_relabel σ
        (rightPrefixReversalMbc (D := D) (ℓ := b) (r := a) k hk hka C).val

/-- The class-level restricted left-prefix reversal commutes with dart
relabelling. Helper toward `lem-bdy-reverse` -/
theorem leftPrefixReversalMbc_relabel {a b : ℕ}
    (σ : Equiv.Perm D) (k : ℕ) (hk : 1 ≤ k) (hka : k < a)
    (B : BoundaryMbcClass D a b) :
    leftPrefixReversalMbc (D := D) (a := a) (b := b) k hk hka
      (relabelBoundaryMbcClass σ B) =
    relabelBoundaryMbcClass σ
      (leftPrefixReversalMbc (D := D) (a := a) (b := b) k hk hka B) := by
  apply Subtype.ext
  exact leftPrefixReversal_relabel σ B.val k hk hka B.property

/-- Restricted left-prefix reversal on a fixed inner-edge size slice. Helper
paper result. -/
@[expose] noncomputable def leftPrefixReversalSize {a b : ℕ}
    (k : ℕ) (hk : 1 ≤ k) (hka : k < a) (n : ℕ) :
    {B : BipolarTriangulationWithBoundary D a b //
      BipolarTriangulationWithBoundary.InMbc a b B ∧ innerEdgeCount B = n} →
    {B : BipolarTriangulationWithBoundary D (a - k) (b + k) //
      BipolarTriangulationWithBoundary.InMbc (a - k) (b + k) B ∧
        innerEdgeCount B = n} := fun B =>
  ⟨leftPrefixReversal B.val k hk hka B.property.1,
    leftPrefixReversal_InMbc B.val k hk hka B.property.1,
    (leftPrefixReversal_innerEdgeCount B.val k hk hka B.property.1).trans
      B.property.2⟩

/-- The fixed-size left-prefix reversal commutes with dart relabelling.
Helper toward `lem-bdy-reverse` -/
theorem leftPrefixReversalSize_relabel {a b : ℕ}
    (σ : Equiv.Perm D) (k : ℕ) (hk : 1 ≤ k) (hka : k < a) (n : ℕ)
    (B : {C : BipolarTriangulationWithBoundary D a b //
      BipolarTriangulationWithBoundary.InMbc a b C ∧ innerEdgeCount C = n}) :
    leftPrefixReversalSize (D := D) (a := a) (b := b) k hk hka n
      (relabelBoundaryMbcSize σ n B) =
    relabelBoundaryMbcSize σ n
      (leftPrefixReversalSize (D := D) (a := a) (b := b) k hk hka n B) := by
  apply Subtype.ext
  exact leftPrefixReversal_relabel σ B.val k hk hka B.property.1

private theorem boundaryMbcClassEquiv_relabel {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (σ : Equiv.Perm D)
    (B : BoundaryMbcClass D a b) :
    boundaryMbcClassEquiv (D := D) ha hb (relabelBoundaryMbcClass σ B) =
      relabelBoundaryMbcClass σ (boundaryMbcClassEquiv (D := D) ha hb B) := by
  cases ha
  cases hb
  rfl

/-- Uniform endpoint symmetry commutes with dart relabelling. Helper toward -/
theorem endpointSymmetryEquiv_relabel (l : ℕ) (hl : 1 ≤ l)
    (σ : Equiv.Perm D) (B : BoundaryMbcClass D l 1) :
    endpointSymmetryEquiv (D := D) l hl (relabelBoundaryMbcClass σ B) =
      relabelBoundaryMbcClass σ (endpointSymmetryEquiv (D := D) l hl B) := by
  by_cases h : l = 1
  · subst l
    rw [endpointSymmetryEquiv_one]
    rfl
  · have hl2 : 2 ≤ l := by omega
    rw [endpointSymmetryEquiv_of_two (D := D) hl2]
    simp only [leftEndpointReversalEquiv, Equiv.trans_apply,
      Equiv.ofBijective_apply]
    change boundaryMbcClassEquiv (D := D) (by omega) (by omega)
        (leftPrefixReversalMbc (D := D) (a := l) (b := 1) (l - 1)
          (by omega) (by omega) (relabelBoundaryMbcClass σ B)) =
      relabelBoundaryMbcClass σ
        (boundaryMbcClassEquiv (D := D) (by omega) (by omega)
          (leftPrefixReversalMbc (D := D) (a := l) (b := 1) (l - 1)
            (by omega) (by omega) B))
    rw [leftPrefixReversalMbc_relabel]
    exact boundaryMbcClassEquiv_relabel (by omega) (by omega) σ _

/-- Dart relabelling on a fixed inner-edge size slice of boundary classes.
Helper toward `lem-bdy-reverse` -/
@[expose] noncomputable def relabelBoundaryMbcClassSize {a b : ℕ}
    (σ : Equiv.Perm D) (n : ℕ) :
    {B : BoundaryMbcClass D a b // innerEdgeCount B.val = n} →
      {B : BoundaryMbcClass D a b // innerEdgeCount B.val = n} := fun B =>
  ⟨relabelBoundaryMbcClass σ B.val,
    (B.val.val.relabel_innerEdgeCount σ).trans B.property⟩

/-- The fixed-size endpoint symmetry commutes with dart relabelling. Helper
toward `lem-bdy-reverse` -/
theorem endpointSymmetrySizedEquiv_relabel (l s : ℕ) (hl : 1 ≤ l)
    (σ : Equiv.Perm D)
    (B : {C : BoundaryMbcClass D l 1 // innerEdgeCount C.val = s}) :
    endpointSymmetrySizedEquiv (D := D) l s hl
      (relabelBoundaryMbcClassSize σ s B) =
    relabelBoundaryMbcClassSize σ s
      (endpointSymmetrySizedEquiv (D := D) l s hl B) := by
  apply Subtype.ext
  exact endpointSymmetryEquiv_relabel l hl σ B.val

end DirectedDistances.PlanarMap
