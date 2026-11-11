/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicDirectedDistance
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart1
public import DirectedDistances.PaperProofs.Section7.SDPFluctuationIdentified
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.Paper.Section1.BusemannM0

/-! # Busemann characterizations on geometric representatives

Helpers toward Proposition 3.9, using Theorem 1.4
and edge sets and missing tags on the representative. The image-cut results
do not identify this cut with an independently characterized intrinsic future
integration remain with the coordinator. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section7
open MeasureTheory Filter

/-- Helper toward Proposition 3.9: the geometric vertices, geometric edges,
and additional missing tags of a specified cut on the ambient representative.
No characterization or existence assertion is included in these data. -/
structure IntrinsicBusemannCut (A : D39DomainRootedMap.{0}) where
  /-- Helper toward Proposition 3.9: the retained vertices. -/
  vertices : Set A.V
  /-- Helper toward Proposition 3.9: individual retained geometric edges. -/
  edges : Set A.E
  /-- Helper toward Proposition 3.9: cut edges without a directed orientation. -/
  missing : A.E → Prop

/-- Helper toward Proposition 3.9: intrinsic reachability by a finite list
of retained present edges, with the empty-path convention. -/
@[expose] def intrinsicBusemannReachable (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (u v : A.V) : Prop :=
  ∃ es, IntrinsicDirectedEdgeListPath A S.edges S.missing u v es

/-- Helper toward Proposition 3.9: Theorem 1.4's normalized SDP
characterization on a specified cut. Both distances are certified finite
before their natural values are subtracted. -/
@[expose] def IsIntrinsicBusemannSDP (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (x : ℤ → A.V) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → A.V, Function.Injective y →
      (∀ j, y j ∈ S.vertices ∧
        intrinsicBusemannReachable A S (x k) (y j) ∧
        intrinsicBusemannReachable A S (x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        intrinsicDirectedSDP A S.edges S.missing (x k') (y j) ≠ ⊤ ∧
        intrinsicDirectedSDP A S.edges S.missing (x k) (y j) ≠ ⊤ ∧
        X k' - X k =
          ((intrinsicDirectedSDP A S.edges S.missing (x k') (y j)).toNat : ℤ) -
          ((intrinsicDirectedSDP A S.edges S.missing (x k) (y j)).toNat : ℤ)

/-- Helper toward Proposition 3.9: Theorem 1.4's normalized LDP
characterization on a specified cut. Explicit natural witnesses certify
finite extended distances before subtraction. -/
@[expose] def IsIntrinsicBusemannLDP (A : D39DomainRootedMap.{0})
    (S : IntrinsicBusemannCut A) (x : ℤ → A.V) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → A.V, Function.Injective y →
      (∀ j, y j ∈ S.vertices ∧
        intrinsicBusemannReachable A S (x k) (y j) ∧
        intrinsicBusemannReachable A S (x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        ∃ n n' : ℕ,
          intrinsicDirectedLDP A S.edges S.missing (x k') (y j) =
            ((n : ℕ∞) : WithBot ℕ∞) ∧
          intrinsicDirectedLDP A S.edges S.missing (x k) (y j) =
            ((n' : ℕ∞) : WithBot ℕ∞) ∧
          X k' - X k = (n : ℤ) - (n' : ℤ)

section ImageCut

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (D : M0CutData W H) (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root)

/-- Helper toward Proposition 3.9: image cut data retain the geometric
vertex and edge identities and transport the cut missing tags. -/
@[expose] def intrinsicBusemannImageCut : IntrinsicBusemannCut A where
  vertices := I.vertexEquiv '' m0CutLeftVertices W H D.seam
  edges := I.edgeEquiv '' D.edges
  missing := fun e => D.missing (I.edgeEquiv.symm e)

/-- Helper toward Proposition 3.9: image-cut reachability is precisely
source cut reachability, by length-preserving actual edge-list transport. -/
theorem intrinsicBusemannImageCut_reachable_iff (u v : WholePlaneVertex W) :
    intrinsicBusemannReachable A (intrinsicBusemannImageCut W H G hp D A I)
      (I.vertexEquiv u) (I.vertexEquiv v) ↔ m0CutReachable W H D.seam u v := by
  have hlen (n : ℕ) :
      n ∈ intrinsicDirectedReachableLengths A (I.edgeEquiv '' D.edges)
        (fun e => D.missing (I.edgeEquiv.symm e)) (I.vertexEquiv u) (I.vertexEquiv v) ↔
      m0CutReachableLength (m0CutDirectedStep W H D.seam) n u v := by
    have ht := intrinsicDirectedReachableLengths_transport
      (A := uibotWholePlaneSourceDomain W H G hp) (B := A) I D.edges D.missing u v
    exact (congrArg (fun s : Set ℕ => n ∈ s) ht).symm.to_iff.trans
      (intrinsicDirected_source_lengths_iff W H G hp D u v n)
  constructor
  · rintro ⟨es, hes⟩
    exact ⟨es.length, (hlen es.length).mp ⟨es, hes, rfl⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨es, hes, _⟩ := (hlen n).mpr hn
    exact ⟨es, hes⟩

end ImageCut

section CharacterizationTransport

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

private theorem intrinsicBusemann_source_target_mem (k : ℤ) (v : WholePlaneVertex W)
    (hr : m0CutReachable W H (D).seam ((D).x k) v) :
    I.vertexEquiv v ∈ (S).vertices := by
  have hx := (D).x_eq h hLL k
  rw [hx] at hr
  obtain ⟨b, hb⟩ := m0Cut_reachable_target_is_vertex W H h hLL (D).seam
    (m0Cut_seamEdge_iff W H h hLL) hr
  refine ⟨v, ?_, rfl⟩
  rw [m0Cut_leftVertices_eq_runZero W H h (D).seam
    (m0Cut_seamEdge_iff W H h hLL)]
  exact ⟨b, hb⟩

/-- Helper toward Proposition 3.9: the full intrinsic SDP
characterization on the image cut is equivalent to the identified one.
Every injective target sequence is pulled back by the inverse vertex equivalence. -/
theorem isIntrinsicBusemannSDP_image_iff (X : ℤ → ℤ) :
    IsIntrinsicBusemannSDP A S (fun k => I.vertexEquiv ((D).x k)) X ↔
      IsIdentifiedM0BusemannSDP D X := by
  have hd := intrinsicDirected_image_source_distances W H G hp D A I
  have hr := intrinsicBusemannImageCut_reachable_iff W H G hp D A I
  constructor
  · rintro ⟨hzero, hX⟩
    refine ⟨hzero, ?_⟩
    intro k k' y hy hyr
    obtain ⟨N, hN⟩ := hX k k' (fun j => I.vertexEquiv (y j))
      (I.vertexEquiv.injective.comp hy) (fun j =>
        ⟨intrinsicBusemann_source_target_mem W H h hLL G hp A I k (y j) (hyr j).1,
          (hr _ _).mpr (hyr j).1, (hr _ _).mpr (hyr j).2⟩)
    refine ⟨N, fun j hj => ?_⟩
    have he := (hN j hj).2.2
    exact he.trans (congrArg₂ (fun a b : ℕ∞ => (a.toNat : ℤ) - (b.toNat : ℤ))
      (hd ((D).x k') (y j)).1 (hd ((D).x k) (y j)).1)
  · rintro ⟨hzero, hX⟩
    refine ⟨hzero, ?_⟩
    intro k k' y hy hyr
    let z : ℕ → WholePlaneVertex W := fun j => I.vertexEquiv.symm (y j)
    have hzr (j : ℕ) : m0CutReachable W H (D).seam ((D).x k) (z j) ∧
        m0CutReachable W H (D).seam ((D).x k') (z j) := by
      constructor
      · apply (hr _ _).mp
        simpa only [z, Equiv.apply_symm_apply] using (hyr j).2.1
      · apply (hr _ _).mp
        simpa only [z, Equiv.apply_symm_apply] using (hyr j).2.2
    obtain ⟨N, hN⟩ := hX k k' z (I.vertexEquiv.symm.injective.comp hy) hzr
    refine ⟨N, fun j hj => ?_⟩
    have hd' := hd ((D).x k') (z j)
    have hd₀ := hd ((D).x k) (z j)
    simp only [z, Equiv.apply_symm_apply] at hd' hd₀
    refine ⟨fun ht => m0CutData_sdp_ne_top_of_reachable W H h hLL _ _
      (hzr j).2 (hd'.1.symm.trans ht),
      fun ht => m0CutData_sdp_ne_top_of_reachable W H h hLL _ _
        (hzr j).1 (hd₀.1.symm.trans ht), ?_⟩
    exact (hN j hj).trans (congrArg₂
      (fun a b : ℕ∞ => (a.toNat : ℤ) - (b.toNat : ℤ)) hd'.1 hd₀.1).symm

/-- Helper toward Proposition 3.9: the full intrinsic LDP
characterization on the image cut is equivalent to the identified one,
preserving both explicit finite natural witnesses before subtraction. -/
theorem isIntrinsicBusemannLDP_image_iff (X : ℤ → ℤ) :
    IsIntrinsicBusemannLDP A S (fun k => I.vertexEquiv ((D).x k)) X ↔
      IsIdentifiedM0BusemannLDP D X := by
  have hd := intrinsicDirected_image_source_distances W H G hp D A I
  have hr := intrinsicBusemannImageCut_reachable_iff W H G hp D A I
  constructor
  · rintro ⟨hzero, hX⟩
    refine ⟨hzero, ?_⟩
    intro k k' y hy hyr
    obtain ⟨N, hN⟩ := hX k k' (fun j => I.vertexEquiv (y j))
      (I.vertexEquiv.injective.comp hy) (fun j =>
        ⟨intrinsicBusemann_source_target_mem W H h hLL G hp A I k (y j) (hyr j).1,
          (hr _ _).mpr (hyr j).1, (hr _ _).mpr (hyr j).2⟩)
    refine ⟨N, fun j hj => ?_⟩
    obtain ⟨n, n', hn, hn', he⟩ := hN j hj
    change intrinsicDirectedLDP A (I.edgeEquiv '' (D).edges)
      (fun e => (D).missing (I.edgeEquiv.symm e)) _ _ = _ at hn hn'
    rw [(hd ((D).x k') (y j)).2] at hn
    rw [(hd ((D).x k) (y j)).2] at hn'
    exact ⟨n, n', hn, hn', he⟩
  · rintro ⟨hzero, hX⟩
    refine ⟨hzero, ?_⟩
    intro k k' y hy hyr
    let z : ℕ → WholePlaneVertex W := fun j => I.vertexEquiv.symm (y j)
    have hzr (j : ℕ) : m0CutReachable W H (D).seam ((D).x k) (z j) ∧
        m0CutReachable W H (D).seam ((D).x k') (z j) := by
      constructor
      · apply (hr _ _).mp
        simpa only [z, Equiv.apply_symm_apply] using (hyr j).2.1
      · apply (hr _ _).mp
        simpa only [z, Equiv.apply_symm_apply] using (hyr j).2.2
    obtain ⟨N, hN⟩ := hX k k' z (I.vertexEquiv.symm.injective.comp hy) hzr
    refine ⟨N, fun j hj => ?_⟩
    obtain ⟨n, n', hn, hn', he⟩ := hN j hj
    have hd' := hd ((D).x k') (z j)
    have hd₀ := hd ((D).x k) (z j)
    simp only [z, Equiv.apply_symm_apply] at hd' hd₀
    exact ⟨n, n', hd'.2.trans hn, hd₀.2.trans hn', he⟩

end CharacterizationTransport

/- conull realization event, every representative admits a geometric source
isomorphism, and every such isomorphism identifies both unique normalized
intrinsic image-cut Busemann sequences with the existing identified sequences.
This is a joint equality of entire functions on the iid sample space. -/
theorem intrinsicBusemann_sample_identification_ae :
    ∀ᵐ U ∂wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      wholePlaneWordIntegral W 0 = (0, 0) ∧
      (∀ t : ℤ, wholePlaneWordIntegral W (t + 1) - wholePlaneWordIntegral W t =
        lazyTwoDimensionalStep (W t)) ∧
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))
      let D := m0CutData W H h hLL
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      z = Quotient.mk d39DomainSetoid (uibotWholePlaneSourceDomain W H G hp) ∧
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2
          (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
          A.map A.root,
        let S := intrinsicBusemannImageCut W H G hp D A I
        let x := fun k => I.vertexEquiv (D.x k)
        (IsIntrinsicBusemannSDP A S x (identifiedSDPBusemann W) ∧
          ∀ X : ℤ → ℤ, IsIntrinsicBusemannSDP A S x X → X = identifiedSDPBusemann W) ∧
        (IsIntrinsicBusemannLDP A S x (identifiedLDPBusemann W) ∧
          ∀ X : ℤ → ℤ, IsIntrinsicBusemannLDP A S x X → X = identifiedLDPBusemann W) := by
  filter_upwards [uibotIntrinsicCut_sample_realization, uibotRecoveredCode_ae,
    DirectedDistances.Paper.Section1.thm_busemann,
    identifiedSDPBusemann_characterization_ae,
    identifiedLDPBusemann_characterization_ae] with U hreal hcode huniq hS hL
  dsimp only at hreal ⊢
  rw [hcode] at hreal ⊢
  obtain ⟨hz, hi, H, h, hpast, hp, hclass, hisos, _⟩ := hreal
  let hLL := fun (k : ℤ) (_hk : k ≤ 0) => hp
    (wholePlaneEdgeι U 0 (kmswLLCreatedEdge (shiftedStream U 0)
      (boundaryHitTime (shiftedStream U 0) h (k - 1))))
  obtain ⟨H', h', hLL', _, _, _, _, _, _, _, hsuniq, hluniq⟩ := huniq
  have hH : H' = H := Subsingleton.elim _ _
  subst H'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  have hc : hLL' = hLL := Subsingleton.elim _ _
  subst hLL'
  obtain ⟨YS, hYS, huS⟩ := hsuniq
  obtain ⟨YL, hYL, huL⟩ := hluniq
  have hcharS := hS H h hLL
  have hcharL := hL H h hLL
  refine ⟨hz, hi, H, h, hpast, hp, hclass, ?_⟩
  intro A hA
  refine ⟨hisos A hA, ?_⟩
  intro I
  have hiffS := isIntrinsicBusemannSDP_image_iff U H h hLL
    (WholePlanePastGlueDrawing.glueDrawing U h hpast H) hp A I
  have hiffL := isIntrinsicBusemannLDP_image_iff U H h hLL
    (WholePlanePastGlueDrawing.glueDrawing U h hpast H) hp A I
  refine ⟨⟨(hiffS _).mpr hcharS, ?_⟩, ⟨(hiffL _).mpr hcharL, ?_⟩⟩
  · intro X hX
    exact (huS X ((hiffS X).mp hX)).trans (huS _ hcharS).symm
  · intro X hX
    exact (huL X ((hiffL X).mp hX)).trans (huL _ hcharL).symm

end DirectedDistances.PaperProofs.Section3
end
