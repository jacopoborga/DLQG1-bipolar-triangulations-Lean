/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute2

/-! Helper toward Proposition 3.9: comparison of components after edge deletion. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open ShiftedStartGeometry ShiftedStartClosedRegionRoute ShiftedStartClosedRegionRoute2
open Set Topology

private theorem subtype_component_image (X R : Set ℂ) (x : X)
    (hx : (x : ℂ) ∉ R) :
    Subtype.val '' connectedComponentIn {a : X | (a : ℂ) ∉ R} x =
      connectedComponentIn (X \ R) (x : ℂ) := by
  let A : Set X := {a | (a : ℂ) ∉ R}
  have hset : Subtype.val '' A = X \ R := by
    ext z
    exact ⟨fun ⟨a, ha, he⟩ => he ▸ ⟨a.property, ha⟩,
      fun ⟨hzX, hzR⟩ => ⟨⟨z, hzX⟩, hzR, rfl⟩⟩
  apply Subset.antisymm
  · rw [← hset]
    exact continuous_subtype_val.continuousOn.image_connectedComponentIn_subset hx
  · have hsub : connectedComponentIn (X \ R) (x : ℂ) ⊆ X :=
      (connectedComponentIn_subset _ _).trans sdiff_subset
    have hconn : IsPreconnected
        (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
      exact isPreconnected_connectedComponentIn
    have hxC : x ∈ (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) :=
      mem_connectedComponentIn ⟨x.property, hx⟩
    have hCA : (Subtype.val ⁻¹' connectedComponentIn (X \ R) (x : ℂ) : Set X) ⊆ A :=
      fun _ ha => (connectedComponentIn_subset _ _ ha).2
    intro y hy
    exact ⟨⟨y, hsub hy⟩, hconn.subset_connectedComponentIn hxC hCA hy, rfl⟩

private theorem relative_component_transport (X Y R S : Set ℂ) (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (x : X) (hx : (x : ℂ) ∉ R) :
    (fun a : X => (g a : ℂ)) ''
        {a : X | (a : ℂ) ∈ connectedComponentIn (X \ R) (x : ℂ)} =
      connectedComponentIn (Y \ S) (g x : ℂ) := by
  let A : Set X := {a | (a : ℂ) ∉ R}
  let B : Set Y := {b | (b : ℂ) ∉ S}
  have hAB : g '' A = B := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun hb => ha ((hRS a).mp hb)
    · intro hb
      refine ⟨g.symm b, ?_, g.apply_symm_apply b⟩
      intro ha
      exact hb (by simpa only [g.apply_symm_apply] using (hRS (g.symm b)).mpr ha)
  have hc : {a : X | (a : ℂ) ∈ connectedComponentIn (X \ R) (x : ℂ)} =
      connectedComponentIn A x := by
    rw [← subtype_component_image X R x hx]
    exact preimage_image_eq _ Subtype.val_injective
  rw [hc]
  change (Subtype.val ∘ g) '' connectedComponentIn A x = _
  rw [image_comp, g.image_connectedComponentIn hx, hAB]
  exact subtype_component_image Y S (g x) (fun hh => hx ((hRS x).mp hh))

private theorem relative_boundary_transport (X Y R S : Set ℂ) (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X)
    (x : X) (hx : (x : ℂ) ∉ R) :
    (connectedComponentIn (X \ R) (x : ℂ) ∩ frontier X).Nonempty ↔
      (connectedComponentIn (Y \ S) (g x : ℂ) ∩ frontier Y).Nonempty := by
  have hc := relative_component_transport X Y R S g hRS x hx
  constructor
  · rintro ⟨z, hz, hzf⟩
    let a : X := ⟨z, (connectedComponentIn_subset _ _ hz).1⟩
    exact ⟨g a, hc ▸ mem_image_of_mem _ hz, (hfront a).mpr hzf⟩
  · rintro ⟨z, hz, hzf⟩
    rw [← hc] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, (hfront a).mp hzf⟩

/-- Helper toward Proposition 3.9: the closed-region comparison transports
every non-exterior full-plane component after deletion, including its deleted
edge points. The same map detects whether the component joins the exterior. -/
theorem plane_component_transport_of_ne_exterior
    (X Y R S : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (hR : IsClosed R) (hS : IsClosed S) (hRX : R ⊆ X) (hSY : S ⊆ Y)
    (hXe : IsPreconnected Xᶜ) (hYe : IsPreconnected Yᶜ)
    (q r : ℂ) (hq : q ∉ X) (hr : r ∉ Y)
    (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X)
    (x : X) (hx : (x : ℂ) ∉ R) :
    (connectedComponentIn Rᶜ (x : ℂ) = connectedComponentIn Rᶜ q ↔
      connectedComponentIn Sᶜ (g x : ℂ) = connectedComponentIn Sᶜ r) ∧
    (connectedComponentIn Rᶜ (x : ℂ) ≠ connectedComponentIn Rᶜ q →
      (fun a : X => (g a : ℂ)) ''
        {a : X | (a : ℂ) ∈ connectedComponentIn Rᶜ (x : ℂ)} =
        connectedComponentIn Sᶜ (g x : ℂ)) := by
  have hgx : (g x : ℂ) ∉ S := fun hh => hx ((hRS x).mp hh)
  have he : connectedComponentIn Rᶜ (x : ℂ) = connectedComponentIn Rᶜ q ↔
      connectedComponentIn Sᶜ (g x : ℂ) = connectedComponentIn Sᶜ r := by
    rw [relative_component_joins_exterior_iff X R hX hR hRX hXe q x hq
      ⟨x.property, hx⟩,
      relative_component_joins_exterior_iff Y S hY hS hSY hYe r (g x) hr
      ⟨(g x).property, hgx⟩]
    exact relative_boundary_transport X Y R S g hRS hfront x hx
  refine ⟨he, fun hn => ?_⟩
  rw [plane_component_eq_relative_of_ne_exterior X R hRX hXe q x hq hx hn,
    plane_component_eq_relative_of_ne_exterior Y S hSY hYe r (g x) hr hgx
      (fun hh => hn (he.mpr hh))]
  exact relative_component_transport X Y R S g hRS x hx

private theorem bounded_image_in_closed_region (X Y : Set ℂ) (hX : IsClosed X)
    (g : X ≃ₜ Y) (A : Set ℂ) (hAX : A ⊆ X) (hA : Bornology.IsBounded A) :
    Bornology.IsBounded ((fun x : X => (g x : ℂ)) '' {x : X | (x : ℂ) ∈ A}) := by
  have hcl : closure A ⊆ X := closure_minimal hAX hX
  let f : closure A → ℂ := fun z => (g ⟨z, hcl z.property⟩ : ℂ)
  have hf : Continuous f := continuous_subtype_val.comp
    (g.continuous.comp (continuous_subtype_val.subtype_mk _))
  let route3CompactClosure : CompactSpace (closure A) :=
    isCompact_iff_compactSpace.mp hA.isCompact_closure
  apply (isCompact_range hf).isBounded.subset
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨⟨a, subset_closure ha⟩, rfl⟩

/-- Helper toward Proposition 3.9: a homeomorphism of closed plane regions
preserves boundedness of every subset, even though it need not be uniformly
continuous. Compact closures supply both implications. -/
theorem closed_region_image_isBounded_iff
    (X Y : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (g : X ≃ₜ Y) (A : Set ℂ) (hAX : A ⊆ X) :
    Bornology.IsBounded ((fun x : X => (g x : ℂ)) '' {x : X | (x : ℂ) ∈ A}) ↔
      Bornology.IsBounded A := by
  constructor
  · intro hb
    have hBY : ((fun x : X => (g x : ℂ)) '' {x : X | (x : ℂ) ∈ A}) ⊆ Y := by
      rintro _ ⟨x, _, rfl⟩
      exact (g x).property
    have hh := bounded_image_in_closed_region Y X hY g.symm _ hBY hb
    apply hh.subset
    intro z hz
    let a : X := ⟨z, hAX hz⟩
    exact ⟨g a, ⟨a, hz, rfl⟩, congrArg Subtype.val (g.symm_apply_apply a)⟩
  · exact bounded_image_in_closed_region X Y hX g A hAX

private theorem component_subset_closed_region
    (X R : Set ℂ) (hRX : R ⊆ X) (hXe : IsPreconnected Xᶜ)
    (q : ℂ) (hq : q ∉ X)
    (A : {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z})
    (hA : A.val ≠ connectedComponentIn Rᶜ q) : A.val ⊆ X := by
  obtain ⟨z, hz, he⟩ := A.property
  rw [he, plane_component_eq_relative_of_ne_exterior X R hRX hXe q z hq hz
    (fun hh => hA (he.trans hh))]
  exact (connectedComponentIn_subset _ _).trans sdiff_subset

private theorem inverse_region_image (X Y : Set ℂ) (g : X ≃ₜ Y)
    (A : Set ℂ) (hAX : A ⊆ X) :
    (fun b : Y => (g.symm b : ℂ)) ''
        {b : Y | (b : ℂ) ∈ (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A}} = A := by
  ext z
  constructor
  · rintro ⟨b, ⟨a, ha, he⟩, rfl⟩
    have hb : g a = b := Subtype.ext he
    rw [← hb]
    change (g.symm (g a) : ℂ) ∈ A
    rw [g.symm_apply_apply]
    exact ha
  · intro hz
    let a : X := ⟨z, hAX hz⟩
    exact ⟨g a, ⟨a, hz, rfl⟩, congrArg Subtype.val (g.symm_apply_apply a)⟩

private theorem exists_component_map
    (X Y R S : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (hR : IsClosed R) (hS : IsClosed S) (hRX : R ⊆ X) (hSY : S ⊆ Y)
    (hXe : IsPreconnected Xᶜ) (hYe : IsPreconnected Yᶜ)
    (q r : ℂ) (hq : q ∉ X) (hr : r ∉ Y)
    (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) :
    let C := {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z}
    let D := {B : Set ℂ // ∃ z, z ∉ S ∧ B = connectedComponentIn Sᶜ z}
    ∃ f : C → D, ∀ A,
      ((f A).val = connectedComponentIn Sᶜ r ↔ A.val = connectedComponentIn Rᶜ q) ∧
      (A.val ≠ connectedComponentIn Rᶜ q →
        (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A.val} = (f A).val) := by
  classical
  intro C D
  suffices hh : ∀ A : C, ∃ B : D,
      (B.val = connectedComponentIn Sᶜ r ↔ A.val = connectedComponentIn Rᶜ q) ∧
      (A.val ≠ connectedComponentIn Rᶜ q →
        (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A.val} = B.val) by
    exact ⟨fun A => (hh A).choose, fun A => (hh A).choose_spec⟩
  intro A
  by_cases hA : A.val = connectedComponentIn Rᶜ q
  · exact ⟨⟨connectedComponentIn Sᶜ r, r, fun h => hr (hSY h), rfl⟩,
      ⟨fun _ => hA, fun _ => rfl⟩, fun hn => (hn hA).elim⟩
  · obtain ⟨z, hz, he⟩ := A.property
    have hzA : z ∈ A.val := he ▸ mem_connectedComponentIn hz
    let x : X := ⟨z, component_subset_closed_region X R hRX hXe q hq A hA hzA⟩
    have hgx : (g x : ℂ) ∉ S := fun hh => hz ((hRS x).mp hh)
    obtain ⟨hext, him⟩ := plane_component_transport_of_ne_exterior
      X Y R S hX hY hR hS hRX hSY hXe hYe q r hq hr g hRS hfront x hz
    have hn : connectedComponentIn Rᶜ z ≠ connectedComponentIn Rᶜ q :=
      fun hh => hA (he.trans hh)
    refine ⟨⟨connectedComponentIn Sᶜ (g x : ℂ), g x, hgx, rfl⟩,
      ⟨fun hh => (hn (hext.mpr hh)).elim, fun hh => (hA hh).elim⟩, fun _ => ?_⟩
    rw [he]
    exact him hn

/-- Helper toward Proposition 3.9: a boundary-preserving homeomorphism of
closed regions yields a bijection of all complementary components after
deletion. The exterior components correspond, and every other component is
the image under the original homeomorphism. -/
theorem exists_plane_component_equiv
    (X Y R S : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (hR : IsClosed R) (hS : IsClosed S) (hRX : R ⊆ X) (hSY : S ⊆ Y)
    (hXe : IsPreconnected Xᶜ) (hYe : IsPreconnected Yᶜ)
    (q r : ℂ) (hq : q ∉ X) (hr : r ∉ Y)
    (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) :
    let C := {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z}
    let D := {B : Set ℂ // ∃ z, z ∉ S ∧ B = connectedComponentIn Sᶜ z}
    ∃ e : C ≃ D, ∀ A,
      ((e A).val = connectedComponentIn Sᶜ r ↔ A.val = connectedComponentIn Rᶜ q) ∧
      (A.val ≠ connectedComponentIn Rᶜ q →
        (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A.val} = (e A).val) := by
  intro C D
  obtain ⟨f, hf⟩ := exists_component_map X Y R S hX hY hR hS hRX hSY hXe hYe
    q r hq hr g hRS hfront
  have hSR (y : Y) : (g.symm y : ℂ) ∈ R ↔ (y : ℂ) ∈ S := by
    simpa only [g.apply_symm_apply] using (hRS (g.symm y)).symm
  have hfront' (y : Y) : (g.symm y : ℂ) ∈ frontier X ↔ (y : ℂ) ∈ frontier Y := by
    simpa only [g.apply_symm_apply] using (hfront (g.symm y)).symm
  obtain ⟨b, hb⟩ := exists_component_map Y X S R hY hX hS hR hSY hRX hYe hXe
    r q hr hq g.symm hSR hfront'
  have hbf (A : C) : b (f A) = A := by
    apply Subtype.ext
    by_cases hA : A.val = connectedComponentIn Rᶜ q
    · exact ((hb (f A)).1.mpr ((hf A).1.mpr hA)).trans hA.symm
    · have hfa := (hf A).2 hA
      have hba := (hb (f A)).2 (fun hh => hA ((hf A).1.mp hh))
      rw [← hfa, inverse_region_image X Y g A.val
        (component_subset_closed_region X R hRX hXe q hq A hA)] at hba
      exact hba.symm
  have hfb (B : D) : f (b B) = B := by
    apply Subtype.ext
    by_cases hB : B.val = connectedComponentIn Sᶜ r
    · exact ((hf (b B)).1.mpr ((hb B).1.mpr hB)).trans hB.symm
    · have hbb := (hb B).2 hB
      have hff := (hf (b B)).2 (fun hh => hB ((hb B).1.mp hh))
      rw [← hbb] at hff
      have hi := inverse_region_image Y X g.symm B.val
        (component_subset_closed_region Y S hSY hYe r hr B hB)
      change (fun a : X => (g a : ℂ)) ''
        {a : X | (a : ℂ) ∈ (fun b : Y => (g.symm b : ℂ)) ''
          {b : Y | (b : ℂ) ∈ B.val}} = B.val at hi
      exact hff.symm.trans hi
  exact ⟨⟨f, b, hbf, hfb⟩, hf⟩

/-- Helper toward Proposition 3.9: the component bijection produced by the
closed-region homeomorphism preserves boundedness of every full-plane face,
including components formed by deleting infinitely many edges. -/
theorem exists_plane_component_equiv_isBounded
    (X Y R S : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (hR : IsClosed R) (hS : IsClosed S) (hRX : R ⊆ X) (hSY : S ⊆ Y)
    (hXe : IsPreconnected Xᶜ) (hYe : IsPreconnected Yᶜ)
    (hXu : ¬ Bornology.IsBounded Xᶜ) (hYu : ¬ Bornology.IsBounded Yᶜ)
    (q r : ℂ) (hq : q ∉ X) (hr : r ∉ Y)
    (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) :
    let C := {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z}
    let D := {B : Set ℂ // ∃ z, z ∉ S ∧ B = connectedComponentIn Sᶜ z}
    ∃ e : C ≃ D,
      (∀ A, Bornology.IsBounded (e A).val ↔ Bornology.IsBounded A.val) ∧
      (∀ A, (e A).val = connectedComponentIn Sᶜ r ↔
        A.val = connectedComponentIn Rᶜ q) ∧
      (∀ A, A.val ≠ connectedComponentIn Rᶜ q →
        (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A.val} = (e A).val) := by
  intro C D
  obtain ⟨e, he⟩ := exists_plane_component_equiv X Y R S hX hY hR hS
    hRX hSY hXe hYe q r hq hr g hRS hfront
  refine ⟨e, ?_, fun A => (he A).1, fun A => (he A).2⟩
  intro A
  by_cases hA : A.val = connectedComponentIn Rᶜ q
  · have hB := (he A).1.mpr hA
    have hEx := hXe.subset_connectedComponentIn hq (compl_subset_compl.mpr hRX)
    have hEy := hYe.subset_connectedComponentIn hr (compl_subset_compl.mpr hSY)
    rw [hA, hB]
    exact ⟨fun hb => (hYu (hb.subset hEy)).elim,
      fun ha => (hXu (ha.subset hEx)).elim⟩
  · rw [← (he A).2 hA]
    exact closed_region_image_isBounded_iff X Y hX hY g A.val
      (component_subset_closed_region X R hRX hXe q hq A hA)

private theorem restricted_vertex_surjective
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T : Set D) :
    Function.Surjective (restrictedVertex P T) := by
  rintro ⟨v, d, hd, hdv⟩
  exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩

private theorem restricted_image_mono
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T U : Set D)
    (hT : ∀ d, d ∈ T ↔ flip d ∈ T) (hU : ∀ d, d ∈ U ↔ flip d ∈ U)
    (hTU : T ⊆ U) : (restrictDrawing P T hT).image ⊆ (restrictDrawing P U hU).image := by
  rw [(restrictDrawing P T hT).image_eq_union_arcs (restricted_vertex_surjective P T),
    (restrictDrawing P U hU).image_eq_union_arcs (restricted_vertex_surjective P U)]
  intro z hz
  obtain ⟨d, hd⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨⟨d.val, hTU d.property⟩, hd⟩

private theorem component_eq_iff_mem (R : Set ℂ)
    (A : {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z})
    (z : ℂ) (hz : z ∉ R) : connectedComponentIn Rᶜ z = A.val ↔ z ∈ A.val := by
  constructor
  · intro he
    exact he ▸ mem_connectedComponentIn hz
  · intro hzA
    obtain ⟨q, _, hq⟩ := A.property
    exact ((connectedComponentIn_eq (hq ▸ hzA)).symm).trans hq.symm

private theorem component_equiv_membership
    (X Y R S : Set ℂ) (hX : IsClosed X) (hY : IsClosed Y)
    (hR : IsClosed R) (hS : IsClosed S) (hRX : R ⊆ X) (hSY : S ⊆ Y)
    (hXe : IsPreconnected Xᶜ) (hYe : IsPreconnected Yᶜ)
    (q r : ℂ) (hq : q ∉ X) (hr : r ∉ Y)
    (g : X ≃ₜ Y)
    (hRS : ∀ x : X, (g x : ℂ) ∈ S ↔ (x : ℂ) ∈ R)
    (hfront : ∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X)
    (A : {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z})
    (B : {B : Set ℂ // ∃ z, z ∉ S ∧ B = connectedComponentIn Sᶜ z})
    (hext : B.val = connectedComponentIn Sᶜ r ↔ A.val = connectedComponentIn Rᶜ q)
    (him : A.val ≠ connectedComponentIn Rᶜ q →
      (fun a : X => (g a : ℂ)) '' {a : X | (a : ℂ) ∈ A.val} = B.val)
    (x : X) (hx : (x : ℂ) ∉ R) : (g x : ℂ) ∈ B.val ↔ (x : ℂ) ∈ A.val := by
  by_cases hA : A.val = connectedComponentIn Rᶜ q
  · have hB := hext.mpr hA
    have ht := (plane_component_transport_of_ne_exterior X Y R S hX hY hR hS
      hRX hSY hXe hYe q r hq hr g hRS hfront x hx).1
    rw [← hA, ← hB, component_eq_iff_mem R A x hx,
      component_eq_iff_mem S B (g x) (fun hh => hx ((hRS x).mp hh))] at ht
    exact ht.symm
  · rw [← him hA]
    constructor
    · rintro ⟨a, ha, he⟩
      exact g.injective (Subtype.ext he) ▸ ha
    · intro hxA
      exact ⟨x, hxA, rfl⟩

/-- Helper toward Proposition 3.9: at every integer start, deleting any
geometric edge set produces an exhaustive face bijection preserving
boundedness and point membership throughout the closed regions, including
the parts of the merged exterior lying in those regions. -/
theorem exists_deletion_face_equiv_and_region_transport
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (K : Set ℕ) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let P' := restrictDrawing P T (fun _ => Iff.rfl)
    let Q' := inheritedDrawing W H G n K
    let Q := inheritedDrawing W H G n univ
    let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
    ∃ (g : X ≃ₜ Y) (τ : P'.Face ≃ Q'.Face),
      (∀ F : P'.Face, Q'.IsUnbounded (τ F) ↔ P'.IsUnbounded F) ∧
      (∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image) ∧
      (∀ (F : P'.Face) (x : X), (x : ℂ) ∉ P'.image →
        ((g x : ℂ) ∈ (τ F).val ↔ (x : ℂ) ∈ F.val)) := by
  intro u P G T P' Q' Q X Y
  obtain ⟨hP, hQ, _, _, _, _, _, _, _, hX, hY⟩ :=
    exists_closed_region_homeomorph W H h hpast n J hfin
  obtain ⟨U, hU, _, hUX⟩ := closed_region_eq_compl_exterior u hfin
    (start_boundary_hits W h n)
  obtain ⟨V, hV, _, hVY⟩ := inherited_exterior_unique W H h hpast n J hfin
  obtain ⟨q, hqP, hqU⟩ := U.property
  obtain ⟨r, hrQ, hrV⟩ := V.property
  have hXe : IsPreconnected Xᶜ := by
    change IsPreconnected ((⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hUX, compl_compl, hqU]
    exact isPreconnected_connectedComponentIn
  have hYe : IsPreconnected Yᶜ := by
    change IsPreconnected ((⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hVY, hrV]
    exact isPreconnected_connectedComponentIn
  have hXu : ¬ Bornology.IsBounded Xᶜ := by
    change ¬ Bornology.IsBounded ((⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hUX, compl_compl]
    exact (P.isUnbounded_iff_not_isBounded U).mp hU
  have hYu : ¬ Bornology.IsBounded Yᶜ := by
    change ¬ Bornology.IsBounded ((⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hVY]
    exact (Q.isUnbounded_iff_not_isBounded V).mp hV
  have hq : q ∉ X := by
    change q ∉ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    rw [hUX]
    exact not_not.mpr (hqU ▸ mem_connectedComponentIn hqP)
  have hr : r ∉ Y := by
    change r ∈ Yᶜ
    rw [show Yᶜ = V.val from hVY, hrV]
    exact mem_connectedComponentIn hrQ
  have hRX : P'.image ⊆ X := (restrictDrawing_image_subset P T _).trans hP
  have hSY : Q'.image ⊆ Y := by
    apply Subset.trans (restricted_image_mono G (retainedDarts W n K)
      (retainedDarts W n univ) (fun _ => Iff.rfl) (fun _ => Iff.rfl) ?_) hQ
    rintro d ⟨a, _, he⟩
    exact ⟨a, mem_univ _, he⟩
  obtain ⟨g, hf, hg⟩ := exists_boundary_restriction_homeomorphs W H h hpast n J hfin
  obtain ⟨hRS, _⟩ := hg K
  obtain ⟨e, he, hext, him⟩ := exists_plane_component_equiv_isBounded X Y P'.image Q'.image
    hX hY (P'.image_isClosed (restricted_vertex_surjective P T))
    (Q'.image_isClosed (restricted_vertex_surjective G (retainedDarts W n K)))
    hRX hSY hXe hYe hXu hYu q r hq hr g hRS hf
  refine ⟨g, e, ?_, hRS, ?_⟩
  · intro F
    rw [Q'.isUnbounded_iff_not_isBounded, P'.isUnbounded_iff_not_isBounded]
    exact not_congr (he F)
  · intro F x hx
    exact component_equiv_membership X Y P'.image Q'.image hX hY
      (P'.image_isClosed (restricted_vertex_surjective P T))
      (Q'.image_isClosed (restricted_vertex_surjective G (retainedDarts W n K)))
      hRX hSY hXe hYe q r hq hr g hRS hf F (e F) (hext F) (him F) x hx

/-- Helper toward Proposition 3.9: at every integer start, every geometric
edge deletion has a face equivalence preserving boundedness. Oriented incidence
for this same equivalence remains a separate obligation. -/
theorem exists_deletion_face_equiv_isUnbounded
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (K : Set ℕ) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let P' := restrictDrawing P T (fun _ => Iff.rfl)
    let Q' := inheritedDrawing W H G n K
    ∃ τ : P'.Face ≃ Q'.Face,
      ∀ F : P'.Face, Q'.IsUnbounded (τ F) ↔ P'.IsUnbounded F := by
  intro u P G T P' Q'
  obtain ⟨_, τ, hτ, _, _⟩ :=
    exists_deletion_face_equiv_and_region_transport W H h hpast n J hfin K
  exact ⟨τ, hτ⟩

private theorem route3_paste_closed_region_cells {ι : Type*} (S T : ι → Set ℂ)
    (hS : LocallyFinite S) (hT : LocallyFinite T)
    (hclS : ∀ i, IsClosed (S i)) (hclT : ∀ i, IsClosed (T i))
    (E : ∀ i, S i ≃ₜ T i)
    (heq : ∀ i j (x : S i) (y : S j),
      (E i x : ℂ) = (E j y : ℂ) ↔ (x : ℂ) = (y : ℂ)) :
    ∃ g : (⋃ i, S i) ≃ₜ (⋃ i, T i),
      ∀ i (x : S i),
        (g ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) := by
  classical
  let A := ⋃ i, S i
  let B := ⋃ i, T i
  have hmem (x : A) : ∃ i, (x : ℂ) ∈ S i := mem_iUnion.mp x.property
  let idx (x : A) := (hmem x).choose
  have hx (x : A) : (x : ℂ) ∈ S (idx x) := (hmem x).choose_spec
  let f (x : A) : B :=
    ⟨E (idx x) ⟨x, hx x⟩, mem_iUnion.mpr ⟨idx x, (E (idx x) _).property⟩⟩
  have hf (i : ι) (x : S i) :
      (f ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (E i x : ℂ) :=
    (heq _ _ _ _).mpr rfl
  have hfi : Function.Injective f := by
    intro x y h
    have hh : (E (idx x) ⟨x, hx x⟩ : ℂ) = (E (idx y) ⟨y, hx y⟩ : ℂ) :=
      congrArg Subtype.val h
    exact Subtype.ext ((heq _ _ _ _).mp hh)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp y.property
    refine ⟨⟨(E i).symm ⟨y, hi⟩, mem_iUnion.mpr
      ⟨i, ((E i).symm ⟨y, hi⟩).property⟩⟩, ?_⟩
    exact Subtype.ext ((hf i _).trans
      (congrArg Subtype.val ((E i).apply_symm_apply _)))
  let a : ι → Set A := fun i => Subtype.val ⁻¹' S i
  let b : ι → Set B := fun i => Subtype.val ⁻¹' T i
  have ha : LocallyFinite a := hS.preimage_continuous continuous_subtype_val
  have hb : LocallyFinite b := hT.preimage_continuous continuous_subtype_val
  have hac : ⋃ i, a i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hbc : ⋃ i, b i = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hfc : Continuous f := ha.continuous hac
      (fun i => (hclS i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun x : a i => (f x.val : ℂ)) =
        fun x => (E i ⟨x.val.val, x.property⟩ : ℂ) :=
      funext fun x => hf i ⟨x.val.val, x.property⟩
    rw [he]
    exact continuous_subtype_val.comp ((E i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hinv (i : ι) (y : T i) :
      (e.symm ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ : ℂ) =
        ((E i).symm y : ℂ) := by
    have hh : e ⟨(E i).symm y,
        mem_iUnion.mpr ⟨i, ((E i).symm y).property⟩⟩ =
        ⟨y, mem_iUnion.mpr ⟨i, y.property⟩⟩ :=
      Subtype.ext ((hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply y)))
    exact congrArg Subtype.val ((congrArg e.symm hh).symm.trans (e.symm_apply_apply _))
  have hic : Continuous e.symm := hb.continuous hbc
      (fun i => (hclT i).preimage continuous_subtype_val) (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have he : (fun y : b i => (e.symm y.val : ℂ)) =
        fun y => ((E i).symm ⟨y.val.val, y.property⟩ : ℂ) :=
      funext fun y => hinv i ⟨y.val.val, y.property⟩
    change Continuous (fun y : b i => (e.symm y.val : ℂ))
    erw [he]
    exact continuous_subtype_val.comp ((E i).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)))
  exact ⟨{ toEquiv := e, continuous_toFun := hfc, continuous_invFun := hic }, hf⟩

private theorem route3_closed_region_nearby_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hvert : Function.Surjective vert)
    (d₀ : D) (F : P.Face) (z : ℂ) (hz : z ∈ F.val) :
    ∃ (d : D) (x : ℂ), x ∈ (P.arc d).image ∧ P.dartBorders d F ∧
      dist x z < dist z (P.pos (vert d₀)) + 1 := by
  obtain ⟨q, d, i, hi, hqi, hqfront, _, _, hmin⟩ :=
    P.face_nearest_segment_contact hvert d₀ F z hz
  have hdist := hmin (P.pos (vert d₀)) (Or.inl ⟨vert d₀, rfl⟩)
  by_cases hend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
  · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
      hvert F q d hi hend (frontier_subset_closure hqfront) zero_lt_one
    obtain ⟨e, hxe, he⟩ := P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
    refine ⟨e, x, hxe, he, ?_⟩
    have hnear : dist x q < 1 := Metric.mem_ball.mp hxball
    have htri := dist_triangle x q z
    rw [dist_comm q z] at htri
    linarith only [hnear, htri, hdist]
  · have hopen := mem_openSegment_of_ne_left_right
      (fun he => hend (Or.inl he.symm)) (fun he => hend (Or.inr he.symm)) hqi
    have hqnear : dist q z < dist z (P.pos (vert d₀)) + 1 := by
      rw [dist_comm]
      linarith only [hdist]
    rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hopen).mp
      (frontier_subset_closure hqfront) with hd | hd
    · exact ⟨d, q, (P.arc d).segmentAt_subset_image hi hqi, hd, hqnear⟩
    · refine ⟨flip d, q, ?_, hd, hqnear⟩
      rw [P.arc_image_flip]
      exact (P.arc d).segmentAt_subset_image hi hqi

private theorem route3_closed_region_faces_locallyFinite
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (hv : Function.Surjective vert) (d₀ : D) :
    LocallyFinite (fun F : P.Face => closure F.val) := by
  classical
  have hu := P.dartBorders_existsUnique_of_locallyFiniteVertexImage32
    (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective P hv)
  let f := fun d => (hu d).choose
  have hf (d : D) (F : P.Face) (hd : P.dartBorders d F) : f d = F :=
    ((hu d).choose_spec.2 F hd).symm
  intro z
  let p₀ := P.pos (vert d₀)
  let R := dist z p₀ + 5
  have hdarts := P.locally_finite (Metric.ball z R) Metric.isBounded_ball
  have hfinite := hdarts.image f
  refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, hfinite.subset ?_⟩
  rintro F ⟨y, hyF, hyz⟩
  obtain ⟨w, hwF, hyw⟩ := Metric.mem_closure_iff.mp hyF 1 zero_lt_one
  have hwz : dist w z < 2 := by
    have ht := dist_triangle w y z
    rw [dist_comm w y] at ht
    have hyz' := Metric.mem_ball.mp hyz
    linarith only [ht, hyw, hyz']
  obtain ⟨d, x, hxd, hdF, hxw⟩ := route3_closed_region_nearby_arc P hv d₀ F w hwF
  have hxz : x ∈ Metric.ball z R := by
    have ht := dist_triangle x w z
    have ht' := dist_triangle w z p₀
    change dist x w < dist w p₀ + 1 at hxw
    change dist x z < dist z p₀ + 5
    linarith only [ht, ht', hxw, hwz]
  exact ⟨d, ⟨x, hxz, hxd⟩, hf d F hdF⟩

/-- Helper toward Proposition 3.9: the entire run drawing and every
bounded closed face paste to the complete corresponding closed region of the
inherited drawing. Both maps are continuous; every bounded target face is hit,
including its interior, and the original vertex and edge formulas hold. -/
private theorem closed_region_homeomorph_with_incidence (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    let C := {F : Q.Face // ¬ Q.IsUnbounded F}
    let X := ⋃ F : B, closure F.val.val
    let Y := ⋃ F : C, closure F.val.val
    ∃ (hP : P.image ⊆ X) (_hQ : Q.image ⊆ Y)
      (g : X ≃ₜ Y) (τ : B ≃ C),
      (∀ v, (g ⟨P.pos v, hP (Or.inl ⟨v, rfl⟩)⟩ : ℂ) =
        G.pos (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))) ∧
      (∀ d : ℕ × Bool, ∃ φ : unitInterval ≃ₜ unitInterval,
        StrictMono φ ∧ ∀ t,
          (g ⟨(P.arc d).toPath t,
            hP (Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d))).toPath (φ t)) ∧
      (∀ F : B, g '' {x : X | (x : ℂ) ∈ closure F.val.val} =
        {y : Y | (y : ℂ) ∈ closure (τ F).val.val}) ∧
      (∀ F : B, g '' {x : X | (x : ℂ) ∈ F.val.val} =
        {y : Y | (y : ℂ) ∈ (τ F).val.val}) ∧
      (∀ x : X, (g x : ℂ) ∈ Q.image ↔ (x : ℂ) ∈ P.image) ∧
      IsClosed X ∧ IsClosed Y ∧
      (∀ (F : B) (d : retainedDarts W n univ), Q.dartBorders d (τ F).val ↔
        ∃ a : ℕ × Bool, P.dartBorders a F.val ∧
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) := by
  intro u P G Q B C X Y
  obtain ⟨Φ, τ, E, hv, ha, he, hb, _hd, hcollision⟩ :=
    exists_bounded_face_equiv W H h hpast n J hfin
  have hPv := kmswLimitDartVertex_surjective u hfin
  have hQv : Function.Surjective (restrictedVertex G (retainedDarts W n univ)) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  let a := J.dart (wholePlaneDartι (shiftWordInt W n) 0 (0, false))
  have haret : a ∈ retainedDarts W n univ := by
    rw [retained_darts_eq_image W n J univ]
    exact ⟨(0, false), mem_univ _, rfl⟩
  have hs : LocallyFinite (fun F : B => closure F.val.val) :=
    (route3_closed_region_faces_locallyFinite P hPv (0, false)).comp_injective Subtype.val_injective
  have ht : LocallyFinite (fun F : C => closure F.val.val) :=
    (route3_closed_region_faces_locallyFinite Q hQv ⟨a, haret⟩).comp_injective Subtype.val_injective
  obtain ⟨g₀, hg₀⟩ := route3_paste_closed_region_cells (fun F : B => closure F.val.val)
    (fun F : B => closure (τ F).val.val) hs (ht.comp_injective τ.injective)
    (fun _ => isClosed_closure) (fun _ => isClosed_closure) E hcollision
  have hY : (⋃ F : B, closure (τ F).val.val) = Y := by
    ext y
    constructor
    · intro hy
      obtain ⟨F, hF⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨τ F, hF⟩
    · intro hy
      obtain ⟨F, hF⟩ := mem_iUnion.mp hy
      refine mem_iUnion.mpr ⟨τ.symm F, ?_⟩
      rwa [τ.apply_symm_apply]
  let g : X ≃ₜ Y := g₀.trans (Homeomorph.setCongr hY)
  have hg (F : B) (x : closure F.val.val) :
      (g ⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩ : ℂ) = (E F x : ℂ) := hg₀ F x
  have hP : P.image ⊆ X := by
    intro x hx
    obtain ⟨F, hF, hxf⟩ := drawing_image_covered_by_bounded_frontiers u hfin
      (start_boundary_hits W h n) x hx
    exact mem_iUnion.mpr ⟨⟨F, hF⟩, frontier_subset_closure hxf⟩
  have hgraph (x : P.image) : (g ⟨x, hP x.property⟩ : ℂ) = (Φ x : ℂ) := by
    obtain ⟨F, hF, hx⟩ := drawing_image_covered_by_bounded_frontiers u hfin
      (start_boundary_hits W h n) x x.property
    exact (hg ⟨F, hF⟩ ⟨x, frontier_subset_closure hx⟩).trans (he ⟨F, hF⟩ x hx)
  have hQ : Q.image ⊆ Y := by
    intro y hy
    obtain ⟨x, hx⟩ := Φ.surjective ⟨y, hy⟩
    have heq := (hgraph x).trans (congrArg Subtype.val hx)
    change (g ⟨x, hP x.property⟩ : ℂ) = y at heq
    exact heq ▸ (g ⟨x, hP x.property⟩).property
  have hcell (F : B) : g '' {x : X | (x : ℂ) ∈ closure F.val.val} =
      {y : Y | (y : ℂ) ∈ closure (τ F).val.val} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (g x : ℂ) ∈ closure (τ F).val.val
      rw [hg F ⟨x, hx⟩]
      exact (E F ⟨x, hx⟩).property
    · intro hy
      let x := (E F).symm ⟨y, hy⟩
      refine ⟨⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩, x.property, ?_⟩
      exact Subtype.ext ((hg F x).trans (congrArg Subtype.val ((E F).apply_symm_apply _)))
  have hinterior (F : B) (x : closure F.val.val) :
      (E F x : ℂ) ∈ (τ F).val.val ↔ (x : ℂ) ∈ F.val.val := by
    have hpopen := (P.face_open_frontier_subset_image hPv F.val).1
    have hqopen := (Q.face_open_frontier_subset_image hQv (τ F).val).1
    have hh := hb F x
    rw [frontier, frontier, hpopen.interior_eq, hqopen.interior_eq] at hh
    have hx := x.property
    have hy := (E F x).property
    change ((E F x : ℂ) ∈ closure (τ F).val.val ∧
        (E F x : ℂ) ∉ (τ F).val.val) ↔
      ((x : ℂ) ∈ closure F.val.val ∧ (x : ℂ) ∉ F.val.val) at hh
    tauto
  refine ⟨hP, hQ, g, τ, ?_, ?_, hcell, ?_, ?_,
    hs.isClosed_iUnion (fun _ => isClosed_closure),
    ht.isClosed_iUnion (fun _ => isClosed_closure), _hd⟩
  · intro v
    exact (hgraph ⟨P.pos v, Or.inl ⟨v, rfl⟩⟩).trans (hv v)
  · intro d
    obtain ⟨φ, hm, hφ⟩ := ha d
    exact ⟨φ, hm, fun t => (hgraph ⟨(P.arc d).toPath t,
      Or.inr ⟨d, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩⟩).trans (hφ t)⟩
  · intro F
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (g x : ℂ) ∈ (τ F).val.val
      rw [hg F ⟨x, subset_closure hx⟩]
      exact (hinterior F _).mpr hx
    · intro hy
      let x := (E F).symm ⟨y, subset_closure hy⟩
      have hEx : (E F x : ℂ) = (y : ℂ) := congrArg Subtype.val ((E F).apply_symm_apply _)
      refine ⟨⟨x, mem_iUnion.mpr ⟨F, x.property⟩⟩, (hinterior F x).mp (hEx.symm ▸ hy), ?_⟩
      exact Subtype.ext ((hg F x).trans hEx)
  · intro x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := Φ.surjective ⟨g x, hx⟩
      have heq : g ⟨z, hP z.property⟩ = g x :=
        Subtype.ext ((hgraph z).trans (congrArg Subtype.val hz))
      exact congrArg Subtype.val (g.injective heq) ▸ z.property
    · intro hx
      exact (hgraph ⟨x, hx⟩).symm ▸ (Φ ⟨x, hx⟩).property


private theorem route3_frontier_eq_arcs
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert)
    (hvert : Function.Surjective vert) (F : P.Face) :
    frontier F.val = ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image := by
  let K := ⋃ d, ⋃ (_ : P.dartBorders d F), (P.arc d).image
  have hlf : LocallyFinite (fun d => (P.arc d).image) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z zero_lt_one, ?_⟩
    simpa only [inter_comm] using P.locally_finite (Metric.ball z 1) Metric.isBounded_ball
  have hsub (d : D) : (⋃ (_ : P.dartBorders d F), (P.arc d).image) ⊆ (P.arc d).image :=
    iUnion_subset fun _ => Subset.rfl
  have hclosed : IsClosed K := (hlf.subset hsub).isClosed_iUnion fun d =>
    isClosed_iUnion_of_finite fun _ => (P.arc d).isCompact_image.isClosed
  apply Subset.antisymm
  · intro q hqfront
    by_contra hqK
    obtain ⟨s, hs, hsafe⟩ := Metric.mem_nhds_iff.mp
      (hclosed.isOpen_compl.mem_nhds hqK)
    have hqimage := (P.face_open_frontier_subset_image hvert F).2 hqfront
    have harc : ∃ d, q ∈ (P.arc d).image := by
      rcases hqimage with ⟨v, rfl⟩ | h
      · obtain ⟨d, rfl⟩ := hvert v
        exact ⟨d, Or.inl (P.arc_start d).symm⟩
      · exact h
    obtain ⟨d, hd⟩ := harc
    have hseg : ∃ i, i + 1 < (P.arc d).points.length ∧
        q ∈ (P.arc d).segmentAt i := by
      rcases hd with hstart | ⟨i, hi, hqi⟩
      · refine ⟨0, by have := P.arc_length d; omega, ?_⟩
        rw [hstart, Polyline.segmentAt, Polyline.point_zero_eq_start]
        exact left_mem_segment ℝ _ _
      · exact ⟨i, hi, hqi⟩
    obtain ⟨i, hi, hqi⟩ := hseg
    by_cases hqend : q = (P.arc d).point i ∨ q = (P.arc d).point (i + 1)
    · obtain ⟨x, hx, hxball, hnot⟩ := P.face_endpoint_frontier_not_vertex_mem_ball
        hvert F q d hi hqend (frontier_subset_closure hqfront) hs
      obtain ⟨e, hxe, heF⟩ :=
        P.exists_mem_arc_dartBorders_of_frontier_not_vertex hvert F hx hnot
      exact hsafe hxball (mem_iUnion₂.mpr ⟨e, heF, hxe⟩)
    · have hqopen := mem_openSegment_of_ne_left_right
        (fun he => hqend (Or.inl he.symm)) (fun he => hqend (Or.inr he.symm)) hqi
      rcases (P.mem_closure_face_openSegment_iff_dartBorders hvert d F hi hqopen).mp
          (frontier_subset_closure hqfront) with hF | hF
      · exact hqK (mem_iUnion₂.mpr
          ⟨d, hF, (P.arc d).segmentAt_subset_image hi hqi⟩)
      · apply hqK
        apply mem_iUnion₂.mpr
        refine ⟨flip d, hF, ?_⟩
        rw [P.arc_image_flip]
        exact (P.arc d).segmentAt_subset_image hi hqi
  · intro q hq
    obtain ⟨d, hd, hqd⟩ := mem_iUnion₂.mp hq
    exact P.dartBorders_arc_subset_frontier hvert d F hd hqd


private theorem route3_restricted_image_iff_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (T : Set D)
    (hT : ∀ d, d ∈ T ↔ flip d ∈ T) (z : ℂ) :
    z ∈ (restrictDrawing P T hT).image ↔ ∃ d ∈ T, z ∈ (P.arc d).image := by
  have hv : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, d, hd, hdv⟩
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩
  rw [(restrictDrawing P T hT).image_eq_union_arcs hv]
  constructor
  · intro hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    exact ⟨d.val, d.property, hd⟩
  · rintro ⟨d, hd, hz⟩
    exact mem_iUnion.mpr ⟨⟨d, hd⟩, hz⟩


/-- Helper toward Proposition 3.9: one closed-region map simultaneously
preserves bounded full-face interiors, their oriented incidences, the exterior
boundary, and every retained geometric drawing. -/
theorem exists_compatible_closed_region_transport
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0)) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let Q := inheritedDrawing W H G n univ
    let B := {F : P.Face // ¬ P.IsUnbounded F}
    let C := {F : Q.Face // ¬ Q.IsUnbounded F}
    let X := ⋃ F : B, closure F.val.val
    let Y := ⋃ F : C, closure F.val.val
    ∃ (g : X ≃ₜ Y) (σ : B ≃ C),
      (∀ F : B, g '' {x : X | (x : ℂ) ∈ F.val.val} =
        {y : Y | (y : ℂ) ∈ (σ F).val.val}) ∧
      (∀ (F : B) (d : retainedDarts W n univ), Q.dartBorders d (σ F).val ↔
        ∃ a : ℕ × Bool, P.dartBorders a F.val ∧
          J.dart (wholePlaneDartι (shiftWordInt W n) 0 a) = d.val) ∧
      (∀ x : X, (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X) ∧
      ∀ K : Set ℕ,
        let P' := restrictDrawing P {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl)
        let Q' := inheritedDrawing W H G n K
        ∀ x : X, (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image := by
  intro u P G Q B C X Y
  obtain ⟨hP, _, g, σ, _, ha, _, hopen, _, _, _, hinc⟩ :=
    closed_region_homeomorph_with_incidence W H h hpast n J hfin
  obtain ⟨U, hU, hu, hX⟩ := closed_region_eq_compl_exterior u hfin
    (start_boundary_hits W h n)
  obtain ⟨V, hV, hv, hYc⟩ := inherited_exterior_unique W H h hpast n J hfin
  have hY : Y = V.valᶜ := compl_injective (by rw [compl_compl]; exact hYc)
  have hPv := kmswLimitDartVertex_surjective u hfin
  have hQv := restricted_vertex_surjective G (retainedDarts W n univ)
  obtain ⟨_, _, hext⟩ := exists_bounded_face_incidence W H h hpast n J hfin
  obtain ⟨U', hU', _, hbU⟩ := monotoneFamilyDrawing_faceClassification_twoSided
    u hfin (start_boundary_hits W h n)
  have hborderU (a : ℕ × Bool) : P.dartBorders a U ↔ limitExternalDart u a :=
    hu U' hU' ▸ hbU a
  let D (a : ℕ × Bool) : retainedDarts W n univ :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), by
      rw [retained_darts_eq_image W n J univ]
      exact ⟨a, mem_univ _, rfl⟩⟩
  have hD (a : ℕ × Bool) : Q.dartBorders (D a) V ↔ P.dartBorders a U := by
    rw [hborderU]
    constructor
    · intro hd
      exact (hext a (D a) rfl).mp ⟨V, hV, hd⟩
    · intro hd
      obtain ⟨F, hF, hdF⟩ := (hext a (D a) rfl).mpr hd
      exact hv F hF ▸ hdF
  have hfront (x : X) : (g x : ℂ) ∈ frontier V.val ↔ (x : ℂ) ∈ frontier U.val := by
    constructor
    · intro hx
      rw [route3_frontier_eq_arcs Q hQv V] at hx
      obtain ⟨d, hdV, hxd⟩ := mem_iUnion₂.mp hx
      have hd := (Set.ext_iff.mp (retained_darts_eq_image W n J univ) d.val).mp d.property
      obtain ⟨a, _, ha'⟩ := hd
      have hDa : D a = d := Subtype.ext ha'
      have haU : P.dartBorders a U := (hD a).mp (hDa.symm ▸ hdV)
      rw [← Polyline.range_toPath] at hxd
      obtain ⟨s, hs⟩ := hxd
      obtain ⟨φ, _, hφ⟩ := ha a
      let t := φ.symm s
      let y : X := ⟨(P.arc a).toPath t,
        hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩
      have hgy : (g y : ℂ) = (g x : ℂ) := by
        rw [hφ]
        change (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath
          (φ (φ.symm s)) = _
        rw [φ.apply_symm_apply]
        exact (congrArg (fun c : WholePlaneDart W => (G.arc c).toPath s) ha').trans hs
      have hyx : y = x := g.injective (Subtype.ext hgy)
      have hyU : (y : ℂ) ∈ frontier U.val := P.dartBorders_arc_subset_frontier hPv a U haU
        ((Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩)
      exact hyx ▸ hyU
    · intro hx
      rw [route3_frontier_eq_arcs P hPv U] at hx
      obtain ⟨a, haU, hxa⟩ := mem_iUnion₂.mp hx
      rw [← Polyline.range_toPath] at hxa
      obtain ⟨t, ht⟩ := hxa
      obtain ⟨φ, _, hφ⟩ := ha a
      have hx' : (⟨(P.arc a).toPath t,
          hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : X) = x :=
        Subtype.ext ht
      rw [← hx', hφ]
      exact Q.dartBorders_arc_subset_frontier hQv (D a) V ((hD a).mpr haU)
        ((Polyline.range_toPath _).symm ▸ ⟨φ t, rfl⟩)

  have hbdy (x : X) : (g x : ℂ) ∈ frontier Y ↔ (x : ℂ) ∈ frontier X := by
    have hfX : frontier X = frontier U.val :=
      (congrArg frontier hX).trans (frontier_compl _)
    have hfY : frontier Y = frontier V.val :=
      (congrArg frontier hY).trans (frontier_compl _)
    simpa only [hfX, hfY] using hfront x
  refine ⟨g, σ, hopen, hinc, hbdy, fun K => ?_⟩
  intro P' Q'
  have himage (x : X) : (g x : ℂ) ∈ Q'.image ↔ (x : ℂ) ∈ P'.image := by
    constructor
    · intro hx
      obtain ⟨d, hd, hxd⟩ := (route3_restricted_image_iff_arc G
        (retainedDarts W n K) (fun _ => Iff.rfl) _).mp hx
      rw [retained_darts_eq_image W n J K] at hd
      obtain ⟨a, haK, rfl⟩ := hd
      obtain ⟨φ, _, hφ⟩ := ha a
      have ht : (g x : ℂ) ∈ range
          (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath := by
        rw [Polyline.range_toPath]
        exact hxd
      obtain ⟨t, ht⟩ := ht
      let z : X := ⟨(P.arc a).toPath (φ.symm t), hP (Or.inr ⟨a, by
        rw [← Polyline.range_toPath]
        exact ⟨φ.symm t, rfl⟩⟩)⟩
      have hz : g z = g x := by
        apply Subtype.ext
        exact (hφ (φ.symm t)).trans (by rw [φ.apply_symm_apply]; exact ht)
      have hzx : (z : ℂ) = (x : ℂ) := congrArg Subtype.val (g.injective hz)
      apply (route3_restricted_image_iff_arc P {d : ℕ × Bool | d.1 ∈ K}
        (fun _ => Iff.rfl) _).mpr
      refine ⟨a, haK, ?_⟩
      rw [← hzx, ← Polyline.range_toPath]
      exact ⟨φ.symm t, rfl⟩
    · intro hx
      obtain ⟨a, haK, hxa⟩ := (route3_restricted_image_iff_arc P
        {d : ℕ × Bool | d.1 ∈ K} (fun _ => Iff.rfl) _).mp hx
      have ht : (x : ℂ) ∈ range (P.arc a).toPath := by
        rw [Polyline.range_toPath]
        exact hxa
      obtain ⟨t, ht⟩ := ht
      obtain ⟨φ, _, hφ⟩ := ha a
      apply (route3_restricted_image_iff_arc G (retainedDarts W n K)
        (fun _ => Iff.rfl) _).mpr
      refine ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a), ?_, ?_⟩
      · rw [retained_darts_eq_image W n J K]
        exact ⟨a, haK, rfl⟩
      · have he : (g x : ℂ) =
            (G.arc (J.dart (wholePlaneDartι (shiftWordInt W n) 0 a))).toPath (φ t) := by
          have hz : (⟨(P.arc a).toPath t,
              hP (Or.inr ⟨a, (Polyline.range_toPath _).symm ▸ ⟨t, rfl⟩⟩)⟩ : X) = x :=
            Subtype.ext ht
          exact hz ▸ hφ t
        rw [he, ← Polyline.range_toPath]
        exact ⟨φ t, rfl⟩

  exact himage

private theorem dartBorders_iff_full_face_subset
    {D V E U : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    {flip' : E → E} {rot' : Equiv.Perm E} {vert' : E → U}
    (P : PLDrawing D V flip rot vert) (Q : PLDrawing E U flip' rot' vert')
    (hQP : Q.image ⊆ P.image) (a : D) (b : E) (hab : Q.arc b = P.arc a)
    (F : P.Face) (hF : P.dartBorders a F) (B : Q.Face) :
    Q.dartBorders b B ↔ F.val ⊆ B.val := by
  constructor
  · intro hB
    obtain ⟨r, hr, hrF⟩ := hF
    obtain ⟨s, hs, hsB⟩ := hB
    let t := min r s / 2
    have ht : 0 < t := half_pos (lt_min hr hs)
    have htr : t < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
    have hts : t < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
    let z := (P.arc a).start + (t : ℂ) *
      ((P.arc a).initialDirection + (t : ℂ) * Complex.I * (P.arc a).initialDirection)
    have hzF : z ∈ F.val := hrF t t ht htr ht htr
    have hzB : z ∈ B.val := by
      have hh := hsB t t ht hts ht hts
      rw [hab] at hh
      exact hh
    obtain ⟨x, _, hx⟩ := F.property
    obtain ⟨y, _, hy⟩ := B.property
    have hFz := hx.trans (connectedComponentIn_eq (hx ▸ hzF))
    have hBz := hy.trans (connectedComponentIn_eq (hy ▸ hzB))
    rw [hFz, hBz]
    exact connectedComponentIn_mono z (compl_subset_compl.mpr hQP)
  · intro hFB
    obtain ⟨r, hr, hrF⟩ := hF
    refine ⟨r, hr, fun t ε ht htr hε hεr => ?_⟩
    rw [hab]
    exact hFB (hrF t ε ht htr hε hεr)

private theorem exterior_subset_component_iff
    (X R : Set ℂ) (hRX : R ⊆ X) (hXe : IsPreconnected Xᶜ)
    (q : ℂ) (hq : q ∉ X)
    (A : {A : Set ℂ // ∃ z, z ∉ R ∧ A = connectedComponentIn Rᶜ z}) :
    Xᶜ ⊆ A.val ↔ A.val = connectedComponentIn Rᶜ q := by
  constructor
  · intro hsub
    exact ((component_eq_iff_mem R A q (fun hh => hq (hRX hh))).mpr (hsub hq)).symm
  · intro he
    rw [he]
    exact hXe.subset_connectedComponentIn hq (compl_subset_compl.mpr hRX)


/-- Helper toward Proposition 3.9: deleting any retained geometric edge
set at any integer start preserves all full-plane faces, their boundedness,
and oriented incidence under one face equivalence. -/
theorem exists_deletion_face_equiv_and_incidence
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (K : Set ℕ) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let P' := restrictDrawing P T (fun _ => Iff.rfl)
    let Q' := inheritedDrawing W H G n K
    ∃ τ : P'.Face ≃ Q'.Face,
      (∀ F : P'.Face, Q'.IsUnbounded (τ F) ↔ P'.IsUnbounded F) ∧
      (∀ (a : T) (d : retainedDarts W n K),
        J.dart (wholePlaneDartι (shiftWordInt W n) 0 a.val) = d.val →
        ∀ F : P'.Face, Q'.dartBorders d (τ F) ↔ P'.dartBorders a F) := by
  intro u P G T P' Q'
  let Q := inheritedDrawing W H G n univ
  let X := ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
  let Y := ⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val
  obtain ⟨hP, hQ, _, _, _, _, _, _, _, hX, hY⟩ :=
    exists_closed_region_homeomorph W H h hpast n J hfin
  obtain ⟨U, hU, huniqU, hUX⟩ := closed_region_eq_compl_exterior u hfin
    (start_boundary_hits W h n)
  obtain ⟨V, hV, huniqV, hVY⟩ := inherited_exterior_unique W H h hpast n J hfin
  obtain ⟨q, hqP, hqU⟩ := U.property
  obtain ⟨r, hrQ, hrV⟩ := V.property
  have hXe : IsPreconnected Xᶜ := by
    change IsPreconnected ((⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hUX, compl_compl, hqU]
    exact isPreconnected_connectedComponentIn
  have hYe : IsPreconnected Yᶜ := by
    change IsPreconnected ((⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hVY, hrV]
    exact isPreconnected_connectedComponentIn
  have hXu : ¬ Bornology.IsBounded Xᶜ := by
    change ¬ Bornology.IsBounded ((⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hUX, compl_compl]
    exact (P.isUnbounded_iff_not_isBounded U).mp hU
  have hYu : ¬ Bornology.IsBounded Yᶜ := by
    change ¬ Bornology.IsBounded ((⋃ F : {F : Q.Face // ¬ Q.IsUnbounded F}, closure F.val.val)ᶜ)
    rw [hVY]
    exact (Q.isUnbounded_iff_not_isBounded V).mp hV
  have hq : q ∉ X := by
    change q ∉ ⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val
    rw [hUX]
    exact not_not.mpr (hqU ▸ mem_connectedComponentIn hqP)
  have hr : r ∉ Y := by
    change r ∈ Yᶜ
    rw [show Yᶜ = V.val from hVY, hrV]
    exact mem_connectedComponentIn hrQ
  have hRX : P'.image ⊆ X := (restrictDrawing_image_subset P T _).trans hP
  have hSY : Q'.image ⊆ Y := by
    apply Subset.trans (restricted_image_mono G (retainedDarts W n K)
      (retainedDarts W n univ) (fun _ => Iff.rfl) (fun _ => Iff.rfl) ?_) hQ
    rintro d ⟨a, _, he⟩
    exact ⟨a, mem_univ _, he⟩
  obtain ⟨g, σ, hopen, hinc, hf, hg⟩ :=
    exists_compatible_closed_region_transport W H h hpast n J hfin
  have hRS := hg K
  obtain ⟨e, he, hext, him⟩ := exists_plane_component_equiv_isBounded X Y P'.image Q'.image
    hX hY (P'.image_isClosed (restricted_vertex_surjective P T))
    (Q'.image_isClosed (restricted_vertex_surjective G (retainedDarts W n K)))
    hRX hSY hXe hYe hXu hYu q r hq hr g hRS hf

  have hmem (A : P'.Face) (x : X) (hx : (x : ℂ) ∉ P'.image) :
      (g x : ℂ) ∈ (e A).val ↔ (x : ℂ) ∈ A.val :=
    component_equiv_membership X Y P'.image Q'.image hX hY
      (P'.image_isClosed (restricted_vertex_surjective P T))
      (Q'.image_isClosed (restricted_vertex_surjective G (retainedDarts W n K)))
      hRX hSY hXe hYe q r hq hr g hRS hf A (e A) (hext A) (him A) x hx
  have hsubP : P'.image ⊆ P.image := restrictDrawing_image_subset P T _
  have hsubQ : Q'.image ⊆ Q.image := by
    apply restricted_image_mono G (retainedDarts W n K) (retainedDarts W n univ)
      (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    rintro d ⟨a, _, ha⟩
    exact ⟨a, mem_univ _, ha⟩
  refine ⟨e, ?_, ?_⟩
  · intro A
    rw [Q'.isUnbounded_iff_not_isBounded, P'.isUnbounded_iff_not_isBounded]
    exact not_congr (he A)
  · intro a d had A
    let d₀ : retainedDarts W n univ := ⟨d.val, by
      obtain ⟨b, _, hb⟩ := d.property
      exact ⟨b, mem_univ _, hb⟩⟩
    have harc : Q'.arc d = Q.arc d₀ := by
      rw [inherited_arc, inherited_arc]
    obtain ⟨F, hFa, _⟩ := dart_borders_unique u hfin (start_boundary_hits W h n) a.val
    have hsource := dartBorders_iff_full_face_subset P P' hsubP a.val a
      (restrictDrawing_arc P T _ a) F hFa A
    by_cases hFu : P.IsUnbounded F
    · have hFU : F = U := huniqU F hFu
      obtain ⟨_, _, houter⟩ := exists_bounded_face_incidence W H h hpast n J hfin
      obtain ⟨U₀, hU₀, _, hbU₀⟩ := monotoneFamilyDrawing_faceClassification_twoSided
        u hfin (start_boundary_hits W h n)
      have haU₀ : P.dartBorders a.val U₀ := (huniqU U₀ hU₀).symm ▸ (hFU ▸ hFa)
      obtain ⟨V₀, hV₀, hdV₀⟩ := (houter a.val d₀ had).mpr ((hbU₀ a.val).mp haU₀)
      have hdV : Q.dartBorders d₀ V := huniqV V₀ hV₀ ▸ hdV₀
      refine (dartBorders_iff_full_face_subset Q Q' hsubQ d₀ d harc V hdV (e A)).trans
        (Iff.trans ?_ hsource.symm)
      change V.val ⊆ (e A).val ↔ F.val ⊆ A.val
      rw [hFU]
      have hUXc : Xᶜ = U.val := by
        change (⋃ F : {F : P.Face // ¬ P.IsUnbounded F}, closure F.val.val)ᶜ = U.val
        rw [hUX, compl_compl]
      have hsourceExt := exterior_subset_component_iff X P'.image hRX hXe q hq A
      have htargetExt := exterior_subset_component_iff Y Q'.image hSY hYe r hr (e A)
      rw [hUXc] at hsourceExt
      rw [show Yᶜ = V.val from hVY] at htargetExt
      exact htargetExt.trans ((hext A).trans hsourceExt.symm)
    · let B := σ ⟨F, hFu⟩
      have hdB : Q.dartBorders d₀ B.val := (hinc ⟨F, hFu⟩ d₀).mpr ⟨a.val, hFa, had⟩
      refine (dartBorders_iff_full_face_subset Q Q' hsubQ d₀ d harc B.val hdB (e A)).trans
        (Iff.trans ?_ hsource.symm)
      change B.val.val ⊆ (e A).val ↔ F.val ⊆ A.val
      have hFX : F.val ⊆ X := fun z hz => mem_iUnion.mpr ⟨⟨F, hFu⟩, subset_closure hz⟩
      have hBY : B.val.val ⊆ Y := fun z hz => mem_iUnion.mpr ⟨B, subset_closure hz⟩
      constructor
      · intro hBA z hzF
        let x : X := ⟨z, hFX hzF⟩
        have hgF : (g x : ℂ) ∈ B.val.val := by
          have hh := mem_image_of_mem g (show x ∈ {x : X | (x : ℂ) ∈ F.val} from hzF)
          rw [hopen ⟨F, hFu⟩] at hh
          exact hh
        exact (hmem A x (fun hh => P.face_subset_compl F hzF (hsubP hh))).mp (hBA hgF)
      · intro hFA z hzB
        let y : Y := ⟨z, hBY hzB⟩
        have hy : y ∈ g '' {x : X | (x : ℂ) ∈ F.val} := by
          rw [hopen ⟨F, hFu⟩]
          exact hzB
        obtain ⟨x, hxF, hxy⟩ := hy
        have hh := (hmem A x (fun hh => P.face_subset_compl F hxF (hsubP hh))).mpr (hFA hxF)
        have hey : (g x : ℂ) = z := congrArg Subtype.val hxy
        exact hey ▸ hh

/-- Helper toward Proposition 3.9: all open complementary regions of every
retained shifted drawing correspond to the actual regions in every geometric
representative, preserving externality and oriented left incidence. -/
theorem representative_deletion_face_regions
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (K : Set ℕ) :
    let u := shiftedStream (shiftWordInt W n) 0
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι (shiftWordInt W n) 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι (shiftWordInt W n) 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp
        (J.dart (wholePlaneDartι (shiftWordInt W n) 0 d)))
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    ∃ R : Q.Face → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F) := by
  intro u G S V E D P T Q
  obtain ⟨τ, hb, hi⟩ := exists_deletion_face_equiv_and_incidence W H h hpast n J hfin K
  let R := fun F : Q.Face => I.h '' (τ F).val
  have hrange := representative_faceRegions W H h hpast hp A I n J K
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · intro F F' he
    apply τ.injective
    apply Subtype.ext
    exact Set.image_injective.mpr I.h.injective he
  · ext B
    constructor
    · rintro ⟨F, rfl⟩
      rw [hrange]
      exact ⟨τ F, rfl⟩
    · intro hB
      rw [hrange] at hB
      obtain ⟨F, rfl⟩ := hB
      refine ⟨τ.symm F, ?_⟩
      change I.h '' (τ (τ.symm F)).val = I.h '' F.val
      rw [τ.apply_symm_apply]
  · intro F
    exact I.h.isOpenMap _ (inherited_face_isOpen W H G n K (τ F))
  · intro F
    exact (representative_external W H h hpast hp A I n K (τ F)).trans (hb F)
  · intro d F
    let a : retainedDarts W n K :=
      ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 d.val), by
        rw [retained_darts_eq_image W n J K]
        exact ⟨d.val, d.property, rfl⟩⟩
    exact (representative_face_side W H h hpast hp A I n K a (τ F)).trans
      (hi d a rfl F)


/- EXACT REMAINING OBLIGATIONS (comments only).

The first a87 obligation, the complete deletion face equivalence with
boundedness and oriented incidence, is proved by
exists_deletion_face_equiv_and_incidence above. All representative face clauses
are proved by representative_deletion_face_regions. No qualifier is removed.

The next unresolved step is the following restricted-rotation comparison.
It is stated here with all binders; it is not an assumed premise.

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H) (n : ℤ) (J : WholePlaneStartIso W n)
  (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
  (K : Set ℕ),
  let u := shiftedStream (shiftWordInt W n) 0
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let T := {d : ℕ × Bool | d.1 ∈ K}
  ∀ (a : T) (d : retainedDarts W n K),
    J.dart (wholePlaneDartι (shiftWordInt W n) 0 a.val) = d.val →
    (drawingFirstReturnPerm G (retainedDarts W n K) d).val =
      J.dart (wholePlaneDartι (shiftWordInt W n) 0
        (drawingFirstReturnPerm P T a).val)

This rotation statement would combine with the proved representative face
clauses to supply every clause of the next target. The unchanged complete
targets, including their law and stopping-time clauses, follow.

2. Exact Proposition 5.1 comparison (ShiftedStartGeometry.lean:425).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
  (n : ℤ) (J : WholePlaneStartIso W n),
  let u := fun i => futureMapShiftedCodePath n W (i + 1)
  ∀ (hflow : HasFlowLineHits u)
    (hhat : hatLimitFiniteIncidence u)
    (hprime : primedLimitFiniteIncidence u)
    (hb : BoundaryHitWitnesses u),
  ∀ K : Set ℕ,
    K = {e | MhatGeometricEdge u e} ∨ K = {e | primeGeomEdge u hprime hb e} →
    let U := shiftWordInt W n
    let S := uibotWholePlaneSourceDomain W H G hp
    let V := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
    let E := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
    let D := fun d => intrinsicFutureDartEquiv (A := S) I
      (uibotCut2SourceDartEquiv W H h hpast hp (J.dart (wholePlaneDartι U 0 d)))
    let P := monotoneFamilyDrawing u hhat (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    let Q := restrictDrawing P T (fun _ => Iff.rfl)
    ∃ R : Q.Face → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (V '' intrinsicConsumer51RunVertices u K) (E '' K)) ∧
      (∀ F, IsOpen (R F)) ∧
      (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)

3. Exact Lemma 5.2 analogue (ShiftedStartGeometry.lean:463).

∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (h : BoundaryHitWitnesses (shiftedStream W 0))
  (hpast : BoundaryHitWitnesses (kmswPastCode W))
  (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
  (A : D39DomainRootedMap.{0}),
  let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
  ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
    (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (k : ℤ),
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := fun i => w (t + i)
  ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
  let S := uibotWholePlaneSourceDomain W H G hp
  let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
  let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
  let D := fun d : ℕ × Bool => intrinsicFutureDartEquiv (A := S) I
    (uibotCut2SourceDartEquiv W H h hpast hp
      (wholePlaneDartι W 0 (kmswWindowEdgeMapInf w t d.1, d.2)))
  let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
  let T := {d : ℕ × Bool | MhatGeometricEdge u d.1}
  let Q := hatRealizedDrawing u hfin
  ∃ R : Q.Face → Set ℂ,
    Function.Injective R ∧
    Set.range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
    (∀ F, IsOpen (R F)) ∧
    (∀ F, (¬ Bornology.IsBounded (R F)) ↔ Q.IsUnbounded F) ∧
    (∀ d : T, intrinsicFutureRotation A (Set.range E)
      (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
    (∀ (d : T) (F : Q.Face),
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F)


4. Exact nonzero-stopping-time face-orbit comparison
(IntrinsicConsumer52FaceOrbits.lean:376). Every binder is retained.

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
  ∀ (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H) hp)
      (uibotWholePlaneSourceRoot W H
        (WholePlanePastGlueDrawing.glueDrawing W h hpast H)) A.map A.root)
    (k : ℤ),
    let t := boundaryHitTime (shiftedStream W 0) h k
    let u := fun i => shiftedStream W 0 (t + i)
    ∀ (hτ : HasFlowLineHits u) (hfin : hatLimitFiniteIncidence u),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
    let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
    ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      (∀ q, IsOpen (R q)) ∧
      (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Quotient.mk _ d = q) ∧
      (∀ q, (¬ Bornology.IsBounded (R q)) ↔
        q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
        (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d)


5. Exact Lemma 5.2 assembly (IntrinsicConsumer52FaceOrbits.lean:419).

  ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
    let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved W
    ∃ (H : WholePlaneRotationHypothesis W)
      (h : BoundaryHitWitnesses (shiftedStream W 0))
      (hpast : BoundaryHitWitnesses (kmswPastCode W))
      (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let hLL := fun (k : ℤ) (_ : k ≤ 0) => hp
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
      Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
      ∃! C : IntrinsicFutureCut2 A,
        (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
        ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root,
        let t := intrinsicStageBoundaryTime W H h hLL G hp A I
        t 0 = 0 ∧
        ∀ k : ℤ,
          IsLeast {n : ℕ | C.x k = intrinsicStageActiveInitial A
            (intrinsicStageActiveEdges W H G hp A I) n} (t k) ∧
          t k = boundaryHitTime (shiftedStream W 0) h k ∧
          boundaryCodeStoppingTime k (shiftedCodePath W 0) = (t k : ℕ∞) ∧
          wholePlaneIIDCodeMeasure.map (boundaryFutureCode k) =
            wholePlaneIIDCodeMeasure.map (boundaryFutureCode 0) ∧
          wholePlaneIIDCodeMeasure.map (hatLawCodes ∘ boundaryFutureCode k) =
            iidCodeMeasure.map (fun ω => pitmanCode (fun i => ω (i + 1))) ∧
          (fun i => boundaryFutureCode k W (i + 1)) =
            (fun i => shiftedStream W 0 (t k + i)) ∧
          (∃ hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)),
            hatLawCodes (boundaryFutureCode k W) =
              hatCodes (fun i => shiftedStream W 0 (t k + i)) hτ) ∧
          M0CutShiftContainment W H h hLL k ∧
          boundaryFutureRootedMapClause W h k ∧
          IntrinsicStageShiftContainment W A
            (fun j => I.vertexEquiv (wholePlaneVertexι W 0 j))
            (fun j => I.edgeEquiv (wholePlaneEdgeι W 0 j))
            C.edges C.missing (C.x k) (t k) ∧
          ∃ (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t k + i)))
            (hfin : hatLimitFiniteIncidence (fun i => shiftedStream W 0 (t k + i))),
          let u := fun i => shiftedStream W 0 (t k + i)
          let V := intrinsicConsumer52HatVertex W H G hp A I (t k) hτ
          let E := intrinsicConsumer52HatEdge W H G hp A I (t k) hτ
          let D := intrinsicConsumer52HatDart W H h hpast hp A I (t k) hτ
          hatLawCodes (boundaryFutureCode k W) = hatCodes u hτ ∧
          hatRootedMapClause u hτ hfin ∧
          Function.Injective E ∧
          E 0 = (intrinsicStageActiveEdges W H G hp A I (t k)).val ∧
          (∀ e : ℕ, ∃ he : ¬ A.map.missing (E e),
            A.map.tail ⟨E e, he⟩ = V (edgeWest (hatCodes u hτ) e) ∧
            A.map.head ⟨E e, he⟩ = V (edgeEast (hatCodes u hτ) e)) ∧
          (∀ d, intrinsicFutureRotation A (Set.range E)
            (D (kmswInfRot (hatCodes u hτ) (hatCodes_finiteIncidence u hτ hfin) d))
            (D d)) ∧
          ∃ R : HatFaceOrbit u hτ hfin → Set ℂ,
            Function.Injective R ∧
            Set.range R = intrinsicConsumer51FaceRegions
              (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
            (∀ q, IsOpen (R q)) ∧
            (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
              Quotient.mk _ d = q) ∧
            (∀ q, (¬ Bornology.IsBounded (R q)) ↔
              q = Quotient.mk _ futureMapOuterDart) ∧
            (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
              (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d) -/

end DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute3
