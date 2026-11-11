/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation4







public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open Set Topology
open scoped Topology

/-- Helper toward Proposition 3.9: the global affine edge parameter is the
identity for a preserved storage order and central reflection for a flip. -/
@[expose] def uibotClassSeparation5_edgeParam
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) (e : E) : unitInterval ≃ₜ unitInterval :=
  if I.flip e then unitInterval.symmHomeomorph else Homeomorph.refl _

private theorem parameter_cases (t : unitInterval) :
    t = 0 ∨ t = 1 ∨ t ∈ openParams := by
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne t.property.1
    (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))⟩)

private theorem arc_collision {V E : Type*} (D : PlaneGraphDrawing V E)
    (e f : E) (t s : unitInterval) (h : D.arc e t = D.arc f s) :
    (e = f ∧ t = s) ∨
      ∃ v, ((t = 0 ∧ D.src e = v) ∨ (t = 1 ∧ D.tgt e = v)) ∧
        ((s = 0 ∧ D.src f = v) ∨ (s = 1 ∧ D.tgt f = v)) := by
  rcases parameter_cases t with rfl | rfl | ht
  · right
    refine ⟨D.src e, Or.inl ⟨rfl, rfl⟩, ?_⟩
    rcases parameter_cases s with rfl | rfl | hs
    · exact Or.inl ⟨rfl, (D.pos_injective (by simpa only [Path.source] using h)).symm⟩
    · exact Or.inr ⟨rfl, (D.pos_injective (by simpa only [Path.source, Path.target] using h)).symm⟩
    · exact (D.openArc_avoids f (D.src e) ⟨s, hs, by simpa only [Path.source] using h.symm⟩).elim
  · right
    refine ⟨D.tgt e, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rcases parameter_cases s with rfl | rfl | hs
    · exact Or.inl ⟨rfl, (D.pos_injective (by simpa only [Path.source, Path.target] using h)).symm⟩
    · exact Or.inr ⟨rfl, (D.pos_injective (by simpa only [Path.target] using h)).symm⟩
    · exact (D.openArc_avoids f (D.tgt e) ⟨s, hs, by simpa only [Path.target] using h.symm⟩).elim
  · rcases parameter_cases s with rfl | rfl | hs
    · exact (D.openArc_avoids e (D.src f) ⟨t, ht, by simpa only [Path.source] using h⟩).elim
    · exact (D.openArc_avoids e (D.tgt f) ⟨t, ht, by simpa only [Path.target] using h⟩).elim
    · have hef : e = f := by
        by_contra hn
        exact Set.disjoint_left.mp (D.openArc_disjoint e f hn)
          ⟨t, ht, rfl⟩ ⟨s, hs, h.symm⟩
      subst f
      exact Or.inl ⟨rfl, D.arc_injOn e ht hs h⟩

/-- Helper toward Proposition 3.9: both endpoints of every global affine
edge map agree with the one global vertex map. -/
theorem uibotClassSeparation5_edgeParam_endpoints
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) (e : E) :
    N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e 0) =
      N.toPlaneMapWithMissing.pos (I.vertexEquiv (M.toPlaneMapWithMissing.src e)) ∧
    N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e 1) =
      N.toPlaneMapWithMissing.pos (I.vertexEquiv (M.toPlaneMapWithMissing.tgt e)) := by
  constructor
  · rw [I.src_map e]
    cases he : I.flip e <;> simp [uibotClassSeparation5_edgeParam, he]
  · rw [I.tgt_map e]
    cases he : I.flip e <;> simp [uibotClassSeparation5_edgeParam, he]

private theorem edgeParam_collision_forward
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) (e f : E) (t s : unitInterval)
    (h : M.toPlaneMapWithMissing.arc e t = M.toPlaneMapWithMissing.arc f s) :
    N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e t) =
      N.toPlaneMapWithMissing.arc (I.edgeEquiv f) (uibotClassSeparation5_edgeParam I f s) := by
  rcases arc_collision M.toPlaneMapWithMissing.toPlaneGraphDrawing e f t s h with
    ⟨rfl, rfl⟩ | ⟨v, ht, hs⟩
  · rfl
  · have left : N.toPlaneMapWithMissing.arc (I.edgeEquiv e)
        (uibotClassSeparation5_edgeParam I e t) = N.toPlaneMapWithMissing.pos (I.vertexEquiv v) := by
      rcases ht with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
      · exact (uibotClassSeparation5_edgeParam_endpoints I e).1.trans
          (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
      · exact (uibotClassSeparation5_edgeParam_endpoints I e).2.trans
          (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
    have right : N.toPlaneMapWithMissing.arc (I.edgeEquiv f)
        (uibotClassSeparation5_edgeParam I f s) = N.toPlaneMapWithMissing.pos (I.vertexEquiv v) := by
      rcases hs with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
      · exact (uibotClassSeparation5_edgeParam_endpoints I f).1.trans
          (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
      · exact (uibotClassSeparation5_edgeParam_endpoints I f).2.trans
          (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
    exact left.trans right.symm

/-- Helper toward Proposition 3.9: the global affine edge parameters preserve
and reflect every point coincidence, including shared vertices and loops. -/
theorem uibotClassSeparation5_edgeParam_collision_iff
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) (e f : E) (t s : unitInterval) :
    M.toPlaneMapWithMissing.arc e t = M.toPlaneMapWithMissing.arc f s ↔
      N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e t) =
        N.toPlaneMapWithMissing.arc (I.edgeEquiv f) (uibotClassSeparation5_edgeParam I f s) := by
  constructor
  · exact edgeParam_collision_forward I e f t s
  · intro h
    have hh := edgeParam_collision_forward I.symm (I.edgeEquiv e) (I.edgeEquiv f)
      (uibotClassSeparation5_edgeParam I e t) (uibotClassSeparation5_edgeParam I f s) h
    have hinv (a : E) (u : unitInterval) :
        uibotClassSeparation5_edgeParam I.symm (I.edgeEquiv a)
          (uibotClassSeparation5_edgeParam I a u) = u := by
      cases he : I.flip a <;>
        simp [uibotClassSeparation5_edgeParam, D39CombDartIso.symm, he]
    rw [hinv, hinv] at hh
    change M.toPlaneMapWithMissing.arc (I.edgeEquiv.symm (I.edgeEquiv e)) t =
      M.toPlaneMapWithMissing.arc (I.edgeEquiv.symm (I.edgeEquiv f)) s at hh
    rw [I.edgeEquiv.symm_apply_apply e, I.edgeEquiv.symm_apply_apply f] at hh
    exact hh

private theorem boundary_homeomorph_of_same_fibres
    {X Y Z : Type*}
    [uibotClassSeparation5TopologyX : TopologicalSpace X]
    [uibotClassSeparation5CompactX : CompactSpace X]
    [uibotClassSeparation5TopologyY : TopologicalSpace Y]
    [uibotClassSeparation5T2Y : T2Space Y]
    [uibotClassSeparation5TopologyZ : TopologicalSpace Z]
    [uibotClassSeparation5T2Z : T2Space Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (heq : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ H : Y ≃ₜ Z, ∀ x, H (f x) = g x := by
  classical
  let s : Y → X := fun y => (hfs y).choose
  have hs (y : Y) : f (s y) = y := (hfs y).choose_spec
  let F : Y → Z := fun y => g (s y)
  have hF (x : X) : F (f x) = g x := (heq _ _).mp (hs (f x))
  have hq := hf.isClosedMap.isQuotientMap hf hfs
  have hFc : Continuous F := hq.continuous_iff.mpr (by
    have he : F ∘ f = g := funext hF
    rw [he]
    exact hg)
  have hFi : Function.Injective F := by
    intro x y hxy
    have h := (heq (s x) (s y)).mpr hxy
    simpa only [hs] using h
  have hFs : Function.Surjective F := by
    intro z
    obtain ⟨x, rfl⟩ := hgs z
    exact ⟨f x, hF x⟩
  let uibotClassSeparation5CompactY : CompactSpace Y :=
    ⟨by simpa only [image_univ, hfs.range_eq] using (isCompact_univ.image hf)⟩
  exact ⟨hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩), hF⟩

/-- Helper toward Proposition 3.9: each source frontier consists of finitely
many complete geometric edges, retaining the original edge identities. -/
theorem uibotClassSeparation5_source_boundary_edges_finite
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
      {e | Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val}.Finite := by
  intro G M F
  have hc := (uibotClassSeparation2_source_face_compact_finite_boundary W H h0 hpast hp F).1
  apply ((G.locally_finite (closure F.val) hc.isBounded).image Prod.fst).subset
  intro e he
  refine ⟨(e, false), ?_, rfl⟩
  refine ⟨M.toPlaneMapWithMissing.arc e 0,
    frontier_subset_closure (he ⟨0, rfl⟩), ?_⟩
  exact (G.toPlaneGraphDrawing_arc_range (e, false)) ▸
    (show M.toPlaneMapWithMissing.arc e 0 ∈ Set.range (M.toPlaneMapWithMissing.arc e) from ⟨0, rfl⟩)

/-- Helper toward Proposition 3.9: a retained face has a boundary
homeomorphism with the prescribed global affine parameter on every boundary
edge. Its values therefore agree across every shared edge and endpoint. -/
theorem uibotClassSeparation5_retained_face_boundary_homeomorph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ (I : D39CombDartIso M ρ A.map A.root) (r : ℕ)
      (J : D39GeomBallIsoV2 r M ρ A.map A.root)
      (F : {F // F ∈ d39GeomRetainedFaces M ρ r}),
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r},
        I.edgeEquiv e.val = (J.edgeEquiv e).val) →
      ∃ b : frontier F.val.val ≃ₜ frontier (J.faceEquiv F).val.val,
        ∀ (e : WholePlaneEdge W)
          (he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val)
          (t : unitInterval),
          (b ⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : ℂ) =
            A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
              (uibotClassSeparation5_edgeParam I e t) := by
  classical
  intro G M ρ I r J F hI
  let B := {e : WholePlaneEdge W |
    Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val}
  let uibotClassSeparation5FiniteBoundary : Finite B :=
    (uibotClassSeparation5_source_boundary_edges_finite W H h0 hpast hp F.val).to_subtype
  let er (e : B) : {e // e ∈ d39GeomBallEdges M ρ r} :=
    ⟨e.val, F.property _ (frontier_subset_closure
      (e.property ⟨0, (M.toPlaneMapWithMissing.arc e.val).source⟩)),
      F.property _ (frontier_subset_closure
        (e.property ⟨1, (M.toPlaneMapWithMissing.arc e.val).target⟩))⟩
  have hrange (e : B) :
      J.h '' Set.range (M.toPlaneMapWithMissing.arc e.val) =
        Set.range (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e.val)) := by
    rw [J.arc_range_map (er e), ← hI (er e)]
  have hfront : J.h '' frontier F.val.val = frontier (J.faceEquiv F).val.val := by
    rw [J.h.image_frontier, J.face_image_map F]
  have htarget (e : B) :
      Set.range (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e.val)) ⊆
        frontier (J.faceEquiv F).val.val := by
    rw [← hrange e, ← hfront]
    exact Set.image_mono e.property
  let X := (e : B) × unitInterval
  let f : X → frontier F.val.val := fun x =>
    ⟨M.toPlaneMapWithMissing.arc x.1.val x.2, x.1.property ⟨x.2, rfl⟩⟩
  let g : X → frontier (J.faceEquiv F).val.val := fun x =>
    ⟨A.map.toPlaneMapWithMissing.arc (I.edgeEquiv x.1.val)
      (uibotClassSeparation5_edgeParam I x.1.val x.2), htarget x.1 ⟨_, rfl⟩⟩
  have hf : Continuous f := continuous_sigma (fun e =>
    (M.toPlaneMapWithMissing.arc e.val).continuous.subtype_mk _)
  have hg : Continuous g := continuous_sigma (fun e =>
    ((A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e.val)).continuous.comp
      (uibotClassSeparation5_edgeParam I e.val).continuous).subtype_mk _)
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨e, he, t, rfl⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F.val z hz
    exact ⟨⟨⟨e, he⟩, t⟩, rfl⟩
  have hgs : Function.Surjective g := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ J.h '' frontier F.val.val := hfront.symm ▸ hz
    obtain ⟨x, hx, rfl⟩ := hz'
    obtain ⟨e, he, t, ht⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F.val x hx
    have hmem : J.h x ∈ Set.range (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)) := by
      rw [← hrange ⟨e, he⟩]
      exact Set.mem_image_of_mem J.h ⟨t, ht⟩
    obtain ⟨s, hs⟩ := hmem
    refine ⟨⟨⟨e, he⟩, (uibotClassSeparation5_edgeParam I e).symm s⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e))
      ((uibotClassSeparation5_edgeParam I e).apply_symm_apply s)).trans hs
  have heq (x y : X) : f x = f y ↔ g x = g y := by
    change (⟨_, _⟩ : frontier F.val.val) = ⟨_, _⟩ ↔
      (⟨_, _⟩ : frontier (J.faceEquiv F).val.val) = ⟨_, _⟩
    simp only [Subtype.mk.injEq]
    exact uibotClassSeparation5_edgeParam_collision_iff I x.1.val y.1.val x.2 y.2
  obtain ⟨b, hb⟩ := boundary_homeomorph_of_same_fibres f g hf hg hfs hgs heq
  exact ⟨b, fun e he t => congrArg Subtype.val (hb ⟨⟨e, he⟩, t⟩)⟩

private theorem extension_boundary_iff (S T : Set ℂ)
    (b : frontier S ≃ₜ frontier T) (E : closure S ≃ₜ closure T)
    (he : ∀ x : frontier S,
      (E ⟨x, frontier_subset_closure x.property⟩ : ℂ) = (b x : ℂ))
    (x : closure S) : (E x : ℂ) ∈ frontier T ↔ (x : ℂ) ∈ frontier S := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := b.surjective ⟨E x, hx⟩
    have hE : E ⟨y, frontier_subset_closure y.property⟩ = E x :=
      Subtype.ext ((he y).trans (congrArg Subtype.val hy))
    have hxy : (y : ℂ) = (x : ℂ) := congrArg Subtype.val (E.injective hE)
    exact hxy ▸ y.property
  · intro hx
    exact (he ⟨x, hx⟩).symm ▸ (b ⟨x, hx⟩).property

/-- Helper toward Proposition 3.9: the coherent target-face equivalence
admits boundary maps with the one global affine edge parameter and extensions
over every closed face. Each extension carries precisely frontier to frontier. -/
theorem uibotClassSeparation5_compatible_face_extensions
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ I : D39CombDartIso M ρ A.map A.root,
      (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.flip e.val = J.edgeFlip e)) →
      ∃ τ : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face ≃
          A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
        LocallyFinite (fun F => closure (τ F).val) ∧
        (⋃ F, closure (τ F).val) = Set.univ ∧
        (∀ F, IsOpen (τ F).val) ∧
        ∃ (b : ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
            frontier F.val ≃ₜ frontier (τ F).val)
          (E : ∀ F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
            closure F.val ≃ₜ closure (τ F).val),
          (∀ F (e : WholePlaneEdge W)
            (he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val)
            (t : unitInterval),
            (b F ⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : ℂ) =
              A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
                (uibotClassSeparation5_edgeParam I e t)) ∧
          (∀ F (x : frontier F.val),
            (E F ⟨x, frontier_subset_closure x.property⟩ : ℂ) = (b F x : ℂ)) ∧
          (∀ F (x : closure F.val),
            (E F x : ℂ) ∈ frontier (τ F).val ↔ (x : ℂ) ∈ frontier F.val) := by
  classical
  intro G M ρ I hlocal
  obtain ⟨τ, hfinite, hcover, hcoh⟩ :=
    uibotClassSeparation4_target_face_equiv W H h0 hpast hp A I hlocal
  have hseen (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
      ∃ (r : ℕ) (J : D39GeomBallIsoV2 (r + 1) M ρ A.map A.root)
        (hF : F ∈ d39GeomRetainedFaces M ρ (r + 1)),
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) r,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (J.faceEquiv ⟨F, hF⟩).val = τ F := by
    obtain ⟨r, _, hr⟩ :=
      uibotClassSeparation2_source_face_eventually_retained W H h0 hpast hp F
    obtain ⟨J, _, he, _⟩ := hlocal r
    have hF : F ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
      D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr v hv)
    exact ⟨r, J, hF, he, hcoh r J he F hF⟩
  have hopen (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
      IsOpen (τ F).val := by
    obtain ⟨r, J, hF, _, hτ⟩ := hseen F
    rw [← hτ, ← J.face_image_map ⟨F, hF⟩]
    obtain ⟨C, T, hC⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F
    rw [hC]
    exact J.h.isOpenMap _ (T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous))
  have hex (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) :
      ∃ (b : frontier F.val ≃ₜ frontier (τ F).val)
        (E : closure F.val ≃ₜ closure (τ F).val),
        (∀ (e : WholePlaneEdge W)
          (he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val)
          (t : unitInterval),
          (b ⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : ℂ) =
            A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
              (uibotClassSeparation5_edgeParam I e t)) ∧
        (∀ x : frontier F.val,
          (E ⟨x, frontier_subset_closure x.property⟩ : ℂ) = (b x : ℂ)) := by
    obtain ⟨r, J, hF, he, hτ⟩ := hseen F
    obtain ⟨b, hb⟩ :=
      uibotClassSeparation5_retained_face_boundary_homeomorph W H h0 hpast hp A I
        (r + 1) J ⟨F, hF⟩ he
    obtain ⟨E, hE⟩ := uibotClassSeparation3_retained_face_boundary_extension
      W H h0 hpast hp A (r + 1) J ⟨F, hF⟩ b
    have hτval := congrArg Subtype.val hτ
    rw [← hτval]
    exact ⟨b, E, hb, hE⟩
  choose b E hb hE using hex
  exact ⟨τ, hfinite, hcover, hopen, b, E, hb, hE,
    fun F x => extension_boundary_iff F.val (τ F).val (b F) (E F) (hE F) x⟩

private theorem closed_face_inter_frontier {V E : Type*} (D : PlaneGraphDrawing V E)
    (F K : D.Face) (ho : IsOpen F.val) (hne : F ≠ K) :
    closure F.val ∩ closure K.val ⊆ frontier F.val := by
  have hd : Disjoint F.val K.val := by
    apply Set.disjoint_left.mpr
    intro x hx hK
    apply hne
    apply Subtype.ext
    obtain ⟨a, _, ha⟩ := F.property
    obtain ⟨b, _, hb⟩ := K.property
    exact ha.trans ((connectedComponentIn_eq (ha ▸ hx)).trans
      ((connectedComponentIn_eq (hb ▸ hK)).symm.trans hb.symm))
  intro x hx
  rw [frontier, ho.interior_eq]
  exact ⟨hx.1, fun hf => Set.disjoint_left.mp (hd.closure_right ho) hf hx.2⟩

private theorem paste_closed_cells {ι : Type*} (S T : ι → Set ℂ)
    (hS : LocallyFinite S) (hT : LocallyFinite T)
    (hcS : ⋃ i, S i = univ) (hcT : ⋃ i, T i = univ)
    (hclS : ∀ i, IsClosed (S i)) (hclT : ∀ i, IsClosed (T i))
    (E : ∀ i, S i ≃ₜ T i)
    (heq : ∀ i j (x : S i) (y : S j),
      (E i x : ℂ) = (E j y : ℂ) ↔ (x : ℂ) = (y : ℂ)) :
    ∃ g : ℂ ≃ₜ ℂ, ∀ i (x : S i), g x = (E i x : ℂ) := by
  classical
  have hmem (x : ℂ) : ∃ i, x ∈ S i := mem_iUnion.mp (hcS.symm ▸ mem_univ x)
  let idx (x : ℂ) := (hmem x).choose
  have hx (x : ℂ) : x ∈ S (idx x) := (hmem x).choose_spec
  let f (x : ℂ) : ℂ := E (idx x) ⟨x, hx x⟩
  have hf (i : ι) (x : S i) : f x = (E i x : ℂ) := (heq _ _ _ _).mpr rfl
  have hfi : Function.Injective f := fun x y h => (heq _ _ _ _).mp h
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcT.symm ▸ mem_univ y)
    refine ⟨(E i).symm ⟨y, hi⟩, ?_⟩
    exact (hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply _))
  have hfc : Continuous f := hS.continuous hcS hclS (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (S i).domRestrict f = fun x => (E i x : ℂ) := funext (hf i)
    rw [he]
    exact continuous_subtype_val.comp (E i).continuous)
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hinv (i : ι) (y : T i) : e.symm y = ((E i).symm y : ℂ) := by
    apply e.injective
    exact (e.apply_symm_apply (y : ℂ)).trans
      ((hf i _).trans (congrArg Subtype.val ((E i).apply_symm_apply y))).symm
  have hic : Continuous e.symm := hT.continuous hcT hclT (fun i => by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (T i).domRestrict e.symm = fun y => ((E i).symm y : ℂ) := funext (hinv i)
    rw [he]
    exact continuous_subtype_val.comp (E i).symm.continuous)
  exact ⟨{ toEquiv := e, continuous_toFun := hfc, continuous_invFun := hic }, hf⟩

/-- Helper toward Proposition 3.9: compatible closed-face extensions paste
to a homeomorphism of the entire plane. The inverse is continuous by the
locally finite target closed-face cover. Winding preservation is separate. -/
theorem uibotClassSeparation5_pasted_homeomorph
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ I : D39CombDartIso M ρ A.map A.root,
      (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.flip e.val = J.edgeFlip e)) →
      ∃ (τ : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face ≃
          A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (g : ℂ ≃ₜ ℂ),
        (∀ F, g '' closure F.val = closure (τ F).val) ∧
        (∀ F, g '' F.val = (τ F).val) ∧
        (∀ (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (e : WholePlaneEdge W)
          (_he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val)
          (t : unitInterval),
          g (M.toPlaneMapWithMissing.arc e t) =
            A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
              (uibotClassSeparation5_edgeParam I e t)) := by
  classical
  intro G M ρ I hlocal
  obtain ⟨τ, hfinite, hcover, hopen, b, E, hb, hE, hboundary⟩ :=
    uibotClassSeparation5_compatible_face_extensions W H h0 hpast hp A I hlocal
  have hsourceOpen (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) : IsOpen F.val := by
    obtain ⟨C, T, hF⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F
    rw [hF]
    exact T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous)
  have hbcollision (F K : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      (x : frontier F.val) (y : frontier K.val) :
      (b F x : ℂ) = (b K y : ℂ) ↔ (x : ℂ) = (y : ℂ) := by
    obtain ⟨e, he, t, ht⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F x x.property
    obtain ⟨f, hf, s, hs⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp K y y.property
    have hx : (⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : frontier F.val) = x :=
      Subtype.ext ht
    have hy : (⟨M.toPlaneMapWithMissing.arc f s, hf ⟨s, rfl⟩⟩ : frontier K.val) = y :=
      Subtype.ext hs
    rw [← hx, ← hy, hb F e he t, hb K f hf s]
    exact (uibotClassSeparation5_edgeParam_collision_iff I e f t s).symm
  have heq (F K : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      (x : closure F.val) (y : closure K.val) :
      (E F x : ℂ) = (E K y : ℂ) ↔ (x : ℂ) = (y : ℂ) := by
    by_cases hFK : F = K
    · subst K
      exact ⟨fun h => congrArg Subtype.val ((E F).injective (Subtype.ext h)),
        fun h => congrArg (fun z => (E F z : ℂ)) (Subtype.ext h)⟩
    have hτ : τ F ≠ τ K := fun h => hFK (τ.injective h)
    constructor
    · intro h
      have hxf : (E F x : ℂ) ∈ frontier (τ F).val :=
        closed_face_inter_frontier A.map.toPlaneMapWithMissing.toPlaneGraphDrawing
          (τ F) (τ K) (hopen F) hτ ⟨(E F x).property, h.symm ▸ (E K y).property⟩
      have hyf : (E K y : ℂ) ∈ frontier (τ K).val :=
        closed_face_inter_frontier A.map.toPlaneMapWithMissing.toPlaneGraphDrawing
          (τ K) (τ F) (hopen K) (Ne.symm hτ) ⟨(E K y).property, h ▸ (E F x).property⟩
      have hx := (hboundary F x).mp hxf
      have hy := (hboundary K y).mp hyf
      exact (hbcollision F K ⟨x, hx⟩ ⟨y, hy⟩).mp
        ((hE F ⟨x, hx⟩).symm.trans (h.trans (hE K ⟨y, hy⟩)))
    · intro h
      have hx : (x : ℂ) ∈ frontier F.val :=
        closed_face_inter_frontier M.toPlaneMapWithMissing.toPlaneGraphDrawing
          F K (hsourceOpen F) hFK ⟨x.property, h.symm ▸ y.property⟩
      have hy : (y : ℂ) ∈ frontier K.val :=
        closed_face_inter_frontier M.toPlaneMapWithMissing.toPlaneGraphDrawing
          K F (hsourceOpen K) (Ne.symm hFK) ⟨y.property, h ▸ x.property⟩
      exact (hE F ⟨x, hx⟩).trans
        (((hbcollision F K ⟨x, hx⟩ ⟨y, hy⟩).mpr h).trans (hE K ⟨y, hy⟩).symm)
  obtain ⟨g, hg⟩ := paste_closed_cells (fun F => closure F.val)
    (fun F => closure (τ F).val)
    (uibotClassSeparation3_source_closed_faces_locallyFinite W H h0 hpast hp)
    hfinite (uibotClassSeparation3_source_closed_faces_cover W H h0 hpast hp)
    hcover (fun _ => isClosed_closure) (fun _ => isClosed_closure) E heq
  refine ⟨τ, g, ?_, ?_, ?_⟩
  · intro F
    apply Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [hg F ⟨x, hx⟩]
      exact (E F ⟨x, hx⟩).property
    · intro z hz
      refine ⟨(E F).symm ⟨z, hz⟩, ((E F).symm ⟨z, hz⟩).property, ?_⟩
      exact (hg F _).trans (congrArg Subtype.val ((E F).apply_symm_apply _))
  · intro F
    have hmem (x : closure F.val) : (E F x : ℂ) ∈ (τ F).val ↔ (x : ℂ) ∈ F.val := by
      have hs : (x : ℂ) ∈ F.val ↔ (x : ℂ) ∉ frontier F.val := by
        rw [frontier, (hsourceOpen F).interior_eq]
        simp only [mem_sdiff, x.property, true_and, not_not]
      have ht : (E F x : ℂ) ∈ (τ F).val ↔ (E F x : ℂ) ∉ frontier (τ F).val := by
        rw [frontier, (hopen F).interior_eq]
        simp only [mem_sdiff, (E F x).property, true_and, not_not]
      rw [ht, hboundary F x, ← hs]
    apply Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [hg F ⟨x, subset_closure hx⟩]
      exact (hmem ⟨x, subset_closure hx⟩).mpr hx
    · intro z hz
      let x := (E F).symm ⟨z, subset_closure hz⟩
      have hEx : (E F x : ℂ) = z := congrArg Subtype.val ((E F).apply_symm_apply _)
      refine ⟨x, (hmem x).mp (hEx.symm ▸ hz), (hg F x).trans hEx⟩
  · intro F e he t
    exact (hg F ⟨_, frontier_subset_closure (he ⟨t, rfl⟩)⟩).trans
      ((hE F ⟨_, he ⟨t, rfl⟩⟩).trans (hb F e he t))

private theorem edgeParam_vertex
    {V E V' E' : Type*}
    {M : DirectedPlaneMapWithMissing V E} {ρ : E × Bool}
    {N : DirectedPlaneMapWithMissing V' E'} {σ : E' × Bool}
    (I : D39CombDartIso M ρ N σ) (e : E) (t : unitInterval) (v : V)
    (h : M.toPlaneMapWithMissing.arc e t = M.toPlaneMapWithMissing.pos v) :
    N.toPlaneMapWithMissing.arc (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e t) =
      N.toPlaneMapWithMissing.pos (I.vertexEquiv v) := by
  rcases parameter_cases t with rfl | rfl | ht
  · have hv : M.toPlaneMapWithMissing.src e = v :=
      M.toPlaneMapWithMissing.pos_injective (by simpa only [Path.source] using h)
    exact (uibotClassSeparation5_edgeParam_endpoints I e).1.trans
      (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
  · have hv : M.toPlaneMapWithMissing.tgt e = v :=
      M.toPlaneMapWithMissing.pos_injective (by simpa only [Path.target] using h)
    exact (uibotClassSeparation5_edgeParam_endpoints I e).2.trans
      (congrArg (fun v => N.toPlaneMapWithMissing.pos (I.vertexEquiv v)) hv)
  · exact (M.toPlaneMapWithMissing.openArc_avoids e v ⟨t, ht, h⟩).elim

/-- Helper toward Proposition 3.9: the pasted homeomorphism maps every
vertex, every geometric edge with its global affine parameter, and every face
to its prescribed counterpart. Its image is open and face-saturated. This
statement does not assert preservation of winding. -/
theorem uibotClassSeparation5_global_topological_map
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    ∀ I : D39CombDartIso M ρ A.map A.root,
      (∀ n : ℕ, ∃ J : D39GeomBallIsoV2 (n + 1) M ρ A.map A.root,
        (∀ v : uibotSeparationBallV (uibotWholePlaneSourceDomain W H G hp) n,
          I.vertexEquiv v.val = (J.vertexEquiv v).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.edgeEquiv e.val = (J.edgeEquiv e).val) ∧
        (∀ e : uibotSeparationBallE (uibotWholePlaneSourceDomain W H G hp) n,
          I.flip e.val = J.edgeFlip e)) →
      ∃ (τ : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face ≃
          A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) (g : ℂ ≃ₜ ℂ),
        (∀ v, g (M.toPlaneMapWithMissing.pos v) =
          A.map.toPlaneMapWithMissing.pos (I.vertexEquiv v)) ∧
        (∀ e t, g (M.toPlaneMapWithMissing.arc e t) =
          A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
            (uibotClassSeparation5_edgeParam I e t)) ∧
        (∀ e, I.flip e = false → StrictMono (uibotClassSeparation5_edgeParam I e)) ∧
        (∀ e, I.flip e = true → StrictAnti (uibotClassSeparation5_edgeParam I e)) ∧
        (∀ F, g '' F.val = (τ F).val) ∧
        IsOpen (Set.range g) ∧
        (∀ F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          (F.val ∩ Set.range g).Nonempty → F.val ⊆ Set.range g) := by
  intro G M ρ I hlocal
  obtain ⟨τ, g, _, hfaces, hedge⟩ :=
    uibotClassSeparation5_pasted_homeomorph W H h0 hpast hp A I hlocal
  have hopen (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face) : IsOpen F.val := by
    obtain ⟨C, T, hF⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F
    rw [hF]
    exact T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous)
  have hfront (F : M.toPlaneMapWithMissing.toPlaneGraphDrawing.Face)
      {x : ℂ} (hx : x ∈ closure F.val)
      (hi : x ∈ M.toPlaneMapWithMissing.toPlaneGraphDrawing.image) : x ∈ frontier F.val := by
    rw [frontier, (hopen F).interior_eq]
    exact ⟨hx, fun hf => M.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image F hf hi⟩
  have hedges (e : WholePlaneEdge W) (t : unitInterval) :
      g (M.toPlaneMapWithMissing.arc e t) = A.map.toPlaneMapWithMissing.arc
        (I.edgeEquiv e) (uibotClassSeparation5_edgeParam I e t) := by
    obtain ⟨F, hF⟩ := uibotClassSeparation4_source_edge_in_closed_face W H h0 hpast hp e
    apply hedge F e
    intro x hx
    exact hfront F (hF hx) (Or.inr (mem_iUnion.mpr ⟨e, hx⟩))
  refine ⟨τ, g, ?_, hedges, ?_, ?_, hfaces, ?_, ?_⟩
  · intro v
    have hcov := uibotClassSeparation3_source_closed_faces_cover W H h0 hpast hp
    obtain ⟨F, hF⟩ := mem_iUnion.mp (hcov.symm ▸ mem_univ (M.toPlaneMapWithMissing.pos v))
    have hv := hfront F hF (Or.inl ⟨v, rfl⟩)
    obtain ⟨e, _, t, ht⟩ :=
      uibotClassSeparation4_source_frontier_covered_by_edges W H h0 hpast hp F _ hv
    exact (congrArg g ht.symm).trans ((hedges e t).trans (edgeParam_vertex I e t v ht))
  · intro e he a b hab
    simpa [uibotClassSeparation5_edgeParam, he] using hab
  · intro e he a b hab
    simpa [uibotClassSeparation5_edgeParam, he] using unitInterval.strictAnti_symm hab
  · rw [g.surjective.range_eq]
    exact isOpen_univ
  · intro F _ x _
    exact g.surjective x















































































end DirectedDistances.PaperProofs.Section3
end
