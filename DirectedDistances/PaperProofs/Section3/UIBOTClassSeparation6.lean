/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTClassSeparation5
public import DirectedDistances.PlanarMap.D39WindingDegree
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7

/-! # Boundary homotopies for source-specific separation

Boundary homotopy and a disk-chart winding witness give orientation of the
cellular homeomorphism. The resulting geometric isomorphism identifies the
almost-everywhere reconstructed class and transports the unique intrinsic cut. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap DirectedDistances.KMSW DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1
open Set Topology
open scoped Topology

private theorem parameter_cases (t : unitInterval) :
    t = 0 ∨ t = 1 ∨ t ∈ openParams := by
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne t.property.1
    (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))⟩)

private theorem arc_collision_endpoints {V E : Type*} (D : PlaneGraphDrawing V E)
    (e f : E) (t s : unitInterval) (h : D.arc e t = D.arc f s) :
    (e = f ∧ t = s) ∨ ((t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) := by
  rcases parameter_cases t with rfl | rfl | ht
  · rcases parameter_cases s with rfl | rfl | hs
    · exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
    · exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    · exact (D.openArc_avoids f (D.src e)
        ⟨s, hs, by simpa only [Path.source] using h.symm⟩).elim
  · rcases parameter_cases s with rfl | rfl | hs
    · exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
    · exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
    · exact (D.openArc_avoids f (D.tgt e)
        ⟨s, hs, by simpa only [Path.target] using h.symm⟩).elim
  · rcases parameter_cases s with rfl | rfl | hs
    · exact (D.openArc_avoids e (D.src f)
        ⟨t, ht, by simpa only [Path.source] using h⟩).elim
    · exact (D.openArc_avoids e (D.tgt f)
        ⟨t, ht, by simpa only [Path.target] using h⟩).elim
    · have hef : e = f := by
        by_contra hn
        exact Set.disjoint_left.mp (D.openArc_disjoint e f hn)
          ⟨t, ht, rfl⟩ ⟨s, hs, h.symm⟩
      subst f
      exact Or.inl ⟨rfl, D.arc_injOn e ht hs h⟩

private theorem interval_endpoints (p : unitInterval ≃ₜ unitInterval) (b : Bool)
    (hm : b = false → StrictMono p) (ha : b = true → StrictAnti p) :
    p 0 = (if b then 1 else 0) ∧ p 1 = (if b then 0 else 1) := by
  cases b
  · have h := (hm rfl).monotone
    constructor
    · apply le_antisymm _ unitInterval.nonneg'
      simpa only [p.apply_symm_apply] using h (unitInterval.nonneg' (t := p.symm 0))
    · apply le_antisymm unitInterval.le_one'
      simpa only [p.apply_symm_apply] using h (unitInterval.le_one' (t := p.symm 1))
  · have h := (ha rfl).antitone
    constructor
    · apply le_antisymm unitInterval.le_one'
      simpa only [p.apply_symm_apply] using h (unitInterval.nonneg' (t := p.symm 1))
    · apply le_antisymm _ unitInterval.nonneg'
      simpa only [p.apply_symm_apply] using h (unitInterval.le_one' (t := p.symm 0))

private theorem continuous_descend_compact
    {X Y Z : Type*}
    [uibotClassSeparation6TopologyX : TopologicalSpace X]
    [uibotClassSeparation6CompactX : CompactSpace X]
    [uibotClassSeparation6TopologyY : TopologicalSpace Y]
    [uibotClassSeparation6T2Y : T2Space Y]
    [uibotClassSeparation6TopologyZ : TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g)
    (hs : Function.Surjective f)
    (he : ∀ x y, f x = f y → g x = g y) :
    ∃ K : C(Y, Z), ∀ x, K (f x) = g x := by
  classical
  let s : Y → X := fun y => (hs y).choose
  have hsec (y : Y) : f (s y) = y := (hs y).choose_spec
  let K : Y → Z := fun y => g (s y)
  have hK (x : X) : K (f x) = g x := he _ _ (hsec (f x))
  have hc : Continuous K := (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr (by
    have hcomp : K ∘ f = g := funext hK
    rw [hcomp]
    exact hg)
  exact ⟨⟨K, hc⟩, hK⟩

/-- Helper toward Proposition 3.9: the affine boundary homeomorphism is
homotopic, within the target frontier, to the retaining-ball homeomorphism.
The interpolation respects every original boundary edge and its endpoints. -/
theorem uibotClassSeparation6_retained_boundary_homotopy
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
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r}, I.flip e.val = J.edgeFlip e) →
      ∃ (b : frontier F.val.val ≃ₜ frontier (J.faceEquiv F).val.val)
        (K : C(unitInterval × frontier F.val.val, frontier (J.faceEquiv F).val.val)),
        (∀ x, K (0, x) = b x) ∧
        (∀ x, (K (1, x) : ℂ) = J.h x) ∧
        (∀ (e : WholePlaneEdge W)
          (he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val)
          (t : unitInterval),
          (b ⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : ℂ) =
            A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
              (uibotClassSeparation5_edgeParam I e t)) := by
  classical
  intro G M ρ I r J F hI hflip
  obtain ⟨b, hb⟩ := uibotClassSeparation5_retained_face_boundary_homeomorph
    W H h0 hpast hp A I r J F hI
  let B := {e : WholePlaneEdge W |
    Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val}
  let uibotClassSeparation6FiniteBoundary : Finite B :=
    (uibotClassSeparation5_source_boundary_edges_finite W H h0 hpast hp F.val).to_subtype
  let er (e : B) : {e // e ∈ d39GeomBallEdges M ρ r} :=
    ⟨e.val, F.property _ (frontier_subset_closure
      (e.property ⟨0, (M.toPlaneMapWithMissing.arc e.val).source⟩)),
      F.property _ (frontier_subset_closure
        (e.property ⟨1, (M.toPlaneMapWithMissing.arc e.val).target⟩))⟩
  let p (e : B) := uibotClassSeparation5_edgeParam I e.val
  let q (e : B) := J.edgeParam (er e)
  have hend (e : B) : q e 0 = p e 0 ∧ q e 1 = p e 1 := by
    have hq := interval_endpoints (q e) (I.flip e.val)
      (fun h => J.edgeParam_mono (er e) ((hflip (er e)).symm.trans h))
      (fun h => J.edgeParam_anti (er e) ((hflip (er e)).symm.trans h))
    cases he : I.flip e.val <;>
      simpa [p, uibotClassSeparation5_edgeParam, he] using hq
  have hfront : J.h '' frontier F.val.val = frontier (J.faceEquiv F).val.val := by
    rw [J.h.image_frontier, J.face_image_map F]
  have htarget (e : B) :
      Set.range (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e.val)) ⊆
        frontier (J.faceEquiv F).val.val := by
    rw [hI (er e), ← J.arc_range_map (er e), ← hfront]
    exact Set.image_mono e.property
  let X := (e : B) × (unitInterval × unitInterval)
  let f : X → unitInterval × frontier F.val.val := fun x =>
    (x.2.1, ⟨M.toPlaneMapWithMissing.arc x.1.val x.2.2, x.1.property ⟨x.2.2, rfl⟩⟩)
  let k : X → frontier (J.faceEquiv F).val.val := fun x =>
    ⟨A.map.toPlaneMapWithMissing.arc (I.edgeEquiv x.1.val)
      (Icc.convexComb (p x.1 x.2.2) (q x.1 x.2.2) x.2.1), htarget x.1 ⟨_, rfl⟩⟩
  have hfc : Continuous f := continuous_sigma fun e =>
    continuous_fst.prodMk
      (((M.toPlaneMapWithMissing.arc e.val).continuous.comp continuous_snd).subtype_mk _)
  have hkc : Continuous k := continuous_sigma fun e => by
    apply Continuous.subtype_mk
    apply (A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e.val)).continuous.comp
    exact Icc.continuous_convexComb_prod.comp
      (((p e).continuous.comp continuous_snd).prodMk
        (((q e).continuous.comp continuous_snd).prodMk continuous_fst))
  have hfs : Function.Surjective f := by
    rintro ⟨u, x⟩
    obtain ⟨e, he, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
      W H h0 hpast hp F.val x x.property
    exact ⟨⟨⟨e, he⟩, u, t⟩, Prod.ext rfl (Subtype.ext ht)⟩
  have hke : ∀ x y, f x = f y → k x = k y := by
    rintro ⟨e, u, t⟩ ⟨e', u', s⟩ h
    have huu : u = u' := congrArg Prod.fst h
    subst u'
    have ha : M.toPlaneMapWithMissing.arc e.val t = M.toPlaneMapWithMissing.arc e'.val s :=
      congrArg (fun x => (x.2 : ℂ)) h
    rcases arc_collision_endpoints M.toPlaneMapWithMissing.toPlaneGraphDrawing
        e.val e'.val t s ha with ⟨hee, hts⟩ | ⟨ht, hs⟩
    · have hee' : e = e' := Subtype.ext hee
      subst e'
      subst s
      rfl
    · have hte : q e t = p e t := by rcases ht with rfl | rfl; exact (hend e).1; exact (hend e).2
      have hse : q e' s = p e' s := by rcases hs with rfl | rfl; exact (hend e').1; exact (hend e').2
      apply Subtype.ext
      change A.map.toPlaneMapWithMissing.arc _ (Icc.convexComb (p e t) (q e t) u) =
        A.map.toPlaneMapWithMissing.arc _ (Icc.convexComb (p e' s) (q e' s) u)
      rw [hte, hse, Icc.convexComb_eq, Icc.convexComb_eq]
      exact (uibotClassSeparation5_edgeParam_collision_iff I e.val e'.val t s).mp ha
  obtain ⟨K, hK⟩ := continuous_descend_compact f k hfc hkc hfs hke
  refine ⟨b, K, ?_, ?_, hb⟩
  · intro x
    obtain ⟨e, he, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
      W H h0 hpast hp F.val x x.property
    have hx : (⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : frontier F.val.val) = x :=
      Subtype.ext ht
    rw [← hx]
    apply Subtype.ext
    exact (congrArg Subtype.val (hK ⟨⟨e, he⟩, 0, t⟩)).trans
      (by simpa only [k, Icc.convexComb_zero] using (hb e he t).symm)
  · intro x
    obtain ⟨e, he, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
      W H h0 hpast hp F.val x x.property
    have hx : (⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : frontier F.val.val) = x :=
      Subtype.ext ht
    rw [← hx]
    apply (congrArg Subtype.val (hK ⟨⟨e, he⟩, 1, t⟩)).trans
    change A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
      (Icc.convexComb (p ⟨e, he⟩ t) (q ⟨e, he⟩ t) 1) = _
    rw [Icc.convexComb_one, show I.edgeEquiv e = (J.edgeEquiv (er ⟨e, he⟩)).val
      from hI (er ⟨e, he⟩)]
    exact (J.arc_map (er ⟨e, he⟩) t).symm

/-- Helper toward Proposition 3.9: on any retained face boundary, the
affinely prescribed global map has the same winding as the genuine ball
witness about every point in that witness's face. -/
theorem uibotClassSeparation6_retained_boundary_winding
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
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r}, I.flip e.val = J.edgeFlip e) →
      ∀ (g : ℂ ≃ₜ ℂ),
      (∀ e t, g (M.toPlaneMapWithMissing.arc e t) =
        A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
          (uibotClassSeparation5_edgeParam I e t)) →
      ∀ {z : ℂ} (L : Path z z), Set.range L ⊆ frontier F.val.val →
      ∀ w ∈ F.val.val, ∀ n : ℤ,
        HasWinding L w n ↔ HasWinding (L.map g.continuous) (J.h w) n := by
  intro G M ρ I r J F hI hflip g hg z L hL w hw n
  obtain ⟨b, K, hK0, hK1, hb⟩ :=
    uibotClassSeparation6_retained_boundary_homotopy W H h0 hpast hp A I r J F hI hflip
  have hgb (x : frontier F.val.val) : (b x : ℂ) = g x := by
    obtain ⟨e, he, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
      W H h0 hpast hp F.val x x.property
    have hx : (⟨M.toPlaneMapWithMissing.arc e t, he ⟨t, rfl⟩⟩ : frontier F.val.val) = x :=
      Subtype.ext ht
    rw [← hx, hb e he t]
    exact (hg e t).symm
  let P : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun u => (K (u.1, ⟨L u.2, hL ⟨u.2, rfl⟩⟩) : ℂ),
      continuous_subtype_val.comp (K.continuous.comp
        (continuous_fst.prodMk ((L.continuous.comp continuous_snd).subtype_mk _)))⟩
  have hP0 (s : unitInterval) : P (0, s) = (L.map g.continuous) s :=
    (congrArg Subtype.val (hK0 _)).trans (hgb _)
  have hP1 (s : unitInterval) : P (1, s) = (L.map J.h.continuous) s := hK1 _
  have hloop (u : unitInterval) : P (u, 1) = P (u, 0) := by
    change (K (u, ⟨L 1, _⟩) : ℂ) = (K (u, ⟨L 0, _⟩) : ℂ)
    exact congrArg (fun x : frontier F.val.val => (K (u, x) : ℂ))
      (Subtype.ext (L.target.trans L.source.symm))
  have havoid (u s : unitInterval) : P (u, s) ≠ J.h w := by
    intro h
    have hf := (K (u, ⟨L s, hL ⟨s, rfl⟩⟩)).property
    change P (u, s) ∈ frontier (J.faceEquiv F).val.val at hf
    rw [h, ← J.face_image_map F, ← J.h.image_frontier,
      J.h.injective.mem_set_image] at hf
    obtain ⟨C, T, hF⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F.val
    have ho : IsOpen F.val.val := by
      rw [hF]
      exact T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous)
    exact hf.2 (ho.interior_eq.symm ▸ hw)
  have hwoff : w ∉ Set.range L := by
    intro h
    have hf := hL h
    exact M.toPlaneMapWithMissing.toPlaneGraphDrawing.face_subset_compl_image F.val hw
      (by
        obtain ⟨e, _, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
          W H h0 hpast hp F.val w hf
        exact Or.inr (mem_iUnion.mpr ⟨e, t, ht⟩))
  constructor
  · intro hn
    let Q : C(unitInterval × unitInterval, ℂ) :=
      ⟨fun u => P (unitInterval.symm u.1, u.2), by fun_prop⟩
    apply hasWinding_freeHomotopy Q
      (fun s => by simpa only [Q, ContinuousMap.coe_mk, unitInterval.symm_zero] using hP1 s)
      (fun s => by simpa only [Q, ContinuousMap.coe_mk, unitInterval.symm_one] using hP0 s)
      (fun u => hloop (unitInterval.symm u))
      (fun u s => havoid (unitInterval.symm u) s)
    exact (J.orientationPreserving L w hwoff n).mp hn
  · intro hn
    exact (J.orientationPreserving L w hwoff n).mpr
      (hasWinding_freeHomotopy P hP0 hP1 hloop havoid hn)

/-- Helper toward Proposition 3.9: an open region with the proved disk chart
has a boundary loop of winding one about an interior point. Radial projection
in the chart deforms a small interior circle without crossing that point. -/
theorem uibotClassSeparation6_disk_boundary_winding_one
    (S : Set ℂ) (hS : IsOpen S)
    (c : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure S)
    (hc : ∀ z, (c z : ℂ) ∈ frontier S ↔ ‖(z : ℂ)‖ = 1) :
    ∃ (z w : ℂ) (L : Path z z), w ∈ S ∧
      Set.range L ⊆ frontier S ∧ HasWinding L w 1 := by
  let o : Metric.closedBall (0 : ℂ) 1 := ⟨0, by simp⟩
  let w : ℂ := c o
  have hw : w ∈ S := by
    by_contra hn
    have hf : w ∈ frontier S := by
      rw [frontier, hS.interior_eq]
      exact ⟨(c o).property, hn⟩
    have hn1 := (hc o).mp hf
    simp [o] at hn1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hw)
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  let L₀ : Path (w + r) (w + r) :=
    { toFun := fun t => w + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [Complex.exp_two_pi_mul_I] }
  have hnorm (t : unitInterval) : ‖L₀ t - w‖ = r := by
    change ‖w + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) - w‖ = r
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, Complex.norm_exp]
    simp
  have hL₀ (t : unitInterval) : L₀ t ∈ S := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hnorm]
    dsimp [r]
    linarith
  have hwind : HasWinding L₀ w 1 := by
    refine ⟨⟨fun t => Complex.log (r : ℂ) + 2 * Real.pi * Complex.I * (t : ℝ),
      by fun_prop⟩, ?_, ?_⟩
    · intro t
      change Complex.exp (Complex.log (r : ℂ) + _) = w + _ - w
      rw [Complex.exp_add, Complex.exp_log (by exact_mod_cast hr.ne')]
      ring
    · simp
  let v : unitInterval → ℂ := fun t => c.symm ⟨L₀ t, subset_closure (hL₀ t)⟩
  have hvc : Continuous v := continuous_subtype_val.comp
    (c.symm.continuous.comp (L₀.continuous.subtype_mk _))
  have hvnorm (t : unitInterval) : ‖v t‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (c.symm ⟨L₀ t, subset_closure (hL₀ t)⟩).property
  have hvne (t : unitInterval) : v t ≠ 0 := by
    intro ht
    have he : c.symm ⟨L₀ t, subset_closure (hL₀ t)⟩ = o := Subtype.ext ht
    have he' := congrArg (fun x => (c x : ℂ)) he
    have hLw : L₀ t = w := by simpa only [c.apply_symm_apply] using he'
    have hh := hnorm t
    rw [hLw, sub_self, norm_zero] at hh
    exact hr.ne' hh.symm
  let a : unitInterval × unitInterval → ℝ := fun p =>
    (1 - (p.1 : ℝ)) + (p.1 : ℝ) / ‖v p.2‖
  have ha (p : unitInterval × unitInterval) : 0 < a p := by
    have hn : 0 < ‖v p.2‖ := norm_pos_iff.mpr (hvne p.2)
    have he : a p * ‖v p.2‖ = (1 - (p.1 : ℝ)) * ‖v p.2‖ + (p.1 : ℝ) := by
      dsimp [a]
      field_simp
    have hprod : 0 < a p * ‖v p.2‖ := by
      rw [he]
      rcases (p.1.property.1).eq_or_lt with h | h
      · rw [← h]; simpa using hn
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr p.1.property.2) hn.le) h
    exact (mul_pos_iff.mp hprod).resolve_right (fun h => (not_lt_of_ge hn.le) h.2) |>.1
  have hac : Continuous a :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).div
        (hvc.comp continuous_snd).norm (fun p => norm_ne_zero_iff.mpr (hvne p.2)))
  have hmem (p : unitInterval × unitInterval) :
      a p • v p.2 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (ha p)]
    dsimp [a]
    rw [add_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hvne p.2))]
    nlinarith [mul_nonneg (sub_nonneg.mpr p.1.property.2) (sub_nonneg.mpr (hvnorm p.2))]
  let K : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => (c ⟨a p • v p.2, hmem p⟩ : ℂ),
      continuous_subtype_val.comp (c.continuous.comp
        ((hac.smul (hvc.comp continuous_snd)).subtype_mk _))⟩
  have hK0 (t : unitInterval) : K (0, t) = L₀ t := by
    change (c ⟨a (0, t) • v t, _⟩ : ℂ) = L₀ t
    have he : (⟨a (0, t) • v t, hmem (0, t)⟩ : Metric.closedBall (0 : ℂ) 1) =
        c.symm ⟨L₀ t, subset_closure (hL₀ t)⟩ := by
      apply Subtype.ext
      simp [a, v]
    rw [he, c.apply_symm_apply]
  have hvloop : v 1 = v 0 := by
    apply congrArg (fun x : closure S => (c.symm x : ℂ))
    exact Subtype.ext (L₀.target.trans L₀.source.symm)
  have hloop (u : unitInterval) : K (u, 1) = K (u, 0) := by
    change (c ⟨a (u, 1) • v 1, _⟩ : ℂ) = (c ⟨a (u, 0) • v 0, _⟩ : ℂ)
    have he : (⟨a (u, 1) • v 1, hmem (u, 1)⟩ : Metric.closedBall (0 : ℂ) 1) =
        ⟨a (u, 0) • v 0, hmem (u, 0)⟩ := by
      apply Subtype.ext
      simp only [a, hvloop]
    rw [he]
  have havoid (u t : unitInterval) : K (u, t) ≠ w := by
    intro he
    have hz := congrArg Subtype.val (c.injective (Subtype.ext he))
    change a (u, t) • v t = (0 : ℂ) at hz
    exact (smul_ne_zero (ha (u, t)).ne' (hvne t)) hz
  let L : Path (K (1, 0)) (K (1, 0)) :=
    { toFun := fun t => K (1, t)
      continuous_toFun := K.continuous.comp (continuous_const.prodMk continuous_id)
      source' := rfl
      target' := hloop 1 }
  refine ⟨_, w, L, hw, ?_,
    hasWinding_freeHomotopy K hK0 (fun _ => rfl) hloop havoid hwind⟩
  rintro x ⟨t, rfl⟩
  apply (hc ⟨a (1, t) • v t, hmem (1, t)⟩).mpr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ha (1, t))]
  simp only [a, Icc.coe_one, sub_self, zero_add, one_div]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hvne t))

/-- Helper toward Proposition 3.9: a retaining-ball witness certifies the
orientation of the affine global extension, without any properness assumption
on the target drawing. -/
theorem uibotClassSeparation6_retained_face_orientation
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
      (_F : {F // F ∈ d39GeomRetainedFaces M ρ r}),
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r},
        I.edgeEquiv e.val = (J.edgeEquiv e).val) →
      (∀ e : {e // e ∈ d39GeomBallEdges M ρ r}, I.flip e.val = J.edgeFlip e) →
      ∀ (g : ℂ ≃ₜ ℂ),
      (∀ e t, g (M.toPlaneMapWithMissing.arc e t) =
        A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
          (uibotClassSeparation5_edgeParam I e t)) → OrientationPreserving g := by
  intro G M ρ I r J F hI hflip g hg
  have hrange (e : WholePlaneEdge W)
      (he : Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val) :
      g '' Set.range (M.toPlaneMapWithMissing.arc e) =
        J.h '' Set.range (M.toPlaneMapWithMissing.arc e) := by
    let er : {e // e ∈ d39GeomBallEdges M ρ r} :=
      ⟨e, F.property _ (frontier_subset_closure (he ⟨0, Path.source _⟩)),
        F.property _ (frontier_subset_closure (he ⟨1, Path.target _⟩))⟩
    rw [J.arc_range_map er, ← hI er]
    apply Subset.antisymm
    · rintro x ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨_, (hg e t).symm⟩
    · rintro x ⟨t, rfl⟩
      refine ⟨M.toPlaneMapWithMissing.arc e ((uibotClassSeparation5_edgeParam I e).symm t),
        ⟨_, rfl⟩, ?_⟩
      rw [hg, (uibotClassSeparation5_edgeParam I e).apply_symm_apply]
  have hsub (g k : ℂ ≃ₜ ℂ)
      (hk : ∀ e, Set.range (M.toPlaneMapWithMissing.arc e) ⊆ frontier F.val.val →
        g '' Set.range (M.toPlaneMapWithMissing.arc e) =
          k '' Set.range (M.toPlaneMapWithMissing.arc e)) :
      g '' frontier F.val.val ⊆ k '' frontier F.val.val := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨e, he, t, ht⟩ := uibotClassSeparation4_source_frontier_covered_by_edges
      W H h0 hpast hp F.val x hx
    exact Set.image_mono he (hk e he ▸ Set.mem_image_of_mem g ⟨t, ht⟩)
  have hface : g '' F.val.val = J.h '' F.val.val :=
    uibotClassSeparation4_source_face_image_eq_of_frontier W H h0 hpast hp F.val g J.h
      (Subset.antisymm (hsub g J.h hrange) (hsub J.h g (fun e he => (hrange e he).symm)))
  obtain ⟨C, T, hF⟩ := uibotClassSeparation4_source_face_cap W H h0 hpast hp F.val
  have ho : IsOpen F.val.val := by
    rw [hF]
    exact T.isOpenMap _ (isOpen_graphRegion C.low_continuous C.high_continuous)
  have hconn : IsPreconnected F.val.val := by
    rw [hF]
    exact (isPathConnected_graphRegion C.ab C.low_continuous C.high_continuous
      C.separated).isConnected.isPreconnected.image T T.continuous.continuousOn
  obtain ⟨c, hc⟩ := uibotClassSeparation3_source_face_disk_chart W H h0 hpast hp F.val
  obtain ⟨z, w, L, hw, hL, hn⟩ := uibotClassSeparation6_disk_boundary_winding_one F.val.val ho c hc
  have hoff : F.val.val ⊆ (Set.range L)ᶜ := by
    intro x hx hxL
    exact (hL hxL).2 (ho.interior_eq.symm ▸ hx)
  obtain ⟨w', hw', he⟩ := hface ▸ Set.mem_image_of_mem g hw
  obtain ⟨n, hconstant⟩ := hasWinding_value_constant_on_preconnected L F.val.val hoff hconn
  have hn1 : n = 1 := hasWinding_unique (hconstant w hw) hn
  have hsource : HasWinding L w' 1 := hn1 ▸ hconstant w' hw'
  have htarget := (uibotClassSeparation6_retained_boundary_winding
    W H h0 hpast hp A I r J F hI hflip g hg L hL w' hw' 1).mp hsource
  rw [he] at htarget
  intro z' L' w' hw' n'
  exact orientationPreserving_of_hasWinding_one g L w (hoff hw) hn htarget L' w' hw' n'

/-- Helper toward Proposition 3.9: the compatible cellular extension is an
orientation-preserving homeomorphism of the entire plane, with the prescribed
vertex and edge maps, complete face images, openness and face saturation. -/
theorem uibotClassSeparation6_oriented_cellular_homeomorph
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
        OrientationPreserving g ∧
        (∀ v, g (M.toPlaneMapWithMissing.pos v) =
          A.map.toPlaneMapWithMissing.pos (I.vertexEquiv v)) ∧
        (∀ e t, g (M.toPlaneMapWithMissing.arc e t) =
          A.map.toPlaneMapWithMissing.arc (I.edgeEquiv e)
            (uibotClassSeparation5_edgeParam I e t)) ∧
        (∀ e, I.flip e = false → StrictMono (uibotClassSeparation5_edgeParam I e)) ∧
        (∀ e, I.flip e = true → StrictAnti (uibotClassSeparation5_edgeParam I e)) ∧
        (∀ F, g '' F.val = (τ F).val) ∧ IsOpen (Set.range g) ∧
        (∀ F : A.map.toPlaneMapWithMissing.toPlaneGraphDrawing.Face,
          (F.val ∩ Set.range g).Nonempty → F.val ⊆ Set.range g) := by
  intro G M ρ I hlocal
  obtain ⟨τ, g, hv, he, hm, ha, hfaces, hopen, hsat⟩ :=
    uibotClassSeparation5_global_topological_map W H h0 hpast hp A I hlocal
  refine ⟨τ, g, ?_, hv, he, hm, ha, hfaces, hopen, hsat⟩
  have hcover := uibotClassSeparation3_source_closed_faces_cover W H h0 hpast hp
  obtain ⟨F, _hF⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ (0 : ℂ))
  obtain ⟨r, _, hr⟩ := uibotClassSeparation2_source_face_eventually_retained W H h0 hpast hp F
  obtain ⟨J, _, hJ, hflip⟩ := hlocal r
  have hret : F ∈ d39GeomRetainedFaces M ρ (r + 1) := fun v hv =>
    D39GeomBallIsoV2.vertexBall_mono (Nat.le_succ r) (hr v hv)
  intro z L w hw n
  exact uibotClassSeparation6_retained_face_orientation
    W H h0 hpast hp A I (r + 1) J ⟨F, hret⟩ hJ hflip g he L w hw n

/-- Helper toward Proposition 3.9: agreement of all finite geometric balls
with the whole-plane source gives a rooted geometric isomorphism, including
preservation of every winding integer. -/
theorem uibotClassSeparation6_global_geometric_iso
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h0 : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
    let M := uibotWholePlaneSourceMap W H G hp
    let ρ := uibotWholePlaneSourceRoot W H G
    (∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r M ρ A.map A.root)) →
      Nonempty (D39GeomRootedMapIsoV2 M ρ A.map A.root) := by
  intro G M ρ hballs
  obtain ⟨I, hlocal⟩ := uibotClassSeparation_global_combinatorial_iso
    (uibotWholePlaneSourceDomain W H G hp) A hballs
  obtain ⟨_τ, g, hor, hv, he, hm, ha, _, _, _⟩ :=
    uibotClassSeparation6_oriented_cellular_homeomorph W H h0 hpast hp A I hlocal
  exact ⟨{
    h := g
    orientationPreserving := hor
    vertexEquiv := I.vertexEquiv
    edgeEquiv := I.edgeEquiv
    edgeFlip := I.flip
    edgeParam := uibotClassSeparation5_edgeParam I
    edgeParam_mono := hm
    edgeParam_anti := ha
    pos_map := hv
    arc_map := he
    src_map := I.src_map
    tgt_map := I.tgt_map
    missing_map := I.missing_map
    orientation_map := I.forward_map
    root_edge_map := I.root_edge
    root_bool_map := I.root_bool }⟩

open MeasureTheory Filter

local instance uibotClassSeparation6MeasurableSpace :
    MeasurableSpace D39GeomRootedMapClass.{0} := borel D39GeomRootedMapClass.{0}
local instance uibotClassSeparation6BorelSpace :
    BorelSpace D39GeomRootedMapClass.{0} := ⟨rfl⟩

private theorem recoveredCode_law :
    (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}).map uibotRecoveredCode = wholePlaneIIDCodeMeasure := by
  change (wholePlaneIIDCodeMeasure.map
    (uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)).map
      uibotRecoveredCode = _
  rw [Measure.map_map measurable_uibotRecoveredCode
    (measurable_uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved)]
  exact (Measure.map_congr uibotRecoveredCode_ae).trans Measure.map_id

/-- Helper toward Proposition 3.9: the recovered entire code reconstructs
the geometric class almost surely. The zero-distance input comes from the
proved measurable conull set, without assuming measurable class equality. -/
theorem uibotClassSeparation6_ae_reconstruction :
    let F := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
    let mu := (uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0})
    ∀ᵐ z ∂mu, F (uibotRecoveredCode z) = z := by
  dsimp only
  have hs := uibotMeasurableWholePlaneClassMap_ae_source
  rw [← recoveredCode_law] at hs
  have hs' := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hs
  filter_upwards [uibotClassReconstruction_ae_all_balls, hs'] with z hz hsource
  obtain ⟨H, h0, hpast, hp, heq, _, _⟩ := hsource
  obtain ⟨A, hA⟩ := Quotient.exists_rep z
  let W := uibotRecoveredCode z
  let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
  let B := uibotWholePlaneSourceDomain W H G hp
  have hballs := hz A B hA heq.symm
  have hgeom := uibotClassSeparation6_global_geometric_iso W H h0 hpast hp A
    (fun r hr => (hballs r hr).map D39GeomBallIsoV2.symm)
  exact heq.trans ((Quotient.sound hgeom).trans hA)

/-- Helper toward Proposition 3.9: almost every class has, on each of its
representatives, exactly one intrinsic future cut. It equals the transported
code cut of the recovered entire code for every geometric source isomorphism;
uniqueness ranges over all intrinsic cuts. -/
theorem uibotClassSeparation6_ae_unique_intrinsic_cut :
    ∀ᵐ z ∂(uibotWholePlaneGeometricProbabilityLaw uibotDeterministicComparison_proved :
      Measure D39GeomRootedMapClass.{0}),
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h0 : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
        let G := WholePlanePastGlueDrawing.glueDrawing W h0 hpast H
        let B := uibotWholePlaneSourceDomain W H G hp
        ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
          Nonempty (D39GeomRootedMapIsoV2 B.map B.root A.map A.root) ∧
          ∃! C : IntrinsicFutureCut2 A,
            (∀ C' : IntrinsicFutureCut2 A, C' = C) ∧
            ∀ I : D39GeomRootedMapIsoV2 B.map B.root A.map A.root,
              C = intrinsicFutureCut2Pushforward I (uibotCut2Source W H h0 hpast hp) := by
  have hs := uibotMeasurableWholePlaneClassMap_ae_source
  rw [← recoveredCode_law] at hs
  have hs' := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hs
  have hu := uibotCut2_sample_existsUnique
  rw [← recoveredCode_law] at hu
  have hu' := ae_of_ae_map measurable_uibotRecoveredCode.aemeasurable hu
  filter_upwards [uibotClassSeparation6_ae_reconstruction, hs', hu'] with z hrec hsource huniq
  obtain ⟨H, h0, hpast, hp, heq, _, _⟩ := hsource
  refine ⟨H, h0, hpast, hp, ?_⟩
  dsimp only
  intro A hA
  have hAF : Quotient.mk d39DomainSetoid A =
      uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved
        (uibotRecoveredCode z) := hA.trans hrec.symm
  obtain ⟨C, _, hC⟩ := huniq A hAF
  refine ⟨Quotient.exact (heq.symm.trans hAF.symm), C, ⟨fun C' => hC C' trivial, ?_⟩, ?_⟩
  · intro I
    exact (hC (intrinsicFutureCut2Pushforward I
      (uibotCut2Source (uibotRecoveredCode z) H h0 hpast hp)) trivial).symm
  · intro C' _
    exact hC C' trivial

end DirectedDistances.PaperProofs.Section3
end
