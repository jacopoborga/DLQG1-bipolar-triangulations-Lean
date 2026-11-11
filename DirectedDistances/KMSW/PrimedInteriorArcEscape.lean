/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedDeletedComponentUnbounded

/-! Supporting lemmas for paper labels `lem-quad-kmsw` (see CORRESPONDENCE.md). -/

/-! # Finite face closures and the retained beta-zero path

Supporting lemmas for Lemma 5.13 (`lem-quad-kmsw`), source
Finite face closures cannot have a nonempty boundary supported on the simple
beta-zero path. Geometric escape requires identifying such a closure from a
bounded complementary component; the combinatorial lemmas do not assume that
identification. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology



theorem finite_perm_mem_iff_of_single_exception {D : Type*} (σ : Equiv.Perm D)
    (X : Set D) (hX : X.Finite) (a : D)
    (hother : ∀ d, d ≠ a → (σ d ∈ X ↔ d ∈ X)) :
    σ a ∈ X ↔ a ∈ X := by
  have forward (τ : Equiv.Perm D) (b : D)
      (hh : ∀ d, d ≠ b → (τ d ∈ X ↔ d ∈ X)) : b ∈ X → τ b ∈ X := by
    intro hb
    by_contra htb
    have hm : MapsTo τ.symm X X := by
      intro d hd
      by_cases he : τ.symm d = b
      · have hbd : τ b = d := by rw [← he, Equiv.apply_symm_apply]
        exact (htb (hbd.symm ▸ hd)).elim
      · exact (hh _ he).mp (by simpa only [Equiv.apply_symm_apply] using hd)
    obtain ⟨d, hd, hdb⟩ :=
      ((hX.injOn_iff_bijOn_of_mapsTo hm).mp τ.symm.injective.injOn).surjOn hb
    have hbd : τ b = d := by rw [← hdb, Equiv.apply_symm_apply]
    exact htb (hbd.symm ▸ hd)
  constructor
  · have hh : ∀ d, d ≠ σ a → (σ.symm d ∈ X ↔ d ∈ X) := by
      intro d hd
      have hne : σ.symm d ≠ a := by
        intro he
        apply hd
        rw [← he, Equiv.apply_symm_apply]
      simpa only [Equiv.apply_symm_apply] using (hother _ hne).symm
    simpa only [Equiv.symm_apply_apply] using forward σ.symm (σ a) hh
  · exact forward σ a hother




theorem finite_perm_vertex_mem_iff_of_single_exception {D V : Type*}
    (σ : Equiv.Perm D) (vert : D → V) (hvert : ∀ d, vert (σ d) = vert d)
    (X : Set D) (hX : X.Finite) (a : D)
    (hother : ∀ d, vert d = vert a → d ≠ a → (σ d ∈ X ↔ d ∈ X)) :
    σ a ∈ X ↔ a ∈ X := by
  let T := {d | d ∈ X ∧ vert d = vert a}
  have hT : T.Finite := hX.subset (fun _ hd => hd.1)
  have hmem := finite_perm_mem_iff_of_single_exception σ T hT a (by
    intro d hd
    change (σ d ∈ X ∧ vert (σ d) = vert a) ↔ (d ∈ X ∧ vert d = vert a)
    rw [hvert]
    by_cases hv : vert d = vert a
    · rw [hother d hv hd]
    · simp only [hv, and_false])
  simpa only [T, mem_ofPred_eq, hvert, and_true] using hmem



theorem primedBeta0Vertices_eq_edgeWest (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (n : ℕ) :
    kmswBeta0Vertices w hfin hb n = edgeWest w (kmswBeta0Stream w hfin hb n).val := by
  cases n with
  | zero => exact (kmswBeta0Stream_start w hfin hb).symm
  | succ n => exact (kmswBeta0Stream_chain w hfin hb n).symm



theorem primedBeta0Stream_edge_injective (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    Function.Injective (fun n => (kmswBeta0Stream w hfin hb n).val) := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  intro i j hij
  apply kmswBeta0Vertices_injective w hfin hb
  exact (primedBeta0Vertices_eq_edgeWest w hfin hb i).trans
    ((congrArg (edgeWest w) hij).trans
      (primedBeta0Vertices_eq_edgeWest w hfin hb j).symm)






theorem primedFiniteFaceClosure_flip_mem_iff (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (X : Set (ℕ × Bool)) (hX : X.Finite)
    (hface : ∀ d, kmswInfFaceSucc w hfin d ∈ X ↔ d ∈ X)
    (hboundary : ∀ d ∈ X, futureMapEdgeInv d ∉ X → primeBetaEdge w hfin hb d.1) :
    ∀ d, futureMapEdgeInv d ∈ X ↔ d ∈ X := by
  classical
  dsimp only [primedLimitFiniteIncidence] at hfin
  let β := fun n => (kmswBeta0Stream w hfin hb n).val
  let B : Set ℕ := {n | ¬ ((β n, false) ∈ X ↔ (β n, true) ∈ X)}
  have hB : B.Finite := by
    apply (Set.Finite.preimage (primedBeta0Stream_edge_injective w hfin hb).injOn
      (hX.image Prod.fst)).subset
    intro n hn
    change β n ∈ Prod.fst '' X
    by_cases hf : (β n, false) ∈ X
    · exact ⟨(β n, false), hf, rfl⟩
    · have ht : (β n, true) ∈ X := by
        by_contra ht
        exact hn (by simp only [hf, ht])
      exact ⟨(β n, true), ht, rfl⟩
  have hσmem (d : ℕ × Bool) :
      (kmswInfRot w hfin).symm d ∈ X ↔ futureMapEdgeInv d ∈ X := by
    simpa only [kmswInfFaceSucc, Equiv.Perm.mul_apply, futureMapEdgeInv,
      Equiv.coe_fn_mk, Bool.not_not] using hface (futureMapEdgeInv d)
  have hσvert (d : ℕ × Bool) :
      kmswLimitDartVertex w ((kmswInfRot w hfin).symm d) = kmswLimitDartVertex w d := by
    have hv := kmswLimitDartVertex_rot w hfin ((kmswInfRot w hfin).symm d)
    simpa only [Equiv.apply_symm_apply] using hv.symm
  have hindex (d : ℕ × Bool)
      (hd : ¬ (futureMapEdgeInv d ∈ X ↔ d ∈ X)) : ∃ n ∈ B, β n = d.1 := by
    have hbeta : primeBetaEdge w hfin hb d.1 := by
      by_cases hx : d ∈ X
      · exact hboundary d hx (fun hf => hd ⟨fun _ => hx, fun _ => hf⟩)
      · have hf : futureMapEdgeInv d ∈ X := by
          by_contra hf
          exact hd (by simp only [hx, hf])
        exact hboundary (futureMapEdgeInv d) hf (by
          simpa only [futureMapEdgeInv_invol] using hx)
    obtain ⟨n, hn⟩ := hbeta
    change β n = d.1 at hn
    refine ⟨n, ?_, hn⟩
    change ¬ ((β n, false) ∈ X ↔ (β n, true) ∈ X)
    rw [hn]
    rcases d with ⟨e, b⟩
    cases b
    · change ¬ ((e, true) ∈ X ↔ (e, false) ∈ X) at hd
      exact fun hh => hd hh.symm
    · exact hd
  have hBempty : B = ∅ := by
    by_contra hempty
    have hne : hB.toFinset.Nonempty := by
      obtain ⟨n, hn⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      exact ⟨n, hB.mem_toFinset.mpr hn⟩
    let N := hB.toFinset.max' hne
    have hN : N ∈ B := hB.mem_toFinset.mp (Finset.max'_mem _ hne)
    have hmax : ∀ n ∈ B, n ≤ N := fun n hn =>
      Finset.le_max' _ n (hB.mem_toFinset.mpr hn)
    let a : ℕ × Bool := (β N, true)
    have ha : kmswLimitDartVertex w a = kmswBeta0Vertices w hfin hb (N + 1) := rfl
    have hunique (d : ℕ × Bool) (hv : kmswLimitDartVertex w d = kmswLimitDartVertex w a)
        (hd : ¬ (futureMapEdgeInv d ∈ X ↔ d ∈ X)) : d = a := by
      obtain ⟨n, hn, hnd⟩ := hindex d hd
      have hle := hmax n hn
      rw [ha] at hv
      cases ht : d.2
      · have hw : kmswBeta0Vertices w hfin hb n =
            kmswBeta0Vertices w hfin hb (N + 1) := by
          exact (primedBeta0Vertices_eq_edgeWest w hfin hb n).trans
            ((congrArg (edgeWest w) hnd).trans (by
              simpa only [kmswLimitDartVertex, ht, Bool.false_eq_true, ↓reduceIte] using hv))
        have := kmswBeta0Vertices_injective w hfin hb hw
        omega
      · have hw : kmswBeta0Vertices w hfin hb (n + 1) =
            kmswBeta0Vertices w hfin hb (N + 1) := by
          change edgeEast w (β n) = _
          rw [hnd]
          simpa only [kmswLimitDartVertex, ht, ↓reduceIte] using hv
        have hi : n = N := by
          have := kmswBeta0Vertices_injective w hfin hb hw
          omega
        exact Prod.ext (hnd.symm.trans (congrArg β hi)) ht
    have hparity := finite_perm_vertex_mem_iff_of_single_exception
      (kmswInfRot w hfin).symm (kmswLimitDartVertex w) hσvert X hX a (by
        intro d hv hne
        have hflip : futureMapEdgeInv d ∈ X ↔ d ∈ X := by
          by_contra hh
          exact hne (hunique d hv hh)
        exact (hσmem d).trans hflip)
    have hflip : futureMapEdgeInv a ∈ X ↔ a ∈ X := (hσmem a).symm.trans hparity
    exact hN hflip
  intro d
  by_contra hd
  obtain ⟨n, hn, _⟩ := hindex d hd
  rw [hBempty] at hn
  exact hn





theorem primedFiniteFaceClosure_eq_empty (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (X : Set (ℕ × Bool)) (hX : X.Finite)
    (hface : ∀ d, kmswInfFaceSucc w hfin d ∈ X ↔ d ∈ X)
    (hboundary : ∀ d ∈ X, futureMapEdgeInv d ∉ X → primeBetaEdge w hfin hb d.1) :
    X = ∅ := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  have hflip := primedFiniteFaceClosure_flip_mem_iff w hfin hb X hX hface hboundary
  have hrotInv (d : ℕ × Bool) : (kmswInfRot w hfin).symm d ∈ X ↔ d ∈ X := by
    have hh := hface (futureMapEdgeInv d)
    have hh' : (kmswInfRot w hfin).symm d ∈ X ↔ futureMapEdgeInv d ∈ X := by
      simpa only [kmswInfFaceSucc, Equiv.Perm.mul_apply, futureMapEdgeInv,
        Equiv.coe_fn_mk, Bool.not_not] using hh
    exact hh'.trans (hflip d)
  have hrot (d : ℕ × Bool) : kmswInfRot w hfin d ∈ X ↔ d ∈ X := by
    simpa only [Equiv.symm_apply_apply] using (hrotInv (kmswInfRot w hfin d)).symm
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hall : ∀ d : ℕ × Bool, d ∈ X := by
    intro d
    have hp := futureMap_connected w hfin a d
    induction hp with
    | refl => exact ha
    | @tail b c hp hbc ih =>
      rcases hbc with rfl | rfl | rfl | rfl
      · exact (hrot _).mpr ih
      · exact (hrotInv _).mpr ih
      · exact (hflip _).mpr ih
      · exact (hflip _).mpr ih
  have hN : (Set.univ : Set ℕ).Finite := (hX.image Prod.fst).subset (by
    intro n _
    exact ⟨(n, false), hall _, rfl⟩)
  exact Set.infinite_univ hN




theorem primedStageTriangleDartList_faceSucc_mem_iff (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (j : TriangleCreationTime w)
    (d : ℕ × Bool) :
    kmswInfFaceSucc w hfin d ∈ stageTriangleDartList w j ↔
      d ∈ stageTriangleDartList w j := by
  dsimp only [primedLimitFiniteIncidence] at hfin
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (hd | hd | hd)
    · exact Or.inr (Or.inr ((kmswInfFaceSucc w hfin).injective (hd.trans hc.2.2.1.symm)))
    · exact Or.inl ((kmswInfFaceSucc w hfin).injective (hd.trans hc.1.symm))
    · exact Or.inr (Or.inl ((kmswInfFaceSucc w hfin).injective (hd.trans hc.2.1.symm)))
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl hc.1)
    · exact Or.inr (Or.inr hc.2.1)
    · exact Or.inl hc.2.2.1






theorem primedFiniteTriangleClosure_eq_empty (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (J : Set (TriangleCreationTime w)) (hJ : J.Finite)
    (hclosed : ∀ j ∈ J, ∀ d ∈ stageTriangleDartList w j,
      ¬ primeBetaEdge w hfin hb d.1 →
        ∃ k ∈ J, futureMapEdgeInv d ∈ stageTriangleDartList w k) :
    J = ∅ := by
  classical
  let X : Set (ℕ × Bool) := ⋃ j ∈ J, {d | d ∈ stageTriangleDartList w j}
  have hX : X.Finite := hJ.biUnion (fun j _ => (stageTriangleDartList w j).finite_toSet)
  have hmem (d : ℕ × Bool) : d ∈ X ↔ ∃ j ∈ J, d ∈ stageTriangleDartList w j := by
    simp only [X, mem_iUnion, mem_ofPred_eq, exists_prop]
  have hempty := primedFiniteFaceClosure_eq_empty w hfin hb X hX (by
    intro d
    simp only [hmem, primedStageTriangleDartList_faceSucc_mem_iff]) (by
    intro d hd hflip
    by_contra hb'
    obtain ⟨j, hj, hdj⟩ := (hmem d).mp hd
    exact hflip ((hmem _).mpr (hclosed j hj d hdj hb')))
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hd : (stageTriangleDartTriple w j).1 ∈ X :=
    (hmem _).mpr ⟨j, hj, List.mem_cons_self⟩
  rw [hempty] at hd
  exact hd





theorem primedArc_component_unbounded_of_infinite_intersections (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (a : ℂ) (S : Set ℕ) (hS : S.Infinite)
    (hinter : ∀ e ∈ S,
      (connectedComponentIn
        (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ a ∩
          ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
            (e, false)).interior).Nonempty) :
    ∀ R : ℝ, ∃ z ∈ connectedComponentIn
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ a, R < ‖z‖ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let C := connectedComponentIn
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ a
  intro R
  by_contra hnone
  push Not at hnone
  have hbounded : Bornology.IsBounded C := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    exact ⟨R, fun z hz => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnone z hz⟩
  apply hS
  apply ((P.locally_finite C hbounded).image Prod.fst).subset
  intro e he
  obtain ⟨z, hzC, hze⟩ := hinter e he
  exact ⟨(e, false), ⟨z, hzC, hze.1⟩, rfl⟩





@[expose] def primedDeletedArcFaceAdj (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (e f : ℕ) : Prop :=
  ¬ primeGeomEdge w hfin hb e ∧ ¬ primeGeomEdge w hfin hb f ∧
    ∃ F : PlaneFaces (hatRealizedDrawing w hfin),
      (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        (e, false)).interior ∩ closure F.val.val).Nonempty ∧
      (((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
        (f, false)).interior ∩ closure F.val.val).Nonempty




theorem primedDeletedArc_component_eq_of_faceReach (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e f : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e)
    (hreach : Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior, ∀ b ∈ (P.arc (f, false)).interior,
      connectedComponentIn Q.imageᶜ a = connectedComponentIn Q.imageᶜ b := by
  dsimp only
  intro a ha
  induction hreach with
  | refl => exact primedDeletedArc_component_eq w hfin hb e he a ha
  | @tail f g hreach hfg ih =>
    obtain ⟨hf, hg, F, hFf, hFg⟩ := hfg
    obtain ⟨c, hc, hcF⟩ := hFf
    intro b hb'
    exact (ih c hc).trans (primedDeletedArc_component_eq_of_common_boundedHatFace
      w h hfin hb f g hf hg F ⟨c, hc, hcF⟩ hFg c hc b hb')




theorem primedDeletedArc_component_unbounded_of_faceReach_externalDart
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e f : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e) (hf : ¬ primeGeomEdge w hfin hb f)
    (hreach : Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f)
    (hext : limitExternalDart w (f, false) ∨ limitExternalDart w (f, true)) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  dsimp only
  intro a ha
  rcases hreach.cases_tail with hfe | ⟨g, heg, hgf⟩
  · subst f
    obtain ⟨hm, hbeta⟩ := (primedDeletedEdge_iff w hfin hb e).mp he
    exact primedDeletedArc_component_unbounded_of_externalDart w hfin hb e hm hbeta hext a ha
  · obtain ⟨_, _, F, _, b, hbArc, _⟩ := hgf
    rw [primedDeletedArc_component_eq_of_faceReach w h hfin hb e f he hreach a ha b hbArc]
    obtain ⟨hm, hbeta⟩ := (primedDeletedEdge_iff w hfin hb f).mp hf
    exact primedDeletedArc_component_unbounded_of_externalDart w hfin hb f hm hbeta hext b hbArc





theorem primedDeletedArc_component_unbounded_of_infinite_faceReach
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e)
    (hinfinite : {f | Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f}.Infinite) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  dsimp only
  intro a ha
  apply primedArc_component_unbounded_of_infinite_intersections w hfin hb a
    {f | Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f} hinfinite
  intro f hf
  rcases hf.cases_tail with hfe | ⟨g, heg, hgf⟩
  · subst f
    exact ⟨a, mem_connectedComponentIn
      (primedDeletedArc_interior_avoids w hfin hb e he ha), ha⟩
  · obtain ⟨_, hfdel, F, _, b, hbArc, _⟩ := hgf
    refine ⟨b, ?_, hbArc⟩
    rw [primedDeletedArc_component_eq_of_faceReach w h hfin hb e f he hf a ha b hbArc]
    exact mem_connectedComponentIn (primedDeletedArc_interior_avoids w hfin hb f hfdel hbArc)




theorem primedDeletedArc_component_unbounded_of_faceReach_deletedBoundaryEndpoint
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (e f : ℕ)
    (he : ¬ primeGeomEdge w hfin hb e) (hf : ¬ primeGeomEdge w hfin hb f)
    (hreach : Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f)
    (k : ℤ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos
      (boundaryVertex w hb k) ∉ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image)
    (hend : edgeWest w f = boundaryVertex w hb k ∨ edgeEast w f = boundaryVertex w hb k) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    ∀ a ∈ (P.arc (e, false)).interior,
      ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  dsimp only
  intro a ha
  rcases hreach.cases_tail with hfe | ⟨g, heg, hgf⟩
  · subst f
    exact primedDeletedArc_component_unbounded_of_deletedBoundaryEndpoint
      w hfin hb e he k hv hend a ha
  · obtain ⟨_, _, F, _, b, hbArc, _⟩ := hgf
    rw [primedDeletedArc_component_eq_of_faceReach w h hfin hb e f he hreach a ha b hbArc]
    exact primedDeletedArc_component_unbounded_of_deletedBoundaryEndpoint
      w hfin hb f hf k hv hend b hbArc





theorem primedBoundedFace_deletedArc_faceReach_finite
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (F : PlaneFaces (mhatPrimeDrawing w hfin hb (monotone_family_all w)))
    (e : ℕ) (he : ¬ primeGeomEdge w hfin hb e) (a : ℂ)
    (ha : a ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc
      (e, false)).interior) (haF : a ∈ F.val.val) :
    {f | Relation.ReflTransGen (primedDeletedArcFaceAdj w hfin hb) e f}.Finite := by
  by_contra hinf
  have hescape := primedDeletedArc_component_unbounded_of_infinite_faceReach
    w h hfin hb e he hinf a ha
  obtain ⟨x, hx, hFx⟩ := F.val.property
  have hFa : F.val.val = connectedComponentIn
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).imageᶜ a :=
    hFx.trans (connectedComponentIn_eq (hFx ▸ haF))
  obtain ⟨R, hR⟩ := F.property.exists_norm_le
  obtain ⟨z, hz, hzR⟩ := hescape R
  exact (not_lt_of_ge (hR z (hFa.symm ▸ hz))) hzR

end DirectedDistances.KMSW
