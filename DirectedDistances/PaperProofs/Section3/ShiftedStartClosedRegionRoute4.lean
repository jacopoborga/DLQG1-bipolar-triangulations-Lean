/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute3

/-! Helper toward Proposition 3.9: restricted rotations at every integer start. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute4

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open ShiftedStartGeometry ShiftedStartClosedRegionRoute2 ShiftedStartClosedRegionRoute3
open Set Topology MeasureTheory

private theorem forward_scan_of_inverse_scan
    {D E : Type*} (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (i : D → E)
    (hscan : ∀ d, ∃ k : ℕ, 0 < k ∧
      (ρ.symm ^ k) (i d) = i (σ.symm d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ.symm ^ j) (i d) ∉ range i)
    (d : D) :
    ∃ k : ℕ, 0 < k ∧ (ρ ^ k) (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ ^ j) (i d) ∉ range i := by
  obtain ⟨k, hk, he, hg⟩ := hscan (σ d)
  rw [Equiv.symm_apply_apply] at he
  have hfwd : (ρ ^ k) (i d) = i (σ d) := by
    rw [← he, show ρ.symm ^ k = (ρ ^ k).symm from inv_pow ρ k,
      Equiv.apply_symm_apply]
  refine ⟨k, hk, hfwd, ?_⟩
  intro j hj hjk
  have hs : (ρ ^ j) (i d) = (ρ.symm ^ (k - j)) (i (σ d)) := by
    apply (ρ ^ (k - j)).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk.le, hfwd,
      show ρ.symm ^ (k - j) = (ρ ^ (k - j)).symm from inv_pow ρ (k - j),
      Equiv.apply_symm_apply]
  rw [hs]
  exact hg (k - j) (by omega) (by omega)

private theorem scan_reaches_first
    {D E : Type*} (σ : Equiv.Perm D) (ρ : Equiv.Perm E) (i : D → E)
    (hscan : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ ^ k) (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ ^ j) (i d) ∉ range i)
    (T : Set D) (q : ℕ) (a : D) (hq : 0 < q)
    (hret : (ρ ^ q) (i a) ∈ i '' T)
    (hmin : ∀ j : ℕ, 0 < j → j < q → (ρ ^ j) (i a) ∉ i '' T) :
    ∃ n : ℕ, 0 < n ∧ i ((σ ^ n) a) = (ρ ^ q) (i a) ∧
      ∀ j : ℕ, 0 < j → j < n → (σ ^ j) a ∉ T := by
  induction q using Nat.strong_induction_on generalizing a with
  | h q ih =>
    obtain ⟨k, hk, he, hg⟩ := hscan a
    have hkq : k ≤ q := by
      by_contra hn
      exact hg q hq (by omega) (image_subset_range i T hret)
    by_cases heq : k = q
    · refine ⟨1, by omega, ?_, ?_⟩
      · simpa only [pow_one, heq] using he.symm
      · intro j hj hjn
        omega
    have hklt : k < q := lt_of_le_of_ne hkq heq
    have hshift (j : ℕ) : (ρ ^ j) (i (σ a)) = (ρ ^ (j + k)) (i a) := by
      rw [← he, ← Equiv.Perm.mul_apply, ← pow_add]
    have hrem : (ρ ^ (q - k)) (i (σ a)) = (ρ ^ q) (i a) := by
      rw [hshift, Nat.sub_add_cancel hkq]
    have hremmin : ∀ j : ℕ, 0 < j → j < q - k →
        (ρ ^ j) (i (σ a)) ∉ i '' T := by
      intro j hj hjq
      rw [hshift]
      exact hmin (j + k) (by omega) (by omega)
    obtain ⟨n, hn, hnret, hnmin⟩ := ih (q - k) (by omega) (σ a)
      (by omega) (hrem.symm ▸ hret) hremmin
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · rw [pow_succ, Equiv.Perm.mul_apply]
      exact hnret.trans hrem
    · intro j hj hjn hjT
      by_cases hjone : j = 1
      · subst j
        apply hmin k hk hklt
        rw [he]
        exact mem_image_of_mem i (by simpa only [pow_one] using hjT)
      · have hjform : j = (j - 1) + 1 := by omega
        apply hnmin (j - 1) (by omega) (by omega)
        rw [hjform, pow_succ, Equiv.Perm.mul_apply] at hjT
        exact hjT

private theorem drawing_first_return_image_of_scan
    {D E V U : Type*}
    {flipD : D → D} {σ : Equiv.Perm D} {vertD : D → V}
    {flipE : E → E} {ρ : Equiv.Perm E} {vertE : E → U}
    (P : PLDrawing D V flipD σ vertD) (Q : PLDrawing E U flipE ρ vertE)
    (i : D → E) (hi : Function.Injective i)
    (hscan : ∀ d, ∃ k : ℕ, 0 < k ∧ (ρ ^ k) (i d) = i (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ ^ j) (i d) ∉ range i)
    (T : Set D) (a : T) :
    (drawingFirstReturnPerm Q (i '' T) ⟨i a.val, mem_image_of_mem i a.property⟩).val =
      i (drawingFirstReturnPerm P T a).val := by
  classical
  let b : i '' T := ⟨i a.val, mem_image_of_mem i a.property⟩
  let q := subsetFirstReturnTime ρ (i '' T) (drawingPositiveReturn Q (i '' T)) b
  have hq := subsetFirstReturnTime_spec ρ (i '' T) (drawingPositiveReturn Q (i '' T)) b
  obtain ⟨n, hn, he, hg⟩ := scan_reaches_first σ ρ i hscan T q a.val hq.1
    (by simpa only [permIterateEqPow] using hq.2.1)
    (by simpa only [permIterateEqPow] using hq.2.2)
  have hnT : (σ ^ n) a.val ∈ T := by
    have hh : i ((σ ^ n) a.val) ∈ i '' T := he.symm ▸
      (show (ρ ^ q) (i a.val) ∈ i '' T from by
        simpa only [permIterateEqPow] using hq.2.1)
    exact (hi.mem_set_image).mp hh
  have htime : subsetFirstReturnTime σ T (drawingPositiveReturn P T) a = n := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (drawingPositiveReturn P T a)
        ⟨hn, by simpa only [permIterateEqPow] using hnT⟩
    · have ht := subsetFirstReturnTime_spec σ T (drawingPositiveReturn P T) a
      by_contra hh
      exact hg _ ht.1 (by omega) (by simpa only [permIterateEqPow] using ht.2.1)
  change (ρ : E → E)^[q] (i a.val) =
    i ((σ : D → D)^[subsetFirstReturnTime σ T (drawingPositiveReturn P T) a] a.val)
  rw [htime, permIterateEqPow, permIterateEqPow]
  exact he.symm

/-- Helper toward Proposition 3.9: deleting any set of geometric edges
commutes with the integer-start embedding at the level of restricted rotations. -/
theorem start_rotation_after_deletion (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (G : WholePlaneDrawing W H)
    (n : ℤ) (J : WholePlaneStartIso W n)
    (hfin : hatLimitFiniteIncidence (shiftedStream (shiftWordInt W n) 0))
    (K : Set ℕ) :
    let u := shiftedStream (shiftWordInt W n) 0
    let P := monotoneFamilyDrawing u hfin (monotone_family_all u)
    let T := {d : ℕ × Bool | d.1 ∈ K}
    ∀ (a : T) (d : retainedDarts W n K),
      J.dart (wholePlaneDartι (shiftWordInt W n) 0 a.val) = d.val →
      (drawingFirstReturnPerm G (retainedDarts W n K) d).val =
        J.dart (wholePlaneDartι (shiftWordInt W n) 0
          (drawingFirstReturnPerm P T a).val) := by
  intro u P T a
  let U := shiftWordInt W n
  let H' := rotation_hypothesis_shift W H n
  let i := fun a => J.dart (wholePlaneDartι U 0 a)
  have hi : Function.Injective i := J.dart.injective.comp (wholePlaneDartι_injective U 0)
  have hstep (x : WholePlaneDart U) :
      J.dart ((wholePlaneRotation U H').symm x) =
        (wholePlaneRotation W H).symm (J.dart x) := by
    apply (wholePlaneRotation W H).injective
    rw [← J.rot H H', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hiter (k : ℕ) (x : WholePlaneDart U) :
      J.dart (((wholePlaneRotation U H').symm ^ k) x) =
        ((wholePlaneRotation W H).symm ^ k) (J.dart x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih,
        pow_succ', Equiv.Perm.mul_apply]
  have hscan (b : ℕ × Bool) : ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm ^ k) (i b) =
        i ((kmswInfRot u hfin).symm b) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm ^ j) (i b) ∉ range i := by
    obtain ⟨k, hk, he, hg⟩ := wholePlaneRotation_symm_firstReturn_run U H' 0 b
    refine ⟨k, hk, ?_, ?_⟩
    · exact (hiter k (wholePlaneDartι U 0 b)).symm.trans (congrArg J.dart he)
    · intro j hj hjk hmem
      obtain ⟨c, hc⟩ := hmem
      apply hg j hj hjk
      refine ⟨c, J.dart.injective ?_⟩
      exact hc.trans (hiter j (wholePlaneDartι U 0 b)).symm
  have hS : retainedDarts W n K = i '' T := retained_darts_eq_image W n J K
  rw [hS]
  intro d ha
  have hd : d = (⟨i a.val, mem_image_of_mem i a.property⟩ : i '' T) := Subtype.ext ha.symm
  subst d
  exact drawing_first_return_image_of_scan P G i hi
    (forward_scan_of_inverse_scan (kmswInfRot u hfin) (wholePlaneRotation W H) i hscan) T a

/-- Helper toward Proposition 3.9: a single region parametrization preserves
every geometric clause, including restricted rotation, for arbitrary retained
edge sets at every integer start and on every geometric representative. -/
theorem representative_deletion_geometry
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
      (∀ d : T, intrinsicFutureRotation A (E '' K)
        (D (drawingFirstReturnPerm P T d).val) (D d.val)) ∧
      (∀ (d : T) (F : Q.Face),
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F) := by
  intro u G S V E D P T Q
  obtain ⟨R, hinj, hrange, hopen, hbound, hside⟩ :=
    representative_deletion_face_regions W H h hpast hp A I n J hfin K
  refine ⟨R, hinj, hrange, hopen, hbound, ?_, hside⟩
  intro a
  let b : retainedDarts W n K :=
    ⟨J.dart (wholePlaneDartι (shiftWordInt W n) 0 a.val), by
      rw [retained_darts_eq_image W n J K]
      exact mem_image_of_mem _ a.property⟩
  have hrot := start_rotation_after_deletion W H G n J hfin K a b rfl
  have hactual := representative_rotation W H h hpast hp A I n K b
  dsimp only at hactual
  rw [hrot] at hactual
  have hE : I.edgeEquiv '' (lemma38StartEdgeι W n '' K) = E '' K := by
    rw [image_image]
    congr 1
    funext e
    exact congrArg I.edgeEquiv (J.iota_edge e).symm
  rw [hE] at hactual
  exact hactual

/-- Helper toward Proposition 3.9: the exact geometric comparison required
for Proposition 5.1 holds for both source submaps at every integer start.
This supplies the recorded geometric obligation, without a law assertion. -/
theorem proposition51_geometry
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0}) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root)
      (n : ℤ) (J : WholePlaneStartIso W n),
    let u := fun i => futureMapShiftedCodePath n W (i + 1)
    ∀ (_hflow : HasFlowLineHits u) (hhat : hatLimitFiniteIncidence u)
      (hprime : primedLimitFiniteIncidence u) (hb : BoundaryHitWitnesses u),
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
          (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F) := by
  intro G I n J u
  have hu : u = shiftedStream (shiftWordInt W n) 0 := by
    funext i
    simp only [u, futureMapShiftedCodePath, shiftedCodePath, shiftWordInt,
      shiftedStream, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel, Int.ofNat_zero, sub_zero]
  dsimp only
  rw [hu]
  intro _hflow hhat _hprime _hb K _hK
  exact representative_deletion_geometry W H h hpast hp A I n J hhat K

private theorem window_edge_eq_shift (w : ℕ → Fin 3) (t : ℕ)
    (e : {e : ℕ // EdgePresent (fun i => w (t + i)) e}) :
    kmswWindowEdgeMapInf w t e.val = shiftLimitEdge w t e := by
  rw [actTime_spec (fun i => w (t + i)) e.val e.property]
  exact kmswWindowEdgeMapInf_active w t _

private theorem start_edge_nat (W : ℤ → Fin 3) (t e : ℕ) :
    lemma38StartEdgeι W (t : ℤ) e =
      wholePlaneEdgeι W 0 (kmswWindowEdgeMapInf (shiftedStream W 0) t e) := by
  by_cases ht : t = 0
  · subst t
    simp only [Nat.cast_zero, lemma38StartEdgeι, le_refl, ite_true, Int.natAbs_zero,
      kmswWindowEdgeMapInf_zero_start, id_eq]
  · simp only [lemma38StartEdgeι, show ¬ (t : ℤ) ≤ 0 by omega,
      ite_false, Int.toNat_natCast]

/-- Helper toward Proposition 3.9: the stopped hatted drawing has one
complete geometric comparison with the actual representative submap, at every
natural time, and hence at every boundary stopping time. -/
theorem stopped_hat_geometry
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
    (t : ℕ) (hτ : HasFlowLineHits (fun i => shiftedStream W 0 (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => shiftedStream W 0 (t + i))) :
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    let w := shiftedStream W 0
    let u := fun i => w (t + i)
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
        (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F) := by
  intro G w u S V E D P T Q
  obtain ⟨J⟩ := wholePlaneStartIso_nonempty W (t : ℤ)
  let U := shiftWordInt W (t : ℤ)
  have hu : shiftedStream U 0 = u := by
    funext i
    simp only [U, u, w, shiftedStream, shiftWordInt, Int.ofNat_zero, sub_zero, Nat.cast_add]
    congr 1
    omega
  let V' := fun v => I.vertexEquiv (J.vertex (wholePlaneVertexι U 0 v))
  let E' := fun e => I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 e))
  let K := {e | MhatGeometricEdge u e}
  have hd (d : ℕ × Bool) : J.dart (wholePlaneDartι U 0 d) =
      wholePlaneDartι W 0 (kmswWindowEdgeMapInf w t d.1, d.2) := by
    erw [J.dart_apply]
    exact Prod.ext ((J.iota_edge d.1).trans (start_edge_nat W t d.1)) rfl
  have he (e : ℕ) : E' (hatLimitEdgeMap u hτ e) = E e := by
    change I.edgeEquiv (J.edge (wholePlaneEdgeι U 0 _)) = _
    rw [J.iota_edge, start_edge_nat]
    exact congrArg (fun e => I.edgeEquiv (wholePlaneEdgeι W 0 e))
      (window_edge_eq_shift w t
        ⟨hatLimitEdgeMap u hτ e, ((hatLimitEdgeMap_range_iff u hτ _).mp ⟨e, rfl⟩).1⟩)
  have hedge : E' '' K = range E := by
    ext e
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨d, hd'⟩ := (hatLimitDartEquiv u hτ).surjective ⟨(f, false), hf⟩
      have hdf := congrArg (fun a : T => a.val.1) hd'
      exact ⟨d.1, (he d.1).symm.trans (congrArg E' hdf)⟩
    · rintro ⟨e, rfl⟩
      exact ⟨hatLimitEdgeMap u hτ e,
        ((hatLimitEdgeMap_range_iff u hτ _).mp ⟨e, rfl⟩).2, he e⟩
  have hvd (d : ℕ × Bool) :
      V' (kmswLimitDartVertex u (hatLimitEdgeMap u hτ d.1, d.2)) =
        V (kmswLimitDartVertex (hatCodes u hτ) d) := by
    have hs := start_iso_dart_vertex W (t : ℤ) J
      (wholePlaneDartι U 0 (hatLimitEdgeMap u hτ d.1, d.2))
    rw [wholePlaneDartVertex_ι, hu, hd, wholePlaneDartVertex_ι] at hs
    have hw : kmswWindowEdgeMapInf w t (hatLimitEdgeMap u hτ d.1) =
        intrinsicConsumer52RawHatEdge w t hτ d.1 :=
      window_edge_eq_shift w t
        ⟨_, ((hatLimitEdgeMap_range_iff u hτ _).mp ⟨d.1, rfl⟩).1⟩
    rw [hw, intrinsicConsumer52RawHat_dart_vertex] at hs
    exact congrArg I.vertexEquiv hs.symm
  have hvertex : V' '' intrinsicConsumer51RunVertices u K = range V := by
    ext v
    constructor
    · rintro ⟨a, ⟨d, hdK, rfl⟩, rfl⟩
      obtain ⟨b, hb⟩ := (hatLimitDartEquiv u hτ).surjective ⟨d, hdK⟩
      have hb' : (hatLimitEdgeMap u hτ b.1, b.2) = d := congrArg Subtype.val hb
      refine ⟨kmswLimitDartVertex (hatCodes u hτ) b, ?_⟩
      rw [← hvd b, hb']
    · rintro ⟨v, rfl⟩
      obtain ⟨d, hdv⟩ := kmswLimitDartVertex_surjective (hatCodes u hτ)
        (hatCodes_finiteIncidence u hτ hfin) v
      refine ⟨kmswLimitDartVertex u (hatLimitEdgeMap u hτ d.1, d.2), ?_, ?_⟩
      · exact ⟨(hatLimitEdgeMap u hτ d.1, d.2),
          ((hatLimitEdgeMap_range_iff u hτ _).mp ⟨d.1, rfl⟩).2, rfl⟩
      · exact (hvd d).trans (congrArg V hdv)
  have hg := fun hf : hatLimitFiniteIncidence (shiftedStream U 0) =>
    representative_deletion_geometry W H h hpast hp A I (t : ℤ) J hf K
  dsimp only at hg
  dsimp only [U] at hu hd
  rw [hu] at hg
  have hg := hg hfin
  obtain ⟨R, hinj, hrange, hopen, hbound, hrot, hside⟩ := hg
  refine ⟨R, hinj, ?_, hopen, hbound, ?_, ?_⟩
  · change range R = intrinsicConsumer51FaceRegions
      (intrinsicConsumer51Trace A (V' '' intrinsicConsumer51RunVertices u K) (E' '' K)) at hrange
    rw [hedge, hvertex] at hrange
    exact hrange
  · intro d
    have hr := hrot d
    erw [hd _, hd _] at hr
    change intrinsicFutureRotation A (E' '' K)
      (D (drawingFirstReturnPerm P T d).val) (D d.val) at hr
    rw [hedge] at hr
    exact hr
  · intro d F
    have hs := hside d F
    erw [hd _] at hs
    exact hs

/-- Helper toward Proposition 3.9: on one iid event, every stopped compressed
face orbit parametrizes precisely one actual representative region, with
oriented incidence and the marked unbounded orbit preserved. -/
theorem ae_stopped_hat_face_regions :
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
          (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d) := by
  filter_upwards [wholePlane_ae_boundaryShift_hatRootedMapHypotheses] with W hW
  intro H h hpast hp A I k t u hτ hfin G V E D
  have htrans := (hW h k).choose_spec.2 hτ
  let Q := hatRealizedDrawing u hfin
  let F := hatFaceOrbitEquiv u hτ hfin htrans
  obtain ⟨R₀, hinj, hrange, hopen, hbound, _, hside⟩ :=
    stopped_hat_geometry W H h hpast hp A I t hτ hfin
  let R := fun q => R₀ (F q)
  have hd (d : ℕ × Bool) :
      kmswWindowEdgeMapInf (shiftedStream W 0) t (hatLimitEdgeMap u hτ d.1) =
        intrinsicConsumer52RawHatEdge (shiftedStream W 0) t hτ d.1 :=
    window_edge_eq_shift _ t
      ⟨_, ((hatLimitEdgeMap_range_iff u hτ _).mp ⟨d.1, rfl⟩).1⟩
  have hs (d : ℕ × Bool) (q : HatFaceOrbit u hτ hfin) :
      (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Q.dartBorders (hatLimitDartEquiv u hτ d) (F q) := by
    have hh := hside (hatLimitDartEquiv u hτ d) (F q)
    dsimp only at hh
    rw [hatLimitDartEquiv_apply, hd] at hh
    exact hh
  refine ⟨R, hinj.comp F.injective, ?_, fun q => hopen (F q),
    fun d q => (hs d q).trans (dartBorders_hatFaceOrbitEquiv_iff u hτ hfin htrans d q),
    fun q => (hbound (F q)).trans (hatFaceOrbitEquiv_isUnbounded_iff u hτ hfin htrans q),
    fun d => (hs d _).trans (hatFaceOrbitEquiv_exterior_border u hτ hfin htrans d)⟩
  rw [← hrange]
  ext B
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨F q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨F.symm q, congrArg R₀ (F.apply_symm_apply q)⟩

/-- Helper toward Proposition 3.9: the exact recorded Lemma 5.2 geometric
comparison, specialized from the theorem at all natural times. -/
theorem lemma52_geometry :
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
      (∀ s, LeftAtOn (R F) (intrinsicFutureDartArc A (D d.val)) s) ↔ Q.dartBorders d F) := by
  intro W H h hpast hp A G I k w t u hτ hfin
  exact stopped_hat_geometry W H h hpast hp A I t hτ hfin

/-- Helper toward Proposition 3.9: the complete recorded Lemma 5.2 assembly
retains the common witnesses, laws, least visits, path containment, rooted
certificate, restricted rotation and actual face-orbit regions. -/
theorem ae_lemma52_assembly :
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
              (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes u hτ) d) := by
  filter_upwards [intrinsicConsumer52_sample, ae_stopped_hat_face_regions] with W hW hfaces
  obtain ⟨H, h, hpast, hp, hW⟩ := hW
  refine ⟨H, h, hpast, hp, ?_⟩
  intro hLL G A hA
  obtain ⟨hI, C, hC, _⟩ := hW A hA
  refine ⟨hI, C, ⟨hC.1, ?_⟩, fun C' _ => hC.1 C'⟩
  intro I t
  obtain ⟨hzero, hk⟩ := hC.2 I
  refine ⟨hzero, fun k => ?_⟩
  obtain ⟨hleast, ht, hstop, hlaw, hhatlaw, hword, hhatword,
    hpath, hmap, hcontain, hτ, hfin, hcode, hclause, hinj, hroot, hinc⟩ := hk k
  refine ⟨hleast, ht, hstop, hlaw, hhatlaw, hword, hhatword, hpath, hmap, hcontain,
    hτ, hfin, ?_⟩
  dsimp only
  refine ⟨hcode, hclause, hinj, hroot, hinc,
    intrinsicConsumer52Rooted_rotation W H h hpast hp A I (t k) hτ hfin, ?_⟩
  have hf := hfaces H h hpast hp A I k
  dsimp only at hf
  rw [← ht] at hf
  exact hf hτ hfin









end DirectedDistances.PaperProofs.Section3.ShiftedStartClosedRegionRoute4
