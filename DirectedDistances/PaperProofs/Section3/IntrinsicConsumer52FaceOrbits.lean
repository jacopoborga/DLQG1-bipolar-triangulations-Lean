/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicConsumer52RootedClauses
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart7

/- # Stopped hatted face-orbit coordinates

The compressed orbit quotient is identified with the face-successor quotient
of the actual restricted original drawing, preserving individual darts.
This is a permutation quotient, not yet a complementary-region equivalence.
The outstanding geometric statement is recorded with all binders below. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open MeasureTheory
open scoped Topology

private theorem faceOrbits_shiftLimitEdge_zero (w : ℕ → Fin 3)
    (e : {e : ℕ // EdgePresent (fun i => w (0 + i)) e}) :
    shiftLimitEdge w 0 e = e.val := by
  unfold shiftLimitEdge
  simpa only [Nat.zero_add] using
    (actTime_spec (fun i => w (0 + i)) e.val e.property).symm

/-- Helper toward Proposition 3.9: at time zero the stopped hatted edge
embedding is the original hatted embedding, edge by edge. -/
theorem intrinsicConsumer52RawHatEdge_zero (w : ℕ → Fin 3)
    (hτ : HasFlowLineHits (fun i => w (0 + i))) (e : ℕ) :
    intrinsicConsumer52RawHatEdge w 0 hτ e =
      hatLimitEdgeMap (fun i => w (0 + i)) hτ e :=
  faceOrbits_shiftLimitEdge_zero w _

/-- Helper toward Proposition 3.9: the retained edge set at time zero
is exactly the full reachable geometric edge set. -/
theorem intrinsicConsumer52RawHatEdge_zero_range (w : ℕ → Fin 3)
    (hτ : HasFlowLineHits w) :
    Set.range (intrinsicConsumer52RawHatEdge w 0
      (by simpa only [Nat.zero_add] using hτ)) = {e | MhatGeometricEdge w e} := by
  have he (e : ℕ) : intrinsicConsumer52RawHatEdge w 0
      (by simpa only [Nat.zero_add] using hτ) e = hatLimitEdgeMap w hτ e := by
    simpa only [Nat.zero_add] using intrinsicConsumer52RawHatEdge_zero w
      (by simpa only [Nat.zero_add] using hτ) e
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    rw [he]
    exact ((hatLimitEdgeMap_range_iff w hτ _).mp ⟨f, rfl⟩).2
  · intro hM
    obtain ⟨d, hd⟩ := (hatLimitDartEquiv w hτ).surjective ⟨(e, false), hM⟩
    refine ⟨d.1, (he d.1).trans ?_⟩
    exact congrArg Prod.fst (congrArg Subtype.val hd)

/-- Helper toward Proposition 3.9: the stopped compressed geometric edge
map is injective before transport to any representative. -/
theorem intrinsicConsumer52RawHatEdge_injective (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) :
    Function.Injective (intrinsicConsumer52RawHatEdge w t hτ) := by
  intro e f hef
  have hh := shiftLimitEdge_injective w t hef
  exact hatLimitEdgeMap_injective _ hτ (congrArg Subtype.val hh)

/-- Helper toward Proposition 3.9: the compressed darts are exactly all
darts of the actual retained original edge set, with the dart bit preserved. -/
@[expose] def intrinsicConsumer52RawHatDartEquiv (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i))) :
    (ℕ × Bool) ≃ {d : ℕ × Bool //
      d.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)} :=
  Equiv.ofBijective
    (fun d : ℕ × Bool =>
      (⟨(intrinsicConsumer52RawHatEdge w t hτ d.1, d.2), ⟨d.1, rfl⟩⟩ :
        {a : ℕ × Bool // a.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)}))
    ⟨by
      intro d e hde
      have hh := congrArg Subtype.val hde
      change (intrinsicConsumer52RawHatEdge w t hτ d.1, d.2) =
        (intrinsicConsumer52RawHatEdge w t hτ e.1, e.2) at hh
      have hb := congrArg (fun a : ℕ × Bool => a.2) hh
      exact Prod.ext
        (intrinsicConsumer52RawHatEdge_injective w t hτ (congrArg Prod.fst hh))
        hb, by
      rintro ⟨⟨e, b⟩, f, hf⟩
      exact ⟨(f, b), Subtype.ext (Prod.ext hf rfl)⟩⟩

/-- Helper toward Proposition 3.9: the actual restricted drawing's face
successor is inverse geometric first-return rotation after incidence reversal. -/
@[expose] def intrinsicConsumer52RestrictedFaceSuccessor (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) :
    Equiv.Perm {d : ℕ × Bool //
      d.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)} :=
  let P := monotoneFamilyDrawing w hfinW (monotone_family_all w)
  let T := {d : ℕ × Bool | d.1 ∈ Set.range (intrinsicConsumer52RawHatEdge w t hτ)}
  (drawingFirstReturnPerm P T).symm *
    { toFun := restrictedFlip P T (fun _ => Iff.rfl)
      invFun := restrictedFlip P T (fun _ => Iff.rfl)
      left_inv := fun d => Subtype.ext (by
        change (d.val.1, !(!d.val.2)) = d.val
        simp only [Bool.not_not])
      right_inv := fun d => Subtype.ext (by
        change (d.val.1, !(!d.val.2)) = d.val
        simp only [Bool.not_not]) }

/-- Helper toward Proposition 3.9: actual restricted face succession
commutes with the complete compressed dart equivalence. -/
theorem intrinsicConsumer52RawHatDartEquiv_faceSuccessor (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    intrinsicConsumer52RawHatDartEquiv w t hτ
      (kmswInfFaceSucc (hatCodes (fun i => w (t + i)) hτ)
        (hatCodes_finiteIncidence _ hτ hfin) d) =
      intrinsicConsumer52RestrictedFaceSuccessor w t hτ hfinW
        (intrinsicConsumer52RawHatDartEquiv w t hτ d) :=
  intrinsicConsumer52RawHat_faceSuccessor w t hτ hfin hfinW d

private theorem faceOrbits_pow_comm {α β : Type*} (f : α → β)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (hcomm : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (x : α) :
    f ((σ ^ n) x) = (τ ^ n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hcomm, ih,
      pow_succ', Equiv.Perm.mul_apply]

private theorem faceOrbits_zpow_comm {α β : Type*} (f : α → β)
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (hcomm : ∀ x, f (σ x) = τ (f x)) (n : ℤ) (x : α) :
    f ((σ ^ n) x) = (τ ^ n) (f x) := by
  have hinv : ∀ x, f (σ.symm x) = τ.symm (f x) := by
    intro x
    apply τ.injective
    rw [Equiv.apply_symm_apply, ← hcomm, Equiv.apply_symm_apply]
  cases n with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
      faceOrbits_pow_comm f σ τ hcomm n x
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using
      faceOrbits_pow_comm f σ.symm τ.symm hinv (n + 1) x

/-- Helper toward Proposition 3.9: two compressed darts belong to the same
face orbit exactly when their actual retained darts do, including infinite orbits. -/
theorem intrinsicConsumer52RawHatDartEquiv_sameCycle (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d e : ℕ × Bool) :
    (intrinsicConsumer52RestrictedFaceSuccessor w t hτ hfinW).SameCycle
      (intrinsicConsumer52RawHatDartEquiv w t hτ d)
      (intrinsicConsumer52RawHatDartEquiv w t hτ e) ↔
    (kmswInfFaceSucc (hatCodes (fun i => w (t + i)) hτ)
      (hatCodes_finiteIncidence _ hτ hfin)).SameCycle d e := by
  let D := intrinsicConsumer52RawHatDartEquiv w t hτ
  let σ := kmswInfFaceSucc (hatCodes (fun i => w (t + i)) hτ)
    (hatCodes_finiteIncidence _ hτ hfin)
  let τ := intrinsicConsumer52RestrictedFaceSuccessor w t hτ hfinW
  have hcomm : ∀ x, D (σ x) = τ (D x) :=
    intrinsicConsumer52RawHatDartEquiv_faceSuccessor w t hτ hfin hfinW
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, D.injective ((faceOrbits_zpow_comm D σ τ hcomm n d).trans hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (faceOrbits_zpow_comm D σ τ hcomm n d).symm.trans (congrArg D hn)⟩

/-- Helper toward Proposition 3.9: the compressed face-orbit quotient is
equivalent to the actual restricted drawing's face-successor quotient.
Identifying this quotient with complementary regions remains a separate obligation. -/
@[expose] def intrinsicConsumer52RestrictedFaceOrbitEquiv (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) :
    HatFaceOrbit (fun i => w (t + i)) hτ hfin ≃
      Quotient (Equiv.Perm.SameCycle.setoid
        (intrinsicConsumer52RestrictedFaceSuccessor w t hτ hfinW)) := by
  let D := intrinsicConsumer52RawHatDartEquiv w t hτ
  let f : HatFaceOrbit (fun i => w (t + i)) hτ hfin →
      Quotient (Equiv.Perm.SameCycle.setoid
        (intrinsicConsumer52RestrictedFaceSuccessor w t hτ hfinW)) :=
    Quotient.map D (fun d e hde =>
      (intrinsicConsumer52RawHatDartEquiv_sameCycle w t hτ hfin hfinW d e).mpr hde)
  apply Equiv.ofBijective f
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro d e hde
    exact Quotient.sound
      ((intrinsicConsumer52RawHatDartEquiv_sameCycle w t hτ hfin hfinW d e).mp
        (Quotient.exact hde))
  · intro q
    refine Quotient.inductionOn q ?_
    intro d
    obtain ⟨e, rfl⟩ := D.surjective d
    exact ⟨Quotient.mk _ e, rfl⟩

/-- Helper toward Proposition 3.9: orbit coordinates retain the precise
geometric dart representative rather than only the underlying edge. -/
theorem intrinsicConsumer52RestrictedFaceOrbitEquiv_mk (w : ℕ → Fin 3) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i)))
    (hfinW : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    intrinsicConsumer52RestrictedFaceOrbitEquiv w t hτ hfin hfinW (Quotient.mk _ d) =
      Quotient.mk _ (intrinsicConsumer52RawHatDartEquiv w t hτ d) := rfl

section Representative

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (A : D39DomainRootedMap.{0})

local notation "w" => shiftedStream W 0
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "P" => monotoneFamilyDrawing w ((And.left H) 0) (monotone_family_all w)

/-- Helper toward Proposition 3.9: every stopped compressed dart has
exactly one actual open complementary region on its left in the representative.
This pointwise result does not yet identify which darts share that region. -/
theorem intrinsicConsumer52_dart_region_existsUnique
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) (t : ℕ)
    (hτ : HasFlowLineHits (fun i => w (t + i)))
    (hfin : hatLimitFiniteIncidence (fun i => w (t + i))) (d : ℕ × Bool) :
    let V := intrinsicConsumer52HatVertex W H G hp A I t hτ
    let E := intrinsicConsumer52HatEdge W H G hp A I t hτ
    let D := intrinsicConsumer52HatDart W H h hpast hp A I t hτ
    ∃! U : Set ℂ,
      U ∈ intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      IsOpen U ∧ ∀ s, LeftAtOn U (intrinsicFutureDartArc A (D d)) s := by
  intro V E D
  let K := Set.range (intrinsicConsumer52RawHatEdge w t hτ)
  let T := {a : ℕ × Bool | a.1 ∈ K}
  let Q := restrictDrawing P T (fun _ => Iff.rfl)
  let δ := intrinsicConsumer52RawHatDartEquiv w t hτ d
  have hvert : Function.Surjective (restrictedVertex P T) := by
    rintro ⟨v, a, ha, hav⟩
    exact ⟨⟨a, ha⟩, Subtype.ext hav⟩
  obtain ⟨F, hF, huniq⟩ :=
    Q.dartBorders_existsUnique_of_locallyFiniteVertexImage32
      (LeftSideHalfDisk.locallyFiniteVertexImage_of_surjective Q hvert) δ
  obtain ⟨_, hrange, hopen, _, _, hside⟩ :=
    intrinsicConsumer52Rooted_geometry W H h hpast hp A I t hτ hfin
  have hs (F' : Q.Face) :
      (∀ s, LeftAtOn (I.h '' F'.val) (intrinsicFutureDartArc A (D d)) s) ↔
        Q.dartBorders δ F' := hside δ F'
  refine ⟨I.h '' F.val, ⟨?_, hopen F, (hs F).mpr hF⟩, ?_⟩
  · rw [← hrange]
    exact ⟨F, rfl⟩
  · rintro U ⟨hU, _, hleft⟩
    rw [← hrange] at hU
    obtain ⟨F', rfl⟩ := hU
    exact congrArg (fun F' : Q.Face => I.h '' F'.val)
      (huniq F' ((hs F').mp hleft))

/-- Helper toward Proposition 3.9: at stopping index zero, compressed
face orbits parametrize the actual representative regions, preserving every
dart-side incidence and the unbounded exterior. The transience input is a
walk property, supplied by the common iid event, not a geometric premise. -/
theorem intrinsicConsumer52_zero_face_regions
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root)
    (hτ : HasFlowLineHits w)
    (htrans : Filter.Tendsto (L (hatCodes w hτ)) Filter.atTop Filter.atTop) :
    let hτ0 : HasFlowLineHits (fun i => w (0 + i)) := by
      simpa only [Nat.zero_add] using hτ
    let V := intrinsicConsumer52HatVertex W H G hp A I 0 hτ0
    let E := intrinsicConsumer52HatEdge W H G hp A I 0 hτ0
    let D := intrinsicConsumer52HatDart W H h hpast hp A I 0 hτ0
    ∃ R : HatFaceOrbit w hτ (H.1 0) → Set ℂ,
      Function.Injective R ∧
      Set.range R = intrinsicConsumer51FaceRegions
        (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
      (∀ q, IsOpen (R q)) ∧
      (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Quotient.mk _ d = q) ∧
      (∀ q, (¬ Bornology.IsBounded (R q)) ↔
        q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
        (intrinsicFutureDartArc A (D d)) s) ↔ limitExternalDart (hatCodes w hτ) d) := by
  intro hτ0 V E D
  let Q := hatRealizedDrawing w (H.1 0)
  let F := hatFaceOrbitEquiv w hτ (H.1 0) htrans
  let R := fun q => I.h '' (F q).val
  obtain ⟨hinj, hrange, hopen, hexternal, _, hside⟩ :=
    intrinsicConsumer52Rooted_geometry W H h hpast hp A I 0 hτ0
      (by simpa only [Nat.zero_add] using (show hatLimitFiniteIncidence w from H.1 0))
  rw [intrinsicConsumer52RawHatEdge_zero_range w hτ] at hinj hrange hopen hexternal hside
  have hd (d : ℕ × Bool) :
      (hatLimitDartEquiv w hτ d).val =
        (intrinsicConsumer52RawHatEdge w 0 hτ0 d.1, d.2) := by
    rw [intrinsicConsumer52RawHatEdge_zero]
    simp only [Nat.zero_add, hatLimitDartEquiv_apply]
  have hs (d : ℕ × Bool) (q : HatFaceOrbit w hτ (H.1 0)) :
      (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
        Q.dartBorders (hatLimitDartEquiv w hτ d) (F q) := by
    have hs' := hside (hatLimitDartEquiv w hτ d) (F q)
    dsimp only at hs'
    rw [hd d] at hs'
    exact hs'
  refine ⟨R, hinj.comp F.injective, ?_, fun q => hopen (F q),
    fun d q => (hs d q).trans (dartBorders_hatFaceOrbitEquiv_iff w hτ _ htrans d q),
    fun q => (hexternal (F q)).trans
      (hatFaceOrbitEquiv_isUnbounded_iff w hτ _ htrans q),
    fun d => (hs d _).trans (hatFaceOrbitEquiv_exterior_border w hτ _ htrans d)⟩
  rw [← hrange]
  ext U
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨F q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨F.symm q, congrArg (fun q : Q.Face => I.h '' q.val)
      (F.apply_symm_apply q)⟩

end Representative

/-- Helper toward Proposition 3.9: one iid event supplies the complete
time-zero face-region identification simultaneously for every representative,
every source isomorphism and every choice of the standing witnesses. -/
theorem intrinsicConsumer52_zero_sample :
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
      (hτ : HasFlowLineHits (shiftedStream W 0)),
      let hτ0 : HasFlowLineHits (fun i => shiftedStream W 0 (0 + i)) := by
        simpa only [Nat.zero_add] using hτ
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let V := intrinsicConsumer52HatVertex W H G hp A I 0 hτ0
      let E := intrinsicConsumer52HatEdge W H G hp A I 0 hτ0
      let D := intrinsicConsumer52HatDart W H h hpast hp A I 0 hτ0
      ∃ R : HatFaceOrbit (shiftedStream W 0) hτ (H.1 0) → Set ℂ,
        Function.Injective R ∧
        Set.range R = intrinsicConsumer51FaceRegions
          (intrinsicConsumer51Trace A (Set.range V) (Set.range E)) ∧
        (∀ q, IsOpen (R q)) ∧
        (∀ d q, (∀ s, LeftAtOn (R q) (intrinsicFutureDartArc A (D d)) s) ↔
          Quotient.mk _ d = q) ∧
        (∀ q, (¬ Bornology.IsBounded (R q)) ↔
          q = Quotient.mk _ futureMapOuterDart) ∧
        (∀ d, (∀ s, LeftAtOn (R (Quotient.mk _ futureMapOuterDart))
          (intrinsicFutureDartArc A (D d)) s) ↔
            limitExternalDart (hatCodes (shiftedStream W 0) hτ) d) := by
  filter_upwards [wholePlane_ae_boundaryShift_hatRootedMapHypotheses] with W hW
  intro H h hpast hp A I hτ
  have hzero := hW h 0
  dsimp only at hzero
  have hu : (fun i => shiftedStream W 0
      (boundaryHitTime (shiftedStream W 0) h 0 + i)) = shiftedStream W 0 := by
    funext i
    rw [boundaryHitTime_zero, Nat.zero_add]
  rw [hu] at hzero
  exact intrinsicConsumer52_zero_face_regions W H h hpast hp A I hτ
    (hzero.choose_spec.2 hτ)

/- EXACT REMAINING GEOMETRIC STATEMENT (not a declaration or a premise).
The zero-time theorem above does not prove this assertion at general k.

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

Concrete obstruction: intrinsicConsumer52RestrictedFaceOrbitEquiv identifies
the two permutation quotients, but does not identify either quotient with
the complementary components of the restricted original drawing. The
pointwise unique actual region supplied by intrinsicConsumer52_dart_region_existsUnique
has not been proved constant precisely on these orbits, exhaustive over all
regions, or unbounded precisely on the marked exterior orbit. At time zero
the already proved hatFaceOrbitEquiv supplies these facts. For a general
stopped shift, its drawing is a different monotone-family construction.

EXACT REMAINING ASSEMBLY STATEMENT (not a declaration or a premise).
This retains the common witnesses and every clause of intrinsicConsumer52_sample,
and adds actual restricted rotation and the complete actual face-region map.
No theorem with this type is exported by this file.

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

end DirectedDistances.PaperProofs.Section3
