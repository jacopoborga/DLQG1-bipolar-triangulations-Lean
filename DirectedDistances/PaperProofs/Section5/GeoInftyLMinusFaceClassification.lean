/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusFaceTransportReduction
public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso8
public import DirectedDistances.KMSW.PrimedInteriorArcBridge

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5: a complete ambient creation triangle in the
range of an injective, flip-preserving first-return rotation embedding lifts
to creation darts. Finiteness is proved from the three ambient darts. -/
private theorem creationDart_preimage_of_firstReturn
    (u v : ℕ → Fin 3) (hu : KMSWFiniteIncidence u) (hv : KMSWFiniteIncidence v)
    (I : (ℕ × Bool) → ℕ × Bool) (hinj : Function.Injective I)
    (hflip : ∀ d, I (futureMapEdgeInv d) = futureMapEdgeInv (I d))
    (hreturn : ∀ d, ∃ n : ℕ, 0 < n ∧
      (kmswInfRot v hv : _ → _)^[n] (I d) = I (kmswInfRot u hu d) ∧
      ∀ m : ℕ, 0 < m → m < n →
        (kmswInfRot v hv : _ → _)^[m] (I d) ∉ Set.range I)
    (J : TriangleCreationTime v)
    (hall : ∀ d ∈ stageTriangleDartList v J, d ∈ Set.range I)
    (a : ℕ × Bool) (ha : I a ∈ stageTriangleDartList v J) :
    ∃ j : TriangleCreationTime u, a ∈ stageTriangleDartList u j := by
  let f := kmswInfFaceSucc u hu
  let g := kmswInfFaceSucc v hv
  let σ := kmswInfRot u hu
  let τ := kmswInfRot v hv
  have reflect (a b : ℕ × Bool) (hab : g (I a) = I b) : f a = b := by
    have hstep : τ (I b) = I (futureMapEdgeInv a) := by
      change τ.symm (futureMapEdgeInv (I a)) = I b at hab
      rw [← hflip] at hab
      have hh := congrArg τ hab
      rw [Equiv.apply_symm_apply] at hh
      exact hh.symm
    obtain ⟨n, hn, hret, hgap⟩ := hreturn b
    have hn1 : n = 1 := by
      by_contra hne
      exact hgap 1 (by omega) (by omega) ⟨futureMapEdgeInv a, by
        simpa only [Function.iterate_one] using hstep.symm⟩
    rw [hn1, Function.iterate_one, hstep] at hret
    have hs : futureMapEdgeInv a = σ b := hinj hret
    change σ.symm (futureMapEdgeInv a) = b
    rw [hs, Equiv.symm_apply_apply]
  have pos (b : ℕ × Bool) (hb : I b ∈ stageTriangleDartList v J) :
      I (f b) ∈ stageTriangleDartList v J := by
    have hg := (primedStageTriangleDartList_faceSucc_mem_iff v hv J (I b)).mpr hb
    obtain ⟨c, hc⟩ := hall _ hg
    rw [reflect b c hc.symm, hc]
    exact hg
  have neg (b : ℕ × Bool) (hb : I b ∈ stageTriangleDartList v J) :
      I (f.symm b) ∈ stageTriangleDartList v J := by
    have hg : g.symm (I b) ∈ stageTriangleDartList v J := by
      apply (primedStageTriangleDartList_faceSucc_mem_iff v hv J _).mp
      simpa only [g, Equiv.apply_symm_apply] using hb
    obtain ⟨c, hc⟩ := hall _ hg
    have hstep : g (I c) = I b := by rw [hc, Equiv.apply_symm_apply]
    have hfc := reflect c b hstep
    have hbc : f.symm b = c := by rw [← hfc, Equiv.symm_apply_apply]
    rw [hbc, hc]
    exact hg
  have hpos (n : ℕ) : I ((f : _ → _)^[n] a) ∈ stageTriangleDartList v J := by
    induction n with
    | zero => exact ha
    | succ n ih => rw [Function.iterate_succ_apply']; exact pos _ ih
  have hneg (n : ℕ) : I ((f.symm : _ → _)^[n] a) ∈ stageTriangleDartList v J := by
    induction n with
    | zero => exact ha
    | succ n ih => rw [Function.iterate_succ_apply']; exact neg _ ih
  have hfinite : {b | f.SameCycle a b}.Finite := by
    apply (Set.Finite.preimage hinj.injOn (stageTriangleDartList v J).finite_toSet).subset
    intro b hb
    obtain ⟨i, rfl⟩ := hb
    cases i with
    | ofNat n =>
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Int.ofNat_eq_natCast,
        zpow_natCast, Equiv.Perm.coe_pow] using hpos n
    | negSucc n =>
      simpa only [Set.mem_preimage, Set.mem_ofPred_eq, zpow_negSucc, ← inv_pow,
        Equiv.Perm.coe_pow, Equiv.Perm.inv_def] using hneg (n + 1)
  exact finiteFaceOrbit_mem_triangle u hu a hfinite

section

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈
    selectedCutCoherentDomain (if longest then XDP.ldp else XDP.sdp)
      renewalTime renewalTime_positiveSuccessTime)
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "p" => primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "D" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hfin in
/-- Helper toward Lemma 5.5: every future creation dart has a primed or
hatted oriented creation-dart representative. A triangle with a nonprimed
edge is fully root reachable; otherwise all three edges are primed. -/
theorem lMinusFutureCreationDart_in_block
    (J : TriangleCreationTime (boundaryGluingFutureStream W h k))
    (a : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList (boundaryGluingFutureStream W h k) J) :
    (∃ b : ℕ × Bool, ∃ j : TriangleCreationTime p,
      primedLimitDartMap (boundaryGluingFutureStream W h k) hτ b = a ∧
        b ∈ stageTriangleDartList p j) ∨
    (∃ b : ℕ × Bool, ∃ j : TriangleCreationTime
        (hatCodes (boundaryGluingFutureStream W h k) hτ),
      (hatLimitEdgeMap (boundaryGluingFutureStream W h k) hτ b.1, b.2) = a ∧
        b ∈ stageTriangleDartList
          (hatCodes (boundaryGluingFutureStream W h k) hτ) j) := by
  let U := boundaryGluingFutureStream W h k
  let hb := hatBoundaryHitWitnesses U hτ
  by_cases hprime : ∀ c ∈ stageTriangleDartList U J, primeGeomEdge U hfin hb c.1
  · let I := primedLimitDartMap U hτ
    let E := primedGeometricDartEquiv U hτ hfin hb
    have hall (c : ℕ × Bool) (hc : c ∈ stageTriangleDartList U J) :
        c ∈ Set.range I := by
      let cP : {c : ℕ × Bool // c ∈ primeDartSet U hfin hb} := ⟨c, hprime c hc⟩
      exact ⟨E.symm cP, congrArg Subtype.val (E.apply_symm_apply cP)⟩
    obtain ⟨b, hb⟩ := hall a ha
    obtain ⟨j, hj⟩ := creationDart_preimage_of_firstReturn p U
      (primedCode_finiteIncidence U hτ hfin) hfin I
      (primedLimitDartMap_injective U hτ) (primedLimitDartMap_edgeInv U hτ)
      (lMinus_primed_future_firstReturn hτ hfin) J hall b (hb.symm ▸ ha)
    exact Or.inl ⟨b, j, hb, hj⟩
  · push Not at hprime
    obtain ⟨c, hc, hnot⟩ := hprime
    have hm : MhatGeometricEdge U c.1 := by
      by_contra hn
      exact hnot (Or.inl hn)
    have hbeta : ¬ primeBetaEdge U hfin hb c.1 := fun h => hnot (Or.inr h)
    have hreach := primedStageTriangle_reachable_of_deletedDart
      U hτ hfin hb J c hc hm hbeta
    let I : (ℕ × Bool) → ℕ × Bool := fun b => (hatLimitEdgeMap U hτ b.1, b.2)
    let E := hatLimitDartEquiv U hτ
    have hall (b : ℕ × Bool) (hb : b ∈ stageTriangleDartList U J) :
        b ∈ Set.range I := by
      have he : b.1 ∈ ({(stageTriangleDartTriple U J).1.1,
          (stageTriangleDartTriple U J).2.1.1,
          (stageTriangleDartTriple U J).2.2.1} : Multiset ℕ) := by
        simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> simp
      rw [stageTriangleDartTriple_edges_eq_record] at he
      have he' : b.1 ∈ [(stageTriangleRecord U J).1,
          (stageTriangleRecord U J).2.1, (stageTriangleRecord U J).2.2] := by
        simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
          List.mem_cons, List.not_mem_nil, or_false] using he
      let bH : {b : ℕ × Bool // MhatGeometricEdge U b.1} := ⟨b, hreach b.1 he'⟩
      exact ⟨E.symm bH, congrArg Subtype.val (E.apply_symm_apply bH)⟩
    obtain ⟨b, hb⟩ := hall a ha
    have hinj : Function.Injective I := by
      intro b c hbc
      have hbit := congrArg (fun d : ℕ × Bool => d.2) hbc
      apply Prod.ext
      · exact hatLimitEdgeMap_injective U hτ (congrArg Prod.fst hbc)
      · exact hbit
    obtain ⟨j, hj⟩ := creationDart_preimage_of_firstReturn (hatCodes U hτ) U
      (hatCodes_inducedFiniteIncidence U hτ hfin) hfin I hinj (fun _ => rfl)
      (hatInfRot_firstReturn U hτ hfin) J hall b (hb.symm ▸ ha)
    exact Or.inr ⟨b, j, hb, hj⟩

include hτ hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: an actual retained face dart has an oriented
creation-dart preimage in the future map. The whole run-zero triangle lies
in that future range, so first return preserves its finite orbit. -/
theorem lMinusActualFaceNext_future_creation
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    ∃ a : ℕ × Bool, ∃ J : TriangleCreationTime (boundaryGluingFutureStream W h k),
      (boundaryGluingEdgeMap W h k a.1, a.2) = d ∧
        a ∈ stageTriangleDartList (boundaryGluingFutureStream W h k) J := by
  let U := boundaryGluingFutureStream W h k
  let I : (ℕ × Bool) → ℕ × Bool :=
    fun a => (boundaryGluingEdgeMap W h k a.1, a.2)
  have hinj : Function.Injective I := by
    intro a b hab
    have hbit := congrArg (fun c : ℕ × Bool => c.2) hab
    apply Prod.ext
    · exact boundaryGluingEdgeMap_injective W h k (congrArg Prod.fst hab)
    · exact hbit
  obtain ⟨J, hd, hretain⟩ := lMinusActualFaceNext_triangle hp P d e hde
  have hall (c : ℕ × Bool) (hc : c ∈ stageTriangleDartList (shiftedStream W 0) J) :
      c ∈ Set.range I := by
    have hblock : c ∈ Set.range (lMinusPrimedDartImage hτ) ∪
        Set.range (fun a : {a : ℕ × Bool // a.1 ∈ (Q).edges} =>
          (boundaryGluingHatEdgeMap W h k hτ a.val.1, a.val.2)) := by
      rw [← lMinus_side_darts_union hτ hp P hqMode Tpath hfin hleft hk]
      exact hretain c hc
    rcases hblock with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact ⟨primedLimitDartMap U hτ b, hb⟩
    · exact ⟨(hatLimitEdgeMap U hτ b.val.1, b.val.2), hb⟩
  obtain ⟨a, ha⟩ := hall d hd
  refine ⟨a, ?_⟩
  obtain ⟨j, hj⟩ := creationDart_preimage_of_firstReturn U (shiftedStream W 0)
    hfin (H.1 0) I hinj (fun _ => rfl)
    (lMinus_future_firstReturn (H := H) hfin) J hall a (ha.symm ▸ hd)
  exact ⟨j, ha, hj⟩

/-- Helper toward Lemma 5.5: every retained actual face dart has an
oriented creation-dart representative in the primed block or hatted block.
The future triangle and its block representative are constructed from the
actual face, without a block-classification premise. -/
theorem lMinusActualFaceNext_creation_in_block
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime p,
      lMinusPrimedDartImage hτ a = d ∧ a ∈ stageTriangleDartList p j) ∨
    (∃ a : ℕ × Bool, ∃ j : TriangleCreationTime
        (hatCodes (boundaryGluingFutureStream W h k) hτ),
      (boundaryGluingHatEdgeMap W h k hτ a.1, a.2) = d ∧
        a ∈ stageTriangleDartList
          (hatCodes (boundaryGluingFutureStream W h k) hτ) j) := by
  obtain ⟨a, J, ha, hJ⟩ := lMinusActualFaceNext_future_creation
    hτ hp P hqMode Tpath hfin hleft hk d e hde
  let I : (ℕ × Bool) → ℕ × Bool :=
    fun c => (boundaryGluingEdgeMap W h k c.1, c.2)
  rcases lMinusFutureCreationDart_in_block hτ hfin J a hJ with
    ⟨b, j, hb, hj⟩ | ⟨b, j, hb, hj⟩
  · exact Or.inl ⟨b, j, (congrArg I hb).trans ha, hj⟩
  · exact Or.inr ⟨b, j, (congrArg I hb).trans ha, hj⟩

/-- Helper toward Lemma 5.5: an actual retained face step starting at the
image of a primed creation dart lifts to the code relation, with both exact
dart images. No face correspondence is assumed for its second dart. -/
theorem lMinusActualFaceNext_primed_creation_lift
    (j : TriangleCreationTime p) (a e : ℕ × Bool)
    (ha : a ∈ stageTriangleDartList p j)
    (hde : (S).faceNext (lMinusPrimedDartImage hτ a) e) :
    ∃ d' e' : LMinusCodeGluedDart rL Q,
      (D d').val = lMinusPrimedDartImage hτ a ∧ (D e').val = e ∧
      lMinusCodeWholeFaceNext rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) d' e' := by
  let d' := lMinusCodePrimedDart rL Q a
  have hd' : (D d').val = lMinusPrimedDartImage hτ a :=
    lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk a
  obtain ⟨J, hdJ, heJ, hJ⟩ :=
    lMinusActualFaceNext_triangle_cycle hp P _ e hde
  let eS : {a : ℕ × Bool // a.1 ∈ (S).edges} := ⟨e, hJ e heJ⟩
  let e' := (D).symm eS
  have he' : (D e').val = e := congrArg Subtype.val ((D).apply_symm_apply eS)
  refine ⟨d', e', hd', he', ?_⟩
  apply lMinusCodeWholeFaceNext_actual_reverse_of_primed_triangle
    hτ hp P hqMode Tpath hfin hleft hk d' e' _ a j rfl ha
  rw [hd', he']
  exact hde

/-- Helper toward Lemma 5.5: every actual retained face step lifts to the
branchwise code relation. The creation-block classification is proved above. -/
theorem lMinusCodeWholeFaceNext_actual_reverse
    (d e : ℕ × Bool) (hde : (S).faceNext d e) :
    ∃ d' e' : LMinusCodeGluedDart rL Q,
      (D d').val = d ∧ (D e').val = e ∧
      lMinusCodeWholeFaceNext rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) d' e' := by
  rcases lMinusActualFaceNext_creation_in_block
      hτ hp P hqMode Tpath hfin hleft hk d e hde with
    ⟨a, j, ha, hj⟩ | ⟨a, j, ha, hj⟩
  · rw [← ha] at hde ⊢
    exact lMinusActualFaceNext_primed_creation_lift
      hτ hp P hqMode Tpath hfin hleft hk j a e hj hde
  · rw [← ha] at hde ⊢
    exact lMinusActualFaceNext_hatted_creation_lift
      hτ hp P hqMode Tpath hfin hleft hk j a e hj hde

/-- Helper toward Lemma 5.5: code face succession and actual retained
face succession agree under the exact glued dart equivalence. -/
theorem lMinusCodeWholeFaceNext_actual_iff
    (d e : LMinusCodeGluedDart rL Q) :
    lMinusCodeWholeFaceNext rL qL
        (lMinus_primed_observation_finiteIncidence hτ hfin) d e ↔
      (S).faceNext (D d).val (D e).val := by
  constructor
  · exact lMinusCodeWholeFaceNext_actual_forward hτ hp P hqMode Tpath hfin hleft hk d e
  · intro hde
    obtain ⟨d', e', hd, he, hcode⟩ := lMinusCodeWholeFaceNext_actual_reverse
      hτ hp P hqMode Tpath hfin hleft hk (D d).val (D e).val hde
    have hd' : d' = d := (D).injective (Subtype.ext hd)
    have he' : e' = e := (D).injective (Subtype.ext he)
    exact hd' ▸ he' ▸ hcode

/-- Helper toward Lemma 5.5: the full glued cell equivalence transports
face succession in both directions, including the identified beta seam. -/
theorem lMinusGluedCellEquiv_faceNext_transport_iff
    (u v : Sum (LMinusGluedVertex hτ hqMode) (LMinusGluedDart hτ hqMode)) :
    lMinusCodeWholeSideRelation hτ hqMode hfin .faceNext
        ((lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u)
        ((lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v) ↔
      geometricSideRelation S .faceNext
        (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk u)
        (lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk v) := by
  constructor
  · exact lMinusGluedCellEquiv_faceNext_transport_forward
      hτ hp P hqMode Tpath hfin hleft hk u v
  · intro hactual
    cases u with
    | inl u => exact False.elim hactual
    | inr u =>
      cases v with
      | inl v => exact False.elim hactual
      | inr v =>
        have hu :
            (lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
                (Sum.inr u) = Sum.inr
                  ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u) := by
          simp [lMinusCodeCellEquiv]
        have hv :
            (lMinusCodeCellEquiv hτ hp P hqMode Tpath hfin hleft hk).symm
                (Sum.inr v) = Sum.inr
                  ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v) := by
          simp [lMinusCodeCellEquiv]
        rw [hu, hv]
        change lMinusCodeWholeFaceNext rL qL
          (lMinus_primed_observation_finiteIncidence hτ hfin)
          ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm u)
          ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm v)
        have hcomp (d : LMinusGluedDart hτ hqMode) :
            (D ((lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk).symm d)).val =
              (lMinusGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk d).val := by
          simp [lMinusCodeGluedDartEquiv, lMinusCodeToGluedDartEquiv]
        apply (lMinusCodeWholeFaceNext_actual_iff
          hτ hp P hqMode Tpath hfin hleft hk _ _).mpr
        rw [hcomp u, hcomp v]
        exact hactual

end
end DirectedDistances.PaperProofs.Section5
