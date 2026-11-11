/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusActualSideIso2

 

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

section ActualFaceReverse

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}

variable (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
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

local notation "w" => shiftedStream W 0
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode :
  selectedCutCoherentDomain X renewalTime renewalTime_positiveSuccessTime)
local notation "Q" => geometricSideSubmap X renewalTime
  renewalTime_positiveSuccessTime ThinMapSide.left qL
local notation "p" => primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin
local notation "z" => hatCodes (boundaryGluingFutureStream W h k) hτ
local notation "EH" => boundaryGluingHatEdgeMap W h k hτ
local notation "E" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: an actual retained face step whose first dart is
represented by a primed creation triangle yields the corresponding code-side
face step. -/
theorem lMinusCodeWholeFaceNext_actual_reverse_of_primed_triangle
    (d e : LMinusCodeGluedDart rL Q)
    (hde : (S).faceNext (E d).val (E e).val)
    (a : ℕ × Bool) (j : TriangleCreationTime p)
    (hd : d = lMinusCodePrimedDart rL Q a)
    (ha : a ∈ stageTriangleDartList p j) :
    lMinusCodeWholeFaceNext rL qL hf d e := by
  subst d
  rw [lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk a] at hde
  have hcode : (rL).code.1 = p := by
    change (leftSideObsNonpos X k W).1 = p
    exact lMinus_primed_observation_code (longest := longest) hτ
  have hcongr : ∀ (c d : ℕ → Fin 3) (hc : KMSWFiniteIncidence c)
      (hd : KMSWFiniteIncidence d), c = d → kmswInfFaceSucc c hc =
        kmswInfFaceSucc d hd := by
    intro c d hc hd hcd
    subst d
    rfl
  have hsuccEq := hcongr _ _ hf (primedCode_finiteIncidence
    (boundaryGluingFutureStream W h k) hτ hfin) hcode
  have hsuccAt := congrArg (fun f : Equiv.Perm (ℕ × Bool) => f a) hsuccEq
  let b := kmswInfFaceSucc (rL).code.1 hf a
  let j' : TriangleCreationTime (rL).code.1 :=
    ⟨j.val, by rw [hcode]; exact j.property⟩
  have hlist : stageTriangleDartList p j =
      stageTriangleDartList (rL).code.1 j' := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, j', hcode]
  have hprimed := lMinusPrimedCodeFaceNext_actual hτ hp P hqMode Tpath
    hfin hleft hk j a ha
  have hsucc : (E e).val = lMinusPrimedDartImage hτ b := by
    calc
      (E e).val = kmswInfFaceSucc w (H.1 0)
          (lMinusPrimedDartImage hτ a) := hde.2.symm
      _ = lMinusPrimedDartImage hτ (kmswInfFaceSucc p
          (primedCode_finiteIncidence
            (boundaryGluingFutureStream W h k) hτ hfin) a) := hprimed.2
      _ = lMinusPrimedDartImage hτ b :=
        congrArg (lMinusPrimedDartImage hτ) hsuccAt.symm
  have he : e = lMinusCodePrimedDart rL Q b := by
    apply (Equiv.injective E)
    apply Subtype.ext
    rw [lMinusCodeGluedDartEquiv_primed hτ hp P hqMode Tpath hfin hleft hk b]
    exact hsucc
  subst e
  exact Or.inl ⟨a, b, rfl, rfl, ⟨j', hlist ▸ ha, rfl⟩⟩

include hτ hp P hqMode Tpath hfin hleft hk in
/-- Helper toward Lemma 5.5: an actual retained face step whose first dart is
represented by a retained hatted creation triangle yields the corresponding
code-side face step. -/
theorem lMinusCodeWholeFaceNext_actual_reverse_of_hatted_triangle
    (d e : LMinusCodeGluedDart rL Q)
    (hde : (S).faceNext (E d).val (E e).val)
    (a : {a : ℕ × Bool // a.1 ∈ (Q).edges}) (j : TriangleCreationTime z)
    (hd : d = lMinusCodeHattedDart rL Q a)
    (ha : a.val ∈ stageTriangleDartList z j)
    (hall : ∀ c ∈ stageTriangleDartList z j, c.1 ∈ (Q).edges) :
    lMinusCodeWholeFaceNext rL qL hf d e := by
  subst d
  have hstream := boundaryGluing_decoded_stream W h k hτ
  let z' := boltzmannKMSWStream (pathCode (boundaryFutureHattedPath k W))
  change z' = z at hstream
  have hprop : z' j.val = 0 ∨ z' j.val = 1 := by
    rw [hstream]
    exact j.property
  let j' : TriangleCreationTime z' := ⟨j.val, hprop⟩
  have hlist : stageTriangleDartList z j = stageTriangleDartList z' j' := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, j']
    rw [hstream]
  have ha' : a.val ∈ stageTriangleDartList z' j' := hlist ▸ ha
  have hall' : ∀ c ∈ stageTriangleDartList z' j', c.1 ∈ (Q).edges := by
    intro c hc
    exact hall c (hlist.symm ▸ hc)
  let hf' := sourceAncestor_finite_incidence X renewalTime
    renewalTime_positiveSuccessTime qL
  let c := kmswInfFaceSucc z' hf' a.val
  have hc : c ∈ stageTriangleDartList z' j' :=
    rMinusWhole_triangle_succ_mem z' hf' j' a.val ha'
  let b : {a : ℕ × Bool // a.1 ∈ (Q).edges} := ⟨c, hall' c hc⟩
  have hQ : (Q).faceNext a.val b.val := ⟨⟨j', ha', hall'⟩, rfl⟩
  have hcode : lMinusCodeWholeFaceNext rL qL hf
      (lMinusCodeHattedDart rL Q a) (lMinusCodeHattedDart rL Q b) :=
    Or.inr ⟨a, b, rfl, rfl, hQ⟩
  have hforward := lMinusCodeWholeFaceNext_actual_forward hτ hp P hqMode
    Tpath hfin hleft hk _ _ hcode
  rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk a,
    lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk b] at hforward
  rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk a] at hde
  have hsucc : (E e).val = (EH b.val.1, b.val.2) := hde.2.symm.trans hforward.2
  have he : e = lMinusCodeHattedDart rL Q b := by
    apply (Equiv.injective E)
    apply Subtype.ext
    rw [lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk b]
    exact hsucc
  subst e
  exact hcode

end ActualFaceReverse











































































end DirectedDistances.PaperProofs.Section5
