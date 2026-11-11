/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLPlusSideMeasurable5

/-! # Stopped-prefix comparison for the nonnegative left presentation

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Probability
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.5. The stopped-prefix observation has exactly the
boundary hit time as its extended stopping frontier. -/
theorem lPlusBoundaryCodeStoppingTime_eq_boundaryHitTime
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ) :
    boundaryCodeStoppingTime k (shiftedCodePath W 0) =
      (boundaryHitTime (shiftedStream W 0) h k : ℕ∞) := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryCodeStoppingTime, boundaryHitTime]
  · by_cases hk : 0 < k
    · have hcode : BoundaryHitWitnesses
          (fun i => shiftedCodePath W 0 (i + 1)) := by
        simpa [shiftedCodePath] using h
      simp only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_left hk]
      simpa [shiftedCodePath] using
        (codeSndFirstHit_eq_boundaryHitTime (shiftedCodePath W 0) hcode
          (by omega : 1 ≤ k))
    · have hcode : BoundaryHitWitnesses
          (fun i => shiftedCodePath W 0 (i + 1)) := by
        simpa [shiftedCodePath] using h
      simp only [boundaryCodeStoppingTime, ite_eq_right hk0, ite_eq_right hk]
      simpa [shiftedCodePath] using
        (codeFstFirstHit_eq_boundaryHitTime (shiftedCodePath W 0) hcode
          (by omega : k ≤ -1))

/-- Helper toward Lemma 5.5. Before its stopping frontier, the prefix code
is the raw zero-based KMSW stream. -/
theorem lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    {i : ℕ} (hi : i < boundaryHitTime (shiftedStream W 0) h k) :
    boundaryPrefixCode k W i = shiftedStream W 0 i := by
  rw [boundaryPrefixCode, codePastVector,
    lPlusBoundaryCodeStoppingTime_eq_boundaryHitTime W h k]
  have hcut : (i : ℕ∞) < (boundaryHitTime (shiftedStream W 0) h k : ℕ∞) := by
    exact_mod_cast hi
  simp [hcut, shiftedCodePath]

/-- Helper toward Lemma 5.5. Equal stopped-prefix observations determine the
first coordinate-hit time, including both signs of the boundary index. -/
theorem lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq
    (W W' : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0)) (k : ℤ)
    (hc : boundaryPrefixCode k W = boundaryPrefixCode k W') :
    boundaryHitTime (shiftedStream W 0) h k =
      boundaryHitTime (shiftedStream W' 0) h' k := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryHitTime]
  · by_cases hkpos : 0 < k
    · let w := shiftedStream W 0
      let w' := shiftedStream W' 0
      let t := boundaryHitTime w h k
      let t' := boundaryHitTime w' h' k
      have hfind : t = Nat.find (h.rightHit k (by omega)) := by
        dsimp only [t]
        unfold boundaryHitTime
        simp only [dite_eq_right (by omega), dite_eq_left hkpos]
      have hfind' : t' = Nat.find (h'.rightHit k (by omega)) := by
        dsimp only [t']
        unfold boundaryHitTime
        simp only [dite_eq_right (by omega), dite_eq_left hkpos]
      have hle : t ≤ t' := by
        by_contra hn
        have hlt : t' < t := Nat.lt_of_not_ge hn
        have hprefix : ∀ i < t', w i = w' i := by
          intro i hi
          have heq := congrFun hc i
          rw [lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k
                (Nat.lt_trans hi hlt),
            lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k hi] at heq
          exact heq
        have hR := R_congr hprefix
        have hhit : R w t' = -k :=
          hR.trans (boundaryHitTime_right_spec w' h' (by omega))
        have hmin : t ≤ t' := by
          rw [hfind]
          exact Nat.find_min' (h.rightHit k (by omega)) hhit
        omega
      have hge : t' ≤ t := by
        by_contra hn
        have hlt : t < t' := Nat.lt_of_not_ge hn
        have hprefix : ∀ i < t, w i = w' i := by
          intro i hi
          have heq := congrFun hc i
          rw [lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi,
            lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k
              (Nat.lt_trans hi hlt)] at heq
          exact heq
        have hR := R_congr hprefix
        have hhit : R w' t = -k :=
          hR.symm.trans (boundaryHitTime_right_spec w h (by omega))
        have hmin : t' ≤ t := by
          rw [hfind']
          exact Nat.find_min' (h'.rightHit k (by omega)) hhit
        omega
      exact Nat.le_antisymm hle hge
    · have hkneg : k ≤ -1 := by omega
      let w := shiftedStream W 0
      let w' := shiftedStream W' 0
      let t := boundaryHitTime w h k
      let t' := boundaryHitTime w' h' k
      have hfind : t = Nat.find (h.leftHit k hkneg) := by
        simp [t, boundaryHitTime, hk0, hkpos]
      have hfind' : t' = Nat.find (h'.leftHit k hkneg) := by
        simp [t', boundaryHitTime, hk0, hkpos]
      have hle : t ≤ t' := by
        by_contra hn
        have hlt : t' < t := Nat.lt_of_not_ge hn
        have hprefix : ∀ i < t', w i = w' i := by
          intro i hi
          have heq := congrFun hc i
          rw [lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k
                (Nat.lt_trans hi hlt),
            lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k hi] at heq
          exact heq
        have hL := L_congr hprefix
        have hhit : L w t' = k :=
          hL.trans (boundaryHitTime_left_spec w' h' hkneg)
        have hmin : t ≤ t' := by
          rw [hfind]
          exact Nat.find_min' (h.leftHit k hkneg) hhit
        omega
      have hge : t' ≤ t := by
        by_contra hn
        have hlt : t < t' := Nat.lt_of_not_ge hn
        have hprefix : ∀ i < t, w i = w' i := by
          intro i hi
          have heq := congrFun hc i
          rw [lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi,
            lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k
              (Nat.lt_trans hi hlt)] at heq
          exact heq
        have hL := L_congr hprefix
        have hhit : L w' t = k :=
          hL.symm.trans (boundaryHitTime_left_spec w h hkneg)
        have hmin : t' ≤ t := by
          rw [hfind']
          exact Nat.find_min' (h'.leftHit k hkneg) hhit
        omega
      exact Nat.le_antisymm hle hge

/-- Helper toward Lemma 5.5. Equal prefix codes give literally equal KMSW
data at the preceding stopped stage. -/
theorem lPlusBoundaryPrefixStage_eq_of_code_eq
    (W W' : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0)) (k : ℤ)
    (hc : boundaryPrefixCode k W = boundaryPrefixCode k W') :
    kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k - 1) =
      kmswStage (shiftedStream W' 0)
        (boundaryHitTime (shiftedStream W' 0) h' k - 1) := by
  have ht := lPlusBoundaryHitTime_eq_of_boundaryPrefixCode_eq W W' h h' k hc
  rw [ht]
  apply kmswStage_congr
  intro i hi
  have hi₁ : i < boundaryHitTime (shiftedStream W 0) h k := by omega
  have hi₂ : i < boundaryHitTime (shiftedStream W' 0) h' k := by omega
  have heq := congrFun hc i
  rw [lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W h k hi₁,
    lPlusBoundaryPrefixCode_eq_shiftedStream_of_lt W' h' k hi₂] at heq
  exact heq

/-- Helper toward Lemma 5.5. Equal prefix codes give the same deleted
stopped-prefix edge carrier, including the empty carrier at zero. -/
theorem lPlusBoundaryPrefixMinusEdges_eq_of_code_eq
    (W W' : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0)) (k : ℤ)
    (hk : 0 ≤ k)
    (hc : boundaryPrefixCode k W = boundaryPrefixCode k W') :
    boundaryGluingPrefixMinusEdges W h k =
      boundaryGluingPrefixMinusEdges W' h' k := by
  by_cases hkpos : 0 < k
  · rw [lPlusPrefixMinusEdges_eq_previousStage hkpos,
      lPlusPrefixMinusEdges_eq_previousStage hkpos,
      lPlusBoundaryPrefixStage_eq_of_code_eq W W' h h' k hc]
  · have hkzero : k = 0 := by omega
    subst k
    simp only [boundaryGluingPrefixMinusEdges_zero]

/-- Helper toward Lemma 5.5. Equal prefix codes give the same deleted
stopped-prefix vertex carrier, including its attachment root at zero. -/
theorem lPlusBoundaryPrefixMinusVertices_eq_of_code_eq
    (W W' : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (h' : BoundaryHitWitnesses (shiftedStream W' 0)) (k : ℤ)
    (hk : 0 ≤ k)
    (hc : boundaryPrefixCode k W = boundaryPrefixCode k W') :
    boundaryGluingPrefixMinusVertices W h k =
      boundaryGluingPrefixMinusVertices W' h' k := by
  by_cases hkpos : 0 < k
  · rw [boundaryGluingPrefixMinusVertices_of_pos hkpos,
      boundaryGluingPrefixMinusVertices_of_pos hkpos,
      lPlusBoundaryPrefixStage_eq_of_code_eq W W' h h' k hc]
  · have hkzero : k = 0 := by omega
    subst k
    simp only [boundaryGluingPrefixMinusVertices_zero]

/-- Helper toward Lemma 5.5. The stopped-prefix stage for two aligned
witnesses with equal presentation codes is literally the same state. -/
theorem lPlusSourceWitnessAligned_prefixStage_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    kmswStage (shiftedStream s.W 0)
        (boundaryHitTime (shiftedStream s.W 0) s.h k - 1) =
      kmswStage (shiftedStream s'.W 0)
        (boundaryHitTime (shiftedStream s'.W 0) s'.h k - 1) := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  exact lPlusBoundaryPrefixStage_eq_of_code_eq s.W s'.W s.h s'.h k hc

/-- Helper toward Lemma 5.5. Equal presentation codes give the same
deleted-prefix geometric edge carrier. -/
theorem lPlusSourceWitnessAligned_prefixEdges_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    boundaryGluingPrefixMinusEdges s.W s.h k =
      boundaryGluingPrefixMinusEdges s'.W s'.h k := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  exact lPlusBoundaryPrefixMinusEdges_eq_of_code_eq
    s.W s'.W s.h s'.h k hk hc

/-- Helper toward Lemma 5.5. Equal presentation codes give the same
deleted-prefix geometric vertex carrier. -/
theorem lPlusSourceWitnessAligned_prefixVertices_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hk : 0 ≤ k) (hr : r.code = r'.code) :
    boundaryGluingPrefixMinusVertices s.W s.h k =
      boundaryGluingPrefixMinusVertices s'.W s'.h k := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).1
  exact lPlusBoundaryPrefixMinusVertices_eq_of_code_eq
    s.W s'.W s.h s'.h k hk hc

/-- Helper toward Lemma 5.5. The primed code respects equality of its raw
future stream, with proof arguments identified by proof irrelevance. -/
private theorem lPlusPrimedCode_congr {u v : ℕ → Fin 3} (huv : u = v)
    (h : HasFlowLineHits u) (h' : HasFlowLineHits v) :
    primedCode (primedSimInput u) h = primedCode (primedSimInput v) h' := by
  cases huv
  have hh : h = h' := Subsingleton.elim _ _
  rw [hh]

/-- Helper toward Lemma 5.5. On the actual future stream, the primed-code
observation is the code used to build the primed KMSW block. -/
private theorem lPlusHatLawPrimedCodes_eq_futurePrimedCode
    (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) :
    hatLawPrimedCodes (boundaryFutureCode k W) =
      primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ := by
  have htail : (fun i => boundaryFutureCode k W (i + 1)) =
      boundaryGluingFutureStream W h k := by
    change (fun i => boundaryFutureCode k W (i + 1)) =
      (fun i => shiftedStream W 0
        (boundaryHitTime (shiftedStream W 0) h k + i))
    exact boundaryFutureCode_tail W h k
  have hhit : HasFlowLineHits (fun i => boundaryFutureCode k W (i + 1)) :=
    htail.symm ▸ hτ
  unfold hatLawPrimedCodes
  rw [dite_eq_left hhit]
  exact lPlusPrimedCode_congr htail hhit hτ

/-- Helper toward Lemma 5.5. Equal primed-code observations give equal
primed KMSW input streams. -/
theorem lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ =
      primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ := by
  have hc := (lPlusSourceWitness_blockCodes_eq_of_presentation_codes_eq
    x k r r' s.toLPlusSidePresentationSourceWitness
      s'.toLPlusSidePresentationSourceWitness hr).2.2
  calc
    _ = hatLawPrimedCodes (boundaryFutureCode k s.W) :=
      (lPlusHatLawPrimedCodes_eq_futurePrimedCode s.W s.h k s.hτ).symm
    _ = hatLawPrimedCodes (boundaryFutureCode k s'.W) := hc
    _ = _ := lPlusHatLawPrimedCodes_eq_futurePrimedCode s'.W s'.h k s'.hτ

/-- Helper toward Lemma 5.5. The primed local KMSW stage is determined by
the primed code prefix. -/
theorem lPlusMissingRootStage_congr {u v : ℕ → Fin 3} {m : ℕ}
    (hc : ∀ i < m, u i = v i) :
    kmswMissingRootStage u m = kmswMissingRootStage v m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change kmswStep (kmswMissingRootStage u m) (u m) =
        kmswStep (kmswMissingRootStage v m) (v m)
      rw [ih (fun i hi => hc i (by omega)), hc m (by omega)]

/-- Helper toward Lemma 5.5. Equal presentation codes give the same primed
local KMSW state at every finite stage. -/
theorem lPlusSourceWitnessAligned_primedStage_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r') (m : ℕ)
    (hr : r.code = r'.code) :
    kmswMissingRootStage
        (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ) m =
      kmswMissingRootStage
        (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ) m := by
  apply lPlusMissingRootStage_congr
  intro i hi
  exact congrFun
    (lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
      x k r r' s s' hr) i

/-- Helper toward Lemma 5.5. The limiting rotation is determined by its
primed code stream and finite-incidence proof. -/
private theorem lPlusKmswInfRot_congr {u v : ℕ → Fin 3} (huv : u = v)
    (hfin : KMSWFiniteIncidence u) (hfin' : KMSWFiniteIncidence v) :
    kmswInfRot u hfin = kmswInfRot v hfin' := by
  cases huv
  have hp : hfin = hfin' := Subsingleton.elim _ _
  rw [hp]

/-- Helper toward Lemma 5.5. Equal presentation codes give the same
primed limiting rotation on the local primed darts. -/
theorem lPlusSourceWitnessAligned_primedRotation_eq_of_presentation_codes_eq
    (x : XDP) (k : ℤ) (r r' : LPlusSidePresentation x)
    (s : LPlusSourceWitnessAligned x k r)
    (s' : LPlusSourceWitnessAligned x k r')
    (hr : r.code = r'.code) :
    kmswInfRot
        (primedCode (primedSimInput (boundaryGluingFutureStream s.W s.h k)) s.hτ)
        (primedCode_finiteIncidence (boundaryGluingFutureStream s.W s.h k)
          s.hτ s.hfin) =
      kmswInfRot
        (primedCode (primedSimInput (boundaryGluingFutureStream s'.W s'.h k)) s'.hτ)
        (primedCode_finiteIncidence (boundaryGluingFutureStream s'.W s'.h k)
          s'.hτ s'.hfin) :=
  lPlusKmswInfRot_congr
    (lPlusSourceWitnessAligned_primedCode_eq_of_presentation_codes_eq
      x k r r' s s' hr) _ _































































end DirectedDistances.PaperProofs.Section5

