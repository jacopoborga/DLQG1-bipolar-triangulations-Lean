/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarInverseWalkIso
public import DirectedDistances.KMSW.KMSWInverseCode

/-! # Inverse walk and code classes

Helpers toward the inverse direction of `thm-kmsw` -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

variable {ℓ r n : ℕ}

/-- Helper toward the `thm-kmsw` inverse
result. The inverse walk code descends to unrooted isomorphism classes. -/
@[expose] noncomputable def kmswClassInverseWalkClass :
    KMSWMapIsoClass ℓ r n → KMSWWalkClass ℓ r n :=
  KMSWMapIsoClass.lift kmswRepInverseWalkClass (by
    intro R R' h
    rcases h with ⟨I⟩
    have hwalk := inverseIso_kmswRepInverseWalk R R' I
    apply Subtype.ext
    change codesOfWalk (kmswRepInverseWalk R) =
      codesOfWalk (kmswRepInverseWalk R')
    exact congrArg codesOfWalk hwalk.symm)

/-- The inverse walk class lift agrees on representatives. Helper toward the -/
theorem kmswClassInverseWalkClass_mk (R : KMSWMapRep ℓ r n) :
    kmswClassInverseWalkClass (KMSWMapIsoClass.mk R) =
      kmswRepInverseWalkClass R := by
  exact KMSWMapIsoClass.lift_mk _ _ _

/-- The representative inverse walk class carries exactly its inverse code. -/
theorem kmswRepInverseWalkClass_val (R : KMSWMapRep ℓ r n) :
    (kmswRepInverseWalkClass R).val = kmswRepInverseCode R := rfl

/-- Integrating the code of a class inverse walk recovers its class inverse
walk at every valid time. Helper toward the `thm-kmsw` inverse -/
theorem integrateCodes_kmswClassInverseWalkClass
    (q : KMSWMapIsoClass ℓ r n) (k : ℕ) (hk : k < n) :
    integrateCodes (codeExtend (kmswClassInverseWalkClass q)) k =
      kmswClassInverseWalk q ⟨k, hk⟩ := by
  refine KMSWMapIsoClass.ind
    (motive := fun q =>
      integrateCodes (codeExtend (kmswClassInverseWalkClass q)) k =
        kmswClassInverseWalk q ⟨k, hk⟩) ?_ q
  intro R
  rw [kmswClassInverseWalkClass_mk, kmswClassInverseWalk_mk]
  change integrateCodes (finiteCodeExtend
    (kmswRepInverseWalkClass R).val) k = _
  rw [kmswRepInverseWalkClass_val]
  exact integrateCodes_kmswRepInverseCode R k hk

end DirectedDistances.KMSW
