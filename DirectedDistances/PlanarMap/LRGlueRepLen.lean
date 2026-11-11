/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathGlueRep
public import DirectedDistances.PlanarMap.PlanarPathGlueSeamGeometric
public import DirectedDistances.PlanarMap.LexLeftmostBaseIso
public import DirectedDistances.PlanarMap.LRCutRep

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

 

public section
namespace DirectedDistances.PlanarMap

variable {DL DR : Type*} [Fintype DL] [DecidableEq DL]
  [Fintype DR] [DecidableEq DR] {ℓ s r : ℕ}

private noncomputable def glueRepBaseIso {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b) :
    BipolarBoundaryBaseIso (glueBase A.B Bm.B) (glueRep A Bm).B :=
  (glueBase A.B Bm.B).transportIso
    (Fintype.equivFin (GlueDart A.B Bm.B))



theorem glueRep_len {x : XDP} {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm) :
    xdpLengthBase (glueRep A Bm).B x = s := by
  change IsUniqueXDPGeodesicBase A.B x A.B.rightPath at hA
  change IsXDPGeodesicBase Bm.B x Bm.B.leftPath at hB
  let I := glueRepBaseIso A Bm
  cases x with
  | ldp =>
      change ldpLengthBase (glueRep A Bm).B = s
      rw [ldpLengthBase_eq_of_baseIso I]
      exact glue_xdpLength A.B Bm.B .ldp hA hB
  | sdp =>
      change sdpLengthBase (glueRep A Bm).B = s
      rw [sdpLengthBase_eq_of_baseIso I]
      exact glue_xdpLength A.B Bm.B .sdp hA hB



@[expose] noncomputable def glueRepSeam {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b) :
    SimpleDirectedDartPath (glueRep A Bm).B.map
      (glueRep A Bm).B.source (glueRep A Bm).B.sink s :=
  let I : BipolarBoundaryBaseIso (glueBase A.B Bm.B) (glueRep A Bm).B :=
    (glueBase A.B Bm.B).transportIso
      (Fintype.equivFin (GlueDart A.B Bm.B))
  I.mapPath (glueSeamPathBase A.B Bm.B)



theorem glueRepSeam_isLexLeftmost {x : XDP} {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm) :
    IsLexLeftmostXDPGeodesic (glueRep A Bm).B x (glueRepSeam A Bm) := by
  change IsUniqueXDPGeodesicBase A.B x A.B.rightPath at hA
  change IsXDPGeodesicBase Bm.B x Bm.B.leftPath at hB
  let I : BipolarBoundaryBaseIso (glueBase A.B Bm.B) (glueRep A Bm).B :=
    (glueBase A.B Bm.B).transportIso
      (Fintype.equivFin (GlueDart A.B Bm.B))
  exact (isLexLeftmostXDPGeodesic_mapPath_iff I x
      (glueSeamPathBase A.B Bm.B)).mpr
    (glueSeamPathBase_isLexLeftmost A.B Bm.B x hA hB)



theorem selectedGeodesicOfLen_glueRep_darts {x : XDP} {a b : ℕ}
    (A : KMSWMapRep ℓ s a) (Bm : KMSWMapRep s r b)
    (hA : IsMLRepresentative x A) (hB : IsMRRepresentative x Bm) :
    (selectedGeodesicOfLen (glueRep A Bm).B x (glueRep_len A Bm hA hB)).darts =
      (glueRepSeam A Bm).darts := by
  exact dartLists_eq_of_isLexLeftmostXDPGeodesic (glueRep A Bm).B x
    (selectedGeodesicOfLen (glueRep A Bm).B x (glueRep_len A Bm hA hB))
    (glueRepSeam A Bm)
    (selectedGeodesicOfLen_isLexLeftmost (glueRep A Bm).B x
      (glueRep_len A Bm hA hB))
    (glueRepSeam_isLexLeftmost A Bm hA hB)

end DirectedDistances.PlanarMap
