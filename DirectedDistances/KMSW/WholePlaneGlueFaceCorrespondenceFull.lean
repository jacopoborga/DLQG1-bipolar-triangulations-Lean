/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondence
public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsIff






public section
namespace DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open WholePlaneGlueFaceCorrespondence WholePlaneGlueFaceOrbits WholePlaneGlueSeamFaces

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0) (monotone_family_all w0)
local notation "Pp" => monotoneFamilyDrawing wp (past_finiteIncidence W H)
  (monotone_family_all wp)
local notation "T" => PastDrawingTransfer.transfer w0 wp h0 hp
  ((And.left H) 0) (past_finiteIncidence W H)
local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h0 hp H
local notation "f" => wholePlaneFaceSucc W H

/-- Supporting result toward Q-M0-repr: every bounded past face is realized
in the glued drawing with precisely its transferred component set. -/
theorem past_bounded_face_exists (Fp : (Pp).Face) (hFp : ¬ (Pp).IsUnbounded Fp) :
    ∃ F : (G).Face, F.val = T '' Fp.val := by
  obtain ⟨z, _, hz, hc⟩ :=
    WholePlanePastGlueFacesLower.glued_component_of_past_boundedFace W h0 hp H Fp hFp
  have hzG : z ∉ (G).image := by
    rw [WholePlanePastGlueDrawing.glueDrawing_image]
    exact hz
  refine ⟨⟨connectedComponentIn (G).imageᶜ z, z, hzG, rfl⟩, ?_⟩
  change connectedComponentIn (G).imageᶜ z = T '' Fp.val
  rw [WholePlanePastGlueDrawing.glueDrawing_image]
  exact hc

/-- Supporting result toward Q-M0-repr: every geometric glued dart borders
a realized face on its left, including both sides of every seam edge. -/
theorem dart_borders_exists (D : WholePlaneDart W) :
    ∃ F : (G).Face, (G).dartBorders D F := by
  rcases wholePlaneFaceSucc_runZero_or_past W H (past_finiteIncidence W H) hp h0 D with
    ⟨d, rfl, ⟨j, hd⟩, _⟩ | ⟨d, rfl, ⟨j, hd⟩, _⟩
  · exact glueSeamFaces_runZero_creation_dartBorders W h0 hp H d j hd
  · obtain ⟨F, hF⟩ := past_bounded_face_exists W h0 hp H
      (capFace wp (past_finiteIncidence W H) j)
      (capFace_isBounded_face wp (past_finiteIncidence W H) j)
    exact ⟨F, (past_dartBorders_iff W h0 hp H d _ F hF).mpr
      ((cap_border_iff wp (past_finiteIncidence W H) j d).mpr hd)⟩

/-- Supporting result toward Q-M0-repr: each glued dart borders exactly one
realized left face. -/
theorem dart_borders_unique (D : WholePlaneDart W) :
    ∃! F : (G).Face, (G).dartBorders D F := by
  obtain ⟨F, hF⟩ := dart_borders_exists W h0 hp H D
  exact ⟨F, hF, fun F' hF' =>
    glueSeamFaces_dartBorders_unique W h0 hp H D F' F hF' hF⟩

/-- Supporting result toward Q-M0-repr: every realized glued face has a
bordering geometric dart. -/
theorem face_bordered (F : (G).Face) :
    ∃ D : WholePlaneDart W, (G).dartBorders D F := by
  rcases WholePlanePastGlueDrawing.glueDrawing_faces W h0 hp H F with
    ⟨F0, _, hF⟩ | ⟨Fp, _, hF⟩
  · obtain ⟨d, hd⟩ := DirectedDistances.KMSW.face_bordered w0 (H.1 0) h0 F0
    refine ⟨wholePlaneDartι W 0 d, ?_⟩
    exact (PLDrawing.dartBorders_congr P0 G F0 F
      (WholePlanePastGlueM0Restriction.restrict_arc W h0 hp H d) hF).mpr hd
  · obtain ⟨d, hd⟩ := DirectedDistances.KMSW.face_bordered
      wp (past_finiteIncidence W H) hp Fp
    exact ⟨kmswPastDart W d, (past_dartBorders_iff W h0 hp H d Fp F hF).mpr hd⟩

/-- The realized left face of a glued dart, selected only after existence
and uniqueness have been proved. Supporting definition toward Q-M0-repr. -/
noncomputable def dartFace (D : WholePlaneDart W) : (G).Face :=
  (dart_borders_exists W h0 hp H D).choose

/-- Complete characterization of the selected left face by dart bordering. -/
theorem dartFace_eq_iff (D : WholePlaneDart W) (F : (G).Face) :
    dartFace W h0 hp H D = F ↔ (G).dartBorders D F := by
  have hd : (G).dartBorders D (dartFace W h0 hp H D) :=
    (dart_borders_exists W h0 hp H D).choose_spec
  exact ⟨fun he => he ▸ hd, fun hF =>
    glueSeamFaces_dartBorders_unique W h0 hp H D _ F hd hF⟩

/-- Supporting result toward Q-M0-repr: the dart-to-face map reaches every
realized face of the glued drawing. -/
theorem dartFace_surjective : Function.Surjective (dartFace W h0 hp H) := by
  intro F
  obtain ⟨D, hD⟩ := face_bordered W h0 hp H F
  exact ⟨D, (dartFace_eq_iff W h0 hp H D F).mpr hD⟩

/-- A source face remains the bordered face throughout its successor orbit. -/
private theorem source_border_of_sameCycle (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (hit : BoundaryHitWitnesses w)
    (d e : ℕ × Bool)
    (F : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F)
    (hde : (kmswInfFaceSucc w hfin).SameCycle d e) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders e F := by
  obtain ⟨F', hd', he'⟩ := (faceOrbit_iff_common_face w hfin hit d e).mp hde
  have heq := dart_border_face_unique w hfin d F' F hd' hd
  exact heq ▸ he'

/-- Every bordered glued face has a bounded one-sided representative, and
the dart has a representative bordering that same source face. -/
theorem bordered_face_cases (D : WholePlaneDart W) (F : (G).Face)
    (hD : (G).dartBorders D F) :
    (∃ (d : ℕ × Bool) (F0 : (P0).Face), D = wholePlaneDartι W 0 d ∧
      ¬ (P0).IsUnbounded F0 ∧ F.val = F0.val ∧ (P0).dartBorders d F0) ∨
    (∃ (d : ℕ × Bool) (Fp : (Pp).Face), D = kmswPastDart W d ∧
      ¬ (Pp).IsUnbounded Fp ∧ F.val = T '' Fp.val ∧ (Pp).dartBorders d Fp) := by
  rcases wholePlaneFaceSucc_runZero_or_past W H (past_finiteIncidence W H) hp h0 D with
    ⟨d, rfl, ⟨j, hd⟩, _⟩ | ⟨d, rfl, ⟨j, hd⟩, _⟩
  · let F0 := capFace w0 (H.1 0) j
    have hF0 : ¬ (P0).IsUnbounded F0 := capFace_isBounded_face w0 (H.1 0) j
    have hd0 : (P0).dartBorders d F0 := (cap_border_iff w0 (H.1 0) j d).mpr hd
    obtain ⟨F', hF', hb⟩ := glueFaceOrbits_runZero_dartBorders W h0 hp H d F0 hF0
    have heq := glueSeamFaces_dartBorders_unique W h0 hp H _ F F' hD (hb.mpr hd0)
    exact Or.inl ⟨d, F0, rfl, hF0, heq ▸ hF', hd0⟩
  · let Fp := capFace wp (past_finiteIncidence W H) j
    have hFp : ¬ (Pp).IsUnbounded Fp :=
      capFace_isBounded_face wp (past_finiteIncidence W H) j
    have hdp : (Pp).dartBorders d Fp :=
      (cap_border_iff wp (past_finiteIncidence W H) j d).mpr hd
    obtain ⟨F', hF'⟩ := past_bounded_face_exists W h0 hp H Fp hFp
    have hd' := (past_dartBorders_iff W h0 hp H d Fp F' hF').mpr hdp
    have heq := glueSeamFaces_dartBorders_unique W h0 hp H _ F F' hD hd'
    exact Or.inr ⟨d, Fp, rfl, hFp, heq ▸ hF', hdp⟩

/-- Face succession preserves the realized left face of every glued dart. -/
theorem faceSucc_dartBorders (D : WholePlaneDart W) (F : (G).Face)
    (hD : (G).dartBorders D F) : (G).dartBorders (f D) F := by
  rcases bordered_face_cases W h0 hp H D F hD with
    ⟨d, F0, rfl, hF0, hval, hd⟩ | ⟨d, Fp, rfl, hFp, hval, hd⟩
  · obtain ⟨j, rfl⟩ := (boundedFace_iff_creation_orbit w0 (H.1 0) h0 F0).mp hF0
    have ht := (cap_border_iff w0 (H.1 0) j d).mp hd
    rw [wholePlaneFaceSucc_run_of_triangle W H 0 d ⟨j, ht⟩]
    apply (PLDrawing.dartBorders_congr P0 G _ F
      (WholePlanePastGlueM0Restriction.restrict_arc W h0 hp H _) hval).mpr
    exact source_border_of_sameCycle w0 (H.1 0) h0 d _ _ hd
      Equiv.Perm.SameCycle.rfl.apply_right
  · obtain ⟨j, rfl⟩ :=
      (boundedFace_iff_creation_orbit wp (past_finiteIncidence W H) hp Fp).mp hFp
    have ht := (cap_border_iff wp (past_finiteIncidence W H) j d).mp hd
    rw [kmswPastDart_faceSucc_of_triangle W H (past_finiteIncidence W H) d ⟨j, ht⟩]
    apply (past_dartBorders_iff W h0 hp H _ _ F hval).mpr
    exact source_border_of_sameCycle wp (past_finiteIncidence W H) hp d _ _ hd
      Equiv.Perm.SameCycle.rfl.apply_right

/-- The selected realized face is invariant under face succession. -/
theorem dartFace_faceSucc (D : WholePlaneDart W) :
    dartFace W h0 hp H (f D) = dartFace W h0 hp H D := by
  apply (dartFace_eq_iff W h0 hp H _ _).mpr
  exact faceSucc_dartBorders W h0 hp H D _
    ((dartFace_eq_iff W h0 hp H D _).mp rfl)

/-- Darts in a common combinatorial face orbit have the same realized face. -/
theorem dartFace_eq_of_sameCycle (D E : WholePlaneDart W) (hDE : (f).SameCycle D E) :
    dartFace W h0 hp H D = dartFace W h0 hp H E := by
  obtain ⟨n, rfl⟩ := hDE
  have hinv (X : WholePlaneDart W) :
      dartFace W h0 hp H ((f).symm X) = dartFace W h0 hp H X := by
    simpa only [Equiv.apply_symm_apply] using
      (dartFace_faceSucc W h0 hp H ((f).symm X)).symm
  symm
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih =>
    rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply,
      dartFace_faceSucc, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega, zpow_add, zpow_neg_one,
      Equiv.Perm.mul_apply]
    exact (hinv _).trans ih

/-- Combinatorial face orbits of the whole-plane map, including all geometric darts. -/
abbrev FaceOrbit := Quotient (Equiv.Perm.SameCycle.setoid f)

/-- Send a face-successor orbit to its uniquely determined realized left face. -/
noncomputable def orbitFace : FaceOrbit W H → (G).Face :=
  Quotient.lift (dartFace W h0 hp H) (dartFace_eq_of_sameCycle W h0 hp H)

/-- Both directions of dart-border compatibility for the orbit-to-face map. -/
theorem orbitFace_eq_iff (D : WholePlaneDart W) (F : (G).Face) :
    orbitFace W h0 hp H (Quotient.mk _ D) = F ↔ (G).dartBorders D F :=
  dartFace_eq_iff W h0 hp H D F

/-- Every realized face is the image of a combinatorial face orbit. -/
theorem orbitFace_surjective : Function.Surjective (orbitFace W h0 hp H) := by
  intro F
  obtain ⟨D, hD⟩ := dartFace_surjective W h0 hp H F
  exact ⟨Quotient.mk _ D, hD⟩

/-- Transport a cycle through a map commuting with succession on that cycle. -/
private theorem sameCycle_map {A B : Type*} (s : Equiv.Perm A) (t : Equiv.Perm B)
    (ι : A → B) (a b : A) (hab : s.SameCycle a b)
    (hc : ∀ x, s.SameCycle a x → t (ι x) = ι (s x)) :
    t.SameCycle (ι a) (ι b) := by
  obtain ⟨n, rfl⟩ := hab
  induction n using Int.induction_on with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ n ih =>
    rw [add_comm (n : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rw [← hc _ (Equiv.Perm.SameCycle.rfl.zpow_right)]
    exact ih.apply_right
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega, zpow_add, zpow_neg_one,
      Equiv.Perm.mul_apply]
    have heq : ι (s.symm ((s ^ (-(n : ℤ))) a)) =
        t.symm (ι ((s ^ (-(n : ℤ))) a)) := by
      apply t.injective
      rw [hc _ (Equiv.Perm.SameCycle.rfl.zpow_right.symm_apply_right),
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change t.SameCycle (ι a) (ι (s.symm ((s ^ (-(n : ℤ))) a)))
    rw [heq]
    exact ih.symm_apply_right

include h0 in
/-- A bounded run-zero face's darts remain in one whole-plane successor orbit. -/
private theorem runZero_common_face_sameCycle (F0 : (P0).Face)
    (hF0 : ¬ (P0).IsUnbounded F0) (d e : ℕ × Bool)
    (hd : (P0).dartBorders d F0) (he : (P0).dartBorders e F0) :
    (f).SameCycle (wholePlaneDartι W 0 d) (wholePlaneDartι W 0 e) := by
  have hde := (faceOrbit_iff_common_face w0 (H.1 0) h0 d e).mpr ⟨F0, hd, he⟩
  obtain ⟨j, rfl⟩ := (boundedFace_iff_creation_orbit w0 (H.1 0) h0 F0).mp hF0
  apply sameCycle_map (kmswInfFaceSucc w0 (H.1 0)) f (wholePlaneDartι W 0) d e hde
  intro x hx
  have hxb := source_border_of_sameCycle w0 (H.1 0) h0 d x _ hd hx
  exact wholePlaneFaceSucc_run_of_triangle W H 0 x
    ⟨j, (cap_border_iff w0 (H.1 0) j x).mp hxb⟩

include hp in
/-- A bounded past face's darts remain in one whole-plane successor orbit. -/
private theorem past_common_face_sameCycle (Fp : (Pp).Face)
    (hFp : ¬ (Pp).IsUnbounded Fp) (d e : ℕ × Bool)
    (hd : (Pp).dartBorders d Fp) (he : (Pp).dartBorders e Fp) :
    (f).SameCycle (kmswPastDart W d) (kmswPastDart W e) := by
  have hde := (faceOrbit_iff_common_face wp (past_finiteIncidence W H) hp d e).mpr
    ⟨Fp, hd, he⟩
  obtain ⟨j, rfl⟩ :=
    (boundedFace_iff_creation_orbit wp (past_finiteIncidence W H) hp Fp).mp hFp
  apply sameCycle_map (kmswInfFaceSucc wp (past_finiteIncidence W H)) f
    (kmswPastDart W) d e hde
  intro x hx
  have hxb := source_border_of_sameCycle wp (past_finiteIncidence W H) hp d x _ hd hx
  exact kmswPastDart_faceSucc_of_triangle W H (past_finiteIncidence W H) x
    ⟨j, (cap_border_iff wp (past_finiteIncidence W H) j x).mp hxb⟩

/-- A bounded run-zero face cannot coincide with a transferred bounded past face. -/
private theorem runZero_face_ne_past_face (F0 : (P0).Face) (Fp : (Pp).Face)
    (hF0 : ¬ (P0).IsUnbounded F0) (hFp : ¬ (Pp).IsUnbounded Fp) :
    F0.val ≠ T '' Fp.val := by
  intro heq
  obtain ⟨z, hz, hcomp⟩ := F0.property
  have hzF : z ∈ F0.val := hcomp ▸ mem_connectedComponentIn hz
  have hupper := boundedFace_subset_upper w0 h0 (H.1 0) F0 hF0 hzF
  have hlower := PastFacesLower.image_boundedFace_subset_lower W h0 hp H Fp hFp
    (heq ▸ hzF)
  exact (show seamFun w0 h0 (H.1 0) z.re < z.im from hupper).not_gt hlower

/-- Darts border a common realized left face exactly when they belong to
the same combinatorial face-successor orbit. -/
theorem faceOrbit_iff_common_face (D E : WholePlaneDart W) :
    (f).SameCycle D E ↔ ∃ F : (G).Face, (G).dartBorders D F ∧ (G).dartBorders E F := by
  constructor
  · intro hDE
    refine ⟨dartFace W h0 hp H D, (dartFace_eq_iff W h0 hp H D _).mp rfl, ?_⟩
    apply (dartFace_eq_iff W h0 hp H E _).mp
    exact (dartFace_eq_of_sameCycle W h0 hp H D E hDE).symm
  · rintro ⟨F, hD, hE⟩
    rcases bordered_face_cases W h0 hp H D F hD with
      ⟨d, F0, rfl, hF0, hv0, hd⟩ | ⟨d, Fp, rfl, hFp, hvp, hd⟩
    · rcases bordered_face_cases W h0 hp H E F hE with
        ⟨e, F0', rfl, _, hv0', he⟩ | ⟨e, Fp', rfl, hFp', hvp', _⟩
      · have heq : F0 = F0' := Subtype.ext (hv0.symm.trans hv0')
        exact runZero_common_face_sameCycle W h0 H F0 hF0 d e hd (heq.symm ▸ he)
      · exact (runZero_face_ne_past_face W h0 hp H F0 Fp' hF0 hFp'
          (hv0.symm.trans hvp')).elim
    · rcases bordered_face_cases W h0 hp H E F hE with
        ⟨e, F0', rfl, hF0', hv0', _⟩ | ⟨e, Fp', rfl, _, hvp', he⟩
      · exact (runZero_face_ne_past_face W h0 hp H F0' Fp hF0' hFp
          (hv0'.symm.trans hvp)).elim
      · have heq : Fp = Fp' := Subtype.ext
          ((Set.image_injective.mpr (T).injective) (hvp.symm.trans hvp'))
        exact past_common_face_sameCycle W hp H Fp hFp d e hd (heq.symm ▸ he)

/-- Distinct combinatorial face orbits have distinct realized glued faces. -/
theorem orbitFace_injective : Function.Injective (orbitFace W h0 hp H) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro D E heq
  apply Quotient.sound
  apply (faceOrbit_iff_common_face W h0 hp H D E).mpr
  refine ⟨dartFace W h0 hp H D, (dartFace_eq_iff W h0 hp H D _).mp rfl, ?_⟩
  exact (dartFace_eq_iff W h0 hp H E _).mp heq.symm

/-- Face-successor orbits correspond bijectively to realized faces of the
glued drawing, with no additional geometric hypothesis. -/
theorem orbitFace_bijective : Function.Bijective (orbitFace W h0 hp H) :=
  ⟨orbitFace_injective W h0 hp H, orbitFace_surjective W h0 hp H⟩

/-- The equivalence between combinatorial face orbits and realized glued faces. -/
noncomputable def faceOrbitEquiv : FaceOrbit W H ≃ (G).Face :=
  Equiv.ofBijective (orbitFace W h0 hp H) (orbitFace_bijective W h0 hp H)

/-- Both directions of bordering for the face-orbit equivalence. -/
theorem faceOrbitEquiv_eq_iff (D : WholePlaneDart W) (F : (G).Face) :
    faceOrbitEquiv W h0 hp H (Quotient.mk _ D) = F ↔ (G).dartBorders D F :=
  orbitFace_eq_iff W h0 hp H D F

/-- A dart borders the face of an orbit exactly when it represents that orbit. -/
theorem dartBorders_faceOrbitEquiv_iff (D : WholePlaneDart W) (q : FaceOrbit W H) :
    (G).dartBorders D (faceOrbitEquiv W h0 hp H q) ↔ Quotient.mk _ D = q := by
  rw [← faceOrbitEquiv_eq_iff]
  exact (faceOrbitEquiv W h0 hp H).injective.eq_iff

end DirectedDistances.KMSW.WholePlaneGlueFaceCorrespondenceFull
