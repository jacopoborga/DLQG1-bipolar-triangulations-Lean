/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.UIQBOTPlaneRealization
public import DirectedDistances.KMSW.UIBHBOTAssemblyFaceNeighborhood
public import DirectedDistances.PlanarMap.FaceDegreeFiniteSupport

/-! # Geometric face degree toward the UIQBOT realization

The deterministic face-orbit and degree results use the constructed monotone
drawing. The final theorems retain its stage agreement and external-face
characterization together with the new conclusions in one witness package. -/

public section

namespace DirectedDistances.KMSW

open Filter MeasureTheory DirectedDistances.RandomWalk DirectedDistances.PlanarMap

open scoped Classical

/-- Helper toward Definition 4.1: finite incidence makes every natural vertex
the tail of a geometric dart, including darts of missing edges. -/
theorem kmswLimitDartVertex_surjective (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    Function.Surjective (kmswLimitDartVertex w) := by
  intro v
  obtain ⟨e, he | he⟩ := kmsw_vertex_incident_to_limit_edge_of_stage_allocation w v
    (kmsw_vertex_allocated_of_finite_incidence w hfin v)
  · exact ⟨(e, false), he⟩
  · exact ⟨(e, true), he⟩

section Drawing

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
  (kmswInfRot w hfin) (kmswLimitDartVertex w))

/-- Helper toward Definition 4.1: every geometric face of a limit drawing
has a bordering original dart, without a face-coverage premise. -/
theorem kmswDrawing_face_has_bordering_dart (F : (P).Face) :
    ∃ d, (P).dartBorders d F :=
  (P).face_has_bordering_dart (kmswLimitDartVertex_surjective w hfin) (0, false) F

/-- Helper toward Definition 4.1: neighborhood multiplicity in the general
plane carrier equals the count of the two original bordering darts. -/
theorem kmswDrawing_faceMult_eq_bordering_dart_count
    (e : (P).GeometricEdge) (F : (P).toPlaneGraphDrawing.Face) :
    (P).toPlaneGraphDrawing.faceMult e F =
      (if (P).dartBorders e.out ((P).toPlaneGraphDrawingFaceEquiv F) then (1 : ℕ∞) else 0) +
      (if (P).dartBorders (e.out.1, !e.out.2) ((P).toPlaneGraphDrawingFaceEquiv F)
        then (1 : ℕ∞) else 0) :=
  (P).faceMult_eq_bordering_dart_count (kmswLimitDartVertex_surjective w hfin) e F

/-- Helper toward Definition 4.1: the created triangle's three geometric
edges are distinct in the actual dart-flip quotient. -/
theorem kmswDrawing_triangle_geometricEdges_injective (j : TriangleCreationTime w) :
    Function.Injective (fun i : Fin 3 => Quotient.mk (P).edgeSetoid
      (if i.val = 0 then (stageTriangleDartTriple w j).1
       else if i.val = 1 then (stageTriangleDartTriple w j).2.1
       else (stageTriangleDartTriple w j).2.2)) := by
  let t := stageTriangleDartTriple w j
  let raw : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  intro i k hik
  have hrel : raw i = raw k ∨ raw i = ((raw k).1, !(raw k).2) := Quotient.exact hik
  have he : (raw i).1 = (raw k).1 := by
    rcases hrel with h | h
    · exact congrArg Prod.fst h
    · have hh := congrArg (fun a : ℕ × Bool => a.1) h
      exact hh
  have hids := stageTriangleDartTriple_edgeIds_distinct w j
  fin_cases i <;> fin_cases k <;> simp_all [raw, t]

end Drawing

section Orbits

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Helper toward Definition 4.1: a created triangle is exactly one
face-successor orbit of the one-sided limit. -/
theorem kmsw_triangle_sameCycle_iff (j : TriangleCreationTime w) (d : ℕ × Bool) :
    (kmswInfFaceSucc w hfin).SameCycle (stageTriangleDartTriple w j).1 d ↔
      d ∈ stageTriangleDartList w j := by
  let f := kmswInfFaceSucc w hfin
  let t := stageTriangleDartTriple w j
  obtain ⟨h1, h2, h3, _, _, _⟩ := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  change f.SameCycle t.1 d ↔ d ∈ [t.1, t.2.1, t.2.2]
  have h1' : f t.1 = t.2.1 := h1
  have h2' : f t.2.1 = t.2.2 := h2
  have h3' : f t.2.2 = t.1 := h3
  have hi1 : f.symm t.1 = t.2.2 := f.symm_apply_eq.mpr h3.symm
  have hi2 : f.symm t.2.1 = t.1 := f.symm_apply_eq.mpr h1.symm
  have hi3 : f.symm t.2.2 = t.2.1 := f.symm_apply_eq.mpr h2.symm
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [add_comm (k : ℤ) 1, zpow_add, Equiv.Perm.mul_apply, zpow_one]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
      rcases ih with h | h | h
      · exact Or.inr (Or.inl (by rw [h, h1']))
      · exact Or.inr (Or.inr (by rw [h, h2']))
      · exact Or.inl (by rw [h, h3'])
    | pred k ih =>
      rw [show (-(k : ℤ) - 1) = -1 + -(k : ℤ) by omega,
        zpow_add, Equiv.Perm.mul_apply, zpow_neg_one]
      change f.symm ((f ^ (-(k : ℤ))) t.1) ∈ [t.1, t.2.1, t.2.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
      rcases ih with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hi1]))
      · exact Or.inl (by rw [h, hi2])
      · exact Or.inr (Or.inl (by rw [h, hi3]))
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa only [zpow_one] using h1'⟩
    · exact ⟨2, by simpa only [show (2 : ℤ) = 1 + 1 by omega,
        zpow_add, zpow_one, Equiv.Perm.mul_apply, h1'] using h2'⟩

end Orbits

section Realization

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
variable (htrans : Tendsto (L w) atTop atTop)
variable (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)

local notation "P" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Definition 4.1: under the UIQBOT realization hypotheses,
every dart borders exactly one geometric face of the constructed drawing. -/
theorem uiqbotDrawing_dartBorders_existsUnique (d : ℕ × Bool) :
    ∃! F : (P).Face, (P).dartBorders d F := by
  obtain ⟨F, hF⟩ := (P).dartBorders_exists_of_wedge_compl d
    ((P).wedgeIn_compl_image (kmswLimitDartVertex_surjective w hfin) _ _
      ((P).initial_nonzero d))
  exact ⟨F, hF, fun G hG => (P).dartBorders_face_unique d G F hG hF⟩

/-- Helper toward Definition 4.1: the uniquely bordered geometric face of a
dart, chosen after existence and uniqueness have been proved. -/
noncomputable def uiqbotDrawing_faceOfDart (d : ℕ × Bool) : (P).Face :=
  (uiqbotDrawing_dartBorders_existsUnique w hfin d).exists.choose

local notation "faceD" => uiqbotDrawing_faceOfDart w hfin

/-- Helper toward Definition 4.1: complete bordering characterization of the
chosen dart face. -/
theorem uiqbotDrawing_faceOfDart_eq_iff (d : ℕ × Bool) (F : (P).Face) :
    faceD d = F ↔ (P).dartBorders d F := by
  have hd : (P).dartBorders d (faceD d) :=
    (uiqbotDrawing_dartBorders_existsUnique w hfin d).exists.choose_spec
  exact ⟨fun h => h ▸ hd, fun h => (P).dartBorders_face_unique d _ _ hd h⟩

include htrans hR hL0 in
/-- Helper toward Definition 4.1: in the transient one-sided regime, two
darts share a geometric face precisely when they share a face-successor orbit. -/
theorem uiqbotDrawing_sameCycle_iff_common_face (d e : ℕ × Bool) :
    (kmswInfFaceSucc w hfin).SameCycle d e ↔
      ∃ F : (P).Face, (P).dartBorders d F ∧ (P).dartBorders e F := by
  obtain ⟨U, _, _, hU⟩ :=
    DirectedDistances.PaperProofs.Section4.monotoneFamilyDrawing_faceClassification
      w hfin htrans hR hL0
  have hext (a : ℕ × Bool) : (P).dartBorders a U ↔
      (kmswInfFaceSucc w hfin).SameCycle (kmswLeftBoundaryEdge w 0, false) a :=
    (hU a).trans (limitExternalDart_iff_sameCycle w hfin htrans hR hL0 a)
  by_cases hd : limitExternalDart w d
  · have hdU := (hU d).mpr hd
    have hroot := (hext d).mp hdU
    constructor
    · intro hde
      exact ⟨U, hdU, (hext e).mpr (hroot.trans hde)⟩
    · rintro ⟨F, hdF, heF⟩
      have hFU := (P).dartBorders_face_unique d F U hdF hdU
      exact hroot.symm.trans ((hext e).mp (hFU ▸ heF))
  · have hleft : ∀ i, d ≠ (kmswLeftBoundaryEdge w i, false) := by
      intro i hi
      exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inl ⟨i, hi⟩))
    have hright : ∀ i, d ≠ (kmswRightBoundaryEdge w i, true) := by
      intro i hi
      exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inr ⟨i, hi⟩))
    obtain ⟨j, ⟨hdj, _⟩, _⟩ :=
      kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL0 d hleft hright
    have hdc := (cap_border_iff w hfin j d).mpr hdj
    have hcycle := (kmsw_triangle_sameCycle_iff w hfin j d).mpr hdj
    constructor
    · intro hde
      exact ⟨capFace w hfin j, hdc, (cap_border_iff w hfin j e).mpr
        ((kmsw_triangle_sameCycle_iff w hfin j e).mp (hcycle.trans hde))⟩
    · rintro ⟨F, hdF, heF⟩
      have hFc := (P).dartBorders_face_unique d F (capFace w hfin j) hdF hdc
      have hej := (cap_border_iff w hfin j e).mp (hFc ▸ heF)
      exact hcycle.symm.trans ((kmsw_triangle_sameCycle_iff w hfin j e).mpr hej)

include htrans hR hL0 in
/-- Helper toward Definition 4.1: the geometric face of a dart is invariant
under the one-sided face-successor orbit relation. -/
theorem uiqbotDrawing_faceOfDart_sameCycle (d e : ℕ × Bool)
    (h : (kmswInfFaceSucc w hfin).SameCycle d e) : faceD d = faceD e := by
  obtain ⟨F, hd, he⟩ :=
    (uiqbotDrawing_sameCycle_iff_common_face w hfin htrans hR hL0 d e).mp h
  exact ((uiqbotDrawing_faceOfDart_eq_iff w hfin d F).mpr hd).trans
    ((uiqbotDrawing_faceOfDart_eq_iff w hfin e F).mpr he).symm

/-- Helper toward Definition 4.1: the geometric face corresponding to a
face-successor orbit of the UIQBOT constructed drawing. -/
noncomputable def uiqbotDrawing_faceOfOrbit :
    Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin)) → (P).Face :=
  Quotient.lift faceD (fun d e h =>
    uiqbotDrawing_faceOfDart_sameCycle w hfin htrans hR hL0 d e h)

local notation "faceO" => uiqbotDrawing_faceOfOrbit w hfin htrans hR hL0

/-- Helper toward Definition 4.1: orbit-face identification preserves the
exact original dart-bordering relation. -/
theorem uiqbotDrawing_faceOfOrbit_mk_eq_iff (d : ℕ × Bool) (F : (P).Face) :
    faceO (Quotient.mk _ d) = F ↔ (P).dartBorders d F :=
  uiqbotDrawing_faceOfDart_eq_iff w hfin d F

/-- Helper toward Definition 4.1: face-successor orbits and geometric faces
of the one-sided constructed drawing correspond bijectively. -/
theorem uiqbotDrawing_faceOfOrbit_bijective : Function.Bijective faceO := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h d =>
      induction b using Quotient.inductionOn with
      | h e =>
        apply Quotient.sound
        apply (uiqbotDrawing_sameCycle_iff_common_face w hfin htrans hR hL0 d e).mpr
        refine ⟨faceD d, ?_, ?_⟩
        · exact (uiqbotDrawing_faceOfDart_eq_iff w hfin d _).mp rfl
        · exact (uiqbotDrawing_faceOfDart_eq_iff w hfin e _).mp hab.symm
  · intro F
    obtain ⟨d, hd⟩ := kmswDrawing_face_has_bordering_dart w hfin P F
    exact ⟨Quotient.mk _ d,
      (uiqbotDrawing_faceOfOrbit_mk_eq_iff w hfin htrans hR hL0 d F).mpr hd⟩

include htrans hR hL0 in
/-- Helper toward Definition 4.1: every non-external orbit consists of the
three created triangle darts, on three distinct geometric edges. -/
theorem uiqbotDrawing_nonexternal_orbit_triangle
    (q : Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin)))
    (hq : q ≠ Quotient.mk _ (kmswLeftBoundaryEdge w 0, false)) :
    ∃ j : TriangleCreationTime w,
      {d : ℕ × Bool | Quotient.mk _ d = q} = {d | d ∈ stageTriangleDartList w j} ∧
      Function.Injective (fun i : Fin 3 => Quotient.mk (P).edgeSetoid
        (if i.val = 0 then (stageTriangleDartTriple w j).1
         else if i.val = 1 then (stageTriangleDartTriple w j).2.1
         else (stageTriangleDartTriple w j).2.2)) := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  have hd : ¬ limitExternalDart w d := by
    intro h
    exact hq (Quotient.sound
      ((limitExternalDart_iff_sameCycle w hfin htrans hR hL0 d).mp h).symm)
  have hleft : ∀ i, d ≠ (kmswLeftBoundaryEdge w i, false) := by
    intro i hi
    exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inl ⟨i, hi⟩))
  have hright : ∀ i, d ≠ (kmswRightBoundaryEdge w i, true) := by
    intro i hi
    exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inr ⟨i, hi⟩))
  obtain ⟨j, ⟨hdj, _⟩, _⟩ :=
    kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL0 d hleft hright
  have hcycle := (kmsw_triangle_sameCycle_iff w hfin j d).mpr hdj
  refine ⟨j, ?_, kmswDrawing_triangle_geometricEdges_injective w hfin (P) j⟩
  ext e
  change Quotient.mk _ e = Quotient.mk _ d ↔ e ∈ stageTriangleDartList w j
  constructor
  · intro h
    exact (kmsw_triangle_sameCycle_iff w hfin j e).mp
      (hcycle.trans (Quotient.exact h).symm)
  · intro h
    exact Quotient.sound
      (((kmsw_triangle_sameCycle_iff w hfin j e).mpr h).symm.trans hcycle)

/-- Helper toward Definition 4.1: the exceptional boundary orbit is exactly
the orbit corresponding to the unique unbounded geometric face. -/
theorem uiqbotDrawing_faceOfOrbit_isUnbounded_iff
    (q : Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin))) :
    (P).IsUnbounded (faceO q) ↔
      q = Quotient.mk _ (kmswLeftBoundaryEdge w 0, false) := by
  obtain ⟨U, hU, huniq, hborder⟩ :=
    DirectedDistances.PaperProofs.Section4.monotoneFamilyDrawing_faceClassification
      w hfin htrans hR hL0
  have hroot : (P).dartBorders (kmswLeftBoundaryEdge w 0, false) U := by
    apply (hborder _).mpr
    exact (limitExternalDart_iff_sameCycle w hfin htrans hR hL0 _).mpr
      Equiv.Perm.SameCycle.rfl
  have ho : faceO (Quotient.mk _ (kmswLeftBoundaryEdge w 0, false)) = U :=
    (uiqbotDrawing_faceOfOrbit_mk_eq_iff w hfin htrans hR hL0 _ U).mpr hroot
  constructor
  · intro hq
    exact (uiqbotDrawing_faceOfOrbit_bijective w hfin htrans hR hL0).1
      ((huniq _ hq).trans ho.symm)
  · intro hq
    rw [hq, ho]
    exact hU

include htrans hR hL0 in
/-- Helper toward Definition 4.1: every bounded geometric face of the
constructed one-sided drawing has exactly the three oriented creation darts. -/
theorem uiqbotDrawing_bounded_face_triangle (F : (P).Face)
    (hF : ¬ (P).IsUnbounded F) :
    ∃ j : TriangleCreationTime w,
      ∀ d : ℕ × Bool, (P).dartBorders d F ↔ d ∈ stageTriangleDartList w j := by
  obtain ⟨d, hdF⟩ := kmswDrawing_face_has_bordering_dart w hfin (P) F
  obtain ⟨U, hU, _, hborder⟩ :=
    DirectedDistances.PaperProofs.Section4.monotoneFamilyDrawing_faceClassification
      w hfin htrans hR hL0
  have hd : ¬ limitExternalDart w d := by
    intro h
    have hFU := (P).dartBorders_face_unique d F U hdF ((hborder d).mpr h)
    exact hF (hFU ▸ hU)
  have hleft : ∀ i, d ≠ (kmswLeftBoundaryEdge w i, false) := by
    intro i hi
    exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inl ⟨i, hi⟩))
  have hright : ∀ i, d ≠ (kmswRightBoundaryEdge w i, true) := by
    intro i hi
    exact hd ((limitExternalDart_iff w htrans hR hL0 d).mpr (Or.inr ⟨i, hi⟩))
  obtain ⟨j, ⟨hdj, _⟩, _⟩ :=
    kmswInfDart_nonOuterFace_cycle w hfin htrans hR hL0 d hleft hright
  have hFc := (P).dartBorders_face_unique d F (capFace w hfin j) hdF
    ((cap_border_iff w hfin j d).mpr hdj)
  exact ⟨j, fun e => hFc ▸ cap_border_iff w hfin j e⟩

include htrans hR hL0 in
/-- Helper toward Definition 4.1: every bounded face of the constructed
KMSW drawing has degree three in the geometric plane carrier, with its
neighborhood-defined multiplicities. -/
theorem uiqbotDrawing_internal_faceDegree (K : (P).toPlaneGraphDrawing.Face)
    (hK : (P).toPlaneGraphDrawing.IsInternal K) :
    (P).toPlaneGraphDrawing.faceDegree K = 3 := by
  let K' := (P).toPlaneGraphDrawingFaceEquiv K
  have hK' : ¬ (P).IsUnbounded K' := by
    intro h
    exact hK (((P).toPlaneGraphDrawing_isExternal_iff K).mpr h)
  obtain ⟨j, htri⟩ := uiqbotDrawing_bounded_face_triangle w hfin htrans hR hL0 K' hK'
  let t := stageTriangleDartTriple w j
  let darts : Fin 3 → ℕ × Bool := fun i =>
    if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else t.2.2
  let edges : Fin 3 → (P).GeometricEdge := fun i => Quotient.mk (P).edgeSetoid (darts i)
  have hinj : Function.Injective edges :=
    kmswDrawing_triangle_geometricEdges_injective w hfin (P) j
  have hb (a : ℕ × Bool) : (P).dartBorders a K' ↔ ∃ i : Fin 3, darts i = a := by
    rw [htri a]
    change a ∈ [t.1, t.2.1, t.2.2] ↔ _
    constructor
    · intro ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [darts]
  have hmult (e : (P).GeometricEdge) : (P).toPlaneGraphDrawing.faceMult e K =
      if ∃ i : Fin 3, edges i = e then (1 : ℕ∞) else 0 := by
    have hc : (∃ i : Fin 3, edges i = e) ↔
        (P).dartBorders e.out K' ∨ (P).dartBorders (e.out.1, !e.out.2) K' := by
      constructor
      · rintro ⟨i, hie⟩
        have hrel : darts i = e.out ∨ darts i = (e.out.1, !e.out.2) :=
          Quotient.exact (hie.trans (Quotient.out_eq e).symm)
        have hbi := (hb (darts i)).mpr ⟨i, rfl⟩
        rcases hrel with he | he
        · exact Or.inl (he ▸ hbi)
        · exact Or.inr (he ▸ hbi)
      · rintro (he | he)
        · obtain ⟨i, hi⟩ := (hb e.out).mp he
          exact ⟨i, (congrArg (Quotient.mk (P).edgeSetoid) hi).trans (Quotient.out_eq e)⟩
        · obtain ⟨i, hi⟩ := (hb (e.out.1, !e.out.2)).mp he
          exact ⟨i, (congrArg (Quotient.mk (P).edgeSetoid) hi).trans
            (((P).geometricEdge_flip e.out).trans (Quotient.out_eq e))⟩
    have hn : ¬ ((P).dartBorders e.out K' ∧
        (P).dartBorders (e.out.1, !e.out.2) K') := by
      rintro ⟨hl, hr⟩
      obtain ⟨i, hi⟩ := (hb e.out).mp hl
      obtain ⟨k, hk⟩ := (hb (e.out.1, !e.out.2)).mp hr
      have heq : edges i = edges k := by
        change Quotient.mk (P).edgeSetoid (darts i) = Quotient.mk (P).edgeSetoid (darts k)
        rw [hi, hk, (P).geometricEdge_flip]
      have hik := hinj heq
      have hd : e.out = (e.out.1, !e.out.2) := hi.symm.trans (hik ▸ hk)
      exact (P).flip_ne e.out hd.symm
    rw [kmswDrawing_faceMult_eq_bordering_dart_count w hfin (P) e K]
    change (if (P).dartBorders e.out K' then (1 : ℕ∞) else 0) +
      (if (P).dartBorders (e.out.1, !e.out.2) K' then (1 : ℕ∞) else 0) = _
    by_cases hl : (P).dartBorders e.out K'
    · have hr : ¬ (P).dartBorders (e.out.1, !e.out.2) K' := fun hr => hn ⟨hl, hr⟩
      have he := hc.mpr (Or.inl hl)
      simp only [hl, hr, he, ite_true, ite_false, add_zero]
    · by_cases hr : (P).dartBorders (e.out.1, !e.out.2) K'
      · have he := hc.mpr (Or.inr hr)
        simp only [hl, hr, he, ite_true, ite_false, zero_add]
      · have he : ¬ ∃ i : Fin 3, edges i = e := fun he => (hc.mp he).elim hl hr
        simp only [hl, hr, he, ite_false, zero_add]
  exact (P).toPlaneGraphDrawing.faceDegree_eq_three_of_injective K edges hinj hmult

include htrans hR hL0 in
/-- Helper toward Definition 4.1: stated directly on the complementary
components of the PL drawing, every bounded face has geometric degree three. -/
theorem uiqbotDrawing_bounded_faceDegree (F : (P).Face)
    (hF : ¬ (P).IsUnbounded F) :
    (P).toPlaneGraphDrawing.faceDegree ((P).toPlaneGraphDrawingFaceEquiv.symm F) = 3 := by
  apply uiqbotDrawing_internal_faceDegree w hfin htrans hR hL0
  intro hext
  apply hF
  have hu := ((P).toPlaneGraphDrawing_isExternal_iff _).mp hext
  simpa only [Equiv.apply_symm_apply] using hu

end Realization

/-- Helper toward Definition 4.1: one joint choice of finite-stage drawings,
limit drawing, external face and orbit-face identification satisfies the
constructed realization and the geometric triangular-face clause of
Definition 1.1. All witnesses refer to the same drawing. -/
theorem kmswConstructedPlaneRealization_with_faceDegree (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    ∃ Q : ∀ n, StageDrawing w n,
      (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
      ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
          (kmswInfRot w hfin) (kmswLimitDartVertex w),
        (∀ n v, P.pos v.val = (Q n).pos v) ∧
        (∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d) ∧
        ∃ U : P.Face,
          P.IsUnbounded U ∧
          (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
          (∀ d, P.dartBorders d U ↔ limitExternalDart w d) ∧
          ∃ faceOfOrbit :
              Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin)) → P.Face,
            Function.Bijective faceOfOrbit ∧
            (∀ (d : ℕ × Bool) (F : P.Face),
              faceOfOrbit (Quotient.mk _ d) = F ↔ P.dartBorders d F) ∧
            (∀ q : Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin)),
              q ≠ Quotient.mk _ (kmswLeftBoundaryEdge w 0, false) →
              ∃ j : TriangleCreationTime w,
                {d : ℕ × Bool | Quotient.mk _ d = q} =
                  {d | d ∈ stageTriangleDartList w j} ∧
                Function.Injective (fun i : Fin 3 => Quotient.mk P.edgeSetoid
                  (if i.val = 0 then (stageTriangleDartTriple w j).1
                   else if i.val = 1 then (stageTriangleDartTriple w j).2.1
                   else (stageTriangleDartTriple w j).2.2))) ∧
            ∀ F : P.toPlaneGraphDrawing.Face,
              P.toPlaneGraphDrawing.IsInternal F → P.toPlaneGraphDrawing.faceDegree F = 3 := by
  let hfam := monotone_family_all w
  let P := monotoneFamilyDrawing w hfin hfam
  obtain ⟨U, hU, huniq, hborder⟩ :=
    DirectedDistances.PaperProofs.Section4.monotoneFamilyDrawing_faceClassification
      w hfin htrans hR hL0
  refine ⟨familyQ w hfam, (fun n => stageExtends_monotoneLayout w n
    (hfam n).choose (hfam (n + 1)).choose), P,
    familyDrawing_pos w hfin hfam, familyDrawing_arc w hfin hfam,
    U, hU, huniq, hborder,
    uiqbotDrawing_faceOfOrbit w hfin htrans hR hL0,
    uiqbotDrawing_faceOfOrbit_bijective w hfin htrans hR hL0,
    uiqbotDrawing_faceOfOrbit_mk_eq_iff w hfin htrans hR hL0,
    uiqbotDrawing_nonexternal_orbit_triangle w hfin htrans hR hL0,
    uiqbotDrawing_internal_faceDegree w hfin htrans hR hL0⟩

/-- Helper toward Definition 4.1: almost surely the same joint constructed
realization witnesses have a bijection from limit face orbits to geometric
faces, created triangles on three distinct geometric edges for every
non-external orbit, and geometric degree three for every bounded face. -/
theorem uiqbot_ae_constructed_plane_realization_faceDegree :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ _htrans : Tendsto (L w) atTop atTop,
          ∃ _hR : ∀ a : ℤ, ∃ n, R w n ≤ a,
            ∃ _hL0 : ∀ j, 0 ≤ L w j,
              ∃ Q : ∀ n, StageDrawing w n,
                (∀ n, StageExtends w n (Q n) (Q (n + 1))) ∧
                ∃ P : PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
                    (kmswInfRot w hfin) (kmswLimitDartVertex w),
                  (∀ n v, P.pos v.val = (Q n).pos v) ∧
                  (∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d) ∧
                  ∃ U : P.Face,
                    P.IsUnbounded U ∧
                    (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
                    (∀ d, P.dartBorders d U ↔ limitExternalDart w d) ∧
                    ∃ faceOfOrbit : Quotient (Equiv.Perm.SameCycle.setoid
                        (kmswInfFaceSucc w hfin)) → P.Face,
                      Function.Bijective faceOfOrbit ∧
                      (∀ (d : ℕ × Bool) (F : P.Face),
                        faceOfOrbit (Quotient.mk _ d) = F ↔ P.dartBorders d F) ∧
                      (∀ q : Quotient (Equiv.Perm.SameCycle.setoid (kmswInfFaceSucc w hfin)),
                        q ≠ Quotient.mk _ (kmswLeftBoundaryEdge w 0, false) →
                        ∃ j : TriangleCreationTime w,
                          {d : ℕ × Bool | Quotient.mk _ d = q} =
                            {d | d ∈ stageTriangleDartList w j} ∧
                          Function.Injective (fun i : Fin 3 => Quotient.mk P.edgeSetoid
                            (if i.val = 0 then (stageTriangleDartTriple w j).1
                             else if i.val = 1 then (stageTriangleDartTriple w j).2.1
                             else (stageTriangleDartTriple w j).2.2))) ∧
                      ∀ F : P.toPlaneGraphDrawing.Face,
                        P.toPlaneGraphDrawing.IsInternal F →
                          P.toPlaneGraphDrawing.faceDegree F = 3 := by
  filter_upwards [uiqbot_ae_constructed_plane_realization] with ω hω
  rcases hω with ⟨hfin, htrans, hR, hL0, _⟩
  exact ⟨hfin, htrans, hR, hL0,
    kmswConstructedPlaneRealization_with_faceDegree
      (pitmanCode (fun i => ω (i + 1))) hfin htrans hR hL0⟩

end DirectedDistances.KMSW
