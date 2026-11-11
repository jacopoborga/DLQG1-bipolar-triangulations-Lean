/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.BoundaryChanneledGeometry13

 

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open unitInterval

private theorem boundaryChanneled_pathCast_range {x y x' y' : ℂ}
    (γ : Path x y) (hx : x' = x) (hy : y' = y) :
    Set.range (γ.cast hx hy) = Set.range γ := by
  ext z
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa only [Path.cast_coe] using ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa only [Path.cast_coe] using ht⟩

/-- Helper toward Definition 3.2: the specific transported drawing preserves
the winding-side tests of each forward map arc. -/
theorem boundaryChanneled_transport_specific_sides
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n)
    (G : BoundaryChanneledPLDrawing R)
    (hOuterUnbounded :
      G.IsUnbounded (boundaryChanneledMarkedOuterFace R G)) :
    ∃ (rot : Equiv.Perm (G.GeometricEdge × Bool))
      (H : PLDrawing (G.GeometricEdge × Bool) (MapVertex R.B.map)
        (fun d => (d.1, !d.2)) rot
        (boundaryDartInitial (boundaryChanneledPlaneMap R G))),
      DrawsMap (boundaryChanneledPlaneMap R G) H ∧
      ∀ U : H.Face, H.IsUnbounded U →
        ∃ F : (Drawing (boundaryChanneledPlaneMap R G)).Face,
          F.val = U.val ∧ (Drawing (boundaryChanneledPlaneMap R G)).IsExternal F ∧
          ∀ e (hp : ¬ (boundaryChanneledPlaneMap R G).toPlaneMapWithMissing.missing e),
            ((∀ s : {t : unitInterval // t ∈ openParams},
                LeftAtOn U.val
                  (H.arc (e, (boundaryChanneledPlaneMap R G).forward ⟨e, hp⟩)).toPath s) ↔
              LeftOf (boundaryChanneledPlaneMap R G) F ⟨e, hp⟩) ∧
            ((∀ s : {t : unitInterval // t ∈ openParams},
                RightAtOn U.val
                  (H.arc (e, (boundaryChanneledPlaneMap R G).forward ⟨e, hp⟩)).toPath s) ↔
              RightOf (boundaryChanneledPlaneMap R G) F ⟨e, hp⟩) := by
  obtain ⟨rot, H, hDraws, _hArcs⟩ :=
    boundaryChanneled_transport_oriented_arcs R G hOuterUnbounded
  refine ⟨rot, H, hDraws, ?_⟩
  intro U hU
  obtain ⟨F, hF, hFext⟩ :=
    boundaryChanneled_drawsMap_externalFace R G rot H U hDraws hU
  refine ⟨F, hF, hFext, ?_⟩
  intro e hp
  let M := boundaryChanneledPlaneMap R G
  let d : G.GeometricEdge × Bool := (e, M.forward ⟨e, hp⟩)
  let γ : Path (H.arc d).start (H.arc d).finish := (H.arc d).toPath
  let δ : Path (M.toPlaneMapWithMissing.pos (M.tail ⟨e, hp⟩))
      (M.toPlaneMapWithMissing.pos (M.head ⟨e, hp⟩)) :=
    orientedArc M ⟨e, hp⟩
  have hinit : boundaryDartInitial M d = M.tail ⟨e, hp⟩ := by
    cases hf : M.forward ⟨e, hp⟩
    · rw [boundaryDartInitial_eq]
      simp [d, hf, DirectedPlaneMapWithMissing.tail]
    · rw [boundaryDartInitial_eq]
      simp [d, hf, DirectedPlaneMapWithMissing.tail]
  have hterm : boundaryDartTerminal M d = M.head ⟨e, hp⟩ := by
    cases hf : M.forward ⟨e, hp⟩
    · rw [boundaryDartTerminal_eq]
      simp [d, hf, DirectedPlaneMapWithMissing.head]
    · rw [boundaryDartTerminal_eq]
      simp [d, hf, DirectedPlaneMapWithMissing.head]
  have htermFlip :
      boundaryDartInitial M (e, !(M.forward ⟨e, hp⟩)) =
        boundaryDartTerminal M (e, M.forward ⟨e, hp⟩) := by
    rw [boundaryDartInitial_eq, boundaryDartTerminal_eq]
    cases M.forward ⟨e, hp⟩ <;> simp
  have hx : M.toPlaneMapWithMissing.pos (M.tail ⟨e, hp⟩) = (H.arc d).start := by
    calc
      M.toPlaneMapWithMissing.pos (M.tail ⟨e, hp⟩) =
          M.toPlaneMapWithMissing.pos (boundaryDartInitial M d) :=
            congrArg M.toPlaneMapWithMissing.pos hinit.symm
      _ = H.pos (boundaryDartInitial M d) := (congrFun hDraws.1 _).symm
      _ = (H.arc d).start := (H.arc_start d).symm
  have hy : M.toPlaneMapWithMissing.pos (M.head ⟨e, hp⟩) = (H.arc d).finish := by
    calc
      M.toPlaneMapWithMissing.pos (M.head ⟨e, hp⟩) =
          M.toPlaneMapWithMissing.pos (boundaryDartTerminal M d) :=
            congrArg M.toPlaneMapWithMissing.pos hterm.symm
      _ = H.pos (boundaryDartTerminal M d) := (congrFun hDraws.1 _).symm
      _ = H.pos (boundaryDartInitial M (e, !(M.forward ⟨e, hp⟩))) :=
        congrArg H.pos htermFlip.symm
      _ = (H.arc d).finish := by simpa [d] using (H.arc_finish d).symm
  let γ' : Path (M.toPlaneMapWithMissing.pos (M.tail ⟨e, hp⟩))
      (M.toPlaneMapWithMissing.pos (M.head ⟨e, hp⟩)) := γ.cast hx hy
  have hγ : Function.Injective γ' := by
    intro s t hst
    apply (H.arc d).toPath_injective (H.arc_length d) (H.arc_simple d)
    simpa [γ', γ, Path.cast_coe] using hst
  have hδ : Function.Injective δ := by
    have hmap : Function.Injective (M.toPlaneMapWithMissing.arc e) := by
      change Function.Injective
        ((G.arc e.out).toPath.cast (G.arc_start e.out).symm (G.arc_finish e.out).symm)
      intro s t hst
      apply (G.arc e.out).toPath_injective (G.arc_length e.out) (G.arc_simple e.out)
      simpa using hst
    have hmapSymm : Function.Injective (M.toPlaneMapWithMissing.arc e).symm :=
      hmap.comp unitInterval.symm_bijective.injective
    intro s t hst
    have hcoe := orientedArc_coe M ⟨e, hp⟩
    change δ s = δ t at hst
    rw [hcoe] at hst
    by_cases hf : M.forward ⟨e, hp⟩
    · have hst' : (M.toPlaneMapWithMissing.arc e) s =
          (M.toPlaneMapWithMissing.arc e) t := by simpa [hf] using hst
      exact hmap hst'
    · have hst' : (M.toPlaneMapWithMissing.arc e).symm s =
          (M.toPlaneMapWithMissing.arc e).symm t := by simpa [hf] using hst
      exact hmapSymm hst'
  have hrange : Set.range δ = Set.range γ' := by
    calc
      Set.range δ = Set.range (M.toPlaneMapWithMissing.arc e) := by
        have hcoe := orientedArc_coe M ⟨e, hp⟩
        change Set.range (⇑δ) = Set.range (⇑(M.toPlaneMapWithMissing.arc e))
        rw [hcoe]
        by_cases hf : M.forward ⟨e, hp⟩
        · simp [hf]
        · simp [hf, Path.symm_range]
      _ = Set.range γ := by
        exact (hDraws.2 d).symm
      _ = Set.range γ' := (boundaryChanneled_pathCast_range γ hx hy).symm
  have hleft := boundaryChanneled_leftAtOn_transfer_of_injective_range_eq
    F.val γ' δ hγ hδ hrange
  have hright := boundaryChanneled_rightAtOn_transfer_of_injective_range_eq
    F.val γ' δ hγ hδ hrange
  constructor
  · change (∀ s : {t : unitInterval // t ∈ openParams}, LeftAtOn U.val γ s) ↔
      LeftOf M F ⟨e, hp⟩
    rw [← hF]
    exact (forall_congr' (fun s => leftAtOn_cast_iff F.val γ hx hy s)).trans hleft.symm
  · change (∀ s : {t : unitInterval // t ∈ openParams}, RightAtOn U.val γ s) ↔
      RightOf M F ⟨e, hp⟩
    rw [← hF]
    exact (forall_congr' (fun s => rightAtOn_cast_iff F.val γ hx hy s)).trans hright.symm





























































































end DirectedDistances.PaperProofs.Section3

end
