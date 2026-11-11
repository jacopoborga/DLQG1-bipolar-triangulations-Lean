/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutHalfMap
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation
public import DirectedDistances.PlanarMap.PlanarPathCutHalves
public import DirectedDistances.PlanarMap.PlanarPathCutLeftBase
public import DirectedDistances.PlanarMap.PlanarPathCutRightBase

import DirectedDistances.PlanarMap.BipolarCanonicalTrees
import DirectedDistances.PlanarMap.PlanarPathCutLeftmostRegion

/-! Supporting lemmas for paper labels `lem-lr-ind` (see CORRESPONDENCE.md). -/

/-! # Local incidence facts for a planar path cut

not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

private theorem pathCutOneSided_tail_mem_pathVertices
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : dartTailVertex B.map d ∈ P.vertices := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hstep := P.edge_step i
  rw [← hi, ← hstep.2.2.1]
  exact List.get_mem _ _

private theorem pathCutOneSided_head_mem_pathVertices
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : dartHeadVertex B.map d ∈ P.vertices := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hstep := P.edge_step i
  rw [← hi, ← hstep.2.2.2]
  exact List.get_mem _ _

/-- Seam darts are based at vertices of the cut path (helper toward -/
theorem pathCutSeamDarts_tailVertex_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ pathCutSeamDarts B P) :
    dartTailVertex B.map d ∈ P.vertices := by
  change d ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv d ∈ P.darts at hd
  rcases hd with hd | hd
  · exact pathCutOneSided_tail_mem_pathVertices B P hd
  · have hhead := pathCutOneSided_head_mem_pathVertices B P hd
    simpa [dartHeadVertex, dartTailVertex,
      B.map.toCombinatorialMap.edgeInv_invol] using hhead

private theorem pathCutOneSided_seam_mem_closed_halves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n) {d : D}
    (hd : d ∈ pathCutSeamDarts B P) :
    d ∈ pathCutLeftHalfDarts B P ∧ d ∈ pathCutRightHalfDarts B P := by
  constructor <;> change _ ∈ _ ∪ pathCutSeamDarts B P <;> exact Or.inr hd

private theorem pathCutOneSided_exists_incoming_pathDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) (hvs : v ≠ B.source) :
    ∃ d ∈ P.darts, dartHeadVertex B.map d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hiLt : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
  have hi0 : i.val ≠ 0 := by
    intro h
    have hifin : i = ⟨0, by rw [P.vertices_length]; omega⟩ := Fin.ext h
    apply hvs
    calc
      v = P.vertices.get i := hi.symm
      _ = B.source := by rw [hifin, P.start_vertex]
  let j : Fin P.darts.length := ⟨i.val - 1, by
    rw [P.darts_length]
    omega⟩
  have hji : j.val + 1 = i.val := by
    dsimp [j]
    omega
  have hstep := P.edge_step j
  have hindex : (⟨j.val + 1, by rw [P.vertices_length]; rw [hji]; exact hiLt⟩ :
      Fin P.vertices.length) = i := by
    exact Fin.ext hji
  refine ⟨P.darts.get j, List.get_mem _ _, ?_⟩
  calc
    dartHeadVertex B.map (P.darts.get j) =
        P.vertices.get ⟨j.val + 1, by rw [P.vertices_length]; omega⟩ :=
      hstep.2.2.2.symm
    _ = P.vertices.get i := congrArg P.vertices.get hindex
    _ = v := hi

private theorem pathCutOneSided_exists_outgoing_pathDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) (hvt : v ≠ B.sink) :
    ∃ d ∈ P.darts, dartTailVertex B.map d = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hiLt : i.val < n + 1 := by simpa [P.vertices_length] using i.isLt
  have hin : i.val ≠ n := by
    intro h
    have hifin : i = ⟨n, by rw [P.vertices_length]; omega⟩ := Fin.ext h
    apply hvt
    calc
      v = P.vertices.get i := hi.symm
      _ = B.sink := by rw [hifin, P.end_vertex]
  let j : Fin P.darts.length := ⟨i.val, by
    rw [P.darts_length]
    omega⟩
  have hstep := P.edge_step j
  have hindex : (⟨j.val, by rw [P.vertices_length]; simpa [j] using hiLt⟩ :
      Fin P.vertices.length) = i := by
    apply Fin.ext
    rfl
  refine ⟨P.darts.get j, List.get_mem _ _, ?_⟩
  calc
    dartTailVertex B.map (P.darts.get j) =
        P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ :=
      hstep.2.2.1.symm
    _ = P.vertices.get i := congrArg P.vertices.get hindex
    _ = v := hi

/-- At a path vertex other than the source, its incoming path dart and the
reverse dart belong to both closed halves (helper toward `lem-lr-ind`, -/
theorem pathCut_vertex_incomingDart_in_both_closed_halves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) (hvs : v ≠ B.source) :
    ∃ d, d ∈ P.darts ∧ dartHeadVertex B.map d = v ∧
      d ∈ pathCutLeftHalfDarts B P ∧
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P ∧
      d ∈ pathCutRightHalfDarts B P ∧
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P := by
  obtain ⟨d, hd, hhead⟩ := pathCutOneSided_exists_incoming_pathDart B P hv hvs
  have hdSeam : d ∈ pathCutSeamDarts B P := Or.inl hd
  have hinvSeam : B.map.toCombinatorialMap.edgeInv d ∈ pathCutSeamDarts B P :=
    (pathCutSeamDarts_edgeInv_iff B P d).2 hdSeam
  exact ⟨d, hd, hhead,
    (pathCutOneSided_seam_mem_closed_halves B P hdSeam).1,
    (pathCutOneSided_seam_mem_closed_halves B P hinvSeam).1,
    (pathCutOneSided_seam_mem_closed_halves B P hdSeam).2,
    (pathCutOneSided_seam_mem_closed_halves B P hinvSeam).2⟩

private theorem pathCutOneSided_outerCorner_sameArc
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    {d : D} (hdOuter : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d))
    (hdTail : dartTailVertex B.map d ∉ P.vertices) :
    side (B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.edgeInv d)) =
      side (B.map.toCombinatorialMap.edgeInv d) := by
  let o := B.map.toCombinatorialMap.edgeInv d
  rcases (isOuter_iff_mem_outerArcs B o).mp hdOuter with hoLeft | hoRight
  · have hoPath : o ∈ B.leftPath.darts :=
      (mem_pathCutLeftOuterArc_iff B o).mp hoLeft
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hoPath
    have hiLt : i.val < ℓ := by simpa [B.leftPath.darts_length] using i.isLt
    by_cases hnext : i.val + 1 < ℓ
    · have hnextD : i.val + 1 < B.leftPath.darts.length := by
        simpa [B.leftPath.darts_length] using hnext
      have hget : B.leftPath.darts[i.val] = o := by
        simpa only [List.get_eq_getElem] using hi
      have hsucc : B.map.toCombinatorialMap.faceSucc o =
          B.leftPath.darts[i.val + 1]'hnextD := by
        rw [← hget]
        exact outerFace_leftPath_successor B i.val hnext
      have hnextLeft : B.leftPath.darts[i.val + 1]'hnextD ∈ pathCutLeftOuterArc B :=
        (mem_pathCutLeftOuterArc_iff B _).2 (List.getElem_mem _)
      calc
        side (B.map.toCombinatorialMap.faceSucc o) = true := by
          rw [hsucc]
          exact hleft _ (.inl hnextLeft)
        _ = side o := (hleft _ (.inl hoLeft)).symm
    · have hlast : i.val + 1 = ℓ := by omega
      have hstep := B.leftPath.edge_step i
      have hhead : dartHeadVertex B.map o = B.sink := by
        have hheadGet : dartHeadVertex B.map o = B.leftPath.vertices.get
            ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ := by
          simpa only [hi] using hstep.2.2.2.symm
        calc
          dartHeadVertex B.map o = B.leftPath.vertices.get
              ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ := hheadGet
          _ = B.leftPath.vertices.get
              ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩ := by
            congr 1
            exact Fin.ext hlast
          _ = B.sink := B.leftPath.end_vertex
      have htailFace : dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc o) = dartHeadVertex B.map o :=
        (corner_consecutiveDarts B o).2.2
      have htailD : dartTailVertex B.map d =
          dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc o) := by
        have h := (corner_consecutiveDarts B o).2.2
        simpa [o, dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using h.symm
      have htailEq : dartTailVertex B.map d = B.sink :=
        htailD.trans (htailFace.trans hhead)
      have hsinkP : B.sink ∈ P.vertices := by
        simpa only [P.end_vertex] using
          List.get_mem P.vertices ⟨n, by rw [P.vertices_length]; omega⟩
      have htailP : dartTailVertex B.map d ∈ P.vertices := by
        simpa only [htailEq] using hsinkP
      apply False.elim
      exact hdTail htailP
  · have hoPath : o ∈
        B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv :=
      (mem_pathCutRightOuterArc_iff B o).mp hoRight
    obtain ⟨p, hpRev, hpo⟩ := List.mem_map.mp hoPath
    have hp : p ∈ B.rightPath.darts := List.mem_reverse.mp hpRev
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    have hiLt : i.val < r := by simpa [B.rightPath.darts_length] using i.isLt
    have hget : B.rightPath.darts[i.val] = p := by
      simpa only [List.get_eq_getElem] using hi
    have hoEq : o = B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i.val]) := by
      calc
        o = B.map.toCombinatorialMap.edgeInv p := hpo.symm
        _ = B.map.toCombinatorialMap.edgeInv
            (B.rightPath.darts[i.val]) := congrArg _ hget.symm
    by_cases hi0 : i.val = 0
    · have htailP : dartTailVertex B.map p = B.source := by
        have htailGet : dartTailVertex B.map p = B.rightPath.vertices.get
            ⟨i.val, by rw [B.rightPath.vertices_length]; omega⟩ := by
          simpa only [hi] using (B.rightPath.edge_step i).2.2.1.symm
        calc
          dartTailVertex B.map p = B.rightPath.vertices.get
              ⟨i.val, by rw [B.rightPath.vertices_length]; omega⟩ := htailGet
          _ = B.rightPath.vertices.get
              ⟨0, by rw [B.rightPath.vertices_length]; omega⟩ := by
            congr 1
            exact Fin.ext hi0
          _ = B.source := B.rightPath.start_vertex
      have hhead : dartHeadVertex B.map o = B.source := by
        calc
          dartHeadVertex B.map o = dartTailVertex B.map p := by
            simp [hoEq, hget, dartHeadVertex, dartTailVertex,
              B.map.toCombinatorialMap.edgeInv_invol]
          _ = B.source := htailP
      have htailFace : dartTailVertex B.map
          (B.map.toCombinatorialMap.faceSucc o) = dartHeadVertex B.map o :=
        (corner_consecutiveDarts B o).2.2
      have htailD : dartTailVertex B.map d =
          dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc o) := by
        have h := (corner_consecutiveDarts B o).2.2
        simpa [o, dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using h.symm
      have htailEq : dartTailVertex B.map d = B.source :=
        htailD.trans (htailFace.trans hhead)
      have hsourceP : B.source ∈ P.vertices := by
        simpa only [P.start_vertex] using
          List.get_mem P.vertices ⟨0, by rw [P.vertices_length]; omega⟩
      have htailP : dartTailVertex B.map d ∈ P.vertices := by
        simpa only [htailEq] using hsourceP
      apply False.elim
      exact hdTail htailP
    · let j : Fin B.rightPath.darts.length := ⟨i.val - 1, by
        omega⟩
      have hgetPrev : B.rightPath.darts[i.val - 1] = B.rightPath.darts.get j := by
        simp [j, List.get_eq_getElem]
      have hsucc : B.map.toCombinatorialMap.faceSucc o =
          B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := by
        calc
          B.map.toCombinatorialMap.faceSucc o =
              B.map.toCombinatorialMap.faceSucc
                (B.map.toCombinatorialMap.edgeInv
                  (B.rightPath.darts[i.val])) := by rw [hoEq]
          _ = B.map.toCombinatorialMap.edgeInv
              (B.rightPath.darts[i.val - 1]) := by
            have hpos : 1 ≤ i.val := by omega
            have hbound : i.val - 1 + 1 < r := by
              simpa [Nat.sub_add_cancel hpos] using hiLt
            have hs := outerFace_rightPath_successor B (i.val - 1) hbound
            simpa only [List.get_eq_getElem, Nat.sub_add_cancel hpos] using hs
          _ = B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) :=
            congrArg _ hgetPrev
      have hnextRight : B.map.toCombinatorialMap.faceSucc o ∈
          pathCutRightOuterArc B := by
        apply (mem_pathCutRightOuterArc_iff B _).2
        apply List.mem_map.mpr
        refine ⟨B.rightPath.darts.get j,
          List.mem_reverse.mpr (List.get_mem _ j), ?_⟩
        exact hsucc.symm
      calc
        side (B.map.toCombinatorialMap.faceSucc o) = false :=
          hright _ (.inl hnextRight)
        _ = side o := (hright _ (.inl hoRight)).symm

private theorem pathCutOneSided_side_eq_rotSymm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    {d : D} (hdTail : dartTailVertex B.map d ∉ P.vertices) :
    side (B.map.toCombinatorialMap.rot.symm d) = side d := by
  have hdSeam : d ∉ pathCutSeamDarts B P := by
    intro h
    exact hdTail (pathCutSeamDarts_tailVertex_mem B P h)
  by_cases hinner : ¬ B.map.IsOuter
      (B.map.toCombinatorialMap.edgeInv d)
  · exact pathCutSide_eq_rotSymm_of_inner_offSeam
      B P side hface hedge d hinner hdSeam
  · have houter := pathCutOneSided_outerCorner_sameArc B P side hleft hright
      (Classical.not_not.mp hinner) hdTail
    calc
      side (B.map.toCombinatorialMap.rot.symm d) =
          side (B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.edgeInv d)) := by
        rw [(corner_consecutiveDarts B
          (B.map.toCombinatorialMap.edgeInv d)).1]
        simp only [B.map.toCombinatorialMap.edgeInv_invol]
      _ = side (B.map.toCombinatorialMap.edgeInv d) := houter
      _ = side d := hedge d hdSeam

private theorem pathCutOneSided_side_eq_of_sameTail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    {w : MapVertex B.map} {d e : D}
    (hdTail : dartTailVertex B.map d = w)
    (heTail : dartTailVertex B.map e = w)
    (hw : w ∉ P.vertices) : side d = side e := by
  let rot := B.map.toCombinatorialMap.rot
  have hlocal (x : D) (hx : dartTailVertex B.map x = w) :
      side (rot.symm x) = side x := by
    exact pathCutOneSided_side_eq_rotSymm B P side hleft hright hface hedge
      (by simpa [hx] using hw)
  have htailRot (x : D) : dartTailVertex B.map (rot x) =
      dartTailVertex B.map x := by
    apply Quotient.sound
    change rot.SameCycle (rot x) x
    exact Equiv.Perm.SameCycle.rfl.apply_left
  have hforward (x : D) (hx : dartTailVertex B.map x = w) :
      side (rot x) = side x := by
    have h := hlocal (rot x) (by simpa [htailRot x] using hx)
    change side (rot.symm (rot x)) = side (rot x) at h
    simpa [rot] using h.symm
  have hcycle : rot.SameCycle d e := by
    exact Quotient.exact (hdTail.trans heTail.symm)
  obtain ⟨k, _, hpow⟩ := hcycle.exists_pow_eq'
  have hiterEq : (rot : D → D)^[k] d = e := by
    simpa only [perm_iterate_eq_pow] using hpow
  have htailIter : ∀ k : ℕ,
      dartTailVertex B.map ((rot : D → D)^[k] d) = dartTailVertex B.map d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (htailRot _).trans ih
  have hiter : ∀ k : ℕ, side ((rot : D → D)^[k] d) = side d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (hforward _ ((htailIter k).trans hdTail)).trans ih
  calc
    side d = side ((rot : D → D)^[k] d) := (hiter k).symm
    _ = side e := congrArg side hiterEq

/-- Every dart at a vertex off the cut path belongs to the same one of the
two side classes (helper toward `lem-lr-ind`,
allows repeated vertices in the two outer boundary paths. -/
theorem pathCut_vertex_darts_one_sided
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {w : MapVertex B.map} (hw : w ∉ P.vertices) :
    (∀ d : D, dartTailVertex B.map d = w → d ∈ pathCutLeftDarts B P) ∨
      (∀ d : D, dartTailVertex B.map d = w → d ∈ pathCutRightDarts B P) := by
  obtain ⟨side, hleft, hright, hface, hedge⟩ := pathCut_exists_side_coloring B P
  have hmem := pathCutLeft_mem_iff_side_true_of_sideColoring
    B P side hleft hright hface hedge
  obtain ⟨d₀, hd₀⟩ := Quotient.exists_rep w
  change dartTailVertex B.map d₀ = w at hd₀
  have hsame (d : D) (hd : dartTailVertex B.map d = w) :
      side d = side d₀ :=
    pathCutOneSided_side_eq_of_sameTail B P side hleft hright hface hedge
      hd hd₀ hw
  by_cases hcolor : side d₀ = true
  · left
    intro d hd
    exact hmem d |>.2 ((hsame d hd).trans hcolor)
  · right
    intro d hd
    have hfalse : side d₀ = false := by
      cases hs : side d₀ <;> simp_all
    have hdFalse : side d = false := (hsame d hd).trans hfalse
    have hnotLeft : d ∉ pathCutLeftDarts B P := by
      intro hleftD
      have htrue := (hmem d).1 hleftD
      rw [hdFalse] at htrue
      cases htrue
    rcases pathCut_darts_cover B P d with hleftD | hrightD
    · exact (hnotLeft hleftD).elim
    · exact hrightD

/-- At a path vertex other than the sink, its outgoing path dart and the
reverse dart belong to both closed halves (helper toward `lem-lr-ind`, -/
theorem pathCut_vertex_outgoingDart_in_both_closed_halves
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) (hvt : v ≠ B.sink) :
    ∃ d, d ∈ P.darts ∧ dartTailVertex B.map d = v ∧
      d ∈ pathCutLeftHalfDarts B P ∧
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P ∧
      d ∈ pathCutRightHalfDarts B P ∧
      B.map.toCombinatorialMap.edgeInv d ∈ pathCutRightHalfDarts B P := by
  obtain ⟨d, hd, htail⟩ := pathCutOneSided_exists_outgoing_pathDart B P hv hvt
  have hdSeam : d ∈ pathCutSeamDarts B P := Or.inl hd
  have hinvSeam : B.map.toCombinatorialMap.edgeInv d ∈ pathCutSeamDarts B P :=
    (pathCutSeamDarts_edgeInv_iff B P d).2 hdSeam
  exact ⟨d, hd, htail,
    (pathCutOneSided_seam_mem_closed_halves B P hdSeam).1,
    (pathCutOneSided_seam_mem_closed_halves B P hinvSeam).1,
    (pathCutOneSided_seam_mem_closed_halves B P hdSeam).2,
    (pathCutOneSided_seam_mem_closed_halves B P hinvSeam).2⟩

private theorem pathCutOneSided_pathDart_tail
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {d : D} (hd : d ∈ P.darts) : B.map.tail d := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  simpa only [hi] using (P.edge_step i).2.1

private theorem pathCutOneSided_leftDart_mem_of_halfVertex_offPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v : MapVertex (pathCutLeftHalfDirectedMap B P))
    (hv : pathCutLeftHalfVertexMap B P v ∉ P.vertices)
    {d : D} (hdTail : dartTailVertex B.map d =
      pathCutLeftHalfVertexMap B P v) : d ∈ pathCutLeftDarts B P := by
  obtain ⟨e, he⟩ := Quotient.exists_rep v
  change dartTailVertex (pathCutLeftHalfDirectedMap B P) e = v at he
  have heTail : dartTailVertex B.map e.1 = pathCutLeftHalfVertexMap B P v := by
    calc
      dartTailVertex B.map e.1 = pathCutLeftHalfVertexMap B P
          (dartTailVertex (pathCutLeftHalfDirectedMap B P) e) :=
        (pathCutLeftHalfVertexMap_dartTailVertex B P e).symm
      _ = pathCutLeftHalfVertexMap B P v := congrArg _ he
  have heNotSeam : e.1 ∉ pathCutSeamDarts B P := by
    intro hseam
    have hvertex := pathCutSeamDarts_tailVertex_mem B P hseam
    exact hv (by simpa only [heTail] using hvertex)
  have heLeft : e.1 ∈ pathCutLeftDarts B P := by
    have heHalf := e.2
    change e.1 ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P at heHalf
    rcases heHalf with hleft | hseam
    · exact hleft
    · exact (heNotSeam hseam).elim
  rcases pathCut_vertex_darts_one_sided B P hv with hleftAll | hrightAll
  · exact hleftAll d hdTail
  · have hrightE := hrightAll e.1 heTail
    have hdisjoint := Set.disjoint_left.mp (pathCut_offSeam_disjoint B P)
    exact (hdisjoint ⟨heLeft, heNotSeam⟩ ⟨hrightE, heNotSeam⟩).elim

private theorem pathCutOneSided_leftHalf_liftDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u v : MapVertex (pathCutLeftHalfDirectedMap B P)} {d : D}
    (hd : d ∈ pathCutLeftHalfDarts B P) (htail : B.map.tail d)
    (hsource : dartTailVertex B.map d = pathCutLeftHalfVertexMap B P u)
    (htarget : dartHeadVertex B.map d = pathCutLeftHalfVertexMap B P v) :
    (pathCutLeftHalfDirectedMap B P).directedStep u v := by
  let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, hd⟩
  have hsourceMap : pathCutLeftHalfVertexMap B P
      (dartTailVertex (pathCutLeftHalfDirectedMap B P) dH) =
        pathCutLeftHalfVertexMap B P u := by
    rw [pathCutLeftHalfVertexMap_dartTailVertex]
    exact hsource
  have htargetMap : pathCutLeftHalfVertexMap B P
      (dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH) =
        pathCutLeftHalfVertexMap B P v := by
    rw [pathCutLeftHalfVertexMap_dartHeadVertex]
    exact htarget
  have hsourceEq := pathCutLeftHalfVertexMap_injective B P hsourceMap
  have htargetEq := pathCutLeftHalfVertexMap_injective B P htargetMap
  refine ⟨dH, ?_, ?_, hsourceEq, htargetEq⟩
  · change ¬ False
    exact not_false
  · exact (pathCutLeftHalf_embedding_fields B P).2.2.1 dH |>.mpr htail

/-- Every incoming base step at the image of a left-half vertex lifts to that
left-half vertex (helper toward `lem-lr-ind`, -/
theorem pathCutLeftHalf_incomingStep_lifts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {v : MapVertex (pathCutLeftHalfDirectedMap B P)}
    {u : MapVertex B.map}
    (h : B.map.directedStep u (pathCutLeftHalfVertexMap B P v)) :
    ∃ uH, (pathCutLeftHalfDirectedMap B P).directedStep uH v := by
  let w := pathCutLeftHalfVertexMap B P v
  change B.map.directedStep u w at h
  by_cases hwPath : w ∈ P.vertices
  · by_cases hwSource : w = B.source
    · rw [hwSource] at h
      exact (B.isSource ⟨u, h⟩).elim
    · obtain ⟨d, hdPath, hdHead, hdLeft, _, _, _⟩ :=
        pathCut_vertex_incomingDart_in_both_closed_halves B P hwPath hwSource
      let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, hdLeft⟩
      have hdTail : B.map.tail d := pathCutOneSided_pathDart_tail B P hdPath
      have hsource : dartTailVertex B.map d =
          pathCutLeftHalfVertexMap B P (dartTailVertex
            (pathCutLeftHalfDirectedMap B P) dH) := by
        exact (pathCutLeftHalfVertexMap_dartTailVertex B P dH).symm
      have htarget : dartHeadVertex B.map d =
          pathCutLeftHalfVertexMap B P v := by
        simpa [w] using hdHead
      exact ⟨dartTailVertex (pathCutLeftHalfDirectedMap B P) dH,
        pathCutOneSided_leftHalf_liftDart B P hdLeft hdTail hsource htarget⟩
  · rcases h with ⟨d, _hmissing, htail, _hsource, htarget⟩
    change dartHeadVertex B.map d = w at htarget
    have hreverseTail : dartTailVertex B.map
        (B.map.toCombinatorialMap.edgeInv d) = w := by
      simpa only [dartTailVertex, dartHeadVertex] using htarget
    have hreverseLeft := pathCutOneSided_leftDart_mem_of_halfVertex_offPath
      B P v hwPath hreverseTail
    have hdLeft : d ∈ pathCutLeftHalfDarts B P := by
      have hreverseHalf : B.map.toCombinatorialMap.edgeInv d ∈
          pathCutLeftHalfDarts B P := Or.inl hreverseLeft
      have h := pathCutLeftHalf_edgeInv_mem B P hreverseHalf
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h
    let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, hdLeft⟩
    have hsource : dartTailVertex B.map d =
        pathCutLeftHalfVertexMap B P (dartTailVertex
          (pathCutLeftHalfDirectedMap B P) dH) := by
      exact (pathCutLeftHalfVertexMap_dartTailVertex B P dH).symm
    have htarget' : dartHeadVertex B.map d = pathCutLeftHalfVertexMap B P v := by
      simpa [w] using htarget
    exact ⟨dartTailVertex (pathCutLeftHalfDirectedMap B P) dH,
      pathCutOneSided_leftHalf_liftDart B P hdLeft htail hsource htarget'⟩

/-- Every outgoing base step at the image of a left-half vertex lifts from
that left-half vertex (helper toward `lem-lr-ind`, -/
theorem pathCutLeftHalf_outgoingStep_lifts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {v : MapVertex (pathCutLeftHalfDirectedMap B P)}
    {u : MapVertex B.map}
    (h : B.map.directedStep (pathCutLeftHalfVertexMap B P v) u) :
    ∃ wH, (pathCutLeftHalfDirectedMap B P).directedStep v wH := by
  let w := pathCutLeftHalfVertexMap B P v
  change B.map.directedStep w u at h
  by_cases hwPath : w ∈ P.vertices
  · by_cases hwSink : w = B.sink
    · rw [hwSink] at h
      exact (B.isSink ⟨u, h⟩).elim
    · obtain ⟨d, hdPath, hdTail, hdLeft, _, _, _⟩ :=
        pathCut_vertex_outgoingDart_in_both_closed_halves B P hwPath hwSink
      let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, hdLeft⟩
      have hdTail' : B.map.tail d := pathCutOneSided_pathDart_tail B P hdPath
      have hsource : dartTailVertex B.map d =
          pathCutLeftHalfVertexMap B P v := by
        simpa [w] using hdTail
      have htarget : dartHeadVertex B.map d =
          pathCutLeftHalfVertexMap B P
            (dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH) := by
        exact (pathCutLeftHalfVertexMap_dartHeadVertex B P dH).symm
      exact ⟨dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH,
        pathCutOneSided_leftHalf_liftDart B P hdLeft hdTail' hsource htarget⟩
  · rcases h with ⟨d, _hmissing, htail, hsource, _htarget⟩
    change dartTailVertex B.map d = w at hsource
    have hdLeft := pathCutOneSided_leftDart_mem_of_halfVertex_offPath
      B P v hwPath hsource
    let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, Or.inl hdLeft⟩
    have hsource' : dartTailVertex B.map d = pathCutLeftHalfVertexMap B P v := by
      simpa [w] using hsource
    have htarget : dartHeadVertex B.map d =
        pathCutLeftHalfVertexMap B P
          (dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH) := by
      exact (pathCutLeftHalfVertexMap_dartHeadVertex B P dH).symm
    exact ⟨dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH,
      pathCutOneSided_leftHalf_liftDart B P (Or.inl hdLeft) htail hsource' htarget⟩

 
theorem pathCutLeftHalfSource_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v : MapVertex (pathCutLeftHalfDirectedMap B P))
    (hv : ¬ ∃ u, (pathCutLeftHalfDirectedMap B P).directedStep u v) :
    v = pathCutLeftHalfSource B P := by
  let w := pathCutLeftHalfVertexMap B P v
  have hnoBase : ¬ ∃ u, B.map.directedStep u w := by
    rintro ⟨u, hu⟩
    obtain ⟨uH, huH⟩ := pathCutLeftHalf_incomingStep_lifts B P hu
    exact hv ⟨uH, huH⟩
  have hw : w = B.source := B.source_unique w hnoBase
  apply pathCutLeftHalfVertexMap_injective B P
  calc
    pathCutLeftHalfVertexMap B P v = w := rfl
    _ = B.source := hw
    _ = pathCutLeftHalfVertexMap B P (pathCutLeftHalfSource B P) :=
      (pathCutLeftHalfSource_map B P).symm

 
theorem pathCutLeftHalfSink_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v : MapVertex (pathCutLeftHalfDirectedMap B P))
    (hv : ¬ ∃ w, (pathCutLeftHalfDirectedMap B P).directedStep v w) :
    v = pathCutLeftHalfSink B P := by
  let w := pathCutLeftHalfVertexMap B P v
  have hnoBase : ¬ ∃ u, B.map.directedStep w u := by
    rintro ⟨u, hu⟩
    obtain ⟨wH, huH⟩ := pathCutLeftHalf_outgoingStep_lifts B P hu
    exact hv ⟨wH, huH⟩
  have hw : w = B.sink := B.sink_unique w hnoBase
  apply pathCutLeftHalfVertexMap_injective B P
  calc
    pathCutLeftHalfVertexMap B P v = w := rfl
    _ = B.sink := hw
    _ = pathCutLeftHalfVertexMap B P (pathCutLeftHalfSink B P) :=
      (pathCutLeftHalfSink_map B P).symm

private theorem pathCutOneSided_rightDart_mem_of_halfVertex_offPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v : MapVertex (pathCutRightHalfDirectedMap B P))
    (hv : pathCutRightHalfVertexMap B P v ∉ P.vertices)
    {d : D} (hdTail : dartTailVertex B.map d =
      pathCutRightHalfVertexMap B P v) : d ∈ pathCutRightDarts B P := by
  obtain ⟨e, he⟩ := Quotient.exists_rep v
  change dartTailVertex (pathCutRightHalfDirectedMap B P) e = v at he
  have heTail : dartTailVertex B.map e.1 = pathCutRightHalfVertexMap B P v := by
    calc
      dartTailVertex B.map e.1 = pathCutRightHalfVertexMap B P
          (dartTailVertex (pathCutRightHalfDirectedMap B P) e) :=
        (pathCutRightHalfVertexMap_dartTailVertex B P e).symm
      _ = pathCutRightHalfVertexMap B P v := congrArg _ he
  have heNotSeam : e.1 ∉ pathCutSeamDarts B P := by
    intro hseam
    have hvertex := pathCutSeamDarts_tailVertex_mem B P hseam
    exact hv (by simpa only [heTail] using hvertex)
  have heRight : e.1 ∈ pathCutRightDarts B P := by
    have heHalf := e.2
    change e.1 ∈ pathCutRightDarts B P ∪ pathCutSeamDarts B P at heHalf
    rcases heHalf with hright | hseam
    · exact hright
    · exact (heNotSeam hseam).elim
  rcases pathCut_vertex_darts_one_sided B P hv with hleftAll | hrightAll
  · have hleftE := hleftAll e.1 heTail
    have hdisjoint := Set.disjoint_left.mp (pathCut_offSeam_disjoint B P)
    exact (hdisjoint ⟨hleftE, heNotSeam⟩ ⟨heRight, heNotSeam⟩).elim
  · exact hrightAll d hdTail

private theorem pathCutOneSided_rightHalf_liftDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {u v : MapVertex (pathCutRightHalfDirectedMap B P)} {d : D}
    (hd : d ∈ pathCutRightHalfDarts B P) (htail : B.map.tail d)
    (hsource : dartTailVertex B.map d = pathCutRightHalfVertexMap B P u)
    (htarget : dartHeadVertex B.map d = pathCutRightHalfVertexMap B P v) :
    (pathCutRightHalfDirectedMap B P).directedStep u v := by
  let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, hd⟩
  have hsourceMap : pathCutRightHalfVertexMap B P
      (dartTailVertex (pathCutRightHalfDirectedMap B P) dH) =
        pathCutRightHalfVertexMap B P u := by
    rw [pathCutRightHalfVertexMap_dartTailVertex]
    exact hsource
  have htargetMap : pathCutRightHalfVertexMap B P
      (dartHeadVertex (pathCutRightHalfDirectedMap B P) dH) =
        pathCutRightHalfVertexMap B P v := by
    rw [pathCutRightHalfVertexMap_dartHeadVertex]
    exact htarget
  have hsourceEq := pathCutRightHalfVertexMap_injective B P hsourceMap
  have htargetEq := pathCutRightHalfVertexMap_injective B P htargetMap
  refine ⟨dH, ?_, ?_, hsourceEq, htargetEq⟩
  · change ¬ False
    exact not_false
  · exact (pathCutRightHalf_embedding_fields B P).2.2.1 dH |>.mpr htail

/-- Every incoming base step at the image of a right-half vertex lifts to that
not the paper result. -/
theorem pathCutRightHalf_incomingStep_lifts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {v : MapVertex (pathCutRightHalfDirectedMap B P)}
    {u : MapVertex B.map}
    (h : B.map.directedStep u (pathCutRightHalfVertexMap B P v)) :
    ∃ uH, (pathCutRightHalfDirectedMap B P).directedStep uH v := by
  let w := pathCutRightHalfVertexMap B P v
  change B.map.directedStep u w at h
  by_cases hwPath : w ∈ P.vertices
  · by_cases hwSource : w = B.source
    · rw [hwSource] at h
      exact (B.isSource ⟨u, h⟩).elim
    · obtain ⟨d, hdPath, hdHead, _, _, hdRight, _⟩ :=
        pathCut_vertex_incomingDart_in_both_closed_halves B P hwPath hwSource
      let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, hdRight⟩
      have hdTail : B.map.tail d := pathCutOneSided_pathDart_tail B P hdPath
      have hsource : dartTailVertex B.map d =
          pathCutRightHalfVertexMap B P (dartTailVertex
            (pathCutRightHalfDirectedMap B P) dH) := by
        exact (pathCutRightHalfVertexMap_dartTailVertex B P dH).symm
      have htarget : dartHeadVertex B.map d =
          pathCutRightHalfVertexMap B P v := by
        simpa [w] using hdHead
      exact ⟨dartTailVertex (pathCutRightHalfDirectedMap B P) dH,
        pathCutOneSided_rightHalf_liftDart B P hdRight hdTail hsource htarget⟩
  · rcases h with ⟨d, _hmissing, htail, _hsource, htarget⟩
    change dartHeadVertex B.map d = w at htarget
    have hreverseTail : dartTailVertex B.map
        (B.map.toCombinatorialMap.edgeInv d) = w := by
      simpa only [dartTailVertex, dartHeadVertex] using htarget
    have hreverseRight := pathCutOneSided_rightDart_mem_of_halfVertex_offPath
      B P v hwPath hreverseTail
    have hdRight : d ∈ pathCutRightHalfDarts B P := by
      have hreverseHalf : B.map.toCombinatorialMap.edgeInv d ∈
          pathCutRightHalfDarts B P := Or.inl hreverseRight
      have h := pathCutRightHalf_edgeInv_mem B P hreverseHalf
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h
    let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, hdRight⟩
    have hsource : dartTailVertex B.map d =
        pathCutRightHalfVertexMap B P (dartTailVertex
          (pathCutRightHalfDirectedMap B P) dH) := by
      exact (pathCutRightHalfVertexMap_dartTailVertex B P dH).symm
    have htarget' : dartHeadVertex B.map d = pathCutRightHalfVertexMap B P v := by
      simpa [w] using htarget
    exact ⟨dartTailVertex (pathCutRightHalfDirectedMap B P) dH,
      pathCutOneSided_rightHalf_liftDart B P hdRight htail hsource htarget'⟩

/-- Every outgoing base step at the image of a right-half vertex lifts from
not the paper result. -/
theorem pathCutRightHalf_outgoingStep_lifts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    {v : MapVertex (pathCutRightHalfDirectedMap B P)}
    {u : MapVertex B.map}
    (h : B.map.directedStep (pathCutRightHalfVertexMap B P v) u) :
    ∃ wH, (pathCutRightHalfDirectedMap B P).directedStep v wH := by
  let w := pathCutRightHalfVertexMap B P v
  change B.map.directedStep w u at h
  by_cases hwPath : w ∈ P.vertices
  · by_cases hwSink : w = B.sink
    · rw [hwSink] at h
      exact (B.isSink ⟨u, h⟩).elim
    · obtain ⟨d, hdPath, hdTail, _, _, hdRight, _⟩ :=
        pathCut_vertex_outgoingDart_in_both_closed_halves B P hwPath hwSink
      let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, hdRight⟩
      have hdTail' : B.map.tail d := pathCutOneSided_pathDart_tail B P hdPath
      have hsource : dartTailVertex B.map d =
          pathCutRightHalfVertexMap B P v := by
        simpa [w] using hdTail
      have htarget : dartHeadVertex B.map d =
          pathCutRightHalfVertexMap B P
            (dartHeadVertex (pathCutRightHalfDirectedMap B P) dH) := by
        exact (pathCutRightHalfVertexMap_dartHeadVertex B P dH).symm
      exact ⟨dartHeadVertex (pathCutRightHalfDirectedMap B P) dH,
        pathCutOneSided_rightHalf_liftDart B P hdRight hdTail' hsource htarget⟩
  · rcases h with ⟨d, _hmissing, htail, hsource, _htarget⟩
    change dartTailVertex B.map d = w at hsource
    have hdRight := pathCutOneSided_rightDart_mem_of_halfVertex_offPath
      B P v hwPath hsource
    let dH : {d : D // d ∈ pathCutRightHalfDarts B P} := ⟨d, Or.inl hdRight⟩
    have hsource' : dartTailVertex B.map d = pathCutRightHalfVertexMap B P v := by
      simpa [w] using hsource
    have htarget : dartHeadVertex B.map d =
        pathCutRightHalfVertexMap B P
          (dartHeadVertex (pathCutRightHalfDirectedMap B P) dH) := by
      exact (pathCutRightHalfVertexMap_dartHeadVertex B P dH).symm
    exact ⟨dartHeadVertex (pathCutRightHalfDirectedMap B P) dH,
      pathCutOneSided_rightHalf_liftDart B P (Or.inl hdRight) htail hsource' htarget⟩

 
theorem pathCutRightHalfSource_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v : MapVertex (pathCutRightHalfDirectedMap B P))
    (hv : ¬ ∃ u, (pathCutRightHalfDirectedMap B P).directedStep u v) :
    v = pathCutRightHalfSource B P := by
  let w := pathCutRightHalfVertexMap B P v
  have hnoBase : ¬ ∃ u, B.map.directedStep u w := by
    rintro ⟨u, hu⟩
    obtain ⟨uH, huH⟩ := pathCutRightHalf_incomingStep_lifts B P hu
    exact hv ⟨uH, huH⟩
  have hw : w = B.source := B.source_unique w hnoBase
  apply pathCutRightHalfVertexMap_injective B P
  calc
    pathCutRightHalfVertexMap B P v = w := rfl
    _ = B.source := hw
    _ = pathCutRightHalfVertexMap B P (pathCutRightHalfSource B P) :=
      (pathCutRightHalfSource_map B P).symm

 
theorem pathCutRightHalfSink_unique
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutRightHalfDarts B P)]
    (v : MapVertex (pathCutRightHalfDirectedMap B P))
    (hv : ¬ ∃ w, (pathCutRightHalfDirectedMap B P).directedStep v w) :
    v = pathCutRightHalfSink B P := by
  let w := pathCutRightHalfVertexMap B P v
  have hnoBase : ¬ ∃ u, B.map.directedStep w u := by
    rintro ⟨u, hu⟩
    obtain ⟨wH, huH⟩ := pathCutRightHalf_outgoingStep_lifts B P hu
    exact hv ⟨wH, huH⟩
  have hw : w = B.sink := B.sink_unique w hnoBase
  apply pathCutRightHalfVertexMap_injective B P
  calc
    pathCutRightHalfVertexMap B P v = w := rfl
    _ = B.sink := hw
    _ = pathCutRightHalfVertexMap B P (pathCutRightHalfSink B P) :=
      (pathCutRightHalfSink_map B P).symm

end DirectedDistances.PlanarMap
