module

public import DirectedDistances.PaperProofs.Section7.BoltzmannSDPUpperIntersection
public import DirectedDistances.PlanarMap.FiniteXDPGeodesicSplit
public import DirectedDistances.PlanarMap.PlanarPathCutSeparation

/-! Supporting lemmas for paper labels `lem-boltzmann-sdp-upper` (see CORRESPONDENCE.md). -/

/-! Reduction of the strict crossing obligation to a complete simple source-to-sink
cut. The named OPEN proposition below is defined, never assumed or asserted.
The planar seam crossing is outstanding; this file does not prove Lemma 7.13. -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap

attribute [local instance 1100] presentDartQuiver

variable {D : Type*} [Fintype D] [DecidableEq D]




private theorem strictCrossing_path_steps (M : DirectedMapWithMissing D)
    {s t : MapVertex M} (p : Quiver.Path s t) (hp : 0 < p.length) :
    Relation.TransGen M.directedStep s t := by
  induction p with
  | nil => simp only [Quiver.Path.length_nil, lt_self_iff_false] at hp
  | @cons b c p e ih =>
    have he : M.directedStep b c := ⟨e.1, e.2⟩
    cases p with
    | nil => exact Relation.TransGen.single he
    | cons p f => exact Relation.TransGen.tail (ih (by simp)) he




theorem boltzmannSdpUpper_presentPath_vertices_nodup
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {s t : MapVertex M} (p : Quiver.Path s t) : p.vertices.Nodup := by
  apply DirectedDistances.vertices_nodup_of_acyclic (p := p)
  intro v q
  by_contra h
  exact hM v (strictCrossing_path_steps M q (Nat.pos_of_ne_zero h))





theorem boltzmannSdpUpper_presentPath_exists_simple
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {s t : MapVertex M} (p : Quiver.Path s t) :
    ∃ S : SimpleDirectedDartPath M s t p.length, S.vertices = p.vertices := by
  induction p with
  | nil =>
    exact ⟨{
      darts := []
      vertices := [s]
      darts_length := rfl
      vertices_length := rfl
      vertices_nodup := List.nodup_singleton s
      start_vertex := rfl
      end_vertex := rfl
      edge_step := fun i => Fin.elim0 i
    }, rfl⟩
  | @cons b c p e ih =>
    obtain ⟨S, hS⟩ := ih
    have hn := boltzmannSdpUpper_presentPath_vertices_nodup M hM (p.cons e)
    refine ⟨{
      darts := S.darts ++ [e.1]
      vertices := p.vertices ++ [c]
      darts_length := by simp only [List.length_append, List.length_singleton,
        S.darts_length, Quiver.Path.length_cons]
      vertices_length := by simp
      vertices_nodup := by
        simpa only [Quiver.Path.vertices_cons, List.concat_eq_append] using hn
      start_vertex := by simp [List.get_eq_getElem]
      end_vertex := by simp [List.get_eq_getElem]
      edge_step := ?_
    }, by simp only [Quiver.Path.vertices_cons, List.concat_eq_append]⟩
    intro i
    have hi : i.val ≤ p.length := by
      have hi := i.isLt
      simp only [List.length_append, List.length_singleton, S.darts_length] at hi
      omega
    by_cases hlt : i.val < p.length
    · have hd : i.val < S.darts.length := by rw [S.darts_length]; exact hlt
      have hv : i.val < p.vertices.length := by simp; omega
      have hv' : i.val + 1 < p.vertices.length := by simp; omega
      have hs := S.edge_step ⟨i.val, hd⟩
      simp only [List.get_eq_getElem, List.getElem_append_left hd,
        List.getElem_append_left hv, List.getElem_append_left hv']
      simpa only [List.get_eq_getElem, hS] using hs
    · have heq : i.val = p.length := by omega
      have hlast : (S.darts ++ [e.1]).get i = e.1 := by
        simp [List.get_eq_getElem, heq, S.darts_length]
      rw [hlast]
      refine ⟨e.2.1, e.2.2.1, ?_, ?_⟩
      · have hlastV : p.vertices[p.length] = b := by
          simpa only [List.getLast_eq_getElem, Quiver.Path.vertices_length,
            Nat.add_sub_cancel_right] using p.vertices_getLast
        simpa [List.get_eq_getElem, heq, hlastV] using e.2.2.2.1.symm
      · simpa [List.get_eq_getElem, heq] using e.2.2.2.2.symm




theorem boltzmannSdpUpper_simple_exists_presentPath
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (S : SimpleDirectedDartPath M s t n) :
    ∃ p : Quiver.Path s t, p.length = n ∧ p.vertices = S.vertices := by
  induction n generalizing t with
  | zero =>
    have hst : s = t := S.start_vertex.symm.trans S.end_vertex
    subst t
    refine ⟨Quiver.Path.nil, rfl, ?_⟩
    have hlen : S.vertices.length = 1 := S.vertices_length
    have h := List.take_concat_get' S.vertices 0 (by omega)
    have hzero : S.vertices[0] = s := S.start_vertex
    rw [List.take_zero, List.nil_append, hzero,
      List.take_of_length_le (by omega)] at h
    exact h
  | succ n ih =>
    let k : Fin (n + 1 + 1) := ⟨n, by omega⟩
    obtain ⟨p, hp, hv⟩ := ih (S.prefix k)
    let d : Fin S.darts.length := ⟨n, by rw [S.darts_length]; omega⟩
    have hs := S.edge_step d
    let e' : S.vertices.get ⟨n, by rw [S.vertices_length]; omega⟩ ⟶ t :=
      ⟨S.darts.get d, hs.1, hs.2.1, hs.2.2.1.symm,
        hs.2.2.2.symm.trans S.end_vertex⟩
    refine ⟨p.cons e', by simp [hp], ?_⟩
    rw [Quiver.Path.vertices_cons, hv, S.prefix_vertices]
    have h := List.take_concat_get' S.vertices (n + 1) (by
      rw [S.vertices_length]; omega)
    have hbound : n + 1 < S.vertices.length := by rw [S.vertices_length]; omega
    have hend : S.vertices[n + 1]'hbound = t := S.end_vertex
    have htake : S.vertices.take (n + 1 + 1) = S.vertices :=
      List.take_of_length_le (by rw [S.vertices_length])
    rw [hend, htake] at h
    simpa only [k, List.concat_eq_append] using h




private theorem strictCrossing_comp_take {M : DirectedMapWithMissing D}
    {s t u : MapVertex M} (p : Quiver.Path s t) (q : Quiver.Path t u) :
    (p.comp q).vertices.take (p.length + 1) = p.vertices := by
  induction q with
  | nil => simp only [Quiver.Path.comp_nil, ← p.vertices_length, List.take_length]
  | cons q e ih =>
    rw [Quiver.Path.comp_cons, Quiver.Path.vertices_cons, List.concat_eq_append,
      List.take_append_of_le_length (by simp)]
    exact ih





theorem boltzmannSdpUpper_presentPath_complete_cut {r : ℕ}
    (q : RightVertexMarkedBoltzmannSpace r) (j : Fin (q.1.1 + 1))
    (p : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j)) :
    ∃ n, ∃ C : SimpleDirectedDartPath q.1.2.2.out.B.map
        q.1.2.2.out.B.source q.1.2.2.out.B.sink n,
      ∃ k : Fin (n + 1),
        C.vertices.get ⟨k.val, by rw [C.vertices_length]; exact k.isLt⟩ =
            boltzmannSdpUpper_leftVertex q j ∧
          C.vertices.take (k.val + 1) = p.vertices := by
  let B := q.1.2.2.out.B
  obtain ⟨R, _, _⟩ := boltzmannSdpUpper_simple_exists_presentPath (B.leftPath.suffix j)
  change Quiver.Path (boltzmannSdpUpper_leftVertex q j) B.sink at R
  obtain ⟨C, hC⟩ := boltzmannSdpUpper_presentPath_exists_simple
    B.map B.acyclic (p.comp R)
  refine ⟨(p.comp R).length, C, ⟨p.length, by simp⟩, ?_, ?_⟩
  · change C.vertices[p.length]'(by rw [C.vertices_length]; simp) =
      boltzmannSdpUpper_leftVertex q j
    simpa only [hC, List.get_eq_getElem] using p.vertices_comp_get_length_eq R
  · rw [hC]
    exact strictCrossing_comp_take p R




private theorem strictCrossing_complete_pos {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (C : SimpleDirectedDartPath B.map B.source B.sink n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  have hst : B.source = B.sink := by
    subst n
    exact C.start_vertex.symm.trans C.end_vertex
  have heq := B.leftPath.start_vertex.trans (hst.trans B.leftPath.end_vertex.symm)
  have hidx := B.leftPath.vertices_nodup.get_inj_iff.mp heq
  have hval : (0 : ℕ) = ℓ := congrArg Fin.val hidx
  have hpos := B.left_length_pos
  omega




private theorem strictCrossing_seam_incident {ℓ r n : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (C : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ C.vertices) :
    ∃ d ∈ pathCutSeamDarts B C,
      v = dartTailVertex B.map d ∨ v = dartHeadVertex B.map d := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
  have hin : i.val ≤ n := by
    have h := i.isLt
    have hlen := C.vertices_length
    omega
  by_cases hlt : i.val < n
  · let d : Fin C.darts.length := ⟨i.val, by rw [C.darts_length]; exact hlt⟩
    refine ⟨C.darts.get d, Or.inl (List.get_mem _ _), Or.inl ?_⟩
    exact hi.symm.trans (C.edge_step d).2.2.1
  · have hpos := strictCrossing_complete_pos B C
    have heq : i.val = n := by omega
    let d : Fin C.darts.length := ⟨n - 1, by rw [C.darts_length]; omega⟩
    refine ⟨C.darts.get d, Or.inl (List.get_mem _ _), Or.inr ?_⟩
    have hs := (C.edge_step d).2.2.2
    have he : (⟨d.val + 1, by rw [C.vertices_length]; dsimp [d]; omega⟩ :
        Fin C.vertices.length) = i := by apply Fin.ext; dsimp [d]; omega
    rw [he] at hs
    exact hi.symm.trans hs






@[expose] def boltzmannSdpUpper_completeCutCrossing_OPEN : Prop :=
  ∀ r : ℕ, ∀ q : RightVertexMarkedBoltzmannSpace r,
    ∀ i j : Fin (q.1.1 + 1), i ≤ q.2 → q.2 ≤ j →
      0 < i.val → i.val < j.val → j.val < q.1.1 →
        ∀ n, ∀ C : SimpleDirectedDartPath q.1.2.2.out.B.map
            q.1.2.2.out.B.source q.1.2.2.out.B.sink n,
          ∀ k : Fin (n + 1),
            C.vertices.get ⟨k.val, by rw [C.vertices_length]; exact k.isLt⟩ =
                boltzmannSdpUpper_leftVertex q j →
              ∀ m, ∀ Q : SimpleDirectedDartPath q.1.2.2.out.B.map
                  (boltzmannSdpUpper_leftVertex q i) q.1.2.2.out.B.sink m,
                ∃ d ∈ pathCutSeamDarts q.1.2.2.out.B C,
                  ∃ v, (v = dartTailVertex q.1.2.2.out.B.map d ∨
                    v = dartHeadVertex q.1.2.2.out.B.map d) ∧
                    v ∈ C.vertices.take (k.val + 1) ∧ v ∈ Q.vertices




private theorem strictCrossing_cast_vertices {M : DirectedMapWithMissing D}
    {s t u : MapVertex M} (h : t = u) (p : Quiver.Path s t) :
    (h ▸ p).vertices = p.vertices := by
  subst u
  rfl




theorem boltzmannSdpUpper_strictBoundaryPathIntersection_iff_completeCut :
    boltzmannSdpUpper_strictBoundaryPathIntersection_OPEN ↔
      boltzmannSdpUpper_completeCutCrossing_OPEN := by
  constructor
  · intro h r q i j hi hj hi0 hij hjL n C k hk m Q
    obtain ⟨p, _, hp⟩ := boltzmannSdpUpper_simple_exists_presentPath (C.prefix k)
    obtain ⟨z, _, hz⟩ := boltzmannSdpUpper_simple_exists_presentPath Q
    let p' : Quiver.Path q.1.2.2.out.B.source (boltzmannSdpUpper_leftVertex q j) :=
      hk ▸ p
    obtain ⟨v, hv, hvQ⟩ := h r q i j hi hj hi0 hij hjL p' z
    have hp' : p'.vertices = C.vertices.take (k.val + 1) := by
      rw [strictCrossing_cast_vertices, hp, C.prefix_vertices]
    rw [hp'] at hv
    rw [hz] at hvQ
    obtain ⟨d, hd, hvd⟩ := strictCrossing_seam_incident q.1.2.2.out.B C
      (List.mem_of_mem_take hv)
    exact ⟨d, hd, v, hvd, hv, hvQ⟩
  · intro h r q i j hi hj hi0 hij hjL p z
    obtain ⟨n, C, k, hk, hp⟩ := boltzmannSdpUpper_presentPath_complete_cut q j p
    obtain ⟨Q, hQ⟩ := boltzmannSdpUpper_presentPath_exists_simple
      q.1.2.2.out.B.map q.1.2.2.out.B.acyclic z
    obtain ⟨d, hd, v, hvd, hv, hvQ⟩ := h r q i j hi hj hi0 hij hjL n C k hk z.length Q
    exact ⟨v, hp ▸ hv, hQ ▸ hvQ⟩





theorem boltzmannSdpUpper_boundaryPathIntersection_iff_completeCut :
    boltzmannSdpUpper_boundaryPathIntersection ↔
      boltzmannSdpUpper_completeCutCrossing_OPEN :=
  boltzmannSdpUpper_boundaryPathIntersection_iff_strict.trans
    boltzmannSdpUpper_strictBoundaryPathIntersection_iff_completeCut

end DirectedDistances.PaperProofs.Section7
