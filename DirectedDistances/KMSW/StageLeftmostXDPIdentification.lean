module

public import DirectedDistances.KMSW.StageDirectedMapPathLengths
public import DirectedDistances.PlanarMap.FiniteXDPCanonicalLeftmost
import DirectedDistances.PlanarMap.LexLeftmostBaseIso

/-! canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result.

Arbitrary stages may have missing edges. The path transport is stated for
arbitrary stages; the canonical bipolar selector is used only on the stages
of finite walk classes, where its base has already been constructed. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stagePath_reaches
    (M : DirectedMapWithMissing D) {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) :
    Relation.ReflTransGen M.directedStep s t := by
  induction n generalizing s t with
  | zero =>
      have hst : s = t := P.start_vertex.symm.trans P.end_vertex
      subst t
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      let iD : Fin P.darts.length := ⟨0, by rw [P.darts_length]; omega⟩
      let iV0 : Fin P.vertices.length := ⟨0, by rw [P.vertices_length]; omega⟩
      let iV1 : Fin P.vertices.length := ⟨1, by rw [P.vertices_length]; omega⟩
      let iN : Fin (n + 1 + 1) := ⟨1, by omega⟩
      have hstep := P.edge_step iD
      have hstepRel : M.directedStep s (P.vertices.get iV1) := by
        change ∃ e, ¬ M.missing e ∧ M.tail e ∧
          dartTailVertex M e = s ∧ dartHeadVertex M e = P.vertices.get iV1
        refine ⟨P.darts.get iD, hstep.1, hstep.2.1, ?_, ?_⟩
        · exact hstep.2.2.1.symm.trans P.start_vertex
        · exact hstep.2.2.2.symm
      have htail : SimpleDirectedDartPath M (P.vertices.get iV1) t n := by
        simpa [iV1, iN] using P.suffix iN
      exact (ih htail).head hstepRel

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem exists_simplePath_concatDart
    (M : DirectedMapWithMissing D) (hacyclic : M.IsAcyclic)
    {s x y t : MapVertex M} {n m : ℕ}
    (P : SimpleDirectedDartPath M s x n) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = x) (hhy : dartHeadVertex M d = y)
    (Q : SimpleDirectedDartPath M y t m) :
    ∃ R : SimpleDirectedDartPath M s t (n + 1 + m), d ∈ R.darts := by
  have hcross : ∀ a ∈ P.vertices, a ∉ Q.vertices := by
    intro a haP haQ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp haP
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp haQ
    let iN : Fin (n + 1) := ⟨i.val, by have hi := i.isLt; have hl := P.vertices_length; omega⟩
    let jN : Fin (m + 1) := ⟨j.val, by have hj := j.isLt; have hl := Q.vertices_length; omega⟩
    have hPi : P.vertices.get i =
        P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩ := by
      exact congrArg P.vertices.get (Fin.ext rfl)
    have hQj : Q.vertices.get j =
        Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩ := by
      exact congrArg Q.vertices.get (Fin.ext rfl)
    have hreachP : Relation.ReflTransGen M.directedStep
        (P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩) x :=
      stagePath_reaches M (P.suffix iN)
    have hreachQ : Relation.ReflTransGen M.directedStep y
        (Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩) :=
      stagePath_reaches M (Q.prefix jN)
    have hsame : P.vertices.get ⟨iN.val, by rw [P.vertices_length]; exact iN.isLt⟩ =
        Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩ := by
      rw [← hPi, ← hQj]
      exact hi.trans hj.symm
    have hreachP' : Relation.ReflTransGen M.directedStep
        (Q.vertices.get ⟨jN.val, by rw [Q.vertices_length]; exact jN.isLt⟩) x := by
      rw [← hsame]
      exact hreachP
    have hback : Relation.ReflTransGen M.directedStep y x := hreachQ.trans hreachP'
    have hstep : M.directedStep x y := ⟨d, hmiss, htail, hty, hhy⟩
    exact hacyclic x (Relation.TransGen.head' hstep hback)
  refine ⟨{
    darts := P.darts ++ (d :: Q.darts)
    vertices := P.vertices ++ Q.vertices
    darts_length := by
      simp only [List.length_append, List.length_cons, P.darts_length, Q.darts_length]
      ac_rfl
    vertices_length := by
      simp only [List.length_append, P.vertices_length, Q.vertices_length]
      ac_rfl
    vertices_nodup := by
      rw [List.nodup_append]
      exact ⟨P.vertices_nodup, Q.vertices_nodup, by
        intro a ha b hb hab
        exact hcross a ha (hab ▸ hb)⟩
    start_vertex := by
      simp [List.get_eq_getElem, P.vertices_length]
      exact P.start_vertex
    end_vertex := by
      simp [List.get_eq_getElem, P.vertices_length]
      exact Q.end_vertex
    edge_step := by
      intro i
      have hiBound : i.val < n + 1 + m := by
        have hi := i.isLt
        simp only [List.length_append, List.length_cons, P.darts_length, Q.darts_length] at hi
        omega
      by_cases hin : i.val < n
      · let jD : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hin⟩
        let jV0 : Fin P.vertices.length := ⟨i.val, by rw [P.vertices_length]; omega⟩
        let jV1 : Fin P.vertices.length := ⟨i.val + 1, by rw [P.vertices_length]; omega⟩
        have hD : (P.darts ++ d :: Q.darts).get i = P.darts.get jD := by
          change (P.darts ++ d :: Q.darts)[i.val]'i.isLt = P.darts[i.val]'jD.isLt
          exact List.getElem_append_left (by rw [P.darts_length]; exact hin)
        have hV0 : (P.vertices ++ Q.vertices).get ⟨i.val, by
            simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
            P.vertices.get jV0 := by
          change (P.vertices ++ Q.vertices)[i.val]'_ = P.vertices[i.val]'jV0.isLt
          exact List.getElem_append_left (by rw [P.vertices_length]; omega)
        have hV1 : (P.vertices ++ Q.vertices).get ⟨i.val + 1, by
            simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
            P.vertices.get jV1 := by
          change (P.vertices ++ Q.vertices)[i.val + 1]'_ = P.vertices[i.val + 1]'jV1.isLt
          exact List.getElem_append_left (by rw [P.vertices_length]; omega)
        rw [hD, hV0, hV1]
        exact P.edge_step jD
      · by_cases hieq : i.val = n
        · have hiFin : i = ⟨n, by
              simp [List.length_append, List.length_cons, P.darts_length,
                Q.darts_length]⟩ := Fin.ext hieq
          subst i
          have hD : (P.darts ++ d :: Q.darts).get ⟨n, by
              simp [List.length_append, List.length_cons, P.darts_length, Q.darts_length]⟩ = d := by
            simp [List.get_eq_getElem, P.darts_length]
          have hV0 : (P.vertices ++ Q.vertices).get ⟨n, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]
              omega⟩ = dartTailVertex M d := by
            calc
              (P.vertices ++ Q.vertices).get ⟨n, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]
                  omega⟩ = P.vertices.get ⟨n, by rw [P.vertices_length]; omega⟩ := by
                    change (P.vertices ++ Q.vertices)[n]'_ = P.vertices[n]'_
                    exact List.getElem_append_left (by rw [P.vertices_length]; omega)
              _ = x := P.end_vertex
              _ = dartTailVertex M d := hty.symm
          have hV1 : (P.vertices ++ Q.vertices).get ⟨n + 1, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]⟩ =
              dartHeadVertex M d := by
            calc
              (P.vertices ++ Q.vertices).get ⟨n + 1, by
                  simp [List.length_append, P.vertices_length, Q.vertices_length]⟩ =
                  Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ := by
                    change (P.vertices ++ Q.vertices)[n + 1]'_ = Q.vertices[0]'_
                    calc
                      (P.vertices ++ Q.vertices)[n + 1]'_ =
                          Q.vertices[n + 1 - P.vertices.length]'_ :=
                        List.getElem_append_right (by have hl := P.vertices_length; omega)
                      _ = Q.vertices[0]'_ := by
                        have hidx : n + 1 - P.vertices.length = 0 := by
                          have hl := P.vertices_length
                          omega
                        simp only [hidx]
              _ = y := Q.start_vertex
              _ = dartHeadVertex M d := hhy.symm
          exact ⟨by rw [hD]; exact hmiss, by rw [hD]; exact htail,
            by rw [hD, hV0], by rw [hD, hV1]⟩
        · have hgt : n < i.val := by omega
          let k : ℕ := i.val - (n + 1)
          have hk : k < m := by dsimp [k]; omega
          let jD : Fin Q.darts.length := ⟨k, by rw [Q.darts_length]; exact hk⟩
          let jV0 : Fin Q.vertices.length := ⟨k, by rw [Q.vertices_length]; omega⟩
          let jV1 : Fin Q.vertices.length := ⟨k + 1, by rw [Q.vertices_length]; omega⟩
          have hD : (P.darts ++ d :: Q.darts).get i = Q.darts.get jD := by
            change (P.darts ++ d :: Q.darts)[i.val]'i.isLt = Q.darts[k]'jD.isLt
            rw [List.getElem_append_right (by rw [P.darts_length]; omega)]
            have hidx : i.val - P.darts.length = k + 1 := by
              have hlen := P.darts_length
              dsimp [k]
              omega
            simp only [hidx, List.getElem_cons_succ]
          have hV0 : (P.vertices ++ Q.vertices).get ⟨i.val, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
              Q.vertices.get jV0 := by
            change (P.vertices ++ Q.vertices)[i.val]'_ = Q.vertices[k]'jV0.isLt
            rw [List.getElem_append_right (by rw [P.vertices_length]; omega)]
            have hidx : i.val - P.vertices.length = k := by
              have hlen := P.vertices_length
              dsimp [k]
              omega
            simp only [hidx]
          have hV1 : (P.vertices ++ Q.vertices).get ⟨i.val + 1, by
              simp [List.length_append, P.vertices_length, Q.vertices_length]; omega⟩ =
              Q.vertices.get jV1 := by
            change (P.vertices ++ Q.vertices)[i.val + 1]'_ = Q.vertices[k + 1]'jV1.isLt
            rw [List.getElem_append_right (by rw [P.vertices_length]; omega)]
            have hidx : i.val + 1 - P.vertices.length = k + 1 := by
              have hlen := P.vertices_length
              dsimp [k]
              omega
            simp only [hidx]
          rw [hD, hV0, hV1]
          exact Q.edge_step jD
  }, by simp [List.mem_append]⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageMap_path_through_dart_iff (w : ℕ → Fin 3) (n k : ℕ)
    (s t : MapVertex (kmswStageDirectedMap w n))
    (d : StageDart (kmswStage w n).nextEdge) :
    (∃ P : SimpleDirectedDartPath (kmswStageDirectedMap w n) s t k,
      d ∈ P.darts) ↔
      (kmswStageDirectedMap w n).tail d ∧
        ∃ p : Path (stageMapVertex w n s)
          (stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d)),
        ∃ q : Path (stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d))
          (stageMapVertex w n t), p.length + 1 + q.length = k := by
  constructor
  · rintro ⟨P, hd⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    have hs := P.edge_step i
    rw [hi] at hs
    have hik : i.val < k := by
      have := i.isLt
      have := P.darts_length
      omega
    let a : Fin (k + 1) := ⟨i.val, by omega⟩
    let b : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    have hp : Nonempty (SimpleDirectedDartPath (kmswStageDirectedMap w n) s
        (dartTailVertex (kmswStageDirectedMap w n) d) i.val) := by
      have P₁ := P.prefix a
      have hv : P.vertices.get ⟨a.val, by rw [P.vertices_length]; exact a.isLt⟩ =
          dartTailVertex (kmswStageDirectedMap w n) d := hs.2.2.1
      rw [hv] at P₁
      exact ⟨P₁⟩
    have hq : Nonempty (SimpleDirectedDartPath (kmswStageDirectedMap w n)
        (dartHeadVertex (kmswStageDirectedMap w n) d) t (k - (i.val + 1))) := by
      have P₂ := P.suffix b
      have hv : P.vertices.get ⟨b.val, by rw [P.vertices_length]; exact b.isLt⟩ =
          dartHeadVertex (kmswStageDirectedMap w n) d := hs.2.2.2
      rw [hv] at P₂
      exact ⟨P₂⟩
    obtain ⟨p, hp⟩ := (stageMap_path_iff w n _ _ _).1 hp
    obtain ⟨q, hq⟩ := (stageMap_path_iff w n _ _ _).1 hq
    exact ⟨hs.2.1, p, q, by omega⟩
  · rintro ⟨ht, p, q, hk⟩
    obtain ⟨P⟩ := (stageMap_path_iff w n p.length _ _).2 ⟨p, rfl⟩
    obtain ⟨Q⟩ := (stageMap_path_iff w n q.length _ _).2 ⟨q, rfl⟩
    have hpresent : (kmswStage w n).present d.1.val = true := ht.1
    have hm : ¬ (kmswStageDirectedMap w n).missing d := by
      change ¬ (kmswStage w n).present d.1.val = false
      rw [hpresent]
      decide
    obtain ⟨R, hR⟩ := exists_simplePath_concatDart (kmswStageDirectedMap w n)
      (kmswStageDirectedMap_isAcyclic w n) P d hm ht rfl rfl Q
    subst k
    exact ⟨R, hR⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stageMap_extremal_dart_iff (w : ℕ → Fin 3) (n : ℕ)
    (s t : MapVertex (kmswStageDirectedMap w n)) (x : XDP)
    (d : StageDart (kmswStage w n).nextEdge) :
    (∃ k, ∃ P : SimpleDirectedDartPath (kmswStageDirectedMap w n) s t k,
      d ∈ P.darts ∧
        (match x with
        | .ldp => ∀ m, SimpleDirectedDartPath (kmswStageDirectedMap w n) s t m → m ≤ k
        | .sdp => ∀ m, SimpleDirectedDartPath (kmswStageDirectedMap w n) s t m → k ≤ m)) ↔
    (kmswStageDirectedMap w n).tail d ∧
      ∃ e : stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d) ⟶
        stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d),
      e.val = d.1.val ∧
      ∃ p : Path (stageMapVertex w n s)
        (stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d)),
      ∃ q : Path (stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d))
        (stageMapVertex w n t),
      (match x with
      | .ldp => IsLongest ((p.cons e).comp q)
      | .sdp => IsShortest ((p.cons e).comp q)) := by
  constructor
  · rintro ⟨k, P, hd, hmax⟩
    obtain ⟨ht, p, q, hk⟩ := (stageMap_path_through_dart_iff w n k s t d).1 ⟨P, hd⟩
    have hm : ¬ (kmswStageDirectedMap w n).missing d := by
      change ¬ (kmswStage w n).present d.1.val = false
      rw [ht.1]
      decide
    have ha := (stageMap_dart_arrow_iff w n d _ _).1 ⟨hm, ht, rfl, rfl⟩
    let e : stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d) ⟶
        stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d) :=
      ⟨d.1.val, d.1.isLt, ha.2⟩
    refine ⟨ht, e, rfl, p, q, ?_⟩
    have hlen : ((p.cons e).comp q).length = k := by
      simpa only [Path.length_comp, Path.length_cons] using hk
    cases x with
    | ldp =>
      intro r
      obtain ⟨R⟩ := (stageMap_path_iff w n r.length s t).2 ⟨r, rfl⟩
      rw [hlen]
      exact hmax r.length R
    | sdp =>
      intro r
      obtain ⟨R⟩ := (stageMap_path_iff w n r.length s t).2 ⟨r, rfl⟩
      rw [hlen]
      exact hmax r.length R
  · rintro ⟨ht, e, _, p, q, hmax⟩
    let k := p.length + 1 + q.length
    obtain ⟨P, hd⟩ := (stageMap_path_through_dart_iff w n k s t d).2
      ⟨ht, p, q, rfl⟩
    refine ⟨k, P, hd, ?_⟩
    have hlen : ((p.cons e).comp q).length = k := by
      simp only [Path.length_comp, Path.length_cons, k]
    cases x with
    | ldp =>
      intro m Q
      obtain ⟨r, hr⟩ := (stageMap_path_iff w n m s t).1 ⟨Q⟩
      have hh := hmax r
      rw [hr, hlen] at hh
      exact hh
    | sdp =>
      intro m Q
      obtain ⟨r, hr⟩ := (stageMap_path_iff w n m s t).1 ⟨Q⟩
      have hh := hmax r
      rw [hr, hlen] at hh
      exact hh

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stageLR_head_zero (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem walkClassBase_labels {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).source = ⟨0⟩ ∧
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).sink =
      ⟨(kmswStage (codeExtend c) (n - 1)).east
        (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  have hf := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hf
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL,
    _, _, _, _, _⟩
  constructor
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    change s.west (s.UL.head _) = 0
    have hs := (kmswStage_boundary_chain_invariant w m).2.2.1
    have hUL := (kmswStage_UL_nonempty_active_last w m).1
    have h0 := (initial_edge_endpoints w m).1
    change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at hs
    have hURs : s.UR = [] := hUR
    have hLLs : s.LL = [] := hLL
    rw [hURs, hLLs, List.append_nil, List.nil_append] at hs
    have huhead : s.UL.head? = some (s.UL.head hUL) := List.head?_eq_some_head hUL
    have hrhead : s.LR.head? = some 0 := stageLR_head_zero w m
    change s.UL.head?.map s.west = s.LR.head?.map s.west at hs
    rw [huhead, hrhead] at hs
    exact (Option.some.inj hs).trans h0
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    have hLR := kmswStage_LR_nonempty w m
    have ha := (kmswStage_boundary_chain_invariant w m).2.2.2.2.2.2 hLR hUR
    rw [ha]
    change stageEndpoint s ((kmswStageLRDartRun w m).head _) = _
    simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, List.head_reverse, ↓reduceIte]
    rfl

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
@[expose] def StageCodeXDPEligible (w : ℕ → Fin 3) (n : ℕ) (x : XDP)
    (s t : StagePresentVertex w n) (edgeId : ℕ) : Prop :=
  ∃ (a b : StagePresentVertex w n) (e : a ⟶ b), e.val = edgeId ∧
    ∃ (p : Path s a) (q : Path b t),
      match x with
      | .ldp => IsLongest ((p.cons e).comp q)
      | .sdp => IsShortest ((p.cons e).comp q)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stageCodeXDPEligible_endpoints (w : ℕ → Fin 3) (n : ℕ) (x : XDP)
    (s t : StagePresentVertex w n) (d : StageDart (kmswStage w n).nextEdge)
    (ht : (kmswStageDirectedMap w n).tail d) :
    StageCodeXDPEligible w n x s t d.1.val ↔
      ∃ e : stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d) ⟶
        stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d),
      e.val = d.1.val ∧
      ∃ p : Path s (stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d)),
      ∃ q : Path (stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d)) t,
      (match x with
      | .ldp => IsLongest ((p.cons e).comp q)
      | .sdp => IsShortest ((p.cons e).comp q)) := by
  have hm : ¬ (kmswStageDirectedMap w n).missing d := by
    change ¬ (kmswStage w n).present d.1.val = false
    rw [ht.1]
    decide
  have hd := (stageMap_dart_arrow_iff w n d _ _).1 ⟨hm, ht, rfl, rfl⟩
  constructor
  · rintro ⟨a, b, e, he, p, q, h⟩
    have ha : a = stageMapVertex w n (dartTailVertex (kmswStageDirectedMap w n) d) := by
      have hval := e.property.2.2.1
      rw [he, hd.2.2.1] at hval
      exact congrArg StagePresentVertex.mk hval.symm
    have hb : b = stageMapVertex w n (dartHeadVertex (kmswStageDirectedMap w n) d) := by
      have hval := e.property.2.2.2
      rw [he, hd.2.2.2] at hval
      exact congrArg StagePresentVertex.mk hval.symm
    subst a
    subst b
    exact ⟨e, he, p, q, h⟩
  · rintro ⟨e, he, p, q, h⟩
    exact ⟨_, _, e, he, p, q, h⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stageMap_extremal_dart_iff_code (w : ℕ → Fin 3) (n : ℕ)
    (s t : MapVertex (kmswStageDirectedMap w n)) (x : XDP)
    (d : StageDart (kmswStage w n).nextEdge) :
    (∃ k, ∃ P : SimpleDirectedDartPath (kmswStageDirectedMap w n) s t k,
      d ∈ P.darts ∧
        (match x with
        | .ldp => ∀ m, SimpleDirectedDartPath (kmswStageDirectedMap w n) s t m → m ≤ k
        | .sdp => ∀ m, SimpleDirectedDartPath (kmswStageDirectedMap w n) s t m → k ≤ m)) ↔
    (kmswStageDirectedMap w n).tail d ∧
      StageCodeXDPEligible w n x (stageMapVertex w n s) (stageMapVertex w n t) d.1.val := by
  exact (stageMap_extremal_dart_iff w n s t x d).trans
    (and_congr_right fun ht => (stageCodeXDPEligible_endpoints w n x _ _ d ht).symm)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem xdp_extremal_iff {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) {k : ℕ}
    (P : SimpleDirectedDartPath B.map B.source B.sink k) :
    IsXDPGeodesicBase B x P ↔
      (match x with
      | .ldp => ∀ m, SimpleDirectedDartPath B.map B.source B.sink m → m ≤ k
      | .sdp => ∀ m, SimpleDirectedDartPath B.map B.source B.sink m → k ≤ m) := by
  cases x <;> rfl

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_isXDPGeodesicDart_iff {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
    IsXDPGeodesicDart (kmswWalkClassBase hN c) x d ↔
      (kmswStageDirectedMap (codeExtend c) (N - 1)).tail d ∧
        StageCodeXDPEligible (codeExtend c) (N - 1) x ⟨0⟩
          ⟨(kmswStage (codeExtend c) (N - 1)).east
            (kmswStage (codeExtend c) (N - 1)).active⟩ d.1.val := by
  let w := codeExtend c
  let n := N - 1
  let B := kmswWalkClassBase hN c
  have h := stageMap_extremal_dart_iff w n B.source B.sink x d
  have hh : IsXDPGeodesicDart B x d ↔
      (kmswStageDirectedMap w n).tail d ∧
        StageCodeXDPEligible w n x (stageMapVertex w n B.source)
          (stageMapVertex w n B.sink) d.1.val := by
    rw [IsXDPGeodesicDart]
    constructor
    · rintro ⟨k, P, hP, hd⟩
      have hmax := (xdp_extremal_iff B x P).1 hP
      obtain ⟨ht, he⟩ := h.1 ⟨k, P, hd, hmax⟩
      exact ⟨ht, (stageCodeXDPEligible_endpoints w n x _ _ d ht).2 he⟩
    · rintro ⟨ht, he⟩
      obtain ⟨k, P, hd, hmax⟩ := h.2
        ⟨ht, (stageCodeXDPEligible_endpoints w n x _ _ d ht).1 he⟩
      refine ⟨k, P, ?_, hd⟩
      exact (xdp_extremal_iff B x P).2 hmax
  rw [(walkClassBase_labels hN c).1, (walkClassBase_labels hN c).2] at hh
  exact hh

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
@[expose] noncomputable def stageOutgoingDartOrder (w : ℕ → Fin 3) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge) :
    List (StageDart (kmswStage w n).nextEdge) := by
  classical
  exact ((List.ofFn fun i : Fin (orderOf (stageRot w n).symm) =>
    ((stageRot w n).symm ^ i.val) corner).filter fun d =>
      stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) corner ∧
        (kmswStage w n).present d.1.val = true ∧ d.2 = false).eraseDups

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
@[expose] noncomputable def stageOutgoingEdgeOrder (w : ℕ → Fin 3) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge) : List ℕ :=
  (stageOutgoingDartOrder w n corner).map (fun d => d.1.val)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem stage_tailVertex_eq_iff (w : ℕ → Fin 3) (n : ℕ)
    (d e : StageDart (kmswStage w n).nextEdge) :
    dartTailVertex (kmswStageDirectedMap w n) d =
      dartTailVertex (kmswStageDirectedMap w n) e ↔
        stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) e := by
  constructor
  · intro h
    exact congrArg (fun v => (stageMapVertex w n v).id) h
  · intro h
    apply stageMapVertex_injective w n
    exact congrArg StagePresentVertex.mk h

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_canonicalOutgoingOrder_eq {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (v : MapVertex (kmswStageDirectedMap (codeExtend c) (N - 1)))
    (hvs : v ≠ (kmswWalkClassBase hN c).sink) :
    canonicalOutgoingOrder (kmswWalkClassBase hN c) v hvs =
      stageOutgoingDartOrder (codeExtend c) (N - 1)
        (leftmostOutgoing (kmswWalkClassBase hN c) v hvs) := by
  classical
  unfold canonicalOutgoingOrder finiteOutgoingRotationOrder finiteRotationScan
    stageOutgoingDartOrder
  congr 2
  funext d
  change decide
    (dartTailVertex (kmswStageDirectedMap (codeExtend c) (N - 1)) d =
      dartTailVertex (kmswStageDirectedMap (codeExtend c) (N - 1))
        (leftmostOutgoing (kmswWalkClassBase hN c) v hvs) ∧
      (kmswStageDirectedMap (codeExtend c) (N - 1)).tail d) = _
  simp only [stage_tailVertex_eq_iff]
  exact Bool.decide_congr Iff.rfl

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem walkStage_tail_iff {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
    (kmswWalkClassBase hN c).map.tail d ↔ d.2 = false := by
  have hm := (kmswWalkClassBase hN c).noMissingDarts d
  change ¬ (kmswStage (codeExtend c) (N - 1)).present d.1.val = false at hm
  have hp : (kmswStage (codeExtend c) (N - 1)).present d.1.val = true := by
    cases h : (kmswStage (codeExtend c) (N - 1)).present d.1.val
    · exact (hm h).elim
    · rfl
  change (_ ∧ _) ↔ _
  rw [hp]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_leftmostOutgoing_internal_iff {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N)
    (v : MapVertex (kmswStageDirectedMap (codeExtend c) (N - 1)))
    (hs : v ≠ (kmswWalkClassBase hN c).source)
    (ht : v ≠ (kmswWalkClassBase hN c).sink)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
    d = leftmostOutgoing (kmswWalkClassBase hN c) v ht ↔
      stageEndpoint (kmswStage (codeExtend c) (N - 1)) d =
          (stageMapVertex (codeExtend c) (N - 1) v).id ∧
        d.2 = false ∧ (stageRot (codeExtend c) (N - 1) d).2 = true := by
  let B := kmswWalkClassBase hN c
  have hchar := leftmostOutgoing_internal_characterization B v hs ht
  have hv (e : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
      dartTailVertex B.map e = v ↔
        stageEndpoint (kmswStage (codeExtend c) (N - 1)) e =
          (stageMapVertex (codeExtend c) (N - 1) v).id := by
    constructor
    · intro h
      exact congrArg (fun u => (stageMapVertex (codeExtend c) (N - 1) u).id) h
    · intro h
      apply stageMapVertex_injective (codeExtend c) (N - 1)
      exact congrArg StagePresentVertex.mk h
  have hp (e : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) :
      ¬ B.map.tail (B.map.toCombinatorialMap.rot e) ↔
        (stageRot (codeExtend c) (N - 1) e).2 = true := by
    rw [walkStage_tail_iff hN c]
    change (¬ (stageRot (codeExtend c) (N - 1) e).2 = false) ↔ _
    cases (stageRot (codeExtend c) (N - 1) e).2 <;> decide
  constructor
  · intro h
    subst d
    exact ⟨(hv _).1 hchar.1, (walkStage_tail_iff hN c _).1 hchar.2.1,
      (hp _).1 hchar.2.2.1⟩
  · rintro ⟨hlabel, hout, hprev⟩
    exact hchar.2.2.2 d ((hv d).2 hlabel) ((walkStage_tail_iff hN c d).2 hout)
      ((hp d).2 hprev)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_leftmostOutgoing_source {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) :
    leftmostOutgoing (kmswWalkClassBase hN c) (kmswWalkClassBase hN c).source
        (bipolar_source_ne_sink (kmswWalkClassBase hN c)) =
      stageULHeadDart (codeExtend c) (N - 1) := by
  rw [leftmostOutgoing_source_eq_firstLeftDart]
  have hp := kmswWalkClassBase_paths hN c
  have hd := (Classical.choose_spec (Classical.choose_spec hp)).1
  have hne : (Classical.choose hp).darts ≠ [] := by
    intro he
    have hlen := (Classical.choose hp).darts_length
    rw [he] at hlen
    have := (kmswWalkClassBase hN c).left_length_pos
    simp only [List.length_nil] at hlen
    omega
  have hh := congrArg List.head? hd
  rw [List.head?_eq_some_head hne] at hh
  have hUL := (kmswStage_UL_nonempty_active_last (codeExtend c) (N - 1)).1
  have hs : (kmswStageULDartRun (codeExtend c) (N - 1)).head? =
      some (stageULHeadDart (codeExtend c) (N - 1)) := by
    simp only [kmswStageULDartRun, stageDarts, List.head?_map, List.head?_attach,
      List.head?_eq_some_head hUL]
    rfl
  rw [hs] at hh
  have hhead := Option.some.inj hh
  change (Classical.choose hp).darts.get ⟨0, _⟩ = _
  simpa only [List.head_eq_getElem, List.get_eq_getElem] using hhead


/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
@[expose] noncomputable def stageEligibleOutgoingEdgeOrder (w : ℕ → Fin 3) (n : ℕ)
    (x : XDP) (s t : StagePresentVertex w n)
    (corner : StageDart (kmswStage w n).nextEdge) : List ℕ := by
  classical
  exact (stageOutgoingEdgeOrder w n corner).filter (fun e =>
    decide (StageCodeXDPEligible w n x s t e))

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_canonicalXDPGeodesicDartOrder_map {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP)
    (v : MapVertex (kmswStageDirectedMap (codeExtend c) (N - 1)))
    (hvs : v ≠ (kmswWalkClassBase hN c).sink) :
    (canonicalXDPGeodesicDartOrder (kmswWalkClassBase hN c) x v hvs).map
        (fun d => d.1.val) =
      stageEligibleOutgoingEdgeOrder (codeExtend c) (N - 1) x ⟨0⟩
        ⟨(kmswStage (codeExtend c) (N - 1)).east
          (kmswStage (codeExtend c) (N - 1)).active⟩
        (leftmostOutgoing (kmswWalkClassBase hN c) v hvs) := by
  classical
  unfold stageEligibleOutgoingEdgeOrder stageOutgoingEdgeOrder
  rw [← stage_canonicalOutgoingOrder_eq hN c v hvs, List.filter_map]
  unfold canonicalXDPGeodesicDartOrder
  congr 1
  apply List.filter_congr
  intro d hd
  apply Bool.decide_congr
  have ht := ((mem_canonicalOutgoingOrder_iff (kmswWalkClassBase hN c) v hvs d).1 hd).2
  exact (stage_isXDPGeodesicDart_iff hN c x d).trans (and_iff_right ht)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem stage_canonicalLeftmostXDPStep_first {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP)
    (v : MapVertex (kmswStageDirectedMap (codeExtend c) (N - 1)))
    (hv : ∃ k, ∃ P : SimpleDirectedDartPath (kmswWalkClassBase hN c).map
      (kmswWalkClassBase hN c).source (kmswWalkClassBase hN c).sink k,
      IsXDPGeodesicBase (kmswWalkClassBase hN c) x P ∧ v ∈ P.vertices)
    (hvs : v ≠ (kmswWalkClassBase hN c).sink) :
    ∃ rest, stageEligibleOutgoingEdgeOrder (codeExtend c) (N - 1) x ⟨0⟩
      ⟨(kmswStage (codeExtend c) (N - 1)).east
        (kmswStage (codeExtend c) (N - 1)).active⟩
      (leftmostOutgoing (kmswWalkClassBase hN c) v hvs) =
        (canonicalLeftmostXDPStep (kmswWalkClassBase hN c) x v).1.val :: rest := by
  obtain ⟨rest, hfirst, _⟩ := canonicalLeftmostXDPStep_first
    (kmswWalkClassBase hN c) x v hv hvs
  rw [← stage_canonicalXDPGeodesicDartOrder_map hN c x v hvs, hfirst, List.map_cons]
  exact ⟨_, rfl⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private noncomputable def repStageBaseIso {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) :
    BipolarBoundaryBaseIso (kmswWalkClassRep hN c).B (kmswWalkClassBase hN c) :=
  ((kmswWalkClassBase hN c).transportIso (Fintype.equivFin _)).symm

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem geoDart_map_iff {E : Type*} [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) (d : D) :
    IsXDPGeodesicDart B' x (I.toEquiv d) ↔ IsXDPGeodesicDart B x d := by
  constructor
  · rintro ⟨k, P, hP, hd⟩
    refine ⟨k, I.symm.mapPath P, (isXDPGeodesicBase_iff_mapPath I.symm x P).2 hP, ?_⟩
    rw [BipolarBoundaryBaseIso.mapPath_darts]
    exact List.mem_map.mpr ⟨I.toEquiv d, hd, I.toEquiv.symm_apply_apply d⟩
  · rintro ⟨k, P, hP, hd⟩
    refine ⟨k, I.mapPath P, (isXDPGeodesicBase_iff_mapPath I x P).2 hP, ?_⟩
    rw [BipolarBoundaryBaseIso.mapPath_darts]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem kmswWalkClassRep_isXDPGeodesicDart_iff_stage {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP) (d : Fin (kmswWalkClassRep hN c).dartCount) :
    IsXDPGeodesicDart (kmswWalkClassRep hN c).B x d ↔
      (kmswStageDirectedMap (codeExtend c) (N - 1)).tail
          ((kmswWalkClassRep_mapIso hN c).toEquiv d) ∧
        StageCodeXDPEligible (codeExtend c) (N - 1) x ⟨0⟩
          ⟨(kmswStage (codeExtend c) (N - 1)).east
            (kmswStage (codeExtend c) (N - 1)).active⟩
          ((kmswWalkClassRep_mapIso hN c).toEquiv d).1.val := by
  exact (geoDart_map_iff (repStageBaseIso hN c) x d).symm.trans
    (stage_isXDPGeodesicDart_iff hN c x ((repStageBaseIso hN c).toEquiv d))

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem kmswWalkClassRep_canonicalOutgoingOrder_map_stage {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (v : MapVertex (kmswWalkClassRep hN c).B.map)
    (hvs : v ≠ (kmswWalkClassRep hN c).B.sink) :
    (canonicalOutgoingOrder (kmswWalkClassRep hN c).B v hvs).map
        (fun d => ((kmswWalkClassRep_mapIso hN c).toEquiv d).1.val) =
      stageOutgoingEdgeOrder (codeExtend c) (N - 1)
        ((kmswWalkClassRep_mapIso hN c).toEquiv
          (leftmostOutgoing (kmswWalkClassRep hN c).B v hvs)) := by
  let I := repStageBaseIso hN c
  have horder := canonicalOutgoingOrder_map I v hvs
  have hleft := leftmostOutgoing_map I v hvs
  unfold stageOutgoingEdgeOrder
  change ((canonicalOutgoingOrder (kmswWalkClassRep hN c).B v hvs).map
    (fun d => (I.toEquiv d).1.val)) = _
  calc
    _ = ((canonicalOutgoingOrder (kmswWalkClassRep hN c).B v hvs).map I.toEquiv).map
        (fun d => d.1.val) := by simp only [List.map_map, Function.comp_def]
    _ = _ := by
      rw [← horder]
      rw [stage_canonicalOutgoingOrder_eq hN c (I.vertexEquiv v)
        (by intro h; exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm)))]
      rw [← hleft]
      rfl

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
private theorem canonicalXDPOrder_map {E : Type*} [Fintype E] [DecidableEq E]
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B B') (x : XDP) (v : MapVertex B.map)
    (hvs : v ≠ B.sink) :
    canonicalXDPGeodesicDartOrder B' x (I.vertexEquiv v)
        (by intro h; exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm))) =
      (canonicalXDPGeodesicDartOrder B x v hvs).map I.toEquiv := by
  classical
  unfold canonicalXDPGeodesicDartOrder
  rw [canonicalOutgoingOrder_map I v hvs, List.filter_map]
  congr 1
  apply List.filter_congr
  intro d _
  exact Bool.decide_congr (geoDart_map_iff I x d)

/-- canonical leftmost XDP geodesic of the KMSW stage map versus stage code-graph
paths; renewal times T_m, F4c and both-mode scope are not treated; not the paper result. -/
theorem kmswWalkClassRep_canonicalLeftmostXDPStep_first_stage {ℓ r N : ℕ}
    (hN : 1 ≤ N) (c : KMSWWalkClass ℓ r N) (x : XDP)
    (v : MapVertex (kmswWalkClassRep hN c).B.map)
    (hv : ∃ k, ∃ P : SimpleDirectedDartPath (kmswWalkClassRep hN c).B.map
      (kmswWalkClassRep hN c).B.source (kmswWalkClassRep hN c).B.sink k,
      IsXDPGeodesicBase (kmswWalkClassRep hN c).B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ (kmswWalkClassRep hN c).B.sink) :
    ∃ rest, stageEligibleOutgoingEdgeOrder (codeExtend c) (N - 1) x ⟨0⟩
      ⟨(kmswStage (codeExtend c) (N - 1)).east
        (kmswStage (codeExtend c) (N - 1)).active⟩
      ((kmswWalkClassRep_mapIso hN c).toEquiv
        (leftmostOutgoing (kmswWalkClassRep hN c).B v hvs)) =
      ((kmswWalkClassRep_mapIso hN c).toEquiv
        (canonicalLeftmostXDPStep (kmswWalkClassRep hN c).B x v)).1.val :: rest := by
  let I := repStageBaseIso hN c
  have hleft := leftmostOutgoing_map I v hvs
  obtain ⟨rest, hfirst, _⟩ := canonicalLeftmostXDPStep_first
    (kmswWalkClassRep hN c).B x v hv hvs
  change ∃ rest, stageEligibleOutgoingEdgeOrder _ _ _ _ _
    (I.toEquiv (leftmostOutgoing _ v hvs)) =
      (I.toEquiv (canonicalLeftmostXDPStep _ x v)).1.val :: rest
  rw [hleft]
  rw [← stage_canonicalXDPGeodesicDartOrder_map hN c x (I.vertexEquiv v)
    (by intro h; exact hvs (I.vertexEquiv.injective (h.trans I.vertexEquiv_sink.symm)))]
  rw [canonicalXDPOrder_map I x v hvs, hfirst, List.map_cons, List.map_cons]
  exact ⟨_, rfl⟩

end DirectedDistances.KMSW
