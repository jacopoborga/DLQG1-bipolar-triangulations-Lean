/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.PlanarPathCutSeparation
public import DirectedDistances.PlanarMap.FiniteXDPOrderCertification
public import DirectedDistances.PlanarMap.FiniteXDPLeftmostLocal

/-! # Geodesics and the left region of a path cut

not the paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r n : ℕ}

/-- A side coloring has the same value on consecutive `rot.symm` darts at a
vertex when the intervening edge is not on the cut and is not an outer dart.
This is a local ingredient toward the outgoing-order description in
not the paper result. -/
theorem pathCutSide_eq_rotSymm_of_inner_offSeam
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    (d : D)
    (hinner : ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv d))
    (hseam : d ∉ pathCutSeamDarts B P) :
    side (B.map.toCombinatorialMap.rot.symm d) = side d := by
  calc
    side (B.map.toCombinatorialMap.rot.symm d) =
        side (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.edgeInv d)) := by
      rw [(corner_consecutiveDarts B (B.map.toCombinatorialMap.edgeInv d)).1]
      simp only [B.map.toCombinatorialMap.edgeInv_invol]
    _ = side (B.map.toCombinatorialMap.edgeInv d) := hface _ hinner
    _ = side d := hedge d hseam

/-- Membership in the left closure is exactly the left color of any coloring
that separates the two closures. This is a helper
toward the local region comparison for `lem-lr-ind` and `def-geodesic` -/
theorem pathCutLeft_mem_iff_side_true_of_sideColoring
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (side : D → Bool)
    (hleft : ∀ d, d ∈ pathCutLeftSeeds B P → side d = true)
    (hright : ∀ d, d ∈ pathCutRightSeeds B P → side d = false)
    (hface : ∀ d, ¬ B.map.IsOuter d →
      side (B.map.toCombinatorialMap.faceSucc d) = side d)
    (hedge : ∀ d, d ∉ pathCutSeamDarts B P →
      side (B.map.toCombinatorialMap.edgeInv d) = side d)
    (d : D) :
    d ∈ pathCutLeftDarts B P ↔ side d = true := by
  have hleftClosure (d : D) (hd : d ∈ pathCutLeftDarts B P) : side d = true := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hleft a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hcut⟩
        · exact (hface b hinner).trans ih
        · exact hleft _ (.inl hnext)
        · exact (hedge b hcut).trans ih
  have hrightClosure (d : D) (hd : d ∈ pathCutRightDarts B P) : side d = false := by
    obtain ⟨a, ha, hreach⟩ := hd
    induction hreach with
    | refl => exact hright a ha
    | @tail b c _ hstep ih =>
        rcases hstep with ⟨rfl, hinner | ⟨_, hnext⟩⟩ | ⟨rfl, hcut⟩
        · exact (hface b hinner).trans ih
        · exact hright _ (.inl hnext)
        · exact (hedge b hcut).trans ih
  constructor
  · exact hleftClosure d
  · intro hcolor
    rcases pathCut_darts_cover B P d with hleftDart | hrightDart
    · exact hleftDart
    · have hfalse := hrightClosure d hrightDart
      rw [hcolor] at hfalse
      cases hfalse

private theorem headVertex_mem_boundary_of_outer
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    dartHeadVertex B.map d ∈ B.leftPath.vertices ∨
      dartHeadVertex B.map d ∈ B.rightPath.vertices := by
  rcases (isOuter_iff_mem_outerArcs B d).mp hd with hleft | hright
  · have hpath := (mem_pathCutLeftOuterArc_iff B d).mp hleft
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpath
    have hstep := B.leftPath.edge_step i
    left
    rw [← hi]
    rw [← hstep.2.2.2]
    exact List.get_mem _ _
  · have hpath := (mem_pathCutRightOuterArc_iff B d).mp hright
    rcases List.mem_map.mp hpath with ⟨p, hp, hpeq⟩
    have hp' : p ∈ B.rightPath.darts := List.mem_reverse.mp hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp'
    have hstep := B.rightPath.edge_step i
    right
    have hhead : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv p) =
        dartTailVertex B.map p := by
      simp [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol]
    rw [← hpeq, hhead, ← hi, ← hstep.2.2.1]
    exact List.get_mem _ _

private theorem outgoing_outer_edge_eq_rightmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {v : MapVertex B.map} {q : D} (ht : v ≠ B.sink)
    (hqv : dartTailVertex B.map q = v) (hqt : B.map.tail q)
    (houter : B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q)) :
    q = rightmostOutgoing B v ht := by
  have hnotTail : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv q) :=
    (B.map.tail_iff q (B.noMissingDarts q)).mp hqt
  rcases (isOuter_iff_mem_outerArcs B _).mp houter with hleft | hright
  · have hleftPath : B.map.toCombinatorialMap.edgeInv q ∈ B.leftPath.darts :=
      (mem_pathCutLeftOuterArc_iff B _).mp hleft
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hleftPath
    have hleftTail : B.map.tail (B.map.toCombinatorialMap.edgeInv q) := by
      rw [← hj]
      exact (B.leftPath.edge_step j).2.1
    exact (hnotTail hleftTail).elim
  · rcases List.mem_map.mp ((mem_pathCutRightOuterArc_iff B _).mp hright) with
      ⟨p, hp, hpq⟩
    have hpPath : p ∈ B.rightPath.darts := List.mem_reverse.mp hp
    have hpEq : p = q := by
      calc
        p = B.map.toCombinatorialMap.edgeInv
            (B.map.toCombinatorialMap.edgeInv p) :=
          (B.map.toCombinatorialMap.edgeInv_invol p).symm
        _ = B.map.toCombinatorialMap.edgeInv
            (B.map.toCombinatorialMap.edgeInv q) :=
          congrArg B.map.toCombinatorialMap.edgeInv hpq
        _ = q := B.map.toCombinatorialMap.edgeInv_invol q
    have hqPath : q ∈ B.rightPath.darts := hpEq ▸ hpPath
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hqPath
    have hjlt : j.val < r := by simpa [B.rightPath.darts_length] using j.isLt
    have hstep := B.rightPath.edge_step j
    have hjv : B.rightPath.vertices.get
        ⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩ = v := by
      calc
        B.rightPath.vertices.get
            ⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩ =
            dartTailVertex B.map (B.rightPath.darts.get j) := hstep.2.2.1
        _ = dartTailVertex B.map q :=
          congrArg (dartTailVertex B.map) hj
        _ = v := hqv
    have hrightmost := rightPath_edge_eq_rightmostOutgoing B j.val hjlt
    calc
      q = B.rightPath.darts.get j := hj.symm
      _ = rightmostOutgoing B v ht := by
        simpa only [hjv] using hrightmost

/-- A local sector argument used for interior and boundary path vertices.
Helper toward `lem-lr-ind` and `def-geodesic` -/
private theorem eraseDups_of_nodup_region
    {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (hl : l.Nodup) :
    l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, ht⟩
      rw [List.eraseDups_cons]
      have hfilter : t.filter (fun b => !(b == a)) = t := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hba : b ≠ a := by
          intro hba
          exact ha (hba ▸ hb)
        simp [hba]
      rw [hfilter, ih ht]

/-- The source outgoing order lists the rotation block from the first left
boundary dart through the first right boundary dart. Helper toward
not the paper result. -/
private theorem canonicalOutgoingOrder_source_eq_iterate_prefix_with_endpoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    ∃ k,
      canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B) =
        List.ofFn (fun i : Fin (k + 1) =>
          B.map.toCombinatorialMap.rot.symm^[i.val]
            (leftmostOutgoing B B.source (bipolar_source_ne_sink B))) ∧
      B.map.toCombinatorialMap.rot.symm^[k]
          (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) =
        rightmostOutgoing B B.source (bipolar_source_ne_sink B) := by
  classical
  let p := B.map.toCombinatorialMap.rot.symm
  let x := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  have hperiodExists : ∃ t, 0 < t ∧ p^[t] x = x := by
    refine ⟨orderOf p, orderOf_pos p, ?_⟩
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  let T := Nat.find hperiodExists
  have hTpos : 0 < T := (Nat.find_spec hperiodExists).1
  have hperiod : p^[T] x = x := (Nat.find_spec hperiodExists).2
  have hTle : T ≤ orderOf p := Nat.find_min' hperiodExists
    ⟨orderOf_pos p, by
      rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
      rfl⟩
  let k := T - 1
  have hkT : k + 1 = T := by dsimp [k]; omega
  have hk : k < orderOf p := by dsimp [k]; omega
  have hxv : dartTailVertex B.map x = B.source :=
    (canonicalLeftmostOutgoing_spec B B.source (bipolar_source_ne_sink B)).1
  have hvertexIter : ∀ j, dartTailVertex B.map (p^[j] x) = B.source := by
    intro j
    induction j with
    | zero => simpa [p, x] using hxv
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B B.source ⟨p^[j] x, ih⟩
  have hsourceCycle (q : D) (hqv : dartTailVertex B.map q = B.source) :
      Equiv.Perm.SameCycle p x q := by
    apply Equiv.Perm.sameCycle_inv.mpr
    exact Quotient.exact (hxv.trans hqv.symm)
  have hiterMod (a : ℕ) : p^[a] x = p^[a % T] x := by
    have hdecomp := Nat.mod_add_div a T
    calc
      p^[a] x = p^[a % T + T * (a / T)] x := by
        exact congrArg (fun j => p^[j] x) hdecomp.symm
      _ = p^[a % T] (p^[T * (a / T)] x) :=
        Function.iterate_add_apply p (a % T) (T * (a / T)) x
      _ = p^[a % T] x := by
        congr 1
        rw [Function.iterate_mul]
        exact Function.iterate_fixed hperiod (a / T)
  have hsourcePower (q : D) (hqv : dartTailVertex B.map q = B.source) :
      ∃ i : Fin T, p^[i.val] x = q := by
    obtain ⟨e, he, heq⟩ := (hsourceCycle q hqv).exists_pow_eq'
    refine ⟨⟨e % T, Nat.mod_lt _ hTpos⟩, ?_⟩
    calc
      p^[e % T] x = p^[e] x := (hiterMod e).symm
      _ = q := by simpa [p, Equiv.Perm.iterate_eq_pow] using heq
  have hf : Function.Injective
      (fun i : Fin T => p^[i.val] x) := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · have hsmall : p^[j.val - i.val] x = x :=
        Function.iterate_cancel p.injective hij.symm
      have hmin := Nat.find_min' hperiodExists ⟨by omega, hsmall⟩
      omega
    · have hsmall : p^[i.val - j.val] x = x :=
        Function.iterate_cancel p.injective hij
      have hmin := Nat.find_min' hperiodExists ⟨by omega, hsmall⟩
      omega
  let preList : List D := List.ofFn (fun i : Fin T => p^[i.val] x)
  let scan : List D := finiteRotationScan B x
  have hscanLen : scan.length = orderOf p := by
    simp [scan, finiteRotationScan, p]
  have hpreNodup : preList.Nodup := List.nodup_ofFn.mpr hf
  have htake : preList = scan.take T := by
    apply List.ext_getElem
    · simp [preList, List.length_take, hscanLen, Nat.min_eq_left hTle]
    · intro a hpre htake
      have ha : a < T := by
        simpa [List.length_take, hscanLen, Nat.min_eq_left hTle] using htake
      have hleft : preList[a]'hpre = p^[a] x := by
        simp [preList]
      have hright : (scan.take T)[a]'htake = p^[a] x := by
        rw [List.getElem_take]
        simp [scan, finiteRotationScan, p, Equiv.Perm.iterate_eq_pow]
      exact hleft.trans hright.symm
  have hscanDecomp : scan = preList ++ scan.drop T := by
    calc
      scan = scan.take T ++ scan.drop T := (List.take_append_drop T scan).symm
      _ = preList ++ scan.drop T := congrArg (fun l => l ++ scan.drop T) htake.symm
  let pred : D → Prop := fun d =>
    dartTailVertex B.map d = B.source ∧ B.map.tail d
  have hpreFilter : preList.filter pred = preList := by
    apply List.filter_eq_self.mpr
    intro d hd
    rw [List.mem_ofFn'] at hd
    obtain ⟨i, hi⟩ := hd
    have hmem : pred (p^[i.val] x) := by
      exact ⟨hvertexIter i.val, source_vertexRotationCycle_all_outgoing B
        ⟨p^[i.val] x, hvertexIter i.val⟩⟩
    rw [← hi]
    exact decide_eq_true hmem
  have hcover (d : D) (hd : pred d) : d ∈ preList := by
    obtain ⟨i, hi⟩ := hsourcePower d hd.1
    rw [List.mem_ofFn']
    exact ⟨i, hi⟩
  have hsuffixSub : ∀ d, d ∈ scan.drop T → d ∈ preList := by
    intro d hd
    have hdscan : d ∈ scan := List.mem_of_mem_drop hd
    have hcycle := (mem_finiteRotationScan_iff B x d).mp hdscan
    have hquot : dartTailVertex B.map x = dartTailVertex B.map d :=
      Quotient.sound hcycle
    have hdv : dartTailVertex B.map d = B.source := hquot.symm.trans hxv
    have htail := source_vertexRotationCycle_all_outgoing B ⟨d, hdv⟩
    exact hcover d ⟨hdv, htail⟩
  have hremoveSubset : ∀ t : List D, (∀ d ∈ t, d ∈ preList) →
      t.removeAll preList = [] := by
    intro t
    induction t with
    | nil => intro _; simp
    | cons a t ih =>
        intro h
        have ha : a ∈ preList := h a (by simp)
        have ht : ∀ d ∈ t, d ∈ preList := by
          intro d hd
          exact h d (by simp [hd])
        simp [List.cons_removeAll, ha, ih ht]
  have hsuffixRemove : (scan.drop T).removeAll preList = [] :=
    hremoveSubset _ hsuffixSub
  have horder : canonicalOutgoingOrder B B.source
      (bipolar_source_ne_sink B) = preList := by
    rw [canonicalOutgoingOrder]
    have hxCorner : x = finiteXDPLeftmostCorner B B.source := by
      simp [x, finiteXDPLeftmostCorner_source,
        leftmostOutgoing_source_eq_firstLeftDart]
    have hscanOut : finiteOutgoingRotationOrder B x = scan := by
      simpa [scan, hxCorner] using finiteOutgoingRotationOrder_eq_scan_at_source B
    rw [hscanOut, hscanDecomp,
      List.eraseDups_append, eraseDups_of_nodup_region preList hpreNodup,
      hsuffixRemove]
    simp
  have hcorner : p (rightmostOutgoing B B.source
      (bipolar_source_ne_sink B)) = x := by
    simpa [p, x] using source_rightmostOutgoing_corner_eq_leftmostOutgoing B
  have hlast : p^[k] x = rightmostOutgoing B B.source
      (bipolar_source_ne_sink B) := by
    have hstep : p^[k + 1] x = p (p^[k] x) := by
      rw [show k + 1 = Nat.succ k by omega, Function.iterate_succ_apply']
    apply p.injective
    calc
      p (p^[k] x) = p^[k + 1] x := hstep.symm
      _ = x := by rw [hkT]; exact hperiod
      _ = p (rightmostOutgoing B B.source
          (bipolar_source_ne_sink B)) := hcorner.symm
  refine ⟨k, ?_, hlast⟩
  rw [horder]
  change List.ofFn (fun i : Fin T => p^[i.val] x) =
    List.ofFn (fun i : Fin (k + 1) =>
      B.map.toCombinatorialMap.rot.symm^[i.val]
        (leftmostOutgoing B B.source (bipolar_source_ne_sink B)))
  rw [← hkT]

private theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_localSector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi : i < n)
    (hnotOuterStep : ∀ q,
      dartTailVertex B.map q =
        P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ →
      B.map.tail q →
      q ≠ rightmostOutgoing B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi) →
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q))
    (hconsecutive : ∀ k (hk : k + 1 <
        (canonicalOutgoingOrder B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi)).length),
      (canonicalOutgoingOrder B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi)).get ⟨k + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm
          ((canonicalOutgoingOrder B
            (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
            (simplePath_vertex_ne_end P i hi)).get ⟨k, by omega⟩))
    (hnotRightmostAt : ∀ k (hk : k + 1 <
        (canonicalOutgoingOrder B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi)).length),
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).get ⟨k, by omega⟩ ≠
        rightmostOutgoing B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi))
    (d : D)
    (htailVertex : dartTailVertex B.map d =
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf d <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf
          (P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) := by
  classical
  let w := P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩
  let b := P.darts.get ⟨i, by rw [P.darts_length]; omega⟩
  let ht : w ≠ B.sink := simplePath_vertex_ne_end P i hi
  let O := canonicalOutgoingOrder B w ht
  have hstepB : dartTailVertex B.map b = w ∧ B.map.tail b := by
    have h := P.edge_step ⟨i, by rw [P.darts_length]; exact hi⟩
    exact ⟨by simpa [b, w] using h.2.2.1.symm, h.2.1⟩
  have hBmem : b ∈ O :=
    (mem_canonicalOutgoingOrder_iff B w ht b).2 hstepB
  have hdmem : d ∈ O :=
    (mem_canonicalOutgoingOrder_iff B w ht d).2
      ⟨by simpa [w] using htailVertex, htail⟩
  have hOnodup : O.Nodup := canonicalOutgoingOrder_nodup B w ht
  let jd := O.idxOf d
  let jb := O.idxOf b
  have hjd : jd < O.length := by
    exact List.idxOf_lt_length_iff.mpr (by simpa [O, w, ht] using hdmem)
  have hjb : jb < O.length := by
    exact List.idxOf_lt_length_iff.mpr (by simpa [O, w, ht] using hBmem)
  have hgetD : O.get ⟨jd, hjd⟩ = d := by
    exact List.idxOf_get hjd
  have hgetB : O.get ⟨jb, hjb⟩ = b := by
    exact List.idxOf_get hjb
  have hnotOuter (q : D) (hqv : dartTailVertex B.map q = w)
      (hqt : B.map.tail q)
      (hqne : q ≠ rightmostOutgoing B w ht) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    exact hnotOuterStep q (by simpa [w] using hqv) hqt (by simpa [w, ht] using hqne)
  have hnotSeam (q : D) (hqv : dartTailVertex B.map q = w)
      (hqt : B.map.tail q) (hqne : q ≠ b) :
      q ∉ pathCutSeamDarts B P := by
    intro hseam
    change q ∈ P.darts ∨ B.map.toCombinatorialMap.edgeInv q ∈ P.darts at hseam
    rcases hseam with hqP | hqInvP
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hqP
      have hjlt : j.val < n := by simpa [P.darts_length] using j.isLt
      have hjstep := P.edge_step j
      have hvertices :
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
            P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ := by
        calc
          P.vertices.get ⟨j.val, by rw [P.vertices_length]; omega⟩ =
              dartTailVertex B.map (P.darts.get j) := hjstep.2.2.1
          _ = dartTailVertex B.map q := congrArg (dartTailVertex B.map) hj
          _ = w := hqv
          _ = P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ := by rfl
      have hji := P.vertices_nodup.get_inj_iff.mp hvertices
      have hval : j.val = i := congrArg Fin.val hji
      apply hqne
      calc
        q = P.darts.get j := hj.symm
        _ = P.darts.get ⟨i, by rw [P.darts_length]; exact hi⟩ := by
          congr 1
          exact Fin.ext hval
        _ = b := rfl
    · have hnotTail : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv q) :=
        (B.map.tail_iff q (B.noMissingDarts q)).mp hqt
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hqInvP
      have htailInv := (P.edge_step j).2.1
      exact hnotTail ((congrArg B.map.tail hj).mp htailInv)
  obtain ⟨side, hleft, hright, hface, hedge⟩ := pathCut_exists_side_coloring B P
  have hbLeft : side b = true := hleft b (Or.inr (List.get_mem _ _))
  have hflipBRight : side (B.map.toCombinatorialMap.edgeInv b) = false :=
    hright _ (Or.inr ⟨b, List.get_mem _ _, rfl⟩)
  have hidxQ (k : ℕ) (hk : k < O.length) :
      O.idxOf (O.get ⟨k, hk⟩) = k := by
    exact List.get_idxOf hOnodup ⟨k, hk⟩
  have hgetNeB (k : ℕ) (hk : k < O.length) (hkne : k ≠ jb) :
      O.get ⟨k, hk⟩ ≠ b := by
    intro h
    have hidx := hidxQ k hk
    rw [h] at hidx
    change jb = k at hidx
    exact hkne hidx.symm
  have hstepColor (k : ℕ) (hk : k + 1 < O.length) (hkne : k ≠ jb) :
      side (O.get ⟨k + 1, by omega⟩) = side (O.get ⟨k, by omega⟩) := by
    have hklen : k < O.length := by omega
    let q := O.get ⟨k, hklen⟩
    have hqmem : q ∈ O := List.get_mem _ _
    have hqv : dartTailVertex B.map q = w :=
      (mem_canonicalOutgoingOrder_iff B w ht q).mp hqmem |>.1
    have hqt : B.map.tail q :=
      (mem_canonicalOutgoingOrder_iff B w ht q).mp hqmem |>.2
    have hqne : q ≠ b := hgetNeB k hklen hkne
    have hrot : O.get ⟨k + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm (O.get ⟨k, hklen⟩) := by
      simpa [O, w, ht] using hconsecutive k (by simpa [O, w, ht] using hk)
    have hcolor := pathCutSide_eq_rotSymm_of_inner_offSeam B P side
      hface hedge q (hnotOuter q hqv hqt (hnotRightmostAt k hk))
        (hnotSeam q hqv hqt hqne)
    dsimp [q] at hrot hcolor ⊢
    rw [hrot]
    exact hcolor
  have hleftColor (hdb : jd < jb) : side d = true := by
    have hwalk : ∀ m, ∀ hm : m ≤ jb - jd,
        side (O.get ⟨jd, hjd⟩) = side (O.get ⟨jd + m, by omega⟩) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm
          have hprev := ih (by omega)
          have hcur : jd + m < jb := by omega
          have hcurStep : jd + m + 1 < O.length := by omega
          have hnext := hstepColor (jd + m) hcurStep (by omega)
          calc
            side (O.get ⟨jd, hjd⟩) = side (O.get ⟨jd + m, by omega⟩) := hprev
            _ = side (O.get ⟨jd + m + 1, by omega⟩) := hnext.symm
    have hend := hwalk (jb - jd) (by omega)
    have hindex : jd + (jb - jd) = jb := by omega
    have hindexFin :
        (⟨jd + (jb - jd), by omega⟩ : Fin O.length) = ⟨jb, hjb⟩ :=
      Fin.ext hindex
    have hgetEnd : O.get ⟨jd + (jb - jd), by omega⟩ = b :=
      (congrArg O.get hindexFin).trans hgetB
    calc
      side d = side (O.get ⟨jd, hjd⟩) := congrArg side hgetD.symm
      _ = side (O.get ⟨jd + (jb - jd), by omega⟩) := hend
      _ = side b := congrArg side hgetEnd
      _ = true := hbLeft
  have hrightColor (hbd : jb < jd) : side d = false := by
    have hjbNext : jb + 1 < O.length := by omega
    have hbnotRightmost := hnotRightmostAt jb hjbNext
    have hnextB := hconsecutive jb (by simpa [O, w, ht] using hjbNext)
    change O.get ⟨jb + 1, hjbNext⟩ =
      B.map.toCombinatorialMap.rot.symm (O.get ⟨jb, hjb⟩) at hnextB
    have hsideAfterB : side (B.map.toCombinatorialMap.rot.symm b) = false := by
      have hcorner := (corner_consecutiveDarts B
        (B.map.toCombinatorialMap.edgeInv b)).1
      have hfaceB := hface (B.map.toCombinatorialMap.edgeInv b)
        (hnotOuter b hstepB.1 hstepB.2 (by
          intro h
          apply hbnotRightmost
          rw [hgetB]
          exact h))
      rw [B.map.toCombinatorialMap.edgeInv_invol] at hcorner
      rw [← hcorner]
      exact hfaceB.trans hflipBRight
    have hcolorNext : side (O.get ⟨jb + 1, hjbNext⟩) = false := by
      rw [hnextB, hgetB]
      exact hsideAfterB
    have hwalk : ∀ m, ∀ hm : m ≤ jd - (jb + 1),
        side (O.get ⟨jb + 1, hjbNext⟩) =
          side (O.get ⟨jb + 1 + m, by omega⟩) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm
          have hprev := ih (by omega)
          have hcur : jb + 1 + m < jd := by omega
          have hcurStep : jb + 1 + m + 1 < O.length := by omega
          have hnext := hstepColor (jb + 1 + m) hcurStep (by omega)
          calc
            side (O.get ⟨jb + 1, hjbNext⟩) =
                side (O.get ⟨jb + 1 + m, by omega⟩) := hprev
            _ = side (O.get ⟨jb + 1 + m + 1, by omega⟩) := hnext.symm
    have hend := hwalk (jd - (jb + 1)) (by omega)
    have hindex : jb + 1 + (jd - (jb + 1)) = jd := by omega
    have hindexFin :
        (⟨jb + 1 + (jd - (jb + 1)), by omega⟩ : Fin O.length) = ⟨jd, hjd⟩ :=
      Fin.ext hindex
    have hgetEnd : O.get ⟨jb + 1 + (jd - (jb + 1)), by omega⟩ = d :=
      (congrArg O.get hindexFin).trans hgetD
    have hend' : side (O.get ⟨jb + 1, hjbNext⟩) = side d :=
      hend.trans (congrArg side hgetEnd)
    exact hend'.symm.trans hcolorNext
  have hjne : jd ≠ jb := by
    intro h
    apply hne
    calc
      d = O.get ⟨jd, hjd⟩ := hgetD.symm
      _ = O.get ⟨jb, hjb⟩ := by congr 1; exact Fin.ext h
      _ = b := hgetB
  have hsideIff : side d = true ↔ jd < jb := by
    rcases lt_or_gt_of_ne hjne with hlt | hgt
    · rw [hleftColor hlt]
      simp [hlt]
    · rw [hrightColor hgt]
      simp [Nat.not_lt_of_gt hgt]
  have hmemColor : d ∈ pathCutLeftDarts B P ↔ side d = true :=
    pathCutLeft_mem_iff_side_true_of_sideColoring B P side hleft hright hface hedge d
  have hnotSeamD : d ∉ pathCutSeamDarts B P :=
    hnotSeam d (by simpa [w] using htailVertex) htail (by simpa [b] using hne)
  change d ∈ pathCutLeftDarts B P ∧ d ∉ pathCutSeamDarts B P ↔ jd < jb
  constructor
  · rintro ⟨hdLeft, _⟩
    exact hsideIff.mp (hmemColor.mp hdLeft)
  · intro hlt
    exact ⟨hmemColor.mpr (hsideIff.mpr hlt), hnotSeamD⟩

private theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_internalSector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi0 : 0 < i) (hi : i < n)
    (hnotOuterStep : ∀ q,
      dartTailVertex B.map q =
        P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ →
      B.map.tail q →
      q ≠ rightmostOutgoing B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi) →
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q))
    (d : D)
    (htailVertex : dartTailVertex B.map d =
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf d <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf
          (P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) := by
  classical
  let w := P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩
  let hs : w ≠ B.source := simplePath_vertex_ne_start P i hi0 (by omega)
  let ht := simplePath_vertex_ne_end P i hi
  let O := canonicalOutgoingOrder B w ht
  have hconsecutive (k : ℕ) (hk : k + 1 < O.length) :
      O.get ⟨k + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm (O.get ⟨k, by omega⟩) := by
    have hkrot : k < O.length - 1 := by omega
    simpa [O, w, ht] using
      canonicalOutgoingOrder_internal_consecutive B w hs ht ⟨k, hkrot⟩
  have hnotRightmostAt (k : ℕ) (hk : k + 1 < O.length) :
      O.get ⟨k, by omega⟩ ≠ rightmostOutgoing B w ht := by
    have hrot := hconsecutive k hk
    have hnextmem : O.get ⟨k + 1, by omega⟩ ∈ O := List.get_mem _ _
    have hnextTail : B.map.tail (O.get ⟨k + 1, by omega⟩) :=
      (mem_canonicalOutgoingOrder_iff B w ht _).mp hnextmem |>.2
    intro hq
    have htailRightmost :=
      (rightmostOutgoing_internal_characterization B w hs ht).2.2.1
    apply htailRightmost
    rw [← hq, ← hrot]
    exact hnextTail
  have hconsecutive' : ∀ k (hk : k + 1 <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).length),
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).get ⟨k + 1, by omega⟩ =
      B.map.toCombinatorialMap.rot.symm
        ((canonicalOutgoingOrder B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi)).get ⟨k, by omega⟩) := by
    intro k hk
    exact hconsecutive k (by simpa [O, w, ht] using hk)
  have hnotRightmostAt' : ∀ k (hk : k + 1 <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).length),
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).get ⟨k, by omega⟩ ≠
        rightmostOutgoing B
          (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
          (simplePath_vertex_ne_end P i hi) := by
    intro k hk
    exact hnotRightmostAt k (by simpa [O, w, ht] using hk)
  exact pathCutLeft_offSeam_iff_precedes_pathDart_of_localSector
    B P i hi hnotOuterStep hconsecutive' hnotRightmostAt'
    d htailVertex htail hne

/-- At the source, the strict-left darts are exactly the outgoing darts before
the first path dart in canonical rotation order. Helper toward lem-lr-ind
result. -/
theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (d : D)
    (htailVertex : dartTailVertex B.map d = B.source)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨0, by
      have hn : 0 < n := by
        by_contra h
        have hn0 : n = 0 := by omega
        subst n
        exact bipolar_source_ne_sink B
          (P.start_vertex.symm.trans P.end_vertex)
      rw [P.darts_length]
      exact hn⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).idxOf d <
        (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).idxOf
          (P.darts.get ⟨0, by
            have hn : 0 < n := by
              by_contra h
              have hn0 : n = 0 := by omega
              subst n
              exact bipolar_source_ne_sink B
                (P.start_vertex.symm.trans P.end_vertex)
            rw [P.darts_length]
            exact hn⟩) := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    exact bipolar_source_ne_sink B
      (P.start_vertex.symm.trans P.end_vertex)
  let ht := simplePath_vertex_ne_end P 0 hn
  let O := canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)
  let p := B.map.toCombinatorialMap.rot.symm
  let x := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  obtain ⟨k, hO, hlast⟩ :=
    canonicalOutgoingOrder_source_eq_iterate_prefix_with_endpoint B
  have hOlen : O.length = k + 1 := by
    simpa [O] using congrArg List.length hO
  have hconsecutive : ∀ j (hj : j + 1 < O.length),
      O.get ⟨j + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm (O.get ⟨j, by omega⟩) := by
    intro j hj
    have hj' : j + 1 < k + 1 := by simpa [hOlen] using hj
    have hstep : p^[j + 1] x = p (p^[j] x) := by
      rw [show j + 1 = Nat.succ j by omega, Function.iterate_succ_apply']
    have hcur : O.get ⟨j, by omega⟩ = p^[j] x := by
      have hjCanon : j < (canonicalOutgoingOrder B B.source
          (bipolar_source_ne_sink B)).length := by
        simpa [O] using (Nat.lt_of_succ_lt hj)
      have h := List.get_of_eq hO ⟨j, hjCanon⟩
      rw [List.get_ofFn] at h
      simpa [O, p, x] using h
    have hnext : O.get ⟨j + 1, by omega⟩ = p^[j + 1] x := by
      have hjCanon : j + 1 < (canonicalOutgoingOrder B B.source
          (bipolar_source_ne_sink B)).length := by
        simpa [O] using hj
      have h := List.get_of_eq hO ⟨j + 1, hjCanon⟩
      rw [List.get_ofFn] at h
      simpa [O, p, x] using h
    calc
      O.get ⟨j + 1, by omega⟩ = p^[j + 1] x := hnext
      _ = p (p^[j] x) := hstep
      _ = B.map.toCombinatorialMap.rot.symm (O.get ⟨j, by omega⟩) := by
        rw [hcur]
  have hhead : O.get ⟨0, by omega⟩ = x := by
    have hzero : 0 < (canonicalOutgoingOrder B B.source
        (bipolar_source_ne_sink B)).length := by
      simpa [O] using (show 0 < O.length by rw [hOlen]; omega)
    have h := List.get_of_eq hO ⟨0, hzero⟩
    rw [List.get_ofFn] at h
    simpa [O, p, x] using h
  have hOnodup : O.Nodup := canonicalOutgoingOrder_nodup B B.source
    (bipolar_source_ne_sink B)
  have hnotRightmostAt : ∀ j (hj : j + 1 < O.length),
      O.get ⟨j, by omega⟩ ≠
        rightmostOutgoing B B.source (bipolar_source_ne_sink B) := by
    intro j hj
    have hstep := hconsecutive j hj
    intro hq
    have hnextX : O.get ⟨j + 1, by omega⟩ = x := by
      calc
        O.get ⟨j + 1, by omega⟩ =
            B.map.toCombinatorialMap.rot.symm (O.get ⟨j, by omega⟩) := hstep
        _ = B.map.toCombinatorialMap.rot.symm
            (rightmostOutgoing B B.source (bipolar_source_ne_sink B)) :=
          congrArg B.map.toCombinatorialMap.rot.symm hq
        _ = x := by simpa [p, x] using
          source_rightmostOutgoing_corner_eq_leftmostOutgoing B
    have hsame : O.get ⟨j + 1, by omega⟩ = O.get ⟨0, by omega⟩ :=
      hnextX.trans hhead.symm
    have hidx : j + 1 = 0 := by
      calc
        j + 1 = O.idxOf (O.get ⟨j + 1, by omega⟩) :=
          (List.get_idxOf hOnodup ⟨j + 1, by omega⟩).symm
        _ = O.idxOf (O.get ⟨0, by omega⟩) := congrArg O.idxOf hsame
        _ = 0 := List.get_idxOf hOnodup ⟨0, by omega⟩
    omega
  have hnotOuterStep (q : D) (hqv : dartTailVertex B.map q = B.source)
      (hqt : B.map.tail q)
      (hqne : q ≠ rightmostOutgoing B B.source
        (bipolar_source_ne_sink B)) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    intro hout
    exact hqne (outgoing_outer_edge_eq_rightmostOutgoing B
      (bipolar_source_ne_sink B) hqv hqt hout)
  have hconsecutive' : ∀ j (hj : j + 1 <
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).length),
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).get
          ⟨j + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm
          ((canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).get
            ⟨j, by omega⟩) := by
    intro j hj
    exact hconsecutive j (by simpa [O] using hj)
  have hnotRightmostAt' : ∀ j (hj : j + 1 <
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).length),
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).get
          ⟨j, by omega⟩ ≠
        rightmostOutgoing B B.source (bipolar_source_ne_sink B) := by
    intro j hj
    exact hnotRightmostAt j (by simpa [O] using hj)
  have htailSource : dartTailVertex B.map d =
      P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
    exact htailVertex.trans P.start_vertex.symm
  let VertexNotSink := {v : MapVertex B.map // v ≠ B.sink}
  have hv : (⟨P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩, ht⟩ :
      VertexNotSink) =
      ⟨B.source, bipolar_source_ne_sink B⟩ := Subtype.ext P.start_vertex
  have hPathOrderEq := congrArg (fun v : VertexNotSink =>
    canonicalOutgoingOrder B v.1 v.2) hv
  have hro := congrArg (fun v : VertexNotSink =>
    rightmostOutgoing B v.1 v.2) hv
  have hnotOuterStep' (q : D)
      (hqv : dartTailVertex B.map q =
        P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩)
      (hqt : B.map.tail q)
      (hqne : q ≠ rightmostOutgoing B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    apply hnotOuterStep q (hqv.trans P.start_vertex) hqt
    intro heq
    apply hqne
    exact hro.symm ▸ heq
  have hconsecutive'' : ∀ j (hj : j + 1 <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).length),
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
          ⟨j + 1, by omega⟩ =
        B.map.toCombinatorialMap.rot.symm
          ((canonicalOutgoingOrder B
            (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
            ⟨j, by omega⟩) := by
    intro j hj
    have hjSource : j + 1 <
        (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).length := by
      rw [← hPathOrderEq]
      exact hj
    have hgetNext := List.get_of_eq hPathOrderEq.symm
      ⟨j + 1, hjSource⟩
    have hgetCur := List.get_of_eq hPathOrderEq.symm
      ⟨j, Nat.lt_of_succ_lt hjSource⟩
    calc
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
          ⟨j + 1, hj⟩ =
        (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).get
          ⟨j + 1, hjSource⟩ := hgetNext.symm
      _ = B.map.toCombinatorialMap.rot.symm
          ((canonicalOutgoingOrder B B.source
            (bipolar_source_ne_sink B)).get ⟨j, Nat.lt_of_succ_lt hjSource⟩) :=
        hconsecutive' j hjSource
      _ = B.map.toCombinatorialMap.rot.symm
          ((canonicalOutgoingOrder B
            (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
            ⟨j, by omega⟩) := congrArg B.map.toCombinatorialMap.rot.symm hgetCur
  have hnotRightmostAt'' : ∀ j (hj : j + 1 <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).length),
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
          ⟨j, by omega⟩ ≠
        rightmostOutgoing B
          (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht := by
    intro j hj
    have hjSource : j + 1 <
        (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).length := by
      rw [← hPathOrderEq]
      exact hj
    intro hbad
    have hget := List.get_of_eq hPathOrderEq ⟨j, Nat.lt_of_succ_lt hj⟩
    have hro : rightmostOutgoing B
        (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht =
      rightmostOutgoing B B.source (bipolar_source_ne_sink B) :=
      congrArg (fun v : VertexNotSink => rightmostOutgoing B v.1 v.2) hv
    apply hnotRightmostAt' j hjSource
    calc
      (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).get
          ⟨j, Nat.lt_of_succ_lt hjSource⟩ =
        (canonicalOutgoingOrder B
          (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht).get
          ⟨j, by omega⟩ := hget.symm
      _ = rightmostOutgoing B
          (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩) ht := hbad
      _ = rightmostOutgoing B B.source (bipolar_source_ne_sink B) := hro
  have hsector := pathCutLeft_offSeam_iff_precedes_pathDart_of_localSector
    B P 0 hn hnotOuterStep' hconsecutive'' hnotRightmostAt''
    d htailSource htail hne
  simpa only [hPathOrderEq] using hsector

/-- At a path vertex away from the outer boundary, the darts in the left
closure that are not on the seam are exactly the outgoing darts before the
path dart in canonical rotation order. Helper toward `lem-lr-ind` and -/
theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_interiorVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi0 : 0 < i) (hi : i < n)
    (hleftBoundary :
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ∉ B.leftPath.vertices)
    (hrightBoundary :
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ∉ B.rightPath.vertices)
    (d : D)
    (htailVertex : dartTailVertex B.map d =
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf d <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf
          (P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) := by
  classical
  let w := P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩
  have hnotOuterStep (q : D)
      (hqv : dartTailVertex B.map q = w) (hqt : B.map.tail q)
      (_hqne : q ≠ rightmostOutgoing B w (simplePath_vertex_ne_end P i hi)) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    intro hout
    have hboundary := headVertex_mem_boundary_of_outer B hout
    have hhead : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv q) =
        dartTailVertex B.map q := by
      simp [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol]
    rw [hhead, hqv] at hboundary
    rcases hboundary with hL | hR
    · exact hleftBoundary hL
    · exact hrightBoundary hR
  exact pathCutLeft_offSeam_iff_precedes_pathDart_of_internalSector
    B P i hi0 hi hnotOuterStep d htailVertex htail hne

/-- At an internal vertex on the left boundary, the darts in the left closure
that are not on the seam are exactly the outgoing darts before the path dart
in canonical rotation order, including when the path dart is the left-boundary
dart. Helper toward `lem-lr-ind` and `def-geodesic` -/
theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_leftBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi0 : 0 < i) (hi : i < n)
    (_hboundary :
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ∈ B.leftPath.vertices)
    (d : D)
    (htailVertex : dartTailVertex B.map d =
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf d <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf
          (P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) := by
  classical
  let w := P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩
  let ht := simplePath_vertex_ne_end P i hi
  have hnotOuterStep (q : D)
      (hqv : dartTailVertex B.map q = w) (hqt : B.map.tail q)
      (hqne : q ≠ rightmostOutgoing B w ht) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    intro hout
    exact hqne (outgoing_outer_edge_eq_rightmostOutgoing B ht
      (by simpa [w] using hqv) hqt hout)
  exact pathCutLeft_offSeam_iff_precedes_pathDart_of_internalSector
    B P i hi0 hi hnotOuterStep d htailVertex htail hne

/-- At an internal vertex on the right boundary, the darts in the left closure
that are not on the seam are exactly the outgoing darts before the path dart
in canonical rotation order, including when the path dart is the
right-boundary dart. Helper toward `lem-lr-ind` and `def-geodesic` -/
theorem pathCutLeft_offSeam_iff_precedes_pathDart_of_rightBoundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi0 : 0 < i) (hi : i < n)
    (_hboundary :
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ∈ B.rightPath.vertices)
    (d : D)
    (htailVertex : dartTailVertex B.map d =
      P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
    (htail : B.map.tail d)
    (hne : d ≠ P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) :
    d ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P ↔
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf d <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i hi)).idxOf
          (P.darts.get ⟨i, by rw [P.darts_length]; omega⟩) := by
  classical
  let w := P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩
  let ht := simplePath_vertex_ne_end P i hi
  have hnotOuterStep (q : D)
      (hqv : dartTailVertex B.map q = w) (hqt : B.map.tail q)
      (hqne : q ≠ rightmostOutgoing B w ht) :
      ¬ B.map.IsOuter (B.map.toCombinatorialMap.edgeInv q) := by
    intro hout
    exact hqne (outgoing_outer_edge_eq_rightmostOutgoing B ht
      (by simpa [w] using hqv) hqt hout)
  exact pathCutLeft_offSeam_iff_precedes_pathDart_of_internalSector
    B P i hi0 hi hnotOuterStep d htailVertex htail hne

/-- Every prefix and suffix of an XDP geodesic realizes the corresponding
source-to-vertex and vertex-to-sink extremal distances. Helper toward
not the paper result. -/
theorem xdpGeodesic_prefix_suffix_distanceNat
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsXDPGeodesicBase B x P) (i : Fin (n + 1)) :
    match x with
    | .ldp =>
        ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = i.val ∧
        ldpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = n - i.val
    | .sdp =>
        sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = i.val ∧
        sdpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = n - i.val := by
  cases x with
  | ldp =>
      change ldpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
        rw [P.vertices_length]; exact i.isLt⟩) = i.val ∧
        ldpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = n - i.val
      exact IsLDPGeodesicBase.prefix_suffix_distanceNat B P hP i
  | sdp =>
      change sdpSourceDistanceNatBase B (P.vertices.get ⟨i.val, by
        rw [P.vertices_length]; exact i.isLt⟩) = i.val ∧
        sdpSinkDistanceNatBase B (P.vertices.get ⟨i.val, by
          rw [P.vertices_length]; exact i.isLt⟩) = n - i.val
      exact IsSDPGeodesicBase.prefix_suffix_distanceNat B P hP i

private theorem path_vertices_eq_of_dart_prefix_here
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    {n : ℕ} (P Q : SimpleDirectedDartPath B.map B.source B.sink n)
    (i : ℕ) (hi : i ≤ n)
    (hpre : ∀ j : Fin i,
      P.darts.get ⟨j.val, by simpa [P.darts_length] using
        (show j.val < n by omega)⟩ =
        Q.darts.get ⟨j.val, by simpa [Q.darts_length] using
          (show j.val < n by omega)⟩) :
    P.vertices.get ⟨i, by simpa [P.vertices_length] using (show i < n + 1 by omega)⟩ =
      Q.vertices.get ⟨i, by simpa [Q.vertices_length] using (show i < n + 1 by omega)⟩ := by
  induction i with
  | zero =>
      exact P.start_vertex.trans Q.start_vertex.symm
  | succ i ih =>
      have hi' : i ≤ n := by omega
      have hprev := ih hi' (fun j => hpre ⟨j.val, by omega⟩)
      have hd := hpre ⟨i, by omega⟩
      have hstepP := (P.edge_step ⟨i, by rw [P.darts_length]; omega⟩).2.2.2
      have hstepQ := (Q.edge_step ⟨i, by rw [Q.darts_length]; omega⟩).2.2.2
      calc
        P.vertices.get ⟨i + 1, by simpa [P.vertices_length] using
            (show i + 1 < n + 1 by omega)⟩ =
            dartHeadVertex B.map (P.darts.get ⟨i, by
              simpa [P.darts_length] using (show i < n by omega)⟩) := hstepP
        _ = dartHeadVertex B.map (Q.darts.get ⟨i, by
              simpa [Q.darts_length] using (show i < n by omega)⟩) :=
          congrArg (dartHeadVertex B.map) hd
        _ = Q.vertices.get ⟨i + 1, by simpa [Q.vertices_length] using
            (show i + 1 < n + 1 by omega)⟩ := hstepQ.symm

 /-- A lex-leftmost XDP geodesic cannot first diverge through an outgoing dart
in the strict-left source sector. This is the index-zero helper toward
not the paper result. -/
theorem lexLeftmost_no_strict_left_dart_at_firstDivergence_source
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P Q : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsLexLeftmostXDPGeodesic B x P)
    (hQ : IsXDPGeodesicBase B x Q)
    (hdiff : P.darts.get ⟨0, by
      have hn : 0 < n := by
        by_contra h
        have hn0 : n = 0 := by omega
        subst n
        exact bipolar_source_ne_sink B
          (P.start_vertex.symm.trans P.end_vertex)
      rw [P.darts_length]
      exact hn⟩ ≠
      Q.darts.get ⟨0, by
        have hn : 0 < n := by
          by_contra h
          have hn0 : n = 0 := by omega
          subst n
          exact bipolar_source_ne_sink B
            (Q.start_vertex.symm.trans Q.end_vertex)
        rw [Q.darts_length]
        exact hn⟩)
    (hleft : Q.darts.get ⟨0, by
      have hn : 0 < n := by
        by_contra h
        have hn0 : n = 0 := by omega
        subst n
        exact bipolar_source_ne_sink B
          (Q.start_vertex.symm.trans Q.end_vertex)
      rw [Q.darts_length]
      exact hn⟩ ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P) : False := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    exact bipolar_source_ne_sink B
      (P.start_vertex.symm.trans P.end_vertex)
  let dP := P.darts.get ⟨0, by rw [P.darts_length]; exact hn⟩
  let dQ := Q.darts.get ⟨0, by rw [Q.darts_length]; exact hn⟩
  have hdiff' : dP ≠ dQ := by simpa [dP, dQ] using hdiff
  have hlistNe : Q.darts ≠ P.darts := by
    intro h
    apply hdiff'
    simp [dP, dQ, h]
  have htailQ : dartTailVertex B.map dQ = B.source := by
    calc
      dartTailVertex B.map dQ =
          Q.vertices.get ⟨0, by rw [Q.vertices_length]; omega⟩ :=
        (Q.edge_step ⟨0, by rw [Q.darts_length]; exact hn⟩).2.2.1.symm
      _ = B.source := Q.start_vertex
  have htailP : dartTailVertex B.map dP = B.source := by
    calc
      dartTailVertex B.map dP =
          P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ :=
        (P.edge_step ⟨0, by rw [P.darts_length]; exact hn⟩).2.2.1.symm
      _ = B.source := P.start_vertex
  have hsourceOrder : (canonicalOutgoingOrder B B.source
      (bipolar_source_ne_sink B)).idxOf dQ <
      (canonicalOutgoingOrder B B.source
        (bipolar_source_ne_sink B)).idxOf dP := by
    have h := pathCutLeft_offSeam_iff_precedes_pathDart_of_source
      B P dQ htailQ
      (Q.edge_step ⟨0, by rw [Q.darts_length]; exact hn⟩).2.1
      (Ne.symm hdiff')
    exact h.mp (by simpa [dQ] using hleft)
  obtain ⟨hvs, hlexOrder⟩ := hP.2 Q hQ hlistNe rfl
    ⟨0, by exact hn⟩ (by simp) hdiff
  let VertexNotSink := {v : MapVertex B.map // v ≠ B.sink}
  have hv : (⟨dartTailVertex B.map dP, hvs⟩ : VertexNotSink) =
      ⟨B.source, bipolar_source_ne_sink B⟩ := Subtype.ext htailP
  have horderEq := congrArg (fun v : VertexNotSink =>
    canonicalOutgoingOrder B v.1 v.2) hv
  have hlexSource : (canonicalOutgoingOrder B B.source
      (bipolar_source_ne_sink B)).idxOf dP <
      (canonicalOutgoingOrder B B.source
        (bipolar_source_ne_sink B)).idxOf dQ := by
    simpa only [horderEq, dP, dQ] using hlexOrder
  exact (Nat.lt_asymm hlexSource hsourceOrder).elim

/-- A lex-leftmost XDP geodesic cannot first diverge through an outgoing dart
in the strict left cut region. This is the first-divergence form of the
comparison toward `lem-lr-ind` and `def-geodesic` -/
theorem lexLeftmost_no_strict_left_dart_at_firstDivergence
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P Q : SimpleDirectedDartPath B.map B.source B.sink n)
    (hP : IsLexLeftmostXDPGeodesic B x P)
    (hQ : IsXDPGeodesicBase B x Q)
    (i : Fin n) (hi0 : 0 < i.val)
    (hprefix : P.darts.take i.val = Q.darts.take i.val)
    (hdiff : P.darts.get ⟨i.val, by simp [P.darts_length]⟩ ≠
      Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩)
    (hleft : Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩ ∈
      pathCutLeftDarts B P \ pathCutSeamDarts B P) : False := by
  classical
  have hprefixDarts : ∀ j : Fin i.val,
      P.darts.get ⟨j.val, by simpa [P.darts_length] using
        (show j.val < n by omega)⟩ =
      Q.darts.get ⟨j.val, by simpa [Q.darts_length] using
        (show j.val < n by omega)⟩ := by
    intro j
    have hjTake : j.val < (P.darts.take i.val).length := by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨j.isLt, by rw [P.darts_length]; omega⟩
    have hTakeJ : (P.darts.take i.val)[j.val] =
        (Q.darts.take i.val)[j.val]'(hprefix ▸ hjTake) :=
      List.getElem_of_eq hprefix hjTake
    have hPj := List.getElem_take' (xs := P.darts) (i := j.val)
      (j := i.val) (by rw [P.darts_length]; omega) j.isLt
    have hQj := List.getElem_take' (xs := Q.darts) (i := j.val)
      (j := i.val) (by rw [Q.darts_length]; omega) j.isLt
    simpa only [List.get_eq_getElem] using hPj.trans (hTakeJ.trans hQj.symm)
  have hvertex := path_vertices_eq_of_dart_prefix_here B P Q i.val (by omega)
    hprefixDarts
  let dP := P.darts.get ⟨i.val, by simp [P.darts_length]⟩
  let dQ := Q.darts.get ⟨i.val, by simp [Q.darts_length]⟩
  have htailP : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
      dartTailVertex B.map dP := by
    change P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
      dartTailVertex B.map
        (P.darts.get ⟨i.val, by rw [P.darts_length]; omega⟩)
    exact (P.edge_step ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩).2.2.1
  have htailQ : Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ =
      dartTailVertex B.map dQ := by
    change Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ =
      dartTailVertex B.map
        (Q.darts.get ⟨i.val, by rw [Q.darts_length]; omega⟩)
    exact (Q.edge_step ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩).2.2.1
  have htailD : dartTailVertex B.map dQ =
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := by
    calc
      dartTailVertex B.map dQ =
          Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩ := htailQ.symm
      _ = P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := hvertex.symm
  have hne : dQ ≠ dP := by simpa [dP, dQ] using hdiff.symm
  have horderLt : (canonicalOutgoingOrder B
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩)
      (simplePath_vertex_ne_end P i.val i.isLt)).idxOf dQ <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end P i.val i.isLt)).idxOf dP := by
    by_cases hleftB : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ ∈
        B.leftPath.vertices
    · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_leftBoundary
        B P i.val hi0 i.isLt hleftB dQ
        htailD ((Q.edge_step ⟨i.val, by rw [Q.darts_length]; omega⟩).2.1)
        hne).mp hleft
    · by_cases hrightB : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ ∈
          B.rightPath.vertices
      · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_rightBoundary
          B P i.val hi0 i.isLt hrightB dQ
          htailD ((Q.edge_step ⟨i.val, by rw [Q.darts_length]; omega⟩).2.1)
          hne).mp hleft
      · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_interiorVertex
          B P i.val hi0 i.isLt
          hleftB hrightB dQ htailD
          ((Q.edge_step ⟨i.val, by rw [Q.darts_length]; omega⟩).2.1) hne).mp hleft
  have hlistNe : Q.darts ≠ P.darts := by
    intro h
    apply hdiff
    simp [h]
  obtain ⟨hvs, hlexLt⟩ := hP.2 Q hQ hlistNe rfl i hprefix hdiff
  have hvsPath : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ ≠ B.sink :=
    simplePath_vertex_ne_end P i.val i.isLt
  have hvsTail : dartTailVertex B.map dP ≠ B.sink := by
    intro h
    exact hvsPath (htailP.trans h)
  let VertexNotSink := {v : MapVertex B.map // v ≠ B.sink}
  have hvertexOrder :
      (⟨P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩, hvsPath⟩ :
        VertexNotSink) = ⟨dartTailVertex B.map dP, hvsTail⟩ :=
    Subtype.ext htailP
  have horderEq := congrArg
    (fun v : VertexNotSink => canonicalOutgoingOrder B v.1 v.2) hvertexOrder
  have hlexLtAtPathVertex := hlexLt
  rw [horderEq.symm] at hlexLtAtPathVertex
  have hlexLt'' : (canonicalOutgoingOrder B
      (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩)
      hvsPath).idxOf dP <
      (canonicalOutgoingOrder B
        (P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩)
        hvsPath).idxOf dQ := hlexLtAtPathVertex
  exact (Nat.lt_asymm hlexLt'' horderLt).elim


end DirectedDistances.PlanarMap
