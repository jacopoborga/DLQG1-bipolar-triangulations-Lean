/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPCanonicalLeftmost
public import DirectedDistances.PlanarMap.FiniteBipolarBlockConventions
public import DirectedDistances.PlanarMap.BipolarCanonicalTrees

/-! # Certification helpers for the canonical XDP outgoing order

paper result. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem internalOutgoingPrefix_facts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ k₀,
      (∀ i ≤ k₀, B.map.tail
        (B.map.toCombinatorialMap.rot.symm^[i] (leftmostOutgoing B v ht))) ∧
      Function.Injective (fun i : Fin (k₀ + 1) =>
        B.map.toCombinatorialMap.rot.symm^[i.val] (leftmostOutgoing B v ht)) ∧
      B.map.toCombinatorialMap.rot.symm^[k₀] (leftmostOutgoing B v ht) =
        rightmostOutgoing B v ht ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ∃ i ≤ k₀,
          B.map.toCombinatorialMap.rot.symm^[i] (leftmostOutgoing B v ht) = q ∧
          ∀ j ≤ i, B.map.tail
            (B.map.toCombinatorialMap.rot.symm^[j] (leftmostOutgoing B v ht))) := by
  classical
  let p : Equiv.Perm D := B.map.toCombinatorialMap.rot.symm
  let x := leftmostOutgoing B v ht
  let Out := {q : D // dartTailVertex B.map q = v ∧ B.map.tail q}
  rcases internal_outgoing_block_segment B v hs ht with
    ⟨k, hend, hcard, hcover, _⟩
  let f : Fin (k + 1) → D := fun i => p^[i.val] x
  let fr : Fin (k + 1) → Set.range f := fun i => ⟨f i, ⟨i, rfl⟩⟩
  have hfrSurj : Function.Surjective fr := by
    intro y
    rcases y with ⟨d, ⟨i, hi⟩⟩
    exact ⟨i, Subtype.ext hi⟩
  have hOutRange : ∀ q : Out, ∃ i : Fin (k + 1), f i = q.1 := by
    intro q
    obtain ⟨i, hi, hiter, _⟩ := hcover q.1 q.2.1 q.2.2
    refine ⟨⟨i, by omega⟩, ?_⟩
    simpa [p, x, f] using hiter
  let toRange : Out → Set.range f := fun q => ⟨q.1, hOutRange q⟩
  have htoRangeInj : Function.Injective toRange := by
    intro q q' heq
    apply Subtype.ext
    exact congrArg (fun z : Set.range f => z.1) heq
  have hOutLe : Fintype.card Out ≤ Fintype.card (Set.range f) :=
    Fintype.card_le_of_injective toRange htoRangeInj
  have hcardOut : Fintype.card Out = k + 1 := by
    simpa [Out] using hcard.symm
  have hfInj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hfrNotInj : ¬ Function.Injective fr := by
      intro hinj
      apply hne
      apply Fin.ext
      have hfrEq : fr i = fr j := Subtype.ext heq
      exact congrArg Fin.val (hinj hfrEq)
    have hlt := Fintype.card_lt_of_surjective_not_injective fr hfrSurj hfrNotInj
    simp only [Fintype.card_fin] at hlt
    omega
  have hro := rightmostOutgoing_internal_characterization B v hs ht
  obtain ⟨j, hj, hiter, hprior⟩ := hcover (rightmostOutgoing B v ht)
    hro.1 hro.2.1
  have hiterEnd : f ⟨k, by omega⟩ = rightmostOutgoing B v ht := by
    simpa [f, p, x] using hend
  have hjEq : j = k := by
    have heq : f ⟨j, by omega⟩ = f ⟨k, by omega⟩ := by
      dsimp [f]
      simpa [p, x] using hiter.trans hiterEnd.symm
    have hfin := hfInj heq
    exact congrArg Fin.val hfin
  refine ⟨k, ?_, hfInj, ?_, ?_⟩
  · intro i hi
    have hle : i ≤ j := by omega
    simpa [p, x] using hprior i hle
  · simpa [p, x] using hend
  · intro q hqv hqt
    obtain ⟨i, hi, hiter, hprior⟩ := hcover q hqv hqt
    exact ⟨i, hi, by simpa [p, x] using hiter,
      fun j hj => by simpa [p, x] using hprior j hj⟩

private theorem eraseDups_of_nodup_local
    {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (hl : l.Nodup) :
    l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, ht⟩
      rw [List.eraseDups_cons]
      have hfilter : t.filter (fun b => !b == a) = t := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hba : b ≠ a := by
          intro hba
          exact ha (hba ▸ hb)
        simp [hba]
      rw [hfilter, ih ht]

private theorem canonicalOutgoingOrder_internal_eq_iterate_prefix_with_endpoint
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ k₀,
      canonicalOutgoingOrder B v ht =
        List.ofFn (fun i : Fin (k₀ + 1) =>
          B.map.toCombinatorialMap.rot.symm^[i.val]
            (leftmostOutgoing B v ht)) ∧
      B.map.toCombinatorialMap.rot.symm^[k₀] (leftmostOutgoing B v ht) =
        rightmostOutgoing B v ht := by
  classical
  let p : Equiv.Perm D := B.map.toCombinatorialMap.rot.symm
  let x := leftmostOutgoing B v ht
  rcases internalOutgoingPrefix_facts B v hs ht with
    ⟨k, hpreTail, hpreInj, hend, hcover⟩
  let m := k + 1
  let N := orderOf p
  let preList : List D := List.ofFn (fun i : Fin m => p^[i.val] x)
  let scan := finiteRotationScan B x
  let pred : D → Prop := fun d => dartTailVertex B.map d = dartTailVertex B.map x ∧ B.map.tail d
  have hanchor := leftmostOutgoing_internal_characterization B v hs ht
  have hvertexIter : ∀ i, dartTailVertex B.map (p^[i] x) = v := by
    intro i
    induction i with
    | zero => simpa [p, x] using hanchor.1
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact vertexRotationCycle_successor_mem B v ⟨p^[i] x, ih⟩
  have hpreTailFin (i : Fin m) : B.map.tail (p^[i.val] x) := by
    exact hpreTail i.val (by dsimp [m]; omega)
  have hprefixNodup : preList.Nodup := by
    dsimp [preList, m]
    exact List.nodup_ofFn.mpr hpreInj
  have hprefixFilter : preList.filter pred = preList := by
    apply List.filter_eq_self.mpr
    intro d hd
    rw [List.mem_ofFn'] at hd
    rcases hd with ⟨i, hi⟩
    have hp : pred (p^[i.val] x) := by
      exact ⟨(hvertexIter i.val).trans hanchor.1.symm, hpreTailFin i⟩
    rw [← hi]
    exact decide_eq_true hp
  have hNpos : 0 < N := by
    dsimp [N]
    exact orderOf_pos p
  have hperiod : p^[N] x = x := by
    rw [Equiv.Perm.iterate_eq_pow]
    exact congrArg (fun e : Equiv.Perm D => e x) (pow_orderOf_eq_one p)
  have hiterMod (a : ℕ) : p^[a] x = p^[a % N] x := by
    have hdecomp := Nat.mod_add_div a N
    calc
      p^[a] x = p^[a % N + N * (a / N)] x := by
        exact congrArg (fun q : ℕ => p^[q] x) hdecomp.symm
      _ = p^[a % N] (p^[N * (a / N)] x) :=
        Function.iterate_add_apply p (a % N) (N * (a / N)) x
      _ = p^[a % N] x := by
        congr 1
        rw [Function.iterate_mul]
        exact Function.iterate_fixed hperiod (a / N)
  have hmodInj : Function.Injective
      (fun i : Fin m => (⟨i.val % N, Nat.mod_lt _ hNpos⟩ : Fin N)) := by
    intro i j hij
    apply Fin.ext
    have hrem : i.val % N = j.val % N := congrArg Fin.val hij
    have hiter : p^[i.val] x = p^[j.val] x := by
      calc
        p^[i.val] x = p^[i.val % N] x := hiterMod i.val
        _ = p^[j.val % N] x := by rw [hrem]
        _ = p^[j.val] x := (hiterMod j.val).symm
    exact congrArg Fin.val (hpreInj hiter)
  have hmle : m ≤ N := by
    have hcard := Fintype.card_le_of_injective
      (fun i : Fin m => (⟨i.val % N, Nat.mod_lt _ hNpos⟩ : Fin N)) hmodInj
    simpa using hcard
  have hprefixTake : preList = scan.take m := by
    let full : Fin N → D := fun i => p^[i.val] x
    have hscanEq : scan = List.ofFn full := by
      dsimp [scan, finiteRotationScan, full, p, x]
      congr 1
    rw [hscanEq]
    apply List.ext_getElem
    · simp [preList, full, m, hmle]
    · intro n hpre hscan
      have hnM : n < m := by simpa [List.length_take, hmle] using hscan
      have hnN : n < N := lt_of_lt_of_le hnM hmle
      have hleft : preList[n]'hpre = p^[n] x := by
        simpa [preList] using
          (List.getElem_ofFn (f := fun i : Fin m => p^[i.val] x) hpre)
      have hright : ((List.ofFn full).take m)[n]'hscan = p^[n] x := by
        rw [List.getElem_take]
        simp [full]
      simpa using hleft.trans hright.symm
  have hdecomp : scan = preList ++ scan.drop m := by
    calc
      scan = scan.take m ++ scan.drop m := (List.take_append_drop m scan).symm
      _ = preList ++ scan.drop m := congrArg (fun l : List D => l ++ scan.drop m)
        hprefixTake.symm
  have hsuffixSub : ∀ d, d ∈ (scan.drop m).filter pred → d ∈ preList := by
    intro d hd
    have hpred := List.mem_filter.mp hd
    have hp : pred d := of_decide_eq_true hpred.2
    obtain ⟨i, hi, hiter, _⟩ := hcover d (hp.1.trans hanchor.1) hp.2
    change d ∈ List.ofFn (fun j : Fin m => p^[j.val] x)
    rw [List.mem_ofFn']
    refine ⟨⟨i, ?_⟩, ?_⟩
    · dsimp [m]
      omega
    · simpa [m, p, x] using hiter
  have hremoveSubset : ∀ t : List D, (∀ d ∈ t, d ∈ preList) →
      t.removeAll preList = [] := by
    intro t
    induction t with
    | nil => intro _; simp
    | cons a t ih =>
        intro ht
        have ha : a ∈ preList := ht a (by simp)
        have ht' : ∀ d ∈ t, d ∈ preList := by
          intro d hd
          exact ht d (by simp [hd])
        have htail := ih ht'
        simp [List.cons_removeAll, ha, htail]
  have hsuffixRemove : ((scan.drop m).filter pred).removeAll preList = [] :=
    hremoveSubset _ hsuffixSub
  refine ⟨k, ?_, ?_⟩
  · rw [canonicalOutgoingOrder, finiteOutgoingRotationOrder]
    change (scan.filter pred).eraseDups = preList
    rw [hdecomp, List.filter_append, hprefixFilter, List.eraseDups_append]
    rw [eraseDups_of_nodup_local preList hprefixNodup, hsuffixRemove]
    simp
  · simpa [p, x] using hend

/-- At an internal vertex, the canonical outgoing order is exactly the
`rot.symm` segment from `leftmostOutgoing` through `rightmostOutgoing`.
The finite scan may repeat the vertex cycle; later outgoing occurrences are
removed as duplicates. Helper toward `lem-lr-ind` -/
theorem canonicalOutgoingOrder_internal_eq_iterate_prefix
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ k₀,
      canonicalOutgoingOrder B v ht =
        List.ofFn (fun i : Fin (k₀ + 1) =>
          B.map.toCombinatorialMap.rot.symm^[i.val]
            (leftmostOutgoing B v ht)) := by
  obtain ⟨k, horder, _⟩ :=
    canonicalOutgoingOrder_internal_eq_iterate_prefix_with_endpoint B v hs ht
  exact ⟨k, horder⟩

/-- At an internal vertex, the last entry of canonical outgoing order is
`rightmostOutgoing`. Helper toward `lem-lr-ind` -/
theorem canonicalOutgoingOrder_internal_getLast?
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    (canonicalOutgoingOrder B v ht).getLast? = some (rightmostOutgoing B v ht) := by
  obtain ⟨k, horder, hend⟩ :=
    canonicalOutgoingOrder_internal_eq_iterate_prefix_with_endpoint B v hs ht
  rw [horder]
  simp only [List.getLast?_eq_getElem?, List.length_ofFn]
  rw [show k + 1 - 1 = k by omega]
  simp only [List.getElem?_ofFn, show k < k + 1 by omega, ↓reduceDIte]
  simpa using congrArg some hend

/-- Consecutive entries of internal canonical outgoing order are consecutive
`rot.symm` iterates. Helper toward `lem-lr-ind` -/
theorem canonicalOutgoingOrder_internal_consecutive
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink)
    (i : Fin ((canonicalOutgoingOrder B v ht).length - 1)) :
    (canonicalOutgoingOrder B v ht).get
        ⟨i.val + 1, by have := i.isLt; omega⟩ =
      B.map.toCombinatorialMap.rot.symm
        ((canonicalOutgoingOrder B v ht).get
          ⟨i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨k, horder, _⟩ :=
    canonicalOutgoingOrder_internal_eq_iterate_prefix_with_endpoint B v hs ht
  have hlen : (canonicalOutgoingOrder B v ht).length = k + 1 := by
    rw [horder]
    simp
  have hcurBound : i.val < (canonicalOutgoingOrder B v ht).length := by
    have hi := i.isLt
    omega
  have hnextBound : i.val + 1 < (canonicalOutgoingOrder B v ht).length := by
    have hi := i.isLt
    omega
  have hcur : (canonicalOutgoingOrder B v ht).get ⟨i.val, hcurBound⟩ =
      B.map.toCombinatorialMap.rot.symm^[i.val] (leftmostOutgoing B v ht) := by
    have h := List.get_of_eq horder ⟨i.val, hcurBound⟩
    rw [List.get_ofFn] at h
    simpa using h
  have hnext : (canonicalOutgoingOrder B v ht).get ⟨i.val + 1, hnextBound⟩ =
      B.map.toCombinatorialMap.rot.symm^[i.val + 1] (leftmostOutgoing B v ht) := by
    have h := List.get_of_eq horder ⟨i.val + 1, hnextBound⟩
    rw [List.get_ofFn] at h
    simpa using h
  have hstep : B.map.toCombinatorialMap.rot.symm^[i.val + 1]
      (leftmostOutgoing B v ht) =
      B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.rot.symm^[i.val] (leftmostOutgoing B v ht)) := by
    rw [show i.val + 1 = Nat.succ i.val by omega, Function.iterate_succ_apply']
  calc
    (canonicalOutgoingOrder B v ht).get ⟨i.val + 1, by have := i.isLt; omega⟩ =
        B.map.toCombinatorialMap.rot.symm^[i.val + 1]
          (leftmostOutgoing B v ht) := by
      exact hnext
    _ = B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.rot.symm^[i.val] (leftmostOutgoing B v ht)) := hstep
    _ = B.map.toCombinatorialMap.rot.symm
        ((canonicalOutgoingOrder B v ht).get
          ⟨i.val, by have := i.isLt; omega⟩) := by rw [← hcur]

/-- At every left-boundary vertex before the sink, the forward boundary dart
is the first dart in the canonical outgoing order. Helper toward `lem-lr-ind` -/
theorem leftPath_edge_eq_leftmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i < ℓ) :
    B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩ =
      leftmostOutgoing B
        (B.leftPath.vertices.get ⟨i, by rw [B.leftPath.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end B.leftPath i hi) := by
  let v := B.leftPath.vertices.get
    ⟨i, by rw [B.leftPath.vertices_length]; omega⟩
  let d := B.leftPath.darts.get
    ⟨i, by rw [B.leftPath.darts_length]; omega⟩
  change d = leftmostOutgoing B v (simplePath_vertex_ne_end B.leftPath i hi)
  by_cases hi0 : i = 0
  · have hv : v = B.source := by
      simpa [v, hi0] using B.leftPath.start_vertex
    have hfirst : d = B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
      simp [d, SimpleDirectedDartPath.firstDart, hi0, List.get_eq_getElem]
    have hsel : leftmostOutgoing B v (simplePath_vertex_ne_end B.leftPath i hi) =
        leftmostOutgoing B B.source (bipolar_source_ne_sink B) := by
      simp only [hv]
    exact hfirst.trans (leftmostOutgoing_source_eq_firstLeftDart B).symm |>.trans hsel.symm
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hsource : v ≠ B.source := simplePath_vertex_ne_start B.leftPath i hiPos (by omega)
    have hsink : v ≠ B.sink := simplePath_vertex_ne_end B.leftPath i hi
    let j : Fin B.leftPath.darts.length := ⟨i - 1, by
      rw [B.leftPath.darts_length]
      omega⟩
    let k : Fin B.leftPath.darts.length := ⟨i, by
      rw [B.leftPath.darts_length]
      exact hi⟩
    have hstepPrev := B.leftPath.edge_step j
    have hstep := B.leftPath.edge_step k
    have hidx : j.val + 1 = i := by dsimp [j]; omega
    have hface : B.map.toCombinatorialMap.faceSucc (B.leftPath.darts.get j) =
        B.leftPath.darts.get k := by
      simpa [j, k, hidx] using outerFace_leftPath_successor B (i - 1) (by omega)
    have hrotSymm : B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j)) =
          B.leftPath.darts.get k := by
      exact (corner_consecutiveDarts B (B.leftPath.darts.get j)).1.symm.trans hface
    have hrot : B.map.toCombinatorialMap.rot d =
        B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j) := by
      dsimp [d, k] at hrotSymm ⊢
      have := congrArg B.map.toCombinatorialMap.rot hrotSymm
      simpa using this.symm
    have htail : B.map.tail d := hstep.2.1
    have hvertex : dartTailVertex B.map d = v := by
      change dartTailVertex B.map (B.leftPath.darts.get k) = v
      exact hstep.2.2.1.symm
    have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.rot d) := by
      rw [hrot]
      exact (B.map.tail_iff (B.leftPath.darts.get j)
        (B.noMissingDarts (B.leftPath.darts.get j))).mp hstepPrev.2.1
    have hleft := (leftmostOutgoing_internal_characterization B v hsource hsink).2.2.2
      d hvertex htail hnot
    simpa [v] using hleft

/-- The left-boundary dart is the head of canonical outgoing order at every
left-boundary vertex before the sink. Helper toward `lem-lr-ind` -/
theorem canonicalOutgoingOrder_leftPath_head
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i < ℓ) :
    (canonicalOutgoingOrder B
      (B.leftPath.vertices.get ⟨i, by rw [B.leftPath.vertices_length]; omega⟩)
      (simplePath_vertex_ne_end B.leftPath i hi)).head? =
        some (B.leftPath.darts.get ⟨i, by rw [B.leftPath.darts_length]; omega⟩) := by
  rw [canonicalOutgoingOrder_head?, leftPath_edge_eq_leftmostOutgoing B i hi]

/-- At every right-boundary vertex before the sink, the forward boundary dart
is `rightmostOutgoing`. Helper toward `lem-lr-ind` -/
theorem rightPath_edge_eq_rightmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ) (hi : i < r) :
    B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ =
      rightmostOutgoing B
        (B.rightPath.vertices.get ⟨i, by rw [B.rightPath.vertices_length]; omega⟩)
        (simplePath_vertex_ne_end B.rightPath i hi) := by
  let v := B.rightPath.vertices.get
    ⟨i, by rw [B.rightPath.vertices_length]; omega⟩
  let d := B.rightPath.darts.get
    ⟨i, by rw [B.rightPath.darts_length]; omega⟩
  change d = rightmostOutgoing B v (simplePath_vertex_ne_end B.rightPath i hi)
  by_cases hi0 : i = 0
  · have hv : v = B.source := by
      simpa [v, hi0] using B.rightPath.start_vertex
    have hfirst : d = B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
      simp [d, SimpleDirectedDartPath.firstDart, hi0, List.get_eq_getElem]
    have hsel : rightmostOutgoing B v (simplePath_vertex_ne_end B.rightPath i hi) =
        rightmostOutgoing B B.source (bipolar_source_ne_sink B) := by
      simp only [hv]
    exact hfirst.trans (rightmostOutgoing_source_eq_firstRightDart B).symm |>.trans hsel.symm
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hsource := simplePath_vertex_ne_start B.rightPath i hiPos (by omega)
    have hsink := simplePath_vertex_ne_end B.rightPath i hi
    let j : Fin B.rightPath.darts.length := ⟨i - 1, by
      rw [B.rightPath.darts_length]
      omega⟩
    let k : Fin B.rightPath.darts.length := ⟨i, by
      rw [B.rightPath.darts_length]
      exact hi⟩
    have hstepPrev := B.rightPath.edge_step j
    have hstep := B.rightPath.edge_step k
    have hidx : j.val + 1 = i := by dsimp [j]; omega
    have hface : B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k)) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := by
      simpa [j, k, hidx] using outerFace_rightPath_successor B (i - 1) (by omega)
    have hcorner : B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k)) =
        B.map.toCombinatorialMap.rot.symm (B.rightPath.darts.get k) := by
      calc
        B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k)) =
            B.map.toCombinatorialMap.rot.symm
              (B.map.toCombinatorialMap.edgeInv
                (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k))) :=
          (corner_consecutiveDarts B
            (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k))).1
        _ = B.map.toCombinatorialMap.rot.symm (B.rightPath.darts.get k) :=
          congrArg B.map.toCombinatorialMap.rot.symm
            (B.map.toCombinatorialMap.edgeInv_invol _)
    have hrotAtK : B.map.toCombinatorialMap.rot.symm (B.rightPath.darts.get k) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := hcorner.symm.trans hface
    have hrotSymm : B.map.toCombinatorialMap.rot.symm d =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j) := by
      simpa [d, k] using hrotAtK
    have htail : B.map.tail d := hstep.2.1
    have hvertex : dartTailVertex B.map d = v := by
      change dartTailVertex B.map (B.rightPath.darts.get k) = v
      exact hstep.2.2.1.symm
    have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm d) := by
      rw [hrotSymm]
      exact (B.map.tail_iff (B.rightPath.darts.get j)
        (B.noMissingDarts (B.rightPath.darts.get j))).mp hstepPrev.2.1
    have hright := (rightmostOutgoing_internal_characterization B v hsource hsink).2.2.2
      d hvertex htail hnot
    simpa [v] using hright

end DirectedDistances.PlanarMap
