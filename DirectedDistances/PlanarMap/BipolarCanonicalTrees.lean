/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BipolarParentTrees
public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock

/-! # Canonical parent trees along the bipolar boundaries

Helper toward `thm-kmsw` (inverse trees); not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The final
dart of a positive-length simple directed path retains its orientation -/
theorem pathLastDart_tail
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) :
    M.tail (pathLastDart P hn) := by
  let i : Fin P.darts.length := ⟨n - 1, by rw [P.darts_length]; omega⟩
  have h := P.edge_step i
  simpa [pathLastDart, i] using h.2.1

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The final
dart of a positive-length simple directed path ends at the path endpoint -/
theorem pathLastDart_head_eq_end
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) :
    dartHeadVertex M (pathLastDart P hn) = t := by
  let i : Fin P.darts.length := ⟨n - 1, by rw [P.darts_length]; omega⟩
  have h := (P.edge_step i).2.2.2
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hidx : (⟨i.val + 1, by rw [P.vertices_length]; omega⟩ : Fin P.vertices.length) =
      ⟨n, by rw [P.vertices_length]; omega⟩ := Fin.ext hi
  rw [hidx] at h
  simpa [pathLastDart, i] using h.symm.trans P.end_vertex

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
oriented outer boundary is the left path followed by the reversed right path -/
@[expose] def canonicalOuterBoundaryDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : List D :=
  B.leftPath.darts ++ B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The -/
theorem canonicalOuterBoundaryDarts_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (canonicalOuterBoundaryDarts B).Nodup := by
  simpa [canonicalOuterBoundaryDarts] using
    B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
outer-boundary list has the `ℓ + r` boundary darts -/
theorem canonicalOuterBoundaryDarts_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (canonicalOuterBoundaryDarts B).length = ℓ + r := by
  simp [canonicalOuterBoundaryDarts, B.leftPath.darts_length,
    B.rightPath.darts_length]

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. Every dart
in the prescribed boundary list lies on the outer face -/
theorem canonicalOuterBoundaryDarts_mem_isOuter
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ canonicalOuterBoundaryDarts B) : B.map.IsOuter d := by
  have hword : d ∈ B.outerWord.letters :=
    (B.outerSplit.2.1.perm.mem_iff).mpr (by
      simpa [canonicalOuterBoundaryDarts] using hd)
  exact (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mp hword

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. On an
outer dart, face succession follows the cyclic order of the canonical -/
theorem canonicalOuterBoundaryDarts_faceSucc_eq_formPerm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d =
      (canonicalOuterBoundaryDarts B).formPerm d := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hd
  calc
    B.map.toCombinatorialMap.faceSucc d = B.outerWord.letters.formPerm d :=
      B.outerSplit.1.2.2 d hword
    _ = (canonicalOuterBoundaryDarts B).formPerm d := by
      simpa [canonicalOuterBoundaryDarts] using congrArg (fun f : Equiv.Perm D => f d)
        (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At every
nonterminal left-boundary vertex, the outer face passes from its incoming -/
theorem outerFace_leftPath_successor
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i + 1 < ℓ) :
    B.map.toCombinatorialMap.faceSucc
        (B.leftPath.darts[i]'(by rw [B.leftPath.darts_length]; omega)) =
      B.leftPath.darts[i + 1]'(by rw [B.leftPath.darts_length]; omega) := by
  have hlefti : i < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    omega
  have hleftNext : i + 1 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact hi
  have hxi : i < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    omega
  have hxnext : i + 1 < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    omega
  have hmod : (i + 1) % (ℓ + r) < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    exact Nat.mod_lt _ (by omega)
  have hxi_eq : (canonicalOuterBoundaryDarts B)[i]'hxi = B.leftPath.darts[i]'hlefti := by
    simpa [canonicalOuterBoundaryDarts] using
      (List.getElem_append_left hlefti :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i] =
          B.leftPath.darts[i])
  have hxnext_eq : (canonicalOuterBoundaryDarts B)[i + 1]'hxnext =
      B.leftPath.darts[i + 1]'hleftNext := by
    simpa [canonicalOuterBoundaryDarts] using
      (List.getElem_append_left hleftNext :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[i + 1] =
          B.leftPath.darts[i + 1])
  have houter : B.map.IsOuter ((canonicalOuterBoundaryDarts B)[i]'hxi) :=
    canonicalOuterBoundaryDarts_mem_isOuter B (List.getElem_mem hxi)
  have hsucc : B.map.toCombinatorialMap.faceSucc ((canonicalOuterBoundaryDarts B)[i]'hxi) =
      (canonicalOuterBoundaryDarts B)[(i + 1) % (ℓ + r)]'hmod := by
    rw [canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B houter]
    simpa only [canonicalOuterBoundaryDarts_length] using
      List.formPerm_apply_getElem (canonicalOuterBoundaryDarts B)
      (canonicalOuterBoundaryDarts_nodup B) i hxi
  have hsucc' : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[i]'hxi) =
      (canonicalOuterBoundaryDarts B)[i + 1]'hxnext := by
    have hiLt : i + 1 < ℓ + r := by omega
    have hmodEq : (i + 1) % (ℓ + r) = i + 1 := Nat.mod_eq_of_lt hiLt
    simpa only [hmodEq] using hsucc
  rw [← hxi_eq, ← hxnext_eq]
  exact hsucc'

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. On the
reversed right-boundary arc, the outer face passes from the reverse of the
next right-path dart to the reverse of the preceding one -/
theorem outerFace_rightPath_successor
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i + 1 < r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.darts[i + 1]'(by rw [B.rightPath.darts_length]; omega))) =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i]'(by rw [B.rightPath.darts_length]; omega)) := by
  let k := r - 2 - i
  let p := ℓ + k
  have hrighti : i < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    omega
  have hrightNext : i + 1 < B.rightPath.darts.length := by
    rw [B.rightPath.darts_length]
    exact hi
  have hp : p < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    dsimp [p, k]
    omega
  have hpNext : p + 1 < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    dsimp [p, k]
    omega
  have hp' : p < (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simpa [canonicalOuterBoundaryDarts] using hp
  have hpNext' : p + 1 < (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv).length := by
    simpa [canonicalOuterBoundaryDarts] using hpNext
  have hreverse : k < B.rightPath.darts.reverse.length := by
    simp [B.rightPath.darts_length, k]
    omega
  have hreverseNext : k + 1 < B.rightPath.darts.reverse.length := by
    simp [B.rightPath.darts_length, k]
    omega
  have hcurrent : (canonicalOuterBoundaryDarts B)[p]'hp =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i + 1]'hrightNext) := by
    change (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[p]'hp' = _
    have hsplit : p - B.leftPath.darts.length = k := by
      rw [B.leftPath.darts_length]
      dsimp [p]
      omega
    have hrev := List.getElem_reverse (l := B.rightPath.darts) (i := k) hreverse
    have hindex : B.rightPath.darts.length - 1 - k = i + 1 := by
      rw [B.rightPath.darts_length]
      dsimp [k]
      omega
    have hrev' : B.rightPath.darts.reverse[k]'hreverse =
        B.rightPath.darts[i + 1]'hrightNext := by
      simpa only [hindex] using hrev
    have hmap : (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[k]'(by
        simpa using hreverse) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts[i + 1]'hrightNext) := by
      rw [List.getElem_map]
      exact congrArg B.map.toCombinatorialMap.edgeInv hrev'
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [p, k]; omega)]
    simpa only [hsplit] using hmap
  have hnext : (canonicalOuterBoundaryDarts B)[p + 1]'hpNext =
      B.map.toCombinatorialMap.edgeInv
        (B.rightPath.darts[i]'hrighti) := by
    change (B.leftPath.darts ++
      B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[p + 1]'hpNext' = _
    have hsplit : (p + 1) - B.leftPath.darts.length = k + 1 := by
      rw [B.leftPath.darts_length]
      dsimp [p]
      omega
    have hrev := List.getElem_reverse (l := B.rightPath.darts) (i := k + 1) hreverseNext
    have hindex : B.rightPath.darts.length - 1 - (k + 1) = i := by
      rw [B.rightPath.darts_length]
      dsimp [k]
      omega
    have hrev' : B.rightPath.darts.reverse[k + 1]'hreverseNext =
        B.rightPath.darts[i]'hrighti := by
      simpa only [hindex] using hrev
    have hmap : (B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[k + 1]'(by
        simpa using hreverseNext) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts[i]'hrighti) := by
      rw [List.getElem_map]
      exact congrArg B.map.toCombinatorialMap.edgeInv hrev'
    rw [List.getElem_append_right (by rw [B.leftPath.darts_length]; dsimp [p, k]; omega)]
    simpa only [hsplit] using hmap
  have hmod : (p + 1) % (ℓ + r) < (canonicalOuterBoundaryDarts B).length := by
    rw [canonicalOuterBoundaryDarts_length]
    exact Nat.mod_lt _ (by omega)
  have houter : B.map.IsOuter ((canonicalOuterBoundaryDarts B)[p]'hp) :=
    canonicalOuterBoundaryDarts_mem_isOuter B (List.getElem_mem hp)
  have hsucc : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[p]'hp) =
      (canonicalOuterBoundaryDarts B)[(p + 1) % (ℓ + r)]'hmod := by
    rw [canonicalOuterBoundaryDarts_faceSucc_eq_formPerm B houter]
    simpa only [canonicalOuterBoundaryDarts_length] using
      List.formPerm_apply_getElem (canonicalOuterBoundaryDarts B)
        (canonicalOuterBoundaryDarts_nodup B) p hp
  have hmodEq : (p + 1) % (ℓ + r) = p + 1 :=
    Nat.mod_eq_of_lt (by rw [canonicalOuterBoundaryDarts_length] at hpNext; omega)
  have hsucc' : B.map.toCombinatorialMap.faceSucc
      ((canonicalOuterBoundaryDarts B)[p]'hp) =
      (canonicalOuterBoundaryDarts B)[p + 1]'hpNext := by
    simpa only [hmodEq] using hsucc
  rw [← hcurrent, ← hnext]
  exact hsucc'

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. A
positive-index vertex on a simple directed path differs from its start -/
theorem simplePath_vertex_ne_start
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : ℕ)
    (hi0 : 0 < i) (hin : i ≤ n) :
    P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ≠ s := by
  intro h
  let j : Fin P.vertices.length := ⟨i, by rw [P.vertices_length]; omega⟩
  let j₀ : Fin P.vertices.length := ⟨0, by rw [P.vertices_length]; omega⟩
  have hget : P.vertices.get j = P.vertices.get j₀ := by
    calc
      P.vertices.get j = s := h
      _ = P.vertices.get j₀ := P.start_vertex.symm
  have hidx := P.vertices_nodup.get_inj_iff.mp hget
  have hval := congrArg Fin.val hidx
  dsimp [j, j₀] at hval
  omega

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. A
`i`-th vertex before the end of a simple directed path differs from its end -/
theorem simplePath_vertex_ne_end
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (i : ℕ)
    (hi : i < n) :
    P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩ ≠ t := by
  intro h
  let j : Fin P.vertices.length := ⟨i, by rw [P.vertices_length]; omega⟩
  let jn : Fin P.vertices.length := ⟨n, by rw [P.vertices_length]; omega⟩
  have hget : P.vertices.get j = P.vertices.get jn := by
    calc
      P.vertices.get j = t := h
      _ = P.vertices.get jn := P.end_vertex.symm
  have hidx := P.vertices_nodup.get_inj_iff.mp hget
  have hval := congrArg Fin.val hidx
  dsimp [j, jn] at hval
  omega

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At each
non-source vertex, the canonical upper-left selector keeps the forward dart -/
@[expose] noncomputable def canonicalULSelector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : IncomingSelector B := by
  classical
  intro v hv
  have hqv : dartTailVertex B.map (leftmostIncoming B v hv) = v := by
    by_cases ht : v = B.sink
    · subst v
      rw [incomingSelectors_sink_boundary B |>.1]
      change dartHeadVertex B.map
        (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) = B.sink
      exact pathLastDart_head_eq_end B.leftPath
        (Nat.zero_lt_of_lt B.left_length_pos)
    · exact (leftmostIncoming_internal_characterization B v hv ht).1
  have hqnot : ¬ B.map.tail (leftmostIncoming B v hv) := by
    by_cases ht : v = B.sink
    · subst v
      rw [incomingSelectors_sink_boundary B |>.1]
      have hlast := pathLastDart_tail B.leftPath
        (Nat.zero_lt_of_lt B.left_length_pos)
      exact (B.map.tail_iff _ (B.noMissingDarts _)).mp hlast
    · exact (leftmostIncoming_internal_characterization B v hv ht).2.1
  let q := leftmostIncoming B v hv
  have hforward : B.map.tail (B.map.toCombinatorialMap.edgeInv q) := by
    have hiff := B.map.tail_iff q (B.noMissingDarts q)
    exact Classical.byContradiction fun h => hqnot (hiff.mpr h)
  refine ⟨B.map.toCombinatorialMap.edgeInv q, B.noMissingDarts _, hforward, ?_⟩
  simpa [dartHeadVertex, dartTailVertex,
    B.map.toCombinatorialMap.edgeInv_invol] using hqv

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At each
non-sink vertex, the canonical lower-right selector keeps the rightmost -/
@[expose] noncomputable def canonicalLRSelector
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : OutgoingSelector B := by
  classical
  intro v hv
  by_cases hs : v = B.source
  · subst v
    refine ⟨rightmostOutgoing B B.source (bipolar_source_ne_sink B),
      B.noMissingDarts _, ?_, ?_⟩
    · rw [rightmostOutgoing_source_eq_firstRightDart B]
      have hstep := B.rightPath.edge_step
        ⟨0, by rw [B.rightPath.darts_length]; exact Nat.zero_lt_of_lt B.right_length_pos⟩
      simpa [SimpleDirectedDartPath.firstDart] using hstep.2.1
    · rw [rightmostOutgoing_source_eq_firstRightDart B]
      have hstep := B.rightPath.edge_step
        ⟨0, by rw [B.rightPath.darts_length]; exact Nat.zero_lt_of_lt B.right_length_pos⟩
      have hstart := hstep.2.2.1
      simpa [SimpleDirectedDartPath.firstDart, dartTailVertex] using
        hstart.symm.trans B.rightPath.start_vertex
  · obtain ⟨hbase, htail, _, _⟩ := rightmostOutgoing_internal_characterization B v hs hv
    exact ⟨rightmostOutgoing B v hv, B.noMissingDarts _, htail, hbase⟩

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical upper-left height is the parent depth for the leftmost incoming -/
noncomputable abbrev canonicalULHeight
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : MapVertex B.map → ℕ :=
  ulHeight B (canonicalULSelector B)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical lower-right height is the parent depth for the rightmost outgoing -/
noncomputable abbrev canonicalLRHeight
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : MapVertex B.map → ℕ :=
  lrHeight B (canonicalLRSelector B)

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical upper-left selector returns the forward dart of the named -/
theorem canonicalULSelector_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hv : v ≠ B.source) :
    (canonicalULSelector B v hv).val =
      B.map.toCombinatorialMap.edgeInv (leftmostIncoming B v hv) := by
  rfl

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical lower-right selector returns the named rightmost outgoing dart -/
theorem canonicalLRSelector_val
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hv : v ≠ B.sink) :
    (canonicalLRSelector B v hv).val = rightmostOutgoing B v hv := by
  by_cases hs : v = B.source
  · subst v
    simp [canonicalLRSelector]
  · simp [canonicalLRSelector, hs]

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At each
positive-index vertex of the left boundary, the selected upper-left dart is -/
theorem canonicalULSelector_leftPath_edge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi0 : 0 < i) (hiℓ : i ≤ ℓ) :
    (canonicalULSelector B
      (B.leftPath.vertices.get ⟨i, by rw [B.leftPath.vertices_length]; omega⟩)
      (simplePath_vertex_ne_start B.leftPath i hi0 hiℓ)).val =
    B.leftPath.darts.get ⟨i - 1, by rw [B.leftPath.darts_length]; omega⟩ := by
  let vi := B.leftPath.vertices.get
    ⟨i, by rw [B.leftPath.vertices_length]; omega⟩
  let hv := simplePath_vertex_ne_start B.leftPath i hi0 hiℓ
  change (canonicalULSelector B vi hv).val =
    B.leftPath.darts.get ⟨i - 1, by rw [B.leftPath.darts_length]; omega⟩
  by_cases hisink : i = ℓ
  · have hvi : vi = B.sink := by
      simpa [vi, hisink] using B.leftPath.end_vertex
    have hleftmost : leftmostIncoming B vi hv =
        B.map.toCombinatorialMap.edgeInv
          (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) := by
      simpa only [hvi] using incomingSelectors_sink_boundary B |>.1
    calc
      (canonicalULSelector B vi hv).val =
          B.map.toCombinatorialMap.edgeInv (leftmostIncoming B vi hv) :=
        canonicalULSelector_val B vi hv
      _ = B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.edgeInv
            (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos))) := by
        rw [hleftmost]
      _ = pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) :=
        B.map.toCombinatorialMap.edgeInv_invol _
      _ = B.leftPath.darts.get ⟨i - 1, by rw [B.leftPath.darts_length]; omega⟩ := by
        simp [pathLastDart, hisink]
  · have hiLt : i < ℓ := by omega
    have hsource := simplePath_vertex_ne_start B.leftPath i hi0 hiℓ
    have hsink := simplePath_vertex_ne_end B.leftPath i hiLt
    let j : Fin B.leftPath.darts.length := ⟨i - 1, by
      rw [B.leftPath.darts_length]
      omega⟩
    let k : Fin B.leftPath.darts.length := ⟨i, by
      rw [B.leftPath.darts_length]
      exact hiLt⟩
    have hstep := B.leftPath.edge_step j
    have hnext := B.leftPath.edge_step k
    have hja : j.val + 1 = i := by
      dsimp [j]
      omega
    have hvertexIdx :
        (⟨j.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ :
          Fin B.leftPath.vertices.length) =
        ⟨i, by rw [B.leftPath.vertices_length]; omega⟩ := by
      apply Fin.ext
      exact hja
    have hbase : dartTailVertex B.map
        (B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j)) = vi := by
      change dartHeadVertex B.map (B.leftPath.darts.get j) = vi
      calc
        dartHeadVertex B.map (B.leftPath.darts.get j) =
            B.leftPath.vertices.get ⟨j.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ :=
          hstep.2.2.2.symm
        _ = vi := by
          simp only [vi]
          rw [hvertexIdx]
    have hnot : ¬ B.map.tail
        (B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j)) :=
      (B.map.tail_iff _ hstep.1).mp hstep.2.1
    have hface : B.map.toCombinatorialMap.faceSucc (B.leftPath.darts.get j) =
        B.leftPath.darts.get k := by
      have hiIdx : i - 1 + 1 = i := by omega
      simpa [j, k, hiIdx] using outerFace_leftPath_successor B (i - 1) (by omega)
    have hrot : B.map.tail
        (B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j))) := by
      have hcorner := (corner_consecutiveDarts B (B.leftPath.darts.get j)).1
      rw [← hcorner, hface]
      exact hnext.2.1
    have hunique := (leftmostIncoming_internal_characterization B vi hsource hsink).2.2.2
    have hleft : leftmostIncoming B vi hsource =
        B.map.toCombinatorialMap.edgeInv (B.leftPath.darts.get j) := by
      exact (hunique _ hbase hnot hrot).symm
    calc
      (canonicalULSelector B vi hv).val =
          B.map.toCombinatorialMap.edgeInv (leftmostIncoming B vi hv) :=
        canonicalULSelector_val B vi hv
      _ = B.leftPath.darts.get j := by
        rw [hleft]
        exact B.map.toCombinatorialMap.edgeInv_invol _
      _ = B.leftPath.darts.get ⟨i - 1, by rw [B.leftPath.darts_length]; omega⟩ := by
        rfl

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. At every
right-boundary vertex before the sink, the lower-right selector chooses the -/
theorem canonicalLRSelector_rightPath_edge
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i < r) :
    (canonicalLRSelector B
      (B.rightPath.vertices.get ⟨i, by rw [B.rightPath.vertices_length]; omega⟩)
      (simplePath_vertex_ne_end B.rightPath i hi)).val =
    B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ := by
  let vi := B.rightPath.vertices.get
    ⟨i, by rw [B.rightPath.vertices_length]; omega⟩
  let hv := simplePath_vertex_ne_end B.rightPath i hi
  change (canonicalLRSelector B vi hv).val =
    B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩
  by_cases hi0 : i = 0
  · have hvi : vi = B.source := by
      simpa [vi, hi0] using B.rightPath.start_vertex
    have hrightmost : rightmostOutgoing B vi hv =
        B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
      simpa only [hvi] using rightmostOutgoing_source_eq_firstRightDart B
    calc
      (canonicalLRSelector B vi hv).val = rightmostOutgoing B vi hv :=
        canonicalLRSelector_val B vi hv
      _ = B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ := by
        rw [hrightmost]
        simp [SimpleDirectedDartPath.firstDart, hi0]
  · have hi0' : 0 < i := by omega
    have hsource := simplePath_vertex_ne_start B.rightPath i hi0' (by omega)
    have hsink := simplePath_vertex_ne_end B.rightPath i hi
    let j : Fin B.rightPath.darts.length := ⟨i, by
      rw [B.rightPath.darts_length]
      exact hi⟩
    let k : Fin B.rightPath.darts.length := ⟨i - 1, by
      rw [B.rightPath.darts_length]
      omega⟩
    have hstep := B.rightPath.edge_step j
    have hprev := B.rightPath.edge_step k
    have hji : j.val = i := by rfl
    have hvertexIdx :
        (⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩ :
          Fin B.rightPath.vertices.length) =
        ⟨i, by rw [B.rightPath.vertices_length]; omega⟩ := Fin.ext hji
    have hbase : dartTailVertex B.map (B.rightPath.darts.get j) = vi := by
      calc
        dartTailVertex B.map (B.rightPath.darts.get j) =
            B.rightPath.vertices.get ⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩ :=
          hstep.2.2.1.symm
        _ = vi := by
          change B.rightPath.vertices.get
            ⟨j.val, by rw [B.rightPath.vertices_length]; omega⟩ =
            B.rightPath.vertices.get
              ⟨i, by rw [B.rightPath.vertices_length]; omega⟩
          rw [hvertexIdx]
    have hrotEq : B.map.toCombinatorialMap.rot.symm (B.rightPath.darts.get j) =
        B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j)) := by
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using
        (corner_consecutiveDarts B (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.darts.get j))).1.symm
    have hface : B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get j)) =
        B.map.toCombinatorialMap.edgeInv (B.rightPath.darts.get k) := by
      have hiIdx : i - 1 + 1 = i := by omega
      simpa [j, k, hiIdx] using outerFace_rightPath_successor B (i - 1) (by omega)
    have hnot : ¬ B.map.tail
        (B.map.toCombinatorialMap.rot.symm (B.rightPath.darts.get j)) := by
      rw [hrotEq, hface]
      exact (B.map.tail_iff _ hprev.1).mp hprev.2.1
    have hunique := (rightmostOutgoing_internal_characterization B vi hsource hsink).2.2.2
    have hrightmost : rightmostOutgoing B vi hsink = B.rightPath.darts.get j := by
      exact (hunique _ hbase hstep.2.1 hnot).symm
    calc
      (canonicalLRSelector B vi hv).val = rightmostOutgoing B vi hv :=
        canonicalLRSelector_val B vi hv
      _ = B.rightPath.darts.get j := by
        rw [hrightmost]
      _ = B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ := by
        rfl

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical upper-left height of the `i`-th left-boundary vertex equals `i` -/
theorem canonicalULHeight_leftPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i ≤ ℓ) :
    canonicalULHeight B
      (B.leftPath.vertices.get ⟨i, by rw [B.leftPath.vertices_length]; omega⟩) = i := by
  classical
  induction i with
  | zero =>
      change ulHeight B (canonicalULSelector B)
        (B.leftPath.vertices.get ⟨0, by rw [B.leftPath.vertices_length]; omega⟩) = 0
      rw [B.leftPath.start_vertex]
      exact ulHeight_source B (canonicalULSelector B)
  | succ i ih =>
      have hiPrev : i ≤ ℓ := by omega
      have hiSucc : i + 1 ≤ ℓ := by omega
      have hsource := simplePath_vertex_ne_start B.leftPath (i + 1) (by omega) hiSucc
      let vi := B.leftPath.vertices.get
        ⟨i, by rw [B.leftPath.vertices_length]; omega⟩
      let vnext := B.leftPath.vertices.get
        ⟨i + 1, by rw [B.leftPath.vertices_length]; omega⟩
      have hparent : ulParent B (canonicalULSelector B) vnext = vi := by
        by_cases h : vnext = B.source
        · exact (hsource h).elim
        · simp [ulParent, h]
          rw [canonicalULSelector_leftPath_edge B (i + 1) (by omega) hiSucc]
          have hstep := B.leftPath.edge_step
            ⟨i, by rw [B.leftPath.darts_length]; omega⟩
          exact hstep.2.2.1.symm
      change ulHeight B (canonicalULSelector B) vnext = i + 1
      rw [ulHeight_parent B (canonicalULSelector B) hsource, hparent]
      have hprev := ih hiPrev
      change ulHeight B (canonicalULSelector B) vi = i at hprev
      omega

/-- Helper toward `thm-kmsw` (inverse trees); not the paper result. The
canonical lower-right height of the `i`-th right-boundary vertex equals -/
theorem canonicalLRHeight_rightPath
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (i : ℕ)
    (hi : i ≤ r) :
    canonicalLRHeight B
      (B.rightPath.vertices.get ⟨i, by rw [B.rightPath.vertices_length]; omega⟩) = r - i := by
  classical
  have haux : ∀ k, k ≤ r →
      canonicalLRHeight B
        (B.rightPath.vertices.get ⟨r - k, by rw [B.rightPath.vertices_length]; omega⟩) = k := by
    intro k
    induction k with
    | zero =>
        intro _
        change lrHeight B (canonicalLRSelector B)
          (B.rightPath.vertices.get ⟨r, by rw [B.rightPath.vertices_length]; omega⟩) = 0
        rw [B.rightPath.end_vertex]
        exact lrHeight_sink B (canonicalLRSelector B)
    | succ k ih =>
        intro hk
        have hq : r - (k + 1) < r := by omega
        have hqle : r - (k + 1) ≤ r := by omega
        let q := r - (k + 1)
        let v := B.rightPath.vertices.get
          ⟨q, by rw [B.rightPath.vertices_length]; omega⟩
        let vnext := B.rightPath.vertices.get
          ⟨r - k, by rw [B.rightPath.vertices_length]; omega⟩
        have hsink := simplePath_vertex_ne_end B.rightPath q (by dsimp [q]; exact hq)
        have hparent : lrParent B (canonicalLRSelector B) v = vnext := by
          by_cases h : v = B.sink
          · exact (hsink h).elim
          · simp [lrParent, h]
            rw [canonicalLRSelector_rightPath_edge B q hq]
            have hstep := B.rightPath.edge_step
              ⟨q, by rw [B.rightPath.darts_length]; exact hq⟩
            have hidx : q + 1 = r - k := by dsimp [q]; omega
            calc
              dartHeadVertex B.map
                  (B.rightPath.darts.get ⟨q, by rw [B.rightPath.darts_length]; exact hq⟩) =
                  B.rightPath.vertices.get
                    ⟨q + 1, by rw [B.rightPath.vertices_length]; omega⟩ :=
                hstep.2.2.2.symm
              _ = vnext := by
                simp only [vnext]
                have hfin :
                    (⟨q + 1, by rw [B.rightPath.vertices_length]; omega⟩ :
                      Fin B.rightPath.vertices.length) =
                    ⟨r - k, by rw [B.rightPath.vertices_length]; omega⟩ := Fin.ext hidx
                rw [hfin]
        have hheight : canonicalLRHeight B v =
            canonicalLRHeight B vnext + 1 := by
          change lrHeight B (canonicalLRSelector B) v =
            lrHeight B (canonicalLRSelector B) vnext + 1
          have hstep := lrHeight_parent B (canonicalLRSelector B) hsink
          rw [hparent] at hstep
          simpa [v, vnext] using hstep
        have hrec := ih (by omega)
        have hrec' : canonicalLRHeight B vnext = k := by
          simpa [vnext] using hrec
        change canonicalLRHeight B v = k + 1
        rw [hheight, hrec']
  have hk : r - i ≤ r := by omega
  have h := haux (r - i) hk
  have hindex : r - (r - i) = i := by omega
  simpa only [hindex] using h

end DirectedDistances.PlanarMap
