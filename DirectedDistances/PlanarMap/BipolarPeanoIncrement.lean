module

public import DirectedDistances.PlanarMap.BipolarPeanoContour
public import DirectedDistances.PlanarMap.BipolarCanonicalTrees

/-! # Heights along the upper-left contour -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)

/-- The upper-left height increases by one along the canonical incoming edge. -/
theorem canonicalULHeight_leftmostIncoming
    (v : MapVertex B.map) (hv : v ≠ B.source) :
    canonicalULHeight B v =
      canonicalULHeight B (dartHeadVertex B.map (leftmostIncoming B v hv)) + 1 := by
  have hp := ulHeight_parent B (canonicalULSelector B) hv
  have he : ulParent B (canonicalULSelector B) v =
      dartHeadVertex B.map (leftmostIncoming B v hv) := by
    simp only [ulParent, dite_eq_right hv, canonicalULSelector_val]
    rfl
  rw [he] at hp
  exact hp

/-- The lower-right height decreases by one along the canonical outgoing edge. -/
theorem canonicalLRHeight_rightmostOutgoing
    (v : MapVertex B.map) (hv : v ≠ B.sink) :
    canonicalLRHeight B v =
      canonicalLRHeight B (dartHeadVertex B.map (rightmostOutgoing B v hv)) + 1 := by
  have hp := lrHeight_parent B (canonicalLRSelector B) hv
  have he : lrParent B (canonicalLRSelector B) v =
      dartHeadVertex B.map (rightmostOutgoing B v hv) := by
    simp only [lrParent, dite_eq_right hv, canonicalLRSelector_val]
  rw [he] at hp
  exact hp

private theorem increment_rot_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem increment_face_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) =
      dartHeadVertex B.map d := by
  apply Quotient.sound
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
    (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.edgeInv d))
    (B.map.toCombinatorialMap.edgeInv d)
  exact ⟨1, by simp⟩

private theorem increment_inverse_forward (d : D) (hd : ¬ B.map.tail d) :
    B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  by_contra h
  exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 h)

private theorem increment_forward_tail_ne_sink (d : D) (hd : B.map.tail d) :
    dartTailVertex B.map d ≠ B.sink := by
  intro h
  exact B.isSink ⟨dartHeadVertex B.map d, d, B.noMissingDarts d, hd, h, rfl⟩

private theorem increment_next_forward (a : D) (ha : B.map.tail a)
    (hb : B.map.tail (contourNext B a)) :
    ((canonicalULHeight B (dartTailVertex B.map (contourNext B a)) : ℤ) -
        canonicalULHeight B (dartTailVertex B.map a),
      (canonicalLRHeight B (dartHeadVertex B.map (contourNext B a)) : ℤ) -
        canonicalLRHeight B (dartHeadVertex B.map a)) = (1, -1) := by
  classical
  have hs := contour_forward_head_ne_source B a ha
  have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  by_cases hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs
  · by_cases ht : dartHeadVertex B.map a = B.sink
    · simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_left ht] at hb
      exact (hn hb).elim
    · have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
        simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
      have htail : dartTailVertex B.map (contourNext B a) = dartHeadVertex B.map a := by
        rw [he, ← canonicalLRSelector_val B _ ht]
        exact (canonicalLRSelector B _ ht).property.2.2
      have hul := canonicalULHeight_leftmostIncoming B (dartHeadVertex B.map a) hs
      rw [← hsel] at hul
      simp only [dartHeadVertex, B.map.toCombinatorialMap.edgeInv_invol] at hul
      have hlr := canonicalLRHeight_rightmostOutgoing B (dartHeadVertex B.map a) ht
      rw [← he] at hlr
      apply Prod.ext
      · dsimp
        rw [htail]
        change canonicalULHeight B (dartHeadVertex B.map a) =
          canonicalULHeight B (dartTailVertex B.map a) + 1 at hul
        omega
      · dsimp
        omega
  · simp only [contourNext, dite_eq_left ha, ite_eq_right hsel] at hb
    exact (hn hb).elim

private theorem increment_bounce_face_reverse (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a) :
    ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc a) := by
  classical
  intro hf
  have hs := contour_forward_head_ne_source B a ha
  have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  have ht : dartHeadVertex B.map a ≠ B.sink := by
    rw [← increment_face_vertex B a]
    exact increment_forward_tail_ne_sink B _ hf
  have hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs :=
    (leftmostIncoming_internal_characterization B _ hs ht).2.2.2 _ rfl hn hf
  have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
    simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
  have hforward : B.map.tail (rightmostOutgoing B (dartHeadVertex B.map a) ht) := by
    rw [← canonicalLRSelector_val B _ ht]
    exact (canonicalLRSelector B _ ht).property.2.1
  rw [← he, hb] at hforward
  exact hn hforward

private theorem increment_triangle_close (a : D) (hi : ¬ B.map.IsOuter a) :
    B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a) =
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) := by
  have h := (B.innerFacesDegreeThree a hi).1
  change B.map.toCombinatorialMap.rot.symm
    (B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a))) = a at h
  have h' := congrArg B.map.toCombinatorialMap.rot h
  simp only [Equiv.apply_symm_apply] at h'
  have h'' := congrArg B.map.toCombinatorialMap.edgeInv h'
  simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h''

private theorem increment_triangle_rotation (a : D) (hi : ¬ B.map.IsOuter a) :
    B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) =
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
  have h := increment_triangle_close B a hi
  change B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)) =
    B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) at h
  have h' := congrArg B.map.toCombinatorialMap.rot h
  simpa only [Equiv.apply_symm_apply] using h'.symm

private theorem increment_bounce_inner (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a)
    (hi : ¬ B.map.IsOuter a) :
    let c := B.map.toCombinatorialMap.rot a
    let b := B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)
    B.map.tail b ∧
      (B.map.tail c →
        ((canonicalULHeight B (dartTailVertex B.map c) : ℤ) -
            canonicalULHeight B (dartTailVertex B.map a),
          (canonicalLRHeight B (dartHeadVertex B.map c) : ℤ) -
            canonicalLRHeight B (dartHeadVertex B.map a)) = (0, 1)) ∧
      (¬ B.map.tail c →
        ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
            canonicalULHeight B (dartTailVertex B.map a),
          (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
            canonicalLRHeight B (dartHeadVertex B.map a)) = (-1, 0)) := by
  classical
  dsimp only
  let c := B.map.toCombinatorialMap.rot a
  let b := B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)
  have hf := increment_bounce_face_reverse B a ha hb
  have hbf : B.map.tail b := increment_inverse_forward B _ hf
  have hclose := increment_triangle_close B a hi
  have hbt : dartTailVertex B.map b = dartHeadVertex B.map c := by
    have hv := increment_face_vertex B (B.map.toCombinatorialMap.faceSucc a)
    rw [hclose] at hv
    exact hv.symm
  have hbh : dartHeadVertex B.map b = dartHeadVertex B.map a := by
    simpa only [b, dartHeadVertex, dartTailVertex,
      B.map.toCombinatorialMap.edgeInv_invol] using
      increment_face_vertex B a
  refine ⟨hbf, ?_, ?_⟩
  · intro hc
    have hs := contour_forward_head_ne_source B c hc
    have ht : dartHeadVertex B.map c ≠ B.sink := by
      rw [← hbt]
      exact increment_forward_tail_ne_sink B b hbf
    have hprev : ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm b) := by
      have he : B.map.toCombinatorialMap.rot.symm b =
          B.map.toCombinatorialMap.edgeInv c := by
        exact hclose
      rw [he]
      exact (B.map.tail_iff c (B.noMissingDarts c)).1 hc
    have hsel : b = rightmostOutgoing B (dartHeadVertex B.map c) ht :=
      (rightmostOutgoing_internal_characterization B _ hs ht).2.2.2 b hbt hbf hprev
    have hlr := canonicalLRHeight_rightmostOutgoing B _ ht
    rw [← hsel, hbh] at hlr
    dsimp only [c] at hlr
    apply Prod.ext
    · dsimp
      rw [increment_rot_vertex B a]
      omega
    · dsimp
      omega
  · intro hc
    have hs : dartTailVertex B.map a ≠ B.source := by
      intro he
      exact hc (tail_of_dartTailVertex_eq_source B c
        ((increment_rot_vertex B a).trans he))
    have ht := increment_forward_tail_ne_sink B a ha
    have hprev : B.map.tail (B.map.toCombinatorialMap.rot.symm c) := by
      simpa only [c, Equiv.symm_apply_apply] using ha
    have hsel : c = leftmostIncoming B (dartTailVertex B.map a) hs :=
      (leftmostIncoming_internal_characterization B _ hs ht).2.2.2
        c (increment_rot_vertex B a) hc hprev
    have hul := canonicalULHeight_leftmostIncoming B _ hs
    rw [← hsel, ← hbt] at hul
    dsimp only [b] at hul
    apply Prod.ext
    · dsimp
      omega
    · dsimp
      rw [hbh]
      omega

private theorem increment_bounce_outer (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a)
    (ho : B.map.IsOuter a) :
    a = pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) := by
  classical
  have hmem : a ∈ B.leftPath.darts := (B.outerSplit.2.2.1 a).mpr
    ⟨B.noMissingDarts a, ha, ho⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
  let a := B.leftPath.darts.get i
  change B.map.tail a at ha
  change contourNext B a = B.map.toCombinatorialMap.edgeInv a at hb
  have hi : i.val < ℓ := by simpa only [B.leftPath.darts_length] using i.isLt
  have hhead := (B.leftPath.edge_step i).2.2.2
  have hs := contour_forward_head_ne_source B a ha
  have hp := canonicalULSelector_leftPath_edge B (i.val + 1) (by omega) (by omega)
  rw [canonicalULSelector_val] at hp
  have hp' : B.map.toCombinatorialMap.edgeInv
      (leftmostIncoming B (dartHeadVertex B.map a) hs) = a := by
    simpa only [a, hhead, Nat.add_sub_cancel, List.get_eq_getElem] using hp
  have hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs := by
    have h := congrArg B.map.toCombinatorialMap.edgeInv hp'
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h.symm
  have ht : dartHeadVertex B.map a = B.sink := by
    by_contra ht
    have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
      simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
    have hf : B.map.tail (contourNext B a) := by
      rw [he, ← canonicalLRSelector_val B _ ht]
      exact (canonicalLRSelector B _ ht).property.2.1
    rw [hb] at hf
    exact (B.map.tail_iff a (B.noMissingDarts a)).1 ha hf
  have hidx : i.val + 1 = ℓ := by
    have hv : B.leftPath.vertices.get
        ⟨i.val + 1, by rw [B.leftPath.vertices_length]; omega⟩ =
        B.leftPath.vertices.get ⟨ℓ, by rw [B.leftPath.vertices_length]; omega⟩ :=
      hhead.trans (ht.trans B.leftPath.end_vertex.symm)
    exact congrArg Fin.val (B.leftPath.vertices_nodup.get_inj_iff.mp hv)
  change B.leftPath.darts.get i = _
  unfold pathLastDart
  congr 1
  apply Fin.ext
  dsimp
  omega

private theorem increment_filter_gap {α : Type*} (p : α → Bool) (xs : List α)
    (j : ℕ) (hj : j + 1 < (xs.filter p).length) :
    ∃ pre gap post,
      xs = pre ++ (xs.filter p)[j] :: (gap ++ (xs.filter p)[j + 1] :: post) ∧
      ∀ d ∈ gap, ¬ p d := by
  have hdrop : (xs.filter p).drop j =
      (xs.filter p)[j] :: (xs.filter p)[j + 1] :: (xs.filter p).drop (j + 2) := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hj]
  have he : xs.filter p = (xs.filter p).take j ++
      (xs.filter p)[j] :: (xs.filter p)[j + 1] :: (xs.filter p).drop (j + 2) := by
    rw [← hdrop]
    exact (List.take_append_drop j (xs.filter p)).symm
  obtain ⟨pre, rest, hxs, _, hrest⟩ := List.filter_eq_append_iff.mp he
  obtain ⟨pre₀, rest₀, hr, _, _, hrest₀⟩ := List.filter_eq_cons_iff.mp hrest
  obtain ⟨gap, post, hr₀, hgap, _, _⟩ := List.filter_eq_cons_iff.mp hrest₀
  refine ⟨pre ++ pre₀, gap, post, ?_, hgap⟩
  calc
    xs = pre ++ rest := hxs
    _ = pre ++ (pre₀ ++ (xs.filter p)[j] ::
        (gap ++ (xs.filter p)[j + 1] :: post)) := by rw [hr, hr₀]
    _ = _ := by rw [List.append_assoc]

private theorem increment_orbit_gap (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    ∃ n m : ℕ, n < m ∧ m < Fintype.card D ∧
      (contourPerm B ^ n) (contourStart B) = peanoEdge B ⟨j, by omega⟩ ∧
      (contourPerm B ^ m) (contourStart B) = peanoEdge B ⟨j + 1, hj⟩ ∧
      ∀ k, n < k → k < m →
        ¬ B.map.tail ((contourPerm B ^ k) (contourStart B)) := by
  classical
  let xs := List.ofFn fun i : Fin (Fintype.card D) =>
    (contourPerm B ^ i.val) (contourStart B)
  have hj' : j + 1 < (xs.filter (fun d => decide (B.map.tail d))).length := by
    change j + 1 < (firstVisitOrder B).length
    rw [firstVisitOrder_length]
    exact hj
  obtain ⟨pre, gap, post, hxs, hgap⟩ :=
    increment_filter_gap (fun d => decide (B.map.tail d)) xs j hj'
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  change xs = pre ++ a :: (gap ++ b :: post) at hxs
  have hlen := congrArg List.length hxs
  simp only [xs, List.length_ofFn, List.length_append, List.length_cons] at hlen
  have hna : xs[pre.length]'(by dsimp [xs]; rw [List.length_ofFn]; omega) = a :=
    List.getElem_of_append hxs rfl
  have hxs' : xs = (pre ++ a :: gap) ++ b :: post := by
    simpa only [List.append_assoc, List.cons_append] using hxs
  have hmb : xs[pre.length + 1 + gap.length]'(by
      dsimp [xs]; rw [List.length_ofFn]; omega) = b :=
    List.getElem_of_append hxs' (by simp only [List.length_append, List.length_cons]; omega)
  refine ⟨pre.length, pre.length + 1 + gap.length, by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [xs, List.getElem_ofFn] using hna
  · simpa only [xs, List.getElem_ofFn] using hmb
  · intro k hnk hkm
    have hkg : k - pre.length - 1 < gap.length := by omega
    have hget : xs[k]'(by dsimp [xs]; rw [List.length_ofFn]; omega) =
        gap[k - pre.length - 1] := by
      simp only [hxs]
      rw [List.getElem_append_right (by omega), List.getElem_cons]
      simp only [show k - pre.length ≠ 0 by omega]
      exact List.getElem_append_left hkg
    have he : (contourPerm B ^ k) (contourStart B) = gap[k - pre.length - 1] := by
      simpa only [xs, List.getElem_ofFn] using hget
    rw [he]
    have h := hgap _ (List.getElem_mem hkg)
    simpa only [decide_eq_true_eq] using h

private theorem increment_orbit_succ (n : ℕ) :
    (contourPerm B ^ (n + 1)) (contourStart B) =
      contourNext B ((contourPerm B ^ n) (contourStart B)) := by
  change (contourPerm B ^ (n + 1)) (contourStart B) =
    contourPerm B ((contourPerm B ^ n) (contourStart B))
  rw [pow_succ', Equiv.Perm.mul_apply]

private theorem increment_next_reverse_bounce (a : D) (ha : B.map.tail a)
    (hn : ¬ B.map.tail (contourNext B a)) :
    contourNext B a = B.map.toCombinatorialMap.edgeInv a := by
  classical
  have hs := contour_forward_head_ne_source B a ha
  by_cases hsel : B.map.toCombinatorialMap.edgeInv a =
      leftmostIncoming B (dartHeadVertex B.map a) hs
  · by_cases ht : dartHeadVertex B.map a = B.sink
    · simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_left ht]
    · have he : contourNext B a = rightmostOutgoing B (dartHeadVertex B.map a) ht := by
        simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
      apply False.elim
      apply hn
      rw [he, ← canonicalLRSelector_val B _ ht]
      exact (canonicalLRSelector B _ ht).property.2.1
  · simp only [contourNext, dite_eq_left ha, ite_eq_right hsel]

/-- The two canonical heights of consecutive first-visit edges have one of the
three increments specified by the literal inverse definition. -/
theorem peanoEdge_height_increment (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    let a := peanoEdge B ⟨j, by omega⟩
    let b := peanoEdge B ⟨j + 1, hj⟩
    ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
        canonicalULHeight B (dartTailVertex B.map a),
      (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
        canonicalLRHeight B (dartHeadVertex B.map a)) = (1, -1) ∨
    ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
        canonicalULHeight B (dartTailVertex B.map a),
      (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
        canonicalLRHeight B (dartHeadVertex B.map a)) = (-1, 0) ∨
    ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
        canonicalULHeight B (dartTailVertex B.map a),
      (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
        canonicalLRHeight B (dartHeadVertex B.map a)) = (0, 1) := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  dsimp only
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  obtain ⟨n, m, hnm, _hm, hna, hmb, hgap⟩ := increment_orbit_gap B j hj
  change (contourPerm B ^ n) (contourStart B) = a at hna
  change (contourPerm B ^ m) (contourStart B) = b at hmb
  have hlast : a ≠ pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos) := by
    intro he
    have hget : peanoEdge B ⟨j, by omega⟩ =
        peanoEdge B ⟨B.map.toCombinatorialMap.numEdges - 1, by
          have := contour_numEdges_pos B
          omega⟩ := he.trans (peanoEdge_last B).symm
    unfold peanoEdge at hget
    have hidx := congrArg Fin.val ((firstVisitOrder_nodup B).get_inj_iff.mp hget)
    dsimp only at hidx
    omega
  have h1 : (contourPerm B ^ (n + 1)) (contourStart B) = contourNext B a := by
    rw [increment_orbit_succ, hna]
  by_cases hf : B.map.tail (contourNext B a)
  · have hm1 : m = n + 1 := by
      by_contra h
      have hn := hgap (n + 1) (by omega) (by omega)
      rw [h1] at hn
      exact hn hf
    have he : b = contourNext B a := by rw [← hmb, hm1, h1]
    dsimp only [b] at he
    left
    rw [he]
    exact increment_next_forward B a ha hf
  · have hbounce := increment_next_reverse_bounce B a ha hf
    have hi : ¬ B.map.IsOuter a := fun ho =>
      hlast (increment_bounce_outer B a ha hbounce ho)
    obtain ⟨hbf, hside, hclimb⟩ := increment_bounce_inner B a ha hbounce hi
    have hninv := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
    have h2 : (contourPerm B ^ (n + 2)) (contourStart B) =
        B.map.toCombinatorialMap.rot a := by
      rw [show n + 2 = (n + 1) + 1 by omega, increment_orbit_succ, h1, hbounce]
      simp only [contourNext, dite_eq_right hninv,
        B.map.toCombinatorialMap.edgeInv_invol]
    have hm2 : n + 2 ≤ m := by
      by_contra h
      have he : m = n + 1 := by omega
      rw [he, h1] at hmb
      exact hf (hmb.symm ▸ hb)
    by_cases hc : B.map.tail (B.map.toCombinatorialMap.rot a)
    · have hm' : m = n + 2 := by
        by_contra h
        have hn := hgap (n + 2) (by omega) (by omega)
        rw [h2] at hn
        exact hn hc
      have he : b = B.map.toCombinatorialMap.rot a := by rw [← hmb, hm', h2]
      dsimp only [b] at he
      right
      right
      rw [he]
      exact hside hc
    · have h3 : (contourPerm B ^ (n + 3)) (contourStart B) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
        rw [show n + 3 = (n + 2) + 1 by omega, increment_orbit_succ, h2]
        simp only [contourNext, dite_eq_right hc]
        exact increment_triangle_rotation B a hi
      have hm3 : n + 3 ≤ m := by
        by_contra h
        have he : m = n + 2 := by omega
        rw [he, h2] at hmb
        exact hc (hmb.symm ▸ hb)
      have hm' : m = n + 3 := by
        by_contra h
        have hn := hgap (n + 3) (by omega) (by omega)
        rw [h3] at hn
        exact hn hbf
      have he : b = B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.faceSucc a) := by rw [← hmb, hm', h3]
      dsimp only [b] at he
      right
      left
      rw [he]
      exact hclimb hc

end DirectedDistances.PlanarMap
