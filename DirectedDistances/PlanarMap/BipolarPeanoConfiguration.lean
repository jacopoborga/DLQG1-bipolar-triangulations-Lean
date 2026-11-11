module

public import DirectedDistances.PlanarMap.BipolarPeanoIncrement
public import DirectedDistances.PlanarMap.BipolarInnerFaceShape
public import DirectedDistances.PlanarMap.FiniteBipolarBlockConventions

/-! # Local configurations of consecutive Peano edges

Here `peanoEdge` denotes the forward-dart subsequence of the contour cycle. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
variable (B : BipolarTriangulationWithBoundaryBase D ℓ r)

/-- The three local contour moves. -/
inductive PeanoStepKind where
  | descend
  | rotate
  | climb
  deriving DecidableEq, Repr

/-- Explicit dart geometry. In the rotation and climb cases the face of `a` is inner.
Its three boundary darts are `a`, `faceSucc a`, and `edgeInv (rot a)`.
A descent can use boundary edges; it requires neither an inner face nor an
internal vertex. The head is a non-sink because a successor exists. -/
@[expose] def PeanoStepConfig (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) (k : PeanoStepKind) : Prop :=
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  match k with
  | .descend =>
      ∃ (hs : dartHeadVertex B.map a ≠ B.source)
        (ht : dartHeadVertex B.map a ≠ B.sink),
        B.map.toCombinatorialMap.edgeInv a = leftmostIncoming B _ hs ∧
          b = rightmostOutgoing B _ ht
  | .rotate =>
      b = B.map.toCombinatorialMap.rot a ∧
      dartTailVertex B.map b = dartTailVertex B.map a ∧
      contourNext B a = B.map.toCombinatorialMap.edgeInv a ∧
      ¬ B.map.IsOuter a ∧
      B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a) =
        B.map.toCombinatorialMap.edgeInv b ∧
      ∃ S : InnerFaceShape B, S.face = Quotient.mk
        (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) a
  | .climb =>
      ∃ hs : dartTailVertex B.map a ≠ B.source,
        contourNext B a = B.map.toCombinatorialMap.edgeInv a ∧
        ¬ B.map.IsOuter a ∧
        dartHeadVertex B.map b = dartHeadVertex B.map a ∧
        dartTailVertex B.map b = ulParent B (canonicalULSelector B)
          (dartTailVertex B.map a) ∧
        B.map.toCombinatorialMap.rot a = leftmostIncoming B _ hs ∧
        b = B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) ∧
        B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) ∧
        ∃ S : InnerFaceShape B, S.face = Quotient.mk
          (Equiv.Perm.SameCycle.setoid B.map.toCombinatorialMap.faceSucc) a

private theorem configuration_rot_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) = dartTailVertex B.map d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot d).apply_left

private theorem configuration_face_vertex (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) =
      dartHeadVertex B.map d := by
  apply Quotient.sound
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
    (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.edgeInv d))
    (B.map.toCombinatorialMap.edgeInv d)
  exact ⟨1, by simp⟩

private theorem configuration_inverse_forward (d : D) (hd : ¬ B.map.tail d) :
    B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
  by_contra h
  exact hd ((B.map.tail_iff d (B.noMissingDarts d)).2 h)

private theorem configuration_forward_tail_ne_sink (d : D) (hd : B.map.tail d) :
    dartTailVertex B.map d ≠ B.sink := by
  intro h
  exact B.isSink ⟨dartHeadVertex B.map d, d, B.noMissingDarts d, hd, h, rfl⟩

private theorem configuration_next_forward (a : D) (ha : B.map.tail a)
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

private theorem configuration_bounce_face_reverse (a : D) (ha : B.map.tail a)
    (hb : contourNext B a = B.map.toCombinatorialMap.edgeInv a) :
    ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc a) := by
  classical
  intro hf
  have hs := contour_forward_head_ne_source B a ha
  have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
  have ht : dartHeadVertex B.map a ≠ B.sink := by
    rw [← configuration_face_vertex B a]
    exact configuration_forward_tail_ne_sink B _ hf
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

private theorem configuration_triangle_close (a : D) (hi : ¬ B.map.IsOuter a) :
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

private theorem configuration_triangle_rotation (a : D) (hi : ¬ B.map.IsOuter a) :
    B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) =
      B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
  have h := configuration_triangle_close B a hi
  change B.map.toCombinatorialMap.rot.symm
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)) =
    B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) at h
  have h' := congrArg B.map.toCombinatorialMap.rot h
  simpa only [Equiv.apply_symm_apply] using h'.symm

private theorem configuration_bounce_inner (a : D) (ha : B.map.tail a)
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
  have hf := configuration_bounce_face_reverse B a ha hb
  have hbf : B.map.tail b := configuration_inverse_forward B _ hf
  have hclose := configuration_triangle_close B a hi
  have hbt : dartTailVertex B.map b = dartHeadVertex B.map c := by
    have hv := configuration_face_vertex B (B.map.toCombinatorialMap.faceSucc a)
    rw [hclose] at hv
    exact hv.symm
  have hbh : dartHeadVertex B.map b = dartHeadVertex B.map a := by
    simpa only [b, dartHeadVertex, dartTailVertex,
      B.map.toCombinatorialMap.edgeInv_invol] using
      configuration_face_vertex B a
  refine ⟨hbf, ?_, ?_⟩
  · intro hc
    have hs := contour_forward_head_ne_source B c hc
    have ht : dartHeadVertex B.map c ≠ B.sink := by
      rw [← hbt]
      exact configuration_forward_tail_ne_sink B b hbf
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
      rw [configuration_rot_vertex B a]
      omega
    · dsimp
      omega
  · intro hc
    have hs : dartTailVertex B.map a ≠ B.source := by
      intro he
      exact hc (tail_of_dartTailVertex_eq_source B c
        ((configuration_rot_vertex B a).trans he))
    have ht := configuration_forward_tail_ne_sink B a ha
    have hprev : B.map.tail (B.map.toCombinatorialMap.rot.symm c) := by
      simpa only [c, Equiv.symm_apply_apply] using ha
    have hsel : c = leftmostIncoming B (dartTailVertex B.map a) hs :=
      (leftmostIncoming_internal_characterization B _ hs ht).2.2.2
        c (configuration_rot_vertex B a) hc hprev
    have hul := canonicalULHeight_leftmostIncoming B _ hs
    rw [← hsel, ← hbt] at hul
    dsimp only [b] at hul
    apply Prod.ext
    · dsimp
      omega
    · dsimp
      rw [hbh]
      omega

private theorem configuration_bounce_outer (a : D) (ha : B.map.tail a)
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

private theorem configuration_filter_gap {α : Type*} (p : α → Bool) (xs : List α)
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

private theorem configuration_orbit_gap (j : ℕ)
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
    configuration_filter_gap (fun d => decide (B.map.tail d)) xs j hj'
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

private theorem configuration_orbit_succ (n : ℕ) :
    (contourPerm B ^ (n + 1)) (contourStart B) =
      contourNext B ((contourPerm B ^ n) (contourStart B)) := by
  change (contourPerm B ^ (n + 1)) (contourStart B) =
    contourPerm B ((contourPerm B ^ n) (contourStart B))
  rw [pow_succ', Equiv.Perm.mul_apply]

private theorem configuration_next_reverse_bounce (a : D) (ha : B.map.tail a)
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


/-- Every consecutive pair has one of the three explicit local configurations. -/
theorem peanoEdge_step_kind (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    ∃ k : PeanoStepKind, PeanoStepConfig B j hj k := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  obtain ⟨n, m, hnm, _hm, hna, hmb, hgap⟩ := configuration_orbit_gap B j hj
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
    rw [configuration_orbit_succ, hna]
  by_cases hf : B.map.tail (contourNext B a)
  · have hm1 : m = n + 1 := by
      by_contra h
      have hn := hgap (n + 1) (by omega) (by omega)
      rw [h1] at hn
      exact hn hf
    have he : b = contourNext B a := by rw [← hmb, hm1, h1]
    have hs := contour_forward_head_ne_source B a ha
    have hn := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
    have hsel : B.map.toCombinatorialMap.edgeInv a =
        leftmostIncoming B (dartHeadVertex B.map a) hs := by
      by_contra hsel
      simp only [contourNext, dite_eq_left ha, ite_eq_right hsel] at hf
      exact hn hf
    have ht : dartHeadVertex B.map a ≠ B.sink := by
      intro ht
      simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_left ht] at hf
      exact hn hf
    refine ⟨.descend, hs, ht, hsel, ?_⟩
    change b = rightmostOutgoing B _ ht
    rw [he]
    simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
  · have hbounce := configuration_next_reverse_bounce B a ha hf
    have hi : ¬ B.map.IsOuter a := fun ho =>
      hlast (configuration_bounce_outer B a ha hbounce ho)
    have hbf := (configuration_bounce_inner B a ha hbounce hi).1
    have hninv := (B.map.tail_iff a (B.noMissingDarts a)).1 ha
    have h2 : (contourPerm B ^ (n + 2)) (contourStart B) =
        B.map.toCombinatorialMap.rot a := by
      rw [show n + 2 = (n + 1) + 1 by omega, configuration_orbit_succ, h1, hbounce]
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
      refine ⟨.rotate, he, ?_, hbounce, hi, ?_, innerFaceShape_exists B a hi⟩
      · change dartTailVertex B.map b = dartTailVertex B.map a
        rw [he]
        exact configuration_rot_vertex B a
      · change B.map.toCombinatorialMap.faceSucc
            (B.map.toCombinatorialMap.faceSucc a) = B.map.toCombinatorialMap.edgeInv b
        rw [he]
        exact configuration_triangle_close B a hi
    · have h3 : (contourPerm B ^ (n + 3)) (contourStart B) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
        rw [show n + 3 = (n + 2) + 1 by omega, configuration_orbit_succ, h2]
        simp only [contourNext, dite_eq_right hc]
        exact configuration_triangle_rotation B a hi
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
      have hs : dartTailVertex B.map a ≠ B.source := by
        intro hv
        exact hc (tail_of_dartTailVertex_eq_source B _
          ((configuration_rot_vertex B a).trans hv))
      have ht := configuration_forward_tail_ne_sink B a ha
      have hprev : B.map.tail
          (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.rot a)) := by
        simpa only [Equiv.symm_apply_apply] using ha
      have hsel : B.map.toCombinatorialMap.rot a =
          leftmostIncoming B (dartTailVertex B.map a) hs :=
        (leftmostIncoming_internal_characterization B _ hs ht).2.2.2
          _ (configuration_rot_vertex B a) hc hprev
      have hbt : dartTailVertex B.map b =
          dartHeadVertex B.map (B.map.toCombinatorialMap.rot a) := by
        have hv := configuration_face_vertex B (B.map.toCombinatorialMap.faceSucc a)
        rw [configuration_triangle_close B a hi] at hv
        rw [he]
        exact hv.symm
      have hbh : dartHeadVertex B.map b = dartHeadVertex B.map a := by
        rw [he]
        simpa only [dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using configuration_face_vertex B a
      have hparent : ulParent B (canonicalULSelector B) (dartTailVertex B.map a) =
          dartHeadVertex B.map (B.map.toCombinatorialMap.rot a) := by
        simp only [ulParent, dite_eq_right hs, canonicalULSelector_val, ← hsel]
        rfl
      exact ⟨.climb, hs, hbounce, hi, hbh, hbt.trans hparent.symm,
        hsel, he, configuration_triangle_close B a hi, innerFaceShape_exists B a hi⟩


/-- The unshifted height differences; the constant shift in the inverse walk's
second coordinate cancels in these differences. -/
@[expose] noncomputable def peanoStepHeightDifference (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) : ℤ × ℤ :=
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
      canonicalULHeight B (dartTailVertex B.map a),
    (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
      canonicalLRHeight B (dartHeadVertex B.map a))

/-- The increment attached to each geometric kind. -/
@[expose] def PeanoStepKind.increment : PeanoStepKind → ℤ × ℤ
  | .descend => (1, -1)
  | .rotate => (0, 1)
  | .climb => (-1, 0)

/-- Each local configuration has its prescribed height increment. -/
theorem peanoStepConfig_height_increment (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) (k : PeanoStepKind)
    (h : PeanoStepConfig B j hj k) :
    peanoStepHeightDifference B j hj = k.increment := by
  classical
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj⟩
  have ha : B.map.tail a := peanoEdge_forward B _
  have hb : B.map.tail b := peanoEdge_forward B _
  cases k with
  | descend =>
      obtain ⟨hs, ht, hsel, he⟩ := h
      change dartHeadVertex B.map a ≠ B.source at hs
      change dartHeadVertex B.map a ≠ B.sink at ht
      change B.map.toCombinatorialMap.edgeInv a =
        leftmostIncoming B (dartHeadVertex B.map a) hs at hsel
      change b = rightmostOutgoing B (dartHeadVertex B.map a) ht at he
      have hn : contourNext B a = b := by
        rw [he]
        simp only [contourNext, dite_eq_left ha, ite_eq_left hsel, dite_eq_right ht]
      have hf : B.map.tail (contourNext B a) := hn.symm ▸ hb
      have hh := configuration_next_forward B a ha hf
      rw [hn] at hh
      exact hh
  | rotate =>
      obtain ⟨he, _, hbounce, hi, _, _⟩ := h
      change b = B.map.toCombinatorialMap.rot a at he
      have hc : B.map.tail (B.map.toCombinatorialMap.rot a) := he ▸ hb
      have hh := (configuration_bounce_inner B a ha hbounce hi).2.1 hc
      change peanoStepHeightDifference B j hj = (0, 1)
      unfold peanoStepHeightDifference
      change ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
          canonicalULHeight B (dartTailVertex B.map a),
        (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
          canonicalLRHeight B (dartHeadVertex B.map a)) = (0, 1)
      rw [he]
      exact hh
  | climb =>
      obtain ⟨hs, hbounce, hi, _, _, hsel, he, _, _⟩ := h
      change b = B.map.toCombinatorialMap.edgeInv
        (B.map.toCombinatorialMap.faceSucc a) at he
      have hc : ¬ B.map.tail (B.map.toCombinatorialMap.rot a) := by
        rw [hsel]
        have hp := (canonicalULSelector B _ hs).property.2.1
        rw [canonicalULSelector_val] at hp
        have hn := (B.map.tail_iff _ (B.noMissingDarts _)).1 hp
        simpa only [B.map.toCombinatorialMap.edgeInv_invol] using hn
      have hh := (configuration_bounce_inner B a ha hbounce hi).2.2 hc
      change peanoStepHeightDifference B j hj = (-1, 0)
      unfold peanoStepHeightDifference
      change ((canonicalULHeight B (dartTailVertex B.map b) : ℤ) -
          canonicalULHeight B (dartTailVertex B.map a),
        (canonicalLRHeight B (dartHeadVertex B.map b) : ℤ) -
          canonicalLRHeight B (dartHeadVertex B.map a)) = (-1, 0)
      rw [he]
      exact hh

/-- The three geometric kinds have distinct increments. -/
theorem PeanoStepKind.increment_injective :
    Function.Injective PeanoStepKind.increment := by
  intro k k' h
  cases k <;> cases k' <;> simp_all [PeanoStepKind.increment]

/-- The local configuration kind is unique. -/
theorem peanoEdge_step_kind_unique (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges)
    {k k' : PeanoStepKind} (h : PeanoStepConfig B j hj k)
    (h' : PeanoStepConfig B j hj k') : k = k' := by
  apply PeanoStepKind.increment_injective
  exact (peanoStepConfig_height_increment B j hj k h).symm.trans
    (peanoStepConfig_height_increment B j hj k' h')

/-- Existence and mutual exclusivity of the three local geometries. -/
theorem peanoEdge_step_kind_existsUnique (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    ∃! k : PeanoStepKind, PeanoStepConfig B j hj k := by
  obtain ⟨k, hk⟩ := peanoEdge_step_kind B j hj
  exact ⟨k, hk, fun k' hk' => peanoEdge_step_kind_unique B j hj hk' hk⟩

/-- Height differences characterize the geometric kind, in both directions. -/
theorem peanoStepConfig_iff_height_increment (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) (k : PeanoStepKind) :
    PeanoStepConfig B j hj k ↔ peanoStepHeightDifference B j hj = k.increment := by
  constructor
  · exact peanoStepConfig_height_increment B j hj k
  · intro h
    obtain ⟨k', hk'⟩ := peanoEdge_step_kind B j hj
    have he : k' = k := PeanoStepKind.increment_injective
      ((peanoStepConfig_height_increment B j hj k' hk').symm.trans h)
    exact he ▸ hk'

/-- The descend kind corresponds to code 2's increment, rotate to code 1's, and
climb to code 0's. This statement uses height differences directly. -/
theorem peanoStepConfig_height_characterization (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    (PeanoStepConfig B j hj .descend ↔ peanoStepHeightDifference B j hj = (1, -1)) ∧
    (PeanoStepConfig B j hj .rotate ↔ peanoStepHeightDifference B j hj = (0, 1)) ∧
    (PeanoStepConfig B j hj .climb ↔ peanoStepHeightDifference B j hj = (-1, 0)) :=
  ⟨peanoStepConfig_iff_height_increment B j hj .descend,
    peanoStepConfig_iff_height_increment B j hj .rotate,
    peanoStepConfig_iff_height_increment B j hj .climb⟩

/-- Exact outer-boundary variant: a forward dart on the outer face, when it has
a further Peano edge, belongs to the left boundary and descends. Rotation
and climb therefore never use the outer face as their triangular witness. -/
theorem peanoEdge_outer_step_descend (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges)
    (ho : B.map.IsOuter (peanoEdge B ⟨j, by omega⟩)) :
    peanoEdge B ⟨j, by omega⟩ ∈ B.leftPath.darts ∧
      PeanoStepConfig B j hj .descend := by
  have hmem : peanoEdge B ⟨j, by omega⟩ ∈ B.leftPath.darts :=
    (B.outerSplit.2.2.1 _).mpr
      ⟨B.noMissingDarts _, peanoEdge_forward B _, ho⟩
  refine ⟨hmem, ?_⟩
  obtain ⟨k, hk⟩ := peanoEdge_step_kind B j hj
  cases k with
  | descend => exact hk
  | rotate => exact (hk.2.2.2.1 ho).elim
  | climb => exact ((Exists.choose_spec hk).2.1 ho).elim

/-- The unique kind, chosen only after its geometric existence and uniqueness
have been established. -/
@[expose] noncomputable def peanoStepKind (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) : PeanoStepKind :=
  Classical.choose (peanoEdge_step_kind B j hj)

/-- The selected kind has the full local dart configuration. -/
theorem peanoStepKind_config (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    PeanoStepConfig B j hj (peanoStepKind B j hj) :=
  Classical.choose_spec (peanoEdge_step_kind B j hj)

/-- Equality with the selected kind is equivalent to the prescribed inverse
height increment. -/
theorem peanoStepKind_eq_iff_height_increment (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) (k : PeanoStepKind) :
    peanoStepKind B j hj = k ↔ peanoStepHeightDifference B j hj = k.increment := by
  have h := peanoStepConfig_height_increment B j hj _ (peanoStepKind_config B j hj)
  constructor
  · intro he
    exact h.trans (congrArg PeanoStepKind.increment he)
  · intro he
    exact PeanoStepKind.increment_injective (h.symm.trans he)

/-- The literal kind equalities corresponding to code letters 2, 1, and 0,
respectively, stated without a dependency on a code-extraction module. -/
theorem peanoStepKind_height_characterization (j : ℕ)
    (hj : j + 1 < B.map.toCombinatorialMap.numEdges) :
    (peanoStepKind B j hj = .descend ↔ peanoStepHeightDifference B j hj = (1, -1)) ∧
    (peanoStepKind B j hj = .rotate ↔ peanoStepHeightDifference B j hj = (0, 1)) ∧
    (peanoStepKind B j hj = .climb ↔ peanoStepHeightDifference B j hj = (-1, 0)) :=
  ⟨peanoStepKind_eq_iff_height_increment B j hj .descend,
    peanoStepKind_eq_iff_height_increment B j hj .rotate,
    peanoStepKind_eq_iff_height_increment B j hj .climb⟩

end DirectedDistances.PlanarMap
