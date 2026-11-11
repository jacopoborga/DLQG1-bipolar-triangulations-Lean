/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteXDPLeftmostSelector

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem faceSucc_tailVertex_eq_headVertex
    (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.toCombinatorialMap.faceSucc d) = dartHeadVertex M d := by
  apply Quotient.sound
  change Equiv.Perm.SameCycle M.toCombinatorialMap.rot
    (M.toCombinatorialMap.rot.symm (M.toCombinatorialMap.edgeInv d))
    (M.toCombinatorialMap.edgeInv d)
  exact ⟨1, by simp⟩

private theorem faceForwardStep
    (M : DirectedMapWithMissing D) (d : D)
    (hmiss : ¬ M.missing d) (htail : M.tail d) :
    M.directedStep (dartTailVertex M d)
      (dartTailVertex M (M.toCombinatorialMap.faceSucc d)) := by
  refine ⟨d, hmiss, htail, rfl, ?_⟩
  exact (faceSucc_tailVertex_eq_headVertex M d).symm

private theorem faceBackwardStep
    (M : DirectedMapWithMissing D) (d : D)
    (hmiss : ¬ M.missing d) (hnontail : ¬ M.tail d) :
    M.directedStep (dartTailVertex M (M.toCombinatorialMap.faceSucc d))
      (dartTailVertex M d) := by
  have hinvTail : M.tail (M.edgeInv d) := by
    by_contra h
    exact hnontail ((M.tail_iff d hmiss).2 h)
  have h : M.directedStep (dartHeadVertex M d) (dartTailVertex M d) := by
    refine ⟨M.edgeInv d, ?_, hinvTail, ?_, ?_⟩
    · intro h
      exact hmiss ((M.missing_edgeInv d).mpr h)
    · rfl
    · simp [dartTailVertex, M.edgeInv_invol]
  rw [← faceSucc_tailVertex_eq_headVertex M d] at h
  exact h

/-- The corner indexed by `d` lies at `head(d)`, between `edgeInv d` and
`faceSucc d`. It is a face-switch when both incident edges point in the same
direction relative to that vertex (`lem-lr-ind`, -/
@[expose] def faceSwitchCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) : Prop :=
  B.map.tail (B.map.toCombinatorialMap.faceSucc d) ↔ ¬ B.map.tail d

/-- The corner indexed by `d` is a vertex-switch when one incident edge
points in and the other points out (`lem-lr-ind`, -/
@[expose] def vertexSwitchCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) : Prop :=
  B.map.tail (B.map.toCombinatorialMap.faceSucc d) ↔ B.map.tail d

/-- Every corner is exactly one of a face-switch and a vertex-switch -/
theorem corner_switch_partition
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    faceSwitchCorner B d ↔ ¬ vertexSwitchCorner B d := by
  classical
  unfold faceSwitchCorner vertexSwitchCorner
  by_cases hp : B.map.tail d <;>
    by_cases hq : B.map.tail (B.map.toCombinatorialMap.faceSucc d) <;>
    simp [hp, hq]

/-- Each triangular inner-face boundary has at least one dart in each
orientation when read around the face. In particular, neither orientation
of its three darts forms a directed cycle. This local consequence of
acyclicity is a helper for the incoming-interval interface used by
interval property. -/
theorem innerFace_has_both_boundary_orientations
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    (B.map.tail d ∨
      B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∨
      B.map.tail (B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.faceSucc d))) ∧
    (¬ B.map.tail d ∨
      ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc d) ∨
      ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.faceSucc d))) := by
  let f := B.map.toCombinatorialMap.faceSucc
  let d₁ := f d
  let d₂ := f d₁
  have htri : f d₂ = d := (B.innerFacesDegreeThree d hinner).1
  have hmiss₀ := B.noMissingDarts d
  have hmiss₁ := B.noMissingDarts d₁
  have hmiss₂ := B.noMissingDarts d₂
  constructor
  · by_contra hnot
    push Not at hnot
    have h20 := faceBackwardStep B.map d₂ hmiss₂ hnot.2.2
    have h20' : B.map.directedStep (dartTailVertex B.map d)
        (dartTailVertex B.map d₂) := by
      change B.map.directedStep (dartTailVertex B.map (f d₂))
        (dartTailVertex B.map d₂) at h20
      rw [htri] at h20
      exact h20
    have h12 := faceBackwardStep B.map d₁ hmiss₁ hnot.2.1
    have h12' : B.map.directedStep (dartTailVertex B.map d₂)
        (dartTailVertex B.map d₁) := by
      change B.map.directedStep (dartTailVertex B.map (f d₁))
        (dartTailVertex B.map d₁) at h12
      exact h12
    have h01 := faceBackwardStep B.map d hmiss₀ hnot.1
    have h01' : B.map.directedStep (dartTailVertex B.map d₁)
        (dartTailVertex B.map d) := by
      change B.map.directedStep (dartTailVertex B.map (f d))
        (dartTailVertex B.map d) at h01
      exact h01
    have hcycle : Relation.TransGen B.map.directedStep
        (dartTailVertex B.map d) (dartTailVertex B.map d) :=
      Relation.TransGen.head' h20'
        ((Relation.ReflTransGen.single h12').trans
          (Relation.ReflTransGen.single h01'))
    exact B.acyclic (dartTailVertex B.map d) hcycle
  · by_contra hnot
    push Not at hnot
    have h01 := faceForwardStep B.map d hmiss₀ hnot.1
    have h01' : B.map.directedStep (dartTailVertex B.map d)
        (dartTailVertex B.map d₁) := by
      change B.map.directedStep (dartTailVertex B.map d)
        (dartTailVertex B.map (f d)) at h01
      exact h01
    have h12 := faceForwardStep B.map d₁ hmiss₁ hnot.2.1
    have h12' : B.map.directedStep (dartTailVertex B.map d₁)
        (dartTailVertex B.map d₂) := by
      change B.map.directedStep (dartTailVertex B.map d₁)
        (dartTailVertex B.map (f d₁)) at h12
      exact h12
    have h20 := faceForwardStep B.map d₂ hmiss₂ hnot.2.2
    have h20' : B.map.directedStep (dartTailVertex B.map d₂)
        (dartTailVertex B.map d) := by
      change B.map.directedStep (dartTailVertex B.map d₂)
        (dartTailVertex B.map (f d₂)) at h20
      rw [htri] at h20
      exact h20
    have hcycle : Relation.TransGen B.map.directedStep
        (dartTailVertex B.map d) (dartTailVertex B.map d) :=
      Relation.TransGen.head' h01'
        ((Relation.ReflTransGen.single h12').trans
          (Relation.ReflTransGen.single h20'))
    exact B.acyclic (dartTailVertex B.map d) hcycle

/-- Each triangular inner face has exactly one vertex-switch corner. The
other two corners are face-switches (`lem-lr-ind`, -/
theorem innerFace_exactly_one_vertexSwitch
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hinner : ¬ B.map.IsOuter d) :
    (vertexSwitchCorner B d ∧
      ¬ vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
    (¬ vertexSwitchCorner B d ∧
      vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      ¬ vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) ∨
    (¬ vertexSwitchCorner B d ∧
      ¬ vertexSwitchCorner B (B.map.toCombinatorialMap.faceSucc d) ∧
      vertexSwitchCorner B
        (B.map.toCombinatorialMap.faceSucc
          (B.map.toCombinatorialMap.faceSucc d))) := by
  classical
  let f := B.map.toCombinatorialMap.faceSucc
  let d₁ := f d
  let d₂ := f d₁
  have htri : f d₂ = d := (B.innerFacesDegreeThree d hinner).1
  have hbits := innerFace_has_both_boundary_orientations B d hinner
  by_cases h₀ : B.map.tail d
  · by_cases h₁ : B.map.tail d₁
    · by_cases h₂ : B.map.tail d₂
      · rcases hbits.2 with hn₀ | hn₁ | hn₂
        · exact (hn₀ h₀).elim
        · exact (hn₁ h₁).elim
        · exact (hn₂ h₂).elim
      · left
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
    · by_cases h₂ : B.map.tail d₂
      · right
        right
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
      · right
        left
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
  · by_cases h₁ : B.map.tail d₁
    · by_cases h₂ : B.map.tail d₂
      · right
        left
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
      · right
        right
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
    · by_cases h₂ : B.map.tail d₂
      · left
        simp [vertexSwitchCorner, f, d₁, d₂, htri, h₀, h₁, h₂]
      · rcases hbits.1 with h₀' | h₁' | h₂'
        · exact (h₀ h₀').elim
        · exact (h₁ h₁').elim
        · exact (h₂ h₂').elim

/-- Every corner at the source is a face-switch because every incident edge
points out of the source (`lem-lr-ind`, -/
theorem source_corner_faceSwitch
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hhead : dartHeadVertex B.map d = B.source) :
    faceSwitchCorner B d := by
  have hnotTail : ¬ B.map.tail d := by
    intro htail
    apply B.isSource
    exact ⟨dartTailVertex B.map d, d, B.noMissingDarts d, htail, rfl, hhead⟩
  have hnext : B.map.tail (B.map.toCombinatorialMap.faceSucc d) := by
    have hvertex := faceSucc_tailVertex_eq_headVertex B.map d
    exact tail_of_dartTailVertex_eq_source B
      (B.map.toCombinatorialMap.faceSucc d) (hvertex.trans hhead)
  exact ⟨fun _ => hnotTail, fun _ => hnext⟩

/-- Every corner at the sink is a face-switch because every incident edge
points in to the sink (`lem-lr-ind`, -/
theorem sink_corner_faceSwitch
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D)
    (hhead : dartHeadVertex B.map d = B.sink) :
    faceSwitchCorner B d := by
  have hnext : ¬ B.map.tail (B.map.toCombinatorialMap.faceSucc d) := by
    intro htail
    apply B.isSink
    refine ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.faceSucc d),
      B.map.toCombinatorialMap.faceSucc d, B.noMissingDarts _, htail, ?_, rfl⟩
    exact (faceSucc_tailVertex_eq_headVertex B.map d).trans hhead
  have hinvNotTail : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
    intro htail
    apply B.isSink
    refine ⟨dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d),
      B.map.toCombinatorialMap.edgeInv d, B.noMissingDarts _, htail, ?_, rfl⟩
    exact hhead
  have htail : B.map.tail d :=
    (B.map.tail_iff d (B.noMissingDarts d)).2 hinvNotTail
  refine ⟨?_, ?_⟩
  · intro h
    exact False.elim (hnext h)
  · intro h
    exact False.elim (h htail)

/-- A vertex other than the sink has an outgoing dart; a vertex other than
the source has an incoming dart (`lem-lr-ind`, -/
theorem nonterminal_vertex_has_incoming_and_outgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hsource : v ≠ B.source) (hsink : v ≠ B.sink) :
    (∃ din, B.map.tail din ∧ dartHeadVertex B.map din = v) ∧
    (∃ dout, B.map.tail dout ∧ dartTailVertex B.map dout = v) := by
  obtain ⟨din, _, hdin, hhead⟩ := exists_incomingDartAt B v hsource
  have houtStep : ∃ w, B.map.directedStep v w := by
    by_contra h
    exact hsink (B.sink_unique v h)
  obtain ⟨w, dout, _, hdout, htail, _⟩ := houtStep
  exact ⟨⟨din, hdin, hhead⟩, ⟨dout, hdout, htail⟩⟩

private theorem perm_transition_count_even (p : Equiv.Perm D) (b : D → Bool) :
    Even (Finset.univ.filter (fun d => b d ≠ b (p d))).card := by
  classical
  let now := Finset.univ.filter (fun d => b d = true)
  let after := Finset.univ.filter (fun d => b (p d) = true)
  let both := Finset.univ.filter (fun d => b d = true ∧ b (p d) = true)
  let down := Finset.univ.filter (fun d => b d = true ∧ b (p d) = false)
  let up := Finset.univ.filter (fun d => b d = false ∧ b (p d) = true)
  have hnow : now.card = after.card := by
    dsimp [now, after]
    apply Finset.card_bijective p.symm p.symm.bijective
    intro d
    simp
  have hnow_split : now.card = both.card + down.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := now) (p := fun d => b (p d) = true)
    simpa [now, both, down, Finset.filter_filter, and_assoc] using h.symm
  have hafter_split : after.card = both.card + up.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := after) (p := fun d => b d = true)
    simpa [after, both, up, Finset.filter_filter, and_comm, and_left_comm,
      and_assoc] using h.symm
  have hdown_up : down.card = up.card := by
    omega
  have htransition :
      (Finset.univ.filter (fun d => b d ≠ b (p d))).card = down.card + up.card := by
    have hset : Finset.univ.filter (fun d => b d ≠ b (p d)) = down ∪ up := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases h₀ : b d <;> cases h₁ : b (p d) <;>
        simp [down, up, h₀, h₁]
    have hdisjoint : Disjoint down up := by
      apply Finset.disjoint_left.mpr
      intro d hd hu
      simp only [down, up, Finset.mem_filter, Finset.mem_univ, true_and] at hd hu
      rw [hd.1] at hu
      cases hu.1
    rw [hset, Finset.card_union_of_disjoint hdisjoint]
  refine ⟨down.card, ?_⟩
  rw [htransition, hdown_up]

private theorem perm_transition_count_ge_two
    (p : Equiv.Perm D) (b : D → Bool) (x y : D)
    (hcycle : p.SameCycle x y) (hxy : b x ≠ b y) :
    2 ≤ (Finset.univ.filter (fun d => b d ≠ b (p d))).card := by
  classical
  have hsome : ∃ k, b ((p ^ k) x) ≠ b ((p ^ (k + 1)) x) := by
    by_contra hnone
    have hstep : ∀ k, b ((p ^ k) x) = b ((p ^ (k + 1)) x) := by
      intro k
      by_contra hne
      exact hnone ⟨k, hne⟩
    have hconst : ∀ k, b ((p ^ k) x) = b x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc
            b ((p ^ (k + 1)) x) = b ((p ^ k) x) := by
              simpa only [pow_succ', Equiv.Perm.mul_apply] using (hstep k).symm
            _ = b x := ih
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    apply hxy
    rw [← hn]
    exact (hconst n).symm
  obtain ⟨k, hk⟩ := hsome
  let z := (p ^ k) x
  have hz : b z ≠ b (p z) := by
    simpa [z, pow_succ'] using hk
  have hpos : 0 < (Finset.univ.filter (fun d => b d ≠ b (p d))).card :=
    Finset.card_pos.mpr ⟨z, by simp [hz]⟩
  have heven := perm_transition_count_even p b
  rcases heven with ⟨m, hm⟩
  omega

private theorem vertexSwitch_iff_rotationTransition
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    vertexSwitchCorner B d ↔
      B.map.tail (B.map.toCombinatorialMap.faceSucc d) ≠
        B.map.tail (B.map.toCombinatorialMap.rot
          (B.map.toCombinatorialMap.faceSucc d)) := by
  have hrot : B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.faceSucc d) = B.map.toCombinatorialMap.edgeInv d := by
    simp [CombinatorialMap.faceSucc]
  have htail : B.map.tail d ↔
      ¬ B.map.tail (B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.faceSucc d)) := by
    rw [hrot]
    exact B.map.tail_iff d (B.noMissingDarts d)
  unfold vertexSwitchCorner
  rw [htail]
  by_cases h₀ : B.map.tail (B.map.toCombinatorialMap.faceSucc d) <;>
    by_cases h₁ : B.map.tail
      (B.map.toCombinatorialMap.rot (B.map.toCombinatorialMap.faceSucc d)) <;>
    simp [h₀, h₁]

private theorem rot_tailVertex_eq (M : DirectedMapWithMissing D) (d : D) :
    dartTailVertex M (M.toCombinatorialMap.rot d) = dartTailVertex M d := by
  apply Quotient.sound
  change M.toCombinatorialMap.rot.SameCycle
    (M.toCombinatorialMap.rot d) d
  exact Equiv.Perm.SameCycle.rfl.apply_left

/-- At a vertex, the number of incident corners where the orientation changes
is even, and is at least two when the vertex has both an incoming and an
outgoing dart. Corners are indexed by darts whose head is the vertex; applying
`faceSucc` identifies them with darts whose tail is the vertex, and the switch
condition becomes a change along the rotation orbit. This is a helper for -/
theorem vertexSwitch_even_and_pos
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map)
    (hin : ∃ d, B.map.tail d ∧ dartHeadVertex B.map d = v)
    (hout : ∃ d, B.map.tail d ∧ dartTailVertex B.map d = v) :
    Even (Nat.card {d : D //
      dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d}) ∧
      2 ≤ Nat.card {d : D //
        dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} := by
  classical
  let rot := B.map.toCombinatorialMap.rot
  let b : D → Bool := fun d =>
    if dartTailVertex B.map d = v then decide (B.map.tail d) else false
  let corners := Finset.univ.filter (fun d =>
    dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d)
  let localTransitions := Finset.univ.filter (fun d =>
    dartTailVertex B.map d = v ∧ B.map.tail d ≠ B.map.tail (rot d))
  let transitions := Finset.univ.filter (fun d => b d ≠ b (rot d))
  rcases hin with ⟨din, hdin, hhead⟩
  rcases hout with ⟨dout, hdout, htail⟩
  let dinOpp := B.map.edgeInv din
  have hdinOppVertex : dartTailVertex B.map dinOpp = v := by
    simpa [dinOpp, dartTailVertex, dartHeadVertex] using hhead
  have hdinOppNotTail : ¬ B.map.tail dinOpp := by
    exact (B.map.tail_iff din (B.noMissingDarts din)).mp hdin
  have hbout : b dout = true := by
    simp [b, htail, hdout]
  have hbin : b dinOpp = false := by
    simp [b, hdinOppVertex, hdinOppNotTail]
  have hcycle : rot.SameCycle dout dinOpp := by
    exact Quotient.exact (htail.trans hdinOppVertex.symm)
  have hbdiff : b dout ≠ b dinOpp := by
    rw [hbout, hbin]
    decide
  have htransitions_local : transitions = localTransitions := by
    ext d
    simp only [transitions, localTransitions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    dsimp [b]
    have hrotVertex := rot_tailVertex_eq B.map d
    by_cases hv : dartTailVertex B.map d = v
    · have hv' : dartTailVertex B.map (rot d) = v := by
        rw [hrotVertex]
        exact hv
      by_cases h₀ : B.map.tail d <;>
        by_cases h₁ : B.map.tail (rot d) <;>
        simp [hv, hv', h₀, h₁]
    · have hv' : dartTailVertex B.map (rot d) ≠ v := by
        rw [hrotVertex]
        exact hv
      simp [hv, hv']
  have hcorners_local : corners.card = localTransitions.card := by
    apply Finset.card_bijective (s := corners) (t := localTransitions)
      (fun d => B.map.toCombinatorialMap.faceSucc d)
      (B.map.toCombinatorialMap.faceSucc).bijective
    intro d
    simp only [corners, localTransitions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hhead, hswitch⟩
      exact ⟨by rw [faceSucc_tailVertex_eq_headVertex]; exact hhead,
        (vertexSwitch_iff_rotationTransition B d).mp hswitch⟩
    · rintro ⟨htail, htransition⟩
      exact ⟨by rw [← faceSucc_tailVertex_eq_headVertex]; exact htail,
        (vertexSwitch_iff_rotationTransition B d).mpr htransition⟩
  have hevenLocal : Even localTransitions.card := by
    rw [← htransitions_local]
    exact perm_transition_count_even rot b
  have hgeLocal : 2 ≤ localTransitions.card := by
    rw [← htransitions_local]
    exact perm_transition_count_ge_two rot b dout dinOpp hcycle hbdiff
  have hcornerCard : Nat.card {d : D //
      dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} = corners.card := by
    rw [Nat.card_eq_fintype_card]
    simpa [corners] using
      (Fintype.card_subtype
        (fun d : D => dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d))
  rw [hcornerCard, hcorners_local]
  exact ⟨hevenLocal, hgeLocal⟩

/-- The exact outer cyclic word has one dart for each edge on the two boundary -/
theorem outerWord_length_eq_boundaryLengths
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.outerWord.letters.length = ℓ + r := by
  have hlen := B.outerSplit.2.1.perm.length_eq
  simpa [B.leftPath.darts_length, B.rightPath.darts_length] using hlen

/-- The marked external face has one dart for each letter of its exact outer
word, hence `ℓ + r` darts (`lem-lr-ind`, -/
theorem outerFace_dartCount_eq_boundaryLengths
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // B.map.IsOuter d} = ℓ + r := by
  classical
  let houter := B.outerSplit.1
  let e : {d : D // B.map.IsOuter d} ≃
      {d : D // d ∈ B.outerWord.letters} := {
    toFun := fun d =>
      ⟨d.1, (mem_iff_isOuter B.map B.outerWord houter d.1).mpr d.2⟩
    invFun := fun d =>
      ⟨d.1, (mem_iff_isOuter B.map B.outerWord houter d.1).mp d.2⟩
    left_inv := by intro d; cases d; rfl
    right_inv := by intro d; cases d; rfl
  }
  have hlist : Nat.card {d : D // d ∈ B.outerWord.letters} =
      B.outerWord.letters.toFinset.card :=
    Nat.subtype_card _ (by intro d; simp)
  calc
    Nat.card {d : D // B.map.IsOuter d} =
        Nat.card {d : D // d ∈ B.outerWord.letters} := Nat.card_congr e
    _ = B.outerWord.letters.toFinset.card := hlist
    _ = B.outerWord.letters.length :=
      List.toFinset_card_of_nodup B.outerWord.nodup
    _ = ℓ + r := outerWord_length_eq_boundaryLengths B

end DirectedDistances.PlanarMap
