/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarEuler
public import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval
public import DirectedDistances.PlanarMap.FiniteXDPLeftmostSelector

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- Darts based at `v`, with parallel edges and the two darts of each edge
kept distinct. Helper toward `lem-lr-ind` and the inverse KMSW trees; not the -/
@[expose] def vertexRotationCycle
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :=
  {d : D // dartTailVertex B.map d = v}

/-- At every vertex dart, the dart is either oriented out of the vertex or is
the reverse dart of an oriented edge into it. Helper toward `lem-lr-ind` and
the inverse KMSW trees; not the paper result
315–318,343–348`). -/
theorem vertexRotationCycle_outgoing_or_reverseIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (d : vertexRotationCycle B v) :
    (B.map.tail d.1) ∨
      ∃ e, B.map.tail e ∧ dartHeadVertex B.map e = v ∧
        d.1 = B.map.toCombinatorialMap.edgeInv e := by
  classical
  by_cases htail : B.map.tail d.1
  · exact Or.inl htail
  · right
    have htailInv : B.map.tail (B.map.toCombinatorialMap.edgeInv d.1) := by
      by_contra h
      exact htail ((B.map.tail_iff d.1 (B.noMissingDarts d.1)).2 h)
    have hhead : dartHeadVertex B.map (B.map.toCombinatorialMap.edgeInv d.1) = v := by
      simpa [dartHeadVertex, dartTailVertex,
        B.map.toCombinatorialMap.edgeInv_invol] using d.2
    exact ⟨B.map.toCombinatorialMap.edgeInv d.1, htailInv, hhead,
      (B.map.toCombinatorialMap.edgeInv_invol d.1).symm⟩

/-- The source has only outgoing darts. Helper toward `lem-lr-ind` and the
inverse KMSW trees; not the paper result
315–318,322–329,343–348`). -/
theorem source_vertexRotationCycle_all_outgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (d : vertexRotationCycle B B.source) : B.map.tail d.1 := by
  exact tail_of_dartTailVertex_eq_source B d.1 d.2

/-- The sink has only incoming edges, so every dart based there is the
reverse of an incoming oriented dart. Helper toward `lem-lr-ind` and the
inverse KMSW trees; not the paper result
315–318,322–329,343–348`). -/
theorem sink_vertexRotationCycle_all_reverseIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (d : vertexRotationCycle B B.sink) :
    ∃ e, B.map.tail e ∧ dartHeadVertex B.map e = B.sink ∧
      d.1 = B.map.toCombinatorialMap.edgeInv e := by
  have hnot : ¬ B.map.tail d.1 := by
    intro htail
    apply B.isSink
    exact ⟨dartHeadVertex B.map d.1, d.1, B.noMissingDarts _, htail,
      d.2, rfl⟩
  exact (vertexRotationCycle_outgoing_or_reverseIncoming B B.sink d).resolve_left hnot

/-- `faceSucc d` is the dart immediately before `edgeInv d` in `rot` order,
or equivalently immediately after it in `rot⁻¹` order. These two darts are
based at `head(d)`. Helper toward `lem-lr-ind` and the inverse KMSW trees; -/
theorem corner_consecutiveDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    B.map.toCombinatorialMap.faceSucc d =
        B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv d) ∧
      dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
        dartHeadVertex B.map d ∧
      dartTailVertex B.map (B.map.toCombinatorialMap.faceSucc d) =
        dartHeadVertex B.map d := by
  constructor
  · simp [CombinatorialMap.faceSucc]
  · constructor
    · simp [dartTailVertex, dartHeadVertex]
    · apply Quotient.sound
      change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.edgeInv d))
        (B.map.toCombinatorialMap.edgeInv d)
      exact ⟨1, by simp⟩

/-- A vertex-switch corner is exactly an orientation change between the
consecutive vertex darts `edgeInv d` and `faceSucc d`, read in `rot⁻¹` order.
This is the corner-to-rotation dictionary used below. Helper toward
`lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem vertexSwitchCorner_iff_consecutiveDarts_change
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    vertexSwitchCorner B d ↔
      B.map.tail (B.map.toCombinatorialMap.edgeInv d) ≠
        B.map.tail (B.map.toCombinatorialMap.faceSucc d) := by
  classical
  have hinv := B.map.tail_iff d (B.noMissingDarts d)
  by_cases hd : B.map.tail d
  · have hinvnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv d) := hinv.mp hd
    simp [vertexSwitchCorner, hd, hinvnot]
  · have hinvyes : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
      by_contra h
      exact hd (hinv.mpr h)
    simp [vertexSwitchCorner, hd, hinvyes]

/-- A dart based at `v` and its next dart in `rot⁻¹` order remain based at
`v`. Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper -/
theorem vertexRotationCycle_successor_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (d : vertexRotationCycle B v) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm d.1) = v := by
  calc
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm d.1) =
        dartTailVertex B.map d.1 := by
      apply Quotient.sound
      change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.rot.symm d.1) d.1
      exact ⟨1, by simp⟩
    _ = v := d.2

/-- The directed switches on a vertex rotation cycle correspond bijectively
to its vertex-switch corners. The transition is read in `rot⁻¹` order.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
def vertexSwitch_cornerFiber_equiv_rotationTransitions
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :
    {d : D // dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} ≃
      {q : D // dartTailVertex B.map q = v ∧
        B.map.tail q ≠ B.map.tail (B.map.toCombinatorialMap.rot.symm q)} := by
  classical
  let e :
      {d : D // dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} ≃
        {q : D // dartTailVertex B.map q = v ∧
          B.map.tail q ≠ B.map.tail (B.map.toCombinatorialMap.rot.symm q)} := {
    toFun := fun d => ⟨B.map.toCombinatorialMap.edgeInv d.1, by
      refine ⟨?_, ?_⟩
      · change dartHeadVertex B.map d.1 = v
        exact d.2.1
      have h := (vertexSwitchCorner_iff_consecutiveDarts_change B d.1).mp d.2.2
      rw [(corner_consecutiveDarts B d.1).1] at h
      simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h⟩
    invFun := fun q => ⟨B.map.toCombinatorialMap.edgeInv q.1, by
      refine ⟨?_, ?_⟩
      · simpa only [dartHeadVertex, dartTailVertex,
          B.map.toCombinatorialMap.edgeInv_invol] using q.2.1
      · apply (vertexSwitchCorner_iff_consecutiveDarts_change B _).2
        simpa [CombinatorialMap.faceSucc,
          B.map.toCombinatorialMap.edgeInv_invol] using q.2.2⟩
    left_inv := by
      intro d
      apply Subtype.ext
      exact B.map.toCombinatorialMap.edgeInv_invol d.1
    right_inv := by
      intro q
      apply Subtype.ext
      exact B.map.toCombinatorialMap.edgeInv_invol q.1 }
  exact e

/-- At a non-pole vertex there are exactly two changes of orientation in the
`rot⁻¹` rotation cycle. Helper toward `lem-lr-ind` and the inverse KMSW -/
theorem rotationTransition_card_eq_two
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    Nat.card {q : D // dartTailVertex B.map q = v ∧
      B.map.tail q ≠ B.map.tail (B.map.toCombinatorialMap.rot.symm q)} = 2 := by
  calc
    Nat.card {q : D // dartTailVertex B.map q = v ∧
        B.map.tail q ≠ B.map.tail (B.map.toCombinatorialMap.rot.symm q)} =
      Nat.card {d : D // dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} :=
        Nat.card_congr (vertexSwitch_cornerFiber_equiv_rotationTransitions B v).symm
    _ = 2 := vertexSwitch_card_eq_two B v hs ht

private theorem rotInv_sameVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot.symm d) =
      dartTailVertex B.map d := by
  apply Quotient.sound
  change Equiv.Perm.SameCycle B.map.toCombinatorialMap.rot
    (B.map.toCombinatorialMap.rot.symm d) d
  exact ⟨1, by simp⟩

private theorem sameCycle_rotInv_of_sameVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {v : MapVertex B.map}
    {x y : D} (hx : dartTailVertex B.map x = v)
    (hy : dartTailVertex B.map y = v) :
    Equiv.Perm.SameCycle (B.map.toCombinatorialMap.rot.symm) x y := by
  have hxy : dartTailVertex B.map x = dartTailVertex B.map y := hx.trans hy.symm
  have hrot : B.map.toCombinatorialMap.rot.SameCycle x y := Quotient.exact hxy
  exact Equiv.Perm.sameCycle_inv.mpr hrot

private theorem exists_false_true_transition
    {α : Type*} [Finite α] (p : Equiv.Perm α) (b : α → Bool) (x y : α)
    (hcycle : Equiv.Perm.SameCycle p x y) (hx : b x = false) (hy : b y = true) :
    ∃ z, b z = false ∧ b (p z) = true := by
  have horbit : ∃ n, (p ^ n) x = y := hcycle.exists_nat_pow_eq
  obtain ⟨n, hn⟩ := horbit
  have hend : b ((p ^ n) x) = true := by rw [hn]; exact hy
  have hsegment : ∀ n, b x = false → b ((p ^ n) x) = true →
      ∃ k < n, b ((p ^ k) x) = false ∧ b ((p ^ (k + 1)) x) = true := by
    intro n
    induction n with
    | zero => intro h₀ h₁; simp_all
    | succ n ih =>
        intro h₀ h₁
        by_cases hmid : b ((p ^ n) x) = true
        · obtain ⟨k, hk, hfalse, htrue⟩ := ih h₀ hmid
          exact ⟨k, by omega, hfalse, htrue⟩
        · have hmid' : b ((p ^ n) x) = false := Bool.eq_false_of_not_eq_true hmid
          refine ⟨n, Nat.lt_succ_self n, hmid', ?_⟩
          simpa only [pow_succ', Equiv.Perm.mul_apply] using h₁
  obtain ⟨k, _, hfalse, htrue⟩ := hsegment n hx hend
  exact ⟨(p ^ k) x, hfalse, by simpa only [pow_succ', Equiv.Perm.mul_apply] using htrue⟩

private theorem exists_true_false_transition
    {α : Type*} [Finite α] (p : Equiv.Perm α) (b : α → Bool) (x y : α)
    (hcycle : Equiv.Perm.SameCycle p x y) (hx : b x = true) (hy : b y = false) :
    ∃ z, b z = true ∧ b (p z) = false := by
  obtain ⟨z, hz, hpz⟩ := exists_false_true_transition p (fun x => !b x)
    x y hcycle (by simpa using hx) (by simpa using hy)
  exact ⟨z, by simpa using hz, by simpa using hpz⟩

/-- Walking in `rot⁻¹` order, every non-pole vertex has one consecutive
block of outgoing darts followed by one consecutive block of incoming
darts. The displayed endpoints are the two unique orientation changes.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem incoming_block
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    ∃ (leftIncoming rightOutgoing : D),
      dartTailVertex B.map leftIncoming = v ∧ ¬ B.map.tail leftIncoming ∧
      dartTailVertex B.map rightOutgoing = v ∧ B.map.tail rightOutgoing ∧
      B.map.tail (B.map.toCombinatorialMap.rot.symm leftIncoming) ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm rightOutgoing) ∧
      (∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        q ≠ leftIncoming →
          ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm q)) ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        q ≠ rightOutgoing →
          B.map.tail (B.map.toCombinatorialMap.rot.symm q)) ∧
      (∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        B.map.tail (B.map.toCombinatorialMap.rot.symm q) →
          q = leftIncoming) ∧
      (∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm q) →
          q = rightOutgoing) := by
  classical
  let p := B.map.toCombinatorialMap.rot.symm
  let transition (q : D) : Prop :=
    dartTailVertex B.map q = v ∧ B.map.tail q ≠ B.map.tail (p q)
  let transitions : Finset D := Finset.univ.filter transition
  have htransitions_card : transitions.card = 2 := by
    have hsub : Nat.card {q : D // transition q} = 2 := by
      simpa [transition, p] using rotationTransition_card_eq_two B v hs ht
    have hcard : Nat.card {q : D // transition q} = transitions.card := by
      dsimp [transitions, transition]
      exact Nat.subtype_card _ (by intro q; simp)
    omega
  obtain ⟨din, hdin, hdinHead⟩ :=
    (nonterminal_vertex_has_incoming_and_outgoing B v hs ht).1
  obtain ⟨dout, hdout, hdoutTail⟩ :=
    (nonterminal_vertex_has_incoming_and_outgoing B v hs ht).2
  let qin := B.map.toCombinatorialMap.edgeInv din
  have hqinV : dartTailVertex B.map qin = v := by
    simpa [qin, dartTailVertex, dartHeadVertex] using hdinHead
  have hqinNot : ¬ B.map.tail qin := by
    exact (B.map.tail_iff din (B.noMissingDarts din)).mp hdin
  have houtV : dartTailVertex B.map dout = v := hdoutTail
  have hcycle := sameCycle_rotInv_of_sameVertex B hqinV houtV
  let b : D → Bool := fun q =>
    if dartTailVertex B.map q = v then decide (B.map.tail q) else false
  have hbqin : b qin = false := by simp [b, hqinV, hqinNot]
  have hbdout : b dout = true := by simp [b, houtV, hdout]
  obtain ⟨leftIncoming, hleftB, hleftNextB⟩ :=
    exists_false_true_transition p b qin dout hcycle hbqin hbdout
  have hleftNextV : dartTailVertex B.map (p leftIncoming) = v := by
    by_cases h : dartTailVertex B.map (p leftIncoming) = v
    · exact h
    · simp [b, h] at hleftNextB
  have hleftV : dartTailVertex B.map leftIncoming = v := by
    rw [← rotInv_sameVertex B leftIncoming]
    exact hleftNextV
  have hleftNot : ¬ B.map.tail leftIncoming := by
    simpa [b, hleftV] using hleftB
  have hleftNext : B.map.tail (p leftIncoming) := by
    simpa [b, hleftNextV] using hleftNextB
  obtain ⟨rightOutgoing, hrightB, hrightNextB⟩ :=
    exists_true_false_transition p b dout qin hcycle.symm hbdout hbqin
  have hrightV : dartTailVertex B.map rightOutgoing = v := by
    by_cases h : dartTailVertex B.map rightOutgoing = v
    · exact h
    · simp [b, h] at hrightB
  have hrightNextV : dartTailVertex B.map (p rightOutgoing) = v :=
    (rotInv_sameVertex B rightOutgoing).trans hrightV
  have hright : B.map.tail rightOutgoing := by
    simpa [b, hrightV] using hrightB
  have hrightNext : ¬ B.map.tail (p rightOutgoing) := by
    simpa [b, hrightNextV] using hrightNextB
  have hleftMem : leftIncoming ∈ transitions := by
    simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hleftV, by simp [hleftNot, hleftNext]⟩
  have hrightMem : rightOutgoing ∈ transitions := by
    simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hrightV, by simp [hright, hrightNext]⟩
  have hdistinct : leftIncoming ≠ rightOutgoing := by
    intro h
    subst rightOutgoing
    exact hleftNot hright
  have hnoOther (q : D) (hq : q ∈ transitions) :
      q = leftIncoming ∨ q = rightOutgoing := by
    by_contra h
    have hqleft : q ≠ leftIncoming := fun heq => h (Or.inl heq)
    have hqright : q ≠ rightOutgoing := fun heq => h (Or.inr heq)
    have hsubset : insert q ({leftIncoming, rightOutgoing} : Finset D) ⊆ transitions := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · simpa [hx] using hq
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · simpa [hx] using hleftMem
        · simpa [hx] using hrightMem
    have hle := Finset.card_le_card hsubset
    have hqnotpair : q ∉ ({leftIncoming, rightOutgoing} : Finset D) := by
      simp [hqleft, hqright]
    have hthree : (insert q ({leftIncoming, rightOutgoing} : Finset D)).card = 3 := by
      rw [Finset.card_insert_of_notMem hqnotpair, Finset.card_pair hdistinct]
    rw [hthree, htransitions_card] at hle
    omega
  have huniqueUp (q : D) (hqv : dartTailVertex B.map q = v)
      (hq : ¬ B.map.tail q) (hpq : B.map.tail (p q)) : q = leftIncoming := by
    have hqmem : q ∈ transitions := by
      simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqv, by simp [hq, hpq]⟩
    rcases hnoOther q hqmem with h | h
    · exact h
    · subst q
      exact (hq hright).elim
  have huniqueDown (q : D) (hqv : dartTailVertex B.map q = v)
      (hq : B.map.tail q) (hpq : ¬ B.map.tail (p q)) : q = rightOutgoing := by
    have hqmem : q ∈ transitions := by
      simp only [transitions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqv, by simp [hq, hpq]⟩
    rcases hnoOther q hqmem with h | h
    · subst q
      exact (hpq hleftNext).elim
    · exact h
  refine ⟨leftIncoming, rightOutgoing, hleftV, hleftNot, hrightV, hright,
    hleftNext, hrightNext, ?_, ?_, ?_, ?_⟩
  · intro q hqv hq hqne
    by_contra hpq
    exact hqne (huniqueUp q hqv hq (by simpa [p] using hpq))
  · intro q hqv hq hqne
    by_contra hpq
    exact hqne (huniqueDown q hqv hq (by simpa [p] using hpq))
  · exact huniqueUp
  · exact huniqueDown

private def outerBoundaryDarts
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : List D :=
  B.leftPath.darts ++
    B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv

private theorem outerBoundaryDarts_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).Nodup := by
  simpa [outerBoundaryDarts] using
    B.outerSplit.2.1.perm.nodup_iff.mp B.outerWord.nodup

private theorem outerBoundaryDarts_length
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (outerBoundaryDarts B).length = ℓ + r := by
  simp [outerBoundaryDarts, B.leftPath.darts_length,
    B.rightPath.darts_length]

private theorem outerBoundaryDarts_faceSucc_eq_formPerm
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : B.map.IsOuter d) :
    B.map.toCombinatorialMap.faceSucc d = (outerBoundaryDarts B).formPerm d := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr hd
  calc
    B.map.toCombinatorialMap.faceSucc d = B.outerWord.letters.formPerm d :=
      B.outerSplit.1.2.2 d hword
    _ = (outerBoundaryDarts B).formPerm d := by
      simpa [outerBoundaryDarts] using congrArg (fun f : Equiv.Perm D => f d)
        (List.formPerm_eq_of_isRotated B.outerWord.nodup B.outerSplit.2.1)

private theorem outerBoundaryDarts_mem_isOuter
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (hd : d ∈ outerBoundaryDarts B) : B.map.IsOuter d := by
  have hword : d ∈ B.outerWord.letters := by
    exact (B.outerSplit.2.1.perm.mem_iff).mpr (by simpa [outerBoundaryDarts] using hd)
  exact (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mp hword

/-- The source corner of the marked outer face is the first left-boundary
dart. This pins the `rot⁻¹` left-to-right convention used by the selectors.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem outerFace_sourceCorner_eq_firstLeftDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    B.map.toCombinatorialMap.faceSucc
        (B.map.toCombinatorialMap.edgeInv
          (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos))) =
      B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  let xs := outerBoundaryDarts B
  let dR := B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)
  have hlen : xs.length = ℓ + r := outerBoundaryDarts_length B
  have hleft : 0 < ℓ := Nat.zero_lt_of_lt B.left_length_pos
  have hright : 0 < r := Nat.zero_lt_of_lt B.right_length_pos
  have hpos : 0 < ℓ + r := by omega
  have hne : xs ≠ [] := by
    intro h
    simp [h] at hlen
    omega
  have hlast : xs.getLast hne = B.map.toCombinatorialMap.edgeInv dR := by
    have hrightNonempty : B.rightPath.darts ≠ [] := by
      intro hn
      have h := congrArg List.length hn
      simp [B.rightPath.darts_length] at h
      omega
    have hhead : B.rightPath.darts.head hrightNonempty = dR := by
      dsimp [dR, SimpleDirectedDartPath.firstDart]
      rw [List.head_eq_getElem_zero hrightNonempty]
    dsimp [xs, outerBoundaryDarts]
    rw [List.getLast_append_of_right_ne_nil]
    · simpa [dR, SimpleDirectedDartPath.firstDart, List.get_eq_getElem] using
        congrArg B.map.toCombinatorialMap.edgeInv hhead
    · intro hnil
      have hlenR := congrArg List.length hnil
      simp [B.rightPath.darts_length] at hlenR
      omega
  have hlastMem : xs.getLast hne ∈ xs := List.getLast_mem hne
  have hlastOuter : B.map.IsOuter (xs.getLast hne) :=
    outerBoundaryDarts_mem_isOuter B hlastMem
  have hmod : (ℓ + r) % (ℓ + r) < xs.length := by
    rw [hlen]
    exact Nat.mod_lt _ hpos
  have hfirst : 0 < xs.length := by rw [hlen]; omega
  have hlastIndex : xs[ℓ + r - 1]'(by rw [hlen]; omega) = xs.getLast hne := by
    have hh : xs[xs.length - 1]'(by omega) = xs.getLast hne := by
      simpa only [List.get_eq_getElem] using
        List.get_length_sub_one (l := xs) (by omega)
    have hlen' : ℓ + r - 1 = xs.length - 1 := congrArg (fun n : ℕ => n - 1) hlen.symm
    simpa only [hlen'] using hh
  have hidxOuter : B.map.IsOuter (xs[ℓ + r - 1]'(by rw [hlen]; omega)) := by
    rw [hlastIndex]
    exact hlastOuter
  have hsucc : B.map.toCombinatorialMap.faceSucc
        (xs[ℓ + r - 1]'(by rw [hlen]; omega)) =
      xs[(ℓ + r) % (ℓ + r)]'hmod := by
    have hform := List.formPerm_apply_getElem xs (outerBoundaryDarts_nodup B)
      (ℓ + r - 1) (by rw [hlen]; omega)
    have hindex : ℓ + r - 1 + 1 = ℓ + r := by omega
    rw [outerBoundaryDarts_faceSucc_eq_formPerm B hidxOuter]
    calc
      (outerBoundaryDarts B).formPerm xs[ℓ + r - 1] = xs[0]'hfirst := by
        simpa only [hindex, hlen, Nat.mod_self] using hform
      _ = xs[(ℓ + r) % (ℓ + r)]'hmod := by simp
  have hcorner : B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.edgeInv dR) =
      xs[0]'(by simpa only [Nat.mod_self] using hmod) := by
    rw [hlastIndex, hlast] at hsucc
    simpa only [Nat.mod_self] using hsucc
  have hxs0 : xs[0]'hfirst = B.leftPath.firstDart
      (Nat.zero_lt_of_lt B.left_length_pos) := by
    have hleftIndex : 0 < B.leftPath.darts.length := by
      rw [B.leftPath.darts_length]
      exact hleft
    have hzero :
        (B.leftPath.darts ++
          B.rightPath.darts.reverse.map B.map.toCombinatorialMap.edgeInv)[0]'
            (by simp [B.leftPath.darts_length]; omega) =
          B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
      rw [List.getElem_append_left hleftIndex]
      simp [SimpleDirectedDartPath.firstDart, List.get_eq_getElem]
    simpa [xs, outerBoundaryDarts] using hzero
  rw [hxs0] at hcorner
  exact hcorner

/-- The source and sink are distinct in a positive finite bipolar map.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem bipolar_source_ne_sink
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) : B.source ≠ B.sink := by
  intro h
  have hlen : 0 < B.leftPath.darts.length := by
    rw [B.leftPath.darts_length]
    exact B.left_length_pos
  let i : Fin B.leftPath.darts.length := ⟨0, hlen⟩
  obtain ⟨_, htail, hstart, _⟩ := B.leftPath.edge_step i
  have hstart' : B.leftPath.vertices.get ⟨0, by
      rw [B.leftPath.vertices_length]
      omega⟩ = dartTailVertex B.map (B.leftPath.darts.get i) := by
    simpa [i] using hstart
  have hv : dartTailVertex B.map (B.leftPath.darts.get i) = B.source :=
    hstart'.symm.trans B.leftPath.start_vertex
  have hstep : B.map.directedStep B.source
      (dartHeadVertex B.map (B.leftPath.darts.get i)) := by
    exact ⟨B.leftPath.darts.get i, B.noMissingDarts _, htail, hv, rfl⟩
  apply B.isSink
  refine ⟨dartHeadVertex B.map (B.leftPath.darts.get i), ?_⟩
  simpa [h] using hstep

/-- The final dart of a positive-length directed boundary path. Helper
toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
@[expose] def pathLastDart
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M s t n) (hn : 0 < n) : D :=
  P.darts.get ⟨n - 1, by rw [P.darts_length]; omega⟩

/-- Choice notation for the unique incoming-block endpoint established by
`incoming_block`. The endpoint is choice-independent by that theorem.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
@[expose] noncomputable def blockLeftIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) : D :=
  Classical.choose (incoming_block B v hs ht)

/-- Choice notation for the unique outgoing-block endpoint established by
`incoming_block`. The endpoint is choice-independent by that theorem.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
@[expose] noncomputable def blockRightOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) : D :=
  Classical.choose (Classical.choose_spec (incoming_block B v hs ht))

/-- Canonical leftmost outgoing dart: the dart immediately after the
incoming block in `rot⁻¹` order. At the source, the marked outer-face corner
sets the first left-boundary dart. Helper toward `lem-lr-ind` and the inverse -/
@[expose] noncomputable def leftmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) : D := by
  classical
  exact if hs : v = B.source then
    B.map.toCombinatorialMap.faceSucc
      (B.map.toCombinatorialMap.edgeInv
        (B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)))
  else
    B.map.toCombinatorialMap.rot.symm
      (blockLeftIncoming B v (fun h => hs h) hvs)

/-- Canonical rightmost outgoing dart: the outgoing dart immediately before
the incoming block in `rot⁻¹` order. At the source, the outer-face corner
selects the first right-boundary dart. Helper toward `lem-lr-ind` and the -/
@[expose] noncomputable def rightmostOutgoing
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) : D := by
  classical
  exact if hs : v = B.source then
    B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos)
  else
    blockRightOutgoing B v (fun h => hs h) hvs

/-- Canonical leftmost incoming dart, represented by its reverse at the
vertex. At the sink, it is the reverse of the last left-boundary dart.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
@[expose] noncomputable def leftmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.source) : D := by
  classical
  exact if ht : v = B.sink then
    B.map.toCombinatorialMap.edgeInv
      (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos))
  else
    blockLeftIncoming B v hvs (fun h => ht h)

/-- Canonical rightmost incoming dart, represented by its reverse at the
vertex. At the sink, it is the reverse of the last right-boundary dart.
Helper toward `lem-lr-ind` and the inverse KMSW trees; not the paper result -/
@[expose] noncomputable def rightmostIncoming
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.source) : D := by
  classical
  exact if ht : v = B.sink then
    B.map.toCombinatorialMap.edgeInv
      (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos))
  else
    B.map.toCombinatorialMap.rot.symm
      (blockRightOutgoing B v hvs (fun h => ht h))

/-- The source selector agrees with the first left-boundary dart because
dart to that first dart. This fixes the left/right convention. Helper toward
`lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem leftmostOutgoing_source_eq_firstLeftDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    leftmostOutgoing B B.source (bipolar_source_ne_sink B) =
      B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  simpa [leftmostOutgoing] using outerFace_sourceCorner_eq_firstLeftDart B

private theorem rot_sameVertex
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (d : D) :
    dartTailVertex B.map (B.map.toCombinatorialMap.rot d) =
      dartTailVertex B.map d := by
  have h := rotInv_sameVertex B (B.map.toCombinatorialMap.rot d)
  simpa using h.symm

/-- At a non-pole vertex, `leftmostOutgoing` is the unique outgoing dart
whose immediately preceding dart in `rot⁻¹` order is incoming. Helper toward
`lem-lr-ind` and the inverse KMSW trees; not the paper result -/
theorem leftmostOutgoing_internal_characterization
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (leftmostOutgoing B v ht) = v ∧
      B.map.tail (leftmostOutgoing B v ht) ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.rot (leftmostOutgoing B v ht)) ∧
      ∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ¬ B.map.tail (B.map.toCombinatorialMap.rot q) →
          q = leftmostOutgoing B v ht := by
  classical
  let hblock := incoming_block B v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : leftmostOutgoing B v ht =
      B.map.toCombinatorialMap.rot.symm (Classical.choose hblock) := by
    simp [leftmostOutgoing, hs, blockLeftIncoming]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact (rotInv_sameVertex B (Classical.choose hblock)).trans hliV
  · rw [hsel]
    exact hliNext
  · rw [hsel]
    simpa using hliNot
  · intro q hqv hq hqprev
    have hprevV : dartTailVertex B.map (B.map.toCombinatorialMap.rot q) = v :=
      (rot_sameVertex B q).trans hqv
    have hprev := huniqueUp (B.map.toCombinatorialMap.rot q)
      hprevV hqprev (by simpa using hq)
    calc
      q = B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.rot q) := by simp
      _ = B.map.toCombinatorialMap.rot.symm (Classical.choose hblock) :=
        congrArg B.map.toCombinatorialMap.rot.symm hprev
      _ = leftmostOutgoing B v ht := hsel.symm

/-- At a non-pole vertex, `rightmostOutgoing` is the unique outgoing dart
whose successor in `rot⁻¹` order is incoming. Helper toward `lem-lr-ind` and
the inverse KMSW trees; not the paper result -/
theorem rightmostOutgoing_internal_characterization
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (rightmostOutgoing B v ht) = v ∧
      B.map.tail (rightmostOutgoing B v ht) ∧
      ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm
        (rightmostOutgoing B v ht)) ∧
      ∀ q, dartTailVertex B.map q = v → B.map.tail q →
        ¬ B.map.tail (B.map.toCombinatorialMap.rot.symm q) →
          q = rightmostOutgoing B v ht := by
  classical
  let hblock := incoming_block B v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : rightmostOutgoing B v ht = blockRightOutgoing B v hs ht := by
    simp [rightmostOutgoing, hs, blockRightOutgoing]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact hroV
  · rw [hsel]
    exact hro
  · rw [hsel]
    exact hroNext
  · intro q hqv hq hqnext
    exact (huniqueDown q hqv hq hqnext).trans hsel.symm

/-- At a non-pole vertex, `leftmostIncoming` is the unique incoming reverse
dart whose successor in `rot⁻¹` order is outgoing. Helper toward `lem-lr-ind`
and the inverse KMSW trees; not the paper result -/
theorem leftmostIncoming_internal_characterization
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (leftmostIncoming B v hs) = v ∧
      ¬ B.map.tail (leftmostIncoming B v hs) ∧
      B.map.tail (B.map.toCombinatorialMap.rot.symm
        (leftmostIncoming B v hs)) ∧
      ∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        B.map.tail (B.map.toCombinatorialMap.rot.symm q) →
          q = leftmostIncoming B v hs := by
  classical
  let hblock := incoming_block B v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : leftmostIncoming B v hs = blockLeftIncoming B v hs ht := by
    simp [leftmostIncoming, ht, blockLeftIncoming]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact hliV
  · rw [hsel]
    exact hliNot
  · rw [hsel]
    exact hliNext
  · intro q hqv hq hqnext
    exact (huniqueUp q hqv hq hqnext).trans hsel.symm

/-- At a non-pole vertex, `rightmostIncoming` is the unique incoming reverse
dart whose predecessor in `rot⁻¹` order is outgoing. Helper toward `lem-lr-ind`
and the inverse KMSW trees; not the paper result -/
theorem rightmostIncoming_internal_characterization
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    dartTailVertex B.map (rightmostIncoming B v hs) = v ∧
      ¬ B.map.tail (rightmostIncoming B v hs) ∧
      B.map.tail (B.map.toCombinatorialMap.rot
        (rightmostIncoming B v hs)) ∧
      ∀ q, dartTailVertex B.map q = v → ¬ B.map.tail q →
        B.map.tail (B.map.toCombinatorialMap.rot q) →
          q = rightmostIncoming B v hs := by
  classical
  let hblock := incoming_block B v hs ht
  rcases Classical.choose_spec (Classical.choose_spec hblock) with
    ⟨hliV, hliNot, hroV, hro, hliNext, hroNext,
      hstayIn, hstayOut, huniqueUp, huniqueDown⟩
  have hsel : rightmostIncoming B v hs =
      B.map.toCombinatorialMap.rot.symm (blockRightOutgoing B v hs ht) := by
    simp [rightmostIncoming, ht, blockRightOutgoing]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel]
    exact (rotInv_sameVertex B (blockRightOutgoing B v hs ht)).trans hroV
  · rw [hsel]
    exact hroNext
  · rw [hsel]
    simpa [blockRightOutgoing] using hro
  · intro q hqv hq hqprev
    have hrotV : dartTailVertex B.map (B.map.toCombinatorialMap.rot q) = v :=
      (rot_sameVertex B q).trans hqv
    have hroEq := huniqueDown (B.map.toCombinatorialMap.rot q)
      hrotV hqprev (by simpa using hq)
    calc
      q = B.map.toCombinatorialMap.rot.symm
          (B.map.toCombinatorialMap.rot q) := by simp
      _ = B.map.toCombinatorialMap.rot.symm (blockRightOutgoing B v hs ht) :=
        congrArg B.map.toCombinatorialMap.rot.symm hroEq
      _ = rightmostIncoming B v hs := hsel.symm

/-- At the source, the rightmost outgoing boundary dart is the first
right-boundary dart. Helper toward `lem-lr-ind` and the inverse KMSW trees; -/
theorem rightmostOutgoing_source_eq_firstRightDart
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    rightmostOutgoing B B.source (bipolar_source_ne_sink B) =
      B.rightPath.firstDart (Nat.zero_lt_of_lt B.right_length_pos) := by
  simp [rightmostOutgoing]

/-- At the sink, the extreme incoming darts are the reverses of the final
left and right boundary darts, respectively. Helper toward `lem-lr-ind` and
the inverse KMSW trees; not the paper result -/
theorem incomingSelectors_sink_boundary
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    leftmostIncoming B B.sink (bipolar_source_ne_sink B).symm =
      B.map.toCombinatorialMap.edgeInv
        (pathLastDart B.leftPath (Nat.zero_lt_of_lt B.left_length_pos)) ∧
    rightmostIncoming B B.sink (bipolar_source_ne_sink B).symm =
      B.map.toCombinatorialMap.edgeInv
        (pathLastDart B.rightPath (Nat.zero_lt_of_lt B.right_length_pos)) := by
  constructor <;> simp [leftmostIncoming, rightmostIncoming]

end DirectedDistances.PlanarMap
