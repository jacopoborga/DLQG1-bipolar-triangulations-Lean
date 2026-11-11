/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarOuterSwitch
public import DirectedDistances.PlanarMap.FiniteBipolarInnerSwitch
public import DirectedDistances.PlanarMap.FiniteBipolarSwitchCount
public import DirectedDistances.PlanarMap.FiniteBipolarIncomingInterval
public import DirectedDistances.PlanarMap.CombinatorialMap

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The corners at either pole cannot be vertex-switches. Helper toward -/
theorem pole_vertexSwitch_card_zero
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // dartHeadVertex B.map d = B.source ∧ vertexSwitchCorner B d} = 0 ∧
    Nat.card {d : D // dartHeadVertex B.map d = B.sink ∧ vertexSwitchCorner B d} = 0 := by
  classical
  constructor
  · have hempty : IsEmpty {d : D // dartHeadVertex B.map d = B.source ∧ vertexSwitchCorner B d} :=
      ⟨fun d => (corner_switch_partition B d.1).mp
        (source_corner_faceSwitch B d.1 d.2.1) d.2.2⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact hempty
  · have hempty : IsEmpty {d : D // dartHeadVertex B.map d = B.sink ∧ vertexSwitchCorner B d} :=
      ⟨fun d => (corner_switch_partition B d.1).mp
        (sink_corner_faceSwitch B d.1 d.2.1) d.2.2⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact hempty

/-- Count all vertex-switch corners by separating the marked outer face from
the inner faces. Helper toward `lem-lr-ind`; not the paper result -/
theorem vertexSwitch_total_card
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    Nat.card {d : D // vertexSwitchCorner B d} =
      B.map.numInnerFaces + (ℓ + r - 2) := by
  classical
  let outer := {d : D // B.map.IsOuter d ∧ vertexSwitchCorner B d}
  let inner := {d : D // ¬ B.map.IsOuter d ∧ vertexSwitchCorner B d}
  let all := {d : D // vertexSwitchCorner B d}
  let e : all ≃ Sum outer inner := {
    toFun := fun d => if h : B.map.IsOuter d.1 then
      Sum.inl ⟨d.1, h, d.2⟩ else Sum.inr ⟨d.1, h, d.2⟩
    invFun := fun x => match x with
      | Sum.inl d => ⟨d.1, d.2.2⟩
      | Sum.inr d => ⟨d.1, d.2.2⟩
    left_inv := by
      intro d
      apply Subtype.ext
      by_cases h : B.map.IsOuter d.1 <;> simp [h]
    right_inv := by
      intro x
      rcases x with d | d
      · simp [d.2.1]
      · simp [d.2.1] }
  calc
    Nat.card all = Nat.card (Sum outer inner) := Nat.card_congr e
    _ = Nat.card outer + Nat.card inner := by simp
    _ = B.map.numInnerFaces + (ℓ + r - 2) := by
      rw [innerVertexSwitch_card, outerVertexSwitch_card]
      omega

private def vertexSwitchFiber
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) :=
  {d : D // dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d}

private theorem vertexSwitchFiber_sum
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    [Fintype (MapVertex B.map)] :
    Nat.card {d : D // vertexSwitchCorner B d} =
      ∑ v : MapVertex B.map, Nat.card (vertexSwitchFiber B v) := by
  classical
  let all := {d : D // vertexSwitchCorner B d}
  let fiber := vertexSwitchFiber B
  let allFintype : Fintype all := Fintype.ofFinite _
  let fiberFintype : ∀ v, Fintype (fiber v) := fun v =>
    Fintype.subtype
      (Finset.univ.filter (fun d : D =>
        dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d))
      (by intro d; simp)
  let sigmaFintype : Fintype (Σ v, fiber v) :=
    @Sigma.instFintype (MapVertex B.map) fiber fiberFintype inferInstance
  let e : all ≃ (Σ v, fiber v) := {
    toFun := fun d => ⟨dartHeadVertex B.map d.1, ⟨d.1, rfl, d.2⟩⟩
    invFun := fun x => ⟨x.2.1, x.2.2.2⟩
    left_inv := by intro d; apply Subtype.ext; rfl
    right_inv := by
      intro x
      rcases x with ⟨v, ⟨d, hv, hs⟩⟩
      cases hv
      rfl }
  calc
    Nat.card all = @Fintype.card all allFintype :=
      @Nat.card_eq_fintype_card all allFintype
    _ = @Fintype.card (Σ v, fiber v) sigmaFintype :=
      @Fintype.card_congr all (Σ v, fiber v) allFintype sigmaFintype e
    _ = ∑ v : MapVertex B.map, @Fintype.card (fiber v) (fiberFintype v) :=
      @Fintype.card_sigma (MapVertex B.map) fiber inferInstance fiberFintype
    _ = ∑ v : MapVertex B.map, Nat.card (fiber v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (@Nat.card_eq_fintype_card (fiber v) (fiberFintype v)).symm

private theorem bipolar_source_ne_sink
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

private theorem euler_vertexSwitch_count
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    2 * (B.map.toCombinatorialMap.numVertices - 2) =
      B.map.numInnerFaces + (ℓ + r - 2) := by
  classical
  let M := B.map.toCombinatorialMap
  have hl := B.left_length_pos
  have hr := B.right_length_pos
  have hL : 2 ≤ ℓ + r := by omega
  have hEuler : (M.numVertices : ℤ) - M.numEdges + M.numFaces = 2 := by
    simpa [CombinatorialMap.eulerChar] using B.planar.2
  have hFpos : 0 < M.numFaces := by
    change 0 < Fintype.card (CombinatorialMap.FaceQuotient M)
    exact Fintype.card_pos_iff.mpr ⟨Quotient.mk
      (Equiv.Perm.SameCycle.setoid M.faceSucc) B.map.outer⟩
  have hF : M.numFaces = B.map.numInnerFaces + 1 := by
    change M.numFaces = M.numFaces - 1 + 1
    omega
  have hD : Fintype.card D = 3 * B.map.numInnerFaces + (ℓ + r) :=
    dartCount_eq_innerFaces B
  have hE : 2 * M.numEdges = 3 * B.map.numInnerFaces + (ℓ + r) := by
    rw [← hD]
    exact M.two_mul_numEdges
  have hEcast : (2 : ℤ) * (M.numEdges : ℤ) =
      ((3 * B.map.numInnerFaces + (ℓ + r) : ℕ) : ℤ) := by
    exact_mod_cast hE
  have hFcast : (M.numFaces : ℤ) =
      ((B.map.numInnerFaces + 1 : ℕ) : ℤ) := by
    exact_mod_cast hF
  have hV : 2 * M.numVertices = B.map.numInnerFaces + (ℓ + r) + 2 := by
    omega
  change 2 * (M.numVertices - 2) = B.map.numInnerFaces + (ℓ + r - 2)
  omega

/-- Every non-pole vertex has exactly two vertex-switch corners. Corners are
counted at `head(d)` as in the incoming-interval convention. Helper toward -/
theorem vertexSwitch_card_eq_two
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    Nat.card {d : D // dartHeadVertex B.map d = v ∧ vertexSwitchCorner B d} = 2 := by
  classical
  let f : MapVertex B.map → ℕ := fun w => Nat.card (vertexSwitchFiber B w)
  let nonpoles : Finset (CombinatorialMap.VertexQuotient B.map.toCombinatorialMap) :=
    (Finset.univ.erase B.source).erase B.sink
  have hst := bipolar_source_ne_sink B
  have hsourceZero : f B.source = 0 := by
    simpa [f, vertexSwitchFiber] using (pole_vertexSwitch_card_zero B).1
  have hsinkZero : f B.sink = 0 := by
    simpa [f, vertexSwitchFiber] using (pole_vertexSwitch_card_zero B).2
  have hsumGlobal : (∑ w : MapVertex B.map, f w) =
      2 * (B.map.toCombinatorialMap.numVertices - 2) := by
    calc
      (∑ w : MapVertex B.map, f w) =
          Nat.card {d : D // vertexSwitchCorner B d} := by
            simpa [f, vertexSwitchFiber] using
              (vertexSwitchFiber_sum B).symm
      _ = B.map.numInnerFaces + (ℓ + r - 2) := vertexSwitch_total_card B
      _ = 2 * (B.map.toCombinatorialMap.numVertices - 2) :=
        (euler_vertexSwitch_count B).symm
  have hcardNonpoles : nonpoles.card =
      B.map.toCombinatorialMap.numVertices - 2 := by
    have hnum : Fintype.card (MapVertex B.map) =
        B.map.toCombinatorialMap.numVertices := by
      unfold CombinatorialMap.numVertices
      exact Fintype.card_congr (Equiv.refl _)
    have hsrc : B.source ∈ Finset.univ := Finset.mem_univ _
    have hsink : B.sink ∈ Finset.univ.erase B.source :=
      Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem hsink, Finset.card_erase_of_mem hsrc,
      Finset.card_univ, hnum]
    omega
  have hsplit : (∑ w : MapVertex B.map, f w) =
      f B.source + f B.sink + ∑ w ∈ nonpoles, f w := by
    rw [← Finset.sum_erase_add (s := Finset.univ) (a := B.source) f
      (Finset.mem_univ B.source)]
    rw [← Finset.sum_erase_add (s := Finset.univ.erase B.source)
      (a := B.sink) f (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩)]
    simp only [nonpoles]
    ac_rfl
  have hsumNonpoles : (∑ w ∈ nonpoles, f w) =
      2 * (B.map.toCombinatorialMap.numVertices - 2) := by
    calc
      (∑ w ∈ nonpoles, f w) =
          f B.source + f B.sink + ∑ w ∈ nonpoles, f w := by
            simp [hsourceZero, hsinkZero]
      _ = ∑ w : MapVertex B.map, f w := hsplit.symm
      _ = 2 * (B.map.toCombinatorialMap.numVertices - 2) := hsumGlobal
  have hge : ∀ w ∈ nonpoles, 2 ≤ f w := by
    intro w hw
    rcases Finset.mem_erase.mp hw with ⟨hwsink, hw'⟩
    rcases Finset.mem_erase.mp hw' with ⟨hwsource, _⟩
    have hlocal := nonterminal_vertex_has_incoming_and_outgoing B w hwsource hwsink
    exact (vertexSwitch_even_and_pos B w hlocal.1 hlocal.2).2
  have hv : v ∈ nonpoles := by simp [nonpoles, hs, ht]
  have hlocal := nonterminal_vertex_has_incoming_and_outgoing B v hs ht
  have hbound := vertexSwitch_even_and_pos B v hlocal.1 hlocal.2
  have hbound' : 2 ≤ f v := by simpa [f, vertexSwitchFiber] using hbound.2
  change f v = 2
  by_contra hne
  have hthree : 3 ≤ f v := by omega
  have hcardErase := Finset.card_erase_of_mem hv
  have hsumSplit : (∑ w ∈ nonpoles, f w) =
      f v + ∑ w ∈ nonpoles.erase v, f w := by
    rw [← Finset.sum_erase_add (s := nonpoles) (a := v) f hv]
    exact add_comm _ _
  have hsumRest : 2 * (nonpoles.erase v).card ≤
      ∑ w ∈ nonpoles.erase v, f w := by
    calc
      2 * (nonpoles.erase v).card =
          ∑ w ∈ nonpoles.erase v, 2 := by
            rw [Finset.sum_const_nat (fun w hw => rfl)]
            omega
      _ ≤ ∑ w ∈ nonpoles.erase v, f w :=
        Finset.sum_le_sum (fun w hw => hge w (Finset.mem_of_mem_erase hw))
  have hlarge : 2 * nonpoles.card + 1 ≤ ∑ w ∈ nonpoles, f w := by
    rw [hsumSplit]
    omega
  rw [hsumNonpoles, hcardNonpoles] at hlarge
  omega

end DirectedDistances.PlanarMap
