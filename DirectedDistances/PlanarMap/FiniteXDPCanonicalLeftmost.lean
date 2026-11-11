/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBipolarIncomingBlock
public import DirectedDistances.PlanarMap.FiniteXDPLeftmostSelector
public import DirectedDistances.PlanarMap.FiniteXDPGeodesicDart
public import DirectedDistances.PlanarMap.FiniteXDPSelectorPath

/-! # Canonical outgoing rotation order and leftmost XDP geodesic helper

Helpers toward `lem-lr-ind` (leftmost XDP geodesic); not the paper result -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

private theorem list_nodup_eraseDups_local
    {α : Type*} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  suffices h : ∀ n : ℕ, ∀ l : List α, l.length = n → l.eraseDups.Nodup by
    exact h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro l hl
      cases l with
      | nil => simp
      | cons a t =>
          simp only [List.length_cons] at hl
          rw [List.eraseDups_cons]
          apply List.nodup_cons.mpr
          constructor
          · intro ha
            have ha' : a ∈ t.filter (fun b => !(b == a)) :=
              (List.mem_eraseDups).mp ha
            rcases List.mem_filter.mp ha' with ⟨_, hneq⟩
            simp at hneq
          · apply ih ((t.filter (fun b => !(b == a))).length)
            · have hle := List.length_filter_le (fun b => !(b == a)) t
              omega
            · rfl

/-- The deduplicated outgoing part of the `rot.symm` scan anchored at the
canonical leftmost outgoing dart. Helper toward `lem-lr-ind` (leftmost XDP -/
@[expose] noncomputable def canonicalOutgoingOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) : List D :=
  (finiteOutgoingRotationOrder B (leftmostOutgoing B v hvs)).eraseDups

/-- The anchor of the canonical order is outgoing at its vertex. Helper
toward `lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem canonicalLeftmostOutgoing_spec
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) :
    dartTailVertex B.map (leftmostOutgoing B v hvs) = v ∧
      B.map.tail (leftmostOutgoing B v hvs) := by
  by_cases hs : v = B.source
  · subst v
    have hcorner := dartTailVertex_finiteXDPLeftmostCorner B B.source
    rw [finiteXDPLeftmostCorner_source] at hcorner
    have hvertex : dartTailVertex B.map
        (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) = B.source := hcorner
    constructor
    · rw [leftmostOutgoing_source_eq_firstLeftDart]
      exact hvertex
    · rw [leftmostOutgoing_source_eq_firstLeftDart]
      exact source_vertexRotationCycle_all_outgoing B
        ⟨B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos), hvertex⟩
  · have h := leftmostOutgoing_internal_characterization B v hs hvs
    exact ⟨h.1, h.2.1⟩

/-- The canonical order contains exactly the outgoing darts based at `v`.
Helper toward `lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem mem_canonicalOutgoingOrder_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) (d : D) :
    d ∈ canonicalOutgoingOrder B v hvs ↔
      dartTailVertex B.map d = v ∧ B.map.tail d := by
  rw [canonicalOutgoingOrder, List.mem_eraseDups,
    mem_finiteOutgoingRotationOrder_iff]
  constructor
  · rintro ⟨hvertex, htail⟩
    exact ⟨hvertex.trans (canonicalLeftmostOutgoing_spec B v hvs).1, htail⟩
  · rintro ⟨hvertex, htail⟩
    exact ⟨hvertex.trans (canonicalLeftmostOutgoing_spec B v hvs).1.symm, htail⟩

/-- The canonical outgoing order has no repeated darts. Helper toward
`lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem canonicalOutgoingOrder_nodup
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) :
    (canonicalOutgoingOrder B v hvs).Nodup := by
  exact list_nodup_eraseDups_local _

/-- The canonical outgoing order begins at `leftmostOutgoing`. Helper toward
`lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem canonicalOutgoingOrder_cons
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) :
    ∃ rest, canonicalOutgoingOrder B v hvs =
      leftmostOutgoing B v hvs :: rest := by
  classical
  let c := leftmostOutgoing B v hvs
  let σ := B.map.toCombinatorialMap.rot.symm
  let n := orderOf σ - 1
  have hpos : 0 < orderOf σ := orderOf_pos σ
  have hn : n + 1 = orderOf σ := by
    dsimp [n]
    omega
  have hscan : finiteRotationScan B c =
      c :: List.ofFn (fun i : Fin n => (σ ^ i.succ.val) c) := by
    unfold finiteRotationScan
    rw [← hn, List.ofFn_succ]
    simp [σ]
  have hfilter : finiteOutgoingRotationOrder B c =
      c :: (List.ofFn (fun i : Fin n => (σ ^ i.succ.val) c)).filter
        (fun d => dartTailVertex B.map d = dartTailVertex B.map c ∧ B.map.tail d) := by
    unfold finiteOutgoingRotationOrder
    rw [hscan, List.filter_cons]
    simp [c, canonicalLeftmostOutgoing_spec]
  refine ⟨((List.ofFn (fun i : Fin n => (σ ^ i.succ.val) c)).filter
      (fun d => dartTailVertex B.map d = dartTailVertex B.map c ∧ B.map.tail d)).filter
        (fun d => !d == c) |>.eraseDups,
    ?_⟩
  rw [canonicalOutgoingOrder, hfilter, List.eraseDups_cons]

/-- The head of canonical outgoing order is `leftmostOutgoing`. Helper
toward `lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem canonicalOutgoingOrder_head?
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) :
    (canonicalOutgoingOrder B v hvs).head? =
      some (leftmostOutgoing B v hvs) := by
  obtain ⟨rest, hcons⟩ := canonicalOutgoingOrder_cons B v hvs
  simp [hcons]

/-- At the source, the canonical outgoing order starts with the first
left-boundary dart. Helper toward `lem-lr-ind` (leftmost XDP geodesic); not -/
theorem canonicalOutgoingOrder_source_head
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) :
    (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).head? =
      some (B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)) := by
  rw [canonicalOutgoingOrder_head?, leftmostOutgoing_source_eq_firstLeftDart]

/-- The sublist of canonical outgoing order consisting of darts on XDP
geodesics. Helper toward `lem-lr-ind` (leftmost XDP geodesic); not the paper -/
@[expose] noncomputable def canonicalXDPGeodesicDartOrder
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) (hvs : v ≠ B.sink) : List D := by
  classical
  exact (canonicalOutgoingOrder B v hvs).filter
    (fun d => decide (IsXDPGeodesicDart B x d))

/-- Choose the first dart in canonical outgoing order that lies on an XDP
geodesic. The fallback values only define the total function off the
geodesic vertex set. Helper toward `lem-lr-ind` (leftmost XDP geodesic); not -/
@[expose] noncomputable def canonicalLeftmostXDPStep
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map) : D := by
  classical
  exact if hvs : v ≠ B.sink then
    match canonicalXDPGeodesicDartOrder B x v hvs with
    | [] => leftmostOutgoing B v hvs
    | d :: _ => d
  else finiteXDPLeftmostCorner B v

/-- At a non-sink vertex on an XDP geodesic, the canonical step is outgoing
and itself lies on an XDP geodesic. Helper toward `lem-lr-ind` (leftmost XDP
343–348`). -/
theorem canonicalLeftmostXDPStep_spec
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink) :
    dartTailVertex B.map (canonicalLeftmostXDPStep B x v) = v ∧
      IsXDPGeodesicDart B x (canonicalLeftmostXDPStep B x v) := by
  classical
  obtain ⟨d, htail, hgeo⟩ := exists_outgoingXDPGeodesicDart_of_geodesic_vertex
    B x hv hvs
  let candidates := canonicalXDPGeodesicDartOrder B x v hvs
  have hmem : d ∈ candidates := by
    change d ∈
      (canonicalOutgoingOrder B v hvs).filter
        (fun e => decide (IsXDPGeodesicDart B x e))
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply (mem_canonicalOutgoingOrder_iff B v hvs d).2
      exact ⟨htail, (IsXDPGeodesicDart.present_tail B x d hgeo).2⟩
    · exact decide_eq_true hgeo
  have hne : candidates ≠ [] := List.ne_nil_of_mem hmem
  have hselected : canonicalLeftmostXDPStep B x v ∈ candidates := by
    simp only [canonicalLeftmostXDPStep]
    dsimp [candidates]
    cases hc : canonicalXDPGeodesicDartOrder B x v hvs with
    | nil => exact (hne hc).elim
    | cons e es => simp [hvs, hc]
  have hselected' : canonicalLeftmostXDPStep B x v ∈
      canonicalXDPGeodesicDartOrder B x v hvs := hselected
  have hspec := List.mem_filter.mp (by
    simpa only [canonicalXDPGeodesicDartOrder] using hselected')
  exact ⟨(mem_canonicalOutgoingOrder_iff B v hvs _).mp hspec.1 |>.1,
    of_decide_eq_true hspec.2⟩

/-- In the admissible sublist, the canonical step is first; every other
outgoing dart lying on an XDP geodesic occurs in the remaining suffix.
This also characterizes the step independently of any choice of definition
that selects the first admissible dart in this order. Helper toward
`lem-lr-ind` (leftmost XDP geodesic); not the paper result -/
theorem canonicalLeftmostXDPStep_first
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink) :
    ∃ rest,
      canonicalXDPGeodesicDartOrder B x v hvs =
          canonicalLeftmostXDPStep B x v :: rest ∧
      ∀ d, dartTailVertex B.map d = v → IsXDPGeodesicDart B x d →
        d = canonicalLeftmostXDPStep B x v ∨ d ∈ rest := by
  classical
  let candidates := canonicalXDPGeodesicDartOrder B x v hvs
  obtain ⟨hvertex, hgeo⟩ := canonicalLeftmostXDPStep_spec B x v hv hvs
  have hmem : canonicalLeftmostXDPStep B x v ∈ candidates := by
    change canonicalLeftmostXDPStep B x v ∈ (canonicalOutgoingOrder B v hvs).filter
      (fun e => decide (IsXDPGeodesicDart B x e))
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true hgeo⟩
    exact (mem_canonicalOutgoingOrder_iff B v hvs _).2
      ⟨hvertex, (IsXDPGeodesicDart.present_tail B x _ hgeo).2⟩
  have hne : candidates ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨rest, hcons⟩ : ∃ rest, candidates =
      canonicalLeftmostXDPStep B x v :: rest := by
    cases hc : candidates with
    | nil => exact (hne hc).elim
    | cons e es =>
        change (canonicalOutgoingOrder B v hvs).filter
          (fun d => decide (IsXDPGeodesicDart B x d)) = e :: es at hc
        have heq : e = canonicalLeftmostXDPStep B x v := by
          simp [canonicalLeftmostXDPStep, canonicalXDPGeodesicDartOrder,
            hvs, hc]
        subst e
        exact ⟨es, rfl⟩
  refine ⟨rest, ?_, ?_⟩
  · exact hcons
  · intro d htail hgeoDart
    have hmemD : d ∈ candidates := by
      change d ∈ (canonicalOutgoingOrder B v hvs).filter
        (fun e => decide (IsXDPGeodesicDart B x e))
      apply List.mem_filter.mpr
      refine ⟨?_, decide_eq_true hgeoDart⟩
      exact (mem_canonicalOutgoingOrder_iff B v hvs d).2
        ⟨htail, (IsXDPGeodesicDart.present_tail B x d hgeoDart).2⟩
    rw [hcons] at hmemD
    exact List.mem_cons.mp hmemD

/-- Any definition whose value is the head of the same admissible sublist
agrees with the canonical XDP step. This is the order-based
choice-independence statement. Helper toward `lem-lr-ind` (leftmost XDP
343–348`). -/
theorem canonicalLeftmostXDPStep_eq_of_admissible_order
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    (v : MapVertex B.map)
    (hv : ∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices)
    (hvs : v ≠ B.sink)
    (d : D) (rest : List D)
    (horder : canonicalXDPGeodesicDartOrder B x v hvs = d :: rest) :
    d = canonicalLeftmostXDPStep B x v := by
  obtain ⟨rest', hfirst, _⟩ := canonicalLeftmostXDPStep_first B x v hv hvs
  have hheads := congrArg List.head? (hfirst.symm.trans horder)
  simp only [List.head?_cons] at hheads
  exact (Option.some.inj hheads).symm

/-- The canonical greedy selector yields an XDP geodesic of the base XDP
length, and its dart at every step is first among the admissible outgoing
darts in canonical rotation order. Helper toward `lem-lr-ind` (leftmost XDP
343–348`). -/
theorem exists_canonicalLeftmost_XDPGeodesic_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
      IsXDPGeodesicBase B x P ∧
        (∀ i : Fin (xdpLengthBase B x),
          P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩ =
            canonicalLeftmostXDPStep B x
              (selectorVertex B (canonicalLeftmostXDPStep B x) i.val)) ∧
        (∀ i : Fin (xdpLengthBase B x),
          ∃ hvs : selectorVertex B (canonicalLeftmostXDPStep B x) i.val ≠ B.sink,
          ∃ rest,
            canonicalXDPGeodesicDartOrder B x
                (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) hvs =
              canonicalLeftmostXDPStep B x
                  (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) :: rest ∧
            ∀ d,
              dartTailVertex B.map d =
                selectorVertex B (canonicalLeftmostXDPStep B x) i.val →
              IsXDPGeodesicDart B x d →
              d = canonicalLeftmostXDPStep B x
                    (selectorVertex B (canonicalLeftmostXDPStep B x) i.val) ∨
                d ∈ rest) := by
  classical
  let sel : MapVertex B.map → D := canonicalLeftmostXDPStep B x
  have hsel : ∀ v, (∃ n, ∃ P : SimpleDirectedDartPath B.map B.source B.sink n,
      IsXDPGeodesicBase B x P ∧ v ∈ P.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v) := by
    intro v hv hvs
    exact canonicalLeftmostXDPStep_spec B x v hv hvs
  obtain ⟨P, hgeo, hpath⟩ := exists_selector_XDPGeodesic_path B x sel hsel
  refine ⟨P, hgeo, ?_, ?_⟩
  · intro i
    simpa [sel] using hpath i
  · intro i
    have hvertex := selectorVertex_mem_XDPGeodesic B x sel hsel i.val
    have hnot := selectorVertex_ne_sink_of_lt_length B x sel hsel i.val i.isLt
    obtain ⟨rest, hfirst, hlocal⟩ := canonicalLeftmostXDPStep_first B x
      (selectorVertex B sel i.val) hvertex hnot
    exact ⟨hnot, rest, by simpa only [sel] using hfirst,
      by simpa only [sel] using hlocal⟩

end DirectedDistances.PlanarMap
