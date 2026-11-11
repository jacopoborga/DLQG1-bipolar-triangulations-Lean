module

public import DirectedDistances.PaperProofs.Section4.ThinSideIsoAssembly

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Intrinsic directed paths in the marked finite ancestor maps. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence x T hT q
local notation "HL" q => sourceAncestor_left_nonneg x T hT q
local notation "HT" q => sourceAncestor_left_transient x T hT q
local notation "HR" q => sourceAncestor_right_unbounded x T hT q
local notation "P" q => sourceAncestorPath x T hT q

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
def GeometricAncestorMarkedIso.symm
    {a : ThinMapSide} {s : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a s q q') :
    GeometricAncestorMarkedIso x T hT a s q' q where
  equiv := I.equiv.symm
  relation_iff tag u v := by
    simpa only [Equiv.apply_symm_apply] using
      (I.relation_iff tag (I.equiv.symm u) (I.equiv.symm v)).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A directed step expressed solely by the marked relations. -/
@[expose] def geometricAncestorCellStep
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u v : GeometricAncestorCell x T hT a s q) : Prop :=
  ∃ d e, geometricAncestorRelation x T hT a s q .oriented d d ∧
    geometricAncestorRelation x T hT a s q .opposite d e ∧
    geometricAncestorRelation x T hT a s q .incident d u ∧
    geometricAncestorRelation x T hT a s q .incident e v

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Marked isomorphisms preserve intrinsic directed steps. -/
theorem GeometricAncestorMarkedIso.cellStep_iff
    {a : ThinMapSide} {s : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a s q q')
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorCellStep x T hT a s q u v ↔
      geometricAncestorCellStep x T hT a s q' (I.equiv u) (I.equiv v) := by
  constructor
  · rintro ⟨d, e, ho, hp, hu, hv⟩
    exact ⟨I.equiv d, I.equiv e, (I.relation_iff _ _ _).mp ho,
      (I.relation_iff _ _ _).mp hp, (I.relation_iff _ _ _).mp hu,
      (I.relation_iff _ _ _).mp hv⟩
  · rintro ⟨d, e, ho, hp, hu, hv⟩
    obtain ⟨d, rfl⟩ := I.equiv.surjective d
    obtain ⟨e, rfl⟩ := I.equiv.surjective e
    exact ⟨d, e, (I.relation_iff _ _ _).mpr ho,
      (I.relation_iff _ _ _).mpr hp, (I.relation_iff _ _ _).mpr hu,
      (I.relation_iff _ _ _).mpr hv⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Marked isomorphisms preserve finite directed reachability. -/
theorem GeometricAncestorMarkedIso.reachable_iff
    {a : ThinMapSide} {s : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a s q q')
    (u v : GeometricAncestorCell x T hT a s q) :
    Relation.ReflTransGen (geometricAncestorCellStep x T hT a s q) u v ↔
      Relation.ReflTransGen (geometricAncestorCellStep x T hT a s q')
        (I.equiv u) (I.equiv v) := by
  constructor
  · exact Relation.ReflTransGen.lift I.equiv
      (fun u v h => (I.cellStep_iff x T hT u v).mp h) u v
  · intro h
    have hh := Relation.ReflTransGen.lift I.equiv.symm
      (fun u v h => ((I.symm x T hT).cellStep_iff x T hT u v).mp h)
      _ _ h
    change Relation.ReflTransGen (geometricAncestorCellStep x T hT a s q)
      (I.equiv.symm (I.equiv u)) (I.equiv.symm (I.equiv v)) at hh
    simpa only [Equiv.symm_apply_apply] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Intrinsic steps between vertices are exactly present retained geometric edges. -/
theorem geometricAncestorCellStep_vertices_iff
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u v : geometricAncestorVertices x T hT a q s) :
    geometricAncestorCellStep x T hT a s q (.inl u) (.inl v) ↔
      ∃ e ∈ geometricAncestorEdges x T hT a q s,
        EdgePresent (W q) e ∧ edgeWest (W q) e = u.1 ∧ edgeEast (W q) e = v.1 := by
  constructor
  · rintro ⟨d, e, ho, hp, hu, hv⟩
    cases d with
    | inl d => exact False.elim ho
    | inr d =>
      cases e with
      | inl e => exact False.elim hp
      | inr e =>
        change EdgePresent (W q) d.1.1 ∧ d.1.2 = false at ho
        change (d.1.1, !d.1.2) = e.1 at hp
        change (if d.1.2 then edgeEast (W q) d.1.1 else edgeWest (W q) d.1.1) =
          u.1 at hu
        change (if e.1.2 then edgeEast (W q) e.1.1 else edgeWest (W q) e.1.1) =
          v.1 at hv
        rw [ho.2] at hp hu
        have he : e.1 = (d.1.1, true) := hp.symm
        rw [he] at hv
        exact ⟨d.1.1, d.2, ho.1, hu, hv⟩
  · rintro ⟨e, he, hp, hu, hv⟩
    exact ⟨.inr ⟨(e, false), he⟩, .inr ⟨(e, true), he⟩,
      ⟨hp, rfl⟩, rfl, hu, hv⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The earlier target is definable using root or indexed boundary incidence. -/
@[expose] def geometricAncestorEarlierTarget
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT) :
    ℕ → GeometricAncestorCell x T hT a t q → Prop
  | 0, u => geometricAncestorRelation x T hT a t q .root u u
  | i + 1, u => ∃ d e,
      geometricAncestorRelation x T hT a t q (.boundary i) d d ∧
      geometricAncestorRelation x T hT a t q .opposite d e ∧
      geometricAncestorRelation x T hT a t q .incident e u

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Marked isomorphisms preserve every earlier indexed target. -/
theorem GeometricAncestorMarkedIso.earlierTarget_iff
    {a : ThinMapSide} {t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q')
    (s : ℕ) (u : GeometricAncestorCell x T hT a t q) :
    geometricAncestorEarlierTarget x T hT a t q s u ↔
      geometricAncestorEarlierTarget x T hT a t q' s (I.equiv u) := by
  cases s with
  | zero => exact I.relation_iff .root u u
  | succ i =>
    constructor
    · rintro ⟨d, e, hb, ho, hi⟩
      exact ⟨I.equiv d, I.equiv e, (I.relation_iff _ _ _).mp hb,
        (I.relation_iff _ _ _).mp ho, (I.relation_iff _ _ _).mp hi⟩
    · rintro ⟨d, e, hb, ho, hi⟩
      obtain ⟨d, rfl⟩ := I.equiv.surjective d
      obtain ⟨e, rfl⟩ := I.equiv.surjective e
      exact ⟨d, e, (I.relation_iff _ _ _).mpr hb,
        (I.relation_iff _ _ _).mpr ho, (I.relation_iff _ _ _).mpr hi⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The intrinsic earlier target agrees with the permanent boundary vertex. -/
theorem geometricAncestorEarlierTarget_vertex_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : geometricAncestorVertices x T hT a q t) :
    geometricAncestorEarlierTarget x T hT a t q s (.inl u) ↔
      u.1 = thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) a s := by
  cases s with
  | zero => rfl
  | succ i =>
    let b := thinMapBoundaryDart (W q) (HF q) (HL q) (HT q) (HR q) a i
    have hb : b.2 = false := by cases a <;> rfl
    constructor
    · rintro ⟨d, e, hd, ho, hi⟩
      cases d with
      | inl d => exact False.elim hd
      | inr d =>
        cases e with
        | inl e => exact False.elim ho
        | inr e =>
          change b = d.1 at hd
          change (d.1.1, !d.1.2) = e.1 at ho
          change (if e.1.2 then edgeEast (W q) e.1.1 else edgeWest (W q) e.1.1) =
            u.1 at hi
          rw [← hd, hb] at ho
          rw [← ho] at hi
          exact hi.symm
    · intro hu
      have hbe : b.1 ∈ geometricAncestorEdges x T hT a q t :=
        geometricAncestorEdges_mono x T hT a q hst
          (thinMapBoundaryDart_mem_sourceAncestorEdges
            (W q) (HF q) (HL q) (HT q) (HR q) (P q) a i)
      refine ⟨.inr ⟨b, hbe⟩, .inr ⟨(b.1, true), hbe⟩, rfl, ?_, ?_⟩
      · change (b.1, !b.2) = (b.1, true)
        rw [hb]
        rfl
      · exact hu.symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A dart cannot be an earlier target. -/
theorem geometricAncestorEarlierTarget_dart_false
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    (s : ℕ) (u : sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a t) :
    ¬ geometricAncestorEarlierTarget x T hT a t q s (.inr u) := by
  cases s with
  | zero => exact id
  | succ i =>
    rintro ⟨d, e, _, _, hi⟩
    cases e <;> exact hi

private theorem cellStep_not_dart_left
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u : sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s)
    (v : GeometricAncestorCell x T hT a s q) :
    ¬ geometricAncestorCellStep x T hT a s q (.inr u) v := by
  rintro ⟨d, e, _, _, hi, _⟩
  cases d <;> exact hi

private theorem cellStep_not_dart_right
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u : GeometricAncestorCell x T hT a s q)
    (v : sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s) :
    ¬ geometricAncestorCellStep x T hT a s q u (.inr v) := by
  rintro ⟨d, e, _, _, _, hi⟩
  cases e <;> exact hi

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The present-edge relation at a finite ancestor level. -/
@[expose] def geometricAncestorVertexStep
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u v : ℕ) : Prop :=
  ∃ e ∈ geometricAncestorEdges x T hT a q t,
    EdgePresent (W q) e ∧ edgeWest (W q) e = u ∧ edgeEast (W q) e = v

private theorem vertexPath_to_cell
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    {u v : ℕ} (hu : u ∈ geometricAncestorVertices x T hT a q t)
    (hv : v ∈ geometricAncestorVertices x T hT a q t)
    (hpath : Relation.ReflTransGen (geometricAncestorVertexStep x T hT a t q) u v) :
    Relation.ReflTransGen (geometricAncestorCellStep x T hT a t q)
      (.inl ⟨u, hu⟩) (.inl ⟨v, hv⟩) := by
  induction hpath generalizing hu with
  | refl => exact .refl
  | @tail b c h hbc ih =>
    obtain ⟨e, he, hp, hw, hz⟩ := hbc
    have hb : b ∈ geometricAncestorVertices x T hT a q t := hw ▸ he.2.1
    exact (ih hu hb).tail
      ((geometricAncestorCellStep_vertices_iff x T hT a t q ⟨b, hb⟩ ⟨c, hv⟩).mpr
        ⟨e, he, hp, hw, hz⟩)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Cell reachability between vertices is precisely geometric directed reachability. -/
theorem geometricAncestorCell_reachable_vertices_iff
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    (u v : geometricAncestorVertices x T hT a q t) :
    Relation.ReflTransGen (geometricAncestorCellStep x T hT a t q) (.inl u) (.inl v) ↔
      Relation.ReflTransGen (geometricAncestorVertexStep x T hT a t q) u.1 v.1 := by
  constructor
  · intro h
    let f : GeometricAncestorCell x T hT a t q → ℕ :=
      Sum.elim Subtype.val (fun _ => 0)
    have hh := Relation.ReflTransGen.lift
      (p := geometricAncestorVertexStep x T hT a t q) f (fun z z' hz => ?_) _ _ h
    · exact hh
    cases z with
    | inr z => exact (cellStep_not_dart_left x T hT a t q z z' hz).elim
    | inl z =>
      cases z' with
      | inr z' => exact (cellStep_not_dart_right x T hT a t q (.inl z) z' hz).elim
      | inl z' => exact (geometricAncestorCellStep_vertices_iff x T hT a t q z z').mp hz
  · exact vertexPath_to_cell x T hT a t q u.2 v.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Earlier ancestor vertices are intrinsically recognizable inside the later marked map. -/
theorem geometricAncestorVertices_iff_intrinsic
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : geometricAncestorVertices x T hT a q t) :
    u.1 ∈ geometricAncestorVertices x T hT a q s ↔
      ∃ z, geometricAncestorEarlierTarget x T hT a t q s z ∧
        Relation.ReflTransGen (geometricAncestorCellStep x T hT a t q) (.inl u) z := by
  constructor
  · intro hu
    let b := thinMapBoundaryVertex (W q) (HF q) (HL q) (HT q) (HR q) a s
    have hb : b ∈ geometricAncestorVertices x T hT a q t :=
      geometricAncestorVertices_mono x T hT a q hst
        (thinMapBoundaryVertex_mem_sourceAncestorVertices
          (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s)
    refine ⟨.inl ⟨b, hb⟩,
      (geometricAncestorEarlierTarget_vertex_iff x T hT a q hst ⟨b, hb⟩).mpr rfl, ?_⟩
    apply (geometricAncestorCell_reachable_vertices_iff x T hT a t q u ⟨b, hb⟩).mpr
    exact ((geometricAncestorVertices_iff_later_reachable x T hT a q hst u.1).mp hu).2
  · rintro ⟨z, hz, hp⟩
    cases z with
    | inr z => exact (geometricAncestorEarlierTarget_dart_false x T hT a t q s z hz).elim
    | inl z =>
      have he := (geometricAncestorEarlierTarget_vertex_iff x T hT a q hst z).mp hz
      have hh := (geometricAncestorCell_reachable_vertices_iff x T hT a t q u z).mp hp
      apply (geometricAncestorVertices_iff_later_reachable x T hT a q hst u.1).mpr
      exact ⟨u.2, he ▸ hh⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The intrinsic earlier-ancestor predicate on the cell carrier. -/
@[expose] def geometricAncestorIntrinsicVertex
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    (s : ℕ) (u : GeometricAncestorCell x T hT a t q) : Prop :=
  geometricAncestorRelation x T hT a t q .vertex u u ∧
    ∃ z, geometricAncestorEarlierTarget x T hT a t q s z ∧
      Relation.ReflTransGen (geometricAncestorCellStep x T hT a t q) u z

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Marked isomorphisms preserve the intrinsically defined earlier vertex carrier. -/
theorem GeometricAncestorMarkedIso.intrinsicVertex_iff
    {a : ThinMapSide} {t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q')
    (s : ℕ) (u : GeometricAncestorCell x T hT a t q) :
    geometricAncestorIntrinsicVertex x T hT a t q s u ↔
      geometricAncestorIntrinsicVertex x T hT a t q' s (I.equiv u) := by
  constructor
  · rintro ⟨hu, z, hz, hp⟩
    exact ⟨(I.relation_iff _ _ _).mp hu, I.equiv z,
      (I.earlierTarget_iff x T hT s z).mp hz, (I.reachable_iff x T hT u z).mp hp⟩
  · rintro ⟨hu, z, hz, hp⟩
    obtain ⟨z, rfl⟩ := I.equiv.surjective z
    exact ⟨(I.relation_iff _ _ _).mpr hu, z,
      (I.earlierTarget_iff x T hT s z).mpr hz, (I.reachable_iff x T hT u z).mpr hp⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
On vertices the intrinsic predicate is earlier ancestor membership. -/
theorem geometricAncestorIntrinsicVertex_inl_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : geometricAncestorVertices x T hT a q t) :
    geometricAncestorIntrinsicVertex x T hT a t q s (.inl u) ↔
      u.1 ∈ geometricAncestorVertices x T hT a q s := by
  exact and_iff_right True.intro |>.trans
    (geometricAncestorVertices_iff_intrinsic x T hT a q hst u).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Intrinsic earlier cells include darts exactly when both endpoints are earlier vertices.
No edge-presence condition is imposed. -/
@[expose] def geometricAncestorIntrinsicCell
    (a : ThinMapSide) (t : ℕ) (q : selectedCutCoherentDomain x T hT)
    (s : ℕ) (u : GeometricAncestorCell x T hT a t q) : Prop :=
  geometricAncestorIntrinsicVertex x T hT a t q s u ∨
    ∃ d v z, geometricAncestorRelation x T hT a t q .opposite u d ∧
      geometricAncestorRelation x T hT a t q .incident u v ∧
      geometricAncestorRelation x T hT a t q .incident d z ∧
      geometricAncestorIntrinsicVertex x T hT a t q s v ∧
      geometricAncestorIntrinsicVertex x T hT a t q s z

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Marked isomorphisms preserve the intrinsic earlier vertex-and-dart carrier. -/
theorem GeometricAncestorMarkedIso.intrinsicCell_iff
    {a : ThinMapSide} {t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q')
    (s : ℕ) (u : GeometricAncestorCell x T hT a t q) :
    geometricAncestorIntrinsicCell x T hT a t q s u ↔
      geometricAncestorIntrinsicCell x T hT a t q' s (I.equiv u) := by
  constructor
  · rintro (h | ⟨d, v, z, hd, hv, hz, hv', hz'⟩)
    · exact Or.inl ((I.intrinsicVertex_iff x T hT s u).mp h)
    · exact Or.inr ⟨I.equiv d, I.equiv v, I.equiv z,
        (I.relation_iff _ _ _).mp hd, (I.relation_iff _ _ _).mp hv,
        (I.relation_iff _ _ _).mp hz, (I.intrinsicVertex_iff x T hT s v).mp hv',
        (I.intrinsicVertex_iff x T hT s z).mp hz'⟩
  · rintro (h | ⟨d, v, z, hd, hv, hz, hv', hz'⟩)
    · exact Or.inl ((I.intrinsicVertex_iff x T hT s u).mpr h)
    · obtain ⟨d, rfl⟩ := I.equiv.surjective d
      obtain ⟨v, rfl⟩ := I.equiv.surjective v
      obtain ⟨z, rfl⟩ := I.equiv.surjective z
      exact Or.inr ⟨d, v, z, (I.relation_iff _ _ _).mpr hd,
        (I.relation_iff _ _ _).mpr hv, (I.relation_iff _ _ _).mpr hz,
        (I.intrinsicVertex_iff x T hT s v).mpr hv',
        (I.intrinsicVertex_iff x T hT s z).mpr hz'⟩

private theorem intrinsicCell_vertex_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : geometricAncestorVertices x T hT a q t) :
    geometricAncestorIntrinsicCell x T hT a t q s (.inl u) ↔
      u.1 ∈ geometricAncestorVertices x T hT a q s := by
  constructor
  · rintro (h | ⟨d, _, _, hd, _⟩)
    · exact (geometricAncestorIntrinsicVertex_inl_iff x T hT a q hst u).mp h
    · cases d <;> exact hd.elim
  · intro h
    exact Or.inl ((geometricAncestorIntrinsicVertex_inl_iff x T hT a q hst u).mpr h)

private theorem intrinsicCell_dart_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t)
    (u : sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a t) :
    geometricAncestorIntrinsicCell x T hT a t q s (.inr u) ↔
      u.1.1 ∈ geometricAncestorEdges x T hT a q s := by
  constructor
  · rintro (h | ⟨d, v, z, hd, hv, hz, hv', hz'⟩)
    · exact h.1.elim
    · cases d with
      | inl d => exact hd.elim
      | inr d =>
        cases v with
        | inr v => exact hv.elim
        | inl v =>
          cases z with
          | inr z => exact hz.elim
          | inl z =>
            have hvlo := (geometricAncestorIntrinsicVertex_inl_iff
              x T hT a q hst v).mp hv'
            have hzlo := (geometricAncestorIntrinsicVertex_inl_iff
              x T hT a q hst z).mp hz'
            change (u.1.1, !u.1.2) = d.1 at hd
            change (if u.1.2 then edgeEast (W q) u.1.1 else edgeWest (W q) u.1.1) =
              v.1 at hv
            change (if d.1.2 then edgeEast (W q) d.1.1 else edgeWest (W q) d.1.1) =
              z.1 at hz
            rw [← hd] at hz
            refine ⟨u.2.1, ?_, ?_⟩
            · cases hb : u.1.2
              · simp [hb] at hv
                exact hv.symm ▸ hvlo
              · simp [hb] at hz
                exact hz.symm ▸ hzlo
            · cases hb : u.1.2
              · simp [hb] at hz
                exact hz.symm ▸ hzlo
              · simp [hb] at hv
                exact hv.symm ▸ hvlo
  · intro hu
    let v : geometricAncestorVertices x T hT a q t :=
      ⟨if u.1.2 then edgeEast (W q) u.1.1 else edgeWest (W q) u.1.1,
        by split
           · exact u.2.2.2
           · exact u.2.2.1⟩
    let z : geometricAncestorVertices x T hT a q t :=
      ⟨if u.1.2 then edgeWest (W q) u.1.1 else edgeEast (W q) u.1.1,
        by split
           · exact u.2.2.1
           · exact u.2.2.2⟩
    refine Or.inr ⟨.inr ⟨(u.1.1, !u.1.2), u.2⟩, .inl v, .inl z,
      rfl, rfl, ?_, ?_, ?_⟩
    · change (if !u.1.2 then edgeEast (W q) u.1.1 else edgeWest (W q) u.1.1) = z.1
      dsimp only [z]
      cases u.1.2 <;> rfl
    · apply (geometricAncestorIntrinsicVertex_inl_iff x T hT a q hst v).mpr
      dsimp only [v]
      split
      · exact hu.2.2
      · exact hu.2.1
    · apply (geometricAncestorIntrinsicVertex_inl_iff x T hT a q hst z).mpr
      dsimp only [z]
      split
      · exact hu.2.1
      · exact hu.2.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The earlier cell carrier is exactly the intrinsic subset of the later marked map. -/
theorem geometricAncestorIntrinsicCell_iff_range
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u : GeometricAncestorCell x T hT a t q) :
    geometricAncestorIntrinsicCell x T hT a t q s u ↔
      ∃ v, geometricAncestorInclusion x T hT a q hst v = u := by
  cases u with
  | inl u =>
    rw [intrinsicCell_vertex_iff x T hT a q hst u]
    constructor
    · intro h
      exact ⟨.inl ⟨u.1, h⟩, rfl⟩
    · rintro ⟨v, hv⟩
      cases v with
      | inl v => exact (Sum.inl.inj hv) ▸ v.2
      | inr v => cases hv
  | inr u =>
    rw [intrinsicCell_dart_iff x T hT a q hst u]
    constructor
    · intro h
      exact ⟨.inr ⟨u.1, h⟩, rfl⟩
    · rintro ⟨v, hv⟩
      cases v with
      | inl v => cases hv
      | inr v => exact (Sum.inr.inj hv) ▸ v.2

private noncomputable def ancestorIntrinsicEquiv
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) :
    GeometricAncestorCell x T hT a s q ≃
      {u : GeometricAncestorCell x T hT a t q //
        geometricAncestorIntrinsicCell x T hT a t q s u} :=
  Equiv.ofBijective
    (fun u => ⟨geometricAncestorInclusion x T hT a q hst u,
      (geometricAncestorIntrinsicCell_iff_range x T hT a q hst _).mpr ⟨u, rfl⟩⟩)
    ⟨fun _ _ h => geometricAncestorInclusion_injective x T hT a q hst
      (congrArg Subtype.val h), by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := (geometricAncestorIntrinsicCell_iff_range x T hT a q hst u).mp hu
      exact ⟨v, Subtype.ext hv⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical restriction of the cell bijection to an earlier ancestor carrier.
Preservation of rotation and retained faces is a separate obligation. -/
noncomputable def GeometricAncestorMarkedIso.restrictEquiv
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t) :
    GeometricAncestorCell x T hT a s q ≃ GeometricAncestorCell x T hT a s q' :=
  (ancestorIntrinsicEquiv x T hT a q hst).trans
    ((I.equiv.subtypeEquiv (I.intrinsicCell_iff x T hT s)).trans
      (ancestorIntrinsicEquiv x T hT a q' hst).symm)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical restricted bijection commutes with permanent-ID inclusion. -/
theorem GeometricAncestorMarkedIso.restrictEquiv_commutes
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t)
    (u : GeometricAncestorCell x T hT a s q) :
    I.equiv (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q' hst ((I.restrictEquiv x T hT hst) u) := by
  exact (congrArg Subtype.val ((ancestorIntrinsicEquiv x T hT a q' hst).apply_symm_apply
    ((I.equiv.subtypeEquiv (I.intrinsicCell_iff x T hT s))
      (ancestorIntrinsicEquiv x T hT a q hst u)))).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All unchanged relations are induced by permanent-ID inclusion. -/
theorem geometricAncestorInclusion_relation_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (tag : TruncationRelation)
    (hr : tag ≠ .rotation) (hf : tag ≠ .faceNext) (ht : tag ≠ .target)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q tag u v ↔
      geometricAncestorRelation x T hT a t q tag
        (geometricAncestorInclusion x T hT a q hst u)
        (geometricAncestorInclusion x T hT a q hst v) := by
  cases tag <;> cases u <;> cases v
  all_goals first | exact (hr rfl).elim | exact (hf rfl).elim | exact (ht rfl).elim | rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The restricted cell bijection preserves every relation except the finite target,
rotation and retained-face succession. -/
theorem GeometricAncestorMarkedIso.restrictEquiv_basic_relation_iff
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t)
    (tag : TruncationRelation)
    (hr : tag ≠ .rotation) (hf : tag ≠ .faceNext) (ht : tag ≠ .target)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q tag u v ↔
      geometricAncestorRelation x T hT a s q' tag
        ((I.restrictEquiv x T hT hst) u) ((I.restrictEquiv x T hT hst) v) := by
  rw [geometricAncestorInclusion_relation_iff x T hT a q hst tag hr hf ht,
    geometricAncestorInclusion_relation_iff x T hT a q' hst tag hr hf ht,
    I.relation_iff, I.restrictEquiv_commutes, I.restrictEquiv_commutes]

private theorem target_iff_earlierTarget
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .target u v ↔
      geometricAncestorEarlierTarget x T hT a t q s
        (geometricAncestorInclusion x T hT a q hst u) := by
  cases u with
  | inl u => exact (geometricAncestorEarlierTarget_vertex_iff
      x T hT a q hst ⟨u.1, geometricAncestorVertices_mono x T hT a q hst u.2⟩).symm
  | inr u =>
    constructor
    · exact False.elim
    · intro h
      exact geometricAncestorEarlierTarget_dart_false x T hT a t q s
        ⟨u.1, geometricAncestorEdges_mono x T hT a q hst u.2⟩ h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The restricted bijection preserves the earlier finite target marking. -/
theorem GeometricAncestorMarkedIso.restrictEquiv_target_iff
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .target u v ↔
      geometricAncestorRelation x T hT a s q' .target
        ((I.restrictEquiv x T hT hst) u) ((I.restrictEquiv x T hT hst) v) := by
  rw [target_iff_earlierTarget x T hT a q hst u v,
    target_iff_earlierTarget x T hT a q' hst]
  rw [← I.restrictEquiv_commutes]
  exact I.earlierTarget_iff x T hT s _

private theorem triangle_successors
    (q : selectedCutCoherentDomain x T hT) (j : TriangleCreationTime (W q))
    (d : ℕ × Bool) (hd : d ∈ stageTriangleDartList (W q) j) :
    kmswInfFaceSucc (W q) (HF q) d ∈ stageTriangleDartList (W q) j ∧
      kmswInfFaceSucc (W q) (HF q) (kmswInfFaceSucc (W q) (HF q) d) ∈
        stageTriangleDartList (W q) j ∧
      ∀ z ∈ stageTriangleDartList (W q) j,
        z = d ∨ z = kmswInfFaceSucc (W q) (HF q) d ∨
          z = kmswInfFaceSucc (W q) (HF q) (kmswInfFaceSucc (W q) (HF q) d) := by
  have hc := kmswInfFaceSucc_stageTriangle_cycle (W q) (HF q) j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl
  all_goals simp only [hc.1, hc.2.1, hc.2.2.1]
  all_goals tauto

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Retained triangular face succession is intrinsically recognized in a later map
by two successive retained-face steps whose three darts belong to the earlier carrier. -/
theorem geometricAncestorInclusion_faceNext_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .faceNext u v ↔
      ∃ z : GeometricAncestorCell x T hT a s q,
        geometricAncestorRelation x T hT a t q .faceNext
          (geometricAncestorInclusion x T hT a q hst u)
          (geometricAncestorInclusion x T hT a q hst v) ∧
        geometricAncestorRelation x T hT a t q .faceNext
          (geometricAncestorInclusion x T hT a q hst v)
          (geometricAncestorInclusion x T hT a q hst z) := by
  cases u with
  | inl u =>
    constructor
    · exact False.elim
    · rintro ⟨z, h, _⟩
      cases v <;> exact h
  | inr u =>
    cases v with
    | inl v =>
      constructor
      · exact False.elim
      · rintro ⟨z, h, _⟩
        exact h
    | inr v =>
      constructor
      · rintro ⟨⟨j, hu, hall⟩, he⟩
        obtain ⟨hv, hz, _⟩ := triangle_successors x T hT q j u.1 hu
        let z := kmswInfFaceSucc (W q) (HF q) v.1
        have hzmem : z ∈ stageTriangleDartList (W q) j := by
          dsimp only [z]
          rw [← he]
          exact hz
        have hupper : ∀ d ∈ stageTriangleDartList (W q) j,
            d.1 ∈ geometricAncestorEdges x T hT a q t :=
          fun d hd => geometricAncestorEdges_mono x T hT a q hst (hall d hd)
        refine ⟨.inr ⟨z, hall z hzmem⟩, ⟨⟨j, hu, hupper⟩, he⟩, ?_⟩
        exact ⟨⟨j, he ▸ hv, hupper⟩, rfl⟩
      · rintro ⟨z, ⟨⟨j, hu, _⟩, he⟩, hnext⟩
        cases z with
        | inl z => exact hnext.elim
        | inr z =>
          have hz := hnext.2
          refine ⟨⟨j, hu, ?_⟩, he⟩
          intro d hd
          rcases (triangle_successors x T hT q j u.1 hu).2.2 d hd with hd | hd | hd
          · exact hd ▸ u.2
          · exact (hd.trans he) ▸ v.2
          · exact (hd.trans ((congrArg (kmswInfFaceSucc (W q) (HF q)) he).trans hz)) ▸ z.2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical restriction preserves retained inner faces and their succession. -/
theorem GeometricAncestorMarkedIso.restrictEquiv_faceNext_iff
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .faceNext u v ↔
      geometricAncestorRelation x T hT a s q' .faceNext
        ((I.restrictEquiv x T hT hst) u) ((I.restrictEquiv x T hT hst) v) := by
  rw [geometricAncestorInclusion_faceNext_iff x T hT a q hst,
    geometricAncestorInclusion_faceNext_iff x T hT a q' hst]
  constructor
  · rintro ⟨z, h₁, h₂⟩
    refine ⟨I.restrictEquiv x T hT hst z, ?_, ?_⟩
    · rw [← I.restrictEquiv_commutes, ← I.restrictEquiv_commutes]
      exact (I.relation_iff _ _ _).mp h₁
    · rw [← I.restrictEquiv_commutes, ← I.restrictEquiv_commutes]
      exact (I.relation_iff _ _ _).mp h₂
  · rintro ⟨z, h₁, h₂⟩
    obtain ⟨z, rfl⟩ := (I.restrictEquiv x T hT hst).surjective z
    refine ⟨z, ?_, ?_⟩
    · apply (I.relation_iff _ _ _).mpr
      rw [I.restrictEquiv_commutes, I.restrictEquiv_commutes]
      exact h₁
    · apply (I.relation_iff _ _ _).mpr
      rw [I.restrictEquiv_commutes, I.restrictEquiv_commutes]
      exact h₂

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A nonempty relation chain whose intermediate vertices avoid the retained subset. -/
inductive AncestorRotationChain {α : Type*} (R : α → α → Prop) (A : α → Prop) :
    α → α → Prop where
  | single {u v} : R u v → AncestorRotationChain R A u v
  | head {u z v} : R u z → ¬ A z → AncestorRotationChain R A z v →
      AncestorRotationChain R A u v

private theorem rotationChain_map {α β : Type*} {R : α → α → Prop}
    {S : β → β → Prop} {A : α → Prop} {B : β → Prop}
    (f : α → β) (hR : ∀ u v, R u v → S (f u) (f v))
    (hA : ∀ u, A u ↔ B (f u)) {u v : α} (h : AncestorRotationChain R A u v) :
    AncestorRotationChain S B (f u) (f v) := by
  induction h with
  | single h => exact .single (hR _ _ h)
  | head h hn _ ih => exact .head (hR _ _ h) (fun hz => hn ((hA _).mpr hz)) ih

private def rotationHit {α : Type*} (f : α → α) (A : Set α) (d e : α) : Prop :=
  ∃ k : ℕ, 0 < k ∧ f^[k] d = e ∧
    ∀ j : ℕ, 0 < j → j < k → f^[j] d ∉ A

private theorem rotationHit_concat {α : Type*} (f : α → α) (A : Set α)
    {d z e : α} (h₁ : rotationHit f A d z) (hz : z ∉ A)
    (h₂ : rotationHit f A z e) : rotationHit f A d e := by
  obtain ⟨k, hk, he, hg⟩ := h₁
  obtain ⟨l, hl, he', hg'⟩ := h₂
  refine ⟨l + k, by omega, ?_, ?_⟩
  · rw [Function.iterate_add_apply, he, he']
  · intro j hj hjkl
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact hg j hj hjk
    · exact he ▸ hz
    · have hshift : f^[j] d = f^[j - k] z := by
        rw [← he, ← Function.iterate_add_apply]
        congr 1
        omega
      rw [hshift]
      exact hg' (j - k) (by omega) (by omega)

private theorem rotationHit_to_chain {α : Type*} (f : α → α) (A B : Set α)
    (hAB : A ⊆ B) {e : α} (heA : e ∈ A) :
    ∀ k : ℕ, ∀ d : B, 0 < k → f^[k] d.1 = e →
      (∀ j : ℕ, 0 < j → j < k → f^[j] d.1 ∉ A) →
      AncestorRotationChain (fun d z : B => rotationHit f B d.1 z.1)
        (fun z : B => z.1 ∈ A) d ⟨e, hAB heA⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro d hk hend hgap
    have hex : ∃ m : ℕ, 0 < m ∧ f^[m] d.1 ∈ B :=
      ⟨k, hk, hend.symm ▸ hAB heA⟩
    let m := Nat.find hex
    have hm : 0 < m ∧ f^[m] d.1 ∈ B := Nat.find_spec hex
    have hmk : m ≤ k := Nat.find_min' hex ⟨hk, hend.symm ▸ hAB heA⟩
    have hmgap : ∀ j : ℕ, 0 < j → j < m → f^[j] d.1 ∉ B := by
      intro j hj hjm hjB
      exact Nat.find_min hex hjm ⟨hj, hjB⟩
    by_cases hmk' : m = k
    · exact .single ⟨k, hk, hend, hmk' ▸ hmgap⟩
    · have hmlt : m < k := lt_of_le_of_ne hmk hmk'
      let z : B := ⟨f^[m] d.1, hm.2⟩
      have hzA : z.1 ∉ A := hgap m hm.1 hmlt
      have hrem : f^[k - m] z.1 = e := by
        dsimp only [z]
        rw [← Function.iterate_add_apply]
        simpa only [Nat.sub_add_cancel hmk] using hend
      have hgrem : ∀ j : ℕ, 0 < j → j < k - m → f^[j] z.1 ∉ A := by
        intro j hj hjk
        dsimp only [z]
        rw [← Function.iterate_add_apply]
        exact hgap (j + m) (by omega) (by omega)
      exact .head ⟨m, hm.1, rfl, hmgap⟩ hzA
        (ih (k - m) (by omega) z (by omega) hrem hgrem)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Induced earlier rotation is exactly first return along the later rotation relation. -/
theorem geometricAncestorInclusion_rotation_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .rotation u v ↔
      AncestorRotationChain
        (geometricAncestorRelation x T hT a t q .rotation)
        (geometricAncestorIntrinsicCell x T hT a t q s)
        (geometricAncestorInclusion x T hT a q hst u)
        (geometricAncestorInclusion x T hT a q hst v) := by
  constructor
  · intro h
    cases u with
    | inl u => cases v <;> exact h.elim
    | inr u =>
      cases v with
      | inl v => exact h.elim
      | inr v =>
        obtain ⟨k, hk, he, hg⟩ := h
        let A := sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s
        let B := sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a t
        have hAB : A ⊆ B := fun _ hd => geometricAncestorEdges_mono x T hT a q hst hd
        have hh := rotationHit_to_chain
          (kmswInfRot (W q) (HF q)) A B hAB v.2 k ⟨u.1, hAB u.2⟩ hk he hg
        exact rotationChain_map (fun d : B => Sum.inr d)
          (fun _ _ h => h)
          (fun d => (intrinsicCell_dart_iff x T hT a q hst d).symm) hh
  · intro h
    let f : (ℕ × Bool) → ℕ × Bool := kmswInfRot (W q) (HF q)
    let A := sourceAncestorDarts (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s
    let dart : GeometricAncestorCell x T hT a t q → ℕ × Bool :=
      Sum.elim (fun _ => (0, false)) Subtype.val
    have aux : ∀ z z' : GeometricAncestorCell x T hT a t q,
        AncestorRotationChain (geometricAncestorRelation x T hT a t q .rotation)
          (geometricAncestorIntrinsicCell x T hT a t q s) z z' →
        rotationHit f A (dart z) (dart z') := by
      intro z z' hc
      induction hc with
      | @single z z' hr =>
        cases z with
        | inl z => cases z' <;> exact hr.elim
        | inr z =>
          cases z' with
          | inl z' => exact hr.elim
          | inr z' =>
            obtain ⟨k, hk, he, hg⟩ := hr
            exact ⟨k, hk, he, fun j hj hjk hjA =>
              hg j hj hjk (geometricAncestorEdges_mono x T hT a q hst hjA)⟩
      | @head z mid z' hr hn _ ih =>
        cases z with
        | inl z => cases mid <;> exact hr.elim
        | inr z =>
          cases mid with
          | inl mid => exact hr.elim
          | inr mid =>
            obtain ⟨k, hk, he, hg⟩ := hr
            apply rotationHit_concat f A
              ⟨k, hk, he, fun j hj hjk hjA =>
                hg j hj hjk (geometricAncestorEdges_mono x T hT a q hst hjA)⟩
              (fun hm => hn ((intrinsicCell_dart_iff x T hT a q hst mid).mpr hm)) ih
    have hh := aux _ _ h
    cases u with
    | inl u =>
      cases h with
      | single hr => cases v <;> exact hr.elim
      | head hr _ _ => cases ‹GeometricAncestorCell x T hT a t q› <;> exact hr.elim
    | inr u =>
      cases v with
      | inl v =>
        have noVertex : ∀ z z',
            AncestorRotationChain (geometricAncestorRelation x T hT a t q .rotation)
              (geometricAncestorIntrinsicCell x T hT a t q s) z z' →
            ∀ b, z' ≠ Sum.inl b := by
          intro z z' hc
          induction hc with
          | @single z z' hr => intro b he; subst z'; cases z <;> exact hr.elim
          | head _ _ _ ih => exact ih
        exact (noVertex _ _ h _ rfl).elim
      | inr v => exact hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical restriction preserves the induced rotation by first return. -/
theorem GeometricAncestorMarkedIso.restrictEquiv_rotation_iff
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t)
    (u v : GeometricAncestorCell x T hT a s q) :
    geometricAncestorRelation x T hT a s q .rotation u v ↔
      geometricAncestorRelation x T hT a s q' .rotation
        ((I.restrictEquiv x T hT hst) u) ((I.restrictEquiv x T hT hst) v) := by
  rw [geometricAncestorInclusion_rotation_iff x T hT a q hst,
    geometricAncestorInclusion_rotation_iff x T hT a q' hst]
  constructor
  · intro h
    have hh := rotationChain_map I.equiv (fun _ _ h => (I.relation_iff _ _ _).mp h)
      (I.intrinsicCell_iff x T hT s) h
    rw [I.restrictEquiv_commutes, I.restrictEquiv_commutes] at hh
    exact hh
  · intro h
    rw [← I.restrictEquiv_commutes, ← I.restrictEquiv_commutes] at h
    have hh := rotationChain_map I.equiv.symm
      (fun _ _ h => ((I.symm x T hT).relation_iff _ _ _).mp h)
      ((I.symm x T hT).intrinsicCell_iff x T hT s) h
    simpa only [Equiv.symm_apply_apply] using hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Restriction to any earlier ancestor level preserves every marked relation. -/
noncomputable def GeometricAncestorMarkedIso.restrict
    {a : ThinMapSide} {s t : ℕ} {q q' : selectedCutCoherentDomain x T hT}
    (I : GeometricAncestorMarkedIso x T hT a t q q') (hst : s ≤ t) :
    GeometricAncestorMarkedIso x T hT a s q q' where
  equiv := I.restrictEquiv x T hT hst
  relation_iff tag u v := by
    by_cases hr : tag = .rotation
    · subst tag
      exact I.restrictEquiv_rotation_iff x T hT hst u v
    by_cases hf : tag = .faceNext
    · subst tag
      exact I.restrictEquiv_faceNext_iff x T hT hst u v
    by_cases ht : tag = .target
    · subst tag
      exact I.restrictEquiv_target_iff x T hT hst u v
    exact I.restrictEquiv_basic_relation_iff x T hT hst tag hr hf ht u v

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every successor-level marked isomorphism restricts to the preceding level. -/
theorem geometricAncestorSuccessorRestriction_proved :
    GeometricAncestorSuccessorRestriction x T hT := by
  intro a q q' s I
  exact ⟨I.restrict x T hT (Nat.le_succ s),
    I.restrictEquiv_commutes x T hT (Nat.le_succ s)⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Finite marked isomorphisms assemble into a compatible whole-side isomorphism. -/
theorem geometricAncestorIsoAssembly_proved : GeometricAncestorIsoAssembly x T hT :=
  geometricAncestorSuccessorRestriction_implies_assembly x T hT
    (geometricAncestorSuccessorRestriction_proved x T hT)

end DirectedDistances.PaperProofs.Section4
