/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceLemma56SliceMeasurable2

/- Raw-ID slice reconstruction with the oriented forward-ray face exclusion. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

/-- Helper toward Lemma 5.6: the raw retained vertex test deletes strict
vertex tails from the closed intrinsic right candidate. -/
@[expose] def geoSliceFixedVertexKept (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b v : ℕ) : Prop :=
  v ∈ M.vertices ∧ geoSliceIntrinsicRightRaw M p (.inl v) ∧
    (¬ ∃ i, a < i ∧ v = M.west (geoSliceSeamRayEdge M p i)) ∧
    (¬ ∃ i, b < i ∧ v = geometricSideDartInitial M (M.seam i))

/-- Helper toward Lemma 5.6: the raw retained edge test preserves both
orientations of each individual edge and deletes the weak edge tails. -/
@[expose] def geoSliceFixedEdgeKept (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b e : ℕ) : Prop :=
  e ∈ M.edges ∧ geoSliceIntrinsicRightRaw M p (.inr (e, false)) ∧
    geoSliceIntrinsicRightRaw M p (.inr (e, true)) ∧
    (¬ ∃ i, a ≤ i ∧ e = geoSliceSeamRayEdge M p i) ∧
    (¬ ∃ i, b ≤ i ∧ e = (M.seam i).1)

/-- Helper toward Lemma 5.6: raw rotation steps retain valid input dart IDs. -/
@[expose] def geoSliceFixedRawRotation (M : GeometricSideSubmap)
    (c e : GeoSliceRawCell) : Prop :=
  match c, e with
  | .inr d, .inr f => M.rotation d f ∧ d.1 ∈ M.edges ∧ f.1 ∈ M.edges
  | _, _ => False

/-- Helper toward Lemma 5.6: the retained raw cell carrier. -/
@[expose] def geoSliceFixedRawKept (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b : ℕ) : Set GeoSliceRawCell :=
  {c | match c with
    | .inl v => geoSliceFixedVertexKept M p a b v
    | .inr d => geoSliceFixedEdgeKept M p a b d.1}

/-- Helper toward Lemma 5.6: a slice candidate whose every field uses raw
IDs. Face succession excludes forward ray corners, retaining the reverse
orientation when its face is on the right. Rotation is first return to the
retained edge carrier; root and indexed marks come from the decoded ray. -/
@[expose] def geoSliceFixedCore (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b : ℕ) : GeometricSideSubmap where
  vertices := {v | geoSliceFixedVertexKept M p a b v}
  edges := {e | geoSliceFixedEdgeKept M p a b e}
  west := M.west
  east := M.east
  present := M.present
  rotation d e := geoSliceFixedEdgeKept M p a b e.1 ∧
    EnclosedSliceRotationChain (geoSliceFixedRawRotation M)
      (geoSliceFixedRawKept M p a b) (.inr d) (.inr e)
  faceNext d e := M.faceNext d e ∧
    geoSliceFixedEdgeKept M p a b d.1 ∧ geoSliceFixedEdgeKept M p a b e.1 ∧
    geoSliceIntrinsicRightRaw M p (.inr d) ∧
    ∀ i, d ≠ (geoSliceSeamRayEdge M p i, false)
  root := M.west (geoSliceSeamRayEdge M p 0)
  boundary i := (geoSliceSeamRayEdge M p i, false)
  seam := M.seam

/-- Helper toward Lemma 5.6: read the ray and joint least offsets from a
single side, failing exactly when one of those two readers fails. -/
@[expose] noncomputable def oneSliceReaderFixed (longest : Bool)
    (M : GeometricSideSubmap) : Option GeometricSideSubmap := do
  let p ← geoSliceOneSideRayCodeOption longest M
  let ab ← geoSliceOneSideOffsetsOption longest M
  pure (geoSliceFixedCore M p ab.1 ab.2)

/-- Helper toward Lemma 5.6: conditional evaluation at successful ray
and joint-offset outputs. -/
theorem oneSliceReaderFixed_eq_some_core {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode} {a b : ℕ}
    (hr : geoSliceOneSideRayCodeOption longest M = some p)
    (hoff : geoSliceOneSideOffsetsOption longest M = some (a, b)) :
    oneSliceReaderFixed longest M = some (geoSliceFixedCore M p a b) := by
  simp [oneSliceReaderFixed, hr, hoff]

/-- Helper toward Lemma 5.6: no forward ray corner has a face successor
in the corrected raw candidate, including at retained ray edges. -/
theorem geoSliceFixedCore_not_faceNext_forward (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b i : ℕ) (e : ℕ × Bool) :
    ¬ (geoSliceFixedCore M p a b).faceNext
      (geoSliceSeamRayEdge M p i, false) e := by
  intro h
  exact h.2.2.2.2 i rfl

/-- Helper toward Lemma 5.6: finite certificates, allowing length zero,
are precisely reflexive-transitive reachability. -/
theorem geoSliceFixed_finiteChain_iff {α : Type*} (R : α → α → Prop) (c e : α) :
    (∃ n : ℕ, ∃ f : Fin (n + 1) → α,
      f 0 = c ∧ f ⟨n, Nat.lt_succ_self n⟩ = e ∧
      ∀ j : Fin n, R (f j.castSucc) (f j.succ)) ↔
    Relation.ReflTransGen R c e := by
  constructor
  · rintro ⟨n, f, hc, he, hf⟩
    have hchain : ∀ i : Fin (n + 1), Relation.ReflTransGen R (f 0) (f i) := by
      intro i
      induction i using Fin.induction with
      | zero => exact .refl
      | succ i ih => exact ih.tail (hf i)
    rw [← hc, ← he]
    exact hchain _
  · intro h
    induction h with
    | refl => exact ⟨0, fun _ => c, rfl, rfl, fun j => Fin.elim0 j⟩
    | @tail d e h hde ih =>
      obtain ⟨n, f, hc, hd, hf⟩ := ih
      refine ⟨n + 1, Fin.snoc f e, ?_, ?_, ?_⟩
      · simpa using hc
      · exact Fin.snoc_last _ _
      · intro j
        cases j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_castSucc]
          have heq : (Fin.last n).succ = Fin.last (n + 1) := rfl
          rw [heq, Fin.snoc_last]
          exact hd ▸ hde
        | cast j =>
          rw [Fin.snoc_castSucc]
          have heq : j.castSucc.succ = j.succ.castSucc := rfl
          rw [heq, Fin.snoc_castSucc]
          exact hf j

/-- Helper toward Lemma 5.6: raw finite slit certificates are exactly
reflexive-transitive raw slit reachability. -/
theorem geoSliceFixed_rawReaches_iff (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (c e : GeoSliceRawCell) :
    geoSliceRawSlitReaches M p c e ↔
      Relation.ReflTransGen (geoSliceRawSlitStep M p) c e := by
  rw [← geoSliceFixed_finiteChain_iff]
  constructor
  · rintro (rfl | ⟨n, _, f, hf⟩)
    · exact ⟨0, fun _ => c, rfl, rfl, fun j => Fin.elim0 j⟩
    · exact ⟨n, f, hf⟩
  · rintro ⟨n, f, hc, he, hf⟩
    cases n with
    | zero => exact Or.inl (hc.symm.trans he)
    | succ n => exact Or.inr ⟨n + 1, Nat.zero_lt_succ n, f, hc, he, hf⟩

/-- Helper toward Lemma 5.6: conditional on a valid ray candidate, raw
right-face seeds decode exactly to the intrinsic side-cell seeds. -/
theorem geoSliceFixed_rawSeed_iff {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c : GeoSliceRawCell) (hc : geoSliceRawCellMem M c) :
    geoSliceRawRightFaceSeed M p c ↔ geometricSide_right_face_seed M
      (geoSliceSeamRayDartCells hcand) (geoSliceRawCellToCell M c hc) := by
  have hri (i : ℕ) : geoSliceRawCellMem M (geoSliceRawRayDart M p i) :=
    (hcand.1 i).1
  constructor
  · rintro ⟨i, hi, e, he⟩
    have he' : geoSliceRawCellMem M e := by
      cases c <;> cases e <;> simp_all [geoSliceRawFaceNext, geoSliceRawCellMem]
    exact ⟨i, (geoSliceRawOpposite_eq_cell _ _ (hri i) hc).1 hi,
      geoSliceRawCellToCell M e he', (geoSliceRawFaceNext_eq_cell _ _ hc he').1 he⟩
  · rintro ⟨i, hi, e, he⟩
    refine ⟨i, (geoSliceRawOpposite_eq_cell _ _ (hri i) hc).2 hi,
      geoSliceCellToRawCell e, ?_⟩
    apply (geoSliceRawFaceNext_eq_cell _ _ hc (geoSliceCellToRawCell_mem e)).2
    rw [geoSliceRawCellToCell_toRawCell]
    exact he

/-- Helper toward Lemma 5.6: conditional on a valid ray and raw carrier,
the raw intrinsic right test equals the dependent side-cell test. -/
theorem geoSliceFixed_rawRight_iff {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hcand : geoSliceSeamRayCandidate longest M p)
    (c : GeoSliceRawCell) (hc : geoSliceRawCellMem M c) :
    geoSliceIntrinsicRightRaw M p c ↔ geometricSide_intrinsic_right M
      (geoSliceSeamRayVertexCells hcand) (geoSliceSeamRayDartCells hcand)
      (geoSliceRawCellToCell M c hc) := by
  rw [geoSliceIntrinsicRightRaw, geometricSide_intrinsic_right,
    geoSliceRawRayVertexPred_iff_cell hcand c hc,
    geoSliceRawRayDartPred_iff_cell hcand c hc]
  apply or_congr Iff.rfl (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨a, ha, hac⟩
    have ham : geoSliceRawCellMem M a := by
      obtain ⟨_, ha, _⟩ := ha
      cases a with
      | inl v => simp [geoSliceRawOpposite, geoSliceRawRayDart] at ha
      | inr d => exact ha.2.1
    exact ⟨geoSliceRawCellToCell M a ham,
      (geoSliceFixed_rawSeed_iff hcand a ham).1 ha,
      (geoSliceRawSlitReflTransGen_iff_cell hcand a c ham hc).1
        ((geoSliceFixed_rawReaches_iff M p a c).1 hac)⟩
  · rintro ⟨a, ha, hac⟩
    let ar := geoSliceCellToRawCell a
    have ham : geoSliceRawCellMem M ar := geoSliceCellToRawCell_mem a
    have hdecode : geoSliceRawCellToCell M ar ham = a :=
      geoSliceRawCellToCell_toRawCell a
    refine ⟨ar, (geoSliceFixed_rawSeed_iff hcand ar ham).2 (hdecode.symm ▸ ha), ?_⟩
    apply (geoSliceFixed_rawReaches_iff M p ar c).2
    apply (geoSliceRawSlitReflTransGen_iff_cell hcand ar c ham hc).2
    rw [hdecode]
    exact hac

/-- Helper toward Lemma 5.6: conditional on a valid ray, the corrected
raw vertex carrier is exactly the earlier intrinsic vertex carrier. -/
theorem geoSliceFixedVertexKept_iff {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) (a b v : ℕ) :
    geoSliceFixedVertexKept M p a b v ↔
      geoSliceIntrinsicVertexKept M p longest hc a b v := by
  constructor
  · rintro ⟨hv, hr, ha, hb⟩
    exact ⟨hv, hv, (geoSliceFixed_rawRight_iff hc (.inl v) hv).1 hr, ha, hb⟩
  · rintro ⟨hv, hv', hr, ha, hb⟩
    exact ⟨hv, (geoSliceFixed_rawRight_iff hc (.inl v) hv').2 hr, ha, hb⟩

/-- Helper toward Lemma 5.6: conditional on a valid ray, the corrected
raw geometric-edge carrier is exactly the earlier intrinsic edge carrier. -/
theorem geoSliceFixedEdgeKept_iff {longest : Bool}
    {M : GeometricSideSubmap} {p : GeoSliceSeamRayCode}
    (hc : geoSliceSeamRayCandidate longest M p) (a b e : ℕ) :
    geoSliceFixedEdgeKept M p a b e ↔
      geoSliceIntrinsicEdgeKept M p longest hc a b e := by
  constructor
  · rintro ⟨he, hf, ht, ha, hb⟩
    exact ⟨he, he, ⟨(geoSliceFixed_rawRight_iff hc (.inr (e, false)) he).1 hf,
      (geoSliceFixed_rawRight_iff hc (.inr (e, true)) he).1 ht⟩, ha, hb⟩
  · rintro ⟨he, he', ⟨hf, ht⟩, ha, hb⟩
    exact ⟨he, (geoSliceFixed_rawRight_iff hc (.inr (e, false)) he').2 hf,
      (geoSliceFixed_rawRight_iff hc (.inr (e, true)) he').2 ht, ha, hb⟩

/-- Helper toward Lemma 5.6: on a source witness the corrected raw
candidate has precisely the source slice's vertex and edge carriers. -/
theorem M0CutGeodesicSliceWitness.oneSliceReaderFixed_carriers
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    ∃ p : GeoSliceSeamRayCode,
      ∃ _hc : geoSliceSeamRayCandidate (if x = XDP.ldp then true else false)
        (m0GeodesicSide s.hp (s.P k) .left) p,
      geoSliceOneSideRayCodeOption (if x = XDP.ldp then true else false)
        (m0GeodesicSide s.hp (s.P k) .left) = some p ∧
      (geoSliceFixedCore (m0GeodesicSide s.hp (s.P k) .left) p
        (s.thetaMinus k) (s.theta k)).vertices =
        (m0CutGeodesicSlice (hp := s.hp) s.P k
          (s.thetaMinus k) (s.theta k) (s.least k)).vertices ∧
      (geoSliceFixedCore (m0GeodesicSide s.hp (s.P k) .left) p
        (s.thetaMinus k) (s.theta k)).edges =
        (m0CutGeodesicSlice (hp := s.hp) s.P k
          (s.thetaMinus k) (s.theta k) (s.least k)).edges := by
  obtain ⟨p, hc, hr, _, _, hoff⟩ := s.oneSideReaders_eq k
  obtain ⟨N, hN, hv, he⟩ := s.intrinsicSliceOfSide_carriers k
  rw [intrinsicSliceOfSide_eq_some_core hr hoff] at hN
  cases Option.some.inj hN
  refine ⟨p, hc, hr, ?_, ?_⟩
  · exact (Set.ext fun v => geoSliceFixedVertexKept_iff hc _ _ v).trans hv
  · exact (Set.ext fun e => geoSliceFixedEdgeKept_iff hc _ _ e).trans he

/-- Helper toward Lemma 5.6: the corrected raw first-return relation is
exactly the first-return relation on dependent input-side cells, conditional
on the displayed retained-cell identity. -/
theorem geoSliceFixed_rotation_chain_iff (M : GeometricSideSubmap)
    (p : GeoSliceSeamRayCode) (a b : ℕ)
    (S : Set (GeometricSideCell M))
    (hS : ∀ c, c ∈ S ↔ geoSliceCellToRawCell c ∈ geoSliceFixedRawKept M p a b)
    (d e : {d : ℕ × Bool // d.1 ∈ M.edges}) :
    EnclosedSliceRotationChain (geometricSideRelation M .rotation) S
      (.inr d) (.inr e) ↔
    EnclosedSliceRotationChain (geoSliceFixedRawRotation M)
      (geoSliceFixedRawKept M p a b) (.inr d.val) (.inr e.val) := by
  apply enclosedSliceRotationChain_injective_iff geoSliceCellToRawCell
  · intro c e h
    have hc := geoSliceRawCellToCell_toRawCell c
    have he := geoSliceRawCellToCell_toRawCell e
    cases c <;> cases e <;> simp_all [geoSliceCellToRawCell]
  · intro c e
    cases c with
    | inl c => cases e <;> exact Iff.rfl
    | inr c => cases e with
      | inl e => exact Iff.rfl
      | inr e => exact ⟨fun h => ⟨h, c.property, e.property⟩, fun h => h.1⟩
  · exact hS
  · intro c y h
    have hy : geoSliceRawCellMem M y := by
      cases c <;> cases y <;>
        simp_all [geoSliceCellToRawCell, geoSliceFixedRawRotation, geoSliceRawCellMem]
    refine ⟨geoSliceRawCellToCell M y hy, ?_⟩
    cases y <;> rfl

/-- Helper toward Lemma 5.6: conditional carrier equality induces the
identity on vertex and dart IDs, preserving multiedge identity. -/
@[expose] def geoSliceFixedCellEquiv {N G : GeometricSideSubmap}
    (hv : N.vertices = G.vertices) (he : N.edges = G.edges) :
    GeometricSideCell N ≃ GeometricSideCell G :=
  Equiv.sumCongr (Equiv.subtypeEquivRight (fun v => by rw [hv]))
    (Equiv.subtypeEquivRight (fun d => by rw [he]))

/-- Helper toward Lemma 5.6: on every source slice witness, the corrected
single-side reader returns exactly the complete intrinsic slice class. -/
theorem M0CutGeodesicSliceWitness.oneSliceReaderFixed_class_eq
    {W : ℤ → Fin 3} {x : XDP} (s : M0CutGeodesicSliceWitness W x) (k : ℤ) :
    (oneSliceReaderFixed (if x = XDP.ldp then true else false)
      (m0GeodesicSide s.hp (s.P k) .left)).map geometricSideClass =
    leftOneSlice (if x = XDP.ldp then true else false)
      (m0GeodesicSide s.hp (s.P k) .left) := by
  obtain ⟨p, hc, hr, hvray, hdray, hoff⟩ := s.oneSideReaders_eq k
  obtain ⟨q, _, hq, hverts, hedges⟩ := s.oneSliceReaderFixed_carriers k
  have hqp : q = p := Option.some.inj (hq.symm.trans hr)
  subst q
  let M := m0GeodesicSide s.hp (s.P k) .left
  let N := geoSliceFixedCore M p (s.thetaMinus k) (s.theta k)
  let G := m0CutGeodesicSlice (hp := s.hp) s.P k
    (s.thetaMinus k) (s.theta k) (s.least k)
  let E : GeometricSideCell N ≃ GeometricSideCell G :=
    geoSliceFixedCellEquiv hverts hedges
  have hedge (i : ℕ) : geoSliceSeamRayEdge M p i =
      (s.P (k - 1)).codePath.edge i :=
    congrArg (fun c => (geoSliceCellDartValue c).1) (congrFun hdray i)
  have hroot : N.root = G.root := by
    change M.west (geoSliceSeamRayEdge M p 0) = _
    rw [hedge]
    exact ((s.P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) 0).2.trans
      (m0Geodesic_initial_zero _)
  have hS (c : GeometricSideCell M) :
      c ∈ Set.range (m0CutGeodesicSliceLeftCell s.hp s.P k
        (s.thetaMinus k) (s.theta k) (s.least k)) ↔
      geoSliceCellToRawCell c ∈ geoSliceFixedRawKept M p (s.thetaMinus k) (s.theta k) := by
    rw [m0CutGeodesicSliceLeftCell_mem_range_iff]
    cases c with
    | inl v => change v.val ∈ G.vertices ↔ v.val ∈ N.vertices; rw [hverts]
    | inr d => change d.val.1 ∈ G.edges ↔ d.val.1 ∈ N.edges; rw [hedges]
  have hrel : ∀ t c e, geometricSideRelation N t c e ↔
      geometricSideRelation G t (E c) (E e) := by
    intro t c e
    cases t with
    | rotation =>
      cases c with
      | inl c => cases e <;> exact Iff.rfl
      | inr c => cases e with
        | inl e => exact Iff.rfl
        | inr e =>
          have hcM : c.val.1 ∈ M.edges := c.property.1
          have heM : e.val.1 ∈ M.edges := e.property.1
          have hchain := geoSliceFixed_rotation_chain_iff M p (s.thetaMinus k)
            (s.theta k) _ hS ⟨c.val, hcM⟩ ⟨e.val, heM⟩
          have hsource := m0CutGeodesicSlice_rotation_iff_left_chain s.hp s.P k
            (s.thetaMinus k) (s.theta k) (s.least k)
            ⟨c.val, hedges ▸ c.property⟩ ⟨e.val, hedges ▸ e.property⟩
          change (_ ∧ _) ↔ G.rotation c.val e.val
          exact ⟨fun h => hsource.mpr (hchain.mpr h.2),
            fun h => ⟨e.property, hchain.mp (hsource.mp h)⟩⟩
    | faceNext =>
      cases c with
      | inl c => cases e <;> exact Iff.rfl
      | inr c => cases e with
        | inl e => exact Iff.rfl
        | inr e =>
          have hcM : c.val.1 ∈ M.edges := c.property.1
          have heM : e.val.1 ∈ M.edges := e.property.1
          have hright := geoSliceFixed_rawRight_iff hc (.inr c.val) hcM
          rw [hvray, hdray] at hright
          have hface := m0GeodesicLeftSide_previousRight_faceNext_iff_of_openA
            s.hp s.P k (s.left_adjacent_containment k)
            (fun c => by cases c <;> exact s.left_intrinsic_right_iff_previousRight k _) ⟨c.val, hcM⟩ ⟨e.val, heM⟩
          change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _)
          constructor
          · rintro ⟨hM, _, _, hR, hnot⟩
            refine ⟨(hface hM).mpr ⟨hright.mp hR, ?_⟩, hM⟩
            intro i hi
            apply hnot i
            have hi' := congrArg Subtype.val (Sum.inr.inj hi)
            rw [hedge]
            exact hi'
          · rintro ⟨hR, hM⟩
            obtain ⟨hR', hnot⟩ := (hface hM).mp hR
            refine ⟨hM, c.property, e.property, hright.mpr hR', ?_⟩
            intro i hi
            apply hnot i
            rw [← hdray]
            exact congrArg Sum.inr (Subtype.ext hi)
    | root =>
      cases c with
      | inl c => cases e <;> change (c.val = N.root ↔ c.val = G.root) <;> rw [hroot]
      | inr c => cases e <;> exact Iff.rfl
    | boundary i =>
      cases c with
      | inl c => cases e <;> exact Iff.rfl
      | inr c => cases e <;> change ((geoSliceSeamRayEdge M p i, false) = c.val ↔
          ((s.P (k - 1)).codePath.edge i, false) = c.val) <;> rw [hedge]
    | vertex => cases c <;> cases e <;> rfl
    | incident => cases c <;> cases e <;> rfl
    | opposite => cases c <;> cases e <;> rfl
    | oriented => cases c <;> cases e <;> rfl
    | target => cases c <;> cases e <;> rfl
    | seam i => cases c <;> cases e <;> rfl
  rw [oneSliceReaderFixed_eq_some_core hr hoff, Option.map_some, s.leftOneSlice_eq k]
  exact congrArg some ((geometricSideClass_eq_iff N G).mpr ⟨⟨E, hrel⟩⟩)

/-- Helper toward Lemma 5.6: the initial vertex of a varying dart is a
measurable raw coordinate, without a directed-presence assumption. -/
theorem measurable_geoSliceFixedDartInitial :
    Measurable (fun z : GeometricSideSubmap × (ℕ × Bool) =>
      geometricSideDartInitial z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro d
  rcases d with ⟨e, bit⟩
  cases bit
  · exact (comap_measurable geometricSideCode).snd.snd.fst.eval (a := e)
  · exact (comap_measurable geometricSideCode).snd.snd.snd.fst.eval (a := e)

/-- Helper toward Lemma 5.6: every fixed raw vertex-retention test is
measurable, with strict tails at both least offsets. -/
theorem measurableSet_geoSliceFixedVertexKept (p : GeoSliceSeamRayCode)
    (a b v : ℕ) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceFixedVertexKept M p a b v} := by
  have hV := measurableSet_geoSliceRawCellMem (.inl v)
  have hR := measurableSet_geoSliceIntrinsicRightRaw p (.inl v)
  have hA : MeasurableSet {M : GeometricSideSubmap |
      ∃ i, a < i ∧ v = M.west (geoSliceSeamRayEdge M p i)} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (by simpa only [eq_comm] using (measurable_geoSliceSeamRayVertex p i).eq_const v |>.setOf)
  have hB : MeasurableSet {M : GeometricSideSubmap |
      ∃ i, b < i ∧ v = geometricSideDartInitial M (M.seam i)} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    apply MeasurableSet.iUnion
    intro i
    have hi := measurable_geoSliceFixedDartInitial.comp
      (measurable_id.prodMk ((comap_measurable geometricSideCode).snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := i)))
    exact (MeasurableSet.const _).inter (by simpa only [Function.comp_apply, id_eq, geometricSideCode, eq_comm] using (hi.eq_const v).setOf)
  exact hV.inter (hR.inter (hA.compl.inter hB.compl))

/-- Helper toward Lemma 5.6: every fixed raw edge-retention test is
measurable, preserving both orientations and the weak edge tails. -/
theorem measurableSet_geoSliceFixedEdgeKept (p : GeoSliceSeamRayCode)
    (a b e : ℕ) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceFixedEdgeKept M p a b e} := by
  have hE := measurableSet_geoSliceRawCellMem (.inr (e, false))
  have hF := measurableSet_geoSliceIntrinsicRightRaw p (.inr (e, false))
  have hT := measurableSet_geoSliceIntrinsicRightRaw p (.inr (e, true))
  have hA : MeasurableSet {M : GeometricSideSubmap |
      ∃ i, a ≤ i ∧ e = geoSliceSeamRayEdge M p i} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (by simpa only [eq_comm] using (measurable_geoSliceSeamRayEdge p i).eq_const e |>.setOf)
  have hB : MeasurableSet {M : GeometricSideSubmap |
      ∃ i, b ≤ i ∧ e = (M.seam i).1} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    apply MeasurableSet.iUnion
    intro i
    have hi := ((comap_measurable geometricSideCode).snd.snd.snd.snd.snd.snd.snd.snd.snd.eval (a := i)).fst
    exact (MeasurableSet.const _).inter (by simpa only [geometricSideCode, eq_comm] using (hi.eq_const e).setOf)
  exact hE.inter (hF.inter (hT.inter (hA.compl.inter hB.compl)))

/-- Helper toward Lemma 5.6: raw input-rotation steps are measurable in
the complete side code, including both endpoint-carrier tests. -/
theorem measurableSet_geoSliceFixedRawRotation (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap | geoSliceFixedRawRotation M c e} := by
  cases c with
  | inl c => cases e <;> exact MeasurableSet.empty
  | inr c => cases e with
    | inl e => exact MeasurableSet.empty
    | inr e =>
      have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
      have hrot : MeasurableSet {M : GeometricSideSubmap | M.rotation c e} := by
        simpa only [geometricSideCode, decide_eq_true_eq] using
          (((hcode.snd.snd.snd.snd.snd.fst.eval (a := c)).eval (a := e)).eq_const true).setOf
      exact hrot.inter ((measurableSet_geoSliceRawCellMem (.inr c)).inter
        (measurableSet_geoSliceRawCellMem (.inr e)))

/-- Helper toward Lemma 5.6: a first-return chain consists of its first
step followed by reflexive-transitive steps whose departures are deleted. -/
theorem geoSliceFixed_firstReturn_iff {α : Type*} (R : α → α → Prop)
    (S : Set α) (c e : α) :
    EnclosedSliceRotationChain R S c e ↔
      ∃ d, R c d ∧ Relation.ReflTransGen (fun u v => u ∉ S ∧ R u v) d e := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨_, h, .refl⟩
    | cons h hb _ ih =>
      obtain ⟨d, hbd, hde⟩ := ih
      exact ⟨_, h, hde.head ⟨hb, hbd⟩⟩
  · rintro ⟨d, hcd, hde⟩
    induction hde using Relation.ReflTransGen.head_induction_on generalizing c with
    | refl => exact .single hcd
    | head h _ ih => exact .cons hcd h.1 (ih _ h.2)

/-- Helper toward Lemma 5.6: fixed raw first-return tests are measurable,
using countable finite certificates for the deleted-departure relation. -/
theorem measurableSet_geoSliceFixedFirstReturn (p : GeoSliceSeamRayCode)
    (a b : ℕ) (c e : GeoSliceRawCell) :
    MeasurableSet {M : GeometricSideSubmap |
      EnclosedSliceRotationChain (geoSliceFixedRawRotation M)
        (geoSliceFixedRawKept M p a b) c e} := by
  have hK (d : GeoSliceRawCell) : MeasurableSet {M : GeometricSideSubmap |
      d ∈ geoSliceFixedRawKept M p a b} := by
    cases d with
    | inl v => exact measurableSet_geoSliceFixedVertexKept p a b v
    | inr d => exact measurableSet_geoSliceFixedEdgeKept p a b d.1
  have hStep (u v : GeoSliceRawCell) : MeasurableSet {M : GeometricSideSubmap |
      u ∉ geoSliceFixedRawKept M p a b ∧ geoSliceFixedRawRotation M u v} :=
    (hK u).compl.inter (measurableSet_geoSliceFixedRawRotation u v)
  have hReach (d : GeoSliceRawCell) : MeasurableSet {M : GeometricSideSubmap |
      Relation.ReflTransGen (fun u v => u ∉ geoSliceFixedRawKept M p a b ∧
        geoSliceFixedRawRotation M u v) d e} := by
    have hEq : {M : GeometricSideSubmap |
        Relation.ReflTransGen (fun u v => u ∉ geoSliceFixedRawKept M p a b ∧
          geoSliceFixedRawRotation M u v) d e} =
        {M | ∃ n : ℕ, ∃ f : Fin (n + 1) → GeoSliceRawCell,
          f 0 = d ∧ f ⟨n, Nat.lt_succ_self n⟩ = e ∧
          ∀ j : Fin n, f j.castSucc ∉ geoSliceFixedRawKept M p a b ∧
            geoSliceFixedRawRotation M (f j.castSucc) (f j.succ)} := by
      ext M
      exact (geoSliceFixed_finiteChain_iff _ d e).symm
    rw [hEq]
    simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun f =>
      (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (MeasurableSet.iInter fun j => hStep _ _))
  have hEq : {M : GeometricSideSubmap |
      EnclosedSliceRotationChain (geoSliceFixedRawRotation M)
        (geoSliceFixedRawKept M p a b) c e} =
      {M | ∃ d, geoSliceFixedRawRotation M c d ∧
        Relation.ReflTransGen (fun u v => u ∉ geoSliceFixedRawKept M p a b ∧
          geoSliceFixedRawRotation M u v) d e} := by
    ext M
    exact geoSliceFixed_firstReturn_iff _ _ _ _
  rw [hEq]
  simp only [Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun d =>
    (measurableSet_geoSliceFixedRawRotation c d).inter (hReach d)

/-- Helper toward Lemma 5.6: the orientation-sensitive fixed-core face
test is measurable on the raw side code. -/
theorem measurableSet_geoSliceFixedCore_faceNext (p : GeoSliceSeamRayCode)
    (a b : ℕ) (d e : ℕ × Bool) :
    MeasurableSet {M : GeometricSideSubmap | (geoSliceFixedCore M p a b).faceNext d e} := by
  have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hface : MeasurableSet {M : GeometricSideSubmap | M.faceNext d e} := by
    simpa only [geometricSideCode, decide_eq_true_eq] using
      (((hcode.snd.snd.snd.snd.snd.snd.fst.eval (a := d)).eval (a := e)).eq_const true).setOf
  have hnot : MeasurableSet {M : GeometricSideSubmap |
      ∀ i, d ≠ (geoSliceSeamRayEdge M p i, false)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hi := ((measurable_geoSliceSeamRayEdge p i).prodMk
      (measurable_const (a := false))).eq_const d
    simpa only [eq_comm, Set.compl_ofPred] using hi.setOf.compl
  exact hface.inter ((measurableSet_geoSliceFixedEdgeKept p a b d.1).inter
    ((measurableSet_geoSliceFixedEdgeKept p a b e.1).inter
      ((measurableSet_geoSliceIntrinsicRightRaw p (.inr d)).inter hnot)))

/-- Helper toward Lemma 5.6: all ten fields of a fixed-ray, fixed-offset
corrected core form a measurable complete code. -/
theorem measurable_geoSliceFixedCore_code (p : GeoSliceSeamRayCode) (a b : ℕ) :
    Measurable (fun M : GeometricSideSubmap => geometricSideCode (geoSliceFixedCore M p a b)) := by
  have hBool (P : GeometricSideSubmap → Prop)
      (hP : MeasurableSet {M | P M}) : Measurable (fun M => decide (P M)) := by
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hP
  have hV := measurable_pi_iff.mpr fun n => hBool _ (measurableSet_geoSliceFixedVertexKept p a b n)
  have hE := measurable_pi_iff.mpr fun n => hBool _ (measurableSet_geoSliceFixedEdgeKept p a b n)
  have hR := measurable_pi_iff.mpr fun d => measurable_pi_iff.mpr fun e =>
    hBool (fun M => (geoSliceFixedCore M p a b).rotation d e) (by
      exact (measurableSet_geoSliceFixedEdgeKept p a b e.1).inter
        (measurableSet_geoSliceFixedFirstReturn p a b (.inr d) (.inr e)))
  have hF := measurable_pi_iff.mpr fun d => measurable_pi_iff.mpr fun e =>
    hBool _ (measurableSet_geoSliceFixedCore_faceNext p a b d e)
  have hcode : Measurable geometricSideCode := comap_measurable geometricSideCode
  have hB : Measurable (fun M : GeometricSideSubmap =>
      fun i => (geoSliceSeamRayEdge M p i, false)) :=
    measurable_pi_iff.mpr fun i => (measurable_geoSliceSeamRayEdge p i).prodMk measurable_const
  exact hV.prodMk (hE.prodMk (hcode.snd.snd.fst.prodMk
    (hcode.snd.snd.snd.fst.prodMk (hcode.snd.snd.snd.snd.fst.prodMk
      (hR.prodMk (hF.prodMk ((measurable_geoSliceSeamRayVertex p 0).prodMk
        (hB.prodMk hcode.snd.snd.snd.snd.snd.snd.snd.snd.snd))))))))

/-- Helper toward Lemma 5.6: the fixed-ray and fixed-offset corrected
core is measurable as a geometric submap. -/
theorem measurable_geoSliceFixedCore (p : GeoSliceSeamRayCode) (a b : ℕ) :
    Measurable (fun M : GeometricSideSubmap => geoSliceFixedCore M p a b) :=
  measurable_comap_iff.mpr (measurable_geoSliceFixedCore_code p a b)

/-- Helper toward Lemma 5.6: the countable optional ray-code sigma algebra. -/
local instance : MeasurableSpace (Option GeoSliceSeamRayCode) := ⊤
/-- Helper toward Lemma 5.6: the countable optional joint-offset sigma algebra. -/
local instance : MeasurableSpace (Option (ℕ × ℕ)) := ⊤

/-- Helper toward Lemma 5.6: countable ray and joint-offset selection
makes the corrected optional class reader measurable on numbered sides. -/
theorem measurable_oneSliceReaderFixed_class (longest : Bool) :
    Measurable (fun M : GeometricSideSubmap =>
      (oneSliceReaderFixed longest M).map geometricSideClass) := by
  let f (z : GeometricSideSubmap × (Option GeoSliceSeamRayCode × Option (ℕ × ℕ))) :
      Option GeometricSideClass := do
    let p ← z.2.1
    let ab ← z.2.2
    pure (geometricSideClass (geoSliceFixedCore z.1 p ab.1 ab.2))
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    rintro ⟨p, ab⟩
    cases p with
    | none => exact measurable_const
    | some p => cases ab with
      | none => exact measurable_const
      | some ab =>
        exact measurable_some_geometricSideClass.comp
          (measurable_geometricSideClass.comp (measurable_geoSliceFixedCore p ab.1 ab.2))
  have h := hf.comp (measurable_id.prodMk
    ((measurable_geoSliceOneSideRayCodeOption longest).prodMk
      (measurable_geoSliceOneSideOffsetsOption longest)))
  have heq : (fun M : GeometricSideSubmap =>
      (oneSliceReaderFixed longest M).map geometricSideClass) =
      f ∘ (fun M => (M, (geoSliceOneSideRayCodeOption longest M,
        geoSliceOneSideOffsetsOption longest M))) := by
    funext M
    simp only [oneSliceReaderFixed, f, Function.comp_apply]
    cases geoSliceOneSideRayCodeOption longest M <;>
      cases geoSliceOneSideOffsetsOption longest M <;> rfl
  rw [heq]
  exact h

/-- Helper toward Lemma 5.6: on one full-measure event, the corrected
reader gives the actual optional slice classes simultaneously at every
integer index, using the same source witness. -/
theorem m0Cut_ae_oneSliceReaderFixed (x : XDP) :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ s : M0CutGeodesicSliceWitness W x, ∀ k : ℤ,
        (oneSliceReaderFixed (if x = XDP.ldp then true else false)
          (m0GeodesicSide s.hp (s.P k) .left)).map geometricSideClass =
        m0CutGeodesicSliceClassOption x k W := by
  filter_upwards [m0Cut_ae_leftSideUpdates x] with W hW
  obtain ⟨s, hs⟩ := hW
  exact ⟨s, fun k => (s.oneSliceReaderFixed_class_eq k).trans (hs k).1⟩








































/- All 29 named declarations were checked by temporary #print axioms probes
axioms is {propext, Classical.choice, Quot.sound}. No custom axiom or
placeholder axiom occurred. All probes were removed before the final compile. -/

end DirectedDistances.PaperProofs.Section5
