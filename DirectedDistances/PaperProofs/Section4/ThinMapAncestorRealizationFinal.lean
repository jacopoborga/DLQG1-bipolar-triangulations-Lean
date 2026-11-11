module

public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealization
public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorClass
public import DirectedDistances.PaperProofs.Section4.ThinCutSideImageEquality

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Permanent-ID descriptions of ancestry in a selected finite half. These descriptions
retain the actual half vertex and dart ranges; ambient ancestry alone does not
identify a geometric side. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

private theorem ancestorFinal_path_vertices_reach
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {x y : MapVertex M} {n : ℕ}
    (P : SimpleDirectedDartPath M x y n) (i d : ℕ) (hid : i + d ≤ n) :
    Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩)
      (P.vertices.get ⟨i + d, by rw [P.vertices_length]; omega⟩) := by
  induction d with
  | zero => exact Relation.ReflTransGen.refl
  | succ d ih =>
      have hs := P.edge_step ⟨i + d, by rw [P.darts_length]; omega⟩
      apply (ih (by omega)).tail
      exact ⟨P.darts.get ⟨i + d, by rw [P.darts_length]; omega⟩,
        hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Stage combinatorial reachability and present-edge reachability have identical -/
theorem ancestorFinal_stage_reachable_iff (w : ℕ → Fin 3) (t : ℕ)
    (v z : MapVertex (kmswStageDirectedMap w t)) :
    Relation.ReflTransGen (kmswStageDirectedMap w t).directedStep v z ↔
      Reachable (stageMapVertex w t v) (stageMapVertex w t z) := by
  constructor
  · intro h
    induction h with
    | refl => exact Reachable.rfl
    | tail _ hstep ih =>
        obtain ⟨e⟩ := (stageMap_directedStep_iff w t _ _).mp hstep
        exact ih.trans e.reachable
  · rintro ⟨p⟩
    obtain ⟨P⟩ := (stageMap_path_iff w t p.length v z).mpr ⟨p, rfl⟩
    have h := ancestorFinal_path_vertices_reach P 0 p.length (by omega)
    simpa only [Nat.zero_add, P.start_vertex, P.end_vertex] using h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestry of a record target in a finite representative is exactly ambient
infinite-map ancestry under the permanent-ID embedding. -/
theorem ancestorFinal_rep_ancestor_record_iff
    {ℓ r n : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v z : MapVertex R.B.map)
    (hv : (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id =
      (recordVertex w u).id) :
    z ∈ ancestors (presentation R a v) ↔
      Reachable
        (⟨(stageMapVertex w t (cutMapIsoVertexEquiv I z)).id⟩ : PresentVertex w)
        (recordVertex w u) := by
  change Relation.ReflTransGen R.B.map.directedStep z v ↔ _
  rw [cutMapIsoVertexEquiv_reachable_iff I, ancestorFinal_stage_reachable_iff]
  have he : stageMapVertex w t (cutMapIsoVertexEquiv I v) =
      (⟨(recordVertex w u).id⟩ : StagePresentVertex w t) :=
    congrArg StagePresentVertex.mk hv
  rw [he]
  exact record_ancestor_reachable_iff_stage w u t _ hut

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Left-half ancestry is precisely ambient ancestry of its image; seam rerouting
is supplied by the proved finite cut API. -/
theorem ancestorFinal_cutL_ancestor_record_iff
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v z : MapVertex (cutLRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
        (recordVertex w u).id) :
    z ∈ ancestors (presentation (cutLRep R hR).2 .left v) ↔
      Reachable (⟨(stageMapVertex w t
        (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z))).id⟩ : PresentVertex w)
        (recordVertex w u) := by
  rw [cutLRep_ancestors_map_iff]
  exact ancestorFinal_rep_ancestor_record_iff w t u hut R I .left _ _ hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Right-half ancestry is precisely ambient ancestry of its image, with the
actual right-half vertex map and unchanged record target. -/
theorem ancestorFinal_cutR_ancestor_record_iff
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v z : MapVertex (cutRRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id =
        (recordVertex w u).id) :
    z ∈ ancestors (presentation (cutRRep R hR).2 .right v) ↔
      Reachable (⟨(stageMapVertex w t
        (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id⟩ : PresentVertex w)
        (recordVertex w u) := by
  rw [cutRRep_ancestors_map_iff]
  exact ancestorFinal_rep_ancestor_record_iff w t u hut R I .right _ _ hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every representative dart is selected exactly when both permanent endpoints
are ambient ancestors of the record target. Missing darts are not dropped -/
theorem ancestorFinal_rep_selectedDarts_record_iff
    {ℓ r n : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v : MapVertex R.B.map)
    (hv : (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id =
      (recordVertex w u).id) (e : Fin R.dartCount) :
    e ∈ selectedDarts (presentation R a v) ↔
      Reachable (⟨edgeWest w (I.toEquiv e).1.val⟩ : PresentVertex w)
        (recordVertex w u) ∧
      Reachable (⟨edgeEast w (I.toEquiv e).1.val⟩ : PresentVertex w)
        (recordVertex w u) := by
  change (_ ∈ ancestors _ ∧ _ ∈ ancestors _) ↔ _
  rw [ancestorFinal_rep_ancestor_record_iff w t u hut R I a _ _ hv,
    ancestorFinal_rep_ancestor_record_iff w t u hut R I a _ _ hv]
  rw [(cutMapIsoVertexEquiv_endpoints I e).1,
    (cutMapIsoVertexEquiv_endpoints I e).2]
  change (Reachable (⟨stageEndpoint (kmswStage w t) (I.toEquiv e)⟩ : PresentVertex w) _ ∧
    Reachable (⟨stageEndpoint (kmswStage w t) (edgeFlip _ (I.toEquiv e))⟩ :
      PresentVertex w) _) ↔ _
  change (Reachable (⟨if (I.toEquiv e).2 then (kmswStage w t).east (I.toEquiv e).1.val
      else (kmswStage w t).west (I.toEquiv e).1.val⟩ : PresentVertex w) _ ∧
    Reachable (⟨if !(I.toEquiv e).2 then (kmswStage w t).east (I.toEquiv e).1.val
      else (kmswStage w t).west (I.toEquiv e).1.val⟩ : PresentVertex w) _) ↔ _
  obtain ⟨hw, he⟩ := edge_endpoints_eq w (I.toEquiv e).1.isLt
  cases hb : (I.toEquiv e).2 with
  | false => simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, hw, he]
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw, he, and_comm]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The left selected-dart image is the actual half-dart range intersected with
ambient ancestry of both permanent endpoints. -/
theorem ancestorFinal_cutL_selectedDarts_image_iff
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v : MapVertex (cutLRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
        (recordVertex w u).id) (e : StageDart (kmswStage w t).nextEdge) :
    e ∈ (I.toEquiv ∘ cutLRepDartMap R hR) ''
        selectedDarts (presentation (cutLRep R hR).2 .left v) ↔
      e ∈ Set.range (I.toEquiv ∘ cutLRepDartMap R hR) ∧
        Reachable (⟨edgeWest w e.1.val⟩ : PresentVertex w) (recordVertex w u) ∧
        Reachable (⟨edgeEast w e.1.val⟩ : PresentVertex w) (recordVertex w u) := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    apply (ancestorFinal_rep_selectedDarts_record_iff w t u hut R I .left
      (cutLRepVertexMap R hR v) hv (cutLRepDartMap R hR d)).mp
    exact cutLRep_selectedDarts_map R hR v d hd
  · rintro ⟨⟨d, rfl⟩, hw, he⟩
    refine ⟨d, ?_, rfl⟩
    have hd := (ancestorFinal_rep_selectedDarts_record_iff w t u hut R I .left
      (cutLRepVertexMap R hR v) hv (cutLRepDartMap R hR d)).mpr ⟨hw, he⟩
    have hh := (cutLRep_selectedDarts_image_iff R hR v (cutLRepDartMap R hR d)).mpr
      ⟨⟨d, rfl⟩, hd⟩
    obtain ⟨d', hd', hdd⟩ := hh
    exact (cutLRep_embedding_fields R hR).1 hdd ▸ hd'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right selected-dart image retains its actual half-dart range and both
ambient endpoint ancestry conditions. -/
theorem ancestorFinal_cutR_selectedDarts_image_iff
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v : MapVertex (cutRRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id =
        (recordVertex w u).id) (e : StageDart (kmswStage w t).nextEdge) :
    e ∈ (I.toEquiv ∘ cutRRepDartMap R hR) ''
        selectedDarts (presentation (cutRRep R hR).2 .right v) ↔
      e ∈ Set.range (I.toEquiv ∘ cutRRepDartMap R hR) ∧
        Reachable (⟨edgeWest w e.1.val⟩ : PresentVertex w) (recordVertex w u) ∧
        Reachable (⟨edgeEast w e.1.val⟩ : PresentVertex w) (recordVertex w u) := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    apply (ancestorFinal_rep_selectedDarts_record_iff w t u hut R I .right
      (cutRRepVertexMap R hR v) hv (cutRRepDartMap R hR d)).mp
    exact cutRRep_selectedDarts_map R hR v d hd
  · rintro ⟨⟨d, rfl⟩, hw, he⟩
    refine ⟨d, ?_, rfl⟩
    have hd := (ancestorFinal_rep_selectedDarts_record_iff w t u hut R I .right
      (cutRRepVertexMap R hR v) hv (cutRRepDartMap R hR d)).mpr ⟨hw, he⟩
    have hh := (cutRRep_selectedDarts_image_iff R hR v (cutRRepDartMap R hR d)).mpr
      ⟨⟨d, rfl⟩, hd⟩
    obtain ⟨d', hd', hdd⟩ := hh
    exact (cutRRep_embedding_fields R hR).1 hdd ▸ hd'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent-ID image of the left ancestor set is its actual vertex range
intersected with ambient ancestry of the record target. -/
theorem ancestorFinal_cutL_ancestor_image_eq
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v : MapVertex (cutLRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR v))).id =
        (recordVertex w u).id) :
    let F := fun z => (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutLRepVertexMap R hR z))).id
    F '' ancestors (presentation (cutLRep R hR).2 .left v) =
      Set.range F ∩ {z | Reachable (⟨z⟩ : PresentVertex w) (recordVertex w u)} := by
  intro F
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩,
      (ancestorFinal_cutL_ancestor_record_iff w t u hut R hR I v b hv).mp hb⟩
  · rintro ⟨⟨b, rfl⟩, hb⟩
    exact ⟨b, (ancestorFinal_cutL_ancestor_record_iff w t u hut R hR I v b hv).mpr hb,
      rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The right ancestor image has the same range-intersection description, using
the actual right cut and the same permanent record target. -/
theorem ancestorFinal_cutR_ancestor_image_eq
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t u : ℕ) (hut : u ≤ t)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (v : MapVertex (cutRRep R hR).2.B.map)
    (hv : (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR v))).id =
        (recordVertex w u).id) :
    let F := fun z => (stageMapVertex w t
      (cutMapIsoVertexEquiv I (cutRRepVertexMap R hR z))).id
    F '' ancestors (presentation (cutRRep R hR).2 .right v) =
      Set.range F ∩ {z | Reachable (⟨z⟩ : PresentVertex w) (recordVertex w u)} := by
  intro F
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, rfl⟩,
      (ancestorFinal_cutR_ancestor_record_iff w t u hut R hR I v b hv).mp hb⟩
  · rintro ⟨⟨b, rfl⟩, hb⟩
    exact ⟨b, (ancestorFinal_cutR_ancestor_record_iff w t u hut R hR I v b hv).mpr hb,
      rfl⟩

private theorem ancestorFinal_reachable_zero_iff (w : ℕ → Fin 3) (v : ℕ) :
    Reachable (⟨v⟩ : PresentVertex w) ⟨0⟩ ↔ v = 0 := by
  constructor
  · intro h
    have hs : Reachable (⟨v⟩ : StagePresentVertex w 0) ⟨0⟩ :=
      (record_ancestor_reachable_iff_stage w 0 0 v le_rfl).mpr h
    obtain ⟨p⟩ := hs
    cases p with
    | nil => rfl
    | cons p e =>
        have he := e.property.2.2.2
        change 1 = 0 at he
        omega
  · rintro rfl
    exact Reachable.rfl

private theorem ancestorFinal_finite_source_ancestor_iff
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (v : MapVertex R.B.map) :
    v ∈ ancestors (presentation R a R.B.source) ↔ v = R.B.source := by
  constructor
  · intro h
    cases h with
    | refl => rfl
    | tail h hs => exact (R.B.isSource ⟨_, hs⟩).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite ancestor restriction at the source contains no geometric darts. -/
theorem ancestorFinal_finite_source_no_darts
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (d : selectedDarts (presentation R a R.B.source)) : False := by
  have ht := (ancestorFinal_finite_source_ancestor_iff R a _).mp d.2.1
  have hh := (ancestorFinal_finite_source_ancestor_iff R a _).mp d.2.2
  by_cases htail : R.B.map.tail d.1
  · apply R.B.isSource
    exact ⟨_, d.1, R.B.noMissingDarts d.1, htail, rfl, hh⟩
  · have hflip : R.B.map.tail (R.B.map.edgeInv d.1) := by
      by_contra h
      exact htail ((R.B.map.tail_iff d.1 (R.B.noMissingDarts d.1)).mpr h)
    apply R.B.isSource
    refine ⟨_, R.B.map.edgeInv d.1, R.B.noMissingDarts _, hflip, rfl, ?_⟩
    simpa only [dartHeadVertex, dartTailVertex,
      R.B.map.toCombinatorialMap.edgeInv_invol] using ht

section CoherentDomain

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
  (q : selectedCutCoherentDomain x T hT)

local notation "w" => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "hfin" => sourceAncestor_finite_incidence x T hT q
local notation "hL" => sourceAncestor_left_nonneg x T hT q
local notation "htrans" => sourceAncestor_left_transient x T hT q
local notation "hR" => sourceAncestor_right_unbounded x T hT q
local notation "P" => sourceAncestorPath x T hT q

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
At level zero the geometric ancestor vertex carrier is precisely the source. -/
theorem ancestorFinal_sourceAncestorVertices_zero (a : ThinMapSide) :
    sourceAncestorVertices w hfin hL htrans hR P a 0 = {0} := by
  ext v
  constructor
  · intro hv
    exact (ancestorFinal_reachable_zero_iff w v).mp
      (ancestor_side_reachable x T hT q hv.2)
  · intro hv
    have hv0 : v = 0 := hv
    subst v
    exact source_mem_sourceAncestorVertices w hfin hL htrans hR P a 0

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
No geometric dart survives the ancestor restriction at level zero. -/
theorem ancestorFinal_sourceAncestorDarts_zero (a : ThinMapSide) :
    sourceAncestorDarts w hfin hL htrans hR P a 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hh : edgeEast w d.1 = 0 := by
    have hv := hd.2.2
    rw [ancestorFinal_sourceAncestorVertices_zero] at hv
    exact hv
  have hr : Reachable (⟨edgeEast w d.1⟩ : PresentVertex w) (recordVertex w 0) := by
    rw [hh]
    exact Reachable.rfl
  have ha := (record_ancestor_geometric_edge_in_stage w hL hR 0 0 d.1 le_rfl hr).1
  have he := (edge_endpoints_eq w ha).2
  change 1 = edgeEast w d.1 at he
  omega

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The level-zero finite restriction and the geometric restriction have the same
entire cell carrier: one source vertex and no darts. -/
@[expose] noncomputable def ancestorFinal_sourceCellEquiv
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide) :
    TruncationCell (presentation R a R.B.source) ≃
      SourceAncestorCell w hfin hL htrans hR P a 0 := by
  let vf : ancestors (presentation R a R.B.source) ≃
      sourceAncestorVertices w hfin hL htrans hR P a 0 :=
    { toFun := fun _ => ⟨0,
        source_mem_sourceAncestorVertices w hfin hL htrans hR P a 0⟩
      invFun := fun _ => ⟨R.B.source, Relation.ReflTransGen.refl⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact ((ancestorFinal_finite_source_ancestor_iff R a v.1).mp v.2).symm
      right_inv := by
        intro v
        apply Subtype.ext
        have hv := (Set.ext_iff.mp
          (ancestorFinal_sourceAncestorVertices_zero x T hT q a) v.1).mp v.2
        exact (show v.1 = 0 from hv).symm }
  let df : selectedDarts (presentation R a R.B.source) ≃
      sourceAncestorDarts w hfin hL htrans hR P a 0 :=
    { toFun := fun d => (ancestorFinal_finite_source_no_darts R a d).elim
      invFun := fun d => by
        have hd := (Set.ext_iff.mp
          (ancestorFinal_sourceAncestorDarts_zero x T hT q a) d.1).mp d.2
        exact hd.elim
      left_inv := fun d => (ancestorFinal_finite_source_no_darts R a d).elim
      right_inv := fun d => by
        have hd := (Set.ext_iff.mp
          (ancestorFinal_sourceAncestorDarts_zero x T hT q a) d.1).mp d.2
        exact hd.elim }
  exact Equiv.sumCongr vf df

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The level-zero cell equivalence preserves every relation and indexed marking,
including induced rotation and retained-face succession. -/
theorem ancestorFinal_sourceCellEquiv_relation
    {ℓ r n : ℕ} (R : KMSWMapRep ℓ r n) (a : ThinMapSide)
    (t : TruncationRelation) (u z : TruncationCell (presentation R a R.B.source)) :
    truncationRelation (presentation R a R.B.source) t u z ↔
      sourceAncestorRelation w hfin hL htrans hR P a 0 t
        (ancestorFinal_sourceCellEquiv x T hT q R a u)
        (ancestorFinal_sourceCellEquiv x T hT q R a z) := by
  cases u with
  | inr d => exact (ancestorFinal_finite_source_no_darts R a d).elim
  | inl v =>
      cases z with
      | inr d => exact (ancestorFinal_finite_source_no_darts R a d).elim
      | inl y =>
          have hv := (ancestorFinal_finite_source_ancestor_iff R a v.1).mp v.2
          cases t with
          | vertex => rfl
          | root =>
              change v.1 = R.B.source ↔ (0 : ℕ) = 0
              exact ⟨fun _ => rfl, fun _ => hv⟩
          | target =>
              change v.1 = R.B.source ↔ (0 : ℕ) = 0
              exact ⟨fun _ => rfl, fun _ => hv⟩
          | incident => rfl
          | opposite => rfl
          | oriented => rfl
          | rotation => rfl
          | faceNext => rfl
          | boundary i => rfl
          | seam i => rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every good cut realizes the full marked geometric ancestor restriction at
level zero. Positive levels are not asserted by this theorem. -/
theorem sourceAncestorCutRealization_zero (a : ThinMapSide) (k : ℕ)
    (hk : (0 : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    ∃ (ℓ r n : ℕ) (R : KMSWMapRep ℓ r n) (v : MapVertex R.B.map),
      selectedCutSide x T a k q.1 = some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩ ∧
      boundaryTarget R.B a 0 = some v ∧
      ∃ e : TruncationCell (presentation R a v) ≃
          SourceAncestorCell w hfin hL htrans hR P a 0,
        ∀ t u z, truncationRelation (presentation R a v) t u z ↔
          sourceAncestorRelation w hfin hL htrans hR P a 0 t (e u) (e z) := by
  obtain ⟨ℓ, r, n, R, v, hrep, hv, _⟩ :=
    selectedCutAncestorClass_representation x T hT a 0 k q hk
  have hv0 : v = R.B.source := (Option.some.inj hv).symm
  subst v
  exact ⟨ℓ, r, n, R, R.B.source, hrep, rfl,
    ancestorFinal_sourceCellEquiv x T hT q R a,
    ancestorFinal_sourceCellEquiv_relation x T hT q R a⟩

omit q in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The sole remaining realization obligation, with the proved level-zero case
removed. This proposition is isolated and is neither assumed nor asserted.
The geometric half-range identification and the positive-level marked -/
@[expose] noncomputable def SourceAncestorCutPositiveRealization : Prop :=
  ∀ (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT),
    0 < s →
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) →
    ∃ (ℓ r n : ℕ) (R : KMSWMapRep ℓ r n) (v : MapVertex R.B.map),
      selectedCutSide x T a k q.1 = some ⟨r, ⟨ℓ, ⟨n, KMSWMapIsoClass.mk R⟩⟩⟩ ∧
      boundaryTarget R.B a s = some v ∧
      ∃ e : TruncationCell (presentation R a v) ≃
          SourceAncestorCell (boltzmannKMSWStream (pathCode q.1))
            (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
            (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
            (sourceAncestorPath x T hT q) a s,
        ∀ t u z, truncationRelation (presentation R a v) t u z ↔
          sourceAncestorRelation (boltzmannKMSWStream (pathCode q.1))
            (sourceAncestor_finite_incidence x T hT q) (sourceAncestor_left_nonneg x T hT q)
            (sourceAncestor_left_transient x T hT q) (sourceAncestor_right_unbounded x T hT q)
            (sourceAncestorPath x T hT q) a s t (e u) (e z)

omit q in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The original realization obligation is equivalent to the isolated positive-level
obligation, using the unconditional marked realization at zero. No realization
hypothesis is added to a paper theorem. -/
theorem sourceAncestorCutRealization_iff_positive :
    SourceAncestorCutRealization x T hT ↔ SourceAncestorCutPositiveRealization x T hT := by
  constructor
  · intro h a s k q _ hk
    exact h a s k q hk
  · intro h a s k q hk
    cases s with
    | zero => exact sourceAncestorCutRealization_zero x T hT q a k hk
    | succ s => exact h a (s + 1) k q (Nat.succ_pos s) hk

end CoherentDomain
end DirectedDistances.PaperProofs.Section4
