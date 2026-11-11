module

public import DirectedDistances.KMSW.KMSWPeanoPrefix
public import DirectedDistances.KMSW.KMSWInverseStepLink
public import DirectedDistances.KMSW.StageOuterWordSucc
public import DirectedDistances.PlanarMap.BipolarPeanoConfiguration
public import DirectedDistances.PlanarMap.BipolarInnerFaceShape

/-! # Peano-prefix climb helper

(code `0` ↦ `(−1,0)`); not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- A target vertex belongs to the image of the current prefix when it is the
tail vertex of an image of a present source dart. -/
@[expose] def KMSWPeanoPrefixVertexInImage
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (v : MapVertex B.map) : Prop :=
  ∃ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    (kmswRootedStage (codeExtend c) j).map.tail d ∧
      B.map.tail (P.emb.dartMap d) ∧
      dartTailVertex B.map (P.emb.dartMap d) = v

/-- The frontier information needed at a climb: a nonempty last-to-first UL
frontier entry is the forward dart of `edgeInv (rot a)`, while an empty UL
frontier means the parent vertex of the next Peano edge is not yet represented.
The second clause is the fresh-vertex case; the stage update adds the new LL
edge from that vertex to the old active edge's west endpoint. This is an
explicit frontier predicate, not derivable from the embedding `P` alone;
it is derived from `KMSWPeanoPrefixInv` in
`KMSWPeanoPrefixInvariantSteps.lean`. In the fresh case the new LL edge is
also required to lie strictly after `b` in Peano order and outside the old dart
image. -/
@[expose] def KMSWPeanoPrefixClimbFrontier
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) : Prop :=
  let s := kmswStage (codeExtend c) j
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  (∀ e es, s.UL.dropLast.reverse = e :: es →
    ∃ he : e < s.nextEdge, s.present e = true ∧
      P.emb.dartMap ((⟨e, he⟩, false) : StageDart s.nextEdge) =
        B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) ∧
  (s.UL.dropLast.reverse = [] →
    ¬ KMSWPeanoPrefixVertexInImage B c j hj P
      (dartTailVertex B.map b)) ∧
  (s.UL.dropLast.reverse = [] →
    B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) ∉
        Set.range P.emb.dartMap ∧
      j + 1 < (peanoIndex B
        (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a))).val)

/-- Extra collision-exclusion fact needed to prove injectivity when the old
prefix map is extended: no old missing frontier dart may already represent
the next Peano edge. -/
@[expose] def KMSWPeanoPrefixClimbNoNextFrontierCollision
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) : Prop :=
  ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    (kmswStage (codeExtend c) j).present d.1.val = false →
      (peanoIndex B (P.emb.dartMap d)).val ≠ j + 1

/-- The empty code word with endpoint parameters `(ℓ,r)=(1,1)` is admissible;
its padded procedure code begins with `0`. This explicit case checks the
fresh-left stage rule: from the initial state, `UL.dropLast.reverse=[]`, and
the rule creates a fresh vertex and prepends the new missing LL edge. It is a -/
def climbExampleWalk : KMSWWalkClass 1 1 1 := by
  refine ⟨fun i => i.elim0, ?_⟩
  unfold KMSWWalkAdmissible
  constructor
  · simp only [integrateCodes]
    rfl
  · intro k hk
    have hk0 : k = 0 := by
      have hk' := Finset.mem_range.mp hk
      omega
    subst k
    simp [integrateCodes]

/-- The explicit empty admissible code is padded by code `0` at stage zero. -/
theorem climbExampleWalk_firstPaddedCode : codeExtend climbExampleWalk 0 = 0 := by
  simp [codeExtend, finiteCodeExtend]

/-- In that example the initial UL list has empty `dropLast.reverse`. -/
theorem climbExampleWalk_initial_frontier_empty :
    (kmswStage (codeExtend climbExampleWalk) 0).UL.dropLast.reverse = [] := by
  simp [kmswStage, kmswInit]

/-- The fresh-left branch records the new vertex and the missing LL edge's
west/east endpoints exactly as in the KMSW procedure. -/
theorem kmswPeanoPrefixClimb_leftFresh_stage_facts
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hcode : codeExtend c j = 0)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = []) :
    let s := kmswStage (codeExtend c) j
    let t := kmswStage (codeExtend c) (j + 1)
    t.nextEdge = s.nextEdge + 2 ∧ t.nextVertex = s.nextVertex + 1 ∧
      t.west (s.nextEdge + 1) = s.nextVertex ∧
      t.east (s.nextEdge + 1) = s.west s.active ∧
      t.present (s.nextEdge + 1) = false ∧
      t.LL = (s.nextEdge + 1) :: s.LL := by
  rcases kmswStage_step_leftFresh_facts (codeExtend c) j hcode hUL with
    ⟨hnextEdge, hnextVertex, _hwest, _heast, hwestLL, heastLL,
      _hactive, _hpresent, hmissing, _hUL, _hLR, _hUR, hLL⟩
  exact ⟨hnextEdge, hnextVertex, hwestLL, heastLL, hmissing, hLL⟩

/-- The existing-predecessor left branch allocates only the new active edge
and moves the UL head `e` into the successor list. -/
theorem kmswPeanoPrefixClimb_leftExisting_stage_facts
    (c : KMSWWalkClass ℓ r n) (j e : ℕ) (es : List ℕ)
    (hcode : codeExtend c j = 0)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es) :
    let s := kmswStage (codeExtend c) j
    let t := kmswStage (codeExtend c) (j + 1)
    t.nextEdge = s.nextEdge + 1 ∧ t.nextVertex = s.nextVertex ∧
      t.west s.nextEdge = s.west e ∧
      t.east s.nextEdge = s.east s.active ∧
      t.active = s.nextEdge ∧ t.present s.nextEdge = true ∧
      t.UL = es.reverse ++ [s.nextEdge] := by
  rcases kmswStage_step_leftExisting_facts
      (codeExtend c) j e es hcode hUL with
    ⟨hnextEdge, hnextVertex, hwest, heast, hactive, hpresent,
      hUL', _hLR, _hUR, _hLL⟩
  exact ⟨hnextEdge, hnextVertex, hwest, heast, hactive, hpresent, hUL'⟩

/-- In the climb configuration, `edgeInv (rot a)` is the forward UL parent
dart at the tail vertex of `a`, hence has the same tail vertex as `b`. -/
theorem peanoClimb_edgeInv_rot_tail_eq_next
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (j : ℕ) (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hkind : peanoStepKind B j hj1 = .climb) :
    dartTailVertex B.map
        (B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, by omega⟩))) =
      dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩) := by
  have hcfg : PeanoStepConfig B j hj1 .climb := by
    simpa [hkind] using peanoStepKind_config B j hj1
  rcases hcfg with ⟨hs, _hcontour, _houter, _hhead, hparent, hrot, _hb,
    _hface, _hinner⟩
  rw [hparent]
  simp [ulParent, hs, canonicalULSelector_val, hrot]

/-- Under the explicit climb frontier hypothesis, the KMSW left update uses
its existing-predecessor branch exactly when the parent of `b` is a vertex in
the prefix image. This procedure-reading helper toward thm-kmsw
result. -/
theorem kmswPeanoPrefixClimb_existing_iff_parent_in_image
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hkind : peanoStepKind B j hj1 = .climb)
    (hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P) :
    (kmswStage (codeExtend c) j).UL.dropLast.reverse ≠ [] ↔
      KMSWPeanoPrefixVertexInImage B c j hj P
        (dartTailVertex B.map (peanoEdge B ⟨j + 1, hj1⟩)) := by
  let s := kmswStage (codeExtend c) j
  let a := peanoEdge B ⟨j, by omega⟩
  dsimp [KMSWPeanoPrefixClimbFrontier, s, a] at hfrontier
  dsimp [KMSWPeanoPrefixVertexInImage]
  change s.UL.dropLast.reverse ≠ [] ↔ _
  constructor
  · intro hUL
    cases hlist : s.UL.dropLast.reverse with
    | nil => contradiction
    | cons e es =>
      obtain ⟨he, hpresent, hmap⟩ := hfrontier.1 e es hlist
      have hdart : (kmswRootedStage (codeExtend c) j).map.tail
          ((⟨e, he⟩, false) : StageDart s.nextEdge) := by
        change (s.present e = true ∧ false = false)
        exact ⟨hpresent, rfl⟩
      have hsourceMissing : ¬ (kmswRootedStage (codeExtend c) j).map.missing
          ((⟨e, he⟩, false) : StageDart s.nextEdge) := by
        change ¬ s.present e = false
        rw [hpresent]
        decide
      have htail := P.emb.tail_comm
        ((⟨e, he⟩, false) : StageDart s.nextEdge) hsourceMissing
      have htargetTail : B.map.tail
          (P.emb.dartMap ((⟨e, he⟩, false) : StageDart s.nextEdge)) :=
        htail.mp hdart
      refine ⟨(⟨e, he⟩, false), hdart, htargetTail, ?_⟩
      rw [hmap, peanoClimb_edgeInv_rot_tail_eq_next B j hj1 hkind]
  · intro himage
    by_contra hUL
    have hempty : s.UL.dropLast.reverse = [] := by
      cases hlist : s.UL.dropLast.reverse with
      | nil => rfl
      | cons e es => simp [hlist] at hUL
    exact hfrontier.2.1 hempty himage

/-- Candidate dart map for the existing-predecessor climb update: it retains
the old prefix map under `outerSucc_castDart`, maps the new present edge to
`b`, and maps its reverse to `edgeInv b`. Helper toward thm-kmsw -/
@[expose] noncomputable def kmswPeanoPrefixClimbLeftExistingDartMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) :
    StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge → D := by
  let s := kmswStage (codeExtend c) j
  let b := peanoEdge B ⟨j + 1, hj1⟩
  exact fun d =>
    if h : d.1.val < s.nextEdge then
      P.emb.dartMap ((⟨d.1.val, h⟩, d.2) : StageDart s.nextEdge)
    else if d.2 then B.map.toCombinatorialMap.edgeInv b else b

/-- Candidate dart map for the fresh-left climb update: it retains old darts,
maps the new present edge to `b`, and maps the new missing LL edge to the
forward dart `edgeInv (rot a)` (with its reverse mapped to `rot a`). Helper -/
@[expose] noncomputable def kmswPeanoPrefixClimbLeftFreshDartMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj) :
    StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge → D := by
  let s := kmswStage (codeExtend c) j
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  exact fun d =>
    if h : d.1.val < s.nextEdge then
      P.emb.dartMap ((⟨d.1.val, h⟩, d.2) : StageDart s.nextEdge)
    else if heq : d.1.val = s.nextEdge then
      if d.2 then B.map.toCombinatorialMap.edgeInv b else b
    else if d.2 then B.map.toCombinatorialMap.rot a
    else B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)

/-- On every old dart, the existing-predecessor candidate map is the prefix
map transported by `outerSucc_castDart`. -/
theorem kmswPeanoPrefixClimbLeftExistingDartMap_old
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
        (outerSucc_castDart
          (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
            (Nat.le_succ j)) d) =
      P.emb.dartMap d := by
  simp [kmswPeanoPrefixClimbLeftExistingDartMap, outerSucc_castDart]

/-- On every old dart, the fresh-left candidate map is the prefix map
transported by `outerSucc_castDart`. -/
theorem kmswPeanoPrefixClimbLeftFreshDartMap_old
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P
        (outerSucc_castDart
          (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
            (Nat.le_succ j)) d) =
      P.emb.dartMap d := by
  simp [kmswPeanoPrefixClimbLeftFreshDartMap, outerSucc_castDart]

/-- In the existing-predecessor candidate map, both darts of the newly
allocated active edge receive `b` and `edgeInv b`. -/
theorem kmswPeanoPrefixClimbLeftExistingDartMap_new
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d =
      if d.2 then
        B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)
      else peanoEdge B ⟨j + 1, hj1⟩ := by
  simp [kmswPeanoPrefixClimbLeftExistingDartMap, hd]

/-- Existing old images cannot have the next Peano index in a climb. -/
theorem kmswPeanoPrefixClimb_old_index_ne_succ
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P)
    (d : StageDart (kmswStage (codeExtend c) j).nextEdge) :
    (peanoIndex B (P.emb.dartMap d)).val ≠ j + 1 := by
  by_cases hp : (kmswStage (codeExtend c) j).present d.1.val = true
  · have hle := (P.present_prefix d).1 hp
    omega
  · have hf : (kmswStage (codeExtend c) j).present d.1.val = false := by
      cases h : (kmswStage (codeExtend c) j).present d.1.val <;> simp_all
    exact hno d hf

private theorem kmswPeanoPrefixClimbLeftExistingDartMap_oldAt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val < (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d =
      P.emb.dartMap ((⟨d.1.val, hd⟩, d.2) :
        StageDart (kmswStage (codeExtend c) j).nextEdge) := by
  let oldD : StageDart (kmswStage (codeExtend c) j).nextEdge :=
    (⟨d.1.val, hd⟩, d.2)
  have hcast : outerSucc_castDart
      (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
        (Nat.le_succ j)) oldD = d := by
    rcases d with ⟨⟨f, hf⟩, side⟩
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  calc
    kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d =
        kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
          (outerSucc_castDart
            (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
              (Nat.le_succ j)) oldD) := congrArg _ hcast.symm
    _ = P.emb.dartMap oldD :=
      kmswPeanoPrefixClimbLeftExistingDartMap_old B c j hj hj1 P oldD

private theorem kmswPeanoPrefixClimbLeftExistingDartMap_new_index
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge) :
    (peanoIndex B
      (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d)).val = j + 1 := by
  rw [kmswPeanoPrefixClimbLeftExistingDartMap_new B c j hj hj1 P d hd]
  cases d.2 <;> simp [peanoIndex_edgeInv, peanoIndex_peanoEdge]

/-- The existing-predecessor candidate dart map is injective assuming the
explicit old-frontier collision exclusion. The current prefix invariant alone
only places old missing darts strictly after `j`, so it does not exclude
collision with index `j+1`. Helper toward thm-kmsw
paper result. -/
theorem kmswPeanoPrefixClimbLeftExistingDartMap_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hcode : codeExtend c j = 0)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es)
    (hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P) :
    Function.Injective (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P) := by
  classical
  let s := kmswStage (codeExtend c) j
  let t := kmswStage (codeExtend c) (j + 1)
  have hsize : t.nextEdge = s.nextEdge + 1 :=
    kmswStage_step_leftExisting_facts (codeExtend c) j e es hcode hUL |>.1
  intro d f hdf
  by_cases hd : d.1.val < s.nextEdge
  · by_cases hf : f.1.val < s.nextEdge
    · rw [kmswPeanoPrefixClimbLeftExistingDartMap_oldAt
        B c j hj hj1 P d hd,
      kmswPeanoPrefixClimbLeftExistingDartMap_oldAt B c j hj hj1 P f hf] at hdf
      have hsource := P.emb.injective hdf
      have hval := congrArg (fun x : StageDart s.nextEdge => x.1.val) hsource
      have hside := congrArg Prod.snd hsource
      exact Prod.ext (Fin.ext hval) hside
    · have hfnew : f.1.val = s.nextEdge := by
        have hbound : f.1.val < t.nextEdge := f.1.isLt
        have hbound' : f.1.val < s.nextEdge + 1 := by
          simpa only [hsize] using hbound
        omega
      have hidxd := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno
        ((⟨d.1.val, hd⟩, d.2) : StageDart s.nextEdge)
      have hidxf := kmswPeanoPrefixClimbLeftExistingDartMap_new_index
        B c j hj hj1 P f hfnew
      have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
      rw [kmswPeanoPrefixClimbLeftExistingDartMap_oldAt B c j hj hj1 P d hd] at heq
      exact (hidxd (heq.trans hidxf)).elim
  · by_cases hf : f.1.val < s.nextEdge
    · have hdnew : d.1.val = s.nextEdge := by
        have hbound : d.1.val < t.nextEdge := d.1.isLt
        have hbound' : d.1.val < s.nextEdge + 1 := by
          simpa only [hsize] using hbound
        omega
      have hidxf := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno
        ((⟨f.1.val, hf⟩, f.2) : StageDart s.nextEdge)
      have hidxd := kmswPeanoPrefixClimbLeftExistingDartMap_new_index
        B c j hj hj1 P d hdnew
      have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
      rw [kmswPeanoPrefixClimbLeftExistingDartMap_oldAt B c j hj hj1 P f hf] at heq
      exact (hidxf (heq.symm.trans hidxd)).elim
    · have hdnew : d.1.val = s.nextEdge := by
        have hbound : d.1.val < t.nextEdge := d.1.isLt
        have hbound' : d.1.val < s.nextEdge + 1 := by
          simpa only [hsize] using hbound
        omega
      have hfnew : f.1.val = s.nextEdge := by
        have hbound : f.1.val < t.nextEdge := f.1.isLt
        have hbound' : f.1.val < s.nextEdge + 1 := by
          simpa only [hsize] using hbound
        omega
      rw [kmswPeanoPrefixClimbLeftExistingDartMap_new
          B c j hj hj1 P d hdnew,
        kmswPeanoPrefixClimbLeftExistingDartMap_new
          B c j hj hj1 P f hfnew] at hdf
      cases hds : d.2 <;> cases hfs : f.2 <;>
        simp only [hds, hfs, Bool.false_eq_true,
          ↓reduceIte] at hdf
      · exact Prod.ext (Fin.ext (hdnew.trans hfnew.symm)) (hds.trans hfs.symm)
      · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf.symm).elim
      · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf).elim
      · exact Prod.ext (Fin.ext (hdnew.trans hfnew.symm)) (hds.trans hfs.symm)

/-- In the fresh-left candidate map, the new active edge receives `b` and
`edgeInv b`. -/
theorem kmswPeanoPrefixClimbLeftFreshDartMap_newActive
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d =
      if d.2 then
        B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)
      else peanoEdge B ⟨j + 1, hj1⟩ := by
  simp [kmswPeanoPrefixClimbLeftFreshDartMap, hd]

/-- In the fresh-left candidate map, the newly allocated missing LL edge is
mapped west-to-east to `edgeInv (rot a)`; its reverse maps to `rot a`. -/
theorem kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge + 1) :
    kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d =
      if d.2 then
        B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, by omega⟩)
      else
        B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, by omega⟩)) := by
  simp [kmswPeanoPrefixClimbLeftFreshDartMap, hd]

private theorem kmswPeanoPrefixClimbLeftFreshDartMap_oldAt
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val < (kmswStage (codeExtend c) j).nextEdge) :
    kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d =
      P.emb.dartMap ((⟨d.1.val, hd⟩, d.2) :
        StageDart (kmswStage (codeExtend c) j).nextEdge) := by
  let oldD : StageDart (kmswStage (codeExtend c) j).nextEdge :=
    (⟨d.1.val, hd⟩, d.2)
  have hcast : outerSucc_castDart
      (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
        (Nat.le_succ j)) oldD = d := by
    rcases d with ⟨⟨f, hf⟩, side⟩
    apply Prod.ext
    · exact Fin.ext rfl
    · rfl
  calc
    kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d =
        kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P
          (outerSucc_castDart
            (kmswStage_nextEdge_mono (codeExtend c) (m := j) (n := j + 1)
              (Nat.le_succ j)) oldD) := congrArg _ hcast.symm
    _ = P.emb.dartMap oldD :=
      kmswPeanoPrefixClimbLeftFreshDartMap_old B c j hj hj1 P oldD

private theorem kmswPeanoPrefixClimbLeftFreshDartMap_newActive_index
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge) :
    (peanoIndex B
      (kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d)).val = j + 1 := by
  rw [kmswPeanoPrefixClimbLeftFreshDartMap_newActive B c j hj hj1 P d hd]
  cases d.2 <;> simp [peanoIndex_edgeInv, peanoIndex_peanoEdge]

private theorem kmswPeanoPrefixClimbLeftFreshDartMap_newLL_index_future
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = [])
    (d : StageDart (kmswStage (codeExtend c) (j + 1)).nextEdge)
    (hd : d.1.val = (kmswStage (codeExtend c) j).nextEdge + 1) :
    j + 1 < (peanoIndex B
      (kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P d)).val := by
  let s := kmswStage (codeExtend c) j
  let a := peanoEdge B ⟨j, by omega⟩
  have hq := (hfrontier.2.2 hUL).2
  have hrot : j + 1 <
      (peanoIndex B (B.map.toCombinatorialMap.rot a)).val := by
    have heq := congrArg Fin.val
      (peanoIndex_edgeInv B (B.map.toCombinatorialMap.rot a))
    exact heq ▸ hq
  rw [kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL B c j hj hj1 P d hd]
  cases d.2 <;> simpa [peanoIndex_edgeInv] using hrot

/-- The fresh-left candidate dart map is injective assuming the two explicit
frontier facts: the old image avoids index `j+1`, and the new missing LL edge
is beyond that index and outside the old image. These are additional
induction information, not consequences of `KMSWPeanoPrefixEmbedding` alone. -/
theorem kmswPeanoPrefixClimbLeftFreshDartMap_injective
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hcode : codeExtend c j = 0)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = [])
    (hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P)
    (hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P) :
    Function.Injective (kmswPeanoPrefixClimbLeftFreshDartMap B c j hj hj1 P) := by
  classical
  let s := kmswStage (codeExtend c) j
  let t := kmswStage (codeExtend c) (j + 1)
  have hsize : t.nextEdge = s.nextEdge + 2 :=
    kmswStage_step_leftFresh_facts (codeExtend c) j hcode hUL |>.1
  have hqnot := (hfrontier.2.2 hUL).1
  have hrotNot : B.map.toCombinatorialMap.rot
      (peanoEdge B ⟨j, by omega⟩) ∉ Set.range P.emb.dartMap := by
    intro hmem
    apply hqnot
    obtain ⟨d, hd⟩ := hmem
    refine ⟨edgeFlip _ d, ?_⟩
    calc
      P.emb.dartMap (edgeFlip _ d) = B.map.toCombinatorialMap.edgeInv
          (P.emb.dartMap d) := P.emb.flip_comm d
      _ = B.map.toCombinatorialMap.edgeInv
          (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, by omega⟩)) :=
        congrArg B.map.toCombinatorialMap.edgeInv hd
  intro d f hdf
  by_cases hd : d.1.val < s.nextEdge
  · by_cases hf : f.1.val < s.nextEdge
    · rw [kmswPeanoPrefixClimbLeftFreshDartMap_oldAt
        B c j hj hj1 P d hd,
      kmswPeanoPrefixClimbLeftFreshDartMap_oldAt B c j hj hj1 P f hf] at hdf
      have hsource := P.emb.injective hdf
      have hval := congrArg (fun x : StageDart s.nextEdge => x.1.val) hsource
      have hside := congrArg Prod.snd hsource
      exact Prod.ext (Fin.ext hval) hside
    · have hbound : f.1.val < t.nextEdge := f.1.isLt
      have hbound' : f.1.val < s.nextEdge + 2 := by
        simpa only [hsize] using hbound
      have hfge : s.nextEdge ≤ f.1.val := Nat.le_of_not_gt hf
      by_cases hfact : f.1.val = s.nextEdge
      · have hidxd := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno
          ((⟨d.1.val, hd⟩, d.2) : StageDart s.nextEdge)
        have hidxf := kmswPeanoPrefixClimbLeftFreshDartMap_newActive_index
          B c j hj hj1 P f hfact
        have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
        rw [kmswPeanoPrefixClimbLeftFreshDartMap_oldAt B c j hj hj1 P d hd] at heq
        exact (hidxd (heq.trans hidxf)).elim
      · have hfLL : f.1.val = s.nextEdge + 1 := by omega
        have hnew := kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL
          B c j hj hj1 P f hfLL
        rw [kmswPeanoPrefixClimbLeftFreshDartMap_oldAt
          B c j hj hj1 P d hd, hnew] at hdf
        by_cases hside : f.2
        · simp [hside] at hdf
          exact False.elim (hrotNot ⟨(⟨d.1.val, hd⟩, d.2), hdf⟩)
        · simp [hside] at hdf
          exact False.elim (hqnot ⟨(⟨d.1.val, hd⟩, d.2), hdf⟩)
  · by_cases hf : f.1.val < s.nextEdge
    · have hbound : d.1.val < t.nextEdge := d.1.isLt
      have hbound' : d.1.val < s.nextEdge + 2 := by
        simpa only [hsize] using hbound
      have hdge : s.nextEdge ≤ d.1.val := Nat.le_of_not_gt hd
      by_cases hfact : d.1.val = s.nextEdge
      · have hidxf := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno
          ((⟨f.1.val, hf⟩, f.2) : StageDart s.nextEdge)
        have hidxd := kmswPeanoPrefixClimbLeftFreshDartMap_newActive_index
          B c j hj hj1 P d hfact
        have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
        rw [kmswPeanoPrefixClimbLeftFreshDartMap_oldAt B c j hj hj1 P f hf] at heq
        exact (hidxf (heq.symm.trans hidxd)).elim
      · have hdLL : d.1.val = s.nextEdge + 1 := by omega
        have hnew := kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL
          B c j hj hj1 P d hdLL
        rw [hnew, kmswPeanoPrefixClimbLeftFreshDartMap_oldAt
          B c j hj hj1 P f hf] at hdf
        by_cases hside : d.2
        · simp [hside] at hdf
          exact False.elim (hrotNot ⟨(⟨f.1.val, hf⟩, f.2), hdf.symm⟩)
        · simp [hside] at hdf
          exact False.elim (hqnot ⟨(⟨f.1.val, hf⟩, f.2), hdf.symm⟩)
    · have hboundD : d.1.val < t.nextEdge := d.1.isLt
      have hboundD' : d.1.val < s.nextEdge + 2 := by
        simpa only [hsize] using hboundD
      have hboundF : f.1.val < t.nextEdge := f.1.isLt
      have hboundF' : f.1.val < s.nextEdge + 2 := by
        simpa only [hsize] using hboundF
      have hdge : s.nextEdge ≤ d.1.val := Nat.le_of_not_gt hd
      have hfge : s.nextEdge ≤ f.1.val := Nat.le_of_not_gt hf
      by_cases hDactive : d.1.val = s.nextEdge
      · have hDidx := kmswPeanoPrefixClimbLeftFreshDartMap_newActive_index
          B c j hj hj1 P d hDactive
        by_cases hFactive : f.1.val = s.nextEdge
        · rw [kmswPeanoPrefixClimbLeftFreshDartMap_newActive
            B c j hj hj1 P d hDactive,
          kmswPeanoPrefixClimbLeftFreshDartMap_newActive
            B c j hj hj1 P f hFactive] at hdf
          cases hds : d.2 <;> cases hfs : f.2 <;>
            simp only [hds, hfs, Bool.false_eq_true, ↓reduceIte] at hdf
          · exact Prod.ext (Fin.ext (hDactive.trans hFactive.symm))
              (hds.trans hfs.symm)
          · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf.symm).elim
          · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf).elim
          · exact Prod.ext (Fin.ext (hDactive.trans hFactive.symm))
              (hds.trans hfs.symm)
        · have hFLL : f.1.val = s.nextEdge + 1 := by omega
          have hFidx := kmswPeanoPrefixClimbLeftFreshDartMap_newLL_index_future
            B c j hj hj1 P hfrontier hUL f hFLL
          have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
          have hfalse : False := by rw [hDidx] at heq; omega
          exact False.elim hfalse
      · have hDLL : d.1.val = s.nextEdge + 1 := by omega
        by_cases hFactive : f.1.val = s.nextEdge
        · have hDidx := kmswPeanoPrefixClimbLeftFreshDartMap_newLL_index_future
            B c j hj hj1 P hfrontier hUL d hDLL
          have hFidx := kmswPeanoPrefixClimbLeftFreshDartMap_newActive_index
            B c j hj hj1 P f hFactive
          have heq := congrArg (fun x : D => (peanoIndex B x).val) hdf
          have hfalse : False := by rw [hFidx] at heq; omega
          exact False.elim hfalse
        · have hFLL : f.1.val = s.nextEdge + 1 := by omega
          have hDidx := kmswPeanoPrefixClimbLeftFreshDartMap_newLL_index_future
            B c j hj hj1 P hfrontier hUL d hDLL
          have hFidx := kmswPeanoPrefixClimbLeftFreshDartMap_newLL_index_future
            B c j hj hj1 P hfrontier hUL f hFLL
          rw [kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL
              B c j hj hj1 P d hDLL,
            kmswPeanoPrefixClimbLeftFreshDartMap_newMissingLL
              B c j hj hj1 P f hFLL] at hdf
          cases hds : d.2 <;> cases hfs : f.2 <;>
            simp only [hds, hfs, Bool.false_eq_true, ↓reduceIte] at hdf
          · exact Prod.ext (Fin.ext (hDLL.trans hFLL.symm)) (hds.trans hfs.symm)
          · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf).elim
          · exact (B.map.toCombinatorialMap.edgeInv_ne _ hdf.symm).elim
          · exact Prod.ext (Fin.ext (hDLL.trans hFLL.symm)) (hds.trans hfs.symm)

/-- Cast stage darts along an equality of edge bounds.
not the paper result. -/
@[expose] def climbCastEquiv {k l : ℕ} (h : k = l) : StageDart k ≃ StageDart l :=
  Equiv.prodCongr (finCongr h) (Equiv.refl Bool)

/-- Express stage rotation resizing through the corresponding dart cast. -/
theorem climb_resize_eq {k l : ℕ} (h : k = l)
    (σ : Equiv.Perm (StageDart k)) :
    StageRotation.resize h σ = (climbCastEquiv h).permCongr σ := by
  cases h
  rfl

/-- Rotation iterates preserve the tail vertex. -/
theorem climb_rot_vertex (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (d : D) (k : ℕ) :
    dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) =
      dartTailVertex B.map d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (show dartTailVertex B.map
        (B.map.toCombinatorialMap.rot
          ((B.map.toCombinatorialMap.rot : D → D)^[k] d)) =
      dartTailVertex B.map ((B.map.toCombinatorialMap.rot : D → D)^[k] d) from by
        apply Quotient.sound
        exact (Equiv.Perm.SameCycle.refl B.map.toCombinatorialMap.rot _).apply_left).trans ih

/-- Recover the predecessor of an iterate from its successor image. -/
theorem climb_iterate_prev {β : Type*} (ρ : Equiv.Perm β) (x q y : β)
    (m : ℕ) (hm : 0 < m) (hnext : ρ q = y)
    (hpow : (ρ : β → β)^[m] x = y) :
    (ρ : β → β)^[m - 1] x = q := by
  apply ρ.injective.iterate 1
  rw [← Function.iterate_add_apply, Nat.add_sub_of_le (by omega),
    Function.iterate_one, hpow, hnext]

/- Corner gap for an existing-predecessor climb. On each unaffected old
rotation interval, neither of the two newly inserted image darts lies strictly
between the old dart and its old FIRST return (minimal `k`). The return must be
the first return: the earlier all-returns version was vacuous on affected
the current prefix invariant. Helper toward thm-kmsw -/
@[expose] def KMSWPeanoClimbCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (p A : StageDart (kmswStage (codeExtend c) j).nextEdge) : Prop :=
  ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    d ≠ p → stageRot (codeExtend c) j d ≠ A →
      ∀ k : ℕ, 0 < k →
        (B.map.toCombinatorialMap.rot : D → D)^[k] (P.emb.dartMap d) =
          P.emb.dartMap (stageRot (codeExtend c) j d) →
        (∀ m : ℕ, 0 < m → m < k →
          (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ∉
            Set.range P.emb.dartMap) →
        ∀ m : ℕ, 0 < m → m < k →
          (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              peanoEdge B ⟨j + 1, hj1⟩ ∧
            (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)

private theorem KMSWPeanoClimbCorner_of_allReturns
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (p A : StageDart (kmswStage (codeExtend c) j).nextEdge)
    (hall : ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
      d ≠ p → stageRot (codeExtend c) j d ≠ A →
        ∀ k : ℕ, 0 < k →
          (B.map.toCombinatorialMap.rot : D → D)^[k] (P.emb.dartMap d) =
            P.emb.dartMap (stageRot (codeExtend c) j d) →
          ∀ m : ℕ, 0 < m → m < k →
            (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
                peanoEdge B ⟨j + 1, hj1⟩ ∧
              (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
                B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩)) :
    KMSWPeanoClimbCorner B c j hj P hj1 p A := by
  intro d hdp hsucc k hk hret hfirst m hm hmk
  exact hall d hdp hsucc k hk hret m hm hmk

/- Corner gap for a fresh-vertex climb. For each unaffected old dart, none of
the four new image darts lies strictly between its old image and its old FIRST
return (minimal `k`). The return must be the first return: the earlier
images are the new Peano edge, its reverse, `rot a`, and `edgeInv (rot a)`.
This local fact is not part of the current prefix invariant. Helper toward -/
@[expose] def KMSWPeanoClimbFreshCorner
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (a A : StageDart (kmswStage (codeExtend c) j).nextEdge) : Prop :=
  ∀ d : StageDart (kmswStage (codeExtend c) j).nextEdge,
    d ≠ a → stageRot (codeExtend c) j d ≠ A →
      ∀ k : ℕ, 0 < k →
        (B.map.toCombinatorialMap.rot : D → D)^[k] (P.emb.dartMap d) =
          P.emb.dartMap (stageRot (codeExtend c) j d) →
        (∀ m : ℕ, 0 < m → m < k →
          (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ∉
            Set.range P.emb.dartMap) →
        ∀ m : ℕ, 0 < m → m < k →
          (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              peanoEdge B ⟨j + 1, hj1⟩ ∧
            (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              B.map.toCombinatorialMap.edgeInv (peanoEdge B ⟨j + 1, hj1⟩) ∧
            (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩) ∧
            (B.map.toCombinatorialMap.rot : D → D)^[m] (P.emb.dartMap d) ≠
              B.map.toCombinatorialMap.edgeInv
                (B.map.toCombinatorialMap.rot (peanoEdge B ⟨j, hj⟩))

/-- Extend the prefix through an existing upper-left predecessor in a climb.
The new Peano dart is inserted at the upper-left corner and its reverse at the
head corner of the old active dart. The explicit corner hypothesis supplies
the first-return gaps for unaffected old darts. -/
@[expose] noncomputable def kmswPeanoPrefixEmbedding_climb_leftExisting
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 0)
    (hkind : peanoStepKind B j hj1 = .climb)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es)
    (hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P)
    (hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P)
    (hcorner : KMSWPeanoClimbCorner B c j hj P hj1
      ((⟨e, (stageRotation_UL_bound (codeExtend c) j) e
        (List.mem_of_mem_dropLast (List.mem_reverse.mp (by
          rw [hUL]
          exact List.mem_cons_self)))⟩, false))
      ((⟨(kmswStage (codeExtend c) j).active,
        act_lt_nextEdge (codeExtend c) (le_refl j)⟩, true))) :
    KMSWPeanoPrefixEmbedding B c (j + 1) hj1 := by
  classical
  let u := codeExtend c
  let s := kmswStage u j
  let t := kmswStage u (j + 1)
  let a := peanoEdge B ⟨j, by omega⟩
  let b := peanoEdge B ⟨j + 1, hj1⟩
  let z := B.map.toCombinatorialMap.edgeInv b
  have hULs : s.UL.dropLast.reverse = e :: es := by simpa [s, u] using hUL
  have heUL : e ∈ s.UL :=
    List.mem_of_mem_dropLast (List.mem_reverse.mp (by rw [hULs]; exact List.mem_cons_self))
  have he : e < s.nextEdge := (stageRotation_UL_bound u j) e heUL
  let p : StageDart s.nextEdge := (⟨e, he⟩, false)
  let A : StageDart s.nextEdge :=
    (⟨s.active, act_lt_nextEdge u (le_refl j)⟩, true)
  have facts := kmswStage_step_leftExisting_facts u j e es hcode hUL
  have hs : t.nextEdge = s.nextEdge + 1 := facts.1
  let Q : StageDart t.nextEdge ≃ StageDart s.nextEdge ⊕ StageDart 1 :=
    (climbCastEquiv hs).trans (StageRotation.allocation s.nextEdge 1).symm
  let f : StageDart s.nextEdge ⊕ StageDart 1 → D :=
    Sum.elim P.emb.dartMap (fun d => if d.2 then z else b)
  have old_val (d : StageDart s.nextEdge) :
      ((Q.symm (.inl d)).1.val, (Q.symm (.inl d)).2) = (d.1.val, d.2) := rfl
  have new_val (v : Bool) :
      ((Q.symm (.inr (0, v))).1.val, (Q.symm (.inr (0, v))).2) =
        (s.nextEdge, v) := by
    simp only [Q, Equiv.symm_trans_apply, Equiv.symm_symm,
      StageRotation.allocation_new]
    rfl
  have fin1 (d : StageDart 1) : d = (0, d.2) := by
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hmap_old (d : StageDart s.nextEdge) :
      kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
        (Q.symm (.inl d)) = P.emb.dartMap d := by
    have hcast : outerSucc_castDart
        (kmswStage_nextEdge_mono u (m := j) (n := j + 1) (Nat.le_succ j)) d =
          Q.symm (.inl d) := by
      apply Prod.ext
      · exact Fin.ext rfl
      · rfl
    rw [← hcast]
    exact kmswPeanoPrefixClimbLeftExistingDartMap_old B c j hj hj1 P d
  have hmap_new (v : Bool) :
      kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
        (Q.symm (.inr (0, v))) = if v then z else b := by
    have hv : (Q.symm (.inr (0, v))).1.val = s.nextEdge :=
      congrArg Prod.fst (new_val v)
    have hside : (Q.symm (.inr (0, v))).2 = v := congrArg Prod.snd (new_val v)
    have hh := kmswPeanoPrefixClimbLeftExistingDartMap_new
      B c j hj hj1 P (Q.symm (.inr (0, v))) hv
    simpa only [hside, z] using hh
  have hmap (d : StageDart s.nextEdge ⊕ StageDart 1) :
      kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P (Q.symm d) = f d := by
    cases d with
    | inl d => exact hmap_old d
    | inr d =>
      rw [fin1 d]
      exact hmap_new d.2
  have hfront : P.emb.dartMap p = B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.rot a) := by
    obtain ⟨he', _hp, hmap⟩ := hfrontier.1 e es hULs
    have hpeq : p = ((⟨e, he'⟩, false) : StageDart s.nextEdge) := by
      apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    rw [hpeq]
    simpa only [a] using hmap
  have hcfg := peanoStepKind_config B j hj1
  rw [hkind] at hcfg
  let _hs := Classical.choose hcfg
  have hcfg' := Classical.choose_spec hcfg
  have hhead : dartHeadVertex B.map b = dartHeadVertex B.map a := hcfg'.2.2.1
  have hbconfig : b = B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.faceSucc a) := hcfg'.2.2.2.2.2.1
  have hface := hcfg'.2.2.2.2.2.2.1
  have hrotq : B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) = b := by
    have hh : B.map.toCombinatorialMap.rot.symm
        (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a)) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a) := by
      change B.map.toCombinatorialMap.faceSucc (B.map.toCombinatorialMap.faceSucc a) = _ at hface
      exact hface
    have hh' := congrArg B.map.toCombinatorialMap.rot hh
    have hrotq' : B.map.toCombinatorialMap.rot
        (B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.rot a)) =
          B.map.toCombinatorialMap.edgeInv (B.map.toCombinatorialMap.faceSucc a) := by
      simpa only [Equiv.apply_symm_apply] using hh'.symm
    exact hrotq'.trans hbconfig.symm
  have hrotpb : (B.map.toCombinatorialMap.rot : D → D) (P.emb.dartMap p) = b := by
    rw [hfront, hrotq]
  have hbconfig' : b = B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.faceSucc a) := hbconfig
  have hrotz : B.map.toCombinatorialMap.rot z =
      B.map.toCombinatorialMap.edgeInv a := by
    rw [show z = B.map.toCombinatorialMap.faceSucc a by
      dsimp [z]
      rw [hbconfig']
      exact B.map.toCombinatorialMap.edgeInv_invol _]
    change B.map.toCombinatorialMap.rot
      (B.map.toCombinatorialMap.rot.symm (B.map.toCombinatorialMap.edgeInv a)) = _
    simp only [Equiv.apply_symm_apply]
  have hA : P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv a := by
    have hh := P.emb.flip_comm (kmswRootedStage u j).root
    change P.emb.dartMap A = B.map.toCombinatorialMap.edgeInv
      (P.emb.dartMap (kmswRootedStage u j).root) at hh
    exact hh.trans (congrArg B.map.toCombinatorialMap.edgeInv P.emb.root_comm)
  have hq : f (.inl p) = B.map.toCombinatorialMap.edgeInv
      (B.map.toCombinatorialMap.rot a) := by
    exact hfront
  have hnewnot : b ∉ Set.range P.emb.dartMap ∧ z ∉ Set.range P.emb.dartMap := by
    have hbnot : b ∉ Set.range P.emb.dartMap := by
      rintro ⟨d, hd⟩
      have hi := congrArg (fun x : D => (peanoIndex B x).val) hd
      have hp := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno d
      have hidxb : (peanoIndex B b).val = j + 1 := by
        simp only [b, peanoIndex_peanoEdge]
      exact hp (hi.trans hidxb)
    have hznot : z ∉ Set.range P.emb.dartMap := by
      rintro ⟨d, hd⟩
      have hi := congrArg (fun x : D => (peanoIndex B x).val) hd
      have hp := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno d
      have hidxz : (peanoIndex B z).val = j + 1 := by
        simp only [z, peanoIndex_edgeInv, b, peanoIndex_peanoEdge]
      exact hp (hi.trans hidxz)
    exact ⟨hbnot, hznot⟩
  have hdiff : dartTailVertex B.map b ≠ dartTailVertex B.map z := by
    simpa only [z] using peano_dart_no_loop B b
  have hqvertex : dartTailVertex B.map (P.emb.dartMap p) =
      dartTailVertex B.map b := by
    rw [hfront]
    exact peanoClimb_edgeInv_rot_tail_eq_next B j hj1 hkind
  have hAvertex : dartTailVertex B.map (P.emb.dartMap A) =
      dartHeadVertex B.map a := by
    rw [hA]
    rfl
  let σ := stageRot u j
  let ρ := B.map.toCombinatorialMap.rot
  let τ : Equiv.Perm (StageDart s.nextEdge ⊕ StageDart 1) :=
    StageRotation.pairSplice σ (Equiv.refl _) p A (0, false) (0, true)
  have τold (d : StageDart s.nextEdge) :
      τ (.inl d) = if d = p then .inr (0, false)
        else if σ d = A then .inr (0, true) else .inl (σ d) := by
    by_cases hdp : d = p <;> by_cases hA' : σ d = A <;>
      simp [τ, StageRotation.pairSplice, insertBefore, insertAfter,
        Equiv.swap_apply_def, hdp, hA']
  have τnew : τ (.inr (0, false)) =
      (if σ p = A then .inr (0, true) else .inl (σ p)) ∧
      τ (.inr (0, true)) = .inl A := by
    constructor
    · by_cases h : σ p = A <;>
        simp [τ, StageRotation.pairSplice, insertBefore, insertAfter,
          Equiv.swap_apply_def, h]
    · simp [τ, StageRotation.pairSplice, insertBefore, insertAfter,
        Equiv.swap_apply_def]
  have hrot (d : StageDart s.nextEdge ⊕ StageDart 1) :
      Q (stageRot u (j + 1) (Q.symm d)) = τ d := by
    have hc : kmswCodeStep (u j) = .left := by
      change kmswCodeStep (codeExtend c j) = .left
      rw [hcode]
      rfl
    have hr := StageRotation.step_leftExisting s
      (act_lt_nextEdge u (le_refl j)) (stageRotation_UL_bound u j) σ (u j)
      hc e es hUL
    have hr' : StageRotation.resize hs (stageRot u (j + 1)) =
        StageRotation.leftExisting s.nextEdge σ p A := by
      rw [stageRot_succ]
      exact hr
    rw [climb_resize_eq] at hr'
    change (climbCastEquiv hs).permCongr (stageRot u (j + 1)) =
      (StageRotation.allocation s.nextEdge 1).permCongr τ at hr'
    have hh := congrArg (fun π : Equiv.Perm (StageDart (s.nextEdge + 1)) =>
      (StageRotation.allocation s.nextEdge 1).symm
        (π (StageRotation.allocation s.nextEdge 1 d))) hr'
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Q,
      Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm] using hh
  have hfinduced (d : StageDart s.nextEdge ⊕ StageDart 1) :
      ∃ k : ℕ, 0 < k ∧ (ρ : D → D)^[k] (f d) = f (τ d) ∧
        ∀ m : ℕ, 0 < m → m < k → (ρ : D → D)^[m] (f d) ∉ Set.range f := by
    cases d with
    | inr d =>
      rcases d with ⟨ed, v⟩
      obtain rfl : ed = 0 := Subsingleton.elim _ _
      cases v with
      | false =>
        obtain ⟨k, hk, hret, hmin⟩ := P.emb.rot_induced p
        have hret' : (ρ : D → D)^[k] (P.emb.dartMap p) =
            P.emb.dartMap (σ p) := by
          change (ρ : D → D)^[k] (P.emb.dartMap p) =
            P.emb.dartMap (stageRot u j p)
          exact hret
        have hminρ : ∀ m : ℕ, 0 < m → m < k →
            (ρ : D → D)^[m] (P.emb.dartMap p) ∉ Set.range P.emb.dartMap := by
          intro m hm hmk hmem
          apply hmin m hm hmk
          change ((baseRootedAt B a (peanoEdge_forward B ⟨j, hj⟩)).map.rot : D → D)^[m]
              (P.emb.dartMap p) ∈ Set.range P.emb.dartMap at hmem
          exact hmem
        have hpA : σ p ≠ A := by
          intro h
          have hretA : (ρ : D → D)^[k] (P.emb.dartMap p) = P.emb.dartMap A := by
            simpa only [h] using hret'
          have hv := (climb_rot_vertex B (P.emb.dartMap p) k).symm.trans
            (congrArg (dartTailVertex B.map) hretA)
          rw [hqvertex, hAvertex, ← hhead] at hv
          exact (peano_dart_no_loop B b) hv
        have hnewret : (ρ : D → D)^[k - 1] b = P.emb.dartMap (σ p) := by
          have hkEq : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
          calc
            (ρ : D → D)^[k - 1] b =
                (ρ : D → D)^[k - 1] (ρ (P.emb.dartMap p)) := by
              rw [hrotpb]
            _ = (ρ : D → D)^[(k - 1) + 1] (P.emb.dartMap p) := by
              rw [← Function.iterate_succ_apply]
            _ = (ρ : D → D)^[k] (P.emb.dartMap p) := by rw [hkEq]
            _ = P.emb.dartMap (σ p) := hret'
        have hkgt : 1 < k := by
          by_contra hle
          have hk1 : k = 1 := by omega
          have hz : b = P.emb.dartMap (σ p) := by
            simpa only [hk1, Nat.sub_self, Function.iterate_zero_apply] using hnewret
          exact hnewnot.1 ⟨σ p, hz.symm⟩
        refine ⟨k - 1, by omega, ?_, ?_⟩
        · rw [τnew.1, ite_eq_right hpA]
          exact hnewret
        · intro m hm hmk hmem
          obtain ⟨x, hx⟩ := hmem
          cases x with
          | inl x =>
            have hshift : (ρ : D → D)^[m + 1] (P.emb.dartMap p) =
                (ρ : D → D)^[m] b := by
              calc
                (ρ : D → D)^[m + 1] (P.emb.dartMap p) =
                    (ρ : D → D)^[m] (ρ (P.emb.dartMap p)) := by
                  rw [Function.iterate_succ_apply]
                _ = (ρ : D → D)^[m] b := by rw [hrotpb]
            have hx' : P.emb.dartMap x =
                (ρ : D → D)^[m + 1] (P.emb.dartMap p) :=
              hx.trans hshift.symm
            exact hminρ (m + 1) (by omega) (by omega) ⟨x, hx'⟩
          | inr x =>
            rcases x with ⟨ex, side⟩
            obtain rfl : ex = 0 := Subsingleton.elim _ _
            cases side with
            | false =>
              have hprev := climb_iterate_prev ρ b
                (P.emb.dartMap p) b m hm hrotpb hx.symm
              by_cases hm1 : m = 1
              · have hbp : b = P.emb.dartMap p := by
                  simpa only [hm1, Nat.sub_self, Function.iterate_zero_apply] using hprev
                exact hnewnot.1 ⟨p, hbp.symm⟩
              · have hmEq : (m - 1) + 1 = m := Nat.sub_add_cancel (by omega)
                have hloop : (ρ : D → D)^[m] (P.emb.dartMap p) = P.emb.dartMap p := by
                  calc
                    (ρ : D → D)^[m] (P.emb.dartMap p) =
                        (ρ : D → D)^[(m - 1) + 1] (P.emb.dartMap p) := by rw [hmEq]
                    _ = (ρ : D → D)^[m - 1] (ρ (P.emb.dartMap p)) := by
                      rw [Function.iterate_succ_apply]
                    _ = (ρ : D → D)^[m - 1] b := by rw [hrotpb]
                    _ = P.emb.dartMap p := hprev
                exact hminρ m hm (by omega) ⟨p, hloop.symm⟩
            | true =>
              have hv : dartTailVertex B.map b = dartTailVertex B.map z := by
                calc
                  dartTailVertex B.map b =
                      dartTailVertex B.map ((ρ : D → D)^[m] b) :=
                    (climb_rot_vertex B b m).symm
                  _ = dartTailVertex B.map z := congrArg (dartTailVertex B.map) hx.symm
              exact hdiff hv
      | true =>
        refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
        · rw [τnew.2]
          change ρ z = P.emb.dartMap A
          rw [hrotz, hA]
        · intro m hm hmk
          omega
    | inl d =>
      obtain ⟨k, hk, hret, hmin⟩ := P.emb.rot_induced d
      have hminB : ∀ m : ℕ, 0 < m → m < k →
          (ρ : D → D)^[m] (P.emb.dartMap d) ∉ Set.range P.emb.dartMap := by
        intro m hm hmk hmem
        apply hmin m hm hmk
        change ((baseRootedAt B a (peanoEdge_forward B ⟨j, hj⟩)).map.rot : D → D)^[m]
            (P.emb.dartMap d) ∈ Set.range P.emb.dartMap at hmem
        exact hmem
      have hretB : (ρ : D → D)^[k] (P.emb.dartMap d) = P.emb.dartMap (σ d) := by
        change (ρ : D → D)^[k] (P.emb.dartMap d) = P.emb.dartMap (stageRot u j d) at hret
        exact hret
      by_cases hd : d = p
      · subst d
        refine ⟨1, Nat.zero_lt_one, ?_, ?_⟩
        · rw [τold]
          simp only [↓reduceIte]
          change ρ (P.emb.dartMap p) = b
          exact hrotpb
        · intro m hm hmk
          omega
      · by_cases hsucc : σ d = A
        · have hretA : (ρ : D → D)^[k] (P.emb.dartMap d) =
              P.emb.dartMap A := by
            simpa only [hsucc] using hretB
          have hnextA : ρ z = P.emb.dartMap A := by rw [hrotz, hA]
          have hcut : (ρ : D → D)^[k - 1] (P.emb.dartMap d) = z :=
            climb_iterate_prev ρ (P.emb.dartMap d) z (P.emb.dartMap A)
              k hk hnextA hretA
          have hkgt : 1 < k := by
            by_contra hle
            have hk1 : k = 1 := by omega
            have hcut' : P.emb.dartMap d = z := by
              simpa only [hk1, Nat.sub_self, Function.iterate_zero_apply] using hcut
            exact hnewnot.2 ⟨d, hcut'⟩
          refine ⟨k - 1, by omega, ?_, ?_⟩
          · rw [τold]
            simp only [hd, hsucc, ↓reduceIte]
            exact hcut
          · intro m hm hmk hmem
            obtain ⟨x, hx⟩ := hmem
            cases x with
            | inl x => exact hminB m hm (by omega) ⟨x, hx⟩
            | inr x =>
              rcases x with ⟨ex, side⟩
              obtain rfl : ex = 0 := Subsingleton.elim _ _
              cases side with
              | true =>
                have hpow : (ρ : D → D)^[m + 1] (P.emb.dartMap d) =
                    P.emb.dartMap A := by
                  rw [Nat.add_one, Function.iterate_succ_apply']
                  exact (congrArg ρ hx.symm).trans hnextA
                exact hminB (m + 1) (by omega) (by omega) ⟨A, hpow.symm⟩
              | false =>
                have hprev := climb_iterate_prev ρ (P.emb.dartMap d)
                  (P.emb.dartMap p) b m hm hrotpb hx.symm
                by_cases hm1 : m = 1
                · have hstart : P.emb.dartMap d = P.emb.dartMap p := by
                    simpa only [hm1, Nat.sub_self, Function.iterate_zero_apply] using hprev
                  exact hd (P.emb.injective hstart)
                · have hprevRange : (ρ : D → D)^[m - 1]
                    (P.emb.dartMap d) ∈ Set.range P.emb.dartMap :=
                      ⟨p, hprev.symm⟩
                  exact hminB (m - 1) (by omega) (by omega) hprevRange
        · have hretOld : f (τ (.inl d)) = P.emb.dartMap (σ d) := by
            rw [τold]
            simp only [hd, hsucc, ↓reduceIte]
            rfl
          refine ⟨k, hk, ?_, ?_⟩
          · change (ρ : D → D)^[k] (P.emb.dartMap d) = f (τ (.inl d))
            rw [hretB]
            exact hretOld.symm
          · intro m hm hmk hmem
            obtain ⟨x, hx⟩ := hmem
            cases x with
            | inl x => exact hminB m hm hmk ⟨x, hx⟩
            | inr x =>
              rcases x with ⟨ex, side⟩
              obtain rfl : ex = 0 := Subsingleton.elim _ _
              cases side with
              | false =>
                have hc := hcorner d hd hsucc k hk hret
                  (by intro m hm hmk; exact hminB m hm hmk) m hm hmk
                exact hc.1 hx.symm
              | true =>
                have hc := hcorner d hd hsucc k hk hret
                  (by intro m hm hmk; exact hminB m hm hmk) m hm hmk
                exact hc.2 hx.symm
  have hinj : Function.Injective
      (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P) :=
    kmswPeanoPrefixClimbLeftExistingDartMap_injective
      B c j hj hj1 P hcode e es hUL hno
  have hpres (f₀ : ℕ) : t.present f₀ =
      if f₀ = s.nextEdge then true else s.present f₀ := by
    have hu : u j = 0 := by simpa [u] using hcode
    simp [u, t, s, kmswStage, kmswStep, kmswCodeStep, kmswStepOfStep, hu, hULs,
      State.addEdge]
  have hmapnewFalse : kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
      (Q.symm (.inr (0, false))) = b := by
    simp [hmap_new]
  have hidxold (d : StageDart s.nextEdge) :
      s.present d.1.val = true ↔
        (peanoIndex B (P.emb.dartMap d)).val ≤ j + 1 := by
    constructor
    · intro hp
      have hp' := (P.present_prefix d).1 hp
      omega
    · intro hi
      by_cases hp : s.present d.1.val = true
      · exact hp
      · have hf : s.present d.1.val = false := by cases h : s.present d.1.val <;> simp_all
        have hfuture := P.missing_is_future d hf
        have hne := kmswPeanoPrefixClimb_old_index_ne_succ B c j hj P hno d
        omega
  have hidxnew (v : Bool) :
      (peanoIndex B (if v then z else b)).val = j + 1 := by
    cases v
    · exact congrArg Fin.val (peanoIndex_peanoEdge B ⟨j + 1, hj1⟩)
    · exact congrArg Fin.val ((peanoIndex_edgeInv B b).trans
        (peanoIndex_peanoEdge B ⟨j + 1, hj1⟩))
  have hprefix (d : StageDart t.nextEdge) :
      t.present d.1.val = true ↔
        (peanoIndex B (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d)).val ≤ j + 1 := by
    obtain ⟨x, rfl⟩ := Q.symm.surjective d
    cases x with
    | inl x =>
      have hval : (Q.symm (.inl x)).1.val = x.1.val :=
        congrArg Prod.fst (old_val x)
      have hne : (Q.symm (.inl x)).1.val ≠ s.nextEdge := by
        rw [hval]
        exact Nat.ne_of_lt x.1.isLt
      rw [hmap_old, hpres, ite_eq_right hne]
      exact hidxold x
    | inr x =>
      rcases x with ⟨ex, v⟩
      obtain rfl : ex = 0 := Subsingleton.elim _ _
      have hval : (Q.symm (.inr (0, v))).1.val = s.nextEdge :=
        congrArg Prod.fst (new_val v)
      rw [hmap_new v, hpres, ite_eq_left hval, hidxnew]
      simp only [le_refl]
  refine { emb := { dartMap := kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
                    injective := hinj
                    flip_comm := ?_
                    present := ?_
                    tail_comm := ?_
                    rot_induced := ?_
                    root_comm := ?_ }
           present_prefix := hprefix
           edges_cover_prefix := ?_
           missing_iff_frontier := ?_
           missing_is_future := ?_ }
  · intro d
    obtain ⟨x, rfl⟩ := Q.symm.surjective d
    have hflip : edgeFlip _ (Q.symm x) =
        Q.symm (Sum.map (edgeFlip _) (edgeFlip 1) x) := by
      cases x with
      | inl x => rcases x with ⟨e, v⟩; rfl
      | inr x => rcases x with ⟨e, v⟩; rfl
    change kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
        (edgeFlip _ (Q.symm x)) =
      B.map.toCombinatorialMap.edgeInv
        (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P (Q.symm x))
    rw [hflip, hmap (Sum.map (edgeFlip _) (edgeFlip 1) x), hmap x]
    cases x with
    | inl x => exact P.emb.flip_comm x
    | inr x =>
      rcases x with ⟨e, v⟩
      have he : e = 0 := Subsingleton.elim _ _
      subst e
      cases v
      · rfl
      · exact (B.map.toCombinatorialMap.edgeInv_invol b).symm
  · intro d hd
    exact B.noMissingDarts _
  · intro d hd
    change ¬ t.present d.1.val = false at hd
    change (t.present d.1.val = true ∧ d.2 = false) ↔
      B.map.tail (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d)
    by_cases hnew : d.1.val = s.nextEdge
    · rw [kmswPeanoPrefixClimbLeftExistingDartMap_new B c j hj hj1 P d hnew]
      cases hside : d.2
      · have hp : t.present d.1.val = true := by
          rw [hpres, ite_eq_left hnew]
        exact iff_of_true ⟨hp, rfl⟩
          (peanoEdge_forward B ⟨j + 1, hj1⟩)
      ·
        have hn := (B.map.tail_iff b (B.noMissingDarts b)).1
          (peanoEdge_forward B ⟨j + 1, hj1⟩)
        apply iff_of_false
        · intro h
          cases h.2
        · exact hn
    · have hbound : d.1.val < s.nextEdge + 1 := by
        have hdlt : d.1.val < t.nextEdge := by
          change d.1.val < (kmswStage u (j + 1)).nextEdge
          exact d.1.isLt
        simpa only [hs] using hdlt
      have hold : d.1.val < s.nextEdge := by omega
      let d₀ : StageDart s.nextEdge := (⟨d.1.val, hold⟩, d.2)
      have hcast : outerSucc_castDart
          (kmswStage_nextEdge_mono u (m := j) (n := j + 1) (Nat.le_succ j)) d₀ = d := by
        rcases d with ⟨⟨f₀, hf₀⟩, side⟩
        apply Prod.ext
        · exact Fin.ext rfl
        · rfl
      rw [← hcast, kmswPeanoPrefixClimbLeftExistingDartMap_old]
      have hp : s.present d₀.1.val = true := by
        rw [hpres] at hd
        simp [hnew] at hd
        exact hd
      have ht := P.emb.tail_comm d₀
        (by change ¬ s.present d₀.1.val = false; rw [hp]; decide)
      change (s.present d₀.1.val = true ∧ d₀.2 = false) ↔
        B.map.tail (P.emb.dartMap d₀) at ht
      change (t.present d₀.1.val = true ∧ d₀.2 = false) ↔
        B.map.tail (P.emb.dartMap d₀)
      rw [hpres, ite_eq_right (Nat.ne_of_lt d₀.1.isLt), hp]
      rw [hp] at ht
      exact ht
  · intro d
    obtain ⟨x, rfl⟩ := Q.symm.surjective d
    obtain ⟨k, hk, hr, hm⟩ := hfinduced x
    refine ⟨k, hk, ?_, ?_⟩
    · have hrot' : stageRot u (j + 1) (Q.symm x) = Q.symm (τ x) := by
        apply Q.injective
        rw [Q.apply_symm_apply]
        exact hrot x
      change (ρ : D → D)^[k]
          (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P (Q.symm x)) =
        kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
          (stageRot u (j + 1) (Q.symm x))
      rw [hmap x, hrot', hmap (τ x)]
      exact hr
    · intro m hm0 hmk hmem
      have hmapRange : Set.range f =
          Set.range (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P) := by
        apply Set.Subset.antisymm
        · rintro y ⟨x, rfl⟩
          exact ⟨Q.symm x, hmap x⟩
        · rintro y ⟨d, rfl⟩
          exact ⟨Q d, by simpa only [Q.symm_apply_apply] using (hmap (Q d)).symm⟩
      rw [hmap x, ← hmapRange] at hmem
      exact hm m hm0 hmk hmem
  · have hroot : (kmswRootedStage u (j + 1)).root =
        Q.symm (.inr (0, false)) := by
      apply Prod.ext
      · apply Fin.ext
        have hactive : t.active = s.nextEdge := facts.2.2.2.2.1
        exact hactive.trans (congrArg Prod.fst (new_val false)).symm
      · rfl
    change kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
      (kmswRootedStage u (j + 1)).root = b
    rw [hroot]
    exact hmapnewFalse
  · intro k hk
    by_cases hkj : k ≤ j
    · obtain ⟨d, hd⟩ := P.edges_cover_prefix k hkj
      refine ⟨outerSucc_castDart
        (kmswStage_nextEdge_mono u (m := j) (n := j + 1) (Nat.le_succ j)) d, ?_⟩
      change ((peanoIndex B
        (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
          (outerSucc_castDart
            (kmswStage_nextEdge_mono u (m := j) (n := j + 1) (Nat.le_succ j)) d))).val = k)
      rw [kmswPeanoPrefixClimbLeftExistingDartMap_old]
      exact hd
    · refine ⟨Q.symm (.inr (0, false)), ?_⟩
      change (peanoIndex B (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P
        (Q.symm (.inr (0, false)) ))).val = k
      rw [hmapnewFalse]
      have hbidx : (peanoIndex B b).val = j + 1 := by
        simpa [b] using congrArg Fin.val (peanoIndex_peanoEdge B ⟨j + 1, hj1⟩)
      rw [hbidx]
      omega
  · intro d
    exact (kmswStage_status u (j + 1)).1 d.1.val d.1.isLt
  · intro d hd
    change t.present d.1.val = false at hd
    change j + 1 < (peanoIndex B
      (kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P d)).val
    by_contra hnot
    have hp := (hprefix d).2 (by omega)
    rw [hd] at hp
    contradiction

/-- The existing-predecessor climb embedding uses its candidate dart map.
not the paper result. -/
theorem kmswPeanoPrefixEmbedding_climb_leftExisting_dartMap
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (c : KMSWWalkClass ℓ r n) (j : ℕ)
    (hj : j < B.map.toCombinatorialMap.numEdges)
    (P : KMSWPeanoPrefixEmbedding B c j hj)
    (hj1 : j + 1 < B.map.toCombinatorialMap.numEdges)
    (hcode : codeExtend c j = 0)
    (hkind : peanoStepKind B j hj1 = .climb)
    (e : ℕ) (es : List ℕ)
    (hUL : (kmswStage (codeExtend c) j).UL.dropLast.reverse = e :: es)
    (hfrontier : KMSWPeanoPrefixClimbFrontier B c j hj hj1 P)
    (hno : KMSWPeanoPrefixClimbNoNextFrontierCollision B c j hj P)
    (hcorner : KMSWPeanoClimbCorner B c j hj P hj1
      ((⟨e, (stageRotation_UL_bound (codeExtend c) j) e
        (List.mem_of_mem_dropLast (List.mem_reverse.mp (by
          rw [hUL]
          exact List.mem_cons_self)))⟩, false))
      ((⟨(kmswStage (codeExtend c) j).active,
        act_lt_nextEdge (codeExtend c) (le_refl j)⟩, true))) :
    (kmswPeanoPrefixEmbedding_climb_leftExisting
      B c j hj P hj1 hcode hkind e es hUL hfrontier hno hcorner).emb.dartMap =
        kmswPeanoPrefixClimbLeftExistingDartMap B c j hj hj1 P := by
  rfl


end DirectedDistances.KMSW
