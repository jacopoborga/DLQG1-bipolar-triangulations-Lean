module

public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealization

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

The geometric side below uses the increasing unions of the actual geometric ancestor
carriers, not the decoded cut classes. The realization obligation is an explicit
parameter only to the finite-class identification results. Levelwise marked
isomorphisms and compatible marked isomorphisms are distinguished explicitly. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 MeasureTheory Filter
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)
local notation "Code" => (ℕ → Option FiniteThinMap)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Permanent geometric carriers, directed incidence, induced rotation, retained face
succession, root and indexed boundary/seam. Missing edges remain in `edges`. -/
structure GeometricSideSubmap where
  vertices : Set ℕ
  edges : Set ℕ
  west : ℕ → ℕ
  east : ℕ → ℕ
  present : Set ℕ
  rotation : (ℕ × Bool) → (ℕ × Bool) → Prop
  faceNext : (ℕ × Bool) → (ℕ × Bool) → Prop
  root : ℕ
  boundary : ℕ → ℕ × Bool
  seam : ℕ → ℕ × Bool

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Vertices and both darts of every geometric edge, including missing edges. -/
abbrev GeometricSideCell (M : GeometricSideSubmap) :=
  Sum M.vertices {d : ℕ × Bool // d.1 ∈ M.edges}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The full marked whole-side relation. There is no finite target in a whole side,
so the finite-only `target` tag is empty. -/
@[expose] def geometricSideRelation (M : GeometricSideSubmap) :
    TruncationRelation → GeometricSideCell M → GeometricSideCell M → Prop
  | .vertex, .inl _, _ => True
  | .root, .inl v, _ => v.1 = M.root
  | .incident, .inr d, .inl v => (if d.1.2 then M.east d.1.1 else M.west d.1.1) = v.1
  | .opposite, .inr d, .inr e => (d.1.1, !d.1.2) = e.1
  | .oriented, .inr d, _ => d.1.1 ∈ M.present ∧ d.1.2 = false
  | .rotation, .inr d, .inr e => M.rotation d.1 e.1
  | .faceNext, .inr d, .inr e => M.faceNext d.1 e.1
  | .boundary i, .inr d, _ => M.boundary i = d.1
  | .seam i, .inr d, _ => M.seam i = d.1
  | _, _, _ => False

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A whole-side marked isomorphism preserves every geometric and marking relation. -/
structure GeometricSideMarkedIso (M N : GeometricSideSubmap) where
  equiv : GeometricSideCell M ≃ GeometricSideCell N
  relation_iff : ∀ t u v,
    geometricSideRelation M t u v ↔ geometricSideRelation N t (equiv u) (equiv v)

section CoherentDomain

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))

local notation "W" q => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "HF" q => sourceAncestor_finite_incidence x T hT q
local notation "HL" q => sourceAncestor_left_nonneg x T hT q
local notation "HT" q => sourceAncestor_left_transient x T hT q
local notation "HR" q => sourceAncestor_right_unbounded x T hT q
local notation "P" q => sourceAncestorPath x T hT q

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual geometric ancestor vertex carrier on the coherent domain. -/
@[expose] noncomputable def geometricAncestorVertices
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (s : ℕ) : Set ℕ :=
  sourceAncestorVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual geometric ancestor edge carrier, without an edge-presence filter. -/
@[expose] noncomputable def geometricAncestorEdges
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (s : ℕ) : Set ℕ :=
  sourceAncestorEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric vertex carriers form an increasing exhaustion. -/
theorem geometricAncestorVertices_mono
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) :
    Monotone (geometricAncestorVertices x T hT a q) :=
  sourceAncestorVertices_mono (W q) (HF q) (HL q) (HT q) (HR q) (P q) a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric edge carriers form an increasing exhaustion. -/
theorem geometricAncestorEdges_mono
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) :
    Monotone (geometricAncestorEdges x T hT a q) :=
  sourceAncestorEdges_mono (W q) (HF q) (HL q) (HT q) (HR q) (P q) a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The increasing union retains exactly the geometric side vertices. -/
theorem iUnion_geometricAncestorVertices
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) :
    (⋃ s, geometricAncestorVertices x T hT a q s) =
      sideVertices (W q) (HF q) (HL q) (HT q) (HR q) (P q) a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcuts, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hv
    exact hs.1
  · intro v hv
    exact Set.mem_iUnion.mpr (sideVertex_mem_sourceAncestorVertices_some
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) hcuts a v hv)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The increasing union retains exactly the geometric side edges, including missing ones. -/
theorem iUnion_geometricAncestorEdges
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) :
    (⋃ s, geometricAncestorEdges x T hT a q s) =
      sideEdges (W q) (HF q) (HL q) (HT q) (HR q) (P q) a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcuts, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp he
    exact hs.1
  · intro e he
    exact Set.mem_iUnion.mpr (sideEdge_mem_sourceAncestorEdges_some
      (W q) (HF q) (HL q) (HT q) (HR q) (P q) hcuts a e he)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The side as the increasing union of geometric restrictions. Rotation is induced
on the union, rather than incorrectly taking the union of finite rotations.
Retained inner faces keep their original triangle succession. -/
@[expose] noncomputable def geometricSideSubmap
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) : GeometricSideSubmap where
  vertices := ⋃ s, geometricAncestorVertices x T hT a q s
  edges := ⋃ s, geometricAncestorEdges x T hT a q s
  west := edgeWest (W q)
  east := edgeEast (W q)
  present := {e | EdgePresent (W q) e}
  rotation d e := ∃ k : ℕ, 0 < k ∧
    (kmswInfRot (W q) (HF q) : (ℕ × Bool) → ℕ × Bool)^[k] d = e ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot (W q) (HF q) : (ℕ × Bool) → ℕ × Bool)^[j] d).1 ∉
          ⋃ s, geometricAncestorEdges x T hT a q s
  faceNext d e :=
    (∃ j : TriangleCreationTime (W q), d ∈ stageTriangleDartList (W q) j ∧
      ∀ z ∈ stageTriangleDartList (W q) j,
        z.1 ∈ ⋃ s, geometricAncestorEdges x T hT a q s) ∧
      kmswInfFaceSucc (W q) (HF q) d = e
  root := 0
  boundary := thinMapBoundaryDart (W q) (HF q) (HL q) (HT q) (HR q) a
  seam i := ((P q).edge i, false)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both endpoints of each edge in the union lie in its vertex union. -/
theorem geometricSideSubmap_endpoints
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (e : ℕ)
    (he : e ∈ (geometricSideSubmap x T hT a q).edges) :
    (geometricSideSubmap x T hT a q).west e ∈
        (geometricSideSubmap x T hT a q).vertices ∧
      (geometricSideSubmap x T hT a q).east e ∈
        (geometricSideSubmap x T hT a q).vertices := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp he
  exact ⟨Set.mem_iUnion.mpr ⟨s, hs.2.1⟩, Set.mem_iUnion.mpr ⟨s, hs.2.2⟩⟩

private theorem list_edges_in_union
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (l : List (ℕ × Bool))
    (h : ∀ d ∈ l, d.1 ∈ ⋃ s, geometricAncestorEdges x T hT a q s) :
    ∃ s, ∀ d ∈ l, d.1 ∈ geometricAncestorEdges x T hT a q s := by
  induction l with
  | nil => exact ⟨0, fun d hd => False.elim (List.not_mem_nil hd)⟩
  | cons d l ih =>
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (h d (List.mem_cons_self))
    obtain ⟨t, ht⟩ := ih (fun z hz => h z (List.mem_cons_of_mem d hz))
    refine ⟨max s t, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact geometricAncestorEdges_mono x T hT a q (le_max_left s t) hs
    · exact geometricAncestorEdges_mono x T hT a q (le_max_right s t) (ht z hz)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Each retained whole-side face occurs at one finite ancestor level, with its original
successor. This proves face exhaustion as well as vertex and edge exhaustion. -/
theorem geometricSideSubmap_faceNext_iff
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (d e : ℕ × Bool) :
    (geometricSideSubmap x T hT a q).faceNext d e ↔
      ∃ s, sourceAncestorRetainedFace (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s d ∧
        kmswInfFaceSucc (W q) (HF q) d = e := by
  constructor
  · rintro ⟨⟨j, hd, hall⟩, he⟩
    obtain ⟨s, hs⟩ := list_edges_in_union x T hT a q (stageTriangleDartList (W q) j) hall
    exact ⟨s, ⟨j, hd, hs⟩, he⟩
  · rintro ⟨s, ⟨j, hd, hall⟩, he⟩
    exact ⟨⟨j, hd, fun z hz => Set.mem_iUnion.mpr ⟨s, hall z hz⟩⟩, he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite geometric vertex-and-dart carrier; it is independent of the decoder. -/
abbrev GeometricAncestorCell
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :=
  SourceAncestorCell (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
All finite geometric marked relations, including their finite target. -/
@[expose] noncomputable def geometricAncestorRelation
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :=
  sourceAncestorRelation (W q) (HF q) (HL q) (HT q) (HR q) (P q) a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A marked isomorphism at one fixed geometric ancestor level. -/
structure GeometricAncestorMarkedIso
    (a : ThinMapSide) (s : ℕ) (q q' : selectedCutCoherentDomain x T hT) where
  equiv : GeometricAncestorCell x T hT a s q ≃ GeometricAncestorCell x T hT a s q'
  relation_iff : ∀ t u v, geometricAncestorRelation x T hT a s q t u v ↔
    geometricAncestorRelation x T hT a s q' t (equiv u) (equiv v)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Under the explicitly unresolved realization, the selected class has a marked
geometric representative. This does not assert the realization hypothesis. -/
theorem selectedCutAncestorClass_geometric_representation
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    ∃ (ℓ r n : ℕ) (R : KMSWMapRep ℓ r n) (v : MapVertex R.B.map),
      finiteThinMapOfAncestors R a v = selectedCutAncestorClass x T hT a s q ∧
      ∃ e : TruncationCell (presentation R a v) ≃ GeometricAncestorCell x T hT a s q,
        ∀ t u z, truncationRelation (presentation R a v) t u z ↔
          geometricAncestorRelation x T hT a s q t (e u) (e z) := by
  let k := leastGoodCut x T hT s q
  have hk := leastGoodCut_spec x T hT s q
  obtain ⟨ℓ, r, n, R, v, hR, hv, e, he⟩ := hreal a s k q hk
  have hc := halfTruncate_eq_some_selectedCutAncestorClass x T hT a s k q hk
  rw [hR, halfTruncate_some_mk_boundaryTarget, hv] at hc
  exact ⟨ℓ, r, n, R, v, Option.some.inj hc, e, he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Under realization, equality at one code level is exactly a marked geometric
isomorphism at that level. No cross-level compatibility is asserted. -/
theorem selectedCutAncestorClass_eq_iff_geometric_iso
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (s : ℕ) (q q' : selectedCutCoherentDomain x T hT) :
    selectedCutAncestorClass x T hT a s q = selectedCutAncestorClass x T hT a s q' ↔
      Nonempty (GeometricAncestorMarkedIso x T hT a s q q') := by
  obtain ⟨ℓ, r, n, R, v, hR, e, he⟩ :=
    selectedCutAncestorClass_geometric_representation x T hT hreal a s q
  obtain ⟨ℓ', r', n', S, v', hS, f, hf⟩ :=
    selectedCutAncestorClass_geometric_representation x T hT hreal a s q'
  rw [← hR, ← hS, finiteThinMapOfAncestors_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨(e.symm.trans g).trans f, ?_⟩⟩
    intro t u z
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
      (he t (e.symm u) (e.symm z)).symm.trans
        ((hg t (e.symm u) (e.symm z)).trans (hf t (g (e.symm u)) (g (e.symm z))))
  · rintro ⟨g⟩
    refine ⟨(e.trans g.equiv).trans f.symm, ?_⟩
    intro t u z
    have hh := (hf t (f.symm (g.equiv (e u))) (f.symm (g.equiv (e z)))).symm
    simp only [Equiv.apply_symm_apply] at hh
    exact (he t u z).trans ((g.relation_iff t (e u) (e z)).trans hh)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Precise finite-level fidelity: under realization, whole code equality is equivalent
to marked geometric isomorphism separately at every ancestor level. Compatibility -/
theorem thinSideCode_eq_iff_levelwise_geometric_iso
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT) :
    thinSideCode x T hT a q.1 = thinSideCode x T hT a q'.1 ↔
      ∀ s, Nonempty (GeometricAncestorMarkedIso x T hT a s q q') := by
  rw [thinSideCode_eq_iff_selectedCutAncestorClasses_eq]
  constructor
  · intro h s
    exact (selectedCutAncestorClass_eq_iff_geometric_iso x T hT hreal a s q q').mp
      (congrFun h s)
  · intro h
    funext s
    exact (selectedCutAncestorClass_eq_iff_geometric_iso x T hT hreal a s q q').mpr
      (h s)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent-ID inclusion of one ancestor level into a later level. -/
@[expose] noncomputable def geometricAncestorInclusion
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    {s t : ℕ} (hst : s ≤ t) :
    GeometricAncestorCell x T hT a s q → GeometricAncestorCell x T hT a t q
  | .inl v => .inl ⟨v.1, geometricAncestorVertices_mono x T hT a q hst v.2⟩
  | .inr d => .inr ⟨d.1, geometricAncestorEdges_mono x T hT a q hst d.2⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent-ID inclusion of each finite geometric restriction into the whole side. -/
@[expose] noncomputable def geometricAncestorIntoSide
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (s : ℕ) :
    GeometricAncestorCell x T hT a s q →
      GeometricSideCell (geometricSideSubmap x T hT a q)
  | .inl v => .inl ⟨v.1, Set.mem_iUnion.mpr ⟨s, v.2⟩⟩
  | .inr d => .inr ⟨d.1, Set.mem_iUnion.mpr ⟨s, d.2⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The inclusion into the union preserves vertex and dart identity injectively. -/
theorem geometricAncestorIntoSide_injective
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT) (s : ℕ) :
    Function.Injective (geometricAncestorIntoSide x T hT a q s) := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      have hh := congrArg (Sum.map Subtype.val Subtype.val) h
      have huv : u.1 = v.1 := Sum.inl.inj hh
      exact congrArg Sum.inl (Subtype.ext huv)
    | inr v => cases h
  | inr u =>
    cases v with
    | inl v => cases h
    | inr v =>
      have hh := congrArg (Sum.map Subtype.val Subtype.val) h
      have huv : u.1 = v.1 := Sum.inr.inj hh
      exact congrArg Sum.inr (Subtype.ext huv)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every whole-side cell belongs to a finite geometric ancestor restriction. -/
theorem geometricAncestorIntoSide_exhausts
    (a : ThinMapSide) (q : selectedCutCoherentDomain x T hT)
    (z : GeometricSideCell (geometricSideSubmap x T hT a q)) :
    ∃ s u, geometricAncestorIntoSide x T hT a q s u = z := by
  cases z with
  | inl v =>
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp v.2
    exact ⟨s, .inl ⟨v.1, hs⟩, rfl⟩
  | inr d =>
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp d.2
    exact ⟨s, .inr ⟨d.1, hs⟩, rfl⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Whole-side marked isomorphism with restrictions at every level that commute with
permanent-ID inclusion. This is stronger than unrelated levelwise isomorphisms. -/
structure GeometricSideCompatibleIso
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT) where
  whole : GeometricSideMarkedIso
    (geometricSideSubmap x T hT a q) (geometricSideSubmap x T hT a q')
  level : ∀ s, GeometricAncestorMarkedIso x T hT a s q q'
  commutes : ∀ s u, whole.equiv (geometricAncestorIntoSide x T hT a q s u) =
    geometricAncestorIntoSide x T hT a q' s ((level s).equiv u)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The level isomorphisms of a compatible whole-side isomorphism agree on overlaps. -/
theorem geometricSideCompatibleIso_levels_commute
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT)
    (I : GeometricSideCompatibleIso x T hT a q q')
    {s t : ℕ} (hst : s ≤ t) (u : GeometricAncestorCell x T hT a s q) :
    (I.level t).equiv (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorInclusion x T hT a q' hst ((I.level s).equiv u) := by
  apply geometricAncestorIntoSide_injective x T hT a q' t
  rw [← I.commutes]
  have hleft : geometricAncestorIntoSide x T hT a q t
      (geometricAncestorInclusion x T hT a q hst u) =
      geometricAncestorIntoSide x T hT a q s u := by cases u <;> rfl
  rw [hleft, I.commutes]
  cases (I.level s).equiv u <;> rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Any compatible whole-side marked isomorphism forces equality of side codes,
conditional only on the separately recorded realization input. -/
theorem geometricSideCompatibleIso_code_eq
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT)
    (I : GeometricSideCompatibleIso x T hT a q q') :
    thinSideCode x T hT a q.1 = thinSideCode x T hT a q'.1 :=
  (thinSideCode_eq_iff_levelwise_geometric_iso x T hT hreal a q q').mpr
    (fun s => ⟨I.level s⟩)

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
marked isomorphism commuting with every geometric ancestor inclusion. No instance
or theorem asserting this proposition is supplied. -/
@[expose] def GeometricAncestorIsoAssembly : Prop :=
  ∀ (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT),
    (∀ s, Nonempty (GeometricAncestorMarkedIso x T hT a s q q')) →
      Nonempty (GeometricSideCompatibleIso x T hT a q q')

/- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
This proposition is isolated, not asserted as a theorem. -/
@[expose] noncomputable def ThinSideCodeGeometricFidelity : Prop :=
  ∀ (a : ThinMapSide) (q q' : selectedCutCoherentDomain x T hT),
    thinSideCode x T hT a q.1 = thinSideCode x T hT a q'.1 ↔
      Nonempty (GeometricSideCompatibleIso x T hT a q q')

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Exact reduction of full code fidelity to the isolated geometric assembly problem.
It does not prove or assume either proposition. -/
theorem thinSideCodeGeometricFidelity_iff_assembly
    (hreal : SourceAncestorCutRealization x T hT) :
    ThinSideCodeGeometricFidelity x T hT ↔ GeometricAncestorIsoAssembly x T hT := by
  constructor
  · intro h a q q' hs
    exact (h a q q').mp
      ((thinSideCode_eq_iff_levelwise_geometric_iso x T hT hreal a q q').mpr hs)
  · intro h a q q'
    constructor
    · intro hc
      exact h a q q'
        ((thinSideCode_eq_iff_levelwise_geometric_iso x T hT hreal a q q').mp hc)
    · rintro ⟨I⟩
      exact geometricSideCompatibleIso_code_eq x T hT hreal a q q' I

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The coherent-domain side code is measurable for the product (cylinder) sigma algebra. -/
theorem measurable_geometricSideCode (a : ThinMapSide) :
    Measurable (fun q : selectedCutCoherentDomain x T hT => thinSideCode x T hT a q.1) :=
  (measurable_thinSideCode x T hT a).comp measurable_subtype_coe

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A fixed finite geometric marked-isomorphism class is a measurable cylinder event,
conditional on realization. This is a statement about geometric restrictions. -/
theorem measurableSet_geometricAncestorMarkedIso
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (s : ℕ) (q' : selectedCutCoherentDomain x T hT) :
    MeasurableSet {q : selectedCutCoherentDomain x T hT |
      Nonempty (GeometricAncestorMarkedIso x T hT a s q q')} := by
  have hm := (measurable_thinTruncationAt x T hT a s)
    (show MeasurableSet ({some (selectedCutAncestorClass x T hT a s q')} :
      Set (Option FiniteThinMap)) from trivial)
  convert hm using 1
  ext q
  change Nonempty (GeometricAncestorMarkedIso x T hT a s q q') ↔
    thinTruncationAt x T hT a s q = some (selectedCutAncestorClass x T hT a s q')
  rw [thinTruncationAt_eq_some_selectedCutAncestorClass, Option.some.injEq]
  exact (selectedCutAncestorClass_eq_iff_geometric_iso x T hT hreal a s q q').symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The simultaneous event of isomorphism at every finite geometric level is measurable.
Compatibility is not inferred from this countable intersection. -/
theorem measurableSet_levelwise_geometric_iso
    (hreal : SourceAncestorCutRealization x T hT)
    (a : ThinMapSide) (q' : selectedCutCoherentDomain x T hT) :
    MeasurableSet {q : selectedCutCoherentDomain x T hT |
      ∀ s, Nonempty (GeometricAncestorMarkedIso x T hT a s q q')} := by
  have hm := MeasurableSet.iInter
    (fun s => measurableSet_geometricAncestorMarkedIso x T hT hreal a s q')
  convert hm using 1
  ext q
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A geometric restriction invariant means a function constant on levelwise marked
isomorphism. This definition does not claim that every whole-side invariant has
this property; that requires the isolated assembly problem. -/
@[expose] def IsGeometricRestrictionInvariant {β : Type*}
    (a : ThinMapSide) (f : selectedCutCoherentDomain x T hT → β) : Prop :=
  ∀ q q', (∀ s, Nonempty (GeometricAncestorMarkedIso x T hT a s q q')) → f q = f q'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every geometric restriction invariant is a function of the whole side code.
This is set-theoretic factorization; measurability of its decoder is not asserted. -/
theorem geometricRestrictionInvariant_factorsThrough_code
    (hreal : SourceAncestorCutRealization x T hT)
    {β : Type*} [Nonempty β] (a : ThinMapSide)
    (f : selectedCutCoherentDomain x T hT → β)
    (hf : IsGeometricRestrictionInvariant x T hT a f) :
    ∃ F : Code → β, ∀ q, f q = F (thinSideCode x T hT a q.1) := by
  have hh : f.FactorsThrough
      (fun q : selectedCutCoherentDomain x T hT => thinSideCode x T hT a q.1) := by
    intro q q' hc
    exact hf q q'
      ((thinSideCode_eq_iff_levelwise_geometric_iso x T hT hreal a q q').mp hc)
  obtain ⟨F, hF⟩ := Function.factorsThrough_iff f |>.mp hh
  exact ⟨F, fun q => congrFun hF q⟩

end CoherentDomain
end DirectedDistances.PaperProofs.Section4
