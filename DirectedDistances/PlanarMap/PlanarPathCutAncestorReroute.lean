module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import DirectedDistances.PlanarMap.GeneralBipolarBoundary
public import DirectedDistances.PlanarMap.BipolarBoundaryData
public import DirectedDistances.PlanarMap.PlanarPathCutOneSided
public import DirectedDistances.PaperProofs.Section4.ThinCutCompatibility

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.

Abstract seam-rerouting argument for the converse `cutLRep_ancestors_map_iff` (the
converse of `cutLRep_ancestors_map`).  A directed path between two vertices of a set `S`
(the closed left side) that leaves `S` can only leave and re-enter through a directed
seam `g 0 → ⋯ → g n` lying in `S`; by acyclicity seam vertices are ordered along the
seam, so each excursion is replaced by a seam segment. -/

public section

namespace DirectedDistances.PlanarMap

open Relation

variable {V : Type*}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Seam vertices joined by an ambient directed path are joined along `S` (the seam is a
directed chain in `S` and the ambient relation is acyclic). -/
theorem seam_reach_of_reach (step : V → V → Prop) (S : Set V) (g : ℕ → V) (n : ℕ)
    (hacyc : ∀ v, ¬ TransGen step v v)
    (hseam : ∀ i < n, step (g i) (g (i + 1)) ∧ g i ∈ S ∧ g (i + 1) ∈ S)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (h : ReflTransGen step (g i) (g j)) :
    ReflTransGen (fun a b => step a b ∧ a ∈ S ∧ b ∈ S) (g i) (g j) := by
  have hforward : ∀ a b : ℕ, a ≤ b → b ≤ n →
      ReflTransGen (fun a b => step a b ∧ a ∈ S ∧ b ∈ S) (g a) (g b) := by
    intro a b
    induction b with
    | zero =>
      intro hab _
      obtain rfl : a = 0 := by omega
      exact ReflTransGen.refl
    | succ b ih =>
      intro hab hb
      by_cases hae : a = b + 1
      · rw [hae]
      · exact (ih (by omega) (by omega)).tail (hseam b (by omega))
  rcases Nat.lt_or_ge j i with hij | hij
  · have h2 : ReflTransGen step (g j) (g i) :=
      ReflTransGen.lift id (fun _ _ hab => hab.1) _ _
        (hforward j i (Nat.le_of_lt hij) hi)
    rcases reflTransGen_iff_eq_or_transGen.mp h2 with heq | htr
    · rw [heq]
    · exact absurd (TransGen.trans_left htr h) (hacyc _)
  · exact hforward i j hij hj

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Rerouting: if every step leaving or entering `S` happens at a seam vertex of the directed
seam `g 0 → ⋯ → g n ⊆ S`, and the ambient relation is acyclic, then an ambient directed
path between vertices of `S` yields a directed path inside `S`. -/
theorem reach_in_of_reach_seam (step : V → V → Prop) (S : Set V) (g : ℕ → V) (n : ℕ)
    (hacyc : ∀ v, ¬ TransGen step v v)
    (hseam : ∀ i < n, step (g i) (g (i + 1)) ∧ g i ∈ S ∧ g (i + 1) ∈ S)
    (hleave : ∀ u w, step u w → u ∈ S → w ∉ S → ∃ i ≤ n, g i = u)
    (henter : ∀ u w, step u w → u ∉ S → w ∈ S → ∃ i ≤ n, g i = w)
    {u w : V} (hw : w ∈ S) (h : ReflTransGen step u w) :
    (u ∈ S → ReflTransGen (fun a b => step a b ∧ a ∈ S ∧ b ∈ S) u w) ∧
    (u ∉ S → ∃ q, (∃ i ≤ n, g i = q) ∧ ReflTransGen step u q ∧
      ReflTransGen (fun a b => step a b ∧ a ∈ S ∧ b ∈ S) q w) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨fun _ => ReflTransGen.refl, fun h' => absurd hw h'⟩
  | @head a c hac hcw ih =>
    by_cases ha : a ∈ S
    · by_cases hc : c ∈ S
      · exact ⟨fun _ => ReflTransGen.head ⟨hac, ha, hc⟩ (ih.1 hc), fun h' => absurd ha h'⟩
      · obtain ⟨i, hi, hgi⟩ := hleave a c hac ha hc
        obtain ⟨q, ⟨j, hj, hgj⟩, hcq, hqw⟩ := ih.2 hc
        refine ⟨fun _ => ?_, fun h' => absurd ha h'⟩
        have hreach : ReflTransGen step (g i) (g j) := by
          rw [hgi, hgj]; exact ReflTransGen.head hac hcq
        have := seam_reach_of_reach step S g n hacyc hseam hi hj hreach
        rw [hgi, hgj] at this
        exact this.trans hqw
    · refine ⟨fun h' => absurd h' ha, fun _ => ?_⟩
      by_cases hc : c ∈ S
      · exact ⟨c, henter a c hac ha hc, ReflTransGen.single hac, ih.1 hc⟩
      · obtain ⟨q, hq, hcq, hqw⟩ := ih.2 hc
        exact ⟨q, hq, ReflTransGen.head hac hcq, hqw⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The `hacyc` hypothesis of the rerouting lemmas holds for the directed step of any
bipolar triangulation with boundary base (hence for `R.B.map`). -/
theorem directedStep_not_transGen_self {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (v : MapVertex B.map) :
    ¬ TransGen B.map.directedStep v v :=
  B.acyclic v

section LeftHalf

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r n : ℕ}

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every dart based at the image of an off-path left-half vertex is a strictly left dart. -/
theorem pathCutLeftHalf_offPath_tail_mem
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v : MapVertex (pathCutLeftHalfDirectedMap B P))
    (hv : pathCutLeftHalfVertexMap B P v ∉ P.vertices)
    {d : D} (hdTail : dartTailVertex B.map d = pathCutLeftHalfVertexMap B P v) :
    d ∈ pathCutLeftDarts B P := by
  obtain ⟨e, he⟩ := Quotient.exists_rep v
  change dartTailVertex (pathCutLeftHalfDirectedMap B P) e = v at he
  have heTail : dartTailVertex B.map e.1 = pathCutLeftHalfVertexMap B P v := by
    calc
      dartTailVertex B.map e.1 = pathCutLeftHalfVertexMap B P
          (dartTailVertex (pathCutLeftHalfDirectedMap B P) e) :=
        (pathCutLeftHalfVertexMap_dartTailVertex B P e).symm
      _ = pathCutLeftHalfVertexMap B P v := congrArg _ he
  have heNotSeam : e.1 ∉ pathCutSeamDarts B P := by
    intro hseam
    have hvertex := pathCutSeamDarts_tailVertex_mem B P hseam
    exact hv (by simpa only [heTail] using hvertex)
  have heLeft : e.1 ∈ pathCutLeftDarts B P := by
    have heHalf := e.2
    change e.1 ∈ pathCutLeftDarts B P ∪ pathCutSeamDarts B P at heHalf
    rcases heHalf with hleft | hseam
    · exact hleft
    · exact (heNotSeam hseam).elim
  rcases pathCut_vertex_darts_one_sided B P hv with hleftAll | hrightAll
  · exact hleftAll d hdTail
  · have hrightE := hrightAll e.1 heTail
    have hdisjoint := Set.disjoint_left.mp (pathCut_offSeam_disjoint B P)
    exact (hdisjoint ⟨heLeft, heNotSeam⟩ ⟨hrightE, heNotSeam⟩).elim

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A base step from the image of the left half to a vertex outside the image starts on the
cut path. -/
theorem pathCutLeftHalf_leave_mem_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u w : MapVertex B.map} (h : B.map.directedStep u w)
    (hu : u ∈ Set.range (pathCutLeftHalfVertexMap B P))
    (hw : w ∉ Set.range (pathCutLeftHalfVertexMap B P)) : u ∈ P.vertices := by
  by_contra hup
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨d, _, _, hsource, htarget⟩ := h
  have hdLeft := pathCutLeftHalf_offPath_tail_mem B P v hup hsource
  let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, Or.inl hdLeft⟩
  exact hw ⟨dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH,
    (pathCutLeftHalfVertexMap_dartHeadVertex B P dH).trans htarget⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A base step from a vertex outside the image of the left half into the image ends on the
cut path. -/
theorem pathCutLeftHalf_enter_mem_path
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {u w : MapVertex B.map} (h : B.map.directedStep u w)
    (hu : u ∉ Set.range (pathCutLeftHalfVertexMap B P))
    (hw : w ∈ Set.range (pathCutLeftHalfVertexMap B P)) : w ∈ P.vertices := by
  by_contra hwp
  obtain ⟨v, rfl⟩ := hw
  obtain ⟨d, _, _, hsource, htarget⟩ := h
  have hrevTail : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
      pathCutLeftHalfVertexMap B P v := by
    simpa only [dartTailVertex, dartHeadVertex] using htarget
  have hrevLeft := pathCutLeftHalf_offPath_tail_mem B P v hwp hrevTail
  have hdLeft : d ∈ pathCutLeftHalfDarts B P := by
    have h' := pathCutLeftHalf_edgeInv_mem B P
      (Or.inl hrevLeft : B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P)
    simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h'
  exact hu ⟨dartTailVertex (pathCutLeftHalfDirectedMap B P) ⟨d, hdLeft⟩,
    (pathCutLeftHalfVertexMap_dartTailVertex B P ⟨d, hdLeft⟩).trans hsource⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every vertex of the cut path lies in the image of the left half. -/
theorem pathCutLeftHalf_pathVertex_mem_range
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {v : MapVertex B.map} (hv : v ∈ P.vertices) :
    v ∈ Set.range (pathCutLeftHalfVertexMap B P) := by
  by_cases hs : v = B.sink
  · exact ⟨pathCutLeftHalfSink B P, (pathCutLeftHalfSink_map B P).trans hs.symm⟩
  · obtain ⟨d, _, hdTail, hdLeft, _⟩ :=
      pathCut_vertex_outgoingDart_in_both_closed_halves B P hv hs
    exact ⟨dartTailVertex (pathCutLeftHalfDirectedMap B P) ⟨d, hdLeft⟩,
      (pathCutLeftHalfVertexMap_dartTailVertex B P ⟨d, hdLeft⟩).trans hdTail⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The cut path, indexed by `g i = P.vertices.getD i B.source`, is a directed chain of base
steps inside the image of the left half. -/
theorem pathCutLeftHalf_seam_chain
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)] :
    ∀ i < n, B.map.directedStep (P.vertices.getD i B.source)
        (P.vertices.getD (i + 1) B.source) ∧
      P.vertices.getD i B.source ∈ Set.range (pathCutLeftHalfVertexMap B P) ∧
      P.vertices.getD (i + 1) B.source ∈ Set.range (pathCutLeftHalfVertexMap B P) := by
  intro i hi
  have hlen : i < P.darts.length := by rw [P.darts_length]; exact hi
  obtain ⟨hm, ht, h1, h2⟩ := P.edge_step ⟨i, hlen⟩
  have hg : ∀ k (hk : k < P.vertices.length),
      P.vertices.getD k B.source = P.vertices.get ⟨k, hk⟩ := by
    intro k hk
    simp [List.getD_eq_getElem?_getD, hk]
  have hv0 : i < P.vertices.length := by rw [P.vertices_length]; omega
  have hv1 : i + 1 < P.vertices.length := by rw [P.vertices_length]; omega
  rw [hg i hv0, hg (i + 1) hv1]
  exact ⟨⟨P.darts.get ⟨i, hlen⟩, hm, ht, h1.symm, h2.symm⟩,
    pathCutLeftHalf_pathVertex_mem_range B P (List.get_mem _ _),
    pathCutLeftHalf_pathVertex_mem_range B P (List.get_mem _ _)⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every cut-path vertex has an index `i ≤ n` in `g i = P.vertices.getD i B.source`. -/
theorem pathCut_pathVertex_index
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    {v : MapVertex B.map} (hv : v ∈ P.vertices) :
    ∃ i ≤ n, P.vertices.getD i B.source = v := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hv
  have hlt : k.val < P.vertices.length := k.isLt
  refine ⟨k.val, by have := P.vertices_length; omega, ?_⟩
  have : P.vertices.getD k.val B.source = P.vertices.get k := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, hk]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A base step between images of left-half vertices lifts to a directed path in the half. -/
theorem pathCutLeftHalf_reach_of_step
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    {a b : MapVertex (pathCutLeftHalfDirectedMap B P)}
    (h : B.map.directedStep (pathCutLeftHalfVertexMap B P a)
      (pathCutLeftHalfVertexMap B P b)) :
    ReflTransGen (pathCutLeftHalfDirectedMap B P).directedStep a b := by
  have lift : ∀ {d : D}, d ∈ pathCutLeftHalfDarts B P → B.map.tail d →
      dartTailVertex B.map d = pathCutLeftHalfVertexMap B P a →
      dartHeadVertex B.map d = pathCutLeftHalfVertexMap B P b →
      ReflTransGen (pathCutLeftHalfDirectedMap B P).directedStep a b := by
    intro d hd htail hs ht
    let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} := ⟨d, hd⟩
    have h1 : pathCutLeftHalfVertexMap B P
        (dartTailVertex (pathCutLeftHalfDirectedMap B P) dH) =
          pathCutLeftHalfVertexMap B P a := by
      rw [pathCutLeftHalfVertexMap_dartTailVertex]; exact hs
    have h2 : pathCutLeftHalfVertexMap B P
        (dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH) =
          pathCutLeftHalfVertexMap B P b := by
      rw [pathCutLeftHalfVertexMap_dartHeadVertex]; exact ht
    exact ReflTransGen.single ⟨dH, not_false,
      (pathCutLeftHalf_embedding_fields B P).2.2.1 dH |>.mpr htail,
      pathCutLeftHalfVertexMap_injective B P h1, pathCutLeftHalfVertexMap_injective B P h2⟩
  obtain ⟨d, hmiss, htail, hs, ht⟩ := h
  by_cases ha : pathCutLeftHalfVertexMap B P a ∈ P.vertices
  · by_cases hb : pathCutLeftHalfVertexMap B P b ∈ P.vertices
    · -- both endpoints on the path: follow the path itself
      obtain ⟨i, hi, hgi⟩ := pathCut_pathVertex_index B P ha
      obtain ⟨j, hj, hgj⟩ := pathCut_pathVertex_index B P hb
      have hchain := pathCutLeftHalf_seam_chain B P
      have hbase : ∀ j i, j ≤ i → i ≤ n → ReflTransGen B.map.directedStep
          (P.vertices.getD j B.source) (P.vertices.getD i B.source) := by
        intro j i
        induction i with
        | zero =>
          intro hji _
          obtain rfl : j = 0 := by omega
          exact ReflTransGen.refl
        | succ i ih =>
          intro hji hin
          by_cases hje : j = i + 1
          · rw [hje]
          · exact (ih (by omega) (by omega)).tail (hchain i (by omega)).1
      have hstep : B.map.directedStep (P.vertices.getD i B.source)
          (P.vertices.getD j B.source) := by
        rw [hgi, hgj]; exact ⟨d, hmiss, htail, hs, ht⟩
      have hij : i < j := by
        by_contra hcon
        have hrev := hbase j i (by omega) hi
        have : TransGen B.map.directedStep (P.vertices.getD i B.source)
            (P.vertices.getD i B.source) :=
          TransGen.head' hstep hrev
        exact directedStep_not_transGen_self B _ this
      have key : ∀ k, k ≤ j → i ≤ k → ∀ x : MapVertex (pathCutLeftHalfDirectedMap B P),
          pathCutLeftHalfVertexMap B P x = P.vertices.getD k B.source →
          ReflTransGen (pathCutLeftHalfDirectedMap B P).directedStep a x := by
        intro k
        induction k with
        | zero =>
          intro _ hik x hx
          obtain rfl : i = 0 := by omega
          have : x = a := pathCutLeftHalfVertexMap_injective B P (hx.trans hgi)
          rw [this]
        | succ k ih =>
          intro hkj hik x hx
          by_cases hie : i = k + 1
          · have : x = a := pathCutLeftHalfVertexMap_injective B P
              (hx.trans (by rw [← hie]; exact hgi))
            rw [this]
          · obtain ⟨hst, hkS, _⟩ := hchain k (by omega)
            obtain ⟨y, hy⟩ := hkS
            refine (ih (by omega) (by omega) y hy).trans ?_
            have hlen : k < P.darts.length := by rw [P.darts_length]; omega
            obtain ⟨hm, hdt, h1, h2⟩ := P.edge_step ⟨k, hlen⟩
            have hg : ∀ m (hm : m < P.vertices.length),
                P.vertices.getD m B.source = P.vertices.get ⟨m, hm⟩ := by
              intro m hm; simp [List.getD_eq_getElem?_getD, hm]
            have hv0 : k < P.vertices.length := by rw [P.vertices_length]; omega
            have hv1 : k + 1 < P.vertices.length := by rw [P.vertices_length]; omega
            have hdh := pathCutLeftHalf_path_mem B P
              (List.get_mem P.darts ⟨k, hlen⟩)
            let dH : {d : D // d ∈ pathCutLeftHalfDarts B P} :=
              ⟨P.darts.get ⟨k, hlen⟩, hdh⟩
            have e1 : pathCutLeftHalfVertexMap B P
                (dartTailVertex (pathCutLeftHalfDirectedMap B P) dH) =
                  pathCutLeftHalfVertexMap B P y := by
              rw [pathCutLeftHalfVertexMap_dartTailVertex, hy, hg k hv0]
              exact h1.symm
            have e2 : pathCutLeftHalfVertexMap B P
                (dartHeadVertex (pathCutLeftHalfDirectedMap B P) dH) =
                  pathCutLeftHalfVertexMap B P x := by
              rw [pathCutLeftHalfVertexMap_dartHeadVertex, hx, hg (k + 1) hv1]
              exact h2.symm
            exact ReflTransGen.single ⟨dH, not_false,
              (pathCutLeftHalf_embedding_fields B P).2.2.1 dH |>.mpr hdt,
              pathCutLeftHalfVertexMap_injective B P e1,
              pathCutLeftHalfVertexMap_injective B P e2⟩
      exact key j le_rfl hij.le b hgj.symm
    · -- head off the path: the reversed dart is a left dart
      have hrevTail : dartTailVertex B.map (B.map.toCombinatorialMap.edgeInv d) =
          pathCutLeftHalfVertexMap B P b := by
        simpa only [dartTailVertex, dartHeadVertex] using ht
      have hrevLeft := pathCutLeftHalf_offPath_tail_mem B P b hb hrevTail
      have hdLeft : d ∈ pathCutLeftHalfDarts B P := by
        have h' := pathCutLeftHalf_edgeInv_mem B P
          (Or.inl hrevLeft : B.map.toCombinatorialMap.edgeInv d ∈ pathCutLeftHalfDarts B P)
        simpa only [B.map.toCombinatorialMap.edgeInv_invol] using h'
      exact lift hdLeft htail hs ht
  · exact lift (Or.inl (pathCutLeftHalf_offPath_tail_mem B P a ha hs)) htail hs ht

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ambient directed reachability between images of left-half vertices is exactly directed
reachability inside the left half. -/
theorem pathCutLeftHalf_reach_iff
    (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (P : SimpleDirectedDartPath B.map B.source B.sink n)
    [DecidablePred (fun d : D => d ∈ pathCutLeftHalfDarts B P)]
    (v t : MapVertex (pathCutLeftHalfDirectedMap B P)) :
    ReflTransGen (pathCutLeftHalfDirectedMap B P).directedStep v t ↔
      ReflTransGen B.map.directedStep (pathCutLeftHalfVertexMap B P v)
        (pathCutLeftHalfVertexMap B P t) := by
  constructor
  · intro hi
    apply ReflTransGen.lift (pathCutLeftHalfVertexMap B P) _ _ _ hi
    intro u z h
    obtain ⟨d, _, ht, hu, hz⟩ := h
    refine ⟨d.1, B.noMissingDarts _,
      ((pathCutLeftHalf_embedding_fields B P).2.2.1 d).mp ht, ?_, ?_⟩
    · exact (pathCutLeftHalfVertexMap_dartTailVertex B P d).symm.trans
        (congrArg (pathCutLeftHalfVertexMap B P) hu)
    · exact (pathCutLeftHalfVertexMap_dartHeadVertex B P d).symm.trans
        (congrArg (pathCutLeftHalfVertexMap B P) hz)
  · intro h
    have hre := (reach_in_of_reach_seam B.map.directedStep
      (Set.range (pathCutLeftHalfVertexMap B P)) (fun i => P.vertices.getD i B.source) n
      (directedStep_not_transGen_self B) (pathCutLeftHalf_seam_chain B P)
      (fun u w hs hu hw => pathCut_pathVertex_index B P
        (pathCutLeftHalf_leave_mem_path B P hs hu hw))
      (fun u w hs hu hw => pathCut_pathVertex_index B P
        (pathCutLeftHalf_enter_mem_path B P hs hu hw))
      ⟨t, rfl⟩ h).1 ⟨v, rfl⟩
    have key : ∀ x y, ReflTransGen (fun a b => B.map.directedStep a b ∧
        a ∈ Set.range (pathCutLeftHalfVertexMap B P) ∧
        b ∈ Set.range (pathCutLeftHalfVertexMap B P)) x y →
        ∀ x' y', pathCutLeftHalfVertexMap B P x' = x →
        pathCutLeftHalfVertexMap B P y' = y →
        ReflTransGen (pathCutLeftHalfDirectedMap B P).directedStep x' y' := by
      intro x y hxy
      induction hxy with
      | refl =>
        intro x' y' hx hy
        have : x' = y' := pathCutLeftHalfVertexMap_injective B P (hx.trans hy.symm)
        rw [this]
      | tail _ hst ih =>
        intro x' y' hx hy
        obtain ⟨hs, ⟨w', hw'⟩, _⟩ := hst
        refine (ih x' w' hx hw').trans (pathCutLeftHalf_reach_of_step B P ?_)
        rw [hw', hy]
        exact hs
    exact key _ _ hre v t rfl rfl

end LeftHalf

end DirectedDistances.PlanarMap

namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.PlanarMap DirectedDistances.KMSW Quiver
open scoped Classical
open DirectedDistances.RandomWalk DirectedDistances.PaperProofs.Section3

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A base isomorphism reflects directed steps. -/
theorem baseIso_step_reflect {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) {u v : MapVertex B.map}
    (h : C.map.directedStep (I.vertexEquiv u) (I.vertexEquiv v)) :
    B.map.directedStep u v := by
  obtain ⟨d', hd, ht, hu, hv⟩ := h
  refine ⟨I.toEquiv.symm d', fun hh => hd (by simpa using (I.missing_iff _).mpr hh),
    ?_, ?_, ?_⟩
  · exact (I.tail_iff _).mp (by simpa using ht)
  · refine I.vertexEquiv.injective ((I.vertexEquiv_dartTailVertex _).trans ?_)
    simpa [dartTailVertex] using hu
  · refine I.vertexEquiv.injective ((I.vertexEquiv_dartHeadVertex _).trans ?_)
    simpa [dartHeadVertex] using hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A base isomorphism reflects directed reachability. -/
theorem baseIso_reach_reflect {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] {ℓ r : ℕ}
    {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {C : BipolarTriangulationWithBoundaryBase E ℓ r}
    (I : BipolarBoundaryBaseIso B C) {u v : MapVertex B.map}
    (h : Relation.ReflTransGen C.map.directedStep (I.vertexEquiv u) (I.vertexEquiv v)) :
    Relation.ReflTransGen B.map.directedStep u v := by
  generalize hb : I.vertexEquiv v = b at h
  induction h generalizing v with
  | refl => rw [I.vertexEquiv.injective hb]
  | @tail b' c _ hs ih =>
    obtain ⟨w, hw⟩ := I.vertexEquiv.surjective b'
    exact (ih hw).tail (baseIso_step_reflect I (by rw [hw, hb]; exact hs))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Ancestor reachability of the relabelled left cut is exactly ancestor reachability of
its image in the original representative. -/
theorem cutLRep_ancestors_map_iff {x : XDP} {ℓ r n m : ℕ}
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (z v : MapVertex (cutLRep R hR).2.B.map) :
    z ∈ ancestors (presentation (cutLRep R hR).2 .left v) ↔
      cutLRepVertexMap R hR z ∈
        ancestors (presentation R .left (cutLRepVertexMap R hR v)) := by
  refine ⟨cutLRep_ancestors_map R hR z v, fun h => ?_⟩
  let P := selectedGeodesicOfLen R.B x hR
  let B := pathCutLeftHalfBase R.B P
  let I := (B.transportIso (Fintype.equivFin _)).symm
  have h1 : Relation.ReflTransGen R.B.map.directedStep
      (pathCutLeftHalfVertexMap R.B P (I.vertexEquiv z))
      (pathCutLeftHalfVertexMap R.B P (I.vertexEquiv v)) := h
  have h2 := (pathCutLeftHalf_reach_iff R.B P _ _).mpr h1
  exact baseIso_reach_reflect I h2

end DirectedDistances.PaperProofs.Section4
