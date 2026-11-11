module

public import DirectedDistances.KMSW.HatLimitRotation
public import DirectedDistances.KMSW.HatFaceRotation
public import DirectedDistances.PlanarMap.PlaneFaceSurvival
public import DirectedDistances.KMSW.StageTriangleCapSideForced
public import DirectedDistances.KMSW.CreationCapExactFrontier
public import DirectedDistances.KMSW.TwoSidedDrawingFaceClassification

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

The reachable restriction retains each reachable creation triangle as the very same
bounded complementary component, including its oriented bordering darts. This is
geometric survival, beyond the permutation conjugacy of `HatLimitRotation`. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The ambient drawing restricted to geometric edges with two reachable endpoints. -/
noncomputable abbrev hatRealizedDrawing (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) :=
  restrictDrawing (monotoneFamilyDrawing w hfin (monotone_family_all w))
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The entire three-arc frontier of a reachable triangle lies in the restriction. -/
theorem hatReachableCreationCap_frontier (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (j : TriangleCreationTime w)
    (hr : HatTriangleReachable w (stageTriangleRecord w j))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    frontier ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ⊆
      (hatRealizedDrawing w hfin).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
  have hedge (e : ℕ) (he : e ∈ [(stageTriangleRecord w j).1,
      (stageTriangleRecord w j).2.1, (stageTriangleRecord w j).2.2]) :
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) e ⊆
        (hatRealizedDrawing w hfin).image := by
    intro z hz
    have hret : MhatGeometricEdge w e := hr e he
    have hb : e < (kmswStage w (j.val + 1)).nextEdge := by
      obtain ⟨h1, h2, h3⟩ := triBound_stage w (j.val + 1)
        (stageTriangleRecord w j) (hi ▸ List.get_mem _ i)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
    have harc := familyDrawing_arc w hfin (monotone_family_all w)
      (j.val + 1) (⟨⟨e, hb⟩, false⟩)
    have hzP : z ∈ (P.arc (e, false)).image := by
      rw [harc]
      simpa only [stageEdgeTrace, dite_eq_left hb] using hz
    rw [restrictDrawing_image_eq]
    exact Or.inr ⟨⟨(e, false), hret⟩, hzP⟩
  rw [creationCap_frontier_eq_traces w j i hi]
  intro z hz
  rcases hz with (hz | hz) | hz
  · exact hedge _ (by simp) hz
  · exact hedge _ (by simp) hz
  · exact hedge _ (by simp) hz

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The surviving cap frontier is exactly the three retained geometric arc images,
with the original edge identities, including parallel edges. -/
theorem hatReachableCreationCap_frontier_eq_arcs (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (j : TriangleCreationTime w)
    (hr : HatTriangleReachable w (stageTriangleRecord w j))
    (i : Fin (kmswStage w (j.val + 1)).triangles.length)
    (hi : (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j) :
    let Q := hatRealizedDrawing w hfin
    let t := stageTriangleRecord w j
    ∃ a b c : {d : ℕ × Bool // MhatGeometricEdge w d.1},
      a.val = (t.1, false) ∧ b.val = (t.2.1, false) ∧ c.val = (t.2.2, false) ∧
      frontier ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region =
        (Q.arc a).image ∪ (Q.arc b).image ∪ (Q.arc c).image := by
  let t := stageTriangleRecord w j
  have h1 : MhatGeometricEdge w t.1 := hr t.1 (by simp [t])
  have h2 : MhatGeometricEdge w t.2.1 := hr t.2.1 (by simp [t])
  have h3 : MhatGeometricEdge w t.2.2 := hr t.2.2 (by simp [t])
  refine ⟨⟨(t.1, false), h1⟩, ⟨(t.2.1, false), h2⟩,
    ⟨(t.2.2, false), h3⟩, rfl, rfl, rfl, ?_⟩
  obtain ⟨hb1, hb2, hb3⟩ := triBound_stage w (j.val + 1)
    (stageTriangleRecord w j) (hi ▸ List.get_mem _ i)
  have htrace (e : ℕ) (hb : e < (kmswStage w (j.val + 1)).nextEdge)
      (he : MhatGeometricEdge w e) :
      stageEdgeTrace (familyQ w (monotone_family_all w) (j.val + 1)) e =
        ((hatRealizedDrawing w hfin).arc ⟨(e, false), he⟩).image := by
    rw [restrictDrawing_arc, familyDrawing_arc w hfin (monotone_family_all w)
      (j.val + 1) (⟨⟨e, hb⟩, false⟩)]
    simp only [stageEdgeTrace, dite_eq_left hb]
  rw [creationCap_frontier_eq_traces w j i hi,
    htrace _ hb1 h1, htrace _ hb2 h2, htrace _ hb3 h3]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A reachable ambient triangle survives with its cap set and every oriented border. -/
theorem hatReachableCreationCap_survives (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (j : TriangleCreationTime w)
    (hr : HatTriangleReachable w (stageTriangleRecord w j)) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := hatRealizedDrawing w hfin
    ∃ (i : Fin (kmswStage w (j.val + 1)).triangles.length)
      (F : PlaneFaces P) (G : PlaneFaces Q),
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
      G.val.val = F.val.val ∧
      ∀ d : {d : ℕ × Bool // MhatGeometricEdge w d.1},
        d.val ∈ stageTriangleDartList w j → Q.dartBorders d G.val := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
  let Q := hatRealizedDrawing w hfin
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  obtain ⟨F, hF, hborder⟩ := stageTriangleDarts_border_creation_cap w hfin j i hi
  have hopen : IsOpen F.val.val := by
    rw [hF]
    exact isOpen_graphRegion
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).low_continuous
      ((familyG w (monotone_family_all w) (j.val + 1)).cap i).high_continuous
  obtain ⟨G, hG⟩ := planeFace_survives P Q F hopen
    (restrictDrawing_image_subset P S (fun _ => Iff.rfl))
    (by rw [hF]; exact hatReachableCreationCap_frontier w hfin j hr i hi)
  refine ⟨i, F, G, hi, hF, hG, ?_⟩
  intro d hd
  exact dartBorders_transport P Q F.val G.val d.val d hG
    (restrictDrawing_arc P S (fun _ => Iff.rfl) d) (hborder d.val hd)

private theorem creation_east_eq_iff (w : ℕ → Fin 3) (j : TriangleCreationTime w) :
    edgeEast w (stageTriangleRecord w j).1 =
      edgeEast w (stageTriangleRecord w j).2.1 ↔ w j.val = 0 := by
  obtain ⟨i, hi⟩ := stageTriangleRecord_fin_index w j
  have hb := triBound_stage w (j.val + 1) _ (hi ▸ List.get_mem _ i)
  rw [← (edge_endpoints_eq w hb.1).2, ← (edge_endpoints_eq w hb.2.1).2]
  have ha := (kmswStage_boundary_ids_lt_nextEdge w j.val).1
  have hne := ne_of_lt ha
  have hne' : (kmswStage w j.val).active ≠ (kmswStage w j.val).nextEdge + 1 := by
    omega
  have hv := (kmswStage_endpoints_lt_nextVertex w j.val _ ha).2
  rcases j.property with h0 | h1
  · cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp [stageTriangleRecord, h0, kmswStage, kmswStep, kmswCodeStep,
        kmswStepOfStep, hp, State.addEdge, hne, hne']
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    simp [stageTriangleRecord, h1, kmswStage, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge, hne, hne', ne_of_lt hv]

private theorem creation_oriented_mem (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (d : ℕ × Bool) :
    d ∈ triangleOrientedDarts w (stageTriangleRecord w j) ↔
      d ∈ stageTriangleDartList w j := by
  have he := creation_east_eq_iff w j
  rcases j.property with h0 | h1
  · have hh := he.mpr h0
    unfold triangleOrientedDarts
    rw [ite_eq_left hh]
    cases hp : (kmswStage w j.val).UL.dropLast.reverse <;>
      simp only [stageTriangleDartList, stageTriangleDartTriple,
        stageTriangleRecord, h0, ↓reduceIte, hp,
        List.mem_cons, List.not_mem_nil, or_false]
    all_goals tauto
  · have h0 : w j.val ≠ 0 := by rw [h1]; decide
    have hh := mt he.mp h0
    unfold triangleOrientedDarts
    rw [ite_eq_right hh]
    simp only [stageTriangleDartList, stageTriangleDartTriple,
      stageTriangleRecord, h0, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false]

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The ordered local triangle word maps under H to the ambient oriented triangle word. -/
theorem hatLimit_triangleOrientedDarts (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (t : HatLocalTri w h) :
    (triangleOrientedDarts (hatCodes w h) t.val).map
        (fun d => (hatLimitDartEquiv w h d).val) =
      triangleOrientedDarts w (hatLimitFaceEquiv w h t).val := by
  obtain ⟨m, hm⟩ := t.property
  have hb := triBound_stage (hatCodes w h) m t.val hm
  have ht := hatAll_triangleOrientedDarts w h m t.val hm
  have hmap : ∀ d ∈ triangleOrientedDarts (hatCodes w h) t.val,
      (hatLimitDartEquiv w h d).val = (hatAllEdgeMap w h m d.1, d.2) := by
    intro d hd
    have he : d.1 = t.val.1 ∨ d.1 = t.val.2.1 ∨ d.1 = t.val.2.2 := by
      unfold triangleOrientedDarts at hd
      split at hd <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd <;>
        rcases hd with rfl | rfl | rfl <;> tauto
    have hbound : d.1 < (kmswStage (hatCodes w h) m).nextEdge := by
      rcases he with he | he | he
      · exact he ▸ hb.1
      · exact he ▸ hb.2.1
      · exact he ▸ hb.2.2
    rw [hatLimitDartEquiv_apply, hatLimitEdgeMap_eq_stage w h m _ hbound]
  rw [List.map_congr_left hmap]
  change _ = triangleOrientedDarts w
    (hatLimitEdgeMap w h t.val.1, hatLimitEdgeMap w h t.val.2.1,
      hatLimitEdgeMap w h t.val.2.2)
  rw [hatLimitEdgeMap_eq_stage w h m _ hb.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.1,
    hatLimitEdgeMap_eq_stage w h m _ hb.2.2]
  exact ht

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every stored compressed triangle has a surviving ambient cap, bordered by its three
H-darts. The ambient triangle has all its boundary vertices reachable. -/
theorem hatLocalTriangle_realized (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (t : HatLocalTri w h) :
    ∃ (j : TriangleCreationTime w)
      (i : Fin (kmswStage w (j.val + 1)).triangles.length)
      (F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)))
      (G : PlaneFaces (hatRealizedDrawing w hfin)),
      stageTriangleRecord w j = (hatLimitFaceEquiv w h t).val ∧
      HatTriangleReachable w (stageTriangleRecord w j) ∧
      (kmswStage w (j.val + 1)).triangles.get i = stageTriangleRecord w j ∧
      F.val.val = ((familyG w (monotone_family_all w) (j.val + 1)).cap i).region ∧
      G.val.val = F.val.val ∧
      ∀ d ∈ triangleOrientedDarts (hatCodes w h) t.val,
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) G.val := by
  obtain ⟨n, hn, hr⟩ := (hatLimitFaceEquiv w h t).property
  rw [← stageTriangleTimes_records] at hn
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hn
  have hreach : HatTriangleReachable w (stageTriangleRecord w j) := hj.symm ▸ hr
  obtain ⟨i, F, G, hi, hF, hG, hb⟩ :=
    hatReachableCreationCap_survives w hfin j hreach
  refine ⟨j, i, F, G, hj, hreach, hi, hF, hG, ?_⟩
  intro d hd
  apply hb
  apply (creation_oriented_mem w j _).mp
  rw [hj, ← hatLimit_triangleOrientedDarts w h t]
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Every finite limiting face orbit contains a recorded triangle dart. A finite outer
orbit is excluded by stabilization and the infinitely many distinct active edges. -/
theorem finiteFaceOrbit_mem_triangle (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc w hfin).SameCycle d e}.Finite) :
    ∃ j : TriangleCreationTime w, d ∈ stageTriangleDartList w j := by
  classical
  let f := kmswInfFaceSucc w hfin
  let C : Set (ℕ × Bool) := {e | f.SameCycle d e}
  have htime (e : ℕ × Bool) := kmswInfFaceSucc_eventually_eq_stage w hfin e
  let T : (ℕ × Bool) → ℕ := fun e => (htime e).choose
  obtain ⟨A, hA⟩ := (hfinite.image T).bddAbove
  have hbad : {n | act w n ∈ Prod.fst '' C}.Finite :=
    (hfinite.image Prod.fst).preimage (CutConverse.act_injective w).injOn
  obtain ⟨B, hB⟩ := hbad.bddAbove
  let n := max A (B + 1)
  have hstable (e : ℕ × Bool) (he : e ∈ C) :
      ∃ hb : e.1 < (kmswStage w n).nextEdge,
        f e = (((kmswMap w n).faceSucc (⟨e.1, hb⟩, e.2)).1.val,
          ((kmswMap w n).faceSucc (⟨e.1, hb⟩, e.2)).2) :=
    (htime e).choose_spec n ((hA (mem_image_of_mem T he)).trans (le_max_left _ _))
  obtain ⟨hd, _⟩ := hstable d (Equiv.Perm.SameCycle.refl f d)
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  rcases stage_dart_partition w n x with hx | ⟨j, hj, _⟩
  · have hclosed (z : StageDart (kmswStage w n).nextEdge)
        (hz : (z.1.val, z.2) ∈ C) :
        (((kmswMap w n).faceSucc z).1.val,
          ((kmswMap w n).faceSucc z).2) ∈ C := by
      obtain ⟨_, heq⟩ := hstable (z.1.val, z.2) hz
      rw [← heq]
      exact hz.apply_right
    have hxouter : (kmswStageDirectedMap w n).IsOuter x := by
      apply (kmswStage_isOuter_iff_boundary w n x).mpr
      rcases (stageOuterWord_mem_iff w n x).mp hx with ⟨hb, hm⟩ | ⟨hb, hm⟩
      · exact Or.inl ⟨hb, List.mem_append.mpr hm⟩
      · exact Or.inr ⟨hb, List.mem_append.mpr (hm.elim Or.inr Or.inl)⟩
    let y : StageDart (kmswStage w n).nextEdge :=
      (⟨act w n, act_lt_nextEdge w (le_refl n)⟩, false)
    have hyouter : (kmswStageDirectedMap w n).IsOuter y := by
      apply (kmswStage_isOuter_iff_boundary w n y).mpr
      obtain ⟨es, hes⟩ := kmswStage_UL_last w n
      left
      refine ⟨rfl, List.mem_append.mpr (Or.inl ?_)⟩
      change (kmswStage w n).active ∈ (kmswStage w n).UL
      rw [hes]
      exact List.mem_append_right _ (List.mem_cons_self)
    have hxy : (kmswMap w n).faceSucc.SameCycle x y := hxouter.symm.trans hyouter
    obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
    have hiter (k : ℕ) :
        ((((kmswMap w n).faceSucc ^ k) x).1.val,
          (((kmswMap w n).faceSucc ^ k) x).2) ∈ C := by
      induction k with
      | zero => exact Equiv.Perm.SameCycle.refl f d
      | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact hclosed _ ih
    have hyC : (act w n, false) ∈ C := by
      have hh := hiter k
      rw [hk] at hh
      exact hh
    have hnB : n ≤ B := hB (mem_image_of_mem Prod.fst hyC)
    have hn : B + 1 ≤ n := le_max_right _ _
    omega
  · exact ⟨j, hj.2⟩

private theorem cycle3_orbit_mem {D : Type*} (f : Equiv.Perm D) (a b c d e : D)
    (hc : FaceSucc3Cycle f a b c) (hd : d ∈ [a, b, c])
    (he : f.SameCycle d e) : e ∈ [a, b, c] := by
  have hfwd (x : D) (hx : x ∈ [a, b, c]) : f x ∈ [a, b, c] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hc.1]; exact List.mem_cons.mpr (Or.inr (List.mem_cons_self))
    · rw [hc.2.1]; exact List.mem_cons.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self))))
    · rw [hc.2.2.1]; exact List.mem_cons_self
  have hinv (x : D) (hx : x ∈ [a, b, c]) : f.symm x ∈ [a, b, c] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [f.symm_apply_eq.mpr hc.2.2.1.symm]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self))))
    · rw [f.symm_apply_eq.mpr hc.1.symm]; exact List.mem_cons_self
    · rw [f.symm_apply_eq.mpr hc.2.1.symm]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons_self))
  have hpos (n : ℕ) : (f : D → D)^[n] d ∈ [a, b, c] := by
    induction n with
    | zero => exact hd
    | succ n ih => rw [Function.iterate_succ_apply']; exact hfwd _ ih
  have hneg (n : ℕ) : (f.symm : D → D)^[n] d ∈ [a, b, c] := by
    induction n with
    | zero => exact hd
    | succ n ih => rw [Function.iterate_succ_apply']; exact hinv _ ih
  obtain ⟨z, rfl⟩ := he
  cases z with
  | ofNat n =>
      change (f ^ (n : ℤ)) d ∈ [a, b, c]
      simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hpos n
  | negSucc n =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow,
        Equiv.Perm.inv_def] using hneg (n + 1)

private theorem cycle3_sameCycle_of_mem {D : Type*} (f : Equiv.Perm D)
    (a b c d e : D) (hc : FaceSucc3Cycle f a b c)
    (hd : d ∈ [a, b, c]) (he : e ∈ [a, b, c]) : f.SameCycle d e := by
  have hmem (x : D) (hx : x ∈ [a, b, c]) : f.SameCycle a x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
    · rw [hx, ← hc.1]; exact (Equiv.Perm.SameCycle.refl f a).apply_right
    · rw [hx, ← hc.2.1, ← hc.1]
      exact ((Equiv.Perm.SameCycle.refl f a).apply_right).apply_right
  exact (hmem d hd).symm.trans (hmem e he)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A finite compressed face orbit is exactly a creation triangle. Its H-images border
a surviving reachable ambient triangle, with the unchanged cap as its face set. -/
theorem hatFiniteFaceOrbit_realized (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    let u := hatCodes w h
    let f := kmswInfFaceSucc u (hatCodes_finiteIncidence w h hfin)
    ∃ (j : TriangleCreationTime u) (k : TriangleCreationTime w)
      (i : Fin (kmswStage w (k.val + 1)).triangles.length)
      (F : PlaneFaces (monotoneFamilyDrawing w hfin (monotone_family_all w)))
      (G : PlaneFaces (hatRealizedDrawing w hfin)),
      (∀ e, f.SameCycle d e ↔ e ∈ stageTriangleDartList u j) ∧
      FaceSucc3Cycle f (stageTriangleDartTriple u j).1
        (stageTriangleDartTriple u j).2.1 (stageTriangleDartTriple u j).2.2 ∧
      stageTriangleRecord w k =
        (hatLimitEdgeMap w h (stageTriangleRecord u j).1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.1,
          hatLimitEdgeMap w h (stageTriangleRecord u j).2.2) ∧
      HatTriangleReachable w (stageTriangleRecord w k) ∧
      (kmswStage w (k.val + 1)).triangles.get i = stageTriangleRecord w k ∧
      F.val.val = ((familyG w (monotone_family_all w) (k.val + 1)).cap i).region ∧
      G.val.val = F.val.val ∧
      ∀ e, f.SameCycle d e →
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h e) G.val := by
  let u := hatCodes w h
  let hf := hatCodes_finiteIncidence w h hfin
  let f := kmswInfFaceSucc u hf
  obtain ⟨j, hd⟩ := finiteFaceOrbit_mem_triangle u hf d hfinite
  have hc := kmswInfFaceSucc_stageTriangle_cycle u hf j
  obtain ⟨i0, hi0⟩ := stageTriangleRecord_fin_index u j
  let t : HatLocalTri w h := ⟨stageTriangleRecord u j, j.val + 1,
    hi0 ▸ List.get_mem _ i0⟩
  obtain ⟨k, i, F, G, hk, hr, hi, hF, hG, hb⟩ :=
    hatLocalTriangle_realized w h hfin t
  have horbit (e : ℕ × Bool) : f.SameCycle d e ↔ e ∈ stageTriangleDartList u j := by
    constructor
    · exact cycle3_orbit_mem f _ _ _ d e hc hd
    · exact cycle3_sameCycle_of_mem f _ _ _ d e hc hd
  refine ⟨j, k, i, F, G, horbit, hc, hk, hr, hi, hF, hG, ?_⟩
  intro e he
  apply hb
  exact (creation_oriented_mem u j e).mpr ((horbit e).mp he)

private theorem limitExternal_of_no_triangle (w : ℕ → Fin 3) (d : ℕ × Bool)
    (hd : ∀ j : TriangleCreationTime w, d ∉ stageTriangleDartList w j) :
    limitExternalDart w d := by
  refine ⟨d.1, fun n hn => ?_⟩
  have hb := kmsw_nextEdge_unbounded w d.1 n hn
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hb⟩, d.2)
  rcases stage_dart_partition w n x with hx | ⟨j, hj, _⟩
  · refine ⟨hb, (kmswStage_isOuter_iff_boundary w n x).mpr ?_⟩
    rcases (stageOuterWord_mem_iff w n x).mp hx with ⟨hs, hm⟩ | ⟨hs, hm⟩
    · exact Or.inl ⟨hs, List.mem_append.mpr hm⟩
    · exact Or.inr ⟨hs, List.mem_append.mpr (hm.elim Or.inr Or.inl)⟩
  · exact (hd j hj.2).elim

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Finite limiting face orbits are exactly the nonpersistent external darts.
The statement concerns permutations; it makes no claim about unbounded components. -/
theorem finiteFaceOrbit_iff_not_external (w : ℕ → Fin 3)
    (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool) :
    {e | (kmswInfFaceSucc w hfin).SameCycle d e}.Finite ↔ ¬ limitExternalDart w d := by
  classical
  constructor
  · intro hf he
    obtain ⟨j, hj⟩ := finiteFaceOrbit_mem_triangle w hfin d hf
    exact stageTriangleDart_not_limitExternal w j d hj he
  · intro he
    by_contra hf
    apply he
    apply limitExternal_of_no_triangle w d
    intro j hj
    apply hf
    apply (stageTriangleDartList w j).finite_toSet.subset
    intro e hde
    exact cycle3_orbit_mem _ _ _ _ d e
      (kmswInfFaceSucc_stageTriangle_cycle w hfin j) hj hde

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
All successive H-darts follow the restricted drawing's face successor in order.
This holds for every orbit, including the persistent external darts. -/
theorem hatRealizedFaceSuccessor_iterate (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (n : ℕ) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let S := {d : ℕ × Bool | MhatGeometricEdge w d.1}
    let g := fun e => (drawingFirstReturnPerm P S).symm
      (restrictedFlip P S (fun _ => Iff.rfl) e)
    hatLimitDartEquiv w h
        ((kmswInfFaceSucc (hatCodes w h) (hatCodes_finiteIncidence w h hfin) :
          (ℕ × Bool) → ℕ × Bool)^[n] d) =
      g^[n] (hatLimitDartEquiv w h d) := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact hatLimitDartEquiv_faceSuccessor w h hfin _

private theorem face_eq_of_border {D V : Type*} {flip : D → D}
    {rot : Equiv.Perm D} {vert : D → V} (P : PLDrawing D V flip rot vert)
    (F G : P.Face) (d : D) (hF : P.dartBorders d F) (hG : P.dartBorders d G) :
    F = G := by
  obtain ⟨δF, hδF, hF⟩ := hF
  obtain ⟨δG, hδG, hG⟩ := hG
  let t := min δF δG / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htF : t < δF := by
    have hh := min_le_left δF δG
    dsimp [t]
    linarith
  have htG : t < δG := by
    have hh := min_le_right δF δG
    dsimp [t]
    linarith
  exact P.faces_eq_of_mem (hF t t ht htF ht htF) (hG t t ht htG ht htG)

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The surviving bounded face bordered by a finite compressed orbit is unique. -/
theorem hatFiniteFaceOrbit_unique_face (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) (d : ℕ × Bool)
    (hfinite : {e | (kmswInfFaceSucc (hatCodes w h)
      (hatCodes_finiteIncidence w h hfin)).SameCycle d e}.Finite) :
    ∃! G : PlaneFaces (hatRealizedDrawing w hfin),
      ∀ e, (kmswInfFaceSucc (hatCodes w h)
        (hatCodes_finiteIncidence w h hfin)).SameCycle d e →
        (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h e) G.val := by
  obtain ⟨_, _, _, _, G, _, _, _, _, _, _, _, hb⟩ :=
    hatFiniteFaceOrbit_realized w h hfin d hfinite
  refine ⟨G, hb, ?_⟩
  intro G' hG'
  apply Subtype.ext
  exact face_eq_of_border (hatRealizedDrawing w hfin) G'.val G.val
    (hatLimitDartEquiv w h d) (hG' d (Equiv.Perm.SameCycle.refl _ _))
    (hb d (Equiv.Perm.SameCycle.refl _ _))

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
A bounded complementary component must border some finite compressed face orbit.
Combined with `hatFiniteFaceOrbit_realized` and uniqueness of a face bordering a
fixed oriented dart, this would exclude any new bounded region formed by deletion. -/
@[expose] def hatBoundedFaceFiniteBorderGoal (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : hatLimitFiniteIncidence w) : Prop :=
  ∀ G : PlaneFaces (hatRealizedDrawing w hfin), ∃ d : ℕ × Bool,
    (hatRealizedDrawing w hfin).dartBorders (hatLimitDartEquiv w h d) G.val ∧
      {e | (kmswInfFaceSucc (hatCodes w h)
        (hatCodes_finiteIncidence w h hfin)).SameCycle d e}.Finite

/- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
its darts with the persistent external orbit. Successor order is already proved by
`hatRealizedFaceSuccessor_iterate`; this goal supplies its geometric interpretation. -/
@[expose] def hatUnboundedFaceIdentificationGoal (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : hatLimitFiniteIncidence w) : Prop :=
  let Q := hatRealizedDrawing w hfin
  let u := hatCodes w h
  let f := kmswInfFaceSucc u (hatCodes_finiteIncidence w h hfin)
  ∃ U : Q.Face, Q.IsUnbounded U ∧
    (∀ F : Q.Face, Q.IsUnbounded F → F = U) ∧
    (∀ d, Q.dartBorders (hatLimitDartEquiv w h d) U ↔ limitExternalDart u d) ∧
    (∀ d, limitExternalDart u d ↔ f.SameCycle futureMapOuterDart d)

end DirectedDistances.KMSW
