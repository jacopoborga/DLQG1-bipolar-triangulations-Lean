module

public import DirectedDistances.KMSW.PrimedSimCrossing
import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.CutEquivalenceConverse










public section
namespace DirectedDistances.KMSW

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
field, recorded so its entry obstruction can be stated exactly. -/
@[expose] def PrimedURUnreachable (u w : ℕ → Fin 3) (m : ℕ)
    (vφ : ℕ → ℕ) : Prop :=
  ∀ e ∈ (kmswMissingRootStage u m).UR,
    ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨vφ ((kmswMissingRootStage u m).west e)⟩

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
retained cut sides, which may have two reachable endpoints. This definition
does not assert preservation or imply crossing freshness for the cut sides. -/
@[expose] def PrimedURUnreachableOrCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k m : ℕ) (eφ vφ : ℕ → ℕ) : Prop :=
  ∀ e ∈ (kmswMissingRootStage u m).UR,
    (¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨vφ ((kmswMissingRootStage u m).west e)⟩) ∨
      eφ e ∈ cutAtExit w h k

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
UR is empty, so the proposed field holds vacuously. -/
theorem primedInitial_URUnreachable (u w : ℕ → Fin 3) (vφ : ℕ → ℕ) :
    PrimedURUnreachable u w 0 vφ := by
  intro e he
  change e ∈ ([] : List ℕ) at he
  cases he

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
the missing UR edge has local west vertex `2` and east vertex `1`.
Under the entry maps these are the terminal and initial endpoints,
respectively, of the old global active edge. -/
theorem primedFirstStep_UR_cut_geometry (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    let sh := kmswMissingRootStage u 1
    let gl := kmswStage w (walkNL w h 0 - 1)
    sh.UR = [2] ∧ sh.present 2 = false ∧ sh.west 2 = 2 ∧ sh.east 2 = 1 ∧
      primedFirstStepEdgeMap w (walkNL w h 0) 2 = gl.active ∧
      primedFirstStepVertexMap w (walkNL w h 0) (sh.west 2) =
        gl.east gl.active ∧
      primedFirstStepVertexMap w (walkNL w h 0) (sh.east 2) =
        gl.west gl.active := by
  simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep,
    kmswStepOfStep, kmswMissingRootInit, kmswInit, State.addEdge,
    primedFirstStepEdgeMap, primedFirstStepVertexMap]

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
first missing UR side are reachable. Thus even the weaker assertion that
each such side has at least one unreachable endpoint fails at entry. -/
theorem primedFirstStep_UR_both_reachable (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    let sh := kmswMissingRootStage u 1
    let vφ := primedFirstStepVertexMap w (walkNL w h 0)
    2 ∈ sh.UR ∧
      Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨vφ (sh.west 2)⟩ ∧
      Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨vφ (sh.east 2)⟩ := by
  have hg := primedFirstStep_UR_cut_geometry u w h hu
  have hr := flowLine_firstLeftExit_triangle w h
  dsimp only at hg hr ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hg.1]
    exact List.mem_cons_self
  · rw [hg.2.2.2.2.2.1]
    exact hr.2.2.1
  · rw [hg.2.2.2.2.2.2]
    exact hr.2.1

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
simulation violates the proposed UR unreachability field. -/
theorem primedFirstStep_not_URUnreachable (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    ¬ PrimedURUnreachable u w 1
      (primedFirstStepVertexMap w (walkNL w h 0)) := by
  intro hn
  have hr := primedFirstStep_UR_both_reachable u w h hu
  exact hn 2 hr.1 hr.2.1

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
holds at the first active entry; its sole UR edge uses the cut exception. -/
theorem primedFirstStep_URUnreachableOrCut (u w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hu : u 0 = 1) :
    PrimedURUnreachableOrCut u w h 0 1
      (primedFirstStepEdgeMap w (walkNL w h 0))
      (primedFirstStepVertexMap w (walkNL w h 0)) := by
  intro e he
  have hg := primedFirstStep_UR_cut_geometry u w h hu
  rw [hg.1] at he
  have he2 : e = 2 := List.mem_singleton.mp he
  subst e
  right
  rw [hg.2.2.2.2.1]
  exact active_mem_cutAtExit w h 0

/-- P2 helper for `lem-quad-kmsw`, primed half; not counted
of the counterexample geometry: at global first exit `1`, local missing
UR edge `2` maps to present global root edge `0`, with endpoint images
`1` and `0`. Reachability of the two images is established separately by
`primedFirstStep_UR_both_reachable` for genuine entry simulations. -/
theorem primedURUnreachable_counterexample_geometry :
    let u : ℕ → Fin 3 := fun _ => 1
    let w := primedCrossingTestCode
    let sh := kmswMissingRootStage u 1
    sh.UR = [2] ∧ sh.present 2 = false ∧
      primedFirstStepEdgeMap w 1 2 = 0 ∧
      (kmswStage w 0).present 0 = true ∧
      primedFirstStepVertexMap w 1 (sh.west 2) = 1 ∧
      primedFirstStepVertexMap w 1 (sh.east 2) = 0 ∧
      L w 1 = L w 0 - 1 := by
  decide

private theorem invariant_local_bounds (u : ℕ → Fin 3) (m e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR) :
    e < (kmswMissingRootStage u m).nextEdge ∧
      (kmswMissingRootStage u m).west e < (kmswMissingRootStage u m).nextVertex := by
  obtain ⟨hv, hE, hw, _, _, _, _, _, hUR, _, _⟩ := kmswMissingRootStage_agree u m
  have hb : e < (kmswStage u m).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u m).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (hUR ▸ he))))
  exact ⟨hE.symm ▸ hb, by rw [hw, hv]; exact (kmswStage_endpoints_lt_nextVertex u m e hb).1⟩

/-- P2 helper; not counted (`lem-quad-kmsw`,
cut-exempt UR invariant, in both allocation branches. -/
theorem primedURUnreachableOrCut_step_left
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 0) :
    PrimedURUnreachableOrCut u w h k (m + 1)
      (primedOrdinaryLeftEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ)
      (primedOrdinaryLeftVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ) := by
  let sh := kmswMissingRootStage u m
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .left := by
    simp only [kmswMissingRootStage, hu]; rfl
  intro e he
  have heold : e ∈ sh.UR := by
    rw [hl] at he
    cases hp : sh.UL.dropLast.reverse <;>
      simpa only [kmswStepOfStep, hp, State.addEdge] using he
  obtain ⟨hb, hv⟩ := invariant_local_bounds u m e heold
  change e < sh.nextEdge at hb
  change sh.west e < sh.nextVertex at hv
  have hwest : (kmswMissingRootStage u (m + 1)).west e = sh.west e := by
    rw [hl]
    cases hp : sh.UL.dropLast.reverse <;>
      simp [kmswStepOfStep, hp, State.addEdge, ne_of_lt hb,
        show e ≠ sh.nextEdge + 1 from by omega]
  have hext := primedLeft_maps_extend sh (kmswStage w n) eφ vφ
  change (¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
    ⟨primedOrdinaryLeftVertexMap sh (kmswStage w n) vφ
      ((kmswMissingRootStage u (m + 1)).west e)⟩) ∨ _
  rw [hwest, hext.2 _ hv, hext.1 e hb]
  exact hinv e heold

/-- P2 helper; not counted (`lem-quad-kmsw`,
or leaves an empty UR; no surviving endpoint or map changes. -/
theorem primedURUnreachableOrCut_step_down
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 2) :
    PrimedURUnreachableOrCut u w h k (m + 1) eφ vφ := by
  let sh := kmswMissingRootStage u m
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .down := by
    simp only [kmswMissingRootStage, hu]; rfl
  intro e he
  rw [hl] at he ⊢
  cases hp : sh.UR with
  | nil => simp only [kmswStepOfStep, hp, State.addEdge, List.not_mem_nil] at he
  | cons a as =>
    simp only [kmswStepOfStep, hp] at he ⊢
    apply hinv e
    change e ∈ sh.UR
    rw [hp]
    exact List.mem_cons_of_mem a he

/-- P2 helper; not counted (`lem-quad-kmsw`,
their pre-exit stage, even though they are missing in the primed map. -/
theorem cutAtExit_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k e : ℕ) (he : e ∈ cutAtExit w h k) :
    (kmswStage w (walkNL w h k - 1)).present e = true := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hb := (kmswStage_boundary_ids_lt_nextEdge (hatCodes w h)
    (hatExitIndex w h k)).2 f (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hf)))
  have hp := (hatAll_sim w h (hatExitIndex w h k)).incidenceSim.present f hb
    ((kmswStage_status (hatCodes w h) (hatExitIndex w h k)).2.1 f hf)
  rwa [quadrantRStageTime_hatExitIndex] at hp

/-- P2 helper; not counted (`lem-quad-kmsw`,
at the next pre-exit stage: its unique activation already occurred. -/
theorem cutAtExit_ne_next_exit_active (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (k e : ℕ) (he : e ∈ cutAtExit w h k) :
    e ≠ (kmswStage w (walkNL w h (k + 1) - 1)).active := by
  obtain ⟨j, hj, hej⟩ := stagePresent_exists_active w (walkNL w h k - 1) e
    (cutAtExit_edge_bound w h k e he) (cutAtExit_present w h k e he)
  intro heq
  have ht := CutConverse.act_injective w (hej.symm.trans heq)
  have hn := (walkNL_spec w h k).1
  have hr := (walkNR_succ_spec w h k).1
  have hl := (walkNL_spec w h (k + 1)).1
  omega

private theorem UL_endpoints_ne_later_east (u : ℕ → Fin 3) (a b f : ℕ)
    (hab : a + 1 ≤ b) (hu : u a = 2) (hf : f ∈ (kmswStage u a).UL) :
    (kmswStage u b).east (act u b) ≠ (kmswStage u a).west f ∧
      (kmswStage u b).east (act u b) ≠ (kmswStage u a).east f := by
  have hwest (g : ℕ) (hg : g ∈ (kmswStage u a).UL) :
      (kmswStage u b).east (act u b) ≠ (kmswStage u a).west g := by
    have hb := (kmswStage_boundary_ids_lt_nextEdge u a).2 g (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hg)))
    obtain ⟨j, hj, hgj⟩ := stagePresent_exists_active u a g hb
      ((kmswStage_status u a).2.1 g hg)
    have hw := (edge_endpoints_eq u hb).1
    rw [hw, hgj]
    exact activeEast_ne_activeInitial u (by omega : j ≤ b)
  refine ⟨hwest f hf, ?_⟩
  have he : (kmswStage u a).east f ∈
      (kmswStage u a).UL.reverse.map (kmswStage u a).east :=
    List.mem_map.mpr ⟨f, List.mem_reverse.mpr hf, rfl⟩
  rw [CutConverse.ul_coherent u a] at he
  rcases List.mem_cons.mp he with he | he
  · have hd : (kmswStage u (a + 1)).west (act u (a + 1)) =
        (kmswStage u a).east (act u a) := by
      have hstage : kmswStage u (a + 1) = kmswStepOfStep (kmswStage u a) .down := by
        simp only [kmswStage, hu]; rfl
      rw [act, hstage]
      cases hp : (kmswStage u a).UR with
      | nil => simp [kmswStepOfStep, hp, State.addEdge, act]
      | cons e es =>
        have hh := (kmswStage_boundary_chain_invariant u a).2.2.2.2.2.1 e es hp
        simp [kmswStepOfStep, hp, hh, act]
    have hb := act_lt_nextEdge u (le_refl (a + 1))
    have hi := (edge_endpoints_eq u hb).1
    have hinit : activeInitial u (a + 1) = (kmswStage u a).east f := by
      exact hi.symm.trans (hd.trans he.symm)
    rw [← hinit]
    exact activeEast_ne_activeInitial u hab
  · obtain ⟨g, hg, hgf⟩ := List.mem_map.mp (List.mem_of_mem_dropLast he)
    rw [← hgf]
    exact hwest g (List.mem_reverse.mp hg)

/-- P2 helper; not counted (`lem-quad-kmsw`,
is the terminal endpoint of the next pre-exit active edge. In the hatted
map, old UL west vertices have already been initial vertices; its terminal
vertex becomes an initial vertex at the intervening down replacement. -/
theorem cutAtExit_endpoints_ne_next_exit_east (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k e : ℕ) (he : e ∈ cutAtExit w h k) :
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    edgeWest w e ≠ gl.east gl.active ∧ edgeEast w e ≠ gl.east gl.active := by
  let u := hatCodes w h
  let a := hatExitIndex w h k
  let b := hatExitIndex w h (k + 1)
  have hab : a + 1 ≤ b := by
    by_contra hn
    have hm := quadrantRStageTime_mono w h (show b ≤ a by omega)
    simp only [a, b, quadrantRStageTime_hatExitIndex] at hm
    have h0 := (walkNL_spec w h k).1
    have h1 := (walkNR_succ_spec w h k).1
    have h2 := (walkNL_spec w h (k + 1)).1
    omega
  have sa := (hatAll_sim w h a).incidenceSim
  have sb := (hatAll_sim w h b).incidenceSim
  rw [show quadrantRStageTime w h a = walkNL w h k - 1 from
    quadrantRStageTime_hatExitIndex w h k] at sa
  rw [show quadrantRStageTime w h b = walkNL w h (k + 1) - 1 from
    quadrantRStageTime_hatExitIndex w h (k + 1)] at sb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hfB : f < (kmswStage u a).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u a).2 f (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hf)))
  have hends := kmswStage_endpoints_lt_nextVertex u a f hfB
  have hsep := UL_endpoints_ne_later_east u a b f hab (hatCodes_at_exit w h k) hf
  have hactB := act_lt_nextEdge u (le_refl b)
  have hnewB := (kmswStage_endpoints_lt_nextVertex u b (act u b) hactB).2
  have hi := (sb.incidence (act u b) hactB).2
  dsimp only [act, u] at hi
  rw [sb.active] at hi
  have hne (v : ℕ) (hv : v < (kmswStage u a).nextVertex)
      (hvne : (kmswStage u b).east (act u b) ≠ v) :
      hatAllVertexMap w h a v ≠
        (kmswStage w (walkNL w h (k + 1) - 1)).east
          (kmswStage w (walkNL w h (k + 1) - 1)).active := by
    intro heq
    rw [← hatAllVertexMap_eq_of_le w h a b v (by omega) hv, hi] at heq
    exact hvne (sb.vertex_injective v _
      (hv.trans_le (CutConverse.nextVertex_mono u (by omega))) hnewB heq).symm
  have hb := sa.edge_bound f hfB
  have heg := edge_endpoints_eq w hb
  have hia := sa.incidence f hfB
  dsimp only
  rw [← heg.1, ← heg.2, hia.1, hia.2]
  exact ⟨hne _ hends.1 hsep.1, hne _ hends.2 hsep.2⟩

private theorem UR_west_image_endpoint
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ) (e : ℕ)
    (he : e ∈ (kmswMissingRootStage u m).UR) :
    vφ ((kmswMissingRootStage u m).west e) = edgeWest w (eφ e) ∨
      vφ ((kmswMissingRootStage u m).west e) = edgeEast w (eφ e) := by
  have hb := (invariant_local_bounds u m e he).1
  have hp : (kmswMissingRootStage u m).present e = false := by
    by_cases hz : e = 0
    · subst e; exact kmswMissingRootStage_present_zero u m
    · obtain ⟨_, hE, _, _, hp, _, _, _, hUR, _, _⟩ := kmswMissingRootStage_agree u m
      rw [hp e hz]
      exact ((kmswStage_status u m).1 e (hE ▸ hb)).mpr (Or.inl (hUR ▸ he))
  have hi := sim.missing_incidence e hb hp
  have hs := edge_endpoints_eq w (sim.edge_bound e hb)
  have hm : vφ ((kmswMissingRootStage u m).west e) ∈
      ({edgeWest w (eφ e), edgeEast w (eφ e)} : Multiset ℕ) := by
    rw [← hs.1, ← hs.2, hi]
    exact Multiset.mem_cons_self _ _
  simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] using hm

/-- P2 helper; not counted (`lem-quad-kmsw`,
invariant implies both UR freshness goals G1 and G2. -/
theorem PrimedSimActive.crossing_UR_separation_of_unreachableOrCut
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    (∀ e ∈ sh.UR, eφ e ≠ gl.active) ∧
      (∀ e ∈ sh.UR, vφ (sh.west e) ≠ gl.east gl.active) := by
  let gl := kmswStage w (walkNL w h (k + 1) - 1)
  have hr := flowLine_leftExit_triangle w h (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega] at hr
  have hg := edge_endpoints_eq w ((kmswStage_boundary_ids_lt_nextEdge w
    (walkNL w h (k + 1) - 1)).1)
  dsimp only
  constructor
  · intro e he heq
    rcases hinv e he with hn | hc
    · rcases UR_west_image_endpoint sim e he with hw | ht
      · rw [heq, ← hg.1] at hw
        apply hn
        rw [hw]
        exact hr.1
      · rw [heq, ← hg.2] at ht
        apply hn
        rw [ht]
        exact hr.2.1
    · exact cutAtExit_ne_next_exit_active w h k (eφ e) hc heq
  · intro e he heq
    rcases hinv e he with hn | hc
    · apply hn
      rw [heq]
      exact hr.2.1
    · have hs := cutAtExit_endpoints_ne_next_exit_east w h k (eφ e) hc
      rcases UR_west_image_endpoint sim e he with hw | ht
      · exact hs.1 (hw.symm.trans heq)
      · exact hs.2 (ht.symm.trans heq)

/-- P2 helper; not counted (`lem-quad-kmsw`,
both injectivity fields of the crossing maps. It does not establish the
remaining boundary-image, face-order, or cut-identification fields. -/
theorem PrimedSimActiveRootLR.crossing_injective_of_unreachableOrCut
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m (walkNR w h (k + 1) - 1) eφ vφ)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ) (hu : u m = 1) :
    let sh := kmswMissingRootStage u m
    let gl := kmswStage w (walkNL w h (k + 1) - 1)
    let eψ := primedCrossingEdgeMap sh gl eφ
    let vψ := primedCrossingVertexMap sh gl vφ
    (∀ e f, e < (kmswMissingRootStage u (m + 1)).nextEdge →
      f < (kmswMissingRootStage u (m + 1)).nextEdge → eψ e = eψ f → e = f) ∧
    (∀ v z, v < (kmswMissingRootStage u (m + 1)).nextVertex →
      z < (kmswMissingRootStage u (m + 1)).nextVertex → vψ v = vψ z → v = z) := by
  have hs := sim.forget.crossing_UR_separation_of_unreachableOrCut hinv
  exact ⟨(sim.forget.crossing_edge_injective_iff hu).mpr hs.1,
    (sim.crossing_vertex_injective_iff_UR hu).mpr hs.2⟩

private theorem R_before_hit (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (a j : ℕ) (haj : a ≤ j) (hj : j < firstFlowRHit w h a) :
    R w a ≤ R w j := by
  classical
  induction j, haj using Nat.le_induction with
  | base => exact le_rfl
  | succ j haj ih =>
    have hp := ih (by omega)
    have hs : R w (j + 1) = R w j +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w j)).2 :=
      Finset.sum_range_succ _ _
    have hlow : -1 ≤ (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w j)).2 := by
      generalize w j = c
      fin_cases c <;> decide
    have hne : R w (j + 1) ≠ R w a - 1 := by
      intro heq
      exact (Nat.find_min (h.2 a) hj) ⟨by omega, heq⟩
    omega

private theorem UR_balanced (w : ℕ → Fin 3) (a b : ℕ) (hab : a ≤ b)
    (hfloor : ∀ j, a ≤ j → j ≤ b → R w a ≤ R w j) :
    ∃ p : List ℕ, (kmswStage w b).UR = p ++ (kmswStage w a).UR ∧
      (p.length : ℤ) = R w b - R w a := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨[], rfl, by simp⟩
  | succ b hab ih =>
    obtain ⟨p, hp, hlen⟩ := ih (fun j hj hjb => hfloor j hj (by omega))
    have hn := hfloor (b + 1) (by omega) le_rfl
    have hs : R w (b + 1) = R w b +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (w b)).2 :=
      Finset.sum_range_succ _ _
    generalize hc : w b = c
    fin_cases c
    · have hr : R w (b + 1) = R w b := by
        simpa [hc, DirectedDistances.RandomWalk.lazyTwoDimensionalStep] using hs
      refine ⟨p, ?_, by omega⟩
      cases hpred : (kmswStage w b).UL.dropLast.reverse <;>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
          kmswStepOfStep, hpred, State.addEdge] using hp
    · have hr : R w (b + 1) = R w b + 1 := by
        simpa [hc, DirectedDistances.RandomWalk.lazyTwoDimensionalStep] using hs
      refine ⟨((kmswStage w b).nextEdge + 1) :: p, ?_, ?_⟩
      · simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
          kmswStepOfStep, State.addEdge, List.cons_append] using
          congrArg (List.cons ((kmswStage w b).nextEdge + 1)) hp
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
    · have hr : R w (b + 1) = R w b - 1 := by
        simpa [hc, DirectedDistances.RandomWalk.lazyTwoDimensionalStep,
          sub_eq_add_neg] using hs
      cases p with
      | nil => simp only [List.length_nil, Nat.cast_zero] at hlen; omega
      | cons e es =>
        refine ⟨es, ?_, ?_⟩
        · simp [kmswStage, hc, kmswStep, kmswCodeStep,
            kmswStepOfStep, hp]
        · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
          omega

private theorem UR_or_present_later (w : ℕ → Fin 3) (a b e : ℕ)
    (hab : a ≤ b) (he : e ∈ (kmswStage w a).UR) :
    e ∈ (kmswStage w b).UR ∨ (kmswStage w b).present e = true := by
  have hbound := (kmswStage_boundary_ids_lt_nextEdge w a).2 e (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr he)))
  induction b, hab using Nat.le_induction with
  | base => exact Or.inl he
  | succ b hab ih =>
    rcases ih with hu | hp
    · generalize hc : w b = c
      fin_cases c
      · left
        cases hpred : (kmswStage w b).UL.dropLast.reverse <;>
          simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
            kmswStepOfStep, hpred, State.addEdge] using hu
      · left
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
          kmswStepOfStep, State.addEdge, List.mem_cons] using Or.inr hu
      · cases hur : (kmswStage w b).UR with
        | nil => rw [hur] at hu; cases hu
        | cons f fs =>
          rw [hur] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · right
            simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur]
          · left
            simpa [kmswStage, hc, kmswStep, kmswCodeStep, ↓reduceIte,
              kmswStepOfStep, hur] using hu
    · right
      exact (present_mono w (hbound.trans_le (kmswStage_nextEdge_mono w hab))
        hp (b + 1) (Nat.le_succ b)).2

/-- P2 helper; not counted (`lem-quad-kmsw`,
an L interval is unreachable. Its new UR side is activated before re-entry,
at a time when the active west vertex is unreachable. -/
theorem lPhase_up_fresh_vertex_unreachable (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (k n : ℕ) (hn : walkNL w h k ≤ n)
    (hnr : n + 1 < walkNR w h (k + 1)) (hw : w n = 1) :
    ¬ Quiver.Reachable (⟨0⟩ : PresentVertex w) ⟨(kmswStage w n).nextVertex⟩ := by
  let b := firstFlowRHit w h (n + 1)
  let e := (kmswStage w n).nextEdge + 1
  have hs : R w (n + 1) = R w n + 1 := by
    simp [R, Finset.sum_range_succ, hw,
      DirectedDistances.RandomWalk.lazyTwoDimensionalStep]
  have hb := firstFlowRHit_spec w h (n + 1)
  change n + 1 + 1 ≤ b ∧ R w b = R w (n + 1) - 1 at hb
  have hbase : R w (walkNL w h k) ≤ R w n :=
    R_before_hit w h (walkNL w h k) n hn (by
      change n < walkNR w h (k + 1)
      omega)
  have hbr : b < walkNR w h (k + 1) := by
    by_contra hnot
    have hr := (walkNR_succ_spec w h k).2
    rcases Nat.eq_or_lt_of_le (show walkNR w h (k + 1) ≤ b by omega) with heq | hlt
    · rw [← heq] at hb
      omega
    · have hf := R_before_hit w h (n + 1) (walkNR w h (k + 1)) (by omega) hlt
      omega
  have hfloor : ∀ j, n ≤ j → j ≤ b → R w n ≤ R w j := by
    intro j hnj hjb
    by_cases hje : j = n
    · subst j; exact le_rfl
    by_cases hjend : j = b
    · subst j; omega
    have hj := R_before_hit w h (n + 1) j (by omega) (by omega)
    omega
  obtain ⟨p, hp, hplen⟩ := UR_balanced w n b (by omega) hfloor
  have hpn : p = [] := List.length_eq_zero_iff.mp (by omega)
  have hURb : (kmswStage w b).UR = (kmswStage w n).UR := by
    simpa [hpn, List.nil_append] using hp
  have he : e ∈ (kmswStage w (n + 1)).UR := by
    simp [e, kmswStage, hw, kmswStep, kmswCodeStep, kmswStepOfStep]
  have heB : e < (kmswStage w (n + 1)).nextEdge := by
    simp [e, kmswStage, hw, kmswStep, kmswCodeStep,
      kmswStepOfStep, State.addEdge]
  have hpresent : (kmswStage w b).present e = true := by
    rcases UR_or_present_later w (n + 1) b e (by omega) he with hu | hp
    · rw [hURb] at hu
      have heold := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr hu)))
      dsimp only [e] at heold
      omega
    · exact hp
  obtain ⟨j, hjb, hej⟩ := stagePresent_exists_active w b e
    (heB.trans_le (kmswStage_nextEdge_mono w (by omega))) hpresent
  have hnj : n < j := by
    by_contra hnot
    have ha := act_lt_nextEdge w (show j ≤ n by omega)
    rw [← hej] at ha
    dsimp only [e] at ha
    omega
  have hewest : edgeWest w e = (kmswStage w n).nextVertex := by
    rw [← (edge_endpoints_eq w heB).1]
    simp [e, kmswStage, hw, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
  have hun := lPhase_activeWest_unreachable w h k j (by omega) (by omega)
  rw [(edge_endpoints_eq w (act_lt_nextEdge w (le_refl j))).1, ← hej, hewest] at hun
  exact hun

/-- P2 helper; not counted (`lem-quad-kmsw`,
cut-exempt invariant. The fresh missing side uses unreachability, rather
than the cut exception; all old UR sides retain their endpoints and maps. -/
theorem PrimedSimActive.URUnreachableOrCut_step_up
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActive u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ)
    (hu : u m = 1) (hw : w n = 1) :
    PrimedURUnreachableOrCut u w h k (m + 1)
      (kmswShiftUpEdgeMap (kmswMissingRootStage u m) (kmswStage w n) eφ)
      (kmswShiftUpVertexMap (kmswMissingRootStage u m) (kmswStage w n) vφ) := by
  let sh := kmswMissingRootStage u m
  let gl := kmswStage w n
  have hl : kmswMissingRootStage u (m + 1) = kmswStepOfStep sh .up := by
    simp only [kmswMissingRootStage, hu]; rfl
  have hbounds := sim.ordinary_bounds hm
  intro e he
  have hcases : e = sh.nextEdge + 1 ∨ e ∈ sh.UR := by
    simpa only [hl, kmswStepOfStep, List.mem_cons] using he
  rcases hcases with rfl | heold
  · left
    have hfresh := lPhase_up_fresh_vertex_unreachable w h k n
      hbounds.1 hbounds.2 hw
    simpa [hl, kmswStepOfStep, State.addEdge, kmswShiftUpVertexMap, sh, gl] using hfresh
  · obtain ⟨hb, hv⟩ := invariant_local_bounds u m e heold
    change e < sh.nextEdge at hb
    change sh.west e < sh.nextVertex at hv
    have hext := primedUp_maps_extend sh gl eφ vφ
    have hwest : (kmswMissingRootStage u (m + 1)).west e = sh.west e := by
      simp [hl, kmswStepOfStep, State.addEdge, ne_of_lt hb,
        show e ≠ sh.nextEdge + 1 from by omega]
    change (¬ Quiver.Reachable (⟨0⟩ : PresentVertex w)
      ⟨kmswShiftUpVertexMap sh gl vφ ((kmswMissingRootStage u (m + 1)).west e)⟩) ∨ _
    rw [hwest, hext.2 _ hv, hext.1 e hb]
    exact hinv e heold

/-- P2 helper; not counted (`lem-quad-kmsw`,
extending maps preserving both the active root-LR simulation and the
cut-exempt UR invariant. This covers all three letters and both left
allocation branches, within one fixed interval. -/
theorem primedSimActiveRootLR_ordinary_step_unreachableOrCut
    {u w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m n : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR u w h k m n eφ vφ)
    (hm : m < primedIntervalBase (primedSimInput w) h k +
      primedIntervalWidth (primedSimInput w) h k)
    (hinv : PrimedURUnreachableOrCut u w h k m eφ vφ)
    (c : Fin 3) (hu : u m = c) (hw : w n = c) :
    ∃ eφ' vφ',
      (∀ e, e < (kmswMissingRootStage u m).nextEdge → eφ' e = eφ e) ∧
      (∀ v, v < (kmswMissingRootStage u m).nextVertex → vφ' v = vφ v) ∧
      PrimedSimActiveRootLR u w h k (m + 1) (n + 1) eφ' vφ' ∧
      PrimedURUnreachableOrCut u w h k (m + 1) eφ' vφ' := by
  fin_cases c
  · have hi := primedURUnreachableOrCut_step_left (n := n) hinv hu
    cases hp : (kmswMissingRootStage u m).UL.dropLast.reverse with
    | nil =>
      refine ⟨_, _, (primedUp_maps_extend _ _ eφ vφ).1,
        (primedUp_maps_extend _ _ eφ vφ).2, sim.step_left_empty hm hu hw hp, ?_⟩
      simpa only [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, hp,
        ↓reduceIte] using hi
    | cons a as =>
      refine ⟨_, _, (primedLeft_nonempty_maps_extend (kmswMissingRootStage u m) (kmswStage w n) eφ vφ).1,
        (primedLeft_nonempty_maps_extend (kmswMissingRootStage u m) (kmswStage w n) eφ vφ).2,
        primedSimActiveRootLR_left_nonempty sim hm hu hw hp, ?_⟩
      simpa only [primedOrdinaryLeftEdgeMap, primedOrdinaryLeftVertexMap, hp,
        List.cons_ne_nil, ↓reduceIte] using hi
  · exact ⟨_, _, (primedUp_maps_extend _ _ eφ vφ).1,
      (primedUp_maps_extend _ _ eφ vφ).2, sim.step_up hm hu hw,
      sim.forget.URUnreachableOrCut_step_up hm hinv hu hw⟩
  · exact ⟨eφ, vφ, fun _ _ => rfl, fun _ _ => rfl, sim.step_down hm hu hw,
      primedURUnreachableOrCut_step_down hinv hu⟩















































end DirectedDistances.KMSW
