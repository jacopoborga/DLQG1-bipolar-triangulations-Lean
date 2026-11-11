module

public import DirectedDistances.KMSW.MonotoneStageCertificate
import DirectedDistances.PlanarMap.GraphRegionClosure
import DirectedDistances.PlanarMap.FiniteDrawingExterior
import DirectedDistances.KMSW.StageBoundaryMap






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

variable {w : ℕ → Fin 3} {n : ℕ} {P : StageDrawing w n}

private theorem trace_subset_image (e : ℕ) : stageEdgeTrace P e ⊆ P.image := by
  unfold stageEdgeTrace
  split
  · intro z hz
    exact Or.inr ⟨_, hz⟩
  · exact empty_subset _

private theorem cap_frontier_subset_image (G : MonotoneStageCertificate w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    frontier (G.cap i).region ⊆ P.image := by
  change frontier (graphRegion _ _ _ _) ⊆ _
  rw [frontier_graphRegion_eq (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
    (G.cap i).left_join (G.cap i).right_join]
  rw [G.cap_lower_trace i, G.cap_upper_trace i]
  rintro z (hz | hz)
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact trace_subset_image e hz
  · obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨_, hz⟩ := mem_iUnion.mp hz
    exact trace_subset_image e hz



theorem monotoneStage_cap_faces (G : MonotoneStageCertificate w n P) :
    ∀ i, ∃ F : P.Face, F.val = (G.cap i).region := by
  intro i
  have hc := isPathConnected_graphRegion (G.cap i).ab (G.cap i).low_continuous
    (G.cap i).high_continuous (G.cap i).separated
  obtain ⟨z, hz⟩ := hc.nonempty
  have hzX : z ∉ P.image := (disjoint_left.mp (G.cap_avoid i)) hz
  refine ⟨⟨(G.cap i).region, z, hzX, ?_⟩, rfl⟩
  exact (connectedComponentIn_compl_eq_of_open_connected
    (isOpen_graphRegion (G.cap i).low_continuous (G.cap i).high_continuous)
    hc.isConnected hc.nonempty (disjoint_iff_inter_eq_empty.mp (G.cap_avoid i))
    (cap_frontier_subset_image G i) hz).symm

private theorem exterior_frontier_subset_image (G : MonotoneStageCertificate w n P) :
    frontier (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ ⊆ P.image := by
  rw [frontier_compl]
  intro z hz
  have hclosed := isClosed_closedGraphRegion G.lower_continuous G.upper_continuous
  have hzK := hclosed.frontier_subset hz
  by_contra hzX
  rw [← G.cover] at hzK
  rcases hzK with hzK | hzK
  · exact hzX hzK
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hzK
    rw [closure_eq_self_union_frontier] at hi
    rcases hi with hi | hi
    · have hopen : IsOpen (G.cap i).region :=
        isOpen_graphRegion (G.cap i).low_continuous (G.cap i).high_continuous
      have hsub : (G.cap i).region ⊆
          closedGraphRegion G.xmin G.xmax G.lower G.upper := by
        rw [← G.cover]
        intro q hq
        exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hq⟩)
      have hinter := interior_mono hsub (hopen.interior_eq.symm ▸ hi)
      exact (mem_frontier_iff_notMem_interior (hclosed.frontier_subset hz)).mp hz hinter
    · exact hzX (cap_frontier_subset_image G i hi)



theorem monotoneStage_exterior_face (G : MonotoneStageCertificate w n P) :
    ∃ U : P.Face,
      U.val = (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ ∧
      P.IsUnbounded U ∧ ∀ F : P.Face, P.IsUnbounded F → F = U := by
  let E := (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ
  have hc : IsPathConnected E := isPathConnected_compl_closedGraphRegion G.hx
    G.lower_continuous G.upper_continuous G.lower_le_upper
  have hsub : P.image ⊆ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
    rw [← G.cover]
    exact subset_union_left
  have hdisj : Disjoint E P.image := disjoint_left.mpr fun _ hz hx => hz (hsub hx)
  obtain ⟨z, hz⟩ := hc.nonempty
  have heq := connectedComponentIn_compl_eq_of_open_connected
    (isClosed_closedGraphRegion G.lower_continuous G.upper_continuous).isOpen_compl
    hc.isConnected hc.nonempty (disjoint_iff_inter_eq_empty.mp hdisj)
    (exterior_frontier_subset_image G) hz
  let U : P.Face := ⟨E, z, disjoint_left.mp hdisj hz, heq.symm⟩
  have hU : P.IsUnbounded U := by
    intro R
    exact exists_norm_gt_compl_closedGraphRegion G.lower_continuous
      G.upper_continuous G.lower_le_upper R
  refine ⟨U, rfl, hU, ?_⟩
  obtain ⟨F₀, _, huniq⟩ := P.existsUnique_unbounded_face
  intro F hF
  exact (huniq F hF).trans (huniq U hU).symm



theorem kmswStage_isOuter_iff_boundary (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    (kmswStageDirectedMap w n).IsOuter d ↔
      (d.2 = false ∧ d.1.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR) ∨
      (d.2 = true ∧ d.1.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false =>
    simp only [Bool.false_eq_true, false_and, or_false, true_and, List.mem_append]
    constructor
    · intro ho
      cases hp : (kmswStage w n).present e.val with
      | false =>
        exact Or.inr ((kmswStageDirectedMap_UR_west w n e).mp ⟨hp, ho⟩)
      | true =>
        apply Or.inl
        apply (kmswStageDirectedMap_UL_bridge w n e).mpr
        exact ⟨by change ¬ (kmswStage w n).present e.val = false; simp [hp],
          ⟨hp, rfl⟩, ho⟩
    · rintro (he | he)
      · exact ((kmswStageDirectedMap_UL_bridge w n e).mp he).2.2
      · exact ((kmswStageDirectedMap_UR_west w n e).mpr he).2
  | true =>
    simp only [Bool.true_eq_false, false_and, false_or, true_and, List.mem_append]
    constructor
    · intro ho
      cases hp : (kmswStage w n).present e.val with
      | false =>
        exact Or.inl ((kmswStageDirectedMap_LL_east w n e).mp ⟨hp, ho⟩)
      | true =>
        apply Or.inr
        apply (kmswStageDirectedMap_LR_bridge w n e).mpr
        refine ⟨?_, ?_, ho⟩
        · change ¬ (kmswStage w n).present e.val = false
          simp [hp]
        · change ¬ ((kmswStage w n).present e.val = true ∧ true = false)
          simp
    · rintro (he | he)
      · exact ((kmswStageDirectedMap_LL_east w n e).mpr he).2
      · exact ((kmswStageDirectedMap_LR_bridge w n e).mp he).2.2

private theorem wedge_incompatible {p dir : ℂ} {S K : Set ℂ}
    (hS : WedgeIn p dir S) (hsub : S ⊆ K) (hK : WedgeIn p dir Kᶜ) : False := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hS
  obtain ⟨δ₂, hδ₂, h₂⟩ := hK
  let t := min δ₁ δ₂ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₁ : t < δ₁ :=
    (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_left δ₁ δ₂)
  have ht₂ : t < δ₂ :=
    (half_lt_self (lt_min hδ₁ hδ₂)).trans_le (min_le_right δ₁ δ₂)
  exact h₂ t t ht ht₂ ht ht₂ (hsub (h₁ t t ht ht₁ ht ht₁))

private theorem cap_subset_closed (G : MonotoneStageCertificate w n P)
    (i : Fin (kmswStage w n).triangles.length) :
    (G.cap i).region ⊆ closedGraphRegion G.xmin G.xmax G.lower G.upper := by
  rw [← G.cover]
  intro z hz
  exact Or.inr (mem_iUnion.mpr ⟨i, subset_closure hz⟩)




theorem monotoneStage_dartBorders_exterior_iff
    (G : MonotoneStageCertificate w n P) (U : P.Face)
    (hU : U.val = (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ)
    (hcovL : ∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∨
        ∃ i, e.val ∈ G.capLower i)
    (hcovU : ∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR ∨
        ∃ i, e.val ∈ G.capUpper i)
    (d : StageDart (kmswStage w n).nextEdge) :
    P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d := by
  change WedgeIn (P.arc d).start (P.arc d).initialDirection U.val ↔ _
  rw [hU, kmswStage_isOuter_iff_boundary]
  rcases d with ⟨e, b⟩
  cases b with
  | false =>
    simp only [Bool.false_eq_true, false_and, or_false, true_and]
    constructor
    · intro hext
      rcases hcovL e with he | ⟨i, hi⟩
      · exact he
      · exact (wedge_incompatible (G.cap_lower_wedge i e.val e.isLt hi)
          (cap_subset_closed G i) hext).elim
    · exact G.ext_upper_wedge e.val e.isLt
  | true =>
    simp only [Bool.true_eq_false, false_and, false_or, true_and]
    constructor
    · intro hext
      rcases hcovU e with he | ⟨i, hi⟩
      · exact he
      · exact (wedge_incompatible (G.cap_upper_wedge i e.val e.isLt hi)
          (cap_subset_closed G i) hext).elim
    · exact G.ext_lower_wedge e.val e.isLt



theorem monotoneStage_face_partition (G : MonotoneStageCertificate w n P)
    (hcovL : ∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).UL ++ (kmswStage w n).UR ∨
        ∃ i, e.val ∈ G.capLower i)
    (hcovU : ∀ e : Fin (kmswStage w n).nextEdge,
      e.val ∈ (kmswStage w n).LL ++ (kmswStage w n).LR ∨
        ∃ i, e.val ∈ G.capUpper i) :
    (∀ i, ∃ F : P.Face, F.val = (G.cap i).region) ∧
      ∃ U : P.Face,
        U.val = (closedGraphRegion G.xmin G.xmax G.lower G.upper)ᶜ ∧
        P.IsUnbounded U ∧
        (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
        ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d := by
  obtain ⟨U, hU, hbound, huniq⟩ := monotoneStage_exterior_face G
  exact ⟨monotoneStage_cap_faces G, U, hU, hbound, huniq,
    monotoneStage_dartBorders_exterior_iff G U hU hcovL hcovU⟩

end DirectedDistances.KMSW
