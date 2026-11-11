module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
import DirectedDistances.KMSW.InftyCutSequence
import DirectedDistances.KMSW.CommonFutureM0
import DirectedDistances.KMSW.UIBOTBoundaryShift
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryRoutes

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk



private theorem separator_window_arrow (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (e : a ⟶ b) :
    EdgePresent w (kmswWindowEdgeMapInf w n e.val) ∧
      edgeWest w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n a.id ∧
      edgeEast w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n b.id := by
  obtain ⟨m, hm, hp⟩ := e.property.1
  have hr := kmswWindowPatchData_rel w n m
  have hg : kmswWindowEdgeMapInf w n e.val < (kmswStage w (n + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.edge_bound e.val hm
  refine ⟨⟨n + m, hg, ?_⟩, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.present e.val hm hp
  · rw [← (edge_endpoints_eq w hg).1,
      kmswWindowEdgeMapInf_west w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).1, e.property.2.1]
  · rw [← (edge_endpoints_eq w hg).2,
      kmswWindowEdgeMapInf_east w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).2, e.property.2.2]



private theorem separator_window_path (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (q : Path a b) :
    ∃ p : Path (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n b.id⟩,
      p.vertices = q.vertices.map
        (fun v => (⟨kmswWindowVertexMapInf w n v.id⟩ : PresentVertex w)) := by
  induction q with
  | nil => exact ⟨Path.nil, rfl⟩
  | cons q e ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.cons ⟨kmswWindowEdgeMapInf w n e.val,
      separator_window_arrow w n e⟩, ?_⟩
    simp only [Path.vertices_cons, List.concat_eq_append, List.map_append,
      List.map_cons, List.map_nil, hp]



private theorem separator_boundary_connector (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (k : ℤ) :
    ∃ d : ℤ, Nonempty (Path (boundaryPresentVertex w h0 d)
      (⟨kmswWindowVertexMapInf w n
        (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)) := by
  obtain ⟨m, hm⟩ := boundaryVertex_allocated (fun i => w (n + i)) hn k
  have hb := (kmswWindowPatchVertexMap_rel w n m).vertex_bound _ hm
  rw [← kmswWindowVertexMapInf_eq_stage w n m _ hm] at hb
  obtain ⟨d, _, _, _, _, ⟨p⟩⟩ := stage_cell_lower_boundary_route w h0 (n + m)
    (⟨kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn k)⟩ : StagePresentVertex w (n + m)) hb
  exact ⟨d, ⟨(stageToLimit w (n + m)).mapPath p⟩⟩



private theorem separator_reachable_preimage (w : ℕ → Fin 3) (n : ℕ)
    (a : PresentVertex (fun i => w (n + i))) (b z : PresentVertex w)
    (c : Path b (⟨kmswWindowVertexMapInf w n a.id⟩ : PresentVertex w))
    (hc : z ∉ c.vertices) (havoid : FiniteAvoidance b z)
    (t : ℕ → PresentVertex (fun i => w (n + i))) (ht : Function.Injective t)
    (hreach : ∀ j, Reachable a (t j)) :
    ∃ v : PresentVertex (fun i => w (n + i)), Reachable a v ∧
      (⟨kmswWindowVertexMapInf w n v.id⟩ : PresentVertex w) = z := by
  let F : PresentVertex (fun i => w (n + i)) → PresentVertex w :=
    fun v => ⟨kmswWindowVertexMapInf w n v.id⟩
  have hF : Function.Injective F := by
    intro x y hxy
    have hid := kmswWindowVertexMapInf_injective w n (congrArg PresentVertex.id hxy)
    cases x
    cases y
    cases hid
    rfl
  have hbase : ∀ j, Reachable b (F (t j)) := by
    intro j
    obtain ⟨q⟩ := hreach j
    obtain ⟨p, _⟩ := separator_window_path w n q
    exact ⟨c.comp p⟩
  obtain ⟨N, hN⟩ := finiteAvoidance_eventually_forces_path_through havoid
    (fun j => F (t j)) (hF.comp ht) hbase
  obtain ⟨q⟩ := hreach N
  obtain ⟨p, hp⟩ := separator_window_path w n q
  have hz := hN N le_rfl (c.comp p)
  rw [Path.vertices_comp] at hz
  have hzp : z ∈ p.vertices := by
    rcases List.mem_append.mp hz with hzc | hzp
    · exact (hc (List.dropLast_subset _ hzc)).elim
    · exact hzp
  rw [hp] at hzp
  obtain ⟨v, hv, hvz⟩ := List.mem_map.mp hzp
  obtain ⟨r, _, _⟩ := q.exists_eq_comp_of_mem_vertices hv
  exact ⟨v, ⟨r⟩, hvz⟩



theorem cell_sdp_ae_shifted_boundary_commonSequence :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n : ℕ,
      ∀ hn : BoundaryHitWitnesses (fun i => ω (n + i + 1)),
        BusemannCommonSequenceHypothesis
          (boundaryPresentVertex (fun i => ω (n + i + 1)) hn) := by
  rw [ae_all_iff]
  intro n
  have h : ∀ᵐ ω ∂iidCodeMeasure.map (codeShift n),
      ∀ hn : BoundaryHitWitnesses (fun i => ω (i + 1)),
        BusemannCommonSequenceHypothesis
          (boundaryPresentVertex (fun i => ω (i + 1)) hn) := by
    rw [map_codeShift]
    exact iidCodes_ae_boundaryCommonSequence
  have ht := (Measure.tendsto_ae_map (measurable_codeShift n).aemeasurable).eventually h
  have htail (ω : ℕ → Fin 3) :
      (fun i => codeShift n ω (i + 1)) = fun i => ω (n + i + 1) := by
    funext i
    simp only [codeShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_assoc]
  filter_upwards [ht] with ω hω
  rw [htail ω] at hω
  exact hω




theorem cell_sdp_separator_targets :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
        ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ ℓ k : ℤ,
          ∃ y : ℕ → PresentVertex (fun i => w (n + i)),
            Function.Injective y ∧
            (∀ j, Reachable
              (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
              Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
                (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
            (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
              (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) := by
  classical
  filter_upwards [ae_cutWindow_finiteAvoidance_infinite,
    cell_sdp_ae_shifted_boundary_commonSequence] with ω hcuts hcommon
  dsimp only
  intro n h0 hn ℓ k
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let u : ℕ → Fin 3 := fun i => w (n + i)
  let σn : ℤ := ((kmswStage w n).UR.length + 1 : ℕ)
  let a : PresentVertex u := boundaryPresentVertex u hn k
  let b : PresentVertex u := boundaryPresentVertex u hn σn
  let F : PresentVertex u → PresentVertex w :=
    fun v => ⟨kmswWindowVertexMapInf w n v.id⟩
  have hF : Function.Injective F := by
    intro x y hxy
    have hid := kmswWindowVertexMapInf_injective w n (congrArg PresentVertex.id hxy)
    cases x
    cases y
    cases hid
    rfl
  obtain ⟨t, ht, hreach⟩ := hcommon n hn k σn
  obtain ⟨d, ⟨c⟩⟩ := separator_boundary_connector w n h0 hn k
  obtain ⟨d', ⟨c'⟩⟩ := separator_boundary_connector w n h0 hn σn
  let K : ℕ := ℓ.natAbs + d.natAbs + d'.natAbs
  have bounds (r : ℤ) (hr : r.natAbs ≤ K) : -(K : ℤ) ≤ r ∧ r ≤ K := by
    have hhi : r ≤ (r.natAbs : ℤ) := Int.le_natAbs
    have hlo : -(r.natAbs : ℤ) ≤ r := by
      cases r <;> simp
      omega
    have hr' : (r.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hr
    constructor <;> omega
  have hℓ := bounds ℓ (by dsimp [K]; omega)
  have hd := bounds d (by dsimp [K]; omega)
  have hd' := bounds d' (by dsimp [K]; omega)
  let C : Set (PresentVertex w) := {z | ∀ r : ℤ, -(K : ℤ) ≤ r → r ≤ K →
    FiniteAvoidance (boundaryPresentVertex w h0 r) z}
  have hC : C.Infinite := hcuts h0 K
  let E : Set (PresentVertex w) := {z | z ∈ c.vertices} ∪ {z | z ∈ c'.vertices}
  have hE : E.Finite := c.vertices.finite_toSet.union c'.vertices.finite_toSet
  have hgood : (C \ E).Infinite := hC.sdiff hE
  have hpre (z : PresentVertex w) (hz : z ∈ C \ E) :
      ∃ v : PresentVertex u, (Reachable a v ∧ Reachable b v) ∧ F v = z := by
    have hzC : ∀ r : ℤ, -(K : ℤ) ≤ r → r ≤ K →
        FiniteAvoidance (boundaryPresentVertex w h0 r) z := hz.1
    have hzc : z ∉ c.vertices := fun h => hz.2 (Or.inl h)
    have hzc' : z ∉ c'.vertices := fun h => hz.2 (Or.inr h)
    obtain ⟨v, hav, hv⟩ := separator_reachable_preimage w n a
      (boundaryPresentVertex w h0 d) z c hzc (hzC d hd.1 hd.2)
      t ht (fun j => (hreach j).1)
    obtain ⟨v', hbv', hv'⟩ := separator_reachable_preimage w n b
      (boundaryPresentVertex w h0 d') z c' hzc' (hzC d' hd'.1 hd'.2)
      t ht (fun j => (hreach j).2)
    have hvv' : v = v' := hF (hv.trans hv'.symm)
    exact ⟨v, ⟨hav, hvv' ▸ hbv'⟩, hv⟩
  let e : ℕ ↪ {z : PresentVertex w // z ∈ C \ E} := hgood.natEmbedding
  choose y hyreach hyimage using fun j => hpre (e j).val (e j).property
  refine ⟨y, ?_, hyreach, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (hyimage i).symm.trans ((congrArg F hij).trans (hyimage j))
  · intro j
    have hz := (e j).property.1 ℓ hℓ.1 hℓ.2
    change FiniteAvoidance (boundaryPresentVertex w h0 ℓ) (F (y j))
    rw [hyimage j]
    exact hz

end DirectedDistances.PaperProofs.Section7
