module

public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorClass
public import DirectedDistances.KMSW.RightBoundaryRightmost
public import DirectedDistances.KMSW.StageLimitEmbedding
import DirectedDistances.KMSW.StageInfiniteOutgoingOrder














public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

section Boundary

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric right boundary follows exactly the permanent right-record edges, -/
theorem ancestor_rightmostPath_edge_eq (i : ℕ) :
    (kmswRightmostPath w hfin hL htrans hR 0).edge i =
      kmswRightBoundaryEdge w i := by
  have horbit (j : ℕ) : kmswRightmostOrbit w hfin hL htrans hR 0 j =
      edgeWest w (kmswRightBoundaryEdge w j) := by
    induction j with
    | zero =>
      exact (kmswRightBoundary_infinite_present_path w hL hR).2.2.1.symm
    | succ j ih =>
      change edgeEast w (kmswRightmostOutgoingEdge w hfin hL htrans hR
        (kmsw_vertex_allocated_of_finite_incidence w hfin)
        (kmswRightmostOrbit w hfin hL htrans hR 0 j)) = _
      rw [ih]
      have he : kmswRightmostOutgoingEdge w hfin hL htrans hR
          (kmsw_vertex_allocated_of_finite_incidence w hfin)
          (edgeWest w (kmswRightBoundaryEdge w j)) = kmswRightBoundaryEdge w j := by
        cases j with
        | zero =>
          rw [(kmswRightBoundary_infinite_present_path w hL hR).2.2.1]
          exact kmswRightmostOutgoingEdge_source w hfin hL htrans hR _
        | succ j =>
          exact kmswRightBoundaryEdge_is_rightmost w hfin hL htrans hR (by omega)
      rw [he]
      exact (kmswRightBoundary_infinite_present_path w hL hR).2.1 j
  change kmswRightmostOutgoingEdge w hfin hL htrans hR
    (kmsw_vertex_allocated_of_finite_incidence w hfin)
    (kmswRightmostOrbit w hfin hL htrans hR 0 i) = _
  rw [horbit]
  cases i with
  | zero =>
    rw [(kmswRightBoundary_infinite_present_path w hL hR).2.2.1]
    exact kmswRightmostOutgoingEdge_source w hfin hL htrans hR _
  | succ i =>
    exact kmswRightBoundaryEdge_is_rightmost w hfin hL htrans hR (by omega)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The indexed geometric boundary darts have the same permanent IDs as the finite -/
theorem ancestor_boundaryDart_eq (a : ThinMapSide) (i : ℕ) :
    thinMapBoundaryDart w hfin hL htrans hR a i =
      (match a with
        | .left => kmswLeftBoundaryEdge w i
        | .right => kmswRightBoundaryEdge w i, false) := by
  cases a with
  | left => rfl
  | right =>
    exact congrArg (fun e => (e, false))
      (ancestor_rightmostPath_edge_eq w hfin hL htrans hR i)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The head-based geometric target and the tail-based permanent boundary target agree -/
theorem ancestor_boundaryVertex_eq (a : ThinMapSide) (s : ℕ) :
    thinMapBoundaryVertex w hfin hL htrans hR a s =
      edgeWest w (match a with
        | .left => kmswLeftBoundaryEdge w s
        | .right => kmswRightBoundaryEdge w s) := by
  cases a with
  | left =>
    cases s with
    | zero => exact (boundary_target_tail_eq w htrans hL hR .left 0).symm
    | succ i => exact (boundary_target_tail_eq w htrans hL hR .left (i + 1)).symm
  | right =>
    cases s with
    | zero => exact (boundary_target_tail_eq w htrans hL hR .right 0).symm
    | succ i =>
      change edgeEast w ((kmswRightmostPath w hfin hL htrans hR 0).edge i) = _
      rw [ancestor_rightmostPath_edge_eq]
      exact (boundary_target_tail_eq w htrans hL hR .right (i + 1)).symm

end Boundary

private theorem ancestor_firstReturn_forward
    {A B : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) (k : ℕ) (hk : 0 < k)
    (he : (σ : A → A)^[k] d.1 = e.1)
    (hgap : ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) :
    ∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
  have hex : ∀ n, n ≤ k → ∃ m : ℕ, n ≤ m ∧ (n = 0 → m = 0) ∧
      (τ : B → B)^[m] (f d.1) = f ((σ : A → A)^[n] d.1) ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨0, le_rfl, fun _ => rfl, rfl, fun j hj hjm => by omega⟩
    | succ n ih =>
        intro hnk
        obtain ⟨m, hnm, hm0, hm, havoid⟩ := ih (by omega)
        obtain ⟨l, hl, hlstep, hlavoid⟩ := hn ((σ : A → A)^[n] d.1)
        refine ⟨m + l, by omega, by omega, ?_, ?_⟩
        · rw [Nat.add_comm m l, Function.iterate_add_apply, hm, hlstep]
          rw [Function.iterate_succ_apply']
        · intro j hj hjml hmem
          by_cases hjm : j < m
          · exact havoid j hj hjm hmem
          · by_cases hjme : j = m
            · subst j
              obtain ⟨a, ha, hea⟩ := hmem
              have hnpos : 0 < n := by
                by_contra h
                have hn0 : n = 0 := by omega
                have := hm0 hn0
                omega
              apply hgap n hnpos (by omega)
              exact (hf (hea.trans hm)).symm ▸ ha
            · have hjpos : 0 < j - m := by omega
              have hjlt : j - m < l := by omega
              apply hlavoid (j - m) hjpos hjlt
              obtain ⟨a, _, hea⟩ := hmem
              refine ⟨a, ?_⟩
              have hjdecomp : j - m + m = j := by omega
              have hh := Function.iterate_add_apply (τ : B → B) (j - m) m (f d.1)
              rw [hjdecomp, hm] at hh
              exact hea.trans hh
  obtain ⟨m, hkm, _, hm, havoid⟩ := hex k le_rfl
  exact ⟨m, by omega, hm.trans (congrArg f he), havoid⟩

private theorem ancestor_firstReturn_image_iff
    {A B : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (τ : Equiv.Perm B) (f : A → B) (hf : Function.Injective f)
    (hn : ∀ d, ∃ k : ℕ, 0 < k ∧ (τ : B → B)^[k] (f d) = f (σ d) ∧
      ∀ j : ℕ, 0 < j → j < k → (τ : B → B)^[j] (f d) ∉ Set.range f)
    (U : Set A) (d e : U) :
    (∃ k : ℕ, 0 < k ∧ (σ : A → A)^[k] d.1 = e.1 ∧
      ∀ j : ℕ, 0 < j → j < k → (σ : A → A)^[j] d.1 ∉ U) ↔
    (∃ m : ℕ, 0 < m ∧ (τ : B → B)^[m] (f d.1) = f e.1 ∧
      ∀ j : ℕ, 0 < j → j < m → (τ : B → B)^[j] (f d.1) ∉ f '' U) := by
  classical
  constructor
  · rintro ⟨k, hk, he, hgap⟩
    exact ancestor_firstReturn_forward σ τ f hf hn U d e k hk he hgap
  · rintro ⟨l, hl, hlend, hlgap⟩
    let k := firstReturnTime σ U d
    let z := firstReturn σ U d
    have hs := firstReturnTime_spec σ U d
    have hc := firstReturn_characterization σ U d
    obtain ⟨m, hm, he, hgap⟩ :=
      ancestor_firstReturn_forward σ τ f hf hn U d z k hs.1 hc.1 hc.2
    have hml : m = l := by
      apply Nat.le_antisymm
      · by_contra h
        exact hgap l hl (by omega) ⟨e.1, e.2, hlend.symm⟩
      · by_contra h
        exact hlgap m hm (by omega) ⟨z.1, z.2, he.symm⟩
    rw [hml] at he
    have hz : z.1 = e.1 := hf (he.symm.trans hlend)
    exact ⟨k, hs.1, hc.1.trans hz, hc.2⟩

section CoherentDomain

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
Geometric side reachability implies ambient present-edge reachability, retaining -/
theorem ancestor_side_reachable {a : ThinMapSide} {u v : ℕ}
    (h : Relation.ReflTransGen (sideDirectedStep w hfin hL htrans hR P a) u v) :
    Reachable (⟨u⟩ : PresentVertex w) ⟨v⟩ := by
  induction h with
  | refl => exact ⟨.nil⟩
  | @tail b c h hbc ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨e, _, hp, hw, he⟩ := hbc
    exact ⟨p.cons ⟨e, hp, hw, he⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric target is an earlier record vertex at every good cut, with the -/
theorem ancestor_target_record (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    ∃ u ≤ (selectedCutTime T (k + 1) q.1).toNat - 1,
      recordVertex w u =
        (⟨thinMapBoundaryVertex w hfin hL htrans hR a s⟩ : PresentVertex w) := by
  obtain ⟨hu, hv⟩ := selectedCut_boundary_target_record x T hT q a k s hk
  let u := match a with
    | .left => natSelect (fun m => ∀ j, m < j → L w m + 1 ≤ L w j) s
    | .right => natSelect (fun m => ∀ j, j < m → R w m < R w j) s
  refine ⟨u, ?_, ?_⟩
  · exact Nat.le_sub_one_of_lt hu
  · rw [ancestor_boundaryVertex_eq]
    exact hv

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every geometric ancestor edge is allocated and present in the actual past stage
of every good cut. The geometric carrier itself imposes no presence condition. -/
theorem ancestor_edge_in_goodCut_stage (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (e : ℕ) (he : e ∈ sourceAncestorEdges w hfin hL htrans hR P a s) :
    e < (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge ∧
      (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).present e = true := by
  obtain ⟨u, hu, hv⟩ := ancestor_target_record x T hT q a s k hk
  apply record_ancestor_geometric_edge_in_stage w hL hR u _ e hu
  rw [hv]
  exact ancestor_side_reachable x T hT q he.2.2.2

private theorem stage_reachable_start_bound (t : ℕ) {u v : StagePresentVertex w t}
    (h : Reachable u v) (hv : v.id < (kmswStage w t).nextVertex) :
    u.id < (kmswStage w t).nextVertex := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hv
  | @cons b c p e ih =>
    apply ih
    have hb := (kmswStage_endpoints_lt_nextVertex w t e.val e.property.1).1
    rwa [e.property.2.2.1] at hb

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every geometric ancestor vertex has an allocated vertex ID in the actual past -/
theorem ancestor_vertex_in_goodCut_stage (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (v : ℕ) (hv : v ∈ sourceAncestorVertices w hfin hL htrans hR P a s) :
    v < (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextVertex := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  obtain ⟨u, hu, htarget⟩ := ancestor_target_record x T hT q a s k hk
  have hr := ancestor_side_reachable x T hT q hv.2
  rw [← htarget] at hr
  obtain ⟨p⟩ := hr
  obtain ⟨p', _⟩ := ancestorPath_to_record_lifts_later hu p
  apply stage_reachable_start_bound x T hT q t ⟨p'⟩
  have he := act_lt_nextEdge w hu
  have hb := (kmswStage_endpoints_lt_nextVertex w t (act w u) he).1
  have heq : edgeWest w (act w u) = (recordVertex w u).id :=
    (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl u))).1.symm
  rwa [(edge_endpoints_eq w he).1, heq] at hb

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric ancestor vertex carrier is equivalent to its restriction inside
the actual past stage, via stageMapVertex. This does not identify the cut half. -/
@[expose] noncomputable def ancestorStageVertexEquiv (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    {v : MapVertex (kmswStageDirectedMap w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)) //
      (stageMapVertex w ((selectedCutTime T (k + 1) q.1).toNat - 1) v).id ∈
        sourceAncestorVertices w hfin hL htrans hR P a s} ≃
      sourceAncestorVertices w hfin hL htrans hR P a s := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  let f : {v : MapVertex (kmswStageDirectedMap w t) //
      (stageMapVertex w t v).id ∈ sourceAncestorVertices w hfin hL htrans hR P a s} →
      sourceAncestorVertices w hfin hL htrans hR P a s :=
    fun v => ⟨(stageMapVertex w t v.1).id, v.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro v z h
    apply Subtype.ext
    apply stageMapVertex_injective w t
    exact congrArg StagePresentVertex.mk (congrArg Subtype.val h)
  · intro v
    have hv := ancestor_vertex_in_goodCut_stage x T hT q a s k hk v.1 v.2
    let z := (stageVertexEquiv w t).symm ⟨v.1, hv⟩
    have hz : (stageMapVertex w t z).id = v.1 := by
      exact congrArg Fin.val ((stageVertexEquiv w t).apply_symm_apply ⟨v.1, hv⟩)
    exact ⟨⟨z, hz.symm ▸ v.2⟩, Subtype.ext hz⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The geometric ancestor dart carrier is equivalent to its actual past-stage
restriction by unchanged edge ID and endpoint side. No presence premise is added. -/
@[expose] noncomputable def ancestorStageDartEquiv (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s} ≃
      sourceAncestorDarts w hfin hL htrans hR P a s where
  toFun d := ⟨(d.1.1.val, d.1.2), d.2⟩
  invFun d := ⟨(⟨d.1.1,
    (ancestor_edge_in_goodCut_stage x T hT q a s k hk d.1.1 d.2).1⟩, d.1.2), d.2⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The stage vertex equivalence is the common permanent-ID embedding. -/
theorem ancestorStageVertexEquiv_apply (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (v : {v : MapVertex (kmswStageDirectedMap w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)) //
      (stageMapVertex w ((selectedCutTime T (k + 1) q.1).toNat - 1) v).id ∈
        sourceAncestorVertices w hfin hL htrans hR P a s}) :
    (ancestorStageVertexEquiv x T hT q a s k hk v).1 =
      (stageMapVertex w ((selectedCutTime T (k + 1) q.1).toNat - 1) v.1).id := rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Incidence agrees between the geometric restriction and its actual past-stage -/
theorem ancestor_stage_incidence_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (d : {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s})
    (v : {v : MapVertex (kmswStageDirectedMap w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)) //
      (stageMapVertex w ((selectedCutTime T (k + 1) q.1).toNat - 1) v).id ∈
        sourceAncestorVertices w hfin hL htrans hR P a s}) :
    dartTailVertex (kmswStageDirectedMap w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)) d.1 = v.1 ↔
      sourceAncestorRelation w hfin hL htrans hR P a s .incident
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d))
        (.inl (ancestorStageVertexEquiv x T hT q a s k hk v)) := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  have hd : (stageMapVertex w t
      (dartTailVertex (kmswStageDirectedMap w t) d.1)).id =
      if d.1.2 then edgeEast w d.1.1.val else edgeWest w d.1.1.val := by
    rw [stageMapVertex_tail]
    dsimp only [stageEndpoint]
    rw [(edge_endpoints_eq w d.1.1.isLt).1, (edge_endpoints_eq w d.1.1.isLt).2]
  change _ ↔ (if d.1.2 then edgeEast w d.1.1.val else edgeWest w d.1.1.val) =
    (stageMapVertex w t v.1).id
  constructor
  · intro h
    exact hd.symm.trans (congrArg (fun z => (stageMapVertex w t z).id) h)
  · intro h
    apply stageMapVertex_injective w t
    exact congrArg StagePresentVertex.mk (hd.trans h)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Orientation agrees between the geometric restriction and its past-stage dart -/
theorem ancestor_stage_orientation_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (d : {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s}) :
    (kmswStageDirectedMap w ((selectedCutTime T (k + 1) q.1).toNat - 1)).tail d.1 ↔
      sourceAncestorRelation w hfin hL htrans hR P a s .oriented
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d))
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d)) := by
  have hp := (ancestor_edge_in_goodCut_stage x T hT q a s k hk d.1.1.val d.2).2
  have hpres := EdgePresent.of_stage_present d.1.1.isLt hp
  change (_ = true ∧ d.1.2 = false) ↔ (EdgePresent w d.1.1.val ∧ d.1.2 = false)
  simp only [hp, hpres, true_and]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every surviving exterior boundary index is the same geometric dart in the actual -/
theorem ancestor_stage_boundary_index (a : ThinMapSide) (s k i : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) (hi : i < s) :
    ((match a with
      | .left => (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).UL
      | .right => (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).LR)[i]?).map
        (fun e => (e, false)) = some (thinMapBoundaryDart w hfin hL htrans hR a i) := by
  have hh := selectedCut_past_boundary_dart_record x T hT q a k s i hk hi
  have hm := congrArg (Option.map (fun e : ℕ => (e, false))) hh
  exact hm.trans (congrArg some
    (ancestor_boundaryDart_eq w hfin hL htrans hR a i).symm)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The permanent-ID stage embedding has exactly the geometric ancestor dart image. -/
theorem ancestor_stage_darts_image (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    stageLimitDart w ((selectedCutTime T (k + 1) q.1).toNat - 1) ''
      {d | (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s} =
        sourceAncestorDarts w hfin hL htrans hR P a s := by
  ext d
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro hd
    obtain ⟨e, he⟩ := (ancestorStageDartEquiv x T hT q a s k hk).surjective ⟨d, hd⟩
    exact ⟨e.1, e.2, congrArg Subtype.val he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Induced rotation on the geometric restriction is first return of the actual
past-stage rotation to its ancestor dart subset. Source: -/
theorem ancestor_stage_rotation_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (d e : {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s}) :
    (∃ m : ℕ, 0 < m ∧
      (stageRot w ((selectedCutTime T (k + 1) q.1).toNat - 1) : _ → _)^[m] d.1 = e.1 ∧
      ∀ j : ℕ, 0 < j → j < m →
        ((stageRot w ((selectedCutTime T (k + 1) q.1).toNat - 1) : _ → _)^[j] d.1).1.val
          ∉ sourceAncestorEdges w hfin hL htrans hR P a s) ↔
      sourceAncestorRelation w hfin hL htrans hR P a s .rotation
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d))
        (.inr (ancestorStageDartEquiv x T hT q a s k hk e)) := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  have hn (z : StageDart (kmswStage w t).nextEdge) :
      ∃ m : ℕ, 0 < m ∧
        (kmswInfRot w hfin : _ → _)^[m] (stageLimitDart w t z) =
          stageLimitDart w t (stageRot w t z) ∧
        ∀ j : ℕ, 0 < j → j < m →
          (kmswInfRot w hfin : _ → _)^[j] (stageLimitDart w t z) ∉
            Set.range (stageLimitDart w t) := by
    obtain ⟨m, hm, he, hg⟩ := kmswInfRot_firstReturn_stage w hfin t z
    refine ⟨m, hm, ?_, ?_⟩
    · simpa only [stageLimitDart, Function.Embedding.coeFn_mk, ← Equiv.Perm.coe_pow] using he
    · intro j hj hjm hmem
      obtain ⟨b, hb⟩ := hmem
      have hge : (kmswStage w t).nextEdge ≤
          ((kmswInfRot w hfin : _ → _)^[j] (stageLimitDart w t z)).1 := by
        simpa only [stageLimitDart, Function.Embedding.coeFn_mk,
          ← Equiv.Perm.coe_pow] using hg j hj hjm
      rw [← hb] at hge
      exact (Nat.not_le_of_lt b.1.isLt) hge
  have hh := ancestor_firstReturn_image_iff (stageRot w t) (kmswInfRot w hfin)
    (stageLimitDart w t) (stageLimitDart w t).injective hn
    {z | (z.1.val, z.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s} d e
  rw [ancestor_stage_darts_image x T hT q a s k hk] at hh
  exact hh

private theorem ancestor_triangle_fresh_mem (j : TriangleCreationTime w) :
    ((kmswStage w j.val).nextEdge, true) ∈ stageTriangleDartList w j := by
  dsimp only [stageTriangleDartList, stageTriangleDartTriple]
  split_ifs
  · cases (kmswStage w j.val).UL.dropLast.reverse <;> simp only [List.mem_cons,
      or_true, true_or]
  · simp only [List.mem_cons, or_true, true_or]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every retained geometric triangle is already a created triangle of the actual -/
theorem ancestor_retainedFace_stage_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) (d : ℕ × Bool) :
    sourceAncestorRetainedFace w hfin hL htrans hR P a s d ↔
      ∃ j ∈ stageTriangleTimes w ((selectedCutTime T (k + 1) q.1).toNat - 1),
        d ∈ stageTriangleDartList w j ∧
          ∀ z ∈ stageTriangleDartList w j,
            z ∈ sourceAncestorDarts w hfin hL htrans hR P a s := by
  constructor
  · rintro ⟨j, hd, hall⟩
    refine ⟨j, (mem_stageTriangleTimes w _ j).mpr ?_, hd, hall⟩
    have he := (ancestor_edge_in_goodCut_stage x T hT q a s k hk
      (kmswStage w j.val).nextEdge (hall _ (ancestor_triangle_fresh_mem x T hT q j))).1
    by_contra hn
    have hm := kmswStage_nextEdge_mono w (Nat.le_of_not_gt hn)
    omega
  · rintro ⟨j, _, hd, hall⟩
    exact ⟨j, hd, hall⟩

private theorem ancestor_triangle_faceSucc (n : ℕ) (j : TriangleCreationTime w)
    (hj : j.val < n) (d : StageDart (kmswStage w n).nextEdge)
    (hd : stageLimitDart w n d ∈ stageTriangleDartList w j) :
    kmswInfFaceSucc w hfin (stageLimitDart w n d) =
      stageLimitDart w n ((kmswMap w n).faceSucc d) := by
  let a := stageTriangleDart₁ w n j hj
  let b := stageTriangleDart₂ w n j hj
  let c := stageTriangleDart₃ w n j hj
  have ha : stageLimitDart w n a = (stageTriangleDartTriple w j).1 := rfl
  have hb : stageLimitDart w n b = (stageTriangleDartTriple w j).2.1 := rfl
  have hc : stageLimitDart w n c = (stageTriangleDartTriple w j).2.2 := rfl
  have hi := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  have hs := stageTriangle_isFace w j n hj
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with hd | hd | hd
  · have hda : d = a := (stageLimitDart w n).injective (hd.trans ha.symm)
    subst d
    exact (congrArg (kmswInfFaceSucc w hfin) ha).trans
      (hi.1.trans (hb.symm.trans (congrArg (stageLimitDart w n) hs.1.symm)))
  · have hdb : d = b := (stageLimitDart w n).injective (hd.trans hb.symm)
    subst d
    exact (congrArg (kmswInfFaceSucc w hfin) hb).trans
      (hi.2.1.trans (hc.symm.trans (congrArg (stageLimitDart w n) hs.2.1.symm)))
  · have hdc : d = c := (stageLimitDart w n).injective (hd.trans hc.symm)
    subst d
    exact (congrArg (kmswInfFaceSucc w hfin) hc).trans
      (hi.2.2.1.trans (ha.symm.trans (congrArg (stageLimitDart w n) hs.2.2.1.symm)))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Retained-face succession agrees with the actual past-stage face permutation,
using the created triangle lists and all geometric ancestor darts. -/
theorem ancestor_stage_faceNext_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (d e : {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s}) :
    sourceAncestorRelation w hfin hL htrans hR P a s .faceNext
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d))
        (.inr (ancestorStageDartEquiv x T hT q a s k hk e)) ↔
      (∃ j ∈ stageTriangleTimes w ((selectedCutTime T (k + 1) q.1).toNat - 1),
        (d.1.1.val, d.1.2) ∈ stageTriangleDartList w j ∧
          ∀ z ∈ stageTriangleDartList w j,
            z ∈ sourceAncestorDarts w hfin hL htrans hR P a s) ∧
      (kmswMap w ((selectedCutTime T (k + 1) q.1).toNat - 1)).faceSucc d.1 = e.1 := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  have hret := ancestor_retainedFace_stage_iff x T hT q a s k hk
    (stageLimitDart w t d.1)
  change (sourceAncestorRetainedFace w hfin hL htrans hR P a s
      (stageLimitDart w t d.1) ∧
      kmswInfFaceSucc w hfin (stageLimitDart w t d.1) = stageLimitDart w t e.1) ↔ _
  constructor
  · rintro ⟨hr, hn⟩
    obtain ⟨j, hj, hd, hall⟩ := hret.mp hr
    refine ⟨⟨j, hj, hd, hall⟩, (stageLimitDart w t).injective ?_⟩
    exact (ancestor_triangle_faceSucc x T hT q t j
      ((mem_stageTriangleTimes w t j).mp hj) d.1 hd).symm.trans hn
  · rintro ⟨⟨j, hj, hd, hall⟩, hn⟩
    refine ⟨hret.mpr ⟨j, hj, hd, hall⟩, ?_⟩
    exact (ancestor_triangle_faceSucc x T hT q t j
      ((mem_stageTriangleTimes w t j).mp hj) d.1 hd).trans
        (congrArg (stageLimitDart w t) hn)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Geometric side ancestry is exactly side-confined ancestry inside the actual past
stage of every good cut. Every lifted step retains its edge ID and direction. -/
theorem ancestor_side_reachable_stage_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) (v : ℕ) :
    v ∈ sourceAncestorVertices w hfin hL htrans hR P a s ↔
      v ∈ sideVertices w hfin hL htrans hR P a ∧
      Relation.ReflTransGen
        (fun u z => ∃ e : ℕ,
          e < (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge ∧
          e ∈ sideEdges w hfin hL htrans hR P a ∧
          (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).present e = true ∧
          (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).west e = u ∧
          (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).east e = z)
        v (thinMapBoundaryVertex w hfin hL htrans hR a s) := by
  constructor
  · rintro ⟨hvside, hpath⟩
    refine ⟨hvside, ?_⟩
    clear hvside
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head u z hstep hpath ih =>
      obtain ⟨e, hes, hp, hw, he⟩ := hstep
      have huanc : edgeWest w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s :=
        ⟨(sideEdges_endpoints w hfin hL htrans hR P a hes).1,
          hw.symm ▸ hpath.head ⟨e, hes, hp, hw, he⟩⟩
      have hzanc : edgeEast w e ∈ sourceAncestorVertices w hfin hL htrans hR P a s :=
        ⟨(sideEdges_endpoints w hfin hL htrans hR P a hes).2, he.symm ▸ hpath⟩
      obtain ⟨ha, hpres⟩ := ancestor_edge_in_goodCut_stage x T hT q a s k hk e
        ⟨hes, huanc, hzanc⟩
      exact ih.head ⟨e, ha, hes, hpres,
        (edge_endpoints_eq w ha).1.trans hw, (edge_endpoints_eq w ha).2.trans he⟩
  · rintro ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    clear hv
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | @head b c hbc h ih =>
      obtain ⟨e, ha, hes, hp, hw, he⟩ := hbc
      exact ih.head ⟨e, hes, EdgePresent.of_stage_present ha hp,
        (edge_endpoints_eq w ha).1.symm.trans hw,
        (edge_endpoints_eq w ha).2.symm.trans he⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common past-stage vertex and dart embeddings give one equivalence of the
entire geometric ancestor cell carrier. This does not identify a selected half. -/
@[expose] noncomputable def ancestorStageCellEquiv (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    Sum
      {v : MapVertex (kmswStageDirectedMap w
          ((selectedCutTime T (k + 1) q.1).toNat - 1)) //
        (stageMapVertex w ((selectedCutTime T (k + 1) q.1).toNat - 1) v).id ∈
          sourceAncestorVertices w hfin hL htrans hR P a s}
      {d : StageDart (kmswStage w
          ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
        (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s} ≃
      SourceAncestorCell w hfin hL htrans hR P a s :=
  Equiv.sumCongr (ancestorStageVertexEquiv x T hT q a s k hk)
    (ancestorStageDartEquiv x T hT q a s k hk)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The past-stage dart embedding preserves and reflects geometric edge pairing, -/
theorem ancestor_stage_opposite_iff (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    (d e : {d : StageDart (kmswStage w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).nextEdge //
      (d.1.val, d.2) ∈ sourceAncestorDarts w hfin hL htrans hR P a s}) :
    (kmswStageDirectedMap w
        ((selectedCutTime T (k + 1) q.1).toNat - 1)).edgeInv d.1 = e.1 ↔
      sourceAncestorRelation w hfin hL htrans hR P a s .opposite
        (.inr (ancestorStageDartEquiv x T hT q a s k hk d))
        (.inr (ancestorStageDartEquiv x T hT q a s k hk e)) := by
  let t := (selectedCutTime T (k + 1) q.1).toNat - 1
  rcases d with ⟨⟨i, b⟩, hd⟩
  rcases e with ⟨⟨j, c⟩, he⟩
  change (i, !b) = (j, c) ↔ (i.val, !b) = (j.val, c)
  constructor
  · intro h
    exact congrArg (fun z : StageDart (kmswStage w t).nextEdge => (z.1.val, z.2)) h
  · intro h
    have hij : i.val = j.val := congrArg (fun z : ℕ × Bool => z.1) h
    have hbc : (!b) = c := congrArg (fun z : ℕ × Bool => z.2) h
    exact Prod.ext (Fin.ext hij) hbc

end CoherentDomain
end DirectedDistances.PaperProofs.Section4
