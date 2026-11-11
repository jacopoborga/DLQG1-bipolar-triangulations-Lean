module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.BusemannUIQBOT
import DirectedDistances.KMSW.OutgoingInterval
import DirectedDistances.KMSW.LocalFinitenessIID
import DirectedDistances.KMSW.LocalFinitenessUpperChain

/-! # Activation order of present edges

and the edge containment in `lem-directed-contain`, -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory DirectedDistances.RandomWalk

/-- Every present edge has exactly one activation time (`def-kmsw`, -/
theorem existsUnique_actTime (w : ℕ → Fin 3) (e : ℕ) (he : EdgePresent w e) :
    ∃! n : ℕ, e = act w n := by
  obtain ⟨j, hj, hp⟩ := he
  obtain ⟨n, _, hn⟩ := stagePresent_exists_active w j e hj hp
  exact ⟨n, hn, fun m hm => CutConverse.act_injective w (hm.symm.trans hn)⟩

/-- The unique activation time of a present edge (`def-kmsw`, -/
@[expose] noncomputable def actTime (w : ℕ → Fin 3) (e : ℕ)
    (he : EdgePresent w e) : ℕ :=
  Classical.choose (existsUnique_actTime w e he).exists

/-- Characterization of the choice in `actTime` (`def-kmsw`, -/
theorem actTime_spec (w : ℕ → Fin 3) (e : ℕ) (he : EdgePresent w e) :
    e = act w (actTime w e he) :=
  Classical.choose_spec (existsUnique_actTime w e he).exists

/-- A prescribed activation time is the chosen one (`def-kmsw`, -/
theorem actTime_eq_iff (w : ℕ → Fin 3) (e : ℕ) (he : EdgePresent w e) (n : ℕ) :
    actTime w e he = n ↔ e = act w n := by
  constructor
  · intro h; rw [← h]; exact actTime_spec w e he
  · intro h; exact CutConverse.act_injective w ((actTime_spec w e he).symm.trans h)

private theorem active_present_at (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n) :
    (kmswStage w n).present (act w m) = true := by
  induction n, hmn using Nat.le_induction with
  | base =>
    obtain ⟨es, hes⟩ := kmswStage_UL_last w m
    apply (kmswStage_status w m).2.1
    rw [hes]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | succ n hmn ih =>
    change (kmswStep (kmswStage w n) (w n)).present (act w m) = true
    rw [kmswStep_present_existing _ _ (act_lt_nextEdge w hmn)]
    split
    · rfl
    · exact ih

/-- Consecutive present edges have strictly increasing activation times -/
theorem actTime_lt_of_consecutive (w : ℕ → Fin 3) {e f : ℕ}
    (he : EdgePresent w e) (hf : EdgePresent w f)
    (hef : edgeEast w e = edgeWest w f) : actTime w e he < actTime w f hf := by
  by_contra h
  have hle : actTime w f hf ≤ actTime w e he := Nat.le_of_not_gt h
  have halloc := act_lt_nextEdge w hle
  have hp := active_present_at w hle
  rw [← actTime_spec w f hf] at halloc hp
  apply stageOutgoing_frontier_empty w (actTime w e he) f halloc hp
  have hw := (edge_endpoints_eq w halloc).1
  rw [hw, ← hef]
  have hend := (edge_endpoints_eq w (act_lt_nextEdge w
    (Nat.le_refl (actTime w e he)))).2
  have heast : edgeEast w e =
      (kmswStage w (actTime w e he)).east (act w (actTime w e he)) := by
    exact (congrArg (edgeEast w) (actTime_spec w e he)).trans hend.symm
  rw [heast]
  exact List.mem_cons_self

private theorem path_before_arrow {w : ℕ → Fin 3} {u v z : PresentVertex w}
    (p : Path u v) (e : v ⟶ z) :
    p.length ≤ actTime w e.val e.property.1 ∧
    ∀ f ∈ pathEdgeList p, ∃ hf : EdgePresent w f,
      actTime w f hf < actTime w e.val e.property.1 := by
  induction p generalizing z with
  | nil => exact ⟨Nat.zero_le _, by simp [pathEdgeList]⟩
  | @cons a b p f ih =>
    have hlt := actTime_lt_of_consecutive w f.property.1 e.property.1
      (f.property.2.2.trans e.property.2.1.symm)
    obtain ⟨hlen, hmem⟩ := ih f
    refine ⟨by simp only [Path.length_cons]; omega, ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hg, hgt⟩ := hmem g hg
      exact ⟨hg, hgt.trans hlt⟩
    · have hgf := List.mem_singleton.mp hg
      subst g
      exact ⟨f.property.1, hlt⟩

/-- Activation times increase strictly along the actual edge list of any path -/
theorem pathEdgeList_actTime_pairwise {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) :
    (pathEdgeList p).Pairwise (fun e f => ∀ he : EdgePresent w e,
      ∀ hf : EdgePresent w f, actTime w e he < actTime w f hf) := by
  induction p with
  | nil => exact List.Pairwise.nil
  | cons p e ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro f hf g hg hfp hgp
    have hge := List.mem_singleton.mp hg
    subst g
    obtain ⟨_, hlt⟩ := (path_before_arrow p e).2 f hf
    exact hlt

private def reverseEdges {w : ℕ → Fin 3} {u : PresentVertex w} :
    {v : PresentVertex w} → Path u v → List ℕ
  | _, .nil => []
  | _, .cons p e => e.val :: reverseEdges p

private theorem reverseEdges_eq {w : ℕ → Fin 3} {u v : PresentVertex w}
    (p : Path u v) : reverseEdges p = (pathEdgeList p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [reverseEdges, pathEdgeList, List.reverse_append,
      List.reverse_singleton, List.singleton_append, ih]

private theorem reverseEdges_injective {w : ℕ → Fin 3} {u v : PresentVertex w} :
    Function.Injective (reverseEdges (u := u) (v := v)) := by
  intro p
  induction p with
  | nil =>
    intro q hq
    cases q with
    | nil => rfl
    | cons q f => cases hq
  | @cons a b p e ih =>
    intro q hq
    cases q with
    | nil => cases hq
    | @cons c d q f =>
      have he : e.val = f.val := (List.cons.inj hq).1
      have hac : a = c := by
        have hid := e.property.2.1.symm.trans
          ((congrArg (edgeWest w) he).trans f.property.2.1)
        cases a
        cases c
        cases hid
        rfl
      subst c
      have hef : e = f := Subtype.ext he
      subst f
      exact congrArg (fun r => r.cons e) (ih (List.cons.inj hq).2)

private theorem bounded_edge_lists_finite (E N : ℕ) :
    {l : List (Fin E) | l.length ≤ N}.Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun a : (k : Fin (N + 1)) × List.Vector (Fin E) k.val => a.2.val))
  intro l hl
  exact ⟨⟨⟨l.length, by change l.length ≤ N at hl; omega⟩, ⟨l, rfl⟩⟩, rfl⟩

section FiniteIncidence

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

include hfin

/-- Incoming activation times form a finite set under geometric local finiteness -/
theorem incomingActTimes_finite (b : ℕ) :
    {n : ℕ | edgeEast w (act w n) = b}.Finite := by
  have hp := Set.Finite.preimage
    (fun _ _ _ _ he => CutConverse.act_injective w he) (hfin b)
  apply hp.subset
  intro n hn
  refine ⟨n, act_lt_nextEdge w le_rfl, Or.inr ?_⟩
  exact ((edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl n))).2).trans hn

/-- Maximum incoming activation time, with value zero for no incoming edges -/
@[expose] noncomputable def incomingActTimeMax (b : ℕ) : ℕ :=
  (incomingActTimes_finite w hfin b).toFinset.sup id

/-- Every incoming present edge is bounded by the incoming maximum -/
theorem actTime_le_incomingActTimeMax {e b : ℕ} (he : EdgePresent w e)
    (hb : edgeEast w e = b) : actTime w e he ≤ incomingActTimeMax w hfin b := by
  apply Finset.le_sup (f := id)
  apply (incomingActTimes_finite w hfin b).mem_toFinset.mpr
  change edgeEast w (act w (actTime w e he)) = b
  exact (congrArg (edgeEast w) (actTime_spec w e he)).symm.trans hb

/-- Every edge on a path ending at `b` has activation time at most the maximum -/
theorem path_actTime_le_incomingMax {a b : PresentVertex w} (p : Path a b) :
    ∀ e ∈ pathEdgeList p, ∃ he : EdgePresent w e,
      actTime w e he ≤ incomingActTimeMax w hfin b.id := by
  cases p with
  | nil => simp [pathEdgeList]
  | cons p f =>
    intro e he
    have hf := actTime_le_incomingActTimeMax w hfin f.property.1 f.property.2.2
    rcases List.mem_append.mp he with he | he
    · obtain ⟨he, hlt⟩ := (path_before_arrow p f).2 e he
      exact ⟨he, hlt.le.trans hf⟩
    · have hef := List.mem_singleton.mp he
      subst e
      exact ⟨f.property.1, hf⟩

/-- Activation order bounds the length of every present path ending at `b` -/
theorem path_length_le_incomingMax {a b : PresentVertex w} (p : Path a b) :
    p.length ≤ incomingActTimeMax w hfin b.id + 1 := by
  cases p with
  | nil => exact Nat.zero_le _
  | cons p e =>
    have hlen := (path_before_arrow p e).1
    have he := actTime_le_incomingActTimeMax w hfin e.property.1 e.property.2.2
    simp only [Path.length_cons]
    omega

/-- There are finitely many actual arrow-valued paths between any pair under -/
theorem present_paths_finite (a b : PresentVertex w) : Finite (Path a b) := by
  classical
  let N := incomingActTimeMax w hfin b.id
  let E := (kmswStage w N).nextEdge
  have he (p : Path a b) : ∀ e ∈ reverseEdges p, e < E := by
    intro e he
    rw [reverseEdges_eq, List.mem_reverse] at he
    obtain ⟨hp, ht⟩ := path_actTime_le_incomingMax w hfin p e he
    have halloc := act_lt_nextEdge w ht
    rwa [← actTime_spec w e hp] at halloc
  let enc (p : Path a b) : List (Fin E) :=
    (reverseEdges p).pmap (fun e h => ⟨e, h⟩) (he p)
  have henc (p : Path a b) : (enc p).map Fin.val = reverseEdges p := by
    simp only [enc, List.map_pmap, List.pmap_eq_map]
    exact List.map_id _
  have hlen (p : Path a b) : (enc p).length ≤ N + 1 := by
    simpa only [enc, List.length_pmap, reverseEdges_eq, List.length_reverse,
      pathEdgeList_length] using path_length_le_incomingMax w hfin p
  let f (p : Path a b) : {l : List (Fin E) | l.length ≤ N + 1} := ⟨enc p, hlen p⟩
  have : Finite {l : List (Fin E) | l.length ≤ N + 1} := bounded_edge_lists_finite E (N + 1)
  apply Finite.of_injective f
  intro p q hpq
  apply reverseEdges_injective
  rw [← henc p, ← henc q]
  exact congrArg (List.map Fin.val) (congrArg Subtype.val hpq)

/-- All present directed path lengths between any two vertices are bounded -/
theorem present_pathLengths_bddAbove (a b : PresentVertex w) :
    BddAbove (pathLengths a b) := by
  refine ⟨incomingActTimeMax w hfin b.id + 1, ?_⟩
  rintro n ⟨p, rfl⟩
  exact path_length_le_incomingMax w hfin p

/-- A reachable pair admits an actual longest path under geometric local -/
theorem present_exists_isLongest {a b : PresentVertex w} (hr : Reachable a b) :
    ∃ p : Path a b, IsLongest p :=
  exists_isLongest_of_bddAbove (present_pathLengths_bddAbove w hfin a b) hr

/-- The extended LDP is attained at a finite path length whenever reachable -/
theorem presentLdp_attained {a b : PresentVertex w} (hr : Reachable a b) :
    ∃ p : Path a b, IsLongest p ∧
      presentLdp a b = ((p.length : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := present_exists_isLongest w hfin hr
  exact ⟨p, hp, presentLdp_eq_length hp⟩

end FiniteIncidence

private theorem boundary_outgoing_actTime_ge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) {e : ℕ} (he : EdgePresent w e)
    (hw : edgeWest w e = boundaryVertex w h k) :
    boundaryHitTime w h k ≤ actTime w e he := by
  by_cases hk : k = 0
  · subst k
    rw [boundaryHitTime_zero]
    exact Nat.zero_le _
  · by_contra hlt
    have hlt : actTime w e he < boundaryHitTime w h k := by omega
    have hv : boundaryVertex w h k = activeInitial w (actTime w e he) := by
      exact hw.symm.trans (congrArg (edgeWest w) (actTime_spec w e he))
    by_cases hpos : 1 ≤ k
    · exact boundaryVertex_first_visit_right w h hpos _ hlt hv
    · exact boundaryVertex_first_visit_left w h (by omega) _ hlt hv

/-- Every edge of a path starting at a hit-indexed boundary vertex activates
at or after its hit time (`lem-directed-contain`, -/
theorem boundary_path_actTime_ge (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℤ) {b : PresentVertex w} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b) :
    ∀ e ∈ pathEdgeList p, ∃ he : EdgePresent w e,
      boundaryHitTime w h k ≤ actTime w e he := by
  induction p with
  | nil => simp [pathEdgeList]
  | @cons a b p e ih =>
    have ht : boundaryHitTime w h k ≤ actTime w e.val e.property.1 := by
      cases p with
      | nil => exact boundary_outgoing_actTime_ge w h k e.property.1 e.property.2.1
      | cons q f =>
        obtain ⟨hf, hft⟩ := ih f.val (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hlt := actTime_lt_of_consecutive w hf e.property.1
          (f.property.2.2.trans e.property.2.1.symm)
        exact hft.trans hlt.le
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih f hf
    · have hfe := List.mem_singleton.mp hf
      subst f
      exact ⟨e.property.1, ht⟩

/-- Edge containment in the active-edge future, for every integer boundary -/
theorem boundary_path_future_edges (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (k : ℤ) {b : PresentVertex w} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) b) :
    ∀ e ∈ pathEdgeList p, ∃ n, boundaryHitTime w h k ≤ n ∧ e = act w n := by
  intro e he
  obtain ⟨he, ht⟩ := boundary_path_actTime_ge w h k p e he
  exact ⟨actTime w e he, ht, actTime_spec w e he⟩

/-- The `k = 0` containment specialization (`lem-directed-contain`, -/
theorem zero_path_future_edges (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {b : PresentVertex w} (p : Path (⟨0⟩ : PresentVertex w) b) :
    ∀ e ∈ pathEdgeList p, ∃ n, boundaryHitTime w h 0 ≤ n ∧ e = act w n := by
  have hp := boundary_path_future_edges w h 0 (b := b)
  rw [boundaryVertex_zero] at hp
  exact hp p

/-- The `k = 1` containment specialization at the initial root terminal vertex -/
theorem one_path_future_edges (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {b : PresentVertex w} (p : Path (⟨1⟩ : PresentVertex w) b) :
    ∀ e ∈ pathEdgeList p, ∃ n, boundaryHitTime w h 1 ≤ n ∧ e = act w n := by
  have hp := boundary_path_future_edges w h 1 (b := b)
  rw [boundaryVertex_one] at hp
  exact hp p

/-- Simultaneously all endpoint pairs have finitely many paths, bounded lengths,
and attained reachable LDP in the iid future map (`def-ldp`, -/
theorem iidCodes_ae_paths_finite_bounded_attained :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ a b : PresentVertex w, Finite (Path a b) ∧ BddAbove (pathLengths a b) ∧
        (Reachable a b → ∃ p : Path a b, IsLongest p ∧
          presentLdp a b = ((p.length : ℕ∞) : WithBot ℕ∞)) := by
  filter_upwards [iidCodes_ae_finite_incident_edges] with ω hfin w a b
  exact ⟨present_paths_finite _ hfin a b, present_pathLengths_bddAbove _ hfin a b,
    fun hr => presentLdp_attained _ hfin hr⟩

/-- Simultaneously all endpoint pairs have finitely many paths, bounded lengths,
and attained reachable LDP in the UIQBOT code realization (`def-uiqbot`, -/
theorem pitmanCodes_ae_paths_finite_bounded_attained :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∀ a b : PresentVertex w, Finite (Path a b) ∧ BddAbove (pathLengths a b) ∧
        (Reachable a b → ∃ p : Path a b, IsLongest p ∧
          presentLdp a b = ((p.length : ℕ∞) : WithBot ℕ∞)) := by
  filter_upwards [pitmanCodes_ae_finite_incident_edges] with ω hfin w a b
  exact ⟨present_paths_finite _ hfin a b, present_pathLengths_bddAbove _ hfin a b,
    fun hr => presentLdp_attained _ hfin hr⟩

end DirectedDistances.KMSW
