module

public import DirectedDistances.KMSW.BoundaryEnumeration
public import DirectedDistances.KMSW.UIQBOTOrientation
import DirectedDistances.KMSW.WalkRecordCounts
public import DirectedDistances.KMSW.StageSubgraph

/-! # Present-edge boundary properties of the one-sided iid KMSW map

Deterministic helpers for `lem-uibot-bdy`,
IDs; missing geometric edges are never treated as arrows. -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory

/-- The right hit witnesses imply the unboundedness needed for the no-sink -/
theorem BoundaryHitWitnesses.R_unbounded_below {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ n, R w n ≤ a := by
  intro a
  obtain ⟨n, hn⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
  exact ⟨n, by have := le_max_right (1 : ℤ) (-a); omega⟩

/-- Every allocated vertex has an outgoing present edge as soon as the right
coordinate is unbounded below. This is the deterministic no-sink assertion of -/
theorem uibot_allocated_vertex_outgoing (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    ∃ e, EdgePresent w e ∧ edgeWest w e = v :=
  allocated_vertex_outgoing_present_edge w hR v hv

/-- Almost surely the iid one-sided map has no allocated sink, simultaneously -/
theorem iidCodes_ae_no_sink :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure, ∀ v : ℕ,
      (∃ n, v < (kmswStage (fun i => ω (i + 1)) n).nextVertex) →
        ∃ e, EdgePresent (fun i => ω (i + 1)) e ∧
          edgeWest (fun i => ω (i + 1)) e = v := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h v hv
  exact uibot_allocated_vertex_outgoing _ h.R_unbounded_below v hv

/-- Consecutive nonnegative boundary indices are joined by a present arrow,
including the root edge at index zero (`lem-uibot-bdy`, -/
theorem boundaryVertex_nonneg_successor_edge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 0 ≤ k) :
    ∃ e, EdgePresent w e ∧ edgeWest w e = boundaryVertex w h k ∧
      edgeEast w e = boundaryVertex w h (k + 1) := by
  by_cases hk0 : k = 0
  · subst k
    have hr := boundaryVertex_root_edge w h
    have he := edge_endpoints_eq w (j := 0) (e := 0) (by change 0 < 1; omega)
    exact ⟨0, ⟨0, by change 0 < 1; omega, hr.2.2.2⟩,
      he.1.symm.trans hr.2.1, he.2.symm.trans hr.2.2.1⟩
  · obtain ⟨N, hN, hs⟩ := boundaryVertex_right_edge w h (by omega : 1 ≤ k)
    obtain ⟨_, hp, hw, he⟩ := hs N le_rfl
    have hb := act_lt_nextEdge w hN
    have hend := edge_endpoints_eq w hb
    exact ⟨_, ⟨N, hb, hp⟩, hend.1.symm.trans hw, hend.2.symm.trans he⟩

/-- The present LR chain gives reachability in increasing nonnegative index -/
theorem boundaryVertex_nonneg_reachable (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k l : ℤ} (hk : 0 ≤ k) (hkl : k ≤ l) :
    Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
      ⟨boundaryVertex w h l⟩ := by
  have hchain : ∀ n : ℕ,
      Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
        ⟨boundaryVertex w h (k + n)⟩ := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.cast_zero, add_zero] using
        (Reachable.refl (⟨boundaryVertex w h k⟩ : PresentVertex w))
    | succ n ih =>
      obtain ⟨e, hp, hw, he⟩ := boundaryVertex_nonneg_successor_edge w h
        (k := k + n) (by omega)
      obtain ⟨p⟩ := ih
      have hr : Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w)
          ⟨boundaryVertex w h (k + n + 1)⟩ := ⟨p.cons ⟨e, hp, hw, he⟩⟩
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hr
  have hl : l = k + ((l - k).toNat : ℤ) := by omega
  rw [hl]
  exact hchain _

/-- The restriction of `BusemannCommonSequenceHypothesis` to nonnegative
indices: an injective tail of the present LR chain is reachable from both
not assert the hypothesis for negative indices. -/
theorem boundaryVertex_commonSequence_nonneg (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k k' : ℤ) (hk : 0 ≤ k) (hk' : 0 ≤ k') :
    ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (⟨boundaryVertex w h k⟩ : PresentVertex w) (y j) ∧
        Reachable (⟨boundaryVertex w h k'⟩ : PresentVertex w) (y j) := by
  let y : ℕ → PresentVertex w := fun j => ⟨boundaryVertex w h (max k k' + j)⟩
  refine ⟨y, ?_, fun j => ⟨?_, ?_⟩⟩
  · intro i j hij
    have heq := boundaryVertex_injective w h (congrArg PresentVertex.id hij)
    omega
  · exact boundaryVertex_nonneg_reachable w h hk (by have := le_max_left k k'; omega)
  · exact boundaryVertex_nonneg_reachable w h hk' (by have := le_max_right k k'; omega)

/-- Almost surely the common-sequence input holds simultaneously for every
pair of nonnegative indices (`lem-uibot-bdy`, -/
theorem iidCodes_ae_commonSequence_nonneg :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ k k' : ℤ, 0 ≤ k → 0 ≤ k' →
          ∃ y : ℕ → PresentVertex (fun i => ω (i + 1)), Function.Injective y ∧
            ∀ j, Reachable (⟨boundaryVertex _ h k⟩ : PresentVertex _) (y j) ∧
              Reachable (⟨boundaryVertex _ h k'⟩ : PresentVertex _) (y j) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, boundaryVertex_commonSequence_nonneg _ h⟩

/-- Every strictly positive boundary index has an incoming present edge,
including `x₁` via the root (`lem-uibot-bdy`, -/
theorem boundaryVertex_pos_incoming (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : 1 ≤ k) :
    ∃ e, EdgePresent w e ∧ edgeEast w e = boundaryVertex w h k := by
  obtain ⟨e, hp, _, he⟩ := boundaryVertex_nonneg_successor_edge w h
    (k := k - 1) (by omega)
  exact ⟨e, hp, by simpa only [sub_add_cancel] using he⟩

/-- Every allocated vertex either has an incoming present edge or is a
nonpositive-index boundary vertex. Fresh down/up vertices receive incoming
edges at birth; fresh left vertices lie on LL (`lem-uibot-bdy`, -/
theorem allocated_stage_incoming_or_left_boundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (n v : ℕ)
    (hv : v < (kmswStage w n).nextVertex) :
    (∃ e, EdgePresent w e ∧ edgeEast w e = v) ∨
      ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k := by
  induction n generalizing v with
  | zero =>
    have hv' : v < 2 := hv
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact Or.inr ⟨0, le_rfl, (boundaryVertex_zero w h).symm⟩
    · left
      simpa only [boundaryVertex_one] using boundaryVertex_pos_incoming w h (k := 1) le_rfl
  | succ n ih =>
    by_cases hold : v < (kmswStage w n).nextVertex
    · exact ih v hold
    · by_cases h0 : w n = 0
      · cases hs : (kmswStage w n).UL.dropLast.reverse with
        | cons e es =>
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge] at hv
          exact (hold hv).elim
        | nil =>
          have hvnew : v = (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
              hs, State.addEdge] at hv
            omega
          have hmem : (kmswStage w n).nextEdge + 1 ∈ (kmswStage w (n + 1)).LL := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep, hs]
          have hw : (kmswStage w (n + 1)).west ((kmswStage w n).nextEdge + 1) = v := by
            simp [kmswStage, kmswStep, kmswCodeStep, h0, kmswStepOfStep,
              hs, State.addEdge, hvnew]
          obtain ⟨k, hk⟩ := boundaryVertex_covers_lowerBoundary w h v
            ⟨n + 1, _, Or.inl hmem, Or.inl hw⟩
          by_cases hkpos : 1 ≤ k
          · exact Or.inl (by rw [← hk]; exact boundaryVertex_pos_incoming w h hkpos)
          · exact Or.inr ⟨k, by omega, hk.symm⟩
      · by_cases h1 : w n = 1
        · have hvnew : v = (kmswStage w n).nextVertex := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep,
              State.addEdge] at hv
            omega
          have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
          have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge]
          have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge = v := by
            simp [kmswStage, kmswStep, kmswCodeStep, h1, kmswStepOfStep, State.addEdge, hvnew]
          exact Or.inl ⟨_, ⟨n + 1, he, hp⟩, (edge_endpoints_eq w he).2.symm.trans ht⟩
        · cases hs : (kmswStage w n).UR with
          | cons e es =>
            simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
              kmswStepOfStep, hs] at hv
            exact (hold hv).elim
          | nil =>
            have hvnew : v = (kmswStage w n).nextVertex := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep,
                hs, State.addEdge] at hv
              omega
            have he : (kmswStage w n).nextEdge < (kmswStage w (n + 1)).nextEdge := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs, State.addEdge]
            have hp : (kmswStage w (n + 1)).present (kmswStage w n).nextEdge = true := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs, State.addEdge]
            have ht : (kmswStage w (n + 1)).east (kmswStage w n).nextEdge = v := by
              simp [kmswStage, kmswStep, kmswCodeStep, h0, h1, kmswStepOfStep, hs,
                State.addEdge, hvnew]
            exact Or.inl ⟨_, ⟨n + 1, he, hp⟩, (edge_endpoints_eq w he).2.symm.trans ht⟩

/-- A source among allocated vertices must have a nonpositive boundary index -/
theorem allocated_source_is_left_boundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex)
    (hin : ¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) :
    ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k := by
  obtain ⟨n, hn⟩ := hv
  rcases allocated_stage_incoming_or_left_boundary w h n v hn with he | hb
  · exact (hin he).elim
  · exact hb

private def lowerSourceVertices (s : State) : List ℕ :=
  0 :: s.LL.map s.west

private theorem lowerSourceVertices_addEdge (s : State) (a b : ℕ) (p : Bool)
    (hids : ∀ f ∈ s.LL, f < s.nextEdge) :
    lowerSourceVertices (s.addEdge a b p) = lowerSourceVertices s := by
  unfold lowerSourceVertices
  congr 1
  apply List.map_congr_left
  intro f hf
  simp only [State.addEdge, ite_eq_right (Nat.ne_of_lt (hids f hf))]

private theorem addEdge_east_avoids_lowerSources (s : State) (a b : ℕ) (p : Bool)
    (hids : ∀ f ∈ s.LL, f < s.nextEdge)
    (hi : ∀ e < s.nextEdge, e ∉ s.LL → s.east e ∉ lowerSourceVertices s)
    (hb : b ∉ lowerSourceVertices s) :
    ∀ e < (s.addEdge a b p).nextEdge,
      e ∉ (s.addEdge a b p).LL →
        (s.addEdge a b p).east e ∉ lowerSourceVertices (s.addEdge a b p) := by
  intro e he hLL
  rw [lowerSourceVertices_addEdge s a b p hids]
  by_cases hnew : e = s.nextEdge
  · subst e
    simpa only [State.addEdge, ite_true] using hb
  · have hold : e < s.nextEdge := by change e < s.nextEdge + 1 at he; omega
    simpa only [State.addEdge, ite_eq_right hnew] using hi e hold hLL

private theorem stage_east_avoids_lowerSources (w : ℕ → Fin 3) (n : ℕ) :
    ∀ e < (kmswStage w n).nextEdge, e ∉ (kmswStage w n).LL →
      (kmswStage w n).east e ∉ lowerSourceVertices (kmswStage w n) := by
  induction n with
  | zero => simp [kmswStage, kmswInit, lowerSourceVertices]
  | succ n ih =>
    let s := kmswStage w n
    have hids : ∀ f ∈ s.LL, f < s.nextEdge := by
      intro f hf
      exact (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by
        simp only [List.mem_append]; tauto)
    have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w n).1
    have haP : s.present s.active = true := by
      obtain ⟨es, hes⟩ := kmswStage_UL_last w n
      apply (kmswStage_status w n).2.1
      simp only [hes, List.mem_append, List.mem_singleton]
      exact Or.inr rfl
    have haLL : s.active ∉ s.LL := by
      intro hmem
      have hh := ((kmswStage_status w n).1 s.active ha).mpr (Or.inr hmem)
      rw [haP] at hh
      contradiction
    have hactive : s.east s.active ∉ lowerSourceVertices s := ih _ ha haLL
    have hvbound : s.west s.active < s.nextVertex ∧ s.east s.active < s.nextVertex :=
      kmswStage_endpoints_lt_nextVertex w n s.active ha
    have hfresh : s.nextVertex ∉ lowerSourceVertices s := by
      simp only [lowerSourceVertices, List.mem_cons, List.mem_map, not_or, not_exists]
      refine ⟨by omega, ?_⟩
      rintro f ⟨hf, heq⟩
      have hb : s.west f < s.nextVertex :=
        (kmswStage_endpoints_lt_nextVertex w n f (hids f hf)).1
      omega
    change ∀ e < (kmswStep s (w n)).nextEdge, e ∉ (kmswStep s (w n)).LL →
      (kmswStep s (w n)).east e ∉ lowerSourceVertices (kmswStep s (w n))
    unfold kmswStep
    cases hc : kmswCodeStep (w n) with
    | down =>
      cases hs : s.UR with
      | cons f fs => simpa only [kmswStepOfStep, hs, lowerSourceVertices] using ih
      | nil =>
        simpa only [kmswStepOfStep, hs, lowerSourceVertices] using
          addEdge_east_avoids_lowerSources s (s.east s.active) s.nextVertex true hids ih hfresh
    | up =>
      let t := s.addEdge (s.west s.active) s.nextVertex true
      have hidsT : ∀ f ∈ t.LL, f < t.nextEdge := by
        intro f hf
        exact (hids f hf).trans (Nat.lt_succ_self _)
      have ht := addEdge_east_avoids_lowerSources s (s.west s.active) s.nextVertex true
        hids ih hfresh
      have hactiveT : s.east s.active ∉ lowerSourceVertices t := by
        rw [lowerSourceVertices_addEdge s _ _ _ hids]
        exact hactive
      simpa only [kmswStepOfStep, lowerSourceVertices, t] using
        addEdge_east_avoids_lowerSources t s.nextVertex (s.east s.active) false hidsT ht hactiveT
    | left =>
      cases hs : s.UL.dropLast.reverse with
      | cons f fs =>
        simpa only [kmswStepOfStep, hs, lowerSourceVertices] using
          addEdge_east_avoids_lowerSources s (s.west f) (s.east s.active) true hids ih hactive
      | nil =>
        let t := kmswStepOfStep s .left
        have hLL : t.LL = (s.nextEdge + 1) :: s.LL := by simp [t, kmswStepOfStep, hs]
        have hwestOld : ∀ f ∈ s.LL, t.west f = s.west f := by
          intro f hf
          have hb := hids f hf
          simp [t, kmswStepOfStep, hs, State.addEdge, show f ≠ s.nextEdge by omega,
            show f ≠ s.nextEdge + 1 by omega]
        have hsource : lowerSourceVertices t = 0 :: s.nextVertex :: s.LL.map s.west := by
          unfold lowerSourceVertices
          rw [hLL, List.map_cons]
          have hnewW : t.west (s.nextEdge + 1) = s.nextVertex := by
            simp [t, kmswStepOfStep, hs, State.addEdge]
          rw [hnewW]
          congr 2
          exact List.map_congr_left hwestOld
        change ∀ e < t.nextEdge, e ∉ t.LL → t.east e ∉ lowerSourceVertices t
        intro e he hnot
        have he' : e < s.nextEdge + 2 := by
          have hb : e < s.nextEdge + 1 + 1 := by
            simpa only [t, kmswStepOfStep, hs, State.addEdge] using he
          omega
        have hne1 : e ≠ s.nextEdge + 1 := by
          intro heq
          apply hnot
          rw [hLL, heq]
          exact List.mem_cons_self
        have hnotOld : e ∉ s.LL := by
          intro hm
          exact hnot (by rw [hLL]; exact List.mem_cons_of_mem _ hm)
        by_cases hne : e = s.nextEdge
        · subst e
          have heast : t.east s.nextEdge = s.east s.active := by
            simp [t, kmswStepOfStep, hs, State.addEdge]
          rw [heast, hsource]
          have hm : s.east s.active ∉ 0 :: s.LL.map s.west := hactive
          simp only [List.mem_cons, not_or] at hm ⊢
          exact ⟨hm.1, (by omega), hm.2⟩
        · have hold : e < s.nextEdge := by omega
          have heast : t.east e = s.east e := by
            simp [t, kmswStepOfStep, hs, State.addEdge, hne, hne1]
          have hm : s.east e ∉ 0 :: s.LL.map s.west := ih e hold hnotOld
          have hb : s.east e < s.nextVertex :=
            (kmswStage_endpoints_lt_nextVertex w n e hold).2
          rw [heast, hsource]
          simp only [List.mem_cons, not_or] at hm ⊢
          exact ⟨hm.1, (by omega), hm.2⟩

/-- The root vertex never receives an incoming present edge, for arbitrary -/
theorem uibot_zero_no_incoming (w : ℕ → Fin 3) (e : ℕ)
    (he : EdgePresent w e) : edgeEast w e ≠ 0 := by
  obtain ⟨n, hn, hp⟩ := he
  have hLL : e ∉ (kmswStage w n).LL := by
    intro hm
    have hh := ((kmswStage_status w n).1 e hn).mpr (Or.inr hm)
    rw [hp] at hh
    contradiction
  have hgood := stage_east_avoids_lowerSources w n e hn hLL
  rw [(edge_endpoints_eq w hn).2] at hgood
  intro hz
  apply hgood
  exact List.mem_cons.mpr (Or.inl hz)

private theorem stage_LL_mem_mono (w : ℕ → Fin 3) {n m f : ℕ}
    (hnm : n ≤ m) (hf : f ∈ (kmswStage w n).LL) : f ∈ (kmswStage w m).LL := by
  induction m, hnm using Nat.le_induction with
  | base => exact hf
  | succ m hm ih =>
    change f ∈ (kmswStep (kmswStage w m) (w m)).LL
    unfold kmswStep
    cases hc : kmswCodeStep (w m) with
    | down => cases hs : (kmswStage w m).UR <;> simpa [kmswStepOfStep, hs, State.addEdge] using ih
    | up => simpa only [kmswStepOfStep, State.addEdge] using ih
    | left =>
      cases hs : (kmswStage w m).UL.dropLast.reverse with
      | cons a as => simpa only [kmswStepOfStep, hs, State.addEdge] using ih
      | nil => simpa only [kmswStepOfStep, hs, State.addEdge, List.mem_cons] using Or.inr ih

/-- The west endpoint of any LL edge remains a source in the limit;
missing LL edges contribute no directed incoming arrows (`lem-uibot-bdy`, -/
theorem uibot_LL_west_no_incoming (w : ℕ → Fin 3) (n f : ℕ)
    (hf : f ∈ (kmswStage w n).LL) (e : ℕ) (he : EdgePresent w e) :
    edgeEast w e ≠ (kmswStage w n).west f := by
  obtain ⟨j, hj, hp⟩ := he
  let m := max n j
  have hnm : n ≤ m := le_max_left _ _
  have hjm : j ≤ m := le_max_right _ _
  have hfM := stage_LL_mem_mono w hnm hf
  have heM := present_mono w hj hp m hjm
  have heLL : e ∉ (kmswStage w m).LL := by
    intro hm
    have hh := ((kmswStage_status w m).1 e heM.1).mpr (Or.inr hm)
    rw [heM.2] at hh
    contradiction
  have hgood := stage_east_avoids_lowerSources w m e heM.1 heLL
  have hfbound : f < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 f (by
      simp only [List.mem_append]; tauto)
  have hstable := (kmswStage_endpoints_stable w hnm hfbound).1
  rw [(edge_endpoints_eq w heM.1).2] at hgood
  intro heq
  apply hgood
  apply List.mem_cons.mpr
  right
  exact List.mem_map.mpr ⟨f, hfM, hstable.trans heq.symm⟩

/-- Each negative boundary vertex is the west endpoint of an LL missing
edge at its coordinate hit (`lem-uibot-bdy`, -/
theorem boundaryVertex_neg_LL_west (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ -1) :
    ∃ n f, f ∈ (kmswStage w n).LL ∧
      (kmswStage w n).west f = boundaryVertex w h k := by
  let τ := boundaryHitTime w h k
  have hfind : τ = Nat.find (h.leftHit k hk) := by
    dsimp only [τ, boundaryHitTime]
    simp only [dite_eq_right (by omega : k ≠ 0), dite_eq_right (by omega : ¬ 0 < k)]
  have hstep : ∀ i, |L w (i + 1) - L w i| ≤ 1 := by
    intro i
    have hs : L w (i + 1) = L w i +
        (RandomWalk.lazyTwoDimensionalStep (w i)).1 := Finset.sum_range_succ _ _
    rw [hs, add_sub_cancel_left]
    change |((w i).val : ℤ) - 1| ≤ 1
    have hb := (w i).isLt
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hchar := (strict_running_minimum_iff_first_hit (L w) rfl hstep τ τ k
    (by omega) (h.leftHit k hk)).mpr
      ⟨le_rfl, boundaryHitTime_left_spec w h hk, hfind⟩
  have hrec := (Finset.mem_filter.mp hchar.1).2
  have hpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hchar.1).1).1
  have hmem : kmswLLCreatedEdge w τ ∈ (kmswStage w τ).LL := by
    rw [kmswStage_LL_eq]
    apply List.mem_map.mpr
    refine ⟨τ, List.mem_reverse.mpr ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega), decide_eq_true ⟨by omega, hrec⟩⟩
  exact ⟨τ, kmswLLCreatedEdge w τ, hmem,
    (boundaryVertex_left_missing_edge w h hk).1⟩

/-- Every nonpositive-index boundary vertex has no incoming present edge -/
theorem boundaryVertex_nonpos_no_incoming (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≤ 0) (e : ℕ)
    (he : EdgePresent w e) : edgeEast w e ≠ boundaryVertex w h k := by
  by_cases hk0 : k = 0
  · subst k
    rw [boundaryVertex_zero]
    exact uibot_zero_no_incoming w e he
  · obtain ⟨n, f, hf, hw⟩ := boundaryVertex_neg_LL_west w h (by omega : k ≤ -1)
    rw [← hw]
    exact uibot_LL_west_no_incoming w n f hf e he

/-- Among allocated vertices the sources are exactly the nonpositive-index
boundary vertices, including the initial root vertex (`lem-uibot-bdy`, -/
theorem allocated_source_iff_left_boundary (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    (¬ ∃ e, EdgePresent w e ∧ edgeEast w e = v) ↔
      ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex w h k := by
  constructor
  · exact allocated_source_is_left_boundary w h v hv
  · rintro ⟨k, hk, rfl⟩ ⟨e, he, hend⟩
    exact boundaryVertex_nonpos_no_incoming w h hk e he hend

/-- Almost surely the iid one-sided map has exactly the left-boundary
sources, simultaneously for all allocated vertices (`lem-uibot-bdy`, -/
theorem iidCodes_ae_sources :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ v : ℕ,
        (∃ n, v < (kmswStage (fun i => ω (i + 1)) n).nextVertex) →
          ((¬ ∃ e, EdgePresent (fun i => ω (i + 1)) e ∧
            edgeEast (fun i => ω (i + 1)) e = v) ↔
              ∃ k : ℤ, k ≤ 0 ∧ v = boundaryVertex (fun i => ω (i + 1)) h k) := by
  filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω h
  exact ⟨h, allocated_source_iff_left_boundary _ h⟩

end DirectedDistances.KMSW
