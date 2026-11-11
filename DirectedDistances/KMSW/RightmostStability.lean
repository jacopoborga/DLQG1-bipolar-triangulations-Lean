module

public import DirectedDistances.KMSW.RightmostCoalescenceM0
public import DirectedDistances.KMSW.CommonFutureM0
public import DirectedDistances.KMSW.OutgoingIntervalFreshLeft
public import DirectedDistances.KMSW.LocalFinitenessIID

/-! # Stage rightmost edges and their stability in the one-sided KMSW map

Work towards the coalescence clause of `lem-uibot-bdy`

**Caveat on "rightmost".** Throughout this file the "rightmost" dart, edge and
path is *defined* as the least-ID present outgoing edge.  Its identification
with the right end of the rotation-order outgoing interval (the geometric
rightmost edge of `lem-uibot-bdy`) is NOT proved in this file (see
`KMSW/RightmostBridge.lean`, if present).  Hence the theorems below prove
coalescence of least-ID outgoing paths; they give the coalescence clause of
`lem-uibot-bdy` only together with that identification. -/

public section
namespace DirectedDistances.KMSW

open Filter Quiver MeasureTheory

/-- The least-ID present outgoing dart at a finite KMSW stage (`def-kmsw`,
outgoing; that this is the right end of the rotation-order outgoing interval
is NOT proved in this file (see `KMSW/RightmostBridge.lean`, if present). -/
@[expose] noncomputable def kmswStageRightmostOutgoingDart
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    StageDart (kmswStage w n).nextEdge :=
  (⟨Nat.find h, (Nat.find_spec h).1⟩, false)

 
theorem kmswStageRightmostOutgoingDart_spec
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    stageOutgoing (kmswStage w n)
        (kmswStageRightmostOutgoingDart w n v h) ∧
      stageEndpoint (kmswStage w n)
        (kmswStageRightmostOutgoingDart w n v h) = v := by
  constructor
  · exact ⟨rfl, (Nat.find_spec h).2.1⟩
  · exact (Nat.find_spec h).2.2

/-- The selected stage dart has least ID among present darts leaving its -/
theorem kmswStageRightmostOutgoingDart_min
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v)
    (e : ℕ) (he : e < (kmswStage w n).nextEdge)
    (hp : (kmswStage w n).present e = true)
    (hw : (kmswStage w n).west e = v) :
    (kmswStageRightmostOutgoingDart w n v h).1.val ≤ e := by
  exact Nat.find_min' h ⟨he, hp, hw⟩

/-- A present outgoing edge at stage `n` remains a present outgoing edge at -/
theorem kmswStage_outgoing_exists_succ
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    ∃ e, e < (kmswStage w (n + 1)).nextEdge ∧
      (kmswStage w (n + 1)).present e = true ∧
        (kmswStage w (n + 1)).west e = v := by
  obtain ⟨e, he, hp, hw⟩ := h
  have hp' := present_mono w he hp (n + 1) (Nat.le_succ n)
  have he' := (kmswStage_endpoints_stable w (Nat.le_succ n) he).1
  exact ⟨e, hp'.1, hp'.2, he'.trans hw⟩

/-- The least-ID present outgoing dart of a vertex is unchanged by one KMSW -/
theorem kmswStageRightmostOutgoingDart_succ
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    (kmswStageRightmostOutgoingDart w (n + 1) v
      (kmswStage_outgoing_exists_succ w n v h)).1.val =
    (kmswStageRightmostOutgoingDart w n v h).1.val := by
  classical
  let s := kmswStage w n
  let t := kmswStage w (n + 1)
  let m := Nat.find h
  have hm := Nat.find_spec h
  have hn := kmswStage_outgoing_exists_succ w n v h
  change Nat.find hn = Nat.find h
  apply (Nat.find_eq_iff hn).2
  refine ⟨?_, ?_⟩
  · exact ⟨hm.1.trans_le (kmswStage_nextEdge_mono w (Nat.le_succ n)),
      (present_mono w hm.1 hm.2.1 (n + 1) (Nat.le_succ n)).2,
      ((kmswStage_endpoints_stable w (Nat.le_succ n) hm.1).1).trans hm.2.2⟩
  · intro f hfm hfc
    rcases hfc with ⟨hfnew, hfpnew, hwnew⟩
    change f < Nat.find h at hfm
    have hf : f < s.nextEdge := lt_trans hfm hm.1
    have hwest : s.west f = v := by
      have hs := (kmswStage_endpoints_stable w (Nat.le_succ n) hf).1
      exact hs.symm.trans hwnew
    have hpresentOld : s.present f = true := by
      have hchange := kmswStep_present_existing s (w n) hf
      change (kmswStep s (w n)).present f = true at hfpnew
      rw [hchange] at hfpnew
      by_cases hactive : f = (kmswStep s (w n)).active
      · cases hc : kmswCodeStep (w n) with
        | down =>
          cases hr : s.UR with
          | nil =>
            have ha : (kmswStep s (w n)).active = s.nextEdge := by
              simp [kmswStep, hc, kmswStepOfStep, hr, State.addEdge]
            rw [ha] at hactive
            omega
          | cons e es =>
            have ha : (kmswStep s (w n)).active = e := by
              simp [kmswStep, hc, kmswStepOfStep, hr]
            have hfe : f = e := hactive.trans ha
            have hwestE : s.west e = v := by simpa [hfe] using hwest
            subst f
            have heUR : e ∈ s.UR := by rw [hr]; simp
            have hneq := stageOutgoing_UR_west_empty w n e heUR m hm.1 hm.2.1
            exact (hneq (hm.2.2.trans hwestE.symm)).elim
        | left =>
          cases hl : s.UL.dropLast.reverse <;>
            simp [kmswStep, hc, kmswStepOfStep, hl, State.addEdge] at hactive <;> omega
        | up =>
          simp [kmswStep, hc, kmswStepOfStep, State.addEdge] at hactive
          omega
      · simpa [hactive] using hfpnew
    have hle : Nat.find h ≤ f := Nat.find_min' h ⟨hf, hpresentOld, hwest⟩
    omega

/-- Existing outgoing availability persists to every later finite stage -/
theorem kmswStage_outgoing_exists_of_le
    (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    ∃ e, e < (kmswStage w m).nextEdge ∧
      (kmswStage w m).present e = true ∧ (kmswStage w m).west e = v := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | @succ m hnm ih => exact kmswStage_outgoing_exists_succ w m v ih

/-- Once present at a vertex, its least-ID outgoing dart is stable at every -/
theorem kmswStageRightmostOutgoingDart_stable
    (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v) :
    (kmswStageRightmostOutgoingDart w m v
      (kmswStage_outgoing_exists_of_le w hnm h)).1.val =
    (kmswStageRightmostOutgoingDart w n v h).1.val := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | @succ m hnm ih =>
    have hcur := kmswStage_outgoing_exists_of_le w hnm h
    rw [kmswStageRightmostOutgoingDart_succ w m v hcur]
    exact ih

/-- The chosen dart lies in the single stage rotation interval containing all
present outgoing darts at its vertex (`def-kmsw`, -/
theorem kmswStageRightmostOutgoingDart_interval
    (w : ℕ → Fin 3) (n v : ℕ)
    (h : ∃ e, e < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present e = true ∧ (kmswStage w n).west e = v)
    (d : StageDart (kmswStage w n).nextEdge)
    (hd : stageOutgoing (kmswStage w n) d)
    (hdv : stageEndpoint (kmswStage w n) d = v) :
    RotationArc (stageRot w n) (stageOutgoing (kmswStage w n))
        (kmswStageRightmostOutgoingDart w n v h) d ∨
      RotationArc (stageRot w n) (stageOutgoing (kmswStage w n))
        d (kmswStageRightmostOutgoingDart w n v h) := by
  have hr := kmswStageRightmostOutgoingDart_spec w n v h
  have hv : stageEndpoint (kmswStage w n)
      (kmswStageRightmostOutgoingDart w n v h) = stageEndpoint (kmswStage w n) d :=
    hr.2.trans hdv.symm
  exact (stageOutgoingInvariant_all w n).1 _ _ hv hr.1 hd

/-- The least-ID present outgoing edge in the limiting one-sided map
here means least-ID outgoing; its identification with the right end of the
rotation-order outgoing interval (the geometric rightmost edge of
`lem-uibot-bdy`) is NOT proved in this file (see `KMSW/RightmostBridge.lean`,
if present). -/
@[expose] noncomputable def kmswM0RightmostOutgoingEdge
    (w : ℕ → Fin 3) (v : ℕ)
    (h : ∃ e, EdgePresent w e ∧ edgeWest w e = v) : ℕ :=
  by classical exact Nat.find h

 
theorem kmswM0RightmostOutgoingEdge_spec
    (w : ℕ → Fin 3) (v : ℕ)
    (h : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    EdgePresent w (kmswM0RightmostOutgoingEdge w v h) ∧
      edgeWest w (kmswM0RightmostOutgoingEdge w v h) = v :=
  by classical exact Nat.find_spec h

/-- The limit edge is eventually exactly the finite-stage selector, since
once it is present no smaller outgoing edge can appear (`remark-kmsw-infinite`, -/
theorem kmswStageRightmostOutgoingDart_eventually_eq_limit
    (w : ℕ → Fin 3) (v : ℕ)
    (h : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    ∃ N, ∀ m, N ≤ m →
      ∀ hm : ∃ f, f < (kmswStage w m).nextEdge ∧
        (kmswStage w m).present f = true ∧ (kmswStage w m).west f = v,
        (kmswStageRightmostOutgoingDart w m v hm).1.val =
          kmswM0RightmostOutgoingEdge w v h := by
  classical
  let e := kmswM0RightmostOutgoingEdge w v h
  obtain ⟨hePresent, heWest⟩ := kmswM0RightmostOutgoingEdge_spec w v h
  obtain ⟨N, hNbound, hNpresent⟩ := hePresent
  let hstage : ∃ f, f < (kmswStage w N).nextEdge ∧
      (kmswStage w N).present f = true ∧ (kmswStage w N).west f = v :=
    ⟨e, hNbound, hNpresent, (edge_endpoints_eq w hNbound).1.trans heWest⟩
  let f := Nat.find hstage
  have hf := Nat.find_spec hstage
  have hstageMin : f ≤ e := by
    exact Nat.find_min' hstage ⟨hNbound, hNpresent,
      (edge_endpoints_eq w hNbound).1.trans heWest⟩
  have hfGlobal : EdgePresent w f ∧ edgeWest w f = v := by
    refine ⟨EdgePresent.of_stage_present hf.1 hf.2.1, ?_⟩
    exact ((edge_endpoints_eq w hf.1).1.symm).trans hf.2.2
  have heMin : e ≤ f := by
    change Nat.find h ≤ f
    exact Nat.find_min' h hfGlobal
  have hEq : f = e := Nat.le_antisymm hstageMin heMin
  refine ⟨N, ?_⟩
  intro m hNm hm
  have hAtM := kmswStage_outgoing_exists_of_le w hNm hstage
  have hstable := kmswStageRightmostOutgoingDart_stable w hNm hstage
  have hp : hm = hAtM := Subsingleton.elim _ _
  rw [hp]
  calc
    (kmswStageRightmostOutgoingDart w m v hAtM).1.val =
        (kmswStageRightmostOutgoingDart w N v hstage).1.val := hstable
    _ = f := rfl
    _ = e := hEq
    _ = kmswM0RightmostOutgoingEdge w v h := rfl

/-- At every stage where a vertex already has an outgoing edge, the stable
stage selector is the least outgoing edge in the limit (`def-kmsw`, -/
theorem kmswStageRightmostOutgoingDart_eq_limit
    (w : ℕ → Fin 3) (n v : ℕ)
    (hs : ∃ f, f < (kmswStage w n).nextEdge ∧
      (kmswStage w n).present f = true ∧ (kmswStage w n).west f = v)
    (h : ∃ e, EdgePresent w e ∧ edgeWest w e = v) :
    (kmswStageRightmostOutgoingDart w n v hs).1.val =
      kmswM0RightmostOutgoingEdge w v h := by
  classical
  let e := kmswM0RightmostOutgoingEdge w v h
  obtain ⟨hePresent, heWest⟩ := kmswM0RightmostOutgoingEdge_spec w v h
  obtain ⟨k, hkbound, hkpresent⟩ := hePresent
  have hAtK : ∃ f, f < (kmswStage w k).nextEdge ∧
      (kmswStage w k).present f = true ∧ (kmswStage w k).west f = v :=
    ⟨e, hkbound, hkpresent, (edge_endpoints_eq w hkbound).1.trans heWest⟩
  let m := max n k
  have hnm : n ≤ m := le_max_left _ _
  have hkm : k ≤ m := le_max_right _ _
  have hsAtM := kmswStage_outgoing_exists_of_le w hnm hs
  have heAtM : e < (kmswStage w m).nextEdge ∧
      (kmswStage w m).present e = true ∧ (kmswStage w m).west e = v := by
    have hp := present_mono w hkbound hkpresent m hkm
    have hw := (kmswStage_endpoints_stable w hkm hkbound).1
    exact ⟨hp.1, hp.2, hw.trans ((edge_endpoints_eq w hkbound).1.trans heWest)⟩
  have hStageLe :
      (kmswStageRightmostOutgoingDart w m v hsAtM).1.val ≤ e :=
    kmswStageRightmostOutgoingDart_min w m v hsAtM e heAtM.1 heAtM.2.1 heAtM.2.2
  have hstable := kmswStageRightmostOutgoingDart_stable w hnm hs
  have hstable' : (kmswStageRightmostOutgoingDart w m v hsAtM).1.val =
      (kmswStageRightmostOutgoingDart w n v hs).1.val := hstable
  have hStageLeN : (kmswStageRightmostOutgoingDart w n v hs).1.val ≤ e := by
    rw [← hstable']
    exact hStageLe
  have hStageGlobal : EdgePresent w
        (kmswStageRightmostOutgoingDart w n v hs).1.val ∧
      edgeWest w (kmswStageRightmostOutgoingDart w n v hs).1.val = v := by
    have hf := Nat.find_spec hs
    refine ⟨EdgePresent.of_stage_present hf.1 hf.2.1, ?_⟩
    exact ((edge_endpoints_eq w hf.1).1.symm).trans hf.2.2
  have hGlobalLe : e ≤ (kmswStageRightmostOutgoingDart w n v hs).1.val := by
    change Nat.find h ≤ (kmswStageRightmostOutgoingDart w n v hs).1.val
    exact Nat.find_min' h hStageGlobal
  have heq : (kmswStageRightmostOutgoingDart w n v hs).1.val = e :=
    Nat.le_antisymm hStageLeN hGlobalLe
  exact heq

/-- The limit least-ID outgoing edge from an allocated vertex ("rightmost" in
this file's naming only; see the module caveat), using the no-sink
consequence of an unbounded-below right walk (`lem-uibot-bdy`, -/
@[expose] noncomputable def kmswM0RightmostOutgoingEdgeFrom
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : ℕ :=
  kmswM0RightmostOutgoingEdge w v
    (uibot_allocated_vertex_outgoing w hR v (halloc v))

/-- The selected limit edge is an arrow with the specified source -/
theorem kmswM0RightmostOutgoingEdgeFrom_spec
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) :
    EdgePresent w (kmswM0RightmostOutgoingEdgeFrom w hR halloc v) ∧
      edgeWest w (kmswM0RightmostOutgoingEdgeFrom w hR halloc v) = v :=
  kmswM0RightmostOutgoingEdge_spec w v
    (uibot_allocated_vertex_outgoing w hR v (halloc v))

/-- The next vertex along the limit least-ID path ("rightmost" in this file's
naming only; see the module caveat) (`def-infinite-geo`, -/
@[expose] noncomputable def kmswM0RightmostNext
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : ℕ :=
  edgeEast w (kmswM0RightmostOutgoingEdgeFrom w hR halloc v)

/-- The least-ID vertex orbit in the limit map ("rightmost" in this file's
naming only; see the module caveat) (`def-infinite-geo`, -/
@[expose] noncomputable def kmswM0RightmostOrbit
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : ℕ → ℕ
  | 0 => v
  | i + 1 => kmswM0RightmostNext w hR halloc
      (kmswM0RightmostOrbit w hR halloc v i)

/-- The edge selected at a given step of the limit least-ID orbit ("rightmost"
in this file's naming only; see the module caveat). -/
@[expose] noncomputable def kmswM0RightmostOrbitEdge
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v i : ℕ) : ℕ :=
  kmswM0RightmostOutgoingEdgeFrom w hR halloc
    (kmswM0RightmostOrbit w hR halloc v i)

/-- Each orbit edge is present and has the consecutive prescribed endpoints -/
theorem kmswM0RightmostOrbitEdge_spec
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v i : ℕ) :
    EdgePresent w (kmswM0RightmostOrbitEdge w hR halloc v i) ∧
      edgeWest w (kmswM0RightmostOrbitEdge w hR halloc v i) =
        kmswM0RightmostOrbit w hR halloc v i ∧
      edgeEast w (kmswM0RightmostOrbitEdge w hR halloc v i) =
        kmswM0RightmostOrbit w hR halloc v (i + 1) := by
  have h := kmswM0RightmostOutgoingEdgeFrom_spec w hR halloc
    (kmswM0RightmostOrbit w hR halloc v i)
  exact ⟨h.1, h.2, rfl⟩

/-- Two deterministic limit least-ID orbits ("rightmost" in this file's naming
only; see the module caveat) agree forever after sharing a vertex.  The
geometric interpretation of this as the coalescence clause of `lem-uibot-bdy`
least-ID with the rotation-order right end of the outgoing interval (proved so
far only at the source vertex in `KMSW/RightmostIdentify.lean`). -/
theorem kmswM0RightmostOrbit_tail_eq
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (x y i j : ℕ)
    (hxy : kmswM0RightmostOrbit w hR halloc x i =
      kmswM0RightmostOrbit w hR halloc y j) :
    ∀ t, kmswM0RightmostOrbit w hR halloc x (i + t) =
      kmswM0RightmostOrbit w hR halloc y (j + t) := by
  intro t
  induction t with
  | zero => simpa using hxy
  | succ t ih =>
    rw [Nat.add_succ, Nat.add_succ,
      kmswM0RightmostOrbit, kmswM0RightmostOrbit, ih]

/-- The finite path prefix following the limit least-ID orbit ("rightmost" in
this file's naming only; see the module caveat). -/
@[expose] noncomputable def kmswM0RightmostPathPrefix
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : (n : ℕ) → Path (⟨v⟩ : PresentVertex w)
      ⟨kmswM0RightmostOrbit w hR halloc v n⟩
  | 0 => Path.nil
  | n + 1 =>
    let e := kmswM0RightmostOrbitEdge w hR halloc v n
    let he := kmswM0RightmostOrbitEdge_spec w hR halloc v n
    (kmswM0RightmostPathPrefix w hR halloc v n).cons
      ⟨e, he.1, by simpa [e, kmswM0RightmostOrbitEdge] using he.2.1,
        by simpa [e, kmswM0RightmostOrbitEdge] using he.2.2⟩

/-- The least-ID finite prefix ("rightmost" in this file's naming only; see the
module caveat) contains exactly `n` directed edges. -/
theorem kmswM0RightmostPathPrefix_length
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v n : ℕ) :
    (kmswM0RightmostPathPrefix w hR halloc v n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [kmswM0RightmostPathPrefix, ih]

/-- The prefix edge list is the selected least-ID edge sequence ("rightmost" in
this file's naming only; see the module caveat). -/
theorem kmswM0RightmostPathPrefix_edges
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v n : ℕ) :
    pathEdgeList (kmswM0RightmostPathPrefix w hR halloc v n) =
      List.ofFn (fun i : Fin n =>
        kmswM0RightmostOrbitEdge w hR halloc v i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kmswM0RightmostPathPrefix, pathEdgeList]
    rw [ih, List.ofFn_succ_last]
    simp

/-- The infinite directed path that always takes the least-ID present
"Rightmost" is by definition least-ID; that this is the geometric rightmost
(rotation-order) path is NOT proved here (see `KMSW/RightmostBridge.lean`, if
present). -/
@[expose] noncomputable def kmswM0RightmostPath
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v : ℕ) : InfinitePresentPath w ⟨v⟩ where
  edge := kmswM0RightmostOrbitEdge w hR halloc v
  initial N :=
    ⟨⟨kmswM0RightmostOrbit w hR halloc v N⟩,
      kmswM0RightmostPathPrefix w hR halloc v N⟩
  prefix_length N := kmswM0RightmostPathPrefix_length w hR halloc v N
  prefix_edges N := kmswM0RightmostPathPrefix_edges w hR halloc v N

/-- The path's `N`th vertex is its orbit vertex at index `N`. -/
theorem kmswM0RightmostPath_initial_id
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (v N : ℕ) :
    ((kmswM0RightmostPath w hR halloc v).initial N).1.id =
      kmswM0RightmostOrbit w hR halloc v N := rfl

/-- The least-ID ("rightmost" by definition only, see the module docstring)
path from a vertex, with vertex allocation supplied by the finite-incidence -/
@[expose] noncomputable def kmswM0RightmostPathOfFiniteIncidence
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage w n).nextEdge ∧
        ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) : InfinitePresentPath w ⟨v⟩ :=
  kmswM0RightmostPath w hR (kmsw_vertex_allocated_of_finite_incidence w hfin) v

/- Any two limit least-ID outgoing paths agree after they visit a common
least-ID paths; it is the geometric rightmost-path statement only together -/
theorem kmswM0RightmostPath_coalesces_of_common_vertex
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (x y i j : ℕ)
    (hxy : ((kmswM0RightmostPath w hR halloc x).initial i).1.id =
      ((kmswM0RightmostPath w hR halloc y).initial j).1.id) :
    ∀ t, ((kmswM0RightmostPath w hR halloc x).initial (i + t)).1.id =
      ((kmswM0RightmostPath w hR halloc y).initial (j + t)).1.id := by
  have hxy' : kmswM0RightmostOrbit w hR halloc x i =
      kmswM0RightmostOrbit w hR halloc y j := by
    simpa [kmswM0RightmostPath] using hxy
  intro t
  simpa [kmswM0RightmostPath] using
    kmswM0RightmostOrbit_tail_eq w hR halloc x y i j hxy' t

private theorem kmswM0RightmostOrbit_stage_successor
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (q : ℕ) (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (v i : ℕ)
    (hv : kmswM0RightmostOrbit w hR halloc v i <
      (kmswStage w (q - 1)).nextVertex)
    (hne : kmswM0RightmostOrbit w hR halloc v i ≠
      (kmswStage w (q - 1)).east (act w (q - 1))) :
    ∃ e, e < (kmswStage w (q - 1)).nextEdge ∧
      (kmswStage w (q - 1)).present e = true ∧
      (kmswStage w (q - 1)).west e = kmswM0RightmostOrbit w hR halloc v i ∧
      (kmswStage w (q - 1)).east e = kmswM0RightmostOrbit w hR halloc v (i + 1) := by
  let t := q - 1
  let x := kmswM0RightmostOrbit w hR halloc v i
  let z := (kmswStage w t).east (act w t)
  obtain ⟨y, ⟨a⟩⟩ := allocated_stage_vertex_has_outgoing_of_strict_record
    w q hA hq x (by simpa [t] using hv) (by simpa [t, z] using hne)
  have hs : ∃ e, e < (kmswStage w t).nextEdge ∧
      (kmswStage w t).present e = true ∧ (kmswStage w t).west e = x :=
    ⟨a.val, a.property.1, a.property.2.1, a.property.2.2.1⟩
  have hGlobal := uibot_allocated_vertex_outgoing w hR x (by
    exact ⟨q - 1, by simpa [t] using hv⟩)
  have hEq := kmswStageRightmostOutgoingDart_eq_limit w t x hs hGlobal
  let d := kmswStageRightmostOutgoingDart w t x hs
  have hd := kmswStageRightmostOutgoingDart_spec w t x hs
  have hsel : d.1.val = kmswM0RightmostOutgoingEdgeFrom w hR halloc x := by
    simpa [d, t, kmswM0RightmostOutgoingEdgeFrom] using hEq
  refine ⟨d.1.val, d.1.isLt, hd.1.2, ?_, ?_⟩
  · have hdb : d.2 = false := rfl
    simpa [stageEndpoint, hdb, d, t, x] using hd.2
  change (kmswStage w t).east d.1.val =
    edgeEast w (kmswM0RightmostOutgoingEdgeFrom w hR halloc x)
  rw [← hsel]
  exact (edge_endpoints_eq w d.1.isLt).2

private theorem recordVertex_id_eq_stage_sink
    (w : ℕ → Fin 3) (q : ℕ)
    (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q) :
    (recordVertex w q).id = (kmswStage w (q - 1)).east (act w (q - 1)) := by
  let t := q - 1
  have hdownUR := record_stage_before_empty_UR_public w q hA hq
  have hnext : activeInitial w q = (kmswStage w t).east (act w t) := by
    have htq : t + 1 = q := by dsimp [t]; omega
    rw [← htq]
    exact activeInitial_next_of_empty_UR_public w t
      (by simpa [t] using hdownUR.1) (by simpa [t] using hdownUR.2)
  change (kmswStage w q).west (act w q) = _
  rw [← CutConverse.activeInitial_eq w q]
  exact hnext

private theorem exists_strict_record_after_avoiding_two
    (w : ℕ → Fin 3) (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (N x y : ℕ) :
    ∃ q, (∀ j < q, R w q < R w j) ∧ N < q ∧
      recordVertex w q ≠ (⟨x⟩ : PresentVertex w) ∧
      recordVertex w q ≠ (⟨y⟩ : PresentVertex w) := by
  classical
  let q₁ := Classical.choose ((right_record_infinite w hR).exists_gt N)
  have hq₁ : (∀ j < q₁, R w q₁ < R w j) ∧ N < q₁ := by
    simpa only [q₁, Set.mem_ofPred_eq] using
      (Classical.choose_spec ((right_record_infinite w hR).exists_gt N))
  let q₂ := Classical.choose ((right_record_infinite w hR).exists_gt q₁)
  have hq₂ : (∀ j < q₂, R w q₂ < R w j) ∧ q₁ < q₂ := by
    simpa only [q₂, Set.mem_ofPred_eq] using
      (Classical.choose_spec ((right_record_infinite w hR).exists_gt q₁))
  let q₃ := Classical.choose ((right_record_infinite w hR).exists_gt q₂)
  have hq₃ : (∀ j < q₃, R w q₃ < R w j) ∧ q₂ < q₃ := by
    simpa only [q₃, Set.mem_ofPred_eq] using
      (Classical.choose_spec ((right_record_infinite w hR).exists_gt q₂))
  let z₁ := recordVertex w q₁
  let z₂ := recordVertex w q₂
  let z₃ := recordVertex w q₃
  have hA₂ : ∀ j < q₂, R w q₂ ≤ R w j - 1 := by
    intro j hj
    have h := hq₂.1 j hj
    omega
  have hA₃ : ∀ j < q₃, R w q₃ ≤ R w j - 1 := by
    intro j hj
    have h := hq₃.1 j hj
    omega
  have h12 : z₁ ≠ z₂ := by
    exact recordVertex_ne w hq₂.2 hA₂
  have h13 : z₁ ≠ z₃ := by
    exact recordVertex_ne w (hq₂.2.trans hq₃.2) hA₃
  have h23 : z₂ ≠ z₃ := by
    exact recordVertex_ne w hq₃.2 hA₃
  by_cases h1x : z₁ = (⟨x⟩ : PresentVertex w)
  · by_cases h1y : z₁ = (⟨y⟩ : PresentVertex w)
    · have h2x : z₂ ≠ (⟨x⟩ : PresentVertex w) := by
        intro he
        exact h12 (h1x.trans he.symm)
      have h2y : z₂ ≠ (⟨y⟩ : PresentVertex w) := by
        intro he
        exact h12 (h1y.trans he.symm)
      exact ⟨q₂, hq₂.1, hq₁.2.trans hq₂.2, by simpa [z₂] using h2x,
        by simpa [z₂] using h2y⟩
    · by_cases h2y : z₂ = (⟨y⟩ : PresentVertex w)
      · have h3x : z₃ ≠ (⟨x⟩ : PresentVertex w) := by
          intro he
          exact h13 (h1x.trans he.symm)
        have h3y : z₃ ≠ (⟨y⟩ : PresentVertex w) := by
          intro he
          exact h23 (h2y.trans he.symm)
        exact ⟨q₃, hq₃.1, hq₁.2.trans (hq₂.2.trans hq₃.2),
          by simpa [z₃] using h3x, by simpa [z₃] using h3y⟩
      · have h2x : z₂ ≠ (⟨x⟩ : PresentVertex w) := by
          intro he
          exact h12 (h1x.trans he.symm)
        exact ⟨q₂, hq₂.1, hq₁.2.trans hq₂.2,
          by simpa [z₂] using h2x, by simpa [z₂] using h2y⟩
  · by_cases h1y : z₁ = (⟨y⟩ : PresentVertex w)
    · by_cases h2x : z₂ = (⟨x⟩ : PresentVertex w)
      · have h3x : z₃ ≠ (⟨x⟩ : PresentVertex w) := by
          intro he
          exact h23 (h2x.trans he.symm)
        have h3y : z₃ ≠ (⟨y⟩ : PresentVertex w) := by
          intro he
          exact h13 (h1y.trans he.symm)
        exact ⟨q₃, hq₃.1, hq₁.2.trans (hq₂.2.trans hq₃.2),
          by simpa [z₃] using h3x, by simpa [z₃] using h3y⟩
      · have h2y : z₂ ≠ (⟨y⟩ : PresentVertex w) := by
          intro he
          exact h12 (h1y.trans he.symm)
        exact ⟨q₂, hq₂.1, hq₁.2.trans hq₂.2,
          by simpa [z₂] using h2x, by simpa [z₂] using h2y⟩
    · exact ⟨q₁, hq₁.1, hq₁.2, by simpa [z₁] using h1x,
        by simpa [z₁] using h1y⟩

/-- At a strict downward record, the limit least-ID orbit ("rightmost" in this
file's naming only; see the module caveat) from every vertex
allocated at the preceding stage visits that stage's unique sink -/
theorem kmswM0RightmostOrbit_hits_strict_record_stage
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (q : ℕ) (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (v : ℕ) (hv : v < (kmswStage w (q - 1)).nextVertex) :
    ∃ i, kmswM0RightmostOrbit w hR halloc v i =
      (kmswStage w (q - 1)).east (act w (q - 1)) := by
  classical
  let t := q - 1
  let z := (kmswStage w t).east (act w t)
  by_contra hnone
  have hnever : ∀ i, kmswM0RightmostOrbit w hR halloc v i ≠ z := by
    intro i hi
    exact hnone ⟨i, by simpa [t, z] using hi⟩
  have hbound : ∀ i, kmswM0RightmostOrbit w hR halloc v i <
      (kmswStage w t).nextVertex := by
    intro i
    induction i with
    | zero => simpa [kmswM0RightmostOrbit, t] using hv
    | succ i ih =>
      obtain ⟨e, he, hp, hw, heast⟩ := kmswM0RightmostOrbit_stage_successor
        w hR halloc q hA hq v i ih (by simpa [t, z] using hnever i)
      have hb := (CutConverse.endpoint_bound w t e he).2
      rw [heast] at hb
      exact hb
  have hrankStep : ∀ i,
      kmswStageRank w t (kmswM0RightmostOrbit w hR halloc v i) <
        kmswStageRank w t (kmswM0RightmostOrbit w hR halloc v (i + 1)) := by
    intro i
    obtain ⟨e, he, hp, hw, heast⟩ := kmswM0RightmostOrbit_stage_successor
      w hR halloc q hA hq v i (hbound i) (by simpa [t, z] using hnever i)
    have hr := kmswStageRank_strict w t e he
    rw [hw, heast] at hr
    exact hr
  have hrank : StrictMono
      (fun i => kmswStageRank w t (kmswM0RightmostOrbit w hR halloc v i)) :=
    strictMono_nat_of_lt_succ hrankStep
  have hinj : Function.Injective (kmswM0RightmostOrbit w hR halloc v) := by
    intro i j hij
    apply hrank.injective
    exact congrArg (kmswStageRank w t) hij
  let f : ℕ → Fin (kmswStage w t).nextVertex := fun i =>
    ⟨kmswM0RightmostOrbit w hR halloc v i, hbound i⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hinj
    exact congrArg Fin.val hij
  have hfinite : (Set.range f).Finite := by
    apply Set.Finite.subset (Set.finite_univ (α := Fin (kmswStage w t).nextVertex))
    intro x hx
    exact Set.mem_univ x
  exact (Set.infinite_range_of_injective hfinj) hfinite

/-- The least-ID outgoing paths from any two vertices allocated before a strict
record coalesce at its finite-stage sink (`lem-uibot-bdy`,
identification with the geometric rightmost edge is NOT proved in this file, so
this gives the coalescence clause of `lem-uibot-bdy` only together with it. -/
theorem kmswM0RightmostPaths_coalesce_of_strict_record
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (q : ℕ) (hA : ∀ j < q, R w q ≤ R w j - 1) (hq : 0 < q)
    (x y : ℕ)
    (hx : x < (kmswStage w (q - 1)).nextVertex)
    (hy : y < (kmswStage w (q - 1)).nextVertex)
    (hxne : (⟨x⟩ : PresentVertex w) ≠ recordVertex w q)
    (hyne : (⟨y⟩ : PresentVertex w) ≠ recordVertex w q) :
    ∃ i j, 0 < i ∧ 0 < j ∧ ∀ t,
      ((kmswM0RightmostPath w hR halloc x).initial (i + t)).1.id =
        ((kmswM0RightmostPath w hR halloc y).initial (j + t)).1.id := by
  obtain ⟨i, hi⟩ := kmswM0RightmostOrbit_hits_strict_record_stage
    w hR halloc q hA hq x hx
  obtain ⟨j, hj⟩ := kmswM0RightmostOrbit_hits_strict_record_stage
    w hR halloc q hA hq y hy
  have hiPos : 0 < i := by
    by_contra hn
    have hi0 : i = 0 := by omega
    subst i
    apply hxne
    apply congrArg (fun id : ℕ => (⟨id⟩ : PresentVertex w))
    calc
      x = (kmswStage w (q - 1)).east (act w (q - 1)) := by
        simpa [kmswM0RightmostOrbit] using hi
      _ = (recordVertex w q).id := (recordVertex_id_eq_stage_sink w q hA hq).symm
  have hjPos : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    subst j
    apply hyne
    apply congrArg (fun id : ℕ => (⟨id⟩ : PresentVertex w))
    calc
      y = (kmswStage w (q - 1)).east (act w (q - 1)) := by
        simpa [kmswM0RightmostOrbit] using hj
      _ = (recordVertex w q).id := (recordVertex_id_eq_stage_sink w q hA hq).symm
  have hxy : ((kmswM0RightmostPath w hR halloc x).initial i).1.id =
      ((kmswM0RightmostPath w hR halloc y).initial j).1.id := by
    rw [kmswM0RightmostPath_initial_id, kmswM0RightmostPath_initial_id, hi, hj]
  exact ⟨i, j, hiPos, hjPos, kmswM0RightmostPath_coalesces_of_common_vertex
    w hR halloc x y i j hxy⟩

/-- Under unbounded descent, every pair of allocated limit least-ID outgoing
paths coalesces at a later strict record (`lem-uibot-bdy`,
identification with the geometric rightmost edge is NOT proved in this file, so
this gives the coalescence clause of `lem-uibot-bdy` only together with it. -/
theorem kmswM0RightmostPaths_coalesce_of_allocated
    (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (halloc : ∀ v, ∃ n, v < (kmswStage w n).nextVertex)
    (x y : ℕ)
    (hx : ∃ n, x < (kmswStage w n).nextVertex)
    (hy : ∃ n, y < (kmswStage w n).nextVertex) :
    ∃ i j, 0 < i ∧ 0 < j ∧ ∀ t,
      ((kmswM0RightmostPath w hR halloc x).initial (i + t)).1.id =
        ((kmswM0RightmostPath w hR halloc y).initial (j + t)).1.id := by
  classical
  obtain ⟨nx, hnx⟩ := hx
  obtain ⟨ny, hny⟩ := hy
  let N := max nx ny
  obtain ⟨q, hqrec, hqgt, hxne, hyne⟩ :=
    exists_strict_record_after_avoiding_two w hR N x y
  have hA : ∀ j < q, R w q ≤ R w j - 1 := by
    intro j hj
    have h := hqrec j hj
    omega
  have hqpos : 0 < q := by have := hqgt; dsimp [N] at this; omega
  have hnxq : nx ≤ q - 1 := by have := hqgt; dsimp [N] at this; omega
  have hnyq : ny ≤ q - 1 := by have := hqgt; dsimp [N] at this; omega
  have hxq : x < (kmswStage w (q - 1)).nextVertex :=
    hnx.trans_le (CutConverse.nextVertex_mono w hnxq)
  have hyq : y < (kmswStage w (q - 1)).nextVertex :=
    hny.trans_le (CutConverse.nextVertex_mono w hnyq)
  exact kmswM0RightmostPaths_coalesce_of_strict_record
    w hR halloc q hA hqpos x y hxq hyq hxne.symm hyne.symm

/-- Almost surely for iid codes, least-ID outgoing paths from every pair of
hit-indexed boundary vertices coalesce (`lem-uibot-bdy`,
here; its identification with the right end of the rotation-order outgoing
interval (the geometric rightmost edge of `lem-uibot-bdy`) is NOT proved in
this file (see `KMSW/RightmostBridge.lean`, if present).  Hence this proves
coalescence of least-ID outgoing paths; it gives the coalescence clause of
`lem-uibot-bdy` only together with that identification. -/
theorem iidCodes_ae_boundaryRightmostPaths_coalesce :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
          e < (kmswStage w n).nextEdge ∧
            ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        ∃ h : BoundaryHitWitnesses w,
          ∀ k k' : ℤ, ∃ i j, 0 < i ∧ 0 < j ∧ ∀ t,
            ((kmswM0RightmostPathOfFiniteIncidence w hfin h.R_unbounded_below
              (boundaryVertex w h k)).initial (i + t)).1.id =
            ((kmswM0RightmostPathOfFiniteIncidence w hfin h.R_unbounded_below
              (boundaryVertex w h k')).initial (j + t)).1.id := by
  filter_upwards [iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hfin hhit
  let w := fun i => ω (i + 1)
  have hfin' : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite := by
    intro v
    simpa [w] using hfin v
  have halloc := kmsw_vertex_allocated_of_finite_incidence w hfin'
  have hR := hhit.R_unbounded_below
  refine ⟨hfin', hhit, ?_⟩
  intro k k'
  simpa [kmswM0RightmostPathOfFiniteIncidence] using
    (kmswM0RightmostPaths_coalesce_of_allocated w hR halloc
      (boundaryVertex w hhit k) (boundaryVertex w hhit k')
      (boundaryVertex_allocated w hhit k) (boundaryVertex_allocated w hhit k'))

end DirectedDistances.KMSW
