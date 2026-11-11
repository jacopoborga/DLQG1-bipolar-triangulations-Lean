module

public import DirectedDistances.KMSW.PastTraceCanonicalGeodesic
public import DirectedDistances.KMSW.PastLeftmostPathInduction
public import DirectedDistances.PaperProofs.Section4.FirstHitPastLeftmostTrace
public import DirectedDistances.KMSW.StageLeftmostXDPIdentification
public import DirectedDistances.PlanarMap.LRCutRep
public import DirectedDistances.PlanarMap.LRGlueRepLen
public import DirectedDistances.PaperProofs.Section4.FirstHitXDPIdentification
import DirectedDistances.PlanarMap.LexLeftmostBaseIso

/-! of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap Quiver
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.RandomWalk MeasureTheory

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private noncomputable def cornerSelector (S : State)
    (σ : Equiv.Perm (StageDart S.nextEdge)) (root : StageDart S.nextEdge)
    (order : StageDart S.nextEdge → List ℕ) (v : ℕ) : Option ℕ := by
  classical
  exact if hc : ∃ d : StageDart S.nextEdge,
      (d = root ∨ d.2 = false ∧ (σ d).2 = true) ∧ stageEndpoint S d = v then
    (order hc.choose).head?
  else none

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
@[expose] noncomputable def stageSinkLeftmostXDPStep (w : ℕ → Fin 3) (n : ℕ)
    (x : XDP) (sink : StagePresentVertex w n) (v : ℕ) : Option ℕ := by
  classical
  exact if hc : ∃ d : StageDart (kmswStage w n).nextEdge,
      (d = stageULHeadDart w n ∨ d.2 = false ∧ (stageRot w n d).2 = true) ∧
        stageEndpoint (kmswStage w n) d = v then
    (stageEligibleOutgoingEdgeOrder w n x ⟨0⟩ sink hc.choose).head?
  else none

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
@[expose] noncomputable def stageSinkLeftmostXDPTrace (w : ℕ → Fin 3) (n : ℕ)
    (x : XDP) (sink : StagePresentVertex w n) :
    ℕ → Option (ℕ × List (StageDart (kmswStage w n).nextEdge))
  | 0 => some (0, [])
  | k + 1 => (stageSinkLeftmostXDPTrace w n x sink k).bind fun z =>
      (stageSinkLeftmostXDPStep w n x sink z.1).bind fun e =>
        if he : e < (kmswStage w n).nextEdge then
          some ((kmswStage w n).east e, z.2 ++ [(⟨e, he⟩, false)])
        else none

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private def stageDartCast {S T : State} (h : S = T) :
    StageDart S.nextEdge ≃ StageDart T.nextEdge :=
  Equiv.prodCongr (finCongr (congrArg State.nextEdge h)) (Equiv.refl Bool)

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem cornerSelector_congr {S T : State} (h : S = T)
    (σ : Equiv.Perm (StageDart S.nextEdge)) (τ : Equiv.Perm (StageDart T.nextEdge))
    (a : StageDart S.nextEdge) (b : StageDart T.nextEdge)
    (f : StageDart S.nextEdge → List ℕ) (g : StageDart T.nextEdge → List ℕ)
    (hr : ∀ d, stageDartCast h (σ d) = τ (stageDartCast h d))
    (ha : stageDartCast h a = b) (hf : ∀ d, f d = g (stageDartCast h d)) (v : ℕ) :
    cornerSelector S σ a f v = cornerSelector T τ b g v := by
  cases h
  have hrot : σ = τ := Equiv.ext hr
  have hord : f = g := funext hf
  have hroot : a = b := ha
  subst τ
  subst g
  subst b
  rfl

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPStep_eq_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (x : XDP) (sink v : ℕ) :
    stageSinkLeftmostXDPStep w n x ⟨sink⟩ v =
      stageSinkLeftmostXDPStep w' n x ⟨sink⟩ v := by
  let hs := kmswStage_eq_of_prefix w w' n h
  let I := kmswStageDirectedMapIsoOfPrefix w w' n h
  have hI (d : StageDart (kmswStage w n).nextEdge) :
      I.toEquiv d = stageDartCast hs d := by
    apply Prod.ext
    · exact Fin.ext (kmswStageDirectedMapIsoOfPrefix_val w w' n h d).1
    · exact (kmswStageDirectedMapIsoOfPrefix_val w w' n h d).2
  change cornerSelector _ _ _ _ _ = cornerSelector _ _ _ _ _
  apply cornerSelector_congr hs (stageRot w n) (stageRot w' n)
    (stageULHeadDart w n) (stageULHeadDart w' n)
    (stageEligibleOutgoingEdgeOrder w n x ⟨0⟩ ⟨sink⟩)
    (stageEligibleOutgoingEdgeOrder w' n x ⟨0⟩ ⟨sink⟩)
  · intro d
    rw [← hI, ← hI]
    exact I.rot_comm d
  · simp [stageDartCast, stageULHeadDart, hs]
  · intro d
    rw [← hI]
    exact stageEligibleOutgoingEdgeOrder_eq_of_prefix w w' n h x 0 sink d

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private noncomputable def dartTrace (S : State) (step : ℕ → Option ℕ) :
    ℕ → Option (ℕ × List (StageDart S.nextEdge))
  | 0 => some (0, [])
  | k + 1 => (dartTrace S step k).bind fun z =>
      (step z.1).bind fun e =>
        if he : e < S.nextEdge then
          some (S.east e, z.2 ++ [(⟨e, he⟩, false)])
        else none

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem dartTrace_congr {S T : State} (h : S = T)
    (f g : ℕ → Option ℕ) (hf : ∀ v, f v = g v) (k : ℕ) :
    (dartTrace S f k).map (fun z => (z.1, z.2.map (stageDartCast h))) =
      dartTrace T g k := by
  cases h
  have heq : f = g := funext hf
  subst g
  have hid : (fun z : ℕ × List (StageDart S.nextEdge) =>
      (z.1, z.2.map (stageDartCast (rfl : S = S)))) = id := by
    funext z
    simp [stageDartCast]
  rw [hid, Option.map_id]
  rfl

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPTrace_eq_of_prefix (w w' : ℕ → Fin 3) (n : ℕ)
    (h : ∀ i < n, w i = w' i) (x : XDP) (sink k : ℕ) :
    (stageSinkLeftmostXDPTrace w n x ⟨sink⟩ k).map
        (fun z => (z.1, z.2.map (kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv)) =
      stageSinkLeftmostXDPTrace w' n x ⟨sink⟩ k := by
  have hs := kmswStage_eq_of_prefix w w' n h
  have hI : (kmswStageDirectedMapIsoOfPrefix w w' n h).toEquiv =
      stageDartCast hs := by
    apply Equiv.ext
    intro d
    apply Prod.ext
    · exact Fin.ext (kmswStageDirectedMapIsoOfPrefix_val w w' n h d).1
    · exact (kmswStageDirectedMapIsoOfPrefix_val w w' n h d).2
  rw [hI]
  have heq (u : ℕ → Fin 3) : stageSinkLeftmostXDPTrace u n x ⟨sink⟩ k =
      dartTrace (kmswStage u n) (stageSinkLeftmostXDPStep u n x ⟨sink⟩) k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [stageSinkLeftmostXDPTrace, dartTrace, ih]
  rw [heq w, heq w']
  exact dartTrace_congr hs _ _
    (stageSinkLeftmostXDPStep_eq_of_prefix w w' n h x sink) k

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPTrace_record (w : ℕ → Fin 3) (t : ℕ) (x : XDP)
    (k : ℕ) :
    stageSinkLeftmostXDPTrace w (t - 1) x ⟨(recordVertex w t).id⟩ k =
      pastStageLeftmostXDPTrace w t x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [stageSinkLeftmostXDPTrace, pastStageLeftmostXDPTrace, ih]
    rfl

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem firstHit_stageSinkLeftmostXDPTrace_eq_past (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r) (x : XDP) (k : ℕ) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    stageSinkLeftmostXDPTrace w (t - 1) x
        ⟨(kmswStage w (t - 1)).east (kmswStage w (t - 1)).active⟩ k =
      pastStageLeftmostXDPTrace w t x k := by
  dsimp only
  rw [← (firstHitPast_sink_eq_record_and_strict r hr ω hE).1]
  exact stageSinkLeftmostXDPTrace_record _ _ x k

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPTrace_stoppedWord (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r)
    {ℓ : ℕ} (c : KMSWWalkClass ℓ r (boltzmannTau r ω))
    (hc : c.val = stoppedWord r ω) (x : XDP) (k : ℕ) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    (stageSinkLeftmostXDPTrace (codeExtend c) (t - 1) x
        ⟨(kmswStage (codeExtend c) (t - 1)).east
          (kmswStage (codeExtend c) (t - 1)).active⟩ k).map
        (fun z => (z.1, z.2.map
          (kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1)
            (fun i hi => (codeExtend_of_lt c i hi).trans
              (congrFun hc ⟨i, hi⟩))).toEquiv)) =
      pastStageLeftmostXDPTrace w t x k := by
  dsimp only
  have hp : ∀ i < boltzmannTau r ω - 1,
      codeExtend c i = boltzmannKMSWStream ω i :=
    fun i hi => (codeExtend_of_lt c i hi).trans (congrFun hc ⟨i, hi⟩)
  have hs := kmswStage_eq_of_prefix (codeExtend c) (boltzmannKMSWStream ω)
    (boltzmannTau r ω - 1) hp
  rw [stageSinkLeftmostXDPTrace_eq_of_prefix]
  have he : (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).east
      (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).active =
      (kmswStage (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)).east
        (kmswStage (boltzmannKMSWStream ω) (boltzmannTau r ω - 1)).active := by
    rw [hs]
  rw [he]
  exact firstHit_stageSinkLeftmostXDPTrace_eq_past r hr ω hE x k

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem cutLRHead (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).LR.head? = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).LR.head? = _
    cases kmswCodeStep (w n) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w n).LR ++ [(kmswStage w n).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w n)] using ih

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem cutLabels {ℓ r n : ℕ} (hn : 1 ≤ n)
    (c : KMSWWalkClass ℓ r n) :
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).source = ⟨0⟩ ∧
    stageMapVertex (codeExtend c) (n - 1) (kmswWalkClassBase hn c).sink =
      ⟨(kmswStage (codeExtend c) (n - 1)).east
        (kmswStage (codeExtend c) (n - 1)).active⟩ := by
  let w := codeExtend c
  let m := n - 1
  let s := kmswStage w m
  have hf := kmswWalkClassMap_mem_sourceClass hn c
  dsimp only at hf
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hUR, hLL,
    _, _, _, _, _⟩
  constructor
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    change s.west (s.UL.head _) = 0
    have hs := (kmswStage_boundary_chain_invariant w m).2.2.1
    have hUL := (kmswStage_UL_nonempty_active_last w m).1
    have h0 := (initial_edge_endpoints w m).1
    change boundaryStart s (s.UL ++ s.UR) = boundaryStart s (s.LL ++ s.LR) at hs
    have hURs : s.UR = [] := hUR
    have hLLs : s.LL = [] := hLL
    rw [hURs, hLLs, List.append_nil, List.nil_append] at hs
    have huhead : s.UL.head? = some (s.UL.head hUL) := List.head?_eq_some_head hUL
    have hrhead : s.LR.head? = some 0 := cutLRHead w m
    change s.UL.head?.map s.west = s.LR.head?.map s.west at hs
    rw [huhead, hrhead] at hs
    exact (Option.some.inj hs).trans h0
  · apply congrArg (StagePresentVertex.mk (w := w) (n := m))
    have hLR := kmswStage_LR_nonempty w m
    have ha := (kmswStage_boundary_chain_invariant w m).2.2.2.2.2.2 hLR hUR
    rw [ha]
    change stageEndpoint s ((kmswStageLRDartRun w m).head _) = _
    simp only [kmswStageLRDartRun, stageDarts, List.head_map, List.head_attach,
      stageEndpoint, List.head_reverse, ↓reduceIte]
    rfl

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem cutCorner_unique {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N)
    (v : MapVertex (kmswWalkClassBase hN c).map)
    (hvs : v ≠ (kmswWalkClassBase hN c).sink)
    (d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge)
    (hd : d = stageULHeadDart (codeExtend c) (N - 1) ∨
      d.2 = false ∧ (stageRot (codeExtend c) (N - 1) d).2 = true)
    (hv : stageEndpoint (kmswStage (codeExtend c) (N - 1)) d =
      (stageMapVertex (codeExtend c) (N - 1) v).id) :
    d = leftmostOutgoing (kmswWalkClassBase hN c) v hvs := by
  let B := kmswWalkClassBase hN c
  have htail : dartTailVertex B.map d = v := by
    apply stageMapVertex_injective (codeExtend c) (N - 1)
    exact congrArg StagePresentVertex.mk hv
  rcases hd with hd | hd
  · subst d
    have hsource : v = B.source := htail.symm
    subst v
    exact (stage_leftmostOutgoing_source hN c).symm
  · by_cases hs : v = B.source
    · have hep : stageEndpoint (kmswStage (codeExtend c) (N - 1))
          (stageRot (codeExtend c) (N - 1) d) =
          stageEndpoint (kmswStage (codeExtend c) (N - 1)) d :=
        ((stageRot_sameCycle_iff_endpoint_eq (codeExtend c) (N - 1) _ _).1
          (Equiv.Perm.SameCycle.refl _ d).apply_left)
      have hrot : dartTailVertex B.map (stageRot (codeExtend c) (N - 1) d) =
          B.source := by
        apply stageMapVertex_injective (codeExtend c) (N - 1)
        exact congrArg StagePresentVertex.mk
          (hep.trans (hv.trans (congrArg
            (fun z => (stageMapVertex (codeExtend c) (N - 1) z).id) hs)))
      have ho := tail_of_dartTailVertex_eq_source B _ hrot
      have hb : (stageRot (codeExtend c) (N - 1) d).2 = false := ho.2
      rw [hd.2] at hb
      contradiction
    · exact (stage_leftmostOutgoing_internal_iff hN c v hs hvs d).2 ⟨hv, hd⟩

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPStep_eq_canonical {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP)
    (v : MapVertex (kmswWalkClassBase hN c).map)
    (hv : ∃ k, ∃ P : SimpleDirectedDartPath (kmswWalkClassBase hN c).map
      (kmswWalkClassBase hN c).source (kmswWalkClassBase hN c).sink k,
      IsXDPGeodesicBase (kmswWalkClassBase hN c) x P ∧ v ∈ P.vertices)
    (hvs : v ≠ (kmswWalkClassBase hN c).sink) :
    stageSinkLeftmostXDPStep (codeExtend c) (N - 1) x
        ⟨(kmswStage (codeExtend c) (N - 1)).east
          (kmswStage (codeExtend c) (N - 1)).active⟩
        (stageMapVertex (codeExtend c) (N - 1) v).id =
      some (canonicalLeftmostXDPStep (kmswWalkClassBase hN c) x v).1.val := by
  classical
  let B := kmswWalkClassBase hN c
  have hc : ∃ d : StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge,
      (d = stageULHeadDart (codeExtend c) (N - 1) ∨
        d.2 = false ∧ (stageRot (codeExtend c) (N - 1) d).2 = true) ∧
        stageEndpoint (kmswStage (codeExtend c) (N - 1)) d =
          (stageMapVertex (codeExtend c) (N - 1) v).id := by
    refine ⟨leftmostOutgoing B v hvs, ?_, ?_⟩
    · by_cases hs : v = B.source
      · subst v
        exact Or.inl (stage_leftmostOutgoing_source hN c)
      · exact Or.inr ((stage_leftmostOutgoing_internal_iff hN c v hs hvs _).1 rfl).2
    · exact congrArg (fun z => (stageMapVertex (codeExtend c) (N - 1) z).id)
        (canonicalLeftmostOutgoing_spec B v hvs).1
  unfold stageSinkLeftmostXDPStep
  rw [dite_eq_left hc]
  rw [cutCorner_unique hN c v hvs hc.choose hc.choose_spec.1 hc.choose_spec.2]
  obtain ⟨rest, he⟩ := stage_canonicalLeftmostXDPStep_first hN c x v hv hvs
  rw [he]
  rfl

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
private theorem cutCanonicalTrace {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP) :
    let B := kmswWalkClassBase hN c
    let P := Classical.choose (exists_canonicalLeftmost_XDPGeodesic_path B x)
    stageSinkLeftmostXDPTrace (codeExtend c) (N - 1) x
        ⟨(kmswStage (codeExtend c) (N - 1)).east
          (kmswStage (codeExtend c) (N - 1)).active⟩ (xdpLengthBase B x) =
      some ((kmswStage (codeExtend c) (N - 1)).east
        (kmswStage (codeExtend c) (N - 1)).active, P.darts) := by
  classical
  let B := kmswWalkClassBase hN c
  let P := Classical.choose (exists_canonicalLeftmost_XDPGeodesic_path B x)
  let sel := canonicalLeftmostXDPStep B x
  have hsel : ∀ v, (∃ m, ∃ Q : SimpleDirectedDartPath B.map B.source B.sink m,
      IsXDPGeodesicBase B x Q ∧ v ∈ Q.vertices) → v ≠ B.sink →
      dartTailVertex B.map (sel v) = v ∧ IsXDPGeodesicDart B x (sel v) :=
    fun v hv hvs => canonicalLeftmostXDPStep_spec B x v hv hvs
  have hP := Classical.choose_spec (exists_canonicalLeftmost_XDPGeodesic_path B x)
  have htrace : ∀ k, k ≤ xdpLengthBase B x →
      stageSinkLeftmostXDPTrace (codeExtend c) (N - 1) x
          ⟨(kmswStage (codeExtend c) (N - 1)).east
            (kmswStage (codeExtend c) (N - 1)).active⟩ k =
        some ((stageMapVertex (codeExtend c) (N - 1) (selectorVertex B sel k)).id,
          P.darts.take k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 := congrArg StagePresentVertex.id (cutLabels hN c).1
      change some (0, []) = some
        ((stageMapVertex (codeExtend c) (N - 1) B.source).id, [])
      rw [h0]
    | succ k ih =>
      intro hk
      have hkl : k < xdpLengthBase B x := by omega
      have hv := selectorVertex_mem_XDPGeodesic B x sel hsel k
      have hvs := selectorVertex_ne_sink_of_lt_length B x sel hsel k hkl
      have hs := stageSinkLeftmostXDPStep_eq_canonical hN c x _ hv hvs
      let d := sel (selectorVertex B sel k)
      have ht := (IsXDPGeodesicDart.present_tail B x d (hsel _ hv hvs).2).2
      have hb : d.2 = false := ht.2
      have hd : P.darts[k]'(by rw [P.darts_length]; exact hkl) = d := hP.2.1 ⟨k, hkl⟩
      have hnext : (kmswStage (codeExtend c) (N - 1)).east d.1.val =
          (stageMapVertex (codeExtend c) (N - 1) (selectorVertex B sel (k + 1))).id := by
        rw [selectorVertex_succ, selectorStep, ite_eq_right hvs]
        change _ = stageEndpoint (kmswStage (codeExtend c) (N - 1))
          (edgeFlip (kmswStage (codeExtend c) (N - 1)).nextEdge d)
        change _ = if !d.2 then
          (kmswStage (codeExtend c) (N - 1)).east d.1.val else
          (kmswStage (codeExtend c) (N - 1)).west d.1.val
        rw [hb]
        rfl
      have hdd : ((⟨d.1.val, d.1.isLt⟩, false) :
          StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge) = d :=
        Prod.ext rfl hb.symm
      simp only [stageSinkLeftmostXDPTrace, ih (by omega), Option.bind_some, hs]
      change (if he : d.1.val < (kmswStage (codeExtend c) (N - 1)).nextEdge then
        some ((kmswStage (codeExtend c) (N - 1)).east d.1.val,
          P.darts.take k ++ [(⟨d.1.val, he⟩, false)]) else none) = _
      rw [dite_eq_left d.1.isLt, hdd, hnext]
      rw [List.take_succ_eq_append_getElem
        (by rw [P.darts_length]; exact hkl), hd]
  have hfull := htrace (xdpLengthBase B x) le_rfl
  rw [selectorVertex_eq_sink_at_length B x sel hsel] at hfull
  rw [cutLabels hN c |>.2] at hfull
  simpa only [List.take_of_length_le (le_of_eq P.darts_length)] using hfull

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPTrace_isLexLeftmost {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP) :
    ∃ P : SimpleDirectedDartPath (kmswWalkClassRep hN c).B.map
        (kmswWalkClassRep hN c).B.source (kmswWalkClassRep hN c).B.sink
        (xdpLengthBase (kmswWalkClassRep hN c).B x),
      IsLexLeftmostXDPGeodesic (kmswWalkClassRep hN c).B x P ∧
        stageSinkLeftmostXDPTrace (codeExtend c) (N - 1) x
            ⟨(kmswStage (codeExtend c) (N - 1)).east
              (kmswStage (codeExtend c) (N - 1)).active⟩
            (xdpLengthBase (kmswWalkClassRep hN c).B x) =
          some ((kmswStage (codeExtend c) (N - 1)).east
            (kmswStage (codeExtend c) (N - 1)).active,
            P.darts.map (kmswWalkClassRep_mapIso hN c).toEquiv) := by
  classical
  let B := kmswWalkClassBase hN c
  let R := (kmswWalkClassRep hN c).B
  let P := Classical.choose (exists_canonicalLeftmost_XDPGeodesic_path R x)
  let Q := Classical.choose (exists_canonicalLeftmost_XDPGeodesic_path B x)
  have hP : IsLexLeftmostXDPGeodesic R x P := canonical_isLexLeftmostXDPGeodesic R x
  have hQ : IsLexLeftmostXDPGeodesic B x Q := canonical_isLexLeftmostXDPGeodesic B x
  let I : BipolarBoundaryBaseIso R B :=
    (B.transportIso (Fintype.equivFin
      (StageDart (kmswStage (codeExtend c) (N - 1)).nextEdge))).symm
  have hmap : Q.darts = P.darts.map (kmswWalkClassRep_mapIso hN c).toEquiv :=
    dartLists_eq_of_isLexLeftmostXDPGeodesic_baseIso I x P Q hP hQ
  have hlen : xdpLengthBase R x = xdpLengthBase B x := by
    have hh := congrArg List.length hmap
    simpa only [List.length_map, P.darts_length, Q.darts_length] using hh.symm
  refine ⟨P, hP, ?_⟩
  change stageSinkLeftmostXDPTrace _ _ _ _ (xdpLengthBase R x) = _
  conv_lhs => rw [hlen]
  rw [cutCanonicalTrace hN c x]
  change some (_, Q.darts) = _
  rw [hmap]

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stageSinkLeftmostXDPTrace_eq_selected {ℓ r N : ℕ} (hN : 1 ≤ N)
    (c : KMSWWalkClass ℓ r N) (x : XDP) :
    stageSinkLeftmostXDPTrace (codeExtend c) (N - 1) x
        ⟨(kmswStage (codeExtend c) (N - 1)).east
          (kmswStage (codeExtend c) (N - 1)).active⟩
        (xdpLengthBase (kmswWalkClassRep hN c).B x) =
      some ((kmswStage (codeExtend c) (N - 1)).east
        (kmswStage (codeExtend c) (N - 1)).active,
        (selectedGeodesicOfLen (kmswWalkClassRep hN c).B x rfl).darts.map
          (kmswWalkClassRep_mapIso hN c).toEquiv) := by
  obtain ⟨P, hP, ht⟩ := stageSinkLeftmostXDPTrace_isLexLeftmost hN c x
  have heq := dartLists_eq_of_isLexLeftmostXDPGeodesic (kmswWalkClassRep hN c).B x
    P (selectedGeodesicOfLen (kmswWalkClassRep hN c).B x rfl) hP
    (selectedGeodesicOfLen_isLexLeftmost (kmswWalkClassRep hN c).B x rfl)
  rwa [heq] at ht

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem stoppedSelectedGeodesic_trace (r : ℕ) (hr : 1 ≤ r)
    (ω : ℕ → Fin 3) (hE : ω ∈ boltzmannEvent r)
    {ℓ : ℕ} (hN : 1 ≤ boltzmannTau r ω)
    (c : KMSWWalkClass ℓ r (boltzmannTau r ω))
    (hc : c.val = stoppedWord r ω) (x : XDP) :
    let t := boltzmannTau r ω
    let w := boltzmannKMSWStream ω
    pastStageLeftmostXDPTrace w t x (xdpLengthBase (kmswWalkClassRep hN c).B x) =
      some ((recordVertex w t).id,
        ((selectedGeodesicOfLen (kmswWalkClassRep hN c).B x rfl).darts.map
          (kmswWalkClassRep_mapIso hN c).toEquiv).map
            (kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1)
              (fun i hi => (codeExtend_of_lt c i hi).trans
                (congrFun hc ⟨i, hi⟩))).toEquiv) := by
  dsimp only
  have ht := stageSinkLeftmostXDPTrace_stoppedWord r hr ω hE c hc x
    (xdpLengthBase (kmswWalkClassRep hN c).B x)
  dsimp only at ht
  rw [stageSinkLeftmostXDPTrace_eq_selected hN c x] at ht
  have hs := stoppedStage_eq_of_stoppedWord_eq r ω c hc
  have he : (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).east
      (kmswStage (codeExtend c) (boltzmannTau r ω - 1)).active =
      (recordVertex (boltzmannKMSWStream ω) (boltzmannTau r ω)).id := by
    rw [hs]
    exact (firstHitPast_sink_eq_record_and_strict r hr ω hE).1.symm
  simp only [Option.map_some, he] at ht
  exact ht.symm

/-- of the stopped KMSW map representative is the past-stage leftmost trace, hence the
past portion of the infinite leftmost geodesic; T_m, F4c and both-mode scope are not treated;
not the paper result. -/
theorem firstHit_selectedCutPath_eq_prefix_ae (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      let t := boltzmannTau r (pathCode p)
      let w := boltzmannKMSWStream (pathCode p)
      ∃ (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
        (hL : ∀ j, 0 ≤ L w j)
        (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
        (hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
        (hgL : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments)
        (hgS : ∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments)
        (hN : 1 ≤ t) (c : KMSWWalkClass (L w t).toNat r t)
        (hc : c.val = stoppedWord r (pathCode p)),
        (∀ j ≥ t, (p t).1 ≤ (p j).1) → ∀ x : XDP,
          let P := match x with
            | .ldp => kmswLeftmostLdpPath w hfin hL htrans hR 0 hgL
            | .sdp => kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
          ∃ i, (P.initial i).1 = recordVertex w t ∧
            (∀ j < i, (P.initial j).1 ≠ recordVertex w t) ∧
            ((selectedGeodesicOfLen (kmswWalkClassRep hN c).B x rfl).darts.map
              (kmswWalkClassRep_mapIso hN c).toEquiv).map
                (fun d => ((kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1)
                  (fun k hk => (codeExtend_of_lt c k hk).trans
                    (congrFun hc ⟨k, hk⟩))).toEquiv d).1.val) =
              pathEdgeList (P.initial i).2 := by
  classical
  filter_upwards [conditionedVectorPathLaw_ae_legal,
    firstHitPastMap_finite_hit_ae r hr, firstHit_past_leftmost_trace_ae r hr]
    with p hp hhit htrace
  dsimp only at htrace ⊢
  have hconv := firstHit_stoppedCode_conventions r p hp.1 hp.2 hhit
  have htime := hconv.2.2.1
  rw [← htime] at htrace
  let t := boltzmannTau r (pathCode p)
  let w := boltzmannKMSWStream (pathCode p)
  obtain ⟨hfin, hL, htrans, hR, hgL, hgS, htrace⟩ := htrace
  have hw : codeWalk (pathCode p) = p := by
    funext n
    rw [codeWalk_pathCode p hp.2 n, hp.1]
    exact sub_zero _
  have hh : ∃ n, (p n).2 = -(r : ℤ) := by
    by_contra hn
    simp only [conditionedSecondCoordinateFirstHit, dite_eq_right hn,
      lt_self_iff_false] at hhit
  have hE : pathCode p ∈ boltzmannEvent r := by
    obtain ⟨n, hn⟩ := hh
    refine ⟨n, by rwa [hw], ?_⟩
    intro j _
    rw [hw]
    have hj := hL j
    rwa [kmsw_L_eq, hconv.2.1] at hj
  have hN : 1 ≤ t := (boltzmann_boundary_observable r hr (pathCode p) hE).1
  let c : KMSWWalkClass (L w t).toNat r t :=
    ⟨stoppedWord r (pathCode p), (stoppedWord_admissible r hr (pathCode p) hE).1⟩
  let j : StoppedWalkIndex r := ⟨t, ⟨(L w t).toNat, c⟩⟩
  have hidx : stoppedIndex r hr (pathCode p) = some j := by
    simp only [stoppedIndex, dite_eq_left hE, j, t, w, c]
  have hmap : stoppedMap r hr (pathCode p) = some (stoppedWalkMap ⟨j, hN⟩) := by
    rw [stoppedMap, hidx]
    change stoppedWalkMapOption r j = _
    exact dite_eq_left (show 1 ≤ j.1 from hN)
  have hlen (x : XDP) : firstHitPastXdpLength x r (stoppedMap r hr (pathCode p)) =
      xdpLengthBase (kmswWalkClassRep hN c).B x := by
    rw [hmap]
    rfl
  refine ⟨hfin, hL, htrans, hR, hgL, hgS, hN, c, rfl, ?_⟩
  intro hbar x
  obtain ⟨_, hldp, hsdp⟩ := htrace hbar
  cases x with
  | ldp =>
    let P := kmswLeftmostLdpPath w hfin hL htrans hR 0 hgL
    obtain ⟨i, ds, hi, hfirst, _, _, ht, hids, hpl, _, _⟩ := hldp
    have hil : i = xdpLengthBase (kmswWalkClassRep hN c).B .ldp := by
      rw [← P.prefix_length i]
      exact hpl.trans (hlen .ldp)
    have hsel := stoppedSelectedGeodesic_trace r hr (pathCode p) hE hN c rfl .ldp
    dsimp only at hsel
    conv_lhs at hsel => rw [← hil]
    rw [ht] at hsel
    have hds := congrArg Prod.snd (Option.some.inj hsel)
    refine ⟨i, hi, hfirst, ?_⟩
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun d => d.1.val)) hds).symm.trans hids
  | sdp =>
    let P := kmswLeftmostSdpPath w hfin hL htrans hR 0 hgS
    obtain ⟨i, ds, hi, hfirst, _, _, ht, hids, hpl, _, _⟩ := hsdp
    have hil : i = xdpLengthBase (kmswWalkClassRep hN c).B .sdp := by
      rw [← P.prefix_length i]
      exact hpl.trans (hlen .sdp)
    have hsel := stoppedSelectedGeodesic_trace r hr (pathCode p) hE hN c rfl .sdp
    dsimp only at hsel
    conv_lhs at hsel => rw [← hil]
    rw [ht] at hsel
    have hds := congrArg Prod.snd (Option.some.inj hsel)
    refine ⟨i, hi, hfirst, ?_⟩
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun d => d.1.val)) hds).symm.trans hids

end DirectedDistances.KMSW
