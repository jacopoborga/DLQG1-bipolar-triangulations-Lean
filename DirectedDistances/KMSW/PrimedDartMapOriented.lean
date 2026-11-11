module

public import DirectedDistances.KMSW.PrimedInducedRotation
public import DirectedDistances.KMSW.PrimedInducedEmbedding
public import DirectedDistances.KMSW.PrimedSimAll
public import DirectedDistances.PlanarMap.BipolarBoundaryData

/-! P2 helper toward lem-quad-kmsw; not counted
Geometric endpoint diagnostics and orientation of primed dart images. -/

public section
namespace DirectedDistances.KMSW

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedAllEdgeMap_one_edges (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    let s := kmswStage w (walkNL w h 0 - 1)
    primedAllEdgeMap w h 1 0 = s.nextEdge + 1 ∧
    primedAllEdgeMap w h 1 1 = s.nextEdge ∧
    primedAllEdgeMap w h 1 2 = s.active := by
  exact ⟨rfl, rfl, rfl⟩

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedLocal_one_endpoints (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) 1
    sh.west 0 = 0 ∧ sh.east 0 = 1 ∧
    sh.west 1 = 0 ∧ sh.east 1 = 2 ∧
    sh.west 2 = 2 ∧ sh.east 2 = 1 := by
  have hu := primedCode_zero (primedSimInput w) h
  simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
    kmswMissingRootInit, kmswInit, State.addEdge]

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedAllVertexMap_one_endpoints (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) 1
    let s := kmswStage w (walkNL w h 0 - 1)
    primedAllVertexMap w h 1 (sh.west 0) = s.nextVertex ∧
    primedAllVertexMap w h 1 (sh.east 0) = s.west s.active ∧
    primedAllVertexMap w h 1 (sh.west 1) = s.nextVertex ∧
    primedAllVertexMap w h 1 (sh.east 1) = s.east s.active ∧
    primedAllVertexMap w h 1 (sh.west 2) = s.east s.active ∧
    primedAllVertexMap w h 1 (sh.east 2) = s.west s.active := by
  obtain ⟨h0w, h0e, h1w, h1e, h2w, h2e⟩ := primedLocal_one_endpoints w h
  dsimp only
  rw [h0w, h0e, h1w, h1e, h2w, h2e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedGlobal_one_endpoints (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    let s := kmswStage w (walkNL w h 0 - 1)
    let gl := kmswStage w (primedStageTime w h 1)
    gl.west (primedAllEdgeMap w h 1 0) = s.nextVertex ∧
    gl.east (primedAllEdgeMap w h 1 0) = s.west s.active ∧
    gl.west (primedAllEdgeMap w h 1 1) = s.nextVertex ∧
    gl.east (primedAllEdgeMap w h 1 1) = s.east s.active ∧
    gl.west (primedAllEdgeMap w h 1 2) = s.west s.active ∧
    gl.east (primedAllEdgeMap w h 1 2) = s.east s.active := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have ht : primedStageTime w h 1 = n := by
    simpa only [primedIntervalBase_zero, zero_add] using primedStageTime_after_crossing w h 0
  have hg : kmswStage w n = kmswStepOfStep s .left := primedInitial_globalExitTransition w h
  have hd : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  dsimp only
  rw [(primedAllEdgeMap_one_edges w h).1, (primedAllEdgeMap_one_edges w h).2.1,
    (primedAllEdgeMap_one_edges w h).2.2, ht, hg]
  simp only [show kmswStage w (walkNL w h 0 - 1) = s from rfl]
  simp [kmswStepOfStep, hd, State.addEdge, show s.active ≠ s.nextEdge by omega,
    show s.active ≠ s.nextEdge + 1 by omega]

/-- P2 helper toward lem-quad-kmsw; not counted
endpoint pair, with multiplicities, including all missing geometric edges. -/
theorem primedAll_endpoint_pair (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
    let gl := kmswStage w (primedStageTime w h m)
    ({gl.west (primedAllEdgeMap w h m e.val),
      gl.east (primedAllEdgeMap w h m e.val)} : Multiset ℕ) =
    {primedAllVertexMap w h m (sh.west e.val),
      primedAllVertexMap w h m (sh.east e.val)} := by
  cases hp : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e.val with
  | false =>
    cases m with
    | zero => exact (primedAll_sim_zero w h).1.missing_incidence _ e.isLt hp
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.missing_incidence _ e.isLt hp
  | true =>
    have hi :
        (kmswStage w (primedStageTime w h m)).west (primedAllEdgeMap w h m e.val) =
          primedAllVertexMap w h m
            ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).west e.val) ∧
        (kmswStage w (primedStageTime w h m)).east (primedAllEdgeMap w h m e.val) =
          primedAllVertexMap w h m
            ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).east e.val) := by
      cases m with
      | zero => exact (primedAll_sim_zero w h).1.present_incidence _ e.isLt hp
      | succ m =>
        obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
        exact hs.present_incidence _ e.isLt hp
    dsimp only
    rw [hi.1, hi.2]

/-- P2 helper toward lem-quad-kmsw; not counted
endpoint orders (the alternatives can coincide only for a loop). -/
theorem primedAll_endpoint_orders (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    let sh := kmswMissingRootStage (primedCode (primedSimInput w) h) m
    let gl := kmswStage w (primedStageTime w h m)
    let a := primedAllVertexMap w h m (sh.west e.val)
    let b := primedAllVertexMap w h m (sh.east e.val)
    (gl.west (primedAllEdgeMap w h m e.val) = a ∧
      gl.east (primedAllEdgeMap w h m e.val) = b) ∨
    (gl.west (primedAllEdgeMap w h m e.val) = b ∧
      gl.east (primedAllEdgeMap w h m e.val) = a) := by
  apply Set.pair_eq_pair_iff.mp
  ext v
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] using
      Iff.of_eq (congrArg (fun t : Multiset ℕ => v ∈ t) (primedAll_endpoint_pair w h m e))

/-- P2 helper toward lem-quad-kmsw; not counted
its local west vertex does not map to the global west vertex. -/
@[expose] noncomputable def primedSideFlip (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) : Bool :=
  decide (primedAllVertexMap w h m
      ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).west e.val) ≠
    (kmswStage w (primedStageTime w h m)).west (primedAllEdgeMap w h m e.val))

/-- P2 helper toward lem-quad-kmsw; not counted -/
@[expose] noncomputable def primedDartMapOriented
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    StageDart (kmswStage w (primedStageTime w h m)).nextEdge :=
  ((primedDartMap w h m d).1, d.2 ^^ primedSideFlip w h m d.1)

/-- P2 helper toward lem-quad-kmsw; not counted
vertex, including darts of missing edges. -/
theorem primedDartMapOriented_endpoint (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    stageEndpoint (kmswStage w (primedStageTime w h m)) (primedDartMapOriented w h m d) =
      primedAllVertexMap w h m
        (stageEndpoint (kmswMissingRootStage (primedCode (primedSimInput w) h) m) d) := by
  rcases primedAll_endpoint_orders w h m d.1 with hi | hi
  · have hf : primedSideFlip w h m d.1 = false := by
      simp only [primedSideFlip, hi.1, ne_eq, not_true_eq_false, decide_false]
    cases hb : d.2 <;>
      simp only [stageEndpoint, primedDartMapOriented, primedDartMap, hf, hb,
        Bool.xor_false, Bool.false_eq_true, ↓reduceIte, hi.1, hi.2]
  · by_cases hw : primedAllVertexMap w h m
        ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).west d.1.val) =
        (kmswStage w (primedStageTime w h m)).west (primedAllEdgeMap w h m d.1.val)
    · have hf : primedSideFlip w h m d.1 = false := by simp [primedSideFlip, hw]
      have he := hi.1.symm.trans hw.symm
      cases hb : d.2 <;>
        simp only [stageEndpoint, primedDartMapOriented, primedDartMap, hf, hb,
          Bool.xor_false, Bool.false_eq_true, ↓reduceIte, hi.1, hi.2]
      · exact he
      · exact he.symm
    · have hf : primedSideFlip w h m d.1 = true := by simp [primedSideFlip, hw]
      cases hb : d.2 <;>
        simp only [stageEndpoint, primedDartMapOriented, primedDartMap, hf, hb,
          Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          hi.1, hi.2]

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedDartMapOriented_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    Function.Injective (primedDartMapOriented w h m) := by
  intro d e hh
  have he : (d.1, d.2 ^^ primedSideFlip w h m d.1) =
      (e.1, e.2 ^^ primedSideFlip w h m e.1) :=
    primedDartMap_injective w h m hh
  have ha := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  dsimp only at ha hb
  apply Prod.ext ha
  rw [ha] at hb
  exact Bool.xor_left_inj.mp hb

/-- P2 helper toward lem-quad-kmsw; not counted
the corrected map, including both darts of each missing edge. -/
theorem primedDartMapOriented_flip_comm
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedDartMapOriented w h m
        (edgeFlip (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge d) =
      edgeFlip (kmswStage w (primedStageTime w h m)).nextEdge
        (primedDartMapOriented w h m d) := by
  apply Prod.ext
  · rfl
  · exact Bool.not_xor _ _

/-- P2 helper toward lem-quad-kmsw; not counted
is stable under the next-stage inclusion. -/
theorem primedSideFlip_compatible (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedSideFlip w h (m + 1)
        (Fin.castLE (primedLocal_nextEdge_succ_le (primedCode (primedSimInput w) h) m) e) =
      primedSideFlip w h m e := by
  let u := primedCode (primedSimInput w) h
  have h0 := kmswMissingRootStage_agree u m
  have h1 := kmswMissingRootStage_agree u (m + 1)
  have he : e.val < (kmswStage u m).nextEdge := by rw [← h0.2.1]; exact e.isLt
  have hl : (kmswMissingRootStage u (m + 1)).west e.val =
      (kmswMissingRootStage u m).west e.val := by
    rw [h1.2.2.1, h0.2.2.1]
    exact (kmswStage_endpoints_stable u (Nat.le_succ m) he).1
  have hv : (kmswMissingRootStage u m).west e.val <
      (kmswMissingRootStage u m).nextVertex := by
    rw [h0.2.2.1, h0.1]
    exact (kmswStage_endpoints_lt_nextVertex u m e.val he).1
  have hg := (kmswStage_endpoints_stable w (primedStageTime_succ_le w h m)
    (primedDartMap w h m (e, false)).1.isLt).1
  unfold primedSideFlip
  change decide (primedAllVertexMap w h (m + 1)
      ((kmswMissingRootStage u (m + 1)).west e.val) ≠
      (kmswStage w (primedStageTime w h (m + 1))).west
        (primedAllEdgeMap w h (m + 1) e.val)) = _
  rw [hl, (primedAll_maps_extend w h m).2 _ hv,
    (primedAll_maps_extend w h m).1 _ e.isLt]
  exact congrArg (fun v => decide (primedAllVertexMap w h m
    ((kmswMissingRootStage u m).west e.val) ≠ v)) hg

/-- P2 helper toward lem-quad-kmsw; not counted
the inclusions of all allocated local and global geometric darts. -/
theorem primedDartMapOriented_compatible
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedDartMapOriented w h (m + 1)
      (outerSucc_castDart
        (primedLocal_nextEdge_succ_le (primedCode (primedSimInput w) h) m) d) =
      outerSucc_castDart
        (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m))
        (primedDartMapOriented w h m d) := by
  apply Prod.ext
  · exact Fin.ext ((primedAll_maps_extend w h m).1 _ d.1.isLt)
  · change (d.2 ^^ primedSideFlip w h (m + 1)
        (Fin.castLE (primedLocal_nextEdge_succ_le (primedCode (primedSimInput w) h) m) d.1)) =
      (d.2 ^^ primedSideFlip w h m d.1)
    rw [primedSideFlip_compatible]

/-- P2 helper toward lem-quad-kmsw; not counted
the existing present, directed-tail and positive-stage active-root lemmas therefore apply. -/
theorem primedDartMapOriented_eq_of_present
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hd : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present d.1.val = true) :
    primedDartMapOriented w h m d = primedDartMap w h m d := by
  have hw : (kmswStage w (primedStageTime w h m)).west (primedAllEdgeMap w h m d.1.val) =
      primedAllVertexMap w h m
        ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).west d.1.val) := by
    cases m with
    | zero => exact ((primedAll_sim_zero w h).1.present_incidence _ d.1.isLt hd).1
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact (hs.present_incidence _ d.1.isLt hd).1
  have hf : primedSideFlip w h m d.1 = false := by simp [primedSideFlip, hw]
  apply Prod.ext
  · rfl
  · change (d.2 ^^ primedSideFlip w h m d.1) = d.2
    rw [hf, Bool.xor_false]

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedSideFlip_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) 0).nextEdge) :
    primedSideFlip w h 0 e = false := by
  have he : e.val = 0 := by have := e.isLt; change e.val < 1 at this; omega
  simp [primedSideFlip, he, primedAllVertexMap, primedAllEdgeMap,
    primedInitialVertexMap, primedInitialEdgeMap, primedStageTime_zero,
    kmswMissingRootStage, kmswMissingRootInit, kmswInit]

/-- P2 helper toward lem-quad-kmsw; not counted -/
theorem primedSideFlip_one (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) 1).nextEdge) :
    primedSideFlip w h 1 e = decide (e.val = 2) := by
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hne : s.east s.active ≠ s.west s.active := by
    intro heq
    exact (activeEast_ne_activeInitial w (j := n - 1) (n := n - 1) le_rfl)
      (heq.trans (edge_endpoints_eq w ha).1)
  have hu := primedCode_zero (primedSimInput w) h
  have hb : e.val < 3 := by
    have := e.isLt
    simpa [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, State.addEdge] using this
  obtain ⟨hv0, _, hv1, _, hv2, _⟩ := primedAllVertexMap_one_endpoints w h
  obtain ⟨hg0, _, hg1, _, hg2, _⟩ := primedGlobal_one_endpoints w h
  have he : e.val = 0 ∨ e.val = 1 ∨ e.val = 2 := by omega
  rcases he with he | he | he
  · simp only [primedSideFlip, he, hv0, hg0, ne_eq, not_true_eq_false,
      decide_false, OfNat.zero_ne_ofNat]
  · simp only [primedSideFlip, he, hv1, hg1, ne_eq, not_true_eq_false,
      decide_false, OfNat.one_ne_ofNat]
  · change decide (_ ≠ _) = decide (e.val = 2)
    rw [he, hv2, hg2]
    change decide (s.east s.active ≠ s.west s.active) = true
    exact decide_eq_true hne

/-- P2 helper toward lem-quad-kmsw; not counted
geometric dart image, including both darts of every missing edge. -/
@[expose] def PrimedRotInducedOrientedAt (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) : Prop :=
  ∀ d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge,
    ∃ k : ℕ, 0 < k ∧
      (stageRot w (primedStageTime w h m) : _ → _)^[k]
        (primedDartMapOriented w h m d) =
          primedDartMapOriented w h m
            (primedLocalRot (primedCode (primedSimInput w) h) m d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (stageRot w (primedStageTime w h m) : _ → _)^[j]
          (primedDartMapOriented w h m d) ∉ Set.range (primedDartMapOriented w h m)

/-- P2 helper toward lem-quad-kmsw; not counted
is induced from the global rotation. -/
theorem primedRotInducedOriented_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    PrimedRotInducedOrientedAt w h 0 := by
  have hm : primedDartMapOriented w h 0 = primedDartMap w h 0 := by
    funext d
    apply Prod.ext
    · rfl
    · change (d.2 ^^ primedSideFlip w h 0 d.1) = d.2
      rw [primedSideFlip_zero, Bool.xor_false]
  unfold PrimedRotInducedOrientedAt
  rw [hm]
  exact primedRotInduced_zero w h

private theorem primed_oriented_first_return {D E : Type*} [Finite E]
    (ρ : Equiv.Perm E) (i : D → E) (d t : D)
    (ht : ρ.SameCycle (i d) (i t))
    (hf : ∀ e, ρ.SameCycle (i d) (i e) → e = d ∨ e = t) :
    ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i t ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ (ρ : E → E)^[k] (i d) = i t := by
    obtain ⟨k, hk, _, he⟩ := ht.exists_pow_eq''
    exact ⟨k, hk, by simpa only [Equiv.Perm.coe_pow] using he⟩
  let k := Nat.find hex
  have hk0 : 0 < k := (Nat.find_spec hex).1
  have hk : (ρ : E → E)^[k] (i d) = i t := (Nat.find_spec hex).2
  refine ⟨k, hk0, hk, ?_⟩
  intro j hj hjk ⟨e, he⟩
  have hc : ρ.SameCycle (i d) (i e) := by
    rw [he, ← Equiv.Perm.coe_pow]
    exact ⟨(j : ℤ), by simp⟩
  rcases hf e hc with hed | het
  · rw [hed] at he
    have hr : (ρ : E → E)^[k - j] (i d) = i t := by
      calc
        _ = (ρ : E → E)^[k - j] ((ρ : E → E)^[j] (i d)) := congrArg _ he
        _ = (ρ : E → E)^[k] (i d) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hjk)]
        _ = i t := hk
    exact Nat.find_min hex (show k - j < k by omega) ⟨by omega, hr⟩
  · rw [het] at he
    exact Nat.find_min hex hjk ⟨hj, he.symm⟩

/-- P2 helper toward lem-quad-kmsw; not counted
correct induced rotation after correcting geometric sides. -/
theorem primedRotInducedOriented_one (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    PrimedRotInducedOrientedAt w h 1 := by
  let u := primedCode (primedSimInput w) h
  let sh := kmswMissingRootStage u 1
  let t := kmswStepOfStep kmswMissingRootInit .up
  have hu : u 0 = 1 := primedCode_zero (primedSimInput w) h
  have hst : sh = t := by
    change kmswStep kmswMissingRootInit (u 0) = t
    rw [hu]
    rfl
  have hsize : sh.nextEdge = 3 := by rw [hst]; rfl
  have hvsize : sh.nextVertex = 3 := by rw [hst]; rfl
  let C : StageDart sh.nextEdge → StageDart 3 := fun d => (Fin.cast hsize d.1, d.2)
  let ρ : Equiv.Perm (StageDart 3) := StageRotation.up 1 1 (0, false) (0, true)
  let p : StageDart 3 → ℕ := fun d => if d.2 then t.east d.1.val else t.west d.1.val
  have htail (d : StageDart sh.nextEdge) : stageEndpoint sh d = p (C d) := by
    change (if d.2 then sh.east d.1.val else sh.west d.1.val) =
      (if d.2 then t.east d.1.val else t.west d.1.val)
    simp only [congrArg State.east hst, congrArg State.west hst]
  have hci : Function.Injective C := by
    intro a b he
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z : StageDart 3 => z.1.val) he)
    · exact congrArg (fun z : StageDart 3 => z.2) he
  have hperm : StageRotation.resize hsize (primedLocalRot u 1) = ρ := by
    have resize_comp {a b c : ℕ} (ha : a = b) (hb : b = c)
        (σ : Equiv.Perm (StageDart a)) :
        StageRotation.resize hb (StageRotation.resize ha σ) =
          StageRotation.resize (ha.trans hb) σ := by
      cases ha
      cases hb
      rfl
    unfold primedLocalRot
    rw [resize_comp]
    exact StageRotation.step_up kmswInit (by decide) (stageRotation_UL_bound u 0)
      1 (u 0) (by rw [hu]; rfl)
  have hcr (d : StageDart sh.nextEdge) : C (primedLocalRot u 1 d) = ρ (C d) := by
    have eval {a b : ℕ} (hab : a = b) (σ : Equiv.Perm (StageDart a))
        (z : StageDart a) :
        StageRotation.resize hab σ (Fin.cast hab z.1, z.2) =
          (Fin.cast hab (σ z).1, (σ z).2) := by
      cases hab
      rfl
    have he := eval hsize (primedLocalRot u 1) d
    rw [hperm] at he
    exact he.symm
  have hρ : ∀ a : StageDart 3, p (ρ a) = p a := by decide
  have hf : ∀ a b : StageDart 3, p a = p b → b = a ∨ b = ρ a := by decide
  have hb : ∀ a : StageDart 3, p a < 3 := by decide
  have hbound (d : StageDart sh.nextEdge) : stageEndpoint sh d < sh.nextVertex := by
    rw [hvsize, htail]
    exact hb (C d)
  obtain ⟨k, hs, _⟩ := primedAll_sim w h 1 (by omega)
  intro d
  have hc : (stageRot w (primedStageTime w h 1)).SameCycle
      (primedDartMapOriented w h 1 d)
      (primedDartMapOriented w h 1 (primedLocalRot u 1 d)) := by
    apply (stageRot_sameCycle_iff_endpoint_eq w (primedStageTime w h 1) _ _).2
    rw [primedDartMapOriented_endpoint, primedDartMapOriented_endpoint]
    congr 1
    change stageEndpoint sh d = stageEndpoint sh (primedLocalRot u 1 d)
    rw [htail, htail, hcr]
    exact (hρ (C d)).symm
  refine primed_oriented_first_return (stageRot w (primedStageTime w h 1))
    (primedDartMapOriented w h 1) d (primedLocalRot u 1 d) hc ?_
  intro e he
  have hep := (stageRot_sameCycle_iff_endpoint_eq w (primedStageTime w h 1) _ _).1 he
  rw [primedDartMapOriented_endpoint, primedDartMapOriented_endpoint] at hep
  have hl : stageEndpoint sh d = stageEndpoint sh e :=
    hs.vertex_injective _ _ (hbound d) (hbound e) hep
  have hraw : p (C d) = p (C e) := by rw [← htail, ← htail]; exact hl
  rcases hf (C d) (C e) hraw with hd | hr
  · exact Or.inl (hci hd)
  · exact Or.inr (hci (hr.trans (hcr d).symm))

/-- P2 helper toward lem-quad-kmsw; not counted
locally; no directed present edge can be reversed. -/
theorem primedSideFlip_true_missing (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (e : Fin (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (he : primedSideFlip w h m e = true) :
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e.val = false := by
  cases hp : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present e.val with
  | false => rfl
  | true =>
    have hh := congrArg (fun z : StageDart (kmswStage w (primedStageTime w h m)).nextEdge => z.2)
      (primedDartMapOriented_eq_of_present w h m (e, false) hp)
    change (false ^^ primedSideFlip w h m e) = false at hh
    rw [he] at hh
    cases hh

/-- P2 helper toward lem-quad-kmsw; not counted
read in its canonical numerical vertex IDs, agrees with the primed vertex map. -/
theorem primedDartMapOriented_dartTail
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    (stageVertexEquiv w (primedStageTime w h m)
      (DirectedDistances.PlanarMap.dartTailVertex
        (kmswRootedStage w (primedStageTime w h m)).map
        (primedDartMapOriented w h m d))).val =
      primedAllVertexMap w h m
        (stageEndpoint (kmswMissingRootStage (primedCode (primedSimInput w) h) m) d) := by
  change stageEndpoint (kmswStage w (primedStageTime w h m))
      (primedDartMapOriented w h m d) = _
  exact primedDartMapOriented_endpoint w h m d

end DirectedDistances.KMSW
