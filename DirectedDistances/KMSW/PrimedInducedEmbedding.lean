module

public import DirectedDistances.KMSW.PrimedSimAll
public import DirectedDistances.KMSW.HatInducedEmbedding

/-! # Primed geometric dart maps and the initial rooted-interface obstruction

P2 helper toward lem-quad-kmsw; not counted
missing initial root. The existing `RootedDirectedMapWithMissing` interface
requires its root to be present, so it cannot package local stage zero.
Moreover the initial active dart maps to a missing global edge rather than
the present global active root. No rooted induced embedding is asserted. -/

public section
namespace DirectedDistances.KMSW

/-- P2 helper toward lem-quad-kmsw; not counted
geometric darts, retaining the west/east side bit and using the separate
initial simulation at stage zero. -/
@[expose] noncomputable def primedDartMap (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    StageDart (kmswStage w (primedStageTime w h m)).nextEdge :=
  (⟨primedAllEdgeMap w h m d.1.val, by
    cases m with
    | zero => exact (primedAll_sim_zero w h).1.edge_bound _ d.1.isLt
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.edge_bound _ d.1.isLt⟩, d.2)

/-- P2 helper toward lem-quad-kmsw; not counted
remain distinct at the aligned global stage. -/
theorem primedDartMap_injective (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ) :
    Function.Injective (primedDartMap w h m) := by
  intro d e heq
  apply Prod.ext
  · apply Fin.ext
    have he : primedAllEdgeMap w h m d.1.val = primedAllEdgeMap w h m e.1.val :=
      congrArg (fun x => x.1.val) heq
    cases m with
    | zero => exact (primedAll_sim_zero w h).1.edge_injective _ _ d.1.isLt e.1.isLt he
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact hs.edge_injective _ _ d.1.isLt e.1.isLt he
  · exact congrArg
      (fun x : StageDart (kmswStage w (primedStageTime w h m)).nextEdge => x.2) heq

/-- P2 helper toward lem-quad-kmsw; not counted
with the primed dart map, including at the missing initial edge. -/
theorem primedDartMap_flip_comm (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedDartMap w h m
        (edgeFlip (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge d) =
      edgeFlip (kmswStage w (primedStageTime w h m)).nextEdge
        (primedDartMap w h m d) := rfl

/-- P2 helper toward lem-quad-kmsw; not counted
The existing rooted interface requires a present root, whereas every edge
of the initial missing-root stage is missing. Thus even its missing predicate
cannot be packaged in that interface at stage zero. -/
theorem primedMissingRootStage_zero_no_rooted_map (u : ℕ → Fin 3) :
    ¬ ∃ N : RootedDirectedMapWithMissing
        (StageDart (kmswMissingRootStage u 0).nextEdge),
      ∀ d, N.map.missing d ↔ (kmswMissingRootStage u 0).present d.1.val = false := by
  rintro ⟨N, hm⟩
  have he : N.root.1.val = 0 := by
    have hb := N.root.1.isLt
    change N.root.1.val < 1 at hb
    omega
  apply N.root_present
  apply (hm N.root).2
  rw [he]
  exact kmswMissingRootStage_present_zero u 0





theorem primedDartMap_initial_active_ne_global_active
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    primedAllEdgeMap w h 0
        (kmswMissingRootStage (primedCode (primedSimInput w) h) 0).active ≠
      (kmswStage w (primedStageTime w h 0)).active := by
  intro he
  change primedAllEdgeMap w h 0 0 =
    (kmswStage w (primedStageTime w h 0)).active at he
  have hm := (primedAll_sim_zero w h).1.missing_root.2.1
  rw [he] at hm
  have hp := (kmswRootedStage w (primedStageTime w h 0)).root_present
  change ¬ (kmswStage w (primedStageTime w h 0)).present
    (kmswStage w (primedStageTime w h 0)).active = false at hp
  exact hp hm

/-- P2 helper toward lem-quad-kmsw; not counted
has a present active edge. This is exploration-root data and does not
resolve the identity of the paper's original primed root. -/
theorem primed_active_present (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
      (kmswMissingRootStage (primedCode (primedSimInput w) h) m).active = true := by
  obtain ⟨k, hs, _⟩ := primedAll_sim w h m hm
  have hne : (kmswMissingRootStage (primedCode (primedSimInput w) h) m).active ≠ 0 := by
    intro hz
    have ha := hs.active_alignment
    rw [hz] at ha
    have hp := kmswStage_active_present w (primedStageTime w h m)
    change (kmswStage w (primedStageTime w h m)).present
      (kmswStage w (primedStageTime w h m)).active = true at hp
    rw [← ha, hs.missing_root.2.1] at hp
    cases hp
  obtain ⟨_, _, _, _, hp, _, ha, _⟩ :=
    kmswMissingRootStage_agree (primedCode (primedSimInput w) h) m
  rw [hp _ hne, ha]
  exact kmswStage_active_present _ m

/-- P2 helper toward lem-quad-kmsw; not counted
present global images, including the vacuous initial-stage case. -/
theorem primedDartMap_present (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hd : ¬ (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
      d.1.val = false) :
    ¬ (kmswRootedStage w (primedStageTime w h m)).map.missing
      (primedDartMap w h m d) := by
  change ¬ (kmswStage w (primedStageTime w h m)).present
    (primedAllEdgeMap w h m d.1.val) = false
  have hp : (kmswStage w (primedStageTime w h m)).present
      (primedAllEdgeMap w h m d.1.val) = true := by
    cases m with
    | zero => exact ((primedAll_sim_zero w h).1.present_complement _ d.1.isLt
        (Bool.eq_true_of_not_eq_false hd)).1
    | succ m =>
      obtain ⟨k, hs, _⟩ := primedAll_sim w h (m + 1) (by omega)
      exact (hs.present_complement _ d.1.isLt (Bool.eq_true_of_not_eq_false hd)).1
  rw [hp]
  decide

/-- P2 helper toward lem-quad-kmsw; not counted
side bit preserves the directed-tail predicate. -/
theorem primedDartMap_tail (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge)
    (hd : ¬ (kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
      d.1.val = false) :
    ((kmswMissingRootStage (primedCode (primedSimInput w) h) m).present
        d.1.val = true ∧ d.2 = false) ↔
      (kmswRootedStage w (primedStageTime w h m)).map.tail
        (primedDartMap w h m d) := by
  have hg := primedDartMap_present w h m d hd
  change ¬ (kmswStage w (primedStageTime w h m)).present
    (primedAllEdgeMap w h m d.1.val) = false at hg
  change (_ = true ∧ d.2 = false) ↔
    ((kmswStage w (primedStageTime w h m)).present
      (primedAllEdgeMap w h m d.1.val) = true ∧ d.2 = false)
  rw [Bool.eq_true_of_not_eq_false hd, Bool.eq_true_of_not_eq_false hg]

/-- P2 helper toward lem-quad-kmsw; not counted
darts map to the global active root at the aligned exploration time. -/
theorem primedDartMap_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) (hm : 1 ≤ m) :
    primedDartMap w h m
      (⟨(kmswMissingRootStage (primedCode (primedSimInput w) h) m).active, by
        have ha := (kmswStage_boundary_ids_lt_nextEdge
          (primedCode (primedSimInput w) h) m).1
        obtain ⟨_, he, _, _, _, _, ha', _⟩ :=
          kmswMissingRootStage_agree (primedCode (primedSimInput w) h) m
        rw [he, ha']
        exact ha⟩, false) =
      (kmswRootedStage w (primedStageTime w h m)).root := by
  obtain ⟨k, hs, _⟩ := primedAll_sim w h m hm
  apply Prod.ext
  · exact Fin.ext hs.active_alignment
  · rfl

/-- P2 helper toward lem-quad-kmsw; not counted
time is nondecreasing when one primed code is consumed. -/
theorem primedStageTime_succ_le (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) : primedStageTime w h m ≤ primedStageTime w h (m + 1) := by
  by_cases hm : m = 0
  · subst m
    rw [primedStageTime_zero]
    have ht := primedStageTime_after_crossing w h 0
    rw [primedIntervalBase_zero, zero_add] at ht
    exact ht.ge
  let k := primedIntervalIndex (primedSimInput w) h (m - 1)
  have hr : m ≤ primedIntervalBase (primedSimInput w) h (k + 1) := by
    have hi := primedIntervalIndex_spec (primedSimInput w) h (m - 1)
    change m - 1 < primedIntervalBase (primedSimInput w) h (k + 1) at hi
    omega
  have hl : primedIntervalBase (primedSimInput w) h k < m := by
    cases hk : primedIntervalIndex (primedSimInput w) h (m - 1) with
    | zero =>
      change primedIntervalBase (primedSimInput w) h
        (primedIntervalIndex (primedSimInput w) h (m - 1)) < m
      rw [hk, primedIntervalBase_zero]
      omega
    | succ j =>
      have hn := Nat.find_min (primedIntervalIndex_exists (primedSimInput w) h (m - 1))
        (show j < Nat.find (primedIntervalIndex_exists (primedSimInput w) h (m - 1)) by
          change j < primedIntervalIndex (primedSimInput w) h (m - 1)
          omega)
      change ¬ m - 1 < primedIntervalBase (primedSimInput w) h (j + 1) at hn
      change primedIntervalBase (primedSimInput w) h
        (primedIntervalIndex (primedSimInput w) h (m - 1)) < m
      rw [hk]
      omega
  by_cases hc : m < primedIntervalBase (primedSimInput w) h (k + 1)
  · rw [primedStageTime_block w h k m hl hr,
      primedStageTime_block w h k (m + 1) (by omega) (by omega)]
    omega
  · have he : m = primedIntervalBase (primedSimInput w) h (k + 1) := by omega
    rw [he, primedStageTime_at_crossing, primedStageTime_after_crossing]
    have hn := (walkNL_spec w h (k + 1)).1
    omega

/-- P2 helper toward lem-quad-kmsw; not counted
Previously allocated geometric darts remain allocated at the next local stage. -/
theorem primedLocal_nextEdge_succ_le (u : ℕ → Fin 3) (m : ℕ) :
    (kmswMissingRootStage u m).nextEdge ≤ (kmswMissingRootStage u (m + 1)).nextEdge := by
  have h0 := (kmswMissingRootStage_agree u m).2.1
  have h1 := (kmswMissingRootStage_agree u (m + 1)).2.1
  rw [h0, h1]
  exact kmswStage_nextEdge_mono u (Nat.le_succ m)

/-- P2 helper toward lem-quad-kmsw; not counted
commute with the inclusions of allocated local and global darts. -/
theorem primedDartMap_compatible (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge) :
    primedDartMap w h (m + 1)
      (outerSucc_castDart
        (primedLocal_nextEdge_succ_le (primedCode (primedSimInput w) h) m) d) =
      outerSucc_castDart
        (kmswStage_nextEdge_mono w (primedStageTime_succ_le w h m))
        (primedDartMap w h m d) := by
  apply Prod.ext
  · exact Fin.ext ((primedAll_maps_extend w h m).1 d.1.val d.1.isLt)
  · rfl

private theorem rotation_resize_values {a b : ℕ} (hab : a = b)
    (σ : Equiv.Perm (StageDart a)) (d : StageDart a) :
    let e : StageDart b := (⟨d.1.val, hab ▸ d.1.isLt⟩, d.2)
    (((StageRotation.resize hab σ) e).1.val, ((StageRotation.resize hab σ) e).2) =
      ((σ d).1.val, (σ d).2) := by
  cases hab
  rfl

/-- P2 helper toward lem-quad-kmsw; not counted
the ordinary stage carrier, which has the identical geometric edge IDs
and rotation; only the presence of edge zero differs under C18. -/
@[expose] noncomputable def primedDartMapOnStage
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (m : ℕ)
    (d : StageDart (kmswStage (primedCode (primedSimInput w) h) m).nextEdge) :
    StageDart (kmswStage w (primedStageTime w h m)).nextEdge :=
  primedDartMap w h m (⟨d.1.val, by
    rw [(kmswMissingRootStage_agree (primedCode (primedSimInput w) h) m).2.1]
    exact d.1.isLt⟩, d.2)






theorem primedDartMap_rot_induced_obstruction
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ∃ d : StageDart (kmswStage (primedCode (primedSimInput w) h) 1).nextEdge,
      d ∉ stageOuterWord (primedCode (primedSimInput w) h) 1 ∧
      (kmswMap (primedCode (primedSimInput w) h) 1).edgeInv
          ((kmswMap (primedCode (primedSimInput w) h) 1).rot d) ∉
        stageOuterWord (primedCode (primedSimInput w) h) 1 ∧
      ∀ k : ℕ,
        ((kmswMap w (primedStageTime w h 1)).rot : _ → _)^[k]
            (primedDartMapOnStage w h 1 d) ≠
          primedDartMapOnStage w h 1
            ((kmswMap (primedCode (primedSimInput w) h) 1).rot d) := by
  let u := primedCode (primedSimInput w) h
  have hu : u 0 = 1 := (primedInitial_code_alignment (primedSimInput w) h).1
  have hsize : (kmswStage u 1).nextEdge = 3 := by
    simp [kmswStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep, kmswInit, State.addEdge]
  let d : StageDart (kmswStage u 1).nextEdge :=
    (⟨2, by rw [hsize]; decide⟩, true)
  let e : StageDart (kmswStage u 1).nextEdge :=
    (⟨0, by rw [hsize]; decide⟩, true)
  have hrot : (kmswMap u 1).rot d = e := by
    have hr : StageRotation.resize hsize (kmswMap u 1).rot =
        StageRotation.up 1 1 (0, false) (0, true) := by
      exact StageRotation.step_up kmswInit (act_lt_nextEdge u (le_refl 0))
        (stageRotation_UL_bound u 0) 1 (u 0) (by rw [hu]; rfl)
    have hv := rotation_resize_values hsize (kmswMap u 1).rot d
    dsimp only at hv
    rw [hr] at hv
    change (((StageRotation.up 1 1 (0, false) (0, true))
        (⟨2, by decide⟩, true)).1.val,
      ((StageRotation.up 1 1 (0, false) (0, true)) (⟨2, by decide⟩, true)).2) =
        (((kmswMap u 1).rot d).1.val, ((kmswMap u 1).rot d).2) at hv
    have hn := (StageRotation.up_new 1 1 (0, false) (0, true)).2.1
    change (StageRotation.up 1 1 (0, false) (0, true))
      (⟨2, by decide⟩, true) = (⟨0, by decide⟩, true) at hn
    rw [hn] at hv
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hv).symm
    · exact (congrArg Prod.snd hv).symm
  have hinner : d ∉ stageOuterWord u 1 := by
    apply stageTriangleDart_not_outer u 1 ⟨0, Or.inr hu⟩ (by change 0 < 1; decide)
    simp [d, stageTriangleDartList, stageTriangleDartTriple, hu, kmswStage, kmswInit]
  have hcorner : (kmswMap u 1).edgeInv e ∉ stageOuterWord u 1 := by
    apply stageTriangleDart_not_outer u 1 ⟨0, Or.inr hu⟩ (by change 0 < 1; decide)
    change (0, false) ∈ stageTriangleDartList u ⟨0, Or.inr hu⟩
    simp [stageTriangleDartList, stageTriangleDartTriple, hu, kmswStage, kmswInit]
  refine ⟨d, hinner, ?_, ?_⟩
  · rw [hrot]
    exact hcorner
  intro k heq
  rw [hrot] at heq
  have hcycle : (stageRot w (primedStageTime w h 1)).SameCycle
      (primedDartMapOnStage w h 1 d) (primedDartMapOnStage w h 1 e) := by
    refine ⟨(k : ℤ), ?_⟩
    simpa only [zpow_natCast, Equiv.Perm.coe_pow, kmswMap_rot] using heq
  have hend := (stageRot_sameCycle_iff_endpoint_eq w (primedStageTime w h 1) _ _).mp hcycle
  have ht : primedStageTime w h 1 = walkNL w h 0 := by
    have ht' := primedStageTime_after_crossing w h 0
    rw [primedIntervalBase_zero, zero_add] at ht'
    exact ht'
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have hstep : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  have ha : s.active < s.nextEdge := (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have ha0 : s.active ≠ s.nextEdge := ne_of_lt ha
  have ha1 : s.active ≠ s.nextEdge + 1 := by omega
  change (kmswStage w (primedStageTime w h 1)).east
      (primedAllEdgeMap w h 1 2) =
    (kmswStage w (primedStageTime w h 1)).east (primedAllEdgeMap w h 1 0) at hend
  simp only [primedAllEdgeMap, ↓reduceIte] at hend
  change (kmswStage w (primedStageTime w h 1)).east (primedFirstStepEdgeMap w n 2) =
    (kmswStage w (primedStageTime w h 1)).east (primedFirstStepEdgeMap w n 0) at hend
  rw [ht] at hend
  change (kmswStage w n).east (primedFirstStepEdgeMap w n 2) =
    (kmswStage w n).east (primedFirstStepEdgeMap w n 0) at hend
  rw [hstep] at hend
  simp only [primedFirstStepEdgeMap, show (2 : ℕ) ≠ 0 by decide,
    show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hend
  change (kmswStepOfStep s .left).east s.active =
    (kmswStepOfStep s .left).east (s.nextEdge + 1) at hend
  simp only [kmswStepOfStep, hdrop, State.addEdge, ha0, ha1, ↓reduceIte] at hend
  have hr := kmswStageRank_strict w (n - 1) s.active ha
  change kmswStageRank w (n - 1) (s.west s.active) <
    kmswStageRank w (n - 1) (s.east s.active) at hr
  rw [hend] at hr
  exact (lt_irrefl _ hr)

end DirectedDistances.KMSW
