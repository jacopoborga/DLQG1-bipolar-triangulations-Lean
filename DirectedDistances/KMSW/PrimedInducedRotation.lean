module

public import DirectedDistances.KMSW.PrimedInducedEmbedding
import DirectedDistances.KMSW.HatInducedExit

/-! # Primed missing-root induced rotations

P2 helper toward lem-quad-kmsw; not counted
Missing geometric darts remain in the local rotation. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- P2 helper toward lem-quad-kmsw; not counted
The C18 initialization changes only presence, so its geometric rotation is
the ordinary rotation transported along the equality of allocated edge counts. -/
@[expose] def primedLocalRot (u : ℕ → Fin 3) (m : ℕ) :
    Equiv.Perm (StageDart (kmswMissingRootStage u m).nextEdge) :=
  StageRotation.resize (kmswMissingRootStage_agree u m).2.1.symm (stageRot u m)

/-- P2 helper toward lem-quad-kmsw; not counted
complete primed dart image, including both darts of every missing edge. -/
@[expose] def PrimedRotInducedAt (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (m : ℕ) : Prop :=
  ∀ d : StageDart (kmswMissingRootStage (primedCode (primedSimInput w) h) m).nextEdge,
    ∃ k : ℕ, 0 < k ∧
      (stageRot w (primedStageTime w h m) : _ → _)^[k]
        (primedDartMap w h m d) =
          primedDartMap w h m (primedLocalRot (primedCode (primedSimInput w) h) m d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (stageRot w (primedStageTime w h m) : _ → _)^[j]
          (primedDartMap w h m d) ∉ Set.range (primedDartMap w h m)

private theorem primed_finite_first_return {D E : Type*} [Finite E]
    (ρ : Equiv.Perm E) (i : D → E) (d : D) :
    ∃ k : ℕ, 0 < k ∧ (∃ e, i e = (ρ : E → E)^[k] (i d)) ∧
      ∀ j : ℕ, 0 < j → j < k → (ρ : E → E)^[j] (i d) ∉ Set.range i := by
  classical
  obtain ⟨n, hn, _, he⟩ := (Equiv.Perm.SameCycle.refl ρ (i d)).exists_pow_eq''
  have hex : ∃ n : ℕ, 0 < n ∧ (ρ : E → E)^[n] (i d) ∈ Set.range i :=
    ⟨n, hn, d, he.symm⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hjk hmem
  exact Nat.find_min hex hjk ⟨hj, hmem⟩

private theorem primed_initial_root_endpoints_ne (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) :
    (kmswStage w (primedStageTime w h 0)).west (primedAllEdgeMap w h 0 0) ≠
      (kmswStage w (primedStageTime w h 0)).east (primedAllEdgeMap w h 0 0) := by
  let sim := (primedAll_sim_zero w h).1
  have hm := sim.missing_incidence 0 (by change 0 < 1; decide)
    (by change false = false; rfl)
  change ({(kmswStage w (primedStageTime w h 0)).west (primedAllEdgeMap w h 0 0),
    (kmswStage w (primedStageTime w h 0)).east (primedAllEdgeMap w h 0 0)} : Multiset ℕ) =
      {primedAllVertexMap w h 0 0, primedAllVertexMap w h 0 1} at hm
  intro hwe
  have h0 : primedAllVertexMap w h 0 0 ∈
      ({(kmswStage w (primedStageTime w h 0)).west (primedAllEdgeMap w h 0 0),
        (kmswStage w (primedStageTime w h 0)).east (primedAllEdgeMap w h 0 0)} : Multiset ℕ) := by
    rw [hm]
    simp
  have h1 : primedAllVertexMap w h 0 1 ∈
      ({(kmswStage w (primedStageTime w h 0)).west (primedAllEdgeMap w h 0 0),
        (kmswStage w (primedStageTime w h 0)).east (primedAllEdgeMap w h 0 0)} : Multiset ℕ) := by
    rw [hm]
    simp
  simp [hwe] at h0 h1
  have he := sim.vertex_injective 0 1 (by change 0 < 2; decide)
    (by change 1 < 2; decide) (h0.trans h1.symm)
  omega

/-- P2 helper toward lem-quad-kmsw; not counted
edge induces two singleton vertex rotations at the first global left exit. -/
theorem primedRotInduced_zero (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    PrimedRotInducedAt w h 0 := by
  intro d
  obtain ⟨k, hk, ⟨e, he⟩, hg⟩ := primed_finite_first_return
    (stageRot w (primedStageTime w h 0)) (primedDartMap w h 0) d
  have hs : (stageRot w (primedStageTime w h 0)).SameCycle
      (primedDartMap w h 0 d) (primedDartMap w h 0 e) := by
    rw [he, ← Equiv.Perm.coe_pow]
    exact ⟨(k : ℤ), by simp⟩
  have hep := (stageRot_sameCycle_iff_endpoint_eq w (primedStageTime w h 0) _ _).1 hs
  have hed : e = d := by
    obtain ⟨⟨a, ha⟩, b⟩ := d
    obtain ⟨⟨c, hc⟩, f⟩ := e
    have ha0 : a = 0 := by change a < 1 at ha; omega
    have hc0 : c = 0 := by change c < 1 at hc; omega
    subst a
    subst c
    cases b <;> cases f
    · rfl
    · exact (primed_initial_root_endpoints_ne w h hep).elim
    · exact (primed_initial_root_endpoints_ne w h hep.symm).elim
    · rfl
  have hrot : primedLocalRot (primedCode (primedSimInput w) h) 0 d = d := rfl
  refine ⟨k, hk, ?_, hg⟩
  simpa only [hrot, hed] using he.symm

private theorem primed_first_rotation_root (u : ℕ → Fin 3) (hu : u 0 = 1)
    (d : StageDart (kmswMissingRootStage u 1).nextEdge)
    (hd : d.1.val = 0) (hb : d.2 = true) :
    (primedLocalRot u 1 d).1.val = 2 ∧ (primedLocalRot u 1 d).2 = true := by
  have hsize : (kmswMissingRootStage u 1).nextEdge = 3 := by
    simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
      kmswMissingRootInit, kmswInit, State.addEdge]
  have resize_comp {k l r : ℕ} (hk : k = l) (hl : l = r)
      (σ : Equiv.Perm (StageDart k)) :
      StageRotation.resize hl (StageRotation.resize hk σ) =
        StageRotation.resize (hk.trans hl) σ := by
    cases hk
    cases hl
    rfl
  have hperm : StageRotation.resize hsize (primedLocalRot u 1) =
      StageRotation.up 1 1 (0, false) (0, true) := by
    unfold primedLocalRot
    rw [resize_comp]
    exact StageRotation.step_up kmswInit (by decide) (stageRotation_UL_bound u 0)
      1 (u 0) (by rw [hu]; rfl)
  have eval {k l : ℕ} (hk : k = l) (σ : Equiv.Perm (StageDart k))
      (z : StageDart k) :
      (StageRotation.resize hk σ (Fin.cast hk z.1, z.2)).1.val = (σ z).1.val ∧
        (StageRotation.resize hk σ (Fin.cast hk z.1, z.2)).2 = (σ z).2 := by
    cases hk
    exact ⟨rfl, rfl⟩
  have hd' : (Fin.cast hsize d.1, d.2) = ((0, true) : StageDart 3) :=
    Prod.ext (Fin.ext hd) hb
  have he := eval hsize (primedLocalRot u 1) d
  rw [hd', hperm] at he
  have ht : StageRotation.up 1 1 (0, false) (0, true) (0, true) = (2, true) := by
    decide
  rw [ht] at he
  exact ⟨he.1.symm, he.2.symm⟩





theorem primedRotInduced_one_impossible (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    ¬ PrimedRotInducedAt w h 1 := by
  let u := primedCode (primedSimInput w) h
  have hu : u 0 = 1 := primedCode_zero (primedSimInput w) h
  let n := walkNL w h 0
  let s := kmswStage w (n - 1)
  have ht : primedStageTime w h 1 = n := by
    simpa only [primedIntervalBase_zero, zero_add] using
      primedStageTime_after_crossing w h 0
  have hg : kmswStage w n = kmswStepOfStep s .left :=
    primedInitial_globalExitTransition w h
  have hdrop : s.UL.dropLast.reverse = [] :=
    (quadrantFirstR_exit_predecessor_emptyUL w h).2.2.2
  let d : StageDart (kmswMissingRootStage u 1).nextEdge :=
    (⟨0, by
      simp [kmswMissingRootStage, hu, kmswStep, kmswCodeStep, kmswStepOfStep,
        kmswMissingRootInit, kmswInit, State.addEdge]⟩, true)
  have hr := primed_first_rotation_root u hu d rfl rfl
  have hend0 : stageEndpoint (kmswStage w (primedStageTime w h 1))
      (primedDartMap w h 1 d) = s.west s.active := by
    change (kmswStage w (primedStageTime w h 1)).east (primedAllEdgeMap w h 1 0) = _
    rw [show primedAllEdgeMap w h 1 0 = s.nextEdge + 1 from rfl, ht, hg]
    simp [kmswStepOfStep, hdrop, State.addEdge]
  have hend1 : stageEndpoint (kmswStage w (primedStageTime w h 1))
      (primedDartMap w h 1 (primedLocalRot u 1 d)) = s.east s.active := by
    simp only [stageEndpoint, primedDartMap, hr.1, hr.2, ↓reduceIte]
    have ha : s.active < s.nextEdge :=
      (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
    rw [show primedAllEdgeMap w h 1 2 = s.active from rfl, ht, hg]
    simp [kmswStepOfStep, hdrop, State.addEdge, show s.active ≠ s.nextEdge by omega,
      show s.active ≠ s.nextEdge + 1 by omega]
  intro hi
  obtain ⟨k, _, he, _⟩ := hi d
  have hs : (stageRot w (primedStageTime w h 1)).SameCycle
      (primedDartMap w h 1 d)
      (primedDartMap w h 1 (primedLocalRot u 1 d)) := by
    rw [← he, ← Equiv.Perm.coe_pow]
    exact ⟨(k : ℤ), by simp⟩
  have hep := (stageRot_sameCycle_iff_endpoint_eq w (primedStageTime w h 1) _ _).1 hs
  rw [hend0, hend1] at hep
  have ha : s.active < s.nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w (n - 1)).1
  have hn := activeEast_ne_activeInitial w (j := n - 1) (n := n - 1) le_rfl
  have hw := (edge_endpoints_eq w ha).1
  exact hn (hep.symm.trans hw)

end DirectedDistances.KMSW
