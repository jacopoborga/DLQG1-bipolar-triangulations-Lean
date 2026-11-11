/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization15
public import DirectedDistances.KMSW.StageLimitEmbedding
public import DirectedDistances.KMSW.WholePlaneRunRotationRestrict
public import DirectedDistances.KMSW.HatInducedExit

/-! # Finite stage restrictions of arbitrary whole-plane drawings

The restriction keeps the actual vertex positions and entire polylines. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3
open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

/-- Helper toward Proposition 3.9: the finite stage rotation is the first
return of the whole-plane rotation, including incomplete boundary stars. -/
theorem uibotWholePlane_stage_inverse_firstReturn
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (N m : ℕ)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge) :
    ∃ k : ℕ, 0 < k ∧
      ((wholePlaneRotation W H).symm : _ → _)^[k]
        (wholePlaneDartι W N (d.1.val, d.2)) =
        wholePlaneDartι W N (((stageRot (shiftedStream W N) m).symm d).1.val,
          ((stageRot (shiftedStream W N) m).symm d).2) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((wholePlaneRotation W H).symm : _ → _)^[j]
          (wholePlaneDartι W N (d.1.val, d.2)) ∉
          range (fun a : StageDart (kmswStage (shiftedStream W N) m).nextEdge =>
            wholePlaneDartι W N (a.1.val, a.2)) := by
  apply hatExit_induced_rotation_comp
    (stageRot (shiftedStream W N) m).symm
    (kmswInfRot (shiftedStream W N) (H.1 N)).symm
    (wholePlaneRotation W H).symm (fun a => (a.1.val, a.2))
    (wholePlaneDartι W N) (wholePlaneDartι_injective W N)
  · intro a
    obtain ⟨k, hk, he, hg⟩ := (kmswStage_limit_firstReturn
      (shiftedStream W N) (H.1 N) m a).2
    refine ⟨k, hk, ?_, ?_⟩
    · rw [permIterateEqPow]
      exact he
    · intro j hj hjk hmem
      obtain ⟨b, hb⟩ := hmem
      have hl := hg j hj hjk
      rw [permIterateEqPow] at hb
      have hval := congrArg Prod.fst hb
      change b.1.val = _ at hval
      change (kmswStage (shiftedStream W N) m).nextEdge ≤
        (((kmswInfRot (shiftedStream W N) (H.1 N)).symm ^ j) (a.1.val, a.2)).1 at hl
      rw [← hval] at hl
      exact (Nat.not_le_of_lt b.1.isLt) hl
  · intro a
    obtain ⟨k, hk, he, hg⟩ := wholePlaneRotation_symm_firstReturn_run W H N a
    refine ⟨k, hk, ?_, ?_⟩
    · rw [permIterateEqPow]; exact he
    · intro j hj hjk
      rw [permIterateEqPow]
      exact hg j hj hjk

/-- Helper toward Proposition 3.9: inverse first-return scans determine
the forward rotation of a restricted drawing. -/
theorem uibotDrawing_firstReturn_of_inverse_scan
    {D E V : Type*} {flip : E → E} {rot : Equiv.Perm E} {vert : E → V}
    (P : PLDrawing E V flip rot vert) (σ : Equiv.Perm D) (i : D → E)
    (hscan : ∀ d, ∃ k : ℕ, 0 < k ∧
      (rot.symm : E → E)^[k] (i d) = i (σ.symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (rot.symm : E → E)^[j] (i d) ∉ range i) (d : D) :
    (drawingFirstReturnPerm P (range i) ⟨i d, ⟨d, rfl⟩⟩).val = i (σ d) := by
  classical
  obtain ⟨k, hk, he, hg⟩ := hscan (σ d)
  rw [Equiv.symm_apply_apply] at he
  have hpow : (rot.symm ^ k) (i (σ d)) = i d := by
    simpa only [permIterateEqPow] using he
  have hfwd : (rot ^ k) (i d) = i (σ d) := by
    rw [← hpow, ← Equiv.Perm.mul_apply, show rot.symm ^ k = (rot ^ k).symm from inv_pow rot k,
      Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  have hgap (j : ℕ) (hj : 0 < j) (hjk : j < k) :
      (rot ^ j) (i d) ∉ range i := by
    have hs : (rot ^ j) (i d) = (rot.symm ^ (k - j)) (i (σ d)) := by
      apply (rot ^ (k - j)).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjk.le, hfwd,
        show rot.symm ^ (k - j) = (rot ^ (k - j)).symm from inv_pow rot (k - j),
        Equiv.apply_symm_apply]
    rw [hs]
    simpa only [permIterateEqPow] using hg (k - j) (by omega) (by omega)
  let x : range i := ⟨i d, ⟨d, rfl⟩⟩
  have htime : subsetFirstReturnTime rot (range i) (drawingPositiveReturn P (range i)) x = k := by
    apply Nat.le_antisymm
    · apply Nat.find_min'
      exact ⟨hk, by rw [permIterateEqPow, hfwd]; exact ⟨σ d, rfl⟩⟩
    · have ht := subsetFirstReturnTime_spec rot (range i) (drawingPositiveReturn P (range i)) x
      by_contra hn
      exact hgap _ ht.1 (Nat.lt_of_not_ge hn)
        (by simpa only [permIterateEqPow] using ht.2.1)
  change (rot : E → E)^[subsetFirstReturnTime rot (range i)
    (drawingPositiveReturn P (range i)) x] (i d) = _
  rw [htime, permIterateEqPow]
  exact hfwd

/-- Helper toward Proposition 3.9: a stage dart has its original endpoint
in every whole-plane realization. -/
theorem uibotWholePlane_stage_endpoint (W : ℤ → Fin 3) (N m : ℕ)
    (a : StageDart (kmswStage (shiftedStream W N) m).nextEdge) :
    wholePlaneDartVertex W (wholePlaneDartι W N (a.1.val, a.2)) =
      wholePlaneVertexι W N (stageVertex (shiftedStream W N) m a).val := by
  rw [wholePlaneDartVertex_ι]
  obtain ⟨hw, he⟩ := edge_endpoints_eq (shiftedStream W N) a.1.isLt
  cases hb : a.2 <;> simp only [kmswLimitDartVertex, stageVertex, stageEndpoint,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

/-- Helper toward Proposition 3.9: restrict any whole-plane drawing to
any finite stage, with exactly the stage rotation, positions and polylines.
No exterior certificate or capture hypothesis is assumed. -/
@[expose] def uibotWholePlaneStageDrawing
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ) : StageDrawing (shiftedStream W N) m := by
  let u := shiftedStream W N
  let I : StageDart (kmswStage u m).nextEdge → WholePlaneDart W :=
    fun a => wholePlaneDartι W N (a.1.val, a.2)
  have hi : Function.Injective I := by
    intro a b h
    have he := wholePlaneDartι_injective W N h
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (congrArg (fun z : ℕ × Bool => z.2) he)
  let S := range I
  have hs : ∀ d, d ∈ S ↔ wholePlaneDartFlip W d ∈ S := by
    intro d
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨edgeFlip _ a, rfl⟩
    · rintro ⟨a, ha⟩
      refine ⟨edgeFlip _ a, ?_⟩
      change wholePlaneDartFlip W (I a) = d
      rw [ha, G.flip_involutive]
  let Q := restrictDrawing G S hs
  let J : StageDart (kmswStage u m).nextEdge → S := fun a => ⟨I a, ⟨a, rfl⟩⟩
  have hrot (a) : drawingFirstReturnPerm G S (J a) = J (stageRot u m a) := by
    apply Subtype.ext
    exact uibotDrawing_firstReturn_of_inverse_scan G (stageRot u m) I
      (uibotWholePlane_stage_inverse_firstReturn W H N m) a
  have hv (a b) : wholePlaneDartVertex W (I a) = wholePlaneDartVertex W (I b) ↔
      stageVertex u m a = stageVertex u m b := by
    rw [uibotWholePlane_stage_endpoint, uibotWholePlane_stage_endpoint]
    exact (wholePlaneVertexι_injective W N).eq_iff.trans Fin.val_inj
  refine {
    flip_involutive := (kmswMap u m).edgeInv_invol
    flip_ne := (kmswMap u m).edgeInv_ne
    vert_rotation := ?_
    pos := fun v => G.pos (wholePlaneVertexι W N v.val)
    pos_injective := ?_
    arc := fun a => G.arc (I a)
    arc_simple := fun a => G.arc_simple (I a)
    arc_length := fun a => G.arc_length (I a)
    arc_start := ?_
    arc_finish := ?_
    arc_flip := fun a => G.arc_flip (I a)
    interior_disjoint := ?_
    interior_avoids_vertices := fun a v => G.interior_avoids_vertices (I a) _
    locally_finite := fun _ _ => Set.toFinite _
    initial_nonzero := fun a => G.initial_nonzero (I a)
    initial_arg_injective := ?_
    rotation_agreement := ?_ }
  · intro a
    apply Fin.ext
    exact (stageRot_sameCycle_iff_endpoint_eq u m _ _).mp
      Equiv.Perm.SameCycle.rfl.apply_right |>.symm
  · intro v z h
    exact Fin.ext (wholePlaneVertexι_injective W N (G.pos_injective h))
  · intro a
    exact (G.arc_start (I a)).trans (congrArg G.pos (uibotWholePlane_stage_endpoint W N m a))
  · intro a
    exact (G.arc_finish (I a)).trans
      (congrArg G.pos (uibotWholePlane_stage_endpoint W N m (edgeFlip _ a)))
  · intro a b hba hbf
    apply G.interior_disjoint
    · exact fun h => hba (hi h)
    · exact fun h => hbf (hi h)
  · intro a b hab he
    apply hi
    exact G.initial_arg_injective _ _ ((hv a b).mpr hab) he
  · intro a
    have hc := Q.rotation_agreement (J a)
    rw [hrot] at hc
    refine ⟨Set.toFinite _, rfl, ?_, ?_⟩
    · exact (hv _ _).mp (congrArg Subtype.val hc.2.2.1)
    · rcases hc.2.2.2 with hsingle | ⟨hne, hmin⟩
      · left
        refine ⟨hi (congrArg Subtype.val hsingle.1), ?_⟩
        ext b
        constructor
        · intro hb
          have hbQ : J b ∈ {e | restrictedVertex G S e = restrictedVertex G S (J a)} :=
            Subtype.ext ((hv b a).mpr hb)
          rw [hsingle.2] at hbQ
          exact Set.mem_singleton_iff.mpr (hi (congrArg Subtype.val (Set.mem_singleton_iff.mp hbQ)))
        · intro hb
          exact (Set.mem_singleton_iff.mp hb) ▸ rfl
      · right
        refine ⟨fun h => hne (congrArg J h), ?_⟩
        intro b hb hba
        exact hmin (J b) (Subtype.ext ((hv b a).mpr hb))
          (fun h => hba (hi (congrArg Subtype.val h)))

/-- Helper toward Proposition 3.9: restriction retains every labeled position. -/
theorem uibotWholePlaneStageDrawing_pos
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ)
    (v : Fin (kmswStage (shiftedStream W N) m).nextVertex) :
    (uibotWholePlaneStageDrawing W H G N m).pos v =
      G.pos (wholePlaneVertexι W N v.val) := rfl

/-- Helper toward Proposition 3.9: restriction retains the entire ordered polyline. -/
theorem uibotWholePlaneStageDrawing_arc
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ)
    (d : StageDart (kmswStage (shiftedStream W N) m).nextEdge) :
    (uibotWholePlaneStageDrawing W H G N m).arc d =
      G.arc (wholePlaneDartι W N (d.1.val, d.2)) := rfl

/-- Helper toward Proposition 3.9: a finite shifted code window inherits
an actual drawing from the complete finite stage. Every vertex and polyline
is the original one selected by the injective KMSW window maps. -/
@[expose] def uibotFiniteWindowStageDrawing (w : ℕ → Fin 3) (s m : ℕ)
    (P : StageDrawing w (s + m)) : StageDrawing (fun i => w (s + i)) m := by
  let u := fun i => w (s + i)
  let I := kmswWindowDartMap w s m
  let V : Fin (kmswStage u m).nextVertex → Fin (kmswStage w (s + m)).nextVertex :=
    fun v => ⟨kmswWindowPatchVertexMap w s m v.val,
      (kmswWindowPatchVertexMap_rel w s m).vertex_bound v.val v.isLt⟩
  have hi := kmswWindowDartMap_injective w s m
  have hvi : Function.Injective V := by
    intro a b he
    apply Fin.ext
    exact kmswWindowPatchVertexMap_injOn w s m a.isLt b.isLt (congrArg Fin.val he)
  have hend (a) : stageVertex w (s + m) (I a) = V (stageVertex u m a) := by
    apply Fin.ext
    cases hb : a.2
    · simpa only [stageVertex, stageEndpoint, I, kmswWindowDartMap, V, hb,
        Bool.false_eq_true, ite_false] using
        ((kmswWindowPatchVertexMap_rel w s m).west_endpoint a.1.val a.1.isLt).symm
    · simpa only [stageVertex, stageEndpoint, I, kmswWindowDartMap, V, hb, ite_true] using
        ((kmswWindowPatchVertexMap_rel w s m).east_endpoint a.1.val a.1.isLt).symm
  let S := range I
  have hs : ∀ d, d ∈ S ↔ edgeFlip _ d ∈ S := by
    intro d
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨edgeFlip _ a, rfl⟩
    · rintro ⟨a, ha⟩
      refine ⟨edgeFlip _ a, ?_⟩
      change edgeFlip _ (I a) = d
      rw [ha, P.flip_involutive]
  let Q := restrictDrawing P S hs
  let J : StageDart (kmswStage u m).nextEdge → S := fun a => ⟨I a, ⟨a, rfl⟩⟩
  have hrot (a) : drawingFirstReturnPerm P S (J a) = J (stageRot u m a) := by
    apply Subtype.ext
    apply uibotDrawing_firstReturn_of_inverse_scan P (stageRot u m) I
    intro d
    obtain ⟨k, hk, he, hg⟩ := kmswWindowDartMap_symm_firstReturn w s m d
    refine ⟨k, hk, ?_, ?_⟩
    · rw [permIterateEqPow]; exact he
    · intro j hj hjk
      rw [permIterateEqPow]
      exact hg j hj hjk
  have hv (a b) : stageVertex w (s + m) (I a) = stageVertex w (s + m) (I b) ↔
      stageVertex u m a = stageVertex u m b := by
    rw [hend, hend]
    exact hvi.eq_iff
  refine {
    flip_involutive := (kmswMap u m).edgeInv_invol
    flip_ne := (kmswMap u m).edgeInv_ne
    vert_rotation := ?_
    pos := fun v => P.pos (V v)
    pos_injective := P.pos_injective.comp hvi
    arc := fun a => P.arc (I a)
    arc_simple := fun a => P.arc_simple (I a)
    arc_length := fun a => P.arc_length (I a)
    arc_start := fun a => (P.arc_start (I a)).trans (congrArg P.pos (hend a))
    arc_finish := fun a => (P.arc_finish (I a)).trans (congrArg P.pos (hend (edgeFlip _ a)))
    arc_flip := fun a => P.arc_flip (I a)
    interior_disjoint := ?_
    interior_avoids_vertices := fun a v => P.interior_avoids_vertices (I a) (V v)
    locally_finite := fun _ _ => Set.toFinite _
    initial_nonzero := fun a => P.initial_nonzero (I a)
    initial_arg_injective := ?_
    rotation_agreement := ?_ }
  · intro a
    apply Fin.ext
    exact (stageRot_sameCycle_iff_endpoint_eq u m _ _).mp
      Equiv.Perm.SameCycle.rfl.apply_right |>.symm
  · intro a b hba hbf
    apply P.interior_disjoint
    · exact fun h => hba (hi h)
    · exact fun h => hbf (hi h)
  · intro a b hab he
    apply hi
    exact P.initial_arg_injective _ _ ((hv a b).mpr hab) he
  · intro a
    have hc := Q.rotation_agreement (J a)
    rw [hrot] at hc
    refine ⟨Set.toFinite _, rfl, ?_, ?_⟩
    · exact (hv _ _).mp (congrArg Subtype.val hc.2.2.1)
    · rcases hc.2.2.2 with hsingle | ⟨hne, hmin⟩
      · left
        refine ⟨hi (congrArg Subtype.val hsingle.1), ?_⟩
        ext b
        constructor
        · intro hb
          have hbQ : J b ∈ {e | restrictedVertex P S e = restrictedVertex P S (J a)} :=
            Subtype.ext ((hv b a).mpr hb)
          rw [hsingle.2] at hbQ
          exact Set.mem_singleton_iff.mpr (hi (congrArg Subtype.val (Set.mem_singleton_iff.mp hbQ)))
        · intro hb
          exact (Set.mem_singleton_iff.mp hb) ▸ rfl
      · right
        refine ⟨fun h => hne (congrArg J h), ?_⟩
        intro b hb hba
        exact hmin (J b) (Subtype.ext ((hv b a).mpr hb))
          (fun h => hba (hi (congrArg Subtype.val h)))

/-- Helper toward Proposition 3.9: finite-window restriction preserves
the original vertex at the KMSW patch label. -/
theorem uibotFiniteWindowStageDrawing_pos (w : ℕ → Fin 3) (s m : ℕ)
    (P : StageDrawing w (s + m)) (v : Fin (kmswStage (fun i => w (s + i)) m).nextVertex) :
    (uibotFiniteWindowStageDrawing w s m P).pos v =
      P.pos ⟨kmswWindowPatchVertexMap w s m v.val,
        (kmswWindowPatchVertexMap_rel w s m).vertex_bound v.val v.isLt⟩ := rfl

/-- Helper toward Proposition 3.9: finite-window restriction preserves
the complete ordered polyline at the KMSW patch dart. -/
theorem uibotFiniteWindowStageDrawing_arc (w : ℕ → Fin 3) (s m : ℕ)
    (P : StageDrawing w (s + m))
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge) :
    (uibotFiniteWindowStageDrawing w s m P).arc d = P.arc (kmswWindowDartMap w s m d) := rfl

end DirectedDistances.PaperProofs.Section3
end
