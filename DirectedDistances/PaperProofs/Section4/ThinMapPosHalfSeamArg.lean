module

public import DirectedDistances.PaperProofs.Section4.ThinMapPosHalfSeamSeed
public import DirectedDistances.PaperProofs.Section4.ThinIndRenewalProvider
import DirectedDistances.KMSW.OutgoingOrderDrawing
import DirectedDistances.KMSW.StageInfiniteOutgoingOrderSource

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver Set
open DirectedDistances.Paper.Section4
open scoped Classical Topology

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_map_eraseDups {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (l : List α) :
    l.eraseDups.map f = (l.map f).eraseDups := by
  suffices h : ∀ n : ℕ, ∀ l : List α, l.length = n →
      l.eraseDups.map f = (l.map f).eraseDups by exact h l.length l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hl
    cases l with
    | nil => rfl
    | cons a t =>
      rw [List.eraseDups_cons]
      simp only [List.map_cons]
      rw [List.eraseDups_cons]
      congr 1
      rw [ih _ (by
        have := List.length_filter_le (fun b => !(b == a)) t
        simp only [List.length_cons] at hl
        omega) _ rfl]
      congr 1
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro b _
      by_cases h : b = a
      · simp only [h, Function.comp_apply, beq_self_eq_true]
      · have h' : f b ≠ f a := fun he => h (hf he)
        simp only [Function.comp_apply, beq_eq_false_iff_ne.mpr h,
          beq_eq_false_iff_ne.mpr h']

section StageOrder

variable {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
  (B : BipolarTriangulationWithBoundaryBase D ℓ r)
  (w : ℕ → Fin 3) (t : ℕ)
  (I : DirectedMapWithMissingIso B.map (kmswStageDirectedMap w t))

include I

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_rot_symm (d : D) :
    I.toEquiv (B.map.rot.symm d) = (stageRot w t).symm (I.toEquiv d) := by
  apply (stageRot w t).injective
  change (kmswStageDirectedMap w t).rot (I.toEquiv (B.map.rot.symm d)) =
    (kmswStageDirectedMap w t).rot
      ((kmswStageDirectedMap w t).rot.symm (I.toEquiv d))
  rw [← I.rot_comm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_rot_pow (j : ℕ) (d : D) :
    I.toEquiv ((B.map.rot.symm ^ j) d) =
      ((stageRot w t).symm ^ j) (I.toEquiv d) := by
  induction j generalizing d with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
    exact (ih _).trans (congrArg _ (seam_rot_symm B w t I d))

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_rot_order : orderOf B.map.rot.symm = orderOf (stageRot w t).symm := by
  apply orderOf_eq_orderOf_iff.mpr
  intro j
  constructor
  · intro h
    apply Equiv.ext
    intro d
    have hh := seam_rot_pow B w t I j (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply, h] at hh
    simpa only [Equiv.Perm.one_apply, Equiv.apply_symm_apply] using hh.symm
  · intro h
    apply Equiv.ext
    intro d
    have hh := seam_rot_pow B w t I j d
    rw [h] at hh
    exact I.toEquiv.injective hh

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_tailVertex_iff (d e : D) :
    dartTailVertex B.map d = dartTailVertex B.map e ↔
      stageEndpoint (kmswStage w t) (I.toEquiv d) =
        stageEndpoint (kmswStage w t) (I.toEquiv e) := by
  constructor
  · intro h
    exact congrArg (fun v => (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id) h
  · intro h
    apply (cutMapIsoVertexEquiv I).injective
    apply stageMapVertex_injective w t
    exact congrArg StagePresentVertex.mk h

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The entire finite canonical list transports to the exact stage scan. -/
private theorem seam_canonicalOutgoingOrder_map_stage (v : MapVertex B.map) (hv : v ≠ B.sink) :
    (canonicalOutgoingOrder B v hv).map I.toEquiv =
      stageOutgoingDartOrder w t (I.toEquiv (leftmostOutgoing B v hv)) := by
  have hscan : (finiteRotationScan B (leftmostOutgoing B v hv)).map I.toEquiv =
      List.ofFn (fun j : Fin (orderOf (stageRot w t).symm) =>
        ((stageRot w t).symm ^ j.val) (I.toEquiv (leftmostOutgoing B v hv))) := by
    unfold finiteRotationScan
    rw [List.map_ofFn, ← seam_rot_order B w t I]
    congr 1
    funext j
    exact seam_rot_pow B w t I j.val _
  unfold canonicalOutgoingOrder stageOutgoingDartOrder
  rw [seam_map_eraseDups I.toEquiv I.toEquiv.injective]
  congr 1
  unfold finiteOutgoingRotationOrder
  rw [← hscan, List.filter_map]
  congr 1
  apply List.filter_congr
  intro d _
  apply Bool.decide_congr
  exact and_congr (seam_tailVertex_iff B w t I d _) (I.tail_iff d).symm

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
There are no missing darts in the finite representative or its stage image. -/
private theorem seam_stage_tail_iff (d : D) : B.map.tail d ↔ (I.toEquiv d).2 = false := by
  have hm := fun h => B.noMissingDarts d ((I.missing_iff d).mp h)
  have hp : (kmswStage w t).present (I.toEquiv d).1.val = true := by
    cases h : (kmswStage w t).present (I.toEquiv d).1.val
    · exact (hm h).elim
    · rfl
  rw [← I.tail_iff d]
  change (_ ∧ _) ↔ _
  rw [hp]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The internal canonical anchor is the outgoing end of an incoming-block cut. -/
private theorem seam_internal_anchor_kind (v : MapVertex B.map)
    (hs : v ≠ B.source) (ht : v ≠ B.sink) :
    (I.toEquiv (leftmostOutgoing B v ht)).2 = false ∧
      (stageRot w t (I.toEquiv (leftmostOutgoing B v ht))).2 = true := by
  have hc := leftmostOutgoing_internal_characterization B v hs ht
  refine ⟨(seam_stage_tail_iff B w t I _).mp hc.2.1, ?_⟩
  have hn : ¬ (I.toEquiv (B.map.rot (leftmostOutgoing B v ht))).2 = false :=
    fun h => hc.2.2.1 ((seam_stage_tail_iff B w t I _).mpr h)
  rw [I.rot_comm] at hn
  exact Bool.eq_true_of_not_eq_false hn

omit B I in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_LR_head : (kmswStage w t).LR.head? = some 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (kmswStepOfStep (kmswStage w t) (kmswCodeStep (w t))).LR.head? = _
    cases kmswCodeStep (w t) with
    | up => exact ih
    | left =>
      simp only [kmswStepOfStep]
      split <;> exact ih
    | down =>
      simp only [kmswStepOfStep]
      split
      · exact ih
      · change ((kmswStage w t).LR ++ [(kmswStage w t).nextEdge]).head? = _
        simpa only [List.head?_append_of_ne_nil _ (kmswStage_LR_nonempty w t)] using ih

omit B I in
/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/
private theorem seam_stage_source_endpoint (hL : ∀ j, 0 ≤ L w j) :
    stageEndpoint (kmswStage w t) (stageULHeadDart w t) = 0 := by
  have hs := (kmswStage_boundary_chain_invariant w t).2.2.1
  have hUL := (kmswStage_UL_nonempty_active_last w t).1
  rw [kmswStage_LL_eq_nil w hL t, List.nil_append] at hs
  have hu := List.head?_eq_some_head hUL
  simp only [boundaryStart, List.head?_append_of_ne_nil _ hUL, hu,
    seam_LR_head w t, Option.map_some] at hs
  exact (Option.some.inj hs).trans (initial_edge_endpoints w t).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The image of the source left-boundary corner is the exact stage source corner. -/
private theorem seam_source_anchor (hL : ∀ j, 0 ≤ L w j)
    (hroot : (stageMapVertex w t (cutMapIsoVertexEquiv I B.source)).id = 0) :
    I.toEquiv (leftmostOutgoing B B.source (bipolar_source_ne_sink B)) =
      stageULHeadDart w t := by
  let c := leftmostOutgoing B B.source (bipolar_source_ne_sink B)
  have hc := canonicalLeftmostOutgoing_spec B B.source (bipolar_source_ne_sink B)
  have hout : B.map.IsOuter c := by
    apply B.outerSplit.1.1 c
    apply B.outerSplit.2.1.mem_iff.mpr
    simp only [List.append_nil, List.mem_append]
    left
    dsimp only [c]
    rw [leftmostOutgoing_source_eq_firstLeftDart]
    exact List.get_mem B.leftPath.darts _
  have hul : (I.toEquiv c).1.val ∈ (kmswStage w t).UL := by
    have hmem : I.toEquiv c ∈ (kmswStageDirectedMap w t).ulDarts :=
      ⟨fun h => B.noMissingDarts c ((I.missing_iff c).mp h),
        (I.tail_iff c).mpr hc.2, (I.outer_iff c).mpr hout⟩
    exact ((kmswStageULDartsFinset_mem w t _).mp
      ((kmswStageULDartsFinset_map_mem w t _).mpr hmem)).2
  have hb : (I.toEquiv c).2 = false := (seam_stage_tail_iff B w t I c).mp hc.2
  have hw : (kmswStage w t).west (I.toEquiv c).1.val = 0 := by
    have hh := congrArg (fun v => (stageMapVertex w t (cutMapIsoVertexEquiv I v)).id)
      hc.1
    change stageEndpoint (kmswStage w t) (I.toEquiv c) = _ at hh
    simpa only [stageEndpoint, hb, Bool.false_eq_true, ite_false, hroot] using hh
  have hhead : (stageULHeadDart w t).1.val ∈ (kmswStage w t).UL :=
    List.head_mem (kmswStage_UL_nonempty_active_last w t).1
  have he : (I.toEquiv c).1.val = (stageULHeadDart w t).1.val := by
    apply List.inj_on_of_nodup_map (CutConverse.westStack_nodup w t)
      (List.mem_reverse.mpr hul) (List.mem_reverse.mpr hhead)
    exact hw.trans (seam_stage_source_endpoint w t hL).symm
  exact Prod.ext (Fin.ext he) hb

end StageOrder

section DrawingOrder

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z)

include hL htrans hRneg

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Source and incoming-block stage scans have decreasing initial arguments. -/
private theorem seam_stageOutgoing_arg_pairwise (t : ℕ)
    (c : StageDart (kmswStage w t).nextEdge)
    (hc : c = stageULHeadDart w t ∨ c.2 = false ∧ (stageRot w t c).2 = true) :
    (stageOutgoingEdgeOrder w t c).Pairwise (fun e f =>
      Complex.arg ((G).arc (f, false)).initialDirection <
        Complex.arg ((G).arc (e, false)).initialDirection) := by
  rw [stageOutgoingEdgeOrder_eq_infinite_filter_of_kind w hfin hL htrans hRneg t c hc]
  exact (kmswOutgoingEdgesLeftToRight_arg_pairwise w hfin
    (fun n => ⟨monotoneLayoutDrawing w n ((monotone_family_all w) n).choose,
      ((monotone_family_all w) n).choose_spec⟩) hL htrans hRneg _ _).filter _

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Canonical finite order has decreasing arguments whenever its source has permanent ID zero. -/
private theorem seam_canonicalOutgoing_arg_pairwise
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (t : ℕ)
    (I : DirectedMapWithMissingIso B.map (kmswStageDirectedMap w t))
    (hroot : (stageMapVertex w t (cutMapIsoVertexEquiv I B.source)).id = 0)
    (v : MapVertex B.map) (hv : v ≠ B.sink) :
    (canonicalOutgoingOrder B v hv).Pairwise (fun d e =>
      Complex.arg ((G).arc ((I.toEquiv e).1.val, false)).initialDirection <
        Complex.arg ((G).arc ((I.toEquiv d).1.val, false)).initialDirection) := by
  have hkind : I.toEquiv (leftmostOutgoing B v hv) = stageULHeadDart w t ∨
      (I.toEquiv (leftmostOutgoing B v hv)).2 = false ∧
        (stageRot w t (I.toEquiv (leftmostOutgoing B v hv))).2 = true := by
    by_cases hs : v = B.source
    · subst v
      exact Or.inl (seam_source_anchor B w t I hL hroot)
    · exact Or.inr (seam_internal_anchor_kind B w t I v hs hv)
  have hh := seam_stageOutgoing_arg_pairwise w hfin hL htrans hRneg t
    (I.toEquiv (leftmostOutgoing B v hv)) hkind
  unfold stageOutgoingEdgeOrder at hh
  rw [← seam_canonicalOutgoingOrder_map_stage B w t I v hv,
    List.map_map, List.pairwise_map] at hh
  exact hh

end DrawingOrder

section SeamOrder

variable {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  (t : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
    (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))

include hp

local notation "G" => monotoneFamilyDrawing w hfin (monotone_family_all w)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both finite half sectors transfer to strict argument order at every seam index.
This includes zero and every positive index with no launch-order premise. -/
theorem ancestorPos_seamLaunch_argumentOrder (a : ThinMapSide) (i : Fin m) :
    AncestorPosHalfSeamLaunchArgumentOrderAt w hfin hL htrans hRneg P t R hR I a i := by
  intro d ht hoff _ hi
  let Q := selectedGeodesicOfLen R.B x hR
  let v := Q.vertices.get ⟨i.val, by rw [Q.vertices_length]; omega⟩
  have hvs : v ≠ R.B.sink := simplePath_vertex_ne_end Q i.val i.isLt
  let O := canonicalOutgoingOrder R.B v hvs
  let p := Q.darts.get ⟨i.val, by rw [Q.darts_length]; exact i.isLt⟩
  let e := ancestorPosDartMap R hR a d
  have hroot := ancestorPos_source_id_of_prefix w P t R hR I hp .left
  change (stageMapVertex w t (cutMapIsoVertexEquiv I
    (ancestorPosVertexMap R hR .left (ancestorPosHalfRep R hR .left).B.source))).id = 0
      at hroot
  rw [ancestorPos_source_map] at hroot
  have hpair := seam_canonicalOutgoing_arg_pairwise
    w hfin hL htrans hRneg R.B t I hroot v hvs
  change O.Pairwise _ at hpair
  have he : e ∈ O := by
    apply (mem_canonicalOutgoingOrder_iff R.B v hvs e).mpr
    refine ⟨ancestorPos_seamLaunch_tailVertex w P t R hR I hp a d ht i hi, ?_⟩
    exact (seam_stage_tail_iff R.B w t I e).mpr
      ((ancestorPos_ids_oriented w t R hR I a d).mp ht).2
  have hpmem : p ∈ O :=
    (mem_canonicalOutgoingOrder_iff R.B v hvs p).mpr
      ⟨(Q.edge_step _).2.2.1.symm, (Q.edge_step _).2.1⟩
  have hsector := ancestorPos_seamLaunch_finite_sector w P t R hR I hp a d ht hoff i hi
  have hid := ancestorPos_prefixDart_id w P t R hR I hp i
  have hfwd : ∀ {b c : Fin R.dartCount}, b ∈ O → c ∈ O → O.idxOf b < O.idxOf c →
      Complex.arg ((G).arc ((I.toEquiv c).1.val, false)).initialDirection <
        Complex.arg ((G).arc ((I.toEquiv b).1.val, false)).initialDirection := by
    intro b c hb hc hbc
    have hh := List.pairwise_iff_getElem.mp hpair (O.idxOf b) (O.idxOf c)
      (List.idxOf_lt_length_of_mem hb) (List.idxOf_lt_length_of_mem hc) hbc
    simpa only [List.getElem_idxOf] using hh
  cases a with
  | left =>
    have hh := hfwd he hpmem hsector
    simpa only [e, p, Q, hid, ancestorPosDartId, stageLimitDart,
      Function.Embedding.coeFn_mk] using hh
  | right =>
    have hh := hfwd hpmem he hsector
    simpa only [e, p, Q, hid, ancestorPosDartId, stageLimitDart,
      Function.Embedding.coeFn_mk] using hh

end SeamOrder

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite cut restrictions realize the source ancestor maps unconditionally. -/
theorem sourceAncestorCutRealization_holds (x : XDP)
    (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    SourceAncestorCutRealization x T hT := by
  apply sourceAncestorCutRealization_of_boundaryLaunch x T hT
  apply (sourceAncestorCut_boundaryLaunch_iff_seamLaunch x T hT).mpr
  intro q k
  dsimp only
  intro ℓ r n m R hR I hp a
  apply (ancestorPos_seamLaunch_iff_argumentOrder _ _ _ _ _ _ _ R hR I hp a).mpr
  intro i
  exact ancestorPos_seamLaunch_argumentOrder _ _ _ _ _ _ _ R hR I hp a i

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical renewal times give the same unconditional ancestor realization. -/
theorem sourceAncestorCutRealization_renewal (x : XDP) :
    SourceAncestorCutRealization x renewalTime renewalTime_positiveSuccessTime :=
  sourceAncestorCutRealization_holds x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The canonical renewal side codes have geometric fidelity. -/
theorem thinSideCodeGeometricFidelity_renewal (x : XDP) :
    ThinSideCodeGeometricFidelity x renewalTime renewalTime_positiveSuccessTime :=
  thinSideCodeGeometricFidelity_renewal_of_realization x
    (sourceAncestorCutRealization_renewal x)

end DirectedDistances.PaperProofs.Section4
