module

public import DirectedDistances.KMSW.KMSWWholePlaneColimit
public import DirectedDistances.KMSW.InfiniteRotation
import DirectedDistances.KMSW.KMSWWindowFreshOuterRotation

/-! Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
one-sided limiting rotation along the whole-plane transition maps at fresh vertices and its
eventual constancy under an explicit deterministic hypothesis on the word (to be discharged
a.s. separately); the whole-plane rotation itself, faces, β_0^{L,R}, the cut and the source
identification (Q-F4c, unanswered) are not treated; not the paper result. -/

public section
namespace DirectedDistances.KMSW

/-- Finite geometric incidence for the helper toward F4c -/
@[expose] def KMSWFiniteIncidence (w : ℕ → Fin 3) : Prop :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite

/-- Freshness under a whole-plane transition, toward F4c -/
@[expose] def wholePlaneFresh (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (v : ℕ) : Prop :=
  (kmswStage (shiftedStream W N') (N' - N)).nextVertex ≤
    wholePlaneVertexTrans W N N' h v

/-- Explicit deterministic gate for the helper toward F4c -/
@[expose] def WholePlaneRotationHypothesis (W : ℤ → Fin 3) : Prop :=
  (∀ N, KMSWFiniteIncidence (shiftedStream W N)) ∧
  (∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v))

/-- Dart transition preserving the side bit, toward F4c -/
@[expose] def wholePlaneDartTrans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (d : ℕ × Bool) : ℕ × Bool :=
  (wholePlaneEdgeTrans W N N' h d.1, d.2)

/-- Identity dart transition, toward F4c -/
theorem wholePlaneDartTrans_self (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneDartTrans W N N (Nat.le_refl N) = id := by
  funext d
  exact Prod.ext (congrFun (wholePlaneEdgeTrans_self W N) d.1) rfl

/-- Functorial dart transitions, toward F4c -/
theorem wholePlaneDartTrans_comp (W : ℤ → Fin 3) (N N' N'' : ℕ)
    (h : N ≤ N') (h' : N' ≤ N'') :
    wholePlaneDartTrans W N' N'' h' ∘ wholePlaneDartTrans W N N' h =
      wholePlaneDartTrans W N N'' (h.trans h') := by
  funext d
  exact Prod.ext (congrFun (wholePlaneEdgeTrans_comp W N N' N'' h h') d.1) rfl

private def dartBase (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem stageEndpoint_eq_base (w : ℕ → Fin 3) (n : ℕ)
    (x : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) x = dartBase w (x.1.val, x.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w x.1.isLt
  cases hb : x.2 <;>
    simp only [stageEndpoint, dartBase, hb, Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem infRot_base (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (d : ℕ × Bool) :
    dartBase w (kmswInfRot w hfin d) = dartBase w d := by
  obtain ⟨n, hn⟩ := kmswInfRot_eventually_eq_stage w hfin d
  obtain ⟨hd, he⟩ := hn n (Nat.le_refl n)
  let x : StageDart (kmswStage w n).nextEdge := (⟨d.1, hd⟩, d.2)
  rw [he, ← stageEndpoint_eq_base w n (stageRot w n x),
    ← stageEndpoint_eq_base w n x]
  exact ((stageRot_sameCycle_iff_endpoint_eq w n x (stageRot w n x)).mp
    ⟨1, rfl⟩).symm

private theorem windowInfRot_trans_of_fresh (w : ℕ → Fin 3) (s : ℕ)
    (hu : KMSWFiniteIncidence (fun i => w (s + i))) (hw : KMSWFiniteIncidence w)
    (v : ℕ) (hf : (kmswStage w s).nextVertex ≤ kmswWindowVertexMapInf w s v)
    (d : ℕ × Bool) (hd : dartBase (fun i => w (s + i)) d = v) :
    (kmswWindowEdgeMapInf w s (kmswInfRot (fun i => w (s + i)) hu d).1,
      (kmswInfRot (fun i => w (s + i)) hu d).2) =
      kmswInfRot w hw (kmswWindowEdgeMapInf w s d.1, d.2) := by
  let u := fun i => w (s + i)
  obtain ⟨a, ha⟩ := kmswInfRot_eventually_eq_stage u hu d
  obtain ⟨b, hb⟩ := kmswInfRot_eventually_eq_stage w hw
    (kmswWindowEdgeMapInf w s d.1, d.2)
  let m := max a b
  obtain ⟨hedge, hsrc⟩ := ha m (Nat.le_max_left a b)
  obtain ⟨himage, htgt⟩ := hb (s + m) (by dsimp [m]; omega)
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hedge⟩, d.2)
  have hx : stageEndpoint (kmswStage u m) x = v :=
    (stageEndpoint_eq_base u m x).trans hd
  have hv : v < (kmswStage u m).nextVertex := by
    have he := kmswStage_endpoints_lt_nextVertex u m d.1 hedge
    rw [← hx]
    cases hside : d.2 <;> simp only [stageEndpoint, x, hside,
      Bool.false_eq_true, ↓reduceIte] <;> tauto
  have hf' : (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    rw [← kmswWindowVertexMapInf_eq_stage w s m v hv]
    exact hf
  have hrot := kmswWindowDartMap_rot_of_fresh w s m v hv hf' x hx
  simp only [kmswMap_rot] at hrot
  have hmap : kmswWindowDartMap w s m x =
      (⟨kmswWindowEdgeMapInf w s d.1, himage⟩, d.2) := by
    apply Prod.ext
    · apply Fin.ext
      exact (kmswWindowEdgeMapInf_eq_stage w s m d.1 hedge).symm
    · rfl
  rw [hsrc]
  have hout := kmswWindowEdgeMapInf_eq_stage w s m
    (stageRot u m x).1.val (stageRot u m x).1.isLt
  change (kmswWindowEdgeMapInf w s (stageRot u m x).1.val,
    (stageRot u m x).2) = _
  rw [hout]
  change ((kmswWindowDartMap w s m (stageRot u m x)).1.val,
    (kmswWindowDartMap w s m (stageRot u m x)).2) = _
  rw [← hrot, hmap]
  exact htgt.symm

/-- Limiting rotation transports at the base vertex alone, toward F4c
No freshness condition on the other endpoint is needed; not the paper result. -/
theorem wholePlaneInfRot_trans_of_fresh
    (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (hN : KMSWFiniteIncidence (shiftedStream W N))
    (hN' : KMSWFiniteIncidence (shiftedStream W N'))
    (v : ℕ) (hf : wholePlaneFresh W N N' h v) (d : ℕ × Bool)
    (hd : (if d.2 then edgeEast (shiftedStream W N) d.1
      else edgeWest (shiftedStream W N) d.1) = v) :
    wholePlaneDartTrans W N N' h (kmswInfRot (shiftedStream W N) hN d) =
      kmswInfRot (shiftedStream W N') hN' (wholePlaneDartTrans W N N' h d) := by
  have hu : KMSWFiniteIncidence
      (fun i => shiftedStream W N' ((N' - N) + i)) := by
    rw [shiftedStream_shift W N N' h]
    exact hN
  have hd' : dartBase (fun i => shiftedStream W N' ((N' - N) + i)) d = v := by
    rw [shiftedStream_shift W N N' h]
    exact hd
  simpa only [wholePlaneDartTrans, wholePlaneEdgeTrans, shiftedStream_shift W N N' h]
    using windowInfRot_trans_of_fresh (shiftedStream W N') (N' - N) hu hN' v hf d hd'

/-- Inverse limiting rotation transports at the same fresh base vertex, toward F4c -/
theorem wholePlaneInfRot_symm_trans_of_fresh
    (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (hN : KMSWFiniteIncidence (shiftedStream W N))
    (hN' : KMSWFiniteIncidence (shiftedStream W N'))
    (v : ℕ) (hf : wholePlaneFresh W N N' h v) (d : ℕ × Bool)
    (hd : (if d.2 then edgeEast (shiftedStream W N) d.1
      else edgeWest (shiftedStream W N) d.1) = v) :
    wholePlaneDartTrans W N N' h ((kmswInfRot (shiftedStream W N) hN).symm d) =
      (kmswInfRot (shiftedStream W N') hN').symm
        (wholePlaneDartTrans W N N' h d) := by
  let r := kmswInfRot (shiftedStream W N) hN
  have he : dartBase (shiftedStream W N) (r.symm d) = v := by
    have he := infRot_base (shiftedStream W N) hN (r.symm d)
    change dartBase (shiftedStream W N) (r (r.symm d)) = _ at he
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans hd
  apply (kmswInfRot (shiftedStream W N') hN').injective
  rw [Equiv.apply_symm_apply]
  have hr := wholePlaneInfRot_trans_of_fresh W N N' h hN hN' v hf (r.symm d) he
  change wholePlaneDartTrans W N N' h (r (r.symm d)) = _ at hr
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Canonical geometric dart map to the colimit, toward F4c -/
@[expose] def wholePlaneDartι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneEdge W × Bool :=
  (wholePlaneEdgeι W N d.1, d.2)

/-- Colimit dart maps commute with transitions, toward F4c -/
theorem wholePlaneDartι_trans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    wholePlaneDartι W N' ∘ wholePlaneDartTrans W N N' h = wholePlaneDartι W N := by
  funext d
  exact Prod.ext (congrFun (wholePlaneEdgeι_trans W N N' h) d.1) rfl

private theorem dartTrans_base (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (d : ℕ × Bool) :
    dartBase (shiftedStream W N') (wholePlaneDartTrans W N N' h d) =
      wholePlaneVertexTrans W N N' h (dartBase (shiftedStream W N) d) := by
  cases hb : d.2 <;> simp only [dartBase, wholePlaneDartTrans, hb,
    Bool.false_eq_true, ↓reduceIte]
  · exact wholePlaneEdgeTrans_west W N N' h d.1
  · exact wholePlaneEdgeTrans_east W N N' h d.1




theorem wholePlaneInfRot_eventually_constant (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) :
    ∃ M, ∃ hNM : N ≤ M, ∃ y : WholePlaneEdge W × Bool,
      ∀ M' (hMM' : M ≤ M'),
        wholePlaneDartι W M' (kmswInfRot (shiftedStream W M') (H.1 M')
          (wholePlaneDartTrans W N M' (hNM.trans hMM') d)) = y := by
  obtain ⟨M, hNM, hf⟩ := H.2 N (dartBase (shiftedStream W N) d)
  let e := wholePlaneDartTrans W N M hNM d
  refine ⟨M, hNM, wholePlaneDartι W M (kmswInfRot (shiftedStream W M) (H.1 M) e), ?_⟩
  intro M' hMM'
  have he := dartTrans_base W N M hNM d
  have hr := wholePlaneInfRot_trans_of_fresh W M M' hMM' (H.1 M) (H.1 M')
    (wholePlaneVertexTrans W N M hNM (dartBase (shiftedStream W N) d))
    (hf M' hMM') e he
  have hc := congrFun (wholePlaneDartTrans_comp W N M M' hNM hMM') d
  change wholePlaneDartTrans W M M' hMM' e =
    wholePlaneDartTrans W N M' (hNM.trans hMM') d at hc
  rw [← hc, ← hr]
  exact congrFun (wholePlaneDartι_trans W M M' hMM')
    (kmswInfRot (shiftedStream W M) (H.1 M) e)

end DirectedDistances.KMSW
