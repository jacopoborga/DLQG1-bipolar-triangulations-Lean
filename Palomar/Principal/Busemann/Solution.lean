module
public import Palomar.Principal.Support.BusemannSource

public section
section BusemannInterface
set_option bootstrap.genMatcherCode false
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
section StageRotationView
@[expose] def stageRot (w : ℕ → Fin 3) :
    (n : ℕ) → Equiv.Perm (StageDart (kmswStage w n).nextEdge)
  | 0 => 1
  | n + 1 => StageRotation.step (kmswStage w n)
      (act_lt_nextEdge w (le_refl n)) (stageRotation_UL_bound w n) (stageRot w n) (w n)
theorem stageRot_eq_source (w : ℕ → Fin 3) (n : ℕ) :
    stageRot w n = DirectedDistances.KMSW.stageRot w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stageRot, DirectedDistances.KMSW.stageRot, ih]
    rfl

variable (w : ℕ → Fin 3) (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
include hfin in
theorem kmswInfRot_existsUnique :
    ∃! σ : Equiv.Perm (ℕ × Bool),
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ (x.1.val, x.2) = ((stageRot w n x).1.val, (stageRot w n x).2)) ∧
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        σ.symm (x.1.val, x.2) =
          (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) := by
  simpa only [stageRot_eq_source] using DirectedDistances.KMSW.kmswInfRot_existsUnique w hfin
@[expose] noncomputable def kmswInfRot : Equiv.Perm (ℕ × Bool) :=
  (kmswInfRot_existsUnique w hfin).exists.choose
theorem kmswInfRot_eq_source : kmswInfRot w hfin = DirectedDistances.KMSW.kmswInfRot w hfin := by
  apply (DirectedDistances.KMSW.kmswInfRot_existsUnique w hfin).unique
  · have he := (kmswInfRot_existsUnique w hfin).exists.choose_spec
    change
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        kmswInfRot w hfin (x.1.val, x.2) = ((stageRot w n x).1.val, (stageRot w n x).2)) ∧
      (∀ n (x : StageDart (kmswStage w n).nextEdge),
        kmswVertexComplete w n (stageEndpoint (kmswStage w n) x) →
        (kmswInfRot w hfin).symm (x.1.val, x.2) =
          (((stageRot w n).symm x).1.val, ((stageRot w n).symm x).2)) at he
    simp only [stageRot_eq_source] at he
    exact he
  · exact (DirectedDistances.KMSW.kmswInfRot_existsUnique w hfin).exists.choose_spec

end StageRotationView
@[expose] def KMSWWindowPatchData.step (G F : State) (c : Step)
    (d : KMSWWindowPatchData) : KMSWWindowPatchData :=
  let alloc := fun e => if e < F.nextEdge then d.φ e else G.nextEdge + (e - F.nextEdge)
  match c with
  | .down => match F.UR with
    | _ :: _ => d
    | [] => match d.B with
      | [] => { d with φ := alloc, XR := d.XR ++ [F.nextEdge] }
      | q :: bs =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else q
          B := bs
          YR := d.YR ++ [F.nextEdge] }
  | .up => { d with φ := alloc }
  | .left => match F.UL.dropLast.reverse with
    | _ :: _ => { d with φ := alloc }
    | [] => match d.A.reverse with
      | [] => { d with φ := alloc, XL := (F.nextEdge + 1) :: d.XL }
      | q :: es =>
        { d with
          φ := fun e => if e < F.nextEdge then d.φ e else
            if e = F.nextEdge then G.nextEdge else q
          A := es.reverse
          YL := (F.nextEdge + 1) :: d.YL }
@[expose] def kmswWindowPatchData (w : ℕ → Fin 3) (s : ℕ) : ℕ → KMSWWindowPatchData
  | 0 => ⟨fun _ => (kmswStage w s).active,
      (kmswStage w s).UL.dropLast, (kmswStage w s).UR, [], [], [], []⟩
  | j + 1 => KMSWWindowPatchData.step (kmswStage w (s + j))
      (kmswStage (fun i => w (s + i)) j) (kmswCodeStep (w (s + j)))
      (kmswWindowPatchData w s j)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWindowPatchVertex
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def kmswWindowPatchVertexMap (w : ℕ → Fin 3) (s : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => fun v => if v = 0 then (kmswStage w s).west (kmswStage w s).active
      else (kmswStage w s).east (kmswStage w s).active
  | j + 1 =>
      let G := kmswStage w (s + j)
      let F := kmswStage (fun i => w (s + i)) j
      let d := kmswWindowPatchData w s j
      let ψ := kmswWindowPatchVertexMap w s j
      let extend := fun z v => if v < F.nextVertex then ψ v else z
      match kmswCodeStep (w (s + j)) with
      | .down => match F.UR with
        | _ :: _ => ψ
        | [] => match d.B with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.east q)
      | .up => extend G.nextVertex
      | .left => match F.UL.dropLast.reverse with
        | _ :: _ => ψ
        | [] => match d.A.reverse with
          | [] => extend G.nextVertex
          | q :: _ => extend (G.west q)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWindowInfiniteMaps
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def kmswWindowEdgeMapInf (w : ℕ → Fin 3) (s e : ℕ) : ℕ :=
  (kmswWindowPatchData w s e).φ e
@[expose] def kmswWindowVertexMapInf (w : ℕ → Fin 3) (s v : ℕ) : ℕ :=
  kmswWindowPatchVertexMap w s (4 * v + 1) v
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneColimit
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def shiftedStream (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 :=
  fun i => W ((i : ℤ) - N)
@[expose] def wholePlaneEdgeTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowEdgeMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneVertexTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowVertexMapInf (shiftedStream W N') (N' - N)
@[expose] def wholePlaneEdgeRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneEdgeTrans W a.1 M ha a.2 = wholePlaneEdgeTrans W b.1 M hb b.2
@[expose] def wholePlaneVertexRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneVertexTrans W a.1 M ha a.2 = wholePlaneVertexTrans W b.1 M hb b.2
theorem patchStep_eq_source (G F : State) (c : Step) (d : DirectedDistances.KMSW.KMSWWindowPatchData) :
    KMSWWindowPatchData.step G F c d = DirectedDistances.KMSW.KMSWWindowPatchData.step G F c d := by
  cases c <;> simp only [KMSWWindowPatchData.step,
    DirectedDistances.KMSW.KMSWWindowPatchData.step] <;> rfl

theorem patchData_eq_source (w : ℕ → Fin 3) (s : ℕ) :
    kmswWindowPatchData w s = DirectedDistances.KMSW.kmswWindowPatchData w s := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kmswWindowPatchData, DirectedDistances.KMSW.kmswWindowPatchData,
      patchStep_eq_source, ih]

theorem patchVertex_eq_source (w : ℕ → Fin 3) (s : ℕ) :
    kmswWindowPatchVertexMap w s = DirectedDistances.KMSW.kmswWindowPatchVertexMap w s := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [kmswWindowPatchVertexMap, DirectedDistances.KMSW.kmswWindowPatchVertexMap,
      patchData_eq_source, ih]
    rfl

theorem windowEdge_eq_source (w : ℕ → Fin 3) (s : ℕ) :
    kmswWindowEdgeMapInf w s = DirectedDistances.KMSW.kmswWindowEdgeMapInf w s := by
  funext e
  simp only [kmswWindowEdgeMapInf, DirectedDistances.KMSW.kmswWindowEdgeMapInf,
    patchData_eq_source]

theorem windowVertex_eq_source (w : ℕ → Fin 3) (s : ℕ) :
    kmswWindowVertexMapInf w s = DirectedDistances.KMSW.kmswWindowVertexMapInf w s := by
  funext v
  simp only [kmswWindowVertexMapInf, DirectedDistances.KMSW.kmswWindowVertexMapInf,
    patchVertex_eq_source]

theorem shiftedStream_eq_source (W : ℤ → Fin 3) (N : ℕ) :
    shiftedStream W N = DirectedDistances.KMSW.shiftedStream W N := by
  funext i
  rfl

theorem edgeTrans_eq_source (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) :
    wholePlaneEdgeTrans W N M h = DirectedDistances.KMSW.wholePlaneEdgeTrans W N M h := by
  simp only [wholePlaneEdgeTrans, DirectedDistances.KMSW.wholePlaneEdgeTrans,
    windowEdge_eq_source, shiftedStream_eq_source]

theorem vertexTrans_eq_source (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) :
    wholePlaneVertexTrans W N M h = DirectedDistances.KMSW.wholePlaneVertexTrans W N M h := by
  simp only [wholePlaneVertexTrans, DirectedDistances.KMSW.wholePlaneVertexTrans,
    windowVertex_eq_source, shiftedStream_eq_source]

theorem edgeRel_iff_source (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) :
    wholePlaneEdgeRel W a b ↔ DirectedDistances.KMSW.wholePlaneEdgeRel W a b := by
  simp only [wholePlaneEdgeRel, DirectedDistances.KMSW.wholePlaneEdgeRel,
    edgeTrans_eq_source]

theorem vertexRel_iff_source (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) :
    wholePlaneVertexRel W a b ↔ DirectedDistances.KMSW.wholePlaneVertexRel W a b := by
  simp only [wholePlaneVertexRel, DirectedDistances.KMSW.wholePlaneVertexRel,
    vertexTrans_eq_source]

theorem edgeRel_eq_source (W : ℤ → Fin 3) :
    wholePlaneEdgeRel W = DirectedDistances.KMSW.wholePlaneEdgeRel W := by
  funext a b
  exact propext (edgeRel_iff_source W a b)

theorem vertexRel_eq_source (W : ℤ → Fin 3) :
    wholePlaneVertexRel W = DirectedDistances.KMSW.wholePlaneVertexRel W := by
  funext a b
  exact propext (vertexRel_iff_source W a b)

theorem wholePlaneEdgeRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneEdgeRel W) := by
  rw [edgeRel_eq_source]
  exact DirectedDistances.KMSW.wholePlaneEdgeRel_equivalence W
theorem wholePlaneVertexRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneVertexRel W) := by
  rw [vertexRel_eq_source]
  exact DirectedDistances.KMSW.wholePlaneVertexRel_equivalence W
@[expose] def wholePlaneEdgeSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneEdgeRel W
  iseqv := wholePlaneEdgeRel_equivalence W
@[expose] def wholePlaneVertexSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneVertexRel W
  iseqv := wholePlaneVertexRel_equivalence W
@[expose] def WholePlaneEdge (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneEdgeSetoid W)
@[expose] def WholePlaneVertex (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneVertexSetoid W)
@[expose] def wholePlaneEdgeι (W : ℤ → Fin 3) (N : ℕ) (e : ℕ) : WholePlaneEdge W :=
  Quotient.mk (wholePlaneEdgeSetoid W) ⟨N, e⟩
@[expose] def wholePlaneVertexι (W : ℤ → Fin 3) (N : ℕ) (v : ℕ) : WholePlaneVertex W :=
  Quotient.mk (wholePlaneVertexSetoid W) ⟨N, v⟩
@[expose] def sourceEdgeEquiv (W : ℤ → Fin 3) :
    WholePlaneEdge W ≃ DirectedDistances.KMSW.WholePlaneEdge W where
  toFun := Quotient.map id (fun {a b} h => (edgeRel_iff_source W a b).mp h)
  invFun := Quotient.map id (fun {a b} h => (edgeRel_iff_source W a b).mpr h)
  left_inv := by
    intro e
    refine Quotient.inductionOn e ?_
    intro a
    rfl
  right_inv := by
    intro e
    refine Quotient.inductionOn e ?_
    intro a
    rfl

@[expose] def sourceVertexEquiv (W : ℤ → Fin 3) :
    WholePlaneVertex W ≃ DirectedDistances.KMSW.WholePlaneVertex W where
  toFun := Quotient.map id (fun {a b} h => (vertexRel_iff_source W a b).mp h)
  invFun := Quotient.map id (fun {a b} h => (vertexRel_iff_source W a b).mpr h)
  left_inv := by
    intro v
    refine Quotient.inductionOn v ?_
    intro a
    rfl
  right_inv := by
    intro v
    refine Quotient.inductionOn v ?_
    intro a
    rfl

theorem sourceEdgeEquiv_ι (W : ℤ → Fin 3) (N e : ℕ) :
    sourceEdgeEquiv W (wholePlaneEdgeι W N e) =
      DirectedDistances.KMSW.wholePlaneEdgeι W N e := rfl

theorem sourceVertexEquiv_ι (W : ℤ → Fin 3) (N v : ℕ) :
    sourceVertexEquiv W (wholePlaneVertexι W N v) =
      DirectedDistances.KMSW.wholePlaneVertexι W N v := rfl

theorem wholePlaneEdgeRel_west (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeWest (shiftedStream W b.1) b.2) := by
  apply (sourceVertexEquiv W).injective
  simpa only [sourceVertexEquiv_ι, shiftedStream_eq_source]
    using DirectedDistances.KMSW.wholePlaneEdgeRel_west W a b
      ((edgeRel_iff_source W a b).mp hab)
theorem wholePlaneEdgeRel_east (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeEast (shiftedStream W b.1) b.2) := by
  apply (sourceVertexEquiv W).injective
  simpa only [sourceVertexEquiv_ι, shiftedStream_eq_source]
    using DirectedDistances.KMSW.wholePlaneEdgeRel_east W a b
      ((edgeRel_iff_source W a b).mp hab)
@[expose] def wholePlaneEdgeWest (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_west W)
@[expose] def wholePlaneEdgeEast (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_east W)
end DLQG1.Palomar.Model.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW

theorem sourceEdgeEquiv_west (W : ℤ → Fin 3) (e : WholePlaneEdge W) :
    sourceVertexEquiv W (wholePlaneEdgeWest W e) =
      DirectedDistances.KMSW.wholePlaneEdgeWest W (sourceEdgeEquiv W e) := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change DirectedDistances.KMSW.wholePlaneVertexι W N (edgeWest (shiftedStream W N) e) =
    DirectedDistances.KMSW.wholePlaneVertexι W N
      (edgeWest (DirectedDistances.KMSW.shiftedStream W N) e)
  rw [shiftedStream_eq_source]

theorem sourceEdgeEquiv_east (W : ℤ → Fin 3) (e : WholePlaneEdge W) :
    sourceVertexEquiv W (wholePlaneEdgeEast W e) =
      DirectedDistances.KMSW.wholePlaneEdgeEast W (sourceEdgeEquiv W e) := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change DirectedDistances.KMSW.wholePlaneVertexι W N (edgeEast (shiftedStream W N) e) =
    DirectedDistances.KMSW.wholePlaneVertexι W N
      (edgeEast (DirectedDistances.KMSW.shiftedStream W N) e)
  rw [shiftedStream_eq_source]
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneRotationTransport
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def KMSWFiniteIncidence (w : ℕ → Fin 3) : Prop :=
  ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite
@[expose] def wholePlaneFresh (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (v : ℕ) : Prop :=
  (kmswStage (shiftedStream W N') (N' - N)).nextVertex ≤
    wholePlaneVertexTrans W N N' h v
@[expose] def WholePlaneRotationHypothesis (W : ℤ → Fin 3) : Prop :=
  (∀ N, KMSWFiniteIncidence (shiftedStream W N)) ∧
  (∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v))
@[expose] def wholePlaneDartTrans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N')
    (d : ℕ × Bool) : ℕ × Bool :=
  (wholePlaneEdgeTrans W N N' h d.1, d.2)
@[expose] def wholePlaneDartι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneEdge W × Bool :=
  (wholePlaneEdgeι W N d.1, d.2)
end DLQG1.Palomar.Model.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW

theorem fresh_iff_source (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) (v : ℕ) :
    wholePlaneFresh W N M h v ↔ DirectedDistances.KMSW.wholePlaneFresh W N M h v := by
  simp only [wholePlaneFresh, DirectedDistances.KMSW.wholePlaneFresh,
    vertexTrans_eq_source, shiftedStream_eq_source]

theorem rotationHyp_iff_source (W : ℤ → Fin 3) :
    WholePlaneRotationHypothesis W ↔ DirectedDistances.KMSW.WholePlaneRotationHypothesis W := by
  simp only [WholePlaneRotationHypothesis,
    DirectedDistances.KMSW.WholePlaneRotationHypothesis, KMSWFiniteIncidence,
    DirectedDistances.KMSW.KMSWFiniteIncidence, fresh_iff_source,
    vertexTrans_eq_source, shiftedStream_eq_source]

theorem sourceHyp {W : ℤ → Fin 3} (H : WholePlaneRotationHypothesis W) :
    DirectedDistances.KMSW.WholePlaneRotationHypothesis W := (rotationHyp_iff_source W).mp H

theorem dartTrans_eq_source (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M) :
    wholePlaneDartTrans W N M h = DirectedDistances.KMSW.wholePlaneDartTrans W N M h := by
  funext d
  simp only [wholePlaneDartTrans, DirectedDistances.KMSW.wholePlaneDartTrans,
    edgeTrans_eq_source]
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneRotation
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def WholePlaneDart (W : ℤ → Fin 3) : Type := WholePlaneEdge W × Bool
@[expose] noncomputable def runRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) :
    Equiv.Perm (ℕ × Bool) :=
  if inv then (kmswInfRot (shiftedStream W N) (H.1 N)).symm
  else kmswInfRot (shiftedStream W N) (H.1 N)
@[expose] def sourceDartEquiv (W : ℤ → Fin 3) :
    WholePlaneDart W ≃ DirectedDistances.KMSW.WholePlaneDart W :=
  (sourceEdgeEquiv W).prodCongr (Equiv.refl Bool)

theorem sourceDartEquiv_ι (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) :
    sourceDartEquiv W (wholePlaneDartι W N d) =
      DirectedDistances.KMSW.wholePlaneDartι W N d := by
  rcases d with ⟨e, b⟩
  rfl

theorem runRot_eq_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) :
    runRot W H inv N = DirectedDistances.KMSW.runRot W (sourceHyp H) inv N := by
  simp only [runRot, DirectedDistances.KMSW.runRot, kmswInfRot_eq_source, shiftedStream_eq_source]
@[expose] def eventualValue (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (N : ℕ) (d : ℕ × Bool) (y : WholePlaneDart W) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
    wholePlaneDartι W M' (runRot W H inv M'
      (wholePlaneDartTrans W N M' (hNM.trans hMM') d)) = y
theorem eventualValue_iff_source (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool)
    (y : WholePlaneDart W) :
    eventualValue W H inv N d y ↔ DirectedDistances.KMSW.eventualValue W
      (sourceHyp H) inv N d (sourceDartEquiv W y) := by
  constructor
  · rintro ⟨M, hNM, hy⟩
    refine ⟨M, hNM, fun L hML => ?_⟩
    have he := congrArg (sourceDartEquiv W) (hy L hML)
    rw [sourceDartEquiv_ι] at he
    simp only [runRot_eq_source, dartTrans_eq_source] at he
    simpa only [DirectedDistances.KMSW.WholePlaneDart] using he
  · rintro ⟨M, hNM, hy⟩
    refine ⟨M, hNM, fun L hML => ?_⟩
    apply (sourceDartEquiv W).injective
    rw [sourceDartEquiv_ι]
    simp only [runRot_eq_source, dartTrans_eq_source]
    simpa only [DirectedDistances.KMSW.WholePlaneDart] using hy L hML

theorem eventualValue_existsUnique (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    ∃! y, eventualValue W H inv N d y := by
  obtain ⟨y, hy, hu⟩ := DirectedDistances.KMSW.eventualValue_existsUnique W
    (sourceHyp H) inv N d
  refine ⟨(sourceDartEquiv W).symm y, ?_, ?_⟩
  · apply (eventualValue_iff_source W H inv N d _).mpr
    simpa only [Equiv.apply_symm_apply] using hy
  · intro z hz
    apply (sourceDartEquiv W).injective
    rw [Equiv.apply_symm_apply]
    exact hu _ ((eventualValue_iff_source W H inv N d z).mp hz)

@[expose] noncomputable def value (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    WholePlaneDart W :=
  (eventualValue_existsUnique W H inv N d).exists.choose
theorem value_eq_source (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (inv : Bool) (N : ℕ) (d : ℕ × Bool) :
    sourceDartEquiv W (value W H inv N d) =
      DirectedDistances.KMSW.value W (sourceHyp H) inv N d := by
  exact (DirectedDistances.KMSW.eventualValue_existsUnique W (sourceHyp H) inv N d).unique
    ((eventualValue_iff_source W H inv N d _).mp
      (eventualValue_existsUnique W H inv N d).exists.choose_spec)
    (DirectedDistances.KMSW.eventualValue_existsUnique W (sourceHyp H) inv N d).exists.choose_spec

theorem value_rel (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (inv : Bool) (a b : Σ _ : ℕ, ℕ) (hab : wholePlaneEdgeRel W a b) (s : Bool) :
    value W H inv a.1 (a.2, s) = value W H inv b.1 (b.2, s) := by
  apply (sourceDartEquiv W).injective
  rw [value_eq_source, value_eq_source]
  exact DirectedDistances.KMSW.value_rel W (sourceHyp H) inv a b
    ((edgeRel_iff_source W a b).mp hab) s

@[expose] noncomputable def wholePlaneRot (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L (kmswInfRot (shiftedStream W L) (H.1 L)
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H false a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H false a b hab x.2) x.1
@[expose] noncomputable def wholePlaneRotInv (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : WholePlaneDart W → WholePlaneDart W :=
  fun x => Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    Classical.choose (show ∃ y : WholePlaneDart W,
      ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
        wholePlaneDartι W L ((kmswInfRot (shiftedStream W L) (H.1 L)).symm
          (wholePlaneDartTrans W a.1 L (hNM.trans hML) (a.2, x.2))) = y from by
            exact (eventualValue_existsUnique W H true a.1 (a.2, x.2)).exists))
    (by
      intro a b hab
      exact value_rel W H true a b hab x.2) x.1
theorem sourceDartEquiv_rot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    sourceDartEquiv W (wholePlaneRot W H d) =
      DirectedDistances.KMSW.wholePlaneRot W (sourceHyp H) (sourceDartEquiv W d) := by
  rcases d with ⟨e, b⟩
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change sourceDartEquiv W (value W H false N (e, b)) =
    DirectedDistances.KMSW.wholePlaneRot W (sourceHyp H)
      (DirectedDistances.KMSW.wholePlaneDartι W N (e, b))
  rw [value_eq_source]
  exact DLQG1.Palomar.Principal.Transport.value_false_eq_sourceRot W (sourceHyp H) N (e, b)

theorem sourceDartEquiv_rotInv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    sourceDartEquiv W (wholePlaneRotInv W H d) =
      DirectedDistances.KMSW.wholePlaneRotInv W (sourceHyp H) (sourceDartEquiv W d) := by
  rcases d with ⟨e, b⟩
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change sourceDartEquiv W (value W H true N (e, b)) =
    DirectedDistances.KMSW.wholePlaneRotInv W (sourceHyp H)
      (DirectedDistances.KMSW.wholePlaneDartι W N (e, b))
  rw [value_eq_source]
  exact DLQG1.Palomar.Principal.Transport.value_true_eq_sourceRotInv W (sourceHyp H) N (e, b)

theorem wholePlaneRot_comp_inv (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    wholePlaneRot W H ∘ wholePlaneRotInv W H = id := by
  funext d
  apply (sourceDartEquiv W).injective
  change sourceDartEquiv W (wholePlaneRot W H (wholePlaneRotInv W H d)) = sourceDartEquiv W d
  rw [sourceDartEquiv_rot, sourceDartEquiv_rotInv]
  exact congrFun (DirectedDistances.KMSW.wholePlaneRot_comp_inv W (sourceHyp H))
    (sourceDartEquiv W d)

theorem wholePlaneRotInv_comp_rot (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    wholePlaneRotInv W H ∘ wholePlaneRot W H = id := by
  funext d
  apply (sourceDartEquiv W).injective
  change sourceDartEquiv W (wholePlaneRotInv W H (wholePlaneRot W H d)) = sourceDartEquiv W d
  rw [sourceDartEquiv_rotInv, sourceDartEquiv_rot]
  exact congrFun (DirectedDistances.KMSW.wholePlaneRotInv_comp_rot W (sourceHyp H))
    (sourceDartEquiv W d)

@[expose] noncomputable def wholePlaneRotation (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) where
  toFun := wholePlaneRot W H
  invFun := wholePlaneRotInv W H
  left_inv := congrFun (wholePlaneRotInv_comp_rot W H)
  right_inv := congrFun (wholePlaneRot_comp_inv W H)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.KMSWWholePlaneFaces
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def wholePlaneDartFlip (W : ℤ → Fin 3) : Equiv.Perm (WholePlaneDart W) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl
@[expose] noncomputable def wholePlaneFaceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Equiv.Perm (WholePlaneDart W) :=
  (wholePlaneRotation W H).symm * wholePlaneDartFlip W
@[expose] def eventualPresence (W : ℤ → Fin 3) (N e : ℕ) : Prop :=
  ∃ M, ∃ hNM : N ≤ M, ∀ L (hML : M ≤ L),
    EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W N L (hNM.trans hML) e)
theorem eventualPresence_iff_source (W : ℤ → Fin 3) (N e : ℕ) :
    eventualPresence W N e ↔ DirectedDistances.KMSW.eventualPresence W N e := by
  simp only [eventualPresence, DirectedDistances.KMSW.eventualPresence,
    edgeTrans_eq_source, shiftedStream_eq_source]

theorem eventualPresence_rel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) : eventualPresence W a.1 a.2 = eventualPresence W b.1 b.2 := by
  apply propext
  rw [eventualPresence_iff_source, eventualPresence_iff_source]
  exact Iff.of_eq (DirectedDistances.KMSW.eventualPresence_rel W a b
    ((edgeRel_iff_source W a b).mp hab))

@[expose] def wholePlaneEdgePresent (W : ℤ → Fin 3) : WholePlaneEdge W → Prop :=
  Quotient.lift (fun a : Σ _ : ℕ, ℕ =>
    ∃ M, ∃ hNM : a.1 ≤ M, ∀ L (hML : M ≤ L),
      EdgePresent (shiftedStream W L) (wholePlaneEdgeTrans W a.1 L (hNM.trans hML) a.2))
    (by
      intro a b hab
      exact eventualPresence_rel W a b hab)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure
namespace DLQG1.Palomar.Model.RandomWalk
open DirectedDistances.RandomWalk
open MeasureTheory ProbabilityTheory
@[expose] noncomputable def wholePlaneIIDCodeMeasure : Measure (ℤ → Fin 3) :=
  Measure.infinitePi (fun _ : ℤ => uniformCodeMeasure)
end DLQG1.Palomar.Model.RandomWalk
-- Source module DirectedDistances.KMSW.WholePlaneRightBoundary
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open MeasureTheory RandomWalk
@[expose] def wholePlaneRightmostOutgoingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeWest W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, false)).2 = true ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, false)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, false)).1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneDrawingCombinatorics
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def wholePlaneDartVertex (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    WholePlaneVertex W :=
  if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.BoundaryLabelling
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open scoped Classical
@[expose] noncomputable def boundaryOuterEdge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (k : ℤ) : ℕ :=
  if k ≤ -1 then kmswLLCreatedEdge w (boundaryHitTime w h k)
  else if 1 ≤ k then kmswRightBoundaryEdge w k.toNat
  else 0
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneRootedMapFields
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open Quiver
@[expose] def wholePlaneDartTail (W : ℤ → Fin 3) : WholePlaneDart W → Prop :=
  fun d => ¬ d.2 ∧ wholePlaneEdgePresent W d.1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutRootTransport
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def m0CutLambdaZero (W : ℤ → Fin 3) : WholePlaneEdge W :=
  wholePlaneEdgeι W 0 0
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneRightmostRays
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
end DLQG1.Palomar.Model.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW

theorem sourceEdgeEquiv_present (W : ℤ → Fin 3) (e : WholePlaneEdge W) :
    wholePlaneEdgePresent W e ↔
      DirectedDistances.KMSW.wholePlaneEdgePresent W (sourceEdgeEquiv W e) := by
  refine Quotient.inductionOn e ?_
  rintro ⟨N, e⟩
  change eventualPresence W N e ↔
    DirectedDistances.KMSW.wholePlaneEdgePresent W
      (DirectedDistances.KMSW.wholePlaneEdgeι W N e)
  rw [← DLQG1.Palomar.Principal.Transport.eventualPresence_eq_source]
  exact eventualPresence_iff_source W N e

theorem sourceDartEquiv_rotation (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    sourceDartEquiv W (wholePlaneRotation W H d) =
      DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H) (sourceDartEquiv W d) :=
  sourceDartEquiv_rot W H d

theorem sourceDartEquiv_rotation_symm (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    sourceDartEquiv W ((wholePlaneRotation W H).symm d) =
      (DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm (sourceDartEquiv W d) :=
  sourceDartEquiv_rotInv W H d

theorem sourceDartEquiv_rotation_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (k : ℕ) (d : WholePlaneDart W) :
    sourceDartEquiv W ((wholePlaneRotation W H ^ k) d) =
      (DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H) ^ k) (sourceDartEquiv W d) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    change sourceDartEquiv W ((wholePlaneRotation W H ^ k) (wholePlaneRotation W H d)) =
      (DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H) ^ k)
        (DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H) (sourceDartEquiv W d))
    rw [ih, sourceDartEquiv_rotation]

theorem sourceDartEquiv_rotation_symm_pow (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (k : ℕ) (d : WholePlaneDart W) :
    sourceDartEquiv W (((wholePlaneRotation W H).symm ^ k) d) =
      ((DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm ^ k)
        (sourceDartEquiv W d) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    change sourceDartEquiv W (((wholePlaneRotation W H).symm ^ k)
        ((wholePlaneRotation W H).symm d)) =
      ((DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm ^ k)
        ((DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm (sourceDartEquiv W d))
    rw [ih, sourceDartEquiv_rotation_symm]

theorem sourceDartEquiv_flip (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    sourceDartEquiv W (wholePlaneDartFlip W d) =
      DirectedDistances.KMSW.wholePlaneDartFlip W (sourceDartEquiv W d) := rfl

theorem sourceDartEquiv_faceSucc (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    sourceDartEquiv W (wholePlaneFaceSucc W H d) =
      DirectedDistances.KMSW.wholePlaneFaceSucc W (sourceHyp H) (sourceDartEquiv W d) := by
  change sourceDartEquiv W ((wholePlaneRotation W H).symm (wholePlaneDartFlip W d)) =
    (DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm
      (DirectedDistances.KMSW.wholePlaneDartFlip W (sourceDartEquiv W d))
  rw [sourceDartEquiv_rotation_symm, sourceDartEquiv_flip]

theorem sourceDartEquiv_fst (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    (sourceDartEquiv W d).1 = sourceEdgeEquiv W d.1 := rfl

theorem sourceDartEquiv_snd (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    (sourceDartEquiv W d).2 = d.2 := rfl
end DLQG1.Palomar.Model.KMSW
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure WholePlaneRightmostRay (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  vertex : ℕ → WholePlaneVertex W
  edge : ℕ → WholePlaneEdge W
  rightmost : ∀ i, wholePlaneRightmostOutgoingAt W H (vertex i) (edge i)
  target : ∀ i, wholePlaneEdgeEast W (edge i) = vertex (i + 1)
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.WholePlaneLeftmostIncoming
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
@[expose] def wholePlaneLeftmostIncomingAt (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W)
    (e : WholePlaneEdge W) : Prop :=
  wholePlaneEdgePresent W e ∧ wholePlaneEdgeEast W e = v ∧
    ∃ k : ℕ, 0 < k ∧
      (((wholePlaneRotation W H).symm ^ k) (e, true)).2 = false ∧
      wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ k) (e, true)).1 ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ wholePlaneEdgePresent W (((wholePlaneRotation W H).symm ^ j) (e, true)).1
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutSeam
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure M0CutLeftmostChain (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (v : WholePlaneVertex W) where
  vertex : ℕ → WholePlaneVertex W
  edge : ℕ → WholePlaneEdge W
  endpoint : vertex 0 = v
  leftmost : ∀ i, wholePlaneLeftmostIncomingAt W H (vertex i) (edge i)
  westEndpoint : ∀ i, wholePlaneEdgeWest W (edge i) = vertex (i + 1)
theorem rotation_symm_pow_fst (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (k : ℕ) (e : WholePlaneEdge W) (b : Bool) :
    sourceEdgeEquiv W (((wholePlaneRotation W H).symm ^ k) (e, b)).1 =
      (((DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm ^ k)
        (sourceEdgeEquiv W e, b)).1 := by
  exact congrArg (fun d : DirectedDistances.KMSW.WholePlaneDart W => d.1)
    (sourceDartEquiv_rotation_symm_pow W H k (e, b))

theorem rotation_symm_pow_snd (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (k : ℕ) (e : WholePlaneEdge W) (b : Bool) :
    (((wholePlaneRotation W H).symm ^ k) (e, b)).2 =
      (((DirectedDistances.KMSW.wholePlaneRotation W (sourceHyp H)).symm ^ k)
        (sourceEdgeEquiv W e, b)).2 := by
  exact congrArg (fun d : DirectedDistances.KMSW.WholePlaneDart W => d.2)
    (sourceDartEquiv_rotation_symm_pow W H k (e, b))

theorem rightmost_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (v : WholePlaneVertex W) (e : WholePlaneEdge W) :
    wholePlaneRightmostOutgoingAt W H v e ↔
      DirectedDistances.KMSW.wholePlaneRightmostOutgoingAt W (sourceHyp H)
        (sourceVertexEquiv W v) (sourceEdgeEquiv W e) := by
  simp only [wholePlaneRightmostOutgoingAt,
    DirectedDistances.KMSW.wholePlaneRightmostOutgoingAt,
    ← rotation_symm_pow_fst W H, ← rotation_symm_pow_snd W H,
    ← sourceEdgeEquiv_present, ← sourceEdgeEquiv_west,
    (sourceVertexEquiv W).injective.eq_iff]

theorem leftmost_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (v : WholePlaneVertex W) (e : WholePlaneEdge W) :
    wholePlaneLeftmostIncomingAt W H v e ↔
      DirectedDistances.KMSW.wholePlaneLeftmostIncomingAt W (sourceHyp H)
        (sourceVertexEquiv W v) (sourceEdgeEquiv W e) := by
  simp only [wholePlaneLeftmostIncomingAt,
    DirectedDistances.KMSW.wholePlaneLeftmostIncomingAt,
    ← rotation_symm_pow_fst W H, ← rotation_symm_pow_snd W H,
    ← sourceEdgeEquiv_present, ← sourceEdgeEquiv_east,
    (sourceVertexEquiv W).injective.eq_iff]

@[expose] def toSourceRightRay {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (P : WholePlaneRightmostRay W H) :
    DirectedDistances.KMSW.WholePlaneRightmostRay W (sourceHyp H) where
  vertex i := sourceVertexEquiv W (P.vertex i)
  edge i := sourceEdgeEquiv W (P.edge i)
  rightmost i := (rightmost_iff_source W H _ _).mp (P.rightmost i)
  target i := (sourceEdgeEquiv_east W _).symm.trans
    (congrArg (sourceVertexEquiv W) (P.target i))

@[expose] def fromSourceRightRay {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (P : DirectedDistances.KMSW.WholePlaneRightmostRay W (sourceHyp H)) :
    WholePlaneRightmostRay W H where
  vertex i := (sourceVertexEquiv W).symm (P.vertex i)
  edge i := (sourceEdgeEquiv W).symm (P.edge i)
  rightmost i := (rightmost_iff_source W H _ _).mpr (by
    simpa only [Equiv.apply_symm_apply] using P.rightmost i)
  target i := by
    apply (sourceVertexEquiv W).injective
    rw [sourceEdgeEquiv_east, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact P.target i

@[expose] def toSourceLeftChain {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {v : WholePlaneVertex W} {v' : DirectedDistances.KMSW.WholePlaneVertex W}
    (P : M0CutLeftmostChain W H v) (hv : sourceVertexEquiv W v = v') :
    DirectedDistances.KMSW.M0CutLeftmostChain W (sourceHyp H) v' where
  vertex i := sourceVertexEquiv W (P.vertex i)
  edge i := sourceEdgeEquiv W (P.edge i)
  endpoint := (congrArg (sourceVertexEquiv W) P.endpoint).trans hv
  leftmost i := (leftmost_iff_source W H _ _).mp (P.leftmost i)
  westEndpoint i := (sourceEdgeEquiv_west W _).symm.trans
    (congrArg (sourceVertexEquiv W) (P.westEndpoint i))

@[expose] def fromSourceLeftChain {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    {v : WholePlaneVertex W} {v' : DirectedDistances.KMSW.WholePlaneVertex W}
    (P : DirectedDistances.KMSW.M0CutLeftmostChain W (sourceHyp H) v')
    (hv : sourceVertexEquiv W v = v') : M0CutLeftmostChain W H v where
  vertex i := (sourceVertexEquiv W).symm (P.vertex i)
  edge i := (sourceEdgeEquiv W).symm (P.edge i)
  endpoint := by
    apply (sourceVertexEquiv W).injective
    rw [Equiv.apply_symm_apply]
    exact P.endpoint.trans hv.symm
  leftmost i := (leftmost_iff_source W H _ _).mpr (by
    simpa only [Equiv.apply_symm_apply] using P.leftmost i)
  westEndpoint i := by
    apply (sourceVertexEquiv W).injective
    rw [sourceEdgeEquiv_west, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact P.westEndpoint i

theorem sourceEdgeEquiv_lambdaZero (W : ℤ → Fin 3) :
    sourceEdgeEquiv W (m0CutLambdaZero W) = DirectedDistances.KMSW.m0CutLambdaZero W := rfl

theorem sourceVertexEquiv_lambdaWest (W : ℤ → Fin 3) :
    sourceVertexEquiv W (wholePlaneEdgeWest W (m0CutLambdaZero W)) =
      DirectedDistances.KMSW.wholePlaneEdgeWest W (DirectedDistances.KMSW.m0CutLambdaZero W) := by
  rw [sourceEdgeEquiv_west, sourceEdgeEquiv_lambdaZero]

theorem sourceVertexEquiv_lambdaEast (W : ℤ → Fin 3) :
    sourceVertexEquiv W (wholePlaneEdgeEast W (m0CutLambdaZero W)) =
      DirectedDistances.KMSW.wholePlaneEdgeEast W (DirectedDistances.KMSW.m0CutLambdaZero W) := by
  rw [sourceEdgeEquiv_east, sourceEdgeEquiv_lambdaZero]

@[expose] def m0CutSeamEdge (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (e : WholePlaneEdge W) : Prop :=
  e = m0CutLambdaZero W ∨
    (∃ P : WholePlaneRightmostRay W H,
      P.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W) ∧
        ∃ j, P.edge j = e) ∨
    ∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
      ∃ j, P.edge j = e
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutLeftSide
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open DirectedDistances.PlanarMap
@[expose] def m0CutLeftStep (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) (d e : WholePlaneDart W) : Prop :=
  e = wholePlaneFaceSucc W H d ∨ (e = wholePlaneDartFlip W d ∧ ¬ S d.1)
@[expose] def m0CutLeftDarts (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneDart W) :=
  {d | ∃ e, S e ∧ Relation.ReflTransGen (m0CutLeftStep W H S) (e, false) d}
@[expose] def m0CutLeftEdges (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneEdge W) :=
  Prod.fst '' m0CutLeftDarts W H S
@[expose] def m0CutLeftVertices (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (S : WholePlaneEdge W → Prop) : Set (WholePlaneVertex W) :=
  wholePlaneDartVertex W '' m0CutLeftDarts W H S
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutPresence
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open Quiver
@[expose] def m0CutMissing (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (E : WholePlaneEdge W) : Prop :=
  (∃ P : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W)),
    ∃ j, P.edge j = E) ∨ ¬ wholePlaneEdgePresent W E
@[expose] def m0CutTail (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : WholePlaneDart W) : Prop :=
  wholePlaneDartTail W d ∧ ¬ m0CutMissing W H d.1
@[expose] def m0CutDirectedStep (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ d : WholePlaneDart W, m0CutTail W H d ∧ d.1 ∈ m0CutLeftEdges W H S ∧
    wholePlaneEdgeWest W d.1 = u ∧ wholePlaneEdgeEast W d.1 = v
section Paths
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
@[expose] def m0CutReachableLength {V : Type*} (R : V → V → Prop) :
    ℕ → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ x, m0CutReachableLength R n u x ∧ R x v
@[expose] noncomputable def m0CutSDP (u v : WholePlaneVertex W) : ℕ∞ :=
  ⨅ n : ℕ, ⨅ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v), (n : ℕ∞)
@[expose] noncomputable def m0CutLDP (u v : WholePlaneVertex W) : WithBot ℕ∞ :=
  ⨆ n : ℕ, ⨆ (_ : m0CutReachableLength (m0CutDirectedStep W H S) n u v),
    ((n : ℕ∞) : WithBot ℕ∞)
end Paths
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutData
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
structure M0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  betaR : WholePlaneRightmostRay W H
  betaR_start : betaR.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)
  betaL : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))
namespace M0CutData
variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
@[expose] def seam (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutSeamEdge W H
@[expose] def missing (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutMissing W H
@[expose] def tail (_D : M0CutData W H) : WholePlaneDart W → Prop :=
  m0CutTail W H
@[expose] def rootDart (_D : M0CutData W H) : WholePlaneDart W :=
  (m0CutLambdaZero W, false)
@[expose] def x (D : M0CutData W H) (k : ℤ) : WholePlaneVertex W :=
  if k = 0 then wholePlaneEdgeWest W (m0CutLambdaZero W)
  else if k = 1 then wholePlaneEdgeEast W (m0CutLambdaZero W)
  else if 2 ≤ k then D.betaR.vertex (k - 1).toNat
  else D.betaL.vertex (-k).toNat
@[expose] noncomputable def sdp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → ℕ∞ :=
  m0CutSDP W H D.seam
@[expose] noncomputable def ldp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → WithBot ℕ∞ :=
  m0CutLDP W H D.seam
end M0CutData
theorem seam_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (e : WholePlaneEdge W) :
    m0CutSeamEdge W H e ↔
      DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H) (sourceEdgeEquiv W e) := by
  constructor
  · rintro (he | ⟨P, hp, j, hj⟩ | ⟨P, j, hj⟩)
    · exact Or.inl ((congrArg (sourceEdgeEquiv W) he).trans (sourceEdgeEquiv_lambdaZero W))
    · refine Or.inr (Or.inl ⟨toSourceRightRay P, ?_, j, congrArg (sourceEdgeEquiv W) hj⟩)
      exact (congrArg (sourceVertexEquiv W) hp).trans (sourceVertexEquiv_lambdaEast W)
    · exact Or.inr (Or.inr ⟨toSourceLeftChain P (sourceVertexEquiv_lambdaWest W), j,
        congrArg (sourceEdgeEquiv W) hj⟩)
  · rintro (he | ⟨P, hp, j, hj⟩ | ⟨P, j, hj⟩)
    · apply Or.inl
      apply (sourceEdgeEquiv W).injective
      exact he.trans (sourceEdgeEquiv_lambdaZero W).symm
    · refine Or.inr (Or.inl ⟨fromSourceRightRay P, ?_, j, ?_⟩)
      · apply (sourceVertexEquiv W).injective
        simpa only [fromSourceRightRay, Equiv.apply_symm_apply,
          sourceVertexEquiv_lambdaEast] using hp
      · apply (sourceEdgeEquiv W).injective
        simpa only [fromSourceRightRay, Equiv.apply_symm_apply] using hj
    · refine Or.inr (Or.inr ⟨fromSourceLeftChain P (sourceVertexEquiv_lambdaWest W), j, ?_⟩)
      apply (sourceEdgeEquiv W).injective
      simpa only [fromSourceLeftChain, Equiv.apply_symm_apply] using hj

theorem missing_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (e : WholePlaneEdge W) :
    m0CutMissing W H e ↔
      DirectedDistances.KMSW.m0CutMissing W (sourceHyp H) (sourceEdgeEquiv W e) := by
  constructor
  · rintro (⟨P, j, hj⟩ | hp)
    · exact Or.inl ⟨toSourceLeftChain P (sourceVertexEquiv_lambdaWest W), j,
        congrArg (sourceEdgeEquiv W) hj⟩
    · exact Or.inr ((not_congr (sourceEdgeEquiv_present W e)).mp hp)
  · rintro (⟨P, j, hj⟩ | hp)
    · refine Or.inl ⟨fromSourceLeftChain P (sourceVertexEquiv_lambdaWest W), j, ?_⟩
      apply (sourceEdgeEquiv W).injective
      simpa only [fromSourceLeftChain, Equiv.apply_symm_apply] using hj
    · exact Or.inr ((not_congr (sourceEdgeEquiv_present W e)).mpr hp)

theorem cutTail_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    m0CutTail W H d ↔
      DirectedDistances.KMSW.m0CutTail W (sourceHyp H) (sourceDartEquiv W d) := by
  simp only [m0CutTail, DirectedDistances.KMSW.m0CutTail,
    wholePlaneDartTail, DirectedDistances.KMSW.wholePlaneDartTail,
    sourceDartEquiv_fst, sourceDartEquiv_snd,
    ← sourceEdgeEquiv_present, ← missing_iff_source W H]

theorem sourceDartEquiv_vertex (W : ℤ → Fin 3) (d : WholePlaneDart W) :
    sourceVertexEquiv W (wholePlaneDartVertex W d) =
      DirectedDistances.KMSW.wholePlaneDartVertex W (sourceDartEquiv W d) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact sourceEdgeEquiv_west W e
  · exact sourceEdgeEquiv_east W e

theorem leftStep_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d e : WholePlaneDart W) :
    m0CutLeftStep W H (m0CutSeamEdge W H) d e ↔
      DirectedDistances.KMSW.m0CutLeftStep W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H))
        (sourceDartEquiv W d) (sourceDartEquiv W e) := by
  simp only [m0CutLeftStep, DirectedDistances.KMSW.m0CutLeftStep,
    ← sourceDartEquiv_faceSucc W H, ← sourceDartEquiv_flip,
    (sourceDartEquiv W).injective.eq_iff,
    sourceDartEquiv_fst, ← seam_iff_source W H]

theorem rtg_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b))
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen S (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hf _ _ hbc)

theorem leftPath_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d e : WholePlaneDart W) :
    Relation.ReflTransGen (m0CutLeftStep W H (m0CutSeamEdge W H)) d e ↔
      Relation.ReflTransGen (DirectedDistances.KMSW.m0CutLeftStep W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H)))
        (sourceDartEquiv W d) (sourceDartEquiv W e) := by
  constructor
  · intro hp
    exact rtg_map (sourceDartEquiv W)
      (fun a b h => (leftStep_iff_source W H a b).mp h) hp
  · intro hp
    have hback := rtg_map (sourceDartEquiv W).symm
      (fun a b h => (leftStep_iff_source W H
        ((sourceDartEquiv W).symm a) ((sourceDartEquiv W).symm b)).mpr
        (by simpa only [Equiv.apply_symm_apply] using h)) hp
    simpa only [Equiv.symm_apply_apply] using hback

theorem leftDarts_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (d : WholePlaneDart W) :
    d ∈ m0CutLeftDarts W H (m0CutSeamEdge W H) ↔
      sourceDartEquiv W d ∈ DirectedDistances.KMSW.m0CutLeftDarts W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H)) := by
  constructor
  · rintro ⟨e, he, hp⟩
    exact ⟨sourceEdgeEquiv W e, (seam_iff_source W H e).mp he,
      (leftPath_iff_source W H (e, false) d).mp hp⟩
  · rintro ⟨e', he, hp⟩
    obtain ⟨e, rfl⟩ := (sourceEdgeEquiv W).surjective e'
    exact ⟨e, (seam_iff_source W H e).mpr he,
      (leftPath_iff_source W H (e, false) d).mpr hp⟩

theorem leftEdges_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (e : WholePlaneEdge W) :
    e ∈ m0CutLeftEdges W H (m0CutSeamEdge W H) ↔
      sourceEdgeEquiv W e ∈ DirectedDistances.KMSW.m0CutLeftEdges W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H)) := by
  constructor
  · rintro ⟨d, hd, he⟩
    exact ⟨sourceDartEquiv W d, (leftDarts_iff_source W H d).mp hd,
      (sourceDartEquiv_fst W d).trans (congrArg (sourceEdgeEquiv W) he)⟩
  · rintro ⟨d', hd, he⟩
    obtain ⟨d, rfl⟩ := (sourceDartEquiv W).surjective d'
    refine ⟨d, (leftDarts_iff_source W H d).mpr hd, ?_⟩
    apply (sourceEdgeEquiv W).injective
    exact (sourceDartEquiv_fst W d).symm.trans he

theorem leftVertices_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (v : WholePlaneVertex W) :
    v ∈ m0CutLeftVertices W H (m0CutSeamEdge W H) ↔
      sourceVertexEquiv W v ∈ DirectedDistances.KMSW.m0CutLeftVertices W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H)) := by
  constructor
  · rintro ⟨d, hd, he⟩
    exact ⟨sourceDartEquiv W d, (leftDarts_iff_source W H d).mp hd,
      (sourceDartEquiv_vertex W d).symm.trans (congrArg (sourceVertexEquiv W) he)⟩
  · rintro ⟨d', hd, he⟩
    obtain ⟨d, rfl⟩ := (sourceDartEquiv W).surjective d'
    refine ⟨d, (leftDarts_iff_source W H d).mpr hd, ?_⟩
    apply (sourceVertexEquiv W).injective
    exact (sourceDartEquiv_vertex W d).trans he

theorem directedStep_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (u v : WholePlaneVertex W) :
    m0CutDirectedStep W H (m0CutSeamEdge W H) u v ↔
      DirectedDistances.KMSW.m0CutDirectedStep W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H))
        (sourceVertexEquiv W u) (sourceVertexEquiv W v) := by
  constructor
  · rintro ⟨d, ht, he, hw, hd⟩
    refine ⟨sourceDartEquiv W d, (cutTail_iff_source W H d).mp ht,
      (leftEdges_iff_source W H d.1).mp he, ?_, ?_⟩
    · exact (sourceEdgeEquiv_west W d.1).symm.trans (congrArg (sourceVertexEquiv W) hw)
    · exact (sourceEdgeEquiv_east W d.1).symm.trans (congrArg (sourceVertexEquiv W) hd)
  · rintro ⟨d', ht, he, hw, hd⟩
    obtain ⟨d, rfl⟩ := (sourceDartEquiv W).surjective d'
    refine ⟨d, (cutTail_iff_source W H d).mpr ht,
      (leftEdges_iff_source W H d.1).mpr he, ?_, ?_⟩
    · apply (sourceVertexEquiv W).injective
      exact (sourceEdgeEquiv_west W d.1).trans hw
    · apply (sourceVertexEquiv W).injective
      exact (sourceEdgeEquiv_east W d.1).trans hd

theorem reachableLength_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (n : ℕ) (u v : WholePlaneVertex W) :
    m0CutReachableLength (m0CutDirectedStep W H (m0CutSeamEdge W H)) n u v ↔
      DirectedDistances.KMSW.m0CutReachableLength
        (DirectedDistances.KMSW.m0CutDirectedStep W (sourceHyp H)
          (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H))) n
        (sourceVertexEquiv W u) (sourceVertexEquiv W v) := by
  induction n generalizing u v with
  | zero =>
    simp only [m0CutReachableLength, DirectedDistances.KMSW.m0CutReachableLength,
      (sourceVertexEquiv W).injective.eq_iff]
  | succ n ih =>
    constructor
    · rintro ⟨x, hx, hstep⟩
      exact ⟨sourceVertexEquiv W x, (ih u x).mp hx,
        (directedStep_iff_source W H x v).mp hstep⟩
    · rintro ⟨x', hx, hstep⟩
      obtain ⟨x, rfl⟩ := (sourceVertexEquiv W).surjective x'
      exact ⟨x, (ih u x).mpr hx, (directedStep_iff_source W H x v).mpr hstep⟩

theorem sdp_eq_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (u v : WholePlaneVertex W) :
    m0CutSDP W H (m0CutSeamEdge W H) u v =
      DirectedDistances.KMSW.m0CutSDP W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H))
        (sourceVertexEquiv W u) (sourceVertexEquiv W v) := by
  simp only [m0CutSDP, DirectedDistances.KMSW.m0CutSDP,
    reachableLength_iff_source]

theorem ldp_eq_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (u v : WholePlaneVertex W) :
    m0CutLDP W H (m0CutSeamEdge W H) u v =
      DirectedDistances.KMSW.m0CutLDP W (sourceHyp H)
        (DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H))
        (sourceVertexEquiv W u) (sourceVertexEquiv W v) := by
  simp only [m0CutLDP, DirectedDistances.KMSW.m0CutLDP,
    reachableLength_iff_source]

@[expose] def toSourceCut {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) : DirectedDistances.KMSW.M0CutData W (sourceHyp H) where
  betaR := toSourceRightRay D.betaR
  betaR_start := (congrArg (sourceVertexEquiv W) D.betaR_start).trans
    (sourceVertexEquiv_lambdaEast W)
  betaL := toSourceLeftChain D.betaL (sourceVertexEquiv_lambdaWest W)

@[expose] def fromSourceCut {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : DirectedDistances.KMSW.M0CutData W (sourceHyp H)) : M0CutData W H where
  betaR := fromSourceRightRay D.betaR
  betaR_start := by
    apply (sourceVertexEquiv W).injective
    simpa only [fromSourceRightRay, Equiv.apply_symm_apply,
      sourceVertexEquiv_lambdaEast] using D.betaR_start
  betaL := fromSourceLeftChain D.betaL (sourceVertexEquiv_lambdaWest W)

theorem toSourceCut_x {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (k : ℤ) :
    sourceVertexEquiv W (D.x k) = (toSourceCut D).x k := by
  dsimp only [M0CutData.x, DirectedDistances.KMSW.M0CutData.x,
    toSourceCut, toSourceRightRay, toSourceLeftChain]
  split_ifs
  · exact sourceVertexEquiv_lambdaWest W
  · exact sourceVertexEquiv_lambdaEast W
  · rfl
  · rfl

theorem cut_sdp_eq_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (u v : WholePlaneVertex W) :
    D.sdp u v = (toSourceCut D).sdp (sourceVertexEquiv W u) (sourceVertexEquiv W v) :=
  sdp_eq_source W H u v

theorem cut_ldp_eq_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (u v : WholePlaneVertex W) :
    D.ldp u v = (toSourceCut D).ldp (sourceVertexEquiv W u) (sourceVertexEquiv W v) :=
  ldp_eq_source W H u v

theorem cut_rootDart_eq_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) :
    sourceDartEquiv W D.rootDart = (toSourceCut D).rootDart := rfl

theorem boundaryOuterEdge_eq_source (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) :
    boundaryOuterEdge w h k = DirectedDistances.KMSW.boundaryOuterEdge w h k := by
  rfl

theorem sourceBoundaryHits {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0)) :
    BoundaryHitWitnesses (DirectedDistances.KMSW.shiftedStream W 0) := by
  simpa only [shiftedStream_eq_source] using h

theorem llPresence_iff_source (W : ℤ → Fin 3) (h : BoundaryHitWitnesses (shiftedStream W 0)) :
    (∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))) ↔
    (∀ k : ℤ, k ≤ 0 → DirectedDistances.KMSW.wholePlaneEdgePresent W
      (DirectedDistances.KMSW.wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (DirectedDistances.KMSW.shiftedStream W 0)
          (boundaryHitTime (DirectedDistances.KMSW.shiftedStream W 0)
            (sourceBoundaryHits h) (k - 1))))) := by
  constructor
  · intro hp k hk
    have he := (sourceEdgeEquiv_present W _).mp (hp k hk)
    simpa only [sourceEdgeEquiv_ι, shiftedStream_eq_source] using he
  · intro hp k hk
    apply (sourceEdgeEquiv_present W _).mpr
    simpa only [sourceEdgeEquiv_ι, shiftedStream_eq_source] using hp k hk

theorem m0CutData_nonempty (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    Nonempty (M0CutData W H) := by
  obtain ⟨D⟩ := DirectedDistances.KMSW.m0CutData_nonempty W (sourceHyp H)
    (sourceBoundaryHits h) ((llPresence_iff_source W h).mp hLL)
  exact ⟨fromSourceCut D⟩

@[expose] noncomputable def m0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))) : M0CutData W H :=
  Classical.choice (m0CutData_nonempty W H h hLL)

@[expose] noncomputable def sourceChosenCut (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    DirectedDistances.KMSW.M0CutData W (sourceHyp H) :=
  DirectedDistances.KMSW.m0CutData W (sourceHyp H) (sourceBoundaryHits h)
    ((llPresence_iff_source W h).mp hLL)

theorem chosen_x_eq_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (k : ℤ) :
    sourceVertexEquiv W ((m0CutData W H h hLL).x k) = (sourceChosenCut W H h hLL).x k := by
  have hx := (DirectedDistances.KMSW.m0CutData_eq_fields W (sourceHyp H)
    (sourceBoundaryHits h) ((llPresence_iff_source W h).mp hLL)
    (toSourceCut (m0CutData W H h hLL)) (sourceChosenCut W H h hLL)).2.2.2.2
  exact (toSourceCut_x (m0CutData W H h hLL) k).trans (congrFun hx k)

end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.KMSW.M0CutBusemann
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW
open Quiver
@[expose] def m0CutReachable (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (S : WholePlaneEdge W → Prop)
    (u v : WholePlaneVertex W) : Prop :=
  ∃ n, m0CutReachableLength (m0CutDirectedStep W H S) n u v
end DLQG1.Palomar.Model.KMSW
-- Source module DirectedDistances.PaperProofs.Section1.BusemannM0Identified
namespace DLQG1.Palomar.Model.PaperProofs.Section1
open MeasureTheory DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW (BoundaryHitWitnesses kmswLLCreatedEdge boundaryHitTime
  boundaryVertex futureMapRootDart EdgePresent edgeWest edgeEast PresentVertex
  presentLdp boundaryPresentVertex)
@[expose] def IsIdentifiedM0BusemannSDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        X k' - X k =
          ((D.sdp (D.x k') (y j)).toNat : ℤ) -
            ((D.sdp (D.x k) (y j)).toNat : ℤ)
@[expose] def IsIdentifiedM0BusemannLDP {W : ℤ → Fin 3}
    {H : WholePlaneRotationHypothesis W} (D : M0CutData W H) (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → WholePlaneVertex W, Function.Injective y →
      (∀ j, m0CutReachable W H D.seam (D.x k) (y j) ∧
        m0CutReachable W H D.seam (D.x k') (y j)) →
      ∃ N, ∀ j, N ≤ j →
        ∃ n n' : ℕ,
          D.ldp (D.x k') (y j) = ((n : ℕ∞) : WithBot ℕ∞) ∧
          D.ldp (D.x k) (y j) = ((n' : ℕ∞) : WithBot ℕ∞) ∧
          X k' - X k = (n : ℤ) - (n' : ℤ)
end DLQG1.Palomar.Model.PaperProofs.Section1
-- Source module DirectedDistances.Paper.Section1.BusemannM0
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW

theorem cutReachable_iff_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (u v : WholePlaneVertex W) :
    m0CutReachable W H D.seam u v ↔
      DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (sourceVertexEquiv W u) (sourceVertexEquiv W v) := by
  simp only [m0CutReachable, DirectedDistances.KMSW.m0CutReachable,
    M0CutData.seam, DirectedDistances.KMSW.M0CutData.seam, reachableLength_iff_source]

theorem boundaryReachable_iff_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k) (k : ℤ) (v : WholePlaneVertex W) :
    m0CutReachable W H D.seam (D.x k) v ↔
      DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (E.x k) (sourceVertexEquiv W v) := by
  simpa only [hx k] using cutReachable_iff_source D E (D.x k) v

theorem boundarySDP_eq_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k) (k : ℤ) (v : WholePlaneVertex W) :
    D.sdp (D.x k) v = E.sdp (E.x k) (sourceVertexEquiv W v) := by
  simpa only [hx k, M0CutData.sdp, DirectedDistances.KMSW.M0CutData.sdp,
    M0CutData.seam, DirectedDistances.KMSW.M0CutData.seam] using sdp_eq_source W H (D.x k) v

theorem boundaryLDP_eq_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k) (k : ℤ) (v : WholePlaneVertex W) :
    D.ldp (D.x k) v = E.ldp (E.x k) (sourceVertexEquiv W v) := by
  simpa only [hx k, M0CutData.ldp, DirectedDistances.KMSW.M0CutData.ldp,
    M0CutData.seam, DirectedDistances.KMSW.M0CutData.seam] using ldp_eq_source W H (D.x k) v
end DLQG1.Palomar.Model.KMSW

namespace DLQG1.Palomar.Model.PaperProofs.Section1
open DLQG1.Palomar.Model.KMSW

theorem identifiedSDP_iff_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k) (X : ℤ → ℤ) :
    IsIdentifiedM0BusemannSDP D X ↔
      DirectedDistances.PaperProofs.Section1.IsIdentifiedM0BusemannSDP E X := by
  constructor
  · rintro ⟨hnorm, hlim⟩
    refine ⟨hnorm, ?_⟩
    intro k k' y hy hreach
    have hy' : Function.Injective (fun j => (sourceVertexEquiv W).symm (y j)) :=
      (sourceVertexEquiv W).symm.injective.comp hy
    have hr : ∀ j, m0CutReachable W H D.seam (D.x k) ((sourceVertexEquiv W).symm (y j)) ∧
        m0CutReachable W H D.seam (D.x k') ((sourceVertexEquiv W).symm (y j)) := by
      intro j
      constructor
      · apply (boundaryReachable_iff_source D E hx k _).mpr
        simpa only [Equiv.apply_symm_apply] using (hreach j).1
      · apply (boundaryReachable_iff_source D E hx k' _).mpr
        simpa only [Equiv.apply_symm_apply] using (hreach j).2
    obtain ⟨N, hN⟩ := hlim k k' (fun j => (sourceVertexEquiv W).symm (y j)) hy' hr
    refine ⟨N, fun j hj => ?_⟩
    simpa only [boundarySDP_eq_source D E hx, Equiv.apply_symm_apply] using hN j hj
  · rintro ⟨hnorm, hlim⟩
    refine ⟨hnorm, ?_⟩
    intro k k' y hy hreach
    have hy' : Function.Injective (fun j => sourceVertexEquiv W (y j)) :=
      (sourceVertexEquiv W).injective.comp hy
    have hr : ∀ j, DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (E.x k) (sourceVertexEquiv W (y j)) ∧
        DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (E.x k') (sourceVertexEquiv W (y j)) := by
      intro j
      exact ⟨(boundaryReachable_iff_source D E hx k _).mp (hreach j).1,
        (boundaryReachable_iff_source D E hx k' _).mp (hreach j).2⟩
    obtain ⟨N, hN⟩ := hlim k k' (fun j => sourceVertexEquiv W (y j)) hy' hr
    refine ⟨N, fun j hj => ?_⟩
    simpa only [← boundarySDP_eq_source D E hx] using hN j hj

theorem identifiedLDP_iff_source {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k) (X : ℤ → ℤ) :
    IsIdentifiedM0BusemannLDP D X ↔
      DirectedDistances.PaperProofs.Section1.IsIdentifiedM0BusemannLDP E X := by
  constructor
  · rintro ⟨hnorm, hlim⟩
    refine ⟨hnorm, ?_⟩
    intro k k' y hy hreach
    have hy' : Function.Injective (fun j => (sourceVertexEquiv W).symm (y j)) :=
      (sourceVertexEquiv W).symm.injective.comp hy
    have hr : ∀ j, m0CutReachable W H D.seam (D.x k) ((sourceVertexEquiv W).symm (y j)) ∧
        m0CutReachable W H D.seam (D.x k') ((sourceVertexEquiv W).symm (y j)) := by
      intro j
      constructor
      · apply (boundaryReachable_iff_source D E hx k _).mpr
        simpa only [Equiv.apply_symm_apply] using (hreach j).1
      · apply (boundaryReachable_iff_source D E hx k' _).mpr
        simpa only [Equiv.apply_symm_apply] using (hreach j).2
    obtain ⟨N, hN⟩ := hlim k k' (fun j => (sourceVertexEquiv W).symm (y j)) hy' hr
    refine ⟨N, fun j hj => ?_⟩
    simpa only [boundaryLDP_eq_source D E hx, Equiv.apply_symm_apply] using hN j hj
  · rintro ⟨hnorm, hlim⟩
    refine ⟨hnorm, ?_⟩
    intro k k' y hy hreach
    have hy' : Function.Injective (fun j => sourceVertexEquiv W (y j)) :=
      (sourceVertexEquiv W).injective.comp hy
    have hr : ∀ j, DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (E.x k) (sourceVertexEquiv W (y j)) ∧
        DirectedDistances.KMSW.m0CutReachable W (sourceHyp H) E.seam
        (E.x k') (sourceVertexEquiv W (y j)) := by
      intro j
      exact ⟨(boundaryReachable_iff_source D E hx k _).mp (hreach j).1,
        (boundaryReachable_iff_source D E hx k' _).mp (hreach j).2⟩
    obtain ⟨N, hN⟩ := hlim k k' (fun j => sourceVertexEquiv W (y j)) hy' hr
    refine ⟨N, fun j hj => ?_⟩
    simpa only [← boundaryLDP_eq_source D E hx] using hN j hj
end DLQG1.Palomar.Model.PaperProofs.Section1
namespace DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW

theorem cut_sdp_eq_anySource {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (u v : WholePlaneVertex W) :
    D.sdp u v = E.sdp (sourceVertexEquiv W u) (sourceVertexEquiv W v) :=
  sdp_eq_source W H u v

theorem cut_ldp_eq_anySource {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H))
    (u v : WholePlaneVertex W) :
    D.ldp u v = E.ldp (sourceVertexEquiv W u) (sourceVertexEquiv W v) :=
  ldp_eq_source W H u v

theorem cut_rootDart_eq_anySource {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
    (D : M0CutData W H) (E : DirectedDistances.KMSW.M0CutData W (sourceHyp H)) :
    sourceDartEquiv W D.rootDart = E.rootDart := rfl

theorem seamVertex_iff_source (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (v : WholePlaneVertex W) :
    (∃ e, m0CutSeamEdge W H e ∧
      (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)) ↔
    (∃ e, DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H) e ∧
      (DirectedDistances.KMSW.wholePlaneEdgeWest W e = sourceVertexEquiv W v ∨
       DirectedDistances.KMSW.wholePlaneEdgeEast W e = sourceVertexEquiv W v)) := by
  constructor
  · rintro ⟨e, he, hw | heast⟩
    · exact ⟨sourceEdgeEquiv W e, (seam_iff_source W H e).mp he,
        Or.inl ((sourceEdgeEquiv_west W e).symm.trans (congrArg (sourceVertexEquiv W) hw))⟩
    · exact ⟨sourceEdgeEquiv W e, (seam_iff_source W H e).mp he,
        Or.inr ((sourceEdgeEquiv_east W e).symm.trans (congrArg (sourceVertexEquiv W) heast))⟩
  · rintro ⟨e', he, hv⟩
    obtain ⟨e, rfl⟩ := (sourceEdgeEquiv W).surjective e'
    refine ⟨e, (seam_iff_source W H e).mpr he, ?_⟩
    rcases hv with hw | heast
    · exact Or.inl ((sourceVertexEquiv W).injective ((sourceEdgeEquiv_west W e).trans hw))
    · exact Or.inr ((sourceVertexEquiv W).injective ((sourceEdgeEquiv_east W e).trans heast))

theorem wholePlaneIIDCodeMeasure_eq_source :
    DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure =
      DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure := rfl
end DLQG1.Palomar.Model.KMSW

namespace DLQG1.Palomar.Principal
open DirectedDistances
open MeasureTheory DLQG1.Palomar.Model.KMSW
open DirectedDistances.KMSW (BoundaryHitWitnesses kmswLLCreatedEdge boundaryHitTime
  boundaryVertex futureMapRootDart EdgePresent edgeWest edgeEast PresentVertex
  presentLdp boundaryPresentVertex)
open DLQG1.Palomar.Model.PaperProofs.Section1
theorem busemann :
    ∀ᵐ W ∂DLQG1.Palomar.Model.RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
        ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
          (wholePlaneEdgeι W 0
            (kmswLLCreatedEdge (shiftedStream W 0)
              (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        let w := shiftedStream W 0
        let V := wholePlaneVertexι W 0
        let E := wholePlaneEdgeι W 0
        let D := m0CutData W H h hLL
        (Function.Injective V ∧
        Set.range V = m0CutLeftVertices W H (m0CutSeamEdge W H) ∧
        Function.Injective E ∧
        Set.range E = m0CutLeftEdges W H (m0CutSeamEdge W H) ∧
        (∀ k, (D).x k = V (boundaryVertex w h k)) ∧
        ((D).rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
          (D).rootDart.1 = E 0 ∧ E 0 = m0CutLambdaZero W ∧
          wholePlaneEdgeWest W (D).rootDart.1 = (D).x 0 ∧
          wholePlaneEdgeEast W (D).rootDart.1 = (D).x 1 ∧
          wholePlaneEdgePresent W (D).rootDart.1 ∧ (D).tail (D).rootDart) ∧
        (∀ e, EdgePresent w e ↔
          (wholePlaneEdgePresent W (E e) ∧
            ¬ ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k)) ∧
        (∀ e, (D).missing (E e) ↔
          ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge w h k) ∧
        (∀ a b, m0CutDirectedStep W H (m0CutSeamEdge W H) (V a) (V b) ↔
          ∃ e, EdgePresent w e ∧ V (edgeWest w e) = V a ∧ V (edgeEast w e) = V b) ∧
        (∀ a b, (D).sdp (V a) (V b) =
          DirectedDistances.sdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ a b, (D).ldp (V a) (V b) = presentLdp (⟨a⟩ : PresentVertex w) ⟨b⟩) ∧
        (∀ k k', (D).sdp ((D).x k) ((D).x k') =
          DirectedDistances.sdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k')) ∧
        (∀ k k', (D).ldp ((D).x k) ((D).x k') =
          presentLdp (boundaryPresentVertex w h k) (boundaryPresentVertex w h k'))) ∧
        Function.Injective D.x ∧
        Set.range D.x = {v | ∃ e, m0CutSeamEdge W H e ∧
          (wholePlaneEdgeWest W e = v ∨ wholePlaneEdgeEast W e = v)} ∧
        (∀ k : ℤ,
          m0CutSeamEdge W H
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) ∧
          wholePlaneEdgeWest W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) = D.x k ∧
          wholePlaneEdgeEast W
              (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h k)) =
            D.x (k + 1)) ∧
        (wholePlaneEdgeι W 0 (boundaryOuterEdge (shiftedStream W 0) h 0) =
            m0CutLambdaZero W ∧
          m0CutSeamEdge W H (m0CutLambdaZero W) ∧
          wholePlaneEdgeWest W (m0CutLambdaZero W) = D.x 0 ∧
          wholePlaneEdgeEast W (m0CutLambdaZero W) = D.x 1) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b → D.sdp a b ≠ ⊤) ∧
        (∀ a b : WholePlaneVertex W, m0CutReachable W H D.seam a b →
          ∃ n : ℕ, D.ldp a b = ((n : ℕ∞) : WithBot ℕ∞)) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannSDP D X) ∧
        (∃! X : ℤ → ℤ, IsIdentifiedM0BusemannLDP D X) := by
  rw [wholePlaneIIDCodeMeasure_eq_source]
  filter_upwards [DirectedDistances.Paper.Section1.thm_busemann] with W hW
  rcases hW with ⟨H₀, h₀, hLL₀, hW⟩
  let H : WholePlaneRotationHypothesis W := (rotationHyp_iff_source W).mpr H₀
  have h : BoundaryHitWitnesses (shiftedStream W 0) := by
    simpa only [shiftedStream_eq_source] using h₀
  have hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))) :=
    (llPresence_iff_source W h).mpr hLL₀
  refine ⟨H, h, hLL, ?_⟩
  dsimp only [shiftedStream, DirectedDistances.KMSW.shiftedStream] at hW ⊢
  let D := m0CutData W H h hLL
  let E := sourceChosenCut W H h hLL
  have hx : ∀ k, sourceVertexEquiv W (D.x k) = E.x k := chosen_x_eq_source W H h hLL
  have hE : E = DirectedDistances.KMSW.m0CutData W H₀ h₀ hLL₀ := by rfl
  rw [← hE] at hW
  rcases hW with ⟨hid, hinjx, hrangex, hboundary, hroot, hfiniteS, hfiniteL, hsdp, hldp⟩
  rcases hid with ⟨hvinj, hvrange, heinj, herange, hlabels, hrest⟩
  rcases hrest with ⟨hrootD, hpresent, hmissing, hstep, hsdist, hldist, hsbdy, hlbdy⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      apply hvinj
      exact (sourceVertexEquiv_ι W 0 a).symm.trans
        ((congrArg (sourceVertexEquiv W) hab).trans (sourceVertexEquiv_ι W 0 b))
    · ext v
      constructor
      · rintro ⟨n, rfl⟩
        apply (leftVertices_iff_source W H _).mpr
        rw [← hvrange]
        exact ⟨n, (sourceVertexEquiv_ι W 0 n).symm⟩
      · intro hv
        have hv' := (leftVertices_iff_source W H v).mp hv
        rw [← hvrange] at hv'
        obtain ⟨n, hn⟩ := hv'
        exact ⟨n, (sourceVertexEquiv W).injective ((sourceVertexEquiv_ι W 0 n).trans hn)⟩
    · intro a b hab
      apply heinj
      exact (sourceEdgeEquiv_ι W 0 a).symm.trans
        ((congrArg (sourceEdgeEquiv W) hab).trans (sourceEdgeEquiv_ι W 0 b))
    · ext e
      constructor
      · rintro ⟨n, rfl⟩
        apply (leftEdges_iff_source W H _).mpr
        rw [← herange]
        exact ⟨n, (sourceEdgeEquiv_ι W 0 n).symm⟩
      · intro he
        have he' := (leftEdges_iff_source W H e).mp he
        rw [← herange] at he'
        obtain ⟨n, hn⟩ := he'
        exact ⟨n, (sourceEdgeEquiv W).injective ((sourceEdgeEquiv_ι W 0 n).trans hn)⟩
    · intro k
      apply (sourceVertexEquiv W).injective
      rw [hx k, sourceVertexEquiv_ι]
      simpa only [D, shiftedStream_eq_source] using hlabels k
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hd := hrootD
        simp only [D, ← cut_rootDart_eq_anySource D E, sourceDartEquiv_fst,
          ← sourceDartEquiv_ι, ← sourceEdgeEquiv_ι, ← sourceEdgeEquiv_lambdaZero,
          ← sourceEdgeEquiv_west, ← sourceEdgeEquiv_east, ← hx,
          ← sourceEdgeEquiv_present, DirectedDistances.KMSW.M0CutData.tail,
          ← cutTail_iff_source W H,
          (sourceEdgeEquiv W).injective.eq_iff,
          (sourceVertexEquiv W).injective.eq_iff] at hd
        exact ⟨(sourceDartEquiv W).injective hd.1, hd.2⟩
      · intro e
        simpa only [D, ← sourceEdgeEquiv_ι, ← sourceEdgeEquiv_present,
          shiftedStream_eq_source, boundaryOuterEdge_eq_source] using hpresent e
      · intro e
        simpa only [D, M0CutData.missing, DirectedDistances.KMSW.M0CutData.missing,
          ← sourceEdgeEquiv_ι, ← missing_iff_source W H,
          shiftedStream_eq_source, boundaryOuterEdge_eq_source] using hmissing e
      · intro a b
        simpa only [D, ← sourceVertexEquiv_ι, ← directedStep_iff_source W H,
          (sourceVertexEquiv W).injective.eq_iff, shiftedStream_eq_source] using hstep a b
      · intro a b
        have he := hsdist a b
        simp only [D, ← sourceVertexEquiv_ι, ← cut_sdp_eq_anySource D E] at he
        exact he
      · intro a b
        have he := hldist a b
        simp only [D, ← sourceVertexEquiv_ι, ← cut_ldp_eq_anySource D E] at he
        exact he
      · intro k k'
        have he := hsbdy k k'
        simp only [D, ← hx, ← cut_sdp_eq_anySource D E] at he
        exact he
      · intro k k'
        have he := hlbdy k k'
        simp only [D, ← hx, ← cut_ldp_eq_anySource D E] at he
        exact he
  · intro k k' he
    apply hinjx
    exact (hx k).symm.trans ((congrArg (sourceVertexEquiv W) he).trans (hx k'))
  · ext v
    have hsrc : (∃ k, E.x k = sourceVertexEquiv W v) ↔
        ∃ e, DirectedDistances.KMSW.m0CutSeamEdge W (sourceHyp H) e ∧
          (DirectedDistances.KMSW.wholePlaneEdgeWest W e = sourceVertexEquiv W v ∨
           DirectedDistances.KMSW.wholePlaneEdgeEast W e = sourceVertexEquiv W v) := by
      change sourceVertexEquiv W v ∈ Set.range E.x ↔ _
      rw [hrangex]
      rfl
    constructor
    · rintro ⟨k, hk⟩
      apply (seamVertex_iff_source W H v).mpr
      exact hsrc.mp ⟨k, (hx k).symm.trans (congrArg (sourceVertexEquiv W) hk)⟩
    · intro hv
      obtain ⟨k, hk⟩ := hsrc.mpr ((seamVertex_iff_source W H v).mp hv)
      exact ⟨k, (sourceVertexEquiv W).injective ((hx k).trans hk)⟩
  · intro k
    simpa only [D, ← sourceEdgeEquiv_ι, ← seam_iff_source W H,
      ← sourceEdgeEquiv_west, ← sourceEdgeEquiv_east, ← hx,
      (sourceVertexEquiv W).injective.eq_iff, shiftedStream_eq_source,
      boundaryOuterEdge_eq_source] using hboundary k
  · simpa only [D, ← sourceEdgeEquiv_ι, ← sourceEdgeEquiv_lambdaZero, ← seam_iff_source W H,
      ← sourceEdgeEquiv_west, ← sourceEdgeEquiv_east, ← hx,
      (sourceEdgeEquiv W).injective.eq_iff, (sourceVertexEquiv W).injective.eq_iff,
      shiftedStream_eq_source, boundaryOuterEdge_eq_source] using hroot
  · intro u v hr
    rw [cut_sdp_eq_anySource D E]
    exact hfiniteS _ _ ((cutReachable_iff_source D E u v).mp hr)
  · intro u v hr
    obtain ⟨n, hn⟩ := hfiniteL _ _ ((cutReachable_iff_source D E u v).mp hr)
    exact ⟨n, (cut_ldp_eq_anySource D E u v).trans hn⟩
  · obtain ⟨X, hX, hu⟩ := hsdp
    exact ⟨X, (identifiedSDP_iff_source D E hx X).mpr hX,
      fun Y hY => hu Y ((identifiedSDP_iff_source D E hx Y).mp hY)⟩
  · obtain ⟨X, hX, hu⟩ := hldp
    exact ⟨X, (identifiedLDP_iff_source D E hx X).mpr hX,
      fun Y hY => hu Y ((identifiedLDP_iff_source D E hx Y).mp hY)⟩
end DLQG1.Palomar.Principal
end BusemannInterface
