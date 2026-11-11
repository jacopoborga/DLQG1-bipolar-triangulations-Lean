module

public import DirectedDistances.KMSW.WholePlaneRootedMapLocalFinite
public import DirectedDistances.PaperProofs.Section5.UIBHBOTRootFrame
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMap
public import DirectedDistances.KMSW.KMSWFutureMapOuterBoundary
public import DirectedDistances.PlanarMap.RootedLocallyFiniteBallFramed
import DirectedDistances.KMSW.StageEdgesConnected
import DirectedDistances.KMSW.WholePlaneLeftBoundaryPresent
import DirectedDistances.KMSW.UIBHBOTRotationHypothesis
import DirectedDistances.KMSW.WholePlaneLeftBoundaryTerminal

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PaperProofs.Section5
open DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open Quiver

private def wholePlaneRunBase (W : ℤ → Fin 3) (N : ℕ) (d : ℕ × Bool) : ℕ :=
  kmswLimitDartVertex (shiftedStream W N) d

private theorem wholePlaneRunBase_trans (W : ℤ → Fin 3) (N M : ℕ)
    (hNM : N ≤ M) (d : ℕ × Bool) :
    wholePlaneRunBase W M (wholePlaneDartTrans W N M hNM d) =
      wholePlaneVertexTrans W N M hNM (wholePlaneRunBase W N d) := by
  rcases d with ⟨e, b⟩
  cases b with
  | false =>
      change edgeWest (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) = _
      exact wholePlaneEdgeTrans_west W N M hNM e
  | true =>
      change edgeEast (shiftedStream W M) (wholePlaneEdgeTrans W N M hNM e) = _
      exact wholePlaneEdgeTrans_east W N M hNM e

private theorem wholePlaneRunBase_rotation (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (N : ℕ) (d : ℕ × Bool) :
    wholePlaneRunBase W N (kmswInfRot (shiftedStream W N) (H.1 N) d) =
      wholePlaneRunBase W N d := by
  exact kmswLimitDartVertex_rot (shiftedStream W N) (H.1 N) d

private theorem wholePlaneRunBase_rotation_symm (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ) (d : ℕ × Bool) :
    wholePlaneRunBase W N ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d) =
      wholePlaneRunBase W N d := by
  simpa only [Equiv.apply_symm_apply] using
    (wholePlaneRunBase_rotation W H N
      ((kmswInfRot (shiftedStream W N) (H.1 N)).symm d)).symm

private theorem wholePlaneSameCycle_reach (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) {d e : WholePlaneDart W}
    (h : (wholePlaneRotation W H).SameCycle d e) :
    Relation.ReflTransGen
      (fun x y : WholePlaneDart W =>
        y = wholePlaneRotation W H x ∨
          y = (wholePlaneRotation W H).symm x) d e := by
  obtain ⟨i, hi⟩ := h
  have hpath (i : ℤ) : Relation.ReflTransGen
      (fun x y : WholePlaneDart W =>
        y = wholePlaneRotation W H x ∨
          y = (wholePlaneRotation W H).symm x) d ((wholePlaneRotation W H ^ i) d) := by
    refine Int.induction_on i ?_ ?_ ?_
    · exact Relation.ReflTransGen.refl
    · intro i ih
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      exact ih.tail (Or.inl rfl)
    · intro i ih
      have hneg : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by ring
      rw [hneg, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact ih.tail (Or.inr rfl)
  rw [← hi]
  exact hpath i

private theorem wholePlaneDartVertex_stage (W : ℤ → Fin 3) (N n : ℕ)
    (d : StageDart (kmswStage (shiftedStream W N) n).nextEdge) :
    wholePlaneDartVertex W (wholePlaneDartι W N (d.1.val, d.2)) =
      wholePlaneVertexι W N (stageEndpoint (kmswStage (shiftedStream W N) n) d) := by
  rw [wholePlaneDartVertex_ι]
  obtain ⟨hw, he⟩ := edge_endpoints_eq (shiftedStream W N) d.1.isLt
  cases hb : d.2 <;>
    simp [kmswLimitDartVertex, stageEndpoint, hb, hw, he]

private theorem stageEndpoint_rot (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) (stageRot w n d) =
      stageEndpoint (kmswStage w n) d := by
  have hcycle : (stageRot w n).SameCycle d (stageRot w n d) := ⟨1, rfl⟩
  exact ((stageRot_sameCycle_iff_endpoint_eq w n d (stageRot w n d)).1 hcycle).symm

private theorem stageEndpoint_rot_symm (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((stageRot w n).symm d) =
      stageEndpoint (kmswStage w n) d := by
  have hcycle : (stageRot w n).SameCycle ((stageRot w n).symm d) d :=
    ⟨1, by simp⟩
  exact (stageRot_sameCycle_iff_endpoint_eq w n ((stageRot w n).symm d) d).1 hcycle


private theorem wholePlaneSameCycle_map_of_intertwining
    {A B : Type*} (f : Equiv.Perm A) (g : Equiv.Perm B) (I : B → A)
    (P : B → Prop)
    (hf : ∀ x, P x → f (I x) = I (g x))
    (hfi : ∀ x, P x → f.symm (I x) = I (g.symm x))
    (hP : ∀ x, P x → P (g x))
    (hPi : ∀ x, P x → P (g.symm x))
    {x y : B} (hx : P x) (hxy : g.SameCycle x y) :
    f.SameCycle (I x) (I y) := by
  obtain ⟨i, hi⟩ := hxy
  have hbase : ∀ i : ℤ, P ((g ^ i) x) := by
    intro i
    refine Int.induction_on i ?_ ?_ ?_
    · simpa using hx
    · intro i hi
      have hmul : g ((g ^ (i : ℤ)) x) = (g ^ (1 + (i : ℤ))) x := by
        simp only [Equiv.Perm.mul_apply, zpow_one_add]
      rw [show (i : ℤ) + 1 = 1 + (i : ℤ) from Int.add_comm _ _]
      simpa only [← hmul] using hP _ hi
    · intro i hi
      have hneg : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by ring
      have hinv : g⁻¹ = g.symm := by
        ext z
        rfl
      have hmulPerm : g.symm * g ^ (-(i : ℤ)) =
          g ^ (-1 + -(i : ℤ)) := by
        simpa only [zpow_neg_one, hinv] using
          (zpow_add g (-1) (-(i : ℤ))).symm
      have hmul : g.symm ((g ^ (-(i : ℤ))) x) =
          (g ^ (-1 + -(i : ℤ))) x := by
        calc
          g.symm ((g ^ (-(i : ℤ))) x) =
              (g.symm * g ^ (-(i : ℤ))) x := by rw [Equiv.Perm.mul_apply]
          _ = (g ^ (-1 + -(i : ℤ))) x :=
            congrArg (fun p : Equiv.Perm B => p x) hmulPerm
      rw [hneg]
      simpa only [← hmul] using hPi _ hi
  have hpow : ∀ i : ℤ, (f ^ i) (I x) = I ((g ^ i) x) := by
    intro i
    refine Int.induction_on i ?_ ?_ ?_
    · simp
    · intro i hi
      have hmulF : f ^ (1 + (i : ℤ)) = f * f ^ (i : ℤ) := zpow_one_add _ _
      have hmulG : g ^ (1 + (i : ℤ)) = g * g ^ (i : ℤ) := zpow_one_add _ _
      calc
        (f ^ ((i : ℤ) + 1)) (I x) = (f ^ (1 + (i : ℤ))) (I x) := by
          exact congrArg (fun n : ℤ => (f ^ n) (I x)) (Int.add_comm _ _)
        _ = (f * f ^ (i : ℤ)) (I x) := congrArg (fun p : Equiv.Perm A => p (I x)) hmulF
        _ = f ((f ^ (i : ℤ)) (I x)) := by rw [Equiv.Perm.mul_apply]
        _ = f (I ((g ^ (i : ℤ)) x)) := congrArg f hi
        _ = I (g ((g ^ (i : ℤ)) x)) := hf _ (hbase i)
        _ = I ((g ^ (1 + (i : ℤ))) x) := by
          have heval := congrArg (fun p : Equiv.Perm B => p x) hmulG.symm
          simpa only [Equiv.Perm.mul_apply] using congrArg I heval
        _ = I ((g ^ ((i : ℤ) + 1)) x) := by
          exact congrArg (fun n : ℤ => I ((g ^ n) x)) (Int.add_comm _ _).symm
    · intro i hi
      have hneg : (-(i : ℤ) - 1) = -1 + -(i : ℤ) := by ring
      have hinvF : f⁻¹ = f.symm := by
        ext z
        rfl
      have hinvG : g⁻¹ = g.symm := by
        ext z
        rfl
      have hmulF : f ^ (-1 + -(i : ℤ)) = f.symm * f ^ (-(i : ℤ)) := by
        rw [zpow_add, zpow_neg_one, hinvF]
      have hmulPermG : g.symm * g ^ (-(i : ℤ)) =
          g ^ (-1 + -(i : ℤ)) := by
        simpa only [zpow_neg_one, hinvG] using
          (zpow_add g (-1) (-(i : ℤ))).symm
      have hmulG : g.symm ((g ^ (-(i : ℤ))) x) =
          (g ^ (-1 + -(i : ℤ))) x := by
        calc
          g.symm ((g ^ (-(i : ℤ))) x) =
              (g.symm * g ^ (-(i : ℤ))) x := by rw [Equiv.Perm.mul_apply]
          _ = (g ^ (-1 + -(i : ℤ))) x :=
            congrArg (fun p : Equiv.Perm B => p x) hmulPermG
      calc
        (f ^ (-(i : ℤ) - 1)) (I x) = (f ^ (-1 + -(i : ℤ))) (I x) := by
          rw [hneg]
        _ = (f.symm * f ^ (-(i : ℤ))) (I x) :=
          congrArg (fun p : Equiv.Perm A => p (I x)) hmulF
        _ = f.symm ((f ^ (-(i : ℤ))) (I x)) := by rw [Equiv.Perm.mul_apply]
        _ = f.symm (I ((g ^ (-(i : ℤ))) x)) := congrArg f.symm hi
        _ = I (g.symm ((g ^ (-(i : ℤ))) x)) := hfi _ (hbase (-(i : ℤ)))
        _ = I ((g ^ (-1 + -(i : ℤ))) x) := congrArg I hmulG
        _ = I ((g ^ (-(i : ℤ) - 1)) x) := by rw [hneg]
  refine ⟨i, ?_⟩
  rw [hpow i, hi]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Darts incident to one geometric vertex lie in one whole-plane rotation cycle. -/
theorem wholePlaneRotation_sameVertex_sameCycle_proof
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) :
    wholePlaneRotation_sameVertex_sameCycle W H := by
  intro d e hde
  obtain ⟨⟨N, ed⟩, hdeEdge⟩ := Quotient.exists_rep d.1
  obtain ⟨⟨M, ee⟩, heeEdge⟩ := Quotient.exists_rep e.1
  let K := max N M
  have hNK : N ≤ K := Nat.le_max_left N M
  have hMK : M ≤ K := Nat.le_max_right N M
  let dK := wholePlaneDartTrans W N K hNK (ed, d.2)
  let eK := wholePlaneDartTrans W M K hMK (ee, e.2)
  have hdRep : wholePlaneDartι W N (ed, d.2) = d := by
    change (wholePlaneEdgeι W N ed, d.2) = (d.1, d.2)
    exact Prod.ext hdeEdge rfl
  have heRep : wholePlaneDartι W M (ee, e.2) = e := by
    change (wholePlaneEdgeι W M ee, e.2) = (e.1, e.2)
    exact Prod.ext heeEdge rfl
  have hdK : wholePlaneDartι W K dK = d := by
    exact (congrFun (wholePlaneDartι_trans W N K hNK) (ed, d.2)).trans hdRep
  have heK : wholePlaneDartι W K eK = e := by
    exact (congrFun (wholePlaneDartι_trans W M K hMK) (ee, e.2)).trans heRep
  have hbaseK : wholePlaneRunBase W K dK = wholePlaneRunBase W K eK := by
    apply wholePlaneVertexι_injective W K
    calc
      wholePlaneVertexι W K (wholePlaneRunBase W K dK) =
          wholePlaneDartVertex W (wholePlaneDartι W K dK) :=
        (wholePlaneDartVertex_ι W K dK).symm
      _ = wholePlaneDartVertex W d := congrArg (wholePlaneDartVertex W) hdK
      _ = wholePlaneDartVertex W e := hde
      _ = wholePlaneDartVertex W (wholePlaneDartι W K eK) :=
        congrArg (wholePlaneDartVertex W) heK.symm
      _ = wholePlaneVertexι W K (wholePlaneRunBase W K eK) :=
        wholePlaneDartVertex_ι W K eK
  obtain ⟨L, hKL, hfresh⟩ := H.2 K (wholePlaneRunBase W K dK)
  let dL := wholePlaneDartTrans W K L hKL dK
  let eL := wholePlaneDartTrans W K L hKL eK
  have hdL : wholePlaneDartι W L dL = d :=
    (congrFun (wholePlaneDartι_trans W K L hKL) dK).trans hdK
  have heL : wholePlaneDartι W L eL = e :=
    (congrFun (wholePlaneDartι_trans W K L hKL) eK).trans heK
  have hbaseL : wholePlaneRunBase W L dL = wholePlaneRunBase W L eL := by
    calc
      wholePlaneRunBase W L dL =
          wholePlaneVertexTrans W K L hKL (wholePlaneRunBase W K dK) :=
        wholePlaneRunBase_trans W K L hKL dK
      _ = wholePlaneVertexTrans W K L hKL (wholePlaneRunBase W K eK) :=
        congrArg _ hbaseK
      _ = wholePlaneRunBase W L eL := (wholePlaneRunBase_trans W K L hKL eK).symm
  have hlocal := kmswLimitDart_same_vertex_sameCycle
    (shiftedStream W L) (H.1 L) dL eL hbaseL
  let σ := kmswInfRot (shiftedStream W L) (H.1 L)
  let I := wholePlaneDartι W L
  let vL := wholePlaneRunBase W L dL
  have hdBase : wholePlaneRunBase W L dL =
      wholePlaneVertexTrans W K L hKL (wholePlaneRunBase W K dK) :=
    wholePlaneRunBase_trans W K L hKL dK
  have hfreshAt (x : ℕ × Bool) (hx : wholePlaneRunBase W L x = vL) :
      ∀ Q (hLQ : L ≤ Q), wholePlaneFresh W L Q hLQ (wholePlaneRunBase W L x) := by
    intro Q hLQ
    change (kmswStage (shiftedStream W Q) (Q - L)).nextVertex ≤
      wholePlaneVertexTrans W L Q hLQ (wholePlaneRunBase W L x)
    rw [hx]
    change (kmswStage (shiftedStream W Q) (Q - L)).nextVertex ≤
      wholePlaneVertexTrans W L Q hLQ (wholePlaneRunBase W L dL)
    rw [hdBase]
    exact hfresh Q hLQ
  have hforward : ∀ x, wholePlaneRunBase W L x = vL →
      wholePlaneRotation W H (I x) = I (σ x) := by
    intro x hx
    exact wholePlaneRotation_ι_of_fresh W H L x (hfreshAt x hx)
  have hbackward : ∀ x, wholePlaneRunBase W L x = vL →
      (wholePlaneRotation W H).symm (I x) = I (σ.symm x) := by
    intro x hx
    exact wholePlaneRotation_symm_ι_of_fresh W H L x (hfreshAt x hx)
  have hP : ∀ x, wholePlaneRunBase W L x = vL →
      wholePlaneRunBase W L (σ x) = vL := by
    intro x hx
    rw [wholePlaneRunBase_rotation W H L x, hx]
  have hPi : ∀ x, wholePlaneRunBase W L x = vL →
      wholePlaneRunBase W L (σ.symm x) = vL := by
    intro x hx
    rw [wholePlaneRunBase_rotation_symm W H L x, hx]
  have hcycle := wholePlaneSameCycle_map_of_intertwining
    (wholePlaneRotation W H) σ I (fun x => wholePlaneRunBase W L x = vL)
    hforward hbackward hP hPi rfl hlocal
  simpa only [I, hdL, heL] using hcycle

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The whole-plane geometric dart graph is connected. Source: -/
theorem wholePlaneDart_connected (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    ∀ d e : WholePlaneDart W, Relation.ReflTransGen
      (fun x y : WholePlaneDart W =>
        y = wholePlaneRotation W H x ∨ y = (wholePlaneRotation W H).symm x ∨
          y = wholePlaneDartFlip W x ∨ y = (wholePlaneDartFlip W).symm x) d e := by
  intro d e
  obtain ⟨⟨N, ed⟩, hdEdge⟩ := Quotient.exists_rep d.1
  obtain ⟨⟨M, ee⟩, heEdge⟩ := Quotient.exists_rep e.1
  let K := max N M
  have hNK : N ≤ K := Nat.le_max_left N M
  have hMK : M ≤ K := Nat.le_max_right N M
  let dK := wholePlaneDartTrans W N K hNK (ed, d.2)
  let eK := wholePlaneDartTrans W M K hMK (ee, e.2)
  have hd : wholePlaneDartι W K dK = d := by
    exact (congrFun (wholePlaneDartι_trans W N K hNK) (ed, d.2)).trans <| by
      change (wholePlaneEdgeι W N ed, d.2) = (d.1, d.2)
      exact Prod.ext hdEdge rfl
  have he : wholePlaneDartι W K eK = e := by
    exact (congrFun (wholePlaneDartι_trans W M K hMK) (ee, e.2)).trans <| by
      change (wholePlaneEdgeι W M ee, e.2) = (e.1, e.2)
      exact Prod.ext heEdge rfl
  let w := shiftedStream W K
  let n := max dK.1 eK.1
  have hdn : dK.1 < (kmswStage w n).nextEdge := by
    exact (kmsw_edge_allocated_by_self w dK.1).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_left dK.1 eK.1))
  have hen : eK.1 < (kmswStage w n).nextEdge := by
    exact (kmsw_edge_allocated_by_self w eK.1).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_right dK.1 eK.1))
  let x : StageDart (kmswStage w n).nextEdge := (⟨dK.1, hdn⟩, dK.2)
  let y : StageDart (kmswStage w n).nextEdge := (⟨eK.1, hen⟩, eK.2)
  let I : StageDart (kmswStage w n).nextEdge → WholePlaneDart W :=
    fun z => wholePlaneDartι W K (z.1.val, z.2)
  have hstart : I x = d := by
    dsimp [I, x, w]
    rw [← hd]
  have hend : I y = e := by
    dsimp [I, y, w]
    rw [← he]
  have hlocal := kmswMap_isConnected w n x y
  change Relation.ReflTransGen
    (fun a b : StageDart (kmswStage w n).nextEdge =>
      b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
        b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a)
    x y at hlocal
  have hstep : ∀ {a b : StageDart (kmswStage w n).nextEdge},
      (b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
        b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a) →
      Relation.ReflTransGen
        (fun p q : WholePlaneDart W =>
          q = wholePlaneRotation W H p ∨ q = (wholePlaneRotation W H).symm p ∨
            q = wholePlaneDartFlip W p ∨ q = (wholePlaneDartFlip W).symm p)
        (I a) (I b) := by
    intro a b hab
    rcases hab with hr | hr | hf | hf
    · subst b
      have hv : wholePlaneDartVertex W (I a) =
          wholePlaneDartVertex W (I ((kmswMap w n).rot a)) := by
        rw [wholePlaneDartVertex_stage, wholePlaneDartVertex_stage,
          kmswMap_rot]
        exact congrArg (wholePlaneVertexι W K)
          (stageEndpoint_rot w n a).symm
      have hcycle := wholePlaneRotation_sameVertex_sameCycle_proof W H (I a)
        (I ((kmswMap w n).rot a)) hv
      have hreach := wholePlaneSameCycle_reach W H hcycle
      refine Relation.ReflTransGen.mono ?_ _ _ hreach
      intro p q hpq
      rcases hpq with hpq | hpq
      · exact Or.inl hpq
      · exact Or.inr (Or.inl hpq)
    · subst b
      let a' := ((kmswMap w n).rot).symm a
      have hv : wholePlaneDartVertex W (I a) = wholePlaneDartVertex W (I a') := by
        rw [wholePlaneDartVertex_stage, wholePlaneDartVertex_stage]
        dsimp [a']
        rw [kmswMap_rot]
        exact congrArg (wholePlaneVertexι W K)
          (stageEndpoint_rot_symm w n a).symm
      have hcycle := wholePlaneRotation_sameVertex_sameCycle_proof W H (I a) (I a') hv
      have hreach := wholePlaneSameCycle_reach W H hcycle
      refine Relation.ReflTransGen.mono ?_ _ _ hreach
      intro p q hpq
      rcases hpq with hpq | hpq
      · exact Or.inl hpq
      · exact Or.inr (Or.inl hpq)
    · subst b
      have hflip : I ((kmswMap w n).edgeInv a) = wholePlaneDartFlip W (I a) := by
        rcases a with ⟨⟨f, hf⟩, b⟩
        rfl
      exact Relation.ReflTransGen.single
        (Or.inr (Or.inr (Or.inl hflip)))
    · subst b
      have hflip : I ((kmswMap w n).edgeInv.symm a) =
          wholePlaneDartFlip W (I a) := by
        have hinv : (kmswMap w n).edgeInv.symm = (kmswMap w n).edgeInv := by
          apply Equiv.ext
          intro z
          apply (kmswMap w n).edgeInv.injective
          rw [Equiv.apply_symm_apply, (kmswMap w n).edgeInv_invol]
        rw [hinv]
        rcases a with ⟨⟨f, hf⟩, b⟩
        rfl
      exact Relation.ReflTransGen.single
        (Or.inr (Or.inr (Or.inl hflip)))
  have hmap : Relation.ReflTransGen
      (fun p q : WholePlaneDart W =>
        q = wholePlaneRotation W H p ∨ q = (wholePlaneRotation W H).symm p ∨
          q = wholePlaneDartFlip W p ∨ q = (wholePlaneDartFlip W).symm p)
      (I x) (I y) := by
    have hmap' : ∀ {z}, Relation.ReflTransGen
        (fun a b : StageDart (kmswStage w n).nextEdge =>
          b = (kmswMap w n).rot a ∨ b = (kmswMap w n).rot.symm a ∨
            b = (kmswMap w n).edgeInv a ∨ b = (kmswMap w n).edgeInv.symm a)
        x z → Relation.ReflTransGen
          (fun p q : WholePlaneDart W =>
            q = wholePlaneRotation W H p ∨ q = (wholePlaneRotation W H).symm p ∨
              q = wholePlaneDartFlip W p ∨ q = (wholePlaneDartFlip W).symm p)
          (I x) (I z) := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b hab hbc ih => exact ih.trans (hstep hbc)
    exact hmap' hlocal
  simpa only [hstart, hend] using hmap


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The tail dart predicate uses the false side of present edges, as in the KMSW -/
@[expose] def wholePlaneDartTail (W : ℤ → Fin 3) : WholePlaneDart W → Prop :=
  fun d => ¬ d.2 ∧ wholePlaneEdgePresent W d.1

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Exactly one dart of each present edge is its tail dart. Source: -/
theorem wholePlaneDartTail_iff (W : ℤ → Fin 3) (d : WholePlaneDart W)
    (hp : wholePlaneEdgePresent W d.1) :
    wholePlaneDartTail W d ↔ ¬ wholePlaneDartTail W (wholePlaneDartFlip W d) := by
  rcases d with ⟨e, b⟩
  change (¬ b ∧ wholePlaneEdgePresent W e) ↔
    ¬ (¬ !b ∧ wholePlaneEdgePresent W e)
  cases b <;> simp [hp]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem wholePlaneDartTail_missing (W : ℤ → Fin 3) (d : WholePlaneDart W)
    (hm : ¬ wholePlaneEdgePresent W d.1) :
    ¬ wholePlaneDartTail W d := by
  intro ht
  exact hm ht.2

private noncomputable def wholePlaneOrbitVertex (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H) →
      WholePlaneVertex W :=
  Quotient.lift (wholePlaneDartVertex W) (fun d e h =>
    (wholePlaneRotation_sameCycle_dartVertex W H d e h).symm)

private theorem wholePlaneDirectedStep_lift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    {u v : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H)}
    (h : rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
      (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W) u v) :
    ∃ N, ∀ M, N ≤ M →
      ∃ a b : PresentVertex (shiftedStream W M),
        wholePlaneVertexι W M a.id = wholePlaneOrbitVertex W H u ∧
        wholePlaneVertexι W M b.id = wholePlaneOrbitVertex W H v ∧
        Nonempty (a ⟶ b) := by
  obtain ⟨⟨q, b⟩, _, ht, hu, hv⟩ := h
  cases b with
  | true => exact (ht.1 rfl).elim
  | false =>
    obtain ⟨⟨N, e⟩, he⟩ := Quotient.exists_rep q
    have heq : wholePlaneEdgeι W N e = q := he
    have hp : wholePlaneEdgePresent W (wholePlaneEdgeι W N e) := by
      rw [heq]
      exact ht.2
    obtain ⟨K, hNK, hK⟩ := (wholePlaneEdgePresent_ι W N e).mp hp
    refine ⟨K, fun M hKM => ?_⟩
    let f := wholePlaneEdgeTrans W N M (hNK.trans hKM) e
    let a : PresentVertex (shiftedStream W M) := ⟨edgeWest (shiftedStream W M) f⟩
    let b : PresentVertex (shiftedStream W M) := ⟨edgeEast (shiftedStream W M) f⟩
    have hf : wholePlaneEdgeι W M f = q :=
      (congrFun (wholePlaneEdgeι_trans W N M (hNK.trans hKM)) e).trans he
    refine ⟨a, b, ?_, ?_, ⟨⟨f, hK M hKM, rfl, rfl⟩⟩⟩
    · rw [← hu]
      change wholePlaneVertexι W M (edgeWest (shiftedStream W M) f) =
        wholePlaneEdgeWest W q
      rw [← wholePlaneEdgeWest_ι, hf]
    · rw [← hv]
      change wholePlaneVertexι W M (edgeEast (shiftedStream W M) f) =
        wholePlaneEdgeEast W q
      rw [← wholePlaneEdgeEast_ι, hf]

private theorem wholePlaneDirectedPath_lift (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    {u v : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H)}
    (h : Relation.TransGen
      (rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
        (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W)) u v) :
    ∃ N, ∀ M, N ≤ M →
      ∃ a b : PresentVertex (shiftedStream W M),
        wholePlaneVertexι W M a.id = wholePlaneOrbitVertex W H u ∧
        wholePlaneVertexι W M b.id = wholePlaneOrbitVertex W H v ∧
        ∃ p : Quiver.Path a b, 0 < p.length := by
  induction h with
  | single h =>
    obtain ⟨N, hN⟩ := wholePlaneDirectedStep_lift W H h
    refine ⟨N, fun M hNM => ?_⟩
    obtain ⟨a, b, ha, hb, ⟨e⟩⟩ := hN M hNM
    exact ⟨a, b, ha, hb, e.toPath, Nat.zero_lt_one⟩
  | tail _ h ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨K, hK⟩ := wholePlaneDirectedStep_lift W H h
    refine ⟨max N K, fun M hM => ?_⟩
    obtain ⟨a, b, ha, hb, p, _⟩ := hN M ((Nat.le_max_left N K).trans hM)
    obtain ⟨c, d, hc, hd, ⟨e⟩⟩ := hK M ((Nat.le_max_right N K).trans hM)
    have hbc : b = c := by
      have hid := wholePlaneVertexι_injective W M (hb.trans hc.symm)
      cases b
      cases c
      exact congrArg (fun n => (⟨n⟩ : PresentVertex (shiftedStream W M))) hid
    subst c
    exact ⟨a, d, ha, hd, p.cons e, Nat.succ_pos _⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every finite directed cycle lifts into a common one-sided present-edge graph,
where finite-stage strict ranks exclude it. No almost-sure premise is needed. -/
theorem wholePlaneDart_acyclic (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    ∀ v : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
      ¬ Relation.TransGen
        (rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
          (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W)) v v := by
  intro v hv
  obtain ⟨N, hN⟩ := wholePlaneDirectedPath_lift W H hv
  obtain ⟨a, b, ha, hb, p, hp⟩ := hN N (Nat.le_refl N)
  have hab : a = b := by
    have hid := wholePlaneVertexι_injective W N (ha.trans hb.symm)
    cases a
    cases b
    exact congrArg (fun n => (⟨n⟩ : PresentVertex (shiftedStream W N))) hid
  subst b
  rw [presentVertex_acyclic (shiftedStream W N) a p] at hp
  exact Nat.lt_irrefl 0 hp

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The root dart uses the west side of the canonical UIBHBOT root edge. Source: -/
@[expose] def uibhbotWholePlaneRootDart (W : ℤ → Fin 3) : WholePlaneDart W :=
  (uibhbotRootEdge W, false)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The frame dart is the canonical missing root edge at its west endpoint. Source: -/
@[expose] def uibhbotWholePlaneFrameEdgeDart (W : ℤ → Fin 3) : WholePlaneDart W :=
  uibhbotWholePlaneRootDart W

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The opposite dart marks the other endpoint of the missing root edge. Source: -/
@[expose] def uibhbotWholePlaneFrameOtherDart (W : ℤ → Fin 3) :
    Option (WholePlaneDart W) :=
  some (wholePlaneDartFlip W (uibhbotWholePlaneFrameEdgeDart W))

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The root dart is incident to the first endpoint of the ordered root edge. Source: -/
theorem uibhbotWholePlaneRootDart_at_root (W : ℤ → Fin 3) :
    wholePlaneDartVertex W (uibhbotWholePlaneRootDart W) =
      uibhbotRootFirstVertex W := by
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The opposite root dart represents its own marked endpoint. Source: -/
theorem uibhbotWholePlaneFrameOtherDart_valid (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) :
    ∀ y, uibhbotWholePlaneFrameOtherDart W = some y →
      (wholePlaneRotation W H).SameCycle
        (wholePlaneDartFlip W (uibhbotWholePlaneFrameEdgeDart W)) y := by
  intro y hy
  have hy' : wholePlaneDartFlip W (uibhbotWholePlaneFrameEdgeDart W) = y :=
    Option.some.inj (by simpa [uibhbotWholePlaneFrameOtherDart] using hy)
  subst y
  exact ⟨0, by simp⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A certified capture makes the chosen whole-plane root frame edge missing. Source: -/
theorem UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_missing
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r) :
    ¬ wholePlaneEdgePresent W (uibhbotWholePlaneFrameEdgeDart W).1 := by
  simpa [uibhbotWholePlaneFrameEdgeDart, uibhbotWholePlaneRootDart] using
    C.root_missing_wholePlane

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The selected root and frame darts represent the same rotation vertex. Source: -/
theorem UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_at_root
    {W : ℤ → Fin 3} (H : WholePlaneRotationHypothesis W) :
    (wholePlaneRotation W H).SameCycle
      (uibhbotWholePlaneRootDart W) (uibhbotWholePlaneFrameEdgeDart W) := by
  rw [uibhbotWholePlaneFrameEdgeDart]

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A certified capture supplies the missing root frame, with its two ordered -/
theorem UIBHBOTCertifiedRootCapture.wholePlaneRootFrame_fields
    {W : ℤ → Fin 3} {r : ℕ} (C : UIBHBOTCertifiedRootCapture W r)
    (H : WholePlaneRotationHypothesis W) :
    wholePlaneDartVertex W (uibhbotWholePlaneRootDart W) =
        uibhbotRootFirstVertex W ∧
      ¬ wholePlaneEdgePresent W (uibhbotWholePlaneFrameEdgeDart W).1 ∧
      (wholePlaneRotation W H).SameCycle
        (uibhbotWholePlaneRootDart W) (uibhbotWholePlaneFrameEdgeDart W) ∧
      (∀ y, uibhbotWholePlaneFrameOtherDart W = some y →
        (wholePlaneRotation W H).SameCycle
          (wholePlaneDartFlip W (uibhbotWholePlaneFrameEdgeDart W)) y) := by
  refine ⟨uibhbotWholePlaneRootDart_at_root W,
    UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_missing C, ?_, ?_⟩
  · exact ⟨0, by simp [uibhbotWholePlaneFrameEdgeDart]⟩
  · exact uibhbotWholePlaneFrameOtherDart_valid W H

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The certified whole-plane root frame holds on the measurable full-measure -/
theorem uibhbotWordFamilyLaw_ae_wholePlaneRootFrame_fields :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ k, IsStoppedExcursionWord (w k),
        let W := uibhbotCodeWord w (fun k => (hw k).1)
        ∃ H : WholePlaneRotationHypothesis W,
          ∀ r, Nonempty (UIBHBOTCertifiedRootCapture W r) ∧
            wholePlaneDartVertex W (uibhbotWholePlaneRootDart W) =
                uibhbotRootFirstVertex W ∧
              ¬ wholePlaneEdgePresent W (uibhbotWholePlaneFrameEdgeDart W).1 ∧
              (wholePlaneRotation W H).SameCycle
                (uibhbotWholePlaneRootDart W) (uibhbotWholePlaneFrameEdgeDart W) ∧
              (∀ y, uibhbotWholePlaneFrameOtherDart W = some y →
                (wholePlaneRotation W H).SameCycle
                  (wholePlaneDartFlip W (uibhbotWholePlaneFrameEdgeDart W)) y) := by
  filter_upwards [uibhbotWordFamilyLaw_ae_certifiedRootCapture] with w h
  obtain ⟨hw, H, hcaptures⟩ := h
  refine ⟨hw, H, ?_⟩
  intro r
  obtain ⟨C⟩ := hcaptures r
  obtain ⟨hroot, hmissing, hframe, hother⟩ :=
    UIBHBOTCertifiedRootCapture.wholePlaneRootFrame_fields C H
  exact ⟨⟨C⟩, hroot, hmissing, hframe, hother⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The canonical outer mark is the east dart of the missing root edge.
Its global outer-orbit characterization is proved below on the walk support. -/
@[expose] def uibhbotWholePlaneOuterDart (W : ℤ → Fin 3) : WholePlaneDart W :=
  wholePlaneDartFlip W (uibhbotWholePlaneRootDart W)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The single-face property for the canonical UIBHBOT outer mark.
It is proved below, then used to construct the rooted locally finite map. -/
@[expose] def uibhbotWholePlaneMissingOuter (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) : Prop :=
  ∀ d : WholePlaneDart W, ¬ wholePlaneEdgePresent W d.1 →
    Equiv.Perm.SameCycle ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
        (uibhbotWholePlaneOuterDart W) d ∨
      Equiv.Perm.SameCycle ((wholePlaneRotation W H).symm * wholePlaneDartFlip W)
        (uibhbotWholePlaneOuterDart W) (wholePlaneDartFlip W d)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The simultaneous rotation-and-capture support for the root-frame fields is
measurable. Acyclicity holds at every word in this set by `wholePlaneDart_acyclic`. -/
theorem measurableSet_uibhbotWholePlaneRootFrame_support :
    MeasurableSet {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W ∧
      ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)} := by
  have heq : {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W ∧
      ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)} =
      ⋂ r : ℕ, {W : ℤ → Fin 3 | WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r)} := by
    ext W
    constructor
    · intro h
      exact Set.mem_iInter.mpr (fun r => ⟨h.1, h.2 r⟩)
    · intro h
      have h' := Set.mem_iInter.mp h
      exact ⟨(h' 0).1, fun r => (h' r).2⟩
  rw [heq]
  exact MeasurableSet.iInter measurableSet_uibhbotBallClassRel_event

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The whole-plane directed acyclicity field holds almost surely under the code law,
together with every certified root capture on the measurable support above. -/
theorem uibhbotCodeLawRel_ae_wholePlaneDart_acyclic :
    ∀ᵐ W ∂(uibhbotCodeLawRel : MeasureTheory.Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
        (∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧
          ∀ v : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
            ¬ Relation.TransGen
              (rootedLocallyFiniteDirectedStep (wholePlaneRotation W H) (wholePlaneDartFlip W)
                (fun d => ¬ wholePlaneEdgePresent W d.1) (wholePlaneDartTail W)) v v := by
  have hall : ∀ᵐ W ∂(uibhbotCodeLawRel : MeasureTheory.Measure (ℤ → Fin 3)),
      ∀ r : ℕ, WholePlaneRotationHypothesis W ∧
        Nonempty (UIBHBOTCertifiedRootCapture W r) :=
    MeasureTheory.ae_all_iff.mpr uibhbotCodeLawRel_ae_ballClassRel_event
  filter_upwards [hall] with W hW
  exact ⟨(hW 0).1, (fun r => (hW r).2), wholePlaneDart_acyclic W (hW 0).1⟩

private theorem missing_record_stays_record (W : ℤ → Fin 3) (N m : ℕ)
    (hm : 0 < m)
    (hr : ∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j)
    (hmiss : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m)))
    (M : ℕ) (hNM : N ≤ M) :
    ∀ j < M - N + m,
      L (shiftedStream W M) (M - N + m) < L (shiftedStream W M) j := by
  by_contra hn
  have hp := wholePlaneLLCreatedEdge_present_of_nonrecord W N M hNM m hm hr hn
  have hc := wholePlaneEdgePresent_ι_of_run_present W M _ hp
  have hi : wholePlaneEdgeι W M
      (wholePlaneEdgeTrans W N M hNM (kmswLLCreatedEdge (shiftedStream W N) m)) =
      wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m) :=
    congrFun (wholePlaneEdgeι_trans W N M hNM) _
  rw [hi] at hc
  exact hmiss hc

private theorem record_step_data (w : ℕ → Fin 3) (k : ℕ)
    (hr : ∀ j < k + 1, L w (k + 1) < L w j) :
    w k = 0 ∧ (kmswStage w k).UL.dropLast.reverse = [] := by
  have hs : L w (k + 1) = L w k + ((w k : ℤ) - 1) :=
    Finset.sum_range_succ _ _
  have hc : w k = 0 := by
    have hl := hr k (by omega)
    apply Fin.ext
    have hb := (w k).isLt
    omega
  have hmin : L w k = minL w k := by
    obtain ⟨j, hj, he⟩ := runningMin_attained (L w) k
    change minL w k = L w j at he
    have hl := hr j (by omega)
    have hb := runningMin_le (L w) k k le_rfl
    change minL w k ≤ L w k at hb
    rw [hc] at hs
    norm_num at hs
    omega
  exact ⟨hc, (kmswStage_UL_dropLast_reverse_eq_nil_iff_record w k).mpr hmin⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
A globally missing strict-record edge has a west endpoint fresh in every earlier-start -/
theorem wholePlane_missing_record_west_fresh (W : ℤ → Fin 3) (N m : ℕ)
    (hm : 0 < m)
    (hr : ∀ j < m, L (shiftedStream W N) m < L (shiftedStream W N) j)
    (hmiss : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (kmswLLCreatedEdge (shiftedStream W N) m))) :
    ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (edgeWest (shiftedStream W N) (kmswLLCreatedEdge (shiftedStream W N) m)) := by
  cases m with
  | zero => omega
  | succ k =>
    let w := shiftedStream W N
    obtain ⟨hc, hUL⟩ := record_step_data w k hr
    have hcode : kmswCodeStep (w k) = .left := by simp [hc, kmswCodeStep]
    have he : kmswLLCreatedEdge w (k + 1) < (kmswStage w (k + 1)).nextEdge := by
      dsimp [kmswLLCreatedEdge]
      have hb := kmswStage_nextEdge_mono w (m := 0) (n := k + 1) (Nat.zero_le _)
      change 1 ≤ (kmswStage w (k + 1)).nextEdge at hb
      omega
    have hw : edgeWest w (kmswLLCreatedEdge w (k + 1)) =
        (kmswStage w k).nextVertex := by
      rw [← (edge_endpoints_eq w he).1]
      simp [kmswLLCreatedEdge, kmswStage, kmswStep, hcode, kmswStepOfStep,
        hUL, State.addEdge]
    rw [hw]
    intro M hNM
    have hrec := missing_record_stays_record W N (k + 1) (by omega) hr hmiss M hNM
    have hrec' : ∀ j < (M - N + k) + 1,
        L (shiftedStream W M) ((M - N + k) + 1) < L (shiftedStream W M) j := by
      simpa only [Nat.add_assoc] using hrec
    have hglobal := (record_step_data (shiftedStream W M) (M - N + k) hrec').2
    have hmin := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ _).mp hglobal
    have hA := kmswWindowPatchData_A_eq_nil_of_global_record
      (shiftedStream W M) (M - N) k hmin.symm
    have hbase : 2 ≤ (kmswStage w k).nextVertex :=
      CutConverse.nextVertex_mono w (Nat.zero_le k)
    by_contra hf
    rcases (wholePlaneFresh_iff_windowSeam W N M hNM _).mp hf with
      hsmall | ⟨j, _, hju, hdown | hleft⟩
    · omega
    · have hj := kmswCreationStage_unique w (kmswStage w k).nextVertex k j rfl
        (Or.inr ⟨hcode, hUL⟩) hju.symm (Or.inl ⟨hdown.1, hdown.2.1⟩)
      subst j
      rw [hcode] at hdown
      cases hdown.1
    · have hj := kmswCreationStage_unique w (kmswStage w k).nextVertex k j rfl
        (Or.inr ⟨hcode, hUL⟩) hju.symm (Or.inr ⟨hleft.1, hleft.2.1⟩)
      subst j
      exact hleft.2.2 (by rw [hA]; rfl)

private theorem missing_edge_west_fresh (W : ℤ → Fin 3) (N e : ℕ)
    (hR : ∀ a : ℤ, ∃ n, R (shiftedStream W N) n ≤ a)
    (hm : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N e)) :
    ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM (edgeWest (shiftedStream W N) e) := by
  have hm' : ¬ EdgePresent (shiftedStream W N) e :=
    fun hp => hm (wholePlaneEdgePresent_ι_of_run_present W N e hp)
  obtain ⟨n, hn⟩ := futureMap_missing_eventually_LL (shiftedStream W N) hR e hm'
  obtain ⟨m, hmpos, _, hr, he⟩ := kmswStage_LL_edge_created_at_record
    (shiftedStream W N) n e (hn n le_rfl).2
  rw [he] at hm ⊢
  exact wholePlane_missing_record_west_fresh W N m hmpos hr hm

private theorem missing_edge_boundary_label (W : ℤ → Fin 3) (N e : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N))
    (hm : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W N e)) :
    ∃ k : ℤ, k ≤ -1 ∧ e = boundaryOuterEdge (shiftedStream W N) h k := by
  have hm' : ¬ EdgePresent (shiftedStream W N) e :=
    fun hp => hm (wholePlaneEdgePresent_ι_of_run_present W N e hp)
  have hd := futureMap_missing_east_external (shiftedStream W N) h.R_unbounded_below e hm'
  obtain ⟨k, hk⟩ := (futureMap_limitExternalDart_iff_boundaryDart
    (shiftedStream W N) h (e, true)).mp hd
  have he : e = boundaryOuterEdge (shiftedStream W N) h k := congrArg Prod.fst hk
  refine ⟨k, ?_, he⟩
  by_contra hneg
  have hp := (boundaryOuterEdge_endpoints (shiftedStream W N) h k).2.2.1 (by omega)
  exact hm' (he ▸ hp)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
At a globally missing boundary edge, the whole-plane face successor decreases the
one-sided integer label by one, and the next edge is also globally missing. -/
theorem wholePlane_missing_boundary_faceSucc (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ -1)
    (hm : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h k))) :
    ¬ wholePlaneEdgePresent W
        (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h (k - 1))) ∧
      wholePlaneFaceSucc W H
          (wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h k)) =
        wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h (k - 1)) := by
  have hf := missing_edge_west_fresh W N _ h.R_unbounded_below hm
  have hs := wholePlaneFaceSucc_ι_of_fresh W H N
    (futureMapBoundaryDart (shiftedStream W N) h k) hf
  rw [futureMapBoundaryDart_faceSucc (shiftedStream W N) (H.1 N) h k] at hs
  refine ⟨?_, hs⟩
  have hf' : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM
      (edgeEast (shiftedStream W N) (boundaryOuterEdge (shiftedStream W N) h (k - 1))) := by
    intro M hNM
    rw [(boundaryOuterEdge_endpoints (shiftedStream W N) h (k - 1)).2.1,
      sub_add_cancel]
    have hw := hf M hNM
    rw [(boundaryOuterEdge_endpoints (shiftedStream W N) h k).1] at hw
    exact hw
  intro hp
  have hp' := (wholePlaneEdgePresent_ι_of_fresh W N _ true hf').mp hp
  exact (boundaryOuterEdge_endpoints (shiftedStream W N) h (k - 1)).2.2.2
    (by omega) hp'

private theorem missing_boundary_descend (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k : ℤ) (hk : k ≤ -1)
    (hm : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h k))) (n : ℕ) :
    ¬ wholePlaneEdgePresent W
        (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h (k - n))) ∧
      (wholePlaneFaceSucc W H).SameCycle
        (wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h k))
        (wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h (k - n))) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, sub_zero] using
      And.intro hm (Equiv.Perm.SameCycle.refl (wholePlaneFaceSucc W H) _)
  | succ n ih =>
    obtain ⟨hmiss, hstep⟩ := wholePlane_missing_boundary_faceSucc W H N h (k - n)
      (by omega) ih.1
    have hcycle := ih.2.apply_right
    rw [hstep] at hcycle
    have heq : k - (n + 1 : ℕ) = k - (n : ℤ) - 1 := by omega
    rw [heq]
    exact ⟨hmiss, hcycle⟩

private theorem missing_boundary_sameCycle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (N : ℕ)
    (h : BoundaryHitWitnesses (shiftedStream W N)) (k l : ℤ)
    (hk : k ≤ -1) (hl : l ≤ -1)
    (hmk : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h k)))
    (hml : ¬ wholePlaneEdgePresent W
      (wholePlaneEdgeι W N (boundaryOuterEdge (shiftedStream W N) h l))) :
    (wholePlaneFaceSucc W H).SameCycle
      (wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h k))
      (wholePlaneDartι W N (futureMapBoundaryDart (shiftedStream W N) h l)) := by
  rcases le_total l k with hlk | hkl
  · have hd := (missing_boundary_descend W H N h k hk hmk (k - l).toNat).2
    have he : k - ((k - l).toNat : ℤ) = l := by omega
    rwa [he] at hd
  · have hd := (missing_boundary_descend W H N h l hl hml (l - k).toNat).2
    have he : l - ((l - k).toNat : ℤ) = k := by omega
    rw [he] at hd
    exact hd.symm

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The east darts of any two globally missing edges lie in one whole-plane face orbit.
The coordinate hitting hypotheses are source walk properties, not face assumptions. -/
theorem wholePlane_missing_east_sameCycle (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (e f : WholePlaneEdge W) (he : ¬ wholePlaneEdgePresent W e)
    (hf : ¬ wholePlaneEdgePresent W f) :
    (wholePlaneFaceSucc W H).SameCycle (e, true) (f, true) := by
  obtain ⟨⟨N, a⟩, ha⟩ := Quotient.exists_rep e
  obtain ⟨⟨M, b⟩, hb⟩ := Quotient.exists_rep f
  let K := max N M
  let aK := wholePlaneEdgeTrans W N K (Nat.le_max_left N M) a
  let bK := wholePlaneEdgeTrans W M K (Nat.le_max_right N M) b
  have haK : wholePlaneEdgeι W K aK = e :=
    (congrFun (wholePlaneEdgeι_trans W N K (Nat.le_max_left N M)) a).trans ha
  have hbK : wholePlaneEdgeι W K bK = f :=
    (congrFun (wholePlaneEdgeι_trans W M K (Nat.le_max_right N M)) b).trans hb
  have hma : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W K aK) := haK ▸ he
  have hmb : ¬ wholePlaneEdgePresent W (wholePlaneEdgeι W K bK) := hbK ▸ hf
  obtain ⟨k, hk, hak⟩ := missing_edge_boundary_label W K aK (hhit K) hma
  obtain ⟨l, hl, hbl⟩ := missing_edge_boundary_label W K bK (hhit K) hmb
  rw [hak] at hma
  rw [hbl] at hmb
  have hcycle := missing_boundary_sameCycle W H K (hhit K) k l hk hl hma hmb
  change (wholePlaneFaceSucc W H).SameCycle
    (wholePlaneEdgeι W K (boundaryOuterEdge (shiftedStream W K) (hhit K) k), true)
    (wholePlaneEdgeι W K (boundaryOuterEdge (shiftedStream W K) (hhit K) l), true)
    at hcycle
  rwa [← hak, ← hbl, haK, hbK] at hcycle

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
All missing geometric edges meet the face orbit marked by the canonical missing root. -/
theorem uibhbotWholePlaneMissingOuter_holds (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) : uibhbotWholePlaneMissingOuter W H := by
  rintro ⟨e, b⟩ hd
  have hc := wholePlane_missing_east_sameCycle W H hhit (uibhbotRootEdge W) e
    C.root_missing_wholePlane hd
  cases b with
  | false => exact Or.inr hc
  | true => exact Or.inl hc

private theorem forward_integral_coordinates (W : ℤ → Fin 3) (n : ℕ) :
    wholePlaneWordIntegral W (n : ℤ) =
      (L (shiftedStream W 0) n, R (shiftedStream W 0) n) := by
  have hsum (f : ℕ → ℤ × ℤ) (n : ℕ) :
      ((List.range n).map f).sum =
        (∑ i ∈ Finset.range n, (f i).1, ∑ i ∈ Finset.range n, (f i).2) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [List.range_succ, Finset.sum_range_succ, ih]
      exact Prod.ext rfl rfl
  simpa [wholePlaneWordIntegral, L, R, shiftedStream, ← List.map_eq_flatMap,
    List.map_map, Function.comp_def] using
    hsum (fun i => lazyTwoDimensionalStep (W (i : ℤ))) n

private theorem negative_level_hit (f : ℕ → ℤ) (hf : f 0 = 0)
    (hstep : ∀ n, f n - 1 ≤ f (n + 1)) (a : ℤ) (ha : a < 0)
    (hbelow : ∃ n, f n ≤ a) : ∃ n, f n = a := by
  let n := Nat.find hbelow
  have hn : f n ≤ a := Nat.find_spec hbelow
  have hpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz, hf] at hn
    omega
  have hprev : a < f (n - 1) := by
    have hh := Nat.find_min hbelow (show n - 1 < n by omega)
    omega
  have hs := hstep (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
  exact ⟨n, by omega⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Stopped excursion blocks and forward R-unboundedness give the coordinate hitting -/
theorem uibhbotCodeWord_boundaryHitWitnesses (w : ℤ → List (Fin 3))
    (hw : ∀ k, IsStoppedExcursionWord (w k))
    (hR : ∀ a : ℤ, ∃ n : ℕ, (uibhbotConcatWalk w n).2 ≤ a) :
    ∀ N, BoundaryHitWitnesses
      (shiftedStream (uibhbotCodeWord w (fun k => (hw k).1)) N) := by
  let W := uibhbotCodeWord w (fun k => (hw k).1)
  have hc (n : ℕ) : (L (shiftedStream W 0) n, R (shiftedStream W 0) n) =
      uibhbotConcatWalk w n := by
    rw [← forward_integral_coordinates]
    exact wholePlaneWordIntegral_uibhbotCodeWord w (fun k => (hw k).1) n
  have hzero : BoundaryHitWitnesses (shiftedStream W 0) := by
    constructor
    · intro k hk
      refine negative_level_hit (R (shiftedStream W 0)) (by simp [R]) ?_ (-k) (by omega) ?_
      · intro n
        have hs : R (shiftedStream W 0) (n + 1) = R (shiftedStream W 0) n +
            (lazyTwoDimensionalStep (shiftedStream W 0 n)).2 := Finset.sum_range_succ _ _
        have hb : -1 ≤ (lazyTwoDimensionalStep (shiftedStream W 0 n)).2 := by
          unfold lazyTwoDimensionalStep
          split_ifs <;> omega
        omega
      · obtain ⟨n, hn⟩ := hR (-k)
        exact ⟨n, by rw [← congrArg Prod.snd (hc n)] at hn; exact hn⟩
    · intro k hk
      refine negative_level_hit (L (shiftedStream W 0)) (by simp [L]) ?_ k (by omega) ?_
      · intro n
        have hs : L (shiftedStream W 0) (n + 1) = L (shiftedStream W 0) n +
            ((shiftedStream W 0 n : ℤ) - 1) := Finset.sum_range_succ _ _
        omega
      · obtain ⟨n, hn⟩ := uibhbotConcatWalk_fst_unbounded_below_of_stopped w hw k
        exact ⟨n, by rw [← congrArg Prod.fst (hc n)] at hn; exact hn⟩
  intro N
  exact boundaryHitWitnesses_of_le W (Nat.zero_le N) hzero

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The simultaneous shifted-run coordinate hitting event is measurable. -/
theorem measurableSet_wholePlane_boundaryHitWitnesses :
    MeasurableSet {W : ℤ → Fin 3 | ∀ N, BoundaryHitWitnesses (shiftedStream W N)} := by
  have hshift (N : ℕ) : Measurable (fun W : ℤ → Fin 3 => shiftedStream W N) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply ((i : ℤ) - N))
  have heq : {W : ℤ → Fin 3 | ∀ N, BoundaryHitWitnesses (shiftedStream W N)} =
      {W | ∀ N, (∀ k : ℤ, 1 ≤ k → ∃ n, R (shiftedStream W N) n = -k) ∧
        (∀ k : ℤ, k ≤ -1 → ∃ n, L (shiftedStream W N) n = k)} := by
    ext W
    exact ⟨fun h N => ⟨(h N).1, (h N).2⟩, fun h N => ⟨(h N).1, (h N).2⟩⟩
  rw [heq]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro N
  change MeasurableSet
    ({W | ∀ k : ℤ, 1 ≤ k → ∃ n, R (shiftedStream W N) n = -k} ∩
      {W | ∀ k : ℤ, k ≤ -1 → ∃ n, L (shiftedStream W N) n = k})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n => (measurableSet_R n (fun x => x = -k)).preimage (hshift N)
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n => (measurableSet_L n (fun x => x = k)).preimage (hshift N)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
Every shifted run has coordinate hitting witnesses almost surely under the code law. -/
theorem uibhbotCodeLawRel_ae_boundaryHitWitnesses :
    ∀ᵐ W ∂(uibhbotCodeLawRel : MeasureTheory.Measure (ℤ → Fin 3)),
      ∀ N, BoundaryHitWitnesses (shiftedStream W N) := by
  change ∀ᵐ W ∂uibhbotWordFamilyLaw.map uibhbotCodeWordRel,
    ∀ N, BoundaryHitWitnesses (shiftedStream W N)
  apply (MeasureTheory.ae_map_iff measurable_uibhbotCodeWordRel.aemeasurable
    measurableSet_wholePlane_boundaryHitWitnesses).mpr
  filter_upwards [ae_uibhbotWordFamily_all_stopped,
    ae_uibhbotConcatWalk_snd_unbounded_below] with w hw hR
  rw [uibhbotCodeWordRel_eq w (fun k => (hw k).1)]
  exact uibhbotCodeWord_boundaryHitWitnesses w hw hR

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The UIBHBOT rooted locally finite map, retaining all geometric missing edges,
their absent orientation, and the missing ordered root frame. -/
@[expose] noncomputable def uibhbotWholePlaneRootedLocallyFiniteMap (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) : RootedLocallyFiniteMap where
  D := WholePlaneDart W
  countableD := wholePlaneDart_countable W
  rot := wholePlaneRotation W H
  edgeInv := wholePlaneDartFlip W
  edgeInv_invol := wholePlaneDartFlip_involutive W
  edgeInv_ne := wholePlaneDartFlip_ne W
  missing := fun d => ¬ wholePlaneEdgePresent W d.1
  missing_edgeInv := wholePlaneDartMissing_flip_iff W
  tail := wholePlaneDartTail W
  tail_iff := fun d hp => wholePlaneDartTail_iff W d (Classical.not_not.mp hp)
  tail_missing := wholePlaneDartTail_missing W
  outer := uibhbotWholePlaneOuterDart W
  missing_outer := uibhbotWholePlaneMissingOuter_holds W H hhit C
  rootDart := uibhbotWholePlaneRootDart W
  frameEdgeDart := uibhbotWholePlaneFrameEdgeDart W
  frameEdge_missing := UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_missing C
  frameEdge_at_root := UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_at_root H
  frameOtherDart := uibhbotWholePlaneFrameOtherDart W
  frameOtherDart_valid := uibhbotWholePlaneFrameOtherDart_valid W H
  locallyFinite := wholePlaneRotation_sameCycleOrbit_finite W H
  connected := wholePlaneDart_connected W H
  acyclic := wholePlaneDart_acyclic W H

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The code law almost surely supplies all inputs to the rooted locally finite map,
with every certified root capture and the canonical missing frame and outer mark. -/
theorem uibhbotCodeLawRel_ae_rootedLocallyFiniteMap :
    ∀ᵐ W ∂(uibhbotCodeLawRel : MeasureTheory.Measure (ℤ → Fin 3)),
      ∃ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0),
        (∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧
          let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
          M.frameEdgeDart = uibhbotWholePlaneFrameEdgeDart W ∧
            M.missing M.frameEdgeDart ∧ M.outer = uibhbotWholePlaneOuterDart W := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses] with W hW hhit
  obtain ⟨H, hcap, _⟩ := hW
  obtain ⟨C⟩ := hcap 0
  exact ⟨H, hhit, C, hcap, rfl,
    UIBHBOTCertifiedRootCapture.wholePlaneFrameEdge_missing C, rfl⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The canonical missing-edge outer-orbit property holds almost surely together with -/
theorem uibhbotCodeLawRel_ae_missingOuter :
    ∀ᵐ W ∂(uibhbotCodeLawRel : MeasureTheory.Measure (ℤ → Fin 3)),
      ∃ H : WholePlaneRotationHypothesis W,
        (∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) ∧
          uibhbotWholePlaneMissingOuter W H := by
  filter_upwards [uibhbotCodeLawRel_ae_wholePlaneDart_acyclic,
    uibhbotCodeLawRel_ae_boundaryHitWitnesses] with W hW hhit
  obtain ⟨H, hcap, _⟩ := hW
  obtain ⟨C⟩ := hcap 0
  exact ⟨H, hcap, uibhbotWholePlaneMissingOuter_holds W H hhit C⟩

private theorem map_dart_radius (M : RootedLocallyFiniteMap) (d : M.D) :
    ∃ r, rootedLocallyFiniteWithinRadius M r (rootedLocallyFiniteVertexClassOf M d) := by
  have hrot (x : M.D) : rootedLocallyFiniteVertexClassOf M (M.rot x) =
      rootedLocallyFiniteVertexClassOf M x :=
    Quotient.sound (Equiv.Perm.SameCycle.rfl.apply_left)
  have hinvrot (x : M.D) : rootedLocallyFiniteVertexClassOf M (M.rot.symm x) =
      rootedLocallyFiniteVertexClassOf M x :=
    Quotient.sound (Equiv.Perm.SameCycle.rfl.symm_apply_left)
  have hedge (x : M.D) : M.edgeInv.symm x = M.edgeInv x := by
    apply M.edgeInv.injective
    rw [Equiv.apply_symm_apply, M.edgeInv_invol]
  have hp := M.connected M.rootDart d
  induction hp with
  | refl => exact ⟨0, .root⟩
  | @tail x y hxy hstep ih =>
    obtain ⟨r, hr⟩ := ih
    rcases hstep with h | h | h | h
    · subst y
      exact ⟨r, (hrot x).symm ▸ hr⟩
    · subst y
      exact ⟨r, (hinvrot x).symm ▸ hr⟩
    · subst y
      exact ⟨r + 1, .edge hr ⟨x, rfl, rfl⟩⟩
    · subst y
      rw [hedge]
      exact ⟨r + 1, .edge hr ⟨x, rfl, rfl⟩⟩

private theorem map_ball_exhaust (M : RootedLocallyFiniteMap) (d : M.D) :
    ∃ r, d ∈ rootedLocallyFiniteBallDarts M r := by
  obtain ⟨r, hr⟩ := map_dart_radius M d
  obtain ⟨s, hs⟩ := map_dart_radius M (M.edgeInv d)
  refine ⟨max r s, (mem_rootedLocallyFiniteBallDarts M _ d).mpr ⟨?_, ?_⟩⟩
  · exact rootedLocallyFiniteRadiusVertices_mono M (Nat.le_max_left r s)
      ((mem_rootedLocallyFiniteRadiusVertices M r _).mpr hr)
  · exact rootedLocallyFiniteRadiusVertices_mono M (Nat.le_max_right r s)
      ((mem_rootedLocallyFiniteRadiusVertices M s _).mpr hs)

private theorem map_ball_mono (M : RootedLocallyFiniteMap) {r s : ℕ} (hrs : r ≤ s)
    {d : M.D} (hd : d ∈ rootedLocallyFiniteBallDarts M r) :
    d ∈ rootedLocallyFiniteBallDarts M s := by
  rw [mem_rootedLocallyFiniteBallDarts] at hd ⊢
  exact ⟨rootedLocallyFiniteRadiusVertices_mono M hrs hd.1,
    rootedLocallyFiniteRadiusVertices_mono M hrs hd.2⟩

private theorem map_ball_capture_finite (M : RootedLocallyFiniteMap) (r : ℕ)
    (S : Finset M.D) :
    ∃ R, r ≤ R ∧ ∀ d ∈ S, d ∈ rootedLocallyFiniteBallDarts M R := by
  classical
  choose radius hradius using map_ball_exhaust M
  refine ⟨max r (S.sup radius), Nat.le_max_left _ _, ?_⟩
  intro d hd
  exact map_ball_mono M ((Finset.le_sup hd).trans (Nat.le_max_right _ _)) (hradius d)

private theorem map_ball_faceSucc_of_mem (M : RootedLocallyFiniteMap) (r : ℕ)
    [DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r}]
    (d : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M r})
    (hface : M.rot.symm (M.edgeInv d.1) ∈ rootedLocallyFiniteBallDarts M r) :
    ((rootedLocallyFiniteBallCombinatorialMap M r).faceSucc d).1 =
      M.rot.symm (M.edgeInv d.1) := by
  classical
  let S := rootedLocallyFiniteBallDarts M r
  let B := rootedLocallyFiniteBallCombinatorialMap M r
  let y : S := ⟨M.rot.symm (M.edgeInv d.1), hface⟩
  have hret : ∀ x : S, ∃ k : ℕ, 0 < k ∧ (M.rot ^ k) x.1 ∈ S := by
    intro x
    obtain ⟨k, hk, heq⟩ := rootedLocallyFiniteRotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  have hnext : M.rot y.1 = M.edgeInv d.1 := M.rot.apply_symm_apply _
  have hy : M.rot y.1 ∈ S := hnext.symm ▸
    rootedLocallyFiniteBallDarts_edgeInv_closed M r d.1 d.2
  have hrot : B.rot y = B.edgeInv d := by
    apply Subtype.ext
    have ht : cyclicFirstReturnTime M.rot S hret y = 1 := by
      apply Nat.le_antisymm
      · exact Nat.find_min' (hret y) ⟨Nat.one_pos, by simpa only [pow_one] using hy⟩
      · exact (cyclicFirstReturnTime_spec M.rot S hret y).1
    change (cyclicFirstReturn M.rot S hret y).1 = M.edgeInv d.1
    rw [(firstReturn_spec M.rot S hret y).1, ht, pow_one]
    exact hnext
  change (B.rot.symm (B.edgeInv d)).1 = _
  rw [← hrot, Equiv.symm_apply_apply]

private theorem map_ball_capture_face_path (M : RootedLocallyFiniteMap) (r : ℕ)
    (x : M.D) (n : ℕ) :
    ∃ R, r ≤ R ∧ ∃ hx : x ∈ rootedLocallyFiniteBallDarts M R,
      ∃ hy : ((M.rot.symm * M.edgeInv) ^ n) x ∈ rootedLocallyFiniteBallDarts M R,
        letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
          Classical.decEq _
        (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle ⟨x, hx⟩
          ⟨((M.rot.symm * M.edgeInv) ^ n) x, hy⟩ := by
  classical
  let f : Equiv.Perm M.D := M.rot.symm * M.edgeInv
  let S := (Finset.range (n + 1)).image fun i => (f ^ i) x
  obtain ⟨R, hrR, hR⟩ := map_ball_capture_finite M r S
  let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
    Classical.decEq _
  have hmem (i : ℕ) (hi : i ≤ n) : (f ^ i) x ∈ rootedLocallyFiniteBallDarts M R := by
    apply hR
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hx : x ∈ rootedLocallyFiniteBallDarts M R := by
    simpa only [pow_zero, Equiv.Perm.one_apply] using hmem 0 (Nat.zero_le n)
  refine ⟨R, hrR, hx, hmem n le_rfl, ?_⟩
  let B := rootedLocallyFiniteBallCombinatorialMap M R
  let z : {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} := ⟨x, hx⟩
  have hpow : ∀ i, i ≤ n → ((B.faceSucc ^ i) z).1 = (f ^ i) x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hv := ih (by omega)
      have hnxt : M.rot.symm (M.edgeInv ((B.faceSucc ^ i) z).1) ∈
          rootedLocallyFiniteBallDarts M R := by
        rw [hv]
        simpa only [f, pow_succ', Equiv.Perm.mul_apply] using hmem (i + 1) hi
      rw [pow_succ', Equiv.Perm.mul_apply]
      rw [map_ball_faceSucc_of_mem M R _ hnxt, hv]
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl
  refine ⟨(n : ℤ), ?_⟩
  apply Subtype.ext
  exact hpow n le_rfl

private theorem map_ball_capture_sameCycle (M : RootedLocallyFiniteMap) (r : ℕ)
    (x y : M.D) (hxy : Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) x y) :
    ∃ R, r ≤ R ∧ ∃ hx : x ∈ rootedLocallyFiniteBallDarts M R,
      ∃ hy : y ∈ rootedLocallyFiniteBallDarts M R,
        letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
          Classical.decEq _
        (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle ⟨x, hx⟩
          ⟨y, hy⟩ := by
  classical
  let f : Equiv.Perm M.D := M.rot.symm * M.edgeInv
  obtain ⟨i, hi⟩ := hxy
  cases i with
  | ofNat n =>
    have heq : (f ^ n) x = y := by
      change (f ^ (n : ℤ)) x = y at hi
      rwa [zpow_natCast] at hi
    obtain ⟨R, hrR, hx, hn, hcycle⟩ := map_ball_capture_face_path M r x n
    let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
      Classical.decEq _
    refine ⟨R, hrR, hx, heq ▸ hn, ?_⟩
    change (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle
      ⟨x, hx⟩ ⟨(f ^ n) x, hn⟩ at hcycle
    simpa only [heq] using hcycle
  | negSucc n =>
    have heq : (f ^ (n + 1)) y = x := by
      rw [← hi, zpow_negSucc]
      exact (f ^ (n + 1)).apply_symm_apply _
    obtain ⟨R, hrR, hy, hn, hcycle⟩ := map_ball_capture_face_path M r y (n + 1)
    let _ : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
      Classical.decEq _
    refine ⟨R, hrR, heq ▸ hn, hy, ?_⟩
    have hcycle' := hcycle.symm
    change (rootedLocallyFiniteBallCombinatorialMap M R).faceSucc.SameCycle
      ⟨(f ^ (n + 1)) y, hn⟩ ⟨y, hy⟩ at hcycle'
    simpa only [heq] using hcycle'

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The selected outer side of the frame and any ambient outer-face dart are captured -/
theorem uibhbotWholePlane_outerFace_captured_in_larger_ball (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
    (C : UIBHBOTCertifiedRootCapture W 0) :
    let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
    ∀ r, 0 < r → ∀ d, d ∈ rootedLocallyFiniteBallDarts M r →
      Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer d →
      ∃ R, r ≤ R ∧ ∃ hdR : d ∈ rootedLocallyFiniteBallDarts M R,
        ∃ hfR : rootedLocallyFiniteOuterFrameDart M ∈ rootedLocallyFiniteBallDarts M R,
          letI : DecidableEq {d : M.D // d ∈ rootedLocallyFiniteBallDarts M R} :=
            Classical.decEq _
          CombinatorialMap.IsOuter (rootedLocallyFiniteBallCombinatorialMap M R)
            ⟨rootedLocallyFiniteOuterFrameDart M, hfR⟩ ⟨d, hdR⟩ := by
  intro M r _ d _ hd
  have hframe := rootedLocallyFiniteOuterFrameDart_outer M
  obtain ⟨R, hrR, hfR, hdR, hcycle⟩ := map_ball_capture_sameCycle M r
    (rootedLocallyFiniteOuterFrameDart M) d (hframe.symm.trans hd)
  exact ⟨R, hrR, hdR, hfR, hcycle⟩













end DirectedDistances.KMSW
