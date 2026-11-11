module

public import DirectedDistances.KMSW.RawHatOutgoingOrder
public import DirectedDistances.KMSW.KMSWShiftAllTimes
import DirectedDistances.KMSW.WholePlaneRunRotationRestrict

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/








public section
namespace DirectedDistances.KMSW

private theorem shift_edge_eq_window (w : ℕ → Fin 3) (t m e : ℕ)
    (he : e < (kmswStage (fun i => w (t + i)) m).nextEdge) :
    kmswShiftEdgeMapAll w t m e = (kmswWindowPatchData w t m).φ e := by
  induction m with
  | zero => rfl
  | succ m ih =>
    let F := kmswStage (fun i => w (t + i)) m
    let G := kmswStage w (t + m)
    let D := kmswWindowPatchData w t m
    have hrel := kmswWindowPatchData_rel w t m
    change KMSWWindowPatchRel _ G F D.φ D.A D.B D.YL D.YR D.XL D.XR at hrel
    by_cases hold : e < F.nextEdge
    · rw [kmswShiftEdgeMapAll_extend w t m e hold,
        kmswWindowPatchData_extends w t m e hold]
      exact ih hold
    have hge : F.nextEdge ≤ e := by omega
    change e < (kmswStep F ((fun i => w (t + i)) m)).nextEdge at he
    change kmswShiftNextEdgeMap F G (kmswCodeStep (w (t + m)))
      (kmswShiftEdgeMapAll w t m) e =
      (KMSWWindowPatchData.step G F (kmswCodeStep (w (t + m))) D).φ e
    cases hc : kmswCodeStep (w (t + m)) with
    | up =>
      have hb : e = F.nextEdge ∨ e = F.nextEdge + 1 := by
        simp only [kmswStep, hc, kmswStepOfStep, State.addEdge] at he
        omega
      rcases hb with rfl | rfl <;>
        simp [kmswShiftNextEdgeMap, kmswShiftUpEdgeMap, KMSWWindowPatchData.step]
    | down =>
      cases hf : F.UR with
      | cons q qs => simp only [kmswStep, hc, kmswStepOfStep, hf] at he; omega
      | nil =>
        have heq : e = F.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        subst e
        have hg : G.UR = D.B := by simpa only [hf, List.map_nil, List.nil_append]
          using hrel.ur
        cases hb : D.B <;>
          simp [kmswShiftNextEdgeMap, hf, hg, hb, kmswShiftFreshEdgeMap,
            kmswShiftDownMismatchEdgeMap, KMSWWindowPatchData.step]
    | left =>
      cases hf : F.UL.dropLast.reverse with
      | cons q qs =>
        have heq : e = F.nextEdge := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        subst e
        simp [kmswShiftNextEdgeMap, hf, kmswShiftFreshEdgeMap,
          KMSWWindowPatchData.step]
      | nil =>
        have hb : e = F.nextEdge ∨ e = F.nextEdge + 1 := by
          simp only [kmswStep, hc, kmswStepOfStep, hf, State.addEdge] at he
          omega
        obtain ⟨xs, hxs⟩ := kmswStage_UL_last (fun i => w (t + i)) m
        have hF : F.UL = [F.active] := by
          have hx : xs = [] := by simpa only [F, hxs, List.dropLast_concat,
            List.reverse_eq_nil_iff] using hf
          simpa only [hx, List.nil_append] using hxs
        have hg : G.UL.dropLast.reverse = D.A.reverse := by
          rw [hrel.ul, hF, List.map_singleton, List.dropLast_concat]
        cases ha : D.A.reverse <;> rcases hb with rfl | rfl <;>
          simp [kmswShiftNextEdgeMap, hf, hg, ha, kmswShiftUpEdgeMap,
            kmswShiftLeftMismatchEdgeMap, KMSWWindowPatchData.step]

private def dartValue {k : ℕ} (d : StageDart k) : ℕ × Bool := (d.1.val, d.2)

private theorem dartValue_injective (k : ℕ) :
    Function.Injective (@dartValue k) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ he
  obtain ⟨hv, hb⟩ := Prod.mk.inj he
  exact Prod.ext (Fin.ext hv) hb

private def endpoint (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1

private theorem stageEndpoint_eq (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) d = endpoint w (dartValue d) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp only [stageEndpoint, endpoint, dartValue, hb,
    Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem window_endpoint (w : ℕ → Fin 3) (t : ℕ) (d : ℕ × Bool) :
    endpoint w (kmswWindowEdgeMapInf w t d.1, d.2) =
      kmswWindowVertexMapInf w t (endpoint (fun i => w (t + i)) d) := by
  have he := kmsw_edge_allocated_by_self (fun i => w (t + i)) d.1
  have hb : kmswWindowEdgeMapInf w t d.1 < (kmswStage w (t + d.1)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w t d.1 d.1 he]
    exact (kmswWindowPatchData_rel w t d.1).edge_bound d.1 he
  have hW := edge_endpoints_eq w hb
  have hU := edge_endpoints_eq (fun i => w (t + i)) he
  cases hd : d.2
  · simpa only [endpoint, hd, Bool.false_eq_true, ↓reduceIte, ← hW.1, ← hU.1]
      using kmswWindowEdgeMapInf_west w t d.1 d.1 he
  · simpa only [endpoint, hd, ↓reduceIte, ← hW.2, ← hU.2]
      using kmswWindowEdgeMapInf_east w t d.1 d.1 he

private theorem complete_exists (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (v : ℕ) : ∃ n, kmswVertexComplete w n v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  exact (hB ⟨e, kmsw_edge_allocated_by_self w e, he⟩).trans_lt
    (kmsw_edge_allocated_by_self w B)

private theorem complete_mono (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete w n v) : kmswVertexComplete w m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem symm_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) ((stageRot w n).symm d) =
      stageEndpoint (kmswStage w n) d :=
  (stageRot_sameCycle_iff_endpoint_eq w n _ _).mp
    ⟨1, (stageRot w n).apply_symm_apply d⟩

private theorem symm_pow_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w n) (((stageRot w n).symm ^ k) d) =
      stageEndpoint (kmswStage w n) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, symm_endpoint, ih]

private theorem inf_symm_pow_stage (w : ℕ → Fin 3) (hfin : KMSWFiniteIncidence w)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) (k : ℕ) :
    ((kmswInfRot w hfin).symm ^ k) (dartValue d) =
      dartValue (((stageRot w n).symm ^ k) d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    exact kmswInfRot_symm_eq_stage w hfin n _ (by rw [symm_pow_endpoint]; exact hc)

private theorem windowInfRot_symm_firstReturn (w : ℕ → Fin 3) (t : ℕ)
    (hfinS : KMSWFiniteIncidence (fun i => w (t + i)))
    (hfinW : KMSWFiniteIncidence w) (d : ℕ × Bool) :
    let I : (ℕ × Bool) → ℕ × Bool := fun x => (kmswWindowEdgeMapInf w t x.1, x.2)
    ∃ k : ℕ, 0 < k ∧
      ((kmswInfRot w hfinW).symm ^ k) (I d) =
        I ((kmswInfRot (fun i => w (t + i)) hfinS).symm d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ((kmswInfRot w hfinW).symm ^ j) (I d) ∉ Set.range I := by
  let u := fun i => w (t + i)
  let I : (ℕ × Bool) → ℕ × Bool := fun x => (kmswWindowEdgeMapInf w t x.1, x.2)
  obtain ⟨Ns, hNs⟩ := complete_exists u hfinS (endpoint u d)
  obtain ⟨Nw, hNw⟩ := complete_exists w hfinW (endpoint w (I d))
  let m := max Ns (max Nw d.1)
  have hsm : Ns ≤ m := Nat.le_max_left _ _
  have hwm : Nw ≤ t + m := by
    have := (Nat.le_max_left Nw d.1).trans (Nat.le_max_right Ns (max Nw d.1))
    omega
  have hdm : d.1 ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcs := complete_mono u hsm hNs
  have hcw := complete_mono w hwm hNw
  have hd := kmsw_nextEdge_unbounded u d.1 m hdm
  let x : StageDart (kmswStage u m).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := kmswWindowDartMap w t m x
  have hmap (z : StageDart (kmswStage u m).nextEdge) :
      dartValue (kmswWindowDartMap w t m z) = I (dartValue z) := by
    apply Prod.ext
    · exact (kmswWindowEdgeMapInf_eq_stage w t m z.1.val z.1.isLt).symm
    · rfl
  have hy : dartValue y = I d := hmap x
  have hcx : kmswVertexComplete u m (stageEndpoint (kmswStage u m) x) := by
    rw [stageEndpoint_eq]
    exact hcs
  have hcy : kmswVertexComplete w (t + m)
      (stageEndpoint (kmswStage w (t + m)) y) := by
    rw [stageEndpoint_eq, hy]
    exact hcw
  have hiter (j : ℕ) : ((kmswInfRot w hfinW).symm ^ j) (I d) =
      dartValue (((stageRot w (t + m)).symm ^ j) y) := by
    rw [← hy]
    exact inf_symm_pow_stage w hfinW _ y hcy j
  obtain ⟨k, hk, hreturn, hgap⟩ := kmswWindowDartMap_symm_firstReturn w t m x
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hiter, hreturn, hmap]
    exact congrArg I (kmswInfRot_symm_eq_stage u hfinS m x hcx).symm
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    have hep : endpoint w (I e) = endpoint w (I d) := by
      calc
        endpoint w (I e) =
            endpoint w (dartValue (((stageRot w (t + m)).symm ^ j) y)) :=
          congrArg (endpoint w) (he.trans (hiter j))
        _ = endpoint w (dartValue y) := by
          rw [← stageEndpoint_eq, ← stageEndpoint_eq, symm_pow_endpoint]
        _ = endpoint w (I d) := congrArg (endpoint w) hy
    have heLocal : endpoint u e = endpoint u d := by
      change endpoint w (kmswWindowEdgeMapInf w t e.1, e.2) =
        endpoint w (kmswWindowEdgeMapInf w t d.1, d.2) at hep
      rw [window_endpoint, window_endpoint] at hep
      exact kmswWindowVertexMapInf_injective w t hep
    have heb : e.1 < (kmswStage u m).nextEdge := by
      apply hcs e.1
      cases hb : e.2
      · exact Or.inl (by
          simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using heLocal)
      · exact Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using heLocal)
    let z : StageDart (kmswStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, dartValue_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))





theorem shiftInfRot_firstReturn (w : ℕ → Fin 3) (t : ℕ)
    (hfinS : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => w (t + i)) n).nextEdge ∧
        ((kmswStage (fun i => w (t + i)) n).west e = v ∨
          (kmswStage (fun i => w (t + i)) n).east e = v)}.Finite)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    let J : (ℕ × Bool) → ℕ × Bool :=
      fun x => (kmswShiftEdgeMapAll w t x.1 x.1, x.2)
    ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfinW : _ → _)^[k] (J d) =
        J (kmswInfRot (fun i => w (t + i)) hfinS d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswInfRot w hfinW : _ → _)^[j] (J d) ∉ Set.range J := by
  let I : (ℕ × Bool) → ℕ × Bool := fun x => (kmswWindowEdgeMapInf w t x.1, x.2)
  let ρw := kmswInfRot w hfinW
  let ρs := kmswInfRot (fun i => w (t + i)) hfinS
  have hmap : (fun x : ℕ × Bool => (kmswShiftEdgeMapAll w t x.1 x.1, x.2)) = I := by
    funext x
    apply Prod.ext
    · exact (shift_edge_eq_window w t x.1 x.1
        (kmsw_edge_allocated_by_self _ x.1)).trans
        (kmswWindowEdgeMapInf_eq_stage w t x.1 x.1
          (kmsw_edge_allocated_by_self _ x.1)).symm
    · rfl
  suffices hI : ∃ k : ℕ, 0 < k ∧
      (ρw : _ → _)^[k] (I d) = I (ρs d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (ρw : _ → _)^[j] (I d) ∉ Set.range I by
    simpa only [← hmap] using hI
  have hcancel (n : ℕ) (x : ℕ × Bool) :
      (ρw : _ → _)^[n] ((ρw.symm : _ → _)^[n] x) = x :=
    (Function.LeftInverse.iterate ρw.apply_symm_apply n) x
  obtain ⟨k, hk, hreturn, hgap⟩ :=
    windowInfRot_symm_firstReturn w t hfinS hfinW (ρs d)
  change (ρw.symm : _ → _)^[k] (I (ρs d)) = I (ρs.symm (ρs d)) at hreturn
  rw [Equiv.symm_apply_apply] at hreturn
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← hreturn, hcancel]
  · intro j hj hjk hmem
    have hreverse :
        (ρw : _ → _)^[j] (I d) =
          (ρw.symm : _ → _)^[k - j] (I (ρs d)) := by
      calc
        (ρw : _ → _)^[j] (I d) =
            (ρw : _ → _)^[j] ((ρw.symm : _ → _)^[k] (I (ρs d))) :=
          congrArg _ hreturn.symm
        _ = (ρw : _ → _)^[j]
            ((ρw.symm : _ → _)^[j] ((ρw.symm : _ → _)^[k - j] (I (ρs d)))) := by
          rw [← Function.iterate_add_apply, show j + (k - j) = k by omega]
        _ = (ρw.symm : _ → _)^[k - j] (I (ρs d)) := hcancel j _
    apply hgap (k - j) (by omega) (by omega)
    change (ρw.symm : _ → _)^[k - j] (I (ρs d)) ∈ Set.range I
    rw [← hreverse]
    exact hmem

private theorem induced_rotation_scan {α β : Type*} (σ : α → α) (τ : β → β)
    (I : α → β)
    (hret : ∀ x, ∃ k : ℕ, 0 < k ∧ τ^[k] (I x) = I (σ x) ∧
      ∀ j : ℕ, 0 < j → j < k → τ^[j] (I x) ∉ Set.range I)
    (d : α) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧
      (∀ n, τ^[N n] (I d) = I (σ^[n] d)) ∧
      (∀ n j, j < N n →
        (τ^[j] (I d) ∈ Set.range I ↔ ∃ i < n, j = N i)) := by
  classical
  let r (n : ℕ) := (hret (σ^[n] d)).choose
  have hr (n : ℕ) : 0 < r n ∧
      τ^[r n] (I (σ^[n] d)) = I (σ (σ^[n] d)) ∧
      ∀ j : ℕ, 0 < j → j < r n →
        τ^[j] (I (σ^[n] d)) ∉ Set.range I :=
    (hret (σ^[n] d)).choose_spec
  let N : ℕ → ℕ := fun n => Nat.rec 0 (fun i acc => acc + r i) n
  have hN0 : N 0 = 0 := rfl
  have hNs (n : ℕ) : N (n + 1) = N n + r n := rfl
  have hmono : StrictMono N := strictMono_nat_of_lt_succ fun n => by
    rw [hNs]
    have := (hr n).1
    omega
  have hmap (n : ℕ) : τ^[N n] (I d) = I (σ^[n] d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hNs, Nat.add_comm, Function.iterate_add_apply, ih,
        (hr n).2.1, Function.iterate_succ_apply']
  refine ⟨N, hmono, hN0, hmap, ?_⟩
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    constructor
    · intro hm
      rcases Nat.lt_trichotomy j (N n) with hlt | heq | hgt
      · obtain ⟨i, hi, he⟩ := (ih j hlt).1 hm
        exact ⟨i, by omega, he⟩
      · exact ⟨n, by omega, heq⟩
      · have hpos : 0 < j - N n := by omega
        have hbound : j - N n < r n := by rw [hNs] at hj; omega
        apply False.elim
        apply (hr n).2.2 (j - N n) hpos hbound
        have he : τ^[j - N n] (I (σ^[n] d)) = τ^[j] (I d) := by
          rw [← hmap, ← Function.iterate_add_apply,
            Nat.sub_add_cancel hgt.le]
        rw [he]
        exact hm
    · rintro ⟨i, _, rfl⟩
      rw [hmap]
      exact ⟨σ^[i] d, rfl⟩

private theorem induced_cyclicOrder_iff {α β : Type*} (σ : α → α) (τ : β → β)
    (I : α → β) (hinj : Function.Injective I)
    (hret : ∀ x, ∃ k : ℕ, 0 < k ∧ τ^[k] (I x) = I (σ x) ∧
      ∀ j : ℕ, 0 < j → j < k → τ^[j] (I x) ∉ Set.range I)
    (d e f : α) :
    (∃ i j : ℕ, 0 < i ∧ i < j ∧ σ^[i] d = e ∧ σ^[j] d = f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → σ^[k] d ≠ d) ↔
    (∃ i j : ℕ, 0 < i ∧ i < j ∧ τ^[i] (I d) = I e ∧ τ^[j] (I d) = I f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → τ^[k] (I d) ≠ I d) := by
  obtain ⟨N, hmono, hzero, hmap, hhits⟩ := induced_rotation_scan σ τ I hret d
  have hpos {i : ℕ} : 0 < N i ↔ 0 < i := by
    calc
      0 < N i ↔ N 0 < N i := by rw [hzero]
      _ ↔ 0 < i := hmono.lt_iff_lt
  have hlower (n : ℕ) : n ≤ N n := by
    induction n with
    | zero => omega
    | succ n ih =>
      have hlt : N n < N (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  constructor
  · rintro ⟨i, j, hi, hij, hei, hfj, hno⟩
    refine ⟨N i, N j, hpos.mpr hi, hmono hij, ?_, ?_, ?_⟩
    · exact (hmap i).trans (congrArg I hei)
    · exact (hmap j).trans (congrArg I hfj)
    · intro k hk hkj heq
      have hbound : k < N (j + 1) :=
        hkj.trans_lt (hmono (Nat.lt_succ_self j))
      obtain ⟨q, _, hkq⟩ := (hhits (j + 1) k hbound).1 ⟨d, heq.symm⟩
      have hqpos : 0 < q := hpos.mp (hkq ▸ hk)
      have hqj : q ≤ j := hmono.le_iff_le.mp (hkq ▸ hkj)
      apply hno q hqpos hqj
      apply hinj
      rw [hkq, hmap] at heq
      exact heq
  · rintro ⟨i, j, hi, hij, hei, hfj, hno⟩
    have hjbound : j < N (j + 1) := by have := hlower (j + 1); omega
    obtain ⟨a, _, hia⟩ := (hhits (j + 1) i (hij.trans hjbound)).1 ⟨e, hei.symm⟩
    obtain ⟨b, _, hjb⟩ := (hhits (j + 1) j hjbound).1 ⟨f, hfj.symm⟩
    refine ⟨a, b, hpos.mp (hia ▸ hi), hmono.lt_iff_lt.mp ?_, ?_, ?_, ?_⟩
    · exact hia ▸ hjb ▸ hij
    · apply hinj
      rw [hia, hmap] at hei
      exact hei
    · apply hinj
      rw [hjb, hmap] at hfj
      exact hfj
    · intro k hk hkb heq
      apply hno (N k) (hpos.mpr hk)
      · rw [hjb]
        exact hmono.monotone hkb
      · rw [hmap, heq]

private theorem shift_edge_inf_eq_window (w : ℕ → Fin 3) (t e : ℕ) :
    kmswShiftEdgeMapAll w t e e = kmswWindowEdgeMapInf w t e :=
  (shift_edge_eq_window w t e e (kmsw_edge_allocated_by_self _ e)).trans
    (kmswWindowEdgeMapInf_eq_stage w t e e (kmsw_edge_allocated_by_self _ e)).symm





theorem shiftHatInfRot_cyclicOrder_iff (w : ℕ → Fin 3) (t : ℕ)
    (h : HasFlowLineHits (fun i => w (t + i)))
    (hfinS : ∀ v, {e : ℕ | ∃ n,
      e < (kmswStage (fun i => w (t + i)) n).nextEdge ∧
        ((kmswStage (fun i => w (t + i)) n).west e = v ∨
          (kmswStage (fun i => w (t + i)) n).east e = v)}.Finite)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d e f : ℕ × Bool) :
    let u := fun i => w (t + i)
    let φ : (ℕ × Bool) → ℕ × Bool := fun x =>
      (kmswShiftEdgeMapAll w t (hatLimitEdgeMap u h x.1) (hatLimitEdgeMap u h x.1), x.2)
    let ρh := kmswInfRot (hatCodes u h) (hatCodes_inducedFiniteIncidence u h hfinS)
    let ρw := kmswInfRot w hfinW
    (∃ i j : ℕ, 0 < i ∧ i < j ∧
      (ρh : _ → _)^[i] d = e ∧ (ρh : _ → _)^[j] d = f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → (ρh : _ → _)^[k] d ≠ d) ↔
    (∃ i j : ℕ, 0 < i ∧ i < j ∧
      (ρw : _ → _)^[i] (φ d) = φ e ∧ (ρw : _ → _)^[j] (φ d) = φ f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → (ρw : _ → _)^[k] (φ d) ≠ φ d) := by
  let u := fun i => w (t + i)
  let I : (ℕ × Bool) → ℕ × Bool := fun x => (hatLimitEdgeMap u h x.1, x.2)
  let J : (ℕ × Bool) → ℕ × Bool := fun x => (kmswShiftEdgeMapAll w t x.1 x.1, x.2)
  have hinj : Function.Injective J := by
    intro a b hab
    apply Prod.ext
    · apply kmswWindowEdgeMapInf_injective w t
      have he := congrArg Prod.fst hab
      change kmswShiftEdgeMapAll w t a.1 a.1 = kmswShiftEdgeMapAll w t b.1 b.1 at he
      rwa [shift_edge_inf_eq_window, shift_edge_inf_eq_window] at he
    · have hb := congrArg (fun z : ℕ × Bool => z.2) hab
      exact hb
  exact (hatInfRot_cyclicOrder_iff u h hfinS d e f).trans
    (induced_cyclicOrder_iff (kmswInfRot u hfinS : _ → _)
      (kmswInfRot w hfinW : _ → _) J hinj (shiftInfRot_firstReturn w t hfinS hfinW)
      (I d) (I e) (I f))

end DirectedDistances.KMSW
