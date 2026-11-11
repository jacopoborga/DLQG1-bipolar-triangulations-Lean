module

public import DirectedDistances.KMSW.PrimedMissingEdgeImages
public import DirectedDistances.KMSW.HatLimitRotation
public import DirectedDistances.PlanarMap.FiniteStarFirstReturn
import DirectedDistances.KMSW.PrimedRotInducedOriented

/-! Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.

Transport the corrected finite-stage primed rotations through stabilization. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

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

private theorem complete_exists (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (v : ℕ) : ∃ n, kmswVertexComplete w n v := by
  obtain ⟨B, hB⟩ := (hfin v).bddAbove
  refine ⟨B, fun e he => ?_⟩
  have hm : e ∈ {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)} :=
    ⟨e, kmsw_edge_allocated_by_self w e, he⟩
  exact (hB hm).trans_lt (kmsw_edge_allocated_by_self w B)

private theorem complete_mono' (w : ℕ → Fin 3) {n m v : ℕ} (hnm : n ≤ m)
    (hc : kmswVertexComplete w n v) : kmswVertexComplete w m v := by
  intro e he
  exact (hc e he).trans_le (kmswStage_nextEdge_mono w hnm)

private theorem rot_endpoint' (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) :
    stageEndpoint (kmswStage w n) (stageRot w n d) =
      stageEndpoint (kmswStage w n) d :=
  ((stageRot_sameCycle_iff_endpoint_eq w n d (stageRot w n d)).1 ⟨1, rfl⟩).symm

private theorem iterate_endpoint (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart (kmswStage w n).nextEdge) (k : ℕ) :
    stageEndpoint (kmswStage w n) ((stageRot w n : _ → _)^[k] d) =
      stageEndpoint (kmswStage w n) d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', rot_endpoint', ih]

private theorem inf_iterate_eq_stage (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (n : ℕ) (d : StageDart (kmswStage w n).nextEdge)
    (hc : kmswVertexComplete w n (stageEndpoint (kmswStage w n) d)) (k : ℕ) :
    (kmswInfRot w hfin : _ → _)^[k] (dartValue d) =
      dartValue ((stageRot w n : _ → _)^[k] d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact kmswInfRot_eq_stage w hfin n _ (by rw [iterate_endpoint]; exact hc)

private def ordinaryDart (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswMissingRootStage u m).nextEdge) :
    StageDart (kmswStage u m).nextEdge :=
  (Fin.cast (kmswMissingRootStage_agree u m).2.1 d.1, d.2)

private theorem localEndpoint_eq (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswMissingRootStage u m).nextEdge) :
    stageEndpoint (kmswMissingRootStage u m) d = endpoint u (dartValue d) := by
  obtain ⟨_, he, hw, ht, _⟩ := kmswMissingRootStage_agree u m
  have hb : d.1.val < (kmswStage u m).nextEdge := by rw [← he]; exact d.1.isLt
  obtain ⟨hW, hE⟩ := edge_endpoints_eq u hb
  cases hd : d.2 <;>
    simp only [stageEndpoint, endpoint, dartValue, hd, Bool.false_eq_true,
      ↓reduceIte, hw, ht, hW, hE]

private theorem localEndpoint_bound (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswMissingRootStage u m).nextEdge) :
    stageEndpoint (kmswMissingRootStage u m) d <
      (kmswMissingRootStage u m).nextVertex := by
  have hb := kmswStage_endpoints_lt_nextVertex u m d.1.val
    (ordinaryDart u m d).1.isLt
  obtain ⟨hv, _, hw, ht, _⟩ := kmswMissingRootStage_agree u m
  cases hd : d.2 <;> simp only [stageEndpoint, hd, Bool.false_eq_true, ↓reduceIte,
    hv, hw, ht]
  · exact hb.1
  · exact hb.2

private theorem resize_value {k l : ℕ} (hkl : k = l)
    (σ : Equiv.Perm (StageDart k)) (d : StageDart l) :
    dartValue (StageRotation.resize hkl σ d) =
      dartValue (σ (Fin.cast hkl.symm d.1, d.2)) := by
  cases hkl
  rfl

private theorem infRot_eq_local (u : ℕ → Fin 3) (hfin : primedLimitFiniteIncidence u)
    (m : ℕ) (d : StageDart (kmswMissingRootStage u m).nextEdge)
    (hc : kmswVertexComplete u m (endpoint u (dartValue d))) :
    kmswInfRot u hfin (dartValue d) = dartValue (primedLocalRot u m d) := by
  rw [primedLocalRot, resize_value]
  exact kmswInfRot_eq_stage u hfin m (ordinaryDart u m d)
    (by rw [stageEndpoint_eq]; exact hc)

private theorem primed_endpoint (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d : ℕ × Bool) :
    endpoint w (primedLimitDartMap w h d) =
      primedLimitVertexMap w h (endpoint (primedCode (primedSimInput w) h) d) := by
  let u := primedCode (primedSimInput w) h
  have he : d.1 < (kmswMissingRootStage u d.1).nextEdge := by
    rw [(kmswMissingRootStage_agree u d.1).2.1]
    exact kmsw_edge_allocated_by_self u d.1
  let x : StageDart (kmswMissingRootStage u d.1).nextEdge := (⟨d.1, he⟩, d.2)
  calc
    endpoint w (primedLimitDartMap w h d) =
        endpoint w (dartValue (primedDartMapOriented w h d.1 x)) :=
      congrArg (endpoint w) (primedLimitDartMap_eq_stage w h d.1 x)
    _ = stageEndpoint (kmswStage w (primedStageTime w h d.1))
        (primedDartMapOriented w h d.1 x) := (stageEndpoint_eq w _ _).symm
    _ = primedAllVertexMap w h d.1
        (stageEndpoint (kmswMissingRootStage u d.1) x) :=
      primedDartMapOriented_endpoint w h d.1 x
    _ = primedLimitVertexMap w h (stageEndpoint (kmswMissingRootStage u d.1) x) :=
      ((primedLimit_maps_eq_of_allocated w h d.1).2 _
        (localEndpoint_bound u d.1 x)).symm
    _ = primedLimitVertexMap w h (endpoint u d) :=
      congrArg (primedLimitVertexMap w h) (localEndpoint_eq u d.1 x)

private theorem primed_endpoint_reflect (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (d e : ℕ × Bool)
    (he : endpoint w (primedLimitDartMap w h d) =
      endpoint w (primedLimitDartMap w h e)) :
    endpoint (primedCode (primedSimInput w) h) d =
      endpoint (primedCode (primedSimInput w) h) e := by
  rw [primed_endpoint, primed_endpoint] at he
  exact (primedLimit_maps_injective_on_allocated w h).2
    ((primedLocalIds_eventually_allocated w h).2 _)
    ((primedLocalIds_eventually_allocated w h).2 _) he

private theorem stageTime_mono (w : ℕ → Fin 3) (h : HasFlowLineHits w) :
    Monotone (primedStageTime w h) :=
  monotone_nat_of_le_succ (primedStageTime_succ_le w h)

private theorem stageTime_unbounded (w : ℕ → Fin 3) (h : HasFlowLineHits w) (N : ℕ) :
    ∃ m, N ≤ primedStageTime w h m := by
  have hindex (k : ℕ) : k ≤ walkNR w h k := by
    induction k with
    | zero => simp only [walkNR_zero, Nat.le_refl]
    | succ k ih =>
      have hL := (walkNL_spec w h k).1
      have hR := (walkNR_succ_spec w h k).1
      omega
  refine ⟨primedIntervalBase (primedSimInput w) h (N + 1), ?_⟩
  rw [primedStageTime_at_crossing]
  have hN := hindex (N + 1)
  omega

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
Stabilization of the corrected finite-stage primed induced rotation. -/
private theorem primedLimitRotation_firstReturn (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfinW : primedLimitFiniteIncidence w) (d : ℕ × Bool) :
    let I := primedLimitDartMap w h
    ∃ k : ℕ, 0 < k ∧
      (kmswInfRot w hfinW : _ → _)^[k] (I d) =
        I (kmswInfRot (primedCode (primedSimInput w) h)
          (primedCode_finiteIncidence w h hfinW) d) ∧
      ∀ j : ℕ, 0 < j → j < k →
        (kmswInfRot w hfinW : _ → _)^[j] (I d) ∉ Set.range I := by
  let u := primedCode (primedSimInput w) h
  let I := primedLimitDartMap w h
  let hfinU := primedCode_finiteIncidence w h hfinW
  obtain ⟨Ns, hNs⟩ := complete_exists u hfinU (endpoint u d)
  obtain ⟨Nw, hNw⟩ := complete_exists w hfinW (endpoint w (I d))
  obtain ⟨M, hM⟩ := stageTime_unbounded w h Nw
  let m := max Ns (max M d.1)
  have hsm : Ns ≤ m := Nat.le_max_left _ _
  have hMm : M ≤ m := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdm : d.1 ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcs := complete_mono' u hsm hNs
  have hcw := complete_mono' w (hM.trans (stageTime_mono w h hMm)) hNw
  have hd : d.1 < (kmswMissingRootStage u m).nextEdge := by
    rw [(kmswMissingRootStage_agree u m).2.1]
    exact kmsw_nextEdge_unbounded u d.1 m hdm
  let x : StageDart (kmswMissingRootStage u m).nextEdge := (⟨d.1, hd⟩, d.2)
  let y := primedDartMapOriented w h m x
  have hmap (z : StageDart (kmswMissingRootStage u m).nextEdge) :
      dartValue (primedDartMapOriented w h m z) = I (dartValue z) :=
    (primedLimitDartMap_eq_stage w h m z).symm
  have hy : dartValue y = I d := hmap x
  have hcy : kmswVertexComplete w (primedStageTime w h m)
      (stageEndpoint (kmswStage w (primedStageTime w h m)) y) := by
    rw [stageEndpoint_eq, hy]
    exact hcw
  have hiter (j : ℕ) :
      (kmswInfRot w hfinW : _ → _)^[j] (I d) =
        dartValue ((stageRot w (primedStageTime w h m) : _ → _)^[j] y) := by
    rw [← hy]
    exact inf_iterate_eq_stage w hfinW _ y hcy j
  obtain ⟨k, hk, hreturn, hgap⟩ := primedRotInducedOriented_all w h m x
  change (stageRot w (primedStageTime w h m) : _ → _)^[k] y =
    primedDartMapOriented w h m (primedLocalRot u m x) at hreturn
  refine ⟨k, hk, ?_, ?_⟩
  · calc
      (kmswInfRot w hfinW : _ → _)^[k] (I d) =
          dartValue ((stageRot w (primedStageTime w h m) : _ → _)^[k] y) := hiter k
      _ = dartValue (primedDartMapOriented w h m (primedLocalRot u m x)) :=
        congrArg dartValue hreturn
      _ = I (dartValue (primedLocalRot u m x)) := hmap _
      _ = I (kmswInfRot u hfinU d) :=
        congrArg I (infRot_eq_local u hfinU m x hcs).symm
  · intro j hj hjk hmem
    obtain ⟨e, he⟩ := hmem
    have hep : endpoint w (I e) = endpoint w (I d) := by
      calc
        endpoint w (I e) = endpoint w
            (dartValue ((stageRot w (primedStageTime w h m) : _ → _)^[j] y)) :=
          congrArg (endpoint w) (he.trans (hiter j))
        _ = endpoint w (dartValue y) := by
          rw [← stageEndpoint_eq, ← stageEndpoint_eq, iterate_endpoint]
        _ = endpoint w (I d) := congrArg (endpoint w) hy
    have heLocal := primed_endpoint_reflect w h e d hep
    have heb : e.1 < (kmswMissingRootStage u m).nextEdge := by
      rw [(kmswMissingRootStage_agree u m).2.1]
      apply hcs e.1
      cases hb : e.2
      · exact Or.inl (by
          simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using heLocal)
      · exact Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using heLocal)
    let z : StageDart (kmswMissingRootStage u m).nextEdge := (⟨e.1, heb⟩, e.2)
    apply hgap j hj hjk
    refine ⟨z, dartValue_injective _ ?_⟩
    exact (hmap z).trans (he.trans (hiter j))

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The coherent dart equivalence intertwines the compressed rotation with first return -/
theorem primedGeometricDartEquiv_rotation (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let S := primeDartSet w hfin hb
    primedGeometricDartEquiv w h hfin hb
        (kmswInfRot (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin) d) =
      drawingFirstReturnPerm P S (primedGeometricDartEquiv w h hfin hb d) := by
  classical
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := primeDartSet w hfin hb
  let H := primedGeometricDartEquiv w h hfin hb
  let σ := kmswInfRot w hfin
  obtain ⟨k, hk, hreturn, hgap⟩ := primedLimitRotation_firstReturn w h hfin d
  change (σ : _ → _)^[k] (H d).val =
    (H (kmswInfRot (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin) d)).val at hreturn
  have hmem : (σ : _ → _)^[k] (H d).val ∈ S := by
    rw [hreturn]
    exact (H _).property
  have htime : subsetFirstReturnTime σ S (drawingPositiveReturn P S) (H d) = k := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (drawingPositiveReturn P S (H d)) ⟨hk, hmem⟩
    · by_contra hn
      have hs := subsetFirstReturnTime_spec σ S (drawingPositiveReturn P S) (H d)
      have hlt : subsetFirstReturnTime σ S (drawingPositiveReturn P S) (H d) < k := by
        omega
      apply hgap _ hs.1 hlt
      obtain ⟨a, ha⟩ := H.surjective ⟨_, hs.2.1⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  apply Subtype.ext
  change (H (kmswInfRot (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin) d)).val =
    (subsetFirstReturnPerm σ S (drawingPositiveReturn P S)
      (drawingPositiveReturnInv P S) (H d)).val
  rw [subsetFirstReturnPerm_apply, htime]
  exact hreturn.symm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The face successor is inverse first-return rotation after geometric edge reversal.
This identifies the permutations, not complementary components or the external boundary. -/
theorem primedGeometricDartEquiv_faceSuccessor (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let S := primeDartSet w hfin hb
    primedGeometricDartEquiv w h hfin hb
        (kmswInfFaceSucc (primedCode (primedSimInput w) h)
          (primedCode_finiteIncidence w h hfin) d) =
      (drawingFirstReturnPerm P S).symm
        (restrictedFlip P S (primeDartSet_flip_closed w hfin hb)
          (primedGeometricDartEquiv w h hfin hb d)) := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let S := primeDartSet w hfin hb
  let H := primedGeometricDartEquiv w h hfin hb
  let ρ := kmswInfRot (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin)
  let τ := drawingFirstReturnPerm P S
  change H (ρ.symm (futureMapEdgeInv d)) =
    τ.symm (restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d))
  apply τ.injective
  rw [Equiv.apply_symm_apply]
  have hflip : restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d) =
      H (futureMapEdgeInv d) := by
    apply Subtype.ext
    exact (primedLimitDartMap_edgeInv w h d).symm
  rw [hflip]
  have hr := primedGeometricDartEquiv_rotation w h hfin hb (ρ.symm (futureMapEdgeInv d))
  change H (ρ (ρ.symm (futureMapEdgeInv d))) =
    τ (H (ρ.symm (futureMapEdgeInv d))) at hr
  rw [Equiv.apply_symm_apply] at hr
  exact hr.symm

/-- Helper toward Lemma 5.13 (lem-quad-kmsw); not a paper result.
The transported primed rotation is the counterclockwise successor in the actual
restricted drawing. Its rotation parameter is definitionally first return. -/
theorem primedGeometricDartEquiv_realizedRotation (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let S := primeDartSet w hfin hb
    let H := primedGeometricDartEquiv w h hfin hb
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    CcwSuccessor {e | restrictedVertex P S e = restrictedVertex P S (H d)}
      (fun e => (Q.arc e).initialDirection) (H d)
      (H (kmswInfRot (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin) d)) := by
  dsimp only
  rw [primedGeometricDartEquiv_rotation]
  exact (mhatPrimeDrawing w hfin hb (monotone_family_all w)).rotation_agreement
    (primedGeometricDartEquiv w h hfin hb d)

end DirectedDistances.KMSW
