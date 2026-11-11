module

public import DirectedDistances.Recursive.BusemannShiftLaw
public import DirectedDistances.KMSW.BusemannM0Unconditional
import DirectedDistances.KMSW.DirectedContainHat
import DirectedDistances.Recursive.OneStepTransport

/-! # A measurable boundary SDP Busemann representative and its shifted law

Helpers for `prop:SDP-recursive-equation`
eventual values over finite stages and right-boundary targets give a measurable
representative on code space. Values off the almost-sure characterization event
are junk. In particular, totalizing a code does not change the SDP convention:
unreachable distance remains `⊤`, and only proved reachable distances are
identified with finite integer values.

The hit-indexed boundary and exploration-graph identifications remain subject
to F1/F4 in `BusemannM0Unconditional`. The process-law identity and first-step
independence below supply probabilistic inputs only; they do not prove the
recursive equation or the remaining Busemann properties. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory Filter ProbabilityTheory
open DirectedDistances.RandomWalk

private theorem measurable_select {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

private theorem measurable_boundaryIdTotal (k : ℤ) :
    Measurable (fun ω => busemannBoundaryIdTotal ω k) := by
  exact measurable_select
    (fun n ω => (kmswStage (fun i => ω (i + 1)) n).west
      (kmswStage (fun i => ω (i + 1)) n).active)
    (fun n => measurable_kmswStage_shift_comp n (fun s => s.west s.active))
    (fun ω => (boundaryHitTimeTotal ω k).toNat)
    ((measurable_of_countable ENat.toNat).comp (measurable_boundaryHitTimeTotal k))

private theorem boundaryIdTotal_eq (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) :
    busemannBoundaryIdTotal ω k = boundaryVertex (fun i => ω (i + 1)) h k := by
  unfold busemannBoundaryIdTotal
  rw [boundaryHitTimeTotal_eq_boundaryHitTime ω h k, ENat.toNat_natCast]
  rw [boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1




@[expose] noncomputable def busemannStageSdpCode
    (ω : ℕ → Fin 3) (n a b : ℕ) : ℤ :=
  Int.ofNat ((sdp
    (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩).toNat)

private def stageCongrMap {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) :
    Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) where
  obj v := ⟨v.id⟩
  map {_ _} e := ⟨e.val, by simpa only [h] using e.property⟩

private theorem stageCongrMap_length {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) {a b : StagePresentVertex w n}
    (p : Path a b) : ((stageCongrMap h).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem stage_sdp_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    sdp (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      sdp (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  apply le_antisymm
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩, (p.length : ℕ∞)
    refine le_iInf fun p => ?_
    have hp := sdp_le_length ((stageCongrMap h.symm).mapPath p)
    rw [stageCongrMap_length] at hp
    exact hp
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w n) ⟨b⟩, (p.length : ℕ∞)
    refine le_iInf fun p => ?_
    have hp := sdp_le_length ((stageCongrMap h).mapPath p)
    rw [stageCongrMap_length] at hp
    exact hp

private theorem measurable_stageSdpCode (n : ℕ)
    (a b : (ℕ → Fin 3) → ℕ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => busemannStageSdpCode ω n (a ω) (b ω)) := by
  apply measurable_select
    (fun p : ℕ × ℕ => fun ω => busemannStageSdpCode ω n p.1 p.2)
    _ (fun ω => (a ω, b ω)) (ha.prodMk hb)
  intro p
  refine measurable_of_factors_prefix (n + 1) _ (fun ω ω' h => ?_)
  unfold busemannStageSdpCode
  rw [stage_sdp_congr (kmswStage_shift_congr (fun i _ hi => h i (by omega)))]

private theorem path_in_late_stages {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ q : Path (⟨a.id⟩ : StagePresentVertex w n) ⟨b.id⟩,
        q.length = p.length := by
  induction p with
  | nil => exact ⟨0, fun _ _ => ⟨Path.nil, rfl⟩⟩
  | @cons b c p e ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := e.property.1.eventually_present
    refine ⟨max N M, fun n hn => ?_⟩
    obtain ⟨q, hq⟩ := hN n ((Nat.le_max_left _ _).trans hn)
    obtain ⟨he, hp⟩ := hM n ((Nat.le_max_right _ _).trans hn)
    let en : (⟨b.id⟩ : StagePresentVertex w n) ⟶ ⟨c.id⟩ :=
      ⟨e.val, he, hp,
        (edge_endpoints_eq w he).1.trans e.property.2.1,
        (edge_endpoints_eq w he).2.trans e.property.2.2⟩
    exact ⟨q.cons en, by simp only [Path.length_cons, hq]⟩

private theorem stageSdpCode_eventually_eq (ω : ℕ → Fin 3)
    {a b : PresentVertex (fun i => ω (i + 1))} (hr : Reachable a b) :
    ∀ᶠ n in atTop, busemannStageSdpCode ω n a.id b.id =
      ((sdp a b).toNat : ℤ) := by
  obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
  obtain ⟨N, hN⟩ := path_in_late_stages p
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn
  have heq : sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩ =
      sdp a b := by
    apply le_antisymm
    · calc
        sdp (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩
            ≤ (q.length : ℕ∞) := sdp_le_length q
        _ = (p.length : ℕ∞) := by rw [hq]
        _ = sdp a b := hp
    · exact sdp_limit_le_sdp_stage (fun i => ω (i + 1)) n ⟨a.id⟩ ⟨b.id⟩
  unfold busemannStageSdpCode
  rw [heq]
  rfl

/-- Eventual stage SDP difference to right-boundary index `j`. Zero is junk
if this sequence fails to stabilize. Helper for `prop:SDP-recursive-equation` -/
@[expose] noncomputable def boundarySdpDifference
    (ω : ℕ → Fin 3) (k : ℤ) (j : ℕ) : ℤ :=
  eventualIntValue 0 (fun n =>
    busemannStageSdpCode ω n (busemannBoundaryIdTotal ω k)
      (busemannBoundaryIdTotal ω (j : ℤ)) -
      busemannStageSdpCode ω n (busemannBoundaryIdTotal ω 0)
        (busemannBoundaryIdTotal ω (j : ℤ)))

/-- Coordinate measurability of the eventual stage difference. Helper for
subject to F1/F4. Values outside the reachable stabilization case are junk. -/
theorem measurable_boundarySdpDifference (k : ℤ) (j : ℕ) :
    Measurable (fun ω => boundarySdpDifference ω k j) := by
  exact measurable_eventualIntValue 0 _ (fun n =>
    (measurable_stageSdpCode n _ _ (measurable_boundaryIdTotal k)
      (measurable_boundaryIdTotal (j : ℤ))).sub
    (measurable_stageSdpCode n _ _ (measurable_boundaryIdTotal 0)
      (measurable_boundaryIdTotal (j : ℤ))))

private theorem boundarySdpDifference_eq (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) (j : ℕ)
    (hr0 : Reachable (boundaryPresentVertex _ h 0) (boundaryPresentVertex _ h (j : ℤ)))
    (hrk : Reachable (boundaryPresentVertex _ h k) (boundaryPresentVertex _ h (j : ℤ))) :
    boundarySdpDifference ω k j =
      ((sdp (boundaryPresentVertex _ h k) (boundaryPresentVertex _ h (j : ℤ))).toNat : ℤ) -
        ((sdp (boundaryPresentVertex _ h 0) (boundaryPresentVertex _ h (j : ℤ))).toNat : ℤ) := by
  unfold boundarySdpDifference
  simp only [boundaryIdTotal_eq ω h]
  apply eventualIntValue_eq
  filter_upwards [stageSdpCode_eventually_eq ω hrk,
    stageSdpCode_eventually_eq ω hr0] with n hk h0
  exact congrArg₂ (· - ·) hk h0

private theorem allocated_reaches_boundary_tail (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : PresentVertex w)
    (hv : kmswVertexAllocated w v) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w h l) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨q, hqrec, hnq⟩ :=
    (right_record_infinite w h.R_unbounded_below).exists_gt n
  have hqpos : 0 < q := by omega
  have hrec : ∀ i < q, R w q < R w i := hqrec
  have hneg : R w q < 0 := by
    have hh := hrec 0 hqpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w q
  have hb : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w h b = q := by
    have hle : boundaryHitTime w h b ≤ q := by
      rw [boundaryHitTime_right_eq_find w h hb]
      exact Nat.find_min' (h.rightHit b hb) (by dsimp [b]; omega)
    have hge : q ≤ boundaryHitTime w h b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w h b) (by omega)
      have hh' := boundaryHitTime_right_spec w h hb
      rw [hh'] at hh
      have hRb : R w q = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w q = boundaryPresentVertex w h b := by
    apply congrArg PresentVertex.mk
    have he := edge_endpoints_eq w (act_lt_nextEdge w (le_refl q))
    rw [boundaryVertex_eq_edgeWest_hit w h b, htime]
    exact he.1
  have hvq : v.id < (kmswStage w (q - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ q - 1))
  have hr : Reachable v (boundaryPresentVertex w h b) := by
    have hh := allocated_vertex_reaches_strict_record w q
      (fun i hi => by have := hrec i hi; omega) hqpos v.id hvq
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w h (by omega) (by omega)

/-- A measurable code-space SDP Busemann representative from successive
stage and boundary eventual values. Its almost-sure meaning is proved below;
values off that event are junk. Helper for `prop:SDP-recursive-equation` -/
@[expose] noncomputable def busemannSDPMeasurableVersion
    (ω : ℕ → Fin 3) (k : ℤ) : ℤ :=
  eventualIntValue 0 (fun j => boundarySdpDifference ω k j)

/-- Each coordinate of the SDP representative is measurable. Helper for
subject to F1/F4; values off the characterization event are junk. -/
theorem measurable_busemannSDPMeasurableVersion (k : ℤ) :
    Measurable (fun ω => busemannSDPMeasurableVersion ω k) := by
  exact measurable_eventualIntValue 0 _ (measurable_boundarySdpDifference k)

private theorem busemannSDPMeasurableVersion_eq_of_data (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ) (hX : IsBoundaryBusemannSDP (boundaryPresentVertex _ h) X)
    (k : ℤ) : busemannSDPMeasurableVersion ω k = X k := by
  let w := fun i => ω (i + 1)
  obtain ⟨B0, hB0⟩ := allocated_reaches_boundary_tail w h
    (boundaryPresentVertex w h 0) (boundaryVertex_allocated w h 0)
  obtain ⟨Bk, hBk⟩ := allocated_reaches_boundary_tail w h
    (boundaryPresentVertex w h k) (boundaryVertex_allocated w h k)
  let B := max B0 Bk
  let y : ℕ → PresentVertex w := fun j => boundaryPresentVertex w h ((B + j : ℕ) : ℤ)
  have hy : Function.Injective y := by
    intro i j hij
    have hh := boundaryVertex_injective w h (congrArg PresentVertex.id hij)
    dsimp [y, boundaryPresentVertex] at hh
    omega
  have hr : ∀ j, Reachable (boundaryPresentVertex w h 0) (y j) ∧
      Reachable (boundaryPresentVertex w h k) (y j) := by
    intro j
    exact ⟨hB0 _ (by dsimp [B]; omega), hBk _ (by dsimp [B]; omega)⟩
  obtain ⟨N, hN⟩ := hX.2 0 k y hy hr
  unfold busemannSDPMeasurableVersion
  apply eventualIntValue_eq
  refine eventually_atTop.mpr ⟨B + N, fun j hj => ?_⟩
  have hjB : B + (j - B) = j := by omega
  have heq := boundarySdpDifference_eq ω h k (B + (j - B))
    (hr (j - B)).1 (hr (j - B)).2
  have hx := hN (j - B) (by omega)
  rw [hX.1, sub_zero] at hx
  exact (congrArg (boundarySdpDifference ω k) hjB).symm.trans (heq.trans hx.symm)

/-- Almost surely, simultaneously at every integer index, this measurable
representative is a boundary SDP Busemann function for a hit witness. Helper
not a paper statement. F1/F4 apply; values off this event are junk. -/
theorem iidCodes_ae_busemannSDPMeasurableVersion :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h)
          (busemannSDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP_existsUnique] with ω hω
  obtain ⟨h, X, hX, -⟩ := hω
  have heq : busemannSDPMeasurableVersion ω = X := by
    funext k
    exact busemannSDPMeasurableVersion_eq_of_data ω h X hX k
  exact ⟨h, heq.symm ▸ hX⟩

/-- Almost surely the representative is the unique boundary SDP Busemann
function for a hit witness. Helper for `prop:SDP-recursive-equation`
are junk. -/
theorem iidCodes_ae_busemannSDPMeasurableVersion_unique :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h)
          (busemannSDPMeasurableVersion ω) ∧
        (∀ X : ℤ → ℤ,
          IsBoundaryBusemannSDP (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
            X = busemannSDPMeasurableVersion ω) := by
  filter_upwards [iidCodes_ae_boundaryBusemannSDP_existsUnique] with ω hω
  obtain ⟨h, X, hX, huniq⟩ := hω
  have heq : busemannSDPMeasurableVersion ω = X := by
    funext k
    exact busemannSDPMeasurableVersion_eq_of_data ω h X hX k
  exact ⟨h, heq.symm ▸ hX, fun Y hY => (huniq Y hY).trans heq.symm⟩

private theorem busemannVersion_congr_positive {ω η : ℕ → Fin 3}
    (h : ∀ i, ω (i + 1) = η (i + 1)) :
    busemannSDPMeasurableVersion ω = busemannSDPMeasurableVersion η := by
  classical
  have htail : (fun i => ω (i + 1)) = (fun i => η (i + 1)) := funext h
  have hw : codeWalk ω = codeWalk η := by
    funext n
    simp only [codeWalk, h]
  have hfst (a : ℤ) : codeFstFirstHit a ω = codeFstFirstHit a η := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).1 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hsnd (a : ℤ) : codeSndFirstHit a ω = codeSndFirstHit a η := by
    let F (z : ℕ → ℤ × ℤ) : ℕ∞ :=
      if h : ∃ n, (z n).2 = a then (Nat.find h : ℕ∞) else ⊤
    exact congrArg F hw
  have hh : boundaryHitTimeTotal ω = boundaryHitTimeTotal η := by
    funext k
    simp only [boundaryHitTimeTotal, hfst, hsnd]
  have hid : busemannBoundaryIdTotal ω = busemannBoundaryIdTotal η := by
    funext k
    simp only [busemannBoundaryIdTotal, htail, hh]
  have hstage (n a b : ℕ) :
      busemannStageSdpCode ω n a b = busemannStageSdpCode η n a b := by
    exact congrArg (fun w : ℕ → Fin 3 => Int.ofNat
      ((DirectedDistances.sdp
        (⟨a⟩ : DirectedDistances.KMSW.StagePresentVertex w n) ⟨b⟩).toNat)) htail
  funext k
  simp only [busemannSDPMeasurableVersion, boundarySdpDifference, hid, hstage]

private theorem measurable_busemannVersion_process :
    Measurable busemannSDPMeasurableVersion :=
  measurable_pi_iff.mpr measurable_busemannSDPMeasurableVersion

/-- Resetting the dummy coordinate does not affect the shifted SDP representative.
Helper for `prop:SDP-recursive-equation`
representative values are junk. -/
theorem busemannSDPMeasurableVersion_shift_eq (ω : ℕ → Fin 3) :
    busemannSDPMeasurableVersion (fun i => ω (i + 1)) =
      busemannSDPMeasurableVersion (codeShift 1 ω) := by
  apply busemannVersion_congr_positive
  intro i
  simp only [codeShift, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ite_false, Nat.add_comm 1]

/-- The full shifted SDP process has the same law as the original representative.
Helper for `prop:SDP-recursive-equation`
representative values are junk. -/
theorem iidCodeMeasure_map_busemannSDPMeasurableVersion_shift :
    iidCodeMeasure.map (fun ω => busemannSDPMeasurableVersion (fun i => ω (i + 1))) =
      iidCodeMeasure.map busemannSDPMeasurableVersion := by
  simp_rw [busemannSDPMeasurableVersion_shift_eq]
  change iidCodeMeasure.map (busemannSDPMeasurableVersion ∘ codeShift 1) = _
  rw [← Measure.map_map measurable_busemannVersion_process (measurable_codeShift 1),
    map_codeShift]

private theorem indepFun_firstCode_codeShift_one :
    (fun ω : ℕ → Fin 3 => ω 1) ⟂ᵢ[iidCodeMeasure] codeShift 1 := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hA : MeasurableSet[codePast 1] ((fun ω : ℕ → Fin 3 => ω 1) ⁻¹' s) := by
    exact ⟨(fun q : Fin 1 → Fin 3 => q 0) ⁻¹' s,
      (measurable_pi_apply 0) hs, rfl⟩
  rw [iidCodeMeasure_inter_codeShift_preimage 1 hA ht]
  rw [← Measure.map_apply (measurable_codeShift 1) ht, map_codeShift]

/-- The first code step is independent of the entire shifted SDP process. This does
not assert independence of the Busemann increments.
Helper for `prop:SDP-recursive-equation`
representative values are junk. -/
theorem indepFun_firstCode_busemannSDPMeasurableVersion_shift :
    (fun ω : ℕ → Fin 3 => ω 1) ⟂ᵢ[iidCodeMeasure]
      (fun ω => busemannSDPMeasurableVersion (fun i => ω (i + 1))) := by
  simp_rw [busemannSDPMeasurableVersion_shift_eq]
  exact indepFun_firstCode_codeShift_one.comp measurable_id
    measurable_busemannVersion_process

end DirectedDistances.Recursive
