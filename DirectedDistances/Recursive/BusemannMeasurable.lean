module

public import DirectedDistances.KMSW.KMSWMeasurability
public import DirectedDistances.Recursive.CanonicalBusemann
public import DirectedDistances.Recursive.CanonicalBusemannMeasurable
import DirectedDistances.Recursive.BusemannCommonFarVertex
import DirectedDistances.KMSW.DirectedContainHat

/-! # A measurable representative of the boundary LDP Busemann function

Two successive eventual values, first over finite stages and then over the
right boundary, give a measurable code-space representative. Its meaning is
the almost-everywhere equality with `canonicalBusemannLDP` proved below.
These are helper declarations, not numbered paper statements. The same
hit-indexed carrier qualifications as in `CanonicalBusemann` apply. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver MeasureTheory Filter

private theorem measurable_select {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] (f : ι → Ω → β) (hf : ∀ i, Measurable (f i))
    (g : Ω → ι) (hg : Measurable g) : Measurable (fun ω => f (g ω) ω) := by
  have h : Measurable (fun p : Ω × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

/-- Totalized hit-indexed boundary allocation ID. Its agreement with the
boundary vertex is used only where hit witnesses exist. Helper for -/
@[expose] noncomputable def busemannBoundaryIdTotal (ω : ℕ → Fin 3) (k : ℤ) : ℕ :=
  let s := kmswStage (fun i => ω (i + 1)) (boundaryHitTimeTotal ω k).toNat
  s.west s.active

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

/-- Integer code of a stage supremum, with zero junk at bottom. This is
not a distance convention: identifications with distances below require
reachability and bounded path lengths. Helper for `thm-busemann` -/
@[expose] noncomputable def busemannStageLdpCode
    (ω : ℕ → Fin 3) (n a b : ℕ) : ℤ :=
  Int.ofNat ((ldpSup
    (⟨a⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b⟩).unbotD 0)

private theorem measurable_stageLdpCode (n : ℕ)
    (a b : (ℕ → Fin 3) → ℕ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => busemannStageLdpCode ω n (a ω) (b ω)) := by
  apply measurable_select
    (fun p : ℕ × ℕ => fun ω => busemannStageLdpCode ω n p.1 p.2)
    _ (fun ω => (a ω, b ω)) (ha.prodMk hb)
  intro p
  unfold busemannStageLdpCode
  exact measurable_stage_ldpSup_comp n p.1 p.2 (fun z => Int.ofNat (z.unbotD 0))

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

private theorem stageLdpCode_eventually_eq (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    {a b : PresentVertex (fun i => ω (i + 1))} (hr : Reachable a b) :
    ∀ᶠ n in atTop, busemannStageLdpCode ω n a.id b.id =
      (presentLdpFiniteNat hb hr : ℤ) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  obtain ⟨N, hN⟩ := path_in_late_stages p
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn
  have heq : ldpSup (⟨a.id⟩ : StagePresentVertex (fun i => ω (i + 1)) n) ⟨b.id⟩ =
      (p.length : WithBot ℕ) := by
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨q.length, ⟨q, rfl⟩, by rw [hq]⟩
    · rintro z ⟨l, ⟨r, rfl⟩, rfl⟩
      have hh := hp ((stageToLimit (fun i => ω (i + 1)) n).mapPath r)
      have hlen := stageToLimit_length (fun i => ω (i + 1)) n r
      have hh' : r.length ≤ p.length := hlen ▸ hh
      change (r.length : WithBot ℕ) ≤ (p.length : WithBot ℕ)
      exact (WithBot.coe_le_coe (α := ℕ) (a := r.length) (b := p.length)).mpr hh'
  rw [presentLdpFiniteNat_eq_length hb hr hp]
  unfold busemannStageLdpCode
  rw [heq]
  rfl

/-- The eventual finite-stage difference to boundary index `j`, with zero
junk if the stage differences do not stabilize. Only the proved reachable
case identifies this with a difference of finite distances. Helper for -/
@[expose] noncomputable def boundaryLdpDifference
    (ω : ℕ → Fin 3) (k : ℤ) (j : ℕ) : ℤ :=
  eventualIntValue 0 (fun n =>
    busemannStageLdpCode ω n (busemannBoundaryIdTotal ω k)
      (busemannBoundaryIdTotal ω (j : ℤ)) -
      busemannStageLdpCode ω n (busemannBoundaryIdTotal ω 0)
        (busemannBoundaryIdTotal ω (j : ℤ)))

/-- The finite-target eventual difference is measurable. Helper for -/
theorem measurable_boundaryLdpDifference (k : ℤ) (j : ℕ) :
    Measurable (fun ω => boundaryLdpDifference ω k j) := by
  exact measurable_eventualIntValue 0 _ (fun n =>
    (measurable_stageLdpCode n _ _ (measurable_boundaryIdTotal k)
      (measurable_boundaryIdTotal (j : ℤ))).sub
    (measurable_stageLdpCode n _ _ (measurable_boundaryIdTotal 0)
      (measurable_boundaryIdTotal (j : ℤ))))

private theorem boundaryLdpDifference_eq (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (k : ℤ) (j : ℕ)
    (hr0 : Reachable (boundaryPresentVertex _ h 0) (boundaryPresentVertex _ h (j : ℤ)))
    (hrk : Reachable (boundaryPresentVertex _ h k) (boundaryPresentVertex _ h (j : ℤ))) :
    boundaryLdpDifference ω k j =
      (presentLdpFiniteNat hb hrk : ℤ) - (presentLdpFiniteNat hb hr0 : ℤ) := by
  unfold boundaryLdpDifference
  simp only [boundaryIdTotal_eq ω h]
  apply eventualIntValue_eq
  filter_upwards [stageLdpCode_eventually_eq ω hb hrk,
    stageLdpCode_eventually_eq ω hb hr0] with n hk h0
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

/-- A measurable code-space version of the LDP Busemann function, obtained
by successive eventual values over stages and right-boundary indices. Its
representative characterization is `iidCodes_ae_busemannLDPMeasurableVersion_eq`.
a paper statement. Values away from the characterization event are junk. -/
@[expose] noncomputable def busemannLDPMeasurableVersion
    (ω : ℕ → Fin 3) (k : ℤ) : ℤ :=
  eventualIntValue 0 (fun j => boundaryLdpDifference ω k j)

/-- Each coordinate of the representative is measurable. Helper for -/
theorem measurable_busemannLDPMeasurableVersion (k : ℤ) :
    Measurable (fun ω => busemannLDPMeasurableVersion ω k) := by
  exact measurable_eventualIntValue 0 _ (measurable_boundaryLdpDifference k)

private theorem busemannLDPMeasurableVersion_eq_of_data (ω : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := fun i => ω (i + 1)))
    (h : BoundaryHitWitnesses (fun i => ω (i + 1)))
    (X : ℤ → ℤ) (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex _ h) X)
    (k : ℤ) : busemannLDPMeasurableVersion ω k = X k := by
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
  unfold busemannLDPMeasurableVersion
  apply eventualIntValue_eq
  refine eventually_atTop.mpr ⟨B + N, fun j hj => ?_⟩
  have hjB : B + (j - B) = j := by omega
  have heq := boundaryLdpDifference_eq ω hb h k (B + (j - B))
    (hr (j - B)).1 (hr (j - B)).2
  have hx := hN (j - B) (by omega)
  rw [hX.1, sub_zero] at hx
  exact (congrArg (boundaryLdpDifference ω k) hjB).symm.trans (heq.trans hx.symm)

/-- Almost surely the measurable representative equals the canonical
boundary LDP Busemann function simultaneously at every integer index.
This characterizes the helper representative using `thm-busemann` -/
theorem iidCodes_ae_busemannLDPMeasurableVersion_eq :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      busemannLDPMeasurableVersion ω = canonicalBusemannLDP ω := by
  filter_upwards [iidCodes_ae_existsUnique_eq_canonicalBusemannLDP] with ω hω
  obtain ⟨hfin, h, X, hX, -, hcanon⟩ := hω
  rw [← hcanon]
  funext k
  exact busemannLDPMeasurableVersion_eq_of_data ω
    (presentPathLengthsBounded_of_hfin _ hfin) h X hX k

end DirectedDistances.Recursive
