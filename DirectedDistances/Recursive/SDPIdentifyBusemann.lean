/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.InftyCutEntry
public import DirectedDistances.KMSW.InftyCutEastChain
public import DirectedDistances.KMSW.InftyCutWest
public import DirectedDistances.KMSW.SDPIdentifyBdy
public import DirectedDistances.KMSW.BusemannBoundaryM0
import DirectedDistances.KMSW.BoundaryAEExistence

/-! Supporting lemmas for paper labels `thm-busemann`, `thm-busemann-property` (see CORRESPONDENCE.md). -/













public section
namespace DirectedDistances.Recursive

open Quiver MeasureTheory
open DirectedDistances.KMSW
open DirectedDistances.RandomWalk

private theorem sdpIdentifyBusemann_R_unbounded {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) : ∀ a : ℤ, ∃ m, R w m ≤ a := by
  intro a
  obtain ⟨m, hm⟩ := h.rightHit (max 1 (-a)) (le_max_left _ _)
  refine ⟨m, ?_⟩
  have hk := le_max_right (1 : ℤ) (-a)
  omega

private theorem sdpIdentifyBusemann_edge_endpoints_mem_vertices
    {w : ℕ → Fin 3} {a b : PresentVertex w} (p : Path a b) {e : ℕ}
    (he : e ∈ pathEdgeList p) :
    (⟨edgeWest w e⟩ : PresentVertex w) ∈ p.vertices ∧
      (⟨edgeEast w e⟩ : PresentVertex w) ∈ p.vertices := by
  induction p with
  | nil => simp [pathEdgeList] at he
  | @cons b c p f ih =>
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hw, ht⟩ := ih he
      exact ⟨(Path.mem_vertices_cons p f).2 (Or.inl hw),
        (Path.mem_vertices_cons p f).2 (Or.inl ht)⟩
    · have hef : e = f.val := List.mem_singleton.mp he
      subst e
      have hw : (⟨edgeWest w f.val⟩ : PresentVertex w) = b := by
        cases b
        exact congrArg PresentVertex.mk f.property.2.1
      have ht : (⟨edgeEast w f.val⟩ : PresentVertex w) = c := by
        cases c
        exact congrArg PresentVertex.mk f.property.2.2
      rw [hw, ht]
      exact ⟨(Path.mem_vertices_cons p f).2 (Or.inl p.end_mem_vertices),
        (p.cons f).end_mem_vertices⟩

/-- Split a path at its first edge activated at or after `t`; the preceding
prefix consists entirely of earlier edges. -/
private theorem sdpIdentifyBusemann_split_first_late {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (t : ℕ) :
    (∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      actTime w e he < t) ∨
    ∃ (z z' : PresentVertex w) (q : Path a z) (f : z ⟶ z')
      (r : Path z' b),
      p = (q.cons f).comp r ∧
      (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
        actTime w e he < t) ∧
      t ≤ actTime w f.val f.property.1 := by
  induction p with
  | nil =>
    left
    intro e he
    simp [pathEdgeList] at he
  | @cons b c p f ih =>
    rcases ih with hp | ⟨z, z', q, g, r, hEq, hq, hgt⟩
    · by_cases hlate : t ≤ actTime w f.val f.property.1
      · right
        refine ⟨b, c, p, f, Path.nil, ?_, hp, hlate⟩
        simp
      · left
        intro e he heP
        simp only [pathEdgeList, List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact hp e he heP
        · have hef : e = f.val := he
          subst e
          exact Nat.lt_of_not_ge hlate
    · right
      refine ⟨z, z', q, g, r.cons f, ?_, hq, hgt⟩
      rw [hEq]
      simp only [Path.comp_cons]

private theorem sdpIdentifyBusemann_not_all_early {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (t : ℕ)
    (ha : a.id < (kmswStage w t).nextVertex)
    (hout : (kmswStage w t).nextVertex ≤ b.id) :
    ¬ ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      actTime w e he < t := by
  intro hearly
  cases p with
  | nil =>
    omega
  | @cons b' c p e =>
    have hmem : e.val ∈ pathEdgeList (p.cons e) := by
      simp [pathEdgeList]
    have hearly' := hearly e.val hmem e.property.1
    have healloc : e.val < (kmswStage w t).nextEdge := by
      rw [actTime_spec w e.val e.property.1]
      exact act_lt_nextEdge w hearly'.le
    have hend := (kmswStage_endpoints_lt_nextVertex w t e.val healloc).2
    have heast : edgeEast w e.val = b.id := e.property.2.2
    have hends := edge_endpoints_eq w healloc
    rw [hends.2, heast] at hend
    omega

private theorem sdpIdentifyBusemann_eta_prefix_length {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) (K : ℕ) (hK : 1 ≤ K) {z : ℕ}
    (hz : z = (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).east
          (act w (boundaryHitTime w h (-(K : ℤ)))) ∨
      ∃ e ∈ (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).UR,
        (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).west e = z ∨
          (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).east e = z) :
    ∃ q : Path (boundaryPresentVertex w h (-(K : ℤ))) ⟨z⟩,
      q.length ≤ (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).UR.length + 1 := by
  let t := boundaryHitTime w h (-(K : ℤ))
  obtain ⟨b, p, hp, _⟩ := cut_entry_eta_future_path w
    (sdpIdentifyBusemann_R_unbounded h) t
  have hroot : (kmswStage w t).west (act w t) = boundaryVertex w h (-(K : ℤ)) :=
    (leftHit_UL_singleton_and_west_endpoint w h (by omega : -(K : ℤ) ≤ -1)).2
  have hstart : (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w) =
      boundaryPresentVertex w h (-(K : ℤ)) := by
    exact congrArg PresentVertex.mk hroot
  have hzmem : (⟨z⟩ : PresentVertex w) ∈ p.vertices := by
    rcases hz with hz | ⟨e, he, hend⟩
    · have hmem : act w t ∈ pathEdgeList p := by rw [hp]; exact List.mem_cons_self
      have heast := (sdpIdentifyBusemann_edge_endpoints_mem_vertices p hmem).2
      have hends := edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl t))
      rw [← hends.2, ← hz] at heast
      exact heast
    · have hmem : e ∈ pathEdgeList p := by
        rw [hp]
        exact List.mem_cons_of_mem _ he
      have hends := edge_endpoints_eq w
        ((kmswStage_boundary_ids_lt_nextEdge w t).2 e (by
          simp only [List.mem_append]
          exact Or.inl (Or.inl (Or.inr he))))
      obtain ⟨hw, ht⟩ := sdpIdentifyBusemann_edge_endpoints_mem_vertices p hmem
      rcases hend with hwz | htz
      · rw [← hends.1, hwz] at hw
        exact hw
      · rw [← hends.2, htz] at ht
        exact ht
  obtain ⟨q, r, hqr⟩ := p.exists_eq_comp_of_mem_vertices hzmem
  have hlenP : p.length = (kmswStage w t).UR.length + 1 := by
    have hlen := congrArg List.length hp
    simpa only [pathEdgeList_length, List.length_cons] using hlen
  have hlen : p.length = q.length + r.length := by
    rw [hqr, Path.length_comp]
  have hprefix : ∃ q' : Path
      (⟨(kmswStage w t).west (act w t)⟩ : PresentVertex w) ⟨z⟩,
      q'.length ≤ (kmswStage w t).UR.length + 1 := ⟨q, by omega⟩
  rwa [hstart] at hprefix

/-- A shortest path from `x₀` to a vertex beyond the cutoff has a junction
that lies on `eta_k`; the initial segment from `x_{-k}` is a prefix of `eta_k`.
This is the path-level helper for the Busemann, triangle, and bound equations -/
private theorem sdpIdentifyBusemann_geodesic_cut {w : ℕ → Fin 3}
    (h : BoundaryHitWitnesses w) (K : ℕ) (hK : 1 ≤ K) {y : PresentVertex w}
    (hout : (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).nextVertex ≤ y.id)
    (hy0 : Reachable (boundaryPresentVertex w h 0) y) :
    ∃ z : PresentVertex w,
      ∃ q : Path (boundaryPresentVertex w h (-(K : ℤ))) z,
      ∃ r : Path z y,
        q.length ≤ (kmswStage w (boundaryHitTime w h (-(K : ℤ)))).UR.length + 1 ∧
        r.length ≤ (sdp (boundaryPresentVertex w h 0) y).toNat := by
  let t := boundaryHitTime w h (-(K : ℤ))
  obtain ⟨p, hpGeo⟩ := exists_length_eq_sdp hy0
  have hrootBound : 2 ≤ (kmswStage w t).nextVertex :=
    CutConverse.nextVertex_mono w (Nat.zero_le t)
  have ha : (boundaryPresentVertex w h 0).id < (kmswStage w t).nextVertex := by
    simp [boundaryPresentVertex, boundaryVertex_zero]
    omega
  have hnotEarly := sdpIdentifyBusemann_not_all_early p t ha hout
  obtain ⟨z, z', q, f, r, hpSplit, hqEarly, hft⟩ :=
    (sdpIdentifyBusemann_split_first_late p t).resolve_left hnotEarly
  have hrootPresent : EdgePresent w 0 := by
    refine ⟨0, ?_, ?_⟩
    · change 0 < 1
      omega
    · exact (boundaryVertex_root_edge w h).2.2.2
  have hrootTime : actTime w 0 hrootPresent = 0 := by
    apply (actTime_eq_iff w 0 hrootPresent 0).2
    rfl
  have hentry :
      (z.id = boundaryVertex w h (-(K : ℤ)) ∨
        let t := boundaryHitTime w h (-(K : ℤ))
        z.id = (kmswStage w t).east (act w t) ∨
          ∃ e ∈ (kmswStage w t).UR,
            (kmswStage w t).west e = z.id ∨ (kmswStage w t).east e = z.id) ∧
      ∃ qη : Path (boundaryPresentVertex w h (-(K : ℤ))) z,
        ∀ e ∈ pathEdgeList qη, ∀ he : EdgePresent w e,
          boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he := by
    cases q with
    | nil =>
      have hhit := boundaryHitTime_left_spec w h (by omega : -(K : ℤ) ≤ -1)
      have hshared := cut_entry_window_shared_endpoint_reachable w h K
        hrootPresent f.property.1 (by
          have htpos : 0 < t := by
            have hzero : L w 0 = 0 := by simp [L]
            by_contra hn
            have ht0 : t = 0 := Nat.eq_zero_of_not_pos hn
            change L w t = -(K : ℤ) at hhit
            rw [ht0, hzero] at hhit
            omega
          simpa [hrootTime] using htpos)
        hft (Or.inl (by
          have hends := edge_endpoints_eq w
            (show 0 < (kmswStage w 0).nextEdge from Nat.zero_lt_one)
          calc
            edgeWest w 0 = (kmswStage w 0).west 0 := hends.1.symm
            _ = boundaryVertex w h 0 := (boundaryVertex_root_edge w h).2.1
            _ = (boundaryPresentVertex w h 0).id := rfl)) f.property.2.1
      exact hshared
    | @cons a' b' q' e =>
      have heMem : e.val ∈ pathEdgeList (q'.cons e) :=
        List.mem_append_right _ (List.mem_singleton_self _)
      have het := hqEarly e.val heMem e.property.1
      have hshared := cut_entry_window_shared_endpoint_reachable w h K
        e.property.1 f.property.1 het hft (Or.inr e.property.2.2) f.property.2.1
      exact hshared
  have hqηExists : ∃ qη : Path (boundaryPresentVertex w h (-(K : ℤ))) z,
      qη.length ≤ (kmswStage w t).UR.length + 1 := by
    rcases hentry.1 with hz | hz
    · have hzEq : z = boundaryPresentVertex w h (-(K : ℤ)) :=
        congrArg PresentVertex.mk hz
      subst z
      exact ⟨Path.nil, Nat.zero_le _⟩
    · obtain ⟨qη', hqη'⟩ := sdpIdentifyBusemann_eta_prefix_length h K hK hz
      exact ⟨qη', by simpa [t] using hqη'⟩
  obtain ⟨qη, hqBound⟩ := hqηExists
  have hzmem : z ∈ p.vertices := by
    have hfmem : f.val ∈ pathEdgeList p := by
      rw [hpSplit, pathEdgeList_comp]
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_singleton_self _))
    have hwmem := (sdpIdentifyBusemann_edge_endpoints_mem_vertices p hfmem).1
    have hwest : (⟨edgeWest w f.val⟩ : PresentVertex w) = z :=
      congrArg PresentVertex.mk f.property.2.1
    rw [hwest] at hwmem
    exact hwmem
  obtain ⟨p₁, p₂, hpDecomp⟩ := p.exists_eq_comp_of_mem_vertices hzmem
  have hpLength : p.length = (sdp (boundaryPresentVertex w h 0) y).toNat := by
    simpa only [ENat.toNat_natCast] using congrArg ENat.toNat hpGeo
  have hp₂Bound : p₂.length ≤ (sdp (boundaryPresentVertex w h 0) y).toNat := by
    have hlen : p.length = p₁.length + p₂.length := by
      rw [hpDecomp, Path.length_comp]
    omega
  exact ⟨z, qη, p₂, hqBound, hp₂Bound⟩

/-- Deterministic half of `eqn-sdp-identify-busemann` and
boundary SDP Busemann function, the negative-index value is bounded by the
length of the realized `act :: UR` path at the first hit of `L=-k`; the final
`+1` is the active edge in that path. The proof uses a late-edge split through
`cut_entry_window_shared_endpoint_reachable`, without a planar-topology premise.
This statement is about the hit-indexed boundary; the paper's boundary
identification carries the F1/F4 caveats documented in the module header. -/
theorem boundaryBusemannSDP_neg_le_eta_length (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {X : ℤ → ℤ}
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    {k : ℕ} (hk : 1 ≤ k) :
    X (-(k : ℤ)) ≤
      ((kmswStage w (boundaryHitTime w h (-(k : ℤ)))).UR.length : ℤ) + 1 := by
  let xneg := boundaryPresentVertex w h (-(k : ℤ))
  let t := boundaryHitTime w h (-(k : ℤ))
  let S : Set ℕ := {l | boundaryVertex w h (l : ℤ) < (kmswStage w t).nextVertex}
  have hinj : Function.Injective (fun l : ℕ => boundaryVertex w h (l : ℤ)) := by
    intro a b hab
    exact Nat.cast_injective (boundaryVertex_injective w h hab)
  have hS : S.Finite := (Set.finite_Iio _).preimage hinj.injOn
  obtain ⟨M, hM⟩ := hS.bddAbove
  let ℓ := M + 1
  let y : ℕ → PresentVertex w := fun j =>
    boundaryPresentVertex w h ((ℓ + j : ℕ) : ℤ)
  have hyOutside (j : ℕ) : (kmswStage w t).nextVertex ≤ (y j).id := by
    have hnot : ℓ + j ∉ S := by
      intro hmem
      have hle : ℓ + j ≤ M := hM hmem
      change M + 1 + j ≤ M at hle
      omega
    dsimp [S, y, boundaryPresentVertex] at hnot ⊢
    omega
  have hyinj : Function.Injective y := by
    intro i j hij
    have hval : boundaryVertex w h ((ℓ + i : ℕ) : ℤ) =
        boundaryVertex w h ((ℓ + j : ℕ) : ℤ) := by
      exact congrArg PresentVertex.id hij
    have hNat : ℓ + i = ℓ + j := Nat.cast_injective
      (boundaryVertex_injective w h hval)
    exact Nat.add_left_cancel hNat
  have hyReach0 (j : ℕ) :
      Reachable (boundaryPresentVertex w h 0) (y j) := by
    apply boundaryVertex_nonneg_reachable w h (by omega)
    dsimp [y]
    omega
  have hyReachNeg (j : ℕ) : Reachable xneg (y j) := by
    obtain ⟨z, q, r, hq, _⟩ :=
      sdpIdentifyBusemann_geodesic_cut h k hk (hyOutside j) (hyReach0 j)
    exact ⟨q.comp r⟩
  have hyr : ∀ j, Reachable xneg (y j) ∧
      Reachable (boundaryPresentVertex w h 0) (y j) := by
    intro j
    exact ⟨hyReachNeg j, hyReach0 j⟩
  obtain ⟨N, hN⟩ := hX.2 (-(k : ℤ)) 0 y hyinj hyr
  obtain ⟨z, q, r, hq, hr⟩ :=
    sdpIdentifyBusemann_geodesic_cut h k hk (hyOutside N) (hyReach0 N)
  have hzr : Reachable z (y N) := ⟨r⟩
  have hdistZ : (sdp z (y N)).toNat ≤ r.length := by
    have hle := sdp_le_length r
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (present_sdp_ne_top hzr)
    rw [← hn] at hle
    have hnat : n ≤ r.length := by exact_mod_cast hle
    simpa only [← hn, ENat.toNat_natCast] using hnat
  have hdistZ0 : (sdp z (y N)).toNat ≤
      (sdp (boundaryPresentVertex w h 0) (y N)).toNat := by
    exact hdistZ.trans hr
  have hnegFin := present_sdp_ne_top (hyReachNeg N)
  have hzFin := present_sdp_ne_top hzr
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hnegFin
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hzFin
  have htri := sdp_triangle xneg z (y N)
  have hqSdp := sdp_le_length q
  have htri' : sdp xneg (y N) ≤ (q.length : ℕ∞) + sdp z (y N) := by
    exact htri.trans (add_le_add hqSdp le_rfl)
  rw [← ha, ← hc] at htri'
  have hNat : a ≤ q.length + c := by exact_mod_cast htri'
  have hcNat : (sdp z (y N)).toNat = c := by rw [← hc]; rfl
  rw [hcNat] at hdistZ0
  have hNat' : a ≤ q.length + (sdp (boundaryPresentVertex w h 0) (y N)).toNat :=
    hNat.trans (Nat.add_le_add_left hdistZ0 _)
  have hbus := hN N le_rfl
  have hdiff : X (-(k : ℤ)) = (a : ℤ) -
      ((sdp (boundaryPresentVertex w h 0) (y N)).toNat : ℤ) := by
    have ha' : (sdp xneg (y N)).toNat = a := by rw [← ha]; rfl
    rw [ha'] at hbus
    rw [hX.1] at hbus
    linarith
  have hboundInt : (a : ℤ) ≤
      (q.length : ℤ) + ((sdp (boundaryPresentVertex w h 0) (y N)).toNat : ℤ) := by
    exact_mod_cast hNat'
  have hqInt : (q.length : ℤ) ≤
      ((kmswStage w t).UR.length : ℤ) + 1 := by exact_mod_cast hq
  calc
    X (-(k : ℤ)) = (a : ℤ) -
        ((sdp (boundaryPresentVertex w h 0) (y N)).toNat : ℤ) := hdiff
    _ ≤ q.length := by linarith
    _ ≤ (kmswStage w t).UR.length + 1 := hqInt

/-- Probability bound in `eqn-sdp-identify-bound`
works for all `k≥1`, and with probability at least `1-δ` every SDP Busemann
function on the hit-indexed boundary satisfies `X(-k) ≤ 2Ak+1`. This combines
the deterministic eta bound with `iidCodeWalk_sdpIdentifyBdy`. It is the
Busemann-side input of `KappaExclusionAssembly`'s `hgeo`; transfer to the
manuscript theorem still has the F1/F4 caveats. The transfer
`Recursive/KappaHgeoTransfer.hgeo_of_linear_bound` requires the `ind`,
`stationary`, and `sym` items of `thm-busemann-property`. -/
theorem iidCodes_ae_boundaryBusemannSDP_linear_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 1 ≤ k →
      iidCodeMeasure.real
        {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
          ∀ X : ℤ → ℤ,
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
              (X (-(k : ℤ)) : ℝ) ≤ 2 * A * k + 1} ≥ 1 - δ := by
  obtain ⟨A, hA, hprob⟩ := iidCodeWalk_sdpIdentifyBdy δ hδ
  refine ⟨A, hA, ?_⟩
  intro k hk
  let E : Set (ℕ → Fin 3) := {ω | ∃ hcode : ∃ n : ℕ,
      L (fun i => ω (i + 1)) n = -(k : ℤ),
      ∃ z : PresentVertex (fun i => ω (i + 1)),
      ∃ p : Path
        (⟨(kmswStage (fun i => ω (i + 1)) (Nat.find hcode)).west
          (act (fun i => ω (i + 1)) (Nat.find hcode))⟩ :
            PresentVertex (fun i => ω (i + 1))) z,
        pathEdgeList p =
            act (fun i => ω (i + 1)) (Nat.find hcode) ::
              (kmswStage (fun i => ω (i + 1)) (Nat.find hcode)).UR ∧
          (p.length : ℝ) ≤ 2 * A * k + 1}
  let H : Set (ℕ → Fin 3) :=
    {ω | BoundaryHitWitnesses (fun i => ω (i + 1))}
  let T : Set (ℕ → Fin 3) :=
    {ω | ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ X : ℤ → ℤ,
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (i + 1)) h) X →
          (X (-(k : ℤ)) : ℝ) ≤ 2 * A * k + 1}
  have hHae : ∀ᵐ ω ∂iidCodeMeasure, ω ∈ H := by
    filter_upwards [iidCodes_ae_boundaryHitWitnesses] with ω hω
    exact hω
  have hHnull : iidCodeMeasure.real Hᶜ = 0 := by
    apply (measureReal_eq_zero_iff).2
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [Set.mem_compl_iff, not_not] using hHae
  have hsubset : E ⊆ T ∪ Hᶜ := by
    intro ω hω
    rcases hω with ⟨hcode, z, p, hp, hplen⟩
    by_cases hωH : ω ∈ H
    · left
      have hh : BoundaryHitWitnesses (fun i => ω (i + 1)) := hωH
      refine ⟨hh, ?_⟩
      intro X hX
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      have hleft := hh.leftHit (-(k : ℤ)) (by omega)
      have hfind : Nat.find hcode = Nat.find hleft := by
        apply Nat.find_congr'
        intro n
        rfl
      have htime : boundaryHitTime w hh (-(k : ℤ)) = Nat.find hcode := by
        have htime' : boundaryHitTime w hh (-(k : ℤ)) = Nat.find hleft := by
          unfold boundaryHitTime
          simp only [dite_eq_right (by omega : -(k : ℤ) ≠ 0),
            dite_eq_right (by omega : ¬ 0 < -(k : ℤ))]
        exact htime'.trans hfind.symm
      have hpathLen : p.length =
          (kmswStage w (boundaryHitTime w hh (-(k : ℤ)))).UR.length + 1 := by
        calc
          p.length = (kmswStage w (Nat.find hcode)).UR.length + 1 := by
            simpa only [pathEdgeList_length, List.length_cons] using
              congrArg List.length hp
          _ = (kmswStage w (boundaryHitTime w hh (-(k : ℤ)))).UR.length + 1 :=
            congrArg (fun n => (kmswStage w n).UR.length + 1) htime.symm
      have hpathLenReal : (p.length : ℝ) =
          ((kmswStage w (boundaryHitTime w hh (-(k : ℤ)))).UR.length : ℝ) + 1 := by
        exact_mod_cast hpathLen
      have hUR :
          ((kmswStage w (boundaryHitTime w hh (-(k : ℤ)))).UR.length : ℝ) + 1 ≤
            2 * A * k + 1 := by
        rw [← hpathLenReal]
        exact hplen
      have hdet := boundaryBusemannSDP_neg_le_eta_length w hh hX hk
      have hdetR : (X (-(k : ℤ)) : ℝ) ≤
          ((kmswStage w (boundaryHitTime w hh (-(k : ℤ)))).UR.length : ℝ) + 1 := by
        exact_mod_cast hdet
      exact hdetR.trans hUR
    · exact Or.inr hωH
  have hprobE : iidCodeMeasure.real E ≥ 1 - δ := by
    have h := hprob k hk
    change iidCodeMeasure.real
      {ω | ∃ hcode : ∃ n : ℕ,
        L (fun i => ω (i + 1)) n = -(k : ℤ),
        ∃ z : PresentVertex (fun i => ω (i + 1)),
        ∃ p : Path
          (⟨(kmswStage (fun i => ω (i + 1)) (Nat.find hcode)).west
            (act (fun i => ω (i + 1)) (Nat.find hcode))⟩ :
              PresentVertex (fun i => ω (i + 1))) z,
          pathEdgeList p =
              act (fun i => ω (i + 1)) (Nat.find hcode) ::
                (kmswStage (fun i => ω (i + 1)) (Nat.find hcode)).UR ∧
            (p.length : ℝ) ≤ 2 * A * k + 1} ≥ 1 - δ at h
    simpa only [E] using h
  calc
    1 - δ ≤ iidCodeMeasure.real E := hprobE
    _ ≤ iidCodeMeasure.real (T ∪ Hᶜ) := measureReal_mono hsubset
    _ ≤ iidCodeMeasure.real T + iidCodeMeasure.real Hᶜ := measureReal_union_le _ _
    _ = iidCodeMeasure.real T := by rw [hHnull, add_zero]

end DirectedDistances.Recursive
