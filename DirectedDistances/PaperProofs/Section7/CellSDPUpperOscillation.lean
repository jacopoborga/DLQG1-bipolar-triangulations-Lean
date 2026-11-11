module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperProps
import DirectedDistances.KMSW.ActiveTimeMonotone
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp
import DirectedDistances.KMSW.RawGeodesicAE
import DirectedDistances.KMSW.KMSWMeasurability

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver MeasureTheory ProbabilityTheory
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem oscillation_window_arrow_data (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex (fun i => w (n + i))} (e : a ⟶ b) :
    EdgePresent w (kmswWindowEdgeMapInf w n e.val) ∧
      edgeWest w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n a.id ∧
      edgeEast w (kmswWindowEdgeMapInf w n e.val) =
        kmswWindowVertexMapInf w n b.id := by
  obtain ⟨m, hm, hp⟩ := e.property.1
  have hr := kmswWindowPatchData_rel w n m
  have hg : kmswWindowEdgeMapInf w n e.val < (kmswStage w (n + m)).nextEdge := by
    rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.edge_bound e.val hm
  refine ⟨⟨n + m, hg, ?_⟩, ?_, ?_⟩
  · rw [kmswWindowEdgeMapInf_eq_stage w n m e.val hm]
    exact hr.present e.val hm hp
  · rw [← (edge_endpoints_eq w hg).1,
      kmswWindowEdgeMapInf_west w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).1, e.property.2.1]
  · rw [← (edge_endpoints_eq w hg).2,
      kmswWindowEdgeMapInf_east w n m e.val hm,
      (edge_endpoints_eq (fun i => w (n + i)) hm).2, e.property.2.2]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem oscillation_late_arrow (w : ℕ → Fin 3) (n : ℕ)
    {a b : PresentVertex w} (e : a ⟶ b)
    (ht : n ≤ actTime w e.val e.property.1) :
    ∃ f : ℕ, EdgePresent (fun i => w (n + i)) f ∧
      edgeWest w e.val =
        kmswWindowVertexMapInf w n (edgeWest (fun i => w (n + i)) f) ∧
      edgeEast w e.val =
        kmswWindowVertexMapInf w n (edgeEast (fun i => w (n + i)) f) := by
  let u := fun i => w (n + i)
  let t := actTime w e.val e.property.1
  let f := act u (t - n)
  have hf : EdgePresent u f := by
    refine ⟨t - n, act_lt_nextEdge _ le_rfl, ?_⟩
    apply (kmswStage_status u (t - n)).2.1
    obtain ⟨es, hes⟩ := kmswStage_UL_last u (t - n)
    rw [hes]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hmap : kmswWindowEdgeMapInf w n f = e.val := by
    rw [kmswWindowEdgeMapInf_eq_stage w n (t - n) f (act_lt_nextEdge _ le_rfl)]
    change (kmswWindowPatchData w n (t - n)).φ
      (kmswStage (fun i => w (n + i)) (t - n)).active = e.val
    rw [(kmswWindowPatchData_rel w n (t - n)).active]
    change act w (n + (t - n)) = e.val
    rw [Nat.add_sub_of_le ht]
    exact (actTime_spec w e.val e.property.1).symm
  let ef : (⟨edgeWest u f⟩ : PresentVertex u) ⟶ ⟨edgeEast u f⟩ :=
    ⟨f, hf, rfl, rfl⟩
  have hd := oscillation_window_arrow_data w n ef
  rw [hmap] at hd
  exact ⟨f, hf, hd.2⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
from a label in the finite upper-boundary range, with no larger length. -/
theorem cellSdpUpper_last_exit_suffix (w : ℕ → Fin 3) (n : ℕ)
    (hn : BoundaryHitWitnesses (fun i => w (n + i))) (k : ℤ)
    (hkL : -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k)
    (hkR : k ≤ ((kmswStage w n).UR.length : ℤ) + 1)
    {b : PresentVertex w}
    (p : Path (⟨kmswWindowVertexMapInf w n
      (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w) b) :
    b.id < (kmswStage w n).nextVertex ∨
      ∃ r : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ r ∧
        r ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
        ∃ v : ℕ, b.id = kmswWindowVertexMapInf w n v ∧
          ∃ q : Path (boundaryPresentVertex (fun i => w (n + i)) hn r)
            (⟨v⟩ : PresentVertex (fun i => w (n + i))), q.length ≤ p.length := by
  let u := fun i => w (n + i)
  induction p with
  | nil => exact Or.inr ⟨k, hkL, hkR, _, rfl, Path.nil, le_rfl⟩
  | @cons a b p e ih =>
    by_cases hb : b.id < (kmswStage w n).nextVertex
    · exact Or.inl hb
    right
    have ht : n ≤ actTime w e.val e.property.1 := by
      by_contra hnot
      have hlt : actTime w e.val e.property.1 ≤ n := by omega
      have ha := act_lt_nextEdge w hlt
      rw [← actTime_spec w e.val e.property.1] at ha
      have hbound := (kmswStage_endpoints_lt_nextVertex w n e.val ha).2
      rw [(edge_endpoints_eq w ha).2, e.property.2.2] at hbound
      exact hb hbound
    obtain ⟨f, hf, hfw, hfe⟩ := oscillation_late_arrow w n e ht
    have hprev : ∃ r : ℤ,
        -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ r ∧
        r ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
        ∃ v : ℕ, a.id = kmswWindowVertexMapInf w n v ∧
          ∃ q : Path (boundaryPresentVertex u hn r) (⟨v⟩ : PresentVertex u),
            q.length ≤ p.length := by
      rcases ih with ha | hs
      · have hfront := (kmswStage_act_endpoint_since w ht (Nat.lt_succ_self _)).1
        have halloc := act_lt_nextEdge w (Nat.le_refl (actTime w e.val e.property.1))
        rw [(edge_endpoints_eq w halloc).1, ← actTime_spec w e.val e.property.1,
          e.property.2.1] at hfront
        obtain ⟨g, hg, hga⟩ := hfront.resolve_right (by omega)
        obtain ⟨r, hrL, hrR, hra⟩ :=
          stage_upper_endpoint_future_boundary_bounded w n hn g a.id hg hga
        exact ⟨r, hrL, hrR, _, hra, Path.nil, Nat.zero_le _⟩
      · exact hs
    obtain ⟨r, hrL, hrR, v, hv, q, hq⟩ := hprev
    have hw : edgeWest u f = v := by
      apply kmswWindowVertexMapInf_injective w n
      exact hfw.symm.trans (e.property.2.1.trans hv)
    refine ⟨r, hrL, hrR, edgeEast u f, e.property.2.2.symm.trans hfe,
      q.cons ⟨f, hf, hw, rfl⟩, ?_⟩
    simp only [Path.length_cons]
    exact Nat.add_le_add_right hq 1

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
also controls all late terms for which the additional boundary start is reachable. -/
private theorem oscillation_eventual_difference {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (X : ℤ → ℤ) (hX : IsBoundaryBusemannSDP x X)
    (a b : ℤ) (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (hb : ∀ j, Reachable (x b) (y j)) :
    ∃ N : ℕ, ∀ j, N ≤ j → Reachable (x a) (y j) →
      X a - X b = ((sdp (x a) (y j)).toNat : ℤ) -
        ((sdp (x b) (y j)).toNat : ℤ) := by
  classical
  let S : Set ℕ := {j | Reachable (x a) (y j) ∧
    X a - X b ≠ ((sdp (x a) (y j)).toNat : ℤ) -
      ((sdp (x b) (y j)).toNat : ℤ)}
  have hS : S.Finite := by
    by_contra hnot
    let f : ℕ ↪ S := Set.Infinite.natEmbedding S hnot
    have hinj : Function.Injective (fun j => y (f j).val) := by
      intro i j hij
      apply f.injective
      apply Subtype.ext
      exact hy hij
    obtain ⟨N, hN⟩ := hX.2 b a (fun j => y (f j).val) hinj
      (fun j => ⟨hb _, (f j).property.1⟩)
    exact (f N).property.2 (hN N le_rfl)
  obtain ⟨N, hN⟩ := hS.bddAbove
  refine ⟨N + 1, fun j hj hr => ?_⟩
  by_contra hne
  have hle := hN (show j ∈ S from ⟨hr, hne⟩)
  omega

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
follows from the last exit, finite upper-boundary range and Busemann characterization. -/
theorem cellSdpUpper_boundaryOscillationConfinement_proved :
    cellSdpUpper_boundaryOscillationConfinement := by
  classical
  intro w n hn X hX M hM k hkL hkR y hy hreach
  let u := fun i => w (n + i)
  let a : ℤ := -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ)
  let b : ℤ := ((kmswStage w n).UR.length : ℤ) + 1
  have hevent (r : ℤ) := oscillation_eventual_difference
    (boundaryPresentVertex u hn) X hX r b y hy (fun j => (hreach j).2)
  choose N hN using hevent
  let K : ℕ := (Finset.Icc a b).sup N
  let img : ℕ → ℕ := fun j => kmswWindowVertexMapInf w n (y j).id
  have himg : Function.Injective img := by
    intro i j hij
    apply hy
    cases hi : y i
    cases hj : y j
    have hh := kmswWindowVertexMapInf_injective w n hij
    simp only [hi, hj] at hh
    cases hh
    rfl
  let S : Set ℕ := img ⁻¹' Set.range (fun i : Fin (kmswStage w n).nextVertex => i.val)
  have hS : S.Finite := (Set.finite_range _).preimage himg.injOn
  obtain ⟨T, hT⟩ := hS.bddAbove
  refine ⟨max K (T + 1), fun j hj => ?_⟩
  have hjK : K ≤ j := (Nat.le_max_left _ _).trans hj
  have hout : ¬ img j < (kmswStage w n).nextVertex := by
    intro hlt
    have hmem : j ∈ S := ⟨⟨img j, hlt⟩, rfl⟩
    have hle := hT hmem
    have := (Nat.le_max_right K (T + 1)).trans hj
    omega
  let xk := boundaryPresentVertex u hn k
  let v : PresentVertex w := ⟨img j⟩
  let z : PresentVertex w := ⟨kmswWindowVertexMapInf w n xk.id⟩
  have hfin := present_sdp_ne_top (hreach j).1
  have hle := cellSdpUpper_window_sdp_le w n xk (y j)
  have hr : Reachable z v := by
    by_contra hnot
    have htop := sdp_eq_top_iff_not_reachable.mpr hnot
    change sdp z v ≤ sdp xk (y j) at hle
    rw [htop] at hle
    exact hfin (top_le_iff.mp hle)
  obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
  obtain ⟨r, hrL, hrR, v', hv', q, hq⟩ :=
    (cellSdpUpper_last_exit_suffix w n hn k hkL hkR p).resolve_left hout
  have hvEq : v' = (y j).id :=
    kmswWindowVertexMapInf_injective w n hv'.symm
  subst v'
  change Path (boundaryPresentVertex u hn r) (y j) at q
  have hNj : N r ≤ j :=
    (Finset.le_sup (f := N) (Finset.mem_Icc.mpr ⟨hrL, hrR⟩)).trans hjK
  have hd := hN r j hNj ⟨q⟩
  have hosc : -M ≤ X r - X b := by
    simpa only [b, Nat.cast_add, Nat.cast_one] using (abs_le.mp (hM r hrL hrR)).1
  have hqle : (sdp (boundaryPresentVertex u hn r) (y j)).toNat ≤ q.length := by
    have hh := ENat.toNat_le_toNat (sdp_le_length q) (by simp)
    simpa only [ENat.toNat_natCast] using hh
  have hpNat : (sdp z v).toNat = p.length := by
    rw [← hp, ENat.toNat_natCast]
  change ((sdp (boundaryPresentVertex u hn b) (y j)).toNat : ℤ) - M ≤
    ((sdp z v).toNat : ℤ)
  rw [hpNat]
  have hlen : (q.length : ℤ) ≤ p.length := by exact_mod_cast hq
  have hqInt : ((sdp (boundaryPresentVertex u hn r) (y j)).toNat : ℤ) ≤
      q.length := by exact_mod_cast hqle
  linarith only [hd, hosc, hlen, hqInt]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result. -/
private theorem oscillation_shifted_tail_eq (ω : ℕ → Fin 3) (n : ℕ) :
    (fun i => (codeShift n ω) (i + 1)) = fun i => ω (n + i + 1) := by
  funext i
  simp only [codeShift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_assoc]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
characterization. -/
private theorem oscillation_ae_shifted_busemann :
    ∀ᵐ ω ∂iidCodeMeasure, ∀ n : ℕ,
      ∃ hn : BoundaryHitWitnesses (fun i => ω (n + i + 1)),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => ω (n + i + 1)) hn)
          (busemannSDPMeasurableVersion (codeShift n ω)) := by
  rw [ae_all_iff]
  intro n
  have hmap : ∀ᵐ η ∂iidCodeMeasure.map (codeShift n),
      ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
        IsBoundaryBusemannSDP
          (boundaryPresentVertex (fun i => η (i + 1)) h)
          (busemannSDPMeasurableVersion η) := by
    simpa only [map_codeShift] using
      (iidCodes_ae_busemannSDPMeasurableVersion :
        ∀ᵐ η ∂iidCodeMeasure,
          ∃ h : BoundaryHitWitnesses (fun i => η (i + 1)),
            IsBoundaryBusemannSDP
              (boundaryPresentVertex (fun i => η (i + 1)) h)
              (busemannSDPMeasurableVersion η))
  have hshift := (Measure.tendsto_ae_map
    (measurable_codeShift n).aemeasurable).eventually hmap
  filter_upwards [hshift] with ω hω
  rw [oscillation_shifted_tail_eq ω n] at hω
  exact hω

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
simultaneously almost surely. -/
theorem cellSdpUpper_first_bullet_oscillation_ae :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
        ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)),
          ∀ M0 Mn : ℤ,
            (∀ ℓ : ℤ,
              -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
              ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
              |busemannSDPMeasurableVersion ω ℓ -
                busemannSDPMeasurableVersion ω
                  ((kmswStage w n).LR.length : ℤ)| ≤ M0) →
            (∀ k : ℤ,
              -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k →
              k ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
              |busemannSDPMeasurableVersion (codeShift n ω) k -
                busemannSDPMeasurableVersion (codeShift n ω)
                  (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)| ≤ Mn) →
            ∀ ℓ : ℤ,
              -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
              ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
              boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex →
              ∃ k : ℤ,
                -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
                k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
                sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
                  ⟨kmswWindowVertexMapInf w n
                    (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
                  (((2 * M0 + 2 * Mn).toNat : ℕ) : ℕ∞) := by
  filter_upwards [iidCodes_ae_busemannSDPMeasurableVersion,
    oscillation_ae_shifted_busemann,
    iidCodes_ae_boundary_infinite_extremal, cell_sdp_separator_targets] with
    ω hbase hshift hgeo hseparator
  dsimp only at hseparator
  intro w n h0 hn M0 Mn hM0 hMn ℓ hℓL hℓR hℓStage
  obtain ⟨hbaseWitness, hbaseX⟩ := hbase
  have hX : IsBoundaryBusemannSDP (boundaryPresentVertex _ h0)
      (busemannSDPMeasurableVersion ω) := by
    simpa using hbaseX
  obtain ⟨hnWitness, hshiftX⟩ := hshift n
  have hXn : IsBoundaryBusemannSDP
      (boundaryPresentVertex (fun i => w (n + i)) hn)
      (busemannSDPMeasurableVersion (codeShift n ω)) := by
    simpa [w] using hshiftX
  obtain ⟨P, hP⟩ := (hgeo h0 ℓ).2
  let hTargets := hseparator n h0 hn ℓ
  exact cellSdpUpper_first_bullet_of_boundaryOscillation
    cellSdpUpper_boundaryOscillationConfinement_proved w n h0 hn
    (busemannSDPMeasurableVersion ω)
    (busemannSDPMeasurableVersion (codeShift n ω)) M0 Mn hX hXn hM0 hMn
    ℓ ⟨hℓL, hℓR⟩ hℓStage P hP hTargets

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
floor. -/
private theorem oscillation_int_abs_le_natFloor {z : ℤ} {q : ℝ} (hq : 0 ≤ q)
    (hz : |(z : ℝ)| ≤ q) : |z| ≤ (⌊q⌋₊ : ℤ) := by
  have hEq : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hnat : z.natAbs ≤ ⌊q⌋₊ := by
    apply (Nat.le_floor_iff hq).2
    rw [hEq]
    exact hz
  have hnatInt : (z.natAbs : ℤ) ≤ (⌊q⌋₊ : ℤ) := by
    exact_mod_cast hnat
  simpa only [Int.natCast_natAbs] using hnatInt

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
surely. -/
private theorem oscillation_ae_shifted_hits :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ n : ℕ, ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)), hn = hn := by
  filter_upwards [iidCodes_ae_uibotBoundary_allTimes] with ω hω
  dsimp only
  intro n
  have h := hω n
  dsimp only at h
  rcases h with ⟨⟨_, _hn, _⟩, _, _⟩
  exact ⟨by simpa [Nat.add_assoc] using _hn, rfl⟩

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
probability bound with no open premise. -/
theorem cellSdpUpper_first_bullet_prob_corrected :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
            -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
            ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
              ∃ k : ℤ,
                -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
                k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
                sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
                  ⟨kmswWindowVertexMapInf w n
                    (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
                    (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)} := by
  classical
  intro δ hδ
  obtain ⟨C, hC, hgood⟩ := cell_sdp_bdy_good_event_sdpCode δ hδ
  let A₀ : ℝ := max 2 (2 * C)
  have hA₀ : 1 < A₀ := by
    dsimp [A₀]
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  have hAhigh : C ≤ A / 2 := by
    dsimp [A₀] at hA
    have htwo : 2 * C ≤ A := (le_max_right 2 (2 * C)).trans hA
    linarith
  have hApos : 0 < A := by linarith [hC, hAhigh]
  let B : ℝ := A / 2
  let q : ℝ := A / 4 * (n : ℝ) ^ (3 / 8 : ℝ)
  let M : ℤ := (⌊q⌋₊ : ℕ)
  let G : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    let K := B * Real.sqrt (n : ℝ)
    let σ₀ := ((kmswStage w n).LR.length : ℤ)
    let σₙ := ((kmswStage w n).UR.length : ℤ) + 1
    ((kmswStage w n).LR.length : ℝ) ≤ K ∧
      ((kmswStage w n).UR.length : ℝ) + 1 ≤ K ∧
      ((kmswStage w n).LL.length : ℝ) ≤ K ∧
      (((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ K ∧
      (∀ ℓ : ℤ, |(ℓ : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion ω ℓ : ℝ) -
          (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤
            B * (n : ℝ) ^ (3 / 8 : ℝ) / 2) ∧
      (∀ k : ℤ, |(k : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion (codeShift n ω) k : ℝ) -
          (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤
            B * (n : ℝ) ^ (3 / 8 : ℝ) / 2)}
  have hG := hgood B hAhigh n hn
  have hprobG : 1 - δ ≤ iidCodeMeasure.real G := by
    simpa [G, B] using hG
  let T : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
      -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
      ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
        ∃ k : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
          k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
          sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
            ⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)}
  have hset : G ∩ T =ᵐ[iidCodeMeasure] G := by
    filter_upwards [oscillation_ae_shifted_hits,
      cellSdpUpper_first_bullet_oscillation_ae] with ω hb ha
    apply propext
    simp only [Set.mem_inter_iff]
    constructor
    · intro h
      exact h.1
    · intro hGω
      refine ⟨hGω, ?_⟩
      let w := fun i => ω (i + 1)
      change ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
        -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
        ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
        ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
          ∃ k : ℤ,
            -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
            k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
            sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
              ⟨kmswWindowVertexMapInf w n
                (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)
      dsimp [G, B] at hGω
      intro h0 ℓ hℓL hℓR
      obtain ⟨hn, _⟩ := hb n
      have hstage := boundaryVertex_lt_stage_of_lowerRange w n h0 ℓ
        ⟨hℓL, hℓR⟩
      have hKnonneg : 0 ≤ B * Real.sqrt (n : ℝ) := by
        apply mul_nonneg (by dsimp [B]; linarith) (Real.sqrt_nonneg _)
      have hqnonneg : 0 ≤ q := by
        dsimp [q]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      let σ₀ : ℤ := ((kmswStage w n).LR.length : ℤ)
      let σₙ : ℤ := ((kmswStage w n).UR.length : ℤ) + 1
      have hM0 : ∀ r : ℤ,
          -((kmswStage w n).LL.length : ℤ) ≤ r →
          r ≤ ((kmswStage w n).LR.length : ℤ) →
          |busemannSDPMeasurableVersion ω r -
            busemannSDPMeasurableVersion ω σ₀| ≤ M := by
        intro r hrL hrR
        have hrAbs : |(r : ℝ)| ≤ (A / 2) * Real.sqrt (n : ℝ) := by
          have hlow : -((kmswStage w n).LL.length : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast hrL
          have hupp : (r : ℝ) ≤ (kmswStage w n).LR.length := by
            exact_mod_cast hrR
          have hll := hGω.2.2.1
          have hlr := hGω.1
          rw [abs_le]
          constructor <;> nlinarith [hKnonneg]
        have hreal := hGω.2.2.2.2.1 r hrAbs
        have hrealq : |(busemannSDPMeasurableVersion ω r : ℝ) -
            (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤ q := by
          calc
            _ ≤ B * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by simpa [σ₀] using hreal
            _ = q := by dsimp [q, B]; ring
        have hcast' :
            |((busemannSDPMeasurableVersion ω r -
              busemannSDPMeasurableVersion ω σ₀ : ℤ) : ℝ)| ≤ q := by
          simpa only [Int.cast_sub] using hrealq
        simpa [M] using oscillation_int_abs_le_natFloor hqnonneg hcast'
      have hMn : ∀ r : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ r →
          r ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
          |busemannSDPMeasurableVersion (codeShift n ω) r -
            busemannSDPMeasurableVersion (codeShift n ω) σₙ| ≤ M := by
        intro r hrL hrR
        have hrAbs : |(r : ℝ)| ≤ (A / 2) * Real.sqrt (n : ℝ) := by
          have hlow :
              -(((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast hrL
          have hupp : (r : ℝ) ≤ (kmswStage w n).UR.length + 1 := by
            exact_mod_cast hrR
          have hul := hGω.2.2.2.1
          have hur := hGω.2.1
          rw [abs_le]
          constructor <;> nlinarith [hKnonneg]
        have hreal := hGω.2.2.2.2.2 r hrAbs
        have hrealq : |(busemannSDPMeasurableVersion (codeShift n ω) r : ℝ) -
            (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤ q := by
          calc
            _ ≤ B * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by
              simpa [σₙ, Nat.cast_add] using hreal
            _ = q := by dsimp [q, B]; ring
        have hcast' :
            |((busemannSDPMeasurableVersion (codeShift n ω) r -
              busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℤ) : ℝ)| ≤ q := by
          simpa only [Int.cast_sub] using hrealq
        simpa [M] using oscillation_int_abs_le_natFloor hqnonneg hcast'
      obtain ⟨k, hkL, hkR, hdist⟩ := ha n h0 hn M M hM0 hMn ℓ
        hℓL hℓR hstage
      have hMle : (M : ℝ) ≤ q := by
        simpa [M] using (Nat.floor_le hqnonneg)
      have htotal : 4 * (M : ℝ) ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) := by
        dsimp [q] at hMle
        nlinarith [hMle]
      have htotalNat : (4 * M).toNat ≤
          ⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ := by
        apply (Nat.le_floor_iff (by positivity :
          0 ≤ A * (n : ℝ) ^ (3 / 8 : ℝ))).2
        have hcastM : ((4 * M).toNat : ℝ) = 4 * (M : ℝ) := by
          rw [← Int.cast_natCast,
            Int.toNat_of_nonneg (by omega : 0 ≤ 4 * M)]
          norm_cast
        rw [hcastM]
        exact htotal
      have hdist' :
          sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
            ⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
            ((4 * M).toNat : ℕ∞) := by
        have heq : 2 * M + 2 * M = 4 * M := by ring
        simpa [heq] using hdist
      refine ⟨hn, k, hkL, hkR, ?_⟩
      exact hdist'.trans (by exact_mod_cast htotalNat)
  have hmeas : iidCodeMeasure.real (G ∩ T) = iidCodeMeasure.real G :=
    measureReal_congr hset
  calc
    1 - δ ≤ iidCodeMeasure.real G := hprobG
    _ = iidCodeMeasure.real (G ∩ T) := hmeas.symm
    _ ≤ iidCodeMeasure.real T := measureReal_mono Set.inter_subset_right

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
distances. -/
private theorem oscillation_stage_sdp_congr {w w' : ℕ → Fin 3} {n : ℕ}
    (h : kmswStage w n = kmswStage w' n) (a b : ℕ) :
    sdp (⟨a⟩ : StagePresentVertex w n) ⟨b⟩ =
      sdp (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩ := by
  let F : Prefunctor (StagePresentVertex w n) (StagePresentVertex w' n) :=
    { obj := fun v => ⟨v.id⟩
      map := fun e => ⟨e.val, by simpa only [h] using e.property⟩ }
  let G : Prefunctor (StagePresentVertex w' n) (StagePresentVertex w n) :=
    { obj := fun v => ⟨v.id⟩
      map := fun e => ⟨e.val, by simpa only [h] using e.property⟩ }
  have hF {u v : StagePresentVertex w n} (p : Path u v) :
      (F.mapPath p).length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  have hG {u v : StagePresentVertex w' n} (p : Path u v) :
      (G.mapPath p).length = p.length := by
    induction p with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  apply le_antisymm
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w' n) ⟨b⟩, (p.length : ℕ∞)
    exact le_iInf fun p => (sdp_le_length (G.mapPath p)).trans_eq (by rw [hG])
  · change _ ≤ ⨅ p : Path (⟨a⟩ : StagePresentVertex w n) ⟨b⟩, (p.length : ℕ∞)
    exact le_iInf fun p => (sdp_le_length (F.mapPath p)).trans_eq (by rw [hF])

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
prefix. -/
private theorem oscillation_measurable_endpoint_event (n : ℕ) (t : ℕ∞) :
    MeasurableSet {ω : ℕ → Fin 3 |
      let w := fun i => ω (i + 1)
      ∀ x : ℕ,
        (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
          (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
        ∃ y : ℕ,
          (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
            (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
          sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤ t} := by
  refine measurableSet_of_factors_prefix (n + 1) _ ?_
  intro ω ω' h
  have hs := kmswStage_shift_congr (n := n)
    (fun i _ hi => h i (by omega : i < n + 1))
  dsimp only
  simp_rw [oscillation_stage_sdp_congr hs]
  rw [hs]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
lower-boundary endpoint. -/
theorem cellSdpUpper_first_endpoint_prob_corrected :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          ∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)} := by
  intro δ hδ
  obtain ⟨A₀, hA₀, hprob⟩ := cellSdpUpper_first_bullet_prob_corrected δ hδ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  refine (hprob A hA n hn).trans (ENNReal.toReal_mono (by finiteness) (measure_mono_ae ?_))
  filter_upwards [cellSdpUpper_boundaryLabelIdentification_proved, iidCodes_ae_boundaryHitWitnesses,
    iidCodes_ae_uibotBoundary_allTimes] with ω hl h0 hf
  intro hfirst
  dsimp only at hl hfirst ⊢
  obtain ⟨⟨_, hn', _⟩, _, _⟩ := hf n
  have hn'' : BoundaryHitWitnesses (fun i => ω (n + i + 1)) := by
    simpa only [Nat.add_assoc] using hn'
  intro x hx
  obtain ⟨ℓ, hℓL, hℓR, hℓx⟩ := (hl n h0 hn'').1 x hx
  obtain ⟨hnw, k, hkL, hkR, hd⟩ := hfirst h0 ℓ hℓL hℓR
  refine ⟨kmswWindowVertexMapInf (fun i => ω (i + 1)) n
    (boundaryVertex (fun i => ω (n + i + 1)) hnw k),
    (hl n h0 hnw).2 k hkL hkR, ?_⟩
  simpa only [hℓx] using hd

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
constants uniform in every positive size. -/
@[expose] def cellSdpUpperConclusion : Prop :=
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          (∀ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
            ∃ y : ℕ,
              (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
                (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)) ∧
          (∀ y : ℕ,
            (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
              (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
            ∃ x : ℕ,
              (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
                (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
              sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
                (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞))}

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
Each original upper endpoint has a reversed lower endpoint whose distances to reversed
upper endpoints bound distances from corresponding original lower endpoints. Only these
endpoint pairs are needed; this definition supplies no proof of their transport. -/
@[expose] def cellSdpUpper_reversalEndpointTransport : Prop :=
  ∀ n : ℕ, ∀ ω : ℕ → Fin 3,
    let w := fun i => ω (i + 1)
    let wr := fun i => codeReversal n ω (i + 1)
    ∀ y : ℕ,
      (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
        (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) →
      ∃ yr : ℕ,
        (∃ e ∈ (kmswStage wr n).LL ++ (kmswStage wr n).LR,
          (kmswStage wr n).west e = yr ∨ (kmswStage wr n).east e = yr) ∧
        ∀ xr : ℕ,
          (∃ e ∈ (kmswStage wr n).UL ++ (kmswStage wr n).UR,
            (kmswStage wr n).west e = xr ∨ (kmswStage wr n).east e = xr) →
          ∃ x : ℕ,
            (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
              (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) ∧
            sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤
              sdp (⟨yr⟩ : StagePresentVertex wr n) ⟨xr⟩



theorem cellSdpUpper_reversalEndpointTransport_of_boundaryDistanceTransport
    (hreverse : cellSdpUpper_reversalBoundaryDistanceTransport) :
    cellSdpUpper_reversalEndpointTransport := by
  intro n ω
  dsimp only
  intro y hy
  obtain ⟨f, hfL, hfU, hdist⟩ := hreverse n ω
  refine ⟨f y, hfL y hy, fun xr hxr => ⟨f.symm xr, hfU xr hxr, ?_⟩⟩
  rw [hdist, f.apply_symm_apply]

/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
conditional only on the endpoint-only reversal obligation. -/
theorem cell_sdp_upper_corrected
    (hreverse : cellSdpUpper_reversalEndpointTransport) :
    cellSdpUpperConclusion := by
  intro δ hδ
  obtain ⟨A₀, hA₀, hprob⟩ :=
    cellSdpUpper_first_endpoint_prob_corrected (δ / 2) (by linarith)
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  let t : ℕ∞ := (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)
  let E : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    ∀ x : ℕ,
      (∃ e ∈ (kmswStage w n).LL ++ (kmswStage w n).LR,
        (kmswStage w n).west e = x ∨ (kmswStage w n).east e = x) →
      ∃ y : ℕ,
        (∃ e ∈ (kmswStage w n).UL ++ (kmswStage w n).UR,
          (kmswStage w n).west e = y ∨ (kmswStage w n).east e = y) ∧
        sdp (⟨x⟩ : StagePresentVertex w n) ⟨y⟩ ≤ t}
  let R := codeReversal n ⁻¹' E
  have hE : MeasurableSet E := oscillation_measurable_endpoint_event n t
  have hR : MeasurableSet R := hE.preimage (measurePreserving_codeReversal n).measurable
  have hER : iidCodeMeasure.real R = iidCodeMeasure.real E := by
    change (iidCodeMeasure R).toReal = (iidCodeMeasure E).toReal
    congr 1
    exact (measurePreserving_codeReversal n).measure_preimage hE.nullMeasurableSet
  have hpE : 1 - δ / 2 ≤ iidCodeMeasure.real E := hprob A hA n hn
  have hpR : 1 - δ / 2 ≤ iidCodeMeasure.real R := by rw [hER]; exact hpE
  have hsum := measureReal_union_add_inter (μ := iidCodeMeasure) (s := E) hR
  have hu : iidCodeMeasure.real (E ∪ R) ≤ 1 := measureReal_le_one
  have hp : 1 - δ ≤ iidCodeMeasure.real (E ∩ R) := by
    linarith only [hsum, hu, hpE, hpR]
  refine hp.trans (measureReal_mono ?_)
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro y hy
  obtain ⟨yr, hyr, htransport⟩ := hreverse n ω y hy
  obtain ⟨xr, hxr, hd⟩ := hω.2 yr hyr
  obtain ⟨x, hx, hdist⟩ := htransport xr hxr
  exact ⟨x, hx, hdist.trans hd⟩


/-- Helper (code level, SDP) toward Lemma 7.8 (lem-cell-sdp-upper); not a paper result.
reversal obligation; oscillation confinement and both probability inputs are proved. -/
theorem cell_sdp_upper_corrected_of_boundaryDistanceTransport
    (hreverse : cellSdpUpper_reversalBoundaryDistanceTransport) :
    cellSdpUpperConclusion :=
  cell_sdp_upper_corrected
    (cellSdpUpper_reversalEndpointTransport_of_boundaryDistanceTransport hreverse)

end DirectedDistances.PaperProofs.Section7
