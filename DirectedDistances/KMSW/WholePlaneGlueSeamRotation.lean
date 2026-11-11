module

public import DirectedDistances.KMSW.WholePlaneGlueSeamMerge
public import DirectedDistances.PlanarMap.CcwSectorMerge

public section
namespace DirectedDistances.KMSW.WholePlaneGlueSeamRotation

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open WholePlaneGlueSeamStar WholePlaneGlueSeamMerge WholePlaneGlueSeamSectors

noncomputable section

variable (W : ℤ → Fin 3)
  (h0 : BoundaryHitWitnesses (shiftedStream W 0))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (H : WholePlaneRotationHypothesis W)
  (k : ℤ)

local notation "w0" => shiftedStream W 0
local notation "wp" => kmswPastCode W
local notation "rot0" => kmswInfRot w0 ((And.left H) 0)
local notation "rotp" => kmswInfRot wp (past_finiteIncidence W H)
local notation "vert0" => kmswLimitDartVertex w0
local notation "vertp" => kmswLimitDartVertex wp
local notation "P0" => monotoneFamilyDrawing w0 ((And.left H) 0)
  (monotone_family_all w0)
local notation "Pt" => pastDrawing W h0 hp H
local notation "f0" => seamFun w0 h0 ((And.left H) 0)
local notation "x0" => seamX w0 h0 ((And.left H) 0) k





private theorem dart_injective : Function.Injective (wholePlaneDartι W 0) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ heq
  change (wholePlaneEdgeι W 0 e, b) = (wholePlaneEdgeι W 0 f, c) at heq
  exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst heq))
    (show b = c from congrArg Prod.snd heq)





private theorem successor_upper (d : ℕ × Bool)
    (hv : vert0 d = boundaryVertex w0 h0 k) :
    CcwSuccessor (U W h0 k) (dir W h0 hp H)
      (wholePlaneDartι W 0 d) (wholePlaneDartι W 0 (rot0 d)) := by
  have hs := (P0).rotation_agreement d
  rw [hv] at hs
  rcases hs with ⟨hfin, hd, hr, hcase⟩
  refine ⟨hfin.image _, ⟨d, hd, rfl⟩, ⟨_, hr, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · left
    refine ⟨congrArg (wholePlaneDartι W 0) heq, ?_⟩
    change wholePlaneDartι W 0 '' _ = _
    rw [hsingle, Set.image_singleton]
    rfl
  · right
    refine ⟨fun heq => hne (dart_injective W heq), ?_⟩
    rintro E ⟨e, he, rfl⟩ hne'
    have he' : e ≠ d := fun heq => hne' (congrArg (wholePlaneDartι W 0) heq)
    simpa only [dir, gluedArc_runZero] using hmin e he he'





private theorem upper_successor_ne_right (D E : WholePlaneDart W)
    (hD : D ∈ A W h0 k ∪ {dR W h0 k})
    (hs : CcwSuccessor (U W h0 k) (dir W h0 hp H) D E) : E ≠ dR W h0 k := by
  have hm := seam_mem W h0 hp k
  have hR : dR W h0 k ∈ U W h0 k := (hm (by simp)).1
  have hL : dL W h0 k ∈ U W h0 k := (hm (by simp)).1
  have hRL := seam_ne W h0 k
  have hnot : U W h0 k ≠ {D} := by
    intro he
    have hr : dR W h0 k = D := by simpa only [he, mem_singleton_iff] using hR
    have hl : dL W h0 k = D := by simpa only [he, mem_singleton_iff] using hL
    exact hRL (hr.trans hl.symm)
  have hmin := hs.2.2.2.resolve_left (fun h => hnot h.2)
  intro he
  rw [he] at hmin
  rcases hD with ha | hr
  · have hLD : dL W h0 k ≠ D := by
      intro hd
      exact ha.2 (by simp only [← hd, mem_insert_iff, mem_singleton_iff, or_true])
    have hRD : dR W h0 k ≠ D := by
      intro hd
      exact ha.2 (by simp only [← hd, mem_insert_iff, true_or])
    have hRs : dR W h0 k ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inl hR
    have hLs : dL W h0 k ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inl hL
    have hDs : D ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inl ha.1
    have hargRL := harg W h0 hp H k _ _ hRs hLs hRL
    have hargRD := harg W h0 hp H k _ _ hRs hDs hRD
    have hbound : ccwTurn (dir W h0 hp H (dR W h0 k))
        (dir W h0 hp H (dL W h0 k)) < 2 * Real.pi :=
      lt_of_le_of_ne (ccwTurn_le_two_pi _ _)
        (fun heq => hargRL ((ccwTurn_eq_two_pi_iff _ _).mp heq))
    have hc := ccwTurn_comp_add (hsectorA W h0 hp H k D ha).2
    have hr := ccwTurn_add_reverse _ _ hargRD
    have hle := hmin.2 _ hL hLD
    linarith only [hc, hr, hle, hbound]
  · exact hmin.1 (Set.mem_singleton_iff.mp hr).symm





theorem rotation_agreement_seam_upper (D : WholePlaneDart W)
    (hD : D ∈ A W h0 k ∪ {dR W h0 k}) :
    CcwSuccessor (S W h0 k) (dir W h0 hp H) D (wholePlaneRotation W H D) := by
  have hDU : D ∈ U W h0 k := by
    rw [hU W h0 hp k]
    rcases hD with ha | hr
    · exact Or.inl ha
    · exact Or.inr (by simp only [mem_singleton_iff] at hr; simp only [hr,
        mem_insert_iff, true_or])
  obtain ⟨d, hv, rfl⟩ := hDU
  have hu := successor_upper W h0 hp H k d hv
  have hn := upper_successor_ne_right W h0 hp H k _ _ hD hu
  have hrot := rot_seam_runZero W h0 H k d hv
    (fun he => hn (congrArg (wholePlaneDartι W 0) he))
  rw [hrot]
  have hm := seam_not_mem W h0 hp k
  exact (ccwSuccessor_upper_star_merge (S W h0 k) (U W h0 k) (WholePlaneGlueSeamMerge.L W hp k)
    (A W h0 k) (B W h0 hp k) (dir W h0 hp H) (dR W h0 k) (dL W h0 k)
    (hU W h0 hp k) (hL W h0 hp k) (hS W h0 hp k) (hSfin W h0 H k)
    (hAB W h0 hp k) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 (seam_ne W h0 k)
    (hsectorA W h0 hp H k) (hsectorB W h0 hp H k) (harg W h0 hp H k)
    _ _ hD).mpr hu





private theorem past_seam_bounds (j : ℤ) (b : Bool) {z : ℂ}
    (hz : z ∈ ((Pt).arc (boundaryOuterEdge wp hp j, b)).image) :
    seamX w0 h0 (H.1 0) (-j) ≤ z.re ∧
      z.re ≤ seamX w0 h0 (H.1 0) (1 - j) ∧ z.im = f0 z.re := by
  rw [(pastDrawing_arc W h0 hp H _).1] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  let Pp := monotoneFamilyDrawing wp (past_finiteIncidence W H) (monotone_family_all wp)
  have hqt : q ∈ (Pp.arc (futureMapBoundaryDart wp hp j)).image := by
    cases b with
    | false =>
      have he := Pp.arc_flip (boundaryOuterEdge wp hp j, true)
      change Pp.arc (boundaryOuterEdge wp hp j, false) = _ at he
      rw [he, Polyline.image_reverse_transfer] at hq
      exact hq
    | true => exact hq
  have hgraph : q.im = seamFun wp hp (past_finiteIncidence W H) q.re := by
    change q ∈ {z : ℂ | z.im = seamFun wp hp (past_finiteIncidence W H) z.re}
    rw [seamFun_graph wp hp (past_finiteIncidence W H)]
    exact Set.mem_iUnion.mpr ⟨j, hqt⟩
  obtain ⟨g, hg⟩ := seam_arc_image_graph wp hp (past_finiteIncidence W H) j
  rw [hg] at hqt
  let phi := PastDrawingTransfer.phi w0 wp h0 hp (H.1 0) (past_finiteIncidence W H)
  have hphi (i : ℤ) : phi (seamX wp hp (past_finiteIncidence W H) i) =
      -(seamX w0 h0 (H.1 0) (1 - i)) :=
    PastDrawingTransfer.phi_breakpoint w0 wp h0 hp (H.1 0)
      (past_finiteIncidence W H) i
  have hl := neg_le_neg (phi.monotone hqt.2.1)
  have hr := neg_le_neg (phi.monotone hqt.1)
  rw [hphi, neg_neg, show 1 - (j + 1) = -j by omega] at hl
  rw [hphi, neg_neg] at hr
  refine ⟨hl, hr, ?_⟩
  change -q.im + f0 (-(phi q.re)) +
    seamFun wp hp (past_finiteIncidence W H) q.re = f0 (-(phi q.re))
  linarith only [hgraph]





private theorem past_seam_args :
    Complex.arg (dir W h0 hp H (dL W h0 k)) =
      Complex.arg ((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).initialDirection ∧
    Complex.arg (dir W h0 hp H (dR W h0 k)) =
      Complex.arg ((Pt).arc (boundaryOuterEdge wp hp (-k), true)).initialDirection := by
  have hstart (d : ℕ × Bool) (hv : vertp d = boundaryVertex wp hp (1 - k)) :
      ((Pt).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    rw [(Pt).arc_start, hv, pastDrawing_seam_pos,
      show 1 - (1 - k) = k by omega]
    exact boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k
  have hw := seamWindow_spec W h0 H k
  have hleftV : vertp (boundaryOuterEdge wp hp (1 - k), false) =
      boundaryVertex wp hp (1 - k) := (boundaryOuterEdge_endpoints wp hp (1 - k)).1
  have hrightV : vertp (boundaryOuterEdge wp hp (-k), true) =
      boundaryVertex wp hp (1 - k) := by
    change edgeEast wp (boundaryOuterEdge wp hp (-k)) = _
    rw [(boundaryOuterEdge_endpoints wp hp (-k)).2.1, show -k + 1 = 1 - k by omega]
  have hdata (j : ℤ) (b : Bool)
      (hv : vertp (boundaryOuterEdge wp hp j, b) = boundaryVertex wp hp (1 - k)) :=
    initialDirection_on_graph_sign f0 x0 (seamWindowR W h0 H k)
      (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
      ((Pt).arc (boundaryOuterEdge wp hp j, b)) (hstart _ hv) ((Pt).arc_length _)
      (fun he => (Pt).initial_nonzero _ (sub_eq_zero.mpr he))
      (fun z hz => (past_seam_bounds W h0 hp H j b hz).2.2)
  constructor
  · have hd := hdata (1 - k) false hleftV
    have hlen := (Pt).arc_length (boundaryOuterEdge wp hp (1 - k), false)
    have hmem := ((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).point_mem_image
      (i := 1) (by omega)
    have hb := past_seam_bounds W h0 hp H (1 - k) false hmem
    rw [show 1 - (1 - k) = k by omega] at hb
    have hle : (((Pt).arc (boundaryOuterEdge wp hp (1 - k), false)).initialDirection).re
        ≤ 0 := by
      change (((Pt).arc _).point 1).re - (((Pt).arc _).start).re ≤ 0
      rw [hstart _ hleftV]
      exact sub_nonpos.mpr hb.2.1
    obtain ⟨c, hc, he⟩ := hd.2.1 (lt_of_le_of_ne hle hd.2.2)
    obtain ⟨a, ha, hea⟩ := dir_dL W h0 hp H k
    rw [hea, he, Complex.arg_real_mul _ ha, Complex.arg_real_mul _ hc]
  · have hd := hdata (-k) true hrightV
    have hlen := (Pt).arc_length (boundaryOuterEdge wp hp (-k), true)
    have hmem := ((Pt).arc (boundaryOuterEdge wp hp (-k), true)).point_mem_image
      (i := 1) (by omega)
    have hb := past_seam_bounds W h0 hp H (-k) true hmem
    rw [neg_neg] at hb
    have hle : 0 ≤ (((Pt).arc (boundaryOuterEdge wp hp (-k), true)).initialDirection).re := by
      change 0 ≤ (((Pt).arc _).point 1).re - (((Pt).arc _).start).re
      rw [hstart _ hrightV]
      exact sub_nonneg.mpr hb.1
    obtain ⟨c, hc, he⟩ := hd.1 (lt_of_le_of_ne hle (Ne.symm hd.2.2))
    obtain ⟨a, ha, hea⟩ := dir_dR W h0 hp H k
    rw [hea, he, Complex.arg_real_mul _ ha, Complex.arg_real_mul _ hc]





private theorem past_arg (d : ℕ × Bool)
    (hv : vertp d = boundaryVertex wp hp (1 - k)) :
    Complex.arg (dir W h0 hp H (kmswPastDart W d)) =
      Complex.arg ((Pt).arc d).initialDirection := by
  by_cases hn : kmswPastSeamEdge W d.1
  · obtain ⟨j, hj⟩ := kmswPastSeamEdge_image_boundary W h0 d.1 hn
    have he : d.1 = boundaryOuterEdge wp hp (-j) := by
      apply kmswPastEdge_injective W
      rw [hj, kmswPastEdge_seam_match_neg W h0 hp (-j), neg_neg]
    rcases past_seam_darts W hp k d hv ⟨-j, he⟩ with rfl | rfl
    · rw [(past_seam_representatives W h0 hp k).1]
      exact (past_seam_args W h0 hp H k).1
    · rw [(past_seam_representatives W h0 hp k).2]
      exact (past_seam_args W h0 hp H k).2
  · rw [dir, gluedArc_past W h0 hp H d hn]





private theorem successor_lower (d : ℕ × Bool)
    (hv : vertp d = boundaryVertex wp hp (1 - k)) :
    CcwSuccessor (WholePlaneGlueSeamMerge.L W hp k) (dir W h0 hp H)
      (kmswPastDart W d) (kmswPastDart W (rotp d)) := by
  have hs := (Pt).rotation_agreement d
  rw [hv] at hs
  rcases hs with ⟨hfin, hd, hr, hcase⟩
  refine ⟨hfin.image _, ⟨d, hd, rfl⟩, ⟨_, hr, rfl⟩, ?_⟩
  rcases hcase with ⟨heq, hsingle⟩ | ⟨hne, hmin⟩
  · left
    refine ⟨congrArg (kmswPastDart W) heq, ?_⟩
    change kmswPastDart W '' _ = _
    rw [hsingle, Set.image_singleton]
  · right
    refine ⟨fun heq => hne (kmswPastDart_injective W heq), ?_⟩
    rintro E ⟨e, he, rfl⟩ hne'
    have he' : e ≠ d := fun heq => hne' (congrArg (kmswPastDart W) heq)
    have hle := hmin e he he'
    unfold ccwTurn at hle ⊢
    rw [past_arg W h0 hp H k d hv, past_arg W h0 hp H k _ hr,
      past_arg W h0 hp H k e he]
    exact hle





private theorem lower_successor_ne_left (D E : WholePlaneDart W)
    (hD : D ∈ B W h0 hp k ∪ {dL W h0 k})
    (hs : CcwSuccessor (WholePlaneGlueSeamMerge.L W hp k) (dir W h0 hp H) D E) :
    E ≠ dL W h0 k := by
  have hm := seam_mem W h0 hp k
  have hR : dR W h0 k ∈ WholePlaneGlueSeamMerge.L W hp k := (hm (by simp)).2
  have hL : dL W h0 k ∈ WholePlaneGlueSeamMerge.L W hp k := (hm (by simp)).2
  have hRL := seam_ne W h0 k
  have hnot : WholePlaneGlueSeamMerge.L W hp k ≠ {D} := by
    intro he
    have hr : dR W h0 k = D := by simpa only [he, mem_singleton_iff] using hR
    have hl : dL W h0 k = D := by simpa only [he, mem_singleton_iff] using hL
    exact hRL (hr.trans hl.symm)
  have hmin := hs.2.2.2.resolve_left (fun h => hnot h.2)
  intro he
  rw [he] at hmin
  rcases hD with hb | hl
  · have hRD : dR W h0 k ≠ D := by
      intro hd
      exact hb.2 (by simp only [← hd, mem_insert_iff, true_or])
    have hLD : dL W h0 k ≠ D := by
      intro hd
      exact hb.2 (by simp only [← hd, mem_insert_iff, mem_singleton_iff, or_true])
    have hRs : dR W h0 k ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inr hR
    have hLs : dL W h0 k ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inr hL
    have hDs : D ∈ S W h0 k := by rw [hS W h0 hp k]; exact Or.inr hb.1
    have hargRD := harg W h0 hp H k _ _ hRs hDs hRD
    have hargLD := harg W h0 hp H k _ _ hLs hDs hLD
    have hc := ccwTurn_comp_add (hsectorB W h0 hp H k D hb)
    have hr := ccwTurn_add_reverse _ _ hargRD
    have hl := ccwTurn_add_reverse _ _ hargLD
    have hpos := ccwTurn_pos (dir W h0 hp H (dR W h0 k))
      (dir W h0 hp H (dL W h0 k))
    have hle := hmin.2 _ hR hRD
    linarith only [hc, hr, hl, hpos, hle]
  · exact hmin.1 (Set.mem_singleton_iff.mp hl).symm





theorem rotation_agreement_seam_lower (D : WholePlaneDart W)
    (hD : D ∈ B W h0 hp k ∪ {dL W h0 k}) :
    CcwSuccessor (S W h0 k) (dir W h0 hp H) D (wholePlaneRotation W H D) := by
  have hDL : D ∈ WholePlaneGlueSeamMerge.L W hp k := by
    rw [hL W h0 hp k]
    rcases hD with hb | hl
    · exact Or.inl hb
    · exact Or.inr (by simp only [mem_singleton_iff] at hl; simp only [hl,
        mem_insert_iff, mem_singleton_iff, or_true])
  obtain ⟨d, hv, rfl⟩ := hDL
  have hl := successor_lower W h0 hp H k d hv
  have hn := lower_successor_ne_left W h0 hp H k _ _ hD hl
  have hrot := rot_seam_past W hp H k d hv (by
    intro he
    apply hn
    rw [he, (past_seam_representatives W h0 hp k).1]
    rfl)
  rw [hrot]
  have hm := seam_not_mem W h0 hp k
  exact (ccwSuccessor_lower_star_merge (S W h0 k) (U W h0 k)
    (WholePlaneGlueSeamMerge.L W hp k) (A W h0 k) (B W h0 hp k)
    (dir W h0 hp H) (dR W h0 k) (dL W h0 k)
    (hU W h0 hp k) (hL W h0 hp k) (hS W h0 hp k) (hSfin W h0 H k)
    (hAB W h0 hp k) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 (seam_ne W h0 k)
    (hsectorA W h0 hp H k) (hsectorB W h0 hp H k) (harg W h0 hp H k)
    _ _ hD).mpr hl





theorem rotation_agreement_seam (D : WholePlaneDart W) (hD : D ∈ S W h0 k) :
    CcwSuccessor (S W h0 k) (dir W h0 hp H) D (wholePlaneRotation W H D) := by
  rw [star_cover W h0 hp k, hU W h0 hp k] at hD
  rcases hD with ((ha | hs) | hb)
  · exact rotation_agreement_seam_upper W h0 hp H k D (Or.inl ha)
  · rcases Set.mem_insert_iff.mp hs with hr | hl
    · exact rotation_agreement_seam_upper W h0 hp H k D
        (Or.inr (Set.mem_singleton_iff.mpr hr))
    · exact rotation_agreement_seam_lower W h0 hp H k D (Or.inr hl)
  · exact rotation_agreement_seam_lower W h0 hp H k D (Or.inl hb)





theorem rotation_agreement_seam_unfolded (D : WholePlaneDart W)
    (hD : D ∈ {E | wholePlaneDartVertex W E =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)}) :
    CcwSuccessor {E | wholePlaneDartVertex W E =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)}
      (fun E => (gluedArc W h0 hp H E).initialDirection) D (wholePlaneRotation W H D) :=
  rotation_agreement_seam W h0 hp H k D hD





theorem initial_arg_injective_seam (D E : WholePlaneDart W)
    (hD : D ∈ S W h0 k) (hE : E ∈ S W h0 k)
    (ha : Complex.arg (dir W h0 hp H D) = Complex.arg (dir W h0 hp H E)) : D = E := by
  by_contra hne
  exact harg W h0 hp H k D E hD hE hne ha





theorem initial_arg_injective_seam_unfolded (D E : WholePlaneDart W)
    (hD : D ∈ {E | wholePlaneDartVertex W E =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)})
    (hE : E ∈ {E | wholePlaneDartVertex W E =
      wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)})
    (ha : Complex.arg (gluedArc W h0 hp H D).initialDirection =
      Complex.arg (gluedArc W h0 hp H E).initialDirection) : D = E :=
  initial_arg_injective_seam W h0 hp H k D E hD hE ha

end
end DirectedDistances.KMSW.WholePlaneGlueSeamRotation
