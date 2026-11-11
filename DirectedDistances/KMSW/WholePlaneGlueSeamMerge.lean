/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.WholePlaneGlueSeamStar
public import DirectedDistances.KMSW.WholePlaneGlueSeamSectors
public import DirectedDistances.PlanarMap.SeamGraphDirection
import DirectedDistances.PlanarMap.MonotonePolyline

public section
namespace DirectedDistances.KMSW.WholePlaneGlueSeamMerge

open DirectedDistances.PlanarMap Set WholePlanePastGlueData
open WholePlaneGlueSeamStar WholePlaneGlueSeamSectors

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




@[expose] def dR : WholePlaneDart W :=
  wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 k, false)




@[expose] def dL : WholePlaneDart W :=
  wholePlaneDartι W 0 (boundaryOuterEdge w0 h0 (k - 1), true)




@[expose] def S : Set (WholePlaneDart W) :=
  {E | wholePlaneDartVertex W E = wholePlaneVertexι W 0 (boundaryVertex w0 h0 k)}




@[expose] def U : Set (WholePlaneDart W) :=
  wholePlaneDartι W 0 '' {e | vert0 e = boundaryVertex w0 h0 k}




@[expose] def L : Set (WholePlaneDart W) :=
  kmswPastDart W '' {e | vertp e = boundaryVertex wp hp (1 - k)}




@[expose] def A : Set (WholePlaneDart W) :=
  U W h0 k \ {dR W h0 k, dL W h0 k}




@[expose] def B : Set (WholePlaneDart W) :=
  L W hp k \ {dR W h0 k, dL W h0 k}




@[expose] def dir (E : WholePlaneDart W) : ℂ :=
  (gluedArc W h0 hp H E).initialDirection




theorem seam_mem :
    {dR W h0 k, dL W h0 k} ⊆ U W h0 k ∩ L W hp k := by
  rw [show U W h0 k ∩ L W hp k = {dR W h0 k, dL W h0 k} from
    overlap W h0 hp k]

include hp in



theorem hU : U W h0 k = A W h0 k ∪ {dR W h0 k, dL W h0 k} := by
  classical
  have hm := seam_mem W h0 hp k
  ext E
  constructor
  · intro he
    by_cases hs : E ∈ ({dR W h0 k, dL W h0 k} : Set (WholePlaneDart W))
    · exact Or.inr hs
    · exact Or.inl ⟨he, hs⟩
  · rintro (he | he)
    · exact he.1
    · exact (hm he).1




theorem hL : L W hp k = B W h0 hp k ∪ {dR W h0 k, dL W h0 k} := by
  classical
  have hm := seam_mem W h0 hp k
  ext E
  constructor
  · intro he
    by_cases hs : E ∈ ({dR W h0 k, dL W h0 k} : Set (WholePlaneDart W))
    · exact Or.inr hs
    · exact Or.inl ⟨he, hs⟩
  · rintro (he | he)
    · exact he.1
    · exact (hm he).2




theorem hS : S W h0 k = U W h0 k ∪ L W hp k :=
  star_seam W h0 hp k

include H in



theorem hSfin : (S W h0 k).Finite :=
  wholePlaneStar_finite W H (wholePlaneVertexι W 0 (boundaryVertex w0 h0 k))




theorem hAB : Disjoint (A W h0 k) (B W h0 hp k) := by
  apply Set.disjoint_left.mpr
  intro E ha hb
  exact ha.2 ((overlap W h0 hp k) ▸ And.intro ha.1 hb.1)




theorem seam_not_mem :
    dR W h0 k ∉ A W h0 k ∧ dL W h0 k ∉ A W h0 k ∧
      dR W h0 k ∉ B W h0 hp k ∧ dL W h0 k ∉ B W h0 hp k := by
  simp only [A, B, mem_sdiff, mem_insert_iff, mem_singleton_iff, true_or,
    or_true, not_true_eq_false, and_false, not_false_eq_true, and_self]




theorem seam_ne : dR W h0 k ≠ dL W h0 k := by
  intro he
  have hb := congrArg Prod.snd he
  change false = true at hb
  cases hb




theorem dir_dR : ∃ c : ℝ, 0 < c ∧
    dir W h0 hp H (dR W h0 k) = (c : ℂ) * ⟨1, seamSlopeR W h0 H k⟩ := by
  let d : ℕ × Bool := (boundaryOuterEdge w0 h0 k, false)
  have hs : ((P0).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    rw [(P0).arc_start, (runZero_seam_darts_incident W h0 k).2.1,
      boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k]
  have hn : ((P0).arc d).point 1 ≠ ((P0).arc d).start := by
    intro he
    exact (P0).initial_nonzero d (sub_eq_zero.mpr he)
  have hg : ∀ z ∈ ((P0).arc d).image, z.im = f0 z.re := by
    intro z hz
    apply WholePlanePastGlueGeometry.seam_arc_graph W h0 hp H k false
    rw [gluedArc_runZero]
    exact hz
  have hpos : 0 < ((P0).arc d).initialDirection.re := by
    have he := kmsw_edge_allocated_by_self w0 d.1
    have ha := monotoneLimitDrawing_arc_layout w0 ((And.left H) 0)
      (fun n => ⟨monotoneLayoutDrawing w0 n ((monotone_family_all w0 n).choose),
        (monotone_family_all w0 n).choose_spec⟩) d.1 d.1 he false
    change (P0).arc d = layoutArc w0 d.1 d.1 at ha
    rw [ha]
    exact Polyline.initialDirection_re_pos (layoutArc_points_pairwise w0 d.1 d.1 he)
      (layoutArc_length_two_le w0 d.1 d.1)
  have hw := seamWindow_spec W h0 H k
  have hr := (initialDirection_on_graph_sign f0 x0 (seamWindowR W h0 H k)
    (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
    ((P0).arc d) hs ((P0).arc_length d) hn hg).1 hpos
  simpa only [dir, dR, gluedArc_runZero] using hr




theorem dir_dL : ∃ c : ℝ, 0 < c ∧
    dir W h0 hp H (dL W h0 k) = (c : ℂ) * ⟨-1, -(seamSlopeL W h0 H k)⟩ := by
  let d : ℕ × Bool := (boundaryOuterEdge w0 h0 (k - 1), true)
  have hs : ((P0).arc d).start = (⟨x0, f0 x0⟩ : ℂ) := by
    rw [(P0).arc_start, (runZero_seam_darts_incident W h0 k).2.2,
      boundaryVertex_pos_eq w0 h0 ((And.left H) 0) k]
  have hn : ((P0).arc d).point 1 ≠ ((P0).arc d).start := by
    intro he
    exact (P0).initial_nonzero d (sub_eq_zero.mpr he)
  have hg : ∀ z ∈ ((P0).arc d).image, z.im = f0 z.re := by
    intro z hz
    apply WholePlanePastGlueGeometry.seam_arc_graph W h0 hp H (k - 1) true
    rw [gluedArc_runZero]
    exact hz
  have hneg : ((P0).arc d).initialDirection.re < 0 := by
    have he := kmsw_edge_allocated_by_self w0 d.1
    have ha := monotoneLimitDrawing_arc_layout w0 ((And.left H) 0)
      (fun n => ⟨monotoneLayoutDrawing w0 n ((monotone_family_all w0 n).choose),
        (monotone_family_all w0 n).choose_spec⟩) d.1 d.1 he true
    change (P0).arc d = (layoutArc w0 d.1 d.1).reverse at ha
    rw [ha]
    exact Polyline.reverse_initialDirection_re_neg
      (layoutArc_points_pairwise w0 d.1 d.1 he) (layoutArc_length_two_le w0 d.1 d.1)
  have hw := seamWindow_spec W h0 H k
  have hl := (initialDirection_on_graph_sign f0 x0 (seamWindowR W h0 H k)
    (seamSlopeL W h0 H k) (seamSlopeR W h0 H k) hw.1 hw.2.1 hw.2.2
    ((P0).arc d) hs ((P0).arc_length d) hn hg).2.1 hneg
  simpa only [dir, dL, gluedArc_runZero] using hl




private theorem A_nonseam (d : ℕ × Bool)
    (hd : vert0 d = boundaryVertex w0 h0 k)
    (ha : wholePlaneDartι W 0 d ∈ A W h0 k) :
    ∀ j : ℤ, d.1 ≠ boundaryOuterEdge w0 h0 j := by
  intro j he
  rcases runZero_seam_darts W h0 k d hd ⟨j, he⟩ with he | he
  · exact ha.2 (Set.mem_insert_iff.mpr (Or.inl (congrArg (wholePlaneDartι W 0) he)))
  · exact ha.2 (Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_singleton_iff.mpr (congrArg (wholePlaneDartι W 0) he))))




private theorem B_nonseam (d : ℕ × Bool)
    (hb : kmswPastDart W d ∈ B W h0 hp k) : ¬ kmswPastSeamEdge W d.1 := by
  intro he
  obtain ⟨e, he⟩ := (kmswPastEdge_mem_runZero_iff W h0 d.1).mpr he
  have heq : wholePlaneDartι W 0 (e, !d.2) = kmswPastDart W d := by
    apply Prod.ext
    · exact he
    · rfl
  have hs : kmswPastDart W d ∈ S W h0 k := by
    rw [hS W h0 hp k]
    exact Or.inr hb.1
  have hv : vert0 (e, !d.2) = boundaryVertex w0 h0 k := by
    apply wholePlaneVertexι_injective W 0
    rw [← wholePlaneDartVertex_ι, heq]
    exact hs
  have hu : kmswPastDart W d ∈ U W h0 k := ⟨(e, !d.2), hv, heq⟩
  exact hb.2 ((overlap W h0 hp k) ▸ And.intro hu hb.1)




theorem hsectorA : ∀ a ∈ A W h0 k,
    0 < ccwTurn (dir W h0 hp H (dR W h0 k)) (dir W h0 hp H a) ∧
      ccwTurn (dir W h0 hp H (dR W h0 k)) (dir W h0 hp H a) <
        ccwTurn (dir W h0 hp H (dR W h0 k)) (dir W h0 hp H (dL W h0 k)) := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := ha.1
  have habove := runZero_nonseam_aboveSector W h0 H k hp d hd
    (A_nonseam W h0 k d hd ha)
  obtain ⟨cR, hcR, hR⟩ := dir_dR W h0 hp H k
  obtain ⟨cL, hcL, hL⟩ := dir_dL W h0 hp H k
  rw [hR, hL, ccwTurn_smul_left _ _ _ hcR, ccwTurn_smul_left _ _ _ hcR,
    ccwTurn_smul_right _ _ _ hcL]
  simpa only [dir, gluedArc_runZero] using aboveSector_turn habove




theorem hsectorB : ∀ b ∈ B W h0 hp k,
    ccwTurn (dir W h0 hp H (dR W h0 k)) (dir W h0 hp H (dL W h0 k)) <
      ccwTurn (dir W h0 hp H (dR W h0 k)) (dir W h0 hp H b) := by
  intro b hb
  obtain ⟨d, hd, rfl⟩ := hb.1
  have hn := B_nonseam W h0 hp k d hb
  have hbelow := past_nonseam_belowSector W h0 hp H k d hd hn
  obtain ⟨cR, hcR, hR⟩ := dir_dR W h0 hp H k
  obtain ⟨cL, hcL, hL⟩ := dir_dL W h0 hp H k
  rw [hR, hL, ccwTurn_smul_left _ _ _ hcR, ccwTurn_smul_left _ _ _ hcR,
    ccwTurn_smul_right _ _ _ hcL]
  simpa only [dir, gluedArc_past W h0 hp H d hn] using (belowSector_turn hbelow).1




theorem arg_injective_U (x y : WholePlaneDart W)
    (hx : x ∈ U W h0 k) (hy : y ∈ U W h0 k)
    (ha : Complex.arg (dir W h0 hp H x) = Complex.arg (dir W h0 hp H y)) : x = y := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨e, he, rfl⟩ := hy
  simp only [dir, gluedArc_runZero] at ha
  exact congrArg (wholePlaneDartι W 0)
    ((P0).initial_arg_injective d e (hd.trans he.symm) ha)




theorem arg_injective_B (x y : WholePlaneDart W)
    (hx : x ∈ B W h0 hp k) (hy : y ∈ B W h0 hp k)
    (ha : Complex.arg (dir W h0 hp H x) = Complex.arg (dir W h0 hp H y)) : x = y := by
  obtain ⟨d, hd, rfl⟩ := hx.1
  obtain ⟨e, he, rfl⟩ := hy.1
  have hnd := B_nonseam W h0 hp k d hx
  have hne := B_nonseam W h0 hp k e hy
  simp only [dir, gluedArc_past W h0 hp H d hnd,
    gluedArc_past W h0 hp H e hne] at ha
  exact congrArg (kmswPastDart W) ((Pt).initial_arg_injective d e (hd.trans he.symm) ha)




theorem arg_dR_ne_B (b : WholePlaneDart W) (hb : b ∈ B W h0 hp k) :
    Complex.arg (dir W h0 hp H (dR W h0 k)) ≠ Complex.arg (dir W h0 hp H b) := by
  intro ha
  obtain ⟨d, hd, rfl⟩ := hb.1
  have hn := B_nonseam W h0 hp k d hb
  have hlower := past_nonseam_belowSector W h0 hp H k d hd hn
  have hbn : dir W h0 hp H (kmswPastDart W d) ≠ 0 := by
    simpa only [dir, gluedArc_past W h0 hp H d hn] using (Pt).initial_nonzero d
  have hbelow : BelowSector (seamSlopeL W h0 H k) (seamSlopeR W h0 H k)
      (dir W h0 hp H (kmswPastDart W d)) := by
    simpa only [dir, gluedArc_past W h0 hp H d hn] using hlower
  obtain ⟨c, hc, hR⟩ := dir_dR W h0 hp H k
  rw [hR, Complex.arg_real_mul _ hc] at ha
  have heR : (⟨1, seamSlopeR W h0 H k⟩ : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  let t : ℝ := ‖dir W h0 hp H (kmswPastDart W d)‖ /
    ‖(⟨1, seamSlopeR W h0 H k⟩ : ℂ)‖
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hbn) (norm_pos_iff.mpr heR)
  have hscale : dir W h0 hp H (kmswPastDart W d) =
      (t : ℂ) * ⟨1, seamSlopeR W h0 H k⟩ := by
    simpa only [t, Complex.ofReal_div] using
      ((Complex.arg_eq_arg_iff heR hbn).mp ha).symm
  rw [hscale] at hbelow
  have hstrict := hbelow.1 (by simpa only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_one, zero_mul, sub_zero] using ht)
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_one, zero_mul, add_zero, sub_zero] at hstrict
  exact (lt_irrefl (t * seamSlopeR W h0 H k)) (by
    simpa only [mul_comm] using hstrict)




theorem arg_ne_U_B (a b : WholePlaneDart W)
    (ha : a ∈ U W h0 k) (hb : b ∈ B W h0 hp k) :
    Complex.arg (dir W h0 hp H a) ≠ Complex.arg (dir W h0 hp H b) := by
  intro heq
  have hturn := ccwTurn_eq_of_arg_eq
    (a := dir W h0 hp H (dR W h0 k)) rfl heq
  rw [hU W h0 hp k] at ha
  rcases ha with ha | ha
  · have hu := (hsectorA W h0 hp H k a ha).2
    have hl := hsectorB W h0 hp H k b hb
    rw [hturn] at hu
    exact (not_lt_of_ge hu.le) hl
  · rcases Set.mem_insert_iff.mp ha with hr | hl
    · subst a
      exact arg_dR_ne_B W h0 hp H k b hb heq
    · have hl' := Set.mem_singleton_iff.mp hl
      subst a
      have hlow := hsectorB W h0 hp H k b hb
      rw [hturn] at hlow
      exact (lt_irrefl _) hlow




theorem star_cover : S W h0 k = U W h0 k ∪ B W h0 hp k := by
  ext E
  rw [hS W h0 hp k, hL W h0 hp k]
  constructor
  · rintro (hu | hb | hs)
    · exact Or.inl hu
    · exact Or.inr hb
    · exact Or.inl (seam_mem W h0 hp k hs).1
  · rintro (hu | hb)
    · exact Or.inl hu
    · exact Or.inr (Or.inl hb)




theorem harg : ∀ x y : WholePlaneDart W, x ∈ S W h0 k → y ∈ S W h0 k → x ≠ y →
    Complex.arg (dir W h0 hp H x) ≠ Complex.arg (dir W h0 hp H y) := by
  intro x y hx hy hne heq
  rw [star_cover W h0 hp k] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hne (arg_injective_U W h0 hp H k x y hx hy heq)
  · exact arg_ne_U_B W h0 hp H k x y hx hy heq
  · exact arg_ne_U_B W h0 hp H k y x hy hx heq.symm
  · exact hne (arg_injective_B W h0 hp H k x y hx hy heq)

end
end DirectedDistances.KMSW.WholePlaneGlueSeamMerge
