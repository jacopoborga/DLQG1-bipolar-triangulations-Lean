/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLFaceExtension4

/-! Helpers toward Proposition 5.16: explicit boundary arcs for the constructed
closed annulus partition. These are the sub-chains and square chains used by the
slit construction, with orientation chosen so that the first cut polygon uses -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
namespace Polyline
open Set Topology

/-- Helper toward Proposition 5.16: the slit construction retains the simple
inner and square arcs, their exact endpoints, cover and intersection, and the
arc-by-arc boundary decomposition of each cut polygon. -/
theorem exists_cyclic_annulus_loops_winding_with_arcs (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      (∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
        p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z) ∧
      (∀ z ∈ p.inside, p.angleSum z = 1) ∧ (∀ z ∈ q.inside, q.angleSum z = 1) ∧
      p.image ∪ q.image =
        (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      p.image ∩ q.image = s.image ∪ t.image ∧
      s.image ∪ t.image ⊆ closure c.outside ∩ closure (enclosingSquare R).inside ∧
      p.inside ⊆ (enclosingSquare R).inside ∧ q.inside ⊆ (enclosingSquare R).inside ∧
      (∃ al be sg ta : Polyline,
        al.IsSimple ∧ be.IsSimple ∧ sg.IsSimple ∧ ta.IsSimple ∧
        2 ≤ al.points.length ∧ 2 ≤ be.points.length ∧
        2 ≤ sg.points.length ∧ 2 ≤ ta.points.length ∧
        al.start = s.start ∧ al.finish = t.start ∧
        be.start = s.start ∧ be.finish = t.start ∧
        al.image ∪ be.image = c.image ∧ al.image ∩ be.image = {s.start, t.start} ∧
        sg.start = s.finish ∧ sg.finish = t.finish ∧
        ta.start = s.finish ∧ ta.finish = t.finish ∧
        sg.image ∪ ta.image = (enclosingSquare R).image ∧
        sg.image ∩ ta.image = {s.finish, t.finish} ∧
        s.start ≠ t.start ∧ s.finish ≠ t.finish ∧
        al.start ≠ al.finish ∧ be.start ≠ be.finish ∧
        sg.start ≠ sg.finish ∧ ta.start ≠ ta.finish ∧
        p.image = al.image ∪ s.image ∪ sg.image ∪ t.image ∧
        q.image = be.image ∪ s.image ∪ ta.image ∪ t.image) := by
  obtain ⟨R, i, j, hR, hi, hj, hbox, hdata⟩ :=
    c.exists_disjoint_horizontal_exterior_slits hc
  dsimp only at hdata
  obtain ⟨hab, haim, hbim, hs, ht, hsinter, htinter, hdisj, hcontain⟩ := hdata
  let a := c.point i
  let b := c.point j
  let l : ℂ := ⟨-R, a.im⟩
  let r : ℂ := ⟨R, b.im⟩
  let s := diagonalArc a l
  let t := diagonalArc r b
  let u := squareUpperChain R a.im b.im
  let v := squareLowerChain R a.im b.im
  let U := boundaryConcat (boundaryConcat s u) t
  let V := boundaryConcat (boundaryConcat s v) t
  have hnest : closure c.inside ⊆ (enclosingSquare R).inside := by
    intro z hz
    rw [enclosingSquare_inside R hR]
    exact ⟨abs_lt.mp (hbox z hz).1, abs_lt.mp (hbox z hz).2⟩
  have ha : a ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hi))
  have hb : b ∈ (enclosingSquare R).inside :=
    hnest (c.image_subset_closure_inside_cyclic hc (c.point_mem_image hj))
  have hne : a ≠ b := fun h => (ne_of_lt hab) (congrArg Complex.re h)
  have huq : u.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_left
  have hvq : v.image ⊆ (enclosingSquare R).image := by
    rw [← square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)]
    exact subset_union_right
  obtain ⟨hU, hUlen, hUs, hUf, hUim⟩ :=
    square_bypass_data R hR a b ha hb hab u
      (squareUpperChain_isSimple R a.im b.im hR (abs_lt.mp haim).2 (abs_lt.mp hbim).2)
      (by change 2 ≤ 4; omega) rfl rfl huq
  obtain ⟨hV, hVlen, hVs, hVf, hVim⟩ :=
    square_bypass_data R hR a b ha hb hab v
      (squareLowerChain_isSimple R a.im b.im hR (abs_lt.mp haim).1 (abs_lt.mp hbim).1)
      (by change 2 ≤ 4; omega) rfl rfl hvq
  obtain ⟨x, y, hx, hy, hxlen, hylen, hxs, hxf, hys, hyf, hxy, hxyinter, hangle⟩ :=
    c.exists_inner_boundary_chains hc i j hi hj hne
  have hxsub : x.image ⊆ c.image := by rw [← hxy]; exact subset_union_left
  have hysub : y.image ⊆ c.image := by rw [← hxy]; exact subset_union_right
  have hcontact (o : Polyline) (ho : o.image ⊆ (enclosingSquare R).image) :
      ((segment ℝ a l ∪ o.image) ∪ segment ℝ b r) ∩ c.image = {a, b} := by
    have havoid : o.image ∩ c.image = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hzo, hzc⟩
      exact (hnest (c.image_subset_closure_inside_cyclic hc hzc)).1 (ho hzo)
    rw [union_inter_distrib_right, union_inter_distrib_right,
      ← (diagonalArc_data a l).2.2.2, ← (diagonalArc_data b r).2.2.2,
      hsinter, htinter, havoid, union_empty]
    rfl
  have hUc : U.image ∩ c.image = {a, b} := by rw [hUim]; exact hcontact u huq
  have hVc : V.image ∩ c.image = {a, b} := by rw [hVim]; exact hcontact v hvq
  have hinter (w W : Polyline) (hwlen : 2 ≤ w.points.length)
      (hws : w.start = a) (hwf : w.finish = b) (hwsub : w.image ⊆ c.image)
      (hWlen : 2 ≤ W.points.length) (hWs : W.start = a) (hWf : W.finish = b)
      (hWc : W.image ∩ c.image = {a, b}) : w.image ∩ W.image = {w.start, w.finish} := by
    rw [hws, hwf]
    apply Set.Subset.antisymm
    · rintro z ⟨hzw, hzW⟩
      exact hWc ▸ ⟨hzW, hwsub hzw⟩
    · rintro z (rfl | rfl)
      · exact ⟨by rw [← hws]; exact Or.inl rfl, by rw [← hWs]; exact Or.inl rfl⟩
      · constructor
        · rw [← hwf, ← point_last_eq_finish]; exact w.point_mem_image (by omega)
        · rw [← hWf, ← point_last_eq_finish]; exact W.point_mem_image (by omega)
  have hyrlen : 2 ≤ y.reverse.points.length := by simpa only [reverse, List.length_reverse] using hylen
  have hyrs : y.reverse.start = a := (start_reverse y).trans hyf
  have hyrf : y.reverse.finish = b := (finish_reverse y).trans hys
  have hyrsub : y.reverse.image ⊆ c.image := by rw [image_reverse_transfer]; exact hysub
  have hxV : (closedConcat x V).IsCyclicSimple := closedConcat_isCyclicSimple x V hx hV
    hxlen hVlen (hxs.trans hVs.symm) (hxf.trans hVf.symm)
    (by rw [hxs, hxf]; exact hne)
    (hinter x V hxlen hxs hxf hxsub hVlen hVs hVf hVc)
  have hyU : (closedConcat y.reverse U).IsCyclicSimple := closedConcat_isCyclicSimple
    y.reverse U (isSimple_reverse_transfer y hy) hU hyrlen hUlen
    (hyrs.trans hUs.symm) (hyrf.trans hUf.symm)
    (by rw [hyrs, hyrf]; exact hne)
    (hinter y.reverse U hyrlen hyrs hyrf hyrsub hUlen hUs hUf hUc)
  let p := (closedConcat x V).reverse
  let q := closedConcat y.reverse U
  have hp : p.IsCyclicSimple := isCyclicSimple_reverse _ hxV
  have hq : q.IsCyclicSimple := hyU
  have hsum : ∀ z : ℂ,
      z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
      p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z := by
    intro z hz
    have hzxV : z ∉ (closedConcat x V).image := by
      intro h
      exact hz (Or.inr (Or.inl ((image_reverse_transfer _).symm ▸ h)))
    have hzU : z ∉ U.image := by
      intro h
      exact hz (Or.inr (Or.inr ((image_closedConcat _ U (hyrf.trans hUf.symm)).symm ▸ Or.inr h)))
    have hzV : z ∉ V.image := by
      intro h
      exact hzxV ((image_closedConcat x V (hxf.trans hVf.symm)).symm ▸ Or.inr h)
    have hzy : z ∉ y.image := fun h => hz (Or.inl (Or.inl (hysub h)))
    change (closedConcat x V).reverse.angleSum z + (closedConcat y.reverse U).angleSum z = _
    rw [angleSum_reverse _ z hzxV, angleSum_closedConcat x V (hxf.trans hVf.symm) z hzV,
      angleSum_closedConcat y.reverse U (hyrf.trans hUf.symm) z hzU, angleSum_reverse y z hzy]
    have hbypass := angleSum_square_bypass_sub R a b z
    change U.angleSum z - V.angleSum z = u.angleSum z - v.angleSum z at hbypass
    have hsquare := angleSum_square_chains_sub R a.im b.im hR
      (abs_lt.mp haim) (abs_lt.mp hbim) z (fun h => hz (Or.inl (Or.inr h)))
    change v.angleSum z - u.angleSum z = _ at hsquare
    have hinner := hangle z
    linarith only [hbypass, hsquare, hinner]
  have hpim : p.image = x.image ∪ ((segment ℝ a l ∪ v.image) ∪ segment ℝ b r) := by
    dsimp only [p]
    rw [image_reverse_transfer, image_closedConcat x V (hxf.trans hVf.symm), hVim]
  have hqim : q.image = y.image ∪ ((segment ℝ a l ∪ u.image) ∪ segment ℝ b r) := by
    dsimp only [q]
    rw [image_closedConcat y.reverse U (hyrf.trans hUf.symm), image_reverse_transfer, hUim]
  have hcim (w : ℂ) (hw : w ∈ c.image) : -R < w.im ∧ w.im < R :=
    abs_lt.mp (hbox w (c.image_subset_closure_inside_cyclic hc hw)).2
  have hqabove : ∀ w ∈ q.image, -R < w.im := by
    intro w hw
    rw [hqim] at hw
    rcases hw with hw | (hw | hw) | hw
    · exact (hcim w (hysub hw)).1
    · exact (convex_halfSpace_im_gt (-R)).segment_subset
        (x := a) (y := l) (abs_lt.mp haim).1 (abs_lt.mp haim).1 hw
    · rcases (mem_squareUpperChain_image_iff R a.im b.im hR
        (abs_lt.mp haim).2 (abs_lt.mp hbim).2 w).mp hw with h | h | h
      · exact (abs_lt.mp haim).1.trans_le h.1
      · rw [h.2.2]; linarith only [hR]
      · exact (abs_lt.mp hbim).1.trans_le h.1
    · exact (convex_halfSpace_im_gt (-R)).segment_subset
        (x := b) (y := r) (abs_lt.mp hbim).1 (abs_lt.mp hbim).1 hw
  have hpbelow : ∀ w ∈ p.image, w.im < R := by
    intro w hw
    rw [hpim] at hw
    rcases hw with hw | (hw | hw) | hw
    · exact (hcim w (hxsub hw)).2
    · exact (convex_halfSpace_im_lt R).segment_subset
        (x := a) (y := l) (abs_lt.mp haim).2 (abs_lt.mp haim).2 hw
    · rcases (mem_squareLowerChain_image_iff R a.im b.im hR
        (abs_lt.mp haim).1 (abs_lt.mp hbim).1 w).mp hw with h | h | h
      · exact h.2.1.trans_lt (abs_lt.mp haim).2
      · rw [h.2.2]; linarith only [hR]
      · exact h.2.1.trans_lt (abs_lt.mp hbim).2
    · exact (convex_halfSpace_im_lt R).segment_subset
        (x := b) (y := r) (abs_lt.mp hbim).2 (abs_lt.mp hbim).2 hw
  have hclosed (d : Polyline) (hd : d.IsCyclicSimple) : d.start = d.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]
    exact hd.2.1
  have havoidp (z : ℂ) (hzc : z ∈ c.outside)
      (hzS : z ∈ (enclosingSquare R).inside) (hzq : z ∈ q.outside) : z ∉ p.image := by
    rw [hpim]
    rintro (hxz | (hsz | hvz) | htz)
    · exact hzc.1 (hxsub hxz)
    · exact hzq.1 (hqim.symm ▸ Or.inr (Or.inl (Or.inl hsz)))
    · exact hzS.1 (hvq hvz)
    · exact hzq.1 (hqim.symm ▸ Or.inr (Or.inr htz))
  have havoidq (z : ℂ) (hzc : z ∈ c.outside)
      (hzS : z ∈ (enclosingSquare R).inside) (hzp : z ∈ p.outside) : z ∉ q.image := by
    rw [hqim]
    rintro (hyz | (hsz | huz) | htz)
    · exact hzc.1 (hysub hyz)
    · exact hzp.1 (hpim.symm ▸ Or.inr (Or.inl (Or.inl hsz)))
    · exact hzS.1 (huq huz)
    · exact hzp.1 (hpim.symm ▸ Or.inr (Or.inr htz))
  have hbase (z : ℂ) (hzS : z ∈ closure (enclosingSquare R).inside)
      (hzc : z ∈ c.outside) (hzq : z ∈ q.outside) : ∃ w ∈ p.inside, p.angleSum w = 1 := by
    obtain ⟨w, ⟨hwc, hwq⟩, hwS⟩ := mem_closure_iff.mp hzS
      (c.outside ∩ q.outside) ((c.isOpen_outside (hclosed c hc)).inter
        (q.isOpen_outside (hclosed q hq))) ⟨hzc, hzq⟩
    have hwp := havoidp w hwc hwS hwq
    have hoff : w ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) := by
      rintro ((hc | hS) | hp | hq)
      · exact hwc.1 hc
      · exact hwS.1 hS
      · exact hwp hp
      · exact hwq.1 hq
    have h := hsum w hoff
    rw [enclosingSquare_angleSum_of_mem_inside R hR w hwS, hwc.2, hwq.2] at h
    have hone : p.angleSum w = 1 := by linarith only [h]
    exact ⟨w, ⟨hwp, by rw [hone]; norm_num⟩, hone⟩
  let bottom : ℂ := ⟨0, -R⟩
  have hbottom : bottom ∈ closure (enclosingSquare R).inside := by
    rw [enclosingSquare_closure_inside R hR]
    exact ⟨by simp only [bottom, abs_zero]; exact hR.le,
      by simp only [bottom, abs_neg, abs_of_pos hR]; exact le_rfl⟩
  obtain ⟨w, hwp, hwone⟩ := hbase bottom hbottom
    (c.im_le_subset_outside_of_image_im_gt (hclosed c hc) (-R)
      (fun w hw => (hcim w hw).1) (by change -R ≤ -R; exact le_rfl))
    (q.im_le_subset_outside_of_image_im_gt (hclosed q hq) (-R) hqabove (by
      change -R ≤ -R
      exact le_rfl))
  have hpone : ∀ z ∈ p.inside, p.angleSum z = 1 := by
    intro z hz
    rw [← hwone]
    exact p.angleSum_eq_of_isPreconnected (hclosed p hp) p.inside
      (p.isConnected_inside_outside_cyclic hp).1.isPreconnected (fun _ h => h.1) z w hz hwp
  let top : ℂ := ⟨0, R⟩
  have htop : top ∈ closure (enclosingSquare R).inside := by
    rw [enclosingSquare_closure_inside R hR]
    exact ⟨by simp only [top, abs_zero]; exact hR.le,
      by simp only [top, abs_of_pos hR]; exact le_rfl⟩
  have htc : top ∈ c.outside := c.im_ge_subset_outside_of_image_im_lt (hclosed c hc) R
    (fun w hw => (hcim w hw).2) (by change R ≤ R; exact le_rfl)
  have htp : top ∈ p.outside := p.im_ge_subset_outside_of_image_im_lt (hclosed p hp) R hpbelow
    (by change R ≤ R; exact le_rfl)
  obtain ⟨w', ⟨hwc, hwp'⟩, hwS⟩ := mem_closure_iff.mp htop
    (c.outside ∩ p.outside) ((c.isOpen_outside (hclosed c hc)).inter
      (p.isOpen_outside (hclosed p hp))) ⟨htc, htp⟩
  have hwq := havoidq w' hwc hwS hwp'
  have hoff : w' ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) := by
    rintro ((hc | hS) | hp | hq)
    · exact hwc.1 hc
    · exact hwS.1 hS
    · exact hwp'.1 hp
    · exact hwq hq
  have h := hsum w' hoff
  rw [enclosingSquare_angleSum_of_mem_inside R hR w' hwS, hwc.2, hwp'.2] at h
  have hqone : q.angleSum w' = 1 := by linarith only [h]
  have hwqinside : w' ∈ q.inside := ⟨hwq, by rw [hqone]; norm_num⟩
  have hqoneall : ∀ z ∈ q.inside, q.angleSum z = 1 := by
    intro z hz
    rw [← hqone]
    exact q.angleSum_eq_of_isPreconnected (hclosed q hq) q.inside
      (q.isConnected_inside_outside_cyclic hq).1.isPreconnected (fun _ h => h.1) z w' hz hwqinside
  have houter : l ≠ r := by
    intro h
    have hre := congrArg Complex.re h
    change -R = R at hre
    linarith only [hR, hre]
  have harcs : ∃ al be sg ta : Polyline,
        al.IsSimple ∧ be.IsSimple ∧ sg.IsSimple ∧ ta.IsSimple ∧
        2 ≤ al.points.length ∧ 2 ≤ be.points.length ∧
        2 ≤ sg.points.length ∧ 2 ≤ ta.points.length ∧
        al.start = (diagonalArc a l).start ∧ al.finish = (diagonalArc b r).start ∧
        be.start = (diagonalArc a l).start ∧ be.finish = (diagonalArc b r).start ∧
        al.image ∪ be.image = c.image ∧ al.image ∩ be.image = {(diagonalArc a l).start, (diagonalArc b r).start} ∧
        sg.start = (diagonalArc a l).finish ∧ sg.finish = (diagonalArc b r).finish ∧
        ta.start = (diagonalArc a l).finish ∧ ta.finish = (diagonalArc b r).finish ∧
        sg.image ∪ ta.image = (enclosingSquare R).image ∧
        sg.image ∩ ta.image = {(diagonalArc a l).finish, (diagonalArc b r).finish} ∧
        (diagonalArc a l).start ≠ (diagonalArc b r).start ∧ (diagonalArc a l).finish ≠ (diagonalArc b r).finish ∧
        al.start ≠ al.finish ∧ be.start ≠ be.finish ∧
        sg.start ≠ sg.finish ∧ ta.start ≠ ta.finish ∧
        p.image = al.image ∪ (diagonalArc a l).image ∪ sg.image ∪ (diagonalArc b r).image ∧
        q.image = be.image ∪ (diagonalArc a l).image ∪ ta.image ∪ (diagonalArc b r).image := by
    refine ⟨x, y.reverse, v, u, hx, isSimple_reverse_transfer y hy,
      squareLowerChain_isSimple R a.im b.im hR (abs_lt.mp haim).1 (abs_lt.mp hbim).1,
      squareUpperChain_isSimple R a.im b.im hR (abs_lt.mp haim).2 (abs_lt.mp hbim).2,
      hxlen, hyrlen, ?_, ?_, hxs, hxf, hyrs, hyrf, ?_, ?_,
      rfl, rfl, rfl, rfl, ?_, ?_, hne, houter, ?_, ?_, houter, houter, ?_, ?_⟩
    · change 2 ≤ 4; omega
    · change 2 ≤ 4; omega
    · rw [image_reverse_transfer]; exact hxy
    · rw [image_reverse_transfer]; exact hxyinter
    · rw [union_comm]
      exact square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)
    · rw [inter_comm]
      exact square_chains_image_inter R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)
    · rw [hxs, hxf]; exact hne
    · rw [hyrs, hyrf]; exact hne
    · rw [hpim, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
      simp only [union_assoc]
    · rw [hqim, image_reverse_transfer,
        (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
      simp only [union_assoc]
  refine ⟨R, s, diagonalArc b r, p, q, hR, hnest, hs, ht, hdisj, hsinter, htinter,
    ?_, ?_, hp, hq, hsum, hpone, hqoneall, ?_, ?_, ?_, ?_, ?_, harcs⟩
  · rw [(diagonalArc_data a l).2.2.2]
    exact (left_slit_inter_enclosingSquare R hR a ha).1
  · rw [(diagonalArc_data b r).2.2.2]
    exact (right_slit_inter_enclosingSquare R hR b hb).1
  · rw [hpim, hqim, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    have huv : u.image ∪ v.image = (enclosingSquare R).image :=
      square_chains_image_union R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim)
    rw [← hxy, ← huv]
    have hidem (A B : Set ℂ) : A ∪ (A ∪ B) = A ∪ B := by
      rw [← union_assoc, union_self]
    simp only [union_assoc, union_left_comm, union_comm, hidem]
  · rw [hpim, hqim, (diagonalArc_data a l).2.2.2, (diagonalArc_data b r).2.2.2]
    apply Set.Subset.antisymm
    · rintro z ⟨hzp, hzq⟩
      by_cases hzs : z ∈ segment ℝ a l
      · exact Or.inl hzs
      by_cases hzt : z ∈ segment ℝ b r
      · exact Or.inr hzt
      have hxp : z ∈ x.image ∨ z ∈ v.image := by
        rcases hzp with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      have hyq : z ∈ y.image ∨ z ∈ u.image := by
        rcases hzq with hz | (hz | hz) | hz
        · exact Or.inl hz
        · exact False.elim (hzs hz)
        · exact Or.inr hz
        · exact False.elim (hzt hz)
      rcases hxp with hzx | hzv <;> rcases hyq with hzy | hzu
      · have hz : z ∈ ({a, b} : Set ℂ) := hxyinter ▸ ⟨hzx, hzy⟩
        rcases hz with rfl | rfl
        · exact Or.inl (left_mem_segment ℝ _ _)
        · exact Or.inr (left_mem_segment ℝ _ _)
      · exact False.elim ((hnest (c.image_subset_closure_inside_cyclic hc (hxsub hzx))).1 (huq hzu))
      · exact False.elim ((hnest (c.image_subset_closure_inside_cyclic hc (hysub hzy))).1 (hvq hzv))
      · have hz : z ∈ ({l, r} : Set ℂ) :=
          square_chains_image_inter R a.im b.im hR (abs_lt.mp haim) (abs_lt.mp hbim) ▸
            ⟨hzu, hzv⟩
        rcases hz with rfl | rfl
        · exact Or.inl (right_mem_segment ℝ _ _)
        · exact Or.inr (right_mem_segment ℝ _ _)
    · rintro z (hzs | hzt)
      · exact ⟨Or.inr (Or.inl (Or.inl hzs)), Or.inr (Or.inl (Or.inl hzs))⟩
      · exact ⟨Or.inr (Or.inr hzt), Or.inr (Or.inr hzt)⟩
  · intro z hz
    rw [enclosingSquare_closure_inside R hR]
    exact hcontain hz
  all_goals
    apply inside_subset_inside_of_image_subset_closure (enclosingSquare R)
      (enclosingSquare_isCyclicSimple R hR)
  · exact hclosed p hp
  · rw [hpim]
    rintro z (hzx | (hzs | hzv) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hxsub hzx)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (hvq hzv)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2
  · exact hclosed q hq
  · rw [hqim]
    rintro z (hzy | (hzs | hzu) | hzt)
    · exact subset_closure (hnest (c.image_subset_closure_inside_cyclic hc (hysub hzy)))
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inl ((diagonalArc_data a l).2.2.2.symm ▸ hzs))).2
    · exact (enclosingSquare R).image_subset_closure_inside_cyclic
        (enclosingSquare_isCyclicSimple R hR) (huq hzu)
    · rw [enclosingSquare_closure_inside R hR]
      exact (hcontain (Or.inr ((diagonalArc_data b r).2.2.2.symm ▸ hzt))).2


/-- Helper toward Proposition 5.16: counterclockwise inner boundaries admit
the exact closed annulus partition, with signed winding subtraction. -/
theorem exists_closed_annulus_partition_counterclockwise_with_arcs (c : Polyline)
    (hc : c.IsCyclicSimple) (hccw : ∀ z ∈ c.inside, c.angleSum z = 1) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧ closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      closure p.inside ∪ closure q.inside = closure c.outside ∩ closure (enclosingSquare R).inside ∧
      closure p.inside ∩ closure q.inside = s.image ∪ t.image ∧
      p.image ∪ q.image = (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      (∀ z : ℂ, z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) →
        p.angleSum z + q.angleSum z = (enclosingSquare R).angleSum z - c.angleSum z) ∧
      (∃ al be sg ta : Polyline,
        al.IsSimple ∧ be.IsSimple ∧ sg.IsSimple ∧ ta.IsSimple ∧
        2 ≤ al.points.length ∧ 2 ≤ be.points.length ∧
        2 ≤ sg.points.length ∧ 2 ≤ ta.points.length ∧
        al.start = s.start ∧ al.finish = t.start ∧
        be.start = s.start ∧ be.finish = t.start ∧
        al.image ∪ be.image = c.image ∧ al.image ∩ be.image = {s.start, t.start} ∧
        sg.start = s.finish ∧ sg.finish = t.finish ∧
        ta.start = s.finish ∧ ta.finish = t.finish ∧
        sg.image ∪ ta.image = (enclosingSquare R).image ∧
        sg.image ∩ ta.image = {s.finish, t.finish} ∧
        s.start ≠ t.start ∧ s.finish ≠ t.finish ∧
        al.start ≠ al.finish ∧ be.start ≠ be.finish ∧
        sg.start ≠ sg.finish ∧ ta.start ≠ ta.finish ∧
        p.image = al.image ∪ s.image ∪ sg.image ∪ t.image ∧
        q.image = be.image ∪ s.image ∪ ta.image ∪ t.image) := by
  obtain ⟨R, s, t, p, q, hR, hnest, hs, ht, hst, hsc, htc, hsS, htS, hp, hq,
    hsum, hpone, hqone, himunion, himinter, hslits, hpS, hqS, harcs⟩ :=
    c.exists_cyclic_annulus_loops_winding_with_arcs hc
  have hcclosed : c.start = c.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hc.2.1
  have hpclosed : p.start = p.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hp.2.1
  have hqclosed : q.start = q.finish := by
    rw [← point_zero_eq_start, ← point_last_eq_finish]; exact hq.2.1
  have hS := enclosingSquare_isCyclicSimple R hR
  have hKp : s.image ∪ t.image ⊆ p.image := fun _ h => (himinter.symm ▸ h).1
  have hKq : s.image ∪ t.image ⊆ q.image := fun _ h => (himinter.symm ▸ h).2
  have hci : c.inside ⊆ p.outside ∩ q.outside := by
    intro z hz
    have hzS := hnest (subset_closure hz)
    have hzK : z ∉ s.image ∪ t.image := fun h =>
      (c.closure_sides_avoid hcclosed).2 (hslits h).1 hz
    have hoff : z ∉ p.image ∪ q.image := by
      rw [himunion]
      exact fun h => h.elim (fun h => h.elim hz.1 hzS.1) hzK
    have hs' := hsum z (fun h => h.elim (fun h => h.elim hz.1 hzS.1) hoff)
    rw [enclosingSquare_angleSum_of_mem_inside R hR z hzS, hccw z hz] at hs'
    have hpv := (p.angleSum_zero_or_one_of_counterclockwise hpone z (fun h => hoff (Or.inl h))).1
    have hqv := (q.angleSum_zero_or_one_of_counterclockwise hqone z (fun h => hoff (Or.inr h))).1
    have hpzero : p.angleSum z = 0 := by rcases hpv with h | h <;> rcases hqv with h' | h' <;> linarith only [hs', h, h']
    have hqzero : q.angleSum z = 0 := by linarith only [hs', hpzero]
    exact ⟨⟨fun h => hoff (Or.inl h), hpzero⟩, ⟨fun h => hoff (Or.inr h), hqzero⟩⟩
  have hpc : p.inside ⊆ c.outside := by
    have havoid : closure c.inside ⊆ p.insideᶜ :=
      (closure_mono (fun _ h => (hci h).1)).trans (p.closure_sides_avoid hpclosed).2
    intro z hz
    have hzoff : z ∉ c.image := fun h => havoid (c.image_subset_closure_inside_cyclic hc h) hz
    exact ⟨hzoff, by
      by_contra h
      exact havoid (subset_closure (show z ∈ c.inside from ⟨hzoff, h⟩)) hz⟩
  have hqc : q.inside ⊆ c.outside := by
    have havoid : closure c.inside ⊆ q.insideᶜ :=
      (closure_mono (fun _ h => (hci h).2)).trans (q.closure_sides_avoid hqclosed).2
    intro z hz
    have hzoff : z ∉ c.image := fun h => havoid (c.image_subset_closure_inside_cyclic hc h) hz
    exact ⟨hzoff, by
      by_contra h
      exact havoid (subset_closure (show z ∈ c.inside from ⟨hzoff, h⟩)) hz⟩
  have hpavoidq {z : ℂ} (hz : z ∈ p.inside) : z ∉ q.image := by
    intro h
    have him : z ∈ p.image ∪ q.image := Or.inr h
    rw [himunion] at him
    rcases him with (hc | hS) | hK
    · exact (hpc hz).1 hc
    · exact (hpS hz).1 hS
    · exact hz.1 (hKp hK)
  have hqavoidp {z : ℂ} (hz : z ∈ q.inside) : z ∉ p.image := by
    intro h
    have him : z ∈ p.image ∪ q.image := Or.inl h
    rw [himunion] at him
    rcases him with (hc | hS) | hK
    · exact (hqc hz).1 hc
    · exact (hqS hz).1 hS
    · exact hz.1 (hKq hK)
  have hdisj : Disjoint p.inside q.inside := by
    apply Set.disjoint_left.mpr
    intro z hzp hzq
    have hoff : z ∉ (c.image ∪ (enclosingSquare R).image) ∪ (p.image ∪ q.image) :=
      fun h => h.elim (fun h => h.elim (hpc hzp).1 (hpS hzp).1)
        (fun h => h.elim hzp.1 hzq.1)
    have h := hsum z hoff
    rw [hpone z hzp, hqone z hzq, enclosingSquare_angleSum_of_mem_inside R hR z (hpS hzp),
      (hpc hzp).2] at h
    norm_num at h
  have hcover : closure p.inside ∪ closure q.inside =
      closure c.outside ∩ closure (enclosingSquare R).inside := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · exact ⟨closure_mono hpc hz, closure_mono hpS hz⟩
      · exact ⟨closure_mono hqc hz, closure_mono hqS hz⟩
    · intro z hz
      by_cases him : z ∈ p.image ∪ q.image
      · exact him.elim (fun h => Or.inl (p.image_subset_closure_inside_cyclic hp h))
          (fun h => Or.inr (q.image_subset_closure_inside_cyclic hq h))
      have hzoffc : z ∉ c.image := fun h => him (himunion.symm ▸ Or.inl (Or.inl h))
      have hzoffS : z ∉ (enclosingSquare R).image := fun h => him (himunion.symm ▸ Or.inl (Or.inr h))
      have hzc : z ∈ c.outside := by
        have hnot := (c.closure_sides_avoid hcclosed).2 hz.1
        exact ⟨hzoffc, by by_contra h; exact hnot ⟨hzoffc, h⟩⟩
      have hzS : z ∈ (enclosingSquare R).inside := by
        rw [closure_inside_eq_union_image _ hS] at hz
        exact hz.2.resolve_right hzoffS
      have h := hsum z (fun h => h.elim (fun h => h.elim hzoffc hzoffS) him)
      rw [enclosingSquare_angleSum_of_mem_inside R hR z hzS, hzc.2] at h
      by_cases hpzero : p.angleSum z = 0
      · right
        apply subset_closure
        exact ⟨fun h => him (Or.inr h), by intro hqzero; rw [hpzero, hqzero] at h; norm_num at h⟩
      · exact Or.inl (subset_closure ⟨fun h => him (Or.inl h), hpzero⟩)
  have hinter : closure p.inside ∩ closure q.inside = s.image ∪ t.image := by
    rw [closure_inside_eq_union_image _ hp, closure_inside_eq_union_image _ hq]
    apply Set.Subset.antisymm
    · rintro z ⟨hz | hz, hw | hw⟩
      · exact False.elim (Set.disjoint_left.mp hdisj hz hw)
      · exact False.elim (hpavoidq hz hw)
      · exact False.elim (hqavoidp hw hz)
      · exact himinter ▸ ⟨hz, hw⟩
    · exact fun z hz => ⟨Or.inr (hKp hz), Or.inr (hKq hz)⟩
  exact ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion, hsum, harcs⟩


/-- Helper toward Proposition 5.16: every cyclically simple inner boundary
admits the closed annulus partition with explicit simple inner and square arcs,
attached to the corresponding cut polygons regardless of orientation. -/
theorem exists_closed_annulus_partition_with_arcs (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (s t p q : Polyline), 0 < R ∧
      (enclosingSquare R).IsCyclicSimple ∧ closure c.inside ⊆ (enclosingSquare R).inside ∧
      s.IsSimple ∧ t.IsSimple ∧ Disjoint s.image t.image ∧
      s.image ∩ c.image = {s.start} ∧ t.image ∩ c.image = {t.start} ∧
      s.image ∩ (enclosingSquare R).image = {s.finish} ∧
      t.image ∩ (enclosingSquare R).image = {t.finish} ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      closure p.inside ∪ closure q.inside = closure c.outside ∩ closure (enclosingSquare R).inside ∧
      closure p.inside ∩ closure q.inside = s.image ∪ t.image ∧
      p.image ∪ q.image = (c.image ∪ (enclosingSquare R).image) ∪ (s.image ∪ t.image) ∧
      (∃ al be sg ta : Polyline,
        al.IsSimple ∧ be.IsSimple ∧ sg.IsSimple ∧ ta.IsSimple ∧
        2 ≤ al.points.length ∧ 2 ≤ be.points.length ∧
        2 ≤ sg.points.length ∧ 2 ≤ ta.points.length ∧
        al.start = s.start ∧ al.finish = t.start ∧
        be.start = s.start ∧ be.finish = t.start ∧
        al.image ∪ be.image = c.image ∧ al.image ∩ be.image = {s.start, t.start} ∧
        sg.start = s.finish ∧ sg.finish = t.finish ∧
        ta.start = s.finish ∧ ta.finish = t.finish ∧
        sg.image ∪ ta.image = (enclosingSquare R).image ∧
        sg.image ∩ ta.image = {s.finish, t.finish} ∧
        s.start ≠ t.start ∧ s.finish ≠ t.finish ∧
        al.start ≠ al.finish ∧ be.start ≠ be.finish ∧
        sg.start ≠ sg.finish ∧ ta.start ≠ ta.finish ∧
        p.image = al.image ∪ s.image ∪ sg.image ∪ t.image ∧
        q.image = be.image ∪ s.image ∪ ta.image ∪ t.image) := by
  obtain ⟨d, _, hd, hdimage, hdinside, hdoutside, hdccw⟩ :=
    c.exists_counterclockwise_reorientation hc
  obtain ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion, _, harcs⟩ :=
    d.exists_closed_annulus_partition_counterclockwise_with_arcs hd hdccw
  rw [hdinside] at hnest
  rw [hdimage] at hsc htc himunion harcs
  rw [hdoutside] at hcover
  exact ⟨R, s, t, p, q, hR, hS, hnest, hs, ht, hst, hsc, htc, hsS, htS,
    hp, hq, hcover, hinter, himunion, harcs⟩


end Polyline
end DirectedDistances.PlanarMap

