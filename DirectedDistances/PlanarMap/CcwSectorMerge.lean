module

public import DirectedDistances.PlanarMap.SlopeAngularOrder

/-! # Counterclockwise successor under a seam-star merge

Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. -/

public section
namespace DirectedDistances.PlanarMap

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. The angular coordinate rooted at
the right seam direction, with that direction's full turn normalized to zero. -/
@[expose] noncomputable def seamTheta {D : Type*} (dir : D → ℂ) (dR x : D) : ℝ :=
  if Complex.arg (dir dR) < Complex.arg (dir x) then
    Complex.arg (dir x) - Complex.arg (dir dR)
  else if Complex.arg (dir x) < Complex.arg (dir dR) then
    Complex.arg (dir x) - Complex.arg (dir dR) + 2 * Real.pi
  else 0

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. Positive cyclic difference in a
real angular coordinate, with equal coordinates representing a full turn. -/
@[expose] noncomputable def seamThetaTurn {D : Type*} (theta : D → ℝ) (x y : D) : ℝ :=
  if theta x < theta y then theta y - theta x
  else theta y - theta x + 2 * Real.pi

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. The rooted coordinate computes
the same turn as `ccwTurn`; the right seam dart has coordinate zero. -/
theorem ccwTurn_eq_seamThetaTurn {D : Type*} (dir : D → ℂ) (dR x y : D) :
    ccwTurn (dir x) (dir y) =
      seamThetaTurn (seamTheta dir dR) x y := by
  unfold ccwTurn seamTheta seamThetaTurn
  have hr := Complex.arg_mem_Ioc (dir dR)
  have hx := Complex.arg_mem_Ioc (dir x)
  have hy := Complex.arg_mem_Ioc (dir y)
  change -Real.pi < Complex.arg (dir dR) ∧ Complex.arg (dir dR) ≤ Real.pi at hr
  change -Real.pi < Complex.arg (dir x) ∧ Complex.arg (dir x) ≤ Real.pi at hx
  change -Real.pi < Complex.arg (dir y) ∧ Complex.arg (dir y) ≤ Real.pi at hy
  dsimp [seamTheta] at *
  split_ifs <;> nlinarith [Real.pi_pos]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. This expresses the finite-star
successor using the angular coordinates rooted at `dR`. -/
theorem ccwSuccessor_iff_seamTheta {D : Type*} (star : Set D) (dir : D → ℂ)
    (dR d e : D) :
    CcwSuccessor star dir d e ↔
      star.Finite ∧ d ∈ star ∧ e ∈ star ∧
        ((e = d ∧ star = {d}) ∨
          (e ≠ d ∧ ∀ f ∈ star, f ≠ d →
            seamThetaTurn (seamTheta dir dR) d e ≤
              seamThetaTurn (seamTheta dir dR) d f)) := by
  unfold CcwSuccessor
  constructor
  · rintro ⟨hfin, hd, he, hcase⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hcase with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · right
      refine ⟨hne, ?_⟩
      intro f hf hfd
      have hle := hmin f hf hfd
      rw [ccwTurn_eq_seamThetaTurn dir dR d e,
        ccwTurn_eq_seamThetaTurn dir dR d f] at hle
      exact hle
  · rintro ⟨hfin, hd, he, hcase⟩
    refine ⟨hfin, hd, he, ?_⟩
    rcases hcase with hsingle | ⟨hne, hmin⟩
    · exact Or.inl hsingle
    · right
      refine ⟨hne, ?_⟩
      intro f hf hfd
      have hle := hmin f hf hfd
      rw [← ccwTurn_eq_seamThetaTurn dir dR d e,
        ← ccwTurn_eq_seamThetaTurn dir dR d f] at hle
      exact hle

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. Restricting a star preserves its
successor when every omitted direction lies past an in-sector anchor. -/
private theorem ccwSuccessor_restrict_of_anchor {D : Type*} (big small : Set D)
    (dir : D → ℂ) (d anchor e : D) (hsub : small ⊆ big)
    (hfin : big.Finite) (hd : d ∈ small) (ha : anchor ∈ small)
    (hda : anchor ≠ d)
    (hfar : ∀ f ∈ big, f ∉ small →
      ccwTurn (dir d) (dir anchor) < ccwTurn (dir d) (dir f)) :
    CcwSuccessor big dir d e ↔ CcwSuccessor small dir d e := by
  have hsmallFin : small.Finite := hfin.subset hsub
  have hbigNe : big ≠ {d} := by
    intro hs
    have had : anchor = d := by simpa [hs] using hsub ha
    exact hda had
  have hsmallNe : small ≠ {d} := by
    intro hs
    have had : anchor = d := by simpa [hs] using ha
    exact hda had
  constructor
  · rintro ⟨_, hdb, heb, hcase⟩
    have hmin : e ≠ d ∧
        ∀ f ∈ big, f ≠ d →
          ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d) (dir f) := by
      rcases hcase with hsingle | hmin
      · exact (hbigNe hsingle.2).elim
      · exact hmin
    have hes : e ∈ small := by
      by_contra hes
      have hle := hmin.2 anchor (hsub ha) hda
      exact (not_lt_of_ge hle) (hfar e heb hes)
    refine ⟨hsmallFin, hd, hes, Or.inr ⟨hmin.1, ?_⟩⟩
    intro f hf hfd
    by_cases hfs : f ∈ small
    · exact hmin.2 f (hsub hfs) hfd
    · have heAnchor := hmin.2 anchor (hsub ha) hda
      exact le_trans heAnchor (le_of_lt (hfar f (hsub hf) hfs))
  · rintro ⟨_, _, _, hcase⟩
    have hmin : e ≠ d ∧
        ∀ f ∈ small, f ≠ d →
          ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d) (dir f) := by
      rcases hcase with hsingle | hmin
      · exact (hsmallNe hsingle.2).elim
      · exact hmin
    have heb : e ∈ big := hsub ‹e ∈ small›
    refine ⟨hfin, hsub hd, heb, Or.inr ⟨hmin.1, ?_⟩⟩
    intro f hf hfd
    by_cases hfs : f ∈ small
    · exact hmin.2 f hfs hfd
    · have hle := hmin.2 anchor ha hda
      exact le_trans hle (le_of_lt (hfar f hf hfs))

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. A direction between the source and
the anchor has a smaller turn than a direction beyond the anchor. -/
private theorem ccwSector_upper_anchor_lt (r d l b : ℂ)
    (hdl : ccwTurn r d < ccwTurn r l) (hlb : ccwTurn r l < ccwTurn r b) :
    ccwTurn d l < ccwTurn d b := by
  have hdl' := ccwTurn_comp_add (a := r) (b := d) (c := l) hdl
  have hdb' := ccwTurn_comp_add (a := r) (b := d) (c := b) (hdl.trans hlb)
  linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. A direction after the root and a
direction before the source have their cyclic order across the root. -/
private theorem ccwSector_lower_anchor_lt {D : Type*} (dir : D → ℂ) (r d a : D)
    (hpos : 0 < ccwTurn (dir r) (dir a))
    (horder : ccwTurn (dir r) (dir a) < ccwTurn (dir r) (dir d))
    (hdr : Complex.arg (dir r) ≠ Complex.arg (dir d))
    (hda : Complex.arg (dir d) ≠ Complex.arg (dir a)) :
    ccwTurn (dir d) (dir r) < ccwTurn (dir d) (dir a) := by
  have hcomp := ccwTurn_comp_add (a := dir r) (b := dir a) (c := dir d) horder
  have hrevdr := ccwTurn_add_reverse (dir d) (dir r) hdr.symm
  have hrevda := ccwTurn_add_reverse (dir d) (dir a) hda
  have hpos' := ccwTurn_pos (dir r) (dir a)
  linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. On the upper side, adding the
lower-sector darts does not change the counterclockwise successor. -/
theorem ccwSuccessor_upper_star_merge {D : Type*} (S U L A B : Set D)
    (dir : D → ℂ) (dR dL : D)
    (hU : U = A ∪ {dR, dL}) (hL : L = B ∪ {dR, dL})
    (hS : S = U ∪ L) (hSfin : S.Finite)
    (_hAB : Disjoint A B) (hAR : dR ∉ A) (hAL : dL ∉ A)
    (hBR : dR ∉ B) (_hBL : dL ∉ B) (hRL : dR ≠ dL)
    (hsectorA : ∀ a ∈ A,
      0 < ccwTurn (dir dR) (dir a) ∧
        ccwTurn (dir dR) (dir a) < ccwTurn (dir dR) (dir dL))
    (hsectorB : ∀ b ∈ B,
      ccwTurn (dir dR) (dir dL) < ccwTurn (dir dR) (dir b))
    (_harg : ∀ x y, x ∈ S → y ∈ S → x ≠ y →
      Complex.arg (dir x) ≠ Complex.arg (dir y))
    (d e : D) (hd : d ∈ A ∪ {dR}) :
    CcwSuccessor S dir d e ↔ CcwSuccessor U dir d e := by
  have hUsub : U ⊆ S := by
    intro x hx
    rw [hS]
    exact Or.inl hx
  have hdU : d ∈ U := by
    rw [hU]
    rcases (show d = dR ∨ d ∈ A by simpa using hd) with hr | ha
    · right
      simp [hr]
    · exact Or.inl ha
  have hAnchor : dL ∈ U := by rw [hU]; simp
  have hR_U : dR ∈ U := by rw [hU]; simp
  have hda : dL ≠ d := by
    intro h
    subst d
    rcases (show dL = dR ∨ dL ∈ A by simpa using hd) with hr | ha
    · exact hRL hr.symm
    · exact hAL ha
  have hfar : ∀ f ∈ S, f ∉ U →
      ccwTurn (dir d) (dir dL) < ccwTurn (dir d) (dir f) := by
    intro f hfS hfU
    have hfL : f ∈ L := by
      have hf : f ∈ U ∨ f ∈ L := by simpa [hS] using hfS
      rcases hf with hfu | hfl
      · exact (hfU hfu).elim
      · exact hfl
    have hfB : f ∈ B := by
      rw [hL] at hfL
      rcases hfL with hfb | hfseam
      · exact hfb
      · have hfseam' : f = dR ∨ f = dL := by simpa using hfseam
        rcases hfseam' with hfr | hfl
        · subst f
          exact (hfU hR_U).elim
        · subst f
          exact (hfU hAnchor).elim
    have hd_cases : d = dR ∨ d ∈ A := by simpa using hd
    rcases hd_cases with rfl | hda'
    · exact hsectorB f hfB
    · exact ccwSector_upper_anchor_lt (dir dR) (dir d) (dir dL) (dir f)
        (hsectorA d hda' |>.2) (hsectorB f hfB)
  exact ccwSuccessor_restrict_of_anchor S U dir d dL e hUsub hSfin hdU
    hAnchor hda hfar

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: merging the upper and lower
stars at a seam vertex); not a paper result. On the lower side, adding the
upper-sector darts does not change the counterclockwise successor. -/
theorem ccwSuccessor_lower_star_merge {D : Type*} (S U L A B : Set D)
    (dir : D → ℂ) (dR dL : D)
    (hU : U = A ∪ {dR, dL}) (hL : L = B ∪ {dR, dL})
    (hS : S = U ∪ L) (hSfin : S.Finite)
    (hAB : Disjoint A B) (_hAR : dR ∉ A) (hAL : dL ∉ A)
    (hBR : dR ∉ B) (hBL : dL ∉ B) (hRL : dR ≠ dL)
    (hsectorA : ∀ a ∈ A,
      0 < ccwTurn (dir dR) (dir a) ∧
        ccwTurn (dir dR) (dir a) < ccwTurn (dir dR) (dir dL))
    (hsectorB : ∀ b ∈ B,
      ccwTurn (dir dR) (dir dL) < ccwTurn (dir dR) (dir b))
    (harg : ∀ x y, x ∈ S → y ∈ S → x ≠ y →
      Complex.arg (dir x) ≠ Complex.arg (dir y))
    (d e : D) (hd : d ∈ B ∪ {dL}) :
    CcwSuccessor S dir d e ↔ CcwSuccessor L dir d e := by
  have hLsub : L ⊆ S := by
    intro x hx
    rw [hS]
    exact Or.inr hx
  have hdL : d ∈ L := by
    rw [hL]
    rcases (show d = dL ∨ d ∈ B by simpa using hd) with hl | hb
    · right
      simp [hl]
    · exact Or.inl hb
  have hAnchor : dR ∈ L := by rw [hL]; simp
  have hR_U : dR ∈ U := by rw [hU]; simp
  have hL_U : dL ∈ U := by rw [hU]; simp
  have hUsub : U ⊆ S := by
    intro x hx
    rw [hS]
    exact Or.inl hx
  have hrootS : dR ∈ S := hUsub hR_U
  have hda : dR ≠ d := by
    intro h
    subst d
    rcases (show dR = dL ∨ dR ∈ B by simpa using hd) with hl | hb
    · exact hRL hl
    · exact hBR hb
  have hfar : ∀ f ∈ S, f ∉ L →
      ccwTurn (dir d) (dir dR) < ccwTurn (dir d) (dir f) := by
    intro f hfS hfL
    have hfU : f ∈ U := by
      have hf : f ∈ U ∨ f ∈ L := by simpa [hS] using hfS
      rcases hf with hfu | hfl
      · exact hfu
      · exact (hfL hfl).elim
    have hfA : f ∈ A := by
      rw [hU] at hfU
      rcases hfU with hfa | hfseam
      · exact hfa
      · have hfseam' : f = dR ∨ f = dL := by simpa using hfseam
        rcases hfseam' with hfr | hfl
        · subst f
          exact (hfL (by rw [hL]; simp)).elim
        · subst f
          exact (hfL (by rw [hL]; simp)).elim
    have hd_cases : d = dL ∨ d ∈ B := by simpa using hd
    have hsourceS : d ∈ S := hLsub hdL
    have hrootArg : Complex.arg (dir dR) ≠ Complex.arg (dir d) :=
      harg dR d hrootS hsourceS hda
    have hsourceArg : Complex.arg (dir d) ≠ Complex.arg (dir f) := by
      have hdf : d ≠ f := by
        intro h
        subst f
        rcases hd_cases with rfl | hb
        · exact hAL hfA
        · exact Set.disjoint_left.mp hAB hfA hb
      exact harg d f hsourceS hfS hdf
    have horder : ccwTurn (dir dR) (dir f) < ccwTurn (dir dR) (dir d) := by
      rcases hd_cases with rfl | hb
      · exact (hsectorA f hfA).2
      · exact (hsectorA f hfA).2.trans (hsectorB d hb)
    exact ccwSector_lower_anchor_lt dir dR d f
      (ccwTurn_pos (dir dR) (dir f)) horder hrootArg hsourceArg
  exact ccwSuccessor_restrict_of_anchor S L dir d dR e hLsub hSfin hdL
    hAnchor hda hfar
