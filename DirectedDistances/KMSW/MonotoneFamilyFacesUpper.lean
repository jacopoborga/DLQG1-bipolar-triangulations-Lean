/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneSeamRegions

public section

namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology Classical

variable (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

local notation "P" => monotoneFamilyDrawing w hfin (monotone_family_all w)
local notation "f" => seamFun w h hfin
local notation "Upper" => (Set.ofPred (fun z : ℂ => f (Complex.re z) < Complex.im z))
local notation "Lower" => (Set.ofPred (fun z : ℂ => Complex.im z < f (Complex.re z)))





theorem lower_isConnected : IsConnected Lower := by
  let T : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2 + f p.1⟩
  have hT : Continuous T :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.add
        ((seamFun_continuous w h hfin).comp continuous_fst)))
  have heq : T '' ((univ : Set ℝ) ×ˢ Iio (0 : ℝ)) = Lower := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨_, hy⟩, rfl⟩
      change y + f x < f x
      have hy' : y < 0 := hy
      linarith only [hy']
    · intro hz
      refine ⟨(z.re, z.im - f z.re), ⟨mem_univ _, sub_neg.mpr hz⟩, ?_⟩
      apply Complex.ext
      · rfl
      · change z.im - f z.re + f z.re = z.im
        exact sub_add_cancel _ _
  rw [← heq]
  exact (isConnected_univ.prod (isConnected_Iio : IsConnected (Iio (0 : ℝ)))).image
    T hT.continuousOn





theorem lower_disjoint_image : Disjoint Lower (P).image := by
  apply disjoint_left.mpr
  intro z hz hzP
  exact (show z.im < f z.re from hz).not_ge
    (monotoneFamilyDrawing_above_seam w h hfin hzP)





theorem graph_subset_image : {z : ℂ | z.im = f z.re} ⊆ (P).image := by
  intro z hz
  rw [seamFun_graph w h hfin] at hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  exact Or.inr ⟨futureMapBoundaryDart w h k, hk⟩





theorem preconnected_upper_of_meets (S : Set ℂ) (hS : S ⊆ (P).imageᶜ)
    (hc : IsPreconnected S) (hmeet : (S ∩ Upper).Nonempty) : S ⊆ Upper := by
  obtain ⟨a, ha, hau⟩ := hmeet
  intro b hb
  by_contra hbu
  have hble : b.im ≤ f b.re := not_lt.mp hbu
  obtain ⟨z, hz, heq⟩ := hc.intermediate_value₂ hb ha
    Complex.continuous_im.continuousOn
    ((seamFun_continuous w h hfin).comp Complex.continuous_re).continuousOn
    hble hau.le
  exact (hS hz) (graph_subset_image w h hfin heq)





theorem face_subset_upper_or_lower (F : (P).Face) :
    F.val ⊆ Upper ∨ F.val = Lower := by
  obtain ⟨a, ha, hFa⟩ := F.property
  have hcomp : F.val ⊆ (P).imageᶜ := by
    rw [hFa]
    exact connectedComponentIn_subset _ _
  have hc : IsPreconnected F.val := by
    rw [hFa]
    exact isPreconnected_connectedComponentIn
  by_cases hmeet : (F.val ∩ Upper).Nonempty
  · exact Or.inl (preconnected_upper_of_meets w h hfin F.val hcomp hc hmeet)
  · right
    have hlow : F.val ⊆ Lower := by
      intro z hz
      have hle : z.im ≤ f z.re := not_lt.mp (fun hu => hmeet ⟨z, hz, hu⟩)
      have hne : z.im ≠ f z.re := fun he =>
        (hcomp hz) (graph_subset_image w h hfin he)
      exact lt_of_le_of_ne hle hne
    apply subset_antisymm hlow
    have haF : a ∈ F.val := hFa ▸ mem_connectedComponentIn ha
    have hlcomp : Lower ⊆ (P).imageᶜ := fun _ hz =>
      disjoint_left.mp (lower_disjoint_image w h hfin) hz
    rw [hFa]
    exact (lower_isConnected w h hfin).isPreconnected.subset_connectedComponentIn
      (hlow haF) hlcomp





theorem unbounded_face_eq_lower (F : (P).Face) : (P).IsUnbounded F ↔ F.val = Lower := by
  have hunbounded (G : (P).Face) (hG : G.val = Lower) : (P).IsUnbounded G := by
    intro R
    let z : ℂ := ⟨R + 1, f (R + 1) - 1⟩
    refine ⟨z, ?_, ?_⟩
    · rw [hG]
      change f (R + 1) - 1 < f (R + 1)
      linarith
    · have hre : R + 1 ≤ ‖z‖ :=
        (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
      linarith only [hre]
  constructor
  · intro hF
    let a : ℂ := ⟨0, f 0 - 1⟩
    have hal : a ∈ Lower := by change f 0 - 1 < f 0; linarith
    have ha : a ∉ (P).image := disjoint_left.mp (lower_disjoint_image w h hfin) hal
    let G : (P).Face := ⟨connectedComponentIn (P).imageᶜ a, a, ha, rfl⟩
    have haG : a ∈ G.val := mem_connectedComponentIn ha
    have hG : G.val = Lower := by
      rcases face_subset_upper_or_lower w h hfin G with hGu | hGl
      · exact False.elim ((show a.im < f a.re from hal).not_ge
          (show f a.re ≤ a.im from (hGu haG).le))
      · exact hGl
    obtain ⟨U, _, huniq, _⟩ :=
      monotoneFamilyDrawing_faceClassification_twoSided w hfin h
    have hFG : F = G := (huniq F hF).trans (huniq G (hunbounded G hG)).symm
    exact hFG ▸ hG
  · exact hunbounded F





theorem boundedFace_subset_upper (F : (P).Face) (hF : ¬ (P).IsUnbounded F) :
    F.val ⊆ Upper := by
  rcases face_subset_upper_or_lower w h hfin F with hu | hl
  · exact hu
  · exact False.elim (hF ((unbounded_face_eq_lower w h hfin F).mpr hl))





theorem mem_boundedFace_of_upper (z : ℂ) (hz : z ∈ Upper) (hzP : z ∉ (P).image) :
    ∃ F : (P).Face, ¬ (P).IsUnbounded F ∧ z ∈ F.val ∧
      connectedComponentIn (P).imageᶜ z = F.val := by
  let F : (P).Face := ⟨connectedComponentIn (P).imageᶜ z, z, hzP, rfl⟩
  have hzF : z ∈ F.val := mem_connectedComponentIn hzP
  refine ⟨F, ?_, hzF, rfl⟩
  intro hF
  have heq := (unbounded_face_eq_lower w h hfin F).mp hF
  have hzl : z ∈ Lower := heq ▸ hzF
  exact (show z.im < f z.re from hzl).not_ge
    (show f z.re ≤ z.im from hz.le)

end DirectedDistances.KMSW
