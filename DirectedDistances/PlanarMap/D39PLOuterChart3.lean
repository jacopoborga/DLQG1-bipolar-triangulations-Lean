/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLOuterChart2
public import DirectedDistances.PlanarMap.D39PLSimpleArcParam
public import DirectedDistances.PlanarMap.D39PLSquareCone2
public import DirectedDistances.PlanarMap.D39PLDrawingHomeomorph3

/-! Helpers toward Proposition 5.16: concrete simple-arc and square-exterior
and integration belong to the sole coordinator. -/

public section
noncomputable section
namespace DirectedDistances.PlanarMap
open Set Topology

/-- Helper toward Proposition 5.16: the simple-arc parameterization ingredient
holds with both prescribed endpoints. -/
theorem simpleArcParamStatement_holds : SimpleArcParamStatement := by
  intro p hp hpne
  exact p.exists_Icc_homeomorph_image hp hpne

/-- Helper toward Proposition 5.16: the square-cone ingredient holds for every
positive pair of radii and every prescribed boundary homeomorphism. -/
theorem squareConeStatement_holds : SquareConeStatement := by
  intro R R' hR hR' g
  exact Polyline.exists_squareOutsideExtension R R' hR hR' g

/-- Helper toward Proposition 5.16: the collisions of an arc family are
determined by its distinct vertices when different arcs meet only at endpoints. -/
theorem parameterized_arcs_collision_iff_of_vertices
    {ι κ : Type*} (A B : ι → Set ℂ) (v w : κ → ℂ)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (lo hi : ι → κ)
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hphi₀ : ∀ i, (phi i ⟨-1, by norm_num⟩ : ℂ) = v (lo i))
    (hphi₁ : ∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) = v (hi i))
    (hpsi₀ : ∀ i, (psi i ⟨-1, by norm_num⟩ : ℂ) = w (lo i))
    (hpsi₁ : ∀ i, (psi i ⟨1, by norm_num⟩ : ℂ) = w (hi i))
    (hA : ∀ i j, i ≠ j → A i ∩ A j ⊆ {v (lo i), v (hi i)})
    (hB : ∀ i j, i ≠ j → B i ∩ B j ⊆ {w (lo i), w (hi i)}) :
    ∀ i j u t,
      (phi i u : ℂ) = (phi j t : ℂ) ↔ (psi i u : ℂ) = (psi j t : ℂ) := by
  have forward {C D : ι → Set ℂ} {z z' : κ → ℂ}
      (hz : Function.Injective z)
      (f : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ C i)
      (g : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ D i)
      (hf₀ : ∀ i, (f i ⟨-1, by norm_num⟩ : ℂ) = z (lo i))
      (hf₁ : ∀ i, (f i ⟨1, by norm_num⟩ : ℂ) = z (hi i))
      (hg₀ : ∀ i, (g i ⟨-1, by norm_num⟩ : ℂ) = z' (lo i))
      (hg₁ : ∀ i, (g i ⟨1, by norm_num⟩ : ℂ) = z' (hi i))
      (hC : ∀ i j, i ≠ j → C i ∩ C j ⊆ {z (lo i), z (hi i)})
      (i j : ι) (u t : Icc (-1 : ℝ) 1)
      (h : (f i u : ℂ) = (f j t : ℂ)) :
      (g i u : ℂ) = (g j t : ℂ) := by
    classical
    by_cases hij : i = j
    · subst j
      exact congrArg (fun r => (g i r : ℂ)) ((f i).injective (Subtype.ext h))
    have hui := hC i j hij ⟨(f i u).property, h.symm ▸ (f j t).property⟩
    have htj := hC j i (Ne.symm hij) ⟨(f j t).property, h ▸ (f i u).property⟩
    have hu : u = ⟨-1, by norm_num⟩ ∨ u = ⟨1, by norm_num⟩ := by
      rcases hui with h₀ | h₁
      · exact Or.inl ((f i).injective (Subtype.ext (h₀.trans (hf₀ i).symm)))
      · exact Or.inr ((f i).injective (Subtype.ext (h₁.trans (hf₁ i).symm)))
    have ht : t = ⟨-1, by norm_num⟩ ∨ t = ⟨1, by norm_num⟩ := by
      rcases htj with h₀ | h₁
      · exact Or.inl ((f j).injective (Subtype.ext (h₀.trans (hf₀ j).symm)))
      · exact Or.inr ((f j).injective (Subtype.ext (h₁.trans (hf₁ j).symm)))
    rcases hu with rfl | rfl <;> rcases ht with rfl | rfl
    · rw [hf₀, hf₀] at h
      rw [hg₀, hg₀, hz h]
    · rw [hf₀, hf₁] at h
      rw [hg₀, hg₁, hz h]
    · rw [hf₁, hf₀] at h
      rw [hg₁, hg₀, hz h]
    · rw [hf₁, hf₁] at h
      rw [hg₁, hg₁, hz h]
  intro i j u t
  exact ⟨forward hv phi psi hphi₀ hphi₁ hpsi₀ hpsi₁ hA i j u t,
    forward hw psi phi hpsi₀ hpsi₁ hphi₀ hphi₁ hB i j u t⟩

/-- Helper toward Proposition 5.16: the six arcs of an annulus partition
have four distinct vertices and distinct arcs intersect only at their endpoints. -/
theorem Polyline.annulus_arcs_vertex_data
    (C Q : Set ℂ) (s t al be sg ta : Polyline)
    (hCQ : Disjoint C Q) (hst : Disjoint s.image t.image)
    (hsc : s.image ∩ C = {s.start}) (htc : t.image ∩ C = {t.start})
    (hsQ : s.image ∩ Q = {s.finish}) (htQ : t.image ∩ Q = {t.finish})
    (hi : al.image ∪ be.image = C)
    (hii : al.image ∩ be.image = {s.start, t.start})
    (ho : sg.image ∪ ta.image = Q)
    (hoi : sg.image ∩ ta.image = {s.finish, t.finish})
    (hne₀ : s.start ≠ t.start) (hne₁ : s.finish ≠ t.finish) :
    let a : Fin 6 → Polyline := ![al, be, sg, ta, s, t]
    let v : Fin 4 → ℂ := ![s.start, t.start, s.finish, t.finish]
    let lo : Fin 6 → Fin 4 := ![0, 0, 2, 2, 0, 1]
    let hi : Fin 6 → Fin 4 := ![1, 1, 3, 3, 2, 3]
    Function.Injective v ∧
      ∀ i j, i ≠ j → (a i).image ∩ (a j).image ⊆ {v (lo i), v (hi i)} := by
  dsimp only
  have hsC : s.start ∈ C := by
    have h : s.start ∈ s.image ∩ C := hsc.symm ▸ mem_singleton _
    exact h.2
  have htC : t.start ∈ C := by
    have h : t.start ∈ t.image ∩ C := htc.symm ▸ mem_singleton _
    exact h.2
  have hsO : s.finish ∈ Q := by
    have h : s.finish ∈ s.image ∩ Q := hsQ.symm ▸ mem_singleton _
    exact h.2
  have htO : t.finish ∈ Q := by
    have h : t.finish ∈ t.image ∩ Q := htQ.symm ▸ mem_singleton _
    exact h.2
  have hal : al.image ⊆ C := fun _ hz => hi ▸ Or.inl hz
  have hbe : be.image ⊆ C := fun _ hz => hi ▸ Or.inr hz
  have hsg : sg.image ⊆ Q := fun _ hz => ho ▸ Or.inl hz
  have hta : ta.image ⊆ Q := fun _ hz => ho ▸ Or.inr hz
  have hCQ' := Set.disjoint_left.mp hCQ
  have hst' := Set.disjoint_left.mp hst
  have hsc' (z) (hz : z ∈ s.image) (hC : z ∈ C) : z = s.start := by
    exact mem_singleton_iff.mp (hsc ▸ show z ∈ s.image ∩ C from ⟨hz, hC⟩)
  have htc' (z) (hz : z ∈ t.image) (hC : z ∈ C) : z = t.start := by
    exact mem_singleton_iff.mp (htc ▸ show z ∈ t.image ∩ C from ⟨hz, hC⟩)
  have hsQ' (z) (hz : z ∈ s.image) (hQ : z ∈ Q) : z = s.finish := by
    exact mem_singleton_iff.mp (hsQ ▸ show z ∈ s.image ∩ Q from ⟨hz, hQ⟩)
  have htQ' (z) (hz : z ∈ t.image) (hQ : z ∈ Q) : z = t.finish := by
    exact mem_singleton_iff.mp (htQ ▸ show z ∈ t.image ∩ Q from ⟨hz, hQ⟩)
  have hii' (z) (hz : z ∈ al.image) (hw : z ∈ be.image) :
      z = s.start ∨ z = t.start := by
    have hm : z ∈ al.image ∩ be.image := ⟨hz, hw⟩
    rwa [hii, mem_insert_iff, mem_singleton_iff] at hm
  have hoi' (z) (hz : z ∈ sg.image) (hw : z ∈ ta.image) :
      z = s.finish ∨ z = t.finish := by
    have hm : z ∈ sg.image ∩ ta.image := ⟨hz, hw⟩
    rwa [hoi, mem_insert_iff, mem_singleton_iff] at hm
  have cross {x y : ℂ} (hx : x ∈ C) (hy : y ∈ Q) : x ≠ y :=
    fun h => hCQ' hx (h.symm ▸ hy)
  have h02 := cross hsC hsO
  have h03 := cross hsC htO
  have h12 := cross htC hsO
  have h13 := cross htC htO
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> (try rfl) <;>
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at hij <;>
      apply False.elim <;> first
      | exact hne₀ hij
      | exact hne₀ hij.symm
      | exact hne₁ hij
      | exact hne₁ hij.symm
      | exact h02 hij
      | exact h02 hij.symm
      | exact h03 hij
      | exact h03 hij.symm
      | exact h12 hij
      | exact h12 hij.symm
      | exact h13 hij
      | exact h13 hij.symm
  · intro i j hij z hz
    fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim) <;>
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at hz ⊢
    · exact hii' z hz.1 hz.2
    · exact (hCQ' (hal hz.1) (hsg hz.2)).elim
    · exact (hCQ' (hal hz.1) (hta hz.2)).elim
    · exact Or.inl (hsc' z hz.2 (hal hz.1))
    · exact Or.inr (htc' z hz.2 (hal hz.1))
    · exact hii' z hz.2 hz.1
    · exact (hCQ' (hbe hz.1) (hsg hz.2)).elim
    · exact (hCQ' (hbe hz.1) (hta hz.2)).elim
    · exact Or.inl (hsc' z hz.2 (hbe hz.1))
    · exact Or.inr (htc' z hz.2 (hbe hz.1))
    · exact (hCQ' (hal hz.2) (hsg hz.1)).elim
    · exact (hCQ' (hbe hz.2) (hsg hz.1)).elim
    · exact hoi' z hz.1 hz.2
    · exact Or.inl (hsQ' z hz.2 (hsg hz.1))
    · exact Or.inr (htQ' z hz.2 (hsg hz.1))
    · exact (hCQ' (hal hz.2) (hta hz.1)).elim
    · exact (hCQ' (hbe hz.2) (hta hz.1)).elim
    · exact hoi' z hz.2 hz.1
    · exact Or.inl (hsQ' z hz.2 (hta hz.1))
    · exact Or.inr (htQ' z hz.2 (hta hz.1))
    · exact Or.inl (hsc' z hz.1 (hal hz.2))
    · exact Or.inl (hsc' z hz.1 (hbe hz.2))
    · exact Or.inr (hsQ' z hz.1 (hsg hz.2))
    · exact Or.inr (hsQ' z hz.1 (hta hz.2))
    · exact (hst' hz.1 hz.2).elim
    · exact Or.inl (htc' z hz.1 (hal hz.2))
    · exact Or.inl (htc' z hz.1 (hbe hz.2))
    · exact Or.inr (htQ' z hz.1 (hsg hz.2))
    · exact Or.inr (htQ' z hz.1 (hta hz.2))
    · exact (hst' hz.2 hz.1).elim

/-- Helper toward Proposition 5.16: a cyclically simple polygon has a closed
annulus partition whose six arcs are parameterized once, with all endpoint
collisions certified by four distinct vertices. -/
theorem Polyline.exists_closed_annulus_partition_with_arc_parameters
    (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ (R : ℝ) (p q : Polyline) (a : Fin 6 → Polyline) (v : Fin 4 → ℂ)
      (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ (a i).image),
      0 < R ∧ (enclosingSquare R).IsCyclicSimple ∧
      closure c.inside ⊆ (enclosingSquare R).inside ∧
      p.IsCyclicSimple ∧ q.IsCyclicSimple ∧
      closure p.inside ∪ closure q.inside =
        closure c.outside ∩ closure (enclosingSquare R).inside ∧
      closure p.inside ∩ closure q.inside = (a 4).image ∪ (a 5).image ∧
      (a 0).image ∪ (a 1).image = c.image ∧
      (a 2).image ∪ (a 3).image = (enclosingSquare R).image ∧
      p.image = (a 0).image ∪ (a 4).image ∪ (a 2).image ∪ (a 5).image ∧
      q.image = (a 1).image ∪ (a 4).image ∪ (a 3).image ∪ (a 5).image ∧
      Function.Injective v ∧
      (∀ i, (phi i ⟨-1, by norm_num⟩ : ℂ) = v (![0, 0, 2, 2, 0, 1] i)) ∧
      (∀ i, (phi i ⟨1, by norm_num⟩ : ℂ) = v (![1, 1, 3, 3, 2, 3] i)) ∧
      ∀ i j, i ≠ j → (a i).image ∩ (a j).image ⊆
        {v (![0, 0, 2, 2, 0, 1] i), v (![1, 1, 3, 3, 2, 3] i)} := by
  obtain ⟨R, s, t, p, q, hR, hQ, hnest, hs, ht, hst, hsc, htc, hsQ, htQ,
    hp, hq, hcover, hinter, _, al, be, sg, ta,
    hal, hbe, hsg, hta, _, _, _, _, hal₀, hal₁, hbe₀, hbe₁,
    hi, hii, hsg₀, hsg₁, hta₀, hta₁, ho, hoi, hne₀, hne₁,
    halne, hbene, hsgne, htane, hpim, hqim⟩ :=
    c.exists_closed_annulus_partition_with_arcs hc
  have hCQ : Disjoint c.image (enclosingSquare R).image := by
    apply Set.disjoint_left.mpr
    intro z hz hw
    exact (hnest (c.image_subset_closure_inside_cyclic hc hz)).1 hw
  obtain ⟨hv, hmeet⟩ := annulus_arcs_vertex_data c.image (enclosingSquare R).image
    s t al be sg ta hCQ hst hsc htc hsQ htQ hi hii ho hoi hne₀ hne₁
  have hsne : s.start ≠ s.finish := by
    intro h
    apply hCQ.notMem_of_mem_left
      (show s.start ∈ c.image from (hsc.symm ▸ mem_singleton s.start).2)
    exact h.symm ▸ (show s.finish ∈ (enclosingSquare R).image from
      (hsQ.symm ▸ mem_singleton s.finish).2)
  have htne : t.start ≠ t.finish := by
    intro h
    apply hCQ.notMem_of_mem_left
      (show t.start ∈ c.image from (htc.symm ▸ mem_singleton t.start).2)
    exact h.symm ▸ (show t.finish ∈ (enclosingSquare R).image from
      (htQ.symm ▸ mem_singleton t.finish).2)
  let a : Fin 6 → Polyline := ![al, be, sg, ta, s, t]
  let v : Fin 4 → ℂ := ![s.start, t.start, s.finish, t.finish]
  have ha (i) : (a i).IsSimple := by
    fin_cases i <;> first | exact hal | exact hbe | exact hsg | exact hta | exact hs | exact ht
  have hane (i) : (a i).start ≠ (a i).finish := by
    fin_cases i <;> first
    | exact halne
    | exact hbene
    | exact hsgne
    | exact htane
    | exact hsne
    | exact htne
  choose phi hphi₀ hphi₁ using fun i => (a i).exists_Icc_homeomorph_image (ha i) (hane i)
  refine ⟨R, p, q, a, v, phi, hR, hQ, hnest, hp, hq, hcover, hinter,
    hi, ho, hpim, hqim, hv, ?_, ?_, hmeet⟩
  · intro i
    rw [hphi₀]
    fin_cases i <;> first | exact hal₀ | exact hbe₀ | exact hsg₀ | exact hta₀ | rfl
  · intro i
    rw [hphi₁]
    fin_cases i <;> first | exact hal₁ | exact hbe₁ | exact hsg₁ | exact hta₁ | rfl

/-- Helper toward Proposition 5.16: restricting a planar homeomorphism to
corresponding subsets preserves the ambient complex coordinates. -/
@[expose] def restrictPlanarHomeomorph
    (S T A B : Set ℂ) (hAS : A ⊆ S) (hBT : B ⊆ T)
    (F : S ≃ₜ T) (hmem : ∀ x : S, (F x : ℂ) ∈ B ↔ (x : ℂ) ∈ A) : A ≃ₜ B :=
  (subsetSubtypeHomeomorph A S hAS).trans
    ((F.subtype (fun x => (hmem x).symm)).trans
      (subsetSubtypeHomeomorph B T hBT).symm)

/-- Helper toward Proposition 5.16: extensions on closed pieces paste when
their overlaps are boundary subsets of one common skeleton homeomorphism. -/
theorem exists_homeomorph_of_closed_pieces_with_skeleton
    {ι : Type*} [Finite ι] (S T B C : Set ℂ)
    (s t b d : ι → Set ℂ)
    (hs : ∀ i, IsClosed (s i)) (ht : ∀ i, IsClosed (t i))
    (hcover : ⋃ i, s i = S) (hcover' : ⋃ i, t i = T)
    (hb : ∀ i, b i ⊆ s i) (hd : ∀ i, d i ⊆ t i)
    (hbB : ∀ i, b i ⊆ B) (hdC : ∀ i, d i ⊆ C)
    (hinter : ∀ i j, i ≠ j → s i ∩ s j ⊆ b i)
    (hinter' : ∀ i j, i ≠ j → t i ∩ t j ⊆ d i)
    (F : B ≃ₜ C)
    (hmem : ∀ i (x : B), (F x : ℂ) ∈ d i ↔ (x : ℂ) ∈ b i)
    (e : ∀ i, s i ≃ₜ t i)
    (he : ∀ i (x : b i),
      (e i ⟨x, hb i x.property⟩ : ℂ) = (F ⟨x, hbB i x.property⟩ : ℂ)) :
    ∃ H : S ≃ₜ T, ∀ i (x : s i),
      (H ⟨x, hcover ▸ mem_iUnion.mpr ⟨i, x.property⟩⟩ : ℂ) = (e i x : ℂ) := by
  classical
  let s' (i) : Set S := {x | (x : ℂ) ∈ s i}
  let t' (i) : Set T := {x | (x : ℂ) ∈ t i}
  have hsS (i) : s i ⊆ S := fun _ hx => hcover ▸ mem_iUnion.mpr ⟨i, hx⟩
  have htT (i) : t i ⊆ T := fun _ hx => hcover' ▸ mem_iUnion.mpr ⟨i, hx⟩
  let ei (i) : s' i ≃ₜ t' i :=
    (subsetSubtypeHomeomorph (s i) S (hsS i)).symm.trans
      ((e i).trans (subsetSubtypeHomeomorph (t i) T (htT i)))
  have coverS : ⋃ i, s' i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ i, (x : ℂ) ∈ s i
    exact mem_iUnion.mp (hcover.symm ▸ x.property)
  have coverT : ⋃ i, t' i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    change ∃ i, (x : ℂ) ∈ t i
    exact mem_iUnion.mp (hcover'.symm ▸ x.property)
  have inverse (i) (y : d i) :
      ((e i).symm ⟨y, hd i y.property⟩ : ℂ) =
        (F.symm ⟨y, hdC i y.property⟩ : ℂ) := by
    let x := F.symm ⟨y, hdC i y.property⟩
    have hx : (x : ℂ) ∈ b i := (hmem i x).mp (by
      change (F (F.symm _) : ℂ) ∈ d i
      rw [F.apply_symm_apply]
      exact y.property)
    have heq : e i ⟨x, hb i hx⟩ = ⟨y, hd i y.property⟩ := by
      apply Subtype.ext
      exact (he i ⟨x, hx⟩).trans (congrArg Subtype.val (F.apply_symm_apply _))
    exact congrArg Subtype.val ((e i).symm_apply_eq.mpr heq.symm)
  obtain ⟨H, hH⟩ := exists_homeomorph_of_finite_closed_covers s' t'
    (fun i => (hs i).preimage continuous_subtype_val)
    (fun i => (ht i).preimage continuous_subtype_val) coverS coverT ei
    (by
      intro i j x hi hj
      by_cases hij : i = j
      · subst j; rfl
      have hxi := hinter i j hij ⟨hi, hj⟩
      have hxj := hinter j i (Ne.symm hij) ⟨hj, hi⟩
      apply Subtype.ext
      exact (he i ⟨x, hxi⟩).trans (he j ⟨x, hxj⟩).symm)
    (by
      intro i j y hi hj
      by_cases hij : i = j
      · subst j; rfl
      have hyi := hinter' i j hij ⟨hi, hj⟩
      have hyj := hinter' j i (Ne.symm hij) ⟨hj, hi⟩
      apply Subtype.ext
      exact (inverse i ⟨y, hyi⟩).trans (inverse j ⟨y, hyj⟩).symm)
  refine ⟨H, fun i x => ?_⟩
  exact congrArg Subtype.val (hH i ((subsetSubtypeHomeomorph (s i) S (hsS i)) x))

/-- Helper toward Proposition 5.16: a synchronized map of the union of arcs
preserves membership in every individual arc, including both slit images. -/
theorem exists_arc_union_homeomorph_with_membership
    {ι : Type*} [Finite ι] (A B : ι → Set ℂ)
    (hA : ∀ i, IsClosed (A i)) (hB : ∀ i, IsClosed (B i))
    (phi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ A i)
    (psi : ∀ i, Icc (-1 : ℝ) 1 ≃ₜ B i)
    (hcollision : ∀ i j u t,
      (phi i u : ℂ) = (phi j t : ℂ) ↔ (psi i u : ℂ) = (psi j t : ℂ)) :
    ∃ F : (⋃ i, A i) ≃ₜ (⋃ i, B i),
      (∀ i u, (F ⟨phi i u, mem_iUnion.mpr ⟨i, (phi i u).property⟩⟩ : ℂ) =
        (psi i u : ℂ)) ∧
      ∀ i (x : ⋃ i, A i), (F x : ℂ) ∈ B i ↔ (x : ℂ) ∈ A i := by
  obtain ⟨F, hF⟩ := exists_homeomorph_of_finite_parameterized_arcs A B
    (⋃ i, A i) (⋃ i, B i) hA hB rfl rfl phi psi hcollision
  refine ⟨F, hF, fun i => ?_⟩
  apply homeomorph_mem_iff_of_boundary_values _ _ (A i) (B i)
    (fun _ hx => mem_iUnion.mpr ⟨i, hx⟩)
    (fun _ hx => mem_iUnion.mpr ⟨i, hx⟩) F ((phi i).symm.trans (psi i))
  intro x
  obtain ⟨u, rfl⟩ := (phi i).surjective x
  simpa only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using hF i u

/-- Helper toward Proposition 5.16: the three exterior-chart pieces meet
only on their corresponding polygon boundaries. -/
theorem Polyline.three_outer_pieces_boundary_overlap
    (p q Q : Polyline) (hp : p.IsCyclicSimple) (hq : q.IsCyclicSimple)
    (hQ : Q.IsCyclicSimple)
    (hsubp : closure p.inside ⊆ closure Q.inside)
    (hsubq : closure q.inside ⊆ closure Q.inside)
    (hpq : closure p.inside ∩ closure q.inside ⊆ p.image ∩ q.image) :
    let s : Fin 3 → Set ℂ := ![closure p.inside, closure q.inside, closure Q.outside]
    let b : Fin 3 → Set ℂ := ![p.image, q.image, Q.image]
    ∀ i j, i ≠ j → s i ∩ s j ⊆ b i := by
  have hpQ := p.closed_inside_inter_closed_outside_eq_boundary_inter Q hp hQ hsubp
  have hqQ := q.closed_inside_inter_closed_outside_eq_boundary_inter Q hq hQ hsubq
  dsimp only
  intro i j hij z hz
  fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim) <;>
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at hz ⊢
  · exact (hpq hz).1
  · exact (hpQ ▸ hz).1
  · exact (hpq ⟨hz.2, hz.1⟩).2
  · exact (hqQ ▸ hz).1
  · exact (hpQ ▸ show z ∈ closure p.inside ∩ closure Q.outside from ⟨hz.2, hz.1⟩).2
  · exact (hqQ ▸ show z ∈ closure q.inside ∩ closure Q.outside from ⟨hz.2, hz.1⟩).2

/-- Helper toward Proposition 5.16: every cyclically simple polygon has a
closed exterior chart to the fixed unit square exterior, carrying exactly its
boundary to the square boundary. -/
theorem Polyline.exists_outer_chart (c : Polyline) (hc : c.IsCyclicSimple) :
    ∃ Phi : closure c.outside ≃ₜ closure (enclosingSquare 1).outside,
      ∀ x : closure c.outside,
        (Phi x : ℂ) ∈ (enclosingSquare 1).image ↔ (x : ℂ) ∈ c.image := by
  let c' := enclosingSquare 1
  have hc' : c'.IsCyclicSimple := enclosingSquare_isCyclicSimple 1 (by norm_num)
  obtain ⟨R, p, q, a, v, phi, hR, hQ, hnest, hp, hq, hcover, hinter,
    hi, ho, hpim, hqim, hv, hphi₀, hphi₁, hmeet⟩ :=
    c.exists_closed_annulus_partition_with_arc_parameters hc
  obtain ⟨R', p', q', a', v', psi, hR', hQ', hnest', hp', hq', hcover', hinter',
    hi', ho', hpim', hqim', hv', hpsi₀, hpsi₁, hmeet'⟩ :=
    c'.exists_closed_annulus_partition_with_arc_parameters hc'
  let S := ⋃ i, (a i).image
  let T := ⋃ i, (a' i).image
  obtain ⟨F, _, hmem⟩ := exists_arc_union_homeomorph_with_membership
    (fun i => (a i).image) (fun i => (a' i).image)
    (fun i => (a i).isCompact_image.isClosed) (fun i => (a' i).isCompact_image.isClosed)
    phi psi (parameterized_arcs_collision_iff_of_vertices _ _ v v' hv hv'
      ![0, 0, 2, 2, 0, 1] ![1, 1, 3, 3, 2, 3]
      phi psi hphi₀ hphi₁ hpsi₀ hpsi₁ hmeet hmeet')
  have haS (i) : (a i).image ⊆ S := fun _ hz => mem_iUnion.mpr ⟨i, hz⟩
  have haT (i) : (a' i).image ⊆ T := fun _ hz => mem_iUnion.mpr ⟨i, hz⟩
  have hpS : p.image ⊆ S := by
    rw [hpim]
    exact union_subset (union_subset (union_subset (haS 0) (haS 4)) (haS 2)) (haS 5)
  have hqS : q.image ⊆ S := by
    rw [hqim]
    exact union_subset (union_subset (union_subset (haS 1) (haS 4)) (haS 3)) (haS 5)
  have hQS : (enclosingSquare R).image ⊆ S := by
    rw [← ho]; exact union_subset (haS 2) (haS 3)
  have hcS : c.image ⊆ S := by
    rw [← hi]; exact union_subset (haS 0) (haS 1)
  have hpT : p'.image ⊆ T := by
    rw [hpim']
    exact union_subset (union_subset (union_subset (haT 0) (haT 4)) (haT 2)) (haT 5)
  have hqT : q'.image ⊆ T := by
    rw [hqim']
    exact union_subset (union_subset (union_subset (haT 1) (haT 4)) (haT 3)) (haT 5)
  have hQT : (enclosingSquare R').image ⊆ T := by
    rw [← ho']; exact union_subset (haT 2) (haT 3)
  have hcT : c'.image ⊆ T := by
    rw [← hi']; exact union_subset (haT 0) (haT 1)
  have memp (x : S) : (F x : ℂ) ∈ p'.image ↔ (x : ℂ) ∈ p.image := by
    rw [hpim, hpim']
    simp only [mem_union, hmem]
  have memq (x : S) : (F x : ℂ) ∈ q'.image ↔ (x : ℂ) ∈ q.image := by
    rw [hqim, hqim']
    simp only [mem_union, hmem]
  have memQ (x : S) : (F x : ℂ) ∈ (enclosingSquare R').image ↔
      (x : ℂ) ∈ (enclosingSquare R).image := by
    rw [← ho, ← ho']
    simp only [mem_union, hmem]
  have memc (x : S) : (F x : ℂ) ∈ c'.image ↔ (x : ℂ) ∈ c.image := by
    rw [← hi, ← hi']
    simp only [mem_union, hmem]
  let fp := restrictPlanarHomeomorph S T p.image p'.image hpS hpT F memp
  let fq := restrictPlanarHomeomorph S T q.image q'.image hqS hqT F memq
  let fQ := restrictPlanarHomeomorph S T (enclosingSquare R).image
    (enclosingSquare R').image hQS hQT F memQ
  let fc := restrictPlanarHomeomorph S T c.image c'.image hcS hcT F memc
  obtain ⟨Hp, hHp⟩ := p.exists_inside_homeomorph_extending_boundary p' hp hp' fp
  obtain ⟨Hq, hHq⟩ := q.exists_inside_homeomorph_extending_boundary q' hq hq' fq
  obtain ⟨E, hE⟩ := Polyline.exists_squareOutsideExtension R R' hR hR' fQ
  let pieces : Fin 3 → Set ℂ :=
    ![closure p.inside, closure q.inside, closure (enclosingSquare R).outside]
  let pieces' : Fin 3 → Set ℂ :=
    ![closure p'.inside, closure q'.inside, closure (enclosingSquare R').outside]
  let bd : Fin 3 → Set ℂ := ![p.image, q.image, (enclosingSquare R).image]
  let bd' : Fin 3 → Set ℂ := ![p'.image, q'.image, (enclosingSquare R').image]
  have closedpieces (i) : IsClosed (pieces i) := by
    fin_cases i <;> exact isClosed_closure
  have closedpieces' (i) : IsClosed (pieces' i) := by
    fin_cases i <;> exact isClosed_closure
  have covers : ⋃ i, pieces i = closure c.outside := by
    have hh := c.closed_outside_eq_cut_pieces_union (enclosingSquare R) p q hc hQ hnest hcover
    rw [hh]
    ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hz⟩
      fin_cases i
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · rintro ((hz | hz) | hz)
      · exact ⟨0, hz⟩
      · exact ⟨1, hz⟩
      · exact ⟨2, hz⟩
  have covers' : ⋃ i, pieces' i = closure c'.outside := by
    have hh := c'.closed_outside_eq_cut_pieces_union (enclosingSquare R') p' q' hc' hQ' hnest' hcover'
    rw [hh]
    ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hz⟩
      fin_cases i
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · rintro ((hz | hz) | hz)
      · exact ⟨0, hz⟩
      · exact ⟨1, hz⟩
      · exact ⟨2, hz⟩
  have hb (i) : bd i ⊆ pieces i := by
    fin_cases i
    · exact p.image_subset_closure_inside_cyclic hp
    · exact q.image_subset_closure_inside_cyclic hq
    · exact (enclosingSquare R).image_subset_closure_outside_cyclic hQ
  have hb' (i) : bd' i ⊆ pieces' i := by
    fin_cases i
    · exact p'.image_subset_closure_inside_cyclic hp'
    · exact q'.image_subset_closure_inside_cyclic hq'
    · exact (enclosingSquare R').image_subset_closure_outside_cyclic hQ'
  have hbS (i) : bd i ⊆ S := by
    fin_cases i <;> first | exact hpS | exact hqS | exact hQS
  have hbT (i) : bd' i ⊆ T := by
    fin_cases i <;> first | exact hpT | exact hqT | exact hQT
  have hpq : closure p.inside ∩ closure q.inside ⊆ p.image ∩ q.image := by
    rw [hinter, hpim, hqim]
    rintro z (hz | hz)
    · exact ⟨Or.inl (Or.inl (Or.inr hz)), Or.inl (Or.inl (Or.inr hz))⟩
    · exact ⟨Or.inr hz, Or.inr hz⟩
  have hpq' : closure p'.inside ∩ closure q'.inside ⊆ p'.image ∩ q'.image := by
    rw [hinter', hpim', hqim']
    rintro z (hz | hz)
    · exact ⟨Or.inl (Or.inl (Or.inr hz)), Or.inl (Or.inl (Or.inr hz))⟩
    · exact ⟨Or.inr hz, Or.inr hz⟩
  have overlaps := p.three_outer_pieces_boundary_overlap q (enclosingSquare R) hp hq hQ
    (fun z hz => (hcover ▸ show z ∈ closure p.inside ∪ closure q.inside from Or.inl hz).2)
    (fun z hz => (hcover ▸ show z ∈ closure p.inside ∪ closure q.inside from Or.inr hz).2) hpq
  have overlaps' := p'.three_outer_pieces_boundary_overlap q' (enclosingSquare R') hp' hq' hQ'
    (fun z hz => (hcover' ▸ show z ∈ closure p'.inside ∪ closure q'.inside from Or.inl hz).2)
    (fun z hz => (hcover' ▸ show z ∈ closure p'.inside ∪ closure q'.inside from Or.inr hz).2) hpq'
  let e : ∀ i, pieces i ≃ₜ pieces' i :=
    Fin.cases Hp (Fin.cases Hq (Fin.cases E (fun i => Fin.elim0 i)))
  have emboundary (i) (x : bd i) :
      (e i ⟨x, hb i x.property⟩ : ℂ) = (F ⟨x, hbS i x.property⟩ : ℂ) := by
    fin_cases i
    · exact hHp x
    · exact hHq x
    · exact hE x
  obtain ⟨H, hH⟩ := exists_homeomorph_of_closed_pieces_with_skeleton
    (closure c.outside) (closure c'.outside) S T pieces pieces' bd bd'
    closedpieces closedpieces' covers covers' hb hb' hbS hbT overlaps overlaps' F
    (by intro i; fin_cases i; exact memp; exact memq; exact memQ) e emboundary
  refine ⟨H, homeomorph_mem_iff_of_boundary_values _ _ c.image c'.image
    (c.image_subset_closure_outside_cyclic hc)
    (c'.image_subset_closure_outside_cyclic hc') H fc ?_⟩
  intro x
  have hx : (x : ℂ) ∈ (a 0).image ∪ (a 1).image := hi.symm ▸ x.property
  rcases hx with hx | hx
  · have hxp : (x : ℂ) ∈ p.image := hpim ▸ Or.inl (Or.inl (Or.inl hx))
    exact (hH 0 ⟨x, p.image_subset_closure_inside_cyclic hp hxp⟩).trans (hHp ⟨x, hxp⟩)
  · have hxq : (x : ℂ) ∈ q.image := hqim ▸ Or.inl (Or.inl (Or.inl hx))
    exact (hH 1 ⟨x, q.image_subset_closure_inside_cyclic hq hxq⟩).trans (hHq ⟨x, hxq⟩)

/-- Helper toward Proposition 5.16: every prescribed homeomorphism of two
cyclically simple polygon boundaries extends over their closed exteriors. -/
theorem polygonOutsideExtension_holds : PolygonOutsideExtension := by
  intro c c' hc hc' f
  obtain ⟨Phi, hPhi⟩ := c.exists_outer_chart hc
  obtain ⟨Psi, hPsi⟩ := c'.exists_outer_chart hc'
  have hQ := Polyline.enclosingSquare_isCyclicSimple 1 (by norm_num)
  let b := (Polyline.enclosingSquare 1).image_subset_closure_outside_cyclic hQ
  let fp : c.image ≃ₜ (Polyline.enclosingSquare 1).image :=
    restrictPlanarHomeomorph _ _ _ _
      (c.image_subset_closure_outside_cyclic hc) b Phi hPhi
  let fq : c'.image ≃ₜ (Polyline.enclosingSquare 1).image :=
    restrictPlanarHomeomorph _ _ _ _
      (c'.image_subset_closure_outside_cyclic hc') b Psi hPsi
  let g := fp.symm.trans (f.trans fq)
  obtain ⟨E, hE⟩ := Polyline.exists_squareOutsideExtension 1 1 (by norm_num) (by norm_num) g
  refine ⟨Phi.trans (E.trans Psi.symm), ?_⟩
  intro x
  have hg : g (fp x) = fq (f x) := by
    simp only [g, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  have heq : E (Phi ⟨x, c.image_subset_closure_outside_cyclic hc x.property⟩) =
      Psi ⟨f x, c'.image_subset_closure_outside_cyclic hc' (f x).property⟩ := by
    apply Subtype.ext
    exact (hE (fp x)).trans (congrArg Subtype.val hg)
  change (Psi.symm (E (Phi _)) : ℂ) = (f x : ℂ)
  rw [heq, Psi.symm_apply_apply]

namespace D39FiniteBall

/-- Helper toward Proposition 5.16: cyclically simple whole boundaries of all
orbit faces suffice to extend the drawing homeomorphism to the plane. -/
theorem exists_plane_homeomorph_of_simple_orbit_boundaries'
    {V : Type*} [Finite V] (B : D39FiniteBall) (vert : B.D → V)
    (P P' : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (hvert : Function.Surjective vert)
    (hconn : ∀ d e : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) d e)
    (f : B.PLImageHomeomorph vert P P')
    (O_ext : D39BallFaceCycleOrbit B)
    (hext : (¬ Bornology.IsBounded (B.plOrbitFace vert P hvert O_ext).val) ∧
      (¬ Bornology.IsBounded (B.plOrbitFace vert P' hvert O_ext).val))
    (hsimple : ∀ O : D39BallFaceCycleOrbit B,
      ∃ q q' : Polyline,
        q.start = q.finish ∧ q.IsCyclicSimple ∧
        q.image = B.plOrbitBoundary vert P O ∧
        q'.start = q'.finish ∧ q'.IsCyclicSimple ∧
        q'.image = B.plOrbitBoundary vert P' O) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P.image, H x = (f.toHomeomorph x : ℂ)) ∧
        ∀ d : B.D, H '' (P.arc d).image = (P'.arc d).image := by
  exact B.exists_plane_homeomorph_of_simple_orbit_boundaries
    vert P P' hvert hconn f O_ext hext hsimple polygonOutsideExtension_holds

end D39FiniteBall
end DirectedDistances.PlanarMap
