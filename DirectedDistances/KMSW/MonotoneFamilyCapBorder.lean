/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbitsCap
public import DirectedDistances.KMSW.MonotoneFamilyFaceOrbits

/-! Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of the

This file records the uniqueness of a face bordered by a fixed dart and proves
`cap_border_edge_mem`: a dart bordering a creation cap has one of the three creation
edge identities. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
A dart borders at most one face of the one-sided KMSW drawing. -/
theorem dart_border_face_unique (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool)
    (F G : (monotoneFamilyDrawing w hfin (monotone_family_all w)).Face)
    (hF : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d F)
    (hG : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d G) :
    F = G := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  obtain ⟨a, ha, hFa⟩ := hF
  obtain ⟨b, hb, hGb⟩ := hG
  let t := min a b / 2
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hta : t < a := by
    have hmin := min_le_left a b
    dsimp [t]
    linarith
  have htb : t < b := by
    have hmin := min_le_right a b
    dsimp [t]
    linarith
  exact P.faces_eq_of_mem (hFa t t ht hta ht hta) (hGb t t ht htb ht htb)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
Two wedge regions with the same initial data cannot be disjoint. -/
private theorem wedgeIn_incompatible {p dir : ℂ} {S K : Set ℂ}
    (hS : WedgeIn p dir S) (hsub : S ⊆ K) (hK : WedgeIn p dir Kᶜ) : False := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hS
  obtain ⟨δ₂, hδ₂, h₂⟩ := hK
  let t := min δ₁ δ₂ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₁ : t < δ₁ := by
    have hmin := min_le_left δ₁ δ₂
    dsimp [t]
    linarith
  have ht₂ : t < δ₂ := by
    have hmin := min_le_right δ₁ δ₂
    dsimp [t]
    linarith
  exact h₂ t t ht ht₂ ht ht₂ (hsub (h₁ t t ht ht₁ ht ht₁))

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
A wedge remains in any larger set containing its target region. -/
private theorem wedgeIn_mono {p dir : ℂ} {S T : Set ℂ} (hST : S ⊆ T)
    (hS : WedgeIn p dir S) : WedgeIn p dir T := by
  obtain ⟨δ, hδ, hw⟩ := hS
  refine ⟨δ, hδ, ?_⟩
  intro t ε ht htδ hε hεδ
  exact hST (hw t ε ht htδ hε hεδ)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
An allocated stage edge keeps the same trace at every later stage. -/
private theorem capBorder_stageEdgeTrace_stable (w : ℕ → Fin 3)
    (Q : ∀ n, StageDrawing w n) (G : ∀ n, MonotoneStageInvariant w n (Q n))
    {n m e : ℕ} (hnm : n ≤ m) (he : e < (kmswStage w n).nextEdge) :
    stageEdgeTrace (Q m) e = stageEdgeTrace (Q n) e := by
  have hstable (k : ℕ) (hnk : n ≤ k) : layoutArc w k e = layoutArc w n e := by
    induction k, hnk using Nat.le_induction with
    | base => rfl
    | succ k hnk ih =>
      rw [layoutArc_old w k e
        (he.trans_le (kmswStage_nextEdge_mono w hnk)), ih]
  have hem : e < (kmswStage w m).nextEdge :=
    he.trans_le (kmswStage_nextEdge_mono w hnm)
  have hArcM : (Q m).arc (⟨⟨e, hem⟩, false⟩ : StageDart (kmswStage w m).nextEdge) =
      layoutArc w m e := by
    simpa using (G m).arc_layout (⟨⟨e, hem⟩, false⟩)
  have hArcN : (Q n).arc (⟨⟨e, he⟩, false⟩ : StageDart (kmswStage w n).nextEdge) =
      layoutArc w n e := by
    simpa using (G n).arc_layout (⟨⟨e, he⟩, false⟩)
  simp only [stageEdgeTrace, dite_eq_left hem, dite_eq_left he, hArcM, hArcN]
  exact congrArg (fun p : Polyline => p.image) (hstable m hnm)

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
The creation cap has a later stage index with the same triangle record and region. -/
private theorem creation_cap_index_persists (w : ℕ → Fin 3)
    (j : TriangleCreationTime w) (n : ℕ) (hn : j.val + 1 ≤ n) :
    ∃ i : Fin (kmswStage w n).triangles.length,
      (kmswStage w n).triangles.get i = stageTriangleRecord w j ∧
      ((familyG w (monotone_family_all w) n).cap i).region =
        ((familyG w (monotone_family_all w) (j.val + 1)).cap
          (stageTriangleRecord_fin_index w j).choose).region := by
  let n₀ := j.val + 1
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  let t := stageTriangleRecord w j
  let i₀ := (stageTriangleRecord_fin_index w j).choose
  have ht₀ : (kmswStage w n₀).triangles.get i₀ = t :=
    (stageTriangleRecord_fin_index w j).choose_spec
  have hmem : t ∈ (kmswStage w n₀).triangles := by
    rw [← ht₀]
    exact List.get_mem _ i₀
  have hmemN := triangles_sub_stage w hn t hmem
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmemN
  let i : Fin (kmswStage w n).triangles.length := ⟨k, hk⟩
  have hgetT : (kmswStage w n).triangles.get i = t := by
    simpa [i] using hget
  have htri : (kmswStage w n₀).triangles.get i₀ =
      (kmswStage w n).triangles.get i := ht₀.trans hgetT.symm
  have hb := triBound_stage w n₀ t hmem
  have htrace : ∀ e, e ∈ [t.1, t.2.1, t.2.2] →
      stageEdgeTrace (Q n₀) e = stageEdgeTrace (Q n) e := by
    intro e he
    have heBound : e < (kmswStage w n₀).nextEdge := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2
    exact (capBorder_stageEdgeTrace_stable w Q G hn heBound).symm
  have htrace' : ∀ e, e ∈ [((kmswStage w n₀).triangles.get i₀).1,
      ((kmswStage w n₀).triangles.get i₀).2.1,
      ((kmswStage w n₀).triangles.get i₀).2.2] →
      stageEdgeTrace (Q n₀) e = stageEdgeTrace (Q n) e := by
    simpa only [ht₀] using htrace
  refine ⟨i, hgetT, ?_⟩
  simpa [G, n₀, i₀] using
    (monotone_cap_region_eq w (G n₀) (G n) i₀ i htri htrace').symm

/-- Helper toward Definition 3.8 and Theorem 1.4 (realized faces = face-successor orbits of
Any dart bordering a creation cap has one of that triangle's three edge identities. -/
theorem cap_border_edge_mem (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (j : TriangleCreationTime w) (d : ℕ × Bool)
    (hd : (monotoneFamilyDrawing w hfin (monotone_family_all w)).dartBorders d
      (capFace w hfin j)) :
    d.1 = (stageTriangleRecord w j).1 ∨
      d.1 = (stageTriangleRecord w j).2.1 ∨
      d.1 = (stageTriangleRecord w j).2.2 := by
  let n := max (j.val + 1) d.1
  let Q := familyQ w (monotone_family_all w)
  let G := familyG w (monotone_family_all w)
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  have hn : j.val + 1 ≤ n := Nat.le_max_left _ _
  have hdBound : d.1 < (kmswStage w n).nextEdge := by
    exact (kmsw_edge_allocated_by_self w d.1).trans_le
      (kmswStage_nextEdge_mono w (Nat.le_max_right _ _))
  obtain ⟨i, htri, hcap⟩ := creation_cap_index_persists w j n hn
  have hcapFace : (capFace w hfin j).val = ((G n).cap i).region := by
    exact (capFace_spec w hfin j).1.trans hcap.symm
  let dN : StageDart (kmswStage w n).nextEdge := (⟨d.1, hdBound⟩, d.2)
  have harc : P.arc d = (Q n).arc dN := by
    simpa [P, dN] using familyDrawing_arc w hfin (monotone_family_all w) n dN
  have hwP : WedgeIn (P.arc d).start (P.arc d).initialDirection
      (capFace w hfin j).val :=
    (dartBorders_iff_WedgeIn P d (capFace w hfin j)).mp hd
  have hw : WedgeIn ((Q n).arc dN).start ((Q n).arc dN).initialDirection
      ((G n).cap i).region := by
    rw [← harc, ← hcapFace]
    exact hwP
  have hcapSub : ((G n).cap i).region ⊆
      closedGraphRegion (G n).xmin (G n).xmax (G n).lower (G n).upper := by
    intro z hz
    rw [← (G n).cover]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, subset_closure hz⟩)
  have hrecordEdge (e : ℕ)
      (he : e ∈ (G n).capLower i ++ (G n).capUpper i) :
      e = (stageTriangleRecord w j).1 ∨
        e = (stageTriangleRecord w j).2.1 ∨
        e = (stageTriangleRecord w j).2.2 := by
    have h := ((G n).cap_edges i e).mp he
    rw [htri] at h
    exact h
  cases hb : d.2 with
  | false =>
    rcases (G n).cover_lower ⟨d.1, hdBound⟩ with hboundary | ⟨k, hside⟩
    · have hOutside := (G n).ext_upper_wedge d.1 hdBound hboundary
      have hOutside' : WedgeIn ((Q n).arc dN).start
          ((Q n).arc dN).initialDirection
          (closedGraphRegion (G n).xmin (G n).xmax
            (G n).lower (G n).upper)ᶜ := by
        simpa [Q, dN, hb] using hOutside
      exact (wedgeIn_incompatible hw hcapSub hOutside').elim
    · by_cases hik : k = i
      · subst k
        exact hrecordEdge d.1 (List.mem_append_left _ hside)
      · have hdisj : Disjoint ((G n).cap i).region ((G n).cap k).region :=
          (G n).cap_disjoint i k (Ne.symm hik)
        have hsub : ((G n).cap k).region ⊆ ((G n).cap i).regionᶜ := by
          intro z hzK hzI
          exact (Set.disjoint_left.mp hdisj hzI) hzK
        have hOutside := wedgeIn_mono hsub
          ((G n).cap_lower_wedge k d.1 hdBound hside)
        have hOutside' : WedgeIn ((Q n).arc dN).start
            ((Q n).arc dN).initialDirection ((G n).cap i).regionᶜ := by
          simpa [Q, dN, hb] using hOutside
        exact (wedgeIn_incompatible hw (Set.Subset.rfl) hOutside').elim
  | true =>
    rcases (G n).cover_upper ⟨d.1, hdBound⟩ with hboundary | ⟨k, hside⟩
    · have hOutside := (G n).ext_lower_wedge d.1 hdBound hboundary
      have hOutside' : WedgeIn ((Q n).arc dN).start
          ((Q n).arc dN).initialDirection
          (closedGraphRegion (G n).xmin (G n).xmax
            (G n).lower (G n).upper)ᶜ := by
        simpa [Q, dN, hb] using hOutside
      exact (wedgeIn_incompatible hw hcapSub hOutside').elim
    · by_cases hik : k = i
      · subst k
        exact hrecordEdge d.1 (List.mem_append_right _ hside)
      · have hdisj : Disjoint ((G n).cap i).region ((G n).cap k).region :=
          (G n).cap_disjoint i k (Ne.symm hik)
        have hsub : ((G n).cap k).region ⊆ ((G n).cap i).regionᶜ := by
          intro z hzK hzI
          exact (Set.disjoint_left.mp hdisj hzI) hzK
        have hOutside := wedgeIn_mono hsub
          ((G n).cap_upper_wedge k d.1 hdBound hside)
        have hOutside' : WedgeIn ((Q n).arc dN).start
            ((Q n).arc dN).initialDirection ((G n).cap i).regionᶜ := by
          simpa [Q, dN, hb] using hOutside
        exact (wedgeIn_incompatible hw (Set.Subset.rfl) hOutside').elim

end DirectedDistances.KMSW
