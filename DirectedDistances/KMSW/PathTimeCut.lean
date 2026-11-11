module

public import DirectedDistances.KMSW.ActiveTimeMonotone
import DirectedDistances.KMSW.InftyCutCore
import DirectedDistances.KMSW.MeasurableCutEvents
import DirectedDistances.KMSW.StageSubgraph

/-! # Early and late pieces of directed paths

Helpers for the frontier decomposition in the item-busemann-ind reduction -/

public section
namespace DirectedDistances.KMSW

open Quiver

/-- Every directed path splits at its activation-time cutoff into an early -/
theorem path_exists_early_late_factorization
    {w : ℕ → Fin 3} (t : ℕ) {x y : PresentVertex w} (p : Path x y) :
    ∃ u : PresentVertex w, ∃ pe : Path x u, ∃ pl : Path u y,
      p = pe.comp pl ∧
      (∀ e ∈ pathEdgeList pe, ∀ he : EdgePresent w e,
        actTime w e he < t) ∧
      (∀ e ∈ pathEdgeList pl, ∀ he : EdgePresent w e,
        t ≤ actTime w e he) := by
  induction p with
  | nil =>
      refine ⟨x, Path.nil, Path.nil, ?_, ?_, ?_⟩
      · rfl
      · simp [pathEdgeList]
      · simp [pathEdgeList]
  | @cons a b p e ih =>
      by_cases hearly : actTime w e.val e.property.1 < t
      · have hpair := pathEdgeList_actTime_pairwise (Path.cons p e)
        rcases List.pairwise_append.mp hpair with ⟨_, _, hcross⟩
        refine ⟨b, Path.cons p e, Path.nil, ?_, ?_, ?_⟩
        · exact Path.comp_nil (Path.cons p e)
        · intro f hf hfPresent
          change f ∈ pathEdgeList p ++ [e.val] at hf
          rcases List.mem_append.mp hf with hfp | hfe
          · have hlt := hcross f hfp e.val (by simp) hfPresent e.property.1
            exact hlt.trans hearly
          · have hfe' : f = e.val := List.mem_singleton.mp hfe
            subst f
            exact hearly
        · simp [pathEdgeList]
      · have helate : t ≤ actTime w e.val e.property.1 := Nat.le_of_not_gt hearly
        obtain ⟨u, pe, pl, hp, hpe, hpl⟩ := ih
        refine ⟨u, pe, Path.cons pl e, ?_, hpe, ?_⟩
        · rw [Path.comp_cons, ← hp]
        · intro f hf hfPresent
          change f ∈ pathEdgeList pl ++ [e.val] at hf
          rcases List.mem_append.mp hf with hfp | hfe
          · exact hpl f hfp hfPresent
          · have hfe' : f = e.val := List.mem_singleton.mp hfe
            subst f
            exact helate

/-- Concatenating an early path and a late path gives a path, with additive -/
theorem path_early_late_comp {w : ℕ → Fin 3}
    {x u y : PresentVertex w} (pe : Path x u) (pl : Path u y) :
    ∃ p : Path x y, p = pe.comp pl ∧ p.length = pe.length + pl.length := by
  exact ⟨pe.comp pl, rfl, Path.length_comp pe pl⟩

private theorem pathEdgeList_edgePresent {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) :
    ∀ e ∈ pathEdgeList p, EdgePresent w e := by
  induction p with
  | nil =>
      intro e he
      simp only [pathEdgeList, List.not_mem_nil] at he
  | cons p f ih =>
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact ih e he
      · have hef : e = f.val := List.mem_singleton.mp he
        subst e
        exact f.property.1

/-- The endpoints reachable from a fixed vertex by paths whose edges all
activate before `t` form a finite set (`lem-directed-contain`, -/
theorem early_reachable_finite (w : ℕ → Fin 3) (t : ℕ) (x : PresentVertex w) :
    {v : PresentVertex w | ∃ p : Path x v,
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        actTime w e he < t}.Finite := by
  apply (finite_endpoints_of_paths_using_finite_edges x
    (cutActivatedBetween w 0 t) (cutActivatedBetween_finite w 0 t)).subset
  rintro v ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro e he
  have hePresent := pathEdgeList_edgePresent p e he
  have htime := hp e he hePresent
  refine ⟨actTime w e hePresent, ⟨Nat.zero_le _, htime⟩, ?_⟩
  exact (actTime_spec w e hePresent).symm

private theorem early_path_transfer {w w' : ℕ → Fin 3} (t : ℕ)
    (hcode : ∀ i, i < t → w i = w' i) {x y : PresentVertex w}
    (p : Path x y)
    (hp : ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
      actTime w e he < t) :
    ∃ q : Path (⟨x.id⟩ : PresentVertex w') ⟨y.id⟩,
      q.length = p.length ∧
      (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w' e,
        actTime w' e he < t) := by
  induction p with
  | nil =>
      refine ⟨Path.nil, rfl, ?_⟩
      simp [pathEdgeList]
  | @cons a b p e ih =>
      have hpref : ∀ f ∈ pathEdgeList p, ∀ hf : EdgePresent w f,
          actTime w f hf < t := by
        intro f hf hfPresent
        apply hp f ?_ hfPresent
        change f ∈ pathEdgeList p ++ [e.val]
        exact List.mem_append_left _ hf
      have hlast : actTime w e.val e.property.1 < t := by
        apply hp e.val ?_ e.property.1
        change e.val ∈ pathEdgeList p ++ [e.val]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      obtain ⟨q, hlen, hq⟩ := ih hpref
      let n := actTime w e.val e.property.1
      have hstage : kmswStage w n = kmswStage w' n :=
        kmswStage_congr (fun i hi => hcode i (hi.trans hlast))
      have hact : act w n = act w' n := by
        change (kmswStage w n).active = (kmswStage w' n).active
        rw [hstage]
      have heq : e.val = act w' n := (actTime_spec w e.val e.property.1).trans hact
      have halloc : act w n < (kmswStage w n).nextEdge :=
        act_lt_nextEdge w (Nat.le_refl n)
      have halloc' : act w' n < (kmswStage w' n).nextEdge :=
        act_lt_nextEdge w' (Nat.le_refl n)
      have hpresent' : (kmswStage w' n).present (act w' n) = true := by
        obtain ⟨es, hes⟩ := kmswStage_UL_last w' n
        apply (kmswStage_status w' n).2.1
        rw [hes]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have he' : EdgePresent w' e.val := by
        rw [heq]
        exact EdgePresent.of_stage_present halloc' hpresent'
      have hbound : e.val < (kmswStage w n).nextEdge := by
        rw [actTime_spec w e.val e.property.1]
        exact halloc
      have hbound' : e.val < (kmswStage w' n).nextEdge := by
        rw [heq]
        exact halloc'
      have hwest : edgeWest w' e.val = a.id := by
        calc
          edgeWest w' e.val = (kmswStage w' n).west e.val :=
            (edge_endpoints_eq w' hbound').1.symm
          _ = (kmswStage w n).west e.val := by rw [← hstage]
          _ = edgeWest w e.val := (edge_endpoints_eq w hbound).1
          _ = a.id := e.property.2.1
      have heast : edgeEast w' e.val = b.id := by
        calc
          edgeEast w' e.val = (kmswStage w' n).east e.val :=
            (edge_endpoints_eq w' hbound').2.symm
          _ = (kmswStage w n).east e.val := by rw [← hstage]
          _ = edgeEast w e.val := (edge_endpoints_eq w hbound).2
          _ = b.id := e.property.2.2
      let e' : (⟨a.id⟩ : PresentVertex w') ⟶ ⟨b.id⟩ :=
        ⟨e.val, he', hwest, heast⟩
      refine ⟨Path.cons q e', ?_, ?_⟩
      · simp only [Path.length_cons, hlen, Path.length_cons]
      · intro f hf hfPresent
        change f ∈ pathEdgeList q ++ [e.val] at hf
        rcases List.mem_append.mp hf with hfp | hfe
        · exact hq f hfp hfPresent
        · have hfe' : f = e.val := List.mem_singleton.mp hfe
          subst f
          have htime : actTime w' e.val he' = n :=
            (actTime_eq_iff w' e.val he' n).2 heq
          rw [htime]
          exact hlast

@[expose] def earlyPathLengths (w : ℕ → Fin 3) (t a b : ℕ) : Set ℕ :=
  {n | ∃ p : Path (⟨a⟩ : PresentVertex w) ⟨b⟩,
    p.length = n ∧
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
        actTime w e he < t}

/-- The lengths of all-early paths between fixed vertex IDs depend only on
the codes before the cutoff (`lem-directed-contain`, -/
theorem earlyPathLengths_congr {w w' : ℕ → Fin 3} (t a b : ℕ)
    (hcode : ∀ i, i < t → w i = w' i) :
    earlyPathLengths w t a b = earlyPathLengths w' t a b := by
  ext n
  constructor
  · rintro ⟨p, hlen, hp⟩
    obtain ⟨q, hqLen, hq⟩ := early_path_transfer t hcode p hp
    exact ⟨q, hqLen.trans hlen, hq⟩
  · rintro ⟨p, hlen, hp⟩
    obtain ⟨q, hqLen, hq⟩ := early_path_transfer t
      (fun i hi => (hcode i hi).symm) p hp
    exact ⟨q, hqLen.trans hlen, hq⟩

end DirectedDistances.KMSW
