module

public import DirectedDistances.KMSW.PathTimeCut
public import DirectedDistances.KMSW.RightShiftAllGeometry
public import DirectedDistances.KMSW.LeftStationaryGeometry
public import DirectedDistances.KMSW.KMSWShiftLateLift
public import DirectedDistances.Recursive.RightStationaryBusemann
public import DirectedDistances.Recursive.LeftStationaryBusemann

/-! Supporting lemmas for paper labels `def-ldp`, `lem-directed-contain`, `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

/- # Frontier envelopes at the first right hit

property is an explicit hypothesis. These helpers are not counted as paper
results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive
open DirectedDistances.KMSW Quiver



@[expose] def RightFrontierLabels (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) : Prop :=
  ∀ u : PresentVertex w,
    (u = ⟨boundaryVertex w h 0⟩ ∨ ∃ e, ∃ he : EdgePresent w e,
      actTime w e he < boundaryHitTime w h 1 ∧ edgeEast w e = u.id) →
    (∃ f, ∃ hf : EdgePresent w f, boundaryHitTime w h 1 ≤ actTime w f hf ∧
      edgeWest w f = u.id) →
    ∃ j : ℕ, u = shiftLimitVertex w (boundaryHitTime w h 1)
      ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩

/-- All-early shortest distance, retaining infinity for no early path. -/
@[expose] noncomputable def earlySdp (w : ℕ → Fin 3) (t : ℕ)
    (a b : PresentVertex w) : ℕ∞ :=
  ⨅ n ∈ earlyPathLengths w t a.id b.id, (n : ℕ∞)




theorem earlySdp_attained (w : ℕ → Fin 3) (t : ℕ) (a b : PresentVertex w)
    (hr : (earlyPathLengths w t a.id b.id).Nonempty) :
    ∃ n ∈ earlyPathLengths w t a.id b.id, earlySdp w t a b = (n : ℕ∞) := by
  classical
  refine ⟨Nat.find hr, Nat.find_spec hr, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le (Nat.find hr) (iInf_le _ (Nat.find_spec hr))
  · refine le_iInf₂ fun n hn => ?_
    exact ENat.natCast_le_natCast.mpr (Nat.find_min' hr hn)




theorem earlySdp_congr {w w' : ℕ → Fin 3} (t a b : ℕ)
    (hcode : ∀ i, i < t → w i = w' i) :
    earlySdp w t ⟨a⟩ ⟨b⟩ = earlySdp w' t ⟨a⟩ ⟨b⟩ := by
  unfold earlySdp
  rw [earlyPathLengths_congr t a b hcode]

/-- Negative shifted boundary labels reachable by an all-early path. -/
@[expose] def rightFrontierIndices (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) : Set ℕ :=
  {j | (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
    (shiftLimitVertex w (boundaryHitTime w h 1)
      ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩).id).Nonempty}



theorem rightFrontierIndices_finite (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) :
    (rightFrontierIndices w h hs).Finite := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let f := fun j : ℕ => shiftLimitVertex w t ⟨boundaryVertex ws hs (-(j : ℤ))⟩
  have hf : Function.Injective f := by
    intro j k hjk
    have hv := shiftLimitVertex_injective w t
      (boundaryVertex_left_allocated ws hs (by omega : -(j : ℤ) ≤ 0))
      (boundaryVertex_left_allocated ws hs (by omega : -(k : ℤ) ≤ 0)) hjk
    have hi := boundaryVertex_injective ws hs (congrArg PresentVertex.id hv)
    omega
  have hh := (early_reachable_finite w t ⟨boundaryVertex w h 0⟩).preimage
    (fun _ _ _ _ heq => hf heq)
  apply hh.subset
  rintro j ⟨n, p, hp, _he⟩
  exact ⟨p, _he⟩

private theorem path_initial_edge {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) (hp : p.length ≠ 0) :
    ∃ e, e ∈ pathEdgeList p ∧ ∃ _he : EdgePresent w e, edgeWest w e = a.id := by
  induction p with
  | nil => exact (hp rfl).elim
  | @cons c d p e ih =>
    by_cases hz : p.length = 0
    · have hac := p.eq_of_length_zero hz
      exact ⟨e.val, List.mem_append_right _ (List.mem_singleton.mpr rfl),
        e.property.1, e.property.2.1.trans (congrArg PresentVertex.id hac.symm)⟩
    · obtain ⟨f, hf, hfp, hfa⟩ := ih hz
      exact ⟨f, List.mem_append_left _ hf, hfp, hfa⟩

private theorem shift_path_map_frontier (w : ℕ → Fin 3) (t : ℕ)
    {a b : PresentVertex (fun i => w (t + i))} (p : Path a b) :
    ∃ q : Path (shiftLimitVertex w t a) (shiftLimitVertex w t b),
      q.length = p.length := by
  induction p with
  | nil => exact ⟨Path.nil, rfl⟩
  | @cons c d p e ih =>
    obtain ⟨q, hq⟩ := ih
    let ef : {e // EdgePresent (fun i => w (t + i)) e} := ⟨e.val, e.property.1⟩
    have hi := shiftLimitEdge_incidence w t ef
    have hc : (⟨edgeWest (fun i => w (t + i)) e.val⟩ :
        PresentVertex (fun i => w (t + i))) = c := congrArg PresentVertex.mk e.property.2.1
    have hd : (⟨edgeEast (fun i => w (t + i)) e.val⟩ :
        PresentVertex (fun i => w (t + i))) = d := congrArg PresentVertex.mk e.property.2.2
    rw [hc, hd] at hi
    let f : shiftLimitVertex w t c ⟶ shiftLimitVertex w t d :=
      ⟨shiftLimitEdge w t ef, shiftLimitEdge_present w t ef, hi⟩
    exact ⟨q.cons f, by simp only [Path.length_cons, hq]⟩

/- Exact path-length convolution at a right hit for targets with no all-early
path. This uses the explicit crossing-label input and is only a helper for -/
theorem rightFrontier_pathLengths (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hlabel : RightFrontierLabels w h hs)
    (b : PresentVertex (fun i => w (boundaryHitTime w h 1 + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h 1 + i)) b)
    (hfar : ¬ (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
      (shiftLimitVertex w (boundaryHitTime w h 1) b).id).Nonempty) :
    pathLengths (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h 1) b) =
      {n | ∃ j ∈ rightFrontierIndices w h hs, ∃ a c : ℕ,
        a ∈ earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩).id ∧
        c ∈ pathLengths
          (⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩ :
            PresentVertex (fun i => w (boundaryHitTime w h 1 + i))) b ∧ n = a + c} := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨u, pe, pl, hp, he, hl⟩ := path_exists_early_late_factorization t p
    have hn : pl.length ≠ 0 := by
      intro hz
      have huv := pl.eq_of_length_zero hz
      subst u
      exact hfar ⟨pe.length, pe, rfl, he⟩
    obtain ⟨f, hf, hfp, hfu⟩ := path_initial_edge pl hn
    have hin : u = ⟨boundaryVertex w h 0⟩ ∨
        ∃ e, ∃ hep : EdgePresent w e, actTime w e hep < t ∧ edgeEast w e = u.id := by
      cases pe with
      | nil => exact Or.inl rfl
      | @cons c d pe e =>
        exact Or.inr ⟨e.val, e.property.1,
          he e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl)) e.property.1,
          e.property.2.2⟩
    obtain ⟨j, hu⟩ := hlabel u hin ⟨f, hfp, hl f hf hfp, hfu⟩
    subst u
    obtain ⟨b', hb', q, hqb, hq, _⟩ := shiftLimitVertex_late_path_lift w t
      ⟨boundaryVertex ws hs (-(j : ℤ))⟩
      (boundaryVertex_left_allocated ws hs (by omega)) pl hl
    have hbb : b' = b := shiftLimitVertex_injective w t hb' hb hqb
    subst b'
    refine ⟨j, ⟨pe.length, pe, rfl, he⟩, pe.length, q.length,
      ⟨pe, rfl, he⟩, ⟨q, rfl⟩, ?_⟩
    change p.length = pe.length + q.length
    rw [hp, Path.length_comp, hq]
  · rintro ⟨j, _, a, c, ⟨pe, hpe, he⟩, ⟨pl, hpl⟩, rfl⟩
    obtain ⟨q, hq⟩ := shift_path_map_frontier w t pl
    refine ⟨pe.comp q, ?_⟩
    change (pe.comp q).length = a + c
    change pl.length = c at hpl
    rw [Path.length_comp, hpe, hq, hpl]





theorem rightFrontier_sdp (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hlabel : RightFrontierLabels w h hs)
    (b : PresentVertex (fun i => w (boundaryHitTime w h 1 + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h 1 + i)) b)
    (hfar : ¬ (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
      (shiftLimitVertex w (boundaryHitTime w h 1) b).id).Nonempty) :
    sdp (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h 1) b) =
      ⨅ j ∈ rightFrontierIndices w h hs,
        earlySdp w (boundaryHitTime w h 1) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩) +
        sdp (⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h 1 + i))) b := by
  have hlengths := rightFrontier_pathLengths w h hs hlabel b hb hfar
  apply le_antisymm
  · refine le_iInf₂ fun j hj => ?_
    unfold earlySdp
    rw [ENat.iInf_add]
    refine le_iInf fun a => ?_
    rw [ENat.iInf_add]
    refine le_iInf fun ha => ?_
    simp only [sdp]
    rw [ENat.add_iInf]
    refine le_iInf fun q => ?_
    obtain ⟨pe, hpe, _⟩ := ha
    obtain ⟨r, hr⟩ := shift_path_map_frontier w (boundaryHitTime w h 1) q
    exact (sdp_le_length (pe.comp r)).trans_eq (by
      rw [Path.length_comp, hpe, hr, ENat.natCast_add])
  · refine le_iInf fun p => ?_
    have hp : p.length ∈ pathLengths
        (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h 1) b) := ⟨p, rfl⟩
    rw [hlengths] at hp
    obtain ⟨j, hj, a, c, ha, ⟨q, hq⟩, hn⟩ := hp
    refine iInf_le_of_le j (iInf_le_of_le hj ?_)
    calc
      _ ≤ (a : ℕ∞) + (c : ℕ∞) := add_le_add
        (iInf_le_of_le a (iInf_le _ ha))
        ((sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hq))
      _ = (p.length : ℕ∞) := by rw [← ENat.natCast_add, ← hn]

/-- Supremum of all-early lengths. Used only on bounded path-length sets;
bottom retains the unreachable convention of `def-ldp`. -/
@[expose] noncomputable def earlyLdp (w : ℕ → Fin 3) (t : ℕ)
    (a b : PresentVertex w) : WithBot ℕ :=
  sSup ((fun n : ℕ => (n : WithBot ℕ)) '' earlyPathLengths w t a.id b.id)




theorem earlyLdp_congr {w w' : ℕ → Fin 3} (t a b : ℕ)
    (hcode : ∀ i, i < t → w i = w' i) :
    earlyLdp w t ⟨a⟩ ⟨b⟩ = earlyLdp w' t ⟨a⟩ ⟨b⟩ := by
  unfold earlyLdp
  rw [earlyPathLengths_congr t a b hcode]

private theorem early_lengths_subset (w : ℕ → Fin 3) (t : ℕ)
    (a b : PresentVertex w) : earlyPathLengths w t a.id b.id ⊆ pathLengths a b := by
  rintro n ⟨p, hp, _⟩
  exact ⟨p, hp⟩

private theorem early_lengths_finite (w : ℕ → Fin 3) (t : ℕ)
    (hbound : PresentPathLengthsBounded (w := w)) (a b : PresentVertex w) :
    (earlyPathLengths w t a.id b.id).Finite := by
  by_cases hr : Reachable a b
  · exact (pathLengths_finite_of_bddAbove (hbound a b hr)).subset
      (early_lengths_subset w t a b)
  · have he : earlyPathLengths w t a.id b.id = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro n ⟨p, _, _⟩
      exact hr ⟨p⟩
    rw [he]
    exact Set.finite_empty



theorem earlyLdp_attained (w : ℕ → Fin 3) (t : ℕ)
    (hbound : PresentPathLengthsBounded (w := w)) (a b : PresentVertex w)
    (hr : (earlyPathLengths w t a.id b.id).Nonempty) :
    ∃ n ∈ earlyPathLengths w t a.id b.id, earlyLdp w t a b = (n : WithBot ℕ) := by
  have hf := (early_lengths_finite w t hbound a b).image (fun n : ℕ => (n : WithBot ℕ))
  obtain ⟨n, hn, heq⟩ := (hr.image (fun n : ℕ => (n : WithBot ℕ))).csSup_mem hf
  exact ⟨n, hn, heq.symm⟩

private theorem length_le_earlyLdp (w : ℕ → Fin 3) (t : ℕ)
    (hbound : PresentPathLengthsBounded (w := w)) (a b : PresentVertex w)
    {n : ℕ} (hn : n ∈ earlyPathLengths w t a.id b.id) :
    (n : WithBot ℕ) ≤ earlyLdp w t a b :=
  le_csSup ((early_lengths_finite w t hbound a b).image _).bddAbove ⟨n, hn, rfl⟩

private theorem ldpSup_eq_longest_frontier {w : ℕ → Fin 3} {a b : PresentVertex w}
    {p : Path a b} (hp : IsLongest p) : ldpSup a b = (p.length : WithBot ℕ) := by
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨n, ⟨q, rfl⟩, rfl⟩
    exact WithBot.coe_le_coe.mpr (hp q)
  · apply le_csSup
    · refine ⟨(p.length : WithBot ℕ), ?_⟩
      rintro _ ⟨n, ⟨q, rfl⟩, rfl⟩
      exact WithBot.coe_le_coe.mpr (hp q)
    · exact ⟨p.length, ⟨p, rfl⟩, rfl⟩

private theorem length_le_ldpSup_frontier {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (p : Path a b) : (p.length : WithBot ℕ) ≤ ldpSup a b := by
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hbound a b ⟨p⟩) ⟨p⟩
  rw [ldpSup_eq_longest_frontier hq]
  exact WithBot.coe_le_coe.mpr (hq p)

private theorem shift_bounded_frontier (w : ℕ → Fin 3) (t : ℕ)
    (hbound : PresentPathLengthsBounded (w := w)) :
    PresentPathLengthsBounded (w := fun i => w (t + i)) := by
  intro a b hr
  obtain ⟨p⟩ := hr
  obtain ⟨q, _⟩ := shift_path_map_frontier w t p
  obtain ⟨N, hN⟩ := hbound _ _ ⟨q⟩
  refine ⟨N, ?_⟩
  rintro n ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := shift_path_map_frontier w t r
  change r.length ≤ N
  rw [← hs]
  exact hN ⟨s, rfl⟩

/- Bounded LDP twin of `rightFrontier_sdp`: the supremum is a maximum over
finitely many frontier labels, with bottom for unreachable suffixes. Plan B.2,
Conditional on the crossing-label input; not counted, F1/F4 remain. -/
theorem rightFrontier_ldpSup (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hlabel : RightFrontierLabels w h hs)
    (hbound : PresentPathLengthsBounded (w := w))
    (b : PresentVertex (fun i => w (boundaryHitTime w h 1 + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h 1 + i)) b)
    (hfar : ¬ (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
      (shiftLimitVertex w (boundaryHitTime w h 1) b).id).Nonempty) :
    ldpSup (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h 1) b) =
      sSup ((fun j : ℕ =>
        earlyLdp w (boundaryHitTime w h 1) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩) +
        ldpSup (⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h 1 + i))) b) ''
        rightFrontierIndices w h hs) := by
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let a := fun j : ℕ => (⟨boundaryVertex ws hs (-(j : ℤ))⟩ : PresentVertex ws)
  let x : PresentVertex w := ⟨boundaryVertex w h 0⟩
  let F := fun j : ℕ => earlyLdp w t x (shiftLimitVertex w t (a j)) + ldpSup (a j) b
  have hfinite : (F '' rightFrontierIndices w h hs).Finite :=
    (rightFrontierIndices_finite w h hs).image F
  have hbs := shift_bounded_frontier w t hbound
  have hlengths := rightFrontier_pathLengths w h hs hlabel b hb hfar
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
    have hp : p.length ∈ pathLengths x (shiftLimitVertex w t b) := ⟨p, rfl⟩
    rw [hlengths] at hp
    obtain ⟨j, hj, m, n, hm, ⟨q, hq⟩, hn⟩ := hp
    have hle : (p.length : WithBot ℕ) ≤ F j := by
      change q.length = n at hq
      rw [hn, Nat.cast_add]
      exact add_le_add (length_le_earlyLdp w t hbound x _ hm)
        (by rw [← hq]; exact length_le_ldpSup_frontier hbs q)
    exact hle.trans (le_csSup hfinite.bddAbove ⟨j, hj, rfl⟩)
  · apply csSup_le'
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨n, hn, heq⟩ := earlyLdp_attained w t hbound x (shiftLimitVertex w t (a j)) hj
    obtain ⟨pe, hpe, _⟩ := hn
    by_cases hr : Reachable (a j) b
    · obtain ⟨pl, hpl⟩ := exists_isLongest_of_bddAbove (hbs _ _ hr) hr
      obtain ⟨q, hq⟩ := shift_path_map_frontier w t pl
      change F j ≤ _
      dsimp only [F]
      rw [heq, ldpSup_eq_longest_frontier hpl]
      have hh := length_le_ldpSup_frontier hbound (pe.comp q)
      simpa only [Path.length_comp, hpe, hq, Nat.cast_add] using hh
    · change F j ≤ _
      dsimp only [F]
      rw [ldpSup_eq_bot_of_not_reachable hr, WithBot.add_bot]
      exact bot_le

/-- The root edge is an early path to shifted frontier label zero
Helper only; the crossing-label obligation and F1/F4 remain. -/
theorem zero_mem_rightFrontierIndices (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) :
    0 ∈ rightFrontierIndices w h hs := by
  have hroot : shiftLimitVertex w (boundaryHitTime w h 1) ⟨0⟩ =
      (⟨boundaryVertex w h 1⟩ : PresentVertex w) :=
    (rightShift_root_labels w h 1 (by omega) hs).1
  change (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
    (shiftLimitVertex w (boundaryHitTime w h 1)
      ⟨boundaryVertex _ hs (-(0 : ℤ))⟩).id).Nonempty
  simp only [neg_zero, boundaryVertex_zero]
  rw [hroot]
  have he : EdgePresent w 0 := ⟨0, by change 0 < 1; omega, by rfl⟩
  have hi := edge_endpoints_eq w (show 0 < (kmswStage w 0).nextEdge by change 0 < 1; omega)
  have hw : edgeWest w 0 = boundaryVertex w h 0 := by
    rw [boundaryVertex_zero, ← hi.1]; rfl
  have hv : edgeEast w 0 = boundaryVertex w h 1 := by
    rw [boundaryVertex_one, ← hi.2]; rfl
  let e : (⟨boundaryVertex w h 0⟩ : PresentVertex w) ⟶ ⟨boundaryVertex w h 1⟩ :=
    ⟨0, he, hw, hv⟩
  refine ⟨1, Path.cons Path.nil e, rfl, ?_⟩
  intro f hf hfp
  have hf0 : f = 0 := by simpa only [pathEdgeList, List.nil_append,
    List.mem_singleton] using hf
  subst f
  have ht : actTime w 0 hfp = 0 := (actTime_eq_iff w 0 hfp 0).mpr rfl
  rw [ht]
  have hh := boundaryHitTime_right_spec w h (show (1 : ℤ) ≤ 1 by omega)
  by_contra hn
  have hz : boundaryHitTime w h 1 = 0 := by omega
  rw [hz] at hh
  have hR : R w 0 = 0 := by simp only [R, Finset.sum_range_zero]
  omega

/-- The finite frontier is nonempty (`lem-directed-contain`, -/
theorem rightFrontierIndices_nonempty (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) :
    (rightFrontierIndices w h hs).Nonempty :=
  ⟨0, zero_mem_rightFrontierIndices w h hs⟩

private theorem allocated_reaches_right_tail_frontier (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (v : PresentVertex w)
    (hv : kmswVertexAllocated w v) :
    ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable v (boundaryPresentVertex w h l) := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨q, hqrec, hnq⟩ :=
    (right_record_infinite w h.R_unbounded_below).exists_gt n
  have hqpos : 0 < q := by omega
  have hrec : ∀ i < q, R w q < R w i := hqrec
  have hneg : R w q < 0 := by
    have hh := hrec 0 hqpos
    simpa only [R, Finset.sum_range_zero] using hh
  let b : ℤ := -R w q
  have hb : 1 ≤ b := by dsimp [b]; omega
  have htime : boundaryHitTime w h b = q := by
    have hle : boundaryHitTime w h b ≤ q := by
      unfold boundaryHitTime
      simp only [dite_eq_right (by omega : b ≠ 0), dite_eq_left (by omega : 0 < b)]
      exact Nat.find_min' (h.rightHit b hb) (by dsimp [b]; omega)
    have hge : q ≤ boundaryHitTime w h b := by
      by_contra hnot
      have hh := hrec (boundaryHitTime w h b) (by omega)
      have hh' := boundaryHitTime_right_spec w h hb
      rw [hh'] at hh
      have hRb : R w q = -b := by dsimp [b]; omega
      omega
    omega
  have heq : recordVertex w q = boundaryPresentVertex w h b := by
    apply congrArg PresentVertex.mk
    rw [boundaryVertex_right_hit_eq w h hb, htime]
    exact (CutConverse.activeInitial_eq w q).symm
  have hvq : v.id < (kmswStage w (q - 1)).nextVertex :=
    hn.trans_le (CutConverse.nextVertex_mono w (by omega : n ≤ q - 1))
  have hr : Reachable v (boundaryPresentVertex w h b) := by
    have hh := allocated_vertex_reaches_strict_record w q
      (fun i hi => by have := hrec i hi; omega) hqpos v.id hvq
    have hvid : (⟨v.id⟩ : PresentVertex w) = v := by cases v; rfl
    rw [hvid, heq] at hh
    exact hh
  refine ⟨b.toNat, fun l hl => hr.trans ?_⟩
  exact boundaryVertex_nonneg_reachable w h (by omega) (by omega)

private theorem rightFrontier_common_sequence (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i))) :
    ∃ y : ℕ → PresentVertex (fun i => w (boundaryHitTime w h 1 + i)),
      Function.Injective y ∧
      (∀ m, kmswVertexAllocated (fun i => w (boundaryHitTime w h 1 + i)) (y m)) ∧
      (∀ j ∈ rightFrontierIndices w h hs, ∀ m,
        Reachable (boundaryPresentVertex _ hs (-(j : ℤ))) (y m)) ∧
      Function.Injective (fun m => shiftLimitVertex w (boundaryHitTime w h 1) (y m)) ∧
      (∀ m, Reachable (boundaryPresentVertex w h 0)
          (shiftLimitVertex w (boundaryHitTime w h 1) (y m)) ∧
        Reachable (boundaryPresentVertex w h 1)
          (shiftLimitVertex w (boundaryHitTime w h 1) (y m))) ∧
      (∀ m, ¬ (earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
        (shiftLimitVertex w (boundaryHitTime w h 1) (y m)).id).Nonempty) := by
  classical
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  have hb : ∀ j : ℕ, ∃ B : ℕ, ∀ l : ℤ, (B : ℤ) ≤ l →
      Reachable (boundaryPresentVertex ws hs (-(j : ℤ)))
        (boundaryPresentVertex ws hs l) := fun j =>
    allocated_reaches_right_tail_frontier ws hs _ (boundaryVertex_left_allocated ws hs (by omega))
  choose B hB using hb
  obtain ⟨K, hK⟩ := ((rightFrontierIndices_finite w h hs).image B).bddAbove
  let z : ℕ → PresentVertex ws := fun m => boundaryPresentVertex ws hs ((K + m : ℕ) : ℤ)
  have hz : Function.Injective z := by
    intro a b hab
    have he := boundaryVertex_injective ws hs (congrArg PresentVertex.id hab)
    change ((K + a : ℕ) : ℤ) = ((K + b : ℕ) : ℤ) at he
    omega
  have ha : ∀ m, kmswVertexAllocated ws (z m) := fun m => boundaryVertex_allocated ws hs _
  have hr : ∀ j ∈ rightFrontierIndices w h hs, ∀ m,
      Reachable (boundaryPresentVertex ws hs (-(j : ℤ))) (z m) := by
    intro j hj m
    apply hB j
    have := hK (Set.mem_image_of_mem B hj)
    exact_mod_cast (show B j ≤ K + m by omega)
  have hiz : Function.Injective (fun m => shiftLimitVertex w t (z m)) := by
    intro a b hab
    exact hz (shiftLimitVertex_injective w t (ha a) (ha b) hab)
  have hf := (early_reachable_finite w t (boundaryPresentVertex w h 0)).preimage
    (fun _ _ _ _ heq => hiz heq)
  obtain ⟨L, hL⟩ := hf.bddAbove
  refine ⟨fun m => z (L + 1 + m), ?_, fun m => ha _, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have := hz hab
    omega
  · exact fun j hj m => hr j hj _
  · intro a b hab
    have := hiz hab
    omega
  · intro m
    have hr0 := hr 0 (zero_mem_rightFrontierIndices w h hs) (L + 1 + m)
    simp only [Nat.cast_zero, neg_zero, boundaryPresentVertex, boundaryVertex_zero] at hr0
    obtain ⟨p⟩ := hr0
    obtain ⟨q, _⟩ := shift_path_map_frontier w t p
    have he : shiftLimitVertex w t ⟨0⟩ = (⟨boundaryVertex w h 1⟩ : PresentVertex w) :=
      (rightShift_root_labels w h 1 (by omega) hs).1
    rw [he] at q
    have hq : Reachable (boundaryPresentVertex w h 1)
        (shiftLimitVertex w t (z (L + 1 + m))) := ⟨q⟩
    exact ⟨(boundaryVertex_nonneg_reachable w h (by omega : (0 : ℤ) ≤ 0)
      (by omega : (0 : ℤ) ≤ 1)).trans hq, hq⟩
  · intro m hm
    obtain ⟨n, p, _, hp⟩ := hm
    have hh := hL (show L + 1 + m ∈
      (fun m => shiftLimitVertex w t (z m)) ⁻¹'
        {v | ∃ p : Path (boundaryPresentVertex w h 0) v,
          ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, actTime w e he < t} from ⟨p, hp⟩)
    omega

private theorem sdp_ne_top_frontier {w : ℕ → Fin 3} {a b : PresentVertex w}
    (hr : Reachable a b) : sdp a b ≠ ⊤ :=
  fun ht => sdp_eq_top_iff_not_reachable.mp ht hr

private theorem neg_inf'_of_enat (s : Finset ℕ) (hs : s.Nonempty)
    (a c : ℕ → ℕ) (Z : ℕ → ℤ) (D d : ℕ)
    (hD : (D : ℕ∞) = ⨅ j ∈ s, (a j : ℕ∞) + (c j : ℕ∞))
    (hZ : ∀ j ∈ s, Z j = (c j : ℤ) - (d : ℤ)) :
    (d : ℤ) - (D : ℤ) = -s.inf' hs (fun j => (a j : ℤ) + Z j) := by
  obtain ⟨k, hk, hmin⟩ := s.exists_mem_eq_inf' hs (fun j => (a j : ℤ) + Z j)
  have hle : D ≤ a k + c k := by
    apply ENat.natCast_le_natCast.mp
    rw [hD, Nat.cast_add]
    exact iInf_le_of_le k (iInf_le _ hk)
  have hge : a k + c k ≤ D := by
    apply ENat.natCast_le_natCast.mp
    rw [hD]
    refine le_iInf₂ fun j hj => ?_
    rw [← Nat.cast_add]
    apply ENat.natCast_le_natCast.mpr
    have hh := s.inf'_le (fun j => (a j : ℤ) + Z j) hj
    rw [hmin, hZ k hk, hZ j hj] at hh
    omega
  rw [hmin, hZ k hk]
  omega

/-- SDP Busemann frontier envelope at the first right hit, with attained
finite early coefficients and a nonempty finite minimum. Conditional on the
explicit crossing-label property (`lem-directed-contain` /
Helper only, not counted; F1/F4 remain. -/
theorem rightFrontier_sdp_busemann (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hlabel : RightFrontierLabels w h hs) (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs) :
    X 1 - X 0 =
      -(rightFrontierIndices_finite w h hs).toFinset.inf'
        ((rightFrontierIndices_finite w h hs).toFinset_nonempty.mpr
          (rightFrontierIndices_nonempty w h hs))
        (fun j => ((earlySdp w (boundaryHitTime w h 1) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs
              (-(j : ℤ))⟩)).toNat : ℤ) + Xs (-(j : ℤ))) := by
  classical
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let s := (rightFrontierIndices_finite w h hs).toFinset
  have hsne : s.Nonempty := (rightFrontierIndices_finite w h hs).toFinset_nonempty.mpr
    (rightFrontierIndices_nonempty w h hs)
  let v := fun j : ℕ => boundaryPresentVertex ws hs (-(j : ℤ))
  let a := fun j => (earlySdp w t (boundaryPresentVertex w h 0)
    (shiftLimitVertex w t (v j))).toNat
  have ha : ∀ j ∈ s, earlySdp w t (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t (v j)) = (a j : ℕ∞) := by
    intro j hj
    obtain ⟨n, _, hn⟩ := earlySdp_attained w t _ _
      ((rightFrontierIndices_finite w h hs).mem_toFinset.mp hj)
    change earlySdp w t (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t (v j)) = (n : ℕ∞) at hn
    dsimp only [a]
    rw [hn, ENat.toNat_natCast]
  obtain ⟨y, hy, hyalloc, hyr, hiy, hir, hfar⟩ := rightFrontier_common_sequence w h hs
  have hstab : ∀ j : s, ∃ N : ℕ, ∀ m, N ≤ m →
      Xs (-(j.val : ℤ)) = ((sdp (v j.val) (y m)).toNat : ℤ) -
        ((sdp (boundaryPresentVertex ws hs 0) (y m)).toNat : ℤ) := by
    intro j
    obtain ⟨N, hN⟩ := hXs.2 0 (-(j.val : ℤ)) y hy (fun m =>
      ⟨by simpa only [Nat.cast_zero, neg_zero] using
          hyr 0 (zero_mem_rightFrontierIndices w h hs) m,
        hyr j.val ((rightFrontierIndices_finite w h hs).mem_toFinset.mp j.property) m⟩)
    refine ⟨N, fun m hm => ?_⟩
    simpa only [hXs.1, sub_zero] using hN m hm
  choose N hN using hstab
  obtain ⟨K, hK⟩ := (Set.finite_range N).bddAbove
  obtain ⟨M, hM⟩ := hX.2 0 1 (fun m => shiftLimitVertex w t (y m)) hiy hir
  let m := max K M
  let b := y m
  let c := fun j => (sdp (v j) b).toNat
  let d := (sdp (boundaryPresentVertex ws hs 0) b).toNat
  let D := (sdp (boundaryPresentVertex w h 0) (shiftLimitVertex w t b)).toNat
  have hc : ∀ j ∈ s, sdp (v j) b = (c j : ℕ∞) := by
    intro j hj
    exact (ENat.natCast_toNat (sdp_ne_top_frontier
      (hyr j ((rightFrontierIndices_finite w h hs).mem_toFinset.mp hj) m))).symm
  have hdecomp : (D : ℕ∞) = ⨅ j ∈ s, (a j : ℕ∞) + (c j : ℕ∞) := by
    rw [show (D : ℕ∞) = sdp (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t b) from
        ENat.natCast_toNat (sdp_ne_top_frontier (hir m).1)]
    have hf := rightFrontier_sdp w h hs hlabel b (hyalloc m) (hfar m)
    change sdp (boundaryPresentVertex w h 0) (shiftLimitVertex w t b) =
      ⨅ j ∈ rightFrontierIndices w h hs,
        earlySdp w t (boundaryPresentVertex w h 0) (shiftLimitVertex w t (v j)) +
          sdp (v j) b at hf
    rw [hf]
    apply iInf_congr
    intro j
    change (⨅ _hj : j ∈ rightFrontierIndices w h hs, _) = _
    rw [← (rightFrontierIndices_finite w h hs).mem_toFinset]
    apply iInf_congr
    intro hj
    rw [ha j hj, hc j hj]
  have hZ : ∀ j ∈ s, Xs (-(j : ℤ)) = (c j : ℤ) - (d : ℤ) := by
    intro j hj
    exact hN ⟨j, hj⟩ m ((hK (Set.mem_range_self ⟨j, hj⟩)).trans (Nat.le_max_left _ _))
  have hg := hM m (Nat.le_max_right _ _)
  have he := (rightShift_distances w h 1 (by omega) hs b (hyalloc m)).1
  have hd : sdp (boundaryPresentVertex w h 1) (shiftLimitVertex w t b) =
      sdp (boundaryPresentVertex ws hs 0) b := by
    change sdp (boundaryPresentVertex w h 1) (shiftLimitVertex w t b) =
      sdp (⟨0⟩ : PresentVertex ws) b at he
    simpa only [boundaryPresentVertex, boundaryVertex_zero] using he
  rw [hd] at hg
  exact hg.trans (neg_inf'_of_enat s hsne a c (fun j => Xs (-(j : ℤ))) D d hdecomp hZ)

private theorem neg_sup'_of_withBot (s : Finset ℕ) (hs : s.Nonempty)
    (a c : ℕ → ℕ) (Z : ℕ → ℤ) (D d : ℕ)
    (hD : (D : WithBot ℕ) =
      sSup ((fun j => (a j : WithBot ℕ) + (c j : WithBot ℕ)) '' (s : Set ℕ)))
    (hZ : ∀ j ∈ s, Z j = (c j : ℤ) - (d : ℤ)) :
    (d : ℤ) - (D : ℤ) = -s.sup' hs (fun j => (a j : ℤ) + Z j) := by
  obtain ⟨k, hk, hmax⟩ := s.exists_mem_eq_sup' hs (fun j => (a j : ℤ) + Z j)
  have hge : a k + c k ≤ D := by
    apply WithBot.coe_le_coe.mp
    change ((a k + c k : ℕ) : WithBot ℕ) ≤ (D : WithBot ℕ)
    rw [hD, Nat.cast_add]
    exact le_csSup (s.finite_toSet.image _).bddAbove ⟨k, hk, rfl⟩
  have hle : D ≤ a k + c k := by
    apply WithBot.coe_le_coe.mp
    change (D : WithBot ℕ) ≤ ((a k + c k : ℕ) : WithBot ℕ)
    rw [hD]
    apply csSup_le'
    rintro _ ⟨j, hj, rfl⟩
    dsimp only
    rw [← Nat.cast_add]
    apply WithBot.coe_le_coe.mpr
    change a j + c j ≤ a k + c k
    have hh := s.le_sup' (fun j => (a j : ℤ) + Z j) hj
    rw [hmax, hZ k hk, hZ j hj] at hh
    omega
  rw [hmax, hZ k hk]
  omega

private theorem ldpSup_eq_finite_frontier {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) : ldpSup a b = (presentLdpFiniteNat hb hr : WithBot ℕ) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  rw [presentLdpFiniteNat_eq_length hb hr hp]
  exact ldpSup_eq_longest_frontier hp

/-- LDP Busemann frontier envelope at the first right hit. The natural
coefficients are attained early longest lengths, and the maximum is over the
explicitly nonempty finite frontier. Conditional on the crossing-label
property (`lem-directed-contain` / `lem-uibot-bdy`, -/
theorem rightFrontier_ldp_busemann (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h 1 + i)))
    (hlabel : RightFrontierLabels w h hs)
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h 1 + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs) :
    ∃ A : ℕ → ℕ,
      (∀ j ∈ rightFrontierIndices w h hs,
        A j ∈ earlyPathLengths w (boundaryHitTime w h 1) (boundaryVertex w h 0)
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩).id ∧
        earlyLdp w (boundaryHitTime w h 1) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h 1)
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h 1 + i)) hs (-(j : ℤ))⟩) =
              (A j : WithBot ℕ)) ∧
      X 1 - X 0 = -(rightFrontierIndices_finite w h hs).toFinset.sup'
        ((rightFrontierIndices_finite w h hs).toFinset_nonempty.mpr
          (rightFrontierIndices_nonempty w h hs))
        (fun j => (A j : ℤ) + Xs (-(j : ℤ))) := by
  classical
  let t := boundaryHitTime w h 1
  let ws := fun i => w (t + i)
  let s := (rightFrontierIndices_finite w h hs).toFinset
  have hsne : s.Nonempty := (rightFrontierIndices_finite w h hs).toFinset_nonempty.mpr
    (rightFrontierIndices_nonempty w h hs)
  let v := fun j : ℕ => boundaryPresentVertex ws hs (-(j : ℤ))
  have hatt : ∀ j : ℕ, ∃ n : ℕ, j ∈ rightFrontierIndices w h hs →
      n ∈ earlyPathLengths w t (boundaryVertex w h 0) (shiftLimitVertex w t (v j)).id ∧
        earlyLdp w t (boundaryPresentVertex w h 0) (shiftLimitVertex w t (v j)) =
          (n : WithBot ℕ) := by
    intro j
    by_cases hj : j ∈ rightFrontierIndices w h hs
    · obtain ⟨n, hn, he⟩ := earlyLdp_attained w t hb
        (boundaryPresentVertex w h 0) (shiftLimitVertex w t (v j)) hj
      exact ⟨n, fun _ => ⟨hn, he⟩⟩
    · exact ⟨0, fun hj' => (hj hj').elim⟩
  choose A hA using hatt
  refine ⟨A, hA, ?_⟩
  obtain ⟨y, hy, hyalloc, hyr, hiy, hir, hfar⟩ := rightFrontier_common_sequence w h hs
  have hr0 : ∀ m, Reachable (boundaryPresentVertex ws hs 0) (y m) := by
    intro m
    simpa only [Nat.cast_zero, neg_zero] using hyr 0 (zero_mem_rightFrontierIndices w h hs) m
  have hstab : ∀ j : s, ∃ N : ℕ, ∀ m, N ≤ m →
      Xs (-(j.val : ℤ)) =
        (presentLdpFiniteNat hbs
          (hyr j.val ((rightFrontierIndices_finite w h hs).mem_toFinset.mp j.property) m) : ℤ) -
        (presentLdpFiniteNat hbs (hr0 m) : ℤ) := by
    intro j
    obtain ⟨N, hN⟩ := hXs.2 0 (-(j.val : ℤ)) y hy (fun m =>
      ⟨hr0 m, hyr j.val ((rightFrontierIndices_finite w h hs).mem_toFinset.mp j.property) m⟩)
    exact ⟨N, fun m hm => by simpa only [hXs.1, sub_zero] using hN m hm⟩
  choose N hN using hstab
  obtain ⟨K, hK⟩ := (Set.finite_range N).bddAbove
  obtain ⟨M, hM⟩ := hX.2 0 1 (fun m => shiftLimitVertex w t (y m)) hiy hir
  let m := max K M
  let b := y m
  let d := presentLdpFiniteNat hbs (hr0 m)
  let D := presentLdpFiniteNat hb (hir m).1
  have hcex : ∀ j : ℕ, ∃ n : ℕ, j ∈ s → ldpSup (v j) b = (n : WithBot ℕ) := by
    intro j
    by_cases hj : j ∈ s
    · have hrj := hyr j ((rightFrontierIndices_finite w h hs).mem_toFinset.mp hj) m
      exact ⟨presentLdpFiniteNat hbs hrj, fun _ => ldpSup_eq_finite_frontier hbs hrj⟩
    · exact ⟨0, fun hj' => (hj hj').elim⟩
  choose c hc using hcex
  have hcval : ∀ j (hj : j ∈ s), c j = presentLdpFiniteNat hbs
      (hyr j ((rightFrontierIndices_finite w h hs).mem_toFinset.mp hj) m) := by
    intro j hj
    apply WithBot.coe_injective
    exact (hc j hj).symm.trans (ldpSup_eq_finite_frontier hbs _)
  have hdecomp : (D : WithBot ℕ) =
      sSup ((fun j => (A j : WithBot ℕ) + (c j : WithBot ℕ)) '' (s : Set ℕ)) := by
    have hf := rightFrontier_ldpSup w h hs hlabel hb b (hyalloc m) (hfar m)
    change ldpSup (boundaryPresentVertex w h 0) (shiftLimitVertex w t b) =
      sSup ((fun j => earlyLdp w t (boundaryPresentVertex w h 0)
        (shiftLimitVertex w t (v j)) + ldpSup (v j) b) '' rightFrontierIndices w h hs) at hf
    rw [← ldpSup_eq_finite_frontier hb (hir m).1]
    rw [hf]
    congr 1
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjs := (rightFrontierIndices_finite w h hs).mem_toFinset.mpr hj
      exact ⟨j, hjs, by dsimp only; rw [(hA j hj).2, hc j hjs]⟩
    · rintro ⟨j, hj, rfl⟩
      have hjJ := (rightFrontierIndices_finite w h hs).mem_toFinset.mp hj
      exact ⟨j, hjJ, by dsimp only; rw [(hA j hjJ).2, hc j hj]⟩
  have hZ : ∀ j ∈ s, Xs (-(j : ℤ)) = (c j : ℤ) - (d : ℤ) := by
    intro j hj
    rw [hcval j hj]
    exact hN ⟨j, hj⟩ m ((hK (Set.mem_range_self ⟨j, hj⟩)).trans (Nat.le_max_left _ _))
  have he : ldpSup (boundaryPresentVertex w h 1) (shiftLimitVertex w t b) =
      ldpSup (⟨0⟩ : PresentVertex ws) b :=
    (rightShift_distances w h 1 (by omega) hs b (hyalloc m)).2.2.1
  have hefin : presentLdpFiniteNat hb (hir m).2 = d := by
    apply WithBot.coe_injective
    change (presentLdpFiniteNat hb (hir m).2 : WithBot ℕ) = (d : WithBot ℕ)
    rw [← ldpSup_eq_finite_frontier hb (hir m).2]
    rw [he]
    exact ldpSup_eq_finite_frontier hbs (hr0 m)
  have hg := hM m (Nat.le_max_right _ _)
  rw [hefin] at hg
  exact hg.trans (neg_sup'_of_withBot s hsne A c (fun j => Xs (-(j : ℤ))) D d hdecomp hZ)

end DirectedDistances.Recursive
