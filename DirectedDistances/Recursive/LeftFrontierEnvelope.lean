module

public import DirectedDistances.KMSW.LeftHitFrontierEntries
public import DirectedDistances.KMSW.PathTimeCut
public import DirectedDistances.KMSW.RightShiftAllGeometry
public import DirectedDistances.KMSW.LeftStationaryGeometry
public import DirectedDistances.Recursive.LeftStationaryBusemann
public import DirectedDistances.Recursive.IndependenceFromLR
public import DirectedDistances.Recursive.RightFrontierEnvelope

/-! Supporting lemmas for paper labels `lem-directed-contain` (see CORRESPONDENCE.md). -/

/-! # Frontier envelopes at the first left hit

Helpers for the frontier decomposition in `item-busemann-ind`,
These helpers are not counted as numbered paper results; F1/F4 remain. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- Reachability using only edges activated strictly before the cutoff.
All early paths, including paths along the interface, are allowed. -/
@[expose] def EarlyReachable (w : ℕ → Fin 3) (t : ℕ)
    (a b : PresentVertex w) : Prop :=
  ∃ p : Path a b, ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e,
    actTime w e he < t

/-- The globally embedded positive shifted boundary labels at a left hit. -/
@[expose] noncomputable def leftFrontierVertex (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (j : ℕ) : PresentVertex w :=
  shiftLimitVertex w (boundaryHitTime w h (-1))
    (boundaryPresentVertex _ hs (j : ℤ))

/-- The positive east-interface labels reachable from `x₀` by an early path -/
@[expose] def leftFrontierIndices (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i))) : Set ℕ :=
  {j | 1 ≤ j ∧ EarlyReachable w (boundaryHitTime w h (-1))
    (boundaryPresentVertex w h 0) (leftFrontierVertex w h hs j)}

private theorem earlySdp_le_length {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (p : Path a b)
    (hp : ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, actTime w e he < t) :
    earlySdp w t a b ≤ p.length := by
  exact iInf_le_of_le p.length (iInf_le _ ⟨p, rfl, hp⟩)

private theorem exists_length_eq_earlySdp {w : ℕ → Fin 3} {t : ℕ}
    {a b : PresentVertex w} (hr : EarlyReachable w t a b) :
    ∃ p : Path a b,
      (∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, actTime w e he < t) ∧
      (p.length : ℕ∞) = earlySdp w t a b := by
  obtain ⟨p, hp⟩ := hr
  obtain ⟨n, ⟨q, hq, he⟩, hn⟩ := earlySdp_attained w t a b ⟨p.length, p, rfl, hp⟩
  exact ⟨q, he, by rw [hq, hn]⟩

/-- The left-hit interface index set is finite. This uses the finite early
reachable set and injectivity on allocated shifted boundary vertices. -/
theorem leftFrontierIndices_finite (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i))) :
    (leftFrontierIndices w h hs).Finite := by
  have hi : Function.Injective (leftFrontierVertex w h hs) := by
    intro a b hab
    have he := shiftLimitVertex_injective w (boundaryHitTime w h (-1))
      (boundaryVertex_allocated _ hs (a : ℤ))
      (boundaryVertex_allocated _ hs (b : ℤ)) hab
    have hab' := boundaryVertex_injective _ hs (congrArg PresentVertex.id he)
    exact_mod_cast hab'
  apply ((early_reachable_finite w (boundaryHitTime w h (-1))
    (boundaryPresentVertex w h 0)).preimage (fun _ _ _ _ heq => hi heq)).subset
  exact fun _ hj => hj.2

private theorem path_first_edge {w : ℕ → Fin 3} {a b : PresentVertex w}
    (p : Path a b) :
    a = b ∨ ∃ e, ∃ _he : EdgePresent w e,
      e ∈ pathEdgeList p ∧ edgeWest w e = a.id := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons c d p e ih =>
    right
    rcases ih with hac | ⟨f, hf, hfp, hfa⟩
    · exact ⟨e.val, e.property.1,
        List.mem_append_right _ (List.mem_singleton.mpr rfl),
        e.property.2.1.trans (congrArg PresentVertex.id hac.symm)⟩
    · exact ⟨f, hf, List.mem_append_left _ hfp, hfa⟩

/-- Every path to a target outside the early reachable set splits at a
positive shifted east label. The late suffix lifts with exactly the same -/
theorem leftHit_path_length_factorization (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (b : PresentVertex (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : kmswVertexAllocated _ b)
    (hnot : ¬ EarlyReachable w (boundaryHitTime w h (-1))
      (boundaryPresentVertex w h 0) (shiftLimitVertex w (boundaryHitTime w h (-1)) b))
    (p : Path (boundaryPresentVertex w h 0)
      (shiftLimitVertex w (boundaryHitTime w h (-1)) b)) :
    ∃ j ∈ leftFrontierIndices w h hs,
      ∃ pe : Path (boundaryPresentVertex w h 0) (leftFrontierVertex w h hs j),
      ∃ q : Path (boundaryPresentVertex _ hs (j : ℤ)) b,
        (∀ e ∈ pathEdgeList pe, ∀ he : EdgePresent w e,
          actTime w e he < boundaryHitTime w h (-1)) ∧
        p.length = pe.length + q.length := by
  obtain ⟨u, pe, pl, hp, he, hl⟩ :=
    path_exists_early_late_factorization (boundaryHitTime w h (-1)) p
  have hin : u = ⟨boundaryVertex w h 0⟩ ∨
      ∃ e, ∃ he : EdgePresent w e,
        actTime w e he < boundaryHitTime w h (-1) ∧ edgeEast w e = u.id := by
    cases pe with
    | nil => exact Or.inl rfl
    | cons pe e =>
      exact Or.inr ⟨e.val, e.property.1,
        he e.val (List.mem_append_right _ (List.mem_singleton.mpr rfl)) e.property.1,
        e.property.2.2⟩
  have hout : ∃ f, ∃ hf : EdgePresent w f,
      boundaryHitTime w h (-1) ≤ actTime w f hf ∧ edgeWest w f = u.id := by
    rcases path_first_edge pl with hu | ⟨f, hf, hfp, hfu⟩
    · exact False.elim (hnot (hu ▸ ⟨pe, he⟩))
    · exact ⟨f, hf, hl f hfp hf, hfu⟩
  obtain ⟨j, hj, hu⟩ := leftHit_crossing_eq_shifted_east_label w h hs u hin hout
  change u = leftFrontierVertex w h hs j at hu
  subst u
  obtain ⟨b', hb', q, hq, hlen, _⟩ := shiftLimitVertex_late_path_lift w
    (boundaryHitTime w h (-1)) (boundaryPresentVertex _ hs (j : ℤ))
    (boundaryVertex_allocated _ hs _) pl hl
  have hbb := shiftLimitVertex_injective w (boundaryHitTime w h (-1)) hb' hb hq
  subst b'
  refine ⟨j, ⟨hj, pe, he⟩, pe, q, he, ?_⟩
  rw [hp, Path.length_comp, hlen]
  rfl

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

/-- Exact convolution of all early-prefix and shifted-suffix lengths at the -/
theorem leftFrontier_pathLengths (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (b : PresentVertex (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : kmswVertexAllocated _ b)
    (hfar : ¬ EarlyReachable w (boundaryHitTime w h (-1))
      (boundaryPresentVertex w h 0) (shiftLimitVertex w (boundaryHitTime w h (-1)) b)) :
    pathLengths (boundaryPresentVertex w h 0)
        (shiftLimitVertex w (boundaryHitTime w h (-1)) b) =
      {n | ∃ j ∈ leftFrontierIndices w h hs, ∃ a c : ℕ,
        a ∈ earlyPathLengths w (boundaryHitTime w h (-1)) (boundaryVertex w h 0)
          (leftFrontierVertex w h hs j).id ∧
        c ∈ pathLengths (boundaryPresentVertex _ hs (j : ℤ)) b ∧ n = a + c} := by
  ext n
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨j, hj, pe, q, he, hlen⟩ :=
      leftHit_path_length_factorization w h hs b hb hfar p
    exact ⟨j, hj, pe.length, q.length, ⟨pe, rfl, he⟩, ⟨q, rfl⟩, hlen⟩
  · rintro ⟨j, _, a, c, ⟨pe, hpe, _⟩, ⟨pl, hpl⟩, rfl⟩
    obtain ⟨q, hq⟩ := shift_path_map_frontier w (boundaryHitTime w h (-1)) pl
    change Path (boundaryPresentVertex w h 0)
      (shiftLimitVertex w (boundaryHitTime w h (-1)) (boundaryPresentVertex _ hs (j : ℤ))) at pe
    refine ⟨pe.comp q, ?_⟩
    change (pe.comp q).length = a + c
    change pl.length = c at hpl
    exact (Path.length_comp pe q).trans (congrArg₂ (· + ·) hpe (hq.trans hpl))

/- SDP is the infimum over the finite positive east frontier, with the -/
theorem leftFrontier_sdp (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (b : PresentVertex (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h (-1) + i)) b)
    (hfar : ¬ EarlyReachable w (boundaryHitTime w h (-1))
      (boundaryPresentVertex w h 0) (shiftLimitVertex w (boundaryHitTime w h (-1)) b)) :
    sdp (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h (-1)) b) =
      ⨅ j ∈ leftFrontierIndices w h hs,
        earlySdp w (boundaryHitTime w h (-1)) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h (-1))
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩) +
        sdp (⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h (-1) + i))) b := by
  have hlengths := leftFrontier_pathLengths w h hs b hb hfar
  dsimp only [boundaryPresentVertex, leftFrontierVertex] at hlengths
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
    obtain ⟨r, hr⟩ := shift_path_map_frontier w (boundaryHitTime w h (-1)) q
    exact (sdp_le_length (pe.comp r)).trans_eq (by
      rw [Path.length_comp, hpe, hr, ENat.natCast_add])
  · refine le_iInf fun p => ?_
    have hp : p.length ∈ pathLengths
        (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h (-1)) b) := ⟨p, rfl⟩
    rw [hlengths] at hp
    obtain ⟨j, hj, a, c, ha, ⟨q, hq⟩, hn⟩ := hp
    refine iInf_le_of_le j (iInf_le_of_le hj ?_)
    calc
      _ ≤ (a : ℕ∞) + (c : ℕ∞) := add_le_add
        (iInf_le_of_le a (iInf_le _ ha))
        ((sdp_le_length q).trans_eq (congrArg (fun n : ℕ => (n : ℕ∞)) hq))
      _ = (p.length : ℕ∞) := by rw [← ENat.natCast_add, ← hn]

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

/-- Under path-length boundedness, the LDP envelope is the maximum over the
finite positive east frontier, retaining `⊥` for unreachable suffixes.
Not counted; F1/F4 remain. -/
theorem leftFrontier_ldpSup (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (hbound : PresentPathLengthsBounded (w := w))
    (b : PresentVertex (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : kmswVertexAllocated (fun i => w (boundaryHitTime w h (-1) + i)) b)
    (hfar : ¬ EarlyReachable w (boundaryHitTime w h (-1))
      (boundaryPresentVertex w h 0) (shiftLimitVertex w (boundaryHitTime w h (-1)) b)) :
    ldpSup (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        (shiftLimitVertex w (boundaryHitTime w h (-1)) b) =
      sSup ((fun j : ℕ =>
        earlyLdp w (boundaryHitTime w h (-1)) ⟨boundaryVertex w h 0⟩
          (shiftLimitVertex w (boundaryHitTime w h (-1))
            ⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩) +
        ldpSup (⟨boundaryVertex (fun i => w (boundaryHitTime w h (-1) + i)) hs (j : ℤ)⟩ :
          PresentVertex (fun i => w (boundaryHitTime w h (-1) + i))) b) ''
        leftFrontierIndices w h hs) := by
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  let a := fun j : ℕ => (⟨boundaryVertex ws hs (j : ℤ)⟩ : PresentVertex ws)
  let x : PresentVertex w := ⟨boundaryVertex w h 0⟩
  let F := fun j : ℕ => earlyLdp w t x (shiftLimitVertex w t (a j)) + ldpSup (a j) b
  have hfinite : (F '' leftFrontierIndices w h hs).Finite :=
    (leftFrontierIndices_finite w h hs).image F
  have hbs := shift_bounded_frontier w t hbound
  have hlengths := leftFrontier_pathLengths w h hs b hb hfar
  dsimp only [boundaryPresentVertex, leftFrontierVertex] at hlengths
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
    obtain ⟨n, hn, heq⟩ := earlyLdp_attained w t hbound x (shiftLimitVertex w t (a j))
      (by obtain ⟨p, hp⟩ := hj.2; exact ⟨p.length, p, rfl, hp⟩)
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

private theorem shift_allocated_leftEnvelope (w : ℕ → Fin 3) (t : ℕ)
    (a : PresentVertex (fun i => w (t + i))) (ha : kmswVertexAllocated _ a) :
    kmswVertexAllocated w (shiftLimitVertex w t a) := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨t + n, ?_⟩
  rw [shiftLimitVertex_eq w t n a hn]
  exact (kmswShift_sim2_all w t n).sim.vertex_bound a.id hn

private theorem path_late_of_incoming_leftEnvelope {w : ℕ → Fin 3} {t : ℕ}
    {a b c : PresentVertex w} (e : a ⟶ b)
    (he : t ≤ actTime w e.val e.property.1) (p : Path b c) :
    ∀ f ∈ pathEdgeList p, ∀ hf : EdgePresent w f, t ≤ actTime w f hf := by
  have hh := pathEdgeList_actTime_pairwise (e.toPath.comp p)
  rw [pathEdgeList_comp] at hh
  have hcross := (List.pairwise_append.mp hh).2.2
  intro f hf hfp
  exact he.trans (hcross e.val (by simp [pathEdgeList, Quiver.Hom.toPath])
    f hf e.property.1 hfp).le




theorem leftFrontier_common_sequence (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i))) :
    ∃ y : ℕ → PresentVertex (fun i => w (boundaryHitTime w h (-1) + i)),
      Function.Injective y ∧
      (∀ m, kmswVertexAllocated _ (y m)) ∧
      (∀ m, Reachable (boundaryPresentVertex _ hs 0) (y m)) ∧
      (∀ j ∈ leftFrontierIndices w h hs, ∀ m,
        Reachable (boundaryPresentVertex _ hs (j : ℤ)) (y m)) ∧
      Function.Injective (fun m => shiftLimitVertex w (boundaryHitTime w h (-1)) (y m)) ∧
      (∀ m, Reachable (boundaryPresentVertex w h 0)
        (shiftLimitVertex w (boundaryHitTime w h (-1)) (y m))) := by
  classical
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  obtain ⟨B, hB⟩ := (leftFrontierIndices_finite w h hs).bddAbove
  let K := B + 2
  let a : PresentVertex ws := boundaryPresentVertex ws hs (K : ℤ)
  have ha : kmswVertexAllocated ws a := by
    change ∃ n, boundaryVertex ws hs (K : ℤ) < (kmswStage ws n).nextVertex
    exact boundaryVertex_allocated ws hs _
  have hai := shift_allocated_leftEnvelope w t a ha
  let x : ℤ → PresentVertex w := fun k =>
    if k = 0 then boundaryPresentVertex w h 0 else shiftLimitVertex w t a
  have hx : ∀ k, kmswVertexAllocated w (x k) := by
    intro k
    dsimp only [x]
    split_ifs
    · exact boundaryVertex_allocated w h 0
    · exact hai
  obtain ⟨z, hz, hzr⟩ := allocatedEnumeration_commonSequence_of_R_unbounded w
    (R_unbounded_below_of_boundaryHitWitnesses w h) x hx 0 1
  have hzr' : ∀ m, Reachable (boundaryPresentVertex w h 0) (z m) ∧
      Reachable (shiftLimitVertex w t a) (z m) := by
    simpa only [x, ite_eq_left rfl, ite_eq_right (by omega : (1 : ℤ) ≠ 0)] using hzr
  have hlate : ∀ m, ∀ p : Path (shiftLimitVertex w t a) (z m),
      ∀ e ∈ pathEdgeList p, ∀ he : EdgePresent w e, t ≤ actTime w e he := by
    intro m p
    have hK : 1 ≤ K - 1 := by dsimp [K]; omega
    obtain ⟨he, hw, ht⟩ := boundaryVertex_right_edge_present_source ws hs hK
    let ef : {e // EdgePresent ws e} := ⟨kmswRightBoundaryEdge ws (K - 1), he⟩
    have hinc := shiftLimitEdge_incidence w t ef
    have hc : ((K - 1 : ℕ) : ℤ) + 1 = (K : ℤ) := by dsimp [K]; omega
    rw [ht, hc] at hinc
    let e : (⟨edgeWest w (shiftLimitEdge w t ef)⟩ : PresentVertex w) ⟶
        shiftLimitVertex w t a :=
      ⟨shiftLimitEdge w t ef, shiftLimitEdge_present w t ef, rfl, hinc.2⟩
    apply path_late_of_incoming_leftEnvelope e ?_ p
    rw [shiftLimitEdge_actTime]
    exact Nat.le_add_right _ _
  have hlift : ∀ m, ∃ b : PresentVertex ws, kmswVertexAllocated ws b ∧
      Reachable a b ∧ shiftLimitVertex w t b = z m := by
    intro m
    obtain ⟨p⟩ := (hzr' m).2
    obtain ⟨b, hb, q, hq, _, _⟩ := shiftLimitVertex_late_path_lift w t a ha p (hlate m p)
    exact ⟨b, hb, ⟨q⟩, hq⟩
  choose y hyalloc hyr hymap using hlift
  have hiy : Function.Injective y := by
    intro m n he
    apply hz
    rw [← hymap m, ← hymap n, he]
  refine ⟨y, hiy, hyalloc, ?_, ?_, ?_, ?_⟩
  · intro m
    exact (boundaryVertex_nonneg_reachable ws hs (by omega : (0 : ℤ) ≤ 0)
      (by dsimp [K]; omega : (0 : ℤ) ≤ (K : ℤ))).trans (hyr m)
  · intro j hj m
    exact (boundaryVertex_nonneg_reachable ws hs (by omega : (0 : ℤ) ≤ (j : ℤ))
      (by have := hB hj; dsimp [K]; omega : (j : ℤ) ≤ (K : ℤ))).trans (hyr m)
  · intro m n he
    exact hz ((hymap m).symm.trans (he.trans (hymap n)))
  · intro m
    rw [hymap]
    exact (hzr' m).1

private theorem eventually_not_earlyReachable_leftEnvelope (w : ℕ → Fin 3)
    (t : ℕ) (x : PresentVertex w) (y : ℕ → PresentVertex w)
    (hy : Function.Injective y) :
    ∀ᶠ m in Filter.atTop, ¬ EarlyReachable w t x (y m) := by
  have hf := (early_reachable_finite w t x).preimage
    (fun _ _ _ _ heq => hy heq)
  obtain ⟨B, hB⟩ := hf.bddAbove
  refine Filter.eventually_atTop.mpr ⟨B + 1, ?_⟩
  intro m hm hbad
  have hh := hB hbad
  omega

/- The SDP increment is the attained finite minimum of all early-prefix
Not counted; F1/F4 remain. -/
theorem leftFrontier_sdp_busemann_isLeast (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs) :
    IsLeast ((fun j : ℕ =>
      ((earlySdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).toNat : ℤ) + Xs (j : ℤ)) ''
      leftFrontierIndices w h hs) (X 0 - X (-1)) := by
  classical
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  let J := leftFrontierIndices w h hs
  let A := fun j : ℕ => (earlySdp w t (boundaryPresentVertex w h 0)
    (leftFrontierVertex w h hs j)).toNat
  obtain ⟨y, hy, ha, hr0, hrj, hiy, hir⟩ := leftFrontier_common_sequence w h hs
  have hrbase : ∀ m, Reachable (boundaryPresentVertex w h (-1))
      (shiftLimitVertex w t (y m)) := by
    intro m
    have hh := (leftShift_reachable_iff w h (k := -1) (by omega) hs
      (by omega : (0 : ℤ) ≤ 0) (y m) (ha m)).mpr (hr0 m)
    simpa only [add_zero, boundaryPresentVertex, t] using hh
  have hg : ∀ᶠ m in Filter.atTop, X 0 - X (-1) =
      ((sdp (boundaryPresentVertex w h 0) (shiftLimitVertex w t (y m))).toNat : ℤ) -
      ((sdp (boundaryPresentVertex ws hs 0) (y m)).toNat : ℤ) := by
    obtain ⟨N, hN⟩ := hX.2 (-1) 0 _ hiy (fun m => ⟨hrbase m, hir m⟩)
    refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
    have hd := (leftShift_distances w h (k := -1) (by omega) hs
      (by omega : (0 : ℤ) ≤ 0) (y m) (ha m)).1
    rw [add_zero] at hd
    have hNm := hN m hm
    rw [hd] at hNm
    exact hNm
  have hsj : ∀ᶠ m in Filter.atTop, ∀ j ∈ J,
      Xs (j : ℤ) = ((sdp (boundaryPresentVertex ws hs (j : ℤ)) (y m)).toNat : ℤ) -
        ((sdp (boundaryPresentVertex ws hs 0) (y m)).toNat : ℤ) := by
    apply (leftFrontierIndices_finite w h hs).eventually_all.mpr
    intro j hj
    obtain ⟨N, hN⟩ := hXs.2 0 (j : ℤ) y hy (fun m => ⟨hr0 m, hrj j hj m⟩)
    exact Filter.eventually_atTop.mpr ⟨N, fun m hm => by
      simpa only [hXs.1, sub_zero] using hN m hm⟩
  have hf := eventually_not_earlyReachable_leftEnvelope w t
    (boundaryPresentVertex w h 0) _ hiy
  obtain ⟨m, hmfar, hmg, hms⟩ := (hf.and (hg.and hsj)).exists
  obtain ⟨p, hp⟩ := exists_length_eq_sdp (hir m)
  have hpn : (sdp (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t (y m))).toNat = p.length := by
    rw [← hp, ENat.toNat_natCast]
  have hlower : ∀ j ∈ J, X 0 - X (-1) ≤ (A j : ℤ) + Xs (j : ℤ) := by
    intro j hj
    obtain ⟨pe, he, hpe⟩ := exists_length_eq_earlySdp hj.2
    obtain ⟨q, hq⟩ := exists_length_eq_sdp (hrj j hj m)
    obtain ⟨q', hq'⟩ := shift_path_map_frontier w t q
    have hA : A j = pe.length := by dsimp [A]; rw [← hpe, ENat.toNat_natCast]
    have hqn : (sdp (boundaryPresentVertex ws hs (j : ℤ)) (y m)).toNat = q.length := by
      rw [← hq, ENat.toNat_natCast]
    change Path (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t (boundaryPresentVertex ws hs (j : ℤ))) at pe
    have hle := ENat.toNat_le_of_le_natCast (sdp_le_length (pe.comp q'))
    have hle' := hle.trans_eq ((Path.length_comp pe q').trans
      (congrArg (pe.length + ·) hq'))
    have hv := hms j hj
    dsimp only [leftFrontierVertex, boundaryPresentVertex, ws, t] at hle' hA hqn hpn hv hmg ⊢
    omega
  obtain ⟨j, hj, pe, q, he, hlen⟩ :=
    leftHit_path_length_factorization w h hs (y m) (ha m) hmfar p
  have hAle : A j ≤ pe.length :=
    ENat.toNat_le_of_le_natCast (earlySdp_le_length pe he)
  have hqle := ENat.toNat_le_of_le_natCast (sdp_le_length q)
  change (sdp (boundaryPresentVertex ws hs (j : ℤ)) (y m)).toNat ≤ q.length at hqle
  have hv := hms j hj
  have hl := hlower j hj
  rw [hpn] at hmg
  have heq : (A j : ℤ) + Xs (j : ℤ) = X 0 - X (-1) := by omega
  exact ⟨⟨j, hj, heq⟩, fun _ ⟨j, hj, heq⟩ => heq ▸ hlower j hj⟩



theorem leftFrontier_sdp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannSDP (boundaryPresentVertex _ hs) Xs) :
    X 0 - X (-1) = sInf ((fun j : ℕ =>
      ((earlySdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).toNat : ℤ) + Xs (j : ℤ)) ''
      leftFrontierIndices w h hs) :=
  (leftFrontier_sdp_busemann_isLeast w h hs X Xs hX hXs).csInf_eq.symm

private theorem ldpFinite_eq_lengths_leftEnvelope {w ws : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := ws))
    {a b : PresentVertex w} {c d : PresentVertex ws}
    (hr : Reachable a b) (hs : Reachable c d)
    (heq : {n | ∃ p : Path a b, p.length = n} =
      {n | ∃ p : Path c d, p.length = n}) :
    presentLdpFiniteNat hb hr = presentLdpFiniteNat hbs hs := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hbs c d hs) hs
  rw [presentLdpFiniteNat_eq_length hb hr hp, presentLdpFiniteNat_eq_length hbs hs hq]
  obtain ⟨p', hp'⟩ := (Set.ext_iff.mp heq p.length).mp ⟨p, rfl⟩
  obtain ⟨q', hq'⟩ := (Set.ext_iff.mp heq q.length).mpr ⟨q, rfl⟩
  have hpq := hq p'
  have hqp := hp q'
  omega

private theorem length_le_ldpFinite_leftEnvelope {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) (p : Path a b) : p.length ≤ presentLdpFiniteNat hb hr := by
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  rw [presentLdpFiniteNat_eq_length hb hr hq]
  exact hq p

/- Bounded LDP increment as an attained maximum over the finite positive
east interface. Integer conversion of early LDP is used only on `J`, where
Not counted; F1/F4 remain. -/
theorem leftFrontier_ldp_busemann_isGreatest (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs) :
    IsGreatest ((fun j : ℕ =>
      (((earlyLdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).unbotD 0 : ℕ) : ℤ) + Xs (j : ℤ)) ''
      leftFrontierIndices w h hs) (X 0 - X (-1)) := by
  classical
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  let J := leftFrontierIndices w h hs
  let A := fun j : ℕ => (earlyLdp w t (boundaryPresentVertex w h 0)
    (leftFrontierVertex w h hs j)).unbotD 0
  obtain ⟨y, hy, ha, hr0, hrj, hiy, hir⟩ := leftFrontier_common_sequence w h hs
  have hrbase : ∀ m, Reachable (boundaryPresentVertex w h (-1))
      (shiftLimitVertex w t (y m)) := by
    intro m
    have hh := (leftShift_reachable_iff w h (k := -1) (by omega) hs
      (by omega : (0 : ℤ) ≤ 0) (y m) (ha m)).mpr (hr0 m)
    simpa only [add_zero, boundaryPresentVertex, t] using hh
  have hg : ∀ᶠ m in Filter.atTop, X 0 - X (-1) =
      (presentLdpFiniteNat hb (hir m) : ℤ) -
      (presentLdpFiniteNat hbs (hr0 m) : ℤ) := by
    obtain ⟨N, hN⟩ := hX.2 (-1) 0 _ hiy (fun m => ⟨hrbase m, hir m⟩)
    refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
    have hd := leftShift_path_lengths w h (k := -1) (by omega) hs
      (by omega : (0 : ℤ) ≤ 0) (y m) (ha m)
    rw [add_zero] at hd
    have hd' := ldpFinite_eq_lengths_leftEnvelope hb hbs (hrbase m) (hr0 m) hd
    have hNm := hN m hm
    rw [hd'] at hNm
    exact hNm
  have hsj : ∀ᶠ m in Filter.atTop, ∀ (j : ℕ) (hj : j ∈ J),
      Xs (j : ℤ) = (presentLdpFiniteNat hbs (hrj j hj m) : ℤ) -
        (presentLdpFiniteNat hbs (hr0 m) : ℤ) := by
    have hsj0 : ∀ᶠ m in Filter.atTop, ∀ j : J,
        Xs (j.val : ℤ) = (presentLdpFiniteNat hbs (hrj j.val j.property m) : ℤ) -
          (presentLdpFiniteNat hbs (hr0 m) : ℤ) := by
      let : Fintype J := (leftFrontierIndices_finite w h hs).fintype
      apply Filter.eventually_all.mpr
      intro j
      obtain ⟨N, hN⟩ := hXs.2 0 (j.val : ℤ) y hy
        (fun m => ⟨hr0 m, hrj j.val j.property m⟩)
      exact Filter.eventually_atTop.mpr ⟨N, fun m hm => by
        simpa only [hXs.1, sub_zero] using hN m hm⟩
    exact hsj0.mono (fun m hm j hj => hm ⟨j, hj⟩)
  have hf := eventually_not_earlyReachable_leftEnvelope w t
    (boundaryPresentVertex w h 0) _ hiy
  obtain ⟨m, hmfar, hmg, hms⟩ := (hf.and (hg.and hsj)).exists
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb _ _ (hir m)) (hir m)
  have hpn := presentLdpFiniteNat_eq_length hb (hir m) hp
  have hupper : ∀ j ∈ J, (A j : ℤ) + Xs (j : ℤ) ≤ X 0 - X (-1) := by
    intro j hj
    obtain ⟨pe0, he0⟩ := hj.2
    obtain ⟨n, ⟨pe, hpe, _⟩, hn⟩ := earlyLdp_attained w t hb
      (boundaryPresentVertex w h 0) (leftFrontierVertex w h hs j)
      ⟨pe0.length, pe0, rfl, he0⟩
    have hA : A j = pe.length := by
      dsimp [A]
      rw [hn]
      change n = pe.length
      exact hpe.symm
    obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hbs _ _ (hrj j hj m)) (hrj j hj m)
    have hqn := presentLdpFiniteNat_eq_length hbs (hrj j hj m) hq
    obtain ⟨q', hq'⟩ := shift_path_map_frontier w t q
    change Path (boundaryPresentVertex w h 0)
      (shiftLimitVertex w t (boundaryPresentVertex ws hs (j : ℤ))) at pe
    have hle := hp (pe.comp q')
    have hlen := (Path.length_comp pe q').trans (congrArg (pe.length + ·) hq')
    have hv := hms j hj
    dsimp only [leftFrontierVertex, boundaryPresentVertex, ws, t] at hle hlen hA hqn hpn hv hmg ⊢
    omega
  obtain ⟨j, hj, pe, q, he, hlen⟩ :=
    leftHit_path_length_factorization w h hs (y m) (ha m) hmfar p
  have hAle : pe.length ≤ A j := by
    apply WithBot.coe_le_coe.mp
    exact (length_le_earlyLdp w t hb _ _ ⟨pe, rfl, he⟩).trans
      (WithBot.le_coe_unbotD _ 0)
  have hqle := length_le_ldpFinite_leftEnvelope hbs (hrj j hj m) q
  have hv := hms j hj
  have hu := hupper j hj
  have heq : (A j : ℤ) + Xs (j : ℤ) = X 0 - X (-1) := by omega
  exact ⟨⟨j, hj, heq⟩, fun _ ⟨j, hj, heq⟩ => heq ▸ hupper j hj⟩



theorem leftFrontier_ldp_busemann (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    (hb : PresentPathLengthsBounded (w := w))
    (hbs : PresentPathLengthsBounded (w := fun i => w (boundaryHitTime w h (-1) + i)))
    (X Xs : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hb (boundaryPresentVertex w h) X)
    (hXs : IsBoundaryBusemannLDP hbs (boundaryPresentVertex _ hs) Xs) :
    X 0 - X (-1) = sSup ((fun j : ℕ =>
      (((earlyLdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j)).unbotD 0 : ℕ) : ℤ) + Xs (j : ℤ)) ''
      leftFrontierIndices w h hs) :=
  (leftFrontier_ldp_busemann_isGreatest w h hs hb hbs X Xs hX hXs).csSup_eq.symm

private theorem leftFrontierVertex_ne_root (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    {j : ℕ} (hj : 1 ≤ j) :
    leftFrontierVertex w h hs j ≠ boundaryPresentVertex w h 0 := by
  let t := boundaryHitTime w h (-1)
  let ws := fun i => w (t + i)
  have hex : ∃ e, ∃ he : EdgePresent ws e, edgeEast ws e = boundaryVertex ws hs (j : ℤ) := by
    by_cases hj1 : j = 1
    · subst j
      refine ⟨0, ⟨0, by change 0 < 1; omega, rfl⟩, ?_⟩
      change edgeEast ws 0 = boundaryVertex ws hs 1
      rw [boundaryVertex_one]
      exact (edge_endpoints_eq ws (j := 0) (e := 0) (by change 0 < 1; omega)).2.symm
    · obtain ⟨he, _, ht⟩ := boundaryVertex_right_edge_present_source ws hs
        (by omega : 1 ≤ j - 1)
      refine ⟨kmswRightBoundaryEdge ws (j - 1), he, ?_⟩
      have hc : ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by omega
      simpa only [hc] using ht
  obtain ⟨e, he, ht⟩ := hex
  let ef : {e // EdgePresent ws e} := ⟨e, he⟩
  have hinc := (shiftLimitEdge_incidence w t ef).2
  rw [ht] at hinc
  intro hroot
  apply boundaryVertex_nonpos_no_incoming w h (by omega : (0 : ℤ) ≤ 0)
    (shiftLimitEdge w t ef) (shiftLimitEdge_present w t ef)
  exact hinc.trans (congrArg PresentVertex.id hroot)




theorem leftFrontierIndices_pending (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    {j : ℕ} (hj : j ∈ leftFrontierIndices w h hs) :
    (CutConverse.pendingVertices (kmswStage w (boundaryHitTime w h (-1))))[j - 1]? =
      some (leftFrontierVertex w h hs j).id := by
  rcases leftHit_shifted_east_label_frontier_or_no_early_edge w h hs hj.1 with hf | hn
  · exact hf
  · obtain ⟨p, hp⟩ := hj.2
    by_cases hz : p.length = 0
    · exact False.elim (leftFrontierVertex_ne_root w h hs hj.1 (p.eq_of_length_zero hz).symm)
    · obtain ⟨u, q, e, hpeq⟩ := p.length_ne_zero_iff_eq_cons.mp hz
      have hmem : e.val ∈ pathEdgeList p := by
        rw [hpeq]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have ht := hp e.val hmem e.property.1
      exact False.elim ((hn e.val e.property.1 ht).2 e.property.2.2)

/-- The ordered frontier ID and both early extremal coefficients at every
actual interface entry are unchanged on replacing the code after the cutoff.
This is partial past determination for B.2 (`lem-directed-contain`,
F1/F4 remain. -/
theorem leftFrontier_coefficients_prefix (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hs : BoundaryHitWitnesses (fun i => w (boundaryHitTime w h (-1) + i)))
    {j : ℕ} (hj : j ∈ leftFrontierIndices w h hs)
    (p : ℕ → Fin 3)
    (hp : ∀ i, i < boundaryHitTime w h (-1) → w i = p i) :
    ∃ v : ℕ,
      (CutConverse.pendingVertices (kmswStage p (boundaryHitTime w h (-1))))[j - 1]? = some v ∧
      earlySdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j) =
        earlySdp p (boundaryHitTime w h (-1)) ⟨0⟩ ⟨v⟩ ∧
      earlyLdp w (boundaryHitTime w h (-1)) (boundaryPresentVertex w h 0)
        (leftFrontierVertex w h hs j) =
        earlyLdp p (boundaryHitTime w h (-1)) ⟨0⟩ ⟨v⟩ := by
  refine ⟨(leftFrontierVertex w h hs j).id, ?_, ?_, ?_⟩
  · rw [← kmswStage_congr hp]
    exact leftFrontierIndices_pending w h hs hj
  · have hh := earlySdp_congr (boundaryHitTime w h (-1)) 0
      (leftFrontierVertex w h hs j).id hp
    simpa only [boundaryPresentVertex, boundaryVertex_zero] using hh
  · have hh := earlyLdp_congr (boundaryHitTime w h (-1)) 0
      (leftFrontierVertex w h hs j).id hp
    simpa only [boundaryPresentVertex, boundaryVertex_zero] using hh

end DirectedDistances.Recursive
