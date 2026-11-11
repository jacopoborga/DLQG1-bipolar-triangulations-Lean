module

public import DirectedDistances.Recursive.LDPRelatingLeftLift
public import DirectedDistances.Recursive.LDPRelatingUpLift
public import DirectedDistances.Recursive.LDPRelatingDown
public import DirectedDistances.KMSW.KMSWShiftLateLift
import DirectedDistances.KMSW.UIBOTBoundaryM0
import DirectedDistances.KMSW.WalkRecordCounts

/-! # Deterministic first-step longest-distance assembly

Path comparisons for `lem:LDP-relating-X1-X` and `eqn-ldp-relating1-3`
The common-vertex input `eqn-LDP-relating-w` (lines 173–175) is a labelled
external input, rather than an assertion of Busemann existence. Normalization
uses `eqn-ldp-busemann-renormalize` (lines 179–183). -/

public section
namespace DirectedDistances.Recursive
open DirectedDistances.KMSW Quiver

private theorem vertex_ext {u : ℕ → Fin 3} {a b : PresentVertex u}
    (h : a.id = b.id) : a = b := by
  cases a
  cases b
  exact congrArg PresentVertex.mk h

private noncomputable def limitMap (w : ℕ → Fin 3) :
    Prefunctor (PresentVertex (fun i => w (1 + i))) (PresentVertex w) where
  obj := shiftLimitVertex w 1
  map {a b} e := by
    let f : {f : ℕ // EdgePresent (fun i => w (1 + i)) f} := ⟨e.val, e.property.1⟩
    have hi := shiftLimitEdge_incidence w 1 f
    have ha : (⟨edgeWest (fun i => w (1 + i)) e.val⟩ :
        PresentVertex (fun i => w (1 + i))) = a := vertex_ext e.property.2.1
    have hb : (⟨edgeEast (fun i => w (1 + i)) e.val⟩ :
        PresentVertex (fun i => w (1 + i))) = b := vertex_ext e.property.2.2
    exact ⟨shiftLimitEdge w 1 f, shiftLimitEdge_present w 1 f,
      hi.1.trans (congrArg PresentVertex.id (congrArg (shiftLimitVertex w 1) ha)),
      hi.2.trans (congrArg PresentVertex.id (congrArg (shiftLimitVertex w 1) hb))⟩

private theorem limitMap_length (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))} (p : Path a b) :
    ((limitMap w).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]

private theorem rebase {u : ℕ → Fin 3} {a a' b : PresentVertex u}
    (h : a = a') (p : Path a b) :
    ∃ q : Path a' b, q.length = p.length ∧ pathEdgeList q = pathEdgeList p := by
  subst a'
  exact ⟨p, rfl, rfl⟩

private theorem root_ends (w : ℕ → Fin 3) :
    edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 := by
  exact edge_endpoints_eq w (j := 0) (e := 0) (by change 0 < 1; omega)

private def rootArrow (w : ℕ → Fin 3) :
    (⟨0⟩ : PresentVertex w) ⟶ ⟨1⟩ :=
  ⟨0, ⟨0, by change 0 < 1; omega, rfl⟩, (root_ends w).1, (root_ends w).2⟩

private theorem path_end_ne_zero {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) : b.id ≠ 0 := by
  induction p with
  | nil => exact ha
  | @cons x y p e ih =>
    intro hz
    exact uibot_zero_no_incoming w e.val e.property.1
      (e.property.2.2.trans hz)

private theorem path_avoids_root {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) (ha : a.id ≠ 0) :
    0 ∉ pathEdgeList p := by
  induction p with
  | nil => simp [pathEdgeList]
  | @cons x y p e ih =>
    have hx := path_end_ne_zero p ha
    rw [pathEdgeList, List.mem_append, not_or]
    refine ⟨ih, ?_⟩
    intro he
    have he0 : e.val = 0 := (List.mem_singleton.mp he).symm
    exact hx (e.property.2.1.symm.trans (he0 ▸ (root_ends w).1))

private theorem path_root_cases {w : ℕ → Fin 3}
    {a b : PresentVertex w} (p : Path a b) :
    0 ∉ pathEdgeList p ∨
      a.id = 0 ∧ ∃ q : Path (⟨1⟩ : PresentVertex w) b,
        p.length = q.length + 1 := by
  induction p with
  | nil => exact Or.inl (by simp [pathEdgeList])
  | @cons x y p e ih =>
    by_cases he : e.val = 0
    · have hx : x.id = 0 := e.property.2.1.symm.trans (he ▸ (root_ends w).1)
      have hy : y = (⟨1⟩ : PresentVertex w) :=
        vertex_ext (e.property.2.2.symm.trans (he ▸ (root_ends w).2))
      subst y
      cases p with
      | nil => exact Or.inr ⟨hx, Path.nil, rfl⟩
      | @cons z x p f =>
        exact (uibot_zero_no_incoming w f.val f.property.1
          (f.property.2.2.trans hx)).elim
    · rcases ih with hp | ⟨ha, q, hq⟩
      · exact Or.inl (by simpa only [pathEdgeList, List.mem_append,
          List.mem_singleton, not_or] using And.intro hp (Ne.symm he))
      · exact Or.inr ⟨ha, q.cons e, by simp only [Path.length_cons, hq]⟩

private theorem lift_avoiding (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (p : Path (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b))
    (hp : 0 ∉ pathEdgeList p) : ∃ q : Path a b, q.length = p.length := by
  obtain ⟨c, hc, q, hq, hl, _⟩ := shiftLimitVertex_late_path_lift w 1 a ha p
    ((upShift_path_avoids_root_iff_late w p).mp hp)
  have hcb : c = b := shiftLimitVertex_injective w 1 hc hb hq
  subst c
  exact ⟨q, hl⟩

private theorem boundary_allocated (u : ℕ → Fin 3)
    (h : BoundaryHitWitnesses u) (k : ℤ) :
    boundaryVertex u h k < (kmswStage u (boundaryHitTime u h k)).nextVertex := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryVertex_zero, boundaryHitTime_zero, kmswStage, kmswInit]
  · by_cases hk1 : k = 1
    · subst k
      have hm := CutConverse.nextVertex_mono u (Nat.zero_le (boundaryHitTime u h 1))
      simpa [boundaryVertex_one, kmswStage, kmswInit] using
        (show 1 < (kmswStage u (boundaryHitTime u h 1)).nextVertex by
          change 2 ≤ _ at hm; omega)
    · have hb := kmswStage_endpoints_lt_nextVertex u (boundaryHitTime u h k)
        (act u (boundaryHitTime u h k)) (act_lt_nextEdge u le_rfl)
      rw [(edge_endpoints_eq u (act_lt_nextEdge u le_rfl)).1] at hb
      simpa [boundaryVertex, hk0, hk1, activeInitial] using hb.1

private theorem shifted_boundary_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    kmswVertexAllocated (fun i => w (1 + i))
      ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ := by
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i; rw [Nat.add_comm]
  exact ⟨boundaryHitTime _ h k, by simpa only [hs] using boundary_allocated _ h k⟩

private theorem boundary_image_of_stage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ =
      (⟨kmswShiftVertexMapAll w 1 (boundaryHitTime (fun i => w (i + 1)) h k)
        (boundaryVertex (fun i => w (i + 1)) h k)⟩ : PresentVertex w) := by
  apply shiftLimitVertex_eq
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i; rw [Nat.add_comm]
  simpa only [hs] using boundary_allocated _ h k

private theorem boundary_ne_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≠ 0) :
    boundaryVertex w h k ≠ 0 := by
  intro he
  have hh := boundaryVertex_injective w h (he.trans (boundaryVertex_zero w h).symm)
  exact hk hh

private theorem image_ldp_eq (w : ℕ → Fin 3)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hz : (shiftLimitVertex w 1 a).id ≠ 0) :
    ldpSup (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) = ldpSup a b := by
  have heq : pathLengths (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) =
      pathLengths a b := by
    apply Set.Subset.antisymm
    · rintro n ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := lift_avoiding w ha hb p (path_avoids_root p hz)
      exact ⟨q, hq⟩
    · rintro n ⟨p, rfl⟩
      exact ⟨(limitMap w).mapPath p, limitMap_length w p⟩
  unfold ldpSup
  rw [heq]

private theorem ldp_eq_longest {V : Type*} [Quiver V] {a b : V}
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

private theorem length_le_sup {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w))
    {a b : PresentVertex w} (p : Path a b) :
    (p.length : WithBot ℕ) ≤ ldpSup a b := by
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hb a b ⟨p⟩) ⟨p⟩
  rw [ldp_eq_longest hq]
  exact WithBot.coe_le_coe.mpr (hq p)

private theorem shifted_bounded (w : ℕ → Fin 3)
    (hb : PresentPathLengthsBounded (w := w)) :
    PresentPathLengthsBounded (w := fun i => w (1 + i)) := by
  intro a b hr
  obtain ⟨p⟩ := hr
  obtain ⟨N, hN⟩ := hb _ _ ⟨(limitMap w).mapPath p⟩
  refine ⟨N, ?_⟩
  rintro n ⟨q, rfl⟩
  have hh := hN ⟨(limitMap w).mapPath q, rfl⟩
  simpa only [limitMap_length] using hh

private theorem ldp_eq_of_dominating_lifts (w : ℕ → Fin 3)
    (hbound : PresentPathLengthsBounded (w := w))
    {a b : PresentVertex (fun i => w (1 + i))}
    (hlift : ∀ p : Path (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b),
      ∃ q : Path a b, p.length ≤ q.length) :
    ldpSup (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) = ldpSup a b := by
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := hlift p
    exact (WithBot.coe_le_coe.mpr hq).trans (length_le_sup (shifted_bounded w hbound) q)
  · apply csSup_le'
    rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
    have hh := length_le_sup hbound ((limitMap w).mapPath p)
    rw [limitMap_length] at hh
    change (p.length : WithBot ℕ) ≤
      ldpSup (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) at hh
    exact hh

private theorem up_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) {j k : ℤ}
    (hpair : (j = -1 ∧ k = -1) ∨ (j = 0 ∧ k = 0) ∨ (j = 1 ∧ k = 2)) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
  rw [boundary_image_of_stage]
  apply congrArg PresentVertex.mk
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact upShift_boundaryVertex_left w h0 h1 hw (-1) (by omega)
  · simpa only [boundaryHitTime_zero, boundaryVertex_zero] using
      (upShift_rootVertices w h0 hw).1
  · exact upShift_boundaryVertex_right w h0 h1 hw 2 (by omega)

private theorem boundary_two_path (u : ℕ → Fin 3) (h : BoundaryHitWitnesses u) :
    ∃ p : Path (⟨boundaryVertex u h 0⟩ : PresentVertex u)
      ⟨boundaryVertex u h 2⟩, p.length = 2 := by
  obtain ⟨e0, hp0, hw0, he0⟩ := boundaryVertex_nonneg_successor_edge u h (k := 0) (by omega)
  obtain ⟨e1, hp1, hw1, he1⟩ := boundaryVertex_nonneg_successor_edge u h (k := 1) (by omega)
  let f0 : (⟨boundaryVertex u h 0⟩ : PresentVertex u) ⟶ ⟨boundaryVertex u h 1⟩ :=
    ⟨e0, hp0, hw0, he0⟩
  let f1 : (⟨boundaryVertex u h 1⟩ : PresentVertex u) ⟶ ⟨boundaryVertex u h 2⟩ :=
    ⟨e1, hp1, hw1, he1⟩
  exact ⟨Path.nil.cons f0 |>.cons f1, rfl⟩

/-- All three deterministic LDP identities in the up case of
`lem:LDP-relating-X1-X`, `eqn-ldp-relating3`
is dominated by the shifted two-edge boundary path. No reachability premise
is required; unreachable pairs have supremum `⊥`. -/
theorem upStep_ldpSup_boundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) (hbound : PresentPathLengthsBounded (w := w))
    (j k : ℤ)
    (hpair : (j = -1 ∧ k = -1) ∨ (j = 0 ∧ k = 0) ∨ (j = 1 ∧ k = 2))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    ldpSup (⟨boundaryVertex w h0 j⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  have himage := up_boundary_image w h0 h1 hw hpair
  rw [← himage]
  have ha := shifted_boundary_allocated w h1 k
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply image_ldp_eq w ha hb
    rw [himage]
    exact boundary_ne_zero w h0 (k := -1) (by omega)
  · apply ldp_eq_of_dominating_lifts w hbound
    intro p
    rcases path_root_cases p with hp | ⟨_, q, hq⟩
    · obtain ⟨r, hr⟩ := lift_avoiding w ha hb p hp
      exact ⟨r, hr.ge⟩
    · have hhead := up_boundary_image w h0 h1 hw (j := 1) (k := 2)
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
      simp only [boundaryVertex_one] at hhead
      obtain ⟨q', hqLen, _⟩ := rebase hhead.symm q
      obtain ⟨r, hr⟩ := lift_avoiding w (shifted_boundary_allocated w h1 2) hb q'
        (path_avoids_root q' (by rw [hhead]; change (1 : ℕ) ≠ 0; omega))
      have hseq : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
        funext i; rw [Nat.add_comm]
      have htwo : ∃ s : Path
          (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ : PresentVertex (fun i => w (1 + i)))
          ⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩, s.length = 2 := by
        let P (u : ℕ → Fin 3) : Prop := ∃ s : Path
          (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ : PresentVertex u)
          ⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩, s.length = 2
        have hP : P (fun i => w (i + 1)) := boundary_two_path _ h1
        exact Eq.mp (congrArg P hseq.symm) hP
      obtain ⟨s, hs⟩ := htwo
      refine ⟨s.comp r, ?_⟩
      rw [Path.length_comp, hs, hr, hqLen, hq]
      omega
  · apply image_ldp_eq w ha hb
    rw [himage]
    exact boundary_ne_zero w h0 (k := 1) (by omega)

private theorem image_root_sup (w : ℕ → Fin 3)
    (hbound : PresentPathLengthsBounded (w := w))
    {a d b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hd : kmswVertexAllocated (fun i => w (1 + i)) d)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hs : shiftLimitVertex w 1 a = (⟨0⟩ : PresentVertex w))
    (ht : shiftLimitVertex w 1 d = (⟨1⟩ : PresentVertex w)) :
    ldpSup (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      max (ldpSup a b) (1 + ldpSup d b) := by
  have hbs := shifted_bounded w hbound
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
    rcases path_root_cases p with hp | ⟨_, q, hq⟩
    · obtain ⟨p', hpLen, hpEdges⟩ := rebase hs.symm p
      obtain ⟨r, hr⟩ := lift_avoiding w ha hb p' (by rw [hpEdges]; exact hp)
      apply le_trans _ (le_max_left _ _)
      have hh := length_le_sup hbs r
      simpa only [hr, hpLen] using hh
    · obtain ⟨q', hqLen, _⟩ := rebase ht.symm q
      obtain ⟨r, hr⟩ := lift_avoiding w hd hb q'
        (path_avoids_root q' (by rw [ht]; change (1 : ℕ) ≠ 0; omega))
      apply le_trans _ (le_max_right _ _)
      calc
        (p.length : WithBot ℕ) = 1 + (r.length : WithBot ℕ) := by
          rw [hq, ← hqLen, ← hr]
          change ((r.length + 1 : ℕ) : WithBot ℕ) = ((1 + r.length : ℕ) : WithBot ℕ)
          congr 1; omega
        _ ≤ 1 + ldpSup d b := by simpa only [add_comm] using add_le_add_left (length_le_sup hbs r) 1
  · apply max_le
    · apply csSup_le'
      rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
      let q := (limitMap w).mapPath p
      change Path (shiftLimitVertex w 1 a) (shiftLimitVertex w 1 b) at q
      obtain ⟨q', hqLen, _⟩ := rebase hs q
      have hh := length_le_sup hbound q'
      have hlen : q.length = p.length := limitMap_length w p
      rw [hqLen, hlen] at hh
      exact hh
    · by_cases hr : Reachable d b
      · obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbs d b hr) hr
        rw [ldp_eq_longest hp]
        let q := (limitMap w).mapPath p
        change Path (shiftLimitVertex w 1 d) (shiftLimitVertex w 1 b) at q
        obtain ⟨q', hqLen, _⟩ := rebase ht q
        have hh := length_le_sup hbound ((rootArrow w).toPath.comp q')
        have hlen : ((rootArrow w).toPath.comp q').length = 1 + p.length := by
          rw [Path.length_comp, Path.length_toPath, hqLen]
          exact congrArg (1 + ·) (limitMap_length w p)
        rw [hlen] at hh
        exact hh
      · rw [ldpSup_eq_bot_of_not_reachable hr]
        simp only [WithBot.add_bot, bot_le]

private theorem left_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (k : ℤ) (hk : k ≤ 0) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 (k - 1)⟩ : PresentVertex w) := by
  rw [boundary_image_of_stage]
  apply congrArg PresentVertex.mk
  by_cases hz : k = 0
  · subst k
    simpa only [boundaryVertex_zero, boundaryHitTime_zero, zero_sub] using
      (leftShift_rootVertices_and_firstStageImage w h0 hw).1
  · exact leftShift_boundaryVertex_left w h0 h1 hw k (by omega)

private theorem left_image_ne_zero (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (a : PresentVertex (fun i => w (1 + i)))
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a) :
    (shiftLimitVertex w 1 a).id ≠ 0 := by
  intro hz
  have hno : ¬ ∃ e, EdgePresent (fun i => w (1 + i)) e ∧
      edgeEast (fun i => w (1 + i)) e = a.id := by
    rintro ⟨e, he, hend⟩
    let f : {f : ℕ // EdgePresent (fun i => w (1 + i)) f} := ⟨e, he⟩
    have hh := (shiftLimitEdge_incidence w 1 f).2
    have hav : (⟨edgeEast (fun i => w (1 + i)) e⟩ :
        PresentVertex (fun i => w (1 + i))) = a := vertex_ext hend
    rw [hav, hz] at hh
    exact uibot_zero_no_incoming w (shiftLimitEdge w 1 f)
      (shiftLimitEdge_present w 1 f) hh
  have hseq : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i; rw [Nat.add_comm]
  have h1' : BoundaryHitWitnesses (fun i => w (1 + i)) := hseq.symm ▸ h1
  obtain ⟨k, hk, hka⟩ := (allocated_source_iff_left_boundary _ h1' a.id ha).mp hno
  have ha' : a = ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ := by
    apply vertex_ext
    simpa only [hseq] using hka
  rw [ha', left_boundary_image w h0 h1 hw k hk] at hz
  exact boundary_ne_zero w h0 (by omega : k - 1 ≠ 0) hz

private theorem left_only_root_outgoing (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) {e : ℕ} (he : EdgePresent w e)
    (hs : edgeWest w e = 0) : e = 0 := by
  by_contra hn
  have hlate : 1 ≤ actTime w e he := by
    by_contra ht
    have hz : actTime w e he = 0 := by omega
    apply hn
    rw [actTime_spec w e he, hz]
    rfl
  obtain ⟨f, hf⟩ := (shiftLimitEdge_image_iff w 1 e he).mpr hlate
  have hinc := (shiftLimitEdge_incidence w 1 f).1
  rw [hf, hs] at hinc
  obtain ⟨m, hm, _⟩ := f.property
  have hb := (kmswStage_endpoints_lt_nextVertex _ m f.val hm).1
  rw [(edge_endpoints_eq _ hm).1] at hb
  exact left_image_ne_zero w h0 h1 hw ⟨edgeWest _ f.val⟩ ⟨m, hb⟩ hinc.symm

private theorem left_root_paths (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) {b : PresentVertex (fun i => w (1 + i))}
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (p : Path (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b)) :
    ∃ q : Path (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b),
      p.length = q.length + 1 := by
  have hp : p.length ≠ 0 := by
    intro hz
    have he := p.eq_of_length_zero hz
    exact left_image_ne_zero w h0 h1 hw b hb (congrArg PresentVertex.id he.symm)
  obtain ⟨c, e, q, _, hlen⟩ := (p.length_ne_zero_iff_eq_comp).mp hp
  have he0 : e.val = 0 := left_only_root_outgoing w h0 h1 hw e.property.1 e.property.2.1
  have hc : c = (⟨1⟩ : PresentVertex w) :=
    vertex_ext (e.property.2.2.symm.trans (by rw [he0]; exact (root_ends w).2))
  subst c
  exact ⟨q, hlen⟩

/-- The left-code root LDP is one plus the shifted right-root LDP, including
`⊥` on unreachable pairs. This is the missing middle distance identity in
`lem:LDP-relating-X1-X`, `eqn-ldp-relating2` -/
theorem leftStep_ldpSup_rootBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (hbound : PresentPathLengthsBounded (w := w))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    ldpSup (⟨boundaryVertex w h0 0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      1 + ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 1⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  have hd : kmswVertexAllocated (fun i => w (1 + i)) (⟨1⟩ : PresentVertex _) :=
    ⟨0, by change 1 < 2; omega⟩
  have ht : shiftLimitVertex w 1 (⟨1⟩ : PresentVertex _) = (⟨1⟩ : PresentVertex w) := by
    rw [shiftLimitVertex_eq w 1 0 ⟨1⟩ (by change 1 < 2; omega)]
    apply congrArg PresentVertex.mk
    simpa only [boundaryVertex_one] using
      (leftShift_rootVertices_and_firstStageImage w h0 hw).2.1
  simp only [boundaryVertex_zero, boundaryVertex_one]
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨n, ⟨p, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := left_root_paths w h0 h1 hw hb p
    obtain ⟨q', hqLen, _⟩ := rebase ht.symm q
    obtain ⟨r, hr⟩ := lift_avoiding w hd hb q'
      (path_avoids_root q' (by rw [ht]; change (1 : ℕ) ≠ 0; omega))
    calc
      (p.length : WithBot ℕ) = 1 + (r.length : WithBot ℕ) := by
        rw [hq, ← hqLen, ← hr]
        change ((r.length + 1 : ℕ) : WithBot ℕ) = ((1 + r.length : ℕ) : WithBot ℕ)
        congr 1; omega
      _ ≤ 1 + ldpSup (⟨1⟩ : PresentVertex _) b :=
        by simpa only [add_comm] using add_le_add_left (length_le_sup (shifted_bounded w hbound) r) 1
  · by_cases hr : Reachable (⟨1⟩ : PresentVertex (fun i => w (1 + i))) b
    · obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove
        (shifted_bounded w hbound _ _ hr) hr
      rw [ldp_eq_longest hp]
      let q := (limitMap w).mapPath p
      change Path (shiftLimitVertex w 1 (⟨1⟩ : PresentVertex _)) (shiftLimitVertex w 1 b) at q
      obtain ⟨q', hqLen, _⟩ := rebase ht q
      have hh := length_le_sup hbound ((rootArrow w).toPath.comp q')
      have hlen : ((rootArrow w).toPath.comp q').length = 1 + p.length := by
        rw [Path.length_comp, Path.length_toPath, hqLen]
        exact congrArg (1 + ·) (limitMap_length w p)
      rw [hlen] at hh
      exact hh
    · rw [ldpSup_eq_bot_of_not_reachable hr]
      simp only [WithBot.add_bot, bot_le]

/-- The two outer-boundary LDP identities for the left code, with `⊥`
preserved for unreachable pairs (`lem:LDP-relating-X1-X`, -/
theorem leftStep_ldpSup_outerBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0) (j k : ℤ)
    (hpair : (j = -1 ∧ k = 0) ∨ (j = 1 ∧ k = 1))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    ldpSup (⟨boundaryVertex w h0 j⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  have hi : shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa only [zero_sub] using left_boundary_image w h0 h1 hw 0 le_rfl
    · simp only [boundaryVertex_one]
      rw [shiftLimitVertex_eq w 1 0 ⟨1⟩ (by change 1 < 2; omega)]
      apply congrArg PresentVertex.mk
      simpa only [boundaryVertex_one] using
        (leftShift_rootVertices_and_firstStageImage w h0 hw).2.1
  rw [← hi]
  exact image_ldp_eq w (shifted_boundary_allocated w h1 k) hb
    (left_image_ne_zero w h0 h1 hw _ (shifted_boundary_allocated w h1 k))

private theorem down_minus_one_image (w : ℕ → Fin 3)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1))) (hw : w 0 = 2) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ =
      (⟨0⟩ : PresentVertex w) := by
  let u : ℕ → Fin 3 := fun i => w (i + 1)
  let t := boundaryHitTime u h1 (-1)
  have hseq : (fun i : ℕ => w (1 + i)) = u := by
    funext i; simp only [u, Nat.add_comm]
  have hstep : ∀ i, |L u (i + 1) - L u i| ≤ 1 := by
    intro i
    have hs : L u (i + 1) = L u i +
        (DirectedDistances.RandomWalk.lazyTwoDimensionalStep (u i)).1 :=
      Finset.sum_range_succ _ _
    rw [hs, add_sub_cancel_left]
    change |((u i).val : ℤ) - 1| ≤ 1
    have hh := (u i).isLt
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hspec : L u t = -1 := boundaryHitTime_left_spec u h1 (by omega)
  have hfind : t = Nat.find (h1.leftHit (-1) (by omega)) := by
    simp [t, boundaryHitTime]
  have hrecord := (strict_running_minimum_iff_first_hit (L u) rfl hstep t t (-1)
    (by omega) (h1.leftHit (-1) (by omega))).mpr ⟨le_rfl, hspec, hfind⟩
  have hbefore : ∀ r, r ≤ t → -1 ≤ L u r := by
    intro r hr
    rcases hr.eq_or_lt with he | he
    · rw [he, hspec]
    · have hh := (Finset.mem_filter.mp hrecord.1).2 r he
      rw [hspec] at hh
      omega
  have hL1 : L w 1 = 1 := by simp [L, hw]
  have hfinish : L w (1 + t) = 0 := by
    have hh := shiftedL_eq_translated w t
    change L u t = _ at hh
    rw [hspec, hL1] at hh
    rw [Nat.add_comm]
    omega
  have habove : ∀ j, 0 ≤ j → j ≤ 1 + t → L w 0 ≤ L w j := by
    intro j _ hj
    by_cases hj0 : j = 0
    · subst j; exact le_rfl
    · have hidx : j - 1 + 1 = j := by omega
      have hh := shiftedL_eq_translated w (j - 1)
      change L u (j - 1) = _ at hh
      rw [hidx, hL1] at hh
      have hb := hbefore (j - 1) (by omega)
      have hz : L w 0 = 0 := rfl
      omega
  have hwest := kmsw_west_act_eq_of_level w (Nat.zero_le (1 + t))
    (by simpa only [hfinish] using (show L w 0 = 0 from rfl)) habove
  have hwzero : edgeWest w (act w (1 + t)) = 0 := by
    rw [← (edge_endpoints_eq w (act_lt_nextEdge w le_rfl)).1]
    have hr := (initial_edge_endpoints w (1 + t)).1
    change (kmswStage w (1 + t)).west 0 = _ at hwest
    exact hwest.symm.trans hr
  rw [boundary_image_of_stage]
  apply congrArg PresentVertex.mk
  have ha := boundaryVertex_eq_edgeWest_hit u h1 (-1)
  have hp := kmswShift_active_present w 1 t
  have hm := (kmswShift_present_edge_maps w 1 t
    (act (fun i => w (1 + i)) t) hp.1 hp.2).2.1
  have hact : boundaryVertex u h1 (-1) =
      edgeWest (fun i => w (1 + i)) (act (fun i => w (1 + i)) t) := by
    simpa only [hseq] using ha
  change kmswShiftVertexMapAll w 1 t (boundaryVertex u h1 (-1)) = 0
  rw [hact, ← hm, kmswShift_active_edge_map, hwzero]

private theorem down_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) {j k : ℤ}
    (hpair : (j = -1 ∧ k = -2) ∨ (j = 0 ∧ k = -1) ∨ (j = 1 ∧ k = 0)) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [boundary_image_of_stage]
    exact congrArg PresentVertex.mk (downShift_boundaryVertex_left w h0 h1 hw (-2) (by omega))
  · simpa only [boundaryVertex_zero] using down_minus_one_image w h1 hw
  · rw [boundary_image_of_stage]
    apply congrArg PresentVertex.mk
    simpa only [boundaryVertex_zero, boundaryHitTime_zero] using
      (downShift_rootVertices_and_firstStageImage w h0 hw).1

/-- Deterministic outer-boundary LDP identities for the down code in
`lem:LDP-relating-X1-X`, `eqn-ldp-relating1` -/
theorem downStep_ldpSup_outerBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) (j k : ℤ)
    (hpair : (j = -1 ∧ k = -2) ∨ (j = 1 ∧ k = 0))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    ldpSup (⟨boundaryVertex w h0 j⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  have hp : (j = -1 ∧ k = -2) ∨ (j = 0 ∧ k = -1) ∨ (j = 1 ∧ k = 0) := by
    rcases hpair with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inr hh)
  have hi := down_boundary_image w h0 h1 hw hp
  rw [← hi]
  apply image_ldp_eq w (shifted_boundary_allocated w h1 k) hb
  rw [hi]
  apply boundary_ne_zero w h0
  rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- At the down-code root, the late paths compete with paths starting with
edge zero, giving a maximum with `1 +` the shifted-root distance. This is the
middle distance identity used in `eqn-ldp-relating1`, before the normalization
of `eqn-ldp-busemann-renormalize` (`lem:LDP-relating-X1-X`, -/
theorem downStep_ldpSup_rootBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 2) (hbound : PresentPathLengthsBounded (w := w))
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    ldpSup (⟨boundaryVertex w h0 0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      max (ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ :
        PresentVertex (fun i => w (1 + i))) b)
        (1 + ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ :
          PresentVertex (fun i => w (1 + i))) b) := by
  rw [boundaryVertex_zero]
  apply image_root_sup w hbound (shifted_boundary_allocated w h1 (-1))
    (shifted_boundary_allocated w h1 0) hb
  · exact down_minus_one_image w h1 hw
  · simpa only [boundaryVertex_one] using down_boundary_image w h0 h1 hw
      (j := 1) (k := 0) (Or.inr (Or.inr ⟨rfl, rfl⟩))

private theorem sup_eq_finiteNat {w : ℕ → Fin 3}
    (hb : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) :
    ldpSup a b = (presentLdpFiniteNat hb hr : WithBot ℕ) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hb a b hr) hr
  rw [presentLdpFiniteNat_eq_length hb hr hp]
  exact ldp_eq_longest hp

/-- Deterministic renormalization and all three first-step formulas from
`lem:LDP-relating-X1-X`, `eqn-ldp-relating1-3`
`hcommon` is exactly the labelled common-vertex distance-difference input
`eqn-LDP-relating-w` (lines 173–175), for both maps and all indices in
`[-2,2]`. Reachability and boundedness ensure all subtracted distances are
finite. No other Busemann property is assumed. -/
theorem firstStep_boundary_pair_of_common_vertex (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hb0 : PresentPathLengthsBounded (w := w))
    (hb1 : PresentPathLengthsBounded (w := fun i => w (1 + i)))
    (z : PresentVertex (fun i => w (1 + i)))
    (hz : kmswVertexAllocated (fun i => w (1 + i)) z)
    (hr0 : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex w h0 k⟩ : PresentVertex w) (shiftLimitVertex w 1 z))
    (hr1 : ∀ k : ℤ, k ∈ Set.Icc (-2 : ℤ) 2 →
      Reachable (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) z)
    (X0 X1 : ℤ → ℤ) (hzero0 : X0 0 = 0) (hzero1 : X1 0 = 0)
    (hcommon :
      (∀ k k' : ℤ, ∀ (hk : k ∈ Set.Icc (-2 : ℤ) 2)
        (hk' : k' ∈ Set.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb0 (hr0 k' hk') : ℤ) -
          (presentLdpFiniteNat hb0 (hr0 k hk) : ℤ) = X0 k' - X0 k) ∧
      (∀ k k' : ℤ, ∀ (hk : k ∈ Set.Icc (-2 : ℤ) 2)
        (hk' : k' ∈ Set.Icc (-2 : ℤ) 2),
        (presentLdpFiniteNat hb1 (hr1 k' hk') : ℤ) -
          (presentLdpFiniteNat hb1 (hr1 k hk) : ℤ) = X1 k' - X1 k)) :
    (w 0 = 2 → (X0 (-1), X0 1) =
      (X1 (-2) - max (X1 (-1)) 1, -max (X1 (-1)) 1)) ∧
    (w 0 = 0 → (X0 (-1), X0 1) = (-X1 1 - 1, -1)) ∧
    (w 0 = 1 → (X0 (-1), X0 1) = (X1 (-1), X1 2)) := by
  let i0 : Set.Icc (-2 : ℤ) 2 := ⟨0, by constructor <;> omega⟩
  let im1 : Set.Icc (-2 : ℤ) 2 := ⟨-1, by constructor <;> omega⟩
  let im2 : Set.Icc (-2 : ℤ) 2 := ⟨-2, by constructor <;> omega⟩
  let i1 : Set.Icc (-2 : ℤ) 2 := ⟨1, by constructor <;> omega⟩
  let i2 : Set.Icc (-2 : ℤ) 2 := ⟨2, by constructor <;> omega⟩
  let D0 (k : Set.Icc (-2 : ℤ) 2) := presentLdpFiniteNat hb0 (hr0 k.val k.property)
  let D1 (k : Set.Icc (-2 : ℤ) 2) := presentLdpFiniteNat hb1 (hr1 k.val k.property)
  have diff0 (k : Set.Icc (-2 : ℤ) 2) : (D0 k : ℤ) - (D0 i0 : ℤ) = X0 k := by
    simpa only [D0, i0, hzero0, sub_zero] using hcommon.1 0 k i0.property k.property
  have diff1 (k : Set.Icc (-2 : ℤ) 2) : (D1 k : ℤ) - (D1 i0 : ℤ) = X1 k := by
    simpa only [D1, i0, hzero1, sub_zero] using hcommon.2 0 k i0.property k.property
  have b0 (k : Set.Icc (-2 : ℤ) 2) :
      ldpSup (⟨boundaryVertex w h0 k⟩ : PresentVertex w) (shiftLimitVertex w 1 z) =
        (D0 k : WithBot ℕ) := sup_eq_finiteNat hb0 (hr0 k k.property)
  have b1 (k : Set.Icc (-2 : ℤ) 2) :
      ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ :
        PresentVertex (fun i => w (1 + i))) z = (D1 k : WithBot ℕ) :=
    sup_eq_finiteNat hb1 (hr1 k k.property)
  have d0m := diff0 im1
  have d0p := diff0 i1
  have d1m := diff1 im1
  have d1mm := diff1 im2
  have d1p := diff1 i1
  have d1pp := diff1 i2
  change (D0 im1 : ℤ) - (D0 i0 : ℤ) = X0 (-1) at d0m
  change (D0 i1 : ℤ) - (D0 i0 : ℤ) = X0 1 at d0p
  change (D1 im1 : ℤ) - (D1 i0 : ℤ) = X1 (-1) at d1m
  change (D1 im2 : ℤ) - (D1 i0 : ℤ) = X1 (-2) at d1mm
  change (D1 i1 : ℤ) - (D1 i0 : ℤ) = X1 1 at d1p
  change (D1 i2 : ℤ) - (D1 i0 : ℤ) = X1 2 at d1pp
  refine ⟨?_, ?_, ?_⟩
  · intro hw
    have hm := downStep_ldpSup_outerBoundary w h0 h1 hw (-1) (-2)
      (Or.inl ⟨rfl, rfl⟩) z hz
    have hp := downStep_ldpSup_outerBoundary w h0 h1 hw 1 0
      (Or.inr ⟨rfl, rfl⟩) z hz
    have hc := downStep_ldpSup_rootBoundary w h0 h1 hw hb0 z hz
    rw [b0 im1, b1 im2] at hm
    rw [b0 i1, b1 i0] at hp
    rw [b0 i0, b1 im1, b1 i0] at hc
    have hmN : D0 im1 = D1 im2 := WithBot.coe_eq_coe.mp hm
    have hpN : D0 i1 = D1 i0 := WithBot.coe_eq_coe.mp hp
    change (D0 i0 : WithBot ℕ) = ((max (D1 im1) (1 + D1 i0) : ℕ) : WithBot ℕ) at hc
    have hcN : D0 i0 = max (D1 im1) (1 + D1 i0) := WithBot.coe_eq_coe.mp hc
    have hcZ : (D0 i0 : ℤ) = max (D1 im1 : ℤ) (1 + (D1 i0 : ℤ)) := by
      exact_mod_cast hcN
    apply Prod.ext <;> dsimp only
    · omega
    · omega
  · intro hw
    have hm := leftStep_ldpSup_leftBoundary w h0 h1 hw hb0 z hz
      (by simpa only [boundaryVertex_zero] using hr1 0 i0.property)
    have hp := leftStep_ldpSup_rightBoundary w h0 h1 hw hb0 z hz
      (by simpa only [boundaryVertex_one] using hr1 1 i1.property)
    have hc := leftStep_ldpSup_rootBoundary w h0 h1 hw hb0 z hz
    have hm' : ldpSup (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
        (shiftLimitVertex w 1 z) =
        ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ : PresentVertex _) z := by
      simpa only [boundaryVertex_zero] using hm
    have hp' : ldpSup (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 z) =
        ldpSup (⟨boundaryVertex (fun i => w (i + 1)) h1 1⟩ : PresentVertex _) z := by
      simpa only [boundaryVertex_one] using hp
    rw [b0 im1, b1 i0] at hm'
    rw [b0 i1, b1 i1] at hp'
    rw [b0 i0, b1 i1] at hc
    have hmN : D0 im1 = D1 i0 := WithBot.coe_eq_coe.mp hm'
    have hpN : D0 i1 = D1 i1 := WithBot.coe_eq_coe.mp hp'
    change (D0 i0 : WithBot ℕ) = ((1 + D1 i1 : ℕ) : WithBot ℕ) at hc
    have hcN : D0 i0 = 1 + D1 i1 := WithBot.coe_eq_coe.mp hc
    apply Prod.ext <;> dsimp only <;> omega
  · intro hw
    have hm := upStep_ldpSup_boundary w h0 h1 hw hb0 (-1) (-1)
      (Or.inl ⟨rfl, rfl⟩) z hz
    have hp := upStep_ldpSup_boundary w h0 h1 hw hb0 1 2
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) z hz
    have hc := upStep_ldpSup_boundary w h0 h1 hw hb0 0 0
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) z hz
    rw [b0 im1, b1 im1] at hm
    rw [b0 i1, b1 i2] at hp
    rw [b0 i0, b1 i0] at hc
    have hmN : D0 im1 = D1 im1 := WithBot.coe_eq_coe.mp hm
    have hpN : D0 i1 = D1 i2 := WithBot.coe_eq_coe.mp hp
    have hcN : D0 i0 = D1 i0 := WithBot.coe_eq_coe.mp hc
    apply Prod.ext <;> dsimp only <;> omega

end DirectedDistances.Recursive
