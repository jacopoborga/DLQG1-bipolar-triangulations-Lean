module

public import DirectedDistances.Recursive.SDPRelatingUp
public import DirectedDistances.Recursive.SDPRelatingLeft
public import DirectedDistances.Recursive.LDPRelatingAssembly
import DirectedDistances.KMSW.BoundaryEnumeration
import DirectedDistances.KMSW.UIBOTBoundaryM0

/-! # Root cases for first-step SDP identities

The remaining deterministic boundary identities in `lem:SDP-relating-X1-X`
are proved by splitting shortest paths at the time-zero root edge. The up
case is the minimum decomposition in `eqn-sdp-relating3`; the left case adds
the forced initial root edge in `eqn-sdp-relating2`
not Busemann or probabilistic claims. -/

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

private theorem vertex_ext {u : ℕ → Fin 3} {a b : PresentVertex u}
    (h : a.id = b.id) : a = b := by
  cases a
  cases b
  exact congrArg PresentVertex.mk h

private theorem root_ends (w : ℕ → Fin 3) :
    edgeWest w 0 = 0 ∧ edgeEast w 0 = 1 :=
  edge_endpoints_eq w (j := 0) (e := 0) (by change 0 < 1; omega)

private def rootArrow (w : ℕ → Fin 3) :
    (⟨0⟩ : PresentVertex w) ⟶ ⟨1⟩ :=
  ⟨0, ⟨0, by change 0 < 1; omega, rfl⟩,
    (root_ends w).1, (root_ends w).2⟩

private theorem enat_cast_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) = 1 + (n : ℕ∞) := by
  rw [ENat.natCast_add, Nat.cast_one]
  exact add_comm _ _

private theorem boundary_allocated (u : ℕ → Fin 3)
    (h : BoundaryHitWitnesses u) (k : ℤ) :
    boundaryVertex u h k < (kmswStage u (boundaryHitTime u h k)).nextVertex := by
  by_cases hk0 : k = 0
  · subst k
    simp [boundaryVertex_zero, boundaryHitTime_zero, kmswStage, kmswInit]
  · by_cases hk1 : k = 1
    · subst k
      have hm := CutConverse.nextVertex_mono u
        (Nat.zero_le (boundaryHitTime u h 1))
      simpa [boundaryVertex_one, kmswStage, kmswInit] using
        (show 1 < (kmswStage u (boundaryHitTime u h 1)).nextVertex by
          change 2 ≤ _ at hm
          omega)
    · have hb := kmswStage_endpoints_lt_nextVertex u
        (boundaryHitTime u h k) (act u (boundaryHitTime u h k))
        (act_lt_nextEdge u le_rfl)
      rw [(edge_endpoints_eq u (act_lt_nextEdge u le_rfl)).1] at hb
      simpa [boundaryVertex, hk0, hk1, activeInitial] using hb.1

private theorem shifted_boundary_allocated (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    kmswVertexAllocated (fun i => w (1 + i))
      ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ := by
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i
    rw [Nat.add_comm]
  exact ⟨boundaryHitTime _ h k,
    by simpa only [hs] using boundary_allocated _ h k⟩

private theorem boundary_image_of_stage (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => w (i + 1))) (k : ℤ) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h k⟩ =
      (⟨kmswShiftVertexMapAll w 1
        (boundaryHitTime (fun i => w (i + 1)) h k)
        (boundaryVertex (fun i => w (i + 1)) h k)⟩ : PresentVertex w) := by
  apply shiftLimitVertex_eq
  have hs : (fun i : ℕ => w (1 + i)) = (fun i => w (i + 1)) := by
    funext i
    rw [Nat.add_comm]
  simpa only [hs] using boundary_allocated _ h k

private theorem up_boundary_image (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1) {j k : ℤ}
    (hpair : (j = -1 ∧ k = -1) ∨ (j = 0 ∧ k = 0) ∨
      (j = 1 ∧ k = 2)) :
    shiftLimitVertex w 1 ⟨boundaryVertex (fun i => w (i + 1)) h1 k⟩ =
      (⟨boundaryVertex w h0 j⟩ : PresentVertex w) := by
  rw [boundary_image_of_stage]
  apply congrArg PresentVertex.mk
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact upShift_boundaryVertex_left w h0 h1 hw (-1) (by omega)
  · simpa only [boundaryHitTime_zero, boundaryVertex_zero] using
      (upShift_rootVertices w h0 hw).1
  · exact upShift_boundaryVertex_right w h0 h1 hw 2 (by omega)

private theorem boundary_ne_zero (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {k : ℤ} (hk : k ≠ 0) :
    boundaryVertex w h k ≠ 0 := by
  intro he
  have hh := boundaryVertex_injective w h
    (he.trans (boundaryVertex_zero w h).symm)
  exact hk hh

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
    (h0 : BoundaryHitWitnesses w) (j : ℤ)
    {a b : PresentVertex (fun i => w (1 + i))}
    (ha : kmswVertexAllocated (fun i => w (1 + i)) a)
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b)
    (hsource : shiftLimitVertex w 1 a = ⟨boundaryVertex w h0 j⟩)
    (p : Path (⟨boundaryVertex w h0 j⟩ : PresentVertex w)
      (shiftLimitVertex w 1 b))
    (havoid : 0 ∉ pathEdgeList p) : ∃ q : Path a b, q.length = p.length := by
  have hact : act w 0 = 0 := by simp [act, kmswStage, kmswInit]
  obtain ⟨c, hc, q, hq, hlen, _⟩ := upShift_path_lift_avoiding_root
    w h0 j a ha hsource p (by
      intro e he heq
      have he0 : e = 0 := heq.trans hact
      apply havoid
      rw [← he0]
      exact he)
  have hcb : c = b := shiftLimitVertex_injective w 1 hc hb hq
  subst c
  exact ⟨q, hlen⟩

private theorem up_root_sdp_min (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1)
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    sdp (⟨boundaryVertex w h0 0⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
      min
        (sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ :
          PresentVertex (fun i => w (1 + i))) b)
        (1 + sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩ :
          PresentVertex (fun i => w (1 + i))) b) := by
  let a : PresentVertex (fun i => w (1 + i)) :=
    ⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩
  let d : PresentVertex (fun i => w (1 + i)) :=
    ⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩
  have ha : kmswVertexAllocated (fun i => w (1 + i)) a :=
    shifted_boundary_allocated w h1 0
  have hd : kmswVertexAllocated (fun i => w (1 + i)) d :=
    shifted_boundary_allocated w h1 2
  have hroot : shiftLimitVertex w 1 a = (⟨0⟩ : PresentVertex w) := by
    simpa only [a, boundaryVertex_zero] using
      (up_boundary_image w h0 h1 hw (j := 0) (k := 0)
        (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hone : shiftLimitVertex w 1 d = (⟨1⟩ : PresentVertex w) := by
    simpa only [d, boundaryVertex_one] using
      (up_boundary_image w h0 h1 hw (j := 1) (k := 2)
        (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have hle0 : sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
      sdp a b := by
    simpa only [hroot] using upShift_sdp_le w a b
  have hle1 : sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
      1 + sdp d b := by
    have hshift : sdp (⟨1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) ≤ sdp d b := by
      simpa only [hone] using upShift_sdp_le w d b
    calc
      sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
          sdp (⟨0⟩ : PresentVertex w) (⟨1⟩ : PresentVertex w) +
            sdp (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b) :=
        sdp_triangle _ _ _
      _ ≤ ((rootArrow w).toPath.length : ℕ∞) + sdp d b :=
        add_le_add (sdp_le_length (rootArrow w).toPath) hshift
      _ = 1 + sdp d b := by simp [Path.length_toPath]
  have hle : sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
      min (sdp a b) (1 + sdp d b) := le_min hle0 hle1
  have hge : min (sdp a b) (1 + sdp d b) ≤
      sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) := by
    by_cases hr : Reachable (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b)
    · obtain ⟨p, hp⟩ := exists_length_eq_sdp hr
      rcases path_root_cases p with hpavoid | ⟨_, q, hq⟩
      · obtain ⟨r, hrlen⟩ := lift_avoiding w h0 0
          (a := a) (b := b) ha hb hroot p hpavoid
        have hdist : sdp a b ≤ (p.length : ℕ∞) := by
          calc
            sdp a b ≤ r.length := sdp_le_length r
            _ = p.length := by exact_mod_cast hrlen
        exact (min_le_left _ _).trans (hdist.trans_eq hp)
      · obtain ⟨r, hrlen⟩ := lift_avoiding w h0 1
          (a := d) (b := b) hd hb
          (by simpa only [boundaryVertex_one] using hone) q
          (path_avoids_root q (by change (1 : ℕ) ≠ 0; omega))
        have hlenNat : p.length = r.length + 1 := by
          calc
            p.length = q.length + 1 := hq
            _ = r.length + 1 := congrArg (fun n : ℕ => n + 1) hrlen.symm
        have hlen : (p.length : ℕ∞) = 1 + (r.length : ℕ∞) := by
          calc
            (p.length : ℕ∞) = ((r.length + 1 : ℕ) : ℕ∞) :=
              congrArg (fun n : ℕ => (n : ℕ∞)) hlenNat
            _ = 1 + (r.length : ℕ∞) := enat_cast_succ r.length
        have hdist : 1 + sdp d b ≤ (p.length : ℕ∞) := by
          calc
            1 + sdp d b ≤ 1 + r.length :=
              add_le_add_right (sdp_le_length r) 1
            _ = p.length := hlen.symm
        exact (min_le_right _ _).trans (hdist.trans_eq hp)
    · rw [sdp_eq_top_iff_not_reachable.mpr hr]
      exact le_top
  simpa only [boundaryVertex_zero, a, d] using le_antisymm hle hge

/-- The up-step identities for `x^0_{-1}`, `x^0_0`, and `x^0_1` in
The middle identity is a minimum: a shortest path can either continue from
shifted `x^1_0`, or use the time-zero root edge and continue from shifted
`x^1_2`. Unreachable pairs retain value `⊤`, including `1 + ⊤ = ⊤`. -/
theorem upStep_sdp_boundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 1)
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    (sdp (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ :
        PresentVertex (fun i => w (1 + i))) b) ∧
    (sdp (⟨boundaryVertex w h0 0⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
      min
        (sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 0⟩ :
          PresentVertex (fun i => w (1 + i))) b)
        (1 + sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩ :
          PresentVertex (fun i => w (1 + i))) b)) ∧
    (sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩ :
        PresentVertex (fun i => w (1 + i))) b) := by
  have himageLeft := up_boundary_image w h0 h1 hw
    (j := -1) (k := -1) (Or.inl ⟨rfl, rfl⟩)
  have himageRight := up_boundary_image w h0 h1 hw
    (j := 1) (k := 2) (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have haLeft := shifted_boundary_allocated w h1 (-1)
  have haRight := shifted_boundary_allocated w h1 2
  have hleft : sdp (⟨boundaryVertex w h0 (-1)⟩ : PresentVertex w)
      (shiftLimitVertex w 1 b) =
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 (-1)⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
    rw [← himageLeft]
    apply leftStep_sdp_image_eq w haLeft hb
    rw [himageLeft]
    exact boundary_ne_zero w h0 (k := -1) (by omega)
  have hright : sdp (⟨boundaryVertex w h0 1⟩ : PresentVertex w)
      (shiftLimitVertex w 1 b) =
      sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 2⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
    rw [← himageRight]
    apply leftStep_sdp_image_eq w haRight hb
    rw [himageRight, boundaryVertex_one]
    change (1 : ℕ) ≠ 0
    omega
  exact ⟨hleft, up_root_sdp_min w h0 h1 hw b hb, hright⟩

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
    funext i
    rw [Nat.add_comm]
  have h1' : BoundaryHitWitnesses (fun i => w (1 + i)) := hseq.symm ▸ h1
  obtain ⟨k, hk, hka⟩ :=
    (allocated_source_iff_left_boundary _ h1' a.id ha).mp hno
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
    exact left_image_ne_zero w h0 h1 hw b hb
      (congrArg PresentVertex.id he.symm)
  obtain ⟨c, e, q, _, hlen⟩ := (p.length_ne_zero_iff_eq_comp).mp hp
  have he0 : e.val = 0 :=
    left_only_root_outgoing w h0 h1 hw e.property.1 e.property.2.1
  have hc : c = (⟨1⟩ : PresentVertex w) :=
    vertex_ext (e.property.2.2.symm.trans (by rw [he0]; exact (root_ends w).2))
  subst c
  exact ⟨q, hlen⟩

private theorem left_root_image_one (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w) (hw : w 0 = 0) :
    shiftLimitVertex w 1 (⟨1⟩ : PresentVertex (fun i => w (1 + i))) =
      (⟨1⟩ : PresentVertex w) := by
  rw [shiftLimitVertex_eq w 1 0 ⟨1⟩ (by change 1 < 2; omega)]
  apply congrArg PresentVertex.mk
  simpa only [boundaryVertex_one] using
    (leftShift_rootVertices_and_firstStageImage w h0 hw).2.1

/-- For the left first step, every path from `x^0_0` to an image target uses
the time-zero root edge. Thus `eqn-sdp-relating2` has the exact identity
`sdp(x^0_0, image b) = 1 + sdp(x^1_1, b)`, with `⊤` preserved -/
theorem leftStep_sdp_rootBoundary (w : ℕ → Fin 3)
    (h0 : BoundaryHitWitnesses w)
    (h1 : BoundaryHitWitnesses (fun i => w (i + 1)))
    (hw : w 0 = 0)
    (b : PresentVertex (fun i => w (1 + i)))
    (hb : kmswVertexAllocated (fun i => w (1 + i)) b) :
    sdp (⟨boundaryVertex w h0 0⟩ : PresentVertex w)
        (shiftLimitVertex w 1 b) =
      1 + sdp (⟨boundaryVertex (fun i => w (i + 1)) h1 1⟩ :
        PresentVertex (fun i => w (1 + i))) b := by
  let a : PresentVertex (fun i => w (1 + i)) := ⟨1⟩
  have ha : kmswVertexAllocated (fun i => w (1 + i)) a := by
    exact ⟨0, by change 1 < 2; omega⟩
  have himage : shiftLimitVertex w 1 a = (⟨1⟩ : PresentVertex w) :=
    left_root_image_one w h0 hw
  have hdist : sdp (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b) =
      sdp a b := by
    rw [← himage]
    exact leftStep_sdp_image_eq w ha hb
      (by rw [himage]; change (1 : ℕ) ≠ 0; omega)
  have hidentity : sdp (⟨0⟩ : PresentVertex w)
      (shiftLimitVertex w 1 b) = 1 + sdp a b := by
    apply le_antisymm
    · calc
        sdp (⟨0⟩ : PresentVertex w) (shiftLimitVertex w 1 b) ≤
            sdp (⟨0⟩ : PresentVertex w) (⟨1⟩ : PresentVertex w) +
              sdp (⟨1⟩ : PresentVertex w) (shiftLimitVertex w 1 b) :=
          sdp_triangle _ _ _
        _ ≤ ((rootArrow w).toPath.length : ℕ∞) + sdp a b :=
          add_le_add (sdp_le_length (rootArrow w).toPath) hdist.le
        _ = 1 + sdp a b := by simp [Path.length_toPath]
    · apply le_iInf
      intro p
      obtain ⟨q, hq⟩ := left_root_paths w h0 h1 hw hb p
      calc
        1 + sdp a b = 1 + sdp (⟨1⟩ : PresentVertex w)
            (shiftLimitVertex w 1 b) := by rw [hdist]
        _ ≤ 1 + q.length := add_le_add_right (sdp_le_length q) 1
        _ = p.length := by
          calc
            1 + (q.length : ℕ∞) = ((q.length + 1 : ℕ) : ℕ∞) :=
              (enat_cast_succ q.length).symm
            _ = (p.length : ℕ∞) :=
              congrArg (fun n : ℕ => (n : ℕ∞)) hq.symm
  simpa only [boundaryVertex_zero, boundaryVertex_one, a] using hidentity

end DirectedDistances.Recursive
