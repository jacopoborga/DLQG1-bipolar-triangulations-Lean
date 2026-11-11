module

public import DirectedDistances.KMSW.MonotoneLayoutInvariant
public import DirectedDistances.PlanarMap.MonotonePolyline






public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set



@[expose] noncomputable def layoutDart (w : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage w m).nextEdge) : Polyline :=
  if d.2 then (layoutArc w m d.1.val).reverse else layoutArc w m d.1.val



structure LayoutGood (w : ℕ → Fin 3) (m : ℕ) : Prop where
  interior_disjoint : ∀ d e, e ≠ d → e ≠ edgeFlip _ d →
    Disjoint (layoutDart w m d).interior (layoutDart w m e).interior
  interior_avoids_vertices : ∀ d (v : Fin (kmswStage w m).nextVertex),
    layoutPos w m v.val ∉ (layoutDart w m d).interior
  initial_arg_injective : ∀ d e, stageVertex w m d = stageVertex w m e →
    Complex.arg (layoutDart w m d).initialDirection =
      Complex.arg (layoutDart w m e).initialDirection → d = e
  rotation_agreement : ∀ d,
    CcwSuccessor {e | stageVertex w m e = stageVertex w m d}
      (fun e => (layoutDart w m e).initialDirection) d (stageRot w m d)

private theorem reverse_point (p : Polyline) (i : ℕ) (hi : i < p.points.length) :
    p.reverse.point i = p.point (p.points.length - 1 - i) := by
  have hj : p.points.length - 1 - i < p.points.length := by omega
  change p.points.reverse.getD i p.reverse.start =
    p.points.getD (p.points.length - 1 - i) p.start
  rw [List.getD_reverse i hi]
  rw [List.getD_eq_getElem (l := p.points) (d := p.reverse.start) hj]
  rw [List.getD_eq_getElem (l := p.points) (d := p.start) hj]

private theorem reverse_segment (p : Polyline) (i : ℕ)
    (hi : i + 1 < p.points.length) :
    p.reverse.segmentAt i = p.segmentAt (p.points.length - 2 - i) := by
  unfold Polyline.segmentAt
  rw [reverse_point p i (by omega), reverse_point p (i + 1) hi]
  have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
  have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
  rw [h₁, h₂, segment_symm]

private theorem simple_reverse (p : Polyline) (hp : p.IsSimple) : p.reverse.IsSimple := by
  have hlen : p.reverse.points.length = p.points.length := List.length_reverse
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    rw [reverse_point p i (by omega), reverse_point p (i + 1) hi]
    have h₁ : p.points.length - 1 - i = p.points.length - 2 - i + 1 := by omega
    have h₂ : p.points.length - 1 - (i + 1) = p.points.length - 2 - i := by omega
    rw [h₁, h₂]
    exact (hp.1 _ (by omega)).symm
  · intro i hi
    rw [hlen] at hi
    rw [reverse_segment p i (by omega), reverse_segment p (i + 1) (by omega),
      reverse_point p (i + 1) (by omega)]
    have h₁ : p.points.length - 2 - i = p.points.length - 2 - (i + 1) + 1 := by omega
    have h₂ : p.points.length - 1 - (i + 1) =
        p.points.length - 2 - (i + 1) + 1 := by omega
    rw [h₁, h₂, inter_comm]
    exact hp.2.1 _ (by omega)
  · intro i j hi hj hij
    rw [hlen] at hi hj
    rw [reverse_segment p i hi, reverse_segment p j hj]
    exact (hp.2.2 _ _ (by omega) (by omega) (by omega)).symm

private theorem layoutArc_length (w : ℕ → Fin 3) (m e : ℕ) :
    2 ≤ (layoutArc w m e).points.length := by
  induction m with
  | zero => exact le_refl 2
  | succ m ih =>
    rw [layoutArc]
    split
    · exact ih
    · split
      · split
        · exact le_refl 2
        · exact roofArc_length _ _ _ _
      · exact ih



@[expose] noncomputable def monotoneLayoutDrawing (w : ℕ → Fin 3) (m : ℕ)
    (h : LayoutGood w m) : StageDrawing w m where
  flip_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  flip_ne := by
    rintro ⟨e, b⟩ he
    have hb := congrArg Prod.snd he
    cases b <;> cases hb
  vert_rotation := by
    intro d
    apply Fin.ext
    exact ((stageRot_sameCycle_iff_endpoint_eq w m d (stageRot w m d)).1 ⟨1, rfl⟩).symm
  pos := fun v => layoutPos w m v.val
  pos_injective := by
    intro v u hvu
    exact Fin.ext (layoutPos_injective w m v.val u.val v.isLt u.isLt hvu)
  arc := layoutDart w m
  arc_simple := by
    rintro ⟨e, b⟩
    have hs := Polyline.isSimple_of_XMonotone (layoutArc_points_pairwise w m e e.isLt)
      (layoutArc_length w m e)
    cases b
    · exact hs
    · exact simple_reverse _ hs
  arc_length := by
    rintro ⟨e, b⟩
    cases b
    · exact layoutArc_length w m e
    · simpa only [layoutDart, Bool.true_eq, ↓reduceIte, Polyline.reverse,
        List.length_reverse] using layoutArc_length w m e
  arc_start := by
    rintro ⟨e, b⟩
    cases b <;> simp only [layoutDart, Bool.false_eq_true, ↓reduceIte,
      Polyline.start_reverse, stageVertex, stageEndpoint]
    · exact layoutArc_start w m e e.isLt
    · exact layoutArc_finish w m e e.isLt
  arc_finish := by
    rintro ⟨e, b⟩
    cases b <;> simp only [layoutDart, Bool.false_eq_true, ↓reduceIte,
      Polyline.finish_reverse, stageVertex, stageEndpoint, edgeFlip,
      Equiv.coe_fn_mk, Bool.not_false, Bool.not_true]
    · exact layoutArc_finish w m e e.isLt
    · exact layoutArc_start w m e e.isLt
  arc_flip := by
    rintro ⟨e, b⟩
    cases b <;> simp [layoutDart, edgeFlip]
  interior_disjoint := h.interior_disjoint
  interior_avoids_vertices := h.interior_avoids_vertices
  locally_finite := by intro K _; exact Set.toFinite _
  initial_nonzero := by
    rintro ⟨e, b⟩
    have hp := layoutArc_points_pairwise w m e e.isLt
    have hl := layoutArc_length w m e
    cases b
    · exact Polyline.initialDirection_ne_zero hp hl
    · intro he
      have hn := Polyline.reverse_initialDirection_re_neg hp hl
      change (layoutArc w m e).reverse.initialDirection = 0 at he
      rw [he, Complex.zero_re] at hn
      exact (lt_irrefl 0) hn
  initial_arg_injective := h.initial_arg_injective
  rotation_agreement := h.rotation_agreement



theorem monotoneLayoutDrawing_extends (w : ℕ → Fin 3) (n : ℕ)
    (h : LayoutGood w n) (h' : LayoutGood w (n + 1)) :
    StageExtends w n (monotoneLayoutDrawing w n h) (monotoneLayoutDrawing w (n + 1) h') := by
  constructor
  · intro v
    exact (layoutPos_old_vertex w n v.val v.isLt).symm
  · rintro ⟨e, b⟩
    change (if b then (layoutArc w n e.val).reverse else layoutArc w n e.val) =
      (if b then (layoutArc w (n + 1) e.val).reverse else layoutArc w (n + 1) e.val)
    rw [layoutArc_old w n e.val e.isLt]



theorem layoutGood_of_layout {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (pos_layout : ∀ v, P.pos v = layoutPos w m v.val)
    (arc_layout : ∀ d, P.arc d = layoutDart w m d) : LayoutGood w m where
  interior_disjoint := by
    intro d e hne hf
    simpa only [arc_layout] using P.interior_disjoint d e hne hf
  interior_avoids_vertices := by
    intro d v
    simpa only [pos_layout, arc_layout] using P.interior_avoids_vertices d v
  initial_arg_injective := by
    intro d e hv ha
    apply P.initial_arg_injective d e hv
    simpa only [arc_layout] using ha
  rotation_agreement := by
    intro d
    simpa only [arc_layout] using P.rotation_agreement d

private theorem drawing_eq {w : ℕ → Fin 3} {m : ℕ} (P Q : StageDrawing w m)
    (hpos : P.pos = Q.pos) (harc : P.arc = Q.arc) : P = Q := by
  cases P
  cases Q
  cases hpos
  cases harc
  rfl



theorem eq_monotoneLayoutDrawing {w : ℕ → Fin 3} {m : ℕ} (P : StageDrawing w m)
    (pos_layout : ∀ v, P.pos v = layoutPos w m v.val)
    (arc_layout : ∀ d, P.arc d = layoutDart w m d) :
    P = monotoneLayoutDrawing w m (layoutGood_of_layout P pos_layout arc_layout) :=
  drawing_eq P _ (funext pos_layout) (funext arc_layout)



theorem layoutGood_of_invariant {w : ℕ → Fin 3} {m : ℕ} {P : StageDrawing w m}
    (G : MonotoneStageInvariant w m P) : LayoutGood w m :=
  layoutGood_of_layout P G.pos_layout G.arc_layout



@[expose] noncomputable def invariant_layoutDrawing {w : ℕ → Fin 3} {m : ℕ} {P : StageDrawing w m}
    (G : MonotoneStageInvariant w m P) :
    MonotoneStageInvariant w m (monotoneLayoutDrawing w m (layoutGood_of_invariant G)) := by
  have h : P = monotoneLayoutDrawing w m (layoutGood_of_invariant G) :=
    eq_monotoneLayoutDrawing P G.pos_layout G.arc_layout
  exact h ▸ G



theorem layoutGood_zero (w : ℕ → Fin 3) : LayoutGood w 0 :=
  layoutGood_of_invariant (kmswStage0MonotoneInvariant w)

end DirectedDistances.KMSW
