/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLCornerSector
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12

/-! # Inserting a chord between two vertex corners

The two new dart identities are `Sum.inr true` and `Sum.inr false`. -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace D39FiniteBall

variable (B : D39FiniteBall)

/-- Helper toward Proposition 5.16: reversal on the augmented dart carrier. -/
@[expose] def chordEdgeInv : Equiv.Perm (B.D ⊕ Bool) where
  toFun := Sum.map B.map.edgeInv Bool.not
  invFun := Sum.map B.map.edgeInv Bool.not
  left_inv := by
    intro d
    cases d with
    | inl d => simp [B.map.edgeInv_invol]
    | inr t => cases t <;> rfl
  right_inv := by
    intro d
    cases d with
    | inl d => simp [B.map.edgeInv_invol]
    | inr t => cases t <;> rfl

/-- Helper toward Proposition 5.16: the new reversal has no fixed dart. -/
theorem chordEdgeInv_ne (d : B.D ⊕ Bool) : B.chordEdgeInv d ≠ d := by
  cases d with
  | inl d => exact fun h => B.map.edgeInv_ne d (Sum.inl.inj h)
  | inr t => cases t <;> simp [chordEdgeInv]

/-- Helper toward Proposition 5.16: splice the new darts immediately after
the two specified old darts, with an explicit inverse. -/
@[expose] def chordRotation (a b : B.D) (hab : a ≠ b) :
    Equiv.Perm (B.D ⊕ Bool) where
  toFun
    | .inl d => if d = a then .inr true else if d = b then .inr false
      else .inl (B.map.rot d)
    | .inr true => .inl (B.map.rot a)
    | .inr false => .inl (B.map.rot b)
  invFun
    | .inl d => if d = B.map.rot a then .inr true
      else if d = B.map.rot b then .inr false else .inl (B.map.rot.symm d)
    | .inr true => .inl a
    | .inr false => .inl b
  left_inv := by
    intro d
    cases d with
    | inl d =>
      by_cases ha : d = a
      · subst d; simp
      · by_cases hb : d = b
        · subst d; simp [Ne.symm hab]
        · simp [ha, hb]
    | inr t => cases t <;> simp [Ne.symm hab]
  right_inv := by
    intro d
    cases d with
    | inl d =>
      by_cases ha : d = B.map.rot a
      · subst d; simp
      · by_cases hb : d = B.map.rot b
        · subst d; simp [Ne.symm hab]
        · have hsa : B.map.rot.symm d ≠ a := by
            intro h
            exact ha ((B.map.rot.apply_symm_apply d).symm.trans (congrArg B.map.rot h))
          have hsb : B.map.rot.symm d ≠ b := by
            intro h
            exact hb ((B.map.rot.apply_symm_apply d).symm.trans (congrArg B.map.rot h))
          simp [ha, hb, hsa, hsb]
    | inr t => cases t <;> simp [Ne.symm hab]

/-- Helper toward Proposition 5.16: the augmented finite combinatorial map. -/
@[expose] def chordMap (a b : B.D) (hab : a ≠ b) :
    CombinatorialMap (B.D ⊕ Bool) where
  edgeInv := B.chordEdgeInv
  edgeInv_invol := by
    intro d
    cases d with
    | inl d => exact congrArg Sum.inl (B.map.edgeInv_invol d)
    | inr t => cases t <;> rfl
  edgeInv_ne := B.chordEdgeInv_ne
  rot := B.chordRotation a b hab

/-- Helper toward Proposition 5.16: the augmented finite ball retains old
tags and the old root, marks neither new dart missing or tail, and records
all faces as original. -/
@[expose] def insertChord (a b : B.D) (hab : a ≠ b) : D39FiniteBall where
  D := B.D ⊕ Bool
  map := B.chordMap a b hab
  missing := Sum.elim B.missing (fun _ => False)
  tail := Sum.elim B.tail (fun _ => False)
  rootDart := .inl B.rootDart
  original := Set.univ
  original_closed := by simp

/-- Helper toward Proposition 5.16: the old darts embed without identification. -/
@[expose] def insertChordIota (a b : B.D) (hab : a ≠ b) :
    B.D ↪ (B.insertChord a b hab).D := ⟨Sum.inl, Sum.inl_injective⟩

/-- Helper toward Proposition 5.16: the old missing and tail tags persist,
both new tags are false, the ordered root persists, and every augmented
dart is marked original. -/
theorem insertChord_retained_data (a b : B.D) (hab : a ≠ b) :
    (∀ d, (B.insertChord a b hab).missing (.inl d) ↔ B.missing d) ∧
    (∀ d, (B.insertChord a b hab).tail (.inl d) ↔ B.tail d) ∧
    (∀ t, ¬ (B.insertChord a b hab).missing (.inr t)) ∧
    (∀ t, ¬ (B.insertChord a b hab).tail (.inr t)) ∧
    (B.insertChord a b hab).rootDart = .inl B.rootDart ∧
    (B.insertChord a b hab).original = Set.univ := by
  exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ h => h,
    fun _ h => h, rfl, rfl⟩

/-- Helper toward Proposition 5.16: the old-dart inclusion commutes with
the augmented edge involution. -/
theorem insertChordIota_edgeInv (a b : B.D) (hab : a ≠ b) (d : B.D) :
    (B.insertChord a b hab).map.edgeInv (B.insertChordIota a b hab d) =
      B.insertChordIota a b hab (B.map.edgeInv d) := rfl

/-- Helper toward Proposition 5.16: every old edge reversal is unchanged. -/
@[simp] theorem chordEdgeInv_inl (d : B.D) :
    B.chordEdgeInv (.inl d) = .inl (B.map.edgeInv d) := rfl

/-- Helper toward Proposition 5.16: the new darts reverse each other. -/
@[simp] theorem chordEdgeInv_inr (t : Bool) :
    B.chordEdgeInv (.inr t) = .inr (!t) := rfl

/-- Helper toward Proposition 5.16: rotation departs the first corner along the chord. -/
@[simp] theorem chordRotation_a (a b : B.D) (hab : a ≠ b) :
    B.chordRotation a b hab (.inl a) = .inr true := by simp [chordRotation]

/-- Helper toward Proposition 5.16: rotation departs the second corner along the reverse chord. -/
@[simp] theorem chordRotation_b (a b : B.D) (hab : a ≠ b) :
    B.chordRotation a b hab (.inl b) = .inr false := by
  simp [chordRotation, Ne.symm hab]

/-- Helper toward Proposition 5.16: rotation rejoins the first old star. -/
@[simp] theorem chordRotation_true (a b : B.D) (hab : a ≠ b) :
    B.chordRotation a b hab (.inr true) = .inl (B.map.rot a) := rfl

/-- Helper toward Proposition 5.16: rotation rejoins the second old star. -/
@[simp] theorem chordRotation_false (a b : B.D) (hab : a ≠ b) :
    B.chordRotation a b hab (.inr false) = .inl (B.map.rot b) := rfl

/-- Helper toward Proposition 5.16: rotation is unchanged away from the two corners. -/
theorem chordRotation_other (a b d : B.D) (hab : a ≠ b) (ha : d ≠ a) (hb : d ≠ b) :
    B.chordRotation a b hab (.inl d) = .inl (B.map.rot d) := by
  simp [chordRotation, ha, hb]

variable {V : Type*} (vert : B.D → V)
  (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)

/-- Helper toward Proposition 5.16: distinct endpoint vertices give distinct corner darts. -/
theorem chord_corners_ne (a b : B.D) (hv : vert a ≠ vert b) : a ≠ b :=
  fun h => hv (congrArg vert h)

include P in
/-- Helper toward Proposition 5.16: rotation cannot carry one endpoint corner to the other. -/
theorem chord_rot_corner_ne (a b : B.D) (hv : vert a ≠ vert b) : B.map.rot a ≠ b := by
  intro h
  exact hv ((P.vert_rotation a).symm.trans (congrArg vert h))

/-- Helper toward Proposition 5.16: old dart vertices persist, and new darts
start at their respective chord endpoints. -/
@[expose] def chordVert (a b : B.D) : B.D ⊕ Bool → V
  | .inl d => vert d
  | .inr true => vert a
  | .inr false => vert b

include P in
/-- Helper toward Proposition 5.16: the augmented rotation preserves vertices. -/
theorem chordVert_rotation (a b : B.D) (hab : a ≠ b) (d : B.D ⊕ Bool) :
    B.chordVert vert a b (B.chordRotation a b hab d) = B.chordVert vert a b d := by
  cases d with
  | inl d =>
    by_cases ha : d = a
    · subst d; simp [chordVert]
    · by_cases hb : d = b
      · subst d; simp [chordVert]
      · rw [B.chordRotation_other a b d hab ha hb]
        exact P.vert_rotation d
  | inr t => cases t <;> exact P.vert_rotation _

/-- Helper toward Proposition 5.16: the arc family retains old arcs and adds
the chord and its reverse. -/
@[expose] def chordArc (g : Polyline) : B.D ⊕ Bool → Polyline
  | .inl d => P.arc d
  | .inr true => g
  | .inr false => g.reverse

/-- Helper toward Proposition 5.16: old arcs are unchanged. -/
@[simp] theorem chordArc_inl (g : Polyline) (d : B.D) :
    B.chordArc vert P g (.inl d) = P.arc d := rfl

/-- Helper toward Proposition 5.16: every augmented arc is simple. -/
theorem chordArc_simple (g : Polyline) (hg : g.IsSimple) (d : B.D ⊕ Bool) :
    (B.chordArc vert P g d).IsSimple := by
  cases d with
  | inl d => exact P.arc_simple d
  | inr t =>
    cases t
    · exact Polyline.isSimple_reverse_transfer g hg
    · exact hg

/-- Helper toward Proposition 5.16: every augmented arc has at least two points. -/
theorem chordArc_length (g : Polyline) (hg : 2 ≤ g.points.length) (d : B.D ⊕ Bool) :
    2 ≤ (B.chordArc vert P g d).points.length := by
  cases d with
  | inl d => exact P.arc_length d
  | inr t =>
    cases t
    · simpa [chordArc, Polyline.reverse] using hg
    · exact hg

/-- Helper toward Proposition 5.16: all augmented arcs have their prescribed starts. -/
theorem chordArc_start (a b : B.D) (g : Polyline)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = P.pos (vert b)) (d : B.D ⊕ Bool) :
    (B.chordArc vert P g d).start = P.pos (B.chordVert vert a b d) := by
  cases d with
  | inl d => exact P.arc_start d
  | inr t =>
    cases t
    · exact (Polyline.start_reverse g).trans hf
    · exact hs

/-- Helper toward Proposition 5.16: all augmented arcs have their prescribed finishes. -/
theorem chordArc_finish (a b : B.D) (g : Polyline)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = P.pos (vert b)) (d : B.D ⊕ Bool) :
    (B.chordArc vert P g d).finish =
      P.pos (B.chordVert vert a b (B.chordEdgeInv d)) := by
  cases d with
  | inl d => exact P.arc_finish d
  | inr t =>
    cases t
    · exact (Polyline.finish_reverse g).trans hs
    · exact hf

/-- Helper toward Proposition 5.16: edge reversal reverses the augmented arcs. -/
theorem chordArc_flip (g : Polyline) (d : B.D ⊕ Bool) :
    B.chordArc vert P g (B.chordEdgeInv d) = (B.chordArc vert P g d).reverse := by
  cases d with
  | inl d => exact P.arc_flip d
  | inr t =>
    cases t
    · exact (Polyline.reverse_reverse g).symm
    · rfl

/-- Helper toward Proposition 5.16: the augmented geometric image is exactly
the old image union the new closed chord. -/
theorem chordArc_image (g : Polyline) :
    Set.range P.pos ∪ {z | ∃ d, z ∈ (B.chordArc vert P g d).image} =
      P.image ∪ g.image := by
  ext z
  constructor
  · rintro (hz | ⟨d, hz⟩)
    · exact Or.inl (Or.inl hz)
    · cases d with
      | inl d => exact Or.inl (Or.inr ⟨d, hz⟩)
      | inr t =>
        cases t
        · exact Or.inr ((Polyline.image_reverse_transfer g) ▸ hz)
        · exact Or.inr hz
  · rintro ((hz | ⟨d, hz⟩) | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨.inl d, hz⟩
    · exact Or.inr ⟨.inr true, hz⟩

/-- Helper toward Proposition 5.16: every new arc interior avoids the old image. -/
theorem chordArc_new_interior_disjoint (g : Polyline)
    (hdis : Disjoint g.interior P.image) (t : Bool) :
    Disjoint (B.chordArc vert P g (.inr t)).interior P.image := by
  cases t
  · simpa only [chordArc, Polyline.interior_reverse_transfer] using hdis
  · exact hdis

/-- Helper toward Proposition 5.16: distinct geometric edges have disjoint
augmented arc interiors. -/
theorem chordArc_interior_disjoint (g : Polyline)
    (hdis : Disjoint g.interior P.image) (d e : B.D ⊕ Bool)
    (hne : e ≠ d) (hflip : e ≠ B.chordEdgeInv d) :
    Disjoint (B.chordArc vert P g d).interior (B.chordArc vert P g e).interior := by
  have hsub (x : B.D) : (P.arc x).interior ⊆ P.image :=
    fun _ hz => Or.inr ⟨x, hz.1⟩
  cases d with
  | inl d =>
    cases e with
    | inl e =>
      exact P.interior_disjoint d e (fun h => hne (congrArg Sum.inl h))
        (fun h => hflip (congrArg Sum.inl h))
    | inr t =>
      exact ((B.chordArc_new_interior_disjoint vert P g hdis t).mono_right (hsub d)).symm
  | inr t =>
    cases e with
    | inl e =>
      exact (B.chordArc_new_interior_disjoint vert P g hdis t).mono_right (hsub e)
    | inr s =>
      cases t <;> cases s <;> simp_all [chordEdgeInv]

/-- Helper toward Proposition 5.16: augmented interiors avoid every vertex position. -/
theorem chordArc_interior_avoids_vertices (g : Polyline)
    (hdis : Disjoint g.interior P.image) (d : B.D ⊕ Bool) (v : V) :
    P.pos v ∉ (B.chordArc vert P g d).interior := by
  cases d with
  | inl d => exact P.interior_avoids_vertices d v
  | inr t =>
    intro hz
    exact Set.disjoint_left.mp (B.chordArc_new_interior_disjoint vert P g hdis t)
      hz (Or.inl ⟨v, rfl⟩)

/-- Helper toward Proposition 5.16: the augmented finite drawing is locally finite. -/
theorem chordArc_locally_finite (g : Polyline) (K : Set ℂ)
    (_hK : Bornology.IsBounded K) :
    {d | (K ∩ (B.chordArc vert P g d).image).Nonempty}.Finite := Set.toFinite _

/-- Helper toward Proposition 5.16: simplicity and two points give a nonzero initial direction. -/
theorem chord_initial_nonzero (g : Polyline) (hg : g.IsSimple)
    (hlen : 2 ≤ g.points.length) : g.initialDirection ≠ 0 := by
  intro h
  have heq := sub_eq_zero.mp h
  exact hg.1 0 (by omega) (g.point_zero_eq_start.trans heq.symm)

/-- Helper toward Proposition 5.16: all augmented initial directions are nonzero. -/
theorem chordArc_initial_nonzero (g : Polyline) (hg : g.IsSimple)
    (hlen : 2 ≤ g.points.length) (d : B.D ⊕ Bool) :
    (B.chordArc vert P g d).initialDirection ≠ 0 := by
  cases d with
  | inl d => exact P.initial_nonzero d
  | inr t =>
    cases t
    · exact chord_initial_nonzero g.reverse (Polyline.isSimple_reverse_transfer g hg)
        (by simpa [Polyline.reverse] using hlen)
    · exact chord_initial_nonzero g hg hlen

/-- Helper toward Proposition 5.16: the two local augmented successor
conditions and distinct endpoint arguments put a new direction strictly
inside its old corner, including a singleton old star. -/
theorem chord_strict_turn_of_successors {E : Type*} {star : Set E} {dir : E → ℂ}
    {a r n : E} (hna : n ≠ a) (hnr : n ≠ r)
    (ha : CcwSuccessor star dir a n) (hn : CcwSuccessor star dir n r)
    (harg : (dir a).arg ≠ (dir n).arg) :
    ccwTurn (dir a) (dir n) < ccwTurn (dir a) (dir r) := by
  have hamem := ha.2.1
  have hlt := d39_ccwTurn_lt_two_pi harg
  by_cases hra : r = a
  · subst r
    rw [(ccwTurn_eq_two_pi_iff _ _).mpr rfl]
    exact hlt
  · rcases ha.2.2.2 with ha | ha
    · exact (hna ha.1).elim
    · have hle := ha.2 r hn.2.2.1 hra
      apply lt_of_le_of_ne hle
      intro heq
      have hargnr := ccwTurn_left_injective heq
      have hfull : ccwTurn (dir n) (dir r) = 2 * Real.pi :=
        (ccwTurn_eq_two_pi_iff _ _).mpr hargnr
      rcases hn.2.2.2 with hn | hn
      · exact hnr hn.1.symm
      · have hbound := hn.2 a hamem (Ne.symm hna)
        have hlt' := d39_ccwTurn_lt_two_pi (Ne.symm harg)
        rw [hfull] at hbound
        exact (not_lt_of_ge hbound) hlt'

/-- Helper toward Proposition 5.16: a direction strictly inside an old
corner differs in argument from every old dart at that vertex. -/
theorem chord_direction_ne_old (a : B.D) (u : ℂ)
    (hturn : ccwTurn (P.arc a).initialDirection u <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (e : B.D) (he : vert e = vert a) :
    u.arg ≠ (P.arc e).initialDirection.arg := by
  intro harg
  have ht : ccwTurn (P.arc a).initialDirection u =
      ccwTurn (P.arc a).initialDirection (P.arc e).initialDirection := by
    simp only [ccwTurn, harg]
  rw [ht] at hturn
  by_cases hea : e = a
  · subst e
    rw [(ccwTurn_eq_two_pi_iff _ _).mpr rfl] at hturn
    exact (not_lt_of_ge (ccwTurn_le_two_pi _ _)) hturn
  · rcases (P.rotation_agreement a).2.2.2 with hs | hs
    · have hm : e ∈ ({a} : Set B.D) := hs.2 ▸ he
      exact hea hm
    · exact (not_lt_of_ge (hs.2 e he hea)) hturn

/-- Helper toward Proposition 5.16: inserting a ray inside one old corner
does not precede the old successor of a different dart at that vertex. -/
theorem chord_old_successor_le_new (a d : B.D) (u : ℂ)
    (hturn : ccwTurn (P.arc a).initialDirection u <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (hv : vert d = vert a) (hda : d ≠ a) :
    ccwTurn (P.arc d).initialDirection (P.arc (B.map.rot d)).initialDirection ≤
      ccwTurn (P.arc d).initialDirection u := by
  have had : (P.arc a).initialDirection.arg ≠ (P.arc d).initialDirection.arg := by
    intro h
    exact hda (P.initial_arg_injective a d hv.symm h).symm
  have hud := B.chord_direction_ne_old vert P a u hturn d hv
  have hua := B.chord_direction_ne_old vert P a u hturn a rfl
  have hamin : ccwTurn (P.arc a).initialDirection
      (P.arc (B.map.rot a)).initialDirection ≤
      ccwTurn (P.arc a).initialDirection (P.arc d).initialDirection := by
    rcases (P.rotation_agreement a).2.2.2 with hs | hs
    · have hm : d ∈ ({a} : Set B.D) := hs.2 ▸ hv
      exact (hda hm).elim
    · exact hs.2 d hv hda
  have hcyc := (d39_between_cyclic had (Ne.symm hud) hua).mp (hturn.trans_le hamin)
  have hdmin : ccwTurn (P.arc d).initialDirection
      (P.arc (B.map.rot d)).initialDirection ≤
      ccwTurn (P.arc d).initialDirection (P.arc a).initialDirection := by
    rcases (P.rotation_agreement d).2.2.2 with hs | hs
    · have hm : a ∈ ({d} : Set B.D) := hs.2 ▸ hv.symm
      exact (hda hm.symm).elim
    · exact hs.2 a hv.symm (Ne.symm hda)
  exact hdmin.trans hcyc.le

/-- Helper toward Proposition 5.16: strict corner insertion preserves
injectivity of initial arguments at each augmented vertex. -/
theorem chordArc_initial_arg_injective (a b : B.D) (hvab : vert a ≠ vert b)
    (g : Polyline)
    (hta : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (htb : ccwTurn (P.arc b).initialDirection g.reverse.initialDirection <
      ccwTurn (P.arc b).initialDirection (P.arc (B.map.rot b)).initialDirection)
    (d e : B.D ⊕ Bool) (hv : B.chordVert vert a b d = B.chordVert vert a b e)
    (harg : (B.chordArc vert P g d).initialDirection.arg =
      (B.chordArc vert P g e).initialDirection.arg) : d = e := by
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (P.initial_arg_injective d e hv harg)
    | inr t =>
      cases t
      · exact (B.chord_direction_ne_old vert P b g.reverse.initialDirection htb d hv
          harg.symm).elim
      · exact (B.chord_direction_ne_old vert P a g.initialDirection hta d hv
          harg.symm).elim
  | inr t =>
    cases e with
    | inl e =>
      cases t
      · exact (B.chord_direction_ne_old vert P b g.reverse.initialDirection htb e hv.symm
          harg).elim
      · exact (B.chord_direction_ne_old vert P a g.initialDirection hta e hv.symm
          harg).elim
    | inr s =>
      cases t <;> cases s
      · rfl
      · exact (hvab hv.symm).elim
      · exact (hvab hv).elim
      · rfl

/-- Helper toward Proposition 5.16: away from the two split corners,
the old successor remains the augmented counterclockwise successor. -/
theorem chordArc_rotation_other (a b d : B.D) (hab : a ≠ b)
    (g : Polyline)
    (hta : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (htb : ccwTurn (P.arc b).initialDirection g.reverse.initialDirection <
      ccwTurn (P.arc b).initialDirection (P.arc (B.map.rot b)).initialDirection)
    (hda : d ≠ a) (hdb : d ≠ b) :
    CcwSuccessor {e | B.chordVert vert a b e = B.chordVert vert a b (.inl d)}
      (fun e => (B.chordArc vert P g e).initialDirection)
      (.inl d) (B.chordRotation a b hab (.inl d)) := by
  rw [B.chordRotation_other a b d hab hda hdb]
  refine ⟨Set.toFinite _, rfl, P.vert_rotation d, ?_⟩
  rcases (P.rotation_agreement d).2.2.2 with hs | hs
  · left
    refine ⟨congrArg Sum.inl hs.1, ?_⟩
    ext e
    constructor
    · intro he
      cases e with
      | inl e =>
        have hm : e ∈ ({d} : Set B.D) := hs.2 ▸ he
        exact congrArg Sum.inl (show e = d from hm)
      | inr t =>
        cases t
        · have hm : b ∈ ({d} : Set B.D) := hs.2 ▸ he
          exact (hdb (show b = d from hm).symm).elim
        · have hm : a ∈ ({d} : Set B.D) := hs.2 ▸ he
          exact (hda (show a = d from hm).symm).elim
    · intro he
      rw [Set.mem_singleton_iff] at he
      subst e
      rfl
  · right
    refine ⟨fun h => hs.1 (Sum.inl.inj h), ?_⟩
    intro e he hne
    cases e with
    | inl e => exact hs.2 e he (fun h => hne (congrArg Sum.inl h))
    | inr t =>
      cases t
      · exact B.chord_old_successor_le_new vert P b d g.reverse.initialDirection
          htb he.symm hdb
      · exact B.chord_old_successor_le_new vert P a d g.initialDirection
          hta he.symm hda

section Drawing

variable (a b : B.D) (hvab : vert a ≠ vert b) (g : Polyline)
  (hg : g.IsSimple) (hstart : g.start = P.pos (vert a))
  (hfinish : g.finish = P.pos (vert b)) (hdis : Disjoint g.interior P.image)
  (ha : CcwSuccessor {e | B.chordVert vert a b e = vert a}
    (fun e => (B.chordArc vert P g e).initialDirection) (.inl a) (.inr true))
  (hga : CcwSuccessor {e | B.chordVert vert a b e = vert a}
    (fun e => (B.chordArc vert P g e).initialDirection) (.inr true) (.inl (B.map.rot a)))
  (hb : CcwSuccessor {e | B.chordVert vert a b e = vert b}
    (fun e => (B.chordArc vert P g e).initialDirection) (.inl b) (.inr false))
  (hgb : CcwSuccessor {e | B.chordVert vert a b e = vert b}
    (fun e => (B.chordArc vert P g e).initialDirection) (.inr false) (.inl (B.map.rot b)))
  (harg_a : (P.arc a).initialDirection.arg ≠ g.initialDirection.arg)
  (harg_b : (P.arc b).initialDirection.arg ≠ g.reverse.initialDirection.arg)

/-- Helper toward Proposition 5.16: insert a simple chord disjoint from the
old drawing except at its two distinct endpoint vertices. The four local
successor hypotheses specify the two split corners in the augmented
direction family; the argument inequalities exclude coincident boundary
rays, including when an old star is a singleton. -/
@[expose] def insertChordDrawing :
    PLDrawing (B.D ⊕ Bool) V B.chordEdgeInv
      (B.chordRotation a b (B.chord_corners_ne vert a b hvab))
      (B.chordVert vert a b) := by
  have hab := B.chord_corners_ne vert a b hvab
  have hlen : 2 ≤ g.points.length := Polyline.length_two_of_start_ne_finish g (by
    rw [hstart, hfinish]
    exact fun h => hvab (P.pos_injective h))
  have hta : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection :=
    chord_strict_turn_of_successors
      (dir := fun e : B.D ⊕ Bool => (B.chordArc vert P g e).initialDirection)
      (a := .inl a) (r := .inl (B.map.rot a)) (n := .inr true)
      (by simp) (by simp) ha hga harg_a
  have htb : ccwTurn (P.arc b).initialDirection g.reverse.initialDirection <
      ccwTurn (P.arc b).initialDirection (P.arc (B.map.rot b)).initialDirection :=
    chord_strict_turn_of_successors
      (dir := fun e : B.D ⊕ Bool => (B.chordArc vert P g e).initialDirection)
      (a := .inl b) (r := .inl (B.map.rot b)) (n := .inr false)
      (by simp) (by simp) hb hgb harg_b
  exact {
    flip_involutive := (B.chordMap a b hab).edgeInv_invol
    flip_ne := B.chordEdgeInv_ne
    vert_rotation := B.chordVert_rotation vert P a b hab
    pos := P.pos
    pos_injective := P.pos_injective
    arc := B.chordArc vert P g
    arc_simple := B.chordArc_simple vert P g hg
    arc_length := B.chordArc_length vert P g hlen
    arc_start := B.chordArc_start vert P a b g hstart hfinish
    arc_finish := B.chordArc_finish vert P a b g hstart hfinish
    arc_flip := B.chordArc_flip vert P g
    interior_disjoint := B.chordArc_interior_disjoint vert P g hdis
    interior_avoids_vertices := B.chordArc_interior_avoids_vertices vert P g hdis
    locally_finite := B.chordArc_locally_finite vert P g
    initial_nonzero := B.chordArc_initial_nonzero vert P g hg hlen
    initial_arg_injective := B.chordArc_initial_arg_injective vert P a b hvab g hta htb
    rotation_agreement := by
      intro d
      cases d with
      | inl d =>
        by_cases hda : d = a
        · subst d
          simpa only [chordRotation_a, chordVert] using ha
        · by_cases hdb : d = b
          · subst d
            simpa only [chordRotation_b, chordVert] using hb
          · exact B.chordArc_rotation_other vert P a b d hab g hta htb hda hdb
      | inr t =>
        cases t
        · simpa only [chordRotation_false, chordVert] using hgb
        · simpa only [chordRotation_true, chordVert] using hga
  }

/-- Helper toward Proposition 5.16: the inserted drawing leaves every
vertex position unchanged. -/
@[simp] theorem insertChordDrawing_pos (v : V) :
    (B.insertChordDrawing vert P a b hvab g hg hstart hfinish hdis
      ha hga hb hgb harg_a harg_b).pos v = P.pos v := rfl

/-- Helper toward Proposition 5.16: the inserted drawing leaves every old
arc unchanged, with its original dart identity. -/
@[simp] theorem insertChordDrawing_arc_inl (d : B.D) :
    (B.insertChordDrawing vert P a b hvab g hg hstart hfinish hdis
      ha hga hb hgb harg_a harg_b).arc (.inl d) = P.arc d := rfl

/-- Helper toward Proposition 5.16: the positive new dart traces the chord. -/
@[simp] theorem insertChordDrawing_arc_true :
    (B.insertChordDrawing vert P a b hvab g hg hstart hfinish hdis
      ha hga hb hgb harg_a harg_b).arc (.inr true) = g := rfl

/-- Helper toward Proposition 5.16: the negative new dart traces the reverse chord. -/
@[simp] theorem insertChordDrawing_arc_false :
    (B.insertChordDrawing vert P a b hvab g hg hstart hfinish hdis
      ha hga hb hgb harg_a harg_b).arc (.inr false) = g.reverse := rfl

/-- Helper toward Proposition 5.16: insertion adds exactly the closed chord
to the image of the drawing. -/
theorem insertChordDrawing_image :
    (B.insertChordDrawing vert P a b hvab g hg hstart hfinish hdis
      ha hga hb hgb harg_a harg_b).image = P.image ∪ g.image :=
  B.chordArc_image vert P g

end Drawing

end D39FiniteBall
end DirectedDistances.PlanarMap
