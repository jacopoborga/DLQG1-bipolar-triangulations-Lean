/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PLCornerSector
public import DirectedDistances.PlanarMap.D39BallOrbitComponents12

/-! # Inserting a pendant edge in a finite plane drawing

The two new dart identities are `Sum.inr true` at the attachment vertex and -/

public section
noncomputable section

namespace DirectedDistances.PlanarMap
namespace D39FiniteBall

open Set

/-- Helper toward Proposition 5.16: reversal on the augmented dart carrier. -/
@[expose] def pendantFlip (B : D39FiniteBall) : B.D ⊕ Bool → B.D ⊕ Bool
  | .inl d => .inl (B.map.edgeInv d)
  | .inr t => .inr (!t)

/-- Helper toward Proposition 5.16: augmented reversal is involutive. -/
theorem pendantFlip_involutive (B : D39FiniteBall) :
    Function.Involutive B.pendantFlip := by
  rintro (d | t)
  · exact congrArg Sum.inl (B.map.edgeInv_invol d)
  · cases t <;> rfl

/-- Helper toward Proposition 5.16: augmented reversal fixes no dart. -/
theorem pendantFlip_ne (B : D39FiniteBall) (d : B.D ⊕ Bool) :
    B.pendantFlip d ≠ d := by
  cases d with
  | inl d => exact fun h => B.map.edgeInv_ne d (Sum.inl.inj h)
  | inr t => cases t <;> simp [pendantFlip]

/-- Helper toward Proposition 5.16: insert the departing new dart after `a`. -/
@[expose] def pendantRotFun (B : D39FiniteBall) (a : B.D) : B.D ⊕ Bool → B.D ⊕ Bool
  | .inl d => if d = a then .inr true else .inl (B.map.rot d)
  | .inr true => .inl (B.map.rot a)
  | .inr false => .inr false

/-- Helper toward Proposition 5.16: inverse of the pendant rotation. -/
@[expose] def pendantRotInv (B : D39FiniteBall) (a : B.D) : B.D ⊕ Bool → B.D ⊕ Bool
  | .inl d => if d = B.map.rot a then .inr true else .inl (B.map.rot.symm d)
  | .inr true => .inl a
  | .inr false => .inr false

/-- Helper toward Proposition 5.16: the pendant rotation is a permutation. -/
@[expose] def pendantRotation (B : D39FiniteBall) (a : B.D) : Equiv.Perm (B.D ⊕ Bool) where
  toFun := B.pendantRotFun a
  invFun := B.pendantRotInv a
  left_inv := by
    rintro (d | t)
    · by_cases h : d = a
      · subst d; simp [pendantRotFun, pendantRotInv]
      · have h' : B.map.rot d ≠ B.map.rot a := fun he => h (B.map.rot.injective he)
        simp [pendantRotFun, pendantRotInv, h, h']
    · cases t <;> simp [pendantRotFun, pendantRotInv]
  right_inv := by
    rintro (d | t)
    · by_cases h : d = B.map.rot a
      · subst d; simp [pendantRotFun, pendantRotInv]
      · have h' : B.map.rot.symm d ≠ a := by
          intro he
          apply h
          rw [← he, Equiv.apply_symm_apply]
        simp [pendantRotFun, pendantRotInv, h, h']
    · cases t <;> simp [pendantRotFun, pendantRotInv]

/-- Helper toward Proposition 5.16: the map retaining all old edges and adding one edge. -/
@[expose] def pendantMap (B : D39FiniteBall) (a : B.D) : CombinatorialMap (B.D ⊕ Bool) where
  edgeInv := ⟨B.pendantFlip, B.pendantFlip,
    B.pendantFlip_involutive, B.pendantFlip_involutive⟩
  edgeInv_invol := B.pendantFlip_involutive
  edgeInv_ne := B.pendantFlip_ne
  rot := B.pendantRotation a

/-- Helper toward Proposition 5.16: the augmented finite ball, with both new darts
present and unmarked as tails, and with the original root retained. -/
@[expose] def insertPendant (B : D39FiniteBall) (a : B.D) : D39FiniteBall where
  D := B.D ⊕ Bool
  map := B.pendantMap a
  missing := Sum.elim B.missing (fun _ => False)
  tail := Sum.elim B.tail (fun _ => False)
  rootDart := .inl B.rootDart
  original := Set.univ
  original_closed := by simp

/-- Helper toward Proposition 5.16: insertion preserves the root dart identity. -/
@[simp] theorem insertPendant_rootDart (B : D39FiniteBall) (a : B.D) :
    (B.insertPendant a).rootDart = Sum.inl B.rootDart := rfl

/-- Helper toward Proposition 5.16: insertion retains old missing-edge tags. -/
@[simp] theorem insertPendant_missing_inl (B : D39FiniteBall) (a d : B.D) :
    (B.insertPendant a).missing (.inl d) ↔ B.missing d := Iff.rfl

/-- Helper toward Proposition 5.16: insertion retains old tail tags. -/
@[simp] theorem insertPendant_tail_inl (B : D39FiniteBall) (a d : B.D) :
    (B.insertPendant a).tail (.inl d) ↔ B.tail d := Iff.rfl

/-- Helper toward Proposition 5.16: neither new dart is missing. -/
@[simp] theorem insertPendant_not_missing_inr (B : D39FiniteBall) (a : B.D) (t : Bool) :
    ¬ (B.insertPendant a).missing (.inr t) := id

/-- Helper toward Proposition 5.16: neither new dart carries a tail tag. -/
@[simp] theorem insertPendant_not_tail_inr (B : D39FiniteBall) (a : B.D) (t : Bool) :
    ¬ (B.insertPendant a).tail (.inr t) := id

/-- Helper toward Proposition 5.16: the augmented original incidence set is universal. -/
@[simp] theorem insertPendant_original (B : D39FiniteBall) (a : B.D) :
    (B.insertPendant a).original = Set.univ := rfl

/-- Helper toward Proposition 5.16: old edge reversal is unchanged. -/
@[simp] theorem pendantMap_edgeInv_inl (B : D39FiniteBall) (a d : B.D) :
    (B.pendantMap a).edgeInv (.inl d) = .inl (B.map.edgeInv d) := rfl

/-- Helper toward Proposition 5.16: the new darts reverse each other. -/
@[simp] theorem pendantMap_edgeInv_inr (B : D39FiniteBall) (a : B.D) (t : Bool) :
    (B.pendantMap a).edgeInv (.inr t) = .inr (!t) := rfl

/-- Helper toward Proposition 5.16: the new outgoing dart follows the attachment dart. -/
@[simp] theorem pendantRotation_attachment (B : D39FiniteBall) (a : B.D) :
    B.pendantRotation a (.inl a) = .inr true := by
  simp [pendantRotation, pendantRotFun]

/-- Helper toward Proposition 5.16: the new outgoing dart precedes the old successor. -/
@[simp] theorem pendantRotation_true (B : D39FiniteBall) (a : B.D) :
    B.pendantRotation a (.inr true) = .inl (B.map.rot a) := rfl

/-- Helper toward Proposition 5.16: the leaf vertex has a singleton rotation. -/
@[simp] theorem pendantRotation_false (B : D39FiniteBall) (a : B.D) :
    B.pendantRotation a (.inr false) = .inr false := rfl

/-- Helper toward Proposition 5.16: rotation at every other old dart is unchanged. -/
theorem pendantRotation_inl_of_ne (B : D39FiniteBall) (a d : B.D) (h : d ≠ a) :
    B.pendantRotation a (.inl d) = .inl (B.map.rot d) := by
  simp [pendantRotation, pendantRotFun, h]

/-- Helper toward Proposition 5.16: old vertices embed into `Option V`, with `none`
representing the new leaf vertex. -/
@[expose] def pendantVert {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (a : B.D) : B.D ⊕ Bool → Option V
  | .inl d => some (vert d)
  | .inr true => some (vert a)
  | .inr false => none

/-- Helper toward Proposition 5.16: the augmented vertex map is surjective. -/
theorem pendantVert_surjective {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (a : B.D) (hvert : Function.Surjective vert) :
    Function.Surjective (B.pendantVert vert a) := by
  rintro (_ | v)
  · exact ⟨.inr false, rfl⟩
  · obtain ⟨d, rfl⟩ := hvert v
    exact ⟨.inl d, rfl⟩

/-- Helper toward Proposition 5.16: the augmented rotation preserves its vertex. -/
theorem pendantVert_rotation {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a : B.D)
    (d : B.D ⊕ Bool) :
    B.pendantVert vert a (B.pendantRotation a d) = B.pendantVert vert a d := by
  cases d with
  | inl d =>
    by_cases h : d = a
    · subst d; simp [pendantRotation, pendantRotFun, pendantVert]
    · simp [pendantRotation, pendantRotFun, pendantVert, h, P.vert_rotation]
  | inr t => cases t <;> simp [pendantRotation, pendantRotFun, pendantVert, P.vert_rotation]

/-- Helper toward Proposition 5.16: augmented positions keep old positions. -/
@[expose] def pendantPos {V : Type*} (pos : V → ℂ) (c : ℂ) : Option V → ℂ
  | some v => pos v
  | none => c

/-- Helper toward Proposition 5.16: augmented arcs keep all old arcs. -/
@[expose] def pendantArc {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline) : B.D ⊕ Bool → Polyline
  | .inl d => P.arc d
  | .inr true => g
  | .inr false => g.reverse

/-- Helper toward Proposition 5.16: the new vertex has exactly one outgoing dart. -/
theorem pendantVert_none_iff {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (a : B.D) (d : B.D ⊕ Bool) : B.pendantVert vert a d = none ↔ d = .inr false := by
  cases d with
  | inl d => simp [pendantVert]
  | inr t => cases t <;> simp [pendantVert]

/-- Helper toward Proposition 5.16: the singleton leaf satisfies counterclockwise rotation. -/
theorem pendant_leaf_rotation_agreement {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (a : B.D) (dir : B.D ⊕ Bool → ℂ) :
    CcwSuccessor {e | B.pendantVert vert a e = B.pendantVert vert a (.inr false)}
      dir (.inr false) (B.pendantRotation a (.inr false)) := by
  have hstar : {e | B.pendantVert vert a e = B.pendantVert vert a (.inr false)} =
      {Sum.inr false} := by
    ext e
    exact B.pendantVert_none_iff vert a e
  rw [hstar, pendantRotation_false]
  exact ⟨Set.finite_singleton _, Set.mem_singleton _, Set.mem_singleton _, Or.inl ⟨rfl, rfl⟩⟩

/-- Helper toward Proposition 5.16: adjoining a point outside the old drawing
preserves injectivity of positions. -/
theorem pendantPos_injective {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (c : ℂ) (hc : c ∉ P.image) :
    Function.Injective (pendantPos P.pos c) := by
  have hcv (v : V) : c ≠ P.pos v := by
    intro h
    exact hc (Or.inl ⟨v, h.symm⟩)
  rintro (_ | v) (_ | w) h
  · rfl
  · exact (hcv w h).elim
  · exact (hcv v h.symm).elim
  · exact congrArg some (P.pos_injective h)

/-- Helper toward Proposition 5.16: a polyline with different endpoints has
at least two points. -/
theorem pendant_length_of_endpoints_ne (g : Polyline) (hne : g.start ≠ g.finish) :
    2 ≤ g.points.length := by
  rcases g with ⟨l, hl⟩
  cases l with
  | nil => exact (hl rfl).elim
  | cons x l =>
    cases l with
    | nil => exact (hne rfl).elim
    | cons y l => simp

/-- Helper toward Proposition 5.16: a simple polyline of length at least two
has a nonzero initial direction. -/
theorem pendant_initialDirection_ne (g : Polyline) (hg : g.IsSimple)
    (hlen : 2 ≤ g.points.length) : g.initialDirection ≠ 0 := by
  intro h
  have heq : g.point 1 = g.start := sub_eq_zero.mp h
  exact hg.1 0 (by omega) (g.point_zero_eq_start.trans heq.symm)

/-- Helper toward Proposition 5.16: the new arc has distinct endpoints. -/
theorem pendant_endpoints_ne {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a : B.D)
    (c : ℂ) (hc : c ∉ P.image) (g : Polyline)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = c) : g.start ≠ g.finish := by
  intro h
  exact hc (Or.inl ⟨vert a, hs.symm.trans (h.trans hf)⟩)

/-- Helper toward Proposition 5.16: simplicity of every augmented arc. -/
theorem pendantArc_simple {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline)
    (hg : g.IsSimple) (d : B.D ⊕ Bool) : (B.pendantArc vert P g d).IsSimple := by
  cases d with
  | inl d => exact P.arc_simple d
  | inr t => cases t; exact Polyline.isSimple_reverse_transfer g hg; exact hg

/-- Helper toward Proposition 5.16: lengths of the augmented arcs. -/
theorem pendantArc_length {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline)
    (hlen : 2 ≤ g.points.length) (d : B.D ⊕ Bool) :
    2 ≤ (B.pendantArc vert P g d).points.length := by
  cases d with
  | inl d => exact P.arc_length d
  | inr t => cases t <;> simpa [pendantArc, Polyline.reverse] using hlen

/-- Helper toward Proposition 5.16: starting points of the augmented arcs. -/
theorem pendantArc_start {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a : B.D)
    (c : ℂ) (g : Polyline) (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (d : B.D ⊕ Bool) :
    (B.pendantArc vert P g d).start = pendantPos P.pos c (B.pendantVert vert a d) := by
  cases d with
  | inl d => exact P.arc_start d
  | inr t => cases t <;> simp [pendantArc, pendantVert, pendantPos, hs, hf]

/-- Helper toward Proposition 5.16: finishing points of the augmented arcs. -/
theorem pendantArc_finish {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a : B.D)
    (c : ℂ) (g : Polyline) (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (d : B.D ⊕ Bool) : (B.pendantArc vert P g d).finish =
    pendantPos P.pos c (B.pendantVert vert a (B.pendantFlip d)) := by
  cases d with
  | inl d => exact P.arc_finish d
  | inr t => cases t <;> simp [pendantArc, pendantVert, pendantPos, pendantFlip, hs, hf]

/-- Helper toward Proposition 5.16: reversal of augmented arcs. -/
theorem pendantArc_flip {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline)
    (d : B.D ⊕ Bool) : B.pendantArc vert P g (B.pendantFlip d) =
      (B.pendantArc vert P g d).reverse := by
  cases d with
  | inl d => exact P.arc_flip d
  | inr t => cases t <;> simp [pendantArc, pendantFlip]

/-- Helper toward Proposition 5.16: distinct augmented edges have disjoint interiors. -/
theorem pendantArc_interior_disjoint {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline)
    (hdis : Disjoint g.interior P.image) (d e : B.D ⊕ Bool)
    (hne : e ≠ d) (hflip : e ≠ B.pendantFlip d) :
    Disjoint (B.pendantArc vert P g d).interior (B.pendantArc vert P g e).interior := by
  have hsub (d : B.D) : (P.arc d).interior ⊆ P.image :=
    fun _ hz => Or.inr ⟨d, hz.1⟩
  cases d with
  | inl d =>
    cases e with
    | inl e =>
      exact P.interior_disjoint d e
        (fun h => hne (congrArg Sum.inl h)) (fun h => hflip (congrArg Sum.inl h))
    | inr t => cases t <;>
        simpa only [pendantArc, Polyline.interior_reverse_transfer] using
          (hdis.mono_right (hsub d)).symm
  | inr t =>
    cases e with
    | inl e => cases t <;>
        simpa only [pendantArc, Polyline.interior_reverse_transfer] using
          hdis.mono_right (hsub e)
    | inr u => cases t <;> cases u <;> simp_all [pendantFlip]

/-- Helper toward Proposition 5.16: augmented arc interiors avoid every vertex,
including the new endpoint. -/
theorem pendantArc_interior_avoids_vertices {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (c : ℂ) (hc : c ∉ P.image) (g : Polyline) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image) (d : B.D ⊕ Bool) (v : Option V) :
    pendantPos P.pos c v ∉ (B.pendantArc vert P g d).interior := by
  have hnew : c ∉ g.interior := by
    intro hz
    exact hz.2 (Or.inr hf.symm)
  have hold (v : V) : P.pos v ∉ g.interior := by
    intro hz
    exact Set.disjoint_left.mp hdis hz (Or.inl ⟨v, rfl⟩)
  cases d with
  | inl d =>
    cases v with
    | none => exact fun hz => hc (Or.inr ⟨d, hz.1⟩)
    | some v => exact P.interior_avoids_vertices d v
  | inr t => cases t <;> cases v <;>
      simpa only [pendantPos, pendantArc, Polyline.interior_reverse_transfer] using
        (by first | exact hnew | exact hold _)

/-- Helper toward Proposition 5.16: every augmented arc has nonzero initial direction. -/
theorem pendantArc_initial_nonzero {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline)
    (hg : g.IsSimple) (hlen : 2 ≤ g.points.length) (d : B.D ⊕ Bool) :
    (B.pendantArc vert P g d).initialDirection ≠ 0 := by
  cases d with
  | inl d => exact P.initial_nonzero d
  | inr t =>
    cases t
    · exact pendant_initialDirection_ne g.reverse (Polyline.isSimple_reverse_transfer g hg)
        (by simpa only [Polyline.reverse, List.length_reverse] using hlen)
    · exact pendant_initialDirection_ne g hg hlen

/-- Helper toward Proposition 5.16: the augmented drawing data have exactly the
union of the old drawing image and the inserted arc image. -/
theorem pendant_image {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (c : ℂ)
    (g : Polyline) (hf : g.finish = c) :
    Set.range (pendantPos P.pos c) ∪ {z | ∃ d, z ∈ (B.pendantArc vert P g d).image} =
      P.image ∪ g.image := by
  have hc : c ∈ g.image := by
    rw [← hf, ← Polyline.start_reverse, ← Polyline.image_reverse_transfer g]
    exact Or.inl rfl
  ext z
  constructor
  · rintro (⟨(_ | v), rfl⟩ | ⟨(d | t), hz⟩)
    · exact Or.inr hc
    · exact Or.inl (Or.inl ⟨v, rfl⟩)
    · exact Or.inl (Or.inr ⟨d, hz⟩)
    · cases t <;> exact Or.inr (by simpa [pendantArc, Polyline.image_reverse_transfer] using hz)
  · rintro ((⟨v, rfl⟩ | ⟨d, hz⟩) | hz)
    · exact Or.inl ⟨some v, rfl⟩
    · exact Or.inr ⟨.inl d, hz⟩
    · exact Or.inr ⟨.inr true, hz⟩

/-- Helper toward Proposition 5.16: a direction in the open attachment sector
has argument different from every old outgoing direction. The full-turn
convention includes an attachment vertex with a singleton star. -/
theorem pendant_arg_ne {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (a : B.D) (g : Polyline)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (d : B.D) (hv : vert d = vert a) :
    Complex.arg g.initialDirection ≠ Complex.arg (P.arc d).initialDirection := by
  intro heq
  have hturn : ccwTurn (P.arc a).initialDirection g.initialDirection =
      ccwTurn (P.arc a).initialDirection (P.arc d).initialDirection := by
    simp only [ccwTurn, heq]
  rw [hturn] at hslot
  by_cases hd : d = a
  · subst d
    rw [(ccwTurn_eq_two_pi_iff _ _).mpr rfl] at hslot
    exact (not_lt_of_ge (ccwTurn_le_two_pi _ _)) hslot
  · rcases P.rotation_agreement a with ⟨_, _, _, hsingle | hmin⟩
    · exact hd (Set.mem_singleton_iff.mp (hsingle.2 ▸ hv))
    · exact (not_lt_of_ge (hmin.2 d hv hd)) hslot

/-- Helper toward Proposition 5.16: outgoing augmented directions have distinct arguments. -/
theorem pendantArc_initial_arg_injective {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (g : Polyline)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (d e : B.D ⊕ Bool) (hv : B.pendantVert vert a d = B.pendantVert vert a e)
    (heq : Complex.arg (B.pendantArc vert P g d).initialDirection =
      Complex.arg (B.pendantArc vert P g e).initialDirection) : d = e := by
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (P.initial_arg_injective d e (Option.some.inj hv) heq)
    | inr t =>
      cases t
      · simp [pendantVert] at hv
      · exact (B.pendant_arg_ne vert P a g hslot d (Option.some.inj hv) heq.symm).elim
  | inr t =>
    cases e with
    | inl e =>
      cases t
      · simp [pendantVert] at hv
      · exact (B.pendant_arg_ne vert P a g hslot e (Option.some.inj hv).symm heq).elim
    | inr u => cases t <;> cases u <;> simp_all [pendantVert]

/-- Helper toward Proposition 5.16: transport an old vertex successor to
the old dart identities inside the augmented carrier. -/
theorem pendant_old_successor {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (g : Polyline) (d : B.D) :
    CcwSuccessor (Sum.inl '' {e | vert e = vert d})
      (fun e => (B.pendantArc vert P g e).initialDirection)
      (.inl d) (.inl (B.map.rot d)) := by
  rcases P.rotation_agreement d with ⟨_, _, hr, hsingle | hmin⟩
  · refine ⟨Set.toFinite _, ⟨d, rfl, rfl⟩, ⟨_, hr, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · exact congrArg Sum.inl hsingle.1
    · rw [hsingle.2, Set.image_singleton]
  · refine ⟨Set.toFinite _, ⟨d, rfl, rfl⟩, ⟨_, hr, rfl⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact fun h => hmin.1 (Sum.inl.inj h)
    · rintro _ ⟨e, he, rfl⟩ hne
      exact hmin.2 e he (fun h => hne (congrArg Sum.inl h))

/-- Helper toward Proposition 5.16: the attachment star is the old star
with precisely the new outgoing dart inserted. -/
theorem pendant_attachment_star {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (a : B.D) :
    {e | B.pendantVert vert a e = some (vert a)} =
      insert (.inr true) (Sum.inl '' {e | vert e = vert a}) := by
  ext e
  cases e with
  | inl e => simp [pendantVert]
  | inr t => cases t <;> simp [pendantVert]

/-- Helper toward Proposition 5.16: the direction hypothesis splits the old
corner into the two successive augmented corners. -/
theorem pendant_attachment_successors {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (g : Polyline)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection) :
    CcwSuccessor {e | B.pendantVert vert a e = some (vert a)}
      (fun e => (B.pendantArc vert P g e).initialDirection) (.inl a) (.inr true) ∧
    CcwSuccessor {e | B.pendantVert vert a e = some (vert a)}
      (fun e => (B.pendantArc vert P g e).initialDirection) (.inr true) (.inl (B.map.rot a)) := by
  have hfirst : CcwSuccessor {e | B.pendantVert vert a e = some (vert a)}
      (fun e => (B.pendantArc vert P g e).initialDirection) (.inl a) (.inr true) := by
    refine ⟨Set.toFinite _, rfl, rfl, Or.inr ⟨by simp, ?_⟩⟩
    intro e he hne
    cases e with
    | inr t => cases t; simp [pendantVert] at he; exact le_rfl
    | inl e =>
      have hev : vert e = vert a := Option.some.inj he
      have hea : e ≠ a := fun h => hne (congrArg Sum.inl h)
      rcases P.rotation_agreement a with ⟨_, _, _, hsingle | hmin⟩
      · exact (hea (Set.mem_singleton_iff.mp (hsingle.2 ▸ hev))).elim
      · exact hslot.le.trans (hmin.2 e hev hea)
  refine ⟨hfirst, ?_⟩
  rw [B.pendant_attachment_star vert a]
  apply ccwSuccessor_insert_next (Sum.inl '' {e | vert e = vert a})
    (fun e => (B.pendantArc vert P g e).initialDirection)
    (.inl a) (.inl (B.map.rot a)) (.inr true)
    (Set.toFinite _)
  · intro p hp q hq hpq heq
    have hpv : B.pendantVert vert a p = some (vert a) := by
      change p ∈ {e | B.pendantVert vert a e = some (vert a)}
      rw [B.pendant_attachment_star vert a]; exact hp
    have hqv : B.pendantVert vert a q = some (vert a) := by
      change q ∈ {e | B.pendantVert vert a e = some (vert a)}
      rw [B.pendant_attachment_star vert a]; exact hq
    exact hpq (B.pendantArc_initial_arg_injective vert P a g hslot p q
      (hpv.trans hqv.symm) heq)
  · exact B.pendant_old_successor vert P g a
  · simp
  · exact hslot

/-- Helper toward Proposition 5.16: distinct directions give a unique
predecessor as well as a unique successor in a finite star. -/
theorem pendant_ccw_predecessor_unique {D : Type*} (star : Set D) (dir : D → ℂ)
    (a d n : D)
    (hargs : ∀ p ∈ star, ∀ q ∈ star,
      Complex.arg (dir p) = Complex.arg (dir q) → p = q)
    (ha : CcwSuccessor star dir a n) (hd : CcwSuccessor star dir d n) : a = d := by
  rcases ha with ⟨_, ha, hn, hsingle | hmin⟩
  · exact (Set.mem_singleton_iff.mp (hsingle.2 ▸ hd.2.1)).symm
  · rcases hd with ⟨_, hd, _, hsingle | hmin'⟩
    · exact Set.mem_singleton_iff.mp (hsingle.2 ▸ ha)
    · by_contra had
      have hle := hmin.2 d hd (Ne.symm had)
      have hne : ccwTurn (dir a) (dir n) ≠ ccwTurn (dir a) (dir d) := by
        intro h
        exact hmin'.1 (hargs n hn d hd (ccwTurn_left_injective h))
      have hlt := lt_of_le_of_ne hle hne
      have hc := ccwTurn_comp_add hlt
      have hnd : Complex.arg (dir n) ≠ Complex.arg (dir d) :=
        fun h => hmin'.1 (hargs n hn d hd h)
      have hadarg : Complex.arg (dir a) ≠ Complex.arg (dir d) :=
        fun h => had (hargs a ha d hd h)
      have hr1 := ccwTurn_add_reverse (dir n) (dir d) hnd
      have hr2 := ccwTurn_add_reverse (dir a) (dir d) hadarg
      have hle' := hmin'.2 a ha had
      linarith [ccwTurn_pos (dir a) (dir n)]

/-- Helper toward Proposition 5.16: once the inserted dart follows `a`,
every other old successor survives insertion. -/
theorem pendant_ccw_insert_preserve {D : Type*} (star : Set D) (dir : D → ℂ)
    (a d e x : D) (ha : a ∈ star) (hdne : d ≠ a) (hx : x ∉ star)
    (hargs : ∀ p ∈ insert x star, ∀ q ∈ insert x star,
      Complex.arg (dir p) = Complex.arg (dir q) → p = q)
    (hold : CcwSuccessor star dir d e) (hnew : CcwSuccessor (insert x star) dir a x) :
    CcwSuccessor (insert x star) dir d e := by
  rcases hold with ⟨hfin, hd, he, hsingle | hmin⟩
  · exact (hdne (Set.mem_singleton_iff.mp (hsingle.2 ▸ ha)).symm).elim
  · refine ⟨hfin.insert x, Set.mem_insert_of_mem _ hd, Set.mem_insert_of_mem _ he,
      Or.inr ⟨hmin.1, ?_⟩⟩
    intro f hf hfd
    rcases Set.mem_insert_iff.mp hf with hfx | hf
    · subst f
      by_contra hle
      have hlt := lt_of_not_ge hle
      have hxd : x ≠ d := fun h => hx (h.symm ▸ hd)
      have hdx : CcwSuccessor (insert x star) dir d x := by
        refine ⟨hfin.insert x, Set.mem_insert_of_mem _ hd, Set.mem_insert _ _,
          Or.inr ⟨hxd, ?_⟩⟩
        intro f hf hfd
        rcases Set.mem_insert_iff.mp hf with hfx | hf
        · subst f; exact le_rfl
        · exact hlt.le.trans (hmin.2 f hf hfd)
      exact hdne (pendant_ccw_predecessor_unique _ _ a d x hargs hnew hdx).symm
    · exact hmin.2 f hf hfd

/-- Helper toward Proposition 5.16: rotation agreement at every augmented dart. -/
theorem pendant_rotation_agreement {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (g : Polyline)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection)
    (d : B.D ⊕ Bool) :
    CcwSuccessor {e | B.pendantVert vert a e = B.pendantVert vert a d}
      (fun e => (B.pendantArc vert P g e).initialDirection) d (B.pendantRotation a d) := by
  obtain ⟨ha, hn⟩ := B.pendant_attachment_successors vert P a g hslot
  cases d with
  | inr t =>
    cases t
    · exact B.pendant_leaf_rotation_agreement vert a _
    · exact hn
  | inl d =>
    by_cases hda : d = a
    · subst d
      simpa only [pendantRotation_attachment, pendantVert] using ha
    rw [B.pendantRotation_inl_of_ne a d hda]
    by_cases hv : vert d = vert a
    · change CcwSuccessor {e | B.pendantVert vert a e = some (vert d)} _ _ _
      rw [hv, B.pendant_attachment_star vert a]
      apply pendant_ccw_insert_preserve (Sum.inl '' {e | vert e = vert a})
        (fun e => (B.pendantArc vert P g e).initialDirection)
        (.inl a) (.inl d) (.inl (B.map.rot d)) (.inr true)
      · exact ⟨a, rfl, rfl⟩
      · exact fun h => hda (Sum.inl.inj h)
      · simp
      · intro p hp q hq heq
        have hpv : B.pendantVert vert a p = some (vert a) := by
          change p ∈ {e | B.pendantVert vert a e = some (vert a)}
          rw [B.pendant_attachment_star vert a]; exact hp
        have hqv : B.pendantVert vert a q = some (vert a) := by
          change q ∈ {e | B.pendantVert vert a e = some (vert a)}
          rw [B.pendant_attachment_star vert a]; exact hq
        exact B.pendantArc_initial_arg_injective vert P a g hslot p q
          (hpv.trans hqv.symm) heq
      · simpa only [hv] using B.pendant_old_successor vert P g d
      · rwa [B.pendant_attachment_star vert a] at ha
    · have hstar : {e | B.pendantVert vert a e = B.pendantVert vert a (.inl d)} =
          Sum.inl '' {e | vert e = vert d} := by
        ext e
        cases e with
        | inl e => simp [pendantVert]
        | inr t => cases t <;> simp [pendantVert, Ne.symm hv]
      rw [hstar]
      exact B.pendant_old_successor vert P g d

/-- Helper toward Proposition 5.16: the pendant-edge PL drawing. The strict
counterclockwise sector hypothesis also handles a singleton old star. -/
@[expose] def insertPendantDrawing {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (c : ℂ) (hc : c ∉ P.image) (g : Polyline) (hg : g.IsSimple)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection) :
    PLDrawing (B.D ⊕ Bool) (Option V) (B.pendantMap a).edgeInv
      (B.pendantRotation a) (B.pendantVert vert a) where
  flip_involutive := B.pendantFlip_involutive
  flip_ne := B.pendantFlip_ne
  vert_rotation := B.pendantVert_rotation vert P a
  pos := pendantPos P.pos c
  pos_injective := B.pendantPos_injective vert P c hc
  arc := B.pendantArc vert P g
  arc_simple := B.pendantArc_simple vert P g hg
  arc_length := B.pendantArc_length vert P g
    (pendant_length_of_endpoints_ne g (B.pendant_endpoints_ne vert P a c hc g hs hf))
  arc_start := B.pendantArc_start vert P a c g hs hf
  arc_finish := B.pendantArc_finish vert P a c g hs hf
  arc_flip := B.pendantArc_flip vert P g
  interior_disjoint := B.pendantArc_interior_disjoint vert P g hdis
  interior_avoids_vertices := B.pendantArc_interior_avoids_vertices vert P c hc g hf hdis
  locally_finite := fun _ _ => Set.toFinite _
  initial_nonzero := B.pendantArc_initial_nonzero vert P g hg
    (pendant_length_of_endpoints_ne g (B.pendant_endpoints_ne vert P a c hc g hs hf))
  initial_arg_injective := B.pendantArc_initial_arg_injective vert P a g hslot
  rotation_agreement := B.pendant_rotation_agreement vert P a g hslot

/-- Helper toward Proposition 5.16: the strict sector condition is equivalent
to the augmented successor condition with strict separation from the old
successor direction. The separation clause excludes ties permitted by the
bare `CcwSuccessor` predicate. -/
theorem pendant_slot_iff_ccwSuccessor {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (g : Polyline) :
    ccwTurn (P.arc a).initialDirection g.initialDirection <
        ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection ↔
      CcwSuccessor {e | B.pendantVert vert a e = some (vert a)}
        (fun e => (B.pendantArc vert P g e).initialDirection) (.inl a) (.inr true) ∧
      Complex.arg g.initialDirection ≠ Complex.arg (P.arc (B.map.rot a)).initialDirection := by
  constructor
  · intro hslot
    exact ⟨(B.pendant_attachment_successors vert P a g hslot).1,
      B.pendant_arg_ne vert P a g hslot (B.map.rot a) (P.vert_rotation a)⟩
  · rintro ⟨hnext, hne⟩
    have hle : ccwTurn (P.arc a).initialDirection g.initialDirection ≤
        ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection := by
      by_cases hrot : B.map.rot a = a
      · rw [hrot, (ccwTurn_eq_two_pi_iff _ _).mpr rfl]
        exact ccwTurn_le_two_pi _ _
      · rcases hnext.2.2.2 with hsingle | hmin
        · cases hsingle.1
        · exact hmin.2 (.inl (B.map.rot a)) (congrArg some (P.vert_rotation a))
            (fun h => hrot (Sum.inl.inj h))
    exact lt_of_le_of_ne hle (fun h => hne (ccwTurn_left_injective h))

/-- Helper toward Proposition 5.16: pendant insertion with its direction
hypothesis stated on the augmented direction family using `CcwSuccessor`. -/
@[expose] def insertPendantDrawingOfCcwSuccessor {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (c : ℂ) (hc : c ∉ P.image) (g : Polyline) (hg : g.IsSimple)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image)
    (hnext : CcwSuccessor {e | B.pendantVert vert a e = some (vert a)}
      (fun e => (B.pendantArc vert P g e).initialDirection) (.inl a) (.inr true))
    (hne : Complex.arg g.initialDirection ≠
      Complex.arg (P.arc (B.map.rot a)).initialDirection) :
    PLDrawing (B.insertPendant a).D (Option V) (B.insertPendant a).map.edgeInv
      (B.insertPendant a).map.rot (B.pendantVert vert a) :=
  B.insertPendantDrawing vert P a c hc g hg hs hf hdis
    ((B.pendant_slot_iff_ccwSuccessor vert P a g).mpr ⟨hnext, hne⟩)

/-- Helper toward Proposition 5.16: insertion leaves every old position and
every old dart arc unchanged, and places the new vertex at the supplied point. -/
theorem insertPendantDrawing_retains_data {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (c : ℂ) (hc : c ∉ P.image) (g : Polyline) (hg : g.IsSimple)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection) :
    let Q := B.insertPendantDrawing vert P a c hc g hg hs hf hdis hslot
    (∀ v, Q.pos (some v) = P.pos v) ∧ Q.pos none = c ∧
      (∀ d, Q.arc (.inl d) = P.arc d) ∧
      Q.arc (.inr true) = g ∧ Q.arc (.inr false) = g.reverse :=
  ⟨fun _ => rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- Helper toward Proposition 5.16: the completed pendant drawing has exactly
the old drawing image union the inserted polyline image. -/
theorem insertPendantDrawing_image {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (a : B.D) (c : ℂ) (hc : c ∉ P.image) (g : Polyline) (hg : g.IsSimple)
    (hs : g.start = P.pos (vert a)) (hf : g.finish = c)
    (hdis : Disjoint g.interior P.image)
    (hslot : ccwTurn (P.arc a).initialDirection g.initialDirection <
      ccwTurn (P.arc a).initialDirection (P.arc (B.map.rot a)).initialDirection) :
    (B.insertPendantDrawing vert P a c hc g hg hs hf hdis hslot).image = P.image ∪ g.image :=
  B.pendant_image vert P c g hf

end D39FiniteBall
end DirectedDistances.PlanarMap
end
