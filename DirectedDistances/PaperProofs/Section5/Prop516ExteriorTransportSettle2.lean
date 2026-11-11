/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorTransportSettle
public import DirectedDistances.PaperProofs.Section5.Prop516ReverseComparison2
public import DirectedDistances.PaperProofs.Section5.Prop516StageSampleRotationField
public import DirectedDistances.PlanarMap.BoundEdgesDefinition32Sides

/-! # Restricted exterior selectors for the digon test

Helpers toward Proposition 5.16 and Definition 3.8
remain with the sole coordinator. No numbered result is claimed. -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.SourceResults
open DirectedDistances.PaperProofs.Section3

private theorem drawing_eq_of_pos_arc
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P Q : PLDrawing D V flip rot vert)
    (hp : P.pos = Q.pos) (ha : P.arc = Q.arc) : P = Q := by
  cases P
  cases Q
  cases hp
  cases ha
  rfl

/-- Helper toward Proposition 5.16: identify the restricted ambient
digon's vertex carrier with its two Boolean endpoint identities. -/
@[expose] def exteriorTestDigonRestrictedVertexEquiv
    (P : PLDrawing exteriorTestDigon.core.D
      (RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot)
      exteriorTestDigon.core.edgeInv exteriorTestDigon.core.rot
      (d39VertexClass exteriorTestDigon)) :
    RestrictedVertex P (d39BallDarts exteriorTestDigon 1 : Set exteriorTestDigon.core.D) ≃
      Bool where
  toFun v := exteriorTestDigonVertexEquiv v.val
  invFun b := ⟨d39VertexClass exteriorTestDigon (false, b),
    (false, b), exteriorTestDigon_all_darts_retained _, rfl⟩
  left_inv v := Subtype.ext (exteriorTestDigonVertexEquiv.left_inv v.val)
  right_inv _ := rfl

/-- Helper toward Proposition 5.16: place any Boolean digon drawing on
the exact quotient vertex carrier of the ambient rooted map. -/
@[expose] def exteriorTestDigonAmbientRelabel
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    PLDrawing exteriorTestDigon.core.D
      (RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot)
      exteriorTestDigon.core.edgeInv exteriorTestDigon.core.rot
      (d39VertexClass exteriorTestDigon) :=
  plDrawingRelabel (Equiv.refl (Bool × Bool))
    exteriorTestDigonVertexEquiv.symm (fun _ => rfl) (fun _ => rfl)
    (fun d => (exteriorTestDigon_vertex_class d.1 d.2).symm) R

/-- Helper toward Proposition 5.16: restricting an ambient digon
drawing obtained by relabelling a Boolean drawing and then forgetting
the retained-dart subtype recovers that Boolean drawing exactly. -/
theorem exteriorTestDigon_restricted_relabel_eq
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    let P := exteriorTestDigonAmbientRelabel R
    plDrawingRelabel exteriorTestDigonBallIsoRaw.toEquiv
      (exteriorTestDigonRestrictedVertexEquiv P)
      exteriorTestDigonBallIsoRaw.edgeInv_comm exteriorTestDigonBallIsoRaw.rot_comm
      (fun _ => rfl) (d39FacedBallPLDrawing exteriorTestDigon P 1 (by decide)) = R := by
  dsimp only
  apply drawing_eq_of_pos_arc
  · funext b
    rfl
  · funext d
    rfl

/-- Helper toward Proposition 5.16: the actual restricted ambient
selector transports to the Boolean drawing's selector. This supplies the
selector identification missing from the preceding digon test. -/
theorem exteriorTestDigon_restricted_external_transport
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    let P := exteriorTestDigonAmbientRelabel R
    plBallFaceOrbitMap exteriorTestDigonBallIsoRaw
        (d39FacedBallPLWithExternal exteriorTestDigon P 1 (by decide)).externalOrbit =
      plExternalOrbit (exteriorTestDigonRawBall false) Prod.snd R
        (fun b => ⟨(false, b), rfl⟩) exteriorTestDigon_eqvGen_connected := by
  dsimp only
  let P := exteriorTestDigonAmbientRelabel R
  let := d39FacedBallPLDrawing_finite_vertices exteriorTestDigon P 1 (by decide)
  have h := plDrawingRelabel_selected_external_transport exteriorTestDigonBallIsoRaw
    (restrictedVertex P (d39BallDarts exteriorTestDigon 1 : Set exteriorTestDigon.core.D))
    Prod.snd (d39FacedBallPLDrawing exteriorTestDigon P 1 (by decide))
    (exteriorTestDigonRestrictedVertexEquiv P) (fun _ => rfl)
    (d39FacedBallPLDrawing_vertex_surjective exteriorTestDigon P 1 (by decide))
    (fun b => ⟨(false, b), rfl⟩)
    (d39FacedBall_connected exteriorTestDigon 1 (by decide))
    exteriorTestDigon_eqvGen_connected
  rw [exteriorTestDigon_restricted_relabel_eq R] at h
  exact h

/-- Helper toward Proposition 5.16: the actual restricted exterior
selector on a Boolean digon drawing, with its ball carrier fixed explicitly. -/
@[expose] def exteriorTestDigonSelectedExternalOrbit
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    D39BallFaceCycleOrbit (d39FacedBall exteriorTestDigon 1 (by decide)) :=
  (d39FacedBallPLWithExternal exteriorTestDigon
    (exteriorTestDigonAmbientRelabel R) 1 (by decide)).externalOrbit

/-- Helper toward Proposition 5.16: the two constructed ambient digon
drawings select different exterior orbits after actual ball restriction.
This concerns the precise selector used by the representation interface. -/
theorem exteriorTestDigon_ambient_restrictions_distinct_externalOrbits :
    exteriorTestDigonSelectedExternalOrbit exteriorTestDigonDrawing ≠
      exteriorTestDigonSelectedExternalOrbit exteriorTestDigonSwappedDrawing := by
  intro h
  apply exteriorTestDigon_same_raw_ball_distinct_externalOrbits
  exact (exteriorTestDigon_restricted_external_transport exteriorTestDigonDrawing).symm.trans
    ((congrArg (plBallFaceOrbitMap exteriorTestDigonBallIsoRaw) h).trans
      (exteriorTestDigon_restricted_external_transport exteriorTestDigonSwappedDrawing))

/-- Helper toward Proposition 5.16: retain the two parallel geometric
edge identities of any Boolean digon drawing in the general plane carrier. -/
@[expose] def exteriorTestDigonPlaneDrawing
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    PlaneGraphDrawing Bool Bool where
  src _ := false
  tgt _ := true
  pos := R.pos
  pos_injective := R.pos_injective
  arc e := (R.arc (e, false)).toPath.cast
    (R.arc_start (e, false)).symm (R.arc_finish (e, false)).symm
  arc_injOn e := (R.arc (e, false)).toPath_injOn
    (R.arc_length _) (R.arc_simple _)
  openArc_disjoint := by
    intro e f hef
    change Disjoint ((R.arc (e, false)).toPath '' openParams)
      ((R.arc (f, false)).toPath '' openParams)
    rw [Polyline.toPath_image_openParams _ (R.arc_length _) (R.arc_simple _),
      Polyline.toPath_image_openParams _ (R.arc_length _) (R.arc_simple _)]
    apply R.interior_disjoint
    · exact fun h => hef (congrArg Prod.fst h).symm
    · exact fun h => hef (congrArg Prod.fst h).symm
  openArc_avoids := by
    intro e v
    change R.pos v ∉ (R.arc (e, false)).toPath '' openParams
    rw [Polyline.toPath_image_openParams _ (R.arc_length _) (R.arc_simple _)]
    exact R.interior_avoids_vertices _ _

/-- Helper toward Proposition 5.16: the edge-identity drawing traces
the exact same plane subset as its four-dart PL drawing. -/
theorem exteriorTestDigonPlaneDrawing_image
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    (exteriorTestDigonPlaneDrawing R).image = R.image := by
  have harc (e : Bool) :
      Set.range ((exteriorTestDigonPlaneDrawing R).arc e) = (R.arc (e, false)).image :=
    Polyline.range_toPath _
  ext z
  change (z ∈ Set.range R.pos ∨ z ∈ ⋃ e, Set.range
    ((exteriorTestDigonPlaneDrawing R).arc e)) ↔
      z ∈ Set.range R.pos ∨ ∃ d, z ∈ (R.arc d).image
  simp only [Set.mem_iUnion, harc]
  constructor
  · rintro (h | ⟨e, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(e, false), he⟩
  · rintro (h | ⟨⟨e, b⟩, he⟩)
    · exact Or.inl h
    · right
      refine ⟨e, ?_⟩
      cases b
      · exact he
      · have hi := R.arc_image_flip (e, false)
        exact hi ▸ he

/-- Helper toward Proposition 5.16: the all-present digon directed
plane map orients both individual edges from the first endpoint to the second. -/
@[expose] def exteriorTestDigonDirectedPlaneMap
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    DirectedPlaneMapWithMissing Bool Bool where
  toPlaneGraphDrawing := exteriorTestDigonPlaneDrawing R
  missing _ := False
  missing_on_external := fun _ h => h.elim
  forward _ := true

/-- Helper toward Proposition 5.16: the geometric directed digon
satisfies the connected, locally finite, valid-root domain requirements. -/
theorem exteriorTestDigonDirectedPlaneMap_domain
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    D39GeomDomain (exteriorTestDigonDirectedPlaneMap R) (false, true) := by
  refine ⟨?_, fun _ => Set.toFinite _, Or.inr ⟨fun h => h, rfl⟩⟩
  have hadj : (d39GeomGraph (exteriorTestDigonDirectedPlaneMap R)).Adj false true :=
    ⟨by decide, false, Or.inl ⟨rfl, rfl⟩⟩
  intro v w
  cases v <;> cases w
  · exact .refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact .refl _

/-- Helper toward Proposition 5.16: the concrete rooted domain map
for either Boolean digon drawing, with both geometric edges present. -/
@[expose] def exteriorTestDigonDomainRootedMap
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    D39DomainRootedMapV2 :=
  ⟨Bool, Bool, exteriorTestDigonDirectedPlaneMap R, (false, true),
    exteriorTestDigonDirectedPlaneMap_domain R⟩

/-- Helper toward Proposition 5.16: the geometric edge drawing and
the dart drawing have exactly the same complementary face sets. -/
@[expose] def exteriorTestDigonPlaneFaceEquiv
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    (exteriorTestDigonPlaneDrawing R).Face ≃ R.Face where
  toFun F := ⟨F.val, by
    rw [← exteriorTestDigonPlaneDrawing_image R]
    exact F.property⟩
  invFun F := ⟨F.val, by
    rw [exteriorTestDigonPlaneDrawing_image R]
    exact F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Helper toward Proposition 5.16: the full base drawing
representation of the rooted digon, including its actual geometric faces
and all left/right side clauses. -/
@[expose] def exteriorTestDigonBaseRepresentation
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd) :
    D39DrawingRepresentationData exteriorTestDigon (exteriorTestDigonDomainRootedMap R) := by
  let A := exteriorTestDigonRawBall false
  let hv : Function.Surjective (Prod.snd : Bool × Bool → Bool) :=
    fun b => ⟨(false, b), rfl⟩
  let face := A.plDartFace Prod.snd R hv
  let E := exteriorTestDigonPlaneFaceEquiv R
  refine
    { vertexEquiv := exteriorTestDigonVertexEquiv
      positions_injective := R.pos_injective
      dartEquiv := exteriorTestDigonFlip
      dart_tail_vertex := ?_
      dart_head_vertex := ?_
      dart_edgeInv := ?_
      dart_missing := fun _ => Iff.rfl
      dart_orientation := ?_
      root_mark := rfl
      faceOfDart := fun d => E.symm (face d)
      faceOrbit_iff := ?_
      face_surjective := ?_
      face_left_of_dart := ?_ }
  · rintro ⟨a, b⟩
    cases b <;> rfl
  · rintro ⟨a, b⟩
    cases b <;> rfl
  · rintro ⟨a, b⟩
    cases b <;> rfl
  · rintro ⟨a, b⟩ _
    change b = false ↔ true = !b
    cases b <;> decide
  · intro d e
    constructor
    · intro h
      exact A.plDartFace_sameCycle_of_eq Prod.snd R hv exteriorTestDigon_eqvGen_connected
        d e (E.symm.injective h)
    · intro h
      exact congrArg E.symm (A.plDartFace_eq_of_sameCycle Prod.snd R hv d e h)
  · intro F
    obtain ⟨d, hd⟩ := A.plDartFace_surjective Prod.snd R hv (E F)
    exact ⟨d, (congrArg E.symm hd).trans (E.symm_apply_apply F)⟩
  · rintro ⟨a, b⟩
    have hborder := (A.plDartFace_eq_iff Prod.snd R hv (a, b) (face (a, b))).mp rfl
    cases b
    · exact fun s => R.dartBorders_toPath_leftAtOn hv (a, false) _ hborder s
    · exact fun s => R.dartBorders_flip_toPath_rightAtOn hv (a, false) _ hborder s

/-- Helper toward Proposition 5.16: the base representation's face
assignment has precisely the required vertex/frontier incidence, for both
the bounded and the unbounded digon face. -/
theorem exteriorTestDigonBaseRepresentation_vertex_frontier_incidence
    (R : PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd)
    (d : exteriorTestDigon.core.D)
    (v : RootedLocallyFiniteVertex exteriorTestDigon.core.D exteriorTestDigon.core.rot) :
    (exteriorTestDigonDomainRootedMap R).map.toPlaneMapWithMissing.pos
        ((exteriorTestDigonBaseRepresentation R).vertexEquiv v) ∈
      frontier ((exteriorTestDigonBaseRepresentation R).faceOfDart d).val ↔
    ∃ e, Equiv.Perm.SameCycle
        (exteriorTestDigon.core.rot.symm * exteriorTestDigon.core.edgeInv) d e ∧
      rootedLocallyFiniteVertexClass exteriorTestDigon.core.rot e = v := by
  let A := exteriorTestDigonRawBall false
  let hv : Function.Surjective (Prod.snd : Bool × Bool → Bool) :=
    fun b => ⟨(false, b), rfl⟩
  let F := A.plDartFace Prod.snd R hv d
  have hborder := (A.plDartFace_eq_iff Prod.snd R hv d F).mp rfl
  have hfront := R.dartBorders_arc_subset_frontier hv d F hborder
  have hstart : R.pos d.2 ∈ frontier F.val :=
    hfront ((R.arc_start d) ▸ (Or.inl rfl))
  have hfinish : R.pos (!d.2) ∈ frontier F.val := by
    change R.pos (exteriorTestDigonFlip d).2 ∈ frontier F.val
    rw [← R.arc_finish d]
    apply hfront
    rw [← Polyline.range_toPath]
    exact ⟨1, (R.arc d).toPath.target⟩
  have hvertex : ∀ b : Bool, R.pos b ∈ frontier F.val := by
    intro b
    cases hb : d.2 <;> cases b
    · simpa only [hb] using hstart
    · simpa only [hb, Bool.not_false] using hfinish
    · simpa only [hb, Bool.not_true] using hfinish
    · simpa only [hb] using hstart
  have hrhs : ∃ e, Equiv.Perm.SameCycle
        (exteriorTestDigon.core.rot.symm * exteriorTestDigon.core.edgeInv) d e ∧
      rootedLocallyFiniteVertexClass exteriorTestDigon.core.rot e = v := by
    obtain ⟨⟨a, b⟩, rfl⟩ := Quotient.exists_rep v
    by_cases hb : d.2 = b
    · exact ⟨d, Equiv.Perm.SameCycle.rfl,
        (exteriorTestDigon_vertex_class d.1 d.2).trans
          (hb ▸ (exteriorTestDigon_vertex_class a b).symm)⟩
    · let e := (exteriorTestDigon.core.rot.symm * exteriorTestDigon.core.edgeInv) d
      have he : e.2 = b := by
        obtain ⟨c, f⟩ := d
        cases f <;> cases b <;> first | rfl | exact (hb rfl).elim
      exact ⟨e, (Equiv.Perm.SameCycle.refl _ d).apply_right,
        (exteriorTestDigon_vertex_class e.1 e.2).trans
          (he ▸ (exteriorTestDigon_vertex_class a b).symm)⟩
  exact ⟨fun _ => hrhs, fun _ => hvertex (exteriorTestDigonVertexEquiv v)⟩

/-- Helper toward Proposition 5.16: reversing the three-point digon
polyline reverses its actual parameterized path, since both segments use
one half of the unit interval. -/
theorem exteriorTestDigonPolyline_reverse_toPath (s : ℝ) (t : unitInterval) :
    (exteriorTestDigonPolyline s).reverse.toPath t =
      (exteriorTestDigonPolyline s).toPath.symm t := by
  have hr : (exteriorTestDigonPolyline s).reverse =
      (⟨[2, 1 + (s : ℂ) * Complex.I, 0], by simp⟩ : Polyline) := rfl
  rw [hr]
  change ((Path.segment (2 : ℂ) (1 + (s : ℂ) * Complex.I)).trans
    (Path.segment (1 + (s : ℂ) * Complex.I) 0)) t =
    ((Path.segment (0 : ℂ) (1 + (s : ℂ) * Complex.I)).trans
      (Path.segment (1 + (s : ℂ) * Complex.I) 2)).symm t
  rw [Path.trans_symm, Path.segment_symm, Path.segment_symm]

/-- Helper toward Proposition 5.16: the two concrete PL digon drawings,
indexed without identifying their geometric edge labels. -/
@[expose] def exteriorTestDigonChosenDrawing (swapped : Bool) :
    PLDrawing (Bool × Bool) Bool exteriorTestDigonFlip exteriorTestDigonRot Prod.snd :=
  if swapped then exteriorTestDigonSwappedDrawing else exteriorTestDigonDrawing

/-- Helper toward Proposition 5.16: the base representation stores
exactly the ordered paths of each concrete digon drawing. -/
theorem exteriorTestDigonChosenDrawing_arc_eq (swapped : Bool)
    (d : Bool × Bool) (t : unitInterval) :
    ((exteriorTestDigonChosenDrawing swapped).arc d).toPath t =
      d39DrawingDartArc
        (exteriorTestDigonDomainRootedMap (exteriorTestDigonChosenDrawing swapped))
        (exteriorTestDigonBaseRepresentation (exteriorTestDigonChosenDrawing swapped)) d t := by
  obtain ⟨a, b⟩ := d
  cases swapped <;> cases b
  · rfl
  · exact exteriorTestDigonPolyline_reverse_toPath (if a then -1 else 1) t
  · rfl
  · exact exteriorTestDigonPolyline_reverse_toPath (if !a then -1 else 1) t

/-- Helper toward Proposition 5.16: both concrete digon drawings have
full v3 representations, with topological rotation and frontier incidence
proved from their actual polylines and complementary face assignments. -/
@[expose] def exteriorTestDigonRepresentation (swapped : Bool) :
    PLCylinderBall.Representation exteriorTestDigon
      (exteriorTestDigonDomainRootedMap (exteriorTestDigonChosenDrawing swapped)) := by
  let R := exteriorTestDigonChosenDrawing swapped
  let base := exteriorTestDigonBaseRepresentation R
  have harc := exteriorTestDigonChosenDrawing_arc_eq swapped
  refine
    { data :=
        { toD39DrawingRepresentationData := base
          rotation_topological_successor := ?_
          vertex_frontier_incidence := exteriorTestDigonBaseRepresentation_vertex_frontier_incidence R }
      drawing := exteriorTestDigonAmbientRelabel R
      pos_eq := fun _ => rfl
      arc_eq := harc }
  intro d
  have hstar :
      {e | rootedLocallyFiniteVertexClass exteriorTestDigon.core.rot e =
        rootedLocallyFiniteVertexClass exteriorTestDigon.core.rot d} =
      {e : Bool × Bool | e.2 = d.2} := by
    ext e
    constructor
    · intro h
      exact congrArg exteriorTestDigonVertexEquiv h
    · intro h
      exact exteriorTestDigonVertexEquiv.injective h
  have hpaths : d39DrawingDartArc (exteriorTestDigonDomainRootedMap R) base =
      fun e t => (R.arc e).toPath t := by
    funext e t
    exact (harc e t).symm
  rw [hstar, hpaths]
  exact plDrawing_toPath_rotation_topological_ccwSuccessor R d

/-- Helper toward Proposition 5.16: expose the exact ambient PL drawing
of each constructed representation without unfolding its proof fields. -/
theorem exteriorTestDigonRepresentation_drawing (swapped : Bool) :
    (exteriorTestDigonRepresentation swapped).drawing =
      exteriorTestDigonAmbientRelabel (exteriorTestDigonChosenDrawing swapped) := rfl

/-- Helper toward Proposition 5.16: the selected orbit of the actual
restriction of a constructed full representation. -/
@[expose] def exteriorTestDigonRepresentationExternalOrbit (swapped : Bool) :
    D39BallFaceCycleOrbit (d39FacedBall exteriorTestDigon 1 (by decide)) :=
  (d39FacedBallPLWithExternal exteriorTestDigon
    (exteriorTestDigonRepresentation swapped).drawing 1 (by decide)).externalOrbit

/-- Helper toward Proposition 5.16: the fully represented digon
exteriors disagree after the actual radius-one restriction. -/
theorem exteriorTestDigonRepresentation_distinct_externalOrbits :
    exteriorTestDigonRepresentationExternalOrbit false ≠
      exteriorTestDigonRepresentationExternalOrbit true := by
  have heq (swapped : Bool) : exteriorTestDigonRepresentationExternalOrbit swapped =
      exteriorTestDigonSelectedExternalOrbit (exteriorTestDigonChosenDrawing swapped) := by
    unfold exteriorTestDigonRepresentationExternalOrbit
    rw [exteriorTestDigonRepresentation_drawing]
    rfl
  rw [heq, heq]
  exact exteriorTestDigon_ambient_restrictions_distinct_externalOrbits

/-- Helper toward Proposition 5.16: an actual represented positive-radius
ball isomorphism need not transport the geometrically selected exterior.
Both witnesses are finite all-present acyclic digons. -/
theorem exists_represented_ballIso_without_external_transport :
    ∃ (M N : D39RootedMap) (B C : D39DomainRootedMapV2.{0})
      (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
      (r : ℕ) (hr : 0 < r)
      (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)),
      plBallFaceOrbitMap I
          (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit ≠
        (d39FacedBallPLWithExternal N y.drawing r hr).externalOrbit := by
  refine ⟨exteriorTestDigon, exteriorTestDigon,
    exteriorTestDigonDomainRootedMap (exteriorTestDigonChosenDrawing false),
    exteriorTestDigonDomainRootedMap (exteriorTestDigonChosenDrawing true),
    exteriorTestDigonRepresentation false, exteriorTestDigonRepresentation true,
    1, by decide, D39BallIso.refl (d39FacedBall exteriorTestDigon 1 (by decide)), ?_⟩
  change plBallFaceOrbitMap
      (D39BallIso.refl (d39FacedBall exteriorTestDigon 1 (by decide)))
      (exteriorTestDigonRepresentationExternalOrbit false) ≠
    exteriorTestDigonRepresentationExternalOrbit true
  rw [plBallFaceOrbitMap_refl]
  exact exteriorTestDigonRepresentation_distinct_externalOrbits

/-- Helper toward Proposition 5.16: the equivalence relation on finite
faced balls which also preserves one explicitly recorded exterior orbit.
This is a strengthened candidate class, not a replacement for the existing -/
@[expose] def exteriorMarkedBallSetoid : Setoid D39FiniteBallWithExternal where
  r A B := Nonempty (D39BallIsoWithExternal A B)
  iseqv :=
    ⟨fun A => ⟨D39BallIsoWithExternal.refl A⟩,
      fun ⟨I⟩ => ⟨I.symm⟩,
      fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩⟩

/-- Helper toward Proposition 5.16: faced-ball isomorphism classes
which record the selected exterior orbit as part of their finite data. -/
@[expose] def ExteriorMarkedBallClass : Type 1 := Quotient exteriorMarkedBallSetoid

/-- Helper toward Proposition 5.16: the strengthened class of the actual
PL restriction, with its unique geometrically unbounded orbit recorded. -/
@[expose] def representedExteriorMarkedBallClass
    {M : D39RootedMap} {B : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (r : ℕ) (hr : 0 < r) :
    ExteriorMarkedBallClass :=
  Quotient.mk exteriorMarkedBallSetoid (d39FacedBallPLWithExternal M x.drawing r hr)

/-- Helper toward Proposition 5.16: equality of the strengthened
classes is exactly existence of an isomorphism retaining all faced-ball
data and the geometrically selected exterior orbit. -/
theorem representedExteriorMarkedBallClass_eq_iff
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r) :
    representedExteriorMarkedBallClass x r hr = representedExteriorMarkedBallClass y r hr ↔
      Nonempty (D39BallIsoWithExternal
        (d39FacedBallPLWithExternal M x.drawing r hr)
        (d39FacedBallPLWithExternal N y.drawing r hr)) :=
  Quotient.eq

/-- Helper toward Proposition 5.16: the strengthened ball-class equality
has the reverse plane comparison, with no remaining exterior-transport
input. This concerns restricted orbit faces, not the still-separate
identification with retained ambient faces. -/
theorem exists_represented_plane_homeomorph_of_exteriorMarkedBallClass_eq
    {M N : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation N C)
    (r : ℕ) (hr : 0 < r)
    (h : representedExteriorMarkedBallClass x r hr = representedExteriorMarkedBallClass y r hr) :
    ∃ (I : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr))
      (H : ℂ ≃ₜ ℂ), OrientationPreserving H ∧
      (∀ d : (d39FacedBall M r hr).D,
        H (B.map.toPlaneMapWithMissing.pos (x.data.vertexEquiv (d39VertexClass M d.1))) =
          C.map.toPlaneMapWithMissing.pos
            (y.data.vertexEquiv (d39VertexClass N (I.toEquiv d).1))) ∧
      (∀ d : (d39FacedBall M r hr).D,
        ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧
          ∀ t, H (d39DrawingDartArc B x.data.toD39DrawingRepresentationData d.1 t) =
            d39DrawingDartArc C y.data.toD39DrawingRepresentationData
              (I.toEquiv d).1 (φ t)) ∧
      (∀ O : D39BallFaceCycleOrbit (d39FacedBall M r hr),
        H '' ((d39FacedBall M r hr).plOrbitFace
          (restrictedVertex x.drawing (d39BallDarts M r : Set M.core.D))
          (d39FacedBallPLDrawing M x.drawing r hr)
          (d39FacedBallPLDrawing_vertex_surjective M x.drawing r hr) O).val =
          ((d39FacedBall N r hr).plOrbitFace
            (restrictedVertex y.drawing (d39BallDarts N r : Set N.core.D))
            (d39FacedBallPLDrawing N y.drawing r hr)
            (d39FacedBallPLDrawing_vertex_surjective N y.drawing r hr)
            (plBallFaceOrbitMap I O)).val) := by
  obtain ⟨I⟩ := (representedExteriorMarkedBallClass_eq_iff x y r hr).mp h
  refine ⟨I.toD39BallIso, ?_⟩
  exact ReverseComparison2.exists_represented_plane_homeomorph_of_external_transport
    x y r hr I.toD39BallIso
    ((plBallFaceOrbitMap_eq_iff I.toD39BallIso _ _).mpr I.external_iff)

/-- Helper toward Proposition 5.16: for two representations of the same
rooted map, equality of the strengthened classes is precisely equality of
their selected exterior orbits, because rooted actual-ball isomorphisms
are unique. -/
theorem representedExteriorMarkedBallClass_self_eq_iff
    {M : D39RootedMap} {B C : D39DomainRootedMapV2}
    (x : PLCylinderBall.Representation M B) (y : PLCylinderBall.Representation M C)
    (r : ℕ) (hr : 0 < r) :
    representedExteriorMarkedBallClass x r hr = representedExteriorMarkedBallClass y r hr ↔
      (d39FacedBallPLWithExternal M x.drawing r hr).externalOrbit =
        (d39FacedBallPLWithExternal M y.drawing r hr).externalOrbit := by
  exact (representedExteriorMarkedBallClass_eq_iff x y r hr).trans
    (d39FacedBall_external_lift_iff M r hr _ _)

/-- Helper toward Proposition 5.16: the two fully represented digons
have distinct exterior-marked ball classes, despite having the same
underlying combinatorial rooted map and hence identical unmarked balls. -/
theorem exteriorTestDigonRepresentation_marked_classes_ne :
    representedExteriorMarkedBallClass (exteriorTestDigonRepresentation false) 1 (by decide) ≠
      representedExteriorMarkedBallClass (exteriorTestDigonRepresentation true) 1 (by decide) := by
  intro h
  have heq := (representedExteriorMarkedBallClass_self_eq_iff
    (exteriorTestDigonRepresentation false) (exteriorTestDigonRepresentation true)
    1 (by decide)).mp h
  exact exteriorTestDigonRepresentation_distinct_externalOrbits heq












































end DirectedDistances.PaperProofs.Section5

end
