module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.Connected.Basic
public import DirectedDistances.KMSW.LimitExternalFace

/-! # Piecewise linear plane drawings

Helpers toward adjudication n308, with source convention
connected component. No existence, uniqueness or boundary classification theorem for
the KMSW limit is proved here. Geometric edges include missing edges and retain their
identities; reversing a dart reverses its arc. -/

public section
namespace DirectedDistances.PlanarMap

noncomputable section




structure Polyline where
  points : List ℂ
  nonempty : points ≠ []

namespace Polyline



@[expose] def start (p : Polyline) : ℂ := p.points.head p.nonempty



@[expose] def finish (p : Polyline) : ℂ := p.points.getLast p.nonempty




@[expose] def point (p : Polyline) (i : ℕ) : ℂ := p.points[i]?.getD p.start



@[expose] def segmentAt (p : Polyline) (i : ℕ) : Set ℂ :=
  segment ℝ (p.point i) (p.point (i + 1))




@[expose] def image (p : Polyline) : Set ℂ :=
  {p.start} ∪ {z | ∃ i, i + 1 < p.points.length ∧ z ∈ p.segmentAt i}




@[expose] def initialDirection (p : Polyline) : ℂ := p.point 1 - p.start



@[expose] def reverse (p : Polyline) : Polyline :=
  ⟨p.points.reverse, List.reverse_ne_nil_iff.mpr p.nonempty⟩





@[expose] def IsSimple (p : Polyline) : Prop :=
  (∀ i, i + 1 < p.points.length → p.point i ≠ p.point (i + 1)) ∧
    (∀ i, i + 2 < p.points.length →
      p.segmentAt i ∩ p.segmentAt (i + 1) = {p.point (i + 1)}) ∧
    (∀ i j, i + 1 < p.points.length → j + 1 < p.points.length → i + 1 < j →
      Disjoint (p.segmentAt i) (p.segmentAt j))



@[expose] def interior (p : Polyline) : Set ℂ := p.image \ {p.start, p.finish}



@[simp] theorem reverse_reverse (p : Polyline) : p.reverse.reverse = p := by
  cases p
  simp only [reverse, List.reverse_reverse]



@[simp] theorem start_reverse (p : Polyline) : p.reverse.start = p.finish := by
  exact List.head_reverse _



@[simp] theorem finish_reverse (p : Polyline) : p.reverse.finish = p.start := by
  exact List.getLast_reverse _

end Polyline





@[expose] def ccwTurn (a b : ℂ) : ℝ :=
  if Complex.arg a < Complex.arg b then Complex.arg b - Complex.arg a
  else Complex.arg b - Complex.arg a + 2 * Real.pi






@[expose] def CcwSuccessor {D : Type*} (star : Set D) (dir : D → ℂ) (d e : D) : Prop :=
  star.Finite ∧ d ∈ star ∧ e ∈ star ∧
    ((e = d ∧ star = {d}) ∨
      (e ≠ d ∧ ∀ f ∈ star, f ≠ d → ccwTurn (dir d) (dir e) ≤ ccwTurn (dir d) (dir f)))








structure PLDrawing (D V : Type*) (flip : D → D) (rot : Equiv.Perm D) (vert : D → V) where
  flip_involutive : Function.Involutive flip
  flip_ne : ∀ d, flip d ≠ d
  vert_rotation : ∀ d, vert (rot d) = vert d
  pos : V → ℂ
  pos_injective : Function.Injective pos
  arc : D → Polyline
  arc_simple : ∀ d, (arc d).IsSimple
  arc_length : ∀ d, 2 ≤ (arc d).points.length
  arc_start : ∀ d, (arc d).start = pos (vert d)
  arc_finish : ∀ d, (arc d).finish = pos (vert (flip d))
  arc_flip : ∀ d, arc (flip d) = (arc d).reverse
  interior_disjoint : ∀ d e, e ≠ d → e ≠ flip d →
    Disjoint (arc d).interior (arc e).interior
  interior_avoids_vertices : ∀ d v, pos v ∉ (arc d).interior
  locally_finite : ∀ K : Set ℂ, Bornology.IsBounded K →
    {d | (K ∩ (arc d).image).Nonempty}.Finite
  initial_nonzero : ∀ d, (arc d).initialDirection ≠ 0
  initial_arg_injective : ∀ d e, vert d = vert e →
    Complex.arg (arc d).initialDirection = Complex.arg (arc e).initialDirection → d = e
  rotation_agreement : ∀ d,
    CcwSuccessor {e | vert e = vert d} (fun e => (arc e).initialDirection) d (rot d)

namespace PLDrawing

variable {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
variable (P : PLDrawing D V flip rot vert)



@[expose] def image : Set ℂ := Set.range P.pos ∪ {z | ∃ d, z ∈ (P.arc d).image}





@[expose] def Face :=
  {F : Set ℂ // ∃ z, z ∉ P.image ∧ F = connectedComponentIn P.imageᶜ z}



@[expose] def IsUnbounded (F : P.Face) : Prop :=
  ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖







@[expose] def dartBorders (d : D) (F : P.Face) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ t ε : ℝ, 0 < t → t < δ → 0 < ε → ε < δ →
    (P.arc d).start + (t : ℂ) *
      ((P.arc d).initialDirection + (ε : ℂ) * Complex.I * (P.arc d).initialDirection)
        ∈ F.val



theorem arc_flip_flip (d : D) : P.arc (flip (flip d)) = P.arc d := by
  rw [P.flip_involutive d]



theorem initialDirection_ne {d e : D} (hv : vert d = vert e) (hne : d ≠ e) :
    (P.arc d).initialDirection ≠ (P.arc e).initialDirection := by
  intro h
  exact hne (P.initial_arg_injective d e hv (congrArg Complex.arg h))



theorem face_subset_compl (F : P.Face) : F.val ⊆ P.imageᶜ := by
  obtain ⟨z, _, hF⟩ := F.property
  rw [hF]
  exact connectedComponentIn_subset _ _



theorem faces_cover_compl (z : ℂ) : (∃ F : P.Face, z ∈ F.val) ↔ z ∉ P.image := by
  constructor
  · rintro ⟨F, hz⟩
    exact P.face_subset_compl F hz
  · intro hz
    exact ⟨⟨connectedComponentIn P.imageᶜ z, z, hz, rfl⟩, mem_connectedComponentIn hz⟩



theorem faces_eq_of_mem {F G : P.Face} {z : ℂ} (hF : z ∈ F.val) (hG : z ∈ G.val) :
    F = G := by
  apply Subtype.ext
  obtain ⟨x, _, hx⟩ := F.property
  obtain ⟨y, _, hy⟩ := G.property
  rw [hx] at hF
  rw [hy] at hG
  exact hx.trans ((connectedComponentIn_eq hF).trans
    ((connectedComponentIn_eq hG).symm.trans hy.symm))



theorem faces_disjoint {F G : P.Face} (h : F ≠ G) : Disjoint F.val G.val := by
  apply Set.disjoint_left.mpr
  intro z hzF hzG
  exact h (P.faces_eq_of_mem hzF hzG)

end PLDrawing

open DirectedDistances.KMSW DirectedDistances.RandomWalk Filter




@[expose] def kmswLimitDartVertex (w : ℕ → Fin 3) (d : ℕ × Bool) : ℕ :=
  if d.2 then edgeEast w d.1 else edgeWest w d.1







@[expose] def KMSWLimitPlaneRealizationStatement (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_htrans : Tendsto (L w) atTop atTop) (_hR : ∀ a : ℤ, ∃ n, R w n ≤ a)
    (_hL0 : ∀ j, 0 ≤ L w j) : Prop :=
  let Drawing := PLDrawing (ℕ × Bool) ℕ (fun d => (d.1, !d.2))
    (kmswInfRot w hfin) (kmswLimitDartVertex w)
  Nonempty Drawing ∧ ∀ P : Drawing, ∃ U : P.Face,
    P.IsUnbounded U ∧ (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ limitExternalDart w d

end
end DirectedDistances.PlanarMap
