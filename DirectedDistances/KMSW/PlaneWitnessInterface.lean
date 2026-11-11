module

public import DirectedDistances.PlanarMap.PlaneRealization
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMap
public import DirectedDistances.KMSW.InfiniteRotation
public import DirectedDistances.KMSW.KMSWFutureMapCarrier

/-! Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface); -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. The edge reversal on the KMSW dart carrier. Source: -/
@[expose] def kmswFlip : Equiv.Perm (ℕ × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv := by rintro ⟨e, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e, b⟩; cases b <;> rfl

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. Its underlying function swaps the two darts of each edge. -/
theorem kmswFlip_apply : ⇑kmswFlip = fun d => (d.1, !d.2) := rfl

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. A geometric drawing with its distinguished unbounded face and -/
structure OuterWitness {D : Type} (rot flip faceSucc : Equiv.Perm D) (o : D) where
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface); -/
  V : Type
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  vert : D → V
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  P : PLDrawing D V ⇑flip rot vert
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Geometric vertices agree with rotation orbits. Source: -/
  vert_iff : ∀ d e, vert d = vert e ↔ rot.SameCycle d e
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Every geometric vertex is represented by a dart. Source: -/
  vert_surj : ∀ v : V, ∃ d, vert d = v
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Face successor is inverse rotation after edge flip. Source: -/
  faceSucc_eq : faceSucc = rot.symm * flip
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  U : P.Face
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. The distinguished face is unbounded. Source: -/
  U_unb : P.IsUnbounded U
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Uniqueness of the unbounded face. Source: -/
  U_uniq : ∀ F : P.Face, P.IsUnbounded F → F = U
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. The distinguished orbit borders exactly the outer face. -/
  U_iff : ∀ d, P.dartBorders d U ↔ faceSucc.SameCycle o d

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. A plane drawing whose vertices and complementary faces are
faithfully represented by rotation and face-successor orbits. Source: -/
structure PlaneWitness {D : Type} (rot flip : Equiv.Perm D) where
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  V : Type
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  vert : D → V
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  P : PLDrawing D V ⇑flip rot vert
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Geometric vertices agree with rotation orbits. Source: -/
  vert_iff : ∀ d e, vert d = vert e ↔ rot.SameCycle d e
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Every geometric vertex is represented by a dart. Source: -/
  vert_surj : ∀ v : V, ∃ d, vert d = v
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Every dart borders a complementary face. Source: -/
  face_exists : ∀ d, ∃ F : P.Face, P.dartBorders d F
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Border relation agrees with the face-successor orbit. -/
  face_iff : ∀ d e (F : P.Face), P.dartBorders d F →
    (P.dartBorders e F ↔ Equiv.Perm.SameCycle (rot.symm * flip) d e)
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Every complementary face borders a dart. Source: -/
  face_surj : ∀ F : P.Face, ∃ d, P.dartBorders d F
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  Definition 3.8. -/
  U : P.Face
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. The distinguished face is unbounded. Source: -/
  U_unb : P.IsUnbounded U
  /-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
  not a paper result. Uniqueness of the unbounded face. Source: -/
  U_uniq : ∀ F : P.Face, P.IsUnbounded F → F = U

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. The limiting KMSW face successor is inverse rotation after edge flip. -/
theorem kmswInfFaceSucc_eq (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite) :
    kmswInfFaceSucc w hfin = (kmswInfRot w hfin).symm * kmswFlip := by
  apply Equiv.ext
  intro d
  rw [kmswInfFaceSucc, Equiv.Perm.mul_apply]
  change (kmswInfRot w hfin).symm (d.1, !d.2) =
    (kmswInfRot w hfin).symm (kmswFlip d)
  rw [kmswFlip_apply]

/-- Helper toward Definition 3.8 / Theorem 1.4 (plane realization witness interface);
not a paper result. Under finite incidence, KMSW geometric endpoint equality is
Definition 3.8. -/
theorem kmswLimitDartVertex_eq_iff_sameCycle (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d e : ℕ × Bool) :
    kmswLimitDartVertex w d = kmswLimitDartVertex w e ↔
      (kmswInfRot w hfin).SameCycle d e :=
  (futureMap_sameCycle_iff w hfin d e).symm

end DirectedDistances.KMSW
