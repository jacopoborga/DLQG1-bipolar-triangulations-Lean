module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso10
import DirectedDistances.KMSW.WholePlaneRunRotationRestrict

/-! Iso2 defines `uibhbotFuturePlaneGeometricSide.rotation` by first return of
`wholePlaneRotation` to the future geometric darts, including missing edges.
Its `faceNext` instead uses first return of `wholePlaneFaceSucc`. The latter
does not give the faces of the planar submap: Iso10 proves that the run-zero
nonnegative external darts lie in past triangles, each with a three-periodic
ambient face orbit. The transitions 3 → 2 → 1 → 0 would require four distinct
darts in one such orbit. Deleting past edges merges those ambient faces.

The corrected construction retains the induced vertex rotation and defines
face succession as its inverse after dart reversal: `faceNext d e` means
`rotation e (flip d)`. This is the convention `ρ.symm (flip d)` used by
`kmswInfFaceSucc` and `wholePlaneFaceSucc`. No existing definition is edited.
The final marked plane-isomorphism target is recorded in Iso2; its old
plane-side `faceNext` cannot satisfy the all-boundary agreement. -/

public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5
open DirectedDistances.PaperProofs.Section4

/-- Helper toward Lemma 5.10. The future geometric carrier with first-return
vertex rotation and face succession given by inverse induced rotation after
dart reversal. This retains both darts of missing geometric edges. -/
@[expose] noncomputable def uibhbotFutureInducedPlaneGeometricSide
    (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (H : WholePlaneRotationHypothesis W) : GeometricSideSubmap :=
  { uibhbotFuturePlaneGeometricSide k W h H with
    faceNext := fun d e =>
      (uibhbotFuturePlaneGeometricSide k W h H).rotation e (d.1, !d.2) }

/-- Helper toward Lemma 5.10. Exact relational characterization of the
corrected face convention; no ambient face orbit is used. -/
theorem uibhbotFutureInducedPlaneGeometricSide_faceNext_iff
    (k : ℤ) (W : ℤ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)))
    (H : WholePlaneRotationHypothesis W) (d e : ℕ × Bool) :
    (uibhbotFutureInducedPlaneGeometricSide k W h H).faceNext d e ↔
      (uibhbotFuturePlaneGeometricSide k W h H).rotation e (d.1, !d.2) := Iff.rfl

/-- Helper toward Lemma 5.10. At every future dart, inverse ambient vertex
rotation first returns exactly at the inverse shifted-code rotation. Every
intermediate dart is outside the future geometric carrier. -/
theorem ae_uibhbotFutureSubmapDartEquiv_rotation_symm_firstReturn :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ d : ℕ × Bool,
                ∃ n : ℕ, 0 < n ∧
                  ((wholePlaneRotation W H).symm ^ n)
                      (uibhbotFutureSubmapDartEquiv k W h d).1 =
                    (uibhbotFutureSubmapDartEquiv k W h
                      ((kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin).symm
                        d)).1 ∧
                  ∀ m : ℕ, 0 < m → m < n →
                    (((wholePlaneRotation W H).symm ^ m)
                      (uibhbotFutureSubmapDartEquiv k W h d).1).1 ∉
                        (uibhbotFutureSubmap k W h).edges := by
  filter_upwards [ae_uibhbotCodeLawRel_boundaryShift_rotationHypothesis]
    with W hrot k h H hfin d
  let t := uibhbotBoundaryHitTime k W
  let V := shiftWordInt W t
  let H' : WholePlaneRotationHypothesis V := hrot k
  let phi := Classical.choice (wholePlaneStartIso_nonempty W t)
  have hstream : (fun i => uibhbotFutureCode k W (i + 1)) = shiftedStream V 0 := by
    rw [uibhbotFutureCode_stream]
    funext i
    simp [lemma38StartStream, shiftedStream, V, shiftWordInt, t]
  have hmap (x : ℕ × Bool) :
      phi.dart (wholePlaneDartι V 0 x) =
        (uibhbotFutureSubmapDartEquiv k W h x).1 := by
    refine (phi.dart_apply _).trans ?_
    rw [uibhbotFutureSubmapDartEquiv_val]
    change (phi.edge (wholePlaneEdgeι V 0 x.1), x.2) =
      (uibhbotFutureEdge k W x.1, x.2)
    rw [phi.iota_edge]
    rfl
  have hstep (x : WholePlaneDart V) :
      phi.dart ((wholePlaneRotation V H').symm x) =
        (wholePlaneRotation W H).symm (phi.dart x) := by
    apply (wholePlaneRotation W H).injective
    rw [← phi.rot H H', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hiter (m : ℕ) (x : WholePlaneDart V) :
      phi.dart (((wholePlaneRotation V H').symm ^ m) x) =
        ((wholePlaneRotation W H).symm ^ m) (phi.dart x) := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih,
          pow_succ', Equiv.Perm.mul_apply]
  obtain ⟨n, hn, heq, hgap⟩ := wholePlaneRotation_symm_firstReturn_run V H' 0 d
  refine ⟨n, hn, ?_, ?_⟩
  · have hcode : (kmswInfRot (shiftedStream V 0) (H'.1 0)).symm d =
        (kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin).symm d := by
      simp only [hstream]
    exact (congrArg _ (hmap d).symm).trans
      ((hiter n _).symm.trans ((congrArg phi.dart heq).trans
        ((hmap _).trans (congrArg (fun x =>
          (uibhbotFutureSubmapDartEquiv k W h x).1) hcode))))
  · intro m hm hmn hmem
    obtain ⟨e, he⟩ := hmem
    let y := ((wholePlaneRotation W H).symm ^ m)
      (uibhbotFutureSubmapDartEquiv k W h d).1
    have hy : (uibhbotFutureSubmapDartEquiv k W h (e, y.2)).1 = y := by
      rw [uibhbotFutureSubmapDartEquiv_val]
      exact Prod.ext he rfl
    apply hgap m hm hmn
    refine ⟨(e, y.2), phi.dart.injective ?_⟩
    exact (hmap _).trans (hy.trans
      ((congrArg _ (hmap d).symm).trans (hiter m _).symm))

/-- Helper toward Lemma 5.10. First return of forward ambient vertex rotation
to the future carrier is the shifted KMSW rotation, at every dart. In particular
this covers every integer boundary index without a sign restriction. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_rotation :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ d : ℕ × Bool,
                (uibhbotFutureInducedPlaneGeometricSide k W h H).rotation d
                  (kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin d) := by
  filter_upwards [ae_uibhbotFutureSubmapDartEquiv_rotation_symm_firstReturn]
    with W hreturn k h H hfin d
  let R := wholePlaneRotation W H
  let r := kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin
  let I := fun x => (uibhbotFutureSubmapDartEquiv k W h x).1
  obtain ⟨n, hn, heq, hgap⟩ := hreturn k h H hfin (r d)
  change (R.symm ^ n) (I (r d)) = I (r.symm (r d)) at heq
  rw [r.symm_apply_apply] at heq
  have hcancel (q : ℕ) (x : WholePlaneDart W) :
      (R ^ q) ((R.symm ^ q) x) = x := by
    change (R ^ q) ((R ^ q).symm x) = x
    exact (R ^ q).apply_symm_apply x
  have hcancel' (q : ℕ) (x : WholePlaneDart W) :
      (R.symm ^ q) ((R ^ q) x) = x := by
    change (R ^ q).symm ((R ^ q) x) = x
    exact (R ^ q).symm_apply_apply x
  have heq' : (R ^ n) (I d) = I (r d) := by
    rw [← heq, hcancel]
  change ∃ n : ℕ, 0 < n ∧ R^[n] (I d) = I (r d) ∧
    ∀ m : ℕ, 0 < m → m < n → (R^[m] (I d)).1 ∉
      (uibhbotFutureSubmap k W h).edges
  refine ⟨n, hn, heq', ?_⟩
  intro m hm hmn hmem
  have hback : (R.symm ^ (n - m)) (I (r d)) = (R ^ m) (I d) := by
    have hp : R ^ n = R ^ (n - m) * R ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [← heq', hp, Equiv.Perm.mul_apply, hcancel']
  apply hgap (n - m) (by omega) (by omega)
  change ((R.symm ^ (n - m)) (I (r d))).1 ∈ (uibhbotFutureSubmap k W h).edges
  rw [hback]
  exact hmem

/-- Helper toward Lemma 5.10. Exact agreement of the induced rotation
relation with the shifted KMSW permutation, including uniqueness of the
first-return endpoint. No rotation compatibility is a hypothesis. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_rotation_iff :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ d e : ℕ × Bool,
                (uibhbotFutureInducedPlaneGeometricSide k W h H).rotation d e ↔
                  kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin d = e := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_rotation]
    with W hreturn k h H hfin d e
  let R := wholePlaneRotation W H
  let r := kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin
  let I := fun x => (uibhbotFutureSubmapDartEquiv k W h x).1
  have hI : Function.Injective I := by
    intro a b hab
    exact (uibhbotFutureSubmapDartEquiv k W h).injective (Subtype.ext hab)
  have hmem (x : ℕ × Bool) : (I x).1 ∈ (uibhbotFutureSubmap k W h).edges :=
    (uibhbotFutureSubmapDartEquiv k W h x).property
  have hcan := hreturn k h H hfin d
  change ∃ n : ℕ, 0 < n ∧ R^[n] (I d) = I (r d) ∧
    ∀ m : ℕ, 0 < m → m < n → (R^[m] (I d)).1 ∉
      (uibhbotFutureSubmap k W h).edges at hcan
  constructor
  · rintro ⟨n, hn, he, hgap⟩
    obtain ⟨n₀, hn₀, he₀, hgap₀⟩ := hcan
    have hnn : n = n₀ := by
      rcases lt_trichotomy n n₀ with hlt | heq | hgt
      · exact False.elim (hgap₀ n hn hlt (he.symm ▸ hmem e))
      · exact heq
      · exact False.elim (hgap n₀ hn₀ hgt (he₀.symm ▸ hmem (r d)))
    subst n₀
    exact hI (he₀.symm.trans he)
  · intro he
    subst e
    exact hcan

/-- Helper toward Lemma 5.10. The corrected face relation agrees with the
shifted-code face permutation on every dart: inverse induced vertex rotation
after reversal, rather than first return within an ambient face. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_faceNext_iff :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ d e : ℕ × Bool,
                (uibhbotFutureInducedPlaneGeometricSide k W h H).faceNext d e ↔
                  kmswInfFaceSucc (fun i => uibhbotFutureCode k W (i + 1)) hfin d = e := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_rotation_iff]
    with W hrot k h H hfin d e
  change (uibhbotFutureInducedPlaneGeometricSide k W h H).rotation e (d.1, !d.2) ↔ _
  rw [hrot k h H hfin e (d.1, !d.2)]
  change kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin e = (d.1, !d.2) ↔
    (kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin).symm (d.1, !d.2) = e
  exact (Equiv.eq_symm_apply _).symm.trans eq_comm

/-- Helper toward Lemma 5.10. Simultaneously for every integer boundary
index, the corrected induced face successor moves from `j` to `j - 1`. -/
theorem ae_uibhbotFutureInducedPlaneGeometricSide_boundary_faceNext :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ _hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ j : ℤ,
                (uibhbotFutureInducedPlaneGeometricSide k W h H).faceNext
                  (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j)
                  (futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h (j - 1)) := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_faceNext_iff]
    with W hface k h H hfin j
  apply (hface k h H hfin _ _).2
  exact futureMapBoundaryDart_faceSucc
    (w := fun i => uibhbotFutureCode k W (i + 1)) (hfin := hfin) h j

/-- Helper toward Lemma 5.10. At each boundary dart, the induced vertex
rotation skips only omitted darts at that same vertex, and its first retained
endpoint is the shifted KMSW rotation. Here "omitted" means outside the full
future geometric carrier, independently of whether an edge is directed. -/
theorem ae_uibhbotFutureSubmap_boundary_rotation_firstReturn :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ k : ℤ,
        ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
          ∀ H : WholePlaneRotationHypothesis W,
            ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
              ∀ j : ℤ,
                let d := futureMapBoundaryDart
                  (fun i => uibhbotFutureCode k W (i + 1)) h j
                let I := fun x => (uibhbotFutureSubmapDartEquiv k W h x).1
                ∃ n : ℕ, 0 < n ∧
                  (wholePlaneRotation W H)^[n] (I d) =
                    I (kmswInfRot (fun i => uibhbotFutureCode k W (i + 1)) hfin d) ∧
                  ∀ m : ℕ, 0 < m → m < n →
                    ((wholePlaneRotation W H)^[m] (I d)).1 ∉
                        (uibhbotFutureSubmap k W h).edges ∧
                      wholePlaneDartVertex W ((wholePlaneRotation W H)^[m] (I d)) =
                        wholePlaneDartVertex W (I d) := by
  filter_upwards [ae_uibhbotFutureInducedPlaneGeometricSide_rotation]
    with W hrot k h H hfin j
  dsimp only
  let d := futureMapBoundaryDart (fun i => uibhbotFutureCode k W (i + 1)) h j
  let I := fun x => (uibhbotFutureSubmapDartEquiv k W h x).1
  let R := wholePlaneRotation W H
  obtain ⟨n, hn, heq, hgap⟩ := hrot k h H hfin d
  refine ⟨n, hn, heq, fun m hm hmn => ⟨hgap m hm hmn, ?_⟩⟩
  have hv (q : ℕ) : wholePlaneDartVertex W ((R ^ q) (I d)) =
      wholePlaneDartVertex W (I d) := by
    induction q with
    | zero => rfl
    | succ q ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact (wholePlaneRotation_preserves_dartVertex W H _).trans ih
  exact hv m

/- The bounded rotation and boundary-face targets are proved above. Independent
completion is claimed.


  ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
    ∀ k : ℤ,
      ∀ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        ∀ H : WholePlaneRotationHypothesis W,
          ∀ hfin : KMSWFiniteIncidence (fun i => uibhbotFutureCode k W (i + 1)),
            Nonempty (GeometricSideMarkedIso
              (uibhbotFutureInducedPlaneGeometricSide k W h H)
              (uibhbotFutureCodeGeometricSide k W h hfin))

This replaces the plane-side object in the intended Iso2 target, rather than
claiming that the old ambient-face-first-return object has become correct.
No existing definition or target is modified, and no isomorphism is assumed.
The omitted darts in the boundary first-return theorem are outside the future
geometric carrier at the same vertex; missing geometric edges in that carrier
are retained. The result does not filter them out by directed-edge presence. -/

end DirectedDistances.RandomWalk
