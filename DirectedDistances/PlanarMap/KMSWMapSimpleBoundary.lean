module

public import DirectedDistances.PlanarMap.KMSWMapChanneled
public import DirectedDistances.PlanarMap.BipolarBoundaryData
public import DirectedDistances.PlanarMap.GeneralBipolarBoundary
public import DirectedDistances.PlanarMap.KMSWLeftEndpointCarrier
public import DirectedDistances.PlanarMap.KMSWRightEndpointCarrier
public import DirectedDistances.PlanarMap.BdyReverseBijective

public section
namespace DirectedDistances.PlanarMap

universe u

private theorem sameCycle_map_simpleBoundary {D D' : Type*}
    [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']
    {ℓ r : ℕ} {B : BipolarTriangulationWithBoundaryBase D ℓ r}
    {B' : BipolarTriangulationWithBoundaryBase D' ℓ r}
    (I : BipolarBoundaryBaseIso B B') {d e : D}
    (h : Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv d e) :
    Equiv.Perm.SameCycle B'.map.toCombinatorialMap.edgeInv
      (I.toEquiv d) (I.toEquiv e) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have hpow : ∀ (n : ℕ) (x : D),
      I.toEquiv ((B.map.toCombinatorialMap.edgeInv ^ n) x) =
        (B'.map.toCombinatorialMap.edgeInv ^ n) (I.toEquiv x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply]
      exact (ih (B.map.toCombinatorialMap.edgeInv x)).trans
        (congrArg (B'.map.toCombinatorialMap.edgeInv ^ n) (I.edgeInv_comm x))
  calc
    (B'.map.toCombinatorialMap.edgeInv ^ n) (I.toEquiv d) =
        I.toEquiv ((B.map.toCombinatorialMap.edgeInv ^ n) d) :=
      (hpow n d).symm
    _ = I.toEquiv e := congrArg I.toEquiv hn

namespace KMSWMapRep

variable {ℓ r n : ℕ}

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[expose] def IsSimpleOuterBoundary (R : KMSWMapRep ℓ r n) : Prop :=
  (∀ v, v ∈ R.B.leftPath.vertices → v ∈ R.B.rightPath.vertices →
    v = R.B.source ∨ v = R.B.sink) ∧
  (∀ d, d ∈ R.B.leftPath.darts → ∀ e, e ∈ R.B.rightPath.darts →
    ¬ Equiv.Perm.SameCycle R.B.map.toCombinatorialMap.edgeInv d e)

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
theorem isSimpleOuterBoundary_iff_of_iso (R R' : KMSWMapRep ℓ r n)
    (I : BipolarBoundaryBaseIso R.B R'.B) :
    R.IsSimpleOuterBoundary ↔ R'.IsSimpleOuterBoundary := by
  have hmap (A C : KMSWMapRep ℓ r n)
      (J : BipolarBoundaryBaseIso A.B C.B)
      (h : A.IsSimpleOuterBoundary) : C.IsSimpleOuterBoundary := by
    constructor
    · intro v hvL hvR
      let w := J.vertexEquiv.symm v
      have hwL : w ∈ A.B.leftPath.vertices :=
        (J.mem_leftPath_vertices_iff).mpr (by simpa [w] using hvL)
      have hwR : w ∈ A.B.rightPath.vertices :=
        (J.mem_rightPath_vertices_iff).mpr (by simpa [w] using hvR)
      rcases h.1 w hwL hwR with hs | ht
      · left
        calc
          v = J.vertexEquiv w := by simp [w]
          _ = J.vertexEquiv A.B.source := congrArg J.vertexEquiv hs
          _ = C.B.source := J.vertexEquiv_source
      · right
        calc
          v = J.vertexEquiv w := by simp [w]
          _ = J.vertexEquiv A.B.sink := congrArg J.vertexEquiv ht
          _ = C.B.sink := J.vertexEquiv_sink
    · intro d hdL e heR hcycle
      have hdPre : d ∈ A.B.leftPath.darts.map J.toEquiv := by
        simpa only [J.leftDarts] using hdL
      have hePre : e ∈ A.B.rightPath.darts.map J.toEquiv := by
        simpa only [J.rightDarts] using heR
      obtain ⟨d₀, hd₀, hdEq⟩ := List.mem_map.mp hdPre
      obtain ⟨e₀, he₀, heEq⟩ := List.mem_map.mp hePre
      have hd₀Eq : d₀ = J.toEquiv.symm d := by
        apply J.toEquiv.injective
        simpa using hdEq
      have he₀Eq : e₀ = J.toEquiv.symm e := by
        apply J.toEquiv.injective
        simpa using heEq
      subst d₀
      subst e₀
      have hback := sameCycle_map_simpleBoundary J.symm hcycle
      have hsymm : J.symm.toEquiv = J.toEquiv.symm := rfl
      rw [hsymm] at hback
      exact h.2 (J.toEquiv.symm d) hd₀ (J.toEquiv.symm e) he₀
        hback
  constructor
  · exact hmap R R' I
  · intro h
    exact hmap R' R I.symm h

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[expose] def toStrong (R : KMSWMapRep ℓ r n)
    (h : R.IsSimpleOuterBoundary) :
    BipolarTriangulationWithBoundary (Fin R.dartCount) ℓ r :=
  R.B.toStrong h.1 h.2

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[simp] theorem toStrong_toBase (R : KMSWMapRep ℓ r n)
    (h : R.IsSimpleOuterBoundary) : (R.toStrong h).toBase = R.B :=
  BipolarTriangulationWithBoundaryBase.toStrong_toBase R.B h.1 h.2

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[expose] def toStrongMbc (R : KMSWMapRep ℓ r n)
    (h : R.IsSimpleOuterBoundary) (hc : R.IsChanneled) :
    BoundaryMbcClass (Fin R.dartCount) ℓ r :=
  ⟨R.toStrong h, by change R.B.IsBoundaryChanneledBase; exact hc⟩

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
theorem isSimpleOuterBoundary_of_rightEndpoint
    (R : KMSWMapRep ℓ 1 n) (hℓ : 2 ≤ ℓ) : R.IsSimpleOuterBoundary := by
  constructor
  · intro v hvL hvR
    exact left_right_paths_meet_only_at_endpoints R.B hℓ v hvL hvR
  · exact left_right_path_edge_disjoint R.B hℓ

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
theorem isSimpleOuterBoundary_of_leftEndpoint
    (R : KMSWMapRep 1 r n) (hr : 2 ≤ r) : R.IsSimpleOuterBoundary := by
  constructor
  · intro v hvL hvR
    exact right_left_paths_meet_only_at_endpoints R.B hr v hvR hvL
  · intro d hdL e heR hcycle
    exact (right_left_path_edge_disjoint R.B hr e heR d hdL) hcycle.symm

end KMSWMapRep

namespace KMSWMapIsoClass

variable {ℓ r n : ℕ}

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[expose] def IsSimpleOuterBoundary (q : KMSWMapIsoClass ℓ r n) : Prop :=
  Quotient.lift (fun R : KMSWMapRep ℓ r n => R.IsSimpleOuterBoundary)
    (by
      intro R R' h
      rcases h with ⟨I⟩
      exact propext (KMSWMapRep.isSimpleOuterBoundary_iff_of_iso R R' I)) q

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
@[simp] theorem isSimpleOuterBoundary_mk (R : KMSWMapRep ℓ r n) :
    IsSimpleOuterBoundary (KMSWMapIsoClass.mk R) ↔ R.IsSimpleOuterBoundary :=
  Iff.rfl

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
theorem isSimpleOuterBoundary_of_rightEndpoint (hℓ : 2 ≤ ℓ)
    (q : KMSWMapIsoClass ℓ 1 n) : q.IsSimpleOuterBoundary := by
  induction q using KMSWMapIsoClass.ind with
  | h R => exact R.isSimpleOuterBoundary_of_rightEndpoint hℓ

/-- the simple-outer-boundary carrier recommended by simple-boundary restriction
adopted; not the paper result. -/
theorem isSimpleOuterBoundary_of_leftEndpoint (hr : 2 ≤ r)
    (q : KMSWMapIsoClass 1 r n) : q.IsSimpleOuterBoundary := by
  induction q using KMSWMapIsoClass.ind with
  | h R => exact R.isSimpleOuterBoundary_of_leftEndpoint hr

end KMSWMapIsoClass

end DirectedDistances.PlanarMap
