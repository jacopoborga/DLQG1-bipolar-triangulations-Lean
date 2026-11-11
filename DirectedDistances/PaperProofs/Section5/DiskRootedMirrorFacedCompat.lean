module

public import DirectedDistances.PaperProofs.Section5.DiskRootedMirrorCompat
public import DirectedDistances.PlanarMap.RootedLocallyFiniteMirrorContinuity
public import DirectedDistances.Probability.LawInvarianceLimit

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory
open DirectedDistances.PaperProofs.Section3.RootedBallSystem
open scoped Topology

noncomputable section

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
by geometric balls, beyond any prescribed radius. -/
private theorem mirrorFiniteExhaustion (M : RootedLocallyFiniteMap) [Finite M.D]
    (r : ℕ) : ∃ R, r ≤ R ∧ ∀ d : M.D, d ∈ rootedLocallyFiniteBallDarts M R := by
  classical
  let := Fintype.ofFinite M.D
  choose radius hradius using rootedLocallyFinite_dart_reachable M
  let R := max r (Finset.univ.sup radius)
  have hv (d : M.D) : rootedLocallyFiniteVertexClassOf M d ∈
      rootedLocallyFiniteRadiusVertices M R := by
    apply rootedLocallyFiniteRadiusVertices_mono M
      (le_trans (Finset.le_sup (Finset.mem_univ d)) (le_max_right _ _))
    exact (mem_rootedLocallyFiniteRadiusVertices M _ _).2 (hradius d)
  exact ⟨R, le_max_left _ _, fun d =>
    (mem_rootedLocallyFiniteBallDarts M R d).2 ⟨hv d, hv (M.edgeInv d)⟩⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
the ambient rotation. -/
private theorem mirrorFullBallRot (M : RootedLocallyFinitePlanarMap)
    (R : ℕ) (hR : 0 < R)
    (hall : ∀ d : M.D, d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap R)
    (d : (rootedLocallyFiniteFacedBall M R hR).toFramedBall.D) :
    (((rootedLocallyFiniteFacedBall M R hR).toFramedBall.map.rot d).1) =
      M.rot d.1 := by
  let B := (rootedLocallyFiniteFacedBall M R hR).toFramedBall
  have h := rootedLocallyFiniteBall_faceSucc_of_mem M.toRootedLocallyFiniteMap R
    (B.map.edgeInv (B.map.rot d)) (hall _)
  have hs : B.map.faceSucc (B.map.edgeInv (B.map.rot d)) = d := by
    change B.map.rot.symm (B.map.edgeInv (B.map.edgeInv (B.map.rot d))) = d
    rw [B.map.edgeInv_invol, Equiv.symm_apply_apply]
  change (B.map.faceSucc (B.map.edgeInv (B.map.rot d))).1 =
    M.rot.symm (M.edgeInv (M.edgeInv (B.map.rot d).1)) at h
  rw [hs, M.edgeInv_invol] at h
  simpa only [Equiv.apply_symm_apply] using (congrArg M.rot h).symm

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
preserving the ordered frame induces equality of every faced-ball class. -/
private theorem mirrorFiniteClassEq (M N : RootedLocallyFinitePlanarMap)
    [Finite M.D] [Finite N.D] (E : M.D ≃ N.D)
    (hrot : ∀ d, E (M.rot d) = N.rot (E d))
    (hedge : ∀ d, E (M.edgeInv d) = N.edgeInv (E d))
    (hmissing : ∀ d, N.missing (E d) ↔ M.missing d)
    (htail : ∀ d, N.tail (E d) ↔ M.tail d)
    (houter : ∀ d,
      Equiv.Perm.SameCycle (N.rot.symm * N.edgeInv) N.outer (E d) ↔
        Equiv.Perm.SameCycle (M.rot.symm * M.edgeInv) M.outer d)
    (hroot : E M.rootDart = N.rootDart)
    (hframe : E M.frameEdgeDart = N.frameEdgeDart)
    (hother : M.frameOtherDart = none ↔ N.frameOtherDart = none) (r : ℕ) :
    rootedLocallyFiniteFacedBallClass r M = rootedLocallyFiniteFacedBallClass r N := by
  classical
  obtain ⟨s, hrs, hs⟩ := mirrorFiniteExhaustion M.toRootedLocallyFiniteMap (r + 1)
  obtain ⟨R, hsR, hN⟩ := mirrorFiniteExhaustion N.toRootedLocallyFiniteMap s
  have hR : 0 < R := by omega
  have hM (d : M.D) : d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap R :=
    rootedLocallyFiniteBallDarts_mono _ hsR (hs d)
  let B := (rootedLocallyFiniteFacedBall M R hR).toFramedBall
  let C := (rootedLocallyFiniteFacedBall N R hR).toFramedBall
  let e : B.D ≃ C.D := {
    toFun := fun d => ⟨E d.1, hN _⟩
    invFun := fun d => ⟨E.symm d.1, hM _⟩
    left_inv := fun d => Subtype.ext (E.symm_apply_apply d.1)
    right_inv := fun d => Subtype.ext (E.apply_symm_apply d.1) }
  have hr (d : B.D) : e (B.map.rot d) = C.map.rot (e d) := by
    apply Subtype.ext
    exact (congrArg E (mirrorFullBallRot M R hR hM d)).trans
      ((hrot d.1).trans (mirrorFullBallRot N R hR hN (e d)).symm)
  have he (d : B.D) : e (B.map.edgeInv d) = C.map.edgeInv (e d) :=
    Subtype.ext (hedge d.1)
  have hf (d : B.D) : e (B.map.faceSucc d) = C.map.faceSucc (e d) := by
    apply C.map.rot.injective
    change C.map.rot (e (B.map.rot.symm (B.map.edgeInv d))) =
      C.map.rot (C.map.rot.symm (C.map.edgeInv (e d)))
    rw [← hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact he d
  have hc := framedBall_sameCycle_iff_of_equiv e B.map.faceSucc C.map.faceSucc hf
  let ec : C.D ≃ N.D := {
    toFun := Subtype.val
    invFun := fun d => ⟨d, hN d⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hfc (d : C.D) : ec (C.map.faceSucc d) =
      (N.rot.symm * N.edgeInv) (ec d) :=
    rootedLocallyFiniteBall_faceSucc_of_mem N.toRootedLocallyFiniteMap R d (hN _)
  have hcc := sameCycle_iff_of_intertwine C.map.faceSucc
    (N.rot.symm * N.edgeInv) ec hfc
  have ho : C.map.faceSucc.SameCycle C.map.outer (e B.map.outer) := by
    apply (hcc _ _).2
    exact (rootedLocallyFiniteOuterFrameDart_outer N.toRootedLocallyFiniteMap).symm.trans
      ((houter _).2 (rootedLocallyFiniteOuterFrameDart_outer M.toRootedLocallyFiniteMap))
  have I : FacedFramedBallIso (rootedLocallyFiniteFacedBall M R hR)
      (rootedLocallyFiniteFacedBall N R hR) := {
    toFramedBallIso := {
      mapIso := {
        toEquiv := e
        rot_comm := hr
        edgeInv_comm := he
        missing_iff := fun d => hmissing d.1
        tail_iff := fun d => htail d.1
        outer_iff := fun d => ⟨fun hd => (hc _ _).2 (ho.symm.trans hd),
          fun hd => ho.trans ((hc _ _).1 hd)⟩ }
      root_vertex := by
        have hh : e B.rootDart = C.rootDart := Subtype.ext hroot
        rw [hh]
      frameEdge_comm := Subtype.ext hframe
      frameOther_comm := by
        change ((M.frameOtherDart.map _).map e = none ∧ N.frameOtherDart.map _ = none) ∨ _
        cases hm : M.frameOtherDart with
        | none =>
          have hn := hother.mp hm
          exact Or.inl ⟨rfl, by simp only [hn, Option.map_none]⟩
        | some d =>
          cases hn : N.frameOtherDart with
          | none => exact (by simpa only [hm, reduceCtorEq] using hother.mpr hn)
          | some d' =>
            right
            refine ⟨e (B.map.edgeInv B.frameEdgeDart),
              C.map.edgeInv C.frameEdgeDart, ?_, ?_, ?_⟩
            · change (M.frameOtherDart.map _).map e = _
              rw [hm]
              rfl
            · change N.frameOtherDart.map _ = _
              rw [hn]
              rfl
            have hh : e B.frameEdgeDart = C.frameEdgeDart := Subtype.ext hframe
            rw [he, hh] }
    original_iff := fun d => ⟨fun _ x _ => hM x, fun _ x _ => hN x⟩ }
  exact Quotient.sound ⟨rootedLocallyFiniteFacedBallIso_restrict M N
    (Nat.succ_pos r) (by omega) I⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
transports the complete geometric sample, including its reversed ordered frame. -/
theorem diskRootedPlanarSampleMirrorFacedClassCompatibility_proved
    (n ell : ℕ) (hell : 0 < ell) :
    diskRootedPlanarSampleMirrorFacedClassCompatibility n ell hell := by
  classical
  intro p r
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let c := F.symm p.1
  let k : Fin ((ell + 1) - 1) := Fin.cast (by omega) p.2
  let c' := F.symm (kmswMirrorSymmetryEquiv (ell + 1) (n + (ell + 1)) (by omega) p.1)
  let k' : Fin ((ell + 1) - 1) := Fin.cast (by omega) (Fin.rev p.2)
  have hc : kmswWalkMirrorEquiv (ell + 1) n (by omega) c = c' := by
    simp only [kmswWalkMirrorEquiv, Equiv.trans_apply, c, c', F,
      Equiv.apply_symm_apply]
  have hk : Fin.rev k = k' := by
    apply Fin.ext
    simp only [k, k', Fin.rev, Fin.val_cast]
    omega
  have hid := rootedStage_walkMirror (by omega : 2 ≤ ell + 1) c k
  rw [hc, hk] at hid
  let A := kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c.val) n
  let B := kmswStageDirectedMap (finiteCodeExtend (n := n + 1) c'.val) n
  obtain ⟨I, hi⟩ := (DirectedMapWithMissing.toRootedClass_eq_iff B
    (kmswDiskRootDart c' k') A.mirror (A.edgeInv (kmswDiskRootDart c k))).mp hid
  let M := mirrorRootedLocallyFinitePlanarMap (diskRootedPlanarMapOfCodeMark c k)
  let N := diskRootedPlanarMapOfCodeMark c' k'
  have : Finite M.D := by
    change Finite (StageDart (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).nextEdge)
    infer_instance
  have : Finite N.D := by
    change Finite (StageDart (kmswStage (finiteCodeExtend (n := n + 1) c'.val) n).nextEdge)
    infer_instance
  have hframe : I.toEquiv.symm M.frameEdgeDart = N.frameEdgeDart := by
    apply I.toEquiv.injective
    change I.toEquiv (I.toEquiv.symm (A.edgeInv (A.edgeInv (kmswDiskRootDart c k)))) =
      I.toEquiv (B.edgeInv (kmswDiskRootDart c' k'))
    rw [Equiv.apply_symm_apply, I.edgeInv_comm, hi, A.edgeInv_invol]
    rfl
  change rootedLocallyFiniteFacedBallClass r M = rootedLocallyFiniteFacedBallClass r N
  apply mirrorFiniteClassEq M N I.toEquiv.symm
  · exact I.symm.rot_comm
  · exact I.symm.edgeInv_comm
  · exact I.symm.missing_iff
  · exact I.symm.tail_iff
  · exact I.symm.outer_iff
  · exact hframe
  · exact hframe
  · change (some _ = none ↔ some _ = none)
    simp only [reduceCtorEq]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
local instance mirrorLawTopology : TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
local instance mirrorLawMeasurable : MeasurableSpace RootedLocallyFinitePlanarMap :=
  borel RootedLocallyFinitePlanarMap

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
local instance mirrorLawBorel : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result. -/
private theorem mirrorLawClassMeasurable (r : ℕ) :
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    Measurable (rootedLocallyFiniteFacedBallClass r) := by
  let : MeasurableSpace FacedFramedBallClass := ⊤
  apply measurable_iff_comap_le.mpr
  let S := rootedLocallyFiniteFacedBallSystem
  change MeasurableSpace.comap (S.ballClass r) ⊤ ≤
    @borel S.Object (bsLocalDistanceTopologyGeneric S)
  rw [borel_bsLocalDistanceTopology_eq_iSup_ballClass_generic S]
  exact le_iSup_of_le r le_rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
disk law is invariant under the geometric reflection. -/
theorem diskRootedPlanarMapLaw_mirror_facedClass_invariant
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) (r : ℕ) :
    letI : MeasurableSpace FacedFramedBallClass := ⊤
    (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
        (rootedLocallyFiniteFacedBallClass r ∘ mirrorRootedLocallyFinitePlanarMap) =
      (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
        (rootedLocallyFiniteFacedBallClass r) := by
  classical
  let Q := {q : KMSWMapIsoClass (ell + 1) 1 (n + (ell + 1)) // q.IsChanneled}
  let : Fintype Q := Fintype.ofEquiv (KMSWLeftWalkClass (ell + 1) n)
    (kmswLeftEndpointSideEquiv (ell + 1) n (by omega))
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace (Fin ell) := ⊤
  let : MeasurableSpace FacedFramedBallClass := ⊤
  let : TopologicalSpace FacedFramedBallClass := ⊥
  let : DiscreteTopology FacedFramedBallClass := ⟨rfl⟩
  let μ := (uniformCountingMeasure Q).prod (uniformCountingMeasure (Fin ell))
  have h := diskRootedPlanarMapLaw_map_mirroredSample_facedClass n ell hell hle hmod r
  have hm := measurable_mirrorRootedLocallyFinitePlanarMap
  have hc := mirrorLawClassMeasurable r
  calc
    _ = μ.map ((rootedLocallyFiniteFacedBallClass r ∘
        mirrorRootedLocallyFinitePlanarMap) ∘ diskRootedPlanarMapOfSample n ell hell) := by
      rw [diskRootedPlanarMapLaw_toMeasure,
        Measure.map_map (hc.comp hm) (measurable_of_countable _)]
    _ = μ.map (rootedLocallyFiniteFacedBallClass r ∘
        diskRootedPlanarMapOfMirroredSample n ell hell) := by
      congr 1
      funext p
      exact diskRootedPlanarSampleMirrorFacedClassCompatibility_proved n ell hell p r
    _ = _ := h.symm

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
reflection invariant. Compatible coordinate cylinders form a generating pi-system. -/
theorem diskRootedPlanarMapLaw_mirror_invariant
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q) :
    (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
      mirrorRootedLocallyFinitePlanarMap =
        (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure := by
  have hm := measurable_mirrorRootedLocallyFinitePlanarMap
  have hbase : IsProbabilityMeasure (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure :=
    (diskRootedPlanarMapLaw n ell hell hle hmod).2
  have hpush : IsProbabilityMeasure
      ((diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
        mirrorRootedLocallyFinitePlanarMap) :=
    ((diskRootedPlanarMapLaw n ell hell hle hmod).map
      mirrorRootedLocallyFinitePlanarMap).2
  refine @measure_eq_of_ballClass_map_eq_generic FacedFramedBallClass inferInstance
    rootedLocallyFiniteFacedBallSystem _ _ hpush hbase ?_
  intro r
  change ((diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
    mirrorRootedLocallyFinitePlanarMap).map (rootedLocallyFiniteFacedBallClass r) =
      (diskRootedPlanarMapLaw n ell hell hle hmod).toMeasure.map
        (rootedLocallyFiniteFacedBallClass r)
  rw [Measure.map_map (mirrorLawClassMeasurable r) hm]
  exact diskRootedPlanarMapLaw_mirror_facedClass_invariant n ell hell hle hmod r

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
at every positive size; enlarging the band absorbs its finite initial segment. -/
private theorem mirrorLawAdmissibleSequence :
    ∃ A : ℝ, 1 < A ∧ ∃ ell : ℕ → ℕ,
      (∀ k, 0 < ell k ∧ ell k ≤ k + 1 ∧
        ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (ell k : ℤ) + 3 * q) ∧
      (∀ k, A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (ell k : ℝ)) ∧
      (∀ k, (ell k : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨N, hN⟩ := DirectedDistances.RandomWalk.exists_admissible_level
    (2 : ℝ) (by norm_num)
  let A : ℝ := (N : ℝ) + 3
  have hA : 2 ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpos : 0 < A := by linarith
  have hinv : A⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hA
  have hex (k : ℕ) : ∃ l : ℕ,
      (0 < l ∧ l ≤ k + 1 ∧
        ∃ q : ℤ, ((k + 1 : ℕ) : ℤ) = (l : ℤ) + 3 * q) ∧
      A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ (l : ℝ) ∧
      (l : ℝ) ≤ A * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    have hnr : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
    have hspos : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
    by_cases ht : N ≤ k + 1
    · obtain ⟨l, hlo, hhi, hle, hmod⟩ := hN (k + 1) ht
      have hlpos : (0 : ℝ) < (l : ℝ) := lt_of_lt_of_le
        (mul_pos (by norm_num) hspos) hlo
      refine ⟨l, ⟨by exact_mod_cast hlpos, hle, hmod⟩, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hinv hspos.le).trans hlo
      · exact hhi.trans (mul_le_mul_of_nonneg_right hA hspos.le)
    · have hnN : k + 1 ≤ N := by omega
      have hnA : ((k + 1 : ℕ) : ℝ) ≤ A := by
        have hh : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
        dsimp [A]
        linarith
      have hsone : 1 ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.one_le_sqrt.2 hnr
      have hsle : Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_self_iff.2 (Or.inr hnr)
      refine ⟨k + 1, ⟨by omega, le_rfl, ⟨0, by simp⟩⟩, ?_, ?_⟩
      · have hi : A⁻¹ ≤ 1 := by norm_num at hinv ⊢; linarith
        exact (calc
          A⁻¹ * Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
              1 * Real.sqrt ((k + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hi hspos.le
          _ = Real.sqrt ((k + 1 : ℕ) : ℝ) := one_mul _).trans hsle
      · exact hnA.trans (by nlinarith [mul_le_mul_of_nonneg_left hsone hpos.le])
  choose ell hadm hlo hhi using hex
  exact ⟨A, by linarith, ell, hadm, hlo, hhi⟩

/-- Helper toward Proposition 5.9 (prop-uihbot-sym) and Theorem 1.7(iv); not a paper result.
the disk laws to the UIBHBOT law. Outer approximation is the remaining explicit
topological prerequisite; it is not a premise asserting symmetry. -/
theorem uibhbotLaw_mirror_invariant
    (hOuter : @HasOuterApproxClosed RootedLocallyFinitePlanarMap
      (bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem)) :
    (uibhbotRootedPlanarMapLaw : ProbabilityMeasure RootedLocallyFinitePlanarMap).toMeasure.map
      mirrorRootedLocallyFinitePlanarMap = uibhbotRootedPlanarMapLaw.toMeasure := by
  obtain ⟨A, hA, ell, hadm, hlo, hhi⟩ := mirrorLawAdmissibleSequence
  have h := DirectedDistances.Probability.uibhbotRootedPlanarMapLaw_map_eq_of_disk_map_eq
    A hA ell hadm hlo hhi hOuter mirrorRootedLocallyFinitePlanarMap
    continuous_mirrorRootedLocallyFinitePlanarMap (fun k => ?_)
  · exact congrArg ProbabilityMeasure.toMeasure h
  · apply Subtype.ext
    exact diskRootedPlanarMapLaw_mirror_invariant (k + 1) (ell k)
      (hadm k).1 (hadm k).2.1 (hadm k).2.2

end
end DirectedDistances.PaperProofs.Section5
