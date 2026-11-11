/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyCutLeftmost
public import DirectedDistances.KMSW.RunRightmostCoalesce
public import DirectedDistances.KMSW.RawHatSourceCut
import DirectedDistances.KMSW.RawGeodesicAE

 

public section
namespace DirectedDistances.PaperProofs.Section5.RightmostRay

open Filter MeasureTheory Quiver DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk




theorem runRightmostRay_exists_presentPath {w : ℕ → Fin 3}
    {hf : KMSWFiniteIncidence w} (R : KMSWRunRightmostRay w hf) :
    ∃ P : InfinitePresentPath w ⟨R.vertex 0⟩,
      P.edge = R.edge ∧ ∀ n, (P.initial n).1.id = R.vertex n := by
  have hprefix (N : ℕ) :
      ∃ p : Path (⟨R.vertex 0⟩ : PresentVertex w) ⟨R.vertex N⟩,
        p.length = N ∧ pathEdgeList p = List.ofFn (fun i : Fin N => R.edge i.val) := by
    induction N with
    | zero => exact ⟨.nil, rfl, rfl⟩
    | succ N ih =>
      obtain ⟨p, hp, he⟩ := ih
      let e : (⟨R.vertex N⟩ : PresentVertex w) ⟶ ⟨R.vertex (N + 1)⟩ :=
        ⟨R.edge N, (R.rightmost N).1, (R.rightmost N).2.1, R.target N⟩
      refine ⟨p.cons e, ?_, ?_⟩
      · rw [Path.length_cons, hp]
      · rw [pathEdgeList, he, List.ofFn_succ']
        simp only [List.concat_eq_append]
        rfl
  choose p hp he using hprefix
  exact ⟨⟨R.edge, fun n => ⟨⟨R.vertex n⟩, p n⟩, hp, he⟩,
    rfl, fun _ => rfl⟩





theorem m0Cut_rightmost_presentPath_exists
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) (k : ℤ) :
    ∃ R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
      R.vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
      (∀ S : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
        S.vertex 0 = boundaryVertex (shiftedStream W 0) h k → S = R) ∧
      ∃ P : InfinitePresentPath (shiftedStream W 0)
          (boundaryPresentVertex (shiftedStream W 0) h k),
        P.edge = R.edge ∧
        (∀ n, (P.initial n).1.id = R.vertex n) ∧
        ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
          (P.initial n).1.id (P.edge n) := by
  obtain ⟨R, hstart, huniq⟩ := kmswRunRightmostRay_existsUnique_from_boundary
    W H h hLL (m0CutData W H h hLL).betaL k
  have hp := runRightmostRay_exists_presentPath R
  rw [hstart] at hp
  obtain ⟨P, he, hv⟩ := hp
  refine ⟨R, hstart, huniq, P, he, hv, fun n => ?_⟩
  rw [hv, he]
  exact R.rightmost n




private theorem outgoing_arc_to_rightmost_eq {w : ℕ → Fin 3}
    {hf : KMSWFiniteIncidence w} {v e f : ℕ}
    (hfmost : kmswRunRightmostOutAt w hf v f)
    (harc : RotationArc (kmswInfRot w hf) (futureMapTail w)
      (e, false) (f, false)) : e = f := by
  have hprev : ¬ futureMapTail w ((kmswInfRot w hf).symm (f, false)) := by
    obtain ⟨_, _, k, hk, hstop, hgap⟩ := hfmost
    by_cases hk1 : k = 1
    · simpa only [hk1, pow_one] using hstop
    · intro hp
      have hnot := hgap 1 (by omega) (by omega)
      rw [pow_one] at hnot
      exact hnot hp.2
  obtain ⟨n, hn, hout⟩ := harc
  cases n with
  | zero => exact congrArg Prod.fst hn
  | succ n =>
    have hpred : (kmswInfRot w hf ^ n) (e, false) =
        (kmswInfRot w hf).symm (f, false) := by
      apply (kmswInfRot w hf).injective
      rw [Equiv.apply_symm_apply]
      exact (congrArg (fun σ : Equiv.Perm (ℕ × Bool) => σ (e, false))
        (pow_succ' (kmswInfRot w hf) n)).symm.trans hn
    exact (hprev (hpred ▸ hout n (Nat.le_succ n))).elim





theorem m0Cut_rightmost_first_edge
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0)) (k : ℤ)
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k) :
    R.edge 0 = act (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k) := by
  have harc := boundaryHit_outgoing_arc (shiftedStream W 0) h (H.1 0) k
    (R.edge 0) (R.rightmost 0).1 ((R.rightmost 0).2.1.trans hstart)
  exact (outgoing_arc_to_rightmost_eq (R.rightmost 0) harc).symm





theorem m0Cut_ae_ldp_geodesic_and_rightmost_exists :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        ∀ k : ℤ,
          Nonempty (M0CutInfiniteGeodesic W H h hLL k true) ∧
          ∃ R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
            R.vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
            ∃ P : InfinitePresentPath (shiftedStream W 0)
                (boundaryPresentVertex (shiftedStream W 0) h k),
              P.edge = R.edge ∧
              ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
                (P.initial n).1.id (P.edge n) := by
  have hp := iidCodes_ae_boundary_infinite_extremal
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  have hmap := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
  filter_upwards [hmap, m0Cut_identification_ae] with W hW hid
  have hs : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp only [shiftedCodePath, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
  rw [hs] at hW
  obtain ⟨H, h, hLL, _⟩ := hid
  refine ⟨H, h, hLL, fun k => ?_⟩
  obtain ⟨Q, hQ⟩ := (hW h k).1
  obtain ⟨R, hr, _, P, he, _, hright⟩ :=
    m0Cut_rightmost_presentPath_exists W H h hLL k
  exact ⟨⟨m0CutInfiniteGeodesicOfPresentPath W H h hLL k true Q hQ⟩,
    R, hr, P, he, hright⟩





theorem m0Cut_ae_xdp_geodesic_and_rightmost_exists :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0
          (kmswLLCreatedEdge (shiftedStream W 0)
            (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
        ∀ (longest : Bool) (k : ℤ),
          Nonempty (M0CutInfiniteGeodesic W H h hLL k longest) ∧
          ∃ R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0),
            R.vertex 0 = boundaryVertex (shiftedStream W 0) h k ∧
            ∃ P : InfinitePresentPath (shiftedStream W 0)
                (boundaryPresentVertex (shiftedStream W 0) h k),
              P.edge = R.edge ∧
              ∀ n, kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0)
                (P.initial n).1.id (P.edge n) := by
  have hp := iidCodes_ae_boundary_infinite_extremal
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  have hmap := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
  filter_upwards [hmap, m0Cut_identification_ae] with W hW hid
  have hs : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp only [shiftedCodePath, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel]
  rw [hs] at hW
  obtain ⟨H, h, hLL, _⟩ := hid
  refine ⟨H, h, hLL, fun longest k => ?_⟩
  have hg : ∃ Q : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k),
      if longest then Q.HasLongestSegments else Q.HasShortestSegments := by
    cases longest with
    | false => exact (hW h k).2
    | true => exact (hW h k).1
  obtain ⟨Q, hQ⟩ := hg
  obtain ⟨R, hr, _, P, he, _, hright⟩ :=
    m0Cut_rightmost_presentPath_exists W H h hLL k
  exact ⟨⟨m0CutInfiniteGeodesicOfPresentPath W H h hLL k longest Q hQ⟩,
    R, hr, P, he, hright⟩

end DirectedDistances.PaperProofs.Section5.RightmostRay
