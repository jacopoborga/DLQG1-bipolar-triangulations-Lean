/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso3
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso4

/-! # Distance consequences of geometric dart ball isomorphisms -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open Filter
open scoped ENNReal Topology

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: a positive-radius geometric dart ball
isomorphism bounds the geometric distance from above. -/
theorem d39GeomDistanceV2_le_of_nonempty {r : ℕ} (hr : 0 < r)
    (hIso : Nonempty (D39GeomBallIsoV2 r M rho M' rho')) :
    d39GeomDistanceV2 M rho M' rho' ≤ (1 / 2 : ℝ≥0∞) ^ r := by
  change (⨅ q : {q : ℕ // 0 < q},
      ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M rho M' rho')),
        ((1 / 2 : ℝ≥0∞) ^ q.1)) ≤ _
  exact (iInf_le (fun q : {q : ℕ // 0 < q} =>
      ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M rho M' rho')),
        ((1 / 2 : ℝ≥0∞) ^ q.1)) ⟨r, hr⟩).trans
    (iInf_le (fun _ : Nonempty (D39GeomBallIsoV2 r M rho M' rho') =>
      ((1 / 2 : ℝ≥0∞) ^ r)) hIso)

/-- Helper toward Definition 3.8: the geometric distance from a rooted map to
itself is zero. -/
theorem d39GeomDistanceV2_self (M : DirectedPlaneMapWithMissing V E)
    (rho : E × Bool) : d39GeomDistanceV2 M rho M rho = 0 := by
  let f : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
  have hfanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
    exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n)
  have hftendsto : Tendsto f atTop (𝓝 0) := by
    simpa only [f] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
  have hinf : (⨅ n, f n) = 0 := iInf_eq_of_tendsto hfanti hftendsto
  apply le_antisymm
  · rw [← hinf]
    apply le_iInf
    intro n
    have hr : 0 < n + 1 := Nat.succ_pos n
    have hIso : Nonempty (D39GeomBallIsoV2 (n + 1) M rho M rho) :=
      ⟨refl (M := M) (rho := rho) hr⟩
    have hbound := d39GeomDistanceV2_le_of_nonempty (M := M) (rho := rho)
      (M' := M) (rho' := rho) (r := n + 1) hr hIso
    change d39GeomDistanceV2 M rho M rho ≤ (1 / 2 : ℝ≥0∞) ^ n
    exact hbound.trans (by
      change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
      exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n))
  · exact bot_le

/-- Helper toward Definition 3.8: restrict a geometric dart ball
isomorphism to a smaller positive radius. -/
@[expose] def D39GeomBallIsoV2.restrict {r s : ℕ}
    (e : D39GeomBallIsoV2 r M rho M' rho') (hs : 0 < s)
    (hsr : s ≤ r) : D39GeomBallIsoV2 s M rho M' rho' := by
  let P := D39GeomBallIsoV2EdgePart.restrict e hs hsr
  refine {
    radius_pos := P.radius_pos
    h := P.h
    orientationPreserving := P.orientationPreserving
    vertexEquiv := P.vertexEquiv
    edgeEquiv := P.edgeEquiv
    faceEquiv := D39GeomBallIsoV2.restrictFaces e hsr
    edgeFlip := P.edgeFlip
    pos_map := P.pos_map
    edgeParam := P.edgeParam
    edgeParam_mono := P.edgeParam_mono
    edgeParam_anti := P.edgeParam_anti
    arc_map := P.arc_map
    src_map := P.src_map
    tgt_map := P.tgt_map
    missing_map := P.missing_map
    orientation_map := P.orientation_map
    root_edge_map := P.root_edge_map
    root_bool_map := P.root_bool_map
    face_image_map := ?_ }
  intro F
  change e.h '' F.1 = (D39GeomBallIsoV2.restrictFaces e hsr F).1
  exact D39GeomBallIsoV2.restrictFaces_image_map e hsr F

/-- Helper toward Definition 3.8: the geometric distance is at most the
radius scale exactly when the corresponding rooted balls are isomorphic. -/
theorem d39GeomDistanceV2_le_iff_nonempty {r : ℕ} (hr : 0 < r) :
    d39GeomDistanceV2 M rho M' rho' ≤ (1 / 2 : ℝ≥0∞) ^ r ↔
      Nonempty (D39GeomBallIsoV2 r M rho M' rho') := by
  constructor
  · intro hdist
    let f : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
    have hfstep : ∀ n, f (n + 1) < f n := by
      intro n
      dsimp [f]
      rw [pow_succ]
      have hbase : (1 / 2 : ℝ≥0∞) < 1 := by norm_num
      have hpow0 : (1 / 2 : ℝ≥0∞) ^ n ≠ 0 :=
        (ENNReal.pow_pos (by norm_num) n).ne'
      have hpowTop : (1 / 2 : ℝ≥0∞) ^ n ≠ ∞ :=
        ENNReal.pow_ne_top (by norm_num)
      exact (ENNReal.mul_lt_mul_right hpow0 hpowTop hbase).trans_eq (by simp)
    have hfanti : StrictAnti f := strictAnti_nat_of_succ_lt hfstep
    have hsub : r - 1 < r := Nat.sub_lt hr (by decide)
    have hfr : f r < f (r - 1) := hfanti hsub
    have hdist' : d39GeomDistanceV2 M rho M' rho' < f (r - 1) := by
      exact hdist.trans_lt (by simpa [f] using hfr)
    change (⨅ q : {q : ℕ // 0 < q},
      ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M rho M' rho')),
        ((1 / 2 : ℝ≥0∞) ^ q.1)) < f (r - 1) at hdist'
    obtain ⟨q, hq⟩ := iInf_lt_iff.mp hdist'
    obtain ⟨hIso, hqpow⟩ := (iInf_lt_iff.mp hq)
    have hqr : r ≤ q.1 := by
      by_contra hnot
      have hle : q.1 ≤ r - 1 := by omega
      have hpow : f (r - 1) ≤ f q.1 := by
        dsimp [f]
        exact pow_le_pow_right_of_le_one' (by norm_num) hle
      exact (not_lt_of_ge hpow) (by simpa [f] using hqpow)
    rcases hIso with ⟨e⟩
    exact ⟨D39GeomBallIsoV2.restrict e hr hqr⟩
  · exact d39GeomDistanceV2_le_of_nonempty hr

/-- Helper toward Definition 3.8: the geometric distance satisfies the
ultrametric inequality. -/
theorem d39GeomDistanceV2_ultrametric {V'' : Type*} {E'' : Type*}
    {M'' : DirectedPlaneMapWithMissing V'' E''} {rho'' : E'' × Bool} :
    d39GeomDistanceV2 M rho M'' rho'' ≤
      max (d39GeomDistanceV2 M rho M' rho')
        (d39GeomDistanceV2 M' rho' M'' rho'') := by
  let f : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
  apply le_of_forall_gt
  intro x hx
  have hAB : d39GeomDistanceV2 M rho M' rho' < x :=
    (le_max_left _ _).trans_lt hx
  have hBC : d39GeomDistanceV2 M' rho' M'' rho'' < x :=
    (le_max_right _ _).trans_lt hx
  change (⨅ q : {q : ℕ // 0 < q},
    ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M rho M' rho')),
      ((1 / 2 : ℝ≥0∞) ^ q.1)) < x at hAB
  change (⨅ q : {q : ℕ // 0 < q},
    ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 M' rho' M'' rho'')),
      ((1 / 2 : ℝ≥0∞) ^ q.1)) < x at hBC
  obtain ⟨qA, hqA⟩ := iInf_lt_iff.mp hAB
  obtain ⟨hIsoA, hscaleA⟩ := iInf_lt_iff.mp hqA
  obtain ⟨qB, hqB⟩ := iInf_lt_iff.mp hBC
  obtain ⟨hIsoB, hscaleB⟩ := iInf_lt_iff.mp hqB
  let s := min qA.1 qB.1
  have hs : 0 < s := by
    dsimp [s]
    omega
  rcases hIsoA with ⟨eA⟩
  rcases hIsoB with ⟨eB⟩
  have hIsoAC : Nonempty (D39GeomBallIsoV2 s M rho M'' rho'') := by
    refine ⟨trans (D39GeomBallIsoV2.restrict eA hs (Nat.min_le_left _ _))
      (D39GeomBallIsoV2.restrict eB hs (Nat.min_le_right _ _))⟩
  have hscaleS : f s < x := by
    by_cases h : qA.1 ≤ qB.1
    · simpa [f, s, min_eq_left h] using hscaleA
    · have h' : qB.1 ≤ qA.1 := Nat.le_of_not_ge h
      simpa [f, s, min_eq_right h'] using hscaleB
  have hbound := d39GeomDistanceV2_le_of_nonempty (M := M) (rho := rho)
    (M' := M'') (rho' := rho'') (r := s) hs hIsoAC
  exact hbound.trans_lt hscaleS

/-- Helper toward Definition 3.8: zero geometric distance is equivalent to
isomorphism at every positive radius. -/
theorem d39GeomDistanceV2_eq_zero_iff :
    d39GeomDistanceV2 M rho M' rho' = 0 ↔
      ∀ r : ℕ, 0 < r → Nonempty (D39GeomBallIsoV2 r M rho M' rho') := by
  constructor
  · intro hzero r hr
    apply (d39GeomDistanceV2_le_iff_nonempty (M := M) (rho := rho)
      (M' := M') (rho' := rho') hr).mp
    simp [hzero]
  · intro hall
    let f : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
    have hfanti : Antitone f := by
      apply antitone_nat_of_succ_le
      intro n
      change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
      exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n)
    have hftendsto : Tendsto f atTop (𝓝 0) := by
      simpa only [f] using
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
    have hinf : (⨅ n, f n) = 0 := iInf_eq_of_tendsto hfanti hftendsto
    apply le_antisymm
    · rw [← hinf]
      apply le_iInf
      intro n
      have hr : 0 < n + 1 := Nat.succ_pos n
      have hIso := hall (n + 1) hr
      have hbound := d39GeomDistanceV2_le_of_nonempty (M := M) (rho := rho)
        (M' := M') (rho' := rho') (r := n + 1) hr hIso
      change d39GeomDistanceV2 M rho M' rho' ≤ (1 / 2 : ℝ≥0∞) ^ n
      exact hbound.trans (by
        change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
        exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n))
    · exact bot_le

end DirectedDistances.PaperProofs.Section3

end
