module

public import DirectedDistances.KMSW.M0CutSeam
public import DirectedDistances.KMSW.M0CutLeftSide
public import DirectedDistances.KMSW.M0CutPresence
public import DirectedDistances.KMSW.M0CutBoundaryLabels
public import DirectedDistances.KMSW.M0CutRootTransport

public section
namespace DirectedDistances.KMSW

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The source cut data at the rotation-system (combinatorial-map) level.
The plane realization of the two-sided map and the complementary-component -/
structure M0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W) where
  /-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
  Q-M0-repr proof obligation); not a paper result.
  The source rightmost outgoing ray. -/
  betaR : WholePlaneRightmostRay W H
  /-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
  Q-M0-repr proof obligation); not a paper result.
  The ray starts at the terminal root endpoint. -/
  betaR_start : betaR.vertex 0 = wholePlaneEdgeEast W (m0CutLambdaZero W)
  /-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
  Q-M0-repr proof obligation); not a paper result.
  The source leftmost incoming chain. -/
  betaL : M0CutLeftmostChain W H (wholePlaneEdgeWest W (m0CutLambdaZero W))


namespace M0CutData
variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The root and extremal paths specify the seam. -/
@[expose] def seam (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutSeamEdge W H

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The geometric edges on the generated left side. -/
@[expose] def edges (D : M0CutData W H) : Set (WholePlaneEdge W) :=
  m0CutLeftEdges W H D.seam

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Both darts of every geometric cut edge, including missing edges. -/
@[expose] def darts (D : M0CutData W H) : Set (WholePlaneDart W) :=
  {d | d.1 ∈ D.edges}

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The missing-edge predicate inherited from the source cut. -/
@[expose] def missing (_D : M0CutData W H) : WholePlaneEdge W → Prop :=
  m0CutMissing W H

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The cut tail predicate retains the ambient orientation. -/
@[expose] def tail (_D : M0CutData W H) : WholePlaneDart W → Prop :=
  m0CutTail W H

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The west-to-east root dart. -/
@[expose] def rootDart (_D : M0CutData W H) : WholePlaneDart W :=
  (m0CutLambdaZero W, false)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Boundary labels defined directly from the source paths and root endpoints. -/
@[expose] def x (D : M0CutData W H) (k : ℤ) : WholePlaneVertex W :=
  if k = 0 then wholePlaneEdgeWest W (m0CutLambdaZero W)
  else if k = 1 then wholePlaneEdgeEast W (m0CutLambdaZero W)
  else if 2 ≤ k then D.betaR.vertex (k - 1).toNat
  else D.betaL.vertex (-k).toNat

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The derived labels satisfy the complete source boundary predicate. -/
theorem x_label (D : M0CutData W H) (k : ℤ) :
    m0CutBoundaryLabel W H k (D.x k) := by
  by_cases h0 : k = 0
  · exact Or.inl ⟨h0, by simp only [x, ite_eq_left h0]⟩
  by_cases h1 : k = 1
  · exact Or.inr (Or.inl ⟨h1, by simp only [x, ite_eq_right h0, ite_eq_left h1]⟩)
  by_cases hk : 2 ≤ k
  · refine Or.inr (Or.inr (Or.inl ⟨hk, D.betaR, D.betaR_start, ?_⟩))
    simp only [x, ite_eq_right h0, ite_eq_right h1, ite_eq_left hk]
  · refine Or.inr (Or.inr (Or.inr ⟨by omega, D.betaL, ?_⟩))
    simp only [x, ite_eq_right h0, ite_eq_right h1, ite_eq_right hk]

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Inverse cut rotation is the first positive ambient return to cut darts. -/
@[expose] def IsRot (D : M0CutData W H) (d d' : WholePlaneDart W) : Prop :=
  d' ∈ D.darts ∧ ∃ k : ℕ, 0 < k ∧
    ((wholePlaneRotation W H).symm ^ k) d = d' ∧
    ∀ j : ℕ, 0 < j → j < k →
      ((wholePlaneRotation W H).symm ^ j) d ∉ D.darts

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Shortest cut distance, with top for unreachable vertices. -/
@[expose] noncomputable def sdp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → ℕ∞ :=
  m0CutSDP W H D.seam

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Longest cut distance, with bottom for unreachable vertices. -/
@[expose] noncomputable def ldp (D : M0CutData W H) :
    WholePlaneVertex W → WholePlaneVertex W → WithBot ℕ∞ :=
  m0CutLDP W H D.seam

end M0CutData

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The two source paths exist under exactly the imported premises. -/
theorem m0CutData_nonempty (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    Nonempty (M0CutData W H) := by
  obtain ⟨P, hP, _⟩ := wholePlaneRightmostRay_exists_root_terminal W H 0 h
  obtain ⟨Q, _⟩ := m0Cut_betaL_exists W H h hLL
  refine ⟨⟨P, ?_, Q⟩⟩
  rw [(m0Cut_lambdaZero_endpoints W h).2, boundaryVertex_one]
  exact hP

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
A canonical choice from the proved nonempty source cut data. -/
@[expose] noncomputable def m0CutData (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) : M0CutData W H :=
  Classical.choice (m0CutData_nonempty W H h hLL)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Any two source data have the same path sequences and boundary labels. -/
theorem m0CutData_eq_fields (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (D E : M0CutData W H) :
    D.betaR.vertex = E.betaR.vertex ∧ D.betaR.edge = E.betaR.edge ∧
      D.betaL.vertex = E.betaL.vertex ∧ D.betaL.edge = E.betaL.edge ∧ D.x = E.x := by
  obtain ⟨hrv, hre⟩ := m0Cut_betaR_unique W H D.betaR E.betaR
    D.betaR_start E.betaR_start
  obtain ⟨hlv, hle⟩ := m0Cut_betaL_unique W H h hLL D.betaL E.betaL
  refine ⟨hrv, hre, hlv, hle, ?_⟩
  funext k
  simp only [M0CutData.x, hrv, hlv]

namespace M0CutData
variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
variable (D : M0CutData W H)
variable (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))))

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Source boundary labels equal the transported run-zero vertices. -/
theorem x_eq (k : ℤ) :
    D.x k = wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k) :=
  (m0Cut_boundaryLabel_iff W H h hLL k _).mp (D.x_label k)

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The geometric cut edges equal the run-zero edge range. -/
theorem edges_eq : D.edges = Set.range (wholePlaneEdgeι W 0) :=
  m0Cut_leftEdges_eq_runZero W H h D.seam (m0Cut_seamEdge_iff W H h hLL)

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The cut darts equal the full run-zero dart range. -/
theorem darts_eq : D.darts = Set.range (wholePlaneDartι W 0) :=
  m0Cut_leftEdgeDarts_eq_runZero W H h D.seam (m0Cut_seamEdge_iff W H h hLL)

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The inclusion commutes with geometric dart reversal. -/
theorem flip_eq (_D : M0CutData W H) (d : ℕ × Bool) :
    wholePlaneDartFlip W (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (futureMapEdgeInv d) := rfl

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The inverse run rotation is the first return of ambient inverse rotation. -/
theorem rot_eq (d : ℕ × Bool) :
    D.IsRot (wholePlaneDartι W 0 d)
      (wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d)) := by
  unfold IsRot
  rw [D.darts_eq h hLL]
  exact ⟨Set.mem_range_self _, m0Cut_rotation_symm_firstReturn W H d⟩

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
First positive return has a unique target on all ambient darts. -/
theorem rot_functional {d a b : WholePlaneDart W}
    (ha : D.IsRot d a) (hb : D.IsRot d b) : a = b := by
  obtain ⟨haS, i, hi, hia, hifirst⟩ := ha
  obtain ⟨hbS, j, hj, hjb, hjfirst⟩ := hb
  have hij : i = j := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact hjfirst i hi hlt (hia ▸ haS)
    · exact hifirst j hj hgt (hjb ▸ hbS)
  exact hia.symm.trans (hij ▸ hjb)

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Cut missingness equals run-zero non-presence. -/
theorem missing_eq (a : ℕ) :
    D.missing (wholePlaneEdgeι W 0 a) ↔ ¬ EdgePresent (shiftedStream W 0) a :=
  m0Cut_missing_iff W H h hLL a

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The cut and run-zero tail predicates agree. -/
theorem tail_eq (d : ℕ × Bool) :
    D.tail (wholePlaneDartι W 0 d) ↔ futureMapTail (shiftedStream W 0) d :=
  m0Cut_tail_iff W H h hLL d

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
The root, its labelled endpoints, presence, and directed tail are preserved. -/
theorem root_eq :
    D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
      wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
      wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
      wholePlaneEdgePresent W D.rootDart.1 ∧
      ¬ D.missing D.rootDart.1 ∧ D.tail D.rootDart := by
  have hr := m0Cut_lambdaZero_present_orientation W
  have ht : D.tail D.rootDart :=
    (D.tail_eq h hLL futureMapRootDart).mpr hr.2.2.1
  refine ⟨rfl, ?_, ?_, hr.2.1, ht.2, ht⟩
  · rfl
  · rfl

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Shortest distances agree at every pair of transported vertices. -/
theorem sdp_eq (u v : ℕ) :
    D.sdp (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      DirectedDistances.sdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ :=
  m0Cut_sdp_eq_present W H h hLL D.seam (m0Cut_seamEdge_iff W H h hLL) u v

include h hLL in
/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
Longest distances agree, including both extended-value conventions. -/
theorem ldp_eq (u v : ℕ) :
    D.ldp (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      presentLdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩ :=
  m0Cut_ldp_eq_present W H h hLL D.seam (m0Cut_seamEdge_iff W H h hLL) u v

end M0CutData

/-- Helper toward Theorem 1.4 (thm-busemann; M_{0,∞} identification,
Q-M0-repr proof obligation); not a paper result.
All combinatorial-map identification clauses for the canonical source data. -/
theorem m0CutData_identification (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0
        (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1))))) :
    let D := m0CutData W H h hLL
    (∀ k, D.x k =
      wholePlaneVertexι W 0 (boundaryVertex (shiftedStream W 0) h k)) ∧
    D.darts = Set.range (wholePlaneDartι W 0) ∧
    D.edges = Set.range (wholePlaneEdgeι W 0) ∧
    (∀ d, wholePlaneDartFlip W (wholePlaneDartι W 0 d) =
      wholePlaneDartι W 0 (futureMapEdgeInv d)) ∧
    (∀ d, D.IsRot (wholePlaneDartι W 0 d)
      (wholePlaneDartι W 0 ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm d))) ∧
    (∀ d a b, D.IsRot d a → D.IsRot d b → a = b) ∧
    (∀ a, D.missing (wholePlaneEdgeι W 0 a) ↔ ¬ EdgePresent (shiftedStream W 0) a) ∧
    (∀ d, D.tail (wholePlaneDartι W 0 d) ↔ futureMapTail (shiftedStream W 0) d) ∧
    (D.rootDart = wholePlaneDartι W 0 futureMapRootDart ∧
      wholePlaneEdgeWest W D.rootDart.1 = D.x 0 ∧
      wholePlaneEdgeEast W D.rootDart.1 = D.x 1 ∧
      wholePlaneEdgePresent W D.rootDart.1 ∧
      ¬ D.missing D.rootDart.1 ∧ D.tail D.rootDart) ∧
    (∀ u v, D.sdp (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      DirectedDistances.sdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩) ∧
    (∀ u v, D.ldp (wholePlaneVertexι W 0 u) (wholePlaneVertexι W 0 v) =
      presentLdp (⟨u⟩ : PresentVertex (shiftedStream W 0)) ⟨v⟩) := by
  let D := m0CutData W H h hLL
  exact ⟨D.x_eq h hLL, D.darts_eq h hLL, D.edges_eq h hLL, D.flip_eq,
    D.rot_eq h hLL, fun _ _ _ => D.rot_functional, D.missing_eq h hLL,
    D.tail_eq h hLL, D.root_eq h hLL, D.sdp_eq h hLL, D.ldp_eq h hLL⟩

end DirectedDistances.KMSW
