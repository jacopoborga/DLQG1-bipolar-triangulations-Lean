module

public import DirectedDistances.PaperProofs.Section5.DiskWindowDecoderEval
public import DirectedDistances.PaperProofs.Section5.DiskStageBallStability
public import DirectedDistances.PaperProofs.Section5.DiskWindowClassEquality
public import DirectedDistances.PaperProofs.Section5.Prop516Assembly

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
This module supplies the source-support bridge for the remaining
`DiskWindowClassComparison.class_eq_on_capture` obligation. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBridgePrefix_admissible_of_cone
    (ell n : ℕ) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n) :
    KMSWLeftWalkAdmissible (ell + 1) n (diskBridgePrefix n p) := by
  have hwalk (j : ℕ) (hj : j ≤ n) :
      integrateCodes (finiteCodeExtend (n := n + 1) (diskBridgePrefix n p)) j =
        codeWalk p.1 j := by
    rw [codeWalk_eq_integrateCodes]
    unfold integrateCodes
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
    simp [finiteCodeExtend, hin, diskBridgePrefix_apply]
  change (∀ j ≤ n,
      0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk p.1 j).1 ∧
        0 ≤ (((ell : ℤ), (0 : ℤ)) + codeWalk p.1 j).2) ∧
    ((ell : ℤ), (0 : ℤ)) + codeWalk p.1 n = (0, 0) at hp
  unfold KMSWLeftWalkAdmissible
  rw [show ((ell + 1 : ℕ) : ℤ) - 1 = (ell : ℤ) by omega]
  refine ⟨?_, ?_⟩
  · rw [hwalk n le_rfl]
    exact hp.2
  · intro j hj
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    rw [hwalk j hjn]
    exact hp.1 j hjn

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem kmswDiskFirstHit_eq_codeFstFirstHit_toNat
    (ell n : ℕ) (p : (ℕ → Fin 3) × ℕ)
    (c : KMSWLeftWalkClass (ell + 1) n)
    (hc : ∀ i : Fin n, c.val i = p.1 (i.val + 1))
    (k : Fin ell) (hk : k.val + 1 = p.2) :
    kmswDiskFirstHit c (Fin.cast (by omega : ell = (ell + 1) - 1) k) =
      (codeFstFirstHit (-(p.2 : ℤ)) p.1).toNat := by
  let kc := Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := finiteCodeExtend (n := n + 1) c.val
  have hwalk (j : ℕ) (hj : j ≤ n) :
      integrateCodes u j = codeWalk p.1 j := by
    rw [codeWalk_eq_integrateCodes]
    unfold integrateCodes
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := (Finset.mem_range.mp hi).trans_le hj
    have hu : u i = p.1 (i + 1) := by
      change (if h : i < n + 1 - 1 then c.val ⟨i, h⟩ else 0) = _
      rw [dite_eq_left (by omega : i < n + 1 - 1)]
      simpa using hc ⟨i, hin⟩
    rw [hu]
  have hL (j : ℕ) (hj : j ≤ n) : L u j = (codeWalk p.1 j).1 := by
    rw [kmsw_L_eq, hwalk j hj]
  let T := kmswDiskFirstHit c kc
  have hspec := kmswDiskFirstHit_spec c kc
  dsimp only [u, T] at hspec
  rcases hspec with ⟨hTpos, hTn, _, hlevel, hbefore, _⟩
  have hhit : ∃ j, (codeWalk p.1 j).1 = -(p.2 : ℤ) := by
    refine ⟨T, ?_⟩
    rw [← hL T hTn, hlevel]
    have hk' : kc.val + 1 = p.2 := by simpa [kc] using hk
    omega
  have hfind : Nat.find hhit = T := by
    apply (Nat.find_eq_iff hhit).2
    constructor
    · rw [← hL T hTn, hlevel]
      have hk' : kc.val + 1 = p.2 := by simpa [kc] using hk
      omega
    · intro j hj hcontra
      have hgt := hbefore j hj
      have hjn : j ≤ n := (Nat.le_of_lt hj).trans hTn
      rw [hL j hjn] at hgt
      have hk' : kc.val + 1 = p.2 := by simpa [kc] using hk
      have hkz : ((kc.val + 1 : ℕ) : ℤ) = (p.2 : ℤ) := by
        exact_mod_cast hk'
      rw [hkz] at hgt
      omega
  have htime : codeFstFirstHit (-(p.2 : ℤ)) p.1 = T := by
    simp [codeFstFirstHit, hhit, hfind]
  rw [htime]
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBridgeDecoder_eq_on_cone_support
    (ell n : ℕ) (hell : 1 ≤ ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q)
    (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    diskBridgeDecoder ell n hell hle hmod p =
      (kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
          ⟨diskBridgePrefix n p,
            diskBridgePrefix_admissible_of_cone ell n p hp⟩,
        ⟨p.2 - 1, by omega⟩) := by
  exact diskBridgeDecoder_eq_on_support ell n hell hle hmod p
    (diskBridgePrefix_admissible_of_cone ell n p hp) hlo hhi

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result. -/
theorem diskBSBallClass_decoder_eq_prefix_stage
    (n ell : ℕ) (hell : 0 < ell) (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ)
    (hp : p.1 ∈ coneEvent (ell : ℤ) 0 n)
    (hlo : 1 ≤ p.2) (hhi : p.2 ≤ ell) :
    diskBSBallClass n ell hell r hr
        (diskBridgeDecoder ell n (by omega) hle hmod p) =
      diskStageBSBallClass r hr
        (⟨diskBridgePrefix n p,
            diskBridgePrefix_admissible_of_cone ell n p hp⟩,
          Fin.cast (by omega : ell = (ell + 1) - 1)
            ⟨p.2 - 1, by omega⟩) := by
  let F := kmswLeftEndpointSideEquiv (ell + 1) n (by omega)
  let c : KMSWLeftWalkClass (ell + 1) n :=
    ⟨diskBridgePrefix n p, diskBridgePrefix_admissible_of_cone ell n p hp⟩
  rw [diskBridgeDecoder_eq_on_cone_support ell n (by omega) hle hmod p hp hlo hhi]
  change Quotient.mk FramedBall.setoid
      (kmswDiskStageFramedBall (F.symm (F c))
        (Fin.cast (by omega : ell = (ell + 1) - 1) ⟨p.2 - 1, by omega⟩)
        r hr) =
    Quotient.mk FramedBall.setoid
      (kmswDiskStageFramedBall c
        (Fin.cast (by omega : ell = (ell + 1) - 1) ⟨p.2 - 1, by omega⟩)
        r hr)
  rw [F.symm_apply_apply]

end DirectedDistances.PaperProofs.Section5
