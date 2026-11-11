module

public import DirectedDistances.PaperProofs.Section5.DiskWindowClassEquality

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The exposed decoder wrapper sends the one-based prefix and mark to its core. -/
theorem diskBridgeDecoder_eq_core (ell n : ℕ) (hell : 1 ≤ ell)
    (hle : ell ≤ n) (hmod : ∃ q : ℤ, (n : ℤ) = ell + 3 * q)
    (p : (ℕ → Fin 3) × ℕ) :
    diskBridgeDecoder ell n hell hle hmod p =
      diskBridgeDecoderCore ell n hell hle hmod (diskBridgePrefix n p, p.2) := by
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The disk class is the quotient of its decoded KMSW stage framed ball. -/
theorem diskBSBallClass_decoder_stage_repr (n ell : ℕ) (hell : 0 < ell)
    (hle : ell ≤ n)
    (hmod : ∃ q : ℤ, (n : ℤ) = (ell : ℤ) + 3 * q)
    (r : ℕ) (hr : 0 < r) (p : (ℕ → Fin 3) × ℕ) :
    diskBSBallClass n ell hell r hr
      (diskBridgeDecoder ell n (by omega) hle hmod p) =
      Quotient.mk FramedBall.setoid
        (kmswDiskStageFramedBall
          ((kmswLeftEndpointSideEquiv (ell + 1) n (by omega)).symm
            (diskBridgeDecoder ell n (by omega) hle hmod p).1)
          (Fin.cast (by omega : ell = (ell + 1) - 1)
            (diskBridgeDecoder ell n (by omega) hle hmod p).2)
          r hr) := by
  rfl

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv); not a paper result.
The decoded-window class is the class from its explicit decoded KMSW stage data. -/
theorem uibhbotDecodedWindowBallClass_stage_repr (N r : ℕ)
    (x : Fin (2 * N + 1) → ℤ × ℤ) :
    uibhbotDecodedWindowBallClass N r x =
      uibhbotStageDataBallClassRel
        ⟨kmswStage (windowCodeDecode N x) (2 * N),
          kmswStageDirectedMap (windowCodeDecode N x) (2 * N)⟩
        r (kmswLLCreatedEdge (windowCodeDecode N x) N) true := by
  rfl

end DirectedDistances.PaperProofs.Section5
