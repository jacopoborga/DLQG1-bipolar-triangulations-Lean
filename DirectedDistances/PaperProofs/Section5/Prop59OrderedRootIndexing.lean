module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Ring

/-! Supporting lemmas for paper labels `prop-uihbot-sym` (see CORRESPONDENCE.md). -/





public section
namespace DirectedDistances.PaperProofs.Section5

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling -/
@[expose] def m59ReflectedBoundary {V W : Type*} (h : V → W)
    (x : ℤ → V) (k : ℤ) : W := h (x (1 - k))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling -/
@[expose] def m59PrintedBoundary {V W : Type*} (h : V → W)
    (x : ℤ → V) (k : ℤ) : W := h (x (-k))

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
reversal shifted by one index. -/
theorem m59ReflectedBoundary_eq_shiftedPrinted {V W : Type*} (h : V → W)
    (x : ℤ → V) (k : ℤ) :
    m59ReflectedBoundary h x k = m59PrintedBoundary h x (k - 1) := by
  have hi : 1 - k = -(k - 1) := by ring
  rw [m59ReflectedBoundary, m59PrintedBoundary, hi]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
index is an involution. -/
theorem m59BoundaryIndex_involution (k : ℤ) : 1 - (1 - k) = k := by
  ring

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
`intrinsicIncrementSource_mirror` uses precisely this reflected index. -/
@[expose] def m59RepositoryMirrorIndex (k : ℤ) : ℤ := 1 - k

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
`k ↦ 1-k`, convention B. -/
theorem m59RepositoryMirrorIndex_eq_one_sub (k : ℤ) :
    m59RepositoryMirrorIndex k = 1 - k := rfl

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling -/
@[expose] def m59ReflectedBusemann (X : ℤ → ℤ) (k : ℤ) : ℤ :=
  X (1 - k) - X 1

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
`X 1 - X 1 = 0`. -/
theorem m59ReflectedBusemann_zero (X : ℤ → ℤ) :
    (m59ReflectedBusemann X 0 = X 1 - X 1) ∧ (X 1 - X 1 = 0) := by
  constructor
  · rfl
  · exact sub_self _



theorem m59ReflectedBusemann_eq_printedRecenter (X : ℤ → ℤ) (k : ℤ) :
    m59ReflectedBusemann X k =
      (fun j : ℤ => X (-j)) (k - 1) - (fun j : ℤ => X (-j)) (-1) := by
  have hi : 1 - k = -(k - 1) := by ring
  have hroot : (1 : ℤ) = -(-1) := by ring
  change X (1 - k) - X 1 = X (-(k - 1)) - X (-(-1))
  rw [hi, ← hroot]

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
sign and index `-k`. -/
theorem m59ReflectedBusemann_forwardIncrement (X : ℤ → ℤ) (k : ℤ) :
    m59ReflectedBusemann X (k + 1) - m59ReflectedBusemann X k =
      -(X (-k + 1) - X (-k)) := by
  have hleft : 1 - (k + 1) = -k := by ring
  have hright : 1 - k = -k + 1 := by ring
  simp only [m59ReflectedBusemann, hleft, hright]
  ring

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
`X 1 - X 0`. -/
theorem m59ReflectedBusemann_forwardIncrement_zero (X : ℤ → ℤ) :
    m59ReflectedBusemann X (0 + 1) - m59ReflectedBusemann X 0 =
      -(X 1 - X 0) := by
  simpa using m59ReflectedBusemann_forwardIncrement X (0 : ℤ)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
`ldpIncrement` (`Recursive/LDPMasterFromLaw.lean:31`) and
`increment` (`Recursive/SDPMasterFromLaw.lean:36`) use `Y k - Y (k-1)`.
The reflected backward increment is minus the original one at `2-k`. -/
theorem m59ReflectedBusemann_backwardIncrement (X : ℤ → ℤ) (k : ℤ) :
    m59ReflectedBusemann X k - m59ReflectedBusemann X (k - 1) =
      -(X (2 - k) - X ((2 - k) - 1)) := by
  have hleft : 1 - (k - 1) = 2 - k := by ring
  have hright : (2 - k) - 1 = 1 - k := by ring
  simp only [m59ReflectedBusemann, hleft, hright]
  ring

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
increment is minus the original backward increment at two. -/
theorem m59ReflectedBusemann_backwardIncrement_zero (X : ℤ → ℤ) :
    m59ReflectedBusemann X 0 - m59ReflectedBusemann X (0 - 1) =
      -(X 2 - X (2 - 1)) := by
  simpa using m59ReflectedBusemann_backwardIncrement X (0 : ℤ)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
increment is minus the original backward increment at one. -/
theorem m59ReflectedBusemann_backwardIncrement_one (X : ℤ → ℤ) :
    m59ReflectedBusemann X 1 - m59ReflectedBusemann X (1 - 1) =
      -(X 1 - X (1 - 1)) := by
  simpa using m59ReflectedBusemann_backwardIncrement X (1 : ℤ)

/-- Helper toward Proposition 5.9 (prop-uihbot-sym; author ruling
recovers the original integer profile. -/
theorem m59ReflectedBusemann_involution (X : ℤ → ℤ) (hX : X 0 = 0) :
    m59ReflectedBusemann (m59ReflectedBusemann X) = X := by
  funext k
  simp only [m59ReflectedBusemann]
  have hi : 1 - (1 - k) = k := by ring
  have hone : (1 : ℤ) - 1 = 0 := by ring
  rw [hi, hone, hX]
  ring

end DirectedDistances.PaperProofs.Section5
