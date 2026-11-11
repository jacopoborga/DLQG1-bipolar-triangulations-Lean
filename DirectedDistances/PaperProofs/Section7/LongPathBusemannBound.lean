module

public import DirectedDistances.KMSW.BusemannReduction
public import DirectedDistances.KMSW.BusemannBoundaryM0













public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem presentLdpFiniteNat_ge_length {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) (q : Path a b) :
    q.length ≤ presentLdpFiniteNat hbound hr := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a b hr) hr
  rw [presentLdpFiniteNat_eq_length hbound hr hp]
  exact hp q

private theorem presentLdpFiniteNat_ge_of_path {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b c : PresentVertex w}
    (q : Path a b) (hrbc : Reachable b c) (hrac : Reachable a c) :
    presentLdpFiniteNat hbound hrbc ≤ presentLdpFiniteNat hbound hrac := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound b c hrbc) hrbc
  have hlen := presentLdpFiniteNat_ge_length hbound hrac (q.comp p)
  rw [Path.length_comp] at hlen
  rw [presentLdpFiniteNat_eq_length hbound hrbc hp]
  omega










theorem ldpPrefix_ge_boundaryBusemannDiff {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w))
    (x : ℤ → PresentVertex w) (X : ℤ → ℤ)
    (hX : IsBoundaryBusemannLDP hbound x X)
    {i j : ℤ} {z : PresentVertex w}
    (y : ℕ → PresentVertex w) (hy : Function.Injective y)
    (hreach : ∀ r, Reachable (x i) (y r) ∧ Reachable (x j) (y r))
    (hzy : ∀ r, Reachable z (y r)) (q : Path (x j) z) (T : ℕ)
    (hdecomp : ∃ N, ∀ r, N ≤ r →
      presentLdpFiniteNat hbound (hreach r).1 =
        T + presentLdpFiniteNat hbound (hzy r)) :
    X i - X j ≤ (T : ℤ) := by
  obtain ⟨Ndecomp, hdecomp⟩ := hdecomp
  obtain ⟨Nbuse, hbuse⟩ := hX.2 i j y hy hreach
  let r := max Ndecomp Nbuse
  have hdecompR := hdecomp r (le_max_left _ _)
  have hbuseR := hbuse r (le_max_right _ _)
  have hI : Reachable (x i) (y r) := (hreach r).1
  have hJ : Reachable (x j) (y r) := (hreach r).2
  have hZ : Reachable z (y r) := hzy r
  have hJZ : presentLdpFiniteNat hbound hZ ≤
      presentLdpFiniteNat hbound hJ :=
    presentLdpFiniteNat_ge_of_path hbound q hZ hJ
  have hbus : X j - X i =
      (presentLdpFiniteNat hbound hJ : ℤ) -
        (presentLdpFiniteNat hbound hI : ℤ) := hbuseR
  have hdiff : X i - X j =
      (presentLdpFiniteNat hbound hI : ℤ) -
        (presentLdpFiniteNat hbound hJ : ℤ) := by
    linarith
  have hdecompZ : (presentLdpFiniteNat hbound hI : ℤ) =
      (T : ℤ) + (presentLdpFiniteNat hbound hZ : ℤ) := by
    exact_mod_cast hdecompR
  have hJZ' : (presentLdpFiniteNat hbound hZ : ℤ) ≤
      (presentLdpFiniteNat hbound hJ : ℤ) := by
    exact_mod_cast hJZ
  linarith

end DirectedDistances.PaperProofs.Section7
