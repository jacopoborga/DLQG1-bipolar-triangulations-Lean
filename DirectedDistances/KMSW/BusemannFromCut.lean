module

public import DirectedDistances.KMSW.BusemannUIQBOT

/-! # Deterministic cut premises for boundary Busemann values

This file records the abstract cut and common-sequence inputs from
`lem-infty-cut` and the footnote to `thm-busemann`, and proves that a cut
vertex in a finite index window is reachable from each boundary vertex there.
Under the labelled cut and common-sequence premises, the stabilized distance
differences are constructed and shown unique. The LDP result is conditional
on the separately labelled bounded-path-length input. -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver
open scoped Classical

/-- Abstract eventual-cut input from `lem-infty-cut`
window there is a vertex that every path to every sufficiently late term of
any injective reachable sequence must visit. -/
def BusemannCutHypothesis {w : ℕ → Fin 3} (x : ℤ → PresentVertex w) : Prop :=
  ∀ K : ℕ, ∃ z : PresentVertex w,
    ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ y : ℕ → PresentVertex w, Function.Injective y →
        (∀ j, Reachable (x k) (y j)) →
          ∃ N : ℕ, ∀ j, N ≤ j → ∀ p : Path (x k) (y j), z ∈ p.vertices

/-- Abstract common-sequence input from the footnote to `thm-busemann` -/
def BusemannCommonSequenceHypothesis {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) : Prop :=
  ∀ k k' : ℤ, ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
    (∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j))

/-- Infinite injective reachable sequences from each boundary vertex, the
individual-sequence consequence of `lem-uibot-bdy` -/
def BusemannInfiniteReachabilityHypothesis {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) : Prop :=
  ∀ k : ℤ, ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
    ∀ j, Reachable (x k) (y j)

/-- The common-sequence input supplies an infinite injective reachable
sequence from each boundary vertex (`lem-uibot-bdy`, -/
theorem commonSequence_implies_infiniteReachability {w : ℕ → Fin 3}
    {x : ℤ → PresentVertex w}
    (h : BusemannCommonSequenceHypothesis x) :
    BusemannInfiniteReachabilityHypothesis x := by
  intro k
  obtain ⟨y, hy, hr⟩ := h k k
  exact ⟨y, hy, fun j => (hr j).1⟩

/-- The cut vertex selected for a finite window is reachable from each
boundary vertex in that window, provided each such vertex has an infinite
injective reachable sequence. This is the reachability obligation in the
construction in `thm-busemann` -/
theorem chosenCutVertex_reachable {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w)
    (hcut : BusemannCutHypothesis x)
    (hinf : BusemannInfiniteReachabilityHypothesis x)
    (K : ℕ) {k : ℤ} (hk₁ : -(K : ℤ) ≤ k) (hk₂ : k ≤ K) :
    Reachable (x k) (hcut K).choose := by
  have hproperty := (hcut K).choose_spec
  obtain ⟨y, hy, hyr⟩ := hinf k
  obtain ⟨N, hN⟩ := hproperty k hk₁ hk₂ y hy hyr
  obtain ⟨p⟩ := hyr N
  obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices (hN N le_rfl p)
  exact ⟨p₁⟩

private theorem reachable_suffix_of_separator {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (hab : Reachable a b)
    (hsep : ∀ p : Path a b, z ∈ p.vertices) : Reachable z b := by
  obtain ⟨p⟩ := hab
  obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices (hsep p)
  exact ⟨p₂⟩

private theorem sdp_difference_eq_of_present_separators {w : ℕ → Fin 3}
    {a a' b z : PresentVertex w}
    (hsep : ∀ p : Path a b, z ∈ p.vertices)
    (hsep' : ∀ p : Path a' b, z ∈ p.vertices)
    (haz : Reachable a z) (ha'z : Reachable a' z) (hzb : Reachable z b) :
    ((sdp a' b).toNat : ℤ) - ((sdp a b).toNat : ℤ) =
      ((sdp a' z).toNat : ℤ) - ((sdp a z).toNat : ℤ) :=
  sdp_difference_eq_of_common_separator hsep hsep' haz ha'z hzb

private noncomputable def cutSdpPotential {w : ℕ → Fin 3} (x : ℤ → PresentVertex w)
    (hcut : BusemannCutHypothesis x) (K : ℕ) (k : ℤ) : ℤ :=
  ((sdp (x k) (hcut K).choose).toNat : ℤ) -
    ((sdp (x 0) (hcut K).choose).toNat : ℤ)

private theorem cutSdpPotential_eq_of_windows {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x)
    (K L : ℕ) (k : ℤ)
    (hK₁ : -(K : ℤ) ≤ k) (hK₂ : k ≤ K)
    (hL₁ : -(L : ℤ) ≤ k) (hL₂ : k ≤ L) :
    cutSdpPotential x hcut K k = cutSdpPotential x hcut L k := by
  obtain ⟨y, hy, hyr⟩ := hcommon k 0
  obtain ⟨NKk, hKk⟩ := (hcut K).choose_spec k hK₁ hK₂ y hy (fun j => (hyr j).1)
  have hK0₁ : -(K : ℤ) ≤ 0 := by omega
  have hK0₂ : (0 : ℤ) ≤ K := Nat.cast_nonneg _
  obtain ⟨NK0, hK0⟩ := (hcut K).choose_spec 0 hK0₁ hK0₂ y hy (fun j => (hyr j).2)
  obtain ⟨NLk, hLk⟩ := (hcut L).choose_spec k hL₁ hL₂ y hy (fun j => (hyr j).1)
  have hL0₁ : -(L : ℤ) ≤ 0 := by omega
  have hL0₂ : (0 : ℤ) ≤ L := Nat.cast_nonneg _
  obtain ⟨NL0, hL0⟩ := (hcut L).choose_spec 0 hL0₁ hL0₂ y hy (fun j => (hyr j).2)
  let j := max (max NKk NK0) (max NLk NL0)
  have hjKk : NKk ≤ j := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hjK0 : NK0 ≤ j := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hjLk : NLk ≤ j := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hjL0 : NL0 ≤ j := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hKsepK : ∀ p : Path (x k) (y j), (hcut K).choose ∈ p.vertices := hKk j hjKk
  have hKsep0 : ∀ p : Path (x 0) (y j), (hcut K).choose ∈ p.vertices := hK0 j hjK0
  have hLsepK : ∀ p : Path (x k) (y j), (hcut L).choose ∈ p.vertices := hLk j hjLk
  have hLsep0 : ∀ p : Path (x 0) (y j), (hcut L).choose ∈ p.vertices := hL0 j hjL0
  have hinf := commonSequence_implies_infiniteReachability hcommon
  have hKreachK : Reachable (x k) (hcut K).choose :=
    chosenCutVertex_reachable x hcut hinf K hK₁ hK₂
  have hKreach0 : Reachable (x 0) (hcut K).choose :=
    chosenCutVertex_reachable x hcut hinf K hK0₁ hK0₂
  have hLreachK : Reachable (x k) (hcut L).choose :=
    chosenCutVertex_reachable x hcut hinf L hL₁ hL₂
  have hLreach0 : Reachable (x 0) (hcut L).choose :=
    chosenCutVertex_reachable x hcut hinf L hL0₁ hL0₂
  have hKtail : Reachable (hcut K).choose (y j) :=
    reachable_suffix_of_separator (hyr j).1 hKsepK
  have hLtail : Reachable (hcut L).choose (y j) :=
    reachable_suffix_of_separator (hyr j).1 hLsepK
  have hKdiff := sdp_difference_eq_of_present_separators hKsep0 hKsepK
    hKreach0 hKreachK hKtail
  have hLdiff := sdp_difference_eq_of_present_separators hLsep0 hLsepK
    hLreach0 hLreachK hLtail
  dsimp [cutSdpPotential]
  exact hKdiff.symm.trans hLdiff

/-- SDP splits at a present vertex visited by every present path between the -/
theorem presentSdp_eq_add_of_forall_path_mem_vertices {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (_hReach : Reachable a b)
    (hsep : ∀ p : Path a b, z ∈ p.vertices) :
    sdp a b = sdp a z + sdp z b :=
  sdp_eq_add_of_forall_mem_vertices hsep

/-- Under the labelled `lem-infty-cut` premise (the producer of
`BusemannCutHypothesis`) and the `lem-uibot-bdy` common-sequence premise, the
finite SDP differences stabilize and are uniquely normalized at zero. This
internal conditional helper follows the cut construction in
`eqn-busemann-vertex`; it is not a claim that `thm-busemann` has been proved -/
theorem existsUnique_sdpBoundaryDifference_from_cut {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x) :
    ∃! X : ℤ → ℤ, X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w, Function.Injective y →
        (∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
          ∃ N, ∀ j, N ≤ j →
            X k' - X k =
              ((sdp (x k') (y j)).toNat : ℤ) - ((sdp (x k) (y j)).toNat : ℤ) := by
  let X : ℤ → ℤ := fun k => cutSdpPotential x hcut k.natAbs k
  have hzero : X 0 = 0 := by
    simp [X, cutSdpPotential]
  have hproperty : ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w, Function.Injective y →
      (∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
        ∃ N, ∀ j, N ≤ j →
          X k' - X k =
            ((sdp (x k') (y j)).toNat : ℤ) - ((sdp (x k) (y j)).toNat : ℤ) := by
    intro k k' y hy hyr
    let K := max k.natAbs k'.natAbs
    have hkabs : k.natAbs ≤ K := Nat.le_max_left _ _
    have hk'abs : k'.natAbs ≤ K := Nat.le_max_right _ _
    have hkupper : k ≤ (k.natAbs : ℤ) := Int.le_natAbs (a := k)
    have hk'upper : k' ≤ (k'.natAbs : ℤ) := Int.le_natAbs (a := k')
    have hklower : -(k.natAbs : ℤ) ≤ k := by
      have h : -k ≤ (k.natAbs : ℤ) := by
        simpa using (Int.le_natAbs (a := -k))
      simpa using (neg_le_neg h)
    have hk'lower : -(k'.natAbs : ℤ) ≤ k' := by
      have h : -k' ≤ (k'.natAbs : ℤ) := by
        simpa using (Int.le_natAbs (a := -k'))
      simpa using (neg_le_neg h)
    have hkcast : (k.natAbs : ℤ) ≤ K := by exact_mod_cast hkabs
    have hk'cast : (k'.natAbs : ℤ) ≤ K := by exact_mod_cast hk'abs
    have hK₁ : -(K : ℤ) ≤ k := by omega
    have hK₂ : k ≤ K := le_trans hkupper (by exact_mod_cast hkabs)
    have hK'₁ : -(K : ℤ) ≤ k' := by omega
    have hK'₂ : k' ≤ K := le_trans hk'upper (by exact_mod_cast hk'abs)
    obtain ⟨Nk, hNk⟩ := (hcut K).choose_spec k hK₁ hK₂ y hy (fun j => (hyr j).1)
    obtain ⟨Nk', hNk'⟩ := (hcut K).choose_spec k' hK'₁ hK'₂ y hy (fun j => (hyr j).2)
    let j := max Nk Nk'
    have hjk : Nk ≤ j := Nat.le_max_left _ _
    have hjk' : Nk' ≤ j := Nat.le_max_right _ _
    have hsep : ∀ p : Path (x k) (y j), (hcut K).choose ∈ p.vertices := hNk j hjk
    have hsep' : ∀ p : Path (x k') (y j), (hcut K).choose ∈ p.vertices := hNk' j hjk'
    have hinf := commonSequence_implies_infiniteReachability hcommon
    have hreach : Reachable (x k) (hcut K).choose :=
      chosenCutVertex_reachable x hcut hinf K hK₁ hK₂
    have hreach' : Reachable (x k') (hcut K).choose :=
      chosenCutVertex_reachable x hcut hinf K hK'₁ hK'₂
    have htail : Reachable (hcut K).choose (y j) :=
      reachable_suffix_of_separator (hyr j).1 hsep
    have hdiff := sdp_difference_eq_of_present_separators hsep hsep' hreach hreach' htail
    have hkCanon : cutSdpPotential x hcut K k = cutSdpPotential x hcut k.natAbs k := by
      have h0₁ : -(K : ℤ) ≤ 0 := by omega
      have h0₂ : (0 : ℤ) ≤ K := Nat.cast_nonneg _
      have hkNat₁ : -((k.natAbs : ℕ) : ℤ) ≤ k := hklower
      have hkNat₂ : k ≤ k.natAbs := hkupper
      exact cutSdpPotential_eq_of_windows x hcut hcommon K k.natAbs k
        hK₁ hK₂ hkNat₁ hkNat₂
    have hk'Canon : cutSdpPotential x hcut K k' = cutSdpPotential x hcut k'.natAbs k' := by
      have hk'Nat₁ : -((k'.natAbs : ℕ) : ℤ) ≤ k' := hk'lower
      have hk'Nat₂ : k' ≤ k'.natAbs := hk'upper
      exact cutSdpPotential_eq_of_windows x hcut hcommon K k'.natAbs k'
        hK'₁ hK'₂ hk'Nat₁ hk'Nat₂
    refine ⟨j, fun m hm => ?_⟩
    have hformula : X k' - X k =
        ((sdp (x k') (hcut K).choose).toNat : ℤ) -
          ((sdp (x k) (hcut K).choose).toNat : ℤ) := by
      dsimp [X]
      rw [← hk'Canon, ← hkCanon]
      dsimp [cutSdpPotential]
      ring
    calc
      X k' - X k =
          ((sdp (x k') (hcut K).choose).toNat : ℤ) -
            ((sdp (x k) (hcut K).choose).toNat : ℤ) := hformula
      _ = ((sdp (x k') (y m)).toNat : ℤ) -
            ((sdp (x k) (y m)).toNat : ℤ) := by
        have hsep_m : ∀ p : Path (x k) (y m), (hcut K).choose ∈ p.vertices := hNk m (le_trans hjk hm)
        have hsep'_m : ∀ p : Path (x k') (y m), (hcut K).choose ∈ p.vertices := hNk' m (le_trans hjk' hm)
        have htail_m : Reachable (hcut K).choose (y m) :=
          reachable_suffix_of_separator (hyr m).1 hsep_m
        exact (sdp_difference_eq_of_present_separators hsep_m hsep'_m
          (chosenCutVertex_reachable x hcut hinf K hK₁ hK₂)
          (chosenCutVertex_reachable x hcut hinf K hK'₁ hK'₂) htail_m).symm
  refine ⟨X, ⟨hzero, hproperty⟩, ?_⟩
  intro Y hY
  funext k
  obtain ⟨y, hy, hyr⟩ := hcommon 0 k
  obtain ⟨NX, hNX⟩ := hproperty 0 k y hy hyr
  obtain ⟨NY, hNY⟩ := hY.2 0 k y hy hyr
  let j := max NX NY
  have hjX : NX ≤ j := Nat.le_max_left _ _
  have hjY : NY ≤ j := Nat.le_max_right _ _
  have hXeq := hNX j hjX
  have hYeq := hNY j hjY
  have hXval : X k = ((sdp (x k) (y j)).toNat : ℤ) -
      ((sdp (x 0) (y j)).toNat : ℤ) := by
    simpa [hzero] using hXeq
  have hYval : Y k = ((sdp (x k) (y j)).toNat : ℤ) -
      ((sdp (x 0) (y j)).toNat : ℤ) := by
    simpa [hY.1] using hYeq
  exact hYval.trans hXval.symm

/-- Internal LDP finiteness premise for the cut-based Busemann construction.
Its intended producer is the concurrent data
`KMSW/ActiveTimeMonotone.lean`: activation times increase along present paths,
so local finiteness bounds the paths into each fixed vertex. This file does not
import or prove that producer. -/
def PresentPathLengthsBounded {w : ℕ → Fin 3} : Prop :=
  ∀ a b : PresentVertex w, Reachable a b → BddAbove (pathLengths a b)

/-- Finite natural longest-path distance on a reachable pair. Its boundedness
input is the labelled premise whose intended producer is
`KMSW/ActiveTimeMonotone.lean`; requiring reachability avoids assigning a
numeric value to unreachable pairs. -/
noncomputable def presentLdpFiniteNat {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) : ℕ :=
  (exists_isLongest_of_bddAbove (hbound a b hr) hr).choose.length

/-- Characterization of `presentLdpFiniteNat` by every actual longest path.
This consumes `PresentPathLengthsBounded`, whose intended producer is
`KMSW/ActiveTimeMonotone.lean`. -/
theorem presentLdpFiniteNat_eq_length {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) {p : Path a b} (hp : IsLongest p) :
    presentLdpFiniteNat hbound hr = p.length := by
  dsimp [presentLdpFiniteNat]
  let q := (exists_isLongest_of_bddAbove (hbound a b hr) hr).choose
  have hq : IsLongest q := (exists_isLongest_of_bddAbove (hbound a b hr) hr).choose_spec
  exact Nat.le_antisymm (hp q) (hq p)

private theorem presentLdpFiniteNat_proof_irrel {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr hr' : Reachable a b) : presentLdpFiniteNat hbound hr = presentLdpFiniteNat hbound hr' := by
  exact congrArg (fun h : Reachable a b => presentLdpFiniteNat hbound h)
    (Subsingleton.elim hr hr')

private theorem presentLdp_eq_natCast {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) :
    presentLdp a b = ((presentLdpFiniteNat hbound hr : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a b hr) hr
  rw [presentLdp_eq_length hp, presentLdpFiniteNat_eq_length hbound hr hp]

private theorem presentLdpFiniteNat_eq_add_of_forall_path_mem_vertices
    {w : ℕ → Fin 3} {a z b : PresentVertex w}
    (hbound : PresentPathLengthsBounded (w := w))
    (hsep : ∀ p : Path a b, z ∈ p.vertices)
    (haz : Reachable a z) (hzb : Reachable z b) :
    presentLdpFiniteNat hbound (by
      obtain ⟨p⟩ := haz
      obtain ⟨q⟩ := hzb
      exact ⟨p.comp q⟩) = presentLdpFiniteNat hbound haz + presentLdpFiniteNat hbound hzb := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a z haz) haz
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hbound z b hzb) hzb
  have hpq : IsLongest (p.comp q) := hp.comp_of_forall_mem_vertices hq hsep
  rw [presentLdpFiniteNat_eq_length hbound _ hpq,
    presentLdpFiniteNat_eq_length hbound haz hp,
    presentLdpFiniteNat_eq_length hbound hzb hq, Path.length_comp]

private theorem presentLdpFiniteNat_difference_eq_of_present_separators
    {w : ℕ → Fin 3} {a a' b z : PresentVertex w}
    (hbound : PresentPathLengthsBounded (w := w))
    (hsep : ∀ p : Path a b, z ∈ p.vertices)
    (hsep' : ∀ p : Path a' b, z ∈ p.vertices)
    (hab : Reachable a b) (ha'b : Reachable a' b)
    (haz : Reachable a z) (ha'z : Reachable a' z) (hzb : Reachable z b) :
    (presentLdpFiniteNat hbound ha'b : ℤ) - (presentLdpFiniteNat hbound hab : ℤ) =
      (presentLdpFiniteNat hbound ha'z : ℤ) - (presentLdpFiniteNat hbound haz : ℤ) := by
  have hsplit : presentLdpFiniteNat hbound hab = presentLdpFiniteNat hbound haz + presentLdpFiniteNat hbound hzb := by
    have h := presentLdpFiniteNat_eq_add_of_forall_path_mem_vertices hbound hsep haz hzb
    exact h
  have hsplit' : presentLdpFiniteNat hbound ha'b = presentLdpFiniteNat hbound ha'z + presentLdpFiniteNat hbound hzb := by
    have h := presentLdpFiniteNat_eq_add_of_forall_path_mem_vertices hbound hsep' ha'z hzb
    exact h
  have hsplitInt : (presentLdpFiniteNat hbound hab : ℤ) =
      (presentLdpFiniteNat hbound haz : ℤ) + (presentLdpFiniteNat hbound hzb : ℤ) := by
    exact_mod_cast hsplit
  have hsplit'Int : (presentLdpFiniteNat hbound ha'b : ℤ) =
      (presentLdpFiniteNat hbound ha'z : ℤ) + (presentLdpFiniteNat hbound hzb : ℤ) := by
    exact_mod_cast hsplit'
  rw [hsplit'Int, hsplitInt]
  ring

/-- Under `PresentPathLengthsBounded` (whose intended producer is
`KMSW/ActiveTimeMonotone.lean`), LDP splits at a present vertex visited by
every path. The path separator supplies reachability of both pieces -/
theorem presentLdp_eq_add_of_forall_path_mem_vertices {w : ℕ → Fin 3}
    {a b z : PresentVertex w} (hbound : PresentPathLengthsBounded (w := w))
    (hReach : Reachable a b) (hsep : ∀ p : Path a b, z ∈ p.vertices) :
    presentLdp a b = presentLdp a z + presentLdp z b := by
  have hReach' := hReach
  obtain ⟨p⟩ := hReach
  obtain ⟨p₁, p₂, _⟩ := p.exists_eq_comp_of_mem_vertices (hsep p)
  have haz : Reachable a z := ⟨p₁⟩
  have hzb : Reachable z b := ⟨p₂⟩
  have hsum := presentLdpFiniteNat_eq_add_of_forall_path_mem_vertices hbound hsep haz hzb
  have hnat : presentLdpFiniteNat hbound hReach' = presentLdpFiniteNat hbound haz +
      presentLdpFiniteNat hbound hzb := by
    simpa only using hsum
  rw [presentLdp_eq_natCast hbound hReach',
    presentLdp_eq_natCast hbound haz, presentLdp_eq_natCast hbound hzb,
    ← WithBot.coe_add]
  apply congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
  rw [← ENat.natCast_add]
  exact congrArg (fun n : ℕ => (n : ℕ∞)) hnat

private theorem int_natAbs_bounds (k : ℤ) :
    -(k.natAbs : ℤ) ≤ k ∧ k ≤ k.natAbs := by
  constructor
  · have h : -k ≤ (k.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -k))
    simpa using (neg_le_neg h)
  · exact Int.le_natAbs (a := k)

private noncomputable def cutLdpPotential {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x)
    (hbound : PresentPathLengthsBounded (w := w)) (K : ℕ) (k : ℤ)
    (hk₁ : -(K : ℤ) ≤ k) (hk₂ : k ≤ K) : ℤ :=
  let hinf := commonSequence_implies_infiniteReachability hcommon
  ((presentLdpFiniteNat hbound (chosenCutVertex_reachable x hcut hinf K hk₁ hk₂) : ℤ) -
    (presentLdpFiniteNat hbound
      (chosenCutVertex_reachable x hcut hinf K (k := 0) (by omega) (by omega)) : ℤ))

private theorem cutLdpPotential_eq_of_windows {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x)
    (hbound : PresentPathLengthsBounded (w := w))
    (K L : ℕ) (k : ℤ)
    (hK₁ : -(K : ℤ) ≤ k) (hK₂ : k ≤ K)
    (hL₁ : -(L : ℤ) ≤ k) (hL₂ : k ≤ L) :
    cutLdpPotential x hcut hcommon hbound K k hK₁ hK₂ =
      cutLdpPotential x hcut hcommon hbound L k hL₁ hL₂ := by
  obtain ⟨y, hy, hyr⟩ := hcommon k 0
  obtain ⟨NKk, hKk⟩ := (hcut K).choose_spec k hK₁ hK₂ y hy (fun j => (hyr j).1)
  have hK0₁ : -(K : ℤ) ≤ 0 := by omega
  have hK0₂ : (0 : ℤ) ≤ K := Nat.cast_nonneg _
  obtain ⟨NK0, hK0⟩ := (hcut K).choose_spec 0 hK0₁ hK0₂ y hy (fun j => (hyr j).2)
  obtain ⟨NLk, hLk⟩ := (hcut L).choose_spec k hL₁ hL₂ y hy (fun j => (hyr j).1)
  have hL0₁ : -(L : ℤ) ≤ 0 := by omega
  have hL0₂ : (0 : ℤ) ≤ L := Nat.cast_nonneg _
  obtain ⟨NL0, hL0⟩ := (hcut L).choose_spec 0 hL0₁ hL0₂ y hy (fun j => (hyr j).2)
  let j := max (max NKk NK0) (max NLk NL0)
  have hjKk : NKk ≤ j := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hjK0 : NK0 ≤ j := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hjLk : NLk ≤ j := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hjL0 : NL0 ≤ j := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hKsepK : ∀ p : Path (x k) (y j), (hcut K).choose ∈ p.vertices := hKk j hjKk
  have hKsep0 : ∀ p : Path (x 0) (y j), (hcut K).choose ∈ p.vertices := hK0 j hjK0
  have hLsepK : ∀ p : Path (x k) (y j), (hcut L).choose ∈ p.vertices := hLk j hjLk
  have hLsep0 : ∀ p : Path (x 0) (y j), (hcut L).choose ∈ p.vertices := hL0 j hjL0
  let hinf := commonSequence_implies_infiniteReachability hcommon
  have hKreachK : Reachable (x k) (hcut K).choose :=
    chosenCutVertex_reachable x hcut hinf K hK₁ hK₂
  have hKreach0 : Reachable (x 0) (hcut K).choose :=
    chosenCutVertex_reachable x hcut hinf K hK0₁ hK0₂
  have hLreachK : Reachable (x k) (hcut L).choose :=
    chosenCutVertex_reachable x hcut hinf L hL₁ hL₂
  have hLreach0 : Reachable (x 0) (hcut L).choose :=
    chosenCutVertex_reachable x hcut hinf L hL0₁ hL0₂
  have hKtail : Reachable (hcut K).choose (y j) :=
    reachable_suffix_of_separator (hyr j).1 hKsepK
  have hLtail : Reachable (hcut L).choose (y j) :=
    reachable_suffix_of_separator (hyr j).1 hLsepK
  have hKdiff := presentLdpFiniteNat_difference_eq_of_present_separators hbound
    hKsep0 hKsepK (hyr j).2 (hyr j).1 hKreach0 hKreachK hKtail
  have hLdiff := presentLdpFiniteNat_difference_eq_of_present_separators hbound
    hLsep0 hLsepK (hyr j).2 (hyr j).1 hLreach0 hLreachK hLtail
  have hKpot : cutLdpPotential x hcut hcommon hbound K k hK₁ hK₂ =
      (presentLdpFiniteNat hbound hKreachK : ℤ) - (presentLdpFiniteNat hbound hKreach0 : ℤ) := by
    dsimp [cutLdpPotential]
  have hLpot : cutLdpPotential x hcut hcommon hbound L k hL₁ hL₂ =
      (presentLdpFiniteNat hbound hLreachK : ℤ) - (presentLdpFiniteNat hbound hLreach0 : ℤ) := by
    dsimp [cutLdpPotential]
  exact hKpot.trans (hKdiff.symm.trans (hLdiff.trans hLpot.symm))

/-- Under the `lem-infty-cut` and `lem-uibot-bdy` inputs, together with
`PresentPathLengthsBounded` from the intended producer
`KMSW/ActiveTimeMonotone.lean`, the finite LDP differences stabilize and are
uniquely normalized at zero. This is an internal conditional helper, not a
claim of `thm-busemann` from its manuscript-level inputs -/
theorem existsUnique_ldpBoundaryDifference_from_cut {w : ℕ → Fin 3}
    (x : ℤ → PresentVertex w) (hcut : BusemannCutHypothesis x)
    (hcommon : BusemannCommonSequenceHypothesis x)
    (hbound : PresentPathLengthsBounded (w := w)) :
    ∃! X : ℤ → ℤ, X 0 = 0 ∧
      ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w,
        (hy : Function.Injective y) →
        (hyr : ∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
          ∃ N, ∀ j, N ≤ j →
            X k' - X k =
              (presentLdpFiniteNat hbound (hyr j).2 : ℤ) -
                (presentLdpFiniteNat hbound (hyr j).1 : ℤ) := by
  let X : ℤ → ℤ := fun k =>
    cutLdpPotential x hcut hcommon hbound k.natAbs k
      (int_natAbs_bounds k).1 (int_natAbs_bounds k).2
  have hzero : X 0 = 0 := by
    simp [X, cutLdpPotential]
  have hproperty : ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w,
      (hy : Function.Injective y) →
      (hyr : ∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
        ∃ N, ∀ j, N ≤ j →
          X k' - X k =
            (presentLdpFiniteNat hbound (hyr j).2 : ℤ) -
              (presentLdpFiniteNat hbound (hyr j).1 : ℤ) := by
    intro k k' y hy hyr
    let K := max k.natAbs k'.natAbs
    have hkabs : k.natAbs ≤ K := Nat.le_max_left _ _
    have hk'abs : k'.natAbs ≤ K := Nat.le_max_right _ _
    have hkcast : (k.natAbs : ℤ) ≤ K := by exact_mod_cast hkabs
    have hk'cast : (k'.natAbs : ℤ) ≤ K := by exact_mod_cast hk'abs
    have hkBounds := int_natAbs_bounds k
    have hk'Bounds := int_natAbs_bounds k'
    have hK₁ : -(K : ℤ) ≤ k := by omega
    have hK₂ : k ≤ K := le_trans hkBounds.2 (by exact_mod_cast hkabs)
    have hK'₁ : -(K : ℤ) ≤ k' := by omega
    have hK'₂ : k' ≤ K := le_trans hk'Bounds.2 (by exact_mod_cast hk'abs)
    obtain ⟨Nk, hNk⟩ := (hcut K).choose_spec k hK₁ hK₂ y hy (fun j => (hyr j).1)
    obtain ⟨Nk', hNk'⟩ := (hcut K).choose_spec k' hK'₁ hK'₂ y hy (fun j => (hyr j).2)
    let j := max Nk Nk'
    have hjk : Nk ≤ j := Nat.le_max_left _ _
    have hjk' : Nk' ≤ j := Nat.le_max_right _ _
    have hsep : ∀ p : Path (x k) (y j), (hcut K).choose ∈ p.vertices := hNk j hjk
    have hsep' : ∀ p : Path (x k') (y j), (hcut K).choose ∈ p.vertices := hNk' j hjk'
    let hinf := commonSequence_implies_infiniteReachability hcommon
    have hreach : Reachable (x k) (hcut K).choose :=
      chosenCutVertex_reachable x hcut hinf K hK₁ hK₂
    have hreach' : Reachable (x k') (hcut K).choose :=
      chosenCutVertex_reachable x hcut hinf K hK'₁ hK'₂
    have htail : Reachable (hcut K).choose (y j) :=
      reachable_suffix_of_separator (hyr j).1 hsep
    have hdiff := presentLdpFiniteNat_difference_eq_of_present_separators hbound
      hsep hsep' (hyr j).1 (hyr j).2 hreach hreach' htail
    have hkCanon : cutLdpPotential x hcut hcommon hbound K k hK₁ hK₂ =
        cutLdpPotential x hcut hcommon hbound k.natAbs k hkBounds.1 hkBounds.2 :=
      cutLdpPotential_eq_of_windows x hcut hcommon hbound K k.natAbs k
        hK₁ hK₂ hkBounds.1 hkBounds.2
    have hk'Canon : cutLdpPotential x hcut hcommon hbound K k' hK'₁ hK'₂ =
        cutLdpPotential x hcut hcommon hbound k'.natAbs k' hk'Bounds.1 hk'Bounds.2 :=
      cutLdpPotential_eq_of_windows x hcut hcommon hbound K k'.natAbs k'
        hK'₁ hK'₂ hk'Bounds.1 hk'Bounds.2
    refine ⟨j, fun m hm => ?_⟩
    have hformula : X k' - X k =
        (presentLdpFiniteNat hbound hreach' : ℤ) -
          (presentLdpFiniteNat hbound hreach : ℤ) := by
      dsimp [X]
      rw [← hk'Canon, ← hkCanon]
      dsimp [cutLdpPotential]
      ring
    calc
      X k' - X k =
          (presentLdpFiniteNat hbound hreach' : ℤ) -
            (presentLdpFiniteNat hbound hreach : ℤ) := hformula
      _ = (presentLdpFiniteNat hbound (hyr m).2 : ℤ) -
            (presentLdpFiniteNat hbound (hyr m).1 : ℤ) := by
        have hsep_m : ∀ p : Path (x k) (y m), (hcut K).choose ∈ p.vertices :=
          hNk m (le_trans hjk hm)
        have hsep'_m : ∀ p : Path (x k') (y m), (hcut K).choose ∈ p.vertices :=
          hNk' m (le_trans hjk' hm)
        have htail_m : Reachable (hcut K).choose (y m) :=
          reachable_suffix_of_separator (hyr m).1 hsep_m
        exact (presentLdpFiniteNat_difference_eq_of_present_separators hbound
          hsep_m hsep'_m (hyr m).1 (hyr m).2
          (chosenCutVertex_reachable x hcut hinf K hK₁ hK₂)
          (chosenCutVertex_reachable x hcut hinf K hK'₁ hK'₂) htail_m).symm
  refine ⟨X, ⟨hzero, hproperty⟩, ?_⟩
  intro Y hY
  funext k
  obtain ⟨y, hy, hyr⟩ := hcommon 0 k
  obtain ⟨NX, hNX⟩ := hproperty 0 k y hy hyr
  obtain ⟨NY, hNY⟩ := hY.2 0 k y hy hyr
  let j := max NX NY
  have hjX : NX ≤ j := Nat.le_max_left _ _
  have hjY : NY ≤ j := Nat.le_max_right _ _
  have hXeq := hNX j hjX
  have hYeq := hNY j hjY
  have hXval : X k =
      (presentLdpFiniteNat hbound (hyr j).2 : ℤ) -
        (presentLdpFiniteNat hbound (hyr j).1 : ℤ) := by
    simpa [hzero] using hXeq
  have hYval : Y k =
      (presentLdpFiniteNat hbound (hyr j).2 : ℤ) -
        (presentLdpFiniteNat hbound (hyr j).1 : ℤ) := by
    simpa [hY.1] using hYeq
  exact hYval.trans hXval.symm

end DirectedDistances.KMSW
