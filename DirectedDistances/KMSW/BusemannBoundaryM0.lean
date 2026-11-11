module

public import DirectedDistances.KMSW.BusemannReduction
public import DirectedDistances.KMSW.UIBOTBoundaryM0
public import DirectedDistances.RandomWalk.CellSDPLowerBdy

/-! # Boundary inequalities for the Busemann characterization on `M₀`

Deterministic consequences of the `thm-busemann` characterization
`x_k = boundaryVertex w h k`: the triangle-type inequality of `lem-sdp-tri`
bounds `item-busemann-pos` of `thm-busemann-property`

Everything here is conditional on the labelled `thm-busemann` premises: window
finite avoidance (producer `lem-infty-cut`) and common reachable injective
sequences (producer: the footnote to `thm-busemann` and `lem-uibot-bdy`). The
file does not prove `thm-busemann`. LDP is `-∞` and SDP is `+∞` on unreachable
pairs; only finite values on reachable pairs (`toNat`, `presentLdpFiniteNat`)
are used. -/

@[expose] public section
namespace DirectedDistances.KMSW

open Quiver

/-- The boundary vertex `x_k` as a present vertex -/
noncomputable def boundaryPresentVertex (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (k : ℤ) :
    PresentVertex w :=
  ⟨boundaryVertex w h k⟩

/-- The SDP case of the `thm-busemann` characterization
at `0`, and every increment is eventually the SDP difference along any common
reachable injective sequence. -/
def IsBoundaryBusemannSDP {w : ℕ → Fin 3} (x : ℤ → PresentVertex w)
    (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w, Function.Injective y →
      (∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
        ∃ N, ∀ j, N ≤ j →
          X k' - X k =
            ((sdp (x k') (y j)).toNat : ℤ) - ((sdp (x k) (y j)).toNat : ℤ)

/-- The LDP case of the `thm-busemann` characterization
bounded-path-length witness `hbound` (`PresentPathLengthsBounded`, produced
under local finiteness by `present_pathLengths_bddAbove`). -/
def IsBoundaryBusemannLDP {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) (x : ℤ → PresentVertex w)
    (X : ℤ → ℤ) : Prop :=
  X 0 = 0 ∧
    ∀ k k' : ℤ, ∀ y : ℕ → PresentVertex w,
      (hy : Function.Injective y) →
      (hyr : ∀ j, Reachable (x k) (y j) ∧ Reachable (x k') (y j)) →
        ∃ N, ∀ j, N ≤ j →
          X k' - X k =
            (presentLdpFiniteNat hbound (hyr j).2 : ℤ) -
              (presentLdpFiniteNat hbound (hyr j).1 : ℤ)

private theorem presentLdpFiniteNat_ge_length {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) (q : Path a b) :
    q.length ≤ presentLdpFiniteNat hbound hr := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a b hr) hr
  rw [presentLdpFiniteNat_eq_length hbound hr hp]
  exact hp q

private theorem presentLdpFiniteNat_add_le {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b c : PresentVertex w}
    (hab : Reachable a b) (hbc : Reachable b c) (hac : Reachable a c) :
    presentLdpFiniteNat hbound hab + presentLdpFiniteNat hbound hbc ≤
      presentLdpFiniteNat hbound hac := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a b hab) hab
  obtain ⟨q, hq⟩ := exists_isLongest_of_bddAbove (hbound b c hbc) hbc
  have h := presentLdpFiniteNat_ge_length hbound hac (p.comp q)
  rw [Path.length_comp] at h
  rw [presentLdpFiniteNat_eq_length hbound hab hp,
    presentLdpFiniteNat_eq_length hbound hbc hq]
  exact h

private theorem sdp_toNat_le_add_one_of_edge {w : ℕ → Fin 3}
    {a b c : PresentVertex w} (hac : Reachable a c) (hbc : Reachable b c)
    (hab : sdp a b ≤ 1) :
    ((sdp a c).toNat : ℤ) ≤ ((sdp b c).toNat : ℤ) + 1 := by
  have h1 : sdp a c ≤ 1 + sdp b c :=
    (sdp_triangle a b c).trans (add_le_add hab le_rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (present_sdp_ne_top hbc)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (present_sdp_ne_top hac)
  rw [← hn, ← hm] at h1
  have h2 : m ≤ 1 + n := by exact_mod_cast h1
  rw [← hn, ← hm]
  simp only [ENat.toNat_natCast]
  omega

private theorem boundary_edge_path (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    {k : ℤ} (hk : 1 ≤ k) :
    ∃ p : Path (boundaryPresentVertex w h (k - 1)) (boundaryPresentVertex w h k),
      p.length = 1 := by
  obtain ⟨e, hp, hw, he⟩ := boundaryVertex_nonneg_successor_edge w h
    (k := k - 1) (by omega)
  have he' : edgeEast w e = boundaryVertex w h k := by
    simpa only [sub_add_cancel] using he
  exact ⟨Path.nil.cons ⟨e, hp, hw, he'⟩, rfl⟩

/-- Busemann function `X` in the SDP sense satisfies `X l - X k ≤ SDP(x_l, x_k)`.
The hypothesis `hy` is the common reachable injective sequence of the footnote
to `thm-busemann` (producer: `lem-uibot-bdy`); it is a labelled premise, not
proved here. Finiteness of `SDP(x_l, x_k)` comes from
`boundaryVertex_nonneg_reachable`. -/
theorem boundaryBusemannSDP_sub_le_sdp (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {X : ℤ → ℤ}
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    {l k : ℤ} (hl : 0 ≤ l) (hlk : l < k)
    (hy : ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (boundaryPresentVertex w h l) (y j) ∧
        Reachable (boundaryPresentVertex w h k) (y j)) :
    X l - X k ≤
      ((sdp (boundaryPresentVertex w h l) (boundaryPresentVertex w h k)).toNat : ℤ) := by
  obtain ⟨y, hyi, hyr⟩ := hy
  obtain ⟨N, hN⟩ := hX.2 l k y hyi hyr
  exact present_sdp_ge_of_busemann_identity (X l) (X k)
    (boundaryVertex_nonneg_reachable w h hl hlk.le) (hyr N).2 (hN N le_rfl)

/-- `0 ≤ l < k` and a Busemann function `X` in the LDP sense,
`LDP(x_l, x_k) ≤ X l - X k`. Finiteness of `LDP(x_l, x_k)` uses
`boundaryVertex_nonneg_reachable`; `hy` is the labelled common-sequence premise
(footnote to `thm-busemann`, producer `lem-uibot-bdy`). The proof concatenates
a longest `x_l → x_k` path with a longest `x_k → y_j` path. -/
theorem boundaryBusemannLDP_ldp_le_sub (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hbound : PresentPathLengthsBounded (w := w)) {X : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound (boundaryPresentVertex w h) X)
    {l k : ℤ} (hl : 0 ≤ l) (hlk : l < k)
    (hy : ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (boundaryPresentVertex w h l) (y j) ∧
        Reachable (boundaryPresentVertex w h k) (y j)) :
    (presentLdpFiniteNat hbound
      (boundaryVertex_nonneg_reachable w h hl hlk.le :
        Reachable (boundaryPresentVertex w h l) (boundaryPresentVertex w h k)) : ℤ) ≤
      X l - X k := by
  have hr : Reachable (boundaryPresentVertex w h l) (boundaryPresentVertex w h k) :=
    boundaryVertex_nonneg_reachable w h hl hlk.le
  obtain ⟨y, hyi, hyr⟩ := hy
  obtain ⟨N, hN⟩ := hX.2 l k y hyi hyr
  have hbus := hN N le_rfl
  have hadd := presentLdpFiniteNat_add_le hbound hr (hyr N).2 (hyr N).1
  have hadd' : (presentLdpFiniteNat hbound hr : ℤ) +
      (presentLdpFiniteNat hbound (hyr N).2 : ℤ) ≤
        (presentLdpFiniteNat hbound (hyr N).1 : ℤ) := by exact_mod_cast hadd
  have hfinal : (presentLdpFiniteNat hbound hr : ℤ) ≤ X l - X k := by linarith
  exact hfinal

/-- `k ≥ 1`, `X k - X (k-1) ≥ -1`, from the present edge `x_{k-1} → x_k`
(`boundaryVertex_nonneg_successor_edge`). `hy` is the labelled common-sequence
premise for `(k-1, k)`. -/
theorem boundaryBusemannSDP_succ_ge (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) {X : ℤ → ℤ}
    (hX : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X)
    {k : ℤ} (hk : 1 ≤ k)
    (hy : ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (boundaryPresentVertex w h (k - 1)) (y j) ∧
        Reachable (boundaryPresentVertex w h k) (y j)) :
    -1 ≤ X k - X (k - 1) := by
  obtain ⟨y, hyi, hyr⟩ := hy
  obtain ⟨N, hN⟩ := hX.2 (k - 1) k y hyi hyr
  obtain ⟨p, hp⟩ := boundary_edge_path w h hk
  have hab : sdp (boundaryPresentVertex w h (k - 1)) (boundaryPresentVertex w h k) ≤ 1 := by
    have := sdp_le_length p
    rw [hp] at this
    exact_mod_cast this
  have hle := sdp_toNat_le_add_one_of_edge (hyr N).1 (hyr N).2 hab
  have hbus := hN N le_rfl
  linarith

/-- `k ≥ 1`, `X k - X (k-1) ≤ -1`, from the present edge `x_{k-1} → x_k`, which has
length `1 ≤ LDP(x_{k-1}, x_k)`. `hy` is the labelled common-sequence premise for
`(k-1, k)`. -/
theorem boundaryBusemannLDP_succ_le (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (hbound : PresentPathLengthsBounded (w := w)) {X : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound (boundaryPresentVertex w h) X)
    {k : ℤ} (hk : 1 ≤ k)
    (hy : ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      ∀ j, Reachable (boundaryPresentVertex w h (k - 1)) (y j) ∧
        Reachable (boundaryPresentVertex w h k) (y j)) :
    X k - X (k - 1) ≤ -1 := by
  obtain ⟨y, hyi, hyr⟩ := hy
  obtain ⟨N, hN⟩ := hX.2 (k - 1) k y hyi hyr
  obtain ⟨p, hp⟩ := boundary_edge_path w h hk
  have hab : Reachable (boundaryPresentVertex w h (k - 1)) (boundaryPresentVertex w h k) :=
    ⟨p⟩
  have hone : 1 ≤ presentLdpFiniteNat hbound hab := by
    have := presentLdpFiniteNat_ge_length hbound hab p
    rwa [hp] at this
  have hadd := presentLdpFiniteNat_add_le hbound hab (hyr N).2 (hyr N).1
  have hadd' : (presentLdpFiniteNat hbound hab : ℤ) +
      (presentLdpFiniteNat hbound (hyr N).2 : ℤ) ≤
        (presentLdpFiniteNat hbound (hyr N).1 : ℤ) := by exact_mod_cast hadd
  have hone' : (1 : ℤ) ≤ presentLdpFiniteNat hbound hab := by exact_mod_cast hone
  have hbus := hN N le_rfl
  linarith

/-- Conditional on window finite avoidance (producer `lem-infty-cut`) and the
common-sequence premise (producer: the footnote to `thm-busemann` and
`lem-uibot-bdy`), the SDP Busemann function on the boundary vertices exists,
is unique, and satisfies `lem-sdp-tri` and `item-busemann-pos`. This does not
prove `thm-busemann`. -/
theorem boundaryBusemannSDP_properties (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
        FiniteAvoidance (boundaryPresentVertex w h k) z)
    (hcommon : BusemannCommonSequenceHypothesis (boundaryPresentVertex w h)) :
    ∃ X : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h) X ∧
      (∀ X' : ℤ → ℤ, IsBoundaryBusemannSDP (boundaryPresentVertex w h) X' → X' = X) ∧
      (∀ l k : ℤ, 0 ≤ l → l < k →
        X l - X k ≤
          ((sdp (boundaryPresentVertex w h l) (boundaryPresentVertex w h k)).toNat : ℤ)) ∧
      (∀ k : ℤ, 1 ≤ k → -1 ≤ X k - X (k - 1)) := by
  obtain ⟨X, hX, huniq⟩ :=
    existsUnique_sdpBusemann_of_finiteAvoidance w (boundaryPresentVertex w h) havoid hcommon
  have hX' : IsBoundaryBusemannSDP (boundaryPresentVertex w h) X := hX
  refine ⟨X, hX', fun X' hX'' => huniq X' hX'', ?_, ?_⟩
  · intro l k hl hlk
    exact boundaryBusemannSDP_sub_le_sdp w h hX' hl hlk (by
      obtain ⟨y, hy, hr⟩ := hcommon l k
      exact ⟨y, hy, hr⟩)
  · intro k hk
    exact boundaryBusemannSDP_succ_ge w h hX' hk (by
      obtain ⟨y, hy, hr⟩ := hcommon (k - 1) k
      exact ⟨y, hy, hr⟩)

/-- Conditional on local finiteness (`hfin`), window finite avoidance (producer
`lem-infty-cut`) and the common-sequence premise (producer: the footnote to
`thm-busemann` and `lem-uibot-bdy`), the LDP Busemann function on the boundary
vertices exists, is unique, and satisfies the LDP analogue of `lem-sdp-tri` and
`item-busemann-pos`. This does not prove `thm-busemann`. -/
theorem boundaryBusemannLDP_properties (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (h : BoundaryHitWitnesses w)
    (havoid : ∀ K : ℕ, ∃ z : PresentVertex w,
      ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
        FiniteAvoidance (boundaryPresentVertex w h k) z)
    (hcommon : BusemannCommonSequenceHypothesis (boundaryPresentVertex w h)) :
    ∃ X : ℤ → ℤ,
      IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin)
        (boundaryPresentVertex w h) X ∧
      (∀ X' : ℤ → ℤ,
        IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin)
          (boundaryPresentVertex w h) X' → X' = X) ∧
      (∀ l k : ℤ, 0 ≤ l → l < k →
        ∀ hr : Reachable (boundaryPresentVertex w h l) (boundaryPresentVertex w h k),
          (presentLdpFiniteNat (presentPathLengthsBounded_of_hfin w hfin) hr : ℤ) ≤
            X l - X k) ∧
      (∀ k : ℤ, 1 ≤ k → X k - X (k - 1) ≤ -1) := by
  obtain ⟨X, hX, huniq⟩ :=
    existsUnique_ldpBusemann_of_finiteAvoidance w hfin (boundaryPresentVertex w h)
      havoid hcommon
  have hX' : IsBoundaryBusemannLDP (presentPathLengthsBounded_of_hfin w hfin)
      (boundaryPresentVertex w h) X := hX
  refine ⟨X, hX', fun X' hX'' => huniq X' hX'', ?_, ?_⟩
  · intro l k hl hlk hr
    exact boundaryBusemannLDP_ldp_le_sub w h _ hX' hl hlk (by
      obtain ⟨y, hy, hr⟩ := hcommon l k
      exact ⟨y, hy, hr⟩)
  · intro k hk
    exact boundaryBusemannLDP_succ_le w h _ hX' hk (by
      obtain ⟨y, hy, hr⟩ := hcommon (k - 1) k
      exact ⟨y, hy, hr⟩)

end DirectedDistances.KMSW
