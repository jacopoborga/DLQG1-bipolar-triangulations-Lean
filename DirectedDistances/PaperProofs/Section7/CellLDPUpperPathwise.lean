module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.StageSubgraph
public import Mathlib.Basic.Real.Basic
import DirectedDistances.PaperProofs.Section7.CellLDPUpperConcatenation
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBusemannBound
import DirectedDistances.PaperProofs.Section7.CellLDPUpperCommonTarget
import DirectedDistances.PaperProofs.Section7.CellLDPUpperBoundaryRoutes
import DirectedDistances.PaperProofs.Section7.CellLDPUpperRouteUp

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/




public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem path_concat_with_allocated_label (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (x y : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex)
    (hy : y.id < (kmswStage w n).nextVertex) (p : Path x y) :
    ∃ ℓ k : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) ∧
      -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
      boundaryVertex w h0 ℓ < (kmswStage w n).nextVertex ∧
      ∀ v : PresentVertex (fun i => w (n + i)),
        ((p.length : ℕ∞) : WithBot ℕ∞) +
            presentLdp (⟨boundaryVertex (fun i => w (n + i)) hn k⟩ :
              PresentVertex (fun i => w (n + i))) v ≤
          presentLdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
            ⟨kmswWindowVertexMapInf w n v.id⟩ := by
  obtain ⟨ℓ, hℓL, hℓR, hℓV, _, ⟨a⟩⟩ := stage_cell_lower_boundary_route w h0 n x hx
  obtain ⟨k, hkL, hkR, ⟨b⟩⟩ := stage_cell_upper_boundary_route w n hn y hy
  refine ⟨ℓ, k, hℓL, hℓR, hkL, hkR, hℓV, fun v => ?_⟩
  let z : PresentVertex (fun i => w (n + i)) := ⟨boundaryVertex _ hn k⟩
  have hpath (q : Path z v) :
      ((p.length : ℕ∞) : WithBot ℕ∞) + ((q.length : ℕ∞) : WithBot ℕ∞) ≤
        presentLdp (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
          ⟨kmswWindowVertexMapInf w n v.id⟩ := by
    obtain ⟨q', hq'⟩ := cell_window_path_forward w n q
    let c : Path (⟨boundaryVertex w h0 ℓ⟩ : PresentVertex w)
        ⟨kmswWindowVertexMapInf w n z.id⟩ :=
      (stageToLimit w n).mapPath ((a.comp p).comp b)
    have hc : c.length = ((a.comp p).comp b).length :=
      stageToLimit_length w n ((a.comp p).comp b)
    let r := c.comp q'
    have hlen : p.length + q.length ≤ r.length := by
      dsimp only [r]
      rw [Path.length_comp, hc, Path.length_comp, Path.length_comp, hq']
      omega
    apply le_trans _ (le_iSup (fun r => ((r.length : ℕ∞) : WithBot ℕ∞)) r)
    rw [← WithBot.coe_add, WithBot.coe_le_coe, ← ENat.natCast_add]
    exact ENat.natCast_le_natCast.mpr hlen
  change ((p.length : ℕ∞) : WithBot ℕ∞) + presentLdp z v ≤ _
  cases isEmpty_or_nonempty (Path z v) with
  | inl he =>
    let := he
    simp only [presentLdp, iSup_of_empty, WithBot.add_bot, bot_le]
  | inr he =>
    let := he
    have hsup : presentLdp z v =
        (↑(⨆ q : Path z v, (q.length : ℕ∞)) : WithBot ℕ∞) :=
      (WithBot.coe_iSup (f := fun q : Path z v => (q.length : ℕ∞))
        (OrderTop.bddAbove _)).symm
    rw [hsup, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (OrderTop.bddAbove _)]
    apply iSup_le
    intro q
    simpa only [WithBot.coe_add] using hpath q




theorem cell_path_length_le_of_busemann_bounds (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (M0 Mn : ℤ)
    (hM0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) → |X i| ≤ M0)
    (hMn : ∀ i : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) → |Xn i| ≤ Mn)
    (x y : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex)
    (hy : y.id < (kmswStage w n).nextVertex) (p : Path x y) :
    (p.length : ℤ) ≤ 2 * M0 + 2 * Mn := by
  obtain ⟨ℓ, k, hℓL, hℓR, hkL, hkR, hℓV, hc⟩ :=
    path_concat_with_allocated_label w n h0 hn x y hx hy p
  obtain ⟨z, hz, hzn, hz0⟩ := cell_common_target w n h0 hn ℓ k hℓV
  exact cellLdpUpper_busemann_bound_of_abs_le w n h0 hn hbound0 hboundn
    hX hXn ℓ k p.length z hz hzn hz0 hc M0 Mn hM0 hMn
    ⟨hℓL, hℓR⟩ ⟨hkL, by simpa only [Nat.cast_add, Nat.cast_one] using hkR⟩



theorem cell_ldpSup_le_of_busemann_bounds (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (M0 Mn : ℤ)
    (hM0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) → |X i| ≤ M0)
    (hMn : ∀ i : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) → |Xn i| ≤ Mn)
    (x y : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex)
    (hy : y.id < (kmswStage w n).nextVertex) :
    ldpSup x y ≤ ((2 * M0 + 2 * Mn).toNat : WithBot ℕ) := by
  unfold ldpSup
  apply csSup_le'
  rintro _ ⟨m, ⟨p, rfl⟩, rfl⟩
  have hp := cell_path_length_le_of_busemann_bounds w n h0 hn hbound0 hboundn
    hX hXn M0 Mn hM0 hMn x y hx hy p
  have hpN : p.length ≤ (2 * M0 + 2 * Mn).toNat := by omega
  exact (WithBot.coe_le_coe (α := ℕ) (a := p.length)
    (b := (2 * M0 + 2 * Mn).toNat)).mpr hpN



theorem cell_path_length_le_of_real_busemann_bounds (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (B0 Bn : ℝ)
    (hB0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) → |(X i : ℝ)| ≤ B0)
    (hBn : ∀ i : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) → |(Xn i : ℝ)| ≤ Bn)
    (x y : StagePresentVertex w n) (hx : x.id < (kmswStage w n).nextVertex)
    (hy : y.id < (kmswStage w n).nextVertex) (p : Path x y) :
    (p.length : ℝ) ≤ 2 * B0 + 2 * Bn := by
  obtain ⟨ℓ, k, hℓL, hℓR, hkL, hkR, hℓV, hc⟩ :=
    path_concat_with_allocated_label w n h0 hn x y hx hy p
  obtain ⟨z, hz, hzn, hz0⟩ := cell_common_target w n h0 hn ℓ k hℓV
  have hlenZ := cellLdpUpper_busemann_bound_explicit w n h0 hn hbound0 hboundn
    hX hXn ℓ k p.length z hz hzn hz0 hc
  have hlenR : (p.length : ℝ) ≤
      ((X ℓ : ℝ) - (X ((kmswStage w n).LR.length : ℤ) : ℝ)) -
        ((Xn k : ℝ) - (Xn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) : ℝ)) := by
    exact_mod_cast hlenZ
  have hℓX := abs_le.mp (hB0 ℓ hℓL hℓR)
  have hkX := abs_le.mp (hBn k hkL (by
    simpa only [Nat.cast_add, Nat.cast_one] using hkR))
  have hσ0X := abs_le.mp (hB0 ((kmswStage w n).LR.length : ℤ) (by omega) le_rfl)
  have hσnX := abs_le.mp
    (hBn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) (by omega) le_rfl)
  linarith only [hlenR, hℓX.2, hkX.1, hσ0X.1, hσnX.2]

end DirectedDistances.PaperProofs.Section7
