module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.PaperProofs.Section7.CellLDPUpperConfinement
import DirectedDistances.PaperProofs.Section7.CellLDPUpperEdgeMerge

/-! Supporting lemmas for paper labels `lem-cell-ldp-upper` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem vertex_id_injective (w : ℕ → Fin 3) :
    Function.Injective (PresentVertex.id (w := w)) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases h
  rfl

private theorem finite_ldp_eq_coe {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a b : PresentVertex w}
    (hr : Reachable a b) :
    presentLdp a b = ((presentLdpFiniteNat hbound hr : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove (hbound a b hr) hr
  rw [presentLdp_eq_length hp, presentLdpFiniteNat_eq_length hbound hr hp]





theorem cellLdpUpper_busemann_bound (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (ℓ k σ0 σn : ℤ) (len : ℕ)
    (y : ℕ → PresentVertex (fun i => w (n + i))) (hy : Function.Injective y)
    (hyrn : ∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
      Reachable (boundaryPresentVertex (fun i => w (n + i)) hn σn) (y j))
    (hyr0 : ∀ j, Reachable (boundaryPresentVertex w h0 ℓ)
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) ∧
      Reachable (boundaryPresentVertex w h0 σ0)
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w))
    (hconcat : ∀ v : PresentVertex (fun i => w (n + i)),
      ((len : ℕ∞) : WithBot ℕ∞) +
          presentLdp (boundaryPresentVertex (fun i => w (n + i)) hn k) v ≤
        presentLdp (boundaryPresentVertex w h0 ℓ) ⟨kmswWindowVertexMapInf w n v.id⟩)
    (hseamLdp : ∀ v : PresentVertex (fun i => w (n + i)),
      presentLdp (boundaryPresentVertex (fun i => w (n + i)) hn σn) v =
        presentLdp (boundaryPresentVertex w h0 σ0) ⟨kmswWindowVertexMapInf w n v.id⟩) :
    (len : ℤ) ≤ (X ℓ - X σ0) - (Xn k - Xn σn) := by
  let u := fun i => w (n + i)
  let img : PresentVertex u → PresentVertex w :=
    fun v => ⟨kmswWindowVertexMapInf w n v.id⟩
  have hy0 : Function.Injective (fun j => img (y j)) := by
    intro a b hab
    apply hy
    apply vertex_id_injective u
    exact kmswWindowVertexMapInf_injective w n (congrArg PresentVertex.id hab)
  obtain ⟨N0, hN0⟩ := hX.2 ℓ σ0 (fun j => img (y j)) hy0 hyr0
  obtain ⟨Nn, hNn⟩ := hXn.2 k σn y hy hyrn
  let j := max N0 Nn
  have hb0 := hN0 j (Nat.le_max_left _ _)
  have hbn := hNn j (Nat.le_max_right _ _)
  have hc := hconcat (y j)
  have hs := hseamLdp (y j)
  rw [finite_ldp_eq_coe hboundn (hyrn j).1,
    finite_ldp_eq_coe hbound0 (hyr0 j).1] at hc
  rw [finite_ldp_eq_coe hboundn (hyrn j).2,
    finite_ldp_eq_coe hbound0 (hyr0 j).2] at hs
  have hnat : len + presentLdpFiniteNat hboundn (hyrn j).1 ≤
      presentLdpFiniteNat hbound0 (hyr0 j).1 := by
    apply ENat.natCast_le_natCast.mp
    apply WithBot.coe_le_coe.mp
    rw [ENat.natCast_add, WithBot.coe_add]
    exact hc
  have hseq : presentLdpFiniteNat hboundn (hyrn j).2 =
      presentLdpFiniteNat hbound0 (hyr0 j).2 :=
    ENat.natCast_inj.mp (WithBot.coe_inj.mp hs)
  have hlen : (len : ℤ) + (presentLdpFiniteNat hboundn (hyrn j).1 : ℤ) ≤
      (presentLdpFiniteNat hbound0 (hyr0 j).1 : ℤ) := by
    exact_mod_cast hnat
  rw [hseq] at hbn
  omega





theorem cellLdpUpper_busemann_bound_explicit (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (ℓ k : ℤ) (len : ℕ)
    (y : ℕ → PresentVertex (fun i => w (n + i))) (hy : Function.Injective y)
    (hyrn : ∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
      Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
        (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j))
    (hyr0 : ∀ j, Reachable (boundaryPresentVertex w h0 ℓ)
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) ∧
      Reachable (boundaryPresentVertex w h0 ((kmswStage w n).LR.length : ℤ))
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w))
    (hconcat : ∀ v : PresentVertex (fun i => w (n + i)),
      ((len : ℕ∞) : WithBot ℕ∞) +
          presentLdp (boundaryPresentVertex (fun i => w (n + i)) hn k) v ≤
        presentLdp (boundaryPresentVertex w h0 ℓ) ⟨kmswWindowVertexMapInf w n v.id⟩) :
    (len : ℤ) ≤ (X ℓ - X ((kmswStage w n).LR.length : ℤ)) -
      (Xn k - Xn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) := by
  apply cellLdpUpper_busemann_bound w n h0 hn hbound0 hboundn hX hXn ℓ k
    ((kmswStage w n).LR.length : ℤ)
    (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) len y hy hyrn hyr0 hconcat
  intro v
  have hmerge : ∀ q : ℕ, 1 ≤ q →
      kmswRightBoundaryEdge w (q - 1 + (kmswStage w n).LR.length) =
        kmswWindowEdgeMapInf w n
          (kmswRightBoundaryEdge (fun i => w (n + i))
            (q - 1 + ((kmswStage w n).UR.length + 1))) := by
    intro q _hq
    exact rightBoundary_edge_merge_explicit w n h0 hn (q - 1)
  have hseam := rightBoundary_vertices_merge_of_edges w n
    (kmswStage w n).LR.length ((kmswStage w n).UR.length + 1) h0 hn hmerge 0
  simp only [Nat.zero_add] at hseam
  exact presentLdp_shared_seam_eq w n (kmswStage w n).LR.length
    ((kmswStage w n).UR.length + 1) v.id h0 hn hseam hmerge





theorem cellLdpUpper_busemann_bound_of_abs_le (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w)
    (hn : BoundaryHitWitnesses (fun i => w (n + i)))
    (hbound0 : PresentPathLengthsBounded (w := w))
    (hboundn : PresentPathLengthsBounded (w := fun i => w (n + i)))
    {X Xn : ℤ → ℤ}
    (hX : IsBoundaryBusemannLDP hbound0 (boundaryPresentVertex w h0) X)
    (hXn : IsBoundaryBusemannLDP hboundn
      (boundaryPresentVertex (fun i => w (n + i)) hn) Xn)
    (ℓ k : ℤ) (len : ℕ)
    (y : ℕ → PresentVertex (fun i => w (n + i))) (hy : Function.Injective y)
    (hyrn : ∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k) (y j) ∧
      Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
        (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j))
    (hyr0 : ∀ j, Reachable (boundaryPresentVertex w h0 ℓ)
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) ∧
      Reachable (boundaryPresentVertex w h0 ((kmswStage w n).LR.length : ℤ))
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w))
    (hconcat : ∀ v : PresentVertex (fun i => w (n + i)),
      ((len : ℕ∞) : WithBot ℕ∞) +
          presentLdp (boundaryPresentVertex (fun i => w (n + i)) hn k) v ≤
        presentLdp (boundaryPresentVertex w h0 ℓ) ⟨kmswWindowVertexMapInf w n v.id⟩)
    (M0 Mn : ℤ)
    (hM0 : ∀ i : ℤ, -((kmswStage w n).LL.length : ℤ) ≤ i →
      i ≤ ((kmswStage w n).LR.length : ℤ) → |X i| ≤ M0)
    (hMn : ∀ i : ℤ, -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ i →
      i ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) → |Xn i| ≤ Mn)
    (hℓ : -((kmswStage w n).LL.length : ℤ) ≤ ℓ ∧
      ℓ ≤ ((kmswStage w n).LR.length : ℤ))
    (hk : -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
      k ≤ (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) :
    (len : ℤ) ≤ 2 * M0 + 2 * Mn := by
  have hlen := cellLdpUpper_busemann_bound_explicit w n h0 hn hbound0 hboundn
    hX hXn ℓ k len y hy hyrn hyr0 hconcat
  have hℓX := abs_le.mp (hM0 ℓ hℓ.1 hℓ.2)
  have hkX := abs_le.mp (hMn k hk.1 hk.2)
  have hσ0X := abs_le.mp (hM0 ((kmswStage w n).LR.length : ℤ) (by omega) le_rfl)
  have hσnX := abs_le.mp
    (hMn (((kmswStage w n).UR.length + 1 : ℕ) : ℤ) (by omega) le_rfl)
  omega

end DirectedDistances.PaperProofs.Section7
