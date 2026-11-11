module

public import DirectedDistances.KMSW.DirectedContain
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.KMSW.BusemannUIQBOT
import DirectedDistances.KMSW.RightBoundaryRightmost
import DirectedDistances.KMSW.RunBoundaryVertexLabels







public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem kmswRightBoundaryEdge_present (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (j : ℕ) :
    EdgePresent w (kmswRightBoundaryEdge w j) := by
  cases j with
  | zero =>
      rw [kmswRightBoundaryEdge_zero]
      exact ⟨0, by simp [kmswStage, kmswInit], by simp [kmswStage, kmswInit]⟩
  | succ j =>
      exact (boundaryVertex_right_edge_present_source w h (by omega)).1




theorem futureRightBoundary_path (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w)
    (j : ℕ) :
    ∃ q : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w)
        ⟨boundaryVertex w h (j : ℤ)⟩,
      q.length = j := by
  induction j with
  | zero =>
      exact ⟨Path.nil, by simp⟩
  | succ j ih =>
      obtain ⟨q, hq⟩ := ih
      have hends := kmswRightBoundaryEdge_hit_endpoints w h j
      have hEast : edgeEast w (kmswRightBoundaryEdge w j) =
          boundaryVertex w h ((j + 1 : ℕ) : ℤ) := by
        simpa only [Nat.cast_succ] using hends.2
      let e : (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) ⟶
          ⟨boundaryVertex w h ((j + 1 : ℕ) : ℤ)⟩ :=
        ⟨kmswRightBoundaryEdge w j, kmswRightBoundaryEdge_present w h j,
          hends.1, hEast⟩
      refine ⟨q.comp e.toPath, ?_⟩
      rw [Path.length_comp, Path.length_toPath, hq]









theorem futureRightBoundary_presentLdp_add_le (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (j : ℕ) {w' : PresentVertex w}
    (hr : Reachable (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w') :
    ((j : ℕ∞) : WithBot ℕ∞) +
        presentLdp (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w' ≤
      presentLdp (⟨boundaryVertex w h 0⟩ : PresentVertex w) w' := by
  obtain ⟨p, hp⟩ := futureRightBoundary_path w h j
  have hreach0 : Reachable (⟨boundaryVertex w h 0⟩ : PresentVertex w) w' := by
    obtain ⟨q⟩ := hr
    exact ⟨p.comp q⟩
  have hldpTail :
      presentLdp (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w' =
        (↑(⨆ q : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w',
          (q.length : ℕ∞)) : WithBot ℕ∞) := by
    unfold presentLdp
    let : Nonempty (Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w') := hr
    exact (WithBot.coe_iSup
      (f := fun q : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w' =>
        (q.length : ℕ∞)) (OrderTop.bddAbove _)).symm
  have hldpStart :
      presentLdp (⟨boundaryVertex w h 0⟩ : PresentVertex w) w' =
        (↑(⨆ q : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w',
          (q.length : ℕ∞)) : WithBot ℕ∞) := by
    unfold presentLdp
    let : Nonempty (Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w') := hreach0
    exact (WithBot.coe_iSup
      (f := fun q : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w' =>
        (q.length : ℕ∞)) (OrderTop.bddAbove _)).symm
  rw [hldpTail, hldpStart]
  apply WithBot.coe_le_coe.mpr
  change (j : ℕ∞) +
      (⨆ q : Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w',
        (q.length : ℕ∞)) ≤
    ⨆ r : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w',
      (r.length : ℕ∞)
  let : Nonempty (Path (⟨boundaryVertex w h (j : ℤ)⟩ : PresentVertex w) w') := hr
  rw [ENat.add_iSup]
  apply iSup_le
  intro q
  calc
    (j : ℕ∞) + (q.length : ℕ∞) = ((p.comp q).length : ℕ∞) := by
      rw [Path.length_comp, hp]
      simp
    _ ≤ ⨆ r : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w',
        (r.length : ℕ∞) :=
      le_iSup (fun r : Path (⟨boundaryVertex w h 0⟩ : PresentVertex w) w' =>
        (r.length : ℕ∞)) (p.comp q)

end DirectedDistances.PaperProofs.Section7
