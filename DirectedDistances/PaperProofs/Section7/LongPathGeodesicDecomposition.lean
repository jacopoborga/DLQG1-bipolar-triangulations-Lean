module

public import DirectedDistances.KMSW.LeftmostGeodesicPlanar
public import DirectedDistances.KMSW.BusemannBoundaryM0

/-! Supporting lemmas for paper labels `lem-long-path` (see CORRESPONDENCE.md). -/






@[expose] public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private def reversePathEdges {w : ℕ → Fin 3} {u : PresentVertex w} :
    {v : PresentVertex w} → Path u v → List ℕ
  | _, .nil => []
  | _, .cons p e => e.val :: reversePathEdges p

private theorem pathEdgeList_eq_reversePathEdges {w : ℕ → Fin 3}
    {u v : PresentVertex w} (p : Path u v) :
    pathEdgeList p = (reversePathEdges p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [pathEdgeList, reversePathEdges, ih]

private theorem presentVertex_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem reversePathEdges_endpoint {w : ℕ → Fin 3}
    {a b c : PresentVertex w} (p : Path a b) (q : Path a c)
    (h : reversePathEdges p = reversePathEdges q) : b = c := by
  induction p generalizing c q with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp [reversePathEdges] at h
  | @cons v b p e ih =>
      cases q with
      | nil => simp [reversePathEdges] at h
      | @cons v' c q f =>
          have hcons := List.cons.inj h
          have hv : v = v' := ih q hcons.2
          subst v'
          have hids : b.id = c.id := by
            calc
              b.id = edgeEast w e.val := e.property.2.2.symm
              _ = edgeEast w f.val := congrArg (edgeEast w) hcons.1
              _ = c.id := f.property.2.2
          exact presentVertex_ext hids

private theorem pathEdgeList_prefix {w : ℕ → Fin 3}
    {a : PresentVertex w} (P : InfinitePresentPath w a) {T s : ℕ}
    (hTs : T ≤ s) :
    (pathEdgeList (P.initial s).2).take T = pathEdgeList (P.initial T).2 := by
  rw [P.prefix_edges s, P.prefix_edges T]
  apply List.ext_getElem
  · simp [Nat.min_eq_left hTs]
  · intro i hi₁ hi₂
    simp only [List.getElem_take, List.getElem_ofFn]

private theorem presentLdpFiniteNat_congr {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w))
    {a a' b b' : PresentVertex w} (ha : a = a') (hb : b = b')
    (hr : Reachable a b) (hr' : Reachable a' b') :
    presentLdpFiniteNat hbound hr = presentLdpFiniteNat hbound hr' := by
  cases ha
  cases hb
  exact congrArg (presentLdpFiniteNat hbound) (Subsingleton.elim hr hr')




theorem prefix_decomp {w : ℕ → Fin 3}
    (hbound : PresentPathLengthsBounded (w := w)) {a z : PresentVertex w}
    (P : InfinitePresentPath w a) (hP : P.HasLongestSegments) (T : ℕ)
    (hz : (P.initial T).1 = z) (y : ℕ → PresentVertex w)
    (htail : ∀ r, ∃ s, T ≤ s ∧ y r = (P.initial s).1)
    (hrA : ∀ r, Reachable a (y r)) (hrZ : ∀ r, Reachable z (y r)) :
    ∃ N, ∀ r, N ≤ r →
      presentLdpFiniteNat hbound (hrA r) =
        T + presentLdpFiniteNat hbound (hrZ r) := by
  cases a with
  | mk start =>
      refine ⟨0, fun r _ => ?_⟩
      obtain ⟨s, hTs, hyr⟩ := htail r
      obtain ⟨u, p, q, hpq, hpLen⟩ :=
        (P.initial s).2.exists_eq_comp_of_le_length
          (show T ≤ (P.initial s).2.length by rw [P.prefix_length]; exact hTs)
      have hprefix := pathEdgeList_prefix P hTs
      have hcompEdges :
          pathEdgeList (P.initial s).2 = pathEdgeList p ++ pathEdgeList q := by
        rw [hpq, pathEdgeList_comp]
      have hlenP : (pathEdgeList p).length = T := by
        rw [pathEdgeList_length, hpLen]
      have htake : (pathEdgeList p ++ pathEdgeList q).take T = pathEdgeList p := by
        rw [List.take_append]
        simp [hlenP]
      have hpEdges : pathEdgeList p = pathEdgeList (P.initial T).2 := by
        calc
          pathEdgeList p = (pathEdgeList p ++ pathEdgeList q).take T := htake.symm
          _ = (pathEdgeList (P.initial s).2).take T := by rw [← hcompEdges]
          _ = pathEdgeList (P.initial T).2 := hprefix
      have hreverse : reversePathEdges p = reversePathEdges (P.initial T).2 := by
        have h := congrArg List.reverse hpEdges
        simpa only [pathEdgeList_eq_reversePathEdges, List.reverse_reverse] using h
      have huT : u = (P.initial T).1 :=
        reversePathEdges_endpoint p (P.initial T).2 hreverse
      have huz : u = z := huT.trans hz
      have hqLen : q.length = s - T := by
        have hslen := P.prefix_length s
        rw [hpq, Path.length_comp, hpLen] at hslen
        omega
      have hqLong : IsLongest q := by
        cases huz
        intro q'
        have hsLong : IsLongest (P.initial s).2 :=
          P.initial_isLongest w hP s
        have hbound' := hsLong (p.comp q')
        rw [Path.length_comp] at hbound'
        have htotal : (P.initial s).2.length = T + q.length := by
          rw [hpq, Path.length_comp, hpLen]
        rw [htotal, hpLen] at hbound'
        omega
      have hAeq : presentLdpFiniteNat hbound (hrA r) = s := by
        have hrA' : Reachable (⟨start⟩ : PresentVertex w) (P.initial s).1 := by
          simpa [hyr] using hrA r
        have hAeq' : presentLdpFiniteNat hbound hrA' = s := by
          rw [presentLdpFiniteNat_eq_length hbound hrA'
            (P.initial_isLongest w hP s)]
          exact P.prefix_length s
        exact (presentLdpFiniteNat_congr hbound rfl hyr (hrA r) hrA').trans hAeq'
      have hZeq : presentLdpFiniteNat hbound (hrZ r) = s - T := by
        have hrq : Reachable u (P.initial s).1 := ⟨q⟩
        have hqeq : presentLdpFiniteNat hbound hrq = s - T := by
          rw [presentLdpFiniteNat_eq_length hbound hrq hqLong, hqLen]
        exact (presentLdpFiniteNat_congr hbound huz.symm hyr (hrZ r) hrq).trans hqeq
      rw [hAeq, hZeq]
      omega

end DirectedDistances.PaperProofs.Section7
