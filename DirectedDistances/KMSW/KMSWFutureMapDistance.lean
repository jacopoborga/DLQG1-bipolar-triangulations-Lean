/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.KMSW.BusemannFromCut
import DirectedDistances.DirectedPath.Maps

/-! Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
This file transfers paths and extended distances between the future-map carrier and -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Quiver

variable (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
instance futureMapCarrierQuiver :
    Quiver (RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) where
  Hom u v := FutureMapArrowDart w hfin u v

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
@[expose] noncomputable def futureMapToPresentPrefunctor :
    RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin) ⥤q PresentVertex w where
  obj := futureMapVertexEquiv w hfin
  map := fun {u v} d => futureMapArrowEquiv w hfin u v d

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
@[expose] noncomputable def presentToFutureMapPrefunctor :
    PresentVertex w ⥤q RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin) where
  obj := (futureMapVertexEquiv w hfin).symm
  map := fun {u v} d =>
    (futureMapArrowEquiv w hfin ((futureMapVertexEquiv w hfin).symm u)
      ((futureMapVertexEquiv w hfin).symm v)).symm (by
        simpa only [Equiv.apply_symm_apply] using d)

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
def futureMapPathCast {V : Type} [Quiver V] {a a' b b' : V}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) : Quiver.Path a' b' :=
  hb ▸ ha ▸ p

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Endpoint transport along equalities leaves the path length unchanged. -/
private theorem futureMapPathCast_length {V : Type} [Quiver V] {a a' b b' : V}
    (ha : a = a') (hb : b = b') (p : Quiver.Path a b) :
    (futureMapPathCast ha hb p).length = p.length := by
  cases ha
  cases hb
  rfl

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
theorem futureMap_reachable_iff_present
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :
    Reachable u v ↔
      Reachable (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨(futureMapToPresentPrefunctor w hfin).mapPath p⟩
  · rintro ⟨p⟩
    have hp := (presentToFutureMapPrefunctor w hfin).mapPath p
    change Quiver.Path ((futureMapVertexEquiv w hfin).symm
      (futureMapVertexEquiv w hfin u)) ((futureMapVertexEquiv w hfin).symm
      (futureMapVertexEquiv w hfin v)) at hp
    exact ⟨futureMapPathCast
      (Equiv.symm_apply_apply (futureMapVertexEquiv w hfin) u)
      (Equiv.symm_apply_apply (futureMapVertexEquiv w hfin) v) hp⟩

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
@[expose] noncomputable def futureMapCarrierPathBack
    {u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)}
    (p : Quiver.Path (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v)) :
    Quiver.Path u v := by
  have hp := (presentToFutureMapPrefunctor w hfin).mapPath p
  change Quiver.Path ((futureMapVertexEquiv w hfin).symm
    (futureMapVertexEquiv w hfin u)) ((futureMapVertexEquiv w hfin).symm
    (futureMapVertexEquiv w hfin v)) at hp
  exact futureMapPathCast
    (Equiv.symm_apply_apply (futureMapVertexEquiv w hfin) u)
    (Equiv.symm_apply_apply (futureMapVertexEquiv w hfin) v) hp

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
The remaining path-equivalence obligation is isolated here, without assuming it. -/
def futureMapCarrierPathEquivObligation : Prop :=
  ∀ u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin),
    Nonempty (Quiver.Path u v ≃
      Quiver.Path (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v))

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
theorem futureMapCarrierPathForward_length
    {u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)}
    (p : Quiver.Path u v) :
    ((futureMapToPresentPrefunctor w hfin).mapPath p).length = p.length := by
  exact DirectedDistances.length_mapPath (futureMapToPresentPrefunctor w hfin) p

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
The reverse path transfer also preserves path length. -/
theorem futureMapCarrierPathBack_length
    {u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)}
    (p : Quiver.Path (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v)) :
    (futureMapCarrierPathBack w hfin p).length = p.length := by
  dsimp [futureMapCarrierPathBack, presentToFutureMapPrefunctor]
  rw [futureMapPathCast_length]
  exact DirectedDistances.length_mapPath (presentToFutureMapPrefunctor w hfin) p

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result. -/
@[expose] def futureMapCarrierPathEdgeIds
    {u : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)} :
    {v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)} →
      Quiver.Path u v → List ℕ
  | _, .nil => []
  | _, .cons p e => futureMapCarrierPathEdgeIds p ++ [e.val.1]

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
The transported paths have the same edge IDs in traversal order. -/
theorem futureMapCarrierPathEdgeIds_eq
    {u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)}
    (p : Quiver.Path u v) :
    futureMapCarrierPathEdgeIds (w := w) (hfin := hfin) p =
      pathEdgeList ((futureMapToPresentPrefunctor w hfin).mapPath p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp [futureMapCarrierPathEdgeIds, futureMapToPresentPrefunctor,
      pathEdgeList, futureMapArrowEquiv_edge, ih]

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Shortest distance in the local future-map quiver, with unreachable value `⊤`. -/
@[expose] noncomputable def futureMapCarrierSDP
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) : ℕ∞ :=
  ⨅ p : Quiver.Path u v, (p.length : ℕ∞)

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Longest-distance supremum in the local future-map quiver; `⊥` is unreachable. -/
@[expose] noncomputable def futureMapCarrierLDP
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) : WithBot ℕ∞ :=
  ⨆ p : Quiver.Path u v, ((p.length : ℕ∞) : WithBot ℕ∞)

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Shortest distance agrees with the present-edge distance, including unreachable pairs. -/
theorem futureMapCarrierSDP_eq_present
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :
    futureMapCarrierSDP w hfin u v =
      sdp (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v) := by
  apply le_antisymm
  · apply le_iInf
    intro q
    let p := futureMapCarrierPathBack w hfin q
    calc
      futureMapCarrierSDP w hfin u v ≤ (p.length : ℕ∞) := iInf_le _ p
      _ = (q.length : ℕ∞) := by
        rw [futureMapCarrierPathBack_length]
  · apply le_iInf
    intro p
    calc
      sdp (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v) ≤
          (((futureMapToPresentPrefunctor w hfin).mapPath p).length : ℕ∞) :=
            sdp_le_length _
      _ = (p.length : ℕ∞) := by rw [futureMapCarrierPathForward_length]

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Unreachable carrier pairs have SDP value `⊤`, the `+∞` convention. -/
theorem futureMapCarrierSDP_eq_top_of_not_reachable
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin))
    (hr : ¬ Reachable u v) : futureMapCarrierSDP w hfin u v = ⊤ := by
  rw [futureMapCarrierSDP_eq_present]
  apply sdp_eq_top_iff_not_reachable.mpr
  intro hp
  exact hr ((futureMap_reachable_iff_present w hfin u v).mpr hp)

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Longest distance agrees with the present-edge extended LDP, including unreachable pairs. -/
theorem futureMapCarrierLDP_eq_present
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin)) :
    futureMapCarrierLDP w hfin u v =
      presentLdp (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    change ((p.length : ℕ∞) : WithBot ℕ∞) ≤
      ⨆ q : Quiver.Path (futureMapVertexEquiv w hfin u)
          (futureMapVertexEquiv w hfin v), ((q.length : ℕ∞) : WithBot ℕ∞)
    rw [← futureMapCarrierPathForward_length w hfin p]
    exact le_iSup
      (fun q : Quiver.Path (futureMapVertexEquiv w hfin u)
        (futureMapVertexEquiv w hfin v) => ((q.length : ℕ∞) : WithBot ℕ∞))
      ((futureMapToPresentPrefunctor w hfin).mapPath p)
  · apply iSup_le
    intro q
    let p := futureMapCarrierPathBack w hfin q
    calc
      ((q.length : ℕ∞) : WithBot ℕ∞) ≤ futureMapCarrierLDP w hfin u v :=
        by
          rw [← futureMapCarrierPathBack_length w hfin q]
          exact le_iSup_of_le p le_rfl

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
On a reachable pair, the carrier LDP is the finite longest-path value. -/
theorem futureMapCarrierLDP_eq_presentLdpFiniteNat
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin))
    (hbound : PresentPathLengthsBounded (w := w)) (hr : Reachable u v) :
    futureMapCarrierLDP w hfin u v =
      ((presentLdpFiniteNat hbound
        ((futureMap_reachable_iff_present w hfin u v).mp hr) : ℕ∞) : WithBot ℕ∞) := by
  rw [futureMapCarrierLDP_eq_present]
  obtain ⟨p, hp⟩ := exists_isLongest_of_bddAbove
    (hbound (futureMapVertexEquiv w hfin u) (futureMapVertexEquiv w hfin v)
      ((futureMap_reachable_iff_present w hfin u v).mp hr))
    ((futureMap_reachable_iff_present w hfin u v).mp hr)
  rw [presentLdp_eq_length hp,
    presentLdpFiniteNat_eq_length hbound _ hp]

/-- Helper toward Theorem 1.4 (thm-busemann, F4c); not a paper result.
Unreachable carrier pairs have LDP value `⊥`, the `−∞` convention. -/
theorem futureMapCarrierLDP_eq_bot_of_not_reachable
    (u v : RootedLocallyFiniteVertex (ℕ × Bool) (kmswInfRot w hfin))
    (hr : ¬ Reachable u v) : futureMapCarrierLDP w hfin u v = ⊥ := by
  let : IsEmpty (Quiver.Path u v) := ⟨fun p => hr ⟨p⟩⟩
  exact iSup_of_empty _

end DirectedDistances.KMSW
