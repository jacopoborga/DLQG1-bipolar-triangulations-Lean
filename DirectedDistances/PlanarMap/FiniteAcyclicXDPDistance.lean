/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.GeneralEndpointGeodesic
public import DirectedDistances.DirectedPath.LongestDistance

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Fixed-length directed map paths correspond to quiver paths on the
rotation-cycle vertices whose arrows retain the identities of present oriented
darts. This reuses `mapQuiver` and `mapPathEquivQuiverPath`. Helper toward -/
def mapPath_fixedLength_equiv_quiverPath
    (M : DirectedMapWithMissing D) (u v : MapVertex M) (n : ℕ) :
    MapPath M u v n ≃ {p : Quiver.Path u v // p.length = n} :=
  mapPathEquivQuiverPath M u v n

/-- On reachable endpoints, the extended LDP agrees with the finite acyclic
LDP after removing its bottom case. The reachability proof is needed to form
the natural-number value of `finiteLdp`. Helper toward Definition 3.13 -/
theorem ldp_eq_finiteLdp_of_reachable
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic)
    {u v : MapVertex M} (hr : Quiver.Reachable u v) :
    DirectedDistances.ldp u v =
      (((DirectedDistances.finiteLdp (mapQuiver_acyclic M hM) u v).unbot
        (by
          intro hbot
          exact (DirectedDistances.finiteLdp_eq_bot_iff_not_reachable
            (mapQuiver_acyclic M hM)).mp hbot hr) : ℕ) : ℕ∞) := by
  classical
  let hq := mapQuiver_acyclic M hM
  let L := DirectedDistances.finiteLdp hq u v
  have hLne : L ≠ ⊥ := by
    intro hbot
    exact (DirectedDistances.finiteLdp_eq_bot_iff_not_reachable hq).mp hbot hr
  obtain ⟨p, hp⟩ := DirectedDistances.exists_length_eq_finiteLdp hq hr
  have hpNat : p.length = L.unbot hLne :=
    ((WithBot.unbot_eq_iff hLne).mpr hp.symm).symm
  have hbound : ∃ N : ℕ, ∀ q : Quiver.Path u v, q.length ≤ N := by
    refine ⟨Fintype.card (MapVertex M), ?_⟩
    intro q
    exact Nat.le_of_lt (DirectedDistances.length_lt_card_of_acyclic hq q)
  have hmax : ∀ q : Quiver.Path u v, q.length ≤ p.length := by
    intro q
    have hqL := DirectedDistances.length_le_finiteLdp hq q
    rw [← hp] at hqL
    exact WithBot.coe_le_coe.mp hqL
  have hchar := DirectedDistances.ldp_eq_of_characterization
    (a := u) (b := v)
    (x := (((p.length : ℕ∞) : WithBot ℕ∞)))
    (Or.inr (Or.inl ⟨hr, hbound, p, rfl, hmax⟩))
  calc
    DirectedDistances.ldp u v = (((p.length : ℕ∞) : WithBot ℕ∞)) := hchar.symm
    _ = (((L.unbot hLne : ℕ) : ℕ∞) : WithBot ℕ∞) := by rw [← hpNat]

/-- The extended LDP is bottom for unreachable endpoints. Acyclicity is
included to match the finite-map Definition 3.13 domain, though the generic
distance characterization already proves this case. Helper toward Definition -/
theorem ldp_eq_bot_of_not_reachable
    (M : DirectedMapWithMissing D) (_hM : M.IsAcyclic)
    {u v : MapVertex M} (hnr : ¬ Quiver.Reachable u v) :
    DirectedDistances.ldp u v = ⊥ :=
  DirectedDistances.ldp_eq_bot_iff_not_reachable.mpr hnr

/-- For a finite acyclic map, an XDP geodesic is exactly a path whose length
equals the corresponding extended distance. The LDP case preserves bottom for
unreachable endpoints; the given path itself supplies reachability. Helper -/
theorem def_3_13_finite_geodesic_iff_extended_distance_eq
    (M : DirectedMapWithMissing D) (hM : M.IsAcyclic) (x : XDP)
    {u v : MapVertex M} {n : ℕ} (P : MapPath M u v n) :
    GeneralEndpointGeodesic.IsXDPGeodesic M hM x P ↔
      (match x with
       | .ldp => ((n : ℕ∞) : WithBot ℕ∞) = DirectedDistances.ldp u v
       | .sdp => (n : ℕ) = DirectedDistances.sdp u v) := by
  cases x with
  | ldp =>
      let hq := mapQuiver_acyclic M hM
      let L := DirectedDistances.finiteLdp hq u v
      have hr : Quiver.Reachable u v := ⟨P.path⟩
      have hLne : L ≠ ⊥ := by
        intro hbot
        exact (DirectedDistances.finiteLdp_eq_bot_iff_not_reachable hq).mp hbot hr
      have hbridge := ldp_eq_finiteLdp_of_reachable M hM hr
      change DirectedDistances.IsLongest P.path ↔
        ((n : ℕ∞) : WithBot ℕ∞) = DirectedDistances.ldp u v
      rw [DirectedDistances.isLongest_iff_length_eq_finiteLdp hq P.path]
      simp only [P.length_eq]
      constructor
      · intro hfinite
        have hn : n = L.unbot hLne :=
          ((WithBot.unbot_eq_iff hLne).mpr hfinite.symm).symm
        rw [hn]
        exact hbridge.symm
      · intro hdist
        rw [hbridge] at hdist
        have hcast : ((n : ℕ∞) : WithBot ℕ∞) =
            (((L.unbot hLne : ℕ) : ℕ∞) : WithBot ℕ∞) := hdist
        have henat : (n : ℕ∞) = (L.unbot hLne : ℕ∞) :=
          WithBot.coe_eq_coe.mp hcast
        have hn : n = L.unbot hLne := WithTop.coe_eq_coe.mp henat
        exact ((WithBot.unbot_eq_iff hLne).mp hn.symm).symm
  | sdp =>
      change DirectedDistances.IsShortest P.path ↔
        (n : ℕ∞) = DirectedDistances.sdp u v
      rw [DirectedDistances.isShortest_iff_length_eq_sdp P.path]
      simp only [P.length_eq]

end DirectedDistances.PlanarMap
