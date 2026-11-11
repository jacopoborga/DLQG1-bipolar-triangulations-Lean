/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartInvariance2
public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIsoSymm

/-! # Geometric rooted map classes -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open Filter
open scoped ENNReal Topology

universe uV uE uV' uE'



structure D39DomainRootedMap.{u} where
  V : Type u
  E : Type u
  map : DirectedPlaneMapWithMissing V E
  root : E × Bool
  domain : D39GeomDomain map root

/-- Helper toward Definition 3.8: domain rooted maps are equivalent when
there is a rooted geometric dart isomorphism between them. -/
@[expose] def d39DomainSetoid : Setoid D39DomainRootedMap where
  r A B := Nonempty (D39GeomRootedMapIsoV2 A.map A.root B.map B.root)
  iseqv := {
    refl := fun A => ⟨D39GeomRootedMapIsoV2.refl A.map A.root⟩
    symm := by
      intro A B h
      rcases h with ⟨e⟩
      exact ⟨D39GeomRootedMapIsoV2.symm e⟩
    trans := by
      intro A B C hAB hBC
      rcases hAB with ⟨e⟩
      rcases hBC with ⟨f⟩
      exact ⟨D39GeomRootedMapIsoV2.trans e f⟩
  }



abbrev D39GeomRootedMapClass := Quotient d39DomainSetoid

/-- Helper toward Definition 3.8: the domain rooted maps represented by a
geometric rooted map class. -/
@[expose] def d39DomainRootedMapClassMembers (c : D39GeomRootedMapClass) :
    Set D39DomainRootedMap :=
  {A | Quotient.mk d39DomainSetoid A = c}

/-- Helper toward Definition 3.8: the maps represented by a class stay in that
class after replacing a representative by a setoid-related one. -/
theorem d39DomainRootedMapClassMembers_closed_under_setoid
    {c : D39GeomRootedMapClass} {A B : D39DomainRootedMap}
    (hA : A ∈ d39DomainRootedMapClassMembers c)
    (hAB : d39DomainSetoid A B) :
    B ∈ d39DomainRootedMapClassMembers c := by
  change Quotient.mk d39DomainSetoid B = c
  change Quotient.mk d39DomainSetoid A = c at hA
  calc
    Quotient.mk d39DomainSetoid B = Quotient.mk d39DomainSetoid A :=
      (Quotient.sound hAB).symm
    _ = c := hA



theorem d39DomainRootedMapClassMembers.domain
    {c : D39GeomRootedMapClass} {A : D39DomainRootedMap}
    (_hA : A ∈ d39DomainRootedMapClassMembers c) :
    D39GeomDomain A.map A.root := A.domain

/-- Helper toward Definition 3.8: the geometric distance descends to rooted
geometric isomorphism classes. -/
@[expose] noncomputable def d39ClassDistance (c d : D39GeomRootedMapClass) : ℝ≥0∞ :=
  Quotient.liftOn₂ c d
    (fun A B => d39GeomDistanceV2 A.map A.root B.map B.root)
    (by
      intro A B A' B' hA hB
      rcases hA with ⟨eA⟩
      rcases hB with ⟨eB⟩
      calc
        d39GeomDistanceV2 A.map A.root B.map B.root =
            d39GeomDistanceV2 A'.map A'.root B.map B.root :=
          D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_left eA
        _ = d39GeomDistanceV2 A'.map A'.root B'.map B'.root :=
          D39GeomRootedMapIsoV2.d39GeomDistanceV2_congr_right eB)

/-- Helper toward Definition 3.8: class distance on quotient representatives
is the geometric distance of their maps. -/
theorem d39ClassDistance_mk (A B : D39DomainRootedMap) :
    d39ClassDistance (Quotient.mk d39DomainSetoid A)
      (Quotient.mk d39DomainSetoid B) =
        d39GeomDistanceV2 A.map A.root B.map B.root := rfl

/-- Helper toward Definition 3.8: the geometric distance from a rooted map to
itself is zero. -/
theorem d39GeomDistanceV2_self {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    d39GeomDistanceV2 M rho M rho = 0 := by
  let f : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
  have hfanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
    exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n)
  have hftendsto : Tendsto f atTop (𝓝 0) := by
    simpa only [f] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
  have hinf : (⨅ n, f n) = 0 := iInf_eq_of_tendsto hfanti hftendsto
  apply le_antisymm
  · rw [← hinf]
    apply le_iInf
    intro n
    have hr : 0 < n + 1 := Nat.succ_pos n
    have hIso : Nonempty (D39GeomBallIsoV2 (n + 1) M rho M rho) :=
      ⟨DirectedDistances.PaperProofs.Section3.refl (M := M) (rho := rho) hr⟩
    have hbound : d39GeomDistanceV2 M rho M rho ≤
        (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
      change (⨅ r : {r : ℕ // 0 < r},
          ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 M rho M rho)),
            ((1 / 2 : ℝ≥0∞) ^ r.1)) ≤ _
      exact (iInf_le
          (fun r : {r : ℕ // 0 < r} =>
            ⨅ (_ : Nonempty (D39GeomBallIsoV2 r.1 M rho M rho)),
              ((1 / 2 : ℝ≥0∞) ^ r.1))
          ⟨n + 1, hr⟩).trans
        (iInf_le
          (fun _ : Nonempty (D39GeomBallIsoV2 (n + 1) M rho M rho) =>
            ((1 / 2 : ℝ≥0∞) ^ (n + 1))) hIso)
    exact hbound.trans (by
      change (1 / 2 : ℝ≥0∞) ^ (n + 1) ≤ (1 / 2 : ℝ≥0∞) ^ n
      exact pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ n))
  · exact bot_le

/-- Helper toward Definition 3.8: class distance is symmetric. -/
theorem d39ClassDistance_comm (c d : D39GeomRootedMapClass) :
    d39ClassDistance c d = d39ClassDistance d c := by
  refine Quotient.inductionOn₂ c d ?_
  intro A B
  rw [d39ClassDistance_mk, d39ClassDistance_mk, d39GeomDistanceV2_comm]

/-- Helper toward Definition 3.8: every class has zero distance to itself. -/
theorem d39ClassDistance_self (c : D39GeomRootedMapClass) :
    d39ClassDistance c c = 0 := by
  refine Quotient.inductionOn c ?_
  intro A
  rw [d39ClassDistance_mk]
  exact d39GeomDistanceV2_self A.map A.root



theorem D39DomainRootedMap.mem_domain (A : D39DomainRootedMap) :
    D39GeomDomain A.map A.root := A.domain



theorem D39DomainRootedMap.domain_of_iso (A : D39DomainRootedMap.{uV})
    {V' : Type uV'} {E' : Type uE'} (M' : DirectedPlaneMapWithMissing V' E')
    (rho' : E' × Bool)
    (e : D39GeomRootedMapIsoV2 A.map A.root M' rho') :
    D39GeomDomain M' rho' :=
  e.domain_map A.domain

end DirectedDistances.PaperProofs.Section3

end


