/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516ExteriorMarkedAssembly2
import all DirectedDistances.PaperProofs.Section5.UIBHBOTD39CanonicalClass

/-! Helper toward Proposition 5.16. Measurable total realization of the canonical
class on a measurable conull subset. Countable measurable combinatorial ball
fibers have arbitrarily small geometric diameter by the proved exterior
comparison. No identification with the source limiting law (F3) is made. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.PlanarMap DirectedDistances.KMSW
open DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.SourceResults
open Prop516RootExteriorEncoding
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Helper toward Proposition 5.16: the option selector agrees with every
canonical domain witness, including the geometric quotient representative. -/
theorem uibhbotD39CanonicalClass_eq_some_domain
    (W : ℤ → Fin 3) (D : UIBHBOTD39CanonicalDomainWitness W) :
    uibhbotD39CanonicalClass W = some (PLCylinderBall.geometricClass
      (uibhbotD39CanonicalRepresentation13Domain W D)) := by
  have hW : uibhbotD39CanonicalDomainEvent W := ⟨D⟩
  simp only [uibhbotD39CanonicalClass, dite_eq_left hW]
  rfl

/-- Helper toward Proposition 5.16: agreement of code balls bounds the
geometric distance between any two canonical source representatives. -/
theorem uibhbotCanonical_edist_le_of_code_ball_eq
    (W W' : ℤ → Fin 3)
    (hW : W ∈ uibhbotRootedPlanarMapConullEvent)
    (hW' : W' ∈ uibhbotRootedPlanarMapConullEvent)
    (D : UIBHBOTD39CanonicalDomainWitness W)
    (D' : UIBHBOTD39CanonicalDomainWitness W')
    (r : ℕ) (hr : 0 < r)
    (hball : d39BallClass
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr =
      d39BallClass
      (uibhbotRootedPlanarMapOfCode W').toRootedLocallyFiniteMap.toD39RootedMap r hr) :
    edist (PLCylinderBall.geometricClass (uibhbotD39CanonicalRepresentation13Domain W D))
      (PLCylinderBall.geometricClass (uibhbotD39CanonicalRepresentation13Domain W' D')) ≤
        (1 / 2 : ℝ≥0∞) ^ r := by
  obtain ⟨hhit, C, iso, x, hxpos, hxarc⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W hW D
  obtain ⟨hhit', C', iso', y, hypos, hyarc⟩ :=
    exteriorMarkedComparison_canonical_reparam_data W' hW' D'
  have hi : d39BallClass _ r hr = d39BallClass
      (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap r hr :=
    Quotient.sound ⟨iso.ballIso r hr⟩
  have hi' : d39BallClass _ r hr = d39BallClass
      (uibhbotRootedPlanarMapOfCode W').toRootedLocallyFiniteMap.toD39RootedMap r hr :=
    Quotient.sound ⟨iso'.ballIso r hr⟩
  have hm : Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal _
        (exteriorMarkedComparison_canonicalDrawing W D hhit C) r hr) =
      Quotient.mk exteriorMarkedBallSetoid
      (d39FacedBallPLWithExternal _
        (exteriorMarkedComparison_canonicalDrawing W' D' hhit' C') r hr) := by
    rw [exteriorMarkedComparison_canonicalDrawing_rootLift,
      exteriorMarkedComparison_canonicalDrawing_rootLift]
    exact congrArg rootLift (hi.trans (hball.trans hi'.symm))
  exact (d39ClassDistance_le_pow_iff_nonempty hr _ _).mpr
    (exteriorMarkedComparison_reparam_geomBallIso x y _ _
      hxpos hypos hxarc hyarc r hr hm)

private theorem measurable_of_small_countable_fibers
    {X C : Type*} [MeasurableSpace X] [Countable C]
    (b : ℕ → X → C) (hb : ∀ r c, MeasurableSet {x | b r x = c})
    (S : Set X) (hS : MeasurableSet S)
    (F : X → D39GeomRootedMapClass) (c₀ : D39GeomRootedMapClass)
    (hout : ∀ x ∉ S, F x = c₀)
    (hsmall : ∀ r, ∀ x ∈ S, ∀ y ∈ S, b r x = b r y →
      edist (F x) (F y) ≤ (1 / 2 : ℝ≥0∞) ^ (r + 1)) :
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    Measurable F := by
  classical
  let : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
  let : BorelSpace D39GeomRootedMapClass := ⟨rfl⟩
  apply measurable_of_isOpen
  intro U hU
  let T (r : ℕ) : Set C := {c | ∀ x ∈ S, b r x = c → F x ∈ U}
  have heq : F ⁻¹' U =
      (⋃ r, ⋃ c ∈ T r, S ∩ {x | b r x = c}) ∪
        (if c₀ ∈ U then Sᶜ else ∅) := by
    ext x
    constructor
    · intro hx
      change F x ∈ U at hx
      by_cases hxS : x ∈ S
      · obtain ⟨ε, hε, hεU⟩ := EMetric.isOpen_iff.mp hU (F x) hx
        obtain ⟨r, hr⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt hε)
        have hpow : (1 / 2 : ℝ≥0∞) ^ (r + 1) < ε :=
          lt_of_le_of_lt (pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_succ r))
            (by simpa only [one_div] using hr)
        have hc : b r x ∈ T r := by
          intro y hy he
          apply hεU
          exact (hsmall r y hy x hxS he).trans_lt hpow
        exact Or.inl (mem_iUnion.mpr ⟨r,
          mem_iUnion₂.mpr ⟨b r x, hc, hxS, rfl⟩⟩)
      · have hc : c₀ ∈ U := by rwa [hout x hxS] at hx
        exact Or.inr (by simpa only [ite_eq_left hc, mem_compl_iff] using hxS)
    · rintro (hx | hx)
      · obtain ⟨r, hx⟩ := mem_iUnion.mp hx
        obtain ⟨c, hc, hxS, he⟩ := mem_iUnion₂.mp hx
        exact hc x hxS he
      · by_cases hc : c₀ ∈ U
        · have hxS : x ∉ S := by simpa only [ite_eq_left hc, mem_compl_iff] using hx
          change F x ∈ U
          simpa only [hout x hxS] using hc
        · simp only [ite_eq_right hc, mem_empty_iff_false] at hx
  rw [heq]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun c =>
      MeasurableSet.iUnion fun _ => hS.inter (hb r c)
  · split_ifs
    · exact hS.compl
    · exact MeasurableSet.empty

/-- Helper toward Proposition 5.16: a total Borel measurable representative
of the almost-surely defined canonical geometric class. This construction
does not assert that its pushforward is the source law of Definition 5.8. -/
theorem exists_measurable_uibhbotD39CanonicalClass_realization :
    ∃ F : (ℤ → Fin 3) → D39GeomRootedMapClass,
      (letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
       Measurable F) ∧
      ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
        ∃ hW : (uibhbotD39CanonicalClass W).isSome,
          F W = (uibhbotD39CanonicalClass W).get hW := by
  classical
  have ha : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      W ∈ uibhbotRootedPlanarMapConullEvent ∧ uibhbotD39CanonicalDomainEvent W :=
    uibhbotRootedPlanarMapConullEvent_spec.2.1.and
      uibhbotCodeLawRel_ae_d39CanonicalDomainEvent
  obtain ⟨S, hSae, hS, hs⟩ := ha.exists_measurable_mem
  obtain ⟨W₀, hW₀⟩ :=
    (show ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), W ∈ S from hSae).exists
  let D (W : ℤ → Fin 3) (hW : W ∈ S) := Classical.choice (hs W hW).2
  let c₀ := PLCylinderBall.geometricClass (uibhbotD39CanonicalRepresentation13Domain W₀ (D W₀ hW₀))
  let F (W : ℤ → Fin 3) : D39GeomRootedMapClass :=
    if hW : W ∈ S then PLCylinderBall.geometricClass
      (uibhbotD39CanonicalRepresentation13Domain W (D W hW)) else c₀
  refine ⟨F, ?_, ?_⟩
  · apply measurable_of_small_countable_fibers
      (fun r W => d39BallClass
        (uibhbotRootedPlanarMapOfCode W).toRootedLocallyFiniteMap.toD39RootedMap
          (r + 1) (Nat.succ_pos r))
      (fun r c => measurable_uibhbotD39BallClass r (by trivial : @MeasurableSet D39BallClass ⊤ {c}))
      S hS F c₀
    · intro W hW
      exact dite_eq_right hW
    · intro r W hW W' hW' hb
      simp only [F, dite_eq_left hW, dite_eq_left hW']
      exact uibhbotCanonical_edist_le_of_code_ball_eq W W'
        (hs W hW).1 (hs W' hW').1 (D W hW) (D W' hW')
        (r + 1) (Nat.succ_pos r) hb
  · filter_upwards [hSae] with W hW
    have he := uibhbotD39CanonicalClass_eq_some_domain W (D W hW)
    have hi : (uibhbotD39CanonicalClass W).isSome := by rw [he]; rfl
    refine ⟨hi, ?_⟩
    simp only [F, dite_eq_left hW, he, Option.get_some]

/-- Helper toward Proposition 5.16: the pushforward does not depend on the
choice of total representative agreeing with the canonical class almost surely.
This is uniqueness of the constructed measure, not source-law identification. -/
theorem uibhbotCanonical_realization_map_unique
    (F G : (ℤ → Fin 3) → D39GeomRootedMapClass)
    (hF : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hW : (uibhbotD39CanonicalClass W).isSome,
        F W = (uibhbotD39CanonicalClass W).get hW)
    (hG : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∃ hW : (uibhbotD39CanonicalClass W).isSome,
        G W = (uibhbotD39CanonicalClass W).get hW) :
    letI : MeasurableSpace D39GeomRootedMapClass := borel D39GeomRootedMapClass
    (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map F =
      (uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map G := by
  apply Measure.map_congr
  filter_upwards [hF, hG] with W hF hG
  obtain ⟨hW, hf⟩ := hF
  obtain ⟨hW', hg⟩ := hG
  exact hf.trans hg.symm

end DirectedDistances.PaperProofs.Section5
end

