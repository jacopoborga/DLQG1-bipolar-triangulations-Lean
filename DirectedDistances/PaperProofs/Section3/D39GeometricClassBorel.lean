/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricClassMetric

/-! # Borel structure for geometric rooted-map classes -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open scoped ENNReal

/-- Helper toward Definition 3.8: two domain rooted maps have equivalent
radius-`r + 1` geometric balls. The successor radius matches the strict open
ball of radius `2⁻ʳ`. -/
@[expose] def d39GeomBallClassSetoid (r : ℕ) : Setoid D39DomainRootedMap where
  r A B := Nonempty (D39GeomBallIsoV2 (r + 1) A.map A.root B.map B.root)
  iseqv := {
    refl := fun A => ⟨DirectedDistances.PaperProofs.Section3.refl
      (M := A.map) (rho := A.root) (Nat.succ_pos r)⟩
    symm := by
      intro A B h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro A B C hAB hBC
      rcases hAB with ⟨e⟩
      rcases hBC with ⟨f⟩
      exact ⟨DirectedDistances.PaperProofs.Section3.trans e f⟩
  }

/-- Helper toward Definition 3.8: the radius-`r + 1` ball class of a domain
rooted map class. -/
@[expose] noncomputable def d39GeomBallClassMap (r : ℕ) :
    D39GeomRootedMapClass → Quotient (d39GeomBallClassSetoid r) :=
  Quotient.lift (fun A : D39DomainRootedMap =>
      Quotient.mk (d39GeomBallClassSetoid r) A)
    (by
      intro A B h
      rcases h with ⟨e⟩
      exact Quotient.sound ⟨e.toBallIsoV2 (r + 1) (Nat.succ_pos r)⟩)

/-- Helper toward Definition 3.8: ball classes of quotient representatives
are their finite-radius ball classes. -/
@[simp] theorem d39GeomBallClassMap_mk (r : ℕ) (A : D39DomainRootedMap) :
    d39GeomBallClassMap r (Quotient.mk d39DomainSetoid A) =
      Quotient.mk (d39GeomBallClassSetoid r) A := rfl

/-- Helper toward Definition 3.8: equality of two ball classes is exactly a
geometric dart isomorphism of the corresponding balls. -/
theorem d39GeomBallClassMap_mk_eq_iff (r : ℕ)
    (A B : D39DomainRootedMap) :
    d39GeomBallClassMap r (Quotient.mk d39DomainSetoid A) =
      d39GeomBallClassMap r (Quotient.mk d39DomainSetoid B) ↔
        Nonempty (D39GeomBallIsoV2 (r + 1) A.map A.root B.map B.root) := by
  rw [d39GeomBallClassMap_mk, d39GeomBallClassMap_mk]
  exact Quotient.eq

/-- Helper toward Definition 3.8: the dyadic scales strictly decrease with
their natural-number index. -/
private theorem d39_half_pow_lt_iff {m n : ℕ} :
    (1 / 2 : ℝ≥0∞) ^ m < (1 / 2 : ℝ≥0∞) ^ n ↔ n < m := by
  have hb : (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by norm_num
  rw [hb, ← ENNReal.coe_inv_two, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
    ENNReal.coe_lt_coe]
  exact pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)

/-- Helper toward Definition 3.8: an open ball of radius `2⁻ʳ` is exactly the
set of classes whose radius-`r + 1` balls have the same geometric class. -/
theorem d39GeomClass_openBall_eq_ballClass (r : ℕ)
    (x : D39GeomRootedMapClass) :
    Metric.eball x ((1 / 2 : ℝ≥0∞) ^ r) =
      {y | d39GeomBallClassMap r x = d39GeomBallClassMap r y} := by
  ext y
  refine Quotient.inductionOn₂ y x ?_
  intro B A
  simp only [Metric.mem_eball, d39GeomBallClassMap_mk]
  constructor
  · intro h
    change (⨅ q : {q : ℕ // 0 < q},
      ⨅ (_ : Nonempty (D39GeomBallIsoV2 q.1 B.map B.root A.map A.root)),
        (1 / 2 : ℝ≥0∞) ^ q.1) < (1 / 2 : ℝ≥0∞) ^ r at h
    obtain ⟨q, hq⟩ := iInf_lt_iff.mp h
    obtain ⟨hIso, hscale⟩ := iInf_lt_iff.mp hq
    rcases hIso with ⟨e⟩
    have hrq : r + 1 ≤ q.1 := by
      have hlt : r < q.1 := (d39_half_pow_lt_iff).mp hscale
      exact Nat.succ_le_iff.mpr hlt
    have e' : D39GeomBallIsoV2 (r + 1) A.map A.root B.map B.root :=
      D39GeomBallIsoV2.restrict e.symm (Nat.succ_pos r) hrq
    exact (d39GeomBallClassMap_mk_eq_iff r A B).2 ⟨e'⟩
  · intro h
    have hIso : Nonempty (D39GeomBallIsoV2 (r + 1) A.map A.root B.map B.root) :=
      (d39GeomBallClassMap_mk_eq_iff r A B).1 h
    have hbound : d39GeomDistanceV2 A.map A.root B.map B.root ≤
        (1 / 2 : ℝ≥0∞) ^ (r + 1) :=
      (d39GeomDistanceV2_le_iff_nonempty (hr := Nat.succ_pos r)).2 hIso
    have hrs : r < r + 1 := by omega
    change d39GeomDistanceV2 B.map B.root A.map A.root < (1 / 2 : ℝ≥0∞) ^ r
    rw [d39GeomDistanceV2_comm]
    exact hbound.trans_lt ((d39_half_pow_lt_iff).2 hrs)

/- First remaining statement toward Definition 3.8: exhibit a countable dense
set of classes. Full binders:

  ∃ S : Set D39GeomRootedMapClass,
    S.Countable ∧ closure S = (Set.univ : Set D39GeomRootedMapClass)

The current geometric definitions give finite vertex and edge-identity balls,
but do not provide a theorem replacing each such embedded finite ball by an
equivalent drawing from a countable rational PL family. Establishing that
normalization while preserving the plane orientation, outside component,
missing-edge identities, and retained-face data is the first unresolved step.
The available hypotheses do not show separability false; they leave this
replacement is mapwise: each domain representative has countable vertex and
edge-identity carriers and finite vertex and edge-identity balls, as shown by
`D39GeomDomain.vertices_countable`, `D39GeomDomain.edges_countable`,
`D39GeomDomain.ballVertices_finite`, and `D39GeomDomain.ballEdges_finite`.
These do not assert countability or separability of the quotient class space. -/

end DirectedDistances.PaperProofs.Section3

end
