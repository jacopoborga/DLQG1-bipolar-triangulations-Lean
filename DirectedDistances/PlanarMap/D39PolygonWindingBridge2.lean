/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.D39PolygonWindingBridge

/-! # Logarithmic lift bridge for polygonal winding

Helpers toward Proposition 5.16. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

open unitInterval
open scoped Topology

namespace Polyline

/-- Helper toward Proposition 5.16: the logarithmic increment of an edge is
the difference of its endpoint log norms plus its signed edge angle. -/
theorem edgeLogIncrement_eq_normLogs_add_edgeAngle
    (p : Polyline) (z : ℂ) (i : ℕ)
    (hi : i + 1 < p.points.length) (hz : z ∉ p.image) :
    Complex.log ((p.point (i + 1) - z) / (p.point i - z)) =
      ((Real.log ‖p.point (i + 1) - z‖ - Real.log ‖p.point i - z‖ : ℝ) : ℂ) +
        (p.edgeAngle z i : ℂ) * Complex.I := by
  have hp (j : ℕ) (hj : j < p.points.length) : p.point j ∈ p.image := by
    by_cases hj0 : j = 0
    · subst j
      have hstart : p.point 0 = p.start := by
        cases h : p.points with
        | nil => exact (p.nonempty h).elim
        | cons a l => simp [point, start, h]
      rw [hstart]
      change p.start ∈ {p.start} ∪ _
      exact Or.inl rfl
    · have hs : j - 1 + 1 = j := by omega
      change p.point j ∈ {p.start} ∪
        {x : ℂ | ∃ k, k + 1 < p.points.length ∧ x ∈ p.segmentAt k}
      right
      refine ⟨j - 1, by omega, ?_⟩
      rw [← hs]
      exact right_mem_segment ℝ _ _
  have hnum : p.point (i + 1) - z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hz (h ▸ hp (i + 1) (by omega)))
  have hden : p.point i - z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hz (h ▸ hp i (by omega)))
  let q : ℂ := (p.point (i + 1) - z) / (p.point i - z)
  have hlog : Complex.log q =
      (Real.log ‖q‖ : ℂ) + (Complex.arg q : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  have hnorm : ‖q‖ = ‖p.point (i + 1) - z‖ / ‖p.point i - z‖ := by
    simp [q]
  have hlognorm : Real.log ‖q‖ =
      Real.log ‖p.point (i + 1) - z‖ - Real.log ‖p.point i - z‖ := by
    rw [hnorm, Real.log_div (norm_ne_zero_iff.mpr hnum)
      (norm_ne_zero_iff.mpr hden)]
  change Complex.log q = _
  rw [hlog, hlognorm]
  simp [q, edgeAngle]

end Polyline

/-- Helper toward Proposition 5.16: splitting a range sum at its first
term leaves the shifted range sum. -/
theorem sum_range_succ_first {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  calc
    _ = (∑ i ∈ Finset.range n, f (i + 1)) + f 0 :=
      Finset.sum_range_succ' f n
    _ = _ := add_comm _ _

/-- Helper toward Proposition 5.16: the recursive path through a vertex list
has lift increment equal to the range sum of its edge logarithms. -/
theorem listPath_hasLiftIncrement_range_sum (z a : ℂ) :
    ∀ l : List ℂ, z ∉ (Polyline.ofHead a l).image →
      HasLiftIncrement (Polyline.listPath a l) z
        (∑ i ∈ Finset.range ((Polyline.ofHead a l).points.length - 1),
          Complex.log
            ((Polyline.point (Polyline.ofHead a l) (i + 1) - z) /
              (Polyline.point (Polyline.ofHead a l) i - z))) := by
  intro l
  induction l generalizing a with
  | nil =>
      intro hz
      have ha : a - z ≠ 0 := by
        intro h
        have hmem : a ∈ (Polyline.ofHead a []).image := by
          change a ∈ {a} ∪ {x : ℂ | ∃ i, i + 1 < (Polyline.ofHead a []).points.length ∧ x ∈ (Polyline.ofHead a []).segmentAt i}
          exact Or.inl rfl
        apply hz
        exact (sub_eq_zero.mp h) ▸ hmem
      let φ : C(unitInterval, ℂ) :=
        ⟨fun _ => Complex.log (a - z), continuous_const⟩
      refine ⟨φ, ?_, ?_⟩
      · intro t
        change Complex.exp (Complex.log (a - z)) = a - z
        exact Complex.exp_log ha
      · simp [φ, Polyline.ofHead]
  | cons b l ih =>
      cases l with
      | nil =>
          intro hz
          let p : Polyline := Polyline.ofHead a [b]
          have hlen : 1 < p.points.length := by simp [p, Polyline.ofHead]
          have hpavoid : z ∉ p.image := by simpa [p, Polyline.image_ofHead_cons] using hz
          have hquot' := edgeRatio_mem_slitPlane p z 0 hlen hpavoid
          have hpa : p.point 0 = a := by
            simpa [p] using Polyline.point_ofHead_zero a [b]
          have hpb : p.point 1 = b := by
            change (Polyline.ofHead a [b]).point 1 = b
            rw [Polyline.point_ofHead_succ a b [] 0 (by simp : 0 < (b :: []).length)]
            exact Polyline.point_ofHead_zero b []
          have hquot : (b - z) / (a - z) ∈ Complex.slitPlane := by
            simpa [hpa, hpb] using hquot'
          have ha : a - z ≠ 0 := by
            apply sub_ne_zero.mpr
            have hmem : a ∈ p.image := by
              change a ∈ {p.start} ∪ _
              exact Or.inl (by simp [p, Polyline.ofHead, Polyline.start])
            intro h
            exact hpavoid (h ▸ hmem)
          have hfirst :=
            hasLiftIncrement_segment (Complex.exp_log ha) hquot
          have hsum :
              (∑ i ∈ Finset.range (p.points.length - 1),
                Complex.log ((p.point (i + 1) - z) / (p.point i - z))) =
                  Complex.log ((b - z) / (a - z)) := by
            simp [p, Polyline.ofHead, Polyline.point, Polyline.start]
          change HasLiftIncrement (Path.segment a b) z _
          rw [hsum]
          simpa [Polyline.listPath] using hfirst
      | cons c l =>
          intro hz
          have hsplit := Polyline.image_ofHead_cons a b (c :: l)
          rw [hsplit] at hz
          have hzseg : z ∉ segment ℝ a b := fun h => hz (Or.inl h)
          have hztail : z ∉ (Polyline.ofHead b (c :: l)).image :=
            fun h => hz (Or.inr h)
          let p : Polyline := Polyline.ofHead a (b :: c :: l)
          let q : Polyline := Polyline.ofHead b (c :: l)
          have hpavoid : z ∉ p.image := by simpa [p, Polyline.image_ofHead_cons] using hz
          have hlenq : q.points.length = (b :: c :: l).length := by
            simp [q, Polyline.ofHead]
          have hcount : p.points.length - 1 = (q.points.length - 1) + 1 := by
            simp [p, q, Polyline.ofHead]
          have hfirstlog :
              Complex.log ((p.point 1 - z) / (p.point 0 - z)) =
                Complex.log ((b - z) / (a - z)) := by
            rw [Polyline.point_ofHead_succ a b (c :: l) 0 (by simp),
              Polyline.point_ofHead_zero b (c :: l),
              Polyline.point_ofHead_zero a (b :: c :: l)]
          have hshift :
              (∑ i ∈ Finset.range (q.points.length - 1),
                Complex.log ((p.point (i + 2) - z) / (p.point (i + 1) - z))) =
              ∑ i ∈ Finset.range (q.points.length - 1),
                Complex.log ((q.point (i + 1) - z) / (q.point i - z)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Finset.mem_range] at hi
            have hi0 : i < (b :: c :: l).length := by omega
            have hi1 : i + 1 < (b :: c :: l).length := by omega
            rw [Polyline.point_ofHead_succ a b (c :: l) (i + 1) hi1,
              Polyline.point_ofHead_succ a b (c :: l) i hi0]
          have hbreak :
              (∑ i ∈ Finset.range (p.points.length - 1),
                Complex.log ((p.point (i + 1) - z) / (p.point i - z))) =
              Complex.log ((b - z) / (a - z)) +
                ∑ i ∈ Finset.range (q.points.length - 1),
                  Complex.log ((q.point (i + 1) - z) / (q.point i - z)) := by
            rw [hcount, sum_range_succ_first, hfirstlog, hshift]
          have hquot' := edgeRatio_mem_slitPlane p z 0 (by simp [p, Polyline.ofHead]) hpavoid
          have hpa : p.point 0 = a := by
            simpa [p] using Polyline.point_ofHead_zero a (b :: c :: l)
          have hpb : p.point 1 = b := by
            change (Polyline.ofHead a (b :: c :: l)).point 1 = b
            rw [Polyline.point_ofHead_succ a b (c :: l) 0 (by simp)]
            exact Polyline.point_ofHead_zero b (c :: l)
          have hquot : (b - z) / (a - z) ∈ Complex.slitPlane := by
            simpa [hpa, hpb] using hquot'
          have ha : a - z ≠ 0 := by
            apply sub_ne_zero.mpr
            intro h
            apply hzseg
            simpa [h] using (left_mem_segment ℝ a b)
          have hfirst :
              HasLiftIncrement (Path.segment a b) z
                (Complex.log ((b - z) / (a - z))) :=
            hasLiftIncrement_segment (Complex.exp_log ha) hquot
          have htail := ih b hztail
          change HasLiftIncrement
            ((Path.segment a b).trans (Polyline.listPath b (c :: l))) z _
          rw [hbreak]
          exact hasLiftIncrement_trans hfirst htail

/-- Helper toward Proposition 5.16: the ordered traversal of a polyline has
lift increment equal to its endpoint log-norm difference plus its angle sum. -/
theorem polyline_toPath_hasLiftIncrement (p : Polyline) (z : ℂ)
    (hz : z ∉ p.image) :
    HasLiftIncrement p.toPath z
      (((Real.log ‖p.finish - z‖ - Real.log ‖p.start - z‖ : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * (p.angleSum z : ℂ)) := by
  cases hpts : p.points with
  | nil =>
      exact (p.nonempty hpts).elim
  | cons a l =>
      have hpeq : p = Polyline.ofHead a l := by
        cases p with
        | mk points hne =>
            simp only at hpts
            subst points
            rfl
      subst p
      let N := (Polyline.ofHead a l).points.length - 1
      have hNlt : N < (Polyline.ofHead a l).points.length := by
        have hlen : 0 < (Polyline.ofHead a l).points.length :=
          List.length_pos_iff_ne_nil.mpr (by simp [Polyline.ofHead])
        dsimp [N]
        omega
      have hpoint0 :
          (Polyline.ofHead a l).point 0 = (Polyline.ofHead a l).start := by
        exact Polyline.point_ofHead_zero a l
      have hpointN :
          (Polyline.ofHead a l).point N = (Polyline.ofHead a l).finish := by
        let q := Polyline.ofHead a l
        have hget? : q.points[N]? = some (q.points.get ⟨N, hNlt⟩) :=
          List.getElem?_eq_getElem hNlt
        change q.points[N]?.getD q.start = q.points.getLast q.nonempty
        rw [hget?]
        simp only [Option.getD_some]
        have hlast := List.get_length_sub_one (l := q.points) hNlt
        simpa [q, N] using hlast
      have hlogsum :
          (∑ i ∈ Finset.range N,
            Complex.log (((Polyline.ofHead a l).point (i + 1) - z) /
              ((Polyline.ofHead a l).point i - z))) =
          (∑ i ∈ Finset.range N,
            (((Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ -
              Real.log ‖(Polyline.ofHead a l).point i - z‖ : ℝ) : ℂ) +
                ((Polyline.edgeAngle (Polyline.ofHead a l) z i : ℂ) * Complex.I))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i + 1 < (Polyline.ofHead a l).points.length := by
          simp only [Finset.mem_range] at hi
          dsimp [N] at hi
          omega
        exact Polyline.edgeLogIncrement_eq_normLogs_add_edgeAngle
          (Polyline.ofHead a l) z i hi' hz
      have hsplit :
          (∑ i ∈ Finset.range N,
            (((Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ -
              Real.log ‖(Polyline.ofHead a l).point i - z‖ : ℝ) : ℂ) +
                ((Polyline.edgeAngle (Polyline.ofHead a l) z i : ℂ) * Complex.I))) =
          (∑ i ∈ Finset.range N,
            ((Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ -
              Real.log ‖(Polyline.ofHead a l).point i - z‖ : ℝ) : ℂ)) +
          (∑ i ∈ Finset.range N,
            ((Polyline.edgeAngle (Polyline.ofHead a l) z i : ℂ) * Complex.I)) := by
        rw [Finset.sum_add_distrib]
      have hreal :
          (∑ i ∈ Finset.range N,
            (Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ -
              Real.log ‖(Polyline.ofHead a l).point i - z‖)) =
            Real.log ‖(Polyline.ofHead a l).finish - z‖ -
              Real.log ‖(Polyline.ofHead a l).start - z‖ := by
        let F : ℕ → ℝ := fun i => Real.log ‖(Polyline.ofHead a l).point i - z‖
        have htel : (∑ i ∈ Finset.range N, (F (i + 1) - F i)) = F N - F 0 := by
          rw [Finset.sum_range_sub]
        calc
          (∑ i ∈ Finset.range N, (Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ - Real.log ‖(Polyline.ofHead a l).point i - z‖)) = F N - F 0 := by simpa only [F] using htel
          _ = Real.log ‖(Polyline.ofHead a l).finish - z‖ - Real.log ‖(Polyline.ofHead a l).start - z‖ := by
            dsimp [F]
            rw [hpointN, hpoint0]
      have hrealC :
          (∑ i ∈ Finset.range N,
            ((Real.log ‖(Polyline.ofHead a l).point (i + 1) - z‖ -
              Real.log ‖(Polyline.ofHead a l).point i - z‖ : ℝ) : ℂ)) =
            ((Real.log ‖(Polyline.ofHead a l).finish - z‖ -
              Real.log ‖(Polyline.ofHead a l).start - z‖ : ℝ) : ℂ) := by
        exact_mod_cast hreal
      have himag :
          (∑ i ∈ Finset.range N,
            ((Polyline.edgeAngle (Polyline.ofHead a l) z i : ℂ) * Complex.I)) =
          ((∑ i ∈ Finset.range N,
            Polyline.edgeAngle (Polyline.ofHead a l) z i : ℝ) : ℂ) * Complex.I := by
        rw [← Finset.sum_mul]
        simp
      have hfactor :
          ((∑ i ∈ Finset.range N,
            Polyline.edgeAngle (Polyline.ofHead a l) z i : ℝ) : ℂ) * Complex.I =
            2 * Real.pi * Complex.I *
              (Polyline.angleSum (Polyline.ofHead a l) z : ℂ) := by
        rw [Polyline.angleSum]
        push_cast
        field_simp [Real.pi_ne_zero]
        ring
      have hsum :
          (∑ i ∈ Finset.range N,
            Complex.log (((Polyline.ofHead a l).point (i + 1) - z) /
              ((Polyline.ofHead a l).point i - z))) =
          ((Real.log ‖(Polyline.ofHead a l).finish - z‖ -
            Real.log ‖(Polyline.ofHead a l).start - z‖ : ℝ) : ℂ) +
            2 * Real.pi * Complex.I *
              (Polyline.angleSum (Polyline.ofHead a l) z : ℂ) := by
        rw [hlogsum, hsplit, hrealC, himag, hfactor]
      have hlift := listPath_hasLiftIncrement_range_sum z a l hz
      have hlift' :
          HasLiftIncrement (Polyline.toPath (Polyline.ofHead a l)) z
            (∑ i ∈ Finset.range N,
              Complex.log (((Polyline.ofHead a l).point (i + 1) - z) /
                ((Polyline.ofHead a l).point i - z))) := by
        have hpath : Polyline.toPath (Polyline.ofHead a l) = Polyline.listPath a l := by
          simp [Polyline.toPath, Polyline.ofHead, Polyline.start, Polyline.finish]
        rw [hpath]
        simpa [Polyline.ofHead, Polyline.start, Polyline.finish, N] using hlift
      rw [hsum] at hlift'
      exact hlift'

/-- Helper toward Proposition 5.16: for a closed polyline the lift increment
is the normalized edge-angle sum multiplied by one full turn. -/
theorem closedPolyline_hasLiftIncrement (p : Polyline)
    (hclosed : p.start = p.finish) (z : ℂ) (hz : z ∉ p.image) :
    HasLiftIncrement (p.toPath.cast rfl hclosed) z
      (2 * Real.pi * Complex.I * (p.angleSum z : ℂ)) := by
  change HasLiftIncrement p.toPath z
    (2 * Real.pi * Complex.I * (p.angleSum z : ℂ))
  simpa [hclosed] using polyline_toPath_hasLiftIncrement p z hz

/-- Helper toward Proposition 5.16: winding around an avoided closed
polyline is the integer represented by its normalized signed-angle sum. -/
theorem hasWinding_iff_angleSum_eq_int (p : Polyline)
    (hclosed : p.start = p.finish) (z : ℂ) (n : ℤ)
    (hz : z ∉ p.image) :
    HasWinding (p.toPath.cast rfl hclosed) z n ↔
      p.angleSum z = (n : ℝ) := by
  let L : Path p.start p.start := p.toPath.cast rfl hclosed
  constructor
  · intro hw
    obtain ⟨m, hm⟩ := Polyline.angleSum_isInt p hclosed z hz
    have hL := closedPolyline_hasLiftIncrement p hclosed z hz
    have hLm : HasLiftIncrement L z
        (2 * Real.pi * Complex.I * (m : ℂ)) := by
      simpa [L, hm] using hL
    have hmw : HasWinding L z m :=
      (hasLiftIncrement_iff_hasWinding L m).mp hLm
    have hmn : m = n := hasWinding_unique hmw (by simpa [L] using hw)
    simpa [hmn] using hm
  · intro hangle
    have hL := closedPolyline_hasLiftIncrement p hclosed z hz
    have hLn : HasLiftIncrement L z
        (2 * Real.pi * Complex.I * (n : ℂ)) := by
      simpa [L, hangle] using hL
    have hnw : HasWinding L z n :=
      (hasLiftIncrement_iff_hasWinding L n).mp hLn
    simpa [L] using hnw

end DirectedDistances.PlanarMap

end

