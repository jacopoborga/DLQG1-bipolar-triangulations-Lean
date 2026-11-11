/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceDetermination14








public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open Quiver

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: vertices of the realized adjacent ray,
retained as cells of the actual left side. -/
@[expose] def m0GeodesicSideAdjacentVertices
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left) :=
  fun n => .inl ⟨((P (k - 1)).codePath.initial n).1.id, (hcontain n).2⟩

/-- Helper toward Lemma 5.6: directed darts of the realized adjacent ray,
with geometric edge identity retained. -/
@[expose] def m0GeodesicSideAdjacentDarts
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left) :=
  fun n => .inr ⟨((P (k - 1)).codePath.edge n, false), (hcontain n).1⟩

/-- Helper toward Lemma 5.6: the candidate is the realized adjacent ray
itself, rather than an unspecified existential witness. -/
theorem m0GeodesicSide_realized_adjacentCandidate
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices) :
    geometricSideAdjacentGeodesicCandidate (m0GeodesicSide hp (P k) .left) longest
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) := by
  let M := m0GeodesicSide hp (P k) .left
  have hr : geometricSideDirectedRay M
      (m0GeodesicSideAdjacentVertices hp P k hcontain)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) := by
    intro n
    have hout := (P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) n
    have hin := (P (k - 1)).codePath.edge_incoming_at_succ (shiftedStream W 0) n
    exact ⟨⟨hout.1, rfl⟩, hout.2,
      .inr ⟨((P (k - 1)).codePath.edge n, true), (hcontain n).1⟩, rfl, hin.2⟩
  refine ⟨hr, ?_, ?_⟩
  · refine ⟨.inr ⟨M.boundary 1,
      m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩, rfl, ?_⟩
    change geometricSideDartInitial M (M.boundary 1) =
      ((P (k - 1)).codePath.initial 0).1.id
    exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
      (m0Geodesic_initial_zero (P (k - 1))).symm
  · intro i n
    refine ⟨geometricSideDirectedRay_walk hr i n, ?_⟩
    intro m hm
    obtain ⟨r, hrlen⟩ := m0GeodesicSide_walk_lifts hp (P k) .left m _ _ hm
    obtain ⟨p, q, hpq, _, hq, _⟩ := (P (k - 1)).codePath.exists_shift_split i n
    cases longest with
    | false =>
      have hopt := (P (k - 1)).codePath.initial_isShortest
        (shiftedStream W 0) (P (k - 1)).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change n ≤ m
      simpa only [hq, hrlen] using hle
    | true =>
      have hopt := (P (k - 1)).codePath.initial_isLongest
        (shiftedStream W 0) (P (k - 1)).segments (i + n)
      rw [hpq] at hopt
      have hle := hopt.of_comp_right r
      change m ≤ n
      simpa only [hq, hrlen] using hle

/-- Helper toward Lemma 5.6: the stored incoming corner at the adjacent
root is exactly exterior-boundary dart 1. -/
theorem m0GeodesicSide_adjacent_incomingCorner_zero
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (a : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    geometricSideRayIncomingCorner (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) 0 a ↔
      a = .inr ⟨(m0GeodesicSide hp (P k) .left).boundary 1,
        m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩ := by
  cases a with
  | inl v => simp only [geometricSideRayIncomingCorner, geometricSideRelation,
      reduceCtorEq]
  | inr d =>
    change _ = d.val ↔ _
    constructor
    · intro he
      exact congrArg Sum.inr (Subtype.ext he.symm)
    · intro he
      cases he
      rfl

/-- Helper toward Lemma 5.6: after a step the stored incoming corner is
the reversed geometric dart of that step, including its edge identity. -/
theorem m0GeodesicSide_adjacent_incomingCorner_succ
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (i : ℕ) (a : GeometricSideCell (m0GeodesicSide hp (P k) .left)) :
    geometricSideRayIncomingCorner (m0GeodesicSide hp (P k) .left)
      (m0GeodesicSideAdjacentDarts hp P k hcontain) (i + 1) a ↔
      a = .inr ⟨((P (k - 1)).codePath.edge i, true), (hcontain i).1⟩ := by
  cases a with
  | inl v => simp only [geometricSideRayIncomingCorner, m0GeodesicSideAdjacentDarts,
      geometricSideRelation, reduceCtorEq]
  | inr d =>
    change _ = d.val ↔ _
    constructor
    · intro he
      exact congrArg Sum.inr (Subtype.ext he.symm)
    · intro he
      cases he
      rfl

private theorem firstReturn_reverse {α : Type*} (σ : Equiv.Perm α)
    (S : Set α) {d e : α}
    (hret : ∃ n : ℕ, 0 < n ∧ (σ : α → α)^[n] d = e ∧
      ∀ j : ℕ, 0 < j → j < n → (σ : α → α)^[j] d ∉ S) :
    ∃ n : ℕ, 0 < n ∧ (σ.symm : α → α)^[n] e = d ∧
      ∀ j : ℕ, 0 < j → j < n → (σ.symm : α → α)^[j] e ∉ S := by
  obtain ⟨n, hn, he, hskip⟩ := hret
  refine ⟨n, hn, ?_, ?_⟩
  · rw [← he]
    exact (σ ^ n).symm_apply_apply d
  · intro j hj hjn
    have hsum : j + (n - j) = n := by omega
    have hback : (σ.symm : α → α)^[j] e = (σ : α → α)^[n - j] d := by
      calc
        (σ.symm : α → α)^[j] e =
            (σ.symm : α → α)^[j]
              ((σ : α → α)^[j] ((σ : α → α)^[n - j] d)) := by
          rw [← Function.iterate_add_apply, hsum, he]
        _ = (σ : α → α)^[n - j] d := (σ ^ j).symm_apply_apply _
    rw [hback]
    exact hskip (n - j) (by omega) (by omega)

/-- Helper toward Lemma 5.6: reversing a retained-edge first-return
relation gives the first return of the inverse ambient rotation. This
identifies the direction of the stored clockwise step and all skipped darts. -/
theorem m0GeodesicSide_clockwiseStep_iff
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges}) :
    geometricSideRelation (m0GeodesicSide hp P s) .rotation (.inr e) (.inr d) ↔
      ∃ n : ℕ, 0 < n ∧
        ((kmswInfRot (shiftedStream W 0) (H.1 0)).symm :
          (ℕ × Bool) → ℕ × Bool)^[n] d.val = e.val ∧
        ∀ j : ℕ, 0 < j → j < n →
          (((kmswInfRot (shiftedStream W 0) (H.1 0)).symm :
            (ℕ × Bool) → ℕ × Bool)^[j] d.val).1 ∉
              (m0GeodesicSide hp P s).edges := by
  constructor
  · exact firstReturn_reverse (kmswInfRot (shiftedStream W 0) (H.1 0))
      {a | a.1 ∈ (m0GeodesicSide hp P s).edges}
  · intro hr
    exact firstReturn_reverse (kmswInfRot (shiftedStream W 0) (H.1 0)).symm
      {a | a.1 ∈ (m0GeodesicSide hp P s).edges} hr

private theorem retainedScan_exists {α : Type*} (τ : α → α) (S : Set α)
    (a b : S) (n : ℕ) (hend : τ^[n] a.val = b.val) :
    ∃ (f : ℕ → S) (m : ℕ), f 0 = a ∧ f m = b ∧
      ∀ j, j < m → ∃ r : ℕ, 0 < r ∧ τ^[r] (f j).val = (f (j + 1)).val ∧
        ∀ t : ℕ, 0 < t → t < r → τ^[t] (f j).val ∉ S := by
  classical
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hab : a = b := Subtype.ext hend
      exact ⟨fun _ => a, 0, rfl, hab, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
    · have hex : ∃ r : ℕ, 0 < r ∧ r ≤ n ∧ τ^[r] a.val ∈ S :=
        ⟨n, by omega, le_rfl, hend ▸ b.property⟩
      let r := Nat.find hex
      have hr : 0 < r ∧ r ≤ n ∧ τ^[r] a.val ∈ S := Nat.find_spec hex
      have hskip (t : ℕ) (ht : 0 < t) (htr : t < r) : τ^[t] a.val ∉ S := by
        intro hm
        have hmin : r ≤ t := Nat.find_min' hex ⟨ht, by omega, hm⟩
        omega
      let c : S := ⟨τ^[r] a.val, hr.2.2⟩
      have hnext : τ^[n - r] c.val = b.val := by
        change τ^[n - r] (τ^[r] a.val) = b.val
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hr.2.1]
        exact hend
      obtain ⟨g, m, hg0, hgm, hstep⟩ := ih (n - r) (by omega) c b hnext
      refine ⟨fun j => Nat.casesOn j a g, m + 1, rfl, hgm, ?_⟩
      intro j hj
      cases j with
      | zero =>
        refine ⟨r, hr.1, ?_, hskip⟩
        change τ^[r] a.val = (g 0).val
        rw [hg0]
      | succ j => exact hstep j (by omega)

/-- Helper toward Lemma 5.6: any two retained darts at a common vertex
are joined by a finite stored clockwise scan. Finiteness is obtained from
the actual run-zero rotation orbit, without an abstract-side finiteness premise. -/
theorem m0GeodesicSide_clockwiseScan_exists
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (a b : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges})
    (hvertex : geometricSideDartInitial (m0GeodesicSide hp P s) a.val =
      geometricSideDartInitial (m0GeodesicSide hp P s) b.val) :
    ∃ (f : ℕ → GeometricSideCell (m0GeodesicSide hp P s)) (n : ℕ),
      geometricSideClockwiseScan (m0GeodesicSide hp P s) (.inr a) f n ∧
        f n = .inr b := by
  let σ := kmswInfRot (shiftedStream W 0) (H.1 0)
  obtain ⟨n, hn⟩ := (kmswInfRot_exists_pow_iff_endpoint
    (shiftedStream W 0) (H.1 0) b.val a.val).2 hvertex.symm
  have hback : (σ.symm : (ℕ × Bool) → ℕ × Bool)^[n] a.val = b.val := by
    rw [← hn]
    exact (σ ^ n).symm_apply_apply b.val
  obtain ⟨f, m, hf0, hfm, hstep⟩ := retainedScan_exists σ.symm
    {d : ℕ × Bool | d.1 ∈ (m0GeodesicSide hp P s).edges} a b n hback
  refine ⟨fun j => .inr (f j), m, ⟨congrArg Sum.inr hf0, ?_⟩,
    congrArg Sum.inr hfm⟩
  intro j hj
  exact (m0GeodesicSide_clockwiseStep_iff hp P s (f j) (f (j + 1))).2 (hstep j hj)

/-- Helper toward Lemma 5.6: at every step of the realized adjacent ray,
the actual incoming corner admits a stored clockwise scan to its departure.
This proves scan existence, without asserting first admissibility. -/
theorem m0GeodesicSide_adjacent_incomingScan
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool}
    (P : ∀ k : ℤ, M0CutInfiniteGeodesic W H h hLL k longest) (k : ℤ)
    (hcontain : ∀ n : ℕ,
      (P (k - 1)).codePath.edge n ∈ (m0GeodesicSide hp (P k) .left).edges ∧
      ((P (k - 1)).codePath.initial n).1.id ∈
        (m0GeodesicSide hp (P k) .left).vertices)
    (i : ℕ) :
    ∃ (a : GeometricSideCell (m0GeodesicSide hp (P k) .left))
      (f : ℕ → GeometricSideCell (m0GeodesicSide hp (P k) .left)) (n : ℕ),
      geometricSideRayIncomingCorner (m0GeodesicSide hp (P k) .left)
        (m0GeodesicSideAdjacentDarts hp P k hcontain) i a ∧
      geometricSideClockwiseScan (m0GeodesicSide hp (P k) .left) a f n ∧
      f n = m0GeodesicSideAdjacentDarts hp P k hcontain i := by
  let M := m0GeodesicSide hp (P k) .left
  cases i with
  | zero =>
    let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨M.boundary 1, m0GeodesicLeftSide_boundary_mem_edges hp (P k) 1⟩
    let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P (k - 1)).codePath.edge 0, false), (hcontain 0).1⟩
    have hv : geometricSideDartInitial M a.val = geometricSideDartInitial M b.val := by
      exact (m0GeodesicLeftSide_adjacent_start hp (P k)).trans
        ((m0Geodesic_initial_zero (P (k - 1))).symm.trans
          ((P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) 0).2.symm)
    obtain ⟨f, n, hf, hend⟩ := m0GeodesicSide_clockwiseScan_exists hp (P k) .left a b hv
    exact ⟨.inr a, f, n, rfl, hf, hend⟩
  | succ i =>
    let a : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P (k - 1)).codePath.edge i, true), (hcontain i).1⟩
    let b : {d : ℕ × Bool // d.1 ∈ M.edges} :=
      ⟨((P (k - 1)).codePath.edge (i + 1), false), (hcontain (i + 1)).1⟩
    have hv : geometricSideDartInitial M a.val = geometricSideDartInitial M b.val :=
      ((P (k - 1)).codePath.edge_incoming_at_succ (shiftedStream W 0) i).2.trans
        ((P (k - 1)).codePath.edge_outgoing_at_initial (shiftedStream W 0) (i + 1)).2.symm
    obtain ⟨f, n, hf, hend⟩ := m0GeodesicSide_clockwiseScan_exists hp (P k) .left a b hv
    exact ⟨.inr a, f, n, rfl, hf, hend⟩

/-- Helper toward Lemma 5.6: a clockwise run-zero scan is the ordered
subsequence of the whole-plane clockwise scan at exactly the run-zero darts.
This retains both dart bits and all missing geometric edges. -/
theorem m0Cut_clockwise_orderedScan (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W) (d : ℕ × Bool) :
    let σ := (kmswInfRot (shiftedStream W 0) (H.1 0)).symm
    let τ := (wholePlaneRotation W H).symm
    let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W 0
    ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧
      (∀ n, (τ : _ → _)^[N n] (I d) = I ((σ : _ → _)^[n] d)) ∧
      (∀ n j, j < N n →
        ((τ : _ → _)^[j] (I d) ∈ Set.range I ↔ ∃ i < n, j = N i)) := by
  classical
  let σ := (kmswInfRot (shiftedStream W 0) (H.1 0)).symm
  let τ := (wholePlaneRotation W H).symm
  let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W 0
  let r (n : ℕ) := (m0Cut_rotation_symm_firstReturn W H ((σ : _ → _)^[n] d)).choose
  have hr (n : ℕ) : 0 < r n ∧
      (τ : _ → _)^[r n] (I ((σ : _ → _)^[n] d)) =
        I (σ ((σ : _ → _)^[n] d)) ∧
      ∀ j : ℕ, 0 < j → j < r n →
        (τ : _ → _)^[j] (I ((σ : _ → _)^[n] d)) ∉ Set.range I :=
    (m0Cut_rotation_symm_firstReturn W H ((σ : _ → _)^[n] d)).choose_spec
  let N : ℕ → ℕ := fun n => Nat.rec 0 (fun i acc => acc + r i) n
  have hN0 : N 0 = 0 := rfl
  have hNs (n : ℕ) : N (n + 1) = N n + r n := rfl
  have hmono : StrictMono N := strictMono_nat_of_lt_succ fun n => by
    rw [hNs]
    have := (hr n).1
    omega
  have hmap (n : ℕ) : (τ : _ → _)^[N n] (I d) = I ((σ : _ → _)^[n] d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hNs, Nat.add_comm (N n) (r n), Function.iterate_add_apply, ih,
        (hr n).2.1, Function.iterate_succ_apply']
  refine ⟨N, hmono, hN0, hmap, ?_⟩
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    constructor
    · intro hm
      rcases Nat.lt_trichotomy j (N n) with hlt | heq | hgt
      · obtain ⟨i, hi, he⟩ := (ih j hlt).1 hm
        exact ⟨i, by omega, he⟩
      · exact ⟨n, by omega, heq⟩
      · have hpos : 0 < j - N n := by omega
        have hbound : j - N n < r n := by rw [hNs] at hj; omega
        apply False.elim
        apply (hr n).2.2 (j - N n) hpos hbound
        have he : (τ : _ → _)^[j - N n] (I ((σ : _ → _)^[n] d)) =
            (τ : _ → _)^[j] (I d) := by
          rw [← hmap, ← Function.iterate_add_apply, Nat.sub_add_cancel hgt.le]
        rw [he]
        exact hm
    · rintro ⟨i, _, rfl⟩
      rw [hmap]
      exact ⟨(σ : _ → _)^[i] d, rfl⟩

/-- Helper toward Lemma 5.6: the side's stored clockwise relation is
exactly first return of the whole-plane clockwise rotation to its retained
geometric darts. In particular, no omitted ambient dart can change encounter
order among retained darts. -/
theorem m0GeodesicSide_clockwiseStep_iff_wholePlane
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (d e : {d : ℕ × Bool // d.1 ∈ (m0GeodesicSide hp P s).edges}) :
    geometricSideRelation (m0GeodesicSide hp P s) .rotation (.inr e) (.inr d) ↔
      ∃ n : ℕ, 0 < n ∧
        ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[n]
          (wholePlaneDartι W 0 d.val) = wholePlaneDartι W 0 e.val ∧
        ∀ j : ℕ, 0 < j → j < n →
          ((wholePlaneRotation W H).symm : WholePlaneDart W → WholePlaneDart W)^[j]
            (wholePlaneDartι W 0 d.val) ∉
              wholePlaneDartι W 0 '' {a : ℕ × Bool | a.1 ∈
                (m0GeodesicSide hp P s).edges} := by
  let σ := (kmswInfRot (shiftedStream W 0) (H.1 0)).symm
  let τ := (wholePlaneRotation W H).symm
  let I : (ℕ × Bool) → WholePlaneDart W := wholePlaneDartι W 0
  let S : Set (ℕ × Bool) := {a | a.1 ∈ (m0GeodesicSide hp P s).edges}
  have hI : Function.Injective I := by
    rintro ⟨a, b⟩ ⟨c, f⟩ hh
    change (wholePlaneEdgeι W 0 a, b) = (wholePlaneEdgeι W 0 c, f) at hh
    exact Prod.ext (wholePlaneEdgeι_injective W 0 (congrArg Prod.fst hh))
      (congrArg (fun x : WholePlaneEdge W × Bool => x.2) hh)
  obtain ⟨N, hmono, hzero, hmap, hhits⟩ := m0Cut_clockwise_orderedScan W H d.val
  have hpos {i : ℕ} : 0 < N i ↔ 0 < i := by
    calc
      0 < N i ↔ N 0 < N i := by rw [hzero]
      _ ↔ 0 < i := hmono.lt_iff_lt
  constructor
  · intro hstep
    obtain ⟨r, hr, hend, hskip⟩ := (m0GeodesicSide_clockwiseStep_iff hp P s d e).1 hstep
    refine ⟨N r, hpos.mpr hr, (hmap r).trans (congrArg I hend), ?_⟩
    intro j hj hjr hm
    obtain ⟨x, hx, hxj⟩ := hm
    obtain ⟨q, hqr, hjq⟩ := (hhits r j hjr).1 ⟨x, hxj⟩
    have hq : 0 < q := hpos.mp (hjq ▸ hj)
    apply hskip q hq hqr
    have heq : (σ : _ → _)^[q] d.val = x := by
      apply hI
      exact (hmap q).symm.trans (hjq ▸ hxj.symm)
    exact heq ▸ hx
  · rintro ⟨r, hr, hend, hskip⟩
    have hlower : ∀ i : ℕ, i ≤ N i := by
      intro i
      induction i with
      | zero => omega
      | succ i ih =>
        have hstep : N i < N (i + 1) := hmono (Nat.lt_succ_self i)
        omega
    have hbound : r < N (r + 1) := by have := hlower (r + 1); omega
    obtain ⟨q, _, hrq⟩ := (hhits (r + 1) r hbound).1 ⟨e.val, hend.symm⟩
    apply (m0GeodesicSide_clockwiseStep_iff hp P s d e).2
    refine ⟨q, hpos.mp (hrq ▸ hr), ?_, ?_⟩
    · apply hI
      exact (hmap q).symm.trans (hrq ▸ hend)
    · intro j hj hjq hm
      apply hskip (N j) (hpos.mpr hj)
      · rw [hrq]
        exact hmono hjq
      · exact ⟨(σ : _ → _)^[j] d.val, hm, (hmap j).symm⟩

/-- Helper toward Lemma 5.6: an ambient path from the closed right side
to the closed left side visits a seam vertex. This is a finite-path
crossing statement and imposes no metric or recurrence premise. -/
theorem m0GeodesicSide_path_hits_seam
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {u v : PresentVertex (shiftedStream W 0)} (p : Path u v)
    (hu : u.id ∈ m0GeodesicSideVertices hp P .right)
    (hv : v.id ∈ m0GeodesicSideVertices hp P .left) :
    ∃ j : ℕ, (P.codePath.initial j).1 ∈ p.vertices := by
  have atSeam {z : PresentVertex (shiftedStream W 0)}
      (hl : z.id ∈ m0GeodesicSideVertices hp P .left)
      (hr : z.id ∈ m0GeodesicSideVertices hp P .right) :
      ∃ j : ℕ, (P.codePath.initial j).1 = z := by
    have hz : z.id ∈ m0GeodesicVertices P := by
      rw [← m0GeodesicSideVertices_inter hp P]
      exact ⟨hl, hr⟩
    obtain ⟨j, hj⟩ := hz
    exact ⟨j, congrArg PresentVertex.mk hj⟩
  have aux : ∀ {z : PresentVertex (shiftedStream W 0)} (q : Path u z),
      z.id ∈ m0GeodesicSideVertices hp P .left →
        ∃ j : ℕ, (P.codePath.initial j).1 ∈ q.vertices := by
    intro z q
    induction q with
    | nil =>
      intro hl
      obtain ⟨j, hj⟩ := atSeam hl hu
      exact ⟨j, hj ▸ Path.end_mem_vertices Path.nil⟩
    | @cons y z q e ih =>
      intro hz
      by_cases hy : y.id ∈ m0GeodesicSideVertices hp P .left
      · obtain ⟨j, hj⟩ := ih hy
        exact ⟨j, (Path.mem_vertices_cons q e).mpr (Or.inl hj)⟩
      · rcases m0GeodesicSideEdges_cover hp P e.val with he | he
        · exact (hy (e.property.2.1 ▸
            (m0GeodesicSide_endpoints hp P .left e.val he).1)).elim
        · have hzr : z.id ∈ m0GeodesicSideVertices hp P .right :=
            e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .right e.val he).2
          obtain ⟨j, hj⟩ := atSeam hz hzr
          exact ⟨j, hj ▸ Path.end_mem_vertices (q.cons e)⟩
  exact aux p hv

/-- Helper toward Lemma 5.6: every ambient competitor between two seam
vertices is dominated in the chosen metric mode by the retained seam
segment. The endpoints are automatically ordered by acyclicity. -/
theorem m0GeodesicSide_seamSegment_dominates
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    (i j : ℕ) (p : Path (P.codePath.initial i).1 (P.codePath.initial j).1) :
    ∃ r : Path (P.codePath.initial i).1 (P.codePath.initial j).1,
      (if longest then p.length ≤ r.length else r.length ≤ p.length) ∧
      ∀ e ∈ pathEdgeList r, e ∈ (m0GeodesicSide hp P s).edges := by
  have hij : i ≤ j := by
    by_contra hn
    have hji : j ≤ i := by omega
    have hs := P.codePath.exists_shift_split j (i - j)
    rw [Nat.add_sub_of_le hji] at hs
    obtain ⟨_, r, _, _, hlen, _⟩ := hs
    have hz := presentVertex_acyclic (shiftedStream W 0) _ (r.comp p)
    rw [Path.length_comp, hlen] at hz
    omega
  have hs := P.codePath.exists_shift_split i (j - i)
  rw [Nat.add_sub_of_le hij] at hs
  obtain ⟨q, r, heq, _, _, hlist⟩ := hs
  refine ⟨r, ?_, ?_⟩
  · cases longest with
    | false =>
      have hop := P.codePath.initial_isShortest (shiftedStream W 0) P.segments j
      rw [heq] at hop
      exact hop.of_comp_right p
    | true =>
      have hop := P.codePath.initial_isLongest (shiftedStream W 0) P.segments j
      rw [heq] at hop
      exact hop.of_comp_right p
  · intro e he
    rw [hlist] at he
    obtain ⟨a, ha⟩ := List.mem_ofFn.mp he
    rw [← ha]
    have hm := m0GeodesicEdges_subset_both hp P ⟨i + a.val, rfl⟩
    cases s
    · exact hm.1
    · exact hm.2

/-- Helper toward Lemma 5.6: any ambient finite path between left-side
vertices has a left-side competitor at least as good in the chosen metric
mode. Every excursion is replaced by a segment of the bounding geodesic. -/
theorem m0GeodesicLeftSide_path_dominance
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {u v : PresentVertex (shiftedStream W 0)} (p : Path u v)
    (hu : u.id ∈ (m0GeodesicSide hp P .left).vertices)
    (hv : v.id ∈ (m0GeodesicSide hp P .left).vertices) :
    ∃ r : Path u v,
      (if longest then p.length ≤ r.length else r.length ≤ p.length) ∧
      ∀ e ∈ pathEdgeList r, e ∈ (m0GeodesicSide hp P .left).edges := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    by_cases hz : p.length = 0
    · obtain rfl := p.eq_of_length_zero hz
      obtain rfl := p.eq_nil_of_length_zero hz
      exact ⟨.nil, by cases longest <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          simp only [Path.length_nil] at hn ⊢ <;> omega,
        fun _ he => False.elim (List.not_mem_nil he)⟩
    · obtain ⟨b, e, t, hp', hlen⟩ := p.length_ne_zero_iff_eq_comp.mp hz
      by_cases he : e.val ∈ (m0GeodesicSide hp P .left).edges
      · have hbl : b.id ∈ (m0GeodesicSide hp P .left).vertices :=
          e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .left e.val he).2
        obtain ⟨r, hrlen, hr⟩ := ih t.length (by omega) t hbl hv rfl
        refine ⟨e.toPath.comp r, ?_, ?_⟩
        · rw [← hn, hp', Path.length_comp, Path.length_comp]
          cases longest <;> exact Nat.add_le_add_left hrlen _
        · intro f hf
          rw [pathEdgeList_comp] at hf
          rcases List.mem_append.mp hf with hf | hf
          · have hfe : f = e.val := by
              change f ∈ ([] ++ [e.val]) at hf
              exact List.mem_singleton.mp hf
            exact hfe ▸ he
          · exact hr f hf
      · have her := (m0GeodesicSideEdges_cover hp P e.val).resolve_left he
        have hur : u.id ∈ m0GeodesicSideVertices hp P .right :=
          e.property.2.1 ▸ (m0GeodesicSide_endpoints hp P .right e.val her).1
        have hus : u.id ∈ m0GeodesicVertices P := by
          rw [← m0GeodesicSideVertices_inter hp P]
          exact ⟨hu, hur⟩
        obtain ⟨i, hi⟩ := hus
        have hi' : (P.codePath.initial i).1 = u := congrArg PresentVertex.mk hi
        have hbr : b.id ∈ m0GeodesicSideVertices hp P .right :=
          e.property.2.2 ▸ (m0GeodesicSide_endpoints hp P .right e.val her).2
        obtain ⟨j, hj⟩ := m0GeodesicSide_path_hits_seam hp P t hbr hv
        obtain ⟨s, t', ht⟩ := t.exists_eq_comp_of_mem_vertices hj
        have hex : ∃ r : Path u (P.codePath.initial j).1,
            (if longest then (e.toPath.comp s).length ≤ r.length
              else r.length ≤ (e.toPath.comp s).length) ∧
            ∀ f ∈ pathEdgeList r, f ∈ (m0GeodesicSide hp P .left).edges := by
          subst u
          exact m0GeodesicSide_seamSegment_dominates hp P .left i j (e.toPath.comp s)
        obtain ⟨r, hrlen, hr⟩ := hex
        have hjl : (P.codePath.initial j).1.id ∈
            (m0GeodesicSide hp P .left).vertices := by
          have hm := m0Geodesic_initial_mem_vertices P j
          rw [← m0GeodesicSideVertices_inter hp P] at hm
          exact hm.1
        have hsplit : p.length = 1 + s.length + t'.length := by
          rw [hp', ht, Path.length_comp, Path.length_comp, Path.length_toPath]
          omega
        obtain ⟨r', hr'len, hr'⟩ := ih t'.length (by omega) t' hjl hv rfl
        refine ⟨r.comp r', ?_, ?_⟩
        · simp only [Path.length_comp, Path.length_toPath] at hrlen ⊢
          cases longest <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrlen hr'len ⊢ <;>
            omega
        · intro f hf
          rw [pathEdgeList_comp] at hf
          exact (List.mem_append.mp hf).elim (hr f) (hr' f)

private theorem geometricSideDirectedWalk_snoc {M : GeometricSideSubmap}
    {n : ℕ} {u v w : GeometricSideCell M}
    (hwalk : GeometricSideDirectedWalk M n u v)
    (hstep : geometricSideDirectedStep M v w) :
    GeometricSideDirectedWalk M (n + 1) u w := by
  induction hwalk with
  | nil => exact .cons hstep (.nil _)
  | cons hs _ ih => exact .cons hs (ih hstep)

/-- Helper toward Lemma 5.6: a finite ambient path whose individual edges
are retained is a walk in the stored side relations, of the same length. -/
theorem m0GeodesicSide_walk_of_path
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (s : ThinMapSide)
    {u v : PresentVertex (shiftedStream W 0)} (p : Path u v)
    (hu : u.id ∈ (m0GeodesicSide hp P s).vertices)
    (hv : v.id ∈ (m0GeodesicSide hp P s).vertices)
    (hedges : ∀ e ∈ pathEdgeList p, e ∈ (m0GeodesicSide hp P s).edges) :
    GeometricSideDirectedWalk (m0GeodesicSide hp P s) p.length
      (.inl ⟨u.id, hu⟩) (.inl ⟨v.id, hv⟩) := by
  let M := m0GeodesicSide hp P s
  have aux : ∀ {z : PresentVertex (shiftedStream W 0)} (q : Path u z)
      (hz : z.id ∈ M.vertices),
      (∀ e ∈ pathEdgeList q, e ∈ M.edges) →
      GeometricSideDirectedWalk M q.length (.inl ⟨u.id, hu⟩) (.inl ⟨z.id, hz⟩) := by
    intro z q
    induction q with
    | nil => intro _ _; exact .nil _
    | @cons y z q e ih =>
      intro hz hq
      have he : e.val ∈ M.edges := hq e.val (by
        change e.val ∈ pathEdgeList q ++ [e.val]
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
      have hy : y.id ∈ M.vertices :=
        e.property.2.1 ▸ (m0GeodesicSide_endpoints hp P s e.val he).1
      have hwalk := ih hy (fun f hf => hq f (by
        change f ∈ pathEdgeList q ++ [e.val]
        exact List.mem_append.mpr (Or.inl hf)))
      have hstep : geometricSideDirectedStep M (.inl ⟨y.id, hy⟩) (.inl ⟨z.id, hz⟩) :=
        (geometricSideDirectedStep_vertices_iff M _ _).2
          ⟨e.val, he, e.property.1, e.property.2.1, e.property.2.2⟩
      exact geometricSideDirectedWalk_snoc hwalk hstep
  exact aux p hv hedges

/-- Helper toward Lemma 5.6: attained intrinsic optimal lengths in the
realized left side are attained ambient optimal lengths, in both modes.
The excursion-replacement theorem discharges the ambient comparisons. -/
theorem m0GeodesicLeftSide_optimalLength_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {k : ℤ}
    (P : M0CutInfiniteGeodesic W H h hLL k longest) (n : ℕ)
    (u v : (m0GeodesicSide hp P .left).vertices)
    (hopt : geometricSideOptimalLength (m0GeodesicSide hp P .left) longest n
      (.inl u) (.inl v)) :
    ∃ p : Path (⟨u.val⟩ : PresentVertex (shiftedStream W 0)) ⟨v.val⟩,
      p.length = n ∧ (if longest then IsLongest p else IsShortest p) := by
  obtain ⟨p, hpLen⟩ := m0GeodesicSide_walk_lifts hp P .left n u v hopt.1
  refine ⟨p, hpLen, ?_⟩
  cases longest with
  | false =>
    intro q
    obtain ⟨r, hr, he⟩ := m0GeodesicLeftSide_path_dominance hp P q u.property v.property
    have hw := m0GeodesicSide_walk_of_path hp P .left r u.property v.property he
    have ho : n ≤ r.length := hopt.2 r.length hw
    rw [hpLen]
    exact ho.trans hr
  | true =>
    intro q
    obtain ⟨r, hr, he⟩ := m0GeodesicLeftSide_path_dominance hp P q u.property v.property
    have hw := m0GeodesicSide_walk_of_path hp P .left r u.property v.property he
    have ho : r.length ≤ n := hopt.2 r.length hw
    rw [hpLen]
    exact hr.trans ho



































































































end DirectedDistances.PaperProofs.Section5
