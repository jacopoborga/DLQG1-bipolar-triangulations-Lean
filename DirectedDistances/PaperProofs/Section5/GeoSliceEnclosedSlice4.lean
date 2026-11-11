/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoSliceEnclosedSlice3
import Mathlib.Topology.Connected.LocallyPathConnected
import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier

/-! Open geometric overlap components and finite arc contacts along their paths.
The conversion of a geometric path to a retained dual chain remains separate. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section4
open scoped Topology

variable {W : ℤ → Fin 3} {H : WholePlaneRotationHypothesis W}
  {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0
      (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1))))}

/-- Helper toward Lemma 5.6: the literal geodesic trace is closed in the
plane, including when its abscissas have a finite upper endpoint. -/
theorem m0GeodesicTrace_isClosed
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) :
    IsClosed (m0GeodesicTrace hp Q) := by
  have hproper := m0GeodesicTrace_properGraphRay hp Q
  have hclosed := isClosed_closedBetween hproper hproper
  obtain ⟨X, f, _, _, hgraph, _⟩ := hproper
  have heq : closedBetween (m0GeodesicTrace hp Q) (m0GeodesicTrace hp Q) =
      m0GeodesicTrace hp Q := by
    ext z
    rw [mem_closedBetween_iff hgraph hgraph, hgraph]
    constructor
    · rintro ⟨hz, hlo, hhi⟩
      exact ⟨hz, le_antisymm (hhi hz) hlo⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, he.ge, fun _ => he.le⟩
  exact heq ▸ hclosed

/-- Helper toward Lemma 5.6: inside the ambient interior, the chosen left
component is open in the plane. Boundary points of the closed ambient map
are deliberately excluded from this statement. -/
theorem m0GeodesicLeftOpen_inter_interior_ambient_isOpen
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) :
    IsOpen (m0GeodesicLeftOpen hp Q ∩
      interior (m0GeodesicAmbientRegion W H h)) := by
  apply Metric.isOpen_iff.mpr
  rintro z ⟨hzL, hzA⟩
  have hzT := (m0GeodesicLeftOpen_subset hp Q hzL).2
  have hopen : IsOpen (interior (m0GeodesicAmbientRegion W H h) \
      m0GeodesicTrace hp Q) :=
    isOpen_interior.sdiff (m0GeodesicTrace_isClosed hp Q)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z ⟨hzA, hzT⟩
  refine ⟨ε, hε, fun q hq => ⟨?_, (hball hq).1⟩⟩
  have hsub : Metric.ball z ε ⊆
      m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp Q :=
    fun q hq => ⟨interior_subset (hball hq).1, (hball hq).2⟩
  have hcomp : connectedComponentIn
      (m0GeodesicAmbientRegion W H h \ m0GeodesicTrace hp Q) z =
        m0GeodesicLeftOpen hp Q :=
    (connectedComponentIn_eq hzL).symm
  rw [← hcomp]
  exact (convex_ball z ε).isPreconnected.subset_connectedComponentIn
    (Metric.mem_ball_self hε) hsub hq

/-- Helper toward Lemma 5.6: each retained future face lies strictly in the
ambient interior. A face cannot be supported only on the geometric seam. -/
theorem m0Geodesic_retained_face_subset_interior_ambient
    (hp : BoundaryHitWitnesses (kmswPastCode W))
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hF : F.val ⊆ m0GeodesicAmbientRegion W H h) :
    F.val ⊆ interior (m0GeodesicAmbientRegion W H h) := by
  obtain ⟨F0, hF0, hval⟩ := m0Geodesic_retained_face_runZero hp F hF
  let U : Set ℂ := {z | seamFun (shiftedStream W 0) h (H.1 0) z.re < z.im}
  have hU : IsOpen U := isOpen_lt
    ((seamFun_continuous (shiftedStream W 0) h (H.1 0)).comp Complex.continuous_re)
    Complex.continuous_im
  have hUA : U ⊆ m0GeodesicAmbientRegion W H h := by
    intro z hz
    change seamFun (shiftedStream W 0) h (H.1 0) z.re ≤ z.im
    exact hz.le
  have hUi := hU.subset_interior_iff.mpr hUA
  intro z hz
  apply hUi
  exact boundedFace_subset_upper (shiftedStream W 0) h (H.1 0) F0 hF0
    (hval ▸ hz)

/-- Helper toward Lemma 5.6: the part of the overlap strictly above the
ambient seam is open in the plane. This uses the actual geometric side
components, rather than an assumed face-chain characterization. -/
theorem m0Geodesic_overlap_interior_isOpen
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest) :
    IsOpen ((m0GeodesicLeftOpen hp P ∩
      interior (m0GeodesicAmbientRegion W H h)) \
        closure (m0GeodesicLeftOpen hp Q)) :=
  (m0GeodesicLeftOpen_inter_interior_ambient_isOpen hp P).sdiff isClosed_closure


/-- Helper toward Lemma 5.6: raising a point of the actual left component
by a positive vertical displacement keeps it on the left and moves it into
the ambient interior. -/
theorem m0GeodesicLeftOpen_raise_mem_interior
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    {z : ℂ} (hz : z ∈ m0GeodesicLeftOpen hp Q) {ε : ℝ} (hε : 0 < ε) :
    z + (ε : ℂ) * Complex.I ∈ m0GeodesicLeftOpen hp Q ∩
      interior (m0GeodesicAmbientRegion W H h) := by
  have hre : (z + (ε : ℂ) * Complex.I).re = z.re := by simp
  have him : (z + (ε : ℂ) * Complex.I).im = z.im + ε := by simp
  have hza := (m0GeodesicLeftOpen_subset hp Q hz).1
  have habove : seamFun (shiftedStream W 0) h (H.1 0)
      (z + (ε : ℂ) * Complex.I).re < (z + (ε : ℂ) * Complex.I).im := by
    rw [hre, him]
    exact lt_of_le_of_lt hza (lt_add_of_pos_right _ hε)
  have hzi : z + (ε : ℂ) * Complex.I ∈
      interior (m0GeodesicAmbientRegion W H h) := by
    let A : Set ℂ := {p | seamFun (shiftedStream W 0) h (H.1 0) p.re < p.im}
    have hA : IsOpen A := isOpen_lt
      ((seamFun_continuous (shiftedStream W 0) h (H.1 0)).comp Complex.continuous_re)
      Complex.continuous_im
    have hsub : A ⊆ m0GeodesicAmbientRegion W H h := by
      intro p hp
      change seamFun (shiftedStream W 0) h (H.1 0) p.re ≤ p.im
      exact hp.le
    exact hA.subset_interior_iff.mpr hsub habove
  refine ⟨?_, hzi⟩
  apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp Q _).mpr
  refine ⟨interior_subset hzi, ?_⟩
  rcases ((m0CutGeodesicLeftOpen_iff_west_or_above_trace hp Q z).mp hz).2 with
    hw | ⟨y, hy, hxy, hyy⟩
  · exact Or.inl (hre ▸ hw)
  · exact Or.inr ⟨y, hy, hxy.trans hre.symm,
      hyy.trans (him ▸ lt_add_of_pos_right z.im hε)⟩

/-- Helper toward Lemma 5.6: the strict ambient part of an actual left
side is path connected. Connectedness is proved from vertical translations
of its defining component; it is not an added premise. -/
theorem m0GeodesicLeftOpen_inter_interior_ambient_isPathConnected
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest) :
    IsPathConnected (m0GeodesicLeftOpen hp Q ∩
      interior (m0GeodesicAmbientRegion W H h)) := by
  let U := m0GeodesicLeftOpen hp Q ∩ interior (m0GeodesicAmbientRegion W H h)
  have hopen : IsOpen U := m0GeodesicLeftOpen_inter_interior_ambient_isOpen hp Q
  apply hopen.isConnected_iff_isPathConnected.mp
  refine ⟨?_, ?_⟩
  · exact ⟨_, m0GeodesicLeftOpen_raise_mem_interior hp Q
      (m0Geodesic_previous_pos_mem_leftOpen hp Q) (show (0 : ℝ) < 1 by norm_num)⟩
  · apply isPreconnected_of_forall_pair
    intro x hx y hy
    obtain ⟨r, hr, hxr⟩ := Metric.isOpen_iff.mp hopen x hx
    obtain ⟨s, hs, hys⟩ := Metric.isOpen_iff.mp hopen y hy
    let ε := min r s / 2
    have hε : 0 < ε := half_pos (lt_min hr hs)
    have hεr : ε < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
    have hεs : ε < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
    have hdist (p : ℂ) : dist (p - (ε : ℂ) * Complex.I) p = ε := by
      simp only [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_of_pos hε]
    have hxlow : x - (ε : ℂ) * Complex.I ∈ m0GeodesicLeftOpen hp Q :=
      (hxr (by rw [Metric.mem_ball, hdist]; exact hεr)).1
    have hylow : y - (ε : ℂ) * Complex.I ∈ m0GeodesicLeftOpen hp Q :=
      (hys (by rw [Metric.mem_ball, hdist]; exact hεs)).1
    let raise : ℂ → ℂ := fun p => p + (ε : ℂ) * Complex.I
    have hraise : Continuous raise := by fun_prop
    refine ⟨raise '' m0GeodesicLeftOpen hp Q, ?_, ?_, ?_, ?_⟩
    · rintro p ⟨q, hq, rfl⟩
      exact m0GeodesicLeftOpen_raise_mem_interior hp Q hq hε
    · exact ⟨x - (ε : ℂ) * Complex.I, hxlow, sub_add_cancel _ _⟩
    · exact ⟨y - (ε : ℂ) * Complex.I, hylow, sub_add_cancel _ _⟩
    · exact (show IsPreconnected (m0GeodesicLeftOpen hp Q) from
        isPreconnected_connectedComponentIn).image raise hraise.continuousOn


/-- Helper toward Lemma 5.6: every component of the strict geometric
overlap accumulates at the preceding trace, at a point still strictly inside
the current left side. No face-chain or component-connectivity premise is used. -/
theorem m0Geodesic_overlap_component_closure_meets_trace
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {z : ℂ}
    (hz : z ∈ (m0GeodesicLeftOpen hp P ∩
      interior (m0GeodesicAmbientRegion W H h)) \
        closure (m0GeodesicLeftOpen hp Q)) :
    ∃ q, q ∈ closure (connectedComponentIn
        ((m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h)) \
          closure (m0GeodesicLeftOpen hp Q)) z) ∧
      q ∈ m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h) ∧
      q ∈ m0GeodesicTrace hp Q := by
  let L := m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h)
  let U := L \ closure (m0GeodesicLeftOpen hp Q)
  let C := connectedComponentIn U z
  have hUopen : IsOpen U := m0Geodesic_overlap_interior_isOpen hp Q P
  have hCopen : IsOpen C := hUopen.connectedComponentIn
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCU : C ⊆ U := connectedComponentIn_subset U z
  have hCclose : closure C ∩ U ⊆ C := by
    intro q hq
    have hc : IsPreconnected (insert q C) :=
      (show IsPreconnected C from isPreconnected_connectedComponentIn).subset_closure
        (Set.subset_insert _ _) (Set.insert_subset hq.1 subset_closure)
    exact hc.subset_connectedComponentIn
      (Set.mem_insert_of_mem _ hzC) (Set.insert_subset hq.2 hCU) (Set.mem_insert _ _)
  have hcontact : ∃ q ∈ closure C ∩ L, q ∉ C := by
    by_contra hnone
    have hclose : closure C ∩ L ⊆ C := by
      intro q hq
      by_contra hnq
      exact hnone ⟨q, hq, hnq⟩
    have hLC : L ⊆ C :=
      (m0GeodesicLeftOpen_inter_interior_ambient_isPathConnected hp P).isConnected.isPreconnected.subset_of_closure_inter_subset
        hCopen ⟨z, hz.1, hzC⟩ hclose
    let a := min (seamX (shiftedStream W 0) h (H.1 0) j)
      (seamX (shiftedStream W 0) h (H.1 0) k) - 1
    let p : ℂ := ⟨a, seamFun (shiftedStream W 0) h (H.1 0) a⟩
    have hpa : p ∈ m0GeodesicAmbientRegion W H h := by
      change seamFun (shiftedStream W 0) h (H.1 0) a ≤
        seamFun (shiftedStream W 0) h (H.1 0) a
      exact le_rfl
    have hpQ : p ∈ m0GeodesicLeftOpen hp Q := by
      apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp Q p).mpr
      refine ⟨hpa, Or.inl ?_⟩
      change min _ _ - 1 < _
      linarith only [min_le_left (seamX (shiftedStream W 0) h (H.1 0) j)
        (seamX (shiftedStream W 0) h (H.1 0) k)]
    have hpP : p ∈ m0GeodesicLeftOpen hp P := by
      apply (m0CutGeodesicLeftOpen_iff_west_or_above_trace hp P p).mpr
      refine ⟨hpa, Or.inl ?_⟩
      change min _ _ - 1 < _
      linarith only [min_le_right (seamX (shiftedStream W 0) h (H.1 0) j)
        (seamX (shiftedStream W 0) h (H.1 0) k)]
    have hpL := m0GeodesicLeftOpen_raise_mem_interior hp P hpP
      (show (0 : ℝ) < 1 by norm_num)
    have hpB := (m0GeodesicLeftOpen_raise_mem_interior hp Q hpQ
      (show (0 : ℝ) < 1 by norm_num)).1
    exact (hCU (hLC hpL)).2 (subset_closure hpB)
  obtain ⟨q, hq, hqC⟩ := hcontact
  have hqBcl : q ∈ closure (m0GeodesicLeftOpen hp Q) := by
    by_contra hqB
    exact hqC (hCclose ⟨hq.1, hq.2, hqB⟩)
  have havoid : closure C ⊆
      (m0GeodesicLeftOpen hp Q ∩ interior (m0GeodesicAmbientRegion W H h))ᶜ := by
    apply closure_minimal _
      (m0GeodesicLeftOpen_inter_interior_ambient_isOpen hp Q).isClosed_compl
    intro p hpC hpB
    exact (hCU hpC).2 (subset_closure hpB.1)
  refine ⟨q, hq.1, hq.2, ?_⟩
  by_contra hqT
  have hqB := m0GeodesicLeftOpen_closure_inter_complement_subset hp Q
    ⟨hqBcl, interior_subset hq.2.2, hqT⟩
  exact havoid hq.1 ⟨hqB, hq.2.2⟩


/-- Helper toward Lemma 5.6: from any point of a retained overlap face,
there are paths inside the actual overlap to points arbitrarily close to
the preceding ray. Each chosen path meets only finitely many whole-plane
geometric darts. This supplies a geometric path, not a dual face chain. -/
theorem m0Geodesic_overlap_face_paths_near_trace_finite_arcs
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right)
    {z : ℂ} (hzF : z ∈ F.val) :
    ∃ q ∈ m0GeodesicTrace hp Q,
      q ∈ m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h) ∧
      ∀ ε : ℝ, 0 < ε → ∃ y : ℂ, dist q y < ε ∧
        ∃ γ : Path z y,
          (∀ t, γ t ∈ (m0GeodesicLeftOpen hp P ∩
            interior (m0GeodesicAmbientRegion W H h)) \
              closure (m0GeodesicLeftOpen hp Q)) ∧
          {d : WholePlaneDart W |
            (Set.range γ ∩
              ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc d).image).Nonempty}.Finite := by
  let U := (m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h)) \
    closure (m0GeodesicLeftOpen hp Q)
  let C := connectedComponentIn U z
  have hzU : z ∈ U := ⟨⟨hFL hzF,
    m0Geodesic_retained_face_subset_interior_ambient hp F (fun p hpF => (hFR hpF).1)
      hzF⟩, (hFR hzF).2⟩
  obtain ⟨q, hqcl, hqL, hqT⟩ := m0Geodesic_overlap_component_closure_meets_trace
    hp Q P hzU
  refine ⟨q, hqT, hqL, fun ε hε => ?_⟩
  have hCopen : IsOpen C :=
    (m0Geodesic_overlap_interior_isOpen hp Q P).connectedComponentIn
  have hCpath : IsPathConnected C := hCopen.isConnected_iff_isPathConnected.mp
    (isConnected_connectedComponentIn_iff.mpr hzU)
  obtain ⟨y, hyC, hqy⟩ := Metric.mem_closure_iff.mp hqcl ε hε
  have hjoin : JoinedIn C z y := hCpath.joinedIn z (mem_connectedComponentIn hzU) y hyC
  refine ⟨y, hqy, hjoin.somePath, ?_, ?_⟩
  · intro t
    exact connectedComponentIn_subset U z (hjoin.somePath_mem t)
  · exact (WholePlanePastGlueDrawing.glueDrawing W h hp H).locally_finite
      (Set.range hjoin.somePath) (isCompact_range hjoin.somePath.continuous).isBounded

/-- Helper toward Lemma 5.6: an actual overlap path avoids both literal
bounding traces, so none of its arc contacts can be a ray edge. This still
allows contacts with off-ray vertices. -/
theorem m0Geodesic_overlap_path_avoids_ray_arcs
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {z y : ℂ} (γ : Path z y)
    (hγ : ∀ t, γ t ∈ (m0GeodesicLeftOpen hp P ∩
      interior (m0GeodesicAmbientRegion W H h)) \
        closure (m0GeodesicLeftOpen hp Q)) (n : ℕ) :
    Disjoint (Set.range γ)
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (m0GeodesicSeam Q n))).image ∧
    Disjoint (Set.range γ)
      ((WholePlanePastGlueDrawing.glueDrawing W h hp H).arc
        (wholePlaneDartι W 0 (m0GeodesicSeam P n))).image := by
  constructor
  · apply Set.disjoint_left.mpr
    rintro p ⟨t, rfl⟩ hpQ
    exact (hγ t).2 (m0GeodesicTrace_subset_closure_leftOpen hp Q
      (m0Geodesic_arc_subset_trace hp Q n hpQ))
  · apply Set.disjoint_left.mpr
    rintro p ⟨t, rfl⟩ hpP
    exact (m0GeodesicLeftOpen_subset hp P (hγ t).1.1).2
      (m0Geodesic_arc_subset_trace hp P n hpP)


/-- Helper toward Lemma 5.6: a trace contact in the strict interior of the
current left side has an incident retained overlap face, with the correct
reverse-ray orientation. The contact belongs to that face's closure. -/
theorem m0Geodesic_trace_contact_has_ray_incident_overlap_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    {q : ℂ} (hqT : q ∈ m0GeodesicTrace hp Q)
    (hqL : q ∈ m0GeodesicLeftOpen hp P ∩
      interior (m0GeodesicAmbientRegion W H h)) :
    ∃ (n : ℕ) (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, true)) F ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp P .left ∧
      F.val ⊆ m0GeodesicSideOpenRegion hp Q .right ∧
      q ∈ closure F.val := by
  let G := WholePlanePastGlueDrawing.glueDrawing W h hp H
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hqT
  obtain ⟨F, hb⟩ := WholePlaneGlueFaceCorrespondenceFull.dart_borders_exists
    W h hp H (wholePlaneDartι W 0 (Q.codePath.edge n, true))
  have hqrev : q ∈ (G.arc (wholePlaneDartι W 0 (Q.codePath.edge n, true))).image := by
    have hf := G.arc_flip (wholePlaneDartι W 0 (Q.codePath.edge n, false))
    change G.arc (wholePlaneDartι W 0 (Q.codePath.edge n, true)) = _ at hf
    rw [hf, Polyline.image_reverse_transfer]
    exact hn
  have hqF : q ∈ closure F.val := G.dartBorders_arc_subset_closure
    (uibhbot_faceOrbit_dartVertex_surjective W H) _ F hb hqrev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (m0GeodesicLeftOpen_inter_interior_ambient_isOpen hp P) q hqL
  obtain ⟨z, hzF, hqz⟩ := Metric.mem_closure_iff.mp hqF ε hε
  have hzL := hball (show z ∈ Metric.ball q ε by
    rw [Metric.mem_ball, dist_comm]
    exact hqz)
  have hFA : F.val ⊆ m0GeodesicAmbientRegion W H h :=
    (m0CutFace_subset_ambient_iff_mem hp F hzF).mpr (interior_subset hzL.2)
  exact ⟨n, F, hb,
    (m0CutFace_subset_sideOpenRegion_iff_mem hp P F .left hzF hFA).mpr hzL.1,
    m0Geodesic_reverse_seam_face_right hp Q n F hFA hb, hqF⟩

/-- Helper toward Lemma 5.6: every retained overlap face has a strict
component contact with a ray-incident overlap face. Both closure memberships
are constructed; a discrete chain between the faces is not asserted. -/
theorem m0Geodesic_overlap_face_component_contacts_ray_face
    (hp : BoundaryHitWitnesses (kmswPastCode W)) {longest : Bool} {j k : ℤ}
    (Q : M0CutInfiniteGeodesic W H h hLL j longest)
    (P : M0CutInfiniteGeodesic W H h hLL k longest)
    (F : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face)
    (hFL : F.val ⊆ m0GeodesicSideOpenRegion hp P .left)
    (hFR : F.val ⊆ m0GeodesicSideOpenRegion hp Q .right)
    {z : ℂ} (hzF : z ∈ F.val) :
    ∃ (q : ℂ) (n : ℕ) (G : (WholePlanePastGlueDrawing.glueDrawing W h hp H).Face),
      q ∈ closure (connectedComponentIn
        ((m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h)) \
          closure (m0GeodesicLeftOpen hp Q)) z) ∧
      q ∈ m0GeodesicLeftOpen hp P ∩ interior (m0GeodesicAmbientRegion W H h) ∧
      q ∈ m0GeodesicTrace hp Q ∧ q ∈ closure G.val ∧
      (WholePlanePastGlueDrawing.glueDrawing W h hp H).dartBorders
        (wholePlaneDartι W 0 (Q.codePath.edge n, true)) G ∧
      G.val ⊆ m0GeodesicSideOpenRegion hp P .left ∧
      G.val ⊆ m0GeodesicSideOpenRegion hp Q .right := by
  have hzU : z ∈ (m0GeodesicLeftOpen hp P ∩
      interior (m0GeodesicAmbientRegion W H h)) \
        closure (m0GeodesicLeftOpen hp Q) :=
    ⟨⟨hFL hzF, m0Geodesic_retained_face_subset_interior_ambient hp F
      (fun p hpF => (hFR hpF).1) hzF⟩, (hFR hzF).2⟩
  obtain ⟨q, hqC, hqL, hqT⟩ := m0Geodesic_overlap_component_closure_meets_trace hp Q P hzU
  obtain ⟨n, G, hb, hGL, hGR, hqG⟩ :=
    m0Geodesic_trace_contact_has_ray_incident_overlap_face hp Q P hqT hqL
  exact ⟨q, n, G, hqC, hqL, hqT, hqG, hb, hGL, hGR⟩

end DirectedDistances.PaperProofs.Section5





































































































































































































