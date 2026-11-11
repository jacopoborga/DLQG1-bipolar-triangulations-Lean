module

public import DirectedDistances.PlanarMap.D39PLSimpleArcParam
public import DirectedDistances.PlanarMap.D39PolygonalConnected2

public section
noncomputable section

namespace DirectedDistances.PlanarMap

open Set

/-- Helper toward Proposition 5.16: the image of a two-point polyline is
exactly the segment between its endpoints. -/
private theorem image_twoPointPolyline (x y : ℂ) :
    (⟨[x, y], by simp⟩ : Polyline).image = segment ℝ x y := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | ⟨i, hi, hz⟩
    · rw [mem_singleton_iff] at hz
      subst z
      change x ∈ segment ℝ x y
      exact left_mem_segment ℝ x y
    · have hi0 : i = 0 := by
        change i + 1 < 2 at hi
        omega
      subst i
      simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz
  · intro hz
    refine Or.inr ⟨0, by simp, ?_⟩
    simpa [Polyline.segmentAt, Polyline.point, Polyline.start] using hz

/-- Helper toward Proposition 5.16: any two points in an open connected
subset of the plane are joined by a polyline contained in that set. -/
theorem exists_polyline_in_open_connected {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsConnected U) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧ p.image ⊆ U := by
  let R : Set ℂ := {z | z ∈ U ∧ ∃ p : Polyline,
    p.start = x ∧ p.finish = z ∧ p.image ⊆ U}
  have hxR : x ∈ R := by
    refine ⟨hx, ?_⟩
    let p : Polyline := ⟨[x], by simp⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · intro z hz
      simp [Polyline.image, p, Polyline.start] at hz ⊢
      exact hz ▸ hx
  have hRopen : IsOpen R := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    rcases hz with ⟨hzU, p, hpstart, hpfinish, hpimage⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
    refine ⟨r, hr, ?_⟩
    intro w hw
    let q : Polyline := ⟨[z, w], by simp⟩
    have hqstart : q.start = z := rfl
    have hqfinish : q.finish = w := rfl
    have hseg : segment ℝ z w ⊆ U :=
      ((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw).trans hball
    have hjoin : p.finish = q.start := hpfinish.trans hqstart
    refine ⟨hball hw, Polyline.boundaryConcat p q, ?_, ?_, ?_⟩
    · simpa [Polyline.start_boundaryConcat] using hpstart
    · rw [Polyline.finish_boundaryConcat (p := p) (q := q) (by simp [q])]
      exact hqfinish
    · rw [Polyline.image_boundaryConcat p q hjoin, image_twoPointPolyline]
      exact union_subset hpimage hseg
  have hUminusRopen : IsOpen (U \ R) := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨hzU, hzR⟩ := hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hzU
    refine ⟨r, hr, ?_⟩
    intro w hw
    refine ⟨hball hw, ?_⟩
    intro hwR
    rcases hwR with ⟨hwU, p, hpstart, hpfinish, hpimage⟩
    let q : Polyline := ⟨[w, z], by simp⟩
    have hqstart : q.start = w := rfl
    have hqfinish : q.finish = z := rfl
    have hseg : segment ℝ w z ⊆ U :=
      ((convex_ball z r).segment_subset hw (Metric.mem_ball_self hr)).trans hball
    have hjoin : p.finish = q.start := hpfinish.trans hqstart
    have hzR' : z ∈ R := by
      refine ⟨hzU, Polyline.boundaryConcat p q, ?_, ?_, ?_⟩
      · simpa [Polyline.start_boundaryConcat] using hpstart
      · rw [Polyline.finish_boundaryConcat (p := p) (q := q) (by simp [q])]
        exact hqfinish
      · rw [Polyline.image_boundaryConcat p q hjoin, image_twoPointPolyline]
        exact union_subset hpimage hseg
    exact hzR hzR'
  have hcover : U ⊆ R ∪ (U \ R) := by
    intro z hz
    by_cases hzR : z ∈ R
    · exact Or.inl hzR
    · exact Or.inr ⟨hz, hzR⟩
  by_cases hyR : y ∈ R
  · rcases hyR with ⟨_, p, hpstart, hpfinish, hpimage⟩
    exact ⟨p, hpstart, hpfinish, hpimage⟩
  · have hdis : (U ∩ (R ∩ (U \ R))).Nonempty :=
      hconn.isPreconnected R (U \ R) hRopen hUminusRopen hcover
        ⟨x, hx, hxR⟩ ⟨y, hy, ⟨hy, hyR⟩⟩
    rcases hdis with ⟨z, _, hz⟩
    exact False.elim (hz.2.2 hz.1)

/-- Helper toward Proposition 5.16: among the polygonal routes in an open
connected set, one can choose a route whose vertex sequence is injective. -/
theorem exists_polyline_with_injective_vertices_of_open_connected
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U) {x y : ℂ}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ p : Polyline, p.start = x ∧ p.finish = y ∧ p.image ⊆ U ∧
      ∀ i j, i < p.points.length → j < p.points.length →
        p.point i = p.point j → i = j := by
  classical
  obtain ⟨p₀, hp₀s, hp₀f, hp₀im⟩ :=
    exists_polyline_in_open_connected hU hconn hx hy
  let P : ℕ → Prop := fun n => ∃ p : Polyline,
    p.start = x ∧ p.finish = y ∧ p.image ⊆ U ∧ p.points.length = n
  have hP : ∃ n, P n := by
    refine ⟨p₀.points.length, ?_⟩
    exact ⟨p₀, hp₀s, hp₀f, hp₀im, rfl⟩
  let n := Nat.find hP
  obtain ⟨p, hps, hpf, hpim, hlen⟩ := Nat.find_spec hP
  have hmin (q : Polyline) (hqs : q.start = x) (hqf : q.finish = y)
      (hqim : q.image ⊆ U) : n ≤ q.points.length := by
    apply Nat.find_min' hP
    exact ⟨q, hqs, hqf, hqim, rfl⟩
  refine ⟨p, hps, hpf, hpim, ?_⟩
  intro i j hi hj hij
  by_contra hne
  have hnoRepeat : ∀ a b, a < b → a < p.points.length → b < p.points.length →
      p.point a = p.point b → False := by
    intro a b hab ha hb heq
    let pre := p.intervalPolyline 0 a
    let suf := p.intervalPolyline b (p.points.length - b - 1)
    have hpreBound : 0 + a < p.points.length := by omega
    have hsufBound : b + (p.points.length - b - 1) < p.points.length := by omega
    have hjoin : pre.finish = suf.start := by
      simp only [pre, Polyline.finish_intervalPolyline, Nat.zero_add,
        suf, Polyline.start_intervalPolyline]
      exact heq
    have hstart : (Polyline.boundaryConcat pre suf).start = x := by
      simp [pre, Polyline.start_boundaryConcat, Polyline.start_intervalPolyline,
        Polyline.point_zero_eq_start, hps]
    have hfinish : (Polyline.boundaryConcat pre suf).finish = y := by
      rw [Polyline.finish_boundaryConcat_of_join pre suf hjoin,
        Polyline.finish_intervalPolyline,
        show b + (p.points.length - b - 1) = p.points.length - 1 by omega,
        p.point_last_eq_finish, hpf]
    have himage : (Polyline.boundaryConcat pre suf).image ⊆ U := by
      rw [Polyline.image_boundaryConcat pre suf hjoin]
      apply union_subset
      · exact (p.image_intervalPolyline_subset 0 a hpreBound).trans hpim
      · exact (p.image_intervalPolyline_subset b (p.points.length - b - 1)
          hsufBound).trans hpim
    have hshort : (Polyline.boundaryConcat pre suf).points.length < p.points.length := by
      rw [Polyline.length_boundaryConcat, Polyline.length_intervalPolyline,
        Polyline.length_intervalPolyline]
      omega
    have hleast := hmin (Polyline.boundaryConcat pre suf) hstart hfinish himage
    rw [hlen] at hshort
    omega
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact (hnoRepeat i j hij' hi hj hij).elim
  · exact (hnoRepeat j i hji' hj hi hij.symm).elim




















end DirectedDistances.PlanarMap
end
