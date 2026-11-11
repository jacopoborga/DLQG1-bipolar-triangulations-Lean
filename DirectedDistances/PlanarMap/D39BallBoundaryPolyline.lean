module

public import DirectedDistances.PlanarMap.D39ExternalFaceBall
public import DirectedDistances.PlanarMap.PLDrawingGeneralCarrier

public section

noncomputable section

namespace DirectedDistances.PlanarMap

namespace Polyline

/-- Helper toward Proposition 5.16: appending a polyline to a vertex list that
ends at its start adds exactly the appended polyline's image. -/
private theorem image_ofHead_append_tail (a : ℂ) (l : List ℂ) (q : Polyline)
    (hfinish : (ofHead a l).finish = q.start) :
    (ofHead a (l ++ q.points.tail)).image = (ofHead a l).image ∪ q.image := by
  induction l generalizing a with
  | nil =>
      have hstart : a = q.start := by
        simpa [ofHead, finish] using hfinish
      have hq : ofHead a q.points.tail = q := by
        cases q with
        | mk points hne =>
          cases points with
          | nil => exact (hne rfl).elim
          | cons b rest =>
              have hab : a = b := by simpa [start] using hstart
              subst b
              rfl
      change (ofHead a q.points.tail).image = _
      rw [hq]
      ext z
      constructor
      · intro hz
        exact Or.inr hz
      · rintro (hz | hz)
        · have hza : z = a := by simpa [image, ofHead, start] using hz
          subst z
          rw [hstart]
          exact Or.inl rfl
        · exact hz
  | cons b l ih =>
      have htail : (ofHead b l).finish = q.start := by
        simpa [ofHead, finish] using hfinish
      change (ofHead a (b :: (l ++ q.points.tail))).image = _
      calc
        (ofHead a (b :: (l ++ q.points.tail))).image =
            segment ℝ a b ∪ (ofHead b (l ++ q.points.tail)).image :=
          image_ofHead_cons a b (l ++ q.points.tail)
        _ = segment ℝ a b ∪ ((ofHead b l).image ∪ q.image) := by
          rw [ih b htail]
        _ = (ofHead a (b :: l)).image ∪ q.image := by
          rw [image_ofHead_cons]
          ac_rfl

/-- Helper toward Proposition 5.16: concatenate two polylines by joining the
last vertex of the first to the first vertex of the second without duplicating
that shared vertex. -/
@[expose] def boundaryConcat (p q : Polyline) : Polyline :=
  ⟨p.points ++ q.points.tail, by
    cases hp : p.points with
    | nil => exact (p.nonempty hp).elim
    | cons a l => simp⟩

/-- Helper toward Proposition 5.16: when the join points agree, concatenation
has exactly the union of the two polyline images. -/
theorem image_boundaryConcat (p q : Polyline) (hjoin : p.finish = q.start) :
    (boundaryConcat p q).image = p.image ∪ q.image := by
  cases p with
  | mk points hne =>
      cases points with
      | nil => exact (hne rfl).elim
      | cons a l =>
          change (ofHead a (l ++ q.points.tail)).image =
            (ofHead a l).image ∪ q.image
          apply image_ofHead_append_tail
          simpa [ofHead, finish] using hjoin

/-- Helper toward Proposition 5.16: concatenation starts where its first
polyline starts. -/
@[simp] theorem start_boundaryConcat (p q : Polyline) :
    (boundaryConcat p q).start = p.start := by
  cases p with
  | mk points hne =>
      cases points with
      | nil => exact (hne rfl).elim
      | cons a l => rfl

/-- Helper toward Proposition 5.16: if the second polyline has at least two
vertices, concatenation ends where it ends. -/
theorem finish_boundaryConcat (p q : Polyline) (hq : 2 ≤ q.points.length) :
    (boundaryConcat p q).finish = q.finish := by
  cases p with
  | mk ppoints hp =>
      cases ppoints with
      | nil => exact (hp rfl).elim
      | cons a pl =>
          cases q with
          | mk qpoints hqne =>
              cases qpoints with
              | nil => simp at hq
              | cons b qtail =>
                  cases qtail with
                  | nil => simp at hq
                  | cons d qrest => simp [boundaryConcat, finish]

end Polyline

/-- Helper toward Proposition 5.16: the polyline arc of a dart ends at the
start of the arc of its face successor. -/
theorem arc_finish_faceSucc {V : Type*} (B : D39FiniteBall) (vert : B.D → V)
    (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert) (d : B.D) :
    (P.arc d).finish = (P.arc (B.map.faceSucc d)).start := by
  rw [P.arc_finish, P.arc_start]
  have hv : vert (B.map.faceSucc d) = vert (B.map.edgeInv d) := by
    change vert (B.map.rot.symm (B.map.edgeInv d)) = vert (B.map.edgeInv d)
    calc
      vert (B.map.rot.symm (B.map.edgeInv d)) =
          vert (B.map.rot (B.map.rot.symm (B.map.edgeInv d))) :=
        (P.vert_rotation (B.map.rot.symm (B.map.edgeInv d))).symm
      _ = vert (B.map.edgeInv d) := by rw [B.map.rot.apply_symm_apply]
  exact congrArg P.pos hv.symm

/-- Helper toward Proposition 5.16: concatenate the first `n + 1` arcs in the
face-successor walk beginning at `d`. -/
@[expose] def faceWalkPolyline {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) : ℕ → Polyline
  | 0 => P.arc d
  | n + 1 =>
      Polyline.boundaryConcat (faceWalkPolyline B vert P d n)
        (P.arc ((B.map.faceSucc : B.D → B.D)^[n + 1] d))

/-- Helper toward Proposition 5.16: every finite initial face-successor walk
ends at the endpoint of its last dart arc. -/
theorem finish_faceWalkPolyline {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) :
    (faceWalkPolyline B vert P d n).finish =
      (P.arc ((B.map.faceSucc : B.D → B.D)^[n] d)).finish := by
  induction n with
  | zero => rfl
  | succ n _ =>
      rw [faceWalkPolyline, Polyline.finish_boundaryConcat _ _ (P.arc_length _)]

/-- Helper toward Proposition 5.16: consecutive polylines in a face-successor
walk meet at their common endpoint. -/
theorem finish_faceWalkPolyline_eq_next_start {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) :
    (faceWalkPolyline B vert P d n).finish =
      (P.arc ((B.map.faceSucc : B.D → B.D)^[n + 1] d)).start := by
  rw [finish_faceWalkPolyline]
  rw [Function.iterate_succ_apply']
  exact arc_finish_faceSucc B vert P ((B.map.faceSucc : B.D → B.D)^[n] d)

/-- Helper toward Proposition 5.16: a finite face-successor walk starts where
its first dart arc starts. -/
@[simp] theorem start_faceWalkPolyline {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) :
    (faceWalkPolyline B vert P d n).start = (P.arc d).start := by
  induction n with
  | zero => rfl
  | succ n ih => simp [faceWalkPolyline, ih]

/-- Helper toward Proposition 5.16: the face-successor permutation has a
positive point period on the finite dart set. -/
private theorem faceSucc_minimalPeriod_pos (B : D39FiniteBall) (d : B.D) :
    0 < Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d := by
  let f : B.D → B.D := B.map.faceSucc
  have hperiod : Function.IsPeriodicPt f (orderOf B.map.faceSucc) d := by
    change f^[orderOf B.map.faceSucc] d = d
    have hpow := congrArg (fun σ : Equiv.Perm B.D => σ d)
      (pow_orderOf_eq_one B.map.faceSucc)
    change (B.map.faceSucc ^ orderOf B.map.faceSucc) d = d at hpow
    simpa only [Equiv.Perm.coe_pow] using hpow
  exact Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos B.map.faceSucc) hperiod

/-- Helper toward Proposition 5.16: concatenating exactly one finite
face-successor cycle gives a closed polyline. -/
theorem faceWalkPolyline_closed {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) :
    let m := Function.minimalPeriod (B.map.faceSucc : B.D → B.D) d
    (faceWalkPolyline B vert P d (m - 1)).start =
      (faceWalkPolyline B vert P d (m - 1)).finish := by
  dsimp
  let f : B.D → B.D := B.map.faceSucc
  let m := Function.minimalPeriod f d
  have hm : 0 < m := faceSucc_minimalPeriod_pos B d
  have hlast : f^[m - 1 + 1] d = d := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact Function.iterate_minimalPeriod
  rw [start_faceWalkPolyline, finish_faceWalkPolyline]
  symm
  calc
    (P.arc (f^[m - 1] d)).finish = (P.arc (f (f^[m - 1] d))).start :=
      arc_finish_faceSucc B vert P (f^[m - 1] d)
    _ = (P.arc (f^[m - 1 + 1] d)).start := by rw [Function.iterate_succ_apply']
    _ = (P.arc d).start := by rw [hlast]

/-- Helper toward Proposition 5.16: the image of a finite initial
face-successor walk is the union of its dart-arc images. -/
@[expose] def faceWalkArcImages {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) : Set ℂ :=
  {z | ∃ i, i ≤ n ∧ z ∈ (P.arc ((B.map.faceSucc : B.D → B.D)^[i] d)).image}

/-- Helper toward Proposition 5.16: a finite initial face-successor walk has
image equal to the union of its successive dart-arc images. -/
theorem image_faceWalkPolyline {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) (n : ℕ) :
    (faceWalkPolyline B vert P d n).image = faceWalkArcImages B vert P d n := by
  induction n with
  | zero =>
      ext z
      simp [faceWalkPolyline, faceWalkArcImages]
  | succ n ih =>
      rw [faceWalkPolyline, Polyline.image_boundaryConcat _ _
        (finish_faceWalkPolyline_eq_next_start B vert P d n), ih]
      change
        ({z | ∃ i, i ≤ n ∧
            z ∈ (P.arc ((B.map.faceSucc : B.D → B.D)^[i] d)).image} ∪
          (P.arc ((B.map.faceSucc : B.D → B.D)^[n + 1] d)).image) =
        {z | ∃ i, i ≤ n + 1 ∧
          z ∈ (P.arc ((B.map.faceSucc : B.D → B.D)^[i] d)).image}
      ext z
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (⟨i, hi, hz⟩ | hz)
        · exact ⟨i, by omega, hz⟩
        · exact ⟨n + 1, le_rfl, hz⟩
      · rintro ⟨i, hi, hz⟩
        rcases eq_or_lt_of_le hi with heq | hlt
        · subst i
          exact Or.inr hz
        · exact Or.inl ⟨i, by omega, hz⟩

/-- Helper toward Proposition 5.16: every dart in a face-successor orbit is
an iterate of the starting dart, and every such iterate remains in the orbit. -/
private theorem iterate_mem_faceSucc_sameCycle (B : D39FiniteBall) (d : B.D)
    (i : ℕ) :
    B.map.faceSucc.SameCycle d ((B.map.faceSucc : B.D → B.D)^[i] d) := by
  induction i with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ih.apply_right

/-- Helper toward Proposition 5.16: the concatenated face-successor cycle is
closed and its image is exactly the union of the dart-arc images in the orbit. -/
theorem exists_closed_faceCyclePolyline {V : Type*} (B : D39FiniteBall)
    (vert : B.D → V) (P : PLDrawing B.D V B.map.edgeInv B.map.rot vert)
    (d : B.D) :
    ∃ c : Polyline, c.start = c.finish ∧
      c.image = ⋃ e ∈ {e | B.map.faceSucc.SameCycle d e}, (P.arc e).image := by
  let f : B.D → B.D := B.map.faceSucc
  let m := Function.minimalPeriod f d
  have hm : 0 < m := faceSucc_minimalPeriod_pos B d
  let c := faceWalkPolyline B vert P d (m - 1)
  refine ⟨c, ?_, ?_⟩
  · simpa [c, m] using faceWalkPolyline_closed B vert P d
  · rw [show c.image = faceWalkArcImages B vert P d (m - 1) by
      simpa [c] using image_faceWalkPolyline B vert P d (m - 1)]
    ext z
    simp only [faceWalkArcImages, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hz⟩
      refine ⟨f^[i] d, iterate_mem_faceSucc_sameCycle B d i, hz⟩
    · rintro ⟨e, he, hz⟩
      obtain ⟨i, hi⟩ := he.exists_nat_pow_eq
      have hiter : f^[i] d = e := by
        simpa only [Equiv.Perm.coe_pow] using hi
      let j := i % m
      have hj : j < m := Nat.mod_lt _ hm
      have hmod := Function.iterate_mod_minimalPeriod_eq
        (f := f) (x := d) (n := i)
      refine ⟨j, by omega, ?_⟩
      rw [hmod.trans hiter]
      exact hz

end DirectedDistances.PlanarMap

end

end
