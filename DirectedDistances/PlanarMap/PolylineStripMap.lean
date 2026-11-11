module

public import DirectedDistances.PlanarMap.MonotonePolyline
public import Mathlib.Data.Finset.Sort

/-! # Polyline subdivision and segmentwise affine transfer

Generic geometric helpers. No KMSW construction is used. -/

public section

namespace DirectedDistances.PlanarMap
namespace Polyline

noncomputable section

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Pointwise application to the vertex list. -/
@[expose] def mapPoints (F : ℂ → ℂ) (p : Polyline) : Polyline :=
  ⟨p.points.map F, by simpa using p.nonempty⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[simp] theorem length_mapPoints (F : ℂ → ℂ) (p : Polyline) :
    (mapPoints F p).points.length = p.points.length := by
  simp [mapPoints]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[simp] theorem start_mapPoints (F : ℂ → ℂ) (p : Polyline) :
    (mapPoints F p).start = F p.start := by
  simp [mapPoints, start]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[simp] theorem finish_mapPoints (F : ℂ → ℂ) (p : Polyline) :
    (mapPoints F p).finish = F p.finish := by
  simp [mapPoints, finish]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. This also holds for out-of-range indices. -/
@[simp] theorem point_mapPoints (F : ℂ → ℂ) (p : Polyline) (i : ℕ) :
    (mapPoints F p).point i = F (p.point i) := by
  simp only [point, start_mapPoints]
  change ((p.points.map F)[i]?).getD (F p.start) = F (p.points[i]?.getD p.start)
  rw [List.getElem?_map]
  cases p.points[i]? <;> rfl

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. An affine extension may depend on the segment. -/
@[expose] def AffineOnSegments (F : ℂ → ℂ) (p : Polyline) : Prop :=
  ∀ i, i + 1 < p.points.length →
    ∃ A : ℂ →ᵃ[ℝ] ℂ, Set.EqOn F A (p.segmentAt i)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem segmentAt_mapPoints (F : ℂ → ℂ) (p : Polyline)
    (hF : AffineOnSegments F p) {i : ℕ} (hi : i + 1 < p.points.length) :
    (mapPoints F p).segmentAt i = F '' p.segmentAt i := by
  obtain ⟨A, hA⟩ := hF i hi
  have ha : F (p.point i) = A (p.point i) := hA (left_mem_segment ℝ _ _)
  have hb : F (p.point (i + 1)) = A (p.point (i + 1)) :=
    hA (right_mem_segment ℝ _ _)
  calc
    (mapPoints F p).segmentAt i =
        segment ℝ (A (p.point i)) (A (p.point (i + 1))) := by
      simp only [segmentAt, point_mapPoints, ha, hb]
    _ = A '' p.segmentAt i := (image_segment ℝ A _ _).symm
    _ = F '' p.segmentAt i := Set.image_congr hA.symm

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem image_mapPoints (F : ℂ → ℂ) (p : Polyline)
    (hF : AffineOnSegments F p) : (mapPoints F p).image = F '' p.image := by
  ext z
  simp only [image, start_mapPoints, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, length_mapPoints]
  constructor
  · rintro (rfl | ⟨i, hi, hz⟩)
    · exact ⟨p.start, Or.inl rfl, rfl⟩
    · rw [segmentAt_mapPoints F p hF hi] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, Or.inr ⟨i, hi, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | ⟨i, hi, hx⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, (segmentAt_mapPoints F p hF hi).symm ▸
        Set.mem_image_of_mem F hx⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem point_mem_image (p : Polyline) {i : ℕ} (hi : i < p.points.length) :
    p.point i ∈ p.image := by
  by_cases h : i = 0
  · subst i
    exact Or.inl p.point_zero_eq_start
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact Or.inr ⟨j, hi, right_mem_segment ℝ _ _⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem segmentAt_subset_image (p : Polyline) {i : ℕ}
    (hi : i + 1 < p.points.length) : p.segmentAt i ⊆ p.image := by
  intro z hz
  exact Or.inr ⟨i, hi, hz⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Preserves the exact segment-intersection simplicity predicate. -/
theorem isSimple_mapPoints (F : ℂ → ℂ) (p : Polyline)
    (hF : AffineOnSegments F p) (hinj : Set.InjOn F p.image) (hp : p.IsSimple) :
    (mapPoints F p).IsSimple := by
  rcases hp with ⟨hne, hadj, hsep⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi heq
    rw [length_mapPoints] at hi
    simp only [point_mapPoints] at heq
    exact hne i hi (hinj (p.point_mem_image (by omega)) (p.point_mem_image hi) heq)
  · intro i hi
    rw [length_mapPoints] at hi
    rw [segmentAt_mapPoints F p hF (by omega),
      segmentAt_mapPoints F p hF (by omega), point_mapPoints]
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
      have heq : y = x := hinj (p.segmentAt_subset_image (by omega) hy)
        (p.segmentAt_subset_image (by omega) hx) hxy
      subst y
      have hx' : x = p.point (i + 1) := by
        have : x ∈ p.segmentAt i ∩ p.segmentAt (i + 1) := ⟨hx, hy⟩
        rw [hadj i hi] at this
        exact this
      exact congrArg F hx'
    · intro hz
      have hz' : z = F (p.point (i + 1)) := hz
      subst z
      exact ⟨⟨_, right_mem_segment ℝ _ _, rfl⟩,
        ⟨_, left_mem_segment ℝ _ _, rfl⟩⟩
  · intro i j hi hj hij
    rw [length_mapPoints] at hi hj
    rw [segmentAt_mapPoints F p hF hi, segmentAt_mapPoints F p hF hj]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq : y = x := hinj (p.segmentAt_subset_image hj hy)
      (p.segmentAt_subset_image hi hx) hxy
    subst y
    exact Set.disjoint_left.mp (hsep i j hi hj hij) hx hy

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Interiors are images when endpoint identifications are excluded. -/
theorem interior_mapPoints (F : ℂ → ℂ) (p : Polyline)
    (hF : AffineOnSegments F p) (hinj : Set.InjOn F p.image) :
    (mapPoints F p).interior = F '' p.interior := by
  have hs : p.start ∈ p.image := Or.inl rfl
  have ht : p.finish ∈ p.image := by
    rw [← p.point_last_eq_finish]
    exact p.point_mem_image (by have := List.length_pos_iff.mpr p.nonempty; omega)
  rw [interior, image_mapPoints F p hF, start_mapPoints, finish_mapPoints]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro he
    apply hn
    rcases he with he | he
    · exact Or.inl (congrArg F he)
    · exact Or.inr (congrArg F he)
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro he
    apply hn
    rcases he with he | he
    · exact Or.inl (hinj hx hs he)
    · exact Or.inr (hinj hx ht he)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Preserves the interior-disjointness condition used by PLDrawing. -/
theorem interior_disjoint_mapPoints (F : ℂ → ℂ) (p q : Polyline)
    (hp : AffineOnSegments F p) (hq : AffineOnSegments F q)
    (hinj : Set.InjOn F (p.image ∪ q.image)) (h : Disjoint p.interior q.interior) :
    Disjoint (mapPoints F p).interior (mapPoints F q).interior := by
  rw [interior_mapPoints F p hp (hinj.mono Set.subset_union_left),
    interior_mapPoints F q hq (hinj.mono Set.subset_union_right)]
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have heq : y = x := hinj (Or.inr hy.1) (Or.inl hx.1) hxy
  subst y
  exact Set.disjoint_left.mp h hx hy

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. A nonempty list constructor used for recursive geometry. -/
@[expose] def ofHead (a : ℂ) (l : List ℂ) : Polyline := ⟨a :: l, by simp⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem point_eq_getElem (p : Polyline) {i : ℕ} (hi : i < p.points.length) :
    p.point i = p.points[i] := by
  exact List.getD_eq_getElem (l := p.points) (d := p.start) hi

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem point_ofHead_succ (a b : ℂ) (l : List ℂ) {i : ℕ}
    (hi : i < (b :: l).length) :
    (ofHead a (b :: l)).point (i + 1) = (ofHead b l).point i := by
  rw [point_eq_getElem _ (by simpa [ofHead] using Nat.succ_lt_succ hi),
    point_eq_getElem _ hi]
  rfl

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem image_ofHead_cons (a b : ℂ) (l : List ℂ) :
    (ofHead a (b :: l)).image = segment ℝ a b ∪ (ofHead b l).image := by
  ext z
  constructor
  · rintro (hz | ⟨i, hi, hz⟩)
    · have hz' : z = a := hz
      exact Or.inl (hz' ▸ left_mem_segment ℝ a b)
    · cases i with
      | zero => exact Or.inl hz
      | succ i =>
        apply Or.inr
        apply Or.inr
        have hil : i + 1 < (b :: l).length := by
          simpa [ofHead] using Nat.lt_of_succ_lt_succ hi
        refine ⟨i, hil, ?_⟩
        simpa only [segmentAt, point_ofHead_succ a b l (i := i) (by omega),
          point_ofHead_succ a b l hil] using hz
  · rintro (hz | hz | ⟨i, hi, hz⟩)
    · exact Or.inr ⟨0, by simp [ofHead], hz⟩
    · have hz' : z = b := hz
      exact Or.inr ⟨0, by simp [ofHead], hz' ▸ right_mem_segment ℝ a b⟩
    · apply Or.inr
      have hil : i + 1 < (b :: l).length := hi
      refine ⟨i + 1, by simpa [ofHead] using Nat.succ_lt_succ hi, ?_⟩
      simpa only [segmentAt, point_ofHead_succ a b l (i := i) (by omega),
        point_ofHead_succ a b l hil] using hz

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Recursive union of segments, including the sole point in a singleton. -/
@[expose] def traceFrom (a : ℂ) : List ℂ → Set ℂ
  | [] => {a}
  | b :: l => segment ℝ a b ∪ traceFrom b l

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem traceFrom_eq_image (a : ℂ) (l : List ℂ) :
    traceFrom a l = (ofHead a l).image := by
  induction l generalizing a with
  | nil => simp [traceFrom, image, ofHead, start]
  | cons b l ih => rw [traceFrom, image_ofHead_cons, ih]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. The segment parameter of a vertical cut. Vertical segments give zero. -/
@[expose] def cutParameter (c : ℝ) (a b : ℂ) : ℝ :=
  (c - a.re) / (b.re - a.re)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[expose] def cutPoint (c : ℝ) (a b : ℂ) : ℂ :=
  AffineMap.lineMap a b (cutParameter c a b)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Inserts a cut only in the strict parameter interior. -/
@[expose] def cutTail (c : ℝ) (a : ℂ) : List ℂ → List ℂ
  | [] => []
  | b :: l =>
    if cutParameter c a b ∈ Set.Ioo 0 1 then
      cutPoint c a b :: b :: cutTail c b l
    else b :: cutTail c b l

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Splitting one segment at an interior parameter preserves its trace. -/
private theorem segment_split (a b : ℂ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    segment ℝ a (AffineMap.lineMap a b t) ∪
      segment ℝ (AffineMap.lineMap a b t) b = segment ℝ a b := by
  let A : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
  have h0 : A 0 = a := by simp [A]
  have h1 : A 1 = b := by simp [A]
  calc
    segment ℝ a (A t) ∪ segment ℝ (A t) b =
        A '' segment ℝ 0 t ∪ A '' segment ℝ t 1 := by
      rw [image_segment ℝ A, image_segment ℝ A, h0, h1]
    _ = A '' (Set.Icc 0 t ∪ Set.Icc t 1) := by
      rw [segment_eq_Icc ht.1, segment_eq_Icc ht.2, Set.image_union]
    _ = A '' Set.Icc 0 1 := by rw [Set.Icc_union_Icc_eq_Icc ht.1 ht.2]
    _ = segment ℝ a b := by
      rw [← segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1), image_segment ℝ A, h0, h1]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem traceFrom_cutTail (c : ℝ) (a : ℂ) (l : List ℂ) :
    traceFrom a (cutTail c a l) = traceFrom a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [cutTail]
    split_ifs with ht
    · simp only [traceFrom, ih, ← Set.union_assoc]
      rw [cutPoint, segment_split a b ⟨ht.1.le, ht.2.le⟩]
    · simp only [traceFrom, ih]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[expose] def subdivideOne (p : Polyline) (c : ℝ) : Polyline :=
  ofHead p.start (cutTail c p.start p.points.tail)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem ofHead_start_tail (p : Polyline) : ofHead p.start p.points.tail = p := by
  cases p with
  | mk points nonempty =>
    cases points with
    | nil => exact (nonempty rfl).elim
    | cons a l => rfl

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem image_subdivideOne (p : Polyline) (c : ℝ) :
    (subdivideOne p c).image = p.image := by
  rw [subdivideOne, ← traceFrom_eq_image, traceFrom_cutTail,
    traceFrom_eq_image, ofHead_start_tail]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Repeated cuts retain segment-parameter order, independently of cut order. -/
@[expose] def subdivideAt (p : Polyline) (xs : Finset ℝ) : Polyline :=
  xs.toList.foldl subdivideOne p

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem image_subdivideAt (p : Polyline) (xs : Finset ℝ) :
    (subdivideAt p xs).image = p.image := by
  unfold subdivideAt
  generalize xs.toList = l
  induction l generalizing p with
  | nil => rfl
  | cons c l ih => exact (ih (subdivideOne p c)).trans (image_subdivideOne p c)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem last_cutTail (c : ℝ) (a : ℂ) (l : List ℂ) :
    (a :: cutTail c a l).getLast? = (a :: l).getLast? := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [cutTail]
    split_ifs <;> simp only [List.getLast?_cons_cons, ih]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[simp] theorem start_subdivideAt (p : Polyline) (xs : Finset ℝ) :
    (subdivideAt p xs).start = p.start := by
  unfold subdivideAt
  generalize xs.toList = l
  induction l generalizing p with
  | nil => rfl
  | cons c l ih => exact (ih (subdivideOne p c)).trans rfl

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem finish_subdivideOne (p : Polyline) (c : ℝ) :
    (subdivideOne p c).finish = p.finish := by
  have h := last_cutTail c p.start p.points.tail
  apply Option.some.inj
  change some ((subdivideOne p c).points.getLast _) = some (p.points.getLast _)
  rw [← List.getLast?_eq_some_getLast (subdivideOne p c).nonempty,
    ← List.getLast?_eq_some_getLast p.nonempty]
  change (p.start :: cutTail c p.start p.points.tail).getLast? = p.points.getLast?
  rw [h]
  have hp := congrArg (fun q : Polyline => q.points) (ofHead_start_tail p)
  exact congrArg List.getLast? hp

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
@[simp] theorem finish_subdivideAt (p : Polyline) (xs : Finset ℝ) :
    (subdivideAt p xs).finish = p.finish := by
  unfold subdivideAt
  generalize xs.toList = l
  induction l generalizing p with
  | nil => rfl
  | cons c l ih => exact (ih (subdivideOne p c)).trans (finish_subdivideOne p c)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem xPairwise_cons_cons (a b : ℂ) (l : List ℂ) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) (a :: b :: l) ↔
      a.re < b.re ∧ List.Pairwise (fun z w : ℂ => z.re < w.re) (b :: l) := by
  let : IsTrans ℂ (fun z w : ℂ => z.re < w.re) := ⟨fun _ _ _ => lt_trans⟩
  exact List.pairwise_cons_cons_iff_of_trans

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem cutPoint_re_formula (c : ℝ) (a b : ℂ) :
    (cutPoint c a b).re =
      (1 - cutParameter c a b) * a.re + cutParameter c a b * b.re := by
  simp [cutPoint, AffineMap.lineMap_apply_module, Complex.real_smul]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem xMonotone_cutTail (c : ℝ) (a : ℂ) (l : List ℂ)
    (h : List.Pairwise (fun z w : ℂ => z.re < w.re) (a :: l)) :
    List.Pairwise (fun z w : ℂ => z.re < w.re) (a :: cutTail c a l) := by
  induction l generalizing a with
  | nil => exact h
  | cons b l ih =>
    obtain ⟨hab, htail⟩ := (xPairwise_cons_cons a b l).mp h
    have hrec := ih b htail
    simp only [cutTail]
    split_ifs with ht
    · have hre := cutPoint_re_formula c a b
      have haq : a.re < (cutPoint c a b).re := by nlinarith [ht.1, ht.2]
      have hqb : (cutPoint c a b).re < b.re := by nlinarith [ht.1, ht.2]
      exact (xPairwise_cons_cons _ _ _).mpr ⟨haq,
        (xPairwise_cons_cons _ _ _).mpr ⟨hqb, hrec⟩⟩
    · exact (xPairwise_cons_cons _ _ _).mpr ⟨hab, hrec⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem xMonotone_subdivideOne (p : Polyline) (c : ℝ) (hp : p.XMonotone) :
    (subdivideOne p c).XMonotone := by
  have h : (ofHead p.start p.points.tail).XMonotone := (ofHead_start_tail p).symm ▸ hp
  exact xMonotone_cutTail c p.start p.points.tail h

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
theorem xMonotone_subdivideAt (p : Polyline) (xs : Finset ℝ) (hp : p.XMonotone) :
    (subdivideAt p xs).XMonotone := by
  unfold subdivideAt
  generalize xs.toList = l
  induction l generalizing p with
  | nil => exact hp
  | cons c l ih => exact ih (subdivideOne p c) (xMonotone_subdivideOne p c hp)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Endpoints lie on one closed side of a vertical line. -/
@[expose] def DoesNotCross (c : ℝ) (a b : ℂ) : Prop :=
  (a.re ≤ c ∧ b.re ≤ c) ∨ (c ≤ a.re ∧ c ≤ b.re)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem doesNotCross_iff (c : ℝ) (a b : ℂ) :
    DoesNotCross c a b ↔ ¬(min a.re b.re < c ∧ c < max a.re b.re) := by
  simp only [DoesNotCross, not_and_or, not_lt, le_min_iff, max_le_iff, or_comm]

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem cutParameter_mem_iff (c : ℝ) (a b : ℂ) :
    cutParameter c a b ∈ Set.Ioo 0 1 ↔ min a.re b.re < c ∧ c < max a.re b.re := by
  rcases lt_trichotomy a.re b.re with hab | hab | hab
  · have hd : 0 < b.re - a.re := sub_pos.mpr hab
    rw [min_eq_left hab.le, max_eq_right hab.le]
    simp only [cutParameter, Set.mem_Ioo, div_pos_iff_of_pos_right hd, div_lt_one hd]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · simp only [cutParameter, hab, sub_self, div_zero, Set.mem_Ioo,
      lt_self_iff_false, false_and, min_self, max_self, false_iff]
    intro h
    exact (lt_asymm h.1 h.2)
  · have hd : b.re - a.re < 0 := sub_neg.mpr hab
    have hpos : 0 < (c - a.re) / (b.re - a.re) ↔ c < a.re := by
      rw [div_pos_iff]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith
      · intro h
        exact Or.inr ⟨by linarith, hd⟩
    rw [min_eq_right hab.le, max_eq_left hab.le]
    simp only [cutParameter, Set.mem_Ioo, hpos, div_lt_one_of_neg hd]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem cutPoint_re (c : ℝ) (a b : ℂ)
    (ht : cutParameter c a b ∈ Set.Ioo 0 1) : (cutPoint c a b).re = c := by
  have hne : b.re - a.re ≠ 0 := by
    intro h
    have hz : cutParameter c a b = 0 := by simp [cutParameter, h]
    rw [hz] at ht
    exact lt_irrefl 0 ht.1
  calc
    (cutPoint c a b).re = a.re + cutParameter c a b * (b.re - a.re) := by
      rw [cutPoint_re_formula]
      ring
    _ = c := by
      unfold cutParameter
      rw [div_mul_cancel₀ _ hne]
      ring

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem doesNotCross_cutPoint (c d : ℝ) (a b : ℂ)
    (ht : cutParameter c a b ∈ Set.Icc 0 1) (hd : DoesNotCross d a b) :
    DoesNotCross d a (cutPoint c a b) ∧ DoesNotCross d (cutPoint c a b) b := by
  have hre := cutPoint_re_formula c a b
  rcases hd with hd | hd
  · have hq : (cutPoint c a b).re ≤ d := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hd.1),
        mul_nonneg ht.1 (sub_nonneg.mpr hd.2)]
    exact ⟨Or.inl ⟨hd.1, hq⟩, Or.inl ⟨hq, hd.2⟩⟩
  · have hq : d ≤ (cutPoint c a b).re := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hd.1),
        mul_nonneg ht.1 (sub_nonneg.mpr hd.2)]
    exact ⟨Or.inr ⟨hd.1, hq⟩, Or.inr ⟨hq, hd.2⟩⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem chain_cutTail (c : ℝ) (xs : Finset ℝ) (a : ℂ) (l : List ℂ)
    (h : List.IsChain (fun a b => ∀ d ∈ xs, DoesNotCross d a b) (a :: l)) :
    List.IsChain (fun a b => ∀ d ∈ insert c xs, DoesNotCross d a b)
      (a :: cutTail c a l) := by
  induction l generalizing a with
  | nil => simp [cutTail]
  | cons b l ih =>
    obtain ⟨hab, htail⟩ := List.isChain_cons_cons.mp h
    have hrec := ih b htail
    simp only [cutTail]
    split_ifs with ht
    · rw [List.isChain_cons_cons, List.isChain_cons_cons]
      have hq := cutPoint_re c a b ht
      refine ⟨?_, ?_, hrec⟩
      · intro d hd
        rcases Finset.mem_insert.mp hd with hdc | hd
        · subst d
          unfold DoesNotCross
          rw [hq]
          rcases le_total a.re c with ha | ha
          · exact Or.inl ⟨ha, le_rfl⟩
          · exact Or.inr ⟨ha, le_rfl⟩
        · exact (doesNotCross_cutPoint c d a b ⟨ht.1.le, ht.2.le⟩ (hab d hd)).1
      · intro d hd
        rcases Finset.mem_insert.mp hd with hdc | hd
        · subst d
          unfold DoesNotCross
          rw [hq]
          rcases le_total b.re c with hb | hb
          · exact Or.inl ⟨le_rfl, hb⟩
          · exact Or.inr ⟨le_rfl, hb⟩
        · exact (doesNotCross_cutPoint c d a b ⟨ht.1.le, ht.2.le⟩ (hab d hd)).2
    · rw [List.isChain_cons_cons]
      refine ⟨?_, hrec⟩
      intro d hd
      rcases Finset.mem_insert.mp hd with hdc | hd
      · subst d
        exact (doesNotCross_iff c a b).mpr (fun hc =>
          ht ((cutParameter_mem_iff c a b).mpr hc))
      · exact hab d hd

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem chain_subdivideOne (p : Polyline) (c : ℝ) (xs : Finset ℝ)
    (hp : List.IsChain (fun a b => ∀ d ∈ xs, DoesNotCross d a b) p.points) :
    List.IsChain (fun a b => ∀ d ∈ insert c xs, DoesNotCross d a b)
      (subdivideOne p c).points := by
  have hpoints : p.start :: p.points.tail = p.points :=
    congrArg (fun q : Polyline => q.points) (ofHead_start_tail p)
  exact chain_cutTail c xs p.start p.points.tail (hpoints.symm ▸ hp)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem chain_foldl (l : List ℝ) (p : Polyline) (xs : Finset ℝ)
    (hp : List.IsChain (fun a b => ∀ d ∈ xs, DoesNotCross d a b) p.points) :
    List.IsChain (fun a b => ∀ d ∈ xs ∪ l.toFinset, DoesNotCross d a b)
      (l.foldl subdivideOne p).points := by
  induction l generalizing p xs with
  | nil => simpa using hp
  | cons c l ih =>
    have h := ih (subdivideOne p c) (insert c xs) (chain_subdivideOne p c xs hp)
    simpa only [List.foldl_cons, List.toFinset_cons, Finset.insert_union,
      Finset.union_insert] using h

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Every supplied vertical line misses each refined segment's x-interior. -/
theorem doesNotCross_subdivideAt (p : Polyline) (xs : Finset ℝ) {i : ℕ}
    (hi : i + 1 < (subdivideAt p xs).points.length) {c : ℝ} (hc : c ∈ xs) :
    DoesNotCross c ((subdivideAt p xs).point i) ((subdivideAt p xs).point (i + 1)) := by
  have hempty : List.IsChain (fun a b => ∀ d ∈ (∅ : Finset ℝ), DoesNotCross d a b)
      p.points := by
    apply List.isChain_iff_getElem.mpr
    intro i hi d hd
    exact (Finset.notMem_empty d hd).elim
  have hchain := chain_foldl xs.toList p ∅ hempty
  have hchain' : List.IsChain (fun a b => ∀ d ∈ xs, DoesNotCross d a b)
      (subdivideAt p xs).points := by simpa [subdivideAt] using hchain
  have h := List.isChain_iff_getElem.mp hchain' i hi c hc
  rw [point_eq_getElem (subdivideAt p xs) (i := i) (by omega),
    point_eq_getElem (subdivideAt p xs) (i := i + 1) hi]
  exact h

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem segment_re_minmax (a b z : ℂ) (hz : z ∈ segment ℝ a b) :
    min a.re b.re ≤ z.re ∧ z.re ≤ max a.re b.re := by
  rcases le_total a.re b.re with hab | hab
  · simpa only [min_eq_left hab, max_eq_right hab] using segment_re_bounds hab hz
  · have hz' : z ∈ segment ℝ b a := (segment_symm ℝ a b) ▸ hz
    simpa only [min_eq_right hab, max_eq_left hab] using segment_re_bounds hab hz'

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem point_re_end_bounds (p : Polyline) (hp : p.XMonotone) {i : ℕ}
    (hi : i < p.points.length) : p.start.re ≤ (p.point i).re ∧
      (p.point i).re ≤ p.finish.re := by
  constructor
  · rw [← p.point_zero_eq_start]
    exact point_re_le_of_le hp (Nat.zero_le i) hi
  · rw [← p.point_last_eq_finish]
    exact point_re_le_of_le hp (by omega) (by omega)

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. -/
private theorem image_re_end_bounds (p : Polyline) (hp : p.XMonotone) {z : ℂ}
    (hz : z ∈ p.image) : p.start.re ≤ z.re ∧ z.re ≤ p.finish.re := by
  rcases hz with hz | ⟨i, hi, hz⟩
  · have hz' : z = p.start := hz
    subst z
    have hlen : 0 < p.points.length := List.length_pos_iff.mpr p.nonempty
    simpa only [point_zero_eq_start] using point_re_end_bounds p hp hlen
  · have hz' := segmentAt_re_bounds hp hi hz
    have hleft := (point_re_end_bounds p hp (by omega : i < p.points.length)).1
    have hright := (point_re_end_bounds p hp hi).2
    exact ⟨hleft.trans hz'.1, hz'.2.trans hright⟩

/-- Helper toward Theorem 1.4 (Q-M0-repr drawing: polyline subdivision and strip-affine transfer);
not a paper result. Affine strips cover the real axis; all interior breakpoints are supplied. -/
theorem affineOnSegments_subdivideAt (F : ℂ → ℂ) (p : Polyline) (xs : Finset ℝ)
    (b : ℤ → ℝ) (hp : p.XMonotone)
    (hcover : ∀ x : ℝ, ∃ k : ℤ, b k ≤ x ∧ x < b (k + 1))
    (haff : ∀ k : ℤ, ∃ A : ℂ →ᵃ[ℝ] ℂ,
      Set.EqOn F A {z | b k ≤ z.re ∧ z.re ≤ b (k + 1)})
    (hcuts : ∀ k : ℤ, p.start.re < b k → b k < p.finish.re → b k ∈ xs) :
    AffineOnSegments F (subdivideAt p xs) := by
  intro i hi
  let q := subdivideAt p xs
  let a := q.point i
  let d := q.point (i + 1)
  have hiq : i + 1 < q.points.length := hi
  have ha : a ∈ p.image := image_subdivideAt p xs ▸ q.point_mem_image (by omega)
  have hd : d ∈ p.image := image_subdivideAt p xs ▸ q.point_mem_image hiq
  have hab := image_re_end_bounds p hp ha
  have hdb := image_re_end_bounds p hp hd
  have hlo : p.start.re ≤ min a.re d.re := le_min hab.1 hdb.1
  have hhi : max a.re d.re ≤ p.finish.re := max_le hab.2 hdb.2
  obtain ⟨k, hk0, hk1⟩ := hcover (min a.re d.re)
  have htop : max a.re d.re ≤ b (k + 1) := by
    by_contra h
    have hb : b (k + 1) < max a.re d.re := lt_of_not_ge h
    have hmem := hcuts (k + 1) (lt_of_le_of_lt hlo hk1) (lt_of_lt_of_le hb hhi)
    have hn := doesNotCross_subdivideAt p xs hi hmem
    exact (doesNotCross_iff _ a d).mp hn ⟨hk1, hb⟩
  obtain ⟨A, hA⟩ := haff k
  refine ⟨A, ?_⟩
  intro z hz
  have hz' := segment_re_minmax a d z hz
  exact hA ⟨hk0.trans hz'.1, hz'.2.trans htop⟩

end
end Polyline
end DirectedDistances.PlanarMap
