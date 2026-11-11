module

public import DirectedDistances.KMSW.MonotoneLimitFaces
public import DirectedDistances.KMSW.MonotoneCapPersistence
public import DirectedDistances.KMSW.MonotoneStageFamily
public import DirectedDistances.KMSW.KMSWConstructedRealization
public import DirectedDistances.KMSW.LimitExternalFace

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

noncomputable section

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] def familyQ (w : ℕ → Fin 3)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    (n : ℕ) : StageDrawing w n := monotoneLayoutDrawing w n (hfam n).choose

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
@[expose] def familyG (w : ℕ → Fin 3)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    (n : ℕ) : MonotoneStageInvariant w n (familyQ w hfam n) :=
  (hfam n).choose_spec.some

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem familyDrawing_pos (w : ℕ → Fin 3) (hfin : ∀ v,
    {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    ∀ n v, (monotoneFamilyDrawing w hfin hfam).pos v.val = (familyQ w hfam n).pos v := by
  intro n v
  have hagree := monotoneLimitDrawing_agrees w hfin
    (fun n => ⟨familyQ w hfam n, ⟨familyG w hfam n⟩⟩)
    (fun n => familyQ w hfam n)
    (fun n v => (familyG w hfam n).pos_layout v)
    (fun n d => (familyG w hfam n).arc_layout d)
  exact hagree.1 n v

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem familyDrawing_arc (w : ℕ → Fin 3) (hfin : ∀ v,
    {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    ∀ n d, (monotoneFamilyDrawing w hfin hfam).arc (d.1.val, d.2) =
      (familyQ w hfam n).arc d := by
  intro n d
  have hagree := monotoneLimitDrawing_agrees w hfin
    (fun n => ⟨familyQ w hfam n, ⟨familyG w hfam n⟩⟩)
    (fun n => familyQ w hfam n)
    (fun n v => (familyG w hfam n).pos_layout v)
    (fun n d => (familyG w hfam n).arc_layout d)
  exact hagree.2 n d

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem family_cap_persistence (w : ℕ → Fin 3)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    MonotoneLimitCapPersistence w (familyQ w hfam) (familyG w hfam) :=
  monotone_cap_persistence w (familyQ w hfam) (familyG w hfam)

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem family_region_mono (w : ℕ → Fin 3)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    ∀ n, monotoneLimitStageRegion w (familyQ w hfam) (familyG w hfam) n ⊆
      monotoneLimitStageRegion w (familyQ w hfam) (familyG w hfam) (n + 1) := by
  intro n
  change closedGraphRegion (familyG w hfam n).xmin (familyG w hfam n).xmax
      (familyG w hfam n).lower (familyG w hfam n).upper ⊆
    closedGraphRegion (familyG w hfam (n + 1)).xmin
      (familyG w hfam (n + 1)).xmax (familyG w hfam (n + 1)).lower
      (familyG w hfam (n + 1)).upper
  exact monotone_region_mono w (familyQ w hfam) (familyG w hfam) n

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneFamilyDrawing_image (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h))) :
    (monotoneFamilyDrawing w hfin hfam).image =
      ⋃ n, (familyQ w hfam n).image := by
  ext z
  constructor
  · intro hz
    change z ∈ Set.range (monotoneFamilyDrawing w hfin hfam).pos ∪
      {z | ∃ d, z ∈ ((monotoneFamilyDrawing w hfin hfam).arc d).image} at hz
    rcases hz with ⟨v, hv⟩ | ⟨d, hd⟩
    · obtain ⟨n, hn⟩ := kmsw_vertex_allocated_of_finite_incidence w hfin v
      refine mem_iUnion.mpr ⟨n, ?_⟩
      change z ∈ Set.range (familyQ w hfam n).pos ∪ _
      apply Or.inl
      refine ⟨⟨v, hn⟩, ?_⟩
      calc
        (familyQ w hfam n).pos ⟨v, hn⟩ =
            (monotoneFamilyDrawing w hfin hfam).pos v :=
          (familyDrawing_pos w hfin hfam n ⟨v, hn⟩).symm
        _ = z := hv
    · let n := d.1
      have he := kmsw_edge_allocated_by_self w d.1
      let d' : StageDart (kmswStage w n).nextEdge := (⟨d.1, he⟩, d.2)
      refine mem_iUnion.mpr ⟨n, ?_⟩
      change z ∈ Set.range (familyQ w hfam n).pos ∪
        {z | ∃ d, z ∈ ((familyQ w hfam n).arc d).image}
      apply Or.inr
      refine ⟨d', ?_⟩
      rw [← familyDrawing_arc w hfin hfam n d']
      exact hd
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    change z ∈ Set.range (familyQ w hfam n).pos ∪
      {z | ∃ d, z ∈ ((familyQ w hfam n).arc d).image} at hn
    change z ∈ Set.range (monotoneFamilyDrawing w hfin hfam).pos ∪
      {z | ∃ d, z ∈ ((monotoneFamilyDrawing w hfin hfam).arc d).image}
    rcases hn with ⟨v, hv⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨v, (familyDrawing_pos w hfin hfam n v).trans hv⟩
    · refine Or.inr ⟨(d.1.val, d.2), ?_⟩
      rw [familyDrawing_arc w hfin hfam n d]
      exact hd

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem monotoneFamily_hface (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (_htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (_hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (_hL0 : ∀ j, 0 ≤ L w j)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    (hEopen : IsOpen (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)))
    (hEconn : IsPathConnected (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)))
    (hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam), R < ‖z‖)
    (hEfront : frontier (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)) ⊆
        ⋃ n, (familyQ w hfam n).image)
    (hEdisj : ∀ n, Disjoint (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)) (familyQ w hfam n).image)
    (hcover : ∀ z, (∀ n, z ∉ (familyQ w hfam n).image) →
      z ∉ monotoneLimitExteriorRegion w (familyQ w hfam) (familyG w hfam) →
      ∃ n i, z ∈ ((familyG w hfam n).cap i).region) :
    let P := monotoneFamilyDrawing w hfin hfam
    ∃ U : P.Face, P.IsUnbounded U ∧
      (∀ F : P.Face, P.IsUnbounded F → F = U) ∧
      ∀ d, P.dartBorders d U ↔ limitExternalDart w d := by
  let Q : ∀ n, StageDrawing w n := familyQ w hfam
  let G : ∀ n, MonotoneStageInvariant w n (Q n) := familyG w hfam
  let P := monotoneFamilyDrawing w hfin hfam
  have hpos : ∀ n v, P.pos v.val = (Q n).pos v :=
    familyDrawing_pos w hfin hfam
  have harc : ∀ n d, P.arc (d.1.val, d.2) = (Q n).arc d :=
    familyDrawing_arc w hfin hfam
  have hpersist : MonotoneLimitCapPersistence w Q G :=
    family_cap_persistence w hfam
  have hnest : ∀ n, monotoneLimitStageRegion w Q G n ⊆
      monotoneLimitStageRegion w Q G (n + 1) := family_region_mono w hfam
  have himage : P.image = ⋃ n, (Q n).image := by
    exact monotoneFamilyDrawing_image w hfin hfam
  have hfront : frontier (monotoneLimitExteriorRegion w Q G) ⊆ P.image := by
    rw [himage]
    exact hEfront
  have hdisj : Disjoint (monotoneLimitExteriorRegion w Q G) P.image := by
    rw [himage]
    apply disjoint_left.mpr
    intro z hzE hzImage
    obtain ⟨n, hzn⟩ := mem_iUnion.mp hzImage
    exact (disjoint_left.mp (hEdisj n)) hzE hzn
  have hcoverP : ∀ z ∉ P.image,
      z ∉ monotoneLimitExteriorRegion w Q G →
        ∃ n i, z ∈ ((G n).cap i).region := by
    intro z hzImage hzE
    apply hcover z ?_ hzE
    intro n hzn
    apply hzImage
    rw [himage]
    exact mem_iUnion.mpr ⟨n, hzn⟩
  obtain ⟨U, _, hUnb, huniq, _, hdart⟩ := monotoneLimit_dartBorders_iff
    w hfin Q G P hpos harc hpersist hnest hEopen hEconn hEunb hfront hdisj hcoverP
  exact ⟨U, hUnb, huniq, hdart⟩

/-- Helper toward the plane-realization obligation of adjudication n308; not a paper result. -/
theorem kmswConstructedPlaneRealization_of_family_exterior (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j)
    (hfam : ∀ n, ∃ h : LayoutGood w n,
      Nonempty (MonotoneStageInvariant w n (monotoneLayoutDrawing w n h)))
    (hEopen : IsOpen (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)))
    (hEconn : IsPathConnected (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)))
    (hEunb : ∀ R : ℝ, ∃ z ∈ monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam), R < ‖z‖)
    (hEfront : frontier (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)) ⊆
        ⋃ n, (familyQ w hfam n).image)
    (hEdisj : ∀ n, Disjoint (monotoneLimitExteriorRegion w
      (familyQ w hfam) (familyG w hfam)) (familyQ w hfam n).image)
    (hcover : ∀ z, (∀ n, z ∉ (familyQ w hfam n).image) →
      z ∉ monotoneLimitExteriorRegion w (familyQ w hfam) (familyG w hfam) →
      ∃ n i, z ∈ ((familyG w hfam n).cap i).region) :
    KMSWConstructedPlaneRealizationStatement w hfin htrans hR hL0 := by
  exact kmswConstructedPlaneRealization_of_family w hfin htrans hR hL0 hfam
    (monotoneFamily_hface w hfin htrans hR hL0 hfam hEopen hEconn hEunb hEfront
      hEdisj hcover)

end
end DirectedDistances.KMSW
