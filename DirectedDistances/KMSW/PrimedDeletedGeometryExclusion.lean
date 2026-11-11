module

public import DirectedDistances.KMSW.PrimedDeletedGeometryEscape
public import DirectedDistances.KMSW.HatRealizedFaces
import DirectedDistances.KMSW.MhatPrimeVertexForward

/-! Helpers toward Lemma 5.13 (`lem-quad-kmsw`), not the paper result.

The deleted ambient geometry is exactly the reachable geometric image with the
retained beta-zero trace removed. This identifies the side on which escape must
be constructed; it does not establish escape or bounded-face exclusion.
The beta trace below uses both darts as geometric parametrizations, without
assigning a directed orientation to any missing primed edge. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology

/-- Helper toward Lemma 5.13: a retained ambient vertex position is incident to -/
private theorem exclusion_pos_mem_restriction {w : ℕ → Fin 3}
    (hfin : primedLimitFiniteIncidence w) (S : Set (ℕ × Bool))
    (hS : ∀ d, d ∈ S ↔ (d.1, !d.2) ∈ S) (v : ℕ)
    (hv : (monotoneFamilyDrawing w hfin (monotone_family_all w)).pos v ∈
      (restrictDrawing (monotoneFamilyDrawing w hfin (monotone_family_all w)) S hS).image) :
    ∃ d ∈ S, kmswLimitDartVertex w d = v := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  rw [restrictDrawing_image_eq] at hv
  rcases hv with ⟨a, ha⟩ | ⟨d, hd⟩
  · have hav : a.val = v := P.pos_injective ha
    obtain ⟨d, hd, hda⟩ := a.property
    exact ⟨d, hd, hda.trans hav⟩
  · have hend : P.pos v = (P.arc d.val).start ∨
        P.pos v = (P.arc d.val).finish := by
      by_contra hn
      exact P.interior_avoids_vertices d.val v
        ⟨hd, by simpa only [mem_insert_iff, mem_singleton_iff] using hn⟩
    rcases hend with hs | ht
    · rw [P.arc_start] at hs
      exact ⟨d.val, d.property, (P.pos_injective hs).symm⟩
    · rw [P.arc_finish] at ht
      exact ⟨(d.val.1, !d.val.2), (hS d.val).mp d.property,
        (P.pos_injective ht).symm⟩

/-- Helper toward Lemma 5.13: every deleted ambient point belongs to the
reachable geometric image. This includes deleted vertices and never requires
the endpoints of a deleted arc to be deleted. -/
theorem primedDeletedGeometry_subset_hatImage (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).image \
        (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image ⊆
      (hatRealizedDrawing w hfin).image := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  rintro z ⟨hzP, hzQ⟩
  rw [restrictDrawing_image_eq]
  rcases hzP with ⟨v, rfl⟩ | ⟨d, hd⟩
  · obtain ⟨e, _, hev⟩ := uibot_allocated_vertex_outgoing w hb.R_unbounded_below v
      (kmsw_vertex_allocated_of_finite_incidence w hfin v)
    have hs : (P.arc (e, false)).start = P.pos v := by
      simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, hev]
        using P.arc_start (e, false)
    have he : ¬ primeGeomEdge w hfin hb e := by
      intro he
      apply hzQ
      change P.pos v ∈ (restrictDrawing P (primeDartSet w hfin hb)
        (primeDartSet_flip_closed w hfin hb)).image
      rw [restrictDrawing_image_eq]
      exact Or.inr ⟨⟨(e, false), he⟩, Or.inl hs.symm⟩
    exact Or.inr ⟨⟨(e, false), ((primedDeletedEdge_iff w hfin hb e).mp he).1⟩,
      Or.inl hs.symm⟩
  · have he : ¬ primeGeomEdge w hfin hb d.1 := by
      intro he
      apply hzQ
      change z ∈ (restrictDrawing P (primeDartSet w hfin hb)
        (primeDartSet_flip_closed w hfin hb)).image
      rw [restrictDrawing_image_eq]
      exact Or.inr ⟨⟨d, he⟩, hd⟩
    exact Or.inr ⟨⟨d, ((primedDeletedEdge_iff w hfin hb d.1).mp he).1⟩, hd⟩

/-- Helper toward Lemma 5.13: the common geometric image of the hatted and
primed restrictions is precisely beta-zero, including all its endpoints.
The crossing-edge vertex characterization is needed at retained endpoints. -/
theorem hatImage_inter_primedImage_eq_betaTrace (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    (hatRealizedDrawing w hfin).image ∩
        (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image =
      {z | ∃ d : ℕ × Bool, primeBetaEdge w hfin hb d.1 ∧
        z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image} := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  ext z
  constructor
  · rintro ⟨hzH, hzQ⟩
    by_cases hv : ∃ v, P.pos v = z
    · obtain ⟨v, rfl⟩ := hv
      obtain ⟨d, hd, hdv⟩ := exclusion_pos_mem_restriction hfin
        {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl) v hzH
      have hr : MhatVertex w v := by
        rw [← hdv]
        cases hd2 : d.2
        · simpa only [kmswLimitDartVertex, hd2, Bool.false_eq_true, ↓reduceIte]
            using hd.1
        · simpa only [kmswLimitDartVertex, hd2, ↓reduceIte] using hd.2
      obtain ⟨a, ha, hav⟩ := exclusion_pos_mem_restriction hfin
        (primeDartSet w hfin hb) (primeDartSet_flip_closed w hfin hb) v hzQ
      have hp : primeVertex w hfin hb v := by
        refine ⟨a.1, ha, ?_⟩
        cases ha2 : a.2
        · exact Or.inl (by simpa only [kmswLimitDartVertex, ha2,
            Bool.false_eq_true, ↓reduceIte] using hav)
        · exact Or.inr (by simpa only [kmswLimitDartVertex, ha2, ↓reduceIte] using hav)
      rcases primeVertexSourceCharacterization_forward w hfin hb v hp with hnot | hbeta
      · exact (hnot hr).elim
      · obtain ⟨e, he, hwest | heast⟩ := hbeta
        · refine ⟨(e, false), he, Or.inl ?_⟩
          change P.pos v = (P.arc (e, false)).start
          simpa only [kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte, hwest]
            using (P.arc_start (e, false)).symm
        · refine ⟨(e, true), he, Or.inl ?_⟩
          change P.pos v = (P.arc (e, true)).start
          simpa only [kmswLimitDartVertex, ↓reduceIte, heast]
            using (P.arc_start (e, true)).symm
    · rw [restrictDrawing_image_eq] at hzH
      change z ∈ (restrictDrawing P (primeDartSet w hfin hb)
        (primeDartSet_flip_closed w hfin hb)).image at hzQ
      rw [restrictDrawing_image_eq] at hzQ
      rcases hzH with ⟨v, hvz⟩ | ⟨d, hd⟩
      · exact (hv ⟨v.val, hvz⟩).elim
      rcases hzQ with ⟨v, hvz⟩ | ⟨a, ha⟩
      · exact (hv ⟨v.val, hvz⟩).elim
      have hdi : z ∈ (P.arc d.val).interior := by
        refine ⟨hd, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun hs => hv ⟨_, (P.arc_start d.val).symm.trans hs.symm⟩,
          fun ht => hv ⟨_, (P.arc_finish d.val).symm.trans ht.symm⟩⟩
      have hai : z ∈ (P.arc a.val).interior := by
        refine ⟨ha, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun hs => hv ⟨_, (P.arc_start a.val).symm.trans hs.symm⟩,
          fun ht => hv ⟨_, (P.arc_finish a.val).symm.trans ht.symm⟩⟩
      have heq : a.val.1 = d.val.1 := by
        by_contra hne
        have hne' : a.val ≠ d.val := fun h => hne (congrArg Prod.fst h)
        have hflip : a.val ≠ (d.val.1, !d.val.2) := by
          intro h
          have hh := congrArg Prod.fst h
          exact hne hh
        exact disjoint_left.mp (P.interior_disjoint d.val a.val hne' hflip) hdi hai
      have hb : primeBetaEdge w hfin hb d.val.1 := by
        have hp : primeGeomEdge w hfin hb a.val.1 := a.property
        rw [heq] at hp
        exact hp.elim (fun hnot => (hnot d.property).elim) id
      exact ⟨d.val, hb, hd⟩
  · rintro ⟨d, hd, hz⟩
    have hboundary := (primeBetaEdge_iff_MhatWestBoundaryEdge w hfin hb d.1).mp hd
    constructor
    · rw [restrictDrawing_image_eq]
      exact Or.inr ⟨⟨d, hboundary.2.1, hboundary.2.2.1⟩, hz⟩
    · change z ∈ (restrictDrawing P (primeDartSet w hfin hb)
        (primeDartSet_flip_closed w hfin hb)).image
      rw [restrictDrawing_image_eq]
      exact Or.inr ⟨⟨d, Or.inr hd⟩, hz⟩

/-- Helper toward Lemma 5.13: deleted geometry is the hatted image with the
entire retained beta-zero trace removed. This is a set identity, not an escape -/
theorem primedDeletedGeometry_eq_hatImage_diff_betaTrace (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    (monotoneFamilyDrawing w hfin (monotone_family_all w)).image \
        (mhatPrimeDrawing w hfin hb (monotone_family_all w)).image =
      (hatRealizedDrawing w hfin).image \
        {z | ∃ d : ℕ × Bool, primeBetaEdge w hfin hb d.1 ∧
          z ∈ ((monotoneFamilyDrawing w hfin (monotone_family_all w)).arc d).image} := by
  have htrace := hatImage_inter_primedImage_eq_betaTrace w hfin hb
  have hsub := primedDeletedGeometry_subset_hatImage w hfin hb
  have hHP := restrictDrawing_image_subset
    (monotoneFamilyDrawing w hfin (monotone_family_all w))
    {d : ℕ × Bool | MhatGeometricEdge w d.1} (fun _ => Iff.rfl)
  rw [← htrace]
  ext z
  constructor
  · rintro ⟨hzP, hzQ⟩
    exact ⟨hsub ⟨hzP, hzQ⟩, fun hz => hzQ hz.2⟩
  · rintro ⟨hzH, hz⟩
    exact ⟨hHP hzH, fun hzQ => hz ⟨hzH, hzQ⟩⟩

/-- Helper toward Lemma 5.13: bounded-face exclusion is equivalent to
unboundedness of the primed complementary component through every deleted-arc
interior point. Unlike escape to a prescribed ambient face, this asks only for
arbitrarily large norms in that component. Neither side is asserted here. -/
theorem primedDeletedGeometryExclusion_iff_arcComponents_unbounded (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_deletedGeometryExclusionGoal w hfin hb ↔
      let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
      let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
      ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
        ∀ a ∈ (P.arc (e, false)).interior,
          ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ := by
  let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  change (∀ F : PlaneFaces Q, Disjoint F.val.val P.image) ↔
    ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
      ∀ a ∈ (P.arc (e, false)).interior,
        ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖
  constructor
  · intro hexcl e hm hbeta a ha
    have he := (primedDeletedEdge_iff w hfin hb e).mpr ⟨hm, hbeta⟩
    have haQ := primedDeletedArc_interior_avoids w hfin hb e he ha
    let F : Q.Face := ⟨connectedComponentIn Q.imageᶜ a, a, haQ, rfl⟩
    change Q.IsUnbounded F
    by_contra hunbounded
    change ¬ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖ at hunbounded
    push Not at hunbounded
    obtain ⟨R, hR⟩ := hunbounded
    have hbounded : Bornology.IsBounded F.val := by
      apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
      exact ⟨R, fun z hz => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
    exact disjoint_left.mp (hexcl ⟨F, hbounded⟩)
      (mem_connectedComponentIn haQ) (Or.inr ⟨(e, false), ha.1⟩)
  · intro hcomponents F
    apply disjoint_left.mpr
    intro z hzF hzP
    have hzQ := Q.face_subset_compl F.val hzF
    obtain ⟨e, he, a, ha, hza⟩ :=
      primedDeletedGeometryPoint_joins_deletedArcInterior w hfin hb z hzP hzQ
    obtain ⟨hm, hbeta⟩ := (primedDeletedEdge_iff w hfin hb e).mp he
    obtain ⟨x, _, hF⟩ := F.val.property
    have hFz : F.val.val = connectedComponentIn Q.imageᶜ z :=
      hF.trans (connectedComponentIn_eq (hF ▸ hzF))
    have haF : a ∈ F.val.val := by
      rw [hFz]
      obtain ⟨γ, hγ⟩ := hza
      exact (isPreconnected_range γ.continuous).subset_connectedComponentIn
        (show z ∈ range γ from ⟨0, γ.source⟩)
        (by rintro b ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
    have hFa : F.val.val = connectedComponentIn Q.imageᶜ a :=
      hF.trans (connectedComponentIn_eq (hF ▸ haF))
    obtain ⟨R, hR⟩ := F.property.subset_closedBall (0 : ℂ)
    obtain ⟨b, hb, hnorm⟩ := hcomponents e hm hbeta a ha R
    have hbF : b ∈ F.val.val := hFa.symm ▸ hb
    have hnormle : ‖b‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hR hbF
    exact (not_lt_of_ge hnormle) hnorm

/-- Helper toward Lemma 5.13: the same component-unboundedness criterion is
equivalent to the original ambient-face goal, by its existing exact link to
deleted-geometry exclusion. This closes no unconditional separation obligation. -/
theorem primedAmbientFace_iff_deletedArcComponents_unbounded (w : ℕ → Fin 3)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    primedBoundedFace_ambientFaceGoal w hfin hb ↔
      let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
      let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
      ∀ e, MhatGeometricEdge w e → ¬ primeBetaEdge w hfin hb e →
        ∀ a ∈ (P.arc (e, false)).interior,
          ∀ R : ℝ, ∃ z ∈ connectedComponentIn Q.imageᶜ a, R < ‖z‖ :=
  (primedBoundedFace_ambientFaceGoal_iff_deletedGeometryExclusion w hfin hb).trans
    (primedDeletedGeometryExclusion_iff_arcComponents_unbounded w hfin hb)

end DirectedDistances.KMSW
