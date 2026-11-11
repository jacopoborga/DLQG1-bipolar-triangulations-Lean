module

public import DirectedDistances.KMSW.InftyCutEntry
public import DirectedDistances.KMSW.InftyCutCore
public import DirectedDistances.KMSW.InftyCutP2








public section
namespace DirectedDistances.KMSW

open Quiver Filter MeasureTheory DirectedDistances.RandomWalk

/-- The explicit finite exceptional vertex set in `lem-infty-cut`
leftmost hit, together with the boundary vertices in the window. -/
@[expose] noncomputable def cutWindowP3Exception (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) : Set (PresentVertex w) :=
  (fun n => (⟨n⟩ : PresentVertex w)) ''
      Set.Iio ((kmswStage w (boundaryHitTime w h (-(K : ℤ)))).nextVertex) ∪
    (fun k => (⟨boundaryVertex w h k⟩ : PresentVertex w)) ''
      Set.Icc (-(K : ℤ)) (K : ℤ)

/-- The finite P3' family from `cut_entry_window_future_suffix`, before
pulling its vertices back through the P1 embedding -/
@[expose] def cutWindowP3EntrySet (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) : Set (PresentVertex w) :=
  {z | z ∈ cutWindowP3Exception w h K ∧
    ∃ r : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) z,
      ∀ e ∈ pathEdgeList r, ∀ he : EdgePresent w e,
        boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he}

/-- The edge region after the leftmost window hit. Membership is vacuous for
missing edge IDs and asserts the late activation time for every present edge -/
@[expose] def cutWindowP3Region (w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ) : Set ℕ :=
  {e | ∀ he : EdgePresent w e,
    boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he}

/-- IDs of allocated vertices in the P3' entry family after pulling them back
through an embedding. This is the finite family to which P1 and P2 apply -/
@[expose] def cutWindowP3AllocatedIdSet (u w : ℕ → Fin 3)
    (f : PresentVertex u ↪ PresentVertex w)
    (h : BoundaryHitWitnesses w) (K : ℕ) : Set ℕ :=
  {i | ∃ b : PresentVertex u, b.id = i ∧
    (∃ N, b.id < (kmswStage u N).nextVertex) ∧
    ∃ z ∈ cutWindowP3EntrySet w h K, f b = z}

/-- The ID set is finite because `f` is injective and the P3' entry set is -/
theorem cutWindowP3AllocatedIdSet_finite (u w : ℕ → Fin 3)
    (f : PresentVertex u ↪ PresentVertex w)
    (h : BoundaryHitWitnesses w) (K : ℕ) :
    (cutWindowP3AllocatedIdSet u w f h K).Finite := by
  classical
  have hentry : (cutWindowP3EntrySet w h K).Finite := by
    have h := cut_entry_window_future_suffix w h K
    simpa only [cutWindowP3EntrySet, cutWindowP3Exception] using h.2.1
  have hpre : (f ⁻¹' cutWindowP3EntrySet w h K).Finite :=
    Set.Finite.preimage_embedding f hentry
  have himage : ((fun b : PresentVertex u => b.id) ''
      (f ⁻¹' cutWindowP3EntrySet w h K)).Finite := hpre.image _
  apply himage.subset
  rintro i ⟨b, hb, halloc, z, hz, hfb⟩
  refine ⟨b, ?_, hb⟩
  change f b ∈ cutWindowP3EntrySet w h K
  simpa [hfb] using hz

/-- The Finset of allocated P3' entry IDs, obtained from the finite set of
their possible preimages (`lem-infty-cut`, -/
@[expose] noncomputable def cutWindowP3AllocatedIds (u w : ℕ → Fin 3)
    (f : PresentVertex u ↪ PresentVertex w)
    (h : BoundaryHitWitnesses w) (K : ℕ) : Finset ℕ :=
  (cutWindowP3AllocatedIdSet_finite u w f h K).toFinset

/-- The exact common-region P3 premise of
`boundary_windowFiniteAvoidance_of_rPhaseCommonRegions`, together with
finiteness of the explicit exception and allocation of every ID in the
constructed entry Finset (`lem-infty-cut`,
chosen allocated preimage using the structure equality
`⟨b.id⟩ = b`. -/
theorem cutWindowP3_of_lateRange (u w : ℕ → Fin 3)
    (h : BoundaryHitWitnesses w) (K : ℕ)
    (f : PresentVertex u ↪ PresentVertex w)
    (hRange : ∀ z : PresentVertex w,
      (∃ r : Path (⟨boundaryVertex w h (-(K : ℤ))⟩ : PresentVertex w) z,
        ∀ e ∈ pathEdgeList r, ∀ he : EdgePresent w e,
          boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he) →
      ∃ b : PresentVertex u, f b = z ∧
        ∃ N, b.id < (kmswStage u N).nextVertex) :
    (cutWindowP3Exception w h K).Finite ∧
    (∀ i ∈ cutWindowP3AllocatedIds u w f h K,
      ∃ N, i < (kmswStage u N).nextVertex) ∧
    (∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
        v ∈ cutWindowP3Exception w h K ∨
        ∃ i ∈ cutWindowP3AllocatedIds u w f h K,
          ∃ q : Path (f (⟨i⟩ : PresentVertex u)) v,
            (∀ e ∈ pathEdgeList q, e ∈ cutWindowP3Region w h K) ∧
            ∀ y ∈ q.vertices, y ∈ p.vertices ∨ y ∈ cutWindowP3Exception w h K) := by
  classical
  have hentry := cut_entry_window_future_suffix w h K
  have hE : (cutWindowP3Exception w h K).Finite := by
    simpa only [cutWindowP3Exception] using hentry.1
  have hA : (cutWindowP3EntrySet w h K).Finite := by
    simpa only [cutWindowP3EntrySet, cutWindowP3Exception] using hentry.2.1
  refine ⟨hE, ?_, ?_⟩
  · intro i hi
    change i ∈ (cutWindowP3AllocatedIdSet_finite u w f h K).toFinset at hi
    rw [Set.Finite.mem_toFinset] at hi
    rcases hi with ⟨b, rfl, halloc, z, hz, hfb⟩
    exact halloc
  · intro k hklo hkhi v p
    have hpaths := hentry.2.2 k hklo hkhi p
    change v ∈ cutWindowP3Exception w h K ∨
      ∃ z ∈ cutWindowP3EntrySet w h K, ∃ q : Path z v,
        (∀ e ∈ pathEdgeList q, ∀ he : EdgePresent w e,
          boundaryHitTime w h (-(K : ℤ)) ≤ actTime w e he) ∧
        ∀ y ∈ q.vertices, y ∈ p.vertices at hpaths
    rcases hpaths with hv | ⟨z, hz, q, hq, hvertices⟩
    · exact Or.inl hv
    · rcases hz with ⟨hzE, r, hr⟩
      obtain ⟨b, hfb, halloc⟩ := hRange z ⟨r, hr⟩
      cases b with
      | mk bid =>
        subst z
        let i := bid
        have hi : i ∈ cutWindowP3AllocatedIds u w f h K := by
          change i ∈ (cutWindowP3AllocatedIdSet_finite u w f h K).toFinset
          rw [Set.Finite.mem_toFinset]
          exact ⟨⟨bid⟩, rfl, halloc, f (⟨bid⟩ : PresentVertex u),
            ⟨hzE, ⟨r, hr⟩⟩, rfl⟩
        refine Or.inr ⟨i, hi, q, ?_, ?_⟩
        · intro e he hePresent
          exact hq e he hePresent
        · intro y hy
          exact Or.inl (hvertices y hy)

/-- Conditional a.s. assembly for the premise consumed verbatim by
`BusemannM0OnePremise` (`thm-busemann`,
`ae_cutWindowRPhaseCodes_infinite_common_finiteAvoidance`, and P3 is proved
above. The sole open inputs are P1 for an a.s. family of embeddings: the
path-lifting property on the late region and an allocated-range property
for every vertex reachable from the leftmost window boundary vertex by a path
all of whose present edges activate at or after the window hit time. -/
theorem ae_cutWindow_finiteAvoidance_of_P1 :
    (∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∃ f : ∀ K : ℕ,
          PresentVertex (cutWindowRPhaseCodes ω h K) ↪
            PresentVertex (fun i => ω (i + 1)),
          (∀ (K : ℕ) (z : PresentVertex (fun i => ω (i + 1))),
            (∃ r : Path
              (⟨boundaryVertex (fun i => ω (i + 1)) h (-(K : ℤ))⟩ :
                PresentVertex (fun i => ω (i + 1))) z,
              ∀ e ∈ pathEdgeList r, ∀ he : EdgePresent (fun i => ω (i + 1)) e,
                boundaryHitTime (fun i => ω (i + 1)) h (-(K : ℤ)) ≤
                  actTime (fun i => ω (i + 1)) e he) →
            ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
              f K b = z ∧
                ∃ N, b.id < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex) ∧
          (∀ (K : ℕ) (i : ℕ),
            i ∈ cutWindowP3AllocatedIds (cutWindowRPhaseCodes ω h K)
              (fun i => ω (i + 1)) (f K) h K →
            ∀ {v} (q : Path
              (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v),
              (∀ e ∈ pathEdgeList q,
                e ∈ cutWindowP3Region (fun i => ω (i + 1)) h K) →
              ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
                ∃ r : Path (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) b,
                  f K b = v ∧ ∀ y ∈ r.vertices, f K y ∈ q.vertices)) →
      ∀ᵐ ω ∂iidCodeMeasure,
        ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
          ∀ K : ℕ, ∃ z : PresentVertex (fun i => ω (i + 1)),
            ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
              FiniteAvoidance
                (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
                  PresentVertex (fun i => ω (i + 1))) z := by
  intro hOpen
  filter_upwards [ae_cutWindowRPhaseCodes_infinite_common_finiteAvoidance,
    hOpen] with ω hP2 hInputs
  intro h
  obtain ⟨f, hRange, hP1⟩ := hInputs h
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let A : ℕ → Finset ℕ := fun K =>
    cutWindowP3AllocatedIds (cutWindowRPhaseCodes ω h K) w (f K) h K
  let region : ℕ → Set ℕ := fun K => cutWindowP3Region w h K
  let E : ℕ → Set (PresentVertex w) := fun K => cutWindowP3Exception w h K
  have halloc : ∀ K i, i ∈ A K →
      ∃ N, i < (kmswStage (cutWindowRPhaseCodes ω h K) N).nextVertex := by
    intro K i hi
    change i ∈ (cutWindowP3AllocatedIdSet_finite
      (cutWindowRPhaseCodes ω h K) w (f K) h K).toFinset at hi
    have himem := (cutWindowP3AllocatedIdSet_finite
      (cutWindowRPhaseCodes ω h K) w (f K) h K).mem_toFinset.mp hi
    rcases himem with ⟨b, rfl, hN, z, hz, hfb⟩
    exact hN
  have hP2 : ∀ K, {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
      ∀ i ∈ A K, FiniteAvoidance
        (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) c}.Infinite :=
    hP2 h A halloc
  have hE : ∀ K, (E K).Finite := by
    intro K
    exact (cutWindowP3_of_lateRange (cutWindowRPhaseCodes ω h K) w h K
      (f K) (hRange K)).1
  have hP1' : ∀ K i, i ∈ A K →
      ∀ {v} (q : Path
        (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v),
        (∀ e ∈ pathEdgeList q, e ∈ region K) →
        ∃ b : PresentVertex (cutWindowRPhaseCodes ω h K),
          ∃ r : Path (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K)) b,
            f K b = v ∧ ∀ y ∈ r.vertices, f K y ∈ q.vertices := by
    intro K i hi v q hq
    exact hP1 K i hi q (by simpa [region] using hq)
  have hP3 : ∀ (K : ℕ) (k : ℤ), -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
        v ∈ E K ∨ ∃ i ∈ A K,
          ∃ q : Path (f K (⟨i⟩ : PresentVertex (cutWindowRPhaseCodes ω h K))) v,
            (∀ e ∈ pathEdgeList q, e ∈ region K) ∧
            ∀ y ∈ q.vertices, y ∈ p.vertices ∨ y ∈ E K := by
    intro K k hklo hkhi v p
    rcases cutWindowP3_of_lateRange (cutWindowRPhaseCodes ω h K)
        w h K (f K) (hRange K) with ⟨_, _, hpaths⟩
    simpa [A, region, E] using hpaths k hklo hkhi p
  exact boundary_windowFiniteAvoidance_of_rPhaseCommonRegions
    ω h f A region E hE hP1' hP2 hP3

end DirectedDistances.KMSW
