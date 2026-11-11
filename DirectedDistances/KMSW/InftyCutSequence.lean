module

public import DirectedDistances.KMSW.BusemannM0Unconditional
public import DirectedDistances.KMSW.InftyCutP3

/-! # Infinite boundary cut sequences

The infinite-cut sequence form associated with `lem-infty-cut`
`boundaryVertex` labelling on the iid-code carrier `fun i => ω (i + 1)`.
The source-to-Lean labelling and carrier rulings F1 and F4 in -/

public section
namespace DirectedDistances.KMSW

open Quiver Filter MeasureTheory DirectedDistances.RandomWalk

/-- Infinite-witness strengthening of the common-region window lemma
labelling and the carrier of its hypotheses; see F1/F4 in -/
theorem boundary_windowInfiniteFiniteAvoidance_of_commonRegion
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (K : ℕ)
    (u : ℕ → Fin 3) (f : PresentVertex u ↪ PresentVertex w)
    (A : Finset ℕ) (region : Set ℕ) (E : Set (PresentVertex w)) (hE : E.Finite)
    (hP1 : ∀ i ∈ A, ∀ {v} (q : Path (f (⟨i⟩ : PresentVertex u)) v),
      (∀ e ∈ pathEdgeList q, e ∈ region) →
        ∃ b : PresentVertex u, ∃ r : Path (⟨i⟩ : PresentVertex u) b,
          f b = v ∧ ∀ y ∈ r.vertices, f y ∈ q.vertices)
    (hP2 : {c : PresentVertex u | ∀ i ∈ A,
      FiniteAvoidance (⟨i⟩ : PresentVertex u) c}.Infinite)
    (hP3 : ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      ∀ {v} (p : Path (⟨boundaryVertex w h k⟩ : PresentVertex w) v),
        v ∈ E ∨ ∃ i ∈ A, ∃ q : Path (f (⟨i⟩ : PresentVertex u)) v,
          (∀ e ∈ pathEdgeList q, e ∈ region) ∧
          ∀ y ∈ q.vertices, y ∈ p.vertices ∨ y ∈ E) :
    {z : PresentVertex w | ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
      FiniteAvoidance (⟨boundaryVertex w h k⟩ : PresentVertex w) z}.Infinite := by
  classical
  let C : Set (PresentVertex u) := {c | ∀ i ∈ A,
    FiniteAvoidance (⟨i⟩ : PresentVertex u) c}
  have hgood : (C \ (f ⁻¹' E)).Infinite := hP2.sdiff (hE.preimage_embedding f)
  let S : Set (PresentVertex w) := {z | ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
    FiniteAvoidance (⟨boundaryVertex w h k⟩ : PresentVertex w) z}
  have hsub : f '' (C \ (f ⁻¹' E)) ⊆ S := by
    rintro z ⟨c, ⟨hc, hcE⟩, rfl⟩
    intro k hk₁ hk₂
    apply finiteAvoidance_of_finite_family_lift _ f A E hE c hc
    intro v p hp
    rcases hP3 k hk₁ hk₂ p with hv | ⟨i, hi, q, hqregion, hqvertices⟩
    · exact Or.inl hv
    · obtain ⟨b, r, hb, hr⟩ := hP1 i hi q hqregion
      refine Or.inr ⟨i, hi, b, hb, r, ?_⟩
      intro hcr
      rcases hqvertices (f c) (hr c hcr) with hcp | hcException
      · exact hp hcp
      · exact hcE hcException
  have hinj : Set.InjOn f (C \ (f ⁻¹' E)) := by
    intro a ha b hb hab
    exact f.injective hab
  exact (hgood.image hinj).mono hsub

/-- Almost surely, every boundary-hit witness and every finite window has
infinitely many common finite-avoidance vertices. This reassembles P1 using
`hatInputExists`, P2 from `InftyCutP2`, and P3 from
`cutWindowP3_of_lateRange` (`lem-infty-cut`,
F1/F4 remain as recorded in -/
theorem ae_cutWindow_finiteAvoidance_infinite :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ K : ℕ,
          {z : PresentVertex (fun i => ω (i + 1)) |
            ∀ k : ℤ, -(K : ℤ) ≤ k → k ≤ K →
              FiniteAvoidance
                (⟨boundaryVertex (fun i => ω (i + 1)) h k⟩ :
                  PresentVertex (fun i => ω (i + 1))) z}.Infinite := by
  filter_upwards [ae_cutWindowRPhaseCodes_infinite_common_finiteAvoidance,
    cutWindowP1Family_of_hatInput hatInputExists] with ω hP2 hP1
  intro h K
  obtain ⟨f, hRange, hP1⟩ := hP1 h
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
  have hP2' : ∀ K, {c : PresentVertex (cutWindowRPhaseCodes ω h K) |
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
  exact boundary_windowInfiniteFiniteAvoidance_of_commonRegion
    w h K (cutWindowRPhaseCodes ω h K) (f K) (A K) (region K) (E K)
    (hE K) (hP1' K) (hP2' K) (hP3 K)

/-- Extracts an injectively indexed sequence from an infinite set of common
window cuts and proves the eventual path-visiting property. This is a helper
hit-indexed labelling and carrier remain subject to F1/F4 in -/
theorem boundary_windowInfiniteAvoidance_sequence
    (w : ℕ → Fin 3) (h : BoundaryHitWitnesses w) (K : ℕ)
    (S : Set (PresentVertex w)) (hS : S.Infinite)
    (hAvoid : ∀ z ∈ S, ∀ ℓ : ℤ, -(K : ℤ) ≤ ℓ → ℓ ≤ K →
      FiniteAvoidance (⟨boundaryVertex w h ℓ⟩ : PresentVertex w) z)
    (k k' : ℤ) (hklo : -(K : ℤ) ≤ k) (hkhi : k' ≤ K) :
    ∃ v : ℕ → PresentVertex w, Function.Injective v ∧
      (∀ m, v m ∈ S) ∧
      ∀ ℓ : ℤ, ℓ ∈ Set.Icc k k' →
        ∀ y : ℕ → PresentVertex w, Function.Injective y →
          (∀ j, Quiver.Reachable
            (⟨boundaryVertex w h ℓ⟩ : PresentVertex w) (y j)) →
            ∀ m, ∃ J, ∀ j, J ≤ j → ∀ p : Path
              (⟨boundaryVertex w h ℓ⟩ : PresentVertex w) (y j),
                (v m : PresentVertex w) ∈ p.vertices := by
  classical
  let e : ℕ ↪ S := hS.natEmbedding
  let v : ℕ → PresentVertex w := fun m => (e m).val
  have hv : Function.Injective v := by
    intro m n hmn
    apply e.injective
    exact Subtype.ext hmn
  refine ⟨v, hv, ?_, ?_⟩
  · intro m
    exact (e m).property
  · intro ℓ hℓ y hy hreach m
    have hℓlo : -(K : ℤ) ≤ ℓ := le_trans hklo hℓ.1
    have hℓhi : ℓ ≤ K := le_trans hℓ.2 hkhi
    exact finiteAvoidance_eventually_forces_path_through
      (hAvoid (v m) (e m).property ℓ hℓlo hℓhi) y hy hreach

/-- Almost surely there is a boundary-hit witness whose hit-indexed boundary
vertices satisfy the sequence form of `lem-infty-cut`
sequence works for every boundary start in `[k,k']` and every injective
reachable endpoint sequence. The source-to-Lean labelling and carrier
caveats F1/F4 remain recorded in -/
theorem ae_lem_infty_cut_sequence :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ k k' : ℤ, k < k' →
          ∃ v : ℕ → PresentVertex (fun i => ω (i + 1)),
            Function.Injective v ∧
            ∀ ℓ : ℤ, ℓ ∈ Set.Icc k k' →
              ∀ y : ℕ → PresentVertex (fun i => ω (i + 1)),
                Function.Injective y →
                (∀ j, Quiver.Reachable
                  (⟨boundaryVertex (fun i => ω (i + 1)) h ℓ⟩ :
                    PresentVertex (fun i => ω (i + 1))) (y j)) →
                ∀ m, ∃ J, ∀ j, J ≤ j → ∀ p : Path
                  (⟨boundaryVertex (fun i => ω (i + 1)) h ℓ⟩ :
                    PresentVertex (fun i => ω (i + 1))) (y j),
                    List.Mem (v m)
                      (Quiver.Path.vertices
                        (V := PresentVertex (fun i => ω (i + 1))) p) := by
  filter_upwards [ae_cutWindow_finiteAvoidance_infinite,
    iidCodes_ae_boundaryHitWitnesses] with ω hCuts hHits
  refine ⟨hHits, ?_⟩
  intro k k' hk
  let K : ℕ := max k.natAbs k'.natAbs
  have hklo : -(K : ℤ) ≤ k := by
    have hAbs : -(k.natAbs : ℤ) ≤ k := by cases k <;> simp <;> omega
    have hmax : k.natAbs ≤ K := Nat.le_max_left _ _
    have hmax' : (k.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hmax
    exact le_trans (neg_le_neg hmax') hAbs
  have hkhi : k' ≤ K := by
    have hAbs : k' ≤ (k'.natAbs : ℤ) := by cases k' <;> simp <;> omega
    have hmax : k'.natAbs ≤ K := Nat.le_max_right _ _
    have hmax' : (k'.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hmax
    exact le_trans hAbs hmax'
  let w : ℕ → Fin 3 := fun i => ω (i + 1)
  let S : Set (PresentVertex w) := {z | ∀ ℓ : ℤ, -(K : ℤ) ≤ ℓ → ℓ ≤ K →
    FiniteAvoidance (⟨boundaryVertex w hHits ℓ⟩ : PresentVertex w) z}
  have hS : S.Infinite := hCuts hHits K
  have hAvoid : ∀ z ∈ S, ∀ ℓ : ℤ, -(K : ℤ) ≤ ℓ → ℓ ≤ K →
      FiniteAvoidance (⟨boundaryVertex w hHits ℓ⟩ : PresentVertex w) z := by
    intro z hz ℓ hℓlo hℓhi
    exact hz ℓ hℓlo hℓhi
  obtain ⟨v, hv, hvS, hseq⟩ := boundary_windowInfiniteAvoidance_sequence
    w hHits K S hS hAvoid k k' hklo hkhi
  refine ⟨v, hv, ?_⟩
  intro ℓ hℓ y hy hreach m
  exact hseq ℓ hℓ y hy hreach m

end DirectedDistances.KMSW
