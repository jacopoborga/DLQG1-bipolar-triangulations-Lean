module

public import DirectedDistances.PaperProofs.Section7.LongPathAE
import DirectedDistances.KMSW.InftyCutSequence
import DirectedDistances.KMSW.CommonFutureM0
import DirectedDistances.KMSW.LeftmostGeodesicPlanar
import Mathlib.Order.Monotone.Basic

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW
open MeasureTheory DirectedDistances.RandomWalk
open DirectedDistances.Recursive

/-- Lemma 5.4: a visited prefix vertex is a stored initial vertex; the infinite-geodesic
existence hgeo (Lemma 5.4 on raw iid M_{0,∞}) is an explicit input; not the paper result. -/
private theorem visited_prefix_vertex {w : ℕ → Fin 3} {a z : PresentVertex w}
    (P : InfinitePresentPath w a) (N : ℕ) (hz : z ∈ (P.initial N).2.vertices) :
    ∃ i, z = (P.initial i).1 := by
  obtain ⟨p, q, hpq⟩ := (P.initial N).2.exists_eq_comp_of_mem_vertices hz
  have hi : p.length ≤ N := by
    have hlen := P.prefix_length N
    rw [hpq, Path.length_comp] at hlen
    omega
  have htake : (pathEdgeList (P.initial N).2).take p.length = pathEdgeList p := by
    rw [hpq, pathEdgeList_comp, List.take_append]
    simp only [pathEdgeList_length, Nat.sub_self, List.take_zero, List.append_nil]
    rw [← pathEdgeList_length p, List.take_length]
  have he : pathEdgeList p = pathEdgeList (P.initial p.length).2 := by
    rw [← htake, P.prefix_edges N, P.prefix_edges p.length]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hi]
    · intro i hi₁ hi₂
      simp only [List.getElem_take, List.getElem_ofFn]
  have hpEnd := pathEdgeList_endpoint p
  have hEnd := pathEdgeList_endpoint (P.initial p.length).2
  rw [he] at hpEnd
  refine ⟨p.length, ?_⟩
  exact congrArg (fun j : ℕ => (⟨j⟩ : PresentVertex w)) (hpEnd.symm.trans hEnd)

/-- Lemma 5.4: common finite-avoidance separators give cofinal reachable targets on a
longest path; the infinite-geodesic existence hgeo (Lemma 5.4 on raw iid M_{0,∞})
is an explicit input; not the paper result. -/
private theorem cofinal_reachable_targets {w : ℕ → Fin 3} {a : ℕ}
    {b : PresentVertex w} (P : InfinitePresentPath w ⟨a⟩)
    (hP : P.HasLongestSegments)
    (C : Set (PresentVertex w)) (hC : C.Infinite)
    (hCa : ∀ z ∈ C, FiniteAvoidance (⟨a⟩ : PresentVertex w) z)
    (hCb : ∀ z ∈ C, FiniteAvoidance b z)
    (u : ℕ → PresentVertex w) (hu : Function.Injective u)
    (hbu : ∀ j, Reachable b (u j)) :
    ∃ y : ℕ → PresentVertex w, Function.Injective y ∧
      (∀ T, ∃ N, ∀ r, N ≤ r → ∃ s, T ≤ s ∧ y r = (P.initial s).1) ∧
      ∀ r, Reachable b (y r) := by
  classical
  let f : ℕ → PresentVertex w := fun i => (P.initial i).1
  have hf : Function.Injective f := by
    intro i j hij
    exact P.index_eq_of_initial_eq w P hP hP i j hij
  have hfa : ∀ j, Reachable (⟨a⟩ : PresentVertex w) (f j) :=
    fun j => ⟨(P.initial j).2⟩
  have hvisit : ∀ z ∈ C, ∃ i, z = f i := by
    intro z hz
    obtain ⟨N, hN⟩ := finiteAvoidance_eventually_forces_path_through
      (hCa z hz) f hf hfa
    exact visited_prefix_vertex P N (hN N le_rfl (P.initial N).2)
  have hreach : ∀ z ∈ C, Reachable b z := by
    intro z hz
    obtain ⟨N, hN⟩ := finiteAvoidance_eventually_forces_path_through
      (hCb z hz) u hu hbu
    obtain ⟨p⟩ := hbu N
    obtain ⟨q, _, _⟩ := p.exists_eq_comp_of_mem_vertices (hN N le_rfl p)
    exact ⟨q⟩
  let S : Set ℕ := {i | Reachable b (f i)}
  have hsub : C ⊆ f '' S := by
    intro z hz
    obtain ⟨i, hi⟩ := hvisit z hz
    refine ⟨i, ?_, hi.symm⟩
    change Reachable b (f i)
    rw [← hi]
    exact hreach z hz
  have hS : S.Infinite := by
    intro hfinite
    exact hC ((hfinite.image f).subset hsub)
  obtain ⟨φ, hφ, hφS⟩ := Nat.exists_strictMono_subsequence (P := fun i => i ∈ S) (by
    intro N
    obtain ⟨i, hi, hNi⟩ := Set.infinite_iff_exists_gt.mp hS N
    exact ⟨i, hNi, hi⟩)
  have hφge : ∀ r, r ≤ φ r := by
    intro r
    induction r with
    | zero => exact Nat.zero_le _
    | succ r ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (hφ (Nat.lt_succ_self r)))
  refine ⟨fun r => f (φ r), hf.comp hφ.injective, ?_, fun r => hφS r⟩
  intro T
  refine ⟨T, fun r hr => ⟨φ r, hr.trans (hφge r), rfl⟩⟩

/-- Lemma 5.4: the exact input consumed by longPath_ae follows from infinite geodesics;
the infinite-geodesic existence hgeo (Lemma 5.4 on raw iid M_{0,∞}) is an explicit
input; not the paper result. -/
theorem longPath_hinput_of_geodesics
    (hgeo : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ k : ℤ,
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasLongestSegments) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)),
      ∀ ell k : ℕ, 1 ≤ ell → ell < k →
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h (-(ell : ℤ))⟩,
          P.HasLongestSegments ∧
          ∃ y : ℕ → PresentVertex (fun i => ω (i + 1)),
            Function.Injective y ∧
            (∀ T, ∃ N, ∀ r, N ≤ r →
              ∃ s, T ≤ s ∧ y r = (P.initial s).1) ∧
            (∀ r, Reachable
              (⟨boundaryVertex (fun i => ω (i + 1)) h (-(k : ℤ))⟩ :
                PresentVertex (fun i => ω (i + 1))) (y r)) := by
  filter_upwards [hgeo, ae_cutWindow_finiteAvoidance_infinite,
    iidCodes_ae_boundaryCommonSequence] with ω hgeoω hcuts hcommon
  intro h ell k hell hlt
  obtain ⟨P, hP⟩ := hgeoω h (-(ell : ℤ))
  refine ⟨P, hP, ?_⟩
  obtain ⟨u, hu, hreach⟩ := hcommon h (-(ell : ℤ)) (-(k : ℤ))
  apply cofinal_reachable_targets P hP _ (hcuts h k)
  · intro z hz
    exact hz (-(ell : ℤ)) (by omega) (by omega)
  · intro z hz
    exact hz (-(k : ℤ)) le_rfl (by omega)
  · exact hu
  · exact fun j => (hreach j).2

/-- Lemma 5.4: compose the geodesic input with longPath_ae; the infinite-geodesic
existence hgeo (Lemma 5.4 on raw iid M_{0,∞}) is an explicit input; not the paper result. -/
theorem longPath_ae_of_geodesics
    (hgeo : ∀ᵐ ω ∂iidCodeMeasure,
      ∀ h : BoundaryHitWitnesses (fun i => ω (i + 1)), ∀ k : ℤ,
        ∃ P : InfinitePresentPath (fun i => ω (i + 1))
          ⟨boundaryVertex (fun i => ω (i + 1)) h k⟩, P.HasLongestSegments) :
    ∀ᵐ ω ∂iidCodeMeasure,
      ∃ hw : BoundaryHitWitnesses (fun i => ω (i + 1)),
        ∀ ℓ k : ℕ, 1 ≤ ℓ → ℓ < k →
          ∃ a b : StagePresentVertex (fun i => ω (i + 1))
            (boundaryHitTime (fun i => ω (i + 1)) hw (-(k : ℤ))),
            ∃ q : Path a b,
              (max (busemannLDPMeasurableVersion ω (-(ℓ : ℤ)) -
                busemannLDPMeasurableVersion ω (-(k : ℤ))) 0).toNat ≤ q.length := by
  exact longPath_ae (longPath_hinput_of_geodesics hgeo)

end DirectedDistances.PaperProofs.Section7
