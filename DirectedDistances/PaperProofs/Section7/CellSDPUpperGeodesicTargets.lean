module

public import DirectedDistances.KMSW.BusemannBoundaryM0
public import DirectedDistances.KMSW.FiniteAvoidance
public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.LeftmostGeodesicAssembly

/-! Supporting lemmas for paper labels `lem-cell-sdp-upper` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open Quiver DirectedDistances.KMSW

private theorem presentVertex_ext {w : ℕ → Fin 3} {u v : PresentVertex w}
    (h : u.id = v.id) : u = v := by
  cases u
  cases v
  cases h
  rfl

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
  exact presentVertex_ext (hpEnd.symm.trans hEnd)

private theorem initial_vertex_ne_of_lt {w : ℕ → Fin 3} {a : PresentVertex w}
    (P : InfinitePresentPath w a) {i j : ℕ} (hij : i < j) :
    (P.initial i).1 ≠ (P.initial j).1 := by
  intro heq
  obtain ⟨z, p₁, p₂, hcomp, hp₁⟩ :=
    (P.initial j).2.exists_eq_comp_of_le_length
      (n := i) (by rw [P.prefix_length j]; omega)
  let full := List.ofFn (fun k : Fin j => P.edge k.val)
  have hfull : pathEdgeList p₁ ++ pathEdgeList p₂ = full := by
    rw [← pathEdgeList_comp, ← hcomp, P.prefix_edges]
  have hsplit : full.take i ++ full.drop i = full := List.take_append_drop i full
  have hconcat : pathEdgeList p₁ ++ pathEdgeList p₂ =
      full.take i ++ full.drop i := by
    calc
      pathEdgeList p₁ ++ pathEdgeList p₂ = full := hfull
      _ = full.take i ++ full.drop i := hsplit.symm
  have htake : pathEdgeList p₁ = full.take i :=
    List.append_inj_left hconcat (by
      rw [pathEdgeList_length, hp₁, List.length_take]
      simp [full]
      omega)
  have hprefix : pathEdgeList (P.initial i).2 = full.take i := by
    rw [P.prefix_edges]
    apply List.ext_getElem
    · simp [full]
      omega
    · intro k hk₁ hk₂
      simp [full]
  have hz : z.id = (P.initial i).1.id := by
    have hpEnd := pathEdgeList_endpoint p₁
    have hiEnd := pathEdgeList_endpoint (P.initial i).2
    rw [htake, ← hprefix] at hpEnd
    exact hpEnd.symm.trans hiEnd
  have hcycleStartEnd : z = (P.initial j).1 :=
    (presentVertex_ext hz).trans heq
  cases hcycleStartEnd
  have hp₂zero : p₂.length = 0 := presentVertex_acyclic w _ p₂
  have htotal := P.prefix_length j
  rw [hcomp, Path.length_comp, hp₁, hp₂zero] at htotal
  omega

private theorem initial_vertex_injective {w : ℕ → Fin 3} {a : PresentVertex w}
    (P : InfinitePresentPath w a) :
    Function.Injective (fun i => (P.initial i).1) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (initial_vertex_ne_of_lt P hlt) hij
  · exact (initial_vertex_ne_of_lt P hgt) hij.symm




theorem sdp_separator_targets_on_geodesic (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w) (ℓ : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h0 ℓ))
    (y : ℕ → PresentVertex (fun i => w (n + i))) (hy : Function.Injective y)
    (havoid : ∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
      (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) :
    ∀ N, ∃ j s, N ≤ s ∧
      (P.initial s).1 =
        (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w) := by
  classical
  let g : ℕ → PresentVertex w := fun j =>
    ⟨kmswWindowVertexMapInf w n (y j).id⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hy
    apply presentVertex_ext
    apply kmswWindowVertexMapInf_injective w n
    exact congrArg PresentVertex.id hij
  let f : ℕ → PresentVertex w := fun i => (P.initial i).1
  have hf : Function.Injective f := initial_vertex_injective P
  have hreach : ∀ i, Reachable (boundaryPresentVertex w h0 ℓ) (f i) :=
    fun i => ⟨(P.initial i).2⟩
  intro N
  let B : Set (PresentVertex w) :=
    Set.range (fun s : Fin (N + 1) => (P.initial s.val).1)
  have hB : B.Finite := Set.finite_range _
  have hpre : (g ⁻¹' B).Finite := by
    apply Set.Finite.preimage (s := B)
    · intro i hi j hj hij
      exact hg hij
    · exact hB
  obtain ⟨M, hM⟩ := hpre.bddAbove
  let j := M + 1
  have hjoutside : j ∉ g ⁻¹' B := by
    intro hj
    have hjle := hM hj
    dsimp [j] at hjle
    omega
  have hjB : g j ∉ B := by
    intro hj
    exact hjoutside hj
  obtain ⟨K, hK⟩ := finiteAvoidance_eventually_forces_path_through
    (havoid j) f hf hreach
  let t := max (N + 1) K
  have htK : K ≤ t := Nat.le_max_right _ _
  have hvisit := hK t htK (P.initial t).2
  obtain ⟨s, hs⟩ := visited_prefix_vertex P t hvisit
  have hsN : N ≤ s := by
    by_contra hnot
    have hsle : s ≤ N := by omega
    have hinB : g j ∈ B := by
      refine ⟨⟨s, by omega⟩, ?_⟩
      exact hs.symm
    exact hjB hinB
  exact ⟨j, s, hsN, hs.symm⟩




theorem sdp_separator_targets_infinite_selection (w : ℕ → Fin 3) (n : ℕ)
    (h0 : BoundaryHitWitnesses w) (ℓ : ℤ)
    (P : InfinitePresentPath w (boundaryPresentVertex w h0 ℓ))
    (y : ℕ → PresentVertex (fun i => w (n + i))) (hy : Function.Injective y)
    (havoid : ∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
      (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)) :
    ∃ j s : ℕ → ℕ, Function.Injective j ∧ StrictMono s ∧
      ∀ r, (P.initial (s r)).1 =
        (⟨kmswWindowVertexMapInf w n (y (j r)).id⟩ : PresentVertex w) := by
  classical
  let g : ℕ → PresentVertex w := fun j =>
    ⟨kmswWindowVertexMapInf w n (y j).id⟩
  have hex : ∀ N, ∃ p : ℕ × ℕ, N ≤ p.2 ∧
      (P.initial p.2).1 = g p.1 := by
    intro N
    obtain ⟨j, s, hN, hvisit⟩ :=
      sdp_separator_targets_on_geodesic w n h0 ℓ P y hy havoid N
    exact ⟨(j, s), hN, hvisit⟩
  choose q hq using hex
  let pair : ℕ → ℕ × ℕ := Nat.rec (q 0) (fun _ prev => q (prev.2 + 1))
  have pair_succ (r : ℕ) : pair (r + 1) = q ((pair r).2 + 1) := rfl
  have hvisit : ∀ r, (P.initial (pair r).2).1 = g (pair r).1 := by
    intro r
    cases r with
    | zero => exact (hq 0).2
    | succ r => rw [pair_succ]; exact (hq ((pair r).2 + 1)).2
  have hstep : ∀ r, (pair r).2 < (pair (r + 1)).2 := by
    intro r
    rw [pair_succ]
    exact (Nat.lt_succ_self _).trans_le (hq ((pair r).2 + 1)).1
  let j : ℕ → ℕ := fun r => (pair r).1
  let s : ℕ → ℕ := fun r => (pair r).2
  have hsMonoAux : ∀ a b, a ≤ b → s a ≤ s b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact ih.trans (Nat.le_of_lt (hstep b))
  have hsMono : StrictMono s := by
    intro a b hab
    exact (hstep a).trans_le (hsMonoAux (a + 1) b (by omega))
  have hf : Function.Injective (fun i => (P.initial i).1) :=
    initial_vertex_injective P
  have hj : Function.Injective j := by
    intro r t hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrt | htr
    · have htimes : s r = s t := by
        apply hf
        calc
          (P.initial (s r)).1 = g (j r) := hvisit r
          _ = g (j t) := congrArg g hj
          _ = (P.initial (s t)).1 := (hvisit t).symm
      exact (ne_of_lt (hsMono hrt)) htimes
    · have htimes : s t = s r := by
        apply hf
        calc
          (P.initial (s t)).1 = g (j t) := hvisit t
          _ = g (j r) := congrArg g hj.symm
          _ = (P.initial (s r)).1 := (hvisit r).symm
      exact (ne_of_lt (hsMono htr)) htimes
  refine ⟨j, s, hj, hsMono, ?_⟩
  intro r
  exact hvisit r

end DirectedDistances.PaperProofs.Section7
