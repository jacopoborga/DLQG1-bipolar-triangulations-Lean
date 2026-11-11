module

public import DirectedDistances.KMSW.KMSWWindowBallCapture

public import DirectedDistances.KMSW.StageFrontier

import DirectedDistances.KMSW.WholePlaneFreshness

/-! Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.

is that predicate
transport on edges with both endpoints in a set does not constrain edges leaving
that set. The second is that freshness depends on the prefix: a window allocation
can instead consume an existing upper-right edge in the global run. -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Counterexample to the stage-dependent-predicate statement deriving global ball
containment from two-endpoint predicate transport and window ball closure.
The window has three vertices and no admissible edges; the global stage has four vertices and all
edges admissible. -/
theorem kmswWindowClosedBall_not_capture_example :
    let w : ℕ → Fin 3 := fun _ => 1
    let P : KMSWStageEdgePredicate := fun t _ => t.nextVertex = 4
    let S : Finset ℕ := {2}
    (∀ v ∈ S,
      v < (kmswStage (fun i => w (1 + i)) 1).nextVertex ∧
        (kmswStage w 1).nextVertex ≤ kmswWindowPatchVertexMap w 1 1 v) ∧
    kmswWindowEdgePredicateTransport P w 1 1 S ∧
    (∀ x, kmswStageDistanceLe P (kmswStage (fun i => w (1 + i)) 1) 1 2 x →
      x ∈ (S : Set ℕ)) ∧
    (∃ x, kmswStageDistanceLe P (kmswStage w (1 + 1)) 1
        (kmswWindowPatchVertexMap w 1 1 2) x ∧
      x ∉ Set.image (kmswWindowPatchVertexMap w 1 1) (S : Set ℕ)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv2 : v = 2 := Finset.mem_singleton.mp hv
    subst v
    decide
  · unfold kmswWindowEdgePredicateTransport
    decide
  · intro x hx
    obtain ⟨k, _, hp⟩ := hx
    cases hp with
    | nil => exact Finset.mem_singleton_self 2
    | snoc hpre hy hz hadj =>
        obtain ⟨d, hd, _, _⟩ := hadj
        change 3 = 4 at hd
        contradiction
  · refine ⟨0, ?_, ?_⟩
    · refine ⟨1, le_rfl, ?_⟩
      refine .snoc (.nil (Set.mem_univ _)) (Set.mem_univ _) (Set.mem_univ _) ?_
      exact ⟨(⟨3, by decide⟩, true), by decide, by decide, by decide⟩
    · rintro ⟨v, hv, heq⟩
      have hv2 : v = 2 := Finset.mem_singleton.mp hv
      subst v
      change 3 = 0 at heq
      contradiction

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
no Definition 3.8 reading adopted; not the paper result.
Counterexample to a naive iff making freshness a function of the suffix:
identical entire suffixes can give opposite freshness outcomes. After a left
prefix the down step allocates a global vertex; after an up prefix it consumes
an existing upper-right edge and maps the same window vertex to an old vertex. -/
theorem kmswWindowFreshness_not_suffix_determined_example :
    let w₀ : ℕ → Fin 3 := fun i => if i = 0 then 0 else 2
    let w₁ : ℕ → Fin 3 := fun i => if i = 0 then 1 else 2
    (∀ i, w₀ (1 + i) = w₁ (1 + i)) ∧
    2 < (kmswStage (fun i => w₀ (1 + i)) 1).nextVertex ∧
    (kmswStage w₀ 1).nextVertex ≤ kmswWindowPatchVertexMap w₀ 1 1 2 ∧
    kmswWindowPatchVertexMap w₁ 1 1 2 < (kmswStage w₁ 1).nextVertex := by
  dsimp only
  refine ⟨?_, by decide, by decide, by decide⟩
  intro i
  have hi : 1 + i ≠ 0 := by omega
  simp only [hi, ↓reduceIte]


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
for ball capture; no Definition 3.8 reading adopted; not the paper result.
The finite-window non-seam condition excludes record allocations and the two
initial vertices. It guarantees freshness for every prefix and every continuation
whose first `m` window letters agree with `u`. -/
theorem kmswWindowPatchVertexMap_fresh_for_every_prefix
    (u : ℕ → Fin 3) (m v : ℕ)
    (hv : v < (kmswStage u m).nextVertex) (hbase : 2 ≤ v)
    (hnonseam : ∀ k < m, v = (kmswStage u k).nextVertex →
      (kmswCodeStep (u k) = .down → (kmswStage u k).UR ≠ []) ∧
      (kmswCodeStep (u k) = .left →
        (kmswStage u k).UL.dropLast.reverse ≠ [])) :
    ∀ (w : ℕ → Fin 3) (s : ℕ), (∀ i < m, w (s + i) = u i) →
      (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
  intro w s hcode
  have hstage (k : ℕ) (hk : k ≤ m) :
      kmswStage (fun i => w (s + i)) k = kmswStage u k := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change kmswStep (kmswStage (fun i => w (s + i)) k) (w (s + k)) =
          kmswStep (kmswStage u k) (u k)
        rw [ih (by omega), hcode k (by omega)]
  have hv' : v < (kmswStage (fun i => w (s + i)) m).nextVertex := by
    rw [hstage m le_rfl]
    exact hv
  by_contra hfresh
  have hseam := (kmswWindowPatchVertexMap_lt_start_iff_seam w s m v hv').mp
    (Nat.lt_of_not_ge hfresh)
  rcases hseam with hsmall | ⟨k, hk, hcreate, hdown | hleft⟩
  · omega
  · rw [hstage k (by omega)] at hcreate hdown
    rw [hcode k hk] at hdown
    exact ((hnonseam k hk hcreate).1 hdown.1) hdown.2.1
  · rw [hstage k (by omega)] at hcreate hleft
    rw [hcode k hk] at hleft
    exact ((hnonseam k hk hcreate).2 hleft.1) hleft.2.1

private theorem windowBallCapture_of_starTransport
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (s m : ℕ)
    (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : ∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S →
      (P (kmswStage (fun i => w (s + i)) m) d.1 ↔
        P (kmswStage w (s + m)) (kmswWindowDartMap w s m d).1))
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ)) :
    ∀ x, kmswStageDistanceLe P (kmswStage w (s + m)) r
      (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S := by
  have hc : c ∈ S := hClosed c ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hlift {k x : ℕ}
      (hp : KMSWStagePath P (kmswStage w (s + m)) Set.univ
        (kmswWindowPatchVertexMap w s m c) k x) (hk : k ≤ r) :
      ∃ v, v ∈ S ∧ kmswWindowPatchVertexMap w s m v = x ∧
        KMSWStagePath P (kmswStage (fun i => w (s + i)) m)
          (S : Set ℕ) c k v := by
    induction hp with
    | nil _ => exact ⟨c, hc, rfl, .nil hc⟩
    | @snoc n y z hpre _ _ hadj ih =>
        obtain ⟨u, hu, huy, hpreF⟩ := ih (by omega)
        obtain ⟨dG, hpredG, hstartG, hendG⟩ := hadj
        have hstartFin : stageEndpoint (kmswStage w (s + m)) dG ∈
            S.image (kmswWindowPatchVertexMap w s m) := by
          rw [hstartG, ← huy]
          exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
        obtain ⟨dF, hdF, hmap⟩ :=
          (kmswWindowFreshSetDartCapture w s m S hS).2.2.1 dG hstartFin
        let a := stageEndpoint (kmswStage (fun i => w (s + i)) m) dF
        let b := stageEndpoint (kmswStage (fun i => w (s + i)) m) (edgeFlip _ dF)
        have ha : kmswWindowPatchVertexMap w s m a = y := by
          calc
            _ = stageEndpoint (kmswStage w (s + m))
                (kmswWindowDartMap w s m dF) :=
              ((kmswWindowFreshSetDartCapture w s m S hS).2.2.2 dF).symm
            _ = y := by rw [hmap]; exact hstartG
        have hb : kmswWindowPatchVertexMap w s m b = z := by
          calc
            _ = stageEndpoint (kmswStage w (s + m))
                (kmswWindowDartMap w s m (edgeFlip _ dF)) :=
              ((kmswWindowFreshSetDartCapture w s m S hS).2.2.2
                (edgeFlip _ dF)).symm
            _ = z := by rw [kmswWindowFreshSetEdgeFlipCapture, hmap]; exact hendG
        have hau : a = u := kmswWindowPatchVertexMap_injOn w s m
          (hS a hdF).1 (hS u hu).1 (ha.trans huy.symm)
        have hpredF : P (kmswStage (fun i => w (s + i)) m) dF.1 := by
          apply (hP dF hdF).mpr
          rw [hmap]
          exact hpredG
        have hadjF : kmswStageAdjacent P
            (kmswStage (fun i => w (s + i)) m) u b :=
          ⟨dF, hpredF, hau, rfl⟩
        have hfull : KMSWStagePath P (kmswStage (fun i => w (s + i)) m)
            Set.univ c (n + 1) b :=
          .snoc (kmswStagePathForgetVertices P _ _ hpreF)
            (Set.mem_univ _) (Set.mem_univ _) hadjF
        have hbS : b ∈ S := hClosed b ⟨n + 1, hk, hfull⟩
        exact ⟨b, hbS, hb, .snoc hpreF hu hbS hadjF⟩
  intro x hx
  obtain ⟨k, hk, hp⟩ := hx
  obtain ⟨v, hv, hvx, _⟩ := hlift hp hk
  exact ⟨v, hv, hvx⟩

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
for ball capture; no Definition 3.8 reading adopted; not the paper result.
For all geometric edges, freshness and window-ball closure imply the global
ball containment hypothesis, with a parametric centre. -/
theorem kmswWindowAllEdgesBallCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hClosed : ∀ x,
      kmswStageDistanceLe (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c x → x ∈ (S : Set ℕ)) :
    ∀ x, kmswStageDistanceLe (fun _ _ => True) (kmswStage w (s + m)) r
      (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S := by
  apply windowBallCapture_of_starTransport (fun _ _ => True) w s m S r c hS
  · intro d hd
    exact Iff.rfl
  · exact hClosed

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
for ball capture; no Definition 3.8 reading adopted; not the paper result.
For present edges, one fresh endpoint suffices to transport admissibility,
so freshness and window-ball closure imply the global ball containment. -/
theorem kmswWindowPresentEdgesBallCapture
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hClosed : ∀ x,
      kmswStageDistanceLe (fun t e => t.present e.val = true)
        (kmswStage (fun i => w (s + i)) m) r c x → x ∈ (S : Set ℕ)) :
    ∀ x, kmswStageDistanceLe (fun t e => t.present e.val = true)
      (kmswStage w (s + m)) r (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S := by
  apply windowBallCapture_of_starTransport
    (fun t e => t.present e.val = true) w s m S r c hS
  · intro d hd
    have hp := kmswWindowFreshSetPresentCapture w s m S hS d hd
    change (kmswStage (fun i => w (s + i)) m).present d.1.val = true ↔
      (kmswStage w (s + m)).present (kmswWindowDartMap w s m d).1.val = true
    rw [hp]
  · exact hClosed

private theorem capture_step_no_new_incidence (s : State) (c : Fin 3) (v : ℕ)
    (hW : s.west s.active ≠ v)
    (hW' : (kmswStep s c).west (kmswStep s c).active ≠ v)
    (hE : s.east s.active ≠ v) (hV : s.nextVertex ≠ v)
    {e : ℕ} (he : s.nextEdge ≤ e) (he' : e < (kmswStep s c).nextEdge) :
    (kmswStep s c).west e ≠ v ∧ (kmswStep s c).east e ≠ v := by
  unfold kmswStep at *
  cases hc : kmswCodeStep c with
  | down =>
    cases hs : s.UR with
    | nil =>
      have heq : e = s.nextEdge := by
        simp only [hc, kmswStepOfStep, hs, State.addEdge] at he'
        omega
      subst e
      simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hE hV
    | cons f fs =>
      simp only [hc, kmswStepOfStep, hs] at he'
      omega
  | left =>
    cases hs : s.UL.dropLast.reverse with
    | nil =>
      have hbound : e < s.nextEdge + 2 := by
        simpa [hc, kmswStepOfStep, hs, State.addEdge, Nat.add_assoc] using he'
      have heq : e = s.nextEdge ∨ e = s.nextEdge + 1 := by omega
      rcases heq with rfl | rfl
      · simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hV hE
      · simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hV hW
    | cons f fs =>
      have heq : e = s.nextEdge := by
        simp only [hc, kmswStepOfStep, hs, State.addEdge] at he'
        omega
      subst e
      have hF : s.west f ≠ v := by
        simpa [hc, kmswStepOfStep, hs, State.addEdge] using hW'
      simpa [hc, kmswStepOfStep, hs, State.addEdge] using And.intro hF hE
  | up =>
    have hbound : e < s.nextEdge + 2 := by
      simpa [hc, kmswStepOfStep, State.addEdge, Nat.add_assoc] using he'
    have heq : e = s.nextEdge ∨ e = s.nextEdge + 1 := by omega
    rcases heq with rfl | rfl
    · simpa [hc, kmswStepOfStep, State.addEdge] using And.intro hW hV
    · simpa [hc, kmswStepOfStep, State.addEdge] using And.intro hV hE


/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
for ball capture; no Definition 3.8 reading adopted; not the paper result.
A vertex outside the upper frontier of stage `t` receives no new incident
geometric edge at any later stage. Missing geometric edges are included. -/
theorem kmswStage_no_new_incidence_of_not_upperFrontier
    (w : ℕ → Fin 3) (t v : ℕ)
    (hv : ¬ UpperFrontierEndpoint (kmswStage w t) v)
    (n : ℕ) (htn : t ≤ n) (e : ℕ)
    (he : e < (kmswStage w n).nextEdge)
    (hnew : (kmswStage w t).nextEdge ≤ e) :
    (kmswStage w n).west e ≠ v ∧ (kmswStage w n).east e ≠ v := by
  have hactive (j : ℕ) (htj : t ≤ j) :
      (kmswStage w j).west (kmswStage w j).active ≠ v ∧
        (kmswStage w j).east (kmswStage w j).active ≠ v := by
    obtain ⟨xs, hxs⟩ := kmswStage_UL_last w j
    have hmem : (kmswStage w j).active ∈
        (kmswStage w j).UL ++ (kmswStage w j).UR := by
      rw [hxs]
      simp
    have hf := kmswStage_upperFrontier_endpoints w t j htj _ hmem
    exact ⟨fun h => hv (h ▸ hf.1), fun h => hv (h ▸ hf.2)⟩
  have hvbound : v < (kmswStage w t).nextVertex := by
    by_contra h
    exact hv (Or.inr (Nat.le_of_not_gt h))
  induction n, htn using Nat.le_induction with
  | base => omega
  | succ n htn ih =>
      by_cases hold : e < (kmswStage w n).nextEdge
      · have hs := kmswStage_endpoints_stable w (Nat.le_succ n) hold
        rw [hs.1, hs.2]
        exact ih hold
      · have hW := hactive n htn
        have hW' := hactive (n + 1) (by omega)
        have hmono := CutConverse.nextVertex_mono w htn
        exact capture_step_no_new_incidence (kmswStage w n) (w n) v
          hW.1 hW'.1 hW.2 (by omega) (Nat.le_of_not_gt hold) he

private theorem capture_adjacent_mono (w : ℕ → Fin 3) {t n x y : ℕ}
    (htn : t ≤ n)
    (h : kmswStageAdjacent (fun _ _ => True) (kmswStage w t) x y) :
    kmswStageAdjacent (fun _ _ => True) (kmswStage w n) x y := by
  obtain ⟨⟨e, b⟩, _, hx, hy⟩ := h
  let e' : Fin (kmswStage w n).nextEdge :=
    ⟨e.val, e.isLt.trans_le (kmswStage_nextEdge_mono w htn)⟩
  have hs := kmswStage_endpoints_stable w htn e.isLt
  refine ⟨(e', b), trivial, ?_, ?_⟩
  · cases b <;> simpa [stageEndpoint, e', hs.1, hs.2] using hx
  · cases b <;> simpa [stageEndpoint, edgeFlip, e', hs.1, hs.2] using hy

private theorem capture_path_mono (w : ℕ → Fin 3) {t n k c x : ℕ}
    (htn : t ≤ n)
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage w t) Set.univ c k x) :
    KMSWStagePath (fun _ _ => True) (kmswStage w n) Set.univ c k x := by
  induction hp with
  | nil _ => exact .nil (Set.mem_univ _)
  | snoc _ _ _ hadj ih =>
      exact .snoc ih (Set.mem_univ _) (Set.mem_univ _)
        (capture_adjacent_mono w htn hadj)

private theorem capture_future_distance_iff (w : ℕ → Fin 3) (t n r c : ℕ)
    (htn : t ≤ n)
    (hfront : ∀ x, kmswStageDistanceLe (fun _ _ => True)
      (kmswStage w t) (r - 1) c x → ¬ UpperFrontierEndpoint (kmswStage w t) x)
    (x : ℕ) :
    kmswStageDistanceLe (fun _ _ => True) (kmswStage w n) r c x ↔
      kmswStageDistanceLe (fun _ _ => True) (kmswStage w t) r c x := by
  constructor
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, hk, ?_⟩
    induction hp with
    | nil _ => exact .nil (Set.mem_univ _)
    | @snoc j y z hpre _ _ hadj ih =>
        have hpreT := ih (by omega)
        have hyfront := hfront y ⟨j, by omega, hpreT⟩
        obtain ⟨⟨e, b⟩, _, hx, hz⟩ := hadj
        have he : e.val < (kmswStage w t).nextEdge := by
          by_contra h
          have hnew := kmswStage_no_new_incidence_of_not_upperFrontier
            w t y hyfront n htn e.val e.isLt (Nat.le_of_not_gt h)
          cases b
          · exact hnew.1 hx
          · exact hnew.2 hx
        let e' : Fin (kmswStage w t).nextEdge := ⟨e.val, he⟩
        have hs := kmswStage_endpoints_stable w htn he
        have hx' : stageEndpoint (kmswStage w t) (e', b) = y := by
          cases b <;> simpa [stageEndpoint, e', hs.1, hs.2] using hx
        have hz' : stageEndpoint (kmswStage w t) (edgeFlip _ (e', b)) = z := by
          cases b <;> simpa [stageEndpoint, edgeFlip, e', hs.1, hs.2] using hz
        exact .snoc hpreT (Set.mem_univ _) (Set.mem_univ _)
          ⟨(e', b), trivial, hx', hz'⟩
  · rintro ⟨k, hk, hp⟩
    exact ⟨k, hk, capture_path_mono w htn hp⟩

private theorem capture_path_endpoint_bound (w : ℕ → Fin 3) (t : ℕ)
    {k c x : ℕ} (hc : c < (kmswStage w t).nextVertex)
    (hp : KMSWStagePath (fun _ _ => True) (kmswStage w t) Set.univ c k x) :
    x < (kmswStage w t).nextVertex := by
  cases hp with
  | nil _ => exact hc
  | snoc _ _ _ hadj =>
      obtain ⟨d, _, _, hend⟩ := hadj
      rw [← hend]
      exact stageEndpoint_lt_nextVertex w t (edgeFlip _ d)

/-- Helper toward Proposition 5.16 (prop-disk-bs-conv,
with window-determined freshness conditions; no Definition 3.8 reading adopted;
not the paper result. The explicit `hfront` premise is not itself window-determined.
It is discharged in `KMSWWindowEventCapture.lean` by
`kmswWindowPatchVertexMap_not_upperFrontier_for_every_prefix`.
For all geometric edges, capture persists at every later stage if the image
of the window radius-`r - 1` ball avoids the upper frontier at the window's end.
The centre remains parametric, and `r = 0` is included. -/
theorem kmswWindowAllEdgesBallVerticesImageEq_future
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hClosed : ∀ x,
      kmswStageDistanceLe (fun _ _ => True)
        (kmswStage (fun i => w (s + i)) m) r c x → x ∈ (S : Set ℕ))
    (hfront : ∀ v, kmswStageDistanceLe (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) (r - 1) c v →
      ¬ UpperFrontierEndpoint (kmswStage w (s + m))
        (kmswWindowPatchVertexMap w s m v))
    (n : ℕ) (hn : s + m ≤ n) :
    (kmswStageBallVertices (fun _ _ => True)
      (kmswStage (fun i => w (s + i)) m) r c).image
        (kmswWindowPatchVertexMap w s m) =
      kmswStageBallVertices (fun _ _ => True) (kmswStage w n) r
        (kmswWindowPatchVertexMap w s m c) := by
  classical
  have hc : c ∈ S := hClosed c ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
  have hBall := kmswWindowAllEdgesBallCapture w s m S r c hS hClosed
  have hP := kmswWindowAllEdgesTransport w s m S
  have hImage := kmswWindowBallVerticesImageEq (fun _ _ => True)
    w s m S r c hS hP hBall hClosed hc
  have hfrontG : ∀ x, kmswStageDistanceLe (fun _ _ => True)
      (kmswStage w (s + m)) (r - 1) (kmswWindowPatchVertexMap w s m c) x →
      ¬ UpperFrontierEndpoint (kmswStage w (s + m)) x := by
    intro x hx
    obtain ⟨k, hk, hp⟩ := hx
    obtain ⟨v, _, hvx, hpF⟩ := kmswWindowPathLift (fun _ _ => True)
      w s m S r c hS hP hBall hc (by omega) hp
    rw [← hvx]
    exact hfront v ⟨k, hk, kmswStagePathForgetVertices _ _ _ hpF⟩
  rw [hImage]
  apply Finset.ext
  intro x
  have hdist := capture_future_distance_iff w (s + m) n r
    (kmswWindowPatchVertexMap w s m c) hn hfrontG x
  constructor
  · intro hx
    obtain ⟨hxrange, hxDist⟩ := Finset.mem_filter.mp hx
    have hxb := (Finset.mem_range.mp hxrange).trans_le
      (CutConverse.nextVertex_mono w hn)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxb, hdist.mpr hxDist⟩
  · intro hx
    have hxDist := hdist.mp (Finset.mem_filter.mp hx).2
    have hcBound := (kmswWindowPatchVertexMap_rel w s m).vertex_bound c (hS c hc).1
    obtain ⟨k, hk, hp⟩ := hxDist
    have hxBound := capture_path_endpoint_bound w (s + m) hcBound hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxBound, k, hk, hp⟩

end DirectedDistances.KMSW
