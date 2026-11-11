module

public import DirectedDistances.KMSW.InfiniteBoundary
public import DirectedDistances.KMSW.LocalFinitenessUpperChain
public import DirectedDistances.KMSW.CutEquivalenceConverse
public import DirectedDistances.RandomWalk.BlockBoundUnconditional
import DirectedDistances.KMSW.StageOuterCycle
import DirectedDistances.RandomWalk.ConditionedTransience
import DirectedDistances.RandomWalk.PitmanPrefixCompatibility
import DirectedDistances.RandomWalk.SecondCoordinateUnbounded

/-! # Orbit boundary and cut-vertex helpers

The two rays of the limiting face permutation are identified with the infinite-stage
not a definition of the source random map. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk

variable (w : ℕ → Fin 3)
variable (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
  ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)

/-- Forward outer-face ray from the first left edge, with its west dart -/
@[expose] noncomputable def mapLeftBoundaryDart (d : ℕ × Bool) : Prop :=
  ∃ i : ℕ, (kmswInfFaceSucc w hfin)^[i] (kmswLeftBoundaryEdge w 0, false) = d

/-- Backward outer-face ray from the first right edge, with its east dart -/
@[expose] noncomputable def mapRightBoundaryDart (d : ℕ × Bool) : Prop :=
  ∃ i : ℕ, ((kmswInfFaceSucc w hfin).symm)^[i] (kmswRightBoundaryEdge w 0, true) = d

/-- Endpoints of edges on the left outer-face ray -/
@[expose] noncomputable def mapLeftBoundaryVertex (v : ℕ) : Prop :=
  ∃ d, mapLeftBoundaryDart w hfin d ∧ (edgeWest w d.1 = v ∨ edgeEast w d.1 = v)

/-- Endpoints of edges on the right outer-face ray -/
@[expose] noncomputable def mapRightBoundaryVertex (v : ℕ) : Prop :=
  ∃ d, mapRightBoundaryDart w hfin d ∧ (edgeWest w d.1 = v ∨ edgeEast w d.1 = v)

/-- Membership in both orbit boundaries (`def-cut-vertex`, -/
@[expose] noncomputable def mapCutVertex (v : ℕ) : Prop :=
  mapLeftBoundaryVertex w hfin v ∧ mapRightBoundaryVertex w hfin v

/-- The forward orbit follows exactly the left record chain -/
theorem mapLeftBoundary_iterate (htrans : Tendsto (L w) atTop atTop) (i : ℕ) :
    (kmswInfFaceSucc w hfin)^[i] (kmswLeftBoundaryEdge w 0, false) =
      (kmswLeftBoundaryEdge w i, false) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    exact kmswInfFaceSucc_left w hfin (stageOuterWord_faceSucc w) htrans i

/-- The backward orbit follows exactly the right record chain -/
theorem mapRightBoundary_iterate (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (i : ℕ) :
    ((kmswInfFaceSucc w hfin).symm)^[i] (kmswRightBoundaryEdge w 0, true) =
      (kmswRightBoundaryEdge w i, true) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    apply (kmswInfFaceSucc w hfin).symm_apply_eq.mpr
    exact (kmswInfFaceSucc_right w hfin (stageOuterWord_faceSucc w) hL0 hR i).symm

/-- The first right dart leads directly to the first left dart, joining the two -/
theorem mapBoundary_junction (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) :
    kmswInfFaceSucc w hfin (kmswRightBoundaryEdge w 0, true) =
      (kmswLeftBoundaryEdge w 0, false) :=
  kmswInfFaceSucc_junction w hfin (stageOuterWord_faceSucc w) hL0 htrans hR

/-- Orbit incidence agrees with infinite upper-left incidence -/
theorem mapLeftBoundaryVertex_iff (htrans : Tendsto (L w) atTop atTop) (v : ℕ) :
    mapLeftBoundaryVertex w hfin v ↔ OnLeftBoundary w v := by
  constructor
  · rintro ⟨d, ⟨i, hi⟩, hv⟩
    rw [mapLeftBoundary_iterate w hfin htrans i] at hi
    subst d
    exact ⟨_, (isLeftBoundaryEdge_iff w htrans _).mpr ⟨i, rfl⟩, hv⟩
  · rintro ⟨e, he, hv⟩
    obtain ⟨i, rfl⟩ := (isLeftBoundaryEdge_iff w htrans e).mp he
    exact ⟨(_, false), ⟨i, mapLeftBoundary_iterate w hfin htrans i⟩, hv⟩

/-- Orbit incidence agrees with infinite lower-right incidence -/
theorem mapRightBoundaryVertex_iff (hL0 : ∀ j, 0 ≤ L w j)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (v : ℕ) :
    mapRightBoundaryVertex w hfin v ↔ OnRightBoundary w v := by
  constructor
  · rintro ⟨d, ⟨i, hi⟩, hv⟩
    rw [mapRightBoundary_iterate w hfin hL0 hR i] at hi
    subst d
    exact ⟨_, (isRightBoundaryEdge_iff w hR _).mpr ⟨i, rfl⟩, hv⟩
  · rintro ⟨e, he, hv⟩
    obtain ⟨i, rfl⟩ := (isRightBoundaryEdge_iff w hR e).mp he
    exact ⟨(_, true), ⟨i, mapRightBoundary_iterate w hfin hL0 hR i⟩, hv⟩

/-- The two orbit boundaries give the bookkeeping cut predicate -/
theorem mapCutVertex_iff (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) (v : ℕ) :
    mapCutVertex w hfin v ↔ IsCutVertex w v := by
  exact and_congr (mapLeftBoundaryVertex_iff w hfin htrans v)
    (mapRightBoundaryVertex_iff w hfin hL0 hR v)

/-- First visits to vertices on both orbit rays are characterized by walk records -/
theorem mapCutVertex_first_visit_iff (htrans : Tendsto (L w) atTop atTop)
    (hR : ∀ a : ℤ, ∃ n, R w n ≤ a) (hL0 : ∀ j, 0 ≤ L w j) (n : ℕ) :
    (mapCutVertex w hfin (activeInitial w n) ∧
      ∀ j < n, activeInitial w j ≠ activeInitial w n) ↔
      ((∀ j < n, R w n ≤ R w j - 1) ∧ (∀ j, n ≤ j → L w n ≤ L w j)) := by
  rw [mapCutVertex_iff w hfin htrans hR hL0]
  exact cut_equiv_of_nonneg_of_tendsto w hL0 htrans n

private theorem measurable_vectorPitman_mapCutVertices : Measurable vectorPitman := by
  have hf : Measurable (fun z : ℕ → ℤ × ℤ => fun k => (z k).1) := by fun_prop
  apply Measurable.of_eval
  intro n
  exact (((measurable_pi_apply n).comp measurable_globalLazyPhi).comp hf).prodMk
    (((measurable_pi_apply n).snd).add ((measurable_globalLazyRunningMinimum n).comp hf))

/-- Almost surely the finite-incidence gate and the walk assumptions hold, and the
vertices on both face-orbit rays form an infinite set. Helper for the boundary/cut
introduced here. -/
theorem pitmanCodes_ae_infinite_mapCutVertices :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := pitmanCode (fun i => ω (i + 1))
      ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
          ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
        Tendsto (L w) atTop atTop ∧ (∀ a : ℤ, ∃ n, R w n ≤ a) ∧
          (∀ j, 0 ≤ L w j) ∧ {v : ℕ | mapCutVertex w hfin v}.Infinite := by
  have hmeas : Measurable (fun ω : ℕ → Fin 3 => fun k => vectorPitman (codeWalk ω) k) :=
    measurable_vectorPitman_mapCutVertices.comp measurable_codeWalk
  have hT := ae_of_ae_map hmeas.aemeasurable
    (by rw [map_vectorPitman_codeWalk]
        exact conditionedVectorPathLaw_tendsto_fst_atTop 0 0)
  filter_upwards [hT, pitmanCodes_ae_R_unbounded_below,
    pitmanCodes_ae_finite_incident_edges, pitmanCodes_ae_infinite_cutVertices]
    with ω hT hR hfin hinf
  let w := pitmanCode (fun i => ω (i + 1))
  have hPw : ∀ n, vectorPitman (codeWalk ω) n = integrateCodes w n := by
    intro n
    rw [integrateCodes_pitmanCode]
    rfl
  have htrans : Tendsto (L w) atTop atTop := by
    have heq : L w = fun j => (vectorPitman (codeWalk ω) j).1 := by
      funext j
      rw [kmsw_L_eq, hPw]
    rw [heq]
    exact hT
  have hL0 : ∀ j, 0 ≤ L w j := by
    intro j
    rw [kmsw_L_eq]
    exact integrateCodes_pitmanCode_fst_nonneg _ j
  have hR' : ∀ a : ℤ, ∃ n, R w n ≤ a := by
    intro a
    obtain ⟨n, hn⟩ := hR a
    exact ⟨n, by rw [kmsw_R_eq]; exact hn⟩
  refine ⟨hfin, htrans, hR', hL0, ?_⟩
  exact hinf.mono (fun v hv => (mapCutVertex_iff w hfin htrans hR' hL0 v).mpr hv)

end DirectedDistances.KMSW
