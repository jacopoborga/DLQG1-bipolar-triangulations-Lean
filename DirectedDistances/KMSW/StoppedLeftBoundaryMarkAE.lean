module

public import DirectedDistances.KMSW.StoppedLeftBoundaryMark
public import DirectedDistances.KMSW.MapCutVertices
public import DirectedDistances.RandomWalk.ConditionedStrongMarkov
public import DirectedDistances.PaperProofs.Section4.PastMapPathDecoding
public import DirectedDistances.PaperProofs.Section3.BoltzmannMarks
import DirectedDistances.KMSW.PathSpaceTransfer
import DirectedDistances.KMSW.PathSpaceTransferCarrier
import DirectedDistances.PaperProofs.Section4.PastMapFirstHitKernelAS

/-! Supporting lemmas for paper labels `lem-uiqbot-boltzmann` (see CORRESPONDENCE.md). -/

/-! # Almost-sure stopped left-boundary mark helpers

The deterministic stopped-stage criterion is transported to the actual face-orbit
boundary, and instantiated on the conditioned path law. -/

public section
namespace DirectedDistances.KMSW

open Filter MeasureTheory
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section4
open DirectedDistances.PaperProofs.Section3

private theorem stoppedPathCode_integrates (p : ℕ → ℤ × ℤ)
    (hzero : p 0 = (0, 0))
    (hlegal : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    integrateCodes (boltzmannKMSWStream (pathCode p)) = p := by
  funext n
  change integrateCodes (fun i => pathCode p (i + 1)) n = p n
  rw [← codeWalk_eq_integrateCodes (pathCode p) n]
  rw [codeWalk_pathCode p hlegal n, hzero]
  simp

private theorem stoppedFirstHit_data (r : ℕ) (hr : 1 ≤ r)
    (p : ℕ → ℤ × ℤ)
    (hfinite : conditionedSecondCoordinateFirstHit r p < ⊤)
    (hzero : p 0 = (0, 0)) :
    let t := (conditionedSecondCoordinateFirstHit r p).toNat
    0 < t ∧ (p t).2 = -(r : ℤ) ∧
      ∀ s < t, (p s).2 ≠ -(r : ℤ) := by
  classical
  let P : ℕ → Prop := fun n => (p n).2 = -(r : ℤ)
  have hhit : ∃ n, P n := by
    by_contra hnone
    have htop : conditionedSecondCoordinateFirstHit r p = ⊤ := by
      simp [conditionedSecondCoordinateFirstHit, P, hnone]
    rw [htop] at hfinite
    exact (lt_irrefl _ hfinite).elim
  have hτ : conditionedSecondCoordinateFirstHit r p =
      (Nat.find hhit : ℕ∞) := by
    simp [conditionedSecondCoordinateFirstHit, P, hhit]
  have ht : (conditionedSecondCoordinateFirstHit r p).toNat = Nat.find hhit := by
    rw [hτ]
    rfl
  have hfind : P (Nat.find hhit) ∧
      ∀ n < Nat.find hhit, ¬P n :=
    (Nat.find_eq_iff hhit).mp (rfl : Nat.find hhit = Nat.find hhit)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [ht]
    have hstart : (p 0).2 = 0 := congrArg Prod.snd hzero
    have hnot0 : ¬P 0 := by
      dsimp [P]
      rw [hzero]
      norm_num
      omega
    have hne : (Nat.find hhit) ≠ 0 := by
      intro heq
      rw [heq] at hfind
      exact hnot0 hfind.1
    omega
  · rw [ht]
    exact hfind.1
  · intro s hs hbad
    rw [ht] at hs
    exact hfind.2 s hs hbad

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
Orbit-boundary version of the stopped left-boundary criterion. -/
theorem stoppedLeftBoundaryVertices_mapLeftBoundary_iff
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    {r t j : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s)
    (htrans : Tendsto (L w) atTop atTop)
    (hj : j < (L w t).toNat + 1) :
    mapLeftBoundaryVertex w hfin
        ((stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0)) ↔
      ∀ s, t ≤ s → (j : ℤ) ≤ L w s := by
  rw [mapLeftBoundaryVertex_iff w hfin htrans]
  exact stoppedLeftBoundaryVertices_onLeftBoundary_iff w hr ht hhit hfirst
    hL0 htrans hj

/-- Helper toward lem-uiqbot-boltzmann / Lemma 7.9
The shared indices on the face-orbit boundary end at the post-hit minimum. -/
theorem stoppedLeftBoundaryVertices_shared_indices_mapLeftBoundary
    (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    {r t : ℕ} (hr : 1 ≤ r) (ht : 0 < t)
    (hhit : R w t = -(r : ℤ))
    (hfirst : ∀ s < t, R w s ≠ -(r : ℤ))
    (hL0 : ∀ s, 0 ≤ L w s)
    (htrans : Tendsto (L w) atTop atTop) :
    ∃ m ≤ (L w t).toNat,
      (∃ u, t ≤ u ∧ L w u = (m : ℤ)) ∧
      (∀ s, t ≤ s → (m : ℤ) ≤ L w s) ∧
      ∀ j, j ≤ (L w t).toNat →
        (mapLeftBoundaryVertex w hfin
          ((stoppedLeftBoundaryVertices w t).getD j (activeInitial w 0)) ↔
            j ≤ m) := by
  obtain ⟨m, hm, hu, hmin, hshared⟩ :=
    stoppedLeftBoundaryVertices_shared_indices w hr ht hhit hfirst hL0 htrans
  refine ⟨m, hm, hu, hmin, ?_⟩
  intro j hj
  rw [mapLeftBoundaryVertex_iff w hfin htrans]
  exact hshared j hj







theorem stoppedLeftBoundaryVertices_shared_indices_ae :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      integrateCodes (boltzmannKMSWStream (pathCode p)) = p ∧
      (∀ s, L (boltzmannKMSWStream (pathCode p)) s = (p s).1) ∧
      ∃ hfin : ∀ v, {e : ℕ | ∃ n,
        e < (kmswStage (boltzmannKMSWStream (pathCode p)) n).nextEdge ∧
          ((kmswStage (boltzmannKMSWStream (pathCode p)) n).west e = v ∨
            (kmswStage (boltzmannKMSWStream (pathCode p)) n).east e = v)}.Finite,
        ∀ r, 1 ≤ r →
          let t := (conditionedSecondCoordinateFirstHit r p).toNat
          0 < t ∧
            ∃ m ≤ (L (boltzmannKMSWStream (pathCode p)) t).toNat,
              (∃ u, t ≤ u ∧
                L (boltzmannKMSWStream (pathCode p)) u = (m : ℤ)) ∧
              (∀ s, t ≤ s →
                (m : ℤ) ≤ L (boltzmannKMSWStream (pathCode p)) s) ∧
              ∀ j, j ≤ (L (boltzmannKMSWStream (pathCode p)) t).toNat →
                (mapLeftBoundaryVertex (boltzmannKMSWStream (pathCode p)) hfin
                  ((stoppedLeftBoundaryVertices
                    (boltzmannKMSWStream (pathCode p)) t).getD j
                      (activeInitial (boltzmannKMSWStream (pathCode p)) 0)) ↔
                        j ≤ m) := by
  classical
  have hfiniteAll : ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      ∀ r, 1 ≤ r → conditionedSecondCoordinateFirstHit r p < ⊤ := by
    rw [ae_all_iff]
    intro r
    by_cases hr : 1 ≤ r
    · filter_upwards [firstHitPastMap_finite_hit_ae r hr] with p hhit
      intro _
      exact hhit
    · exact Filter.Eventually.of_forall fun p h => (hr h).elim
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit,
    conditionedVectorPathLaw_ae_legal, hfiniteAll] with p hcarrier hpath
      hlegal hfinite
  obtain ⟨w, hw, _⟩ := hcarrier
  rcases hw with ⟨hwcode, _, _, htail⟩
  obtain ⟨hfin, _⟩ := htail
  obtain ⟨u, hup, _, htrans, _, hL0, _, _⟩ := hpath
  have hcode : integrateCodes (boltzmannKMSWStream (pathCode p)) = p :=
    stoppedPathCode_integrates p hlegal.1 hlegal.2
  have hwu : w = boltzmannKMSWStream (pathCode p) :=
    integrateCodes_injective (hwcode.trans hcode.symm)
  have huu : u = boltzmannKMSWStream (pathCode p) :=
    integrateCodes_injective (hup.trans hcode.symm)
  subst w
  subst u
  have hLpath : ∀ s, L (boltzmannKMSWStream (pathCode p)) s = (p s).1 := by
    intro s
    rw [kmsw_L_eq, hcode]
  have htrans' : Tendsto (L (boltzmannKMSWStream (pathCode p))) atTop atTop := by
    simpa only [kmsw_L_eq, hcode] using htrans
  have hL0' : ∀ s, 0 ≤ L (boltzmannKMSWStream (pathCode p)) s := by
    intro s
    simpa only [kmsw_L_eq, hcode] using hL0 s
  refine ⟨hcode, hLpath, hfin, ?_⟩
  intro r hr
  let t := (conditionedSecondCoordinateFirstHit r p).toNat
  obtain ⟨ht, hphit, hpfirst⟩ :=
    stoppedFirstHit_data r hr p (hfinite r hr) hlegal.1
  have hhit : R (boltzmannKMSWStream (pathCode p)) t = -(r : ℤ) := by
    rw [kmsw_R_eq, hcode]
    exact hphit
  have hfirst : ∀ s < t,
      R (boltzmannKMSWStream (pathCode p)) s ≠ -(r : ℤ) := by
    intro s hs
    rw [kmsw_R_eq, hcode]
    exact hpfirst s hs
  refine ⟨ht, ?_⟩
  simpa only [t] using stoppedLeftBoundaryVertices_shared_indices_mapLeftBoundary
    (boltzmannKMSWStream (pathCode p)) hfin hr ht hhit hfirst hL0' htrans'

end DirectedDistances.KMSW
