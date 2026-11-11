module

public import DirectedDistances.KMSW.PrimedSimCrossing
public import DirectedDistances.KMSW.PrimedSimCrossingInvariant
public import DirectedDistances.KMSW.PrimedSimCrossingEntry

/-! # Iteration of the primed complement simulation

P2 helpers toward `lem-quad-kmsw`; not counted. These finite-stage helpers
use the C13 `(0,1)` replacement and the interval code stream of
face identification, and the cut-completed object remain separate obligations. -/

public section
namespace DirectedDistances.KMSW

/-- P2 helper toward lem-quad-kmsw; not counted
crossing used by `PrimedSimActiveRootLR.crossing`, the actual primed letter
is the C13 replacement code `1`. -/
theorem PrimedSimActiveRootLR.crossing_primedCode
    {w : ℕ → Fin 3} {h : HasFlowLineHits w} {k m : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR (primedCode (primedSimInput w) h)
      w h k m (walkNR w h (k + 1) - 1) eφ vφ) :
    primedCode (primedSimInput w) h m = 1 := by
  rw [sim.forget.crossing_time.1]
  exact (primedCrossing_codes w h k).1

/-- P2 helper toward lem-quad-kmsw; not counted
after a replacement crossing, run all ordinary steps of its block to the
next crossing, carrying the unreachable-or-cut invariant. The block index
is arbitrary, so this applies in particular to the entry at `k + 1`. -/
theorem primedSimActiveRootLR_ordinary_run_to_crossing
    {w : ℕ → Fin 3} {h : HasFlowLineHits w} {k : ℕ} {eφ vφ : ℕ → ℕ}
    (sim : PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k
      (primedIntervalBase (primedSimInput w) h k + 1) (walkNL w h k) eφ vφ)
    (hinv : PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k
      (primedIntervalBase (primedSimInput w) h k + 1) eφ vφ) :
    ∃ eψ vψ,
      PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k
        (primedIntervalBase (primedSimInput w) h (k + 1))
        (walkNR w h (k + 1) - 1) eψ vψ ∧
      PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k
        (primedIntervalBase (primedSimInput w) h (k + 1)) eψ vψ := by
  let B := primedIntervalBase (primedSimInput w) h k
  let W := primedIntervalWidth (primedSimInput w) h k
  have hrun : ∀ d : ℕ, 1 + d ≤ W → ∃ eψ vψ,
      PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k
        (B + 1 + d) (walkNL w h k + d) eψ vψ ∧
      PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k
        (B + 1 + d) eψ vψ := by
    intro d
    induction d with
    | zero =>
        intro _
        exact ⟨eφ, vφ, sim, hinv⟩
    | succ d ih =>
        intro hd
        obtain ⟨eψ, vψ, hs, hi⟩ := ih (by omega)
        have hm : B + 1 + d <
            primedIntervalBase (primedSimInput w) h k +
              primedIntervalWidth (primedSimInput w) h k := by
          change B + 1 + d < B + W
          omega
        have hu : primedCode (primedSimInput w) h (B + 1 + d) =
            w (walkNL w h k + d) := by
          have hc := primedCode_positive_offset (primedSimInput w) h k (1 + d)
            (by omega) (show 1 + d < W by omega)
          have hm' : B + (1 + d) = B + 1 + d := by omega
          have hn' : primedIntervalLeft (primedSimInput w) h k + (1 + d) - 1 =
              walkNL w h k + d := by
            change walkNL w h k + (1 + d) - 1 = walkNL w h k + d
            omega
          simpa only [← hm', hn'] using hc
        obtain ⟨eχ, vχ, _, _, hs', hi'⟩ :=
          primedSimActiveRootLR_ordinary_step_unreachableOrCut hs hm hi
            (w (walkNL w h k + d)) hu rfl
        exact ⟨eχ, vχ, hs', hi'⟩
  have hW := primedIntervalWidth_pos (primedSimInput w) h k
  obtain ⟨eψ, vψ, hs, hi⟩ := hrun (W - 1) (by dsimp [W]; omega)
  have hbase : B + 1 + (W - 1) =
      primedIntervalBase (primedSimInput w) h (k + 1) := by
    rw [primedIntervalBase_succ]
    change B + 1 + (W - 1) = B + W
    change 1 ≤ W at hW
    omega
  have htime : walkNL w h k + (W - 1) = walkNR w h (k + 1) - 1 := by
    have hgap := (walkNR_succ_spec w h k).1
    change walkNL w h k +
      ((walkNR w h (k + 1) - walkNL w h k) - 1) = _
    omega
  exact ⟨eψ, vψ, hbase ▸ htime ▸ hs, hbase ▸ hi⟩

/-- P2 helper toward lem-quad-kmsw; not counted
kept global stage, the C13 primed code admits the active root-LR simulation
and its unreachable-or-cut invariant. The base uses the proved initial
replacement-triangle simulation with the actual first primed code; the
induction alternates compressed crossings and ordinary runs. This does not
identify ordered boundaries, planar faces, or the cut-completed object. -/
theorem primedSimActiveRootLR_at_crossing
    (w : ℕ → Fin 3) (h : HasFlowLineHits w) (k : ℕ) :
    ∃ eφ vφ,
      PrimedSimActiveRootLR (primedCode (primedSimInput w) h) w h k
        (primedIntervalBase (primedSimInput w) h (k + 1))
        (walkNR w h (k + 1) - 1) eφ vφ ∧
      PrimedURUnreachableOrCut (primedCode (primedSimInput w) h) w h k
        (primedIntervalBase (primedSimInput w) h (k + 1)) eφ vφ := by
  induction k with
  | zero =>
      have hu := (primedInitial_code_alignment (primedSimInput w) h).1
      have hs := primedFirstStep_simActiveRootLR
        (primedCode (primedSimInput w) h) w h hu
      have hi := primedFirstStep_URUnreachableOrCut
        (primedCode (primedSimInput w) h) w h hu
      rw [← primedIntervalBase_zero (primedSimInput w) h] at hs hi
      exact primedSimActiveRootLR_ordinary_run_to_crossing hs hi
  | succ k ih =>
      obtain ⟨eφ, vφ, hs, hi⟩ := ih
      have hu := hs.crossing_primedCode
      have hs' := hs.crossing hi hu
      have hi' := primedURUnreachableOrCut_crossing hi hu
      exact primedSimActiveRootLR_ordinary_run_to_crossing hs' hi'

end DirectedDistances.KMSW
