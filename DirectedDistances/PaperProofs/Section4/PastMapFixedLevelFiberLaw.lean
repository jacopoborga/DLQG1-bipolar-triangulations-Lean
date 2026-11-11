module

public import DirectedDistances.KMSW.BoltzmannEndpointFiberLaw

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3
open MeasureTheory ProbabilityTheory

private theorem map_cond_preimage {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ[| f ⁻¹' s]).map f = (μ.map f)[| s] := by
  ext t ht
  rw [Measure.map_apply hf ht, cond_apply' (hf ht) μ,
    cond_apply' ht (μ.map f), Measure.map_apply hf hs,
    Measure.map_apply hf (hs.inter ht), Set.preimage_inter]

/-- fixed level r: XDP-length fiber refinement of the stopped-map law, consuming Lemma 3.11's
on the future walk are not treated here; not the paper result. -/
theorem stoppedMap_cond_leftLength_xdpFiber_procedureReading
    (x : XDP) (ℓ r s : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (_hF : 0 < boltzmannLaw ℓ r
      (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
      (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2
      (boltzmannFiber (ℓ := ℓ) (r := r) x s)) :
    let E : Set (ℕ → Fin 3) :=
      boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹'
        {o : Option (AllBoltzmannSpace r) |
          ∃ m : BoltzmannSpace ℓ r,
            o = some (⟨ℓ, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
    (iidCodeMeasure[| E]).map (stoppedMap r hr) =
      ((boltzmannLaw ℓ r
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).1
        (boltzmannPartition_ne_zero_and_ne_top ℓ r hℓ hr).2)[|
          boltzmannFiber (ℓ := ℓ) (r := r) x s]).map
        (β := Option (AllBoltzmannSpace r))
        (fun m : BoltzmannSpace ℓ r => some (⟨ℓ, m⟩ : AllBoltzmannSpace r)) := by
  classical
  let S : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ℓ r,
      o = some (⟨ℓ, m⟩ : AllBoltzmannSpace r) ∧ xdpLen x m = s}
  let L : Set (Option (AllBoltzmannSpace r)) :=
    {o | ∃ m : BoltzmannSpace ℓ r, o = some (⟨ℓ, m⟩ : AllBoltzmannSpace r)}
  let ι : BoltzmannSpace ℓ r → Option (AllBoltzmannSpace r) :=
    fun m => some (⟨ℓ, m⟩ : AllBoltzmannSpace r)
  have hS : MeasurableSet S := trivial
  have hL : MeasurableSet L := trivial
  have hf := measurable_stoppedMap r hr
  have hι : Measurable ι := by intro t ht; trivial
  have hA : MeasurableSet (boltzmannEvent r) := by
    have heq : stoppedIndex r hr ⁻¹' {none} = (boltzmannEvent r)ᶜ := by
      ext ω
      simp [stoppedIndex]
    have hm := (measurable_stoppedIndex r hr) (measurableSet_singleton none)
    rw [heq] at hm
    exact hm.of_compl
  have hE : boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹' S =
      (boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹' L) ∩ (stoppedMap r hr) ⁻¹' S := by
    ext ω
    constructor
    · rintro ⟨hω, m, hm, hx⟩
      exact ⟨⟨hω, m, hm⟩, m, hm, hx⟩
    · rintro ⟨⟨hω, _⟩, hm⟩
      exact ⟨hω, hm⟩
  have hpre : ι ⁻¹' S = boltzmannFiber (ℓ := ℓ) (r := r) x s := by
    ext m
    change (∃ m' : BoltzmannSpace ℓ r,
      ι m = ι m' ∧ xdpLen x m' = s) ↔ xdpLen x m = s
    constructor
    · rintro ⟨m', heq, hx⟩
      have hm : m = m' :=
        eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj heq)).2
      subst m'
      exact hx
    · intro hx
      exact ⟨m, rfl, hx⟩
  have hsig : Measurable (β := AllBoltzmannSpace r) (fun m : BoltzmannSpace ℓ r =>
      (⟨ℓ, m⟩ : AllBoltzmannSpace r)) := by intro t ht; trivial
  have hsome : Measurable (some : AllBoltzmannSpace r →
      Option (AllBoltzmannSpace r)) := by intro t ht; trivial
  change (iidCodeMeasure[| boltzmannEvent r ∩ (stoppedMap r hr) ⁻¹' S]).map
    (stoppedMap r hr) = _
  rw [hE, ← cond_cond_eq_cond_inter (hA.inter (hf hL)) (hf hS) iidCodeMeasure,
    map_cond_preimage _ hf hS,
    stoppedMap_cond_leftLength_procedureReading ℓ r hℓ hr]
  erw [Measure.map_map hsome hsig]
  change ((boltzmannLaw ℓ r _ _).map ι)[| S] = _
  rw [← map_cond_preimage _ hι hS, hpre]

end DirectedDistances.PaperProofs.Section4
