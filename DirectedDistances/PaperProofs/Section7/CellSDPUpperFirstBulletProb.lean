module

public import DirectedDistances.PaperProofs.Section7.CellSDPUpperGoodEvent
public import DirectedDistances.PaperProofs.Section7.CellSDPUpperFirstBulletAE
public import DirectedDistances.PaperProofs.Section7.CellLowerBoundaryStage
public import DirectedDistances.KMSW.UIBOTBoundaryShift

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory Quiver
open DirectedDistances.KMSW DirectedDistances.RandomWalk DirectedDistances.Recursive

private theorem int_abs_le_natFloor {z : ℤ} {q : ℝ} (hq : 0 ≤ q)
    (hz : |(z : ℝ)| ≤ q) : |z| ≤ (⌊q⌋₊ : ℤ) := by
  have hEq : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hnat : z.natAbs ≤ ⌊q⌋₊ := by
    apply (Nat.le_floor_iff hq).2
    rw [hEq]
    exact hz
  have hnatInt : (z.natAbs : ℤ) ≤ (⌊q⌋₊ : ℤ) := by
    exact_mod_cast hnat
  simpa only [Int.natCast_natAbs] using hnatInt

private theorem iidCodes_ae_shiftedBoundaryHitWitnesses :
    ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ n : ℕ, ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)), hn = hn := by
  filter_upwards [iidCodes_ae_uibotBoundary_allTimes] with ω hω
  dsimp only
  intro n
  have h := hω n
  dsimp only at h
  rcases h with ⟨⟨_, _hn, _⟩, _, _⟩
  exact ⟨by simpa [Nat.add_assoc] using _hn, rfl⟩

/-- CONDITIONAL helper toward Lemma 7.8 (lem-cell-sdp-upper,
bound follows from the good event and a.e. composition. Lemma 7.7, future-law
stationarity and per-selected-target confinement (root concern
result. Confinement applies to the `Classical.choose` targets from
`cell_sdp_separator_targets`, which are the targets returned by the a.e. helper. -/
theorem cellSdpUpper_first_bullet_prob
    (hfluc : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ B : ℝ, C ≤ B →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ k →
            |(busemannSDPMeasurableVersion ω i : ℝ)| ≤
              B * (k : ℝ) ^ (3 / 4 : ℝ)})
    (hstat : ∀ n : ℕ,
      iidCodeMeasure.map (fun ω =>
        busemannSDPMeasurableVersion (codeShift n ω)) =
          iidCodeMeasure.map busemannSDPMeasurableVersion)
    (hconf : ∀ᵐ ω ∂iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∀ hseparator : ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
        ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ ℓ k : ℤ,
          ∃ y : ℕ → PresentVertex (fun i => w (n + i)),
            Function.Injective y ∧
            (∀ j, Reachable (boundaryPresentVertex (fun i => w (n + i)) hn k)
                (y j) ∧
              Reachable (boundaryPresentVertex (fun i => w (n + i)) hn
                (((kmswStage w n).UR.length + 1 : ℕ) : ℤ)) (y j)) ∧
            (∀ j, FiniteAvoidance (boundaryPresentVertex w h0 ℓ)
              (⟨kmswWindowVertexMapInf w n (y j).id⟩ : PresentVertex w)),
        ∀ n : ℕ, ∀ h0 : BoundaryHitWitnesses w,
          ∀ hn : BoundaryHitWitnesses (fun i => w (n + i)), ∀ ℓ : ℤ,
            -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
            ∀ k : ℤ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
              (sdp (boundaryPresentVertex (fun i => w (n + i)) hn k)
                ((Classical.choose (hseparator n h0 hn ℓ k)) j)).toNat ≤
              (sdp
                (⟨kmswWindowVertexMapInf w n
                  (boundaryVertex (fun i => w (n + i)) hn k)⟩ : PresentVertex w)
                (⟨kmswWindowVertexMapInf w n
                  ((Classical.choose (hseparator n h0 hn ℓ k)) j).id⟩ :
                    PresentVertex w)).toNat) :
    ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ, 1 ≤ n →
        1 - δ ≤ iidCodeMeasure.real {ω : ℕ → Fin 3 |
          let w := fun i => ω (i + 1)
          ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
            -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
            ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
            ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
              ∃ k : ℤ,
                -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
                k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
                sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
                  ⟨kmswWindowVertexMapInf w n
                    (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
                    (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)} := by
  classical
  intro δ hδ
  obtain ⟨C, hC, hgood⟩ := cell_sdp_bdy_good_event hfluc hstat δ hδ
  let A₀ : ℝ := max 2 (2 * C)
  have hA₀ : 1 < A₀ := by
    dsimp [A₀]
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA n hn
  have hAhigh : C ≤ A / 2 := by
    dsimp [A₀] at hA
    have htwo : 2 * C ≤ A := (le_max_right 2 (2 * C)).trans hA
    linarith
  have hApos : 0 < A := by linarith [hC, hAhigh]
  let B : ℝ := A / 2
  let q : ℝ := A / 4 * (n : ℝ) ^ (3 / 8 : ℝ)
  let M : ℤ := (⌊q⌋₊ : ℕ)
  let G : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    let K := B * Real.sqrt (n : ℝ)
    let σ₀ := ((kmswStage w n).LR.length : ℤ)
    let σₙ := ((kmswStage w n).UR.length : ℤ) + 1
    ((kmswStage w n).LR.length : ℝ) ≤ K ∧
      ((kmswStage w n).UR.length : ℝ) + 1 ≤ K ∧
      ((kmswStage w n).LL.length : ℝ) ≤ K ∧
      (((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ K ∧
      (∀ ℓ : ℤ, |(ℓ : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion ω ℓ : ℝ) -
          (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤
            B * (n : ℝ) ^ (3 / 8 : ℝ) / 2) ∧
      (∀ k : ℤ, |(k : ℝ)| ≤ K →
        |(busemannSDPMeasurableVersion (codeShift n ω) k : ℝ) -
          (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤
            B * (n : ℝ) ^ (3 / 8 : ℝ) / 2)}
  have hG := hgood B hAhigh n hn
  have hprobG : 1 - δ ≤ iidCodeMeasure.real G := by
    simpa [G, B] using hG
  let T : Set (ℕ → Fin 3) := {ω |
    let w := fun i => ω (i + 1)
    ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
      -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
      ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
      ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
        ∃ k : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
          k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
          sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
            ⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)}
  have hset : G ∩ T =ᵐ[iidCodeMeasure] G := by
    filter_upwards [iidCodes_ae_shiftedBoundaryHitWitnesses,
      cellSdpUpper_first_bullet_ae, cell_sdp_separator_targets, hconf]
      with ω hb ha hseparator hc
    dsimp only at hseparator hc
    apply propext
    simp only [Set.mem_inter_iff]
    constructor
    · intro h
      exact h.1
    · intro hGω
      refine ⟨hGω, ?_⟩
      let w := fun i => ω (i + 1)
      change ∀ h0 : BoundaryHitWitnesses w, ∀ ℓ : ℤ,
        -((kmswStage w n).LL.length : ℤ) ≤ ℓ →
        ℓ ≤ ((kmswStage w n).LR.length : ℤ) →
        ∃ hn : BoundaryHitWitnesses (fun i => w (n + i)),
          ∃ k : ℤ,
            -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ k ∧
            k ≤ ((kmswStage w n).UR.length : ℤ) + 1 ∧
            sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
              ⟨kmswWindowVertexMapInf w n
                (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
              (⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ : ℕ∞)
      dsimp [G, B] at hGω
      intro h0 ℓ hℓL hℓR
      obtain ⟨hn, _⟩ := hb n
      have hstage := boundaryVertex_lt_stage_of_lowerRange w n h0 ℓ
        ⟨hℓL, hℓR⟩
      have hKnonneg : 0 ≤ B * Real.sqrt (n : ℝ) := by
        apply mul_nonneg (by dsimp [B]; linarith) (Real.sqrt_nonneg _)
      have hqnonneg : 0 ≤ q := by
        dsimp [q]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      let σ₀ : ℤ := ((kmswStage w n).LR.length : ℤ)
      let σₙ : ℤ := ((kmswStage w n).UR.length : ℤ) + 1
      have hM0 : ∀ r : ℤ,
          -((kmswStage w n).LL.length : ℤ) ≤ r →
          r ≤ ((kmswStage w n).LR.length : ℤ) →
          |busemannSDPMeasurableVersion ω r -
            busemannSDPMeasurableVersion ω σ₀| ≤ M := by
        intro r hrL hrR
        have hrAbs : |(r : ℝ)| ≤ (A / 2) * Real.sqrt (n : ℝ) := by
          have hlow : -((kmswStage w n).LL.length : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast hrL
          have hupp : (r : ℝ) ≤ (kmswStage w n).LR.length := by
            exact_mod_cast hrR
          have hll := hGω.2.2.1
          have hlr := hGω.1
          rw [abs_le]
          constructor <;> nlinarith [hKnonneg]
        have hreal := hGω.2.2.2.2.1 r hrAbs
        have hrealq : |(busemannSDPMeasurableVersion ω r : ℝ) -
            (busemannSDPMeasurableVersion ω σ₀ : ℝ)| ≤ q := by
          calc
            _ ≤ B * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by simpa [σ₀] using hreal
            _ = q := by dsimp [q, B]; ring
        have hcast' :
            |((busemannSDPMeasurableVersion ω r -
              busemannSDPMeasurableVersion ω σ₀ : ℤ) : ℝ)| ≤ q := by
          simpa only [Int.cast_sub] using hrealq
        simpa [M] using int_abs_le_natFloor hqnonneg hcast'
      have hMn : ∀ r : ℤ,
          -(((kmswStage w n).UL.length - 1 : ℕ) : ℤ) ≤ r →
          r ≤ ((kmswStage w n).UR.length : ℤ) + 1 →
          |busemannSDPMeasurableVersion (codeShift n ω) r -
            busemannSDPMeasurableVersion (codeShift n ω) σₙ| ≤ M := by
        intro r hrL hrR
        have hrAbs : |(r : ℝ)| ≤ (A / 2) * Real.sqrt (n : ℝ) := by
          have hlow :
              -(((kmswStage w n).UL.length - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast hrL
          have hupp : (r : ℝ) ≤ (kmswStage w n).UR.length + 1 := by
            exact_mod_cast hrR
          have hul := hGω.2.2.2.1
          have hur := hGω.2.1
          rw [abs_le]
          constructor <;> nlinarith [hKnonneg]
        have hreal := hGω.2.2.2.2.2 r hrAbs
        have hrealq : |(busemannSDPMeasurableVersion (codeShift n ω) r : ℝ) -
            (busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℝ)| ≤ q := by
          calc
            _ ≤ B * (n : ℝ) ^ (3 / 8 : ℝ) / 2 := by
              simpa [σₙ, Nat.cast_add] using hreal
            _ = q := by dsimp [q, B]; ring
        have hcast' :
            |((busemannSDPMeasurableVersion (codeShift n ω) r -
              busemannSDPMeasurableVersion (codeShift n ω) σₙ : ℤ) : ℝ)| ≤ q := by
          simpa only [Int.cast_sub] using hrealq
        simpa [M] using int_abs_le_natFloor hqnonneg hcast'
      have htargetsConf := hc hseparator n h0 hn ℓ hℓL hℓR
      obtain ⟨hTargets, hfirst⟩ := ha n h0 hn M M hM0 hMn ℓ
        hℓL hℓR hstage
      have hTargetsEq : hTargets = hseparator n h0 hn ℓ :=
        Subsingleton.elim _ _
      rw [← hTargetsEq] at htargetsConf
      obtain ⟨k, hkL, hkR, hdist⟩ := hfirst htargetsConf
      have hMle : (M : ℝ) ≤ q := by
        simpa [M] using (Nat.floor_le hqnonneg)
      have htotal : 4 * (M : ℝ) ≤ A * (n : ℝ) ^ (3 / 8 : ℝ) := by
        dsimp [q] at hMle
        nlinarith [hMle]
      have htotalNat : (4 * M).toNat ≤
          ⌊A * (n : ℝ) ^ (3 / 8 : ℝ)⌋₊ := by
        apply (Nat.le_floor_iff (by positivity :
          0 ≤ A * (n : ℝ) ^ (3 / 8 : ℝ))).2
        have hcastM : ((4 * M).toNat : ℝ) = 4 * (M : ℝ) := by
          rw [← Int.cast_natCast,
            Int.toNat_of_nonneg (by omega : 0 ≤ 4 * M)]
          norm_cast
        rw [hcastM]
        exact htotal
      have hdist' :
          sdp (⟨boundaryVertex w h0 ℓ⟩ : StagePresentVertex w n)
            ⟨kmswWindowVertexMapInf w n
              (boundaryVertex (fun i => w (n + i)) hn k)⟩ ≤
            ((4 * M).toNat : ℕ∞) := by
        have heq : 2 * M + 2 * M = 4 * M := by ring
        simpa [heq] using hdist
      refine ⟨hn, k, hkL, hkR, ?_⟩
      exact hdist'.trans (by exact_mod_cast htotalNat)
  have hmeas : iidCodeMeasure.real (G ∩ T) = iidCodeMeasure.real G :=
    measureReal_congr hset
  calc
    1 - δ ≤ iidCodeMeasure.real G := hprobG
    _ = iidCodeMeasure.real (G ∩ T) := hmeas.symm
    _ ≤ iidCodeMeasure.real T := measureReal_mono Set.inter_subset_right

end DirectedDistances.PaperProofs.Section7
