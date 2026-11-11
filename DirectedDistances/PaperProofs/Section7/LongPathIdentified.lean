module

public import DirectedDistances.PaperProofs.Section7.LongPathAEStage
public import DirectedDistances.PaperProofs.Section7.LDPFluctuationIdentified
public import DirectedDistances.KMSW.M0CutPathVisit
import DirectedDistances.KMSW.CutEquivalenceConverse

/-! Supporting lemmas for paper labels `lem-long-path` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section7

open MeasureTheory DirectedDistances.KMSW DirectedDistances.RandomWalk
open Quiver DirectedDistances.Recursive DirectedDistances.PaperProofs.Section1




@[expose] def IdentifiedStagePath (W : ℤ → Fin 3)
    (V : ℕ → WholePlaneVertex W) (n N : ℕ)
    (p : Fin (N + 1) → WholePlaneVertex W) : Prop :=
  (∀ i, ∃ z : ℕ, z < (kmswStage (shiftedStream W 0) n).nextVertex ∧
    p i = V z) ∧
  (∀ i : Fin N, ∃ e : ℕ,
    e < (kmswStage (shiftedStream W 0) n).nextEdge ∧
    (kmswStage (shiftedStream W 0) n).present e = true ∧
    wholePlaneEdgeWest W (wholePlaneEdgeι W 0 e) = p i.castSucc ∧
    wholePlaneEdgeEast W (wholePlaneEdgeι W 0 e) = p i.succ)




private theorem stage_path_identified (W : ℤ → Fin 3)
    (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
      (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
    (n : ℕ) {a b : StagePresentVertex (shiftedStream W 0) n}
    (ha : a.id < (kmswStage (shiftedStream W 0) n).nextVertex)
    (q : Path a b) :
    ∃ p : Fin (q.length + 1) → WholePlaneVertex W,
      p 0 = wholePlaneVertexι W 0 a.id ∧
      p (Fin.last q.length) = wholePlaneVertexι W 0 b.id ∧
      (∀ i : Fin q.length, m0CutDirectedStep W H (m0CutData W H h hLL).seam
        (p i.castSucc) (p i.succ)) ∧
      IdentifiedStagePath W (wholePlaneVertexι W 0) n q.length p := by
  induction q with
  | nil =>
    refine ⟨fun _ => wholePlaneVertexι W 0 a.id, rfl, rfl, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact ⟨a.id, ha, rfl⟩
    · intro i
      exact Fin.elim0 i
  | @cons c b q e ih =>
    simp only [Path.length_cons]
    obtain ⟨p, hp0, hpend, hsteps, hverts, hedges⟩ := ih
    let f := (stageToLimit (shiftedStream W 0) n).map e
    have hstep : m0CutDirectedStep W H (m0CutData W H h hLL).seam
        (wholePlaneVertexι W 0 c.id) (wholePlaneVertexι W 0 b.id) :=
      (m0Cut_identification_directedStep W H h hLL c.id b.id).2
        ⟨f.1, f.2.1, congrArg (wholePlaneVertexι W 0) f.2.2.1,
          congrArg (wholePlaneVertexι W 0) f.2.2.2⟩
    have hb : b.id < (kmswStage (shiftedStream W 0) n).nextVertex := by
      have hb := (CutConverse.endpoint_bound (shiftedStream W 0) n
        e.val e.property.1).2
      rw [e.property.2.2.2] at hb
      exact hb
    refine ⟨Fin.snoc p (wholePlaneVertexι W 0 b.id), ?_, ?_, ?_, ?_, ?_⟩
    · exact (Fin.snoc_castSucc (α := fun _ => WholePlaneVertex W)
        (wholePlaneVertexι W 0 b.id) p (0 : Fin (q.length + 1))).trans hp0
    · simp
    · intro i
      cases i using Fin.lastCases with
      | cast j =>
        simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using hsteps j
      | last =>
        simpa [hpend] using hstep
    · intro i
      cases i using Fin.lastCases with
      | cast j => simpa only [Fin.snoc_castSucc] using hverts j
      | last => exact ⟨b.id, hb, by simp⟩
    · intro i
      cases i using Fin.lastCases with
      | cast j =>
        simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using hedges j
      | last =>
        refine ⟨e.val, e.property.1, e.property.2.1, ?_, ?_⟩
        · simp only [Fin.snoc_castSucc, hpend]
          rw [wholePlaneEdgeWest_ι]
          exact congrArg (wholePlaneVertexι W 0) f.2.2.1
        · simp only [Fin.succ_last, Fin.snoc_last]
          rw [wholePlaneEdgeEast_ι]
          exact congrArg (wholePlaneVertexι W 0) f.2.2.2






theorem lem_long_path_identified :
    ∀ᵐ W ∂RandomWalk.wholePlaneIIDCodeMeasure,
      ∃ H : WholePlaneRotationHypothesis W,
      ∃ h : BoundaryHitWitnesses (shiftedStream W 0),
      ∃ hLL : ∀ k : ℤ, k ≤ 0 → wholePlaneEdgePresent W
        (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
          (boundaryHitTime (shiftedStream W 0) h (k - 1)))),
      let w := shiftedStream W 0
      let V := wholePlaneVertexι W 0
      let D := m0CutData W H h hLL
      IsIdentifiedM0BusemannLDP D (identifiedLDPBusemann W) ∧
      ∀ ell k : ℕ, 1 ≤ ell → ell < k →
        let n := boundaryHitTime w h (-(k : ℤ))
        ∃ (N : ℕ) (p : Fin (N + 1) → WholePlaneVertex W),
          (∀ i : Fin N, m0CutDirectedStep W H D.seam (p i.castSucc) (p i.succ)) ∧
          IdentifiedStagePath W V n N p ∧
          (max (identifiedLDPBusemann W (-(ell : ℤ)) -
            identifiedLDPBusemann W (-(k : ℤ))) 0).toNat ≤ N := by
  have hp := lem_long_path
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hp
  have hpull := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hp
  filter_upwards [hpull, thm_busemann_paper,
    identifiedLDPBusemann_eq_carrier_ae,
    identifiedLDPBusemann_characterization_ae] with W hpath hpaper heq hchar
  have htail : (fun i => shiftedCodePath W 0 (i + 1)) = shiftedStream W 0 := by
    funext i
    simp [shiftedCodePath]
  rw [htail] at hpath
  obtain ⟨h', hpath⟩ := hpath
  obtain ⟨H, h, hLL, _⟩ := hpaper
  refine ⟨H, h, hLL, ?_⟩
  dsimp only
  refine ⟨hchar H h hLL, ?_⟩
  intro ell k hell hlt
  obtain ⟨a, b, ha, _, q, hq⟩ := hpath ell k hell hlt
  obtain ⟨p, _, _, hsteps, hstage⟩ :=
    stage_path_identified W H h hLL _ ha q
  refine ⟨q.length, p, hsteps, hstage, ?_⟩
  rw [heq]
  exact hq

end DirectedDistances.PaperProofs.Section7
