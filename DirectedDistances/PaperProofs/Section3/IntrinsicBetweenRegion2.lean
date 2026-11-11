/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.IntrinsicBetweenRegion
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart6

/-! # Restricted rightmost references for intrinsic between regions

the geometric star and stop the outgoing block without gaining orientation.
Source-region identification and intrinsic leftmost uniqueness remain separate -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1 DirectedDistances.PaperProofs.Section5
open Set

/-- Helper toward Proposition 3.9: the vertical-fiber region between
a proper graph ray and itself consists of exactly that complete ray. -/
theorem intrinsicBetween_closedBetween_self {T : Set ℂ} {x₀ : ℝ}
    (hT : ProperGraphRay T x₀) : closedBetween T T = T := by
  obtain ⟨X, f, _, _, heq, _⟩ := hT
  ext z
  rw [mem_closedBetween_iff heq heq, heq]
  constructor
  · rintro ⟨hx, hlo, hhi⟩
    exact ⟨hx, le_antisymm (hhi hx) hlo⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, hz.ge, fun _ => hz.le⟩

/-- Helper toward Proposition 3.9: a run-rightmost outgoing edge has a
nonoutgoing immediate clockwise predecessor, even when that predecessor
is a missing geometric boundary edge. -/
theorem intrinsicBetween_runRightmost_predecessor_not_tail
    {w : ℕ → Fin 3} {hfin : KMSWFiniteIncidence w} {v e : ℕ}
    (he : kmswRunRightmostOutAt w hfin v e) :
    ¬ futureMapTail w ((kmswInfRot w hfin).symm (e, false)) := by
  obtain ⟨_, _, k, hk, hstop, hgap⟩ := he
  by_cases hk1 : k = 1
  · simpa only [hk1, pow_one] using hstop
  · intro ht
    have hn := hgap 1 (by omega) (by omega)
    rw [pow_one] at hn
    exact hn ht.2

section Source

variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "hLL" => (fun (k : ℤ) (_ : k ≤ 0) => hp
  (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h (k - 1)))))
local notation "D" => m0CutData W H h hLL
local notation "C" => intrinsicGeodesicSourceCut W H G hp D
local notation "E" => uibotCut2SourceDartEquiv W H h hpast hp

/-- Helper toward Proposition 3.9: every source present path has a
proper graph-ray trace, including the possibility of a finite limiting
abscissa and unbounded height. -/
theorem intrinsicBetween_source_trace_properGraphRay
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) :
    ProperGraphRay
      (intrinsicEdgeRayTrace S (fun n => wholePlaneEdgeι W 0 (P.edge n)))
      (((monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
        (monotone_family_all (shiftedStream W 0))).arc (P.edge 0, false)).start.re) := by
  erw [intrinsicGeodesicSource_trace, m0Cut_pathTrace_eq W H h hpast]
  exact infinitePresentPath_properGraphRay (H.1 0)
    (fun n => ⟨monotoneLayoutDrawing (shiftedStream W 0) n
      ((monotone_family_all (shiftedStream W 0)) n).choose,
      ((monotone_family_all (shiftedStream W 0)) n).choose_spec⟩) P

/- Helper toward Proposition 3.9: source ray traces are closed; this -/
theorem intrinsicBetween_source_trace_isClosed
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) :
    IsClosed (intrinsicEdgeRayTrace S (fun n => wholePlaneEdgeι W 0 (P.edge n))) := by
  have hproper := intrinsicBetween_source_trace_properGraphRay W H h hpast hp P
  have hclosed := isClosed_closedBetween hproper hproper
  exact (intrinsicBetween_closedBetween_self hproper) ▸ hclosed

/-- Helper toward Proposition 3.9: the source characterization holds
on the coincident-ray diagonal, including the full boundary trace. The
classification of components for distinct rays is a separate obligation. -/
theorem intrinsicBetween_source_self
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) :
    nativeBetween S (fun n => wholePlaneEdgeι W 0 (P.edge n))
        (fun n => wholePlaneEdgeι W 0 (P.edge n)) =
      closedBetween
        (pathTrace G (fun n => wholePlaneDartι W 0 (P.edge n, false)))
        (pathTrace G (fun n => wholePlaneDartι W 0 (P.edge n, false))) := by
  rw [nativeBetween_self S _
    (intrinsicBetween_source_trace_isClosed W H h hpast hp P)]
  erw [← intrinsicGeodesicSource_trace W H G hp]
  exact (intrinsicBetween_closedBetween_self
    (intrinsicBetween_source_trace_properGraphRay W H h hpast hp P)).symm

/-- Helper toward Proposition 3.9: the stored source arc and the
chronological dart arc have exactly the same simultaneous winding-side
tests, despite their possibly different parameter schedules. -/
theorem intrinsicBetween_source_dart_leftAtOn_iff
    (d : WholePlaneDart W) (F : Set ℂ) :
    (∀ s, LeftAtOn F (intrinsicFutureDartArc S (E d)) s) ↔
      ∀ s, LeftAtOn F (((G).arc d).toPath) s := by
  obtain ⟨φ, hmono, hparam⟩ :=
    uibotCut2SourceDartEquiv_arc_param W H h hpast hp d
  have h0 : φ 0 = 0 := by
    obtain ⟨t, ht⟩ := φ.surjective 0
    exact le_antisymm ((hmono.monotone bot_le).trans_eq ht) bot_le
  have h1 : φ 1 = 1 := by
    obtain ⟨t, ht⟩ := φ.surjective 1
    exact le_antisymm le_top (ht.symm.trans_le (hmono.monotone le_top))
  refine Iff.trans ?_ (forall_leftAtOn_reparam_iff F ((G).arc d).toPath φ h0 h1)
  exact forall_congr' (fun s => leftAtOn_congr_fun F _ _ s hparam)

/-- Helper toward Proposition 3.9: the native ray-side incidence test
is exactly a chronological winding-side test on an edge of the source ray.
The reverse bit tests the reversed geometric dart, retaining edge identity. -/
theorem intrinsicBetween_source_ray_touches_side_iff
    {v : PresentVertex (shiftedStream W 0)}
    (P : InfinitePresentPath (shiftedStream W 0) v) (F : Set ℂ) (reverse : Bool) :
    intrinsicRayTouchesSide S (fun n => wholePlaneEdgeι W 0 (P.edge n)) F reverse ↔
      ∃ n, ∀ s, LeftAtOn F
        (((G).arc (wholePlaneDartι W 0 (P.edge n, reverse))).toPath) s := by
  have hxor (e : WholePlaneEdge W) :
      ((E (e, false)).1, Bool.xor (E (e, false)).2 reverse) = E (e, reverse) := by
    apply Prod.ext
    · rfl
    change Bool.xor (Bool.xor false _) reverse = Bool.xor reverse _
    simp only [Bool.false_xor, Bool.xor_comm]
  have htail (n : ℕ) : intrinsicFutureAmbientTail S
      (E (wholePlaneDartι W 0 (P.edge n, false))) := by
    apply (uibotCut2SourceDartEquiv_tail W H h hpast hp _).mpr
    exact ⟨Bool.false_ne_true, hp _⟩
  constructor
  · rintro ⟨n, d, hd, ht, hs⟩
    have heq : d = E (wholePlaneDartι W 0 (P.edge n, false)) := by
      obtain ⟨hn, hb⟩ := ht
      obtain ⟨hn', hb'⟩ := htail n
      apply Prod.ext hd
      have hsub : (⟨d.1, hn⟩ : {e : (S).E // ¬ (S).map.missing e}) =
          ⟨(E (wholePlaneDartι W 0 (P.edge n, false))).1, hn'⟩ := Subtype.ext hd
      exact hb.symm.trans ((congrArg (S).map.forward hsub).trans hb')
    subst d
    change ∀ s, LeftAtOn F
      (intrinsicFutureDartArc S
        (((E (wholePlaneDartι W 0 (P.edge n, false))).1),
          Bool.xor (E (wholePlaneDartι W 0 (P.edge n, false))).2 reverse)) s at hs
    erw [hxor] at hs
    exact ⟨n, (intrinsicBetween_source_dart_leftAtOn_iff W H h hpast hp _ F).mp hs⟩
  · rintro ⟨n, hs⟩
    refine ⟨n, E (wholePlaneDartι W 0 (P.edge n, false)), rfl, htail n, ?_⟩
    erw [hxor]
    exact (intrinsicBetween_source_dart_leftAtOn_iff W H h hpast hp _ F).mpr hs

/-- Helper toward Proposition 3.9: cut-tail orientation under source
dart conversion agrees with the run-zero tail predicate, with geometric
missing boundary edges retained and unoriented. -/
theorem intrinsicBetween_source_cut_tail_iff (d : ℕ × Bool) :
    intrinsicBetweenCutTail S C (E (wholePlaneDartι W 0 d)) ↔
      futureMapTail (shiftedStream W 0) d := by
  have hm : wholePlaneDartι W 0 d ∈ (D).darts := by
    rw [(D).darts_eq h hLL]
    exact mem_range_self d
  change ((wholePlaneDartι W 0 d).1 ∈ (D).edges ∧
    ¬ (D).missing (wholePlaneDartι W 0 d).1 ∧
    intrinsicFutureAmbientTail S (E (wholePlaneDartι W 0 d))) ↔ _
  erw [uibotCut2SourceDartEquiv_tail W H h hpast hp]
  change (_ ∧ ¬ (D).missing _ ∧ wholePlaneDartTail W _) ↔ _
  constructor
  · rintro ⟨_, hn, ht⟩
    exact (m0Cut_tail_iff W H h hLL d).mp ⟨ht, hn⟩
  · intro ht
    obtain ⟨ht, hn⟩ := (m0Cut_tail_iff W H h hLL d).mpr ht
    exact ⟨hm, hn, ht⟩

/-- Helper toward Proposition 3.9: each code rightmost edge is
rightmost in the cut's restricted geometric rotation. This uses the actual
immediate predecessor, including missing boundary incidences. -/
theorem intrinsicBetween_source_rightmost_outgoing {v e : ℕ}
    (he : kmswRunRightmostOutAt (shiftedStream W 0) (H.1 0) v e) :
    intrinsicBetweenCutRightmostOutgoingAt S C
      (wholePlaneVertexι W 0 v) (wholePlaneEdgeι W 0 e) := by
  let d : ℕ × Bool := (e, false)
  let a := (kmswInfRot (shiftedStream W 0) (H.1 0)).symm d
  refine ⟨E (wholePlaneDartι W 0 d), rfl, ?_,
    (intrinsicBetween_source_cut_tail_iff W H h hpast hp d).mpr ⟨rfl, he.1⟩,
    E (wholePlaneDartι W 0 a), ?_, ?_⟩
  · erw [uibotCut2SourceDartEquiv_vertex W H h hpast hp, wholePlaneDartVertex_ι]
    exact congrArg (wholePlaneVertexι W 0) he.2.1
  · have hr := uibotCut2_source_cut_rotation W H h hpast hp a
    dsimp only [a] at hr
    rw [Equiv.apply_symm_apply] at hr
    exact hr
  · intro ht
    exact intrinsicBetween_runRightmost_predecessor_not_tail he
      ((intrinsicBetween_source_cut_tail_iff W H h hpast hp a).mp ht)

/-- Helper toward Proposition 3.9: every edge of a source-cut path
whose stream is the code rightmost ray is intrinsically cut-rightmost. -/
theorem intrinsicBetween_source_reference_rightmost (k : ℤ)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (_hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge) :
    RightmostInCut S C ((D).x k)
      (intrinsicSourceInfinitePathEquiv W H G hp D ((D).x k)
        (m0CutPathOfPresentPath W H h hLL k T)) := by
  intro n
  rw [intrinsicSourceInfinitePathEquiv_vertex, m0CutPathOfPresentPath_vertex]
  change intrinsicBetweenCutRightmostOutgoingAt S C
    (wholePlaneVertexι W 0 (T.initial n).1.id)
    (wholePlaneEdgeι W 0 (T.edge n))
  apply intrinsicBetween_source_rightmost_outgoing W H h hpast hp
  have he := R.rightmost n
  rw [← hedge] at he
  have hv : R.vertex n = (T.initial n).1.id :=
    he.2.1.symm.trans (T.edge_outgoing_at_initial (shiftedStream W 0) n).2
  exact hv ▸ he

/-- Helper toward Proposition 3.9: in every geometric representative,
the image code reference is rightmost in the image cut's restricted star.
This is the full deterministic cut-rightmost attribution, with the original
source binders and the same cut witnesses. -/
theorem intrinsicBetween_image_reference_rightmost (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2
      (uibotWholePlaneSourceMap W H G hp) (uibotWholePlaneSourceRoot W H G)
      A.map A.root)
    (k : ℤ)
    (T : InfinitePresentPath (shiftedStream W 0)
      (boundaryPresentVertex (shiftedStream W 0) h k))
    (R : KMSWRunRightmostRay (shiftedStream W 0) (H.1 0))
    (hstart : R.vertex 0 = boundaryVertex (shiftedStream W 0) h k)
    (hedge : T.edge = R.edge) :
    RightmostInCut A (intrinsicBusemannImageCut W H G hp D A I)
      (I.vertexEquiv ((D).x k))
      (intrinsicImageInfinitePathEquiv W H G hp D A I ((D).x k)
        (m0CutPathOfPresentPath W H h hLL k T)) :=
  (rightmostInCut_map_iff I _).mpr
    (intrinsicBetween_source_reference_rightmost W H h hpast hp k T R hstart hedge)

end Source




































































































end DirectedDistances.PaperProofs.Section3
end
