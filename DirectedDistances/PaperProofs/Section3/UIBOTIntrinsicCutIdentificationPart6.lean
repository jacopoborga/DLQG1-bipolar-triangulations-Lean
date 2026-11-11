/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section1.IntrinsicFutureCut2
public import DirectedDistances.PaperProofs.Section3.UIBOTIntrinsicCutIdentificationPart5

/-! # Intrinsic future cut with restricted submap rotation

retained cut darts. These helpers preserve every geometric carrier and -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section1
open MeasureTheory Filter

section Transport
variable {A B : D39DomainRootedMap.{0}}
    (I : D39GeomRootedMapIsoV2 A.map A.root B.map B.root)

/-- Helper toward Proposition 3.9: transport the complete submap interface,
including its restricted rotation, by the proved geometric pushforward. -/
@[expose] def intrinsicFutureCut2Pushforward (C : IntrinsicFutureCut2 A) :
    IntrinsicFutureCut2 B :=
  (intrinsicFutureCutPushforward I C.toIntrinsicFutureCut).toIntrinsicFutureCut2

/-- Helper toward Proposition 3.9: all cut carriers, orientations, restricted
rotation pairs, boundary labels and extremal rays are transported together. -/
theorem intrinsicFutureCut2_pushforward (C : IntrinsicFutureCut2 A) :
    ∃ C' : IntrinsicFutureCut2 B,
      C'.vertices = I.vertexEquiv '' C.vertices ∧
      C'.edges = I.edgeEquiv '' C.edges ∧
      C'.faces = I.faceEquiv '' C.faces ∧
      (∀ e, C'.seam (I.edgeEquiv e) ↔ C.seam e) ∧
      (∀ e, C'.missing (I.edgeEquiv e) ↔ C.missing e) ∧
      (∀ d, C'.tail (intrinsicFutureDartEquiv I d) ↔ C.tail d) ∧
      (∀ d a, C'.rotation (intrinsicFutureDartEquiv I d)
        (intrinsicFutureDartEquiv I a) ↔ C.rotation d a) ∧
      (∀ k, C'.x k = I.vertexEquiv (C.x k)) ∧
      (∀ n, C'.betaRVertex n = I.vertexEquiv (C.betaRVertex n) ∧
        C'.betaLVertex n = I.vertexEquiv (C.betaLVertex n) ∧
        C'.betaREdge n = I.edgeEquiv (C.betaREdge n) ∧
        C'.betaLEdge n = I.edgeEquiv (C.betaLEdge n)) := by
  obtain ⟨C', hC'⟩ := intrinsicFutureCut_pushforward I C.toIntrinsicFutureCut
  exact ⟨C'.toIntrinsicFutureCut2, hC'⟩

end Transport



/-- Helper toward Proposition 3.9: an ambient directed dart has the
ordered tail and head of its edge, independently of endpoint storage. -/
theorem intrinsicFuture_dart_endpoints_of_tail
    (A : D39DomainRootedMap.{0}) (d : A.E × Bool)
    (hd : intrinsicFutureAmbientTail A d) :
    ∃ he : ¬ A.map.missing d.1,
      d39GeomRootVertex A.map d = A.map.tail ⟨d.1, he⟩ ∧
      d39GeomRootOtherVertex A.map d = A.map.head ⟨d.1, he⟩ := by
  rcases d with ⟨e, b⟩
  obtain ⟨he, hb⟩ := hd
  refine ⟨he, ?_, ?_⟩ <;>
      cases b <;> simp only [DirectedPlaneMapWithMissing.tail,
        DirectedPlaneMapWithMissing.head, hb, d39GeomRootVertex,
        d39GeomRootOtherVertex, Bool.false_eq_true, ↓reduceIte]



/-- Helper toward Proposition 3.9: an injective reindexing of a star
preserves its topological cyclic successor, with no omitted incidences. -/
theorem intrinsicFutureCut2_topological_image {α β : Type*}
    [intrinsicFutureCut2Nonempty : Nonempty α]
    (ι : α → β) (hι : Function.Injective ι)
    (star : Set α) (arc : α → unitInterval → ℂ)
    (arc' : β → unitInterval → ℂ)
    (harc : ∀ a t, arc' (ι a) t = arc a t) {d a : α}
    (ht : D39TopologicalCcwSuccessor star arc d a) :
    D39TopologicalCcwSuccessor (ι '' star) arc' (ι d) (ι a) := by
  obtain ⟨T, hT, dir, hn, hi, hc, hs⟩ := ht
  let dir' := fun b => dir (Function.invFun ι b)
  have hd (a : α) : dir' (ι a) = dir a :=
    congrArg dir (Function.leftInverse_invFun hι a)
  refine ⟨T, hT, dir', ?_, ?_, ?_, ?_⟩
  · rintro b ⟨b, hb, rfl⟩
    rw [hd]
    exact hn b hb
  · rintro b ⟨b, hb, rfl⟩ c ⟨c, hc, rfl⟩ hbc
    rw [hd, hd] at hbc
    exact congrArg ι (hi b hb c hc hbc)
  · obtain ⟨hfin, hds, has, hcase⟩ := hc
    refine ⟨hfin.image ι, ⟨d, hds, rfl⟩, ⟨a, has, rfl⟩, ?_⟩
    rcases hcase with ⟨rfl, hsingle⟩ | ⟨hne, hmin⟩
    · exact Or.inl ⟨rfl, by rw [hsingle, Set.image_singleton]⟩
    · refine Or.inr ⟨fun h => hne (hι h), ?_⟩
      rintro b ⟨b, hb, rfl⟩ hbd
      simp only [hd]
      exact hmin b hb (fun hh => hbd (congrArg ι hh))
  · rintro b ⟨b, hb, rfl⟩
    obtain ⟨t, ht0, ht1, ht⟩ := hs b hb
    refine ⟨t, ht0, ht1, ?_⟩
    rw [hd, show arc' (ι b) = arc b from funext (harc b)]
    exact ht



/-- Helper toward Proposition 3.9: forgetting the direction retains the
same unordered endpoint pair, for either stored orientation. -/
theorem intrinsicFutureCut2_endpoints_iff (A : D39DomainRootedMap.{0})
    (e : A.E) (he : ¬ A.map.missing e) (v : A.V) :
    (A.map.tail ⟨e, he⟩ = v ∨ A.map.head ⟨e, he⟩ = v) ↔
      (A.map.src e = v ∨ A.map.tgt e = v) := by
  cases hb : A.map.forward ⟨e, he⟩ <;>
    simp only [DirectedPlaneMapWithMissing.tail, DirectedPlaneMapWithMissing.head,
      hb, Bool.false_eq_true, ↓reduceIte, or_comm]

section Source
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)

local notation "G" => WholePlanePastGlueDrawing.glueDrawing W h hpast H
local notation "S" => uibotWholePlaneSourceDomain W H G hp
local notation "D" => m0CutData W H h (fun _ _ => hp _)
local notation "f" => seamFun (shiftedStream W 0) h ((And.left H) 0)

/-- Helper toward Proposition 3.9: the code dart and the stored geometric
dart differ only by the storage orientation of their common edge. -/
@[expose] def uibotCut2SourceDartEquiv : WholePlaneDart W ≃ (S).E × Bool where
  toFun d := (d.1, Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2))
  invFun d := (d.1, Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2))
  left_inv d := by
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    rfl
  right_inv d := by
    simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Prod.mk.eta]

/-- Helper toward Proposition 3.9: source dart conversion retains the
actual incident vertex, including the effect of stored endpoint reversal. -/
theorem uibotCut2SourceDartEquiv_vertex (d : WholePlaneDart W) :
    d39GeomRootVertex (S).map (uibotCut2SourceDartEquiv W H h hpast hp d) =
      wholePlaneDartVertex W d := by
  let q := (uibotWholePlaneSourceEdgeEquiv W H G d.1).out
  have ho : q.1 = d.1 := uibotWholePlaneSourceEdgeEquiv_out W H G d.1
  change (if Bool.xor d.2 (!q.2) then
      (if q.2 then wholePlaneEdgeEast W q.1 else wholePlaneEdgeWest W q.1)
    else (if !q.2 then wholePlaneEdgeEast W q.1 else wholePlaneEdgeWest W q.1)) =
    (if d.2 then wholePlaneEdgeEast W d.1 else wholePlaneEdgeWest W d.1)
  rw [ho]
  cases d.2 <;> cases q.2 <;> rfl

/-- Helper toward Proposition 3.9: source dart conversion preserves the
ambient directed-tail predicate on every geometric edge. -/
theorem uibotCut2SourceDartEquiv_tail (d : WholePlaneDart W) :
    intrinsicFutureAmbientTail S (uibotCut2SourceDartEquiv W H h hpast hp d) ↔
      wholePlaneDartTail W d := by
  change (∃ he : ¬ ¬ wholePlaneEdgePresent W d.1,
    (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2) =
      Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2)) ↔ _
  cases hb : d.2 <;> cases he : (uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2 <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_xor, Bool.true_xor,
      wholePlaneDartTail, hb, Bool.false_eq_true, not_false_eq_true, not_true_eq_false,
      hp d.1, not_true_eq_false, not_false_eq_true, exists_true_left,
      and_self, false_and, Bool.true_eq_false]


/-- Helper toward Proposition 3.9: the code-to-source dart equivalence
commutes with reversing an incidence of the same geometric edge. -/
theorem uibotCut2SourceDartEquiv_flip (d : WholePlaneDart W) :
    uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartFlip W d) =
      ((uibotCut2SourceDartEquiv W H h hpast hp d).1,
        !(uibotCut2SourceDartEquiv W H h hpast hp d).2) := by
  apply Prod.ext
  · rfl
  change Bool.xor (!d.2) (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2) =
    !(Bool.xor d.2 (!(uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2))
  cases d.2 <;> cases (uibotWholePlaneSourceEdgeEquiv W H G d.1).out.2 <;> rfl

/-- Helper toward Proposition 3.9: each source geometric dart arc is an
increasing reparameterization of its chronological polyline. -/
theorem uibotCut2SourceDartEquiv_arc_param (d : WholePlaneDart W) :
    ∃ φ : unitInterval ≃ₜ unitInterval, StrictMono φ ∧ ∀ t,
      intrinsicFutureDartArc S (uibotCut2SourceDartEquiv W H h hpast hp d) t =
        ((G).arc d).toPath (φ t) := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  let q := (uibotWholePlaneSourceEdgeEquiv W H G d.1).out
  have hrec : (if (E d).2 then q else wholePlaneDartFlip W q) = d := by
    have ho := uibotWholePlaneSourceEdgeEquiv_out W H G d.1
    change (if Bool.xor d.2 (!q.2) then q else wholePlaneDartFlip W q) = d
    cases hb : d.2 <;> cases hq : q.2 <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_xor, Bool.true_xor,
        Bool.false_eq_true, ↓reduceIte] <;>
      apply Prod.ext
    all_goals first | exact ho | exact hq.trans hb.symm |
      (change (!q.2) = d.2; rw [hq, hb]; rfl)
  have hformula (t : unitInterval) :
      intrinsicFutureDartArc S (E d) t =
        if (E d).2 then ((G).arc q).toPath t else ((G).arc q).toPath.symm t := by
    cases hb : (E d).2
    · change intrinsicFutureDartArc S ((E d).1, (E d).2) t = _
      rw [hb]
      rfl
    · change intrinsicFutureDartArc S ((E d).1, (E d).2) t = _
      rw [hb]
      rfl
  cases hb : (E d).2
  · have hd : wholePlaneDartFlip W q = d := by
      simpa only [hb, Bool.false_eq_true, ↓reduceIte] using hrec
    obtain ⟨φ, h0, h1, hφ⟩ :=
      DirectedDistances.PaperProofs.Section5.polyline_reverse_toPath_exists_reparam
        ((G).arc q) ((G).arc_length q) ((G).arc_simple q)
    refine ⟨φ, φ.continuous.strictMono_of_inj_boundedOrder ?_ φ.injective, ?_⟩
    · change φ 0 ≤ φ 1
      rw [h0, h1]; exact bot_le
    · intro t
      rw [hformula, hb]
      change ((G).arc q).toPath.symm t = _
      rw [← hd, (G).arc_flip]
      exact hφ t
  · have hd : q = d := by simpa only [hb, ↓reduceIte] using hrec
    refine ⟨Homeomorph.refl _, strictMono_id, ?_⟩
    intro t
    rw [hformula, hb]
    exact congrArg (fun a => ((G).arc a).toPath t) hd

/-- Helper toward Proposition 3.9: forward ambient rotation is the
topological cyclic successor of the actual source dart arcs. -/
theorem uibotCut2SourceDartEquiv_rotation (d : WholePlaneDart W) :
    intrinsicFutureRotation S Set.univ
      (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneRotation W H d))
      (uibotCut2SourceDartEquiv W H h hpast hp d) := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  have hv := uibotCut2SourceDartEquiv_vertex W H h hpast hp
  have hstar : E '' {a | wholePlaneDartVertex W a = wholePlaneDartVertex W d} =
      {q : (S).E × Bool | q.1 ∈ (Set.univ : Set (S).E) ∧
        d39GeomRootVertex (S).map q =
          d39GeomRootVertex (S).map (E (wholePlaneRotation W H d))} := by
    ext q
    obtain ⟨q, rfl⟩ := E.surjective q
    rw [E.injective.mem_set_image]
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, E, hv,
      wholePlaneRotation_preserves_dartVertex]
    rfl
  have htop := DirectedDistances.PaperProofs.Section5.plDrawing_toPath_rotation_topological_ccwSuccessor
    G d
  have hm := d39TopologicalCcwSuccessor_map_equiv E htop
  rw [hstar] at hm
  have hparam := uibotCut2SourceDartEquiv_arc_param W H h hpast hp
  let φ := fun q => (hparam (E.symm q)).choose.symm
  refine ⟨Set.mem_univ _, Set.mem_univ _, ?_, ?_⟩
  · rw [hv, hv, wholePlaneRotation_preserves_dartVertex]
  · apply d39TopologicalCcwSuccessor_map_orientedHomeomorph _ _ _
      φ (E d) (E (wholePlaneRotation W H d)) (Homeomorph.refl ℂ)
      orientationPreserving_refl ?_ ?_ hm
    · intro q _ x y hxy
      apply (hparam (E.symm q)).choose_spec.1.lt_iff_lt.mp
      simpa only [φ, Homeomorph.apply_symm_apply] using hxy
    · intro q _ t
      have hh := (hparam (E.symm q)).choose_spec.2 (φ q t)
      dsimp only [φ] at hh
      rw [(hparam (E.symm q)).choose.apply_symm_apply] at hh
      change _ = intrinsicFutureDartArc S q (φ q t)
      change intrinsicFutureDartArc S (E (E.symm q)) (φ q t) = _ at hh
      exact hh.symm.trans (congrArg (fun d => intrinsicFutureDartArc S d (φ q t))
        (E.apply_symm_apply q))


/-- Helper toward Proposition 3.9: the closure of the winding-positive
component is the weak upper region, including every seam point. -/
theorem uibotCut2_source_closedLeft_eq_upper :
    closure (intrinsicFutureOpenLeft S (D).seam) =
      {z : ℂ | f z.re ≤ z.im} := by
  rw [uibotCut_source_openLeft_eq_upper W H h hpast hp]
  apply Set.Subset.antisymm
  · apply closure_minimal (fun z hz => show f z.re ≤ z.im from le_of_lt hz)
    exact isClosed_le ((seamFun_continuous _ h (H.1 0)).comp
      Complex.continuous_re) Complex.continuous_im
  · intro z hz
    change f z.re ≤ z.im at hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let y : ℂ := z + (ε / 2 : ℝ) * Complex.I
    refine ⟨y, ?_, ?_⟩
    · change f y.re < y.im
      dsimp only [y]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      linarith
    · have hn : ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ = ε / 2 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hε)]
      simpa only [y, dist_self_add_right, hn] using (half_lt_self hε)

/-- Helper toward Proposition 3.9: the code cut vertex set satisfies the
intrinsic closed-side clause on the source map. -/
theorem uibotCut2_source_vertices (v : WholePlaneVertex W) :
    v ∈ m0CutLeftVertices W H (D).seam ↔
      (S).map.pos v ∈ closure (intrinsicFutureOpenLeft S (D).seam) := by
  rw [uibotCut2_source_closedLeft_eq_upper W H h hpast hp]
  exact futureMap_left_vertex_iff_above W H D h (fun _ _ => hp _) hpast v

/-- Helper toward Proposition 3.9: the code cut geometric edge set
satisfies the intrinsic closed-side clause, retaining missing edges. -/
theorem uibotCut2_source_edges (e : WholePlaneEdge W) :
    e ∈ (D).edges ↔
      Set.range ((S).map.arc e) ⊆ closure (intrinsicFutureOpenLeft S (D).seam) := by
  have hr : Set.range ((S).map.arc e) = ((G).arc (e, false)).image :=
    (G).toPlaneGraphDrawing_arc_range (e, false)
  rw [uibotCut2_source_closedLeft_eq_upper W H h hpast hp, hr]
  exact futureMap_left_edge_iff_above W H D h (fun _ _ => hp _) hpast e

/-- Helper toward Proposition 3.9: the code cut internal faces satisfy
the intrinsic open-side clause as actual complementary components. -/
theorem uibotCut2_source_faces (F : (S).map.toPlaneGraphDrawing.Face) :
    (∃ q, uibotCutFaceInRepresentative W H h hpast hp S
      (D39GeomRootedMapIsoV2.refl _ _) q = F) ↔
      F.val ⊆ intrinsicFutureOpenLeft S (D).seam := by
  rw [uibotCut_source_openLeft_eq_upper W H h hpast hp]
  simpa only [D39GeomRootedMapIsoV2.refl, Homeomorph.refl_apply, Set.image_id] using
    uibotCut_face_in_representative W H h hpast hp S
      (D39GeomRootedMapIsoV2.refl _ _) F


/-- Helper toward Proposition 3.9: the code's rightmost outgoing selector
satisfies the intrinsic selector on the source realization. -/
theorem uibotCut2_source_rightmost (v : WholePlaneVertex W) (e : WholePlaneEdge W)
    (he : wholePlaneRightmostOutgoingAt W H v e) :
    intrinsicFutureRightmostOutgoingAt S v e := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  obtain ⟨hpE, hv, k, hk, hb, _, hfirst⟩ := he
  have hk1 : k = 1 := by
    by_contra hn
    exact hfirst 1 (by omega) (by omega) (hp _)
  rw [hk1, pow_one] at hb
  let a := (wholePlaneRotation W H).symm (e, false)
  have hrot := uibotCut2SourceDartEquiv_rotation W H h hpast hp a
  dsimp only [a] at hrot
  erw [Equiv.apply_symm_apply] at hrot
  have hset : {edge : (S).E | ¬ (S).map.missing edge} = Set.univ := by
    ext edge
    exact iff_true_intro (uibotWholePlaneSourceMap_noMissing W H G hp edge)
  refine ⟨(E (e, false)).2, ?_, ?_, E a, ?_, ?_⟩
  · exact (uibotCut2SourceDartEquiv_tail W H h hpast hp (e, false)).mpr
      ⟨Bool.false_ne_true, hpE⟩
  · exact (uibotCut2SourceDartEquiv_vertex W H h hpast hp (e, false)).trans hv
  · rw [hset]
    exact hrot
  · rw [← uibotCut2SourceDartEquiv_flip W H h hpast hp a]
    apply (uibotCut2SourceDartEquiv_tail W H h hpast hp _).mpr
    change ¬ (!a.2) = true ∧ wholePlaneEdgePresent W a.1
    exact ⟨by rw [show a.2 = true from hb]; decide, hp _⟩

/-- Helper toward Proposition 3.9: the code's leftmost incoming selector
satisfies the intrinsic incoming selector on the source realization. -/
theorem uibotCut2_source_leftmost (v : WholePlaneVertex W) (e : WholePlaneEdge W)
    (he : wholePlaneLeftmostIncomingAt W H v e) :
    intrinsicFutureLeftmostIncomingAt S v e := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  obtain ⟨hpE, hv, k, hk, hb, _, hfirst⟩ := he
  have hk1 : k = 1 := by
    by_contra hn
    exact hfirst 1 (by omega) (by omega) (hp _)
  rw [hk1, pow_one] at hb
  let a := (wholePlaneRotation W H).symm (e, true)
  have hrot := uibotCut2SourceDartEquiv_rotation W H h hpast hp a
  dsimp only [a] at hrot
  erw [Equiv.apply_symm_apply] at hrot
  have hset : {edge : (S).E | ¬ (S).map.missing edge} = Set.univ := by
    ext edge
    exact iff_true_intro (uibotWholePlaneSourceMap_noMissing W H G hp edge)
  refine ⟨(E (e, true)).2, ?_, ?_, E a, ?_, ?_⟩
  · change intrinsicFutureAmbientTail S ((E (e, true)).1, !(E (e, true)).2)
    rw [← uibotCut2SourceDartEquiv_flip W H h hpast hp (e, true)]
    exact (uibotCut2SourceDartEquiv_tail W H h hpast hp (e, false)).mpr
      ⟨Bool.false_ne_true, hpE⟩
  · exact (uibotCut2SourceDartEquiv_vertex W H h hpast hp (e, true)).trans hv
  · rw [hset]
    exact hrot
  · apply (uibotCut2SourceDartEquiv_tail W H h hpast hp a).mpr
    change ¬ a.2 = true ∧ wholePlaneEdgePresent W a.1
    exact ⟨by rw [show a.2 = false from hb]; decide, hp _⟩


/-- Helper toward Proposition 3.9: with all ambient edges present, cut
missingness on the entire ambient edge carrier is exactly the left ray. -/
theorem uibotCut2_source_missing (e : WholePlaneEdge W) :
    (D).missing e ↔ e ∈ Set.range (D).betaL.edge := by
  constructor
  · rintro (⟨P, n, hn⟩ | hn)
    · have he := (m0Cut_betaL_unique W H h (fun _ _ => hp _) P (D).betaL).2
      exact ⟨n, (congrFun he n).symm.trans hn⟩
    · exact (hn (hp e)).elim
  · rintro ⟨n, hn⟩
    exact Or.inl ⟨(D).betaL, n, hn⟩

/-- Helper toward Proposition 3.9: complete intrinsic source satisfaction.
Rotation is the submap's geometric cyclic successor on retained incidences. -/
@[expose] def uibotCut2Source : IntrinsicFutureCut2 S := by
  let Ctail : (S).E × Bool → Prop := fun d =>
    d.1 ∈ (D).edges ∧ intrinsicFutureAmbientTail S d ∧ ¬ (D).missing d.1
  have hroot : intrinsicFutureAmbientTail S (S).root := ⟨fun hn => hn (hp _), rfl⟩
  have hrootEnds := intrinsicFuture_dart_endpoints_of_tail S (S).root hroot
  have hrv := hrootEnds.choose_spec.1
  have hro := hrootEnds.choose_spec.2
  have hEnd := uibotWholePlaneSourceMap_endpoints W H G hp
  have hrootV : d39GeomRootVertex (S).map (S).root = (D).x 0 :=
    hrv.trans ((hEnd _).1.trans ((D).root_eq h (fun _ _ => hp _)).2.1)
  have hrootO : d39GeomRootOtherVertex (S).map (S).root = (D).x 1 :=
    hro.trans ((hEnd _).2.trans ((D).root_eq h (fun _ _ => hp _)).2.2.1)
  refine {
    vertices := m0CutLeftVertices W H (D).seam
    edges := (D).edges
    faces := Set.range (uibotCutFaceInRepresentative W H h hpast hp S
      (D39GeomRootedMapIsoV2.refl _ _))
    seam := (D).seam
    missing := (D).missing
    tail := Ctail
    rotation := intrinsicFutureRotation S (D).edges
    x := (D).x
    betaRVertex := (D).betaR.vertex
    betaLVertex := (D).betaL.vertex
    betaREdge := (D).betaR.edge
    betaLEdge := (D).betaL.edge
    root_initial := hrootV.symm
    root_terminal := hrootO.symm
    root_tail := hroot
    betaR_start := (D).betaR_start.trans ((D).root_eq h (fun _ _ => hp _)).2.2.1
    betaR_extremal := fun n => uibotCut2_source_rightmost W H h hpast hp _ _
      ((D).betaR.rightmost n)
    betaR_step := ?_
    betaL_start := (D).betaL.endpoint.trans ((D).root_eq h (fun _ _ => hp _)).2.1
    betaL_extremal := fun n => uibotCut2_source_leftmost W H h hpast hp _ _
      ((D).betaL.leftmost n)
    betaL_step := ?_
    seam_iff := futureMap_seam_iff D h (fun _ _ => hp _)
    vertices_iff := uibotCut2_source_vertices W H h hpast hp
    edges_iff := uibotCut2_source_edges W H h hpast hp
    faces_iff := uibotCut2_source_faces W H h hpast hp
    seam_mem := fun _ he => futureMap_seam_mem_edges D he
    ambient_present := fun e _ hn => hn (hp e)
    missing_iff := uibotCut2_source_missing W H h hp
    present_iff := futureMap_present_edges_iff D h (fun _ _ => hp _)
    tail_iff := fun _ => Iff.rfl
    missing_unoriented := fun _ hm =>
      ⟨fun ht => ht.2.2 hm, fun ht => ht.2.2 hm⟩
    root_not_missing := ((D).root_eq h (fun _ _ => hp _)).2.2.2.2.1
    cut_root_tail := ⟨futureMap_seam_mem_edges D (Or.inl rfl), hroot,
      ((D).root_eq h (fun _ _ => hp _)).2.2.2.2.1⟩
    rotation_iff := fun _ _ => Iff.rfl
    x_injective := m0CutData_x_injective W H h (fun _ _ => hp _)
    x_range := ?_
    x_mem := futureMap_label_mem_vertices D h (fun _ _ => hp _)
    x_right := ?_
    x_left := ?_
    acyclic := ?_
    internal_triangles := fun F _ => uibotWholePlaneSourceDirectedMap_faceDegree
      W H h hpast hp F }
  · intro n
    exact ⟨fun hn => hn (hp _), (hEnd _).1.trans ((D).betaR.rightmost n).2.1,
      (hEnd _).2.trans ((D).betaR.target n)⟩
  · intro n
    exact ⟨fun hn => hn (hp _), (hEnd _).2.trans ((D).betaL.leftmost n).2.1,
      (hEnd _).1.trans ((D).betaL.westEndpoint n)⟩
  · change Set.range (D).x = {v : WholePlaneVertex W | ∃ e : WholePlaneEdge W,
      (D).seam e ∧ ((S).map.src e = v ∨ (S).map.tgt e = v)}
    rw [futureMap_label_range D h (fun _ _ => hp _)]
    ext v
    apply exists_congr
    intro e
    apply and_congr_right
    intro _
    have he := hEnd e
    exact (or_congr (Iff.of_eq (congrArg (fun u => u = v) he.1.symm))
      (Iff.of_eq (congrArg (fun u => u = v) he.2.symm))).trans
        (intrinsicFutureCut2_endpoints_iff S e (fun hn => hn (hp e)) v)
  · intro n
    exact ((D).x_eq h (fun _ _ => hp _) _).trans
      (m0Cut_betaR_vertices W H h (D).betaR (D).betaR_start n).symm
  · intro n
    exact ((D).x_eq h (fun _ _ => hp _) _).trans
      (m0Cut_betaL_vertices W H h (fun _ _ => hp _) (D).betaL n).symm
  · intro v hcycle
    have hacyc := (uibotWholePlaneSourceDirectedMap_bipolarTriangulation W H h hpast hp).2.1.1
    apply hacyc v
    apply Relation.TransGen.mono ?_ v v hcycle
    rintro u w ⟨d, hd, hu, hw⟩
    obtain ⟨he, ht, hh⟩ := intrinsicFuture_dart_endpoints_of_tail S d hd.2.1
    exact ⟨d.1, ht.symm.trans hu, hh.symm.trans hw⟩


/-- Helper toward Proposition 3.9: source dart conversion transports any
topological star relation, including a star restricted to cut edges. -/
theorem uibotCut2_source_topological_map (star : Set (WholePlaneDart W))
    {d a : WholePlaneDart W}
    (ht : D39TopologicalCcwSuccessor star (fun q t => ((G).arc q).toPath t) d a) :
    D39TopologicalCcwSuccessor (uibotCut2SourceDartEquiv W H h hpast hp '' star)
      (fun q t => intrinsicFutureDartArc S q t)
      (uibotCut2SourceDartEquiv W H h hpast hp d)
      (uibotCut2SourceDartEquiv W H h hpast hp a) := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  have hm := d39TopologicalCcwSuccessor_map_equiv E ht
  have hparam := uibotCut2SourceDartEquiv_arc_param W H h hpast hp
  let φ := fun q => (hparam (E.symm q)).choose.symm
  apply d39TopologicalCcwSuccessor_map_orientedHomeomorph _ _ _
    φ (E d) (E a) (Homeomorph.refl ℂ) orientationPreserving_refl ?_ ?_ hm
  · intro q _ x y hxy
    apply (hparam (E.symm q)).choose_spec.1.lt_iff_lt.mp
    simpa only [φ, Homeomorph.apply_symm_apply] using hxy
  · intro q _ t
    have hh := (hparam (E.symm q)).choose_spec.2 (φ q t)
    dsimp only [φ] at hh
    rw [(hparam (E.symm q)).choose.apply_symm_apply] at hh
    change intrinsicFutureDartArc S (E (E.symm q)) (φ q t) = _ at hh
    exact hh.symm.trans (congrArg (fun b => intrinsicFutureDartArc S b (φ q t))
      (E.apply_symm_apply q))

/-- Helper toward Proposition 3.9: rotation in run zero is the cyclic
successor on the retained geometric star of the source cut. -/
theorem uibotCut2_source_cut_rotation (d : ℕ × Bool) :
    intrinsicFutureRotation S (D).edges
      (uibotCut2SourceDartEquiv W H h hpast hp
        (wholePlaneDartι W 0 (kmswInfRot (shiftedStream W 0) (H.1 0) d)))
      (uibotCut2SourceDartEquiv W H h hpast hp (wholePlaneDartι W 0 d)) := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  let ι := wholePlaneDartι W 0
  let R := kmswInfRot (shiftedStream W 0) (H.1 0)
  let P := monotoneFamilyDrawing (shiftedStream W 0) (H.1 0)
    (monotone_family_all (shiftedStream W 0))
  have hi : Function.Injective ι := (futureMap_dart_coordinates W H D h (fun _ _ => hp _)).1
  have hmem (q : ℕ × Bool) : ι q ∈ (D).darts := by
    rw [(D).darts_eq h (fun _ _ => hp _)]
    exact Set.mem_range_self q
  have hv := uibotCut2SourceDartEquiv_vertex W H h hpast hp
  have hstar :
      E '' (ι '' {q | kmswLimitDartVertex (shiftedStream W 0) q =
        kmswLimitDartVertex (shiftedStream W 0) d}) =
      {q : (S).E × Bool | q.1 ∈ (D).edges ∧
        d39GeomRootVertex (S).map q = d39GeomRootVertex (S).map (E (ι (R d)))} := by
    ext q
    obtain ⟨q, rfl⟩ := E.surjective q
    rw [E.injective.mem_set_image]
    change (q ∈ ι '' _) ↔ q ∈ (D).darts ∧
      d39GeomRootVertex (S).map (E q) = d39GeomRootVertex (S).map (E (ι (R d)))
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨hmem b, ?_⟩
      erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι,
        kmswLimitDartVertex_rot]
      exact congrArg (wholePlaneVertexι W 0) hb
    · rintro ⟨hq, hvq⟩
      rw [(D).darts_eq h (fun _ _ => hp _)] at hq
      obtain ⟨b, rfl⟩ := hq
      refine ⟨b, ?_, rfl⟩
      erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι,
        kmswLimitDartVertex_rot] at hvq
      exact wholePlaneVertexι_injective W 0 hvq
  have ht := DirectedDistances.PaperProofs.Section5.plDrawing_toPath_rotation_topological_ccwSuccessor P d
  have himage := intrinsicFutureCut2_topological_image ι hi
    {q | kmswLimitDartVertex (shiftedStream W 0) q = kmswLimitDartVertex (shiftedStream W 0) d}
    (fun q t => (P.arc q).toPath t) (fun q t => ((G).arc q).toPath t)
    (fun q t => congrArg (fun p : Polyline => p.toPath t)
      (WholePlanePastGlueM0Restriction.restrict_arc W h hpast H q)) ht
  have hm := uibotCut2_source_topological_map W H h hpast hp _ himage
  change D39TopologicalCcwSuccessor (E '' (ι '' _))
    (fun q t => intrinsicFutureDartArc S q t) (E (ι d)) (E (ι (R d))) at hm
  rw [hstar] at hm
  refine ⟨hmem (R d), hmem d, ?_, hm⟩
  erw [hv, hv, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι,
    kmswLimitDartVertex_rot]


/-- Helper toward Proposition 3.9: the intrinsic submap rotation is
exactly IsRot restricted to cut darts; no outside starting dart is admitted. -/
theorem uibotCut2_source_rotation_iff (d a : WholePlaneDart W) :
    (uibotCut2Source W H h hpast hp).rotation
      (uibotCut2SourceDartEquiv W H h hpast hp d)
      (uibotCut2SourceDartEquiv W H h hpast hp a) ↔
      d ∈ (D).darts ∧ a ∈ (D).darts ∧ (D).IsRot d a := by
  let E := uibotCut2SourceDartEquiv W H h hpast hp
  let ι := wholePlaneDartι W 0
  let R := kmswInfRot (shiftedStream W 0) (H.1 0)
  have hi : Function.Injective ι := (futureMap_dart_coordinates W H D h (fun _ _ => hp _)).1
  change intrinsicFutureRotation S (D).edges (E d) (E a) ↔ _
  constructor
  · intro hr
    have hd : d ∈ (D).darts := hr.1
    have ha : a ∈ (D).darts := hr.2.1
    refine ⟨hd, ha, ?_⟩
    rw [(D).darts_eq h (fun _ _ => hp _)] at hd ha
    obtain ⟨d0, rfl⟩ := hd
    obtain ⟨a0, rfl⟩ := ha
    have hf := uibotCut2_source_cut_rotation W H h hpast hp a0
    have hcenter : d39GeomRootVertex (S).map (E (ι (R a0))) =
        d39GeomRootVertex (S).map (E (ι d0)) :=
      hf.2.2.1.symm.trans hr.2.2.1
    have ht := hf.2.2.2
    change D39TopologicalCcwSuccessor
      {q : (S).E × Bool | q.1 ∈ (D).edges ∧
        d39GeomRootVertex (S).map q = d39GeomRootVertex (S).map (E (ι (R a0)))}
      (fun q t => intrinsicFutureDartArc S q t) (E (ι a0)) (E (ι (R a0))) at ht
    rw [hcenter] at ht
    have heq := DirectedDistances.PaperProofs.Section5.d39TopologicalCcwSuccessor_unique
      hr.2.2.2 ht
    have hq : d0 = R a0 := hi (E.injective heq)
    have ha0 : a0 = R.symm d0 :=
      (R.symm_apply_apply a0).symm.trans (congrArg R.symm hq.symm)
    apply (futureMap_rotation_iff D h (fun _ _ => hp _) d0 (ι a0)).mpr
    exact congrArg ι ha0
  · rintro ⟨hd, _, hr⟩
    rw [(D).darts_eq h (fun _ _ => hp _)] at hd
    obtain ⟨d0, rfl⟩ := hd
    have ha := (futureMap_rotation_iff D h (fun _ _ => hp _) d0 a).mp hr
    subst a
    have hf := uibotCut2_source_cut_rotation W H h hpast hp (R.symm d0)
    change intrinsicFutureRotation S (D).edges (E (ι (R (R.symm d0))))
      (E (ι (R.symm d0))) at hf
    rw [R.apply_symm_apply] at hf
    exact hf

/-- Helper toward Proposition 3.9: the source cut tail is exactly the
code tail restricted to retained geometric darts. -/
theorem uibotCut2_source_tail_iff (d : WholePlaneDart W) :
    (uibotCut2Source W H h hpast hp).tail
      (uibotCut2SourceDartEquiv W H h hpast hp d) ↔
      d ∈ (D).darts ∧ (D).tail d := by
  change (d.1 ∈ (D).edges ∧
    intrinsicFutureAmbientTail S (uibotCut2SourceDartEquiv W H h hpast hp d) ∧
    ¬ (D).missing d.1) ↔ _
  rw [uibotCut2SourceDartEquiv_tail W H h hpast hp d]
  rfl

/-- Helper toward Proposition 3.9: every rooted geometric representative
receives the source cut with all image fields and guarded code rotation. -/
theorem uibotCut2_in_representative (A : D39DomainRootedMap.{0})
    (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
      (uibotWholePlaneSourceRoot W H G) A.map A.root) :
    let J := intrinsicFutureDartEquiv (A := S) I
    ∃ C : IntrinsicFutureCut2 A,
      C.vertices = I.vertexEquiv '' m0CutLeftVertices W H (D).seam ∧
      C.edges = I.edgeEquiv '' (D).edges ∧
      C.faces = Set.range (uibotCutFaceInRepresentative W H h hpast hp A I) ∧
      (∀ e, C.seam (I.edgeEquiv e) ↔ (D).seam e) ∧
      (∀ e, C.missing (I.edgeEquiv e) ↔ (D).missing e) ∧
      (∀ d, C.tail (J (uibotCut2SourceDartEquiv W H h hpast hp d)) ↔
        d ∈ (D).darts ∧ (D).tail d) ∧
      (∀ d a, C.rotation (J (uibotCut2SourceDartEquiv W H h hpast hp d))
        (J (uibotCut2SourceDartEquiv W H h hpast hp a)) ↔
        d ∈ (D).darts ∧ a ∈ (D).darts ∧ (D).IsRot d a) ∧
      (∀ k, C.x k = I.vertexEquiv ((D).x k)) ∧
      (∀ n, C.betaRVertex n = I.vertexEquiv ((D).betaR.vertex n) ∧
        C.betaLVertex n = I.vertexEquiv ((D).betaL.vertex n) ∧
        C.betaREdge n = I.edgeEquiv ((D).betaR.edge n) ∧
        C.betaLEdge n = I.edgeEquiv ((D).betaL.edge n)) := by
  dsimp only
  obtain ⟨C, hv, he, hF, hs, hm, ht, hr, hx, hb⟩ :=
    intrinsicFutureCut2_pushforward (A := S) (B := A) I (uibotCut2Source W H h hpast hp)
  refine ⟨C, hv, he, ?_, hs, hm, ?_, ?_, hx, hb⟩
  · rw [hF]
    change I.faceEquiv '' Set.range
      (uibotCutFaceInRepresentative W H h hpast hp S (D39GeomRootedMapIsoV2.refl _ _)) = _
    erw [← Set.range_comp]
    apply congrArg Set.range
    funext q
    apply Subtype.ext
    change (I.faceEquiv (uibotCutFaceInRepresentative W H h hpast hp S
      (D39GeomRootedMapIsoV2.refl _ _) q)).val = _
    erw [I.faceEquiv_val, uibotCutFaceInRepresentative_val,
      uibotCutFaceInRepresentative_val]
    change I.h '' (id '' _) = I.h '' _
    rw [Set.image_id]
  · intro d
    exact (ht _).trans (uibotCut2_source_tail_iff W H h hpast hp d)
  · intro d a
    exact (hr _ _).trans (uibotCut2_source_rotation_iff W H h hpast hp d a)

end Source


/- same recovered witnesses work for every representative and every rooted
geometric source isomorphism. All cut marks and restricted rotations agree. -/
theorem uibotCut2_sample_realization :
    ∀ᵐ U ∂DirectedDistances.RandomWalk.wholePlaneIIDCodeMeasure,
      let z := uibotMeasurableWholePlaneClassMap uibotDeterministicComparison_proved U
      let W := uibotRecoveredCode z
      ∃ (H : WholePlaneRotationHypothesis W)
        (h : BoundaryHitWitnesses (shiftedStream W 0))
        (hpast : BoundaryHitWitnesses (kmswPastCode W))
        (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
      let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
      let D := m0CutData W H h (fun _ _ => hp _)
      ∀ A : D39DomainRootedMap.{0}, Quotient.mk d39DomainSetoid A = z →
        Nonempty (D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root) ∧
        ∀ I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
          (uibotWholePlaneSourceRoot W H G) A.map A.root,
        let J := fun d => intrinsicFutureDartEquiv
          (A := uibotWholePlaneSourceDomain W H G hp) I
          (uibotCut2SourceDartEquiv W H h hpast hp d)
        ∃ C : IntrinsicFutureCut2 A,
          C.vertices = I.vertexEquiv '' m0CutLeftVertices W H D.seam ∧
          C.edges = I.edgeEquiv '' D.edges ∧
          C.faces = Set.range (uibotCutFaceInRepresentative W H h hpast hp A I) ∧
          (∀ e, C.seam (I.edgeEquiv e) ↔ D.seam e) ∧
          (∀ e, C.missing (I.edgeEquiv e) ↔ D.missing e) ∧
          (∀ d, C.tail (J d) ↔ d ∈ D.darts ∧ D.tail d) ∧
          (∀ d a, C.rotation (J d) (J a) ↔
            d ∈ D.darts ∧ a ∈ D.darts ∧ D.IsRot d a) ∧
          (∀ k, C.x k = I.vertexEquiv (D.x k)) ∧
          (∀ n, C.betaRVertex n = I.vertexEquiv (D.betaR.vertex n) ∧
            C.betaLVertex n = I.vertexEquiv (D.betaL.vertex n) ∧
            C.betaREdge n = I.edgeEquiv (D.betaR.edge n) ∧
            C.betaLEdge n = I.edgeEquiv (D.betaL.edge n)) := by
  filter_upwards [uibotIntrinsicCut_sample_realization] with U hU
  dsimp only at hU ⊢
  obtain ⟨_, _, H, h, hpast, hp, _, hrep, _⟩ := hU
  refine ⟨H, h, hpast, hp, ?_⟩
  intro A hA
  exact ⟨hrep A hA, fun I => uibotCut2_in_representative _ H h hpast hp A I⟩


/- REMAINING OPTIONAL TARGET (comment only; no assumed premise):
uniqueness among all intrinsically characterized cuts, rather than only the
constructed images. The forward source selector lemmas do not by themselves
show that every intrinsic extremal ray is the corresponding code ray.

  ∀ (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (h : BoundaryHitWitnesses (shiftedStream W 0))
    (hpast : BoundaryHitWitnesses (kmswPastCode W))
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e),
    let G := WholePlanePastGlueDrawing.glueDrawing W h hpast H
    ∀ (A : D39DomainRootedMap.{0})
      (I : D39GeomRootedMapIsoV2 (uibotWholePlaneSourceMap W H G hp)
        (uibotWholePlaneSourceRoot W H G) A.map A.root)
      (C C' : IntrinsicFutureCut2 A), C = C'

coordinator. These helpers make no qualifier-removal or paper-completion claim. -/

end DirectedDistances.PaperProofs.Section3
end

