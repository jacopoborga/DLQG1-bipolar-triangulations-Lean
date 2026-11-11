module

public import DirectedDistances.PaperProofs.Section4.ThinMapAncestorRealizationPos
import DirectedDistances.KMSW.LeftmostGeodesicCutSuffix
import DirectedDistances.PaperProofs.Section4.ThinMapSeamSeparationStage









public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3 Filter Quiver
open scoped Classical

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both original exterior boundary lists map to the corresponding uncut boundary. -/
theorem ancestorPos_boundaryDarts_map
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    (boundaryDarts (ancestorPosHalfRep R hR a).B a).map
        (ancestorPosDartMap R hR a) = boundaryDarts R.B a := by
  cases a with
  | left => exact (cutLRep_boundaryDarts_map R hR).1
  | right => exact (cutRRep_boundaryDarts_map R hR).1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both seam boundary lists map to the selected finite path, in their original order. -/
theorem ancestorPos_seamDarts_map
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) :
    (boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a)).map
        (ancestorPosDartMap R hR a) = (selectedGeodesicOfLen R.B x hR).darts := by
  cases a with
  | left => exact (cutLRep_boundaryDarts_map R hR).2
  | right => exact (cutRRep_boundaryDarts_map R hR).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The original boundary target commutes with either concrete half vertex map. -/
theorem ancestorPos_boundaryTarget_map
    {x : XDP} {ℓ r n m : ℕ} (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m) (a : ThinMapSide) (s : ℕ) :
    (boundaryTarget (ancestorPosHalfRep R hR a).B a s).map
        (ancestorPosVertexMap R hR a) = boundaryTarget R.B a s := by
  cases a with
  | left => exact cutLRep_boundaryTarget_map R hR s
  | right => exact cutRRep_boundaryTarget_map R hR s

private theorem positive_path_reachable
    {D : Type*} [Fintype D] [DecidableEq D] {M : DirectedMapWithMissing D}
    {u v : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M u v n) :
    Relation.ReflTransGen M.directedStep u v := by
  have hr (i : ℕ) (hi : i ≤ n) : Relation.ReflTransGen M.directedStep
      (P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩)
      (P.vertices.get ⟨i, by rw [P.vertices_length]; omega⟩) := by
    induction i with
    | zero => exact .refl
    | succ i ih =>
      have hs := P.edge_step ⟨i, by rw [P.darts_length]; omega⟩
      exact (ih (by omega)).tail ⟨P.darts.get ⟨i, by rw [P.darts_length]; omega⟩,
        hs.1, hs.2.1, hs.2.2.1.symm, hs.2.2.2.symm⟩
  simpa only [P.start_vertex, P.end_vertex] using hr n le_rfl

private theorem positive_stage_head_id
    {ℓ r n t : ℕ} {w : ℕ → Fin 3} (R : KMSWMapRep ℓ r n)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (d : Fin R.dartCount) (hd : (I.toEquiv d).2 = false) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map d))).id =
      edgeEast w (I.toEquiv d).1.val := by
  rw [(cutMapIsoVertexEquiv_endpoints I d).2]
  change (stageMapVertex w t (dartTailVertex (kmswStageDirectedMap w t)
    ((kmswStageDirectedMap w t).edgeInv (I.toEquiv d)))).id = _
  rw [stageMapVertex_tail]
  change (if !(I.toEquiv d).2 then (kmswStage w t).east (I.toEquiv d).1.val
    else (kmswStage w t).west (I.toEquiv d).1.val) = _
  rw [hd]
  exact (edge_endpoints_eq w (I.toEquiv d).1.isLt).2

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The finite prefix's terminal vertex has exactly the infinite prefix's permanent ID. -/
theorem ancestorPos_sink_id_of_prefix
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
    (P : InfinitePresentPath w ⟨0⟩) (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    (stageMapVertex w t (cutMapIsoVertexEquiv I R.B.sink)).id =
      (P.initial m).1.id := by
  let Q := selectedGeodesicOfLen R.B x hR
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    have he : R.B.source = R.B.sink := by
      have hs := Q.start_vertex
      have ht := Q.end_vertex
      have hi : (⟨0, by rw [Q.vertices_length]; omega⟩ : Fin Q.vertices.length) =
          ⟨m, by rw [Q.vertices_length]; omega⟩ := Fin.ext hz.symm
      exact hs.symm.trans ((congrArg Q.vertices.get hi).trans ht)
    exact bipolar_source_ne_sink R.B he
  let j : Fin Q.darts.length := ⟨m - 1, by rw [Q.darts_length]; omega⟩
  let d := Q.darts.get j
  have hd : Q.darts[m - 1]? = some d := List.getElem?_eq_getElem j.isLt
  have hh := congrArg (fun ds => ds[m - 1]?) hp
  rw [List.getElem?_map, List.getElem?_map, hd, Option.map_some, Option.map_some,
    List.getElem?_ofFn, dite_eq_left (show m - 1 < m by omega)] at hh
  have hid : (I.toEquiv d).1.val = P.edge (m - 1) := Option.some.inj hh
  have hsink : dartHeadVertex R.B.map d = R.B.sink := by
    have he := (Q.edge_step j).2.2.2
    have hj : j.val + 1 = m := by dsimp [j]; omega
    simpa only [hj, Q.end_vertex] using he.symm
  rw [← hsink, positive_stage_head_id R I d
    (directedPath_stageIso_darts_forward I Q d (List.get_mem _ _)), hid]
  have he := (P.edge_incoming_at_succ w (m - 1)).2
  rwa [Nat.sub_add_cancel hm] at he

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A finite selected-path prefix identifies every seam index, including all indices
beyond its length: a later infinite-path edge cannot occur in the finite stage.
The two hypotheses are explicit finite-path representation data. -/
theorem ancestorPos_seam_iff_of_prefix
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
    (P : InfinitePresentPath w ⟨0⟩) (R : KMSWMapRep ℓ r n)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val))
    (hsink : (stageMapVertex w t (cutMapIsoVertexEquiv I R.B.sink)).id =
      (P.initial m).1.id)
    (a : ThinMapSide) (i : ℕ) (d : Fin (ancestorPosHalfRep R hR a).dartCount) :
    (boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a))[i]? = some d ↔
      (P.edge i, false) = ancestorPosDartId w t R hR I a d := by
  let f := ancestorPosDartId w t R hR I a
  have hf := (ancestorPos_ids_injective w t R hR I a).2
  have hlist : (boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a)).map f =
      List.ofFn (fun j : Fin m => (P.edge j.val, false)) := by
    have hseam := congrArg (List.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) (ancestorPos_seamDarts_map R hR a)
    rw [List.map_map] at hseam
    change _ = _ at hseam
    calc
      _ = (selectedGeodesicOfLen R.B x hR).darts.map
          (fun e => ((I.toEquiv e).1.val, (I.toEquiv e).2)) := hseam
      _ = (((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
          (fun e => e.1.val)).map (fun e => (e, false)) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro e he
        rw [directedPath_stageIso_darts_forward I (selectedGeodesicOfLen R.B x hR) e he]
        rfl
      _ = _ := by rw [hp, List.map_ofFn]; rfl
  have hsmall (hi : i < m) :
      ((boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a))[i]?).map f =
        some (P.edge i, false) := by
    have hh := congrArg (fun ds => ds[i]?) hlist
    simpa only [List.getElem?_map, List.getElem?_ofFn, dite_eq_left hi] using hh
  constructor
  · intro hd
    have hi : i < m := by
      have hlen := congrArg List.length (ancestorPos_seamDarts_map R hR a)
      rw [List.length_map, (selectedGeodesicOfLen R.B x hR).darts_length] at hlen
      have hb' := (List.getElem?_eq_some_iff.mp hd).1
      omega
    have hh := hsmall hi
    rw [hd, Option.map_some] at hh
    exact (Option.some.inj hh).symm
  · intro he
    have hi : i < m := by
      by_contra hn
      have hm : m ≤ i := by omega
      let e := ancestorPosDartMap R hR a d
      have hside : (I.toEquiv e).2 = false :=
        (congrArg Prod.snd he).symm
      have hid : (I.toEquiv e).1.val = P.edge i :=
        (congrArg Prod.fst he).symm
      obtain ⟨N, Q, _⟩ := exists_simple_sink_pathBase R.B (dartHeadVertex R.B.map e)
      have hr := positive_path_reachable Q
      rw [cutMapIsoVertexEquiv_reachable_iff I, ancestorFinal_stage_reachable_iff] at hr
      have hr' := stageToLimit_reachable w t hr
      change Reachable
        (⟨(stageMapVertex w t (cutMapIsoVertexEquiv I (dartHeadVertex R.B.map e))).id⟩ :
          PresentVertex w)
        ⟨(stageMapVertex w t (cutMapIsoVertexEquiv I R.B.sink)).id⟩ at hr'
      rw [positive_stage_head_id R I e hside, hid, hsink,
        (P.edge_incoming_at_succ w i).2] at hr'
      obtain ⟨q⟩ := hr'
      obtain ⟨_, p, _, _, hlen, _⟩ := P.exists_shift_split m (i + 1 - m)
      have hs : m + (i + 1 - m) = i + 1 := by omega
      have hr'' : Reachable (P.initial (m + (i + 1 - m))).1 (P.initial m).1 := by
        rw [hs]
        exact ⟨q⟩
      obtain ⟨q'⟩ := hr''
      have hz := presentVertex_acyclic w _ (p.comp q')
      rw [Path.length_comp, hlen] at hz
      omega
    obtain ⟨e, he', hef⟩ := Option.map_eq_some_iff.mp (hsmall hi)
    exact hf (hef.trans he) ▸ he'

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every retained finite-half face has its actual infinite-map successor. -/
theorem ancestorPos_retained_faceSucc_id
    {x : XDP} {ℓ r n m : ℕ} (w : ℕ → Fin 3) (t : ℕ)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
    (a : ThinMapSide) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)
    (d : Fin (ancestorPosHalfRep R hR a).dartCount)
    (hd : retainedFace (presentation (ancestorPosHalfRep R hR a) a v) d) :
    ancestorPosDartId w t R hR I a
        ((ancestorPosHalfRep R hR a).B.map.toCombinatorialMap.faceSucc d) =
      kmswInfFaceSucc w hfin (ancestorPosDartId w t R hR I a d) := by
  have hinner : ¬ R.B.map.IsOuter (ancestorPosDartMap R hR a d) := by
    cases a with
    | left => exact (cutLRep_retainedFace_map R hR v d hd).1
    | right => exact (cutRRep_retainedFace_map R hR v d hd).1
  have hstage : I.toEquiv (ancestorPosDartMap R hR a d) ∉ stageOuterWord w t := by
    intro ho
    have ho' : (kmswStageDirectedMap w t).IsOuter
        (I.toEquiv (ancestorPosDartMap R hR a d)) :=
      (mem_iff_isOuter _ _ (Section3.kmsw_bdy_source_four_arcs w t).1.1 _).mp ho
    exact hinner ((I.outer_iff _).mp ho')
  have hnext : ancestorPosDartMap R hR a
      ((ancestorPosHalfRep R hR a).B.map.toCombinatorialMap.faceSucc d) =
        R.B.map.toCombinatorialMap.faceSucc (ancestorPosDartMap R hR a d) := by
    cases a with
    | left => exact cutLRep_retainedFace_faceSucc_map R hR v d hd
    | right => exact cutRRep_retainedFace_faceSucc_map R hR v d hd
  have hs := thinMapStage_faceSucc_eq_infinite_of_not_outer w hfin t _ hstage
  dsimp only [ancestorPosDartId, stageLimitDart, Function.Embedding.coeFn_mk]
  have hc : I.toEquiv (R.B.map.toCombinatorialMap.faceSucc
      (ancestorPosDartMap R hR a d)) =
        (kmswMap w t).faceSucc (I.toEquiv (ancestorPosDartMap R hR a d)) := by
    have hr (e : Fin R.dartCount) : I.toEquiv (R.B.map.rot.symm e) =
        (kmswStageDirectedMap w t).rot.symm (I.toEquiv e) := by
      apply (kmswStageDirectedMap w t).rot.injective
      calc
        _ = I.toEquiv (R.B.map.rot (R.B.map.rot.symm e)) := (I.rot_comm _).symm
        _ = I.toEquiv e := congrArg I.toEquiv (Equiv.apply_symm_apply _ e)
        _ = _ := (Equiv.apply_symm_apply _ (I.toEquiv e)).symm
    change I.toEquiv (R.B.map.rot.symm
      (R.B.map.edgeInv (ancestorPosDartMap R hR a d))) =
        (kmswStageDirectedMap w t).rot.symm
          ((kmswStageDirectedMap w t).edgeInv (I.toEquiv (ancestorPosDartMap R hR a d)))
    rw [hr, I.edgeInv_comm]
  rw [hnext, hc]
  exact hs

private theorem positive_retained_selected (H : HalfTruncationRep)
    (d e : Fin H.rep.dartCount) (hd : retainedFace H d)
    (he : Equiv.Perm.SameCycle H.rep.B.map.toCombinatorialMap.faceSucc d e) :
    e ∈ selectedDarts H := by
  refine ⟨hd.2 e he, ?_⟩
  have ht : dartTailVertex H.rep.B.map (H.rep.B.map.toCombinatorialMap.faceSucc e) =
      dartHeadVertex H.rep.B.map e := by
    apply Quotient.sound
    change Equiv.Perm.SameCycle H.rep.B.map.rot
      (H.rep.B.map.rot.symm (H.rep.B.map.edgeInv e)) (H.rep.B.map.edgeInv e)
    exact ⟨1, by simp⟩
  rw [← ht]
  exact hd.2 _ he.apply_right

section RemainingGeometry

variable {x : XDP} (w : ℕ → Fin 3)
  (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
    ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
  (hL : ∀ j, 0 ≤ L w j) (htrans : Tendsto (L w) atTop atTop)
  (hRneg : ∀ z : ℤ, ∃ n, KMSW.R w n ≤ z) (P : InfinitePresentPath w ⟨0⟩)
  {ℓ r n m : ℕ} (t : ℕ) (R : KMSWMapRep ℓ r n)
  (hR : xdpLengthBase R.B x = m)
  (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
  (a : ThinMapSide) (s : ℕ) (v : MapVertex (ancestorPosHalfRep R hR a).B.map)

local notation "H" => presentation (ancestorPosHalfRep R hR a) a v
local notation "f" => ancestorPosDartId w t R hR I a

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining exact dart-image obligation; this proposition is not asserted. -/
@[expose] noncomputable def AncestorPosHalfDartImageIdentification : Prop :=
  f '' selectedDarts H = sourceAncestorDarts w hfin hL htrans hRneg P a s

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The remaining exact retained-face membership obligation, with successor equality
removed. This proposition is isolated and is not asserted to hold. -/
@[expose] noncomputable def AncestorPosHalfFaceMembershipIdentification : Prop :=
  ∀ d : selectedDarts H, retainedFace H d.1 ↔
    sourceAncestorRetainedFace w hfin hL htrans hRneg P a s (f d.1)

private theorem positive_geometric_successor_mem (d : ℕ × Bool)
    (hd : sourceAncestorRetainedFace w hfin hL htrans hRneg P a s d) :
    kmswInfFaceSucc w hfin d ∈ sourceAncestorDarts w hfin hL htrans hRneg P a s := by
  obtain ⟨j, hj, hall⟩ := hd
  apply hall
  have hc := kmswInfFaceSucc_stageTriangle_cycle w hfin j
  simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
  rcases hj with rfl | rfl | rfl
  · exact Or.inr (Or.inl hc.1)
  · exact Or.inr (Or.inr hc.2.1)
  · exact Or.inl hc.2.2.1

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
For an actual finite path prefix, geometric identification is exactly the two
smaller obligations above. Face succession and every seam index require no
further geometric input. Neither remaining obligation is asserted here. -/
theorem ancestorPos_geometricIdentification_iff_of_prefix
    (hp : ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => P.edge j.val)) :
    AncestorPosHalfGeometricIdentification w hfin hL htrans hRneg P t R hR I a s v ↔
      AncestorPosHalfDartImageIdentification w hfin hL htrans hRneg P t R hR I a s v ∧
      AncestorPosHalfFaceMembershipIdentification
        w hfin hL htrans hRneg P t R hR I a s v := by
  have hf := (ancestorPos_ids_injective w t R hR I a).2
  constructor
  · intro hg
    refine ⟨hg.1, ?_⟩
    intro d
    constructor
    · intro hd
      let e : selectedDarts H := ⟨(ancestorPosHalfRep R hR a).B.map.toCombinatorialMap.faceSucc d.1,
        positive_retained_selected H d.1 _ hd (Equiv.Perm.SameCycle.refl _ _).apply_right⟩
      exact ((hg.2.1 d e).mp ⟨hd, rfl⟩).1
    · intro hd
      have hm := positive_geometric_successor_mem w hfin hL htrans hRneg P a s _ hd
      rw [← hg.1] at hm
      obtain ⟨e, he, hef⟩ := hm
      exact ((hg.2.1 d ⟨e, he⟩).mpr ⟨hd, hef.symm⟩).1
  · rintro ⟨himage, hface⟩
    refine ⟨himage, ?_, ?_⟩
    · intro d e
      constructor
      · rintro ⟨hd, he⟩
        refine ⟨(hface d).mp hd, ?_⟩
        exact (ancestorPos_retained_faceSucc_id w t hfin R hR I a v d.1 hd).symm.trans
          (congrArg f he)
      · rintro ⟨hd, he⟩
        have hd' := (hface d).mpr hd
        refine ⟨hd', hf ?_⟩
        exact (ancestorPos_retained_faceSucc_id w t hfin R hR I a v d.1 hd').trans he
    · intro i d
      exact ancestorPos_seam_iff_of_prefix w t P R hR I hp
        (ancestorPos_sink_id_of_prefix w t P R hR I hp) a i d.1

end RemainingGeometry

section SelectedCut

local notation "Ω" => (ℕ → ℤ × ℤ)

variable (x : XDP) (T : ℕ → Ω → ℕ∞)
  (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
  (q : selectedCutCoherentDomain x T hT)

local notation "w" => boltzmannKMSWStream (pathCode (Subtype.val q))
local notation "hfin" => sourceAncestor_finite_incidence x T hT q
local notation "hL" => sourceAncestor_left_nonneg x T hT q
local notation "htrans" => sourceAncestor_left_transient x T hT q
local notation "hRneg" => sourceAncestor_right_unbounded x T hT q
local notation "P" => sourceAncestorPath x T hT q

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual selected path is the indexed prefix of the canonical infinite path.
The representative and its boundary transport are the existing good-cut data. -/
theorem sourceAncestorPosHalf_path_prefix (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    {ℓ m : ℕ}
    (R : KMSWMapRep ℓ
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
      (selectedCutTime T (k + 1) q.1).toNat)
    (hR : xdpLengthBase R.B x = m)
    (I : DirectedMapWithMissingIso R.B.map
      (kmswStageDirectedMap w ((selectedCutTime T (k + 1) q.1).toNat - 1)))
    (hb : ∀ a : ThinMapSide, (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).UL
          | .right => (kmswStage w ((selectedCutTime T (k + 1) q.1).toNat - 1)).LR).map
            (fun e => (e, false)))
    (hc : selectedCutPastCuts x T (k + 1) q.1 =
      (some ⟨m, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨_, ⟨m, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩)) :
    ((selectedGeodesicOfLen R.B x hR).darts.map I.toEquiv).map
      (fun d => d.1.val) = List.ofFn (fun j : Fin m => (P).edge j.val) := by
  obtain ⟨ht, hA, hB⟩ := selectedCut_good_record x T hT q k s hk
  obtain ⟨c, hcode⟩ := selectedCutRep_exists_walkClass x T hT q k s hk R hR hc
  obtain ⟨hgL, hgS⟩ := selectedCutCoherentDomain_infinite_extremal x T hT q
  have hgen (x₀ : XDP) (hR₀ : xdpLengthBase R.B x₀ = m) :
      ((selectedGeodesicOfLen R.B x₀ hR₀).darts.map I.toEquiv).map
        (fun d => d.1.val) = List.ofFn (fun j : Fin m =>
          (match x₀ with
            | .ldp => kmswLeftmostLdpPath w hfin hL htrans hRneg 0 hgL
            | .sdp => kmswLeftmostSdpPath w hfin hL htrans hRneg 0 hgS).edge j.val) := by
    cases x₀ with
    | ldp =>
      obtain ⟨hlen, _, _, _, _, hids⟩ := selectedCutRep_recordStage_edgeIds_eq_ldpPrefix
        ht hA hB hfin hL htrans hRneg c hcode R I hb hgL
      have he : (selectedGeodesicOfLen R.B .ldp hlen).darts.length = m := by
        rw [(selectedGeodesicOfLen R.B .ldp hlen).darts_length, ← hlen, hR₀]
      rw [List.ofFn_congr he] at hids
      simpa only [Fin.val_cast, selectedGeodesicOfLen_darts] using hids
    | sdp =>
      obtain ⟨hlen, _, _, _, _, hids⟩ := selectedCutRep_recordStage_edgeIds_eq_sdpPrefix
        ht hA hB hfin hL htrans hRneg c hcode R I hb hgS
      have he : (selectedGeodesicOfLen R.B .sdp hlen).darts.length = m := by
        rw [(selectedGeodesicOfLen R.B .sdp hlen).darts_length, ← hlen, hR₀]
      rw [List.ofFn_congr he] at hids
      simpa only [Fin.val_cast, selectedGeodesicOfLen_darts] using hids
  let Q (x₀ : XDP) : InfinitePresentPath w ⟨0⟩ := match x₀ with
    | .ldp => kmswLeftmostLdpPath w hfin hL htrans hRneg 0 hgL
    | .sdp => kmswLeftmostSdpPath w hfin hL htrans hRneg 0 hgS
  have hpath : P = Q x := by
    cases x <;> rfl
  rw [hpath]
  exact hgen x hR

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every good cut has the actual half representative with the correct root, target
and all exterior boundary indices below the truncation level. No geometric
dart-image or face identification is assumed or asserted. -/
theorem sourceAncestorPosHalf_boundary_embedding (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    ∃ (ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      selectedCutSide x T a k q.1 =
        some ⟨_, ⟨_, ⟨_, KMSWMapIsoClass.mk (ancestorPosHalfRep R hR a)⟩⟩⟩ ∧
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
      ancestorPosVertexId w t R hR I a (ancestorPosHalfRep R hR a).B.source = 0 ∧
      ancestorPosVertexId w t R hR I a v =
        thinMapBoundaryVertex w hfin hL htrans hRneg a s ∧
      (∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map
        (ancestorPosDartId w t R hR I a) =
          some (thinMapBoundaryDart w hfin hL htrans hRneg a i)) := by
  intro t
  obtain ⟨ℓ, m, R, hR, I, _, _, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_boundary_stageIso x T hT q k s hk
  let F := fun z => (stageMapVertex w t (cutMapIsoVertexEquiv I z)).id
  have htarget : (boundaryTarget R.B a s).map F =
      some (thinMapBoundaryVertex w hfin hL htrans hRneg a s) := by
    rw [ancestor_boundaryVertex_eq]
    have hp := selectedCut_past_boundary_target_record x T hT q a k s hk
    cases s <;> exact (ht a _).trans hp
  have hhalf := congrArg (Option.map F) (ancestorPos_boundaryTarget_map R hR a s)
  rw [Option.map_map, htarget] at hhalf
  obtain ⟨v, hv, hvid⟩ := Option.map_eq_some_iff.mp hhalf
  refine ⟨ℓ, _, _, m, R, hR, I, v, ?_, hv, ?_, hvid, ?_⟩
  · cases a with
    | left => exact congrArg Prod.fst hc
    | right => exact congrArg Prod.snd hc
  · change F (ancestorPosVertexMap R hR a (ancestorPosHalfRep R hR a).B.source) = 0
    rw [ancestorPos_source_map]
    exact Option.some.inj (ht a 0)
  · intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q a k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb a)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (ancestorPos_boundaryDarts_map R hR a)
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    rw [ancestor_boundaryDart_eq]
    exact hm.trans hs

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every good cut has the actual half representative with the correct root and target,
all exterior boundary indices below the truncation level and every seam index. No geometric
dart-image or face identification is assumed or asserted. -/
theorem sourceAncestorPosHalf_boundary_seam_embedding (a : ThinMapSide) (s k : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let t := (selectedCutTime T (k + 1) q.1).toNat - 1
    ∃ (ℓ r n m : ℕ) (R : KMSWMapRep ℓ r n) (hR : xdpLengthBase R.B x = m)
      (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w t))
      (v : MapVertex (ancestorPosHalfRep R hR a).B.map),
      selectedCutSide x T a k q.1 =
        some ⟨_, ⟨_, ⟨_, KMSWMapIsoClass.mk (ancestorPosHalfRep R hR a)⟩⟩⟩ ∧
      boundaryTarget (ancestorPosHalfRep R hR a).B a s = some v ∧
      ancestorPosVertexId w t R hR I a (ancestorPosHalfRep R hR a).B.source = 0 ∧
      ancestorPosVertexId w t R hR I a v =
        thinMapBoundaryVertex w hfin hL htrans hRneg a s ∧
      (∀ i < s, ((boundaryDarts (ancestorPosHalfRep R hR a).B a)[i]?).map
        (ancestorPosDartId w t R hR I a) =
          some (thinMapBoundaryDart w hfin hL htrans hRneg a i)) ∧
      (∀ (i : ℕ) (d : selectedDarts (presentation (ancestorPosHalfRep R hR a) a v)),
        (boundaryDarts (ancestorPosHalfRep R hR a).B (oppositeSide a))[i]? = some d.1 ↔
          ((P).edge i, false) = ancestorPosDartId w t R hR I a d.1) := by
  intro t
  obtain ⟨ℓ, m, R, hR, I, _, _, hb, ht, hc⟩ :=
    selectedCutPastCuts_representatives_boundary_stageIso x T hT q k s hk
  let F := fun z => (stageMapVertex w t (cutMapIsoVertexEquiv I z)).id
  have htarget : (boundaryTarget R.B a s).map F =
      some (thinMapBoundaryVertex w hfin hL htrans hRneg a s) := by
    rw [ancestor_boundaryVertex_eq]
    have hp := selectedCut_past_boundary_target_record x T hT q a k s hk
    cases s <;> exact (ht a _).trans hp
  have hhalf := congrArg (Option.map F) (ancestorPos_boundaryTarget_map R hR a s)
  rw [Option.map_map, htarget] at hhalf
  obtain ⟨v, hv, hvid⟩ := Option.map_eq_some_iff.mp hhalf
  refine ⟨ℓ, _, _, m, R, hR, I, v, ?_, hv, ?_, hvid, ?_, ?_⟩
  · cases a with
    | left => exact congrArg Prod.fst hc
    | right => exact congrArg Prod.snd hc
  · change F (ancestorPosVertexMap R hR a (ancestorPosHalfRep R hR a).B.source) = 0
    rw [ancestorPos_source_map]
    exact Option.some.inj (ht a 0)
  · intro i hi
    have hp := selectedCut_past_boundary_dart_record x T hT q a k s i hk hi
    have hs := congrArg (fun ds => ds[i]?) (hb a)
    rw [List.getElem?_map, List.getElem?_map, hp, Option.map_some] at hs
    have hh := congrArg (fun ds => ds[i]?) (ancestorPos_boundaryDarts_map R hR a)
    rw [List.getElem?_map] at hh
    have hm := congrArg (Option.map (fun e => ((I.toEquiv e).1.val,
      (I.toEquiv e).2))) hh
    rw [Option.map_map] at hm
    rw [ancestor_boundaryDart_eq]
    exact hm.trans hs

  · have hp := sourceAncestorPosHalf_path_prefix x T hT q s k hk R hR I hb hc
    have hsink := ancestorPos_sink_id_of_prefix w t P R hR I hp
    intro i d
    exact ancestorPos_seam_iff_of_prefix w t P R hR I hp hsink a i d.1

end SelectedCut
end DirectedDistances.PaperProofs.Section4
