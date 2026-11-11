module

public import DirectedDistances.PaperProofs.Section4.ThinCutHalfTruncateAssembly
public import DirectedDistances.PaperProofs.Section4.SelectedCutGeodesicPrefix
import DirectedDistances.KMSW.InfiniteGeodesicAE
import DirectedDistances.KMSW.CutVertexDisconnects

/-! Helper toward Proposition 4.7 (prop-thin-ind); not a paper result. -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open scoped Classical

local notation "Ω" => (ℕ → ℤ × ℤ)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Both infinite extremal paths exist pointwise on the existing coherent domain. -/
theorem selectedCutCoherentDomain_infinite_extremal
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) :
    let w := boltzmannKMSWStream (pathCode q.1)
    (∃ P : InfinitePresentPath w ⟨0⟩, P.HasLongestSegments) ∧
      (∃ P : InfinitePresentPath w ⟨0⟩, P.HasShortestSegments) := by
  obtain ⟨_, _, _, _, _, hfin, htrans, hR, hL, hinf, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  let w := boltzmannKMSWStream (pathCode q.1)
  let S : Set ℕ := {n | (∀ j < n, R w n ≤ R w j - 1) ∧
    ∀ j, n ≤ j → L w n ≤ L w j}
  have hsub : {v : ℕ | mapCutVertex w hfin v} ⊆ activeInitial w '' S := by
    intro v hv
    obtain ⟨n, hnv, _, hA, hB, _⟩ :=
      mapCutVertex_firstVisit_records w hfin htrans hR hL hv
    exact ⟨n, ⟨hA, hB⟩, hnv.symm⟩
  have hS : S.Infinite := by
    intro hf
    exact (hinf.mono hsub) (hf.image (activeInitial w))
  exact infinite_records_exists_source_extremal w hS (zero_mem_records_of_L_nonneg w hL)

private theorem selectedCut_success_of_threshold
    (x : XDP) (T : ℕ → (ℕ → ℤ × ℤ) → ℕ∞)
    (hT : ∀ p m, DirectedDistances.RandomWalk.IsPositiveSuccessTime
      (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    literalSuccessGraph q.1 (selectedCutTime T (k + 1) q.1).toNat := by
  open DirectedDistances.RandomWalk in
  obtain ⟨_, hl, hf, _⟩ := selectedCutCoherentDomain_spec x T hT q
  let r := selectedCutRank T (k + 1) q.1
  have hz : T 0 q.1 = 0 :=
    (DirectedDistances.RandomWalk.isPositiveSuccessTime_zero_iff _ _).mp (hT q.1 0)
  have hs : selectedCutTime T (k + 1) q.1 = T r q.1 := by
    rw [selectedCutTime, dite_eq_left (hf (k + 1))]
  have hle : T r q.1 ≤ conditionedSecondCoordinateFirstHit (k + 1) q.1 := by
    dsimp only [r, selectedCutRank]
    apply Nat.findGreatest_spec (m := 0)
      (P := fun m => T m q.1 ≤ conditionedSecondCoordinateFirstHit (k + 1) q.1)
    · exact Nat.zero_le _
    · rw [hz]
      exact bot_le
  have hfin : T r q.1 < ⊤ := hle.trans_lt (hf (k + 1))
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have ht0 : selectedCutTime T (k + 1) q.1 = 0 := by rw [hs, hr0, hz]
    rw [ht0] at hk
    have hright := (le_min_iff.mp hk).2
    change (s : ℤ) + 1 ≤ -(q.1 0).2 at hright
    rw [hl.1] at hright
    change (s : ℤ) + 1 ≤ 0 at hright
    omega
  have hc : T r q.1 = ((T r q.1).toNat : ℕ∞) :=
    (ENat.natCast_toNat hfin.ne).symm
  have hspec := hT q.1 r
  rw [hc] at hspec
  rw [hs]
  exact ((DirectedDistances.RandomWalk.isPositiveSuccessTime_natCast_iff _ hr _).mp
    hspec).2.1

private theorem simplePath_dart_eq_first_of_tail_source
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : DirectedMapWithMissing D} {s t : MapVertex M} {k : ℕ}
    (P : SimpleDirectedDartPath M s t k) (hk : 0 < k) {d : D}
    (hd : d ∈ P.darts) (hsource : dartTailVertex M d = s) :
    d = P.darts.get ⟨0, by rw [P.darts_length]; exact hk⟩ := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have hiLt : i.val < k := by simpa [P.darts_length] using i.isLt
  have hstep := P.edge_step i
  have hvertex : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ = s := by
    calc
      P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex M (P.darts.get i) := hstep.2.2.1
      _ = dartTailVertex M d := congrArg (dartTailVertex M) hi
      _ = s := hsource
  have hi0 : i.val = 0 := by
    by_contra hne
    have hget : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
        P.vertices.get ⟨0, by rw [P.vertices_length]; omega⟩ := by
      calc
        _ = s := hvertex
        _ = _ := P.start_vertex.symm
    have hidx := P.vertices_nodup.get_inj_iff.mp hget
    have hval : i.val = 0 := by simpa using congrArg Fin.val hidx
    exact hne hval
  have hifin : i = ⟨0, by rw [P.darts_length]; exact hk⟩ := Fin.ext hi0
  rw [hifin] at hi
  exact hi.symm

private theorem outer_tail_at_source_eq_firstLeft
    {D : Type*} [Fintype D] [DecidableEq D] {ℓ r : ℕ}
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) {d : D}
    (houter : B.map.IsOuter d) (htail : B.map.tail d)
    (hsource : dartTailVertex B.map d = B.source) :
    d = B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos) := by
  have hword : d ∈ B.outerWord.letters :=
    (mem_iff_isOuter B.map B.outerWord B.outerSplit.1 d).mpr houter
  have hcanon : d ∈ canonicalOuterBoundaryDarts B := by
    simpa [canonicalOuterBoundaryDarts] using
      B.outerSplit.2.1.perm.mem_iff.mp hword
  rcases List.mem_append.mp hcanon with hleft | hright
  · exact simplePath_dart_eq_first_of_tail_source B.leftPath
      (Nat.zero_lt_of_lt B.left_length_pos) hleft hsource
  · obtain ⟨x, hx, hxd⟩ := List.mem_map.mp hright
    have hx' : x ∈ B.rightPath.darts := List.mem_reverse.mp hx
    have hxtail : B.map.tail x := by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx'
      rw [← hi]
      exact (B.rightPath.edge_step i).2.1
    have hnot : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv x) :=
      (B.map.tail_iff x (B.noMissingDarts x)).mp hxtail
    exact (hnot (hxd ▸ htail)).elim

private theorem baseMapIso_boundaryDarts
    {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundaryBase D ℓ r)
    (C : BipolarTriangulationWithBoundaryBase E ℓ r)
    (I : DirectedMapWithMissingIso B.map C.map) (a : ThinMapSide) :
    (boundaryDarts B a).map I.toEquiv = boundaryDarts C a := by
  let d := B.leftPath.firstDart (Nat.zero_lt_of_lt B.left_length_pos)
  have hd : d ∈ B.leftPath.darts := List.get_mem _ _
  have hstep := B.leftPath.edge_step
    ⟨0, by rw [B.leftPath.darts_length]; exact B.left_length_pos⟩
  have htail : B.map.tail d := hstep.2.1
  have hsource : dartTailVertex B.map d = B.source :=
    hstep.2.2.1.symm.trans B.leftPath.start_vertex
  have houter : B.map.IsOuter d := canonicalOuterBoundaryDarts_mem_isOuter B
    (List.mem_append.mpr (Or.inl hd))
  have hfirst : I.toEquiv d =
      C.leftPath.firstDart (Nat.zero_lt_of_lt C.left_length_pos) := by
    apply outer_tail_at_source_eq_firstLeft C ((I.outer_iff d).mpr houter)
      ((I.tail_iff d).mpr htail)
    rw [← bipolarBaseVertexEquiv_dartTailVertex B C I.toEquiv I.rot_comm d,
      hsource]
    exact bipolarBaseVertexEquiv_source B C I.toEquiv I.rot_comm
      I.edgeInv_comm I.tail_iff
  have hp := bipolarBoundaryPaths_map_of_firstLeft B C I.toEquiv I.rot_comm
    I.edgeInv_comm hfirst
  cases a with
  | left => exact hp.1
  | right => exact hp.2

private theorem selectedCutRep_boundary_stage
    {ℓ r t : ℕ} {w : ℕ → Fin 3} (ht : 1 ≤ t)
    (c : KMSWWalkClass ℓ r t) (hc : ∀ i < t - 1, codeExtend c i = w i)
    (R : KMSWMapRep ℓ r t)
    (I : DirectedMapWithMissingIso R.B.map (kmswStageDirectedMap w (t - 1)))
    (a : ThinMapSide) :
    (boundaryDarts R.B a).map
      (fun d => ((I.toEquiv d).1.val, (I.toEquiv d).2)) =
        (match a with
          | .left => (kmswStage w (t - 1)).UL
          | .right => (kmswStage w (t - 1)).LR).map (fun e => (e, false)) := by
  let E := kmswStageDirectedMapIsoOfPrefix (codeExtend c) w (t - 1) hc
  let J := kmswWalkClassRep_mapIso ht c
  let G := I.trans (E.symm.trans J.symm)
  have hb := baseMapIso_boundaryDarts R.B (kmswWalkClassRep ht c).B G a
  have hj : ∀ d, ((E.toEquiv d).1.val, (E.toEquiv d).2) = (d.1.val, d.2) := by
    intro d
    exact Prod.ext (kmswStageDirectedMapIsoOfPrefix_val _ _ _ hc d).1
      (kmswStageDirectedMapIsoOfPrefix_val _ _ _ hc d).2
  have hmap (d) : I.toEquiv d = E.toEquiv (J.toEquiv (G.toEquiv d)) := by
    simp [G, DirectedMapWithMissingIso.trans, DirectedMapWithMissingIso.symm]
  have hstage := kmswStage_eq_of_prefix (codeExtend c) w (t - 1) hc
  calc
    _ = (boundaryDarts R.B a).map
        (fun d => let e := J.toEquiv (G.toEquiv d); (e.1.val, e.2)) := by
      apply List.map_congr_left
      intro d _
      rw [hmap]
      exact hj _
    _ = (boundaryDarts (kmswWalkClassRep ht c).B a).map
        (fun d => let e := J.toEquiv d; (e.1.val, e.2)) := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun d => let e := J.toEquiv d; (e.1.val, e.2))) hb
    _ = _ := by
      rw [cut_walkClassRep_boundary_stage ht c a, hstage]
      rfl

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
Every actual representative of a good selected cut has a stopped walk class with
exactly its boundary parameters and the actual past code prefix. -/
theorem selectedCutRep_exists_walkClass
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2))
    {ℓ d : ℕ}
    (R : KMSWMapRep ℓ
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
      (selectedCutTime T (k + 1) q.1).toNat)
    (hR : xdpLengthBase R.B x = d)
    (hc : selectedCutPastCuts x T (k + 1) q.1 =
      (some ⟨d, ⟨ℓ, ⟨(cutLRep R hR).1, KMSWMapIsoClass.mk (cutLRep R hR).2⟩⟩⟩,
       some ⟨_, ⟨d, ⟨(cutRRep R hR).1, KMSWMapIsoClass.mk (cutRRep R hR).2⟩⟩⟩)) :
    ∃ c : KMSWWalkClass ℓ
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2).toNat
      (selectedCutTime T (k + 1) q.1).toNat,
      ∀ i < (selectedCutTime T (k + 1) q.1).toNat - 1,
        codeExtend c i = boltzmannKMSWStream (pathCode q.1) i := by
  let w := boltzmannKMSWStream (pathCode q.1)
  let t := (selectedCutTime T (k + 1) q.1).toNat
  let r := (-(q.1 t).2).toNat
  obtain ⟨hr, htau, hE⟩ := selectedCut_stopped_time x T hT q k s hk
  have hrpos : 1 ≤ r := by
    have hr' : s + 1 ≤ r := hr
    omega
  have hout := firstHitPastAllCuts_representative_boundary_stageIso
    x r hrpos (pathCode q.1) hE
  dsimp only at hout
  rw [htau] at hout
  obtain ⟨R₀, d₀, hR₀, _, _, hc₀⟩ := hout
  have hcuts : selectedCutPastCuts x T (k + 1) q.1 =
      (some ⟨d₀, ⟨(L w t).toNat,
        ⟨(cutLRep R₀ hR₀).1, KMSWMapIsoClass.mk (cutLRep R₀ hR₀).2⟩⟩⟩,
       some ⟨r, ⟨d₀, ⟨(cutRRep R₀ hR₀).1,
         KMSWMapIsoClass.mk (cutRRep R₀ hR₀).2⟩⟩⟩) := by
    change (if h : 1 ≤ r then firstHitPositiveCutEmbedding r
      (firstHitPastAllCuts x r (stoppedMap r h (pathCode q.1))) else (none, none)) = _
    rw [dite_eq_left hrpos, hc₀]
    rfl
  have hell : ℓ = (L w t).toNat := by
    have hh := congrArg (fun z : PositiveCutOutput => z.1.map (fun m => m.2.1))
      (hc.symm.trans hcuts)
    exact Option.some.inj hh
  have hclass : ∃ c : KMSWWalkClass (L w t).toNat r t,
      ∀ i < t - 1, codeExtend c i = w i := by
    have htau' : boltzmannTau r (pathCode q.1) = t := htau
    rw [← htau']
    let c : KMSWWalkClass
        (L w (boltzmannTau r (pathCode q.1))).toNat r
        (boltzmannTau r (pathCode q.1)) :=
      ⟨stoppedWord r (pathCode q.1),
        (stoppedWord_admissible r hrpos (pathCode q.1) hE).1⟩
    refine ⟨c, ?_⟩
    intro i hi
    exact (codeExtend_of_lt c i hi).trans rfl
  change ∃ c : KMSWWalkClass ℓ r t, ∀ i < t - 1, codeExtend c i = w i
  rw [hell]
  exact hclass

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
A good selected cut has positive time and the exact strict-right and future-left
record conditions used by the common-prefix theorem. -/
theorem selectedCut_good_record
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) (k s : ℕ)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    let w := boltzmannKMSWStream (pathCode q.1)
    let t := (selectedCutTime T (k + 1) q.1).toNat
    1 ≤ t ∧ (∀ j < t, R w t ≤ R w j - 1) ∧
      (∀ j, t ≤ j → L w t ≤ L w j) := by
  obtain ⟨_, _, _, _, hwp, _⟩ := selectedCutCoherentDomain_spec x T hT q
  have hs := selectedCut_success_of_threshold x T hT q k s hk
  have hb := selectedCut_boundary_indices_before x T hT q k s hk
  refine ⟨by have h := hb.1.1; omega, ?_, ?_⟩
  · intro j hj
    simpa only [kmsw_R_eq, hwp] using hs.1 j hj
  · intro j hj
    simpa only [kmsw_L_eq, hwp] using hs.2 j hj

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The common-prefix family holds for every actual representative and stage isomorphism
on the existing coherent domain, with no additional source hypotheses. -/
theorem selectedCutCommonPrefixFamily_holds
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    SelectedCutCommonPrefixFamily x T hT := by
  intro q s k K _ hk hK
  dsimp only
  intro ha ℓ d ℓ' d' R₀ hR S₀ hS I J hc hc'
  obtain ⟨ht, hA, hB⟩ := selectedCut_good_record x T hT q k s hk
  obtain ⟨ht', hA', hB'⟩ := selectedCut_good_record x T hT q K s hK
  obtain ⟨c, hcode⟩ := selectedCutRep_exists_walkClass x T hT q k s hk R₀ hR hc
  obtain ⟨c', hcode'⟩ := selectedCutRep_exists_walkClass x T hT q K s hK S₀ hS hc'
  obtain ⟨_, _, _, _, _, hfin, htrans, hRbound, hL, _⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  obtain ⟨hgL, hgS⟩ := selectedCutCoherentDomain_infinite_extremal x T hT q
  have htt' : (selectedCutTime T (k + 1) q.1).toNat ≤
      (selectedCutTime T (K + 1) q.1).toNat := by omega
  exact selectedCutRep_commonSelectedPrefix htt' ht ht' hA hB hA' hB'
    hfin hL htrans hRbound c hcode R₀ I
    (selectedCutRep_boundary_stage ht c hcode R₀ I)
    c' hcode' S₀ J (selectedCutRep_boundary_stage ht' c' hcode' S₀ J)
    x hR hS hgL hgS

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The actual half truncations satisfy least-good-cut compatibility on the existing -/
theorem halfTruncateCutEqLeastGood_holds
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p)) :
    HalfTruncateCutEqLeastGood x T hT := by
  exact halfTruncateCutEqLeastGood_of_commonPrefixFamily x T hT
    (selectedCutCommonPrefixFamily_holds x T hT)

/-- Helper toward Proposition 4.7 (prop-thin-ind); not a paper result.
The decoder equals the actual selected-cut half truncation at every good cut. -/
theorem thinTruncationAt_decode
    (x : XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (a : ThinMapSide) (s k : ℕ) (q : selectedCutCoherentDomain x T hT)
    (hk : (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) :
    thinTruncationAt x T hT a s q =
      halfTruncate a s (selectedCutSide x T a k q.1) := by
  exact thinTruncationAt_decode_of_commonPrefixFamily x T hT
    (selectedCutCommonPrefixFamily_holds x T hT) a s k q hk

end DirectedDistances.PaperProofs.Section4
