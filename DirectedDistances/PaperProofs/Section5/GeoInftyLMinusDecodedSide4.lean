/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyLMinusDecodedSide3
public import DirectedDistances.PaperProofs.Section5.GeoInftyNonnegLeftSideBoundaryOrder5
public import DirectedDistances.Recursive.HLRLdpFinal

/-! lower-left creation records, rather than the hatted interface. No
paper-completion claim is made. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5: enumerate the retained primed root, followed
by lower-left creation records in order from that root. `natSelect` is the
existing record enumeration; the finite-word characterization below specifies
its value whenever the indexed record exists. -/
@[expose] noncomputable def lMinusCodeExteriorBoundaryEdge (p : ℕ → Fin 3) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kmswLLCreatedEdge p
      (natSelect (fun m => 0 < m ∧ ∀ j < m, L p m < L p j) i)

/-- Helper toward Lemma 5.5: the exterior boundary uses reversed darts of
the primed root and lower-left records. This reads only the two code blocks;
no actual side or geometric equivalence enters its definition. -/
@[expose] noncomputable def lMinusCodeExteriorBoundaryDart {x : XDP}
    (r : LMinusSidePresentation x) (q : Coherent x) (i : ℕ) :
    LMinusCodeGluedDart r (lMinusCoherentLeftSide x q) :=
  (⟦Sum.inl (lMinusCodeExteriorBoundaryEdge r.code.1 i)⟧, true)

/-- Helper toward Lemma 5.5: the code exterior enumeration agrees with
every allocated finite root/LL word, including its root at index zero. -/
theorem lMinusCodeExteriorBoundaryEdge_stage (p : ℕ → Fin 3) (n i : ℕ)
    (hi : i < (0 :: (kmswStage p n).LL.reverse).length) :
    (0 :: (kmswStage p n).LL.reverse)[i]? =
      some (lMinusCodeExteriorBoundaryEdge p i) := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [List.length_cons, List.length_reverse] at hi
    simp only [List.getElem?_cons_succ, lMinusCodeExteriorBoundaryEdge]
    rw [kmswStage_LL_eq, ← List.map_reverse, List.reverse_reverse, List.getElem?_map]
    let b := fun m => decide (0 < m ∧ ∀ j < m, L p m < L p j)
    have hlen : i < ((List.range (n + 1)).filter b).length := by
      have hh := congrArg List.length (kmswStage_LL_eq p n)
      simp only [List.length_map, List.length_reverse] at hh
      dsimp only [b]
      omega
    have hs := filter_range_getElem?_eq b (n + 1) i hlen
    simp only [b, decide_eq_true_eq] at hs
    rw [hs]
    rfl

/-- Helper toward Lemma 5.5: replace only the boundary field of decoder 2.
The root, seam, directed presence, rotation and face succession are inherited. -/
@[expose] noncomputable def lMinusDecodedSide4
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈
      Coherent (if longest then XDP.ldp else XDP.sdp))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    GeometricSideSubmap :=
  let x := if longest then XDP.ldp else XDP.sdp
  let r := decodeLMinus x k (leftSideObsNonpos x k W)
  let q : Coherent x := ⟨boundaryFutureHattedPath k W, hqMode⟩
  { lMinusDecodedSide2 hτ hqMode hfin with
    boundary := fun i => lMinusCodeDartId r _ (lMinusCodeExteriorBoundaryDart r q i) }

/-- Helper toward Lemma 5.5: all nine non-boundary fields are unchanged. -/
theorem lMinusDecodedSide4_nonboundary_fields
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈
      Coherent (if longest then XDP.ldp else XDP.sdp))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    let A := lMinusDecodedSide4 hτ hqMode hfin
    let B := lMinusDecodedSide2 hτ hqMode hfin
    A.vertices = B.vertices ∧ A.edges = B.edges ∧ A.west = B.west ∧
      A.east = B.east ∧ A.present = B.present ∧ A.rotation = B.rotation ∧
      A.faceNext = B.faceNext ∧ A.root = B.root ∧ A.seam = B.seam :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩



theorem lMinus_LL_reverse_boundary (w : ℕ → Fin 3) (hb : BoundaryHitWitnesses w)
    (n i : ℕ) (hi : i < (kmswStage w n).LL.reverse.length) :
    (kmswStage w n).LL.reverse[i]? =
      some (boundaryOuterEdge w hb (-((i : ℤ) + 1))) := by
  have hin : i + 1 ≤ (kmswStage w n).LL.length := by
    simp only [List.length_reverse] at hi; omega
  have hh := kmswLL_reverse_get_first_hit w n (i + 1) (by omega) hin
  dsimp only at hh
  have ht : boundaryHitTime w hb (-((i : ℤ) + 1)) =
      Nat.find (kmswLL_level_hit w n (i + 1) (by omega) hin) := by
    simp only [boundaryHitTime, dite_eq_right (by omega : -((i : ℤ) + 1) ≠ 0),
      dite_eq_right (by omega : ¬ 0 < -((i : ℤ) + 1))]
  rw [boundaryOuterEdge_of_negative w hb (by omega), ht]
  have he := hh.2.2
  simp only [Nat.add_sub_cancel] at he
  rw [List.getElem?_eq_getElem hi]
  exact congrArg some he

/-- Helper toward Lemma 5.5: at a nonpositive hit the future reversed LL
word maps to the run-zero LL word after its already explored prefix. -/
theorem lMinus_future_LL_word
    {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : k ≤ 0) (n : ℕ) :
    (kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k + n)).LL.reverse =
      (kmswStage (shiftedStream W 0)
        (boundaryHitTime (shiftedStream W 0) h k)).LL.reverse ++
      (kmswStage (boundaryGluingFutureStream W h k) n).LL.reverse.map
        (boundaryGluingEdgeMap W h k) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let u := boundaryGluingFutureStream W h k
  let D := kmswWindowPatchData w t n
  have hr := kmswWindowPatchData_rel w t n
  change KMSWWindowPatchRel (kmswStage w t) (kmswStage w (t + n))
    (kmswStage u n) D.φ D.A D.B D.YL D.YR D.XL D.XR at hr
  have hA : (kmswStage w t).UL.dropLast = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have hm : e ∈ boundaryGluingUpperLeftEdges W h k := he
    rw [boundaryGluingUpperLeftEdges_of_nonpos W h k hk] at hm
    exact hm
  have hy : D.YL = [] := by
    have hh := hr.left_residual.symm.trans hA
    exact List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp hh).2
  have hxl : (kmswStage u n).LL = D.XL := by
    simpa only [hy, List.append_nil] using hr.ll_split
  have hh := congrArg List.reverse hr.ll
  rw [List.reverse_append, ← List.map_reverse, ← hxl] at hh
  refine hh.trans ?_
  congr 1
  apply List.map_congr_left
  intro e he
  have hb : e < (kmswStage u n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge u n).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_reverse.mp he)))
  exact (kmswWindowEdgeMapInf_eq_stage w t n e hb).symm

/-- Helper toward Lemma 5.5: the explored LL prefix has exactly `-k`
edges at a nonpositive hit, also at zero. -/
theorem lMinus_initial_LL_length
    {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : k ≤ 0) :
    ((kmswStage (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h k)).LL.length : ℤ) = -k := by
  by_cases hz : k = 0
  · subst k
    rw [boundaryHitTime_zero]
    rfl
  have hs := (leftHit_UL_singleton_and_west_endpoint
    (shiftedStream W 0) h (by omega : k ≤ -1)).1
  have hl := congrArg List.length hs
  simp only [List.length_singleton] at hl
  have hUL := kmswStage_UL_length (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)
  have hLL := kmswStage_LL_length (shiftedStream W 0)
    (boundaryHitTime (shiftedStream W 0) h k)
  have hh := boundaryHitTime_left_spec (shiftedStream W 0) h (by omega : k ≤ -1)
  rw [hl] at hUL
  omega

/-- Helper toward Lemma 5.5: every allocated future LL entry maps to the
exterior boundary at exactly `k - 1 - i`. -/
theorem lMinus_future_LL_index
    {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : k ≤ 0) (n i e : ℕ)
    (he : (kmswStage (boundaryGluingFutureStream W h k) n).LL.reverse[i]? = some e) :
    boundaryGluingEdgeMap W h k e =
      boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)) := by
  let w := shiftedStream W 0
  let t := boundaryHitTime w h k
  let c := (kmswStage w t).LL.length
  have hw := congrArg (fun l : List ℕ => l[c + i]?)
    (lMinus_future_LL_word h k hk n)
  rw [List.getElem?_append_right (by simp only [List.length_reverse]; change (kmswStage w t).LL.length ≤ c + i; dsimp [c]; omega),
    List.length_reverse] at hw
  have hc : c + i - (kmswStage w t).LL.length = i := by dsimp [c]; omega
  rw [hc, List.getElem?_map, he] at hw
  change (kmswStage w (t + n)).LL.reverse[c + i]? =
    some (boundaryGluingEdgeMap W h k e) at hw
  have hl := lMinus_LL_reverse_boundary w h (t + n) (c + i)
    (List.getElem?_eq_some_iff.mp hw).1
  rw [hl] at hw
  have hci : -(((c + i : ℕ) : ℤ) + 1) = k - 1 - (i : ℤ) := by
    have hlen := lMinus_initial_LL_length h k hk
    change (c : ℤ) = -k at hlen
    push_cast
    omega
  exact (Option.some.inj hw).symm.trans (congrArg (boundaryOuterEdge w h) hci)

/-- Helper toward Lemma 5.5: every exterior root/LL index occurs in a
finite primed word. This proves existence before the decoder is identified. -/
theorem lMinus_primed_exterior_index_exists (w : ℕ → Fin 3)
    (hτ : HasFlowLineHits w) (i : ℕ) :
    ∃ m, i < (0 :: (kmswStage (primedCode (primedSimInput w) hτ) m).LL.reverse).length := by
  cases i with
  | zero => exact ⟨0, by simp only [List.length_cons]; omega⟩
  | succ i =>
    obtain ⟨m, hm⟩ :=
      (DirectedDistances.Recursive.primedEntryOuterLLVertexIdentification_proved
        w hτ (hatBoundaryHitWitnesses w hτ) i).exists
    obtain ⟨v, hv, _⟩ := hm
    have hi := (List.getElem?_eq_some_iff.mp hv).1
    simp only [List.length_map] at hi
    exact ⟨m, by simp only [List.length_cons]; omega⟩

/-- Helper toward Lemma 5.5: the exterior edge selected from the primed
code maps to the actual missing exterior edge, for every boundary index. -/
theorem lMinusCodeExteriorBoundaryEdge_image
    {W : ℤ → Fin 3} (h : BoundaryHitWitnesses (shiftedStream W 0))
    (k : ℤ) (hk : k ≤ 0)
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k)) (i : ℕ) :
    boundaryGluingPrimedEdgeMap W h k hτ
      (lMinusCodeExteriorBoundaryEdge
        (primedCode (primedSimInput (boundaryGluingFutureStream W h k)) hτ) i) =
      boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)) := by
  let w := boundaryGluingFutureStream W h k
  let p := primedCode (primedSimInput w) hτ
  let a := lMinusCodeExteriorBoundaryEdge p i
  obtain ⟨m, hm⟩ := lMinus_primed_exterior_index_exists w hτ i
  have ha := lMinusCodeExteriorBoundaryEdge_stage p m i hm
  have hw := lPlus_primed_LL_dart_word w hτ m
  have hlen := congrArg List.length hw
  simp only [List.length_map] at hlen
  have hi : i < (kmswStage w (primedStageTime w hτ m)).LL.reverse.length := by omega
  let e := (kmswStage w (primedStageTime w hτ m)).LL.reverse[i]
  have he : (kmswStage w (primedStageTime w hτ m)).LL.reverse[i]? = some e :=
    List.getElem?_eq_getElem hi
  have hget := congrArg (fun l : List (ℕ × Bool) => l[i]?) hw
  rw [List.getElem?_map, List.getElem?_map, ha, he] at hget
  have hed : primedLimitEdgeMap w hτ a = e :=
    congrArg Prod.fst (Option.some.inj hget)
  change boundaryGluingEdgeMap W h k (primedLimitEdgeMap w hτ a) = _
  rw [hed]
  exact lMinus_future_LL_index h k hk (primedStageTime w hτ m) i e he

/-- Helper toward Lemma 5.5: the corrected side on intrinsic code data. -/
@[expose] noncomputable def lMinusCodeSide4 (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) : GeometricSideSubmap :=
  { lMinusCodeSide2 x r q hf with
    boundary := fun i => lMinusCodeDartId r _ (lMinusCodeExteriorBoundaryDart r q i) }

/-- Helper toward Lemma 5.5: decoder 4 is exactly the code-only formula. -/
theorem lMinusDecodedSide4_eq_codeSide4
    {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
    {k : ℤ} {longest : Bool}
    (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
    (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
    (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k)) :
    lMinusDecodedSide4 hτ hqMode hfin =
      lMinusCodeSide4 (if longest then XDP.ldp else XDP.sdp)
        (decodeLMinus (if longest then XDP.ldp else XDP.sdp) k
          (leftSideObsNonpos (if longest then XDP.ldp else XDP.sdp) k W))
        ⟨boundaryFutureHattedPath k W, hqMode⟩
        (lMinus_primed_observation_finiteIncidence hτ hfin) := by
  unfold lMinusDecodedSide4 lMinusCodeSide4
  rw [lMinusDecodedSide2_eq_codeSide2]

section GeometricIdentification

variable {W : ℤ → Fin 3} {h : BoundaryHitWitnesses (shiftedStream W 0)}
  {k : ℤ} {H : WholePlaneRotationHypothesis W}
  {hLL : ∀ j : ℤ, j ≤ 0 → wholePlaneEdgePresent W
    (wholePlaneEdgeι W 0 (kmswLLCreatedEdge (shiftedStream W 0)
      (boundaryHitTime (shiftedStream W 0) h (j - 1))))}
  {longest : Bool}
  (hτ : HasFlowLineHits (boundaryGluingFutureStream W h k))
  (hp : BoundaryHitWitnesses (kmswPastCode W))
  (P : M0CutInfiniteGeodesic W H h hLL k longest)
  (hqMode : boundaryFutureHattedPath k W ∈ Coherent (if longest then XDP.ldp else XDP.sdp))
  (Tpath : InfinitePresentPath (shiftedStream W 0)
    (boundaryPresentVertex (shiftedStream W 0) h k))
  (hfin : hatLimitFiniteIncidence (boundaryGluingFutureStream W h k))
  (hleft : Xdp.CutLeftmostXdp W H h hp hLL longest k P Tpath)
  (hk : k ≤ 0)

local notation "X" => (ite (longest = true) XDP.ldp XDP.sdp)
local notation "rL" => decodeLMinus X k (leftSideObsNonpos X k W)
local notation "qL" => (Subtype.mk (boundaryFutureHattedPath k W) hqMode : Coherent X)
local notation "Q" => lMinusCoherentLeftSide X qL
local notation "S" => m0GeodesicSide hp P ThinMapSide.left
local notation "D4" => lMinusDecodedSide4 hτ hqMode hfin
local notation "GD" => lMinusCodeGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "V" => lMinusCodeToGluedVertexEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "E" => lMinusCodeToGluedDartEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "Φ" => lMinusGluedCellEquiv hτ hp P hqMode Tpath hfin hleft hk
local notation "hf" => lMinus_primed_observation_finiteIncidence hτ hfin

/-- Helper toward Lemma 5.5: the code-only exterior dart maps to the
prescribed run-zero exterior mark, retaining the missing edge and reversed bit. -/
theorem lMinusCodeExteriorBoundaryDart_image (i : ℕ) :
    (GD (lMinusCodeExteriorBoundaryDart rL qL i)).val =
      (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), true) := by
  apply Prod.ext
  · change (lMinusCodeGluedEdgeEquiv hτ hp P hqMode Tpath hfin hleft hk
        (⟦Sum.inl (lMinusCodeExteriorBoundaryEdge (rL).code.1 i)⟧)).val = _
    rw [lMinusCodeGluedEdgeEquiv_val hτ hp P hqMode Tpath hfin hleft hk]
    change boundaryGluingPrimedEdgeMap W h k hτ
      (lMinusCodeExteriorBoundaryEdge (rL).code.1 i) = _
    have hc : (rL).code.1 = primedCode
        (primedSimInput (boundaryGluingFutureStream W h k)) hτ :=
      lMinus_primed_observation_code hτ
    rw [hc]
    exact lMinusCodeExteriorBoundaryEdge_image h k hk hτ i
  · rfl

/-- Helper toward Lemma 5.5: the corrected decoder retains the same
intrinsic code-cell carrier and natural-number encoding as decoder 2. -/
@[expose] noncomputable def lMinusDecodedSide4CellEquiv :
    Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q) ≃
      GeometricSideCell D4 :=
  lMinusDecodedCellEquiv hτ hqMode hfin

/-- Helper toward Lemma 5.5: the corrected decoder's geometric cell map
is the composition of the code-to-glued and glued-to-geometric equivalences. -/
@[expose] noncomputable def lMinusDecodedSide4ToGeometricCellEquiv :
    GeometricSideCell D4 ≃ GeometricSideCell S :=
  lMinusDecodedSide2ToGeometricCellEquiv hτ hp P hqMode Tpath hfin hleft hk

/-- Helper toward Lemma 5.5: the exterior mark has its required image
under the full glued-cell equivalence, not merely under an edge projection. -/
theorem lMinusCodeExteriorBoundaryDart_glued_image (i : ℕ) :
    Φ (.inr (E (lMinusCodeExteriorBoundaryDart rL qL i))) =
      .inr ⟨(boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), true),
        by
          have hh := (GD (lMinusCodeExteriorBoundaryDart rL qL i)).property
          exact (congrArg Prod.fst
            (lMinusCodeExteriorBoundaryDart_image hτ hp P hqMode Tpath hfin hleft hk i)) ▸ hh⟩ := by
  apply congrArg Sum.inr
  apply Subtype.ext
  rw [lMinusCodeToGluedDartEquiv_equiv hτ hp P hqMode Tpath hfin hleft hk]
  exact lMinusCodeExteriorBoundaryDart_image hτ hp P hqMode Tpath hfin hleft hk i

/-- Helper toward Lemma 5.5: every non-boundary tag of decoder 4 is
literally the corresponding decoder-2 relation on the common cell carrier. -/
theorem lMinusDecodedSide4_nonboundary_relation
    (t : TruncationRelation) (ht : ∀ i, t ≠ .boundary i)
    (u v : GeometricSideCell D4) :
    geometricSideRelation D4 t u v ↔
      geometricSideRelation (lMinusDecodedSide2 hτ hqMode hfin) t u v := by
  cases t <;> cases u <;> cases v <;> first | rfl | exact (ht _ rfl).elim

local notation "B" => Equiv.trans (Equiv.sumCongr V E) Φ
local notation "A" => lMinusCodeSide2CellEquiv X rL qL hf
local notation "C4" => lMinusCodeSide4 X rL qL hf

/-- Helper toward Lemma 5.5: evaluation of the composite on intrinsic darts. -/
theorem lMinusCodeSide4_geometric_dart (d : LMinusCodeGluedDart rL Q) :
    B (.inr d) = .inr (GD d) := by
  exact congrArg Sum.inr
    (lMinusCodeToGluedDartEquiv_equiv hτ hp P hqMode Tpath hfin hleft hk d)

/-- Helper toward Lemma 5.5: the unchanged intrinsic relations map to the
actual side through the proved geometric gluing. -/
theorem lMinusCodeRelation2_nonboundary_actual_iff
    (t : TruncationRelation) (ht : ∀ i, t ≠ .boundary i)
    (a b : Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q)) :
    lMinusCodeRelation2 X rL qL hf t a b ↔
      geometricSideRelation S t (B a) (B b) := by
  cases t with
  | vertex => cases a <;> cases b <;> rfl
  | target => cases a <;> cases b <;> rfl
  | root =>
    exact (lMinusCodeRelation2_root_glued_iff hτ hp P hqMode Tpath hfin hleft hk a b).trans
      (lMinusGluedCellEquiv_root_iff hτ hp P hqMode Tpath hfin hleft hk _ _)
  | incident =>
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      cases b with
      | inr e => rfl
      | inl v =>
        have hc := lMinusCodeToGluedDartEndpoint_compat hτ hp P hqMode Tpath hfin hleft hk d
        have hh : lMinusCodeEndpointVertex X rL qL d.2 d.1 = v ↔
            lMinusGluedDartEndpoint hτ hqMode (E d) = V v := by
          rw [← hc]
          exact (V).injective.eq_iff.symm
        exact hh.trans (lMinusGluedCellEquiv_incident_iff
          hτ hp P hqMode Tpath hfin hleft hk (.inr (E d)) (.inl (V v)))
  | opposite =>
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      cases b with
      | inl b => rfl
      | inr e =>
        rw [lMinusCodeSide4_geometric_dart, lMinusCodeSide4_geometric_dart]
        change (d.1, !d.2) = e ↔
          ((GD d).val.1, !(GD d).val.2) = (GD e).val
        constructor
        · rintro rfl
          rfl
        · intro he
          apply (GD).injective
          exact Subtype.ext he
  | oriented =>
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      have hh := (lMinusCodeToGluedEdgePresence_iff
        hτ hp P hqMode Tpath hfin hleft hk d).trans
        (lMinusGluedCellEquiv_oriented_iff hτ hp P hqMode Tpath hfin hleft hk
          (.inr (E (d.1, false))) (.inr (E (d.1, false))))
      change _ ↔ geometricSideRelation S .oriented (B (.inr (d.1, false)))
        (B (.inr (d.1, false))) at hh
      simp only [lMinusCodeSide4_geometric_dart] at hh
      change lMinusCodeEdgePresent rL Q (PrimedEdgePresent _ hτ) d.1 ↔
        EdgePresent (shiftedStream W 0) (GD d).val.1 ∧ false = false at hh
      have hc : (PrimedEdgePresent (boundaryGluingFutureStream W h k) hτ) =
          (fun e => ∃ m, e < (kmswMissingRootStage (rL).code.1 m).nextEdge ∧
            (kmswMissingRootStage (rL).code.1 m).present e = true) := by
        have hs : (rL).code.1 = primedCode
            (primedSimInput (boundaryGluingFutureStream W h k)) hτ :=
          lMinus_primed_observation_code hτ
        rw [hs]
        rfl
      rw [hc] at hh
      simp only [and_true] at hh
      rw [lMinusCodeSide4_geometric_dart]
      cases b <;> exact and_congr hh Iff.rfl
  | faceNext =>
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      cases b with
      | inl b => rfl
      | inr e =>
        rw [lMinusCodeSide4_geometric_dart, lMinusCodeSide4_geometric_dart]
        exact lMinusCodeWholeFaceNext_actual_iff
          hτ hp P hqMode Tpath hfin hleft hk d e
  | rotation =>
    have hb (c : Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q)) :
        (lMinusDecodedSide2ToGeometricCellEquiv hτ hp P hqMode Tpath hfin hleft hk)
          ((lMinusDecodedCellEquiv hτ hqMode hfin) c) = B c := by
      change Φ ((Equiv.sumCongr V E)
        ((lMinusDecodedCellEquiv hτ hqMode hfin).symm
          ((lMinusDecodedCellEquiv hτ hqMode hfin) c))) = B c
      rw [Equiv.symm_apply_apply]
      rfl
    have hh := lMinusDecodedSide2_rotation_iff hτ hp P hqMode Tpath hfin hleft hk
      ((lMinusDecodedCellEquiv hτ hqMode hfin) a)
      ((lMinusDecodedCellEquiv hτ hqMode hfin) b)
    rw [hb, hb] at hh
    cases a with
    | inl a => cases b <;> exact hh
    | inr d =>
      cases b with
      | inl b => exact hh
      | inr e =>
        change (lMinusDecodedSide2 hτ hqMode hfin).rotation
          (lMinusCodeDartId rL Q d) (lMinusCodeDartId rL Q e) ↔ _ at hh
        rw [lMinusDecodedSide2_rotation_code_iff] at hh
        exact hh
  | seam i =>
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      rw [lMinusCodeSide4_geometric_dart]
      have hb := lMinusCodeGluedDartEquiv_hatted hτ hp P hqMode Tpath hfin hleft hk
        ⟨(Q).seam i, lMinus_hatted_seam_mem X qL i⟩
      have hs := lMinus_hatted_seam_image hτ hp P hqMode Tpath hfin hleft i
      cases b <;>
        change lMinusCodeHattedDart rL Q _ = d ↔ (S).seam i = (GD d).val
      all_goals
        rw [← hs, ← hb]
        exact ⟨fun he => congrArg (fun z => (GD z).val) he,
          fun he => (GD).injective (Subtype.ext he)⟩
  | boundary i => exact (ht i rfl).elim

/-- Helper toward Lemma 5.5: all ten corrected code-side relations agree
with the actual side under the same full glued-cell equivalence. -/
theorem lMinusCodeSide4_relation_actual_iff
    (t : TruncationRelation)
    (a b : Sum (LMinusCodeGluedVertex rL Q) (LMinusCodeGluedDart rL Q)) :
    geometricSideRelation C4 t (A a) (A b) ↔
      geometricSideRelation S t (B a) (B b) := by
  by_cases hb : ∃ i, t = .boundary i
  · obtain ⟨i, rfl⟩ := hb
    cases a with
    | inl a => cases b <;> rfl
    | inr d =>
      rw [lMinusCodeSide4_geometric_dart]
      have himage := lMinusCodeExteriorBoundaryDart_image
        hτ hp P hqMode Tpath hfin hleft hk i
      cases b <;>
        change lMinusCodeDartId rL Q (lMinusCodeExteriorBoundaryDart rL qL i) =
          lMinusCodeDartId rL Q d ↔
          (boundaryOuterEdge (shiftedStream W 0) h (k - 1 - (i : ℤ)), true) = (GD d).val
      all_goals
        rw [← himage]
        exact (lMinusCodeDartId_injective rL Q).eq_iff.trans
          ⟨fun he => congrArg (fun e => (GD e).val) he,
            fun he => (GD).injective (Subtype.ext he)⟩
  · have ht : ∀ i, t ≠ .boundary i := fun i hi => hb ⟨i, hi⟩
    have hsame : geometricSideRelation C4 t (A a) (A b) ↔
        geometricSideRelation (lMinusCodeSide2 X rL qL hf) t (A a) (A b) := by
      cases t <;> cases a <;> cases b <;> first | rfl | exact (ht _ rfl).elim
    exact hsame.trans ((lMinusCodeSide2CellEquiv_relation_iff X rL qL hf t a b).trans
      (lMinusCodeRelation2_nonboundary_actual_iff hτ hp P hqMode Tpath hfin hleft hk t ht a b))

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: the actual nonpositive left side is marked
isomorphic to decoder 4, including its missing exterior boundary edges. -/
theorem boundaryGluing_nonpos_left_markedIso_lMinusDecodedSide4 :
    Nonempty (GeometricSideMarkedIso S D4) := by
  rw [lMinusDecodedSide4_eq_codeSide4]
  refine ⟨{ equiv := (B).symm.trans A, relation_iff := ?_ }⟩
  intro t u v
  have hh := lMinusCodeSide4_relation_actual_iff
    hτ hp P hqMode Tpath hfin hleft hk t ((B).symm u) ((B).symm v)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
  exact hh.symm

include Tpath hleft hk in
/-- Helper toward Lemma 5.5: the corrected decoded class is the actual
left-side class. This is an identification, not a measurability assertion. -/
theorem lMinusDecodedSide4_class_eq_actual :
    geometricSideClass D4 = geometricSideClass S :=
  ((geometricSideClass_eq_iff S D4).mpr
    (boundaryGluing_nonpos_left_markedIso_lMinusDecodedSide4
      hτ hp P hqMode Tpath hfin hleft hk)).symm

end GeometricIdentification
/-- Helper toward Lemma 5.5: exterior marks are natural under the hatted
marked action, since the primed edge labels are fixed. -/
theorem lMinusCodeExteriorBoundaryDart_transport (x : XDP)
    (r : LMinusSidePresentation x) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso (lMinusCoherentLeftSide x q)
      (lMinusCoherentLeftSide x q')) (i : ℕ) :
    lMinusCodeGluedDartTransportEquiv x r q q' phi
      (lMinusCodeExteriorBoundaryDart r q i) =
      lMinusCodeExteriorBoundaryDart r q' i := by
  rfl

/-- Helper toward Lemma 5.5: arbitrary encoded non-boundary relations
are unchanged by the code-side boundary correction. -/
theorem lMinusCodeSide4_nonboundary_relation (x : XDP)
    (r : LMinusSidePresentation x) (q : Coherent x)
    (hf : KMSWFiniteIncidence r.code.1) (t : TruncationRelation)
    (ht : ∀ i, t ≠ .boundary i)
    (u v : GeometricSideCell (lMinusCodeSide4 x r q hf)) :
    geometricSideRelation (lMinusCodeSide4 x r q hf) t u v ↔
      geometricSideRelation (lMinusCodeSide2 x r q hf) t u v := by
  cases t <;> cases u <;> cases v <;> first | rfl | exact (ht _ rfl).elim































































end DirectedDistances.PaperProofs.Section5

