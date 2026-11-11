/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.BdyReverseBoundary
public import DirectedDistances.DirectedPath.BoundaryFlipAcyclic

/-! # Acyclicity and bipolarity after the planar boundary reversal

Graph-level consequences of the right-prefix reversal, transferred back to
Helpers; not counted in the paper inventory. -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

open BipolarTriangulationWithBoundary
open DirectedDistances.DirectedPath

private abbrev OldDirectedDart (B : BipolarTriangulationWithBoundary D ℓ r) :=
  {d : D // ¬ B.map.missing d ∧ B.map.tail d}

private noncomputable def oldOrientation
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Orientation (MapVertex B.map) (OldDirectedDart B) where
  src e := dartTailVertex B.map e.1
  tgt e := dartHeadVertex B.map e.1

private noncomputable def oldRightBoundaryPath
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    BoundaryPath (oldOrientation B) r where
  vertex i := B.rightPath.vertices.get ⟨min i r, by
    rw [B.rightPath.vertices_length]
    exact Nat.lt_succ_of_le (Nat.min_le_right i r)⟩
  edge i := ⟨B.rightPath.darts.get ⟨min i (r - 1), by
      rw [B.rightPath.darts_length]
      have hrpos : 1 ≤ r := B.right_length_pos
      have hr : r - 1 < r := by omega
      exact Nat.lt_of_le_of_lt (Nat.min_le_right i (r - 1)) hr⟩,
    (B.rightPath.edge_step ⟨min i (r - 1), by
      rw [B.rightPath.darts_length]
      have hrpos : 1 ≤ r := B.right_length_pos
      have hr : r - 1 < r := by omega
      exact Nat.lt_of_le_of_lt (Nat.min_le_right i (r - 1)) hr⟩).1,
    (B.rightPath.edge_step ⟨min i (r - 1), by
      rw [B.rightPath.darts_length]
      have hrpos : 1 ≤ r := B.right_length_pos
      have hr : r - 1 < r := by omega
      exact Nat.lt_of_le_of_lt (Nat.min_le_right i (r - 1)) hr⟩).2.1⟩
  vertex_injective := by
    intro i j hi hj hij
    have hget : B.rightPath.vertices.get ⟨i, by
        rw [B.rightPath.vertices_length]; omega⟩ =
      B.rightPath.vertices.get ⟨j, by rw [B.rightPath.vertices_length]; omega⟩ := by
      simpa [Nat.min_eq_left hi, Nat.min_eq_left hj] using hij
    have hidx := (List.Nodup.get_inj_iff B.rightPath.vertices_nodup).mp hget
    exact congrArg Fin.val hidx
  edge_injective := by
    intro i j hi hj hij
    have htail := congrArg (fun e : OldDirectedDart B => dartTailVertex B.map e.1) hij
    have himin : min i (r - 1) = i := Nat.min_eq_left (by omega)
    have hjmin : min j (r - 1) = j := Nat.min_eq_left (by omega)
    have hi' := (B.rightPath.edge_step ⟨i, by rw [B.rightPath.darts_length]; omega⟩).2.2.1
    have hj' := (B.rightPath.edge_step ⟨j, by rw [B.rightPath.darts_length]; omega⟩).2.2.1
    have hget : B.rightPath.vertices.get
        ⟨i, by rw [B.rightPath.vertices_length]; omega⟩ =
      B.rightPath.vertices.get ⟨j, by rw [B.rightPath.vertices_length]; omega⟩ := by
      calc
        _ = dartTailVertex B.map (B.rightPath.darts.get ⟨i, by
              rw [B.rightPath.darts_length]; omega⟩) := hi'
        _ = dartTailVertex B.map (B.rightPath.darts.get ⟨j, by
              rw [B.rightPath.darts_length]; omega⟩) := by
                simpa only [himin, hjmin] using htail
        _ = _ := hj'.symm
    have hidx := (List.Nodup.get_inj_iff B.rightPath.vertices_nodup).mp hget
    exact congrArg Fin.val hidx
  edge_src := by
    intro i hi
    have hstep := (B.rightPath.edge_step ⟨i, by rw [B.rightPath.darts_length]; omega⟩).2.2.1
    have hmin : min i (r - 1) = i := Nat.min_eq_left (by omega)
    simpa [oldOrientation, Nat.min_eq_left (Nat.le_of_lt hi), hmin] using hstep.symm
  edge_tgt := by
    intro i hi
    have hstep := (B.rightPath.edge_step ⟨i, by rw [B.rightPath.darts_length]; omega⟩).2.2.2
    have hmin₁ : min i (r - 1) = i := Nat.min_eq_left (by omega)
    have hmin₂ : min (i + 1) r = i + 1 := Nat.min_eq_left (by omega)
    simpa [oldOrientation, hmin₁, hmin₂] using hstep.symm

private theorem finite_acyclic_rank {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (hR : ∀ v, ¬ Relation.TransGen R v v) :
    ∃ cap : ℕ, ∃ rank : V → ℕ,
      (∀ v, rank v ≤ cap) ∧ (∀ {u v}, R u v → rank u < rank v) := by
  classical
  let Reach : V → V → Prop := fun v w => w = v ∨ Relation.TransGen R w v
  let rank : V → ℕ := fun v => Fintype.card {w : V // Reach v w}
  refine ⟨Fintype.card V, rank, ?_, ?_⟩
  · intro v
    exact Fintype.card_subtype_le _
  · intro u v huv
    let f : {w : V // Reach u w} → {w : V // Reach v w} := fun w =>
      ⟨w.1, by
        rcases w with ⟨x, hx⟩
        change Reach v x
        rcases hx with hx | hx
        · rw [hx]
          exact Or.inr (Relation.TransGen.single huv)
        · exact Or.inr (Relation.TransGen.tail hx huv)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : {w : V // Reach v w} => x.1) hab
    have hnot : (⟨v, Or.inl rfl⟩ : {w : V // Reach v w}) ∉ Set.range f := by
      rintro ⟨a, ha⟩
      have hav : a.1 = v := congrArg (fun x : {w : V // Reach v w} => x.1) ha
      rcases a.2 with h | h
      · have hvu : v = u := hav.symm.trans h
        have huu : R u u := by simpa only [hvu] using huv
        exact hR u (Relation.TransGen.single huu)
      · have hvu : Relation.TransGen R v u := by simpa [hav] using h
        exact hR u (Relation.TransGen.trans (Relation.TransGen.single huv) hvu)
    change Fintype.card {w : V // Reach u w} <
      Fintype.card {w : V // Reach v w}
    exact Fintype.card_lt_of_injective_of_notMem f hf hnot

private theorem oldRightBoundaryPath_start
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    (oldRightBoundaryPath B).vertex 0 = B.source := by
  simpa [oldRightBoundaryPath, Nat.min_eq_left (Nat.zero_le r)] using
    B.rightPath.start_vertex

private theorem oldRightBoundaryPath_end
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    (oldRightBoundaryPath B).vertex r = B.sink := by
  simpa [oldRightBoundaryPath, Nat.min_self] using B.rightPath.end_vertex

private theorem oldOrientation_acyclic
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Acyclic (oldOrientation B) := by
  letI : Fintype (MapVertex B.map) := Fintype.ofFinite _
  letI : DecidableEq (MapVertex B.map) := Classical.decEq _
  let R : MapVertex B.map → MapVertex B.map → Prop :=
    fun u v => ∃ e : OldDirectedDart B, (oldOrientation B).src e = u ∧
      (oldOrientation B).tgt e = v
  have hR : ∀ v, ¬ Relation.TransGen R v v := by
    intro v hv
    apply B.acyclic v
    apply Relation.TransGen.mono (r := R)
    · intro u w he
      rcases he with ⟨e, rfl, rfl⟩
      exact ⟨e.1, e.2.1, e.2.2, rfl, rfl⟩
    · exact hv
  rcases finite_acyclic_rank R hR with ⟨cap, rank, hbound, hrank⟩
  refine ⟨cap, rank, hbound, ?_⟩
  intro e
  exact hrank ⟨e, rfl, rfl⟩

private theorem oldOrientation_bipolar
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    Bipolar (oldOrientation B) ((oldRightBoundaryPath B).vertex 0)
      ((oldRightBoundaryPath B).vertex r) := by
  have hp0 := oldRightBoundaryPath_start B
  have hpr := oldRightBoundaryPath_end B
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨e, he⟩
    apply B.isSource
    refine ⟨(oldOrientation B).src e, e.1, e.2.1, e.2.2, rfl, ?_⟩
    exact he.trans hp0
  · intro v hv
    by_contra hn
    have hno : ¬ ∃ u, B.map.directedStep u v := by
      rintro ⟨u, d, hmiss, htail, hsrc, htgt⟩
      exact hn ⟨⟨d, B.noMissingDarts d, htail⟩, htgt⟩
    have hvs := B.source_unique v hno
    exact hv (hvs.trans hp0.symm)
  · rintro ⟨e, he⟩
    apply B.isSink
    refine ⟨(oldOrientation B).tgt e, e.1, e.2.1, e.2.2, ?_, rfl⟩
    exact he.trans hpr
  · intro v hv
    by_contra hn
    have hno : ¬ ∃ w, B.map.directedStep v w := by
      rintro ⟨w, d, hmiss, htail, hsrc, htgt⟩
      exact hn ⟨⟨d, B.noMissingDarts d, htail⟩, hsrc⟩
    have hvs := B.sink_unique v hno
    exact hv (hvs.trans hpr.symm)

private theorem oldRightBoundaryPath_leftEdge
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) :
    ∃ e : OldDirectedDart B,
      e ≠ (oldRightBoundaryPath B).edge 0 ∧
        (oldOrientation B).src e = (oldRightBoundaryPath B).vertex 0 := by
  have hleft := B.firstLeftEdge_leavesSource_and_differs_from_firstRight
  let dL := B.leftPath.firstDart (Nat.lt_of_lt_of_le (by decide) B.left_length_pos)
  rcases hleft with ⟨htail, hstart, hdiff⟩
  refine ⟨⟨dL, B.noMissingDarts dL, htail⟩, ?_, ?_⟩
  · intro he
    apply hdiff
    have hval : dL = ((oldRightBoundaryPath B).edge 0).1 := congrArg Subtype.val he
    have hr : 0 < r := Nat.lt_of_lt_of_le (by decide) B.right_length_pos
    change Equiv.Perm.SameCycle B.map.toCombinatorialMap.edgeInv dL
      (B.rightPath.darts.get ⟨0, by rw [B.rightPath.darts_length]; exact hr⟩)
    apply Eq.sameCycle
    simpa [oldRightBoundaryPath, Nat.min_eq_left (Nat.zero_le (r - 1))] using hval
  · change dartTailVertex B.map dL = (oldRightBoundaryPath B).vertex 0
    calc
      dartTailVertex B.map dL = B.source := hstart
      _ = (oldRightBoundaryPath B).vertex 0 := (oldRightBoundaryPath_start B).symm

private theorem oldRightBoundaryPath_channeled
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r)
    (hbc : B.IsBoundaryChanneled) :
    BoundaryChanneled (oldOrientation B) (oldRightBoundaryPath B) := by
  constructor
  · intro e he
    apply B.isSource
    refine ⟨(oldOrientation B).src e, e.1, e.2.1, e.2.2, rfl, ?_⟩
    exact he.trans (oldRightBoundaryPath_start B)
  · intro i hi0 hir e he
    have hp0 := oldRightBoundaryPath_start B
    have hpr := oldRightBoundaryPath_end B
    have hbound : (oldRightBoundaryPath B).vertex i ∈ B.boundaryVertices := by
      change (oldRightBoundaryPath B).vertex i ∈
        {v | v ∈ B.leftPath.vertices ∨ v ∈ B.rightPath.vertices}
      right
      change B.rightPath.vertices.get ⟨min i r, by
        rw [B.rightPath.vertices_length]
        exact Nat.lt_succ_of_le (Nat.min_le_right i r)⟩ ∈ B.rightPath.vertices
      have hmin : min i r = i := Nat.min_eq_left (Nat.le_of_lt hir)
      simpa [hmin] using
        (List.get_mem B.rightPath.vertices ⟨i, by rw [B.rightPath.vertices_length]; omega⟩)
    have hnotSink : (oldRightBoundaryPath B).vertex i ≠ B.sink := by
      intro h
      have hidx := (oldRightBoundaryPath B).vertex_injective i r (by omega) le_rfl
        (h.trans hpr.symm)
      omega
    have hheadEq : dartHeadVertex B.map e.1 = (oldRightBoundaryPath B).vertex i := by
      simpa [oldOrientation] using he
    have hbe := hbc e.1 e.2.1 e.2.2 (by
      rw [hheadEq]
      exact hbound) (by rw [hheadEq]; exact hnotSink)
    rcases hbe with ⟨a, ha, hcyc⟩
    have hboundaryTail : ∀ d, d ∈ B.leftPath.darts ++ B.rightPath.darts →
        B.map.tail d := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
        rw [← hj]
        exact (B.leftPath.edge_step j).2.1
      · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
        rw [← hj]
        exact (B.rightPath.edge_step j).2.1
    have hnotInv : ¬ B.map.tail (B.map.toCombinatorialMap.edgeInv e.1) :=
      (B.map.tail_iff e.1 e.2.1).mp e.2.2
    have hsame := (B.map.toCombinatorialMap.edgeInv_sameCycle_iff e.1 a).mp hcyc
    have hda : e.1 = a := by
      rcases hsame with hsame | hsame
      · exact hsame.symm
      · exfalso
        apply hnotInv
        have hat := hboundaryTail a ha
        rw [hsame] at hat
        exact hat
    have hmem : e.1 ∈ B.leftPath.darts ++ B.rightPath.darts := by
      rw [hda]
      exact ha
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hleft
      have hjlt : j.val < ℓ := by simpa [B.leftPath.darts_length] using j.isLt
      have hhead : dartHeadVertex B.map e.1 = (oldRightBoundaryPath B).vertex i := by
        simpa [oldOrientation] using he
      have hleftV : B.leftPath.vertices.get ⟨j.val + 1, by
          rw [B.leftPath.vertices_length]
          omega⟩ = (oldRightBoundaryPath B).vertex i := by
        calc
          _ = dartHeadVertex B.map (B.leftPath.darts.get j) :=
            (B.leftPath.edge_step j).2.2.2
          _ = dartHeadVertex B.map e.1 := by exact congrArg (dartHeadVertex B.map) hj
          _ = _ := hhead
      have hmemLeft : (oldRightBoundaryPath B).vertex i ∈ B.leftPath.vertices := by
        rw [← hleftV]
        exact List.get_mem _ _
      have hmemRight : (oldRightBoundaryPath B).vertex i ∈ B.rightPath.vertices := by
        change B.rightPath.vertices.get ⟨min i r, by
          rw [B.rightPath.vertices_length]
          exact Nat.lt_succ_of_le (Nat.min_le_right i r)⟩ ∈ B.rightPath.vertices
        have hmin : min i r = i := Nat.min_eq_left (Nat.le_of_lt hir)
        simpa [hmin] using
          (List.get_mem B.rightPath.vertices ⟨i, by rw [B.rightPath.vertices_length]; omega⟩)
      have hdisj := B.paths_internally_vertex_disjoint
        ((oldRightBoundaryPath B).vertex i) hmemLeft hmemRight
      rcases hdisj with hsource | hsink
      · have hidx := (oldRightBoundaryPath B).vertex_injective i 0 (by omega) (by omega)
          (hsource.trans hp0.symm)
        omega
      · have hidx := (oldRightBoundaryPath B).vertex_injective i r (by omega) le_rfl
          (hsink.trans hpr.symm)
        omega
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hright
      have hjlt : j.val < r := by simpa [B.rightPath.darts_length] using j.isLt
      have hval : e.1 = B.rightPath.darts.get j := by
        exact hj.symm
      have hidxVertex : (oldRightBoundaryPath B).vertex (j.val + 1) =
          (oldRightBoundaryPath B).vertex i := by
        have hhead : dartHeadVertex B.map e.1 = (oldRightBoundaryPath B).vertex i := hheadEq
        have hstep := (B.rightPath.edge_step j).2.2.2
        have hget : B.rightPath.vertices.get ⟨j.val + 1, by
            rw [B.rightPath.vertices_length]
            omega⟩ = (oldRightBoundaryPath B).vertex i := by
          calc
            _ = dartHeadVertex B.map (B.rightPath.darts.get j) := hstep
            _ = dartHeadVertex B.map e.1 := by rw [← hval]
            _ = _ := hhead
        simpa [oldRightBoundaryPath, Nat.min_eq_left (by omega : j.val + 1 ≤ r)] using hget
      have hidx := (oldRightBoundaryPath B).vertex_injective (j.val + 1) i (by omega)
        (by omega) hidxVertex
      have hji : j.val = i - 1 := by omega
      have heqEdge : e = (oldRightBoundaryPath B).edge j.val := by
        apply Subtype.ext
        have hm : min j.val (r - 1) = j.val := Nat.min_eq_left (by omega)
        simpa [oldRightBoundaryPath, hm] using hval
      rw [← hji]
      exact heqEdge

private theorem rightPathDart_tail
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r)
    {d : D} (hd : d ∈ B.rightPath.darts) : B.map.tail d := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  rw [← hi]
  exact (B.rightPath.edge_step i).2.1

private theorem oldGraphFlipped_iff_prefixDart
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (e : OldDirectedDart B) :
    IsFlipped (oldRightBoundaryPath B).edge k e ↔
      e.1 ∈ rightBoundaryPrefixDarts B k := by
  constructor
  · rintro ⟨i, hik, he⟩
    have hi : i < r := by omega
    have hval : e.1 = B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ := by
      have h := congrArg Subtype.val he.symm
      simpa [oldRightBoundaryPath,
        Nat.min_eq_left (by omega : i ≤ r - 1)] using h
    have hmem : B.rightPath.darts.get ⟨i, by rw [B.rightPath.darts_length]; omega⟩ ∈
        B.rightPath.darts.take k := by
      apply List.mem_iff_getElem.mpr
      refine ⟨i, ?_, ?_⟩
      · simp only [List.length_take, B.rightPath.darts_length]
        omega
      · simp [List.get_eq_getElem, hik]
    unfold rightBoundaryPrefixDarts
    rw [hval]
    exact hmem
  · intro hd
    have hdall : e.1 ∈ B.rightPath.darts := List.mem_of_mem_take hd
    have hik : B.rightPath.darts.idxOf e.1 < k :=
      (List.mem_take_iff_idxOf_lt hdall).mp hd
    have hiLen : B.rightPath.darts.idxOf e.1 < B.rightPath.darts.length :=
      List.idxOf_lt_length_iff.mpr hdall
    let i := B.rightPath.darts.idxOf e.1
    have hget : B.rightPath.darts.get ⟨i, hiLen⟩ = e.1 :=
      List.idxOf_get hiLen
    have hi : i < r := by simpa [B.rightPath.darts_length] using hiLen
    have he : (oldRightBoundaryPath B).edge i = e := by
      apply Subtype.ext
      have hm : min i (r - 1) = i := Nat.min_eq_left (by omega)
      simpa [oldRightBoundaryPath, hm] using hget
    exact ⟨i, hik, he⟩

private theorem oldGraphFlipped_iff_mapSelected
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (e : OldDirectedDart B) :
    IsFlipped (oldRightBoundaryPath B).edge k e ↔
      e.1 ∈ rightPrefixFlipDarts B k := by
  constructor
  · intro h
    apply Set.mem_ofPred_eq.mpr
    exact Or.inl (oldGraphFlipped_iff_prefixDart B k hk hkr e |>.mp h)
  · intro h
    change e.1 ∈ rightBoundaryPrefixDarts B k ∨
      B.map.toCombinatorialMap.edgeInv e.1 ∈ rightBoundaryPrefixDarts B k at h
    rcases h with hd | hd
    · exact oldGraphFlipped_iff_prefixDart B k hk hkr e |>.mpr hd
    · have htailInv := rightPathDart_tail B (List.mem_of_mem_take hd)
      have hnotInv := (B.map.tail_iff e.1 e.2.1).mp e.2.2
      exact (hnotInv htailInv).elim

private theorem mapStep_iff_graphFlipStep
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (v w : MapVertex B.map) :
    (flipRightPrefix B k hk hkr).directedStep v w ↔
      ∃ e : OldDirectedDart B,
        (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).src e = v ∧
        (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).tgt e = w := by
  let F := flipRightPrefix B k hk hkr
  let O := oldOrientation B
  let p := oldRightBoundaryPath B
  let G := flipPrefix O p k
  have htailVertex (d : D) : dartTailVertex F d = dartTailVertex B.map d := by
    rfl
  have hheadVertex (d : D) : dartHeadVertex F d = dartHeadVertex B.map d := by
    rfl
  constructor
  · rintro ⟨d, hmiss, htail, hsrc, hdst⟩
    have hmissOld : ¬ B.map.missing d := by
      simpa [F, flipRightPrefix_missing] using hmiss
    by_cases hsel : d ∈ rightPrefixFlipDarts B k
    · have htailInv : B.map.tail (B.map.toCombinatorialMap.edgeInv d) := by
        exact (flipRightPrefix_tail_of_mem B k hk hkr d hsel).mp htail
      have hselRaw : d ∈ rightBoundaryPrefixDarts B k ∨
          B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k := by
        simpa [rightPrefixFlipDarts] using hsel
      have hinvPrefix : B.map.toCombinatorialMap.edgeInv d ∈
          rightBoundaryPrefixDarts B k := by
        rcases hselRaw with hd | hd
        · have htailD := rightPathDart_tail B (List.mem_of_mem_take hd)
          have hnotInv := (B.map.tail_iff d hmissOld).mp htailD
          exact False.elim (hnotInv htailInv)
        · exact hd
      have hmissInv : ¬ B.map.missing (B.map.toCombinatorialMap.edgeInv d) := by
        intro hm
        exact hmissOld ((B.map.missing_edgeInv d).mpr hm)
      let e : OldDirectedDart B :=
        ⟨B.map.toCombinatorialMap.edgeInv d, hmissInv, htailInv⟩
      have hf : IsFlipped p.edge k e :=
        (oldGraphFlipped_iff_prefixDart B k hk hkr e).mpr hinvPrefix
      have hgs : G.src e = dartTailVertex F d := by
        simp [G, F, O, p, e, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
          oldOrientation, dartTailVertex, dartHeadVertex,
          flipRightPrefix_toCombinatorialMap,
          B.map.toCombinatorialMap.edgeInv_invol] <;> rfl
      have hgt : G.tgt e = dartHeadVertex F d := by
        simp [G, F, O, p, e, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
          oldOrientation, dartTailVertex, dartHeadVertex,
          flipRightPrefix_toCombinatorialMap,
          B.map.toCombinatorialMap.edgeInv_invol] <;> rfl
      exact ⟨e, hgs.trans hsrc, hgt.trans hdst⟩
    · have htailOld : B.map.tail d :=
        (flipRightPrefix_tail_of_not_mem B k hk hkr d hsel).mp htail
      let e : OldDirectedDart B := ⟨d, hmissOld, htailOld⟩
      have hf : ¬ IsFlipped p.edge k e := by
        intro hf
        have hpref := (oldGraphFlipped_iff_prefixDart B k hk hkr e).mp hf
        apply hsel
        change d ∈ rightBoundaryPrefixDarts B k ∨
          B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k
        exact Or.inl hpref
      have hgs : G.src e = dartTailVertex F d := by
        simp [G, F, O, p, e, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
          oldOrientation, dartTailVertex, flipRightPrefix_toCombinatorialMap] <;> rfl
      have hgt : G.tgt e = dartHeadVertex F d := by
        simp [G, F, O, p, e, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
          oldOrientation, dartHeadVertex, flipRightPrefix_toCombinatorialMap] <;> rfl
      exact ⟨e, hgs.trans hsrc, hgt.trans hdst⟩
  · rintro ⟨e, hsrc, hdst⟩
    by_cases hf : IsFlipped p.edge k e
    · have hpref := (oldGraphFlipped_iff_prefixDart B k hk hkr e).mp hf
      let d := B.map.toCombinatorialMap.edgeInv e.1
      have hsel : d ∈ rightPrefixFlipDarts B k := by
        change d ∈ rightBoundaryPrefixDarts B k ∨
          B.map.toCombinatorialMap.edgeInv d ∈ rightBoundaryPrefixDarts B k
        right
        simpa [d, B.map.toCombinatorialMap.edgeInv_invol] using hpref
      have hmiss : ¬ F.missing d := by
        intro hm
        have hmissOld : B.map.missing d := by simpa [F, flipRightPrefix_missing] using hm
        have hmissE : B.map.missing e.1 := (B.map.missing_edgeInv e.1).mpr hmissOld
        exact e.2.1 hmissE
      have htail : F.tail d := by
        apply (flipRightPrefix_tail_of_mem B k hk hkr d hsel).mpr
        simpa [d, B.map.toCombinatorialMap.edgeInv_invol] using e.2.2
      have hsrc : dartTailVertex F d = v := by
        have hgs : G.src e = dartTailVertex F d := by
          simp [G, F, O, p, d, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
            oldOrientation, dartTailVertex, dartHeadVertex,
            flipRightPrefix_toCombinatorialMap,
            B.map.toCombinatorialMap.edgeInv_invol] <;> rfl
        exact hgs.symm.trans hsrc
      have hdst : dartHeadVertex F d = w := by
        have hgt : G.tgt e = dartHeadVertex F d := by
          simp [G, F, O, p, d, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
            oldOrientation, dartTailVertex, dartHeadVertex,
            flipRightPrefix_toCombinatorialMap,
            B.map.toCombinatorialMap.edgeInv_invol] <;> rfl
        exact hgt.symm.trans hdst
      exact ⟨d, hmiss, htail, hsrc, hdst⟩
    · have hprefNot : e.1 ∉ rightBoundaryPrefixDarts B k := by
        intro hpref
        exact hf ((oldGraphFlipped_iff_prefixDart B k hk hkr e).mpr hpref)
      have hinvNot : B.map.toCombinatorialMap.edgeInv e.1 ∉
          rightBoundaryPrefixDarts B k := by
        intro hpref
        have htailInv := rightPathDart_tail B (List.mem_of_mem_take hpref)
        have hnotInv := (B.map.tail_iff e.1 e.2.1).mp e.2.2
        exact hnotInv htailInv
      have hnotSel : e.1 ∉ rightPrefixFlipDarts B k := by
        change ¬ (e.1 ∈ rightBoundaryPrefixDarts B k ∨
          B.map.toCombinatorialMap.edgeInv e.1 ∈ rightBoundaryPrefixDarts B k)
        exact not_or_intro hprefNot hinvNot
      have hmiss : ¬ F.missing e.1 := by
        simpa [F, flipRightPrefix_missing] using e.2.1
      have htail : F.tail e.1 :=
        (flipRightPrefix_tail_of_not_mem B k hk hkr e.1 hnotSel).mpr e.2.2
      have hsrc : dartTailVertex F e.1 = v := by
        have hgs : G.src e = dartTailVertex F e.1 := by
          simp [G, F, O, p, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
            oldOrientation, dartTailVertex, flipRightPrefix_toCombinatorialMap] <;> rfl
        exact hgs.symm.trans hsrc
      have hdst : dartHeadVertex F e.1 = w := by
        have hgt : G.tgt e = dartHeadVertex F e.1 := by
          simp [G, F, O, p, DirectedPath.flipPrefix, DirectedPath.flipEdges, hf,
            oldOrientation, dartHeadVertex, flipRightPrefix_toCombinatorialMap] <;> rfl
        exact hgt.symm.trans hdst
      exact ⟨e.1, hmiss, htail, hsrc, hdst⟩

private theorem rightPrefixGraph_acyclic
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    Acyclic (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k) := by
  letI : Fintype (OldDirectedDart B) := Fintype.ofFinite _
  exact DirectedDistances.DirectedPath.boundaryFlip_acyclic
    (oldOrientation B) (oldRightBoundaryPath B) (oldOrientation_acyclic B)
    (oldRightBoundaryPath_channeled B hbc) hk (by omega)

private theorem rightPrefixGraph_bipolar
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    Bipolar (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k)
      ((oldRightBoundaryPath B).vertex k) ((oldRightBoundaryPath B).vertex r) := by
  letI : Fintype (OldDirectedDart B) := Fintype.ofFinite _
  exact DirectedDistances.DirectedPath.boundaryFlip_bipolar
    (oldOrientation B) (oldRightBoundaryPath B) (oldOrientation_bipolar B)
    (oldRightBoundaryPath_channeled B hbc) (oldRightBoundaryPath_leftEdge B)
    hk (by omega)

private theorem rightPrefixVertex_eq_graphVertex
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hkr : k < r) :
    rightBoundaryVertexAt B k (Nat.le_of_lt hkr) =
      (oldRightBoundaryPath B).vertex k := by
  simp [rightBoundaryVertexAt, oldRightBoundaryPath,
    Nat.min_eq_left (Nat.le_of_lt hkr)]

/-- The right-prefix reversal is acyclic at the map level, by transfer of the
finite ranking argument (`lem-bdy-reverse`,
inventory. -/
theorem flipRightPrefix_isAcyclic
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    (flipRightPrefix B k hk hkr).IsAcyclic := by
  rcases rightPrefixGraph_acyclic B k hk hkr hbc with ⟨cap, rank, hbound, hrank⟩
  intro v hcycle
  have hlt : Relation.TransGen (fun a b : ℕ => a < b) (rank v) (rank v) :=
    hcycle.lift rank (by
      intro u w hstep
      rcases (mapStep_iff_graphFlipStep B k hk hkr u w).mp hstep with ⟨e, hsrc, hdst⟩
      have h := hrank e
      rw [hsrc, hdst] at h
      exact h)
  have hlt' : rank v < rank v := by
    simpa only [Relation.transGen_eq_self] using hlt
  exact Nat.lt_irrefl (rank v) hlt'

/-- The flipped right-boundary vertex `x_k` has no incoming edge
counted in the paper inventory. -/
theorem flipRightPrefix_noIncomingAtK
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep u
      (rightBoundaryVertexAt B k (Nat.le_of_lt hkr)) := by
  intro h
  rcases h with ⟨u, hu⟩
  have hgraph := (mapStep_iff_graphFlipStep B k hk hkr u _).mp hu
  rcases hgraph with ⟨e, hs, ht⟩
  have hnone := (rightPrefixGraph_bipolar B k hk hkr hbc).1
  have hx := rightPrefixVertex_eq_graphVertex B k hkr
  exact hnone ⟨e, ht.trans hx⟩

/-- Every vertex with no incoming edge after the flip is the new right
boundary source (`lem-bdy-reverse`,
inventory. -/
theorem flipRightPrefix_source_unique
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ∀ v, (¬ ∃ u, (flipRightPrefix B k hk hkr).directedStep u v) →
      v = rightBoundaryVertexAt B k (Nat.le_of_lt hkr) := by
  intro v hno
  have hgraphNo : ¬ ∃ e : OldDirectedDart B,
      (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).tgt e = v := by
    rintro ⟨e, he⟩
    exact hno ⟨(flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).src e,
      (mapStep_iff_graphFlipStep B k hk hkr _ _).mpr ⟨e, rfl, he⟩⟩
  have hsource : v = (oldRightBoundaryPath B).vertex k := by
    by_contra hv
    rcases (rightPrefixGraph_bipolar B k hk hkr hbc).2.1 v hv with ⟨e, he⟩
    exact hgraphNo ⟨e, he⟩
  exact hsource.trans (rightPrefixVertex_eq_graphVertex B k hkr).symm

/-- The old sink remains without outgoing edges after the flip
counted in the paper inventory. -/
theorem flipRightPrefix_noOutgoingAtSink
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep B.sink w := by
  intro h
  rcases h with ⟨w, hw⟩
  have hgraph := (mapStep_iff_graphFlipStep B k hk hkr _ _).mp hw
  rcases hgraph with ⟨e, hs, ht⟩
  have hnone := (rightPrefixGraph_bipolar B k hk hkr hbc).2.2.1
  have hpr := oldRightBoundaryPath_end B
  exact hnone ⟨e, hs.trans hpr.symm⟩

/-- Every vertex with no outgoing edge after the flip is the old sink
counted in the paper inventory. -/
theorem flipRightPrefix_sink_unique
    {ℓ r : ℕ} (B : BipolarTriangulationWithBoundary D ℓ r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : k < r) (hbc : B.IsBoundaryChanneled) :
    ∀ v, (¬ ∃ w, (flipRightPrefix B k hk hkr).directedStep v w) → v = B.sink := by
  intro v hno
  have hgraphNo : ¬ ∃ e : OldDirectedDart B,
      (flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).src e = v := by
    rintro ⟨e, he⟩
    exact hno ⟨(flipPrefix (oldOrientation B) (oldRightBoundaryPath B) k).tgt e,
      (mapStep_iff_graphFlipStep B k hk hkr _ _).mpr ⟨e, he, rfl⟩⟩
  have hsink : v = (oldRightBoundaryPath B).vertex r := by
    by_contra hv
    rcases (rightPrefixGraph_bipolar B k hk hkr hbc).2.2.2 v hv with ⟨e, he⟩
    exact hgraphNo ⟨e, he⟩
  exact hsink.trans (oldRightBoundaryPath_end B)

end DirectedDistances.PlanarMap
