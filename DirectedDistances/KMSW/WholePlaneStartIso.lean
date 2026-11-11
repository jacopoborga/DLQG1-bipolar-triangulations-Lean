module

public import DirectedDistances.KMSW.WholePlaneShiftIso
public import DirectedDistances.KMSW.WholePlaneLemma38IntegerStart
public import DirectedDistances.KMSW.WholePlaneIntegerRuns

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.KMSW

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
@[expose] def shiftWordInt (W : ℤ → Fin 3) (n : ℤ) : ℤ → Fin 3 :=
  fun i => W (i + n)

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
theorem shiftWordInt_nat (W : ℤ → Fin 3) (m : ℕ) :
    shiftWordInt W (m : ℤ) = shiftWord W m := by
  funext i
  simp [shiftWordInt, shiftWord]

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
structure NatShiftIso (V V' : ℤ → Fin 3) (m : ℕ)
    (h : V' = shiftWord V m) where
  

  vertex : WholePlaneVertex V ≃ WholePlaneVertex V'
  

  edge : WholePlaneEdge V ≃ WholePlaneEdge V'
  

  dart : WholePlaneDart V ≃ WholePlaneDart V'
  

  dart_apply : ∀ d, dart d = (edge d.1, d.2)
  

  west : ∀ e, wholePlaneEdgeWest V' (edge e) = vertex (wholePlaneEdgeWest V e)
  

  east : ∀ e, wholePlaneEdgeEast V' (edge e) = vertex (wholePlaneEdgeEast V e)
  

  present : ∀ e, wholePlaneEdgePresent V' (edge e) ↔ wholePlaneEdgePresent V e
  

  vertex_iota : ∀ N v,
    vertex (wholePlaneVertexι V N v) = wholePlaneVertexι V' (N + m) v
  

  edge_iota : ∀ N e,
    edge (wholePlaneEdgeι V N e) = wholePlaneEdgeι V' (N + m) e
  

  rot : ∀ (H : WholePlaneRotationHypothesis V)
    (H' : WholePlaneRotationHypothesis V') (x : WholePlaneDart V),
    dart (wholePlaneRotation V H x) =
      wholePlaneRotation V' H' (dart x)

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
@[expose] noncomputable def natShiftIsoOfEq (V V' : ℤ → Fin 3) (m : ℕ)
    (h : V' = shiftWord V m) : NatShiftIso V V' m h := by
  subst V'
  refine {
    vertex := wholePlaneVertexShiftEquiv V m
    edge := wholePlaneEdgeShiftEquiv V m
    dart := Equiv.prodCongr (wholePlaneEdgeShiftEquiv V m) (Equiv.refl Bool)
    dart_apply := ?_
    west := ?_
    east := ?_
    present := ?_
    vertex_iota := ?_
    edge_iota := ?_
    rot := ?_ }
  · intro d
    rfl
  · exact wholePlaneEdgeShift_west V m
  · exact wholePlaneEdgeShift_east V m
  · exact wholePlaneEdgePresent_shift V m
  · intro N v
    exact wholePlaneVertexShift_ι V m N v
  · intro N e
    exact wholePlaneEdgeShift_ι V m N e
  · intro H H' x
    have hH : H = wholePlaneRotationHypothesis_of_shiftWord V m H' :=
      Subsingleton.elim _ _
    subst H
    exact wholePlaneRotation_shift V m H' x

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
private theorem startVertexIotaNat (W : ℤ → Fin 3) (m : ℕ) (v : ℕ) :
    lemma38StartVertexι W (m : ℤ) v =
      wholePlaneVertexι W 0
        (wholePlaneVertexTrans (shiftWord W m) 0 m (Nat.zero_le m) v) := by
  by_cases hm : m = 0
  · subst m
    simp [lemma38StartVertexι, wholePlaneVertexTrans,
      kmswWindowVertexMapInf_zero_start]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hs : shiftedStream (shiftWord W m) m = shiftedStream W 0 := by
      funext i
      simp only [shiftedStream, shiftWord, Nat.cast_zero, sub_zero]
      congr 1
      omega
    have hmcast : (m : ℤ).toNat = m := by simp
    simp only [lemma38StartVertexι]
    split
    · omega
    · rw [wholePlaneVertexTrans, hs, hmcast, Nat.sub_zero]

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
private theorem startEdgeIotaNat (W : ℤ → Fin 3) (m : ℕ) (e : ℕ) :
    lemma38StartEdgeι W (m : ℤ) e =
      wholePlaneEdgeι W 0
        (wholePlaneEdgeTrans (shiftWord W m) 0 m (Nat.zero_le m) e) := by
  by_cases hm : m = 0
  · subst m
    simp [lemma38StartEdgeι, wholePlaneEdgeTrans,
      kmswWindowEdgeMapInf_zero_start]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hs : shiftedStream (shiftWord W m) m = shiftedStream W 0 := by
      funext i
      simp only [shiftedStream, shiftWord, Nat.cast_zero, sub_zero]
      congr 1
      omega
    have hmcast : (m : ℤ).toNat = m := by simp
    simp only [lemma38StartEdgeι]
    split
    · omega
    · rw [wholePlaneEdgeTrans, hs, hmcast, Nat.sub_zero]

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
structure WholePlaneStartIso (W : ℤ → Fin 3) (n : ℤ) where
  

  vertex : WholePlaneVertex (shiftWordInt W n) ≃ WholePlaneVertex W
  

  edge : WholePlaneEdge (shiftWordInt W n) ≃ WholePlaneEdge W
  

  dart : WholePlaneDart (shiftWordInt W n) ≃ WholePlaneDart W
  

  dart_apply : ∀ d, dart d = (edge d.1, d.2)
  

  west : ∀ e, wholePlaneEdgeWest W (edge e) =
    vertex (wholePlaneEdgeWest (shiftWordInt W n) e)
  

  east : ∀ e, wholePlaneEdgeEast W (edge e) =
    vertex (wholePlaneEdgeEast (shiftWordInt W n) e)
  

  present : ∀ e, wholePlaneEdgePresent W (edge e) ↔
    wholePlaneEdgePresent (shiftWordInt W n) e
  

  iota_vertex : ∀ v,
    vertex (wholePlaneVertexι (shiftWordInt W n) 0 v) =
      lemma38StartVertexι W n v
  

  iota_edge : ∀ e,
    edge (wholePlaneEdgeι (shiftWordInt W n) 0 e) = lemma38StartEdgeι W n e
  

  rot : ∀ (H : WholePlaneRotationHypothesis W)
    (H' : WholePlaneRotationHypothesis (shiftWordInt W n))
    (x : WholePlaneDart (shiftWordInt W n)),
    dart (wholePlaneRotation (shiftWordInt W n) H' x) =
      wholePlaneRotation W H (dart x)

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
private noncomputable def wholePlaneStartIsoNat (W : ℤ → Fin 3) (m : ℕ) :
    WholePlaneStartIso W (m : ℤ) := by
  let ψ := natShiftIsoOfEq W (shiftWordInt W (m : ℤ)) m
    (shiftWordInt_nat W m)
  refine {
    vertex := ψ.vertex.symm
    edge := ψ.edge.symm
    dart := Equiv.prodCongr ψ.edge.symm (Equiv.refl Bool)
    dart_apply := ?_
    west := ?_
    east := ?_
    present := ?_
    iota_vertex := ?_
    iota_edge := ?_
    rot := ?_ }
  · intro d
    rfl
  · intro e
    apply ψ.vertex.injective
    simpa using (ψ.west (ψ.edge.symm e)).symm
  · intro e
    apply ψ.vertex.injective
    simpa using (ψ.east (ψ.edge.symm e)).symm
  · intro e
    simpa using (ψ.present (ψ.edge.symm e)).symm
  · intro v
    let u := wholePlaneVertexTrans (shiftWordInt W (m : ℤ)) 0 m
      (Nat.zero_le m) v
    have ht := congrFun (wholePlaneVertexι_trans
      (shiftWordInt W (m : ℤ)) 0 m (Nat.zero_le m)) v
    calc
      ψ.vertex.symm (wholePlaneVertexι (shiftWordInt W (m : ℤ)) 0 v) =
          ψ.vertex.symm
            (wholePlaneVertexι (shiftWordInt W (m : ℤ)) m u) := by
        simpa [u] using (congrArg ψ.vertex.symm ht).symm
      _ = wholePlaneVertexι W 0 u := by
        apply ψ.vertex.injective
        simpa [u] using (ψ.vertex_iota 0 u).symm
      _ = lemma38StartVertexι W (m : ℤ) v := (startVertexIotaNat W m v).symm
  · intro e
    let u := wholePlaneEdgeTrans (shiftWordInt W (m : ℤ)) 0 m
      (Nat.zero_le m) e
    have ht := congrFun (wholePlaneEdgeι_trans
      (shiftWordInt W (m : ℤ)) 0 m (Nat.zero_le m)) e
    calc
      ψ.edge.symm (wholePlaneEdgeι (shiftWordInt W (m : ℤ)) 0 e) =
          ψ.edge.symm (wholePlaneEdgeι (shiftWordInt W (m : ℤ)) m u) := by
        simpa [u] using (congrArg ψ.edge.symm ht).symm
      _ = wholePlaneEdgeι W 0 u := by
        apply ψ.edge.injective
        simpa [u] using (ψ.edge_iota 0 u).symm
      _ = lemma38StartEdgeι W (m : ℤ) e := (startEdgeIotaNat W m e).symm
  · intro H H' x
    have hr := ψ.rot H H' (ψ.dart.symm x)
    have hrot : wholePlaneRotation W H (ψ.dart.symm x) =
        ψ.dart.symm (wholePlaneRotation (shiftWordInt W (m : ℤ)) H' x) := by
      simpa using congrArg ψ.dart.symm hr
    exact hrot.symm

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
private noncomputable def wholePlaneStartIsoNeg (W : ℤ → Fin 3) (k : ℕ) :
    WholePlaneStartIso W (Int.negSucc k) := by
  let V := shiftWordInt W (Int.negSucc k)
  let N := k + 1
  have hword : W = shiftWord V N := by
    funext i
    apply congrArg W
    omega
  let ψ := natShiftIsoOfEq V W N hword
  refine {
    vertex := ψ.vertex
    edge := ψ.edge
    dart := ψ.dart
    dart_apply := ψ.dart_apply
    west := ?_
    east := ?_
    present := ?_
    iota_vertex := ?_
    iota_edge := ?_
    rot := ?_ }
  · exact ψ.west
  · exact ψ.east
  · exact ψ.present
  · intro v
    have hn : (Int.negSucc k : ℤ) ≤ 0 := by omega
    simpa [V, N, lemma38StartVertexι, hn] using (ψ.vertex_iota 0 v)
  · intro e
    have hn : (Int.negSucc k : ℤ) ≤ 0 := by omega
    simpa [V, N, lemma38StartEdgeι, hn] using (ψ.edge_iota 0 e)
  · intro H H' x
    exact ψ.rot H' H x

/-- Helper toward Lemma 3.10 (lem-uibot-bdy, integer starts: canonical reindexing -/
theorem wholePlaneStartIso_nonempty (W : ℤ → Fin 3) (n : ℤ) :
    Nonempty (WholePlaneStartIso W n) := by
  cases n with
  | ofNat m => exact ⟨wholePlaneStartIsoNat W m⟩
  | negSucc k => exact ⟨wholePlaneStartIsoNeg W k⟩

end DirectedDistances.KMSW
