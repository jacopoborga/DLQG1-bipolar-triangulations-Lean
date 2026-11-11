module

public import DirectedDistances.KMSW.KMSWWindowInfiniteMaps
public import DirectedDistances.KMSW.CutEquivalence
import DirectedDistances.KMSW.InfiniteRotation









public section
namespace DirectedDistances.KMSW

/-- Shifted one-sided code for the helper toward F4c -/
@[expose] def shiftedStream (W : ℤ → Fin 3) (N : ℕ) : ℕ → Fin 3 :=
  fun i => W ((i : ℤ) - N)

/-- Nested shifts agree in the helper toward F4c -/
theorem shiftedStream_shift (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    (fun i => shiftedStream W N' ((N' - N) + i)) = shiftedStream W N := by
  funext i
  unfold shiftedStream
  congr 1
  omega

/-- Zero-start edge identity for the helper toward F4c -/
theorem kmswWindowEdgeMapInf_zero_start (w : ℕ → Fin 3) :
    kmswWindowEdgeMapInf w 0 = id := by
  funext e
  have hw : (fun i => w (0 + i)) = w := by
    funext i
    rw [Nat.zero_add]
  have hc := kmswWindowEdgeMapInf_comp w 0 0 e
  rw [hw, Nat.zero_add] at hc
  exact kmswWindowEdgeMapInf_injective w 0 hc

/-- Edge transition in the helper toward F4c -/
@[expose] def wholePlaneEdgeTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowEdgeMapInf (shiftedStream W N') (N' - N)

/-- Vertex transition in the helper toward F4c -/
@[expose] def wholePlaneVertexTrans (W : ℤ → Fin 3) (N N' : ℕ) (_h : N ≤ N') :
    ℕ → ℕ :=
  kmswWindowVertexMapInf (shiftedStream W N') (N' - N)

/-- Identity edge transition for the helper toward F4c -/
theorem wholePlaneEdgeTrans_self (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneEdgeTrans W N N (Nat.le_refl N) = id := by
  simp only [wholePlaneEdgeTrans, Nat.sub_self, kmswWindowEdgeMapInf_zero_start]

/-- Identity vertex transition for the helper toward F4c -/
theorem wholePlaneVertexTrans_self (W : ℤ → Fin 3) (N : ℕ) :
    wholePlaneVertexTrans W N N (Nat.le_refl N) = id := by
  simp only [wholePlaneVertexTrans, Nat.sub_self, kmswWindowVertexMapInf_zero_start]

/-- Functorial edge transitions for the helper toward F4c -/
theorem wholePlaneEdgeTrans_comp (W : ℤ → Fin 3) (N N' N'' : ℕ)
    (h : N ≤ N') (h' : N' ≤ N'') :
    wholePlaneEdgeTrans W N' N'' h' ∘ wholePlaneEdgeTrans W N N' h =
      wholePlaneEdgeTrans W N N'' (h.trans h') := by
  funext e
  dsimp only [Function.comp_def, wholePlaneEdgeTrans]
  rw [← shiftedStream_shift W N' N'' h', kmswWindowEdgeMapInf_comp]
  congr 1
  omega

/-- Functorial vertex transitions for the helper toward F4c -/
theorem wholePlaneVertexTrans_comp (W : ℤ → Fin 3) (N N' N'' : ℕ)
    (h : N ≤ N') (h' : N' ≤ N'') :
    wholePlaneVertexTrans W N' N'' h' ∘ wholePlaneVertexTrans W N N' h =
      wholePlaneVertexTrans W N N'' (h.trans h') := by
  funext v
  dsimp only [Function.comp_def, wholePlaneVertexTrans]
  rw [← shiftedStream_shift W N' N'' h', kmswWindowVertexMapInf_comp]
  congr 1
  omega

/-- Injective edge transitions for the helper toward F4c -/
theorem wholePlaneEdgeTrans_injective (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    Function.Injective (wholePlaneEdgeTrans W N N' h) :=
  kmswWindowEdgeMapInf_injective (shiftedStream W N') (N' - N)

/-- Injective vertex transitions for the helper toward F4c -/
theorem wholePlaneVertexTrans_injective (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    Function.Injective (wholePlaneVertexTrans W N N' h) :=
  kmswWindowVertexMapInf_injective (shiftedStream W N') (N' - N)

private theorem commonImage_equivalence
    (T : (N N' : ℕ) → N ≤ N' → ℕ → ℕ)
    (hcomp : ∀ (N N' N'' : ℕ) (h : N ≤ N') (h' : N' ≤ N''),
      T N' N'' h' ∘ T N N' h = T N N'' (h.trans h')) :
    Equivalence (fun (a b : Σ _ : ℕ, ℕ) =>
      ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M, T a.1 M ha a.2 = T b.1 M hb b.2) := by
  constructor
  · intro a
    exact ⟨a.1, Nat.le_refl _, Nat.le_refl _, rfl⟩
  · rintro a b ⟨M, ha, hb, he⟩
    exact ⟨M, hb, ha, he.symm⟩
  · rintro a b c ⟨M, ha, hb, hab⟩ ⟨L, hb', hc, hbc⟩
    have hM : M ≤ max M L := Nat.le_max_left M L
    have hL : L ≤ max M L := Nat.le_max_right M L
    refine ⟨max M L, ha.trans hM, hc.trans hL, ?_⟩
    calc
      T a.1 (max M L) (ha.trans hM) a.2 =
          T M (max M L) hM (T a.1 M ha a.2) :=
        (congrFun (hcomp a.1 M (max M L) ha hM) a.2).symm
      _ = T M (max M L) hM (T b.1 M hb b.2) := congrArg _ hab
      _ = T b.1 (max M L) (hb.trans hM) b.2 :=
        congrFun (hcomp b.1 M (max M L) hb hM) b.2
      _ = T L (max M L) hL (T b.1 L hb' b.2) :=
        (congrFun (hcomp b.1 L (max M L) hb' hL) b.2).symm
      _ = T L (max M L) hL (T c.1 L hc c.2) := congrArg _ hbc
      _ = T c.1 (max M L) (hc.trans hL) c.2 :=
        congrFun (hcomp c.1 L (max M L) hc hL) c.2

/-- Common-stage edge equality for the helper toward F4c -/
@[expose] def wholePlaneEdgeRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneEdgeTrans W a.1 M ha a.2 = wholePlaneEdgeTrans W b.1 M hb b.2

/-- Common-stage vertex equality for the helper toward F4c -/
@[expose] def wholePlaneVertexRel (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ) : Prop :=
  ∃ M, ∃ ha : a.1 ≤ M, ∃ hb : b.1 ≤ M,
    wholePlaneVertexTrans W a.1 M ha a.2 = wholePlaneVertexTrans W b.1 M hb b.2

/-- Edge equivalence for the helper toward F4c -/
theorem wholePlaneEdgeRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneEdgeRel W) :=
  commonImage_equivalence (wholePlaneEdgeTrans W) (wholePlaneEdgeTrans_comp W)

/-- Vertex equivalence for the helper toward F4c -/
theorem wholePlaneVertexRel_equivalence (W : ℤ → Fin 3) :
    Equivalence (wholePlaneVertexRel W) :=
  commonImage_equivalence (wholePlaneVertexTrans W) (wholePlaneVertexTrans_comp W)

/-- Edge setoid for the helper toward F4c -/
@[expose] def wholePlaneEdgeSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneEdgeRel W
  iseqv := wholePlaneEdgeRel_equivalence W

/-- Vertex setoid for the helper toward F4c -/
@[expose] def wholePlaneVertexSetoid (W : ℤ → Fin 3) : Setoid (Σ _ : ℕ, ℕ) where
  r := wholePlaneVertexRel W
  iseqv := wholePlaneVertexRel_equivalence W

/-- Geometric edge colimit for the helper toward F4c, including missing edges
not the paper result. -/
@[expose] def WholePlaneEdge (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneEdgeSetoid W)

/-- Vertex colimit for the helper toward F4c
not the paper result. -/
@[expose] def WholePlaneVertex (W : ℤ → Fin 3) : Type :=
  Quotient (wholePlaneVertexSetoid W)

/-- Canonical edge map for the helper toward F4c -/
@[expose] def wholePlaneEdgeι (W : ℤ → Fin 3) (N : ℕ) (e : ℕ) : WholePlaneEdge W :=
  Quotient.mk (wholePlaneEdgeSetoid W) ⟨N, e⟩

/-- Canonical vertex map for the helper toward F4c -/
@[expose] def wholePlaneVertexι (W : ℤ → Fin 3) (N : ℕ) (v : ℕ) : WholePlaneVertex W :=
  Quotient.mk (wholePlaneVertexSetoid W) ⟨N, v⟩

/-- Each one-sided edge carrier embeds in the helper toward F4c -/
theorem wholePlaneEdgeι_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneEdgeι W N) := by
  intro e f hef
  obtain ⟨M, hN, _, he⟩ := Quotient.exact hef
  exact wholePlaneEdgeTrans_injective W N M hN he

/-- Each one-sided vertex carrier embeds in the helper toward F4c -/
theorem wholePlaneVertexι_injective (W : ℤ → Fin 3) (N : ℕ) :
    Function.Injective (wholePlaneVertexι W N) := by
  intro v z hvz
  obtain ⟨M, hN, _, hv⟩ := Quotient.exact hvz
  exact wholePlaneVertexTrans_injective W N M hN hv

/-- The canonical edge maps commute with transitions in the helper toward F4c -/
theorem wholePlaneEdgeι_trans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    wholePlaneEdgeι W N' ∘ wholePlaneEdgeTrans W N N' h = wholePlaneEdgeι W N := by
  funext e
  apply Quotient.sound
  refine ⟨N', Nat.le_refl _, h, ?_⟩
  change wholePlaneEdgeTrans W N' N' (Nat.le_refl N')
      (wholePlaneEdgeTrans W N N' h e) = wholePlaneEdgeTrans W N N' h e
  exact congrFun (wholePlaneEdgeTrans_self W N') (wholePlaneEdgeTrans W N N' h e)

/-- The canonical vertex maps commute with transitions in the helper toward F4c -/
theorem wholePlaneVertexι_trans (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') :
    wholePlaneVertexι W N' ∘ wholePlaneVertexTrans W N N' h =
      wholePlaneVertexι W N := by
  funext v
  apply Quotient.sound
  refine ⟨N', Nat.le_refl _, h, ?_⟩
  change wholePlaneVertexTrans W N' N' (Nat.le_refl N')
      (wholePlaneVertexTrans W N N' h v) = wholePlaneVertexTrans W N N' h v
  exact congrFun (wholePlaneVertexTrans_self W N') (wholePlaneVertexTrans W N N' h v)

/-- West endpoints commute with infinite window maps in the helper toward F4c -/
theorem kmswWindowEdgeMapInf_edgeWest (w : ℕ → Fin 3) (s e : ℕ) :
    edgeWest w (kmswWindowEdgeMapInf w s e) =
      kmswWindowVertexMapInf w s (edgeWest (fun i => w (s + i)) e) := by
  have he := kmsw_edge_allocated_by_self (fun i => w (s + i)) e
  have hb : kmswWindowEdgeMapInf w s e < (kmswStage w (s + e)).nextEdge :=
    (kmswWindowPatchData_rel w s e).edge_bound e he
  have hw := kmswWindowEdgeMapInf_west w s e e he
  rw [(edge_endpoints_eq w hb).1,
    (edge_endpoints_eq (fun i => w (s + i)) he).1] at hw
  exact hw

/-- East endpoints commute with infinite window maps in the helper toward F4c -/
theorem kmswWindowEdgeMapInf_edgeEast (w : ℕ → Fin 3) (s e : ℕ) :
    edgeEast w (kmswWindowEdgeMapInf w s e) =
      kmswWindowVertexMapInf w s (edgeEast (fun i => w (s + i)) e) := by
  have he := kmsw_edge_allocated_by_self (fun i => w (s + i)) e
  have hb : kmswWindowEdgeMapInf w s e < (kmswStage w (s + e)).nextEdge :=
    (kmswWindowPatchData_rel w s e).edge_bound e he
  have hw := kmswWindowEdgeMapInf_east w s e e he
  rw [(edge_endpoints_eq w hb).2,
    (edge_endpoints_eq (fun i => w (s + i)) he).2] at hw
  exact hw

/-- West endpoints commute with transitions in the helper toward F4c -/
theorem wholePlaneEdgeTrans_west (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') (e : ℕ) :
    edgeWest (shiftedStream W N') (wholePlaneEdgeTrans W N N' h e) =
      wholePlaneVertexTrans W N N' h (edgeWest (shiftedStream W N) e) := by
  simpa only [wholePlaneEdgeTrans, wholePlaneVertexTrans, shiftedStream_shift W N N' h]
    using kmswWindowEdgeMapInf_edgeWest (shiftedStream W N') (N' - N) e

/-- East endpoints commute with transitions in the helper toward F4c -/
theorem wholePlaneEdgeTrans_east (W : ℤ → Fin 3) (N N' : ℕ) (h : N ≤ N') (e : ℕ) :
    edgeEast (shiftedStream W N') (wholePlaneEdgeTrans W N N' h e) =
      wholePlaneVertexTrans W N N' h (edgeEast (shiftedStream W N) e) := by
  simpa only [wholePlaneEdgeTrans, wholePlaneVertexTrans, shiftedStream_shift W N N' h]
    using kmswWindowEdgeMapInf_edgeEast (shiftedStream W N') (N' - N) e

/-- Equivalent edge representatives have equal west endpoints in the helper toward F4c -/
theorem wholePlaneEdgeRel_west (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeWest (shiftedStream W b.1) b.2) := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply Quotient.sound
  refine ⟨M, ha, hb, ?_⟩
  change wholePlaneVertexTrans W a.1 M ha (edgeWest (shiftedStream W a.1) a.2) =
    wholePlaneVertexTrans W b.1 M hb (edgeWest (shiftedStream W b.1) b.2)
  rw [← wholePlaneEdgeTrans_west, ← wholePlaneEdgeTrans_west, he]

/-- Equivalent edge representatives have equal east endpoints in the helper toward F4c -/
theorem wholePlaneEdgeRel_east (W : ℤ → Fin 3) (a b : Σ _ : ℕ, ℕ)
    (hab : wholePlaneEdgeRel W a b) :
    wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2) =
      wholePlaneVertexι W b.1 (edgeEast (shiftedStream W b.1) b.2) := by
  obtain ⟨M, ha, hb, he⟩ := hab
  apply Quotient.sound
  refine ⟨M, ha, hb, ?_⟩
  change wholePlaneVertexTrans W a.1 M ha (edgeEast (shiftedStream W a.1) a.2) =
    wholePlaneVertexTrans W b.1 M hb (edgeEast (shiftedStream W b.1) b.2)
  rw [← wholePlaneEdgeTrans_east, ← wholePlaneEdgeTrans_east, he]

/-- Well-defined geometric west endpoint for the helper toward F4c -/
@[expose] def wholePlaneEdgeWest (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeWest (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_west W)

/-- Well-defined geometric east endpoint for the helper toward F4c -/
@[expose] def wholePlaneEdgeEast (W : ℤ → Fin 3) : WholePlaneEdge W → WholePlaneVertex W :=
  Quotient.lift (fun a => wholePlaneVertexι W a.1 (edgeEast (shiftedStream W a.1) a.2))
    (wholePlaneEdgeRel_east W)

/-- West endpoint compatibility with the canonical maps in the helper toward F4c -/
theorem wholePlaneEdgeWest_ι (W : ℤ → Fin 3) (N e : ℕ) :
    wholePlaneEdgeWest W (wholePlaneEdgeι W N e) =
      wholePlaneVertexι W N (edgeWest (shiftedStream W N) e) := rfl

/-- East endpoint compatibility with the canonical maps in the helper toward F4c -/
theorem wholePlaneEdgeEast_ι (W : ℤ → Fin 3) (N e : ℕ) :
    wholePlaneEdgeEast W (wholePlaneEdgeι W N e) =
      wholePlaneVertexι W N (edgeEast (shiftedStream W N) e) := rfl

end DirectedDistances.KMSW
