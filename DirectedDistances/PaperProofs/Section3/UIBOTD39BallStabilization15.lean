/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.UIBOTD39BallStabilization14
public import DirectedDistances.PlanarMap.EdgeRestrictedDrawing

/-! # Original retained faces of arbitrary whole-plane drawings

A finite connected restriction retaining the complete frontier identifies
original face orbits. No ambient homeomorphism is assumed. -/

public section
noncomputable section
namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open DirectedDistances.PaperProofs.Section5
open Set Metric Topology

private theorem window_endpoint (W : ℤ → Fin 3) (N m : ℕ)
    (a : StageDart (kmswStage (shiftedStream W N) m).nextEdge) :
    wholePlaneDartVertex W (wholePlaneDartι W N (a.1.val, a.2)) =
      wholePlaneVertexι W N (stageEndpoint (kmswStage (shiftedStream W N) m) a) := by
  rw [wholePlaneDartVertex_ι]
  obtain ⟨hw, he⟩ := edge_endpoints_eq (shiftedStream W N) a.1.isLt
  cases hb : a.2 <;> simp only [kmswLimitDartVertex, stageEndpoint,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem window_sameCycle_of_border_of_orbit_subset
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N m : ℕ) (F : G.Face)
    (d e : WholePlaneDart W) (hd : G.dartBorders d F) (he : G.dartBorders e F)
    (hdS : ∃ a : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
      wholePlaneDartι W N (a.1.val, a.2) = d)
    (heS : ∃ a : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
      wholePlaneDartι W N (a.1.val, a.2) = e)
    (ho : ∀ x, (wholePlaneFaceSucc W H).SameCycle d x →
      ∃ a : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
        wholePlaneDartι W N (a.1.val, a.2) = x) :
    (wholePlaneFaceSucc W H).SameCycle d e := by
  classical
  let u := shiftedStream W N
  let I : StageDart (kmswStage u m).nextEdge → WholePlaneDart W :=
    fun a => wholePlaneDartι W N (a.1.val, a.2)
  let S : Set (WholePlaneDart W) := Set.range I
  have hS : S.Finite := Set.finite_range I
  let : Fintype S := hS.fintype
  have hflip : ∀ a, a ∈ S ↔ wholePlaneDartFlip W a ∈ S := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨edgeFlip _ b, rfl⟩
    · rintro ⟨b, hb⟩
      refine ⟨edgeFlip _ b, ?_⟩
      change wholePlaneDartFlip W (I b) = a
      rw [hb]
      exact G.flip_involutive a
  let Q := restrictDrawing G S hflip
  let vQ := restrictedVertex G S
  have hvQ : Function.Surjective vQ := by
    rintro ⟨v, a, ha, hav⟩
    exact ⟨⟨a, ha⟩, Subtype.ext hav⟩
  let B : D39FiniteBall := {
    D := S
    map := {
      edgeInv := {
        toFun := restrictedFlip G S hflip
        invFun := restrictedFlip G S hflip
        left_inv := Q.flip_involutive
        right_inv := Q.flip_involutive }
      edgeInv_invol := Q.flip_involutive
      edgeInv_ne := Q.flip_ne
      rot := drawingFirstReturnPerm G S }
    missing := fun _ => False
    tail := fun _ => False
    rootDart := ⟨I (kmswRootedStage u m).root, ⟨_, rfl⟩⟩
    original := Set.univ
    original_closed := fun _ => Iff.rfl }
  let J : StageDart (kmswStage u m).nextEdge → B.D := fun a => ⟨I a, ⟨a, rfl⟩⟩
  have hJ : Function.Surjective J := by
    rintro ⟨a, b, hb⟩
    exact ⟨b, Subtype.ext hb⟩
  have hconn : ∀ a b : B.D, Relation.EqvGen
      (fun x y => B.map.rot x = y ∨ B.map.edgeInv x = y) a b := by
    intro a b
    obtain ⟨a, rfl⟩ := hJ a
    obtain ⟨b, rfl⟩ := hJ b
    have hv (x y : StageDart (kmswStage u m).nextEdge)
        (hxy : stageEndpoint (kmswStage u m) x = stageEndpoint (kmswStage u m) y) :
        vQ (J x) = vQ (J y) := by
      apply Subtype.ext
      change wholePlaneDartVertex W (I x) = wholePlaneDartVertex W (I y)
      rw [window_endpoint, window_endpoint, hxy]
    have hc := kmswMap_isConnected u m a b
    induction hc with
    | refl => exact Relation.EqvGen.refl _
    | @tail b c _ hbc ih =>
      apply ih.trans
      rcases hbc with h | h | h | h
      · subst c
        apply CombinatorialMap.eqvGen_of_rotation_sameCycle B.map.rot _ (fun _ => Or.inl rfl)
        apply Q.rot_sameCycle_of_vert_eq
        apply hv
        exact (stageRot_sameCycle_iff_endpoint_eq u m _ _).mp
          (Equiv.Perm.SameCycle.rfl.apply_right)
      · subst c
        apply CombinatorialMap.eqvGen_of_rotation_sameCycle B.map.rot _ (fun _ => Or.inl rfl)
        apply Q.rot_sameCycle_of_vert_eq
        apply hv
        exact (stageRot_sameCycle_iff_endpoint_eq u m _ _).mp
          (Equiv.Perm.SameCycle.rfl.symm_apply_right)
      · subst c
        exact Relation.EqvGen.rel _ _ (Or.inr rfl)
      · subst c
        exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  obtain ⟨z, hz, hF⟩ := F.property
  have hzQ : z ∉ Q.image := fun h => hz (restrictDrawing_image_subset G S hflip h)
  let K : Q.Face := ⟨connectedComponentIn Q.imageᶜ z, z, hzQ, rfl⟩
  have hsub : F.val ⊆ K.val := by
    rw [hF]
    exact connectedComponentIn_mono z
      (compl_subset_compl.mpr (restrictDrawing_image_subset G S hflip))
  have hborder (x : B.D) (hx : G.dartBorders x.val F) : Q.dartBorders x K := by
    obtain ⟨δ, hδ, hx⟩ := hx
    exact ⟨δ, hδ, fun t ε ht htδ hε hεδ => hsub (hx t ε ht htδ hε hεδ)⟩
  let a : B.D := ⟨d, hdS⟩
  let b : B.D := ⟨e, heS⟩
  have hcycle : B.map.faceSucc.SameCycle a b := by
    apply B.plDartFace_sameCycle_of_eq vQ Q hvQ hconn
    exact ((B.plDartFace_eq_iff vQ Q hvQ a K).mpr (hborder a hd)).trans
      ((B.plDartFace_eq_iff vQ Q hvQ b K).mpr (hborder b he)).symm
  have hstep (x : B.D) (hx : (wholePlaneFaceSucc W H).SameCycle d x.val) :
      (B.map.faceSucc x).val = wholePlaneFaceSucc W H x.val := by
    let y : B.D := ⟨wholePlaneFaceSucc W H x.val, ho _ hx.apply_right⟩
    have hrot : B.map.rot y = B.map.edgeInv x := by
      apply Subtype.ext
      have hnext : wholePlaneRotation W H y.val ∈ S := by
        change wholePlaneRotation W H ((wholePlaneRotation W H).symm
          (wholePlaneDartFlip W x.val)) ∈ S
        rw [Equiv.apply_symm_apply]
        exact (hflip x.val).mp x.property
      rw [show (B.map.rot y).val = wholePlaneRotation W H y.val from
        drawingFirstReturn_eq_next G S y hnext]
      exact (wholePlaneRotation W H).apply_symm_apply _
    have hy : B.map.faceSucc x = y := by
      apply B.map.rot.injective
      change B.map.rot (B.map.rot.symm (B.map.edgeInv x)) = B.map.rot y
      rw [Equiv.apply_symm_apply, hrot]
    exact congrArg Subtype.val hy
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hpow (k : ℕ) : ((B.map.faceSucc ^ k) a).val =
      ((wholePlaneFaceSucc W H) ^ k) d := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      rw [hstep, ih]
      exact ⟨(k : ℤ), by simpa only [zpow_natCast] using ih.symm⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, ← hpow, hk]

/-- Helper toward Proposition 3.9: all and only the darts of one
whole-plane face-successor orbit border a given retained original face,
for every whole-plane drawing under the original capture hypotheses. -/
theorem uibotWholePlane_retainedFace_sameCycle_iff
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : G.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r)
    (d e : WholePlaneDart W)
    (hd : G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv F)) :
    G.dartBorders e (G.toPlaneGraphDrawingFaceEquiv F) ↔
      (wholePlaneFaceSucc W H).SameCycle d e := by
  have hm (a : WholePlaneDart W)
      (ha : G.dartBorders a (G.toPlaneGraphDrawingFaceEquiv F)) :
      ∃ b : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge,
        wholePlaneDartι W N (b.1.val, b.2) = a := by
    obtain ⟨b, hb, _⟩ := uibotWholePlane_retainedFace_dart_allocated
      W H G hp N r hcap F hF a ha
    exact ⟨b, hb⟩
  constructor
  · intro he
    apply window_sameCycle_of_border_of_orbit_subset W H G N (2 * N) _ d e hd he
      (hm d hd) (hm e he)
    intro x hx
    exact hm x ((uibotWholePlane_sameCycle_border_iff W H G d x hx _).mp hd)
  · intro hde
    exact (uibotWholePlane_sameCycle_border_iff W H G d e hde _).mp hd

private theorem wholePlaneDart_rep_at_later (W : ℤ → Fin 3)
    (d : WholePlaneDart W) (N : ℕ) (x : ℕ × Bool)
    (hx : wholePlaneDartι W N x = d) (M : ℕ) (hNM : N ≤ M) :
    wholePlaneDartι W M (wholePlaneDartTrans W N M hNM x) = d := by
  change wholePlaneDartι W N x = (d.1, d.2) at hx
  change wholePlaneDartι W M (wholePlaneDartTrans W N M hNM x) = (d.1, d.2)
  exact (congrFun (wholePlaneDartι_trans W N M hNM) x).trans hx

private theorem wholePlaneDart_finite_common_run (W : ℤ → Fin 3)
    (s : Finset (WholePlaneDart W)) :
    ∃ N, ∀ d ∈ s, ∃ x, wholePlaneDartι W N x = d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert d s hds ih =>
      obtain ⟨⟨N, x⟩, hx⟩ := Quotient.exists_rep d.1
      obtain ⟨M, hs⟩ := ih
      let L := max N M
      have hNL : N ≤ L := Nat.le_max_left N M
      have hML : M ≤ L := Nat.le_max_right N M
      refine ⟨L, ?_⟩
      intro e he
      simp only [Finset.mem_insert] at he
      rcases he with hEq | he
      · refine ⟨wholePlaneDartTrans W N L hNL (x, d.2), ?_⟩
        exact (wholePlaneDart_rep_at_later W d N (x, d.2)
          (Prod.ext hx rfl) L hNL).trans hEq.symm
      · obtain ⟨y, hy⟩ := hs e he
        exact ⟨wholePlaneDartTrans W M L hML y,
          wholePlaneDart_rep_at_later W e M y hy L hML⟩

private theorem finite_common_stage (W : ℤ → Fin 3) (s : Finset (WholePlaneDart W)) :
    ∃ N m, ∀ d ∈ s, ∃ a : StageDart (kmswStage (shiftedStream W N) m).nextEdge,
      wholePlaneDartι W N (a.1.val, a.2) = d := by
  classical
  obtain ⟨N, hN⟩ := wholePlaneDart_finite_common_run W s
  choose x hx using (fun d : s => hN d.val d.property)
  let m := s.attach.sup (fun d => (x d).1)
  refine ⟨N, m, ?_⟩
  intro d hd
  have hm : (x ⟨d, hd⟩).1 ≤ m := Finset.le_sup (f := fun d => (x d).1)
    (Finset.mem_attach _ _)
  have he := (kmsw_edge_allocated_by_self (shiftedStream W N) (x ⟨d, hd⟩).1).trans_le
    (kmswStage_nextEdge_mono (shiftedStream W N) hm)
  exact ⟨(⟨(x ⟨d, hd⟩).1, he⟩, (x ⟨d, hd⟩).2), hx ⟨d, hd⟩⟩

private theorem finite_orbit_sameCycle_of_border
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (F : G.Face) (d e : WholePlaneDart W)
    (hd : G.dartBorders d F) (he : G.dartBorders e F)
    (hfin : {x | (wholePlaneFaceSucc W H).SameCycle d x}.Finite) :
    (wholePlaneFaceSucc W H).SameCycle d e := by
  classical
  let s := insert e hfin.toFinset
  obtain ⟨N, m, hs⟩ := finite_common_stage W s
  have hmem (x) (hx : (wholePlaneFaceSucc W H).SameCycle d x) : x ∈ s :=
    Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hx)
  exact window_sameCycle_of_border_of_orbit_subset W H G N m F d e hd he
    (hs d (hmem d Equiv.Perm.SameCycle.rfl)) (hs e (Finset.mem_insert_self _ _))
    (fun x hx => hs x (hmem x hx))

/-- Helper toward Proposition 3.9: every centered triangle label has
exactly one original complementary face in an arbitrary whole-plane drawing,
with the complete bordering-dart relation proved in both directions. -/
theorem uibotWholePlane_windowTriangleFace_existsUnique
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) :
    ∃! F : G.toPlaneGraphDrawing.Face,
      ∀ d, G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
          wholePlaneDartι W N a = d := by
  classical
  let d := wholePlaneDartι W N (stageTriangleDartTriple (shiftedStream W N) q).1
  have hfirst : (stageTriangleDartTriple (shiftedStream W N) q).1 ∈
      stageTriangleDartList (shiftedStream W N) q := by
    simp only [stageTriangleDartList, List.mem_cons, List.not_mem_nil, or_false, true_or]
  have hfin : {x | (wholePlaneFaceSucc W H).SameCycle d x}.Finite := by
    have hlist : {a | a ∈ stageTriangleDartList (shiftedStream W N) q}.Finite := by
      apply (stageTriangleDartList (shiftedStream W N) q).toFinset.finite_toSet.subset
      intro a ha
      exact List.mem_toFinset.mpr ha
    apply (hlist.image (wholePlaneDartι W N)).subset
    intro x hx
    exact (wholePlane_stageTriangle_sameCycle_iff W H N q x).mp hx
  obtain ⟨F, hdF⟩ := G.dartBorders_exists_of_wedge_compl d
    (G.wedgeIn_compl_image (uibhbot_faceOrbit_dartVertex_surjective W H)
      _ _ (G.initial_nonzero d))
  have hchar (e : WholePlaneDart W) : G.dartBorders e F ↔
      ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
        wholePlaneDartι W N a = e := by
    constructor
    · intro he
      exact (wholePlane_stageTriangle_sameCycle_iff W H N q e).mp
        (finite_orbit_sameCycle_of_border W H G F d e hdF he hfin)
    · intro he
      exact (uibotWholePlane_sameCycle_border_iff W H G d e
        ((wholePlane_stageTriangle_sameCycle_iff W H N q e).mpr he) F).mp hdF
  refine ⟨G.toPlaneGraphDrawingFaceEquiv.symm F, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hchar
  · intro K hK
    apply G.toPlaneGraphDrawingFaceEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact G.dartBorders_face_unique d _ F ((hK d).mpr ⟨_, hfirst, rfl⟩) hdF

/-- Helper toward Proposition 3.9: the original triangle face in any
whole-plane drawing, chosen after existence, uniqueness and its full
bordering-dart characterization have been proved. -/
@[expose] def uibotWholePlaneWindowTriangleFace
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) : G.toPlaneGraphDrawing.Face :=
  (uibotWholePlane_windowTriangleFace_existsUnique W H G N q).exists.choose

/-- Helper toward Proposition 3.9: the full characterization of the
chosen original triangle face holds for arbitrary whole-plane drawings. -/
theorem uibotWholePlaneWindowTriangleFace_border
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H) (N : ℕ)
    (q : TriangleCreationTime (shiftedStream W N)) (d : WholePlaneDart W) :
    G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv
      (uibotWholePlaneWindowTriangleFace W H G N q)) ↔
      ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
        wholePlaneDartι W N a = d :=
  (uibotWholePlane_windowTriangleFace_existsUnique W H G N q).exists.choose_spec d

section WholePlaneFaces
variable (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
  (G : WholePlaneDrawing W H)

/-- Helper toward Proposition 3.9: different centered creation labels
give different original whole-plane faces, without a retention assumption. -/
theorem uibotWholePlaneWindowTriangleFace_injective (N : ℕ) :
    Function.Injective (uibotWholePlaneWindowTriangleFace W H G N) := by
  intro q p he
  let a := (stageTriangleDartTriple (shiftedStream W N) q).1
  have ha : a ∈ stageTriangleDartList (shiftedStream W N) q := by
    simp only [a, stageTriangleDartList, List.mem_cons, List.not_mem_nil,
      or_false, true_or]
  have hd := (uibotWholePlaneWindowTriangleFace_border W H G N q
    (wholePlaneDartι W N a)).mpr ⟨a, ha, rfl⟩
  rw [he] at hd
  obtain ⟨b, hb, hba⟩ :=
    (uibotWholePlaneWindowTriangleFace_border W H G N p _).mp hd
  have hba' : b = a := wholePlaneDartι_injective W N hba
  have ham : a ∈ stageTriangleDartList (shiftedStream W N) p := hba' ▸ hb
  by_contra hne
  exact (List.disjoint_left.mp (stageTriangleDartLists_disjoint
    (shiftedStream W N) (max q.val p.val + 1) q p
    (by omega) (by omega) hne)) ha ham

private theorem window_vertex_mem (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r x : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    wholePlaneVertexι W N x ∈ d39GeomBallVertices (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r ↔
    x ∈ kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
      (activeInitial (shiftedStream W N) N) := by
  rw [uibotWholePlaneGeometricBallVertices_eq_window W H G hp N r hcap]
  constructor
  · rintro ⟨y, hy, he⟩
    exact wholePlaneVertexι_injective W N he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Helper toward Proposition 3.9: retention of an original whole-plane triangle
face is exactly the finite centered-window test on all its dart endpoints.
The equivalence uses the full closure-based original-face definition. -/
theorem uibotWholePlaneWindowTriangleFace_retained_iff
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (q : TriangleCreationTime (shiftedStream W N)) :
    uibotWholePlaneWindowTriangleFace W H G N q ∈
      d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r ↔
    ∀ a ∈ stageTriangleDartList (shiftedStream W N) q,
      kmswLimitDartVertex (shiftedStream W N) a ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N) ∧
      kmswLimitDartVertex (shiftedStream W N) (a.1, !a.2) ∈
        kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
          (activeInitial (shiftedStream W N) N) := by
  rw [uibotWholePlane_face_retained_iff_borderEndpoints W H G hp N r hcap]
  have hend (a : ℕ × Bool) :
      wholePlaneDartFlip W (wholePlaneDartι W N a) =
        wholePlaneDartι W N (a.1, !a.2) := rfl
  constructor
  · intro h a ha
    have he := h _ ((uibotWholePlaneWindowTriangleFace_border W H G N q _).mpr
      ⟨a, ha, rfl⟩)
    rw [hend, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι] at he
    exact ⟨(window_vertex_mem W H G hp N r _ hcap).mp he.1,
      (window_vertex_mem W H G hp N r _ hcap).mp he.2⟩
  · intro h d hd
    obtain ⟨a, ha, rfl⟩ :=
      (uibotWholePlaneWindowTriangleFace_border W H G N q d).mp hd
    rw [hend, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι]
    exact ⟨(window_vertex_mem W H G hp N r _ hcap).mpr (h a ha).1,
      (window_vertex_mem W H G hp N r _ hcap).mpr (h a ha).2⟩

private theorem endpoint_limit (u : ℕ → Fin 3) (m : ℕ)
    (a : StageDart (kmswStage u m).nextEdge) :
    stageEndpoint (kmswStage u m) a = kmswLimitDartVertex u (a.1.val, a.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq u a.1.isLt
  cases hb : a.2 <;> simp only [stageEndpoint, kmswLimitDartVertex,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

private theorem complete_of_not_frontier (u : ℕ → Fin 3) (m v : ℕ)
    (hv : ¬ UpperFrontierEndpoint (kmswStage u m) v) : kmswVertexComplete u m v := by
  intro e he
  by_contra hne
  let t := max m e
  have het : e < (kmswStage u t).nextEdge :=
    (kmsw_edge_allocated_by_self u e).trans_le (kmswStage_nextEdge_mono u (Nat.le_max_right _ _))
  have hno := kmswStage_no_new_incidence_of_not_upperFrontier u m v hv t
    (Nat.le_max_left _ _) e het (by omega)
  rw [(edge_endpoints_eq u het).1, (edge_endpoints_eq u het).2] at hno
  exact he.elim hno.1 hno.2

/-- Helper toward Proposition 3.9: face succession at each captured
opposite endpoint agrees exactly with the centered finite stage, including
the actual dart identities. -/
theorem uibotWholePlane_capturedFaceSucc (N r : ℕ)
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (a : StageDart (kmswStage (shiftedStream W N) (2 * N)).nextEdge)
    (ha : stageEndpoint (kmswStage (shiftedStream W N) (2 * N)) (edgeFlip _ a) ∈
      kmswStageBallVertices (fun _ _ => True) (kmswStage (shiftedStream W N) (2 * N)) r
        (activeInitial (shiftedStream W N) N)) :
    wholePlaneFaceSucc W H (wholePlaneDartι W N (a.1.val, a.2)) =
      wholePlaneDartι W N
        (((kmswMap (shiftedStream W N) (2 * N)).faceSucc a).1.val,
          ((kmswMap (shiftedStream W N) (2 * N)).faceSucc a).2) := by
  let v := stageEndpoint (kmswStage (shiftedStream W N) (2 * N)) (edgeFlip _ a)
  have hv := stageEndpoint_lt_nextVertex (shiftedStream W N) (2 * N) (edgeFlip _ a)
  have hlim : v = kmswLimitDartVertex (shiftedStream W N) (a.1.val, !a.2) :=
    endpoint_limit _ _ (edgeFlip _ a)
  have hf : ∀ M (hNM : N ≤ M), wholePlaneFresh W N M hNM v := by
    intro M hNM
    have hcode : ∀ i < 2 * N, shiftedStream W M (M - N + i) = shiftedStream W N i :=
      fun i _ => congrFun (shiftedStream_shift W N M hNM) i
    have hnew := kmswWindowPatchVertexMap_fresh_for_every_prefix
      (shiftedStream W N) (2 * N) v hv (hcap.1.2.1 v ha).1 (hcap.1.2.1 v ha).2
      (shiftedStream W M) (M - N) hcode
    change (kmswStage (shiftedStream W M) (M - N)).nextVertex ≤
      kmswWindowVertexMapInf (shiftedStream W M) (M - N) v
    rw [kmswWindowVertexMapInf_eq_stage _ _ (2 * N) v (by
      rw [shiftedStream_shift W N M hNM]; exact hv)]
    exact hnew
  have hc := complete_of_not_frontier (shiftedStream W N) (2 * N) v (hcap.2 v ha)
  have hrot := wholePlaneRotation_symm_ι_of_fresh W H N (a.1.val, !a.2)
    (by
      intro M hNM
      change wholePlaneFresh W N M hNM (kmswLimitDartVertex (shiftedStream W N) (a.1.val, !a.2))
      rw [← hlim]
      exact hf M hNM)
  have hs := kmswInfRot_symm_eq_stage (shiftedStream W N) (H.1 N) (2 * N)
    (edgeFlip _ a) hc
  change (wholePlaneRotation W H).symm (wholePlaneDartι W N (a.1.val, !a.2)) = _
  rw [hrot]
  exact congrArg (wholePlaneDartι W N) hs

/-- Helper toward Proposition 3.9: every retained original whole-plane face
has exactly one triangle label created within the centered window. This
exhausts the retained faces, including faces crossing the centered-window boundary. -/
theorem uibotWholePlane_retainedFace_windowTriangle
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (N r : ℕ) (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : (G).toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
      (uibotWholePlaneGeometricRoot W H G) r) :
    ∃! q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
      F = uibotWholePlaneWindowTriangleFace W H G N q := by
  let u := shiftedStream W N
  let m := 2 * N
  let f := (kmswMap u m).faceSucc
  let I := fun a : StageDart (kmswStage u m).nextEdge => wholePlaneDartι W N (a.1.val, a.2)
  let F' := (G).toPlaneGraphDrawingFaceEquiv F
  obtain ⟨d, hd⟩ := (G).face_has_bordering_dart (uibhbot_faceOrbit_dartVertex_surjective W H)
    (wholePlaneDartι W 0 (0, false)) F'
  obtain ⟨a, ha, _⟩ := uibotWholePlane_retainedFace_dart_allocated
    W H G hp N r hcap F hF d hd
  have hab : (G).dartBorders (I a) F' := by
    dsimp only [I]
    rw [ha]
    exact hd
  have hends (b : StageDart (kmswStage u m).nextEdge) (hb : (G).dartBorders (I b) F') :
      stageEndpoint (kmswStage u m) b ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) r (activeInitial u N) ∧
      stageEndpoint (kmswStage u m) (edgeFlip _ b) ∈ kmswStageBallVertices (fun _ _ => True)
        (kmswStage u m) r (activeInitial u N) := by
    have he := (uibotWholePlane_face_retained_iff_borderEndpoints W H G hp N r hcap F).mp hF
      (I b) hb
    have hfl : wholePlaneDartFlip W (I b) = wholePlaneDartι W N (b.1.val, !b.2) := rfl
    change wholePlaneDartVertex W (wholePlaneDartι W N (b.1.val, b.2)) ∈ _ ∧ _ at he
    rw [hfl, wholePlaneDartVertex_ι, wholePlaneDartVertex_ι] at he
    rw [endpoint_limit, endpoint_limit]
    exact ⟨(window_vertex_mem W H G hp N r _ hcap).mp he.1,
      (window_vertex_mem W H G hp N r _ hcap).mp he.2⟩
  have hiter (k : ℕ) : (G).dartBorders (I ((f ^ k) a)) F' := by
    induction k with
    | zero => exact hab
    | succ k ih =>
      have hh := (uibotWholePlane_faceSucc_border_iff W H G
        (I ((f ^ k) a)) F').mpr ih
      rw [uibotWholePlane_capturedFaceSucc W H N r hcap _ (hends _ ih).2] at hh
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hh
  have hnot : a ∉ stageOuterWord u m := by
    intro hao
    let C := familyQ u (monotone_family_all u) m
    obtain ⟨Uc, _, _, hbc⟩ := uibotCanonicalStage_exterior u m
    let b : StageDart (kmswStage u m).nextEdge :=
      (⟨act u m, act_lt_nextEdge u le_rfl⟩, false)
    have hbUL : b.1.val ∈ (kmswStage u m).UL := by
      obtain ⟨xs, hxs⟩ := kmswStage_UL_last u m
      rw [hxs]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hbo : (kmswStageDirectedMap u m).IsOuter b :=
      ((kmswStageDirectedMap_UL_bridge u m b.1).mp hbUL).2.2
    have hao' : (kmswStageDirectedMap u m).IsOuter a := by
      rw [kmswStage_isOuter_iff_boundary]
      have hh := (stageOuterWord_mem_iff u m a).mp hao
      simpa only [List.mem_append, or_comm] using hh
    have hfaces : kmswStageDrawing_leftFace C a = kmswStageDrawing_leftFace C b :=
      ((kmswStageDrawing_leftFace_eq_iff C a Uc).mpr ((hbc a).mpr hao')).trans
        ((kmswStageDrawing_leftFace_eq_iff C b Uc).mpr ((hbc b).mpr hbo)).symm
    have hcyc : f.SameCycle a b := kmswStageDrawing_sameCycle_of_leftFace_eq C a b hfaces
    obtain ⟨k, hk⟩ := hcyc.exists_nat_pow_eq
    have hbm := (hends b (hk ▸ hiter k)).1
    apply hcap.2 _ hbm
    exact Or.inl ⟨b.1.val, List.mem_append_left _ hbUL, Or.inl rfl⟩
  obtain ⟨q, ⟨hq, haq⟩, _⟩ := (stage_dart_partition u m a).resolve_left hnot
  have haq' := (uibotWholePlaneWindowTriangleFace_border W H G N q (I a)).mpr
    ⟨(a.1.val, a.2), haq, rfl⟩
  have he : F = uibotWholePlaneWindowTriangleFace W H G N q :=
    (G).toPlaneGraphDrawingFaceEquiv.injective ((G).dartBorders_face_unique (I a) _ _ hab haq')
  refine ⟨q, ⟨hq, he⟩, ?_⟩
  intro p hp'
  exact uibotWholePlaneWindowTriangleFace_injective W H G N (hp'.2.symm.trans he)

end WholePlaneFaces

private theorem stage_vertex_eq_limit (w : ℕ → Fin 3) (t : ℕ)
    (d : StageDart (kmswStage w t).nextEdge) :
    (stageVertex w t d).val = kmswLimitDartVertex w (d.1.val, d.2) := by
  obtain ⟨hw, he⟩ := edge_endpoints_eq w d.1.isLt
  cases hb : d.2 <;> simp only [stageVertex, stageEndpoint, kmswLimitDartVertex,
    hb, Bool.false_eq_true, ↓reduceIte, hw, he]

/-- Helper toward Proposition 3.9: every retained original finite face
has a centered creation label whose original whole-plane face is retained too.
The complete finite bordering-dart characterization is retained jointly. -/
theorem uibotFiniteRootWindow_retainedFace_wholePlaneTriangle {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (F : P.toPlaneGraphDrawing.Face)
    (hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
      (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r) :
    ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
      (∀ d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) ∧
      uibotWholePlaneWindowTriangleFace W H G N q ∈
        d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
          (uibotWholePlaneGeometricRoot W H G) r := by
  obtain ⟨q, ⟨hq, hchar⟩, _⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
    w j (shiftedStream W N) P U hU hborder hwindow hcap F hF
  refine ⟨q, hq, hchar, ?_⟩
  apply (uibotWholePlaneWindowTriangleFace_retained_iff W H G hp N r hcap q).mpr
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hst : j.val - N + 2 * N ≤ n - 1 := by have := hv.1; have := hv.2; omega
  intro a ha
  have hab := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
  have htrans := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
    (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc a hab
  have hflip := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
    (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc (a.1, !a.2) hab
  let d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge :=
    (⟨kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, htrans.1⟩, a.2)
  have hd : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) :=
    (hchar d).mpr ⟨a, ha, rfl⟩
  obtain ⟨hs, ht⟩ := (uibotFiniteStage_face_retained_iff_borderEndpoints P U hU hborder
    j.val (by have := j.isLt; omega) r F).mp hF d hd
  constructor
  · apply (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
      P U hU hborder hwindow hcap _).mp
    exact ⟨stageVertex (finiteCodeExtend w) (n - 1) d,
      (stage_vertex_eq_limit _ _ d).trans htrans.2, hs⟩
  · apply (uibotFiniteRootWindow_exteriorVertexInf_mem_iff w j (shiftedStream W N)
      P U hU hborder hwindow hcap _).mp
    exact ⟨stageVertex (finiteCodeExtend w) (n - 1) (edgeFlip _ d),
      (stage_vertex_eq_limit _ _ (edgeFlip _ d)).trans hflip.2, ht⟩

/-- Helper toward Proposition 3.9: retained original finite faces inject
into retained original whole-plane faces. One centered triangle label identifies
the complete bordering-dart relation on both sides. -/
theorem uibotFiniteRootWindow_retainedFaces_wholePlaneEmbedding {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ f : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ↪
      {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ F, ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
        (f F).val = uibotWholePlaneWindowTriangleFace W H G N q ∧
        (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) := by
  let A := {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
    (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r}
  have hex (F : A) := uibotFiniteRootWindow_retainedFace_wholePlaneTriangle
    w j W H G hp P U hU hborder hwindow hcap F.val F.property
  choose q hq hchar hret using hex
  let B := {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
    (uibotWholePlaneGeometricRoot W H G) r}
  let f : A → B := fun F => ⟨uibotWholePlaneWindowTriangleFace W H G N (q F), hret F⟩
  refine ⟨⟨f, ?_⟩, fun F => ⟨q F, hq F, rfl, hchar F⟩⟩
  intro F K he
  have hqeq : q F = q K := uibotWholePlaneWindowTriangleFace_injective W H G N
    (congrArg Subtype.val he)
  obtain ⟨d, hd⟩ := P.face_has_bordering_dart (kmswStageDrawing_vertex_surjective _ _)
    (kmswRootedStage (finiteCodeExtend w) (n - 1)).root (P.toPlaneGraphDrawingFaceEquiv F.val)
  have hdK : P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv K.val) := by
    apply (hchar K d).mpr
    rw [← hqeq]
    exact (hchar F d).mp hd
  apply Subtype.ext
  apply P.toPlaneGraphDrawingFaceEquiv.injective
  exact P.dartBorders_face_unique d _ _ hd hdK

private theorem finite_triangle_face {w : ℕ → Fin 3} {n : ℕ}
    (P : StageDrawing w n) (U : P.Face)
    (hborder : ∀ d, P.dartBorders d U ↔ (kmswStageDirectedMap w n).IsOuter d)
    (q : TriangleCreationTime w) (hq : q.val < n) :
    ∃ F : P.toPlaneGraphDrawing.Face,
      ∀ d : StageDart (kmswStage w n).nextEdge,
        P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
          (d.1.val, d.2) ∈ stageTriangleDartList w q := by
  let d := stageTriangleDart₁ w n q hq
  have hdq : (d.1.val, d.2) ∈ stageTriangleDartList w q := by
    simp only [d, stageTriangleDart₁, stageTriangleDartAt, stageTriangleDartList,
      List.mem_cons, List.not_mem_nil, or_false, true_or]
  let F := kmswStageDrawing_leftFace P d
  have hd : P.dartBorders d F := (kmswStageDrawing_leftFace_eq_iff P d F).mp rfl
  have hFU : F ≠ U := by
    intro he
    have ho := (hborder d).mp (he ▸ hd)
    have hon : d ∈ stageOuterWord w n := by
      rw [kmswStage_isOuter_iff_boundary] at ho
      apply (stageOuterWord_mem_iff w n d).mpr
      simpa only [List.mem_append, or_comm] using ho
    exact stageTriangleDart_not_outer w n q hq d hdq hon
  obtain ⟨k, ⟨hk, hchar⟩, _⟩ :=
    uibotFiniteStage_nonexteriorFace_triangle P U hborder F hFU
  have hkq : k = q := by
    by_contra hne
    exact (List.disjoint_left.mp (stageTriangleDartLists_disjoint w n k q hk hq hne))
      ((hchar d).mp hd) hdq
  exact ⟨P.toPlaneGraphDrawingFaceEquiv.symm F, by
    intro e
    rw [Equiv.apply_symm_apply]
    exact hkq ▸ hchar e⟩

private theorem window_triangle_mem (w u : ℕ → Fin 3) (s m : ℕ)
    (hcode : ∀ i < m, w (s + i) = u i)
    (q : TriangleCreationTime u) (hq : q.val < m)
    (hc : w (s + q.val) = 0 ∨ w (s + q.val) = 1) (d : ℕ × Bool) :
    d ∈ stageTriangleDartList w ⟨s + q.val, hc⟩ ↔
      ∃ a, a ∈ stageTriangleDartList u q ∧
        (kmswWindowEdgeMapInf w s a.1, a.2) = d := by
  have hs : kmswStage (fun i => w (s + i)) q.val = kmswStage u q.val :=
    kmswStage_congr (fun i hi => hcode i (hi.trans hq))
  have hsfull : kmswStage (fun i => w (s + i)) m = kmswStage u m :=
    kmswStage_congr hcode
  have hl : stageTriangleDartList (fun i => w (s + i)) ⟨q.val, hc⟩ =
      stageTriangleDartList u q := by
    simp only [stageTriangleDartList, stageTriangleDartTriple, hs, hcode q.val hq]
  have hr := kmswWindowPatchData_triangle_rotated w s m q.val hq hc
  rw [hl] at hr
  have hm (a : ℕ × Bool) (ha : a ∈ stageTriangleDartList u q) :
      ((kmswWindowPatchData w s m).φ a.1, a.2) =
        (kmswWindowEdgeMapInf w s a.1, a.2) := by
    apply Prod.ext
    · symm
      apply kmswWindowEdgeMapInf_eq_stage
      rw [hsfull]
      exact stageTriangleDartList_lt u m q hq a ha
    · rfl
  constructor
  · intro hd
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (hr.mem_iff.mpr hd)
    exact ⟨a, ha, (hm a ha).symm.trans he⟩
  · rintro ⟨a, ha, he⟩
    exact hr.mem_iff.mp (List.mem_map.mpr ⟨a, ha, (hm a ha).trans he⟩)

/-- Helper toward Proposition 3.9: each centered triangle is realized by
an original face of every exterior-certified finite drawing. Its retention
is equivalent to retention of the original whole-plane face with the same label. -/
theorem uibotFiniteRootWindow_triangleFace_wholePlaneCorrespondence {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r)
    (q : TriangleCreationTime (shiftedStream W N)) (hq : q.val < 2 * N) :
    ∃ F : P.toPlaneGraphDrawing.Face,
      (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2)) ∧
      (F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r ↔
        uibotWholePlaneWindowTriangleFace W H G N q ∈
          d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
            (uibotWholePlaneGeometricRoot W H G) r) := by
  obtain ⟨hv, hc⟩ := uibotFiniteRootWindow_codeAgreement w j (shiftedStream W N) hwindow
  have hst : j.val - N + 2 * N ≤ n - 1 := by have := hv.1; have := hv.2; omega
  have hcode : finiteCodeExtend w (j.val - N + q.val) = 0 ∨
      finiteCodeExtend w (j.val - N + q.val) = 1 := by
    rw [hc q.val hq]
    exact q.property
  obtain ⟨F, hF⟩ := finite_triangle_face P U hborder
    ⟨j.val - N + q.val, hcode⟩ (by dsimp; omega)
  have hchar (d : StageDart (kmswStage (finiteCodeExtend w) (n - 1)).nextEdge) :
      P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F) ↔
        ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
          (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
            (d.1.val, d.2) :=
    (hF d).trans (window_triangle_mem _ _ _ _ hc q hq hcode _)
  refine ⟨F, hchar, ?_⟩
  constructor
  · intro hret
    obtain ⟨p, _, hpchar, hpret⟩ := uibotFiniteRootWindow_retainedFace_wholePlaneTriangle
      w j W H G hp P U hU hborder hwindow hcap F hret
    obtain ⟨p', ⟨hp', hpchar'⟩, huniq⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
      w j (shiftedStream W N) P U hU hborder hwindow hcap F hret
    have hqeq : q = p' := huniq q ⟨hq, hchar⟩
    have hpeq : p = p' := huniq p ⟨by assumption, hpchar⟩
    exact (hpeq.trans hqeq.symm) ▸ hpret
  · intro hret
    have hends := (uibotWholePlaneWindowTriangleFace_retained_iff
      W H G hp N r hcap q).mp hret
    apply (uibotFiniteStage_face_retained_iff_borderEndpoints P U hU hborder
      j.val (by have := j.isLt; omega) r F).mpr
    intro d hd
    obtain ⟨a, ha, he⟩ := (hchar d).mp hd
    have hab := stageTriangleDartList_lt (shiftedStream W N) (2 * N) q hq a ha
    have htrans := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
      (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc a hab
    have hflip := uibotWindowDart_endpoint_transport (finiteCodeExtend w)
      (shiftedStream W N) (j.val - N) (2 * N) (n - 1) hst hc (a.1, !a.2) hab
    have hvd : (stageVertex (finiteCodeExtend w) (n - 1) d).val =
        kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (kmswLimitDartVertex (shiftedStream W N) a) :=
      (stage_vertex_eq_limit _ _ d).trans ((congrArg (kmswLimitDartVertex _) he).symm.trans htrans.2)
    have heflip : (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, !a.2) =
        ((edgeFlip _ d).1.val, (edgeFlip _ d).2) := by
      exact congrArg (fun z : ℕ × Bool => (z.1, !z.2)) he
    have hvt : (stageVertex (finiteCodeExtend w) (n - 1) (edgeFlip _ d)).val =
        kmswWindowVertexMapInf (finiteCodeExtend w) (j.val - N)
          (kmswLimitDartVertex (shiftedStream W N) (a.1, !a.2)) :=
      (stage_vertex_eq_limit _ _ (edgeFlip _ d)).trans
        ((congrArg (kmswLimitDartVertex _) heflip).symm.trans hflip.2)
    constructor
    · obtain ⟨v, hv, hvm⟩ := (uibotFiniteRootWindow_exteriorVertexInf_mem_iff
        w j (shiftedStream W N) P U hU hborder hwindow hcap _).mpr (hends a ha).1
      exact (Fin.ext (hv.trans hvd.symm)) ▸ hvm
    · obtain ⟨v, hv, hvm⟩ := (uibotFiniteRootWindow_exteriorVertexInf_mem_iff
        w j (shiftedStream W N) P U hU hborder hwindow hcap _).mpr (hends a ha).2
      exact (Fin.ext (hv.trans hvt.symm)) ▸ hvm

/-- Helper toward Proposition 3.9: retained original finite faces and
retained original whole-plane whole-plane faces are in bijection. The same
centered triangle label gives both complete bordering-dart relations. -/
theorem uibotFiniteRootWindow_retainedFaces_wholePlaneEquiv {n N r : ℕ}
    (w : Fin (n - 1) → Fin 3) (j : Fin n)
    (W : ℤ → Fin 3) (H : WholePlaneRotationHypothesis W)
    (G : WholePlaneDrawing W H)
    (hp : ∀ e : WholePlaneEdge W, wholePlaneEdgePresent W e)
    (P : StageDrawing (finiteCodeExtend w) (n - 1))
    (U : P.Face) (hU : P.IsUnbounded U)
    (hborder : ∀ d, P.dartBorders d U ↔
      (kmswStageDirectedMap (finiteCodeExtend w) (n - 1)).IsOuter d)
    (hwindow : uibotFiniteRootWindow N w j =
      some (fun i => shiftedStream W N i.val))
    (hcap : UIBOTRootWindowCapture (shiftedStream W N) N r) :
    ∃ E : {F // F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r} ≃
      {F // F ∈ d39GeomRetainedFaces (uibotWholePlaneGeometricMap W H G hp)
        (uibotWholePlaneGeometricRoot W H G) r},
      ∀ F, ∃ q : TriangleCreationTime (shiftedStream W N), q.val < 2 * N ∧
        (E F).val = uibotWholePlaneWindowTriangleFace W H G N q ∧
        (∀ d, P.dartBorders d (P.toPlaneGraphDrawingFaceEquiv F.val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            (kmswWindowEdgeMapInf (finiteCodeExtend w) (j.val - N) a.1, a.2) =
              (d.1.val, d.2)) ∧
        (∀ d, G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv (E F).val) ↔
          ∃ a, a ∈ stageTriangleDartList (shiftedStream W N) q ∧
            wholePlaneDartι W N a = d) := by
  obtain ⟨f, hf⟩ := uibotFiniteRootWindow_retainedFaces_wholePlaneEmbedding
    w j W H G hp P U hU hborder hwindow hcap
  have hsurj : Function.Surjective f := by
    intro K
    obtain ⟨q, ⟨hq, hK⟩, _⟩ := uibotWholePlane_retainedFace_windowTriangle
      W H G hp N r hcap K.val K.property
    obtain ⟨F, hchar, hret⟩ := uibotFiniteRootWindow_triangleFace_wholePlaneCorrespondence
      w j W H G hp P U hU hborder hwindow hcap q hq
    have hF : F ∈ d39GeomRetainedFaces (uibotFiniteStageExteriorMap P U hU hborder)
        (uibotFiniteStageExteriorRoot P j.val (by have := j.isLt; omega)) r :=
      hret.mpr (hK ▸ K.property)
    obtain ⟨p, hp', hfp, hpchar⟩ := hf ⟨F, hF⟩
    obtain ⟨q', _, huniq⟩ := uibotFiniteRootWindow_retainedFace_windowTriangle
      w j (shiftedStream W N) P U hU hborder hwindow hcap F hF
    have hpq : p = q := (huniq p ⟨hp', hpchar⟩).trans (huniq q ⟨hq, hchar⟩).symm
    exact ⟨⟨F, hF⟩, Subtype.ext (hfp.trans
      ((congrArg (uibotWholePlaneWindowTriangleFace W H G N) hpq).trans hK.symm))⟩
  let E := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  refine ⟨E, ?_⟩
  intro F
  obtain ⟨q, hq, he, hchar⟩ := hf F
  refine ⟨q, hq, he, hchar, ?_⟩
  intro d
  change G.dartBorders d (G.toPlaneGraphDrawingFaceEquiv (f F).val) ↔ _
  rw [he]
  exact uibotWholePlaneWindowTriangleFace_border W H G N q d


























end DirectedDistances.PaperProofs.Section3
end
