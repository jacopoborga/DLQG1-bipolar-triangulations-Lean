module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableCloseSdp

/-! Finite-ball SDP comparison and shell stabilization at every integer index.
Observable reflection and symmetry are conditional only on the explicitly named -/

public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW DirectedMapWithMissing
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite directed dart walks used only for the finite-distance comparison. -/
private def closeSdp2Walk {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) : List D → MapVertex M → MapVertex M → Prop
  | [], s, t => s = t
  | d :: ds, s, t => ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      closeSdp2Walk M ds (dartHeadVertex M d) t

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Prepending outside the existing vertex list preserves simplicity. -/
private def closeSdp2Prepend
    (M : DirectedMapWithMissing D) {s y t : MapVertex M} {n : ℕ}
    (d : D) (hmiss : ¬ M.missing d) (htail : M.tail d)
    (hty : dartTailVertex M d = s) (hhy : dartHeadVertex M d = y)
    (P : SimpleDirectedDartPath M y t n) (hs : s ∉ P.vertices) :
    SimpleDirectedDartPath M s t (n + 1) := by
  refine {
    darts := d :: P.darts
    vertices := s :: P.vertices
    darts_length := by simp [P.darts_length]
    vertices_length := by simp [P.vertices_length]
    vertices_nodup := by simp [List.nodup_cons, hs, P.vertices_nodup]
    start_vertex := by simp
    end_vertex := by simpa [List.get_eq_getElem] using P.end_vertex
    edge_step := by
      intro i
      have hi : i.val ≤ n := by
        have h := i.isLt
        simp only [List.length_cons, P.darts_length] at h
        omega
      by_cases hi0 : i.val = 0
      · have hifin : i = ⟨0, by simp [List.length_cons, P.darts_length]⟩ := Fin.ext hi0
        subst i
        have hstart : P.vertices.get ⟨0, by simp [P.vertices_length]⟩ = y := P.start_vertex
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [List.get_eq_getElem] using hmiss
        · simpa [List.get_eq_getElem] using htail
        · simpa [List.get_eq_getElem] using hty.symm
        · simpa [List.get_eq_getElem] using hstart.trans hhy.symm
      · have hpos : 0 < i.val := by omega
        have hdlen := P.darts_length
        have hvlen := P.vertices_length
        let j : Fin P.darts.length := ⟨i.val - 1, by omega⟩
        let jv : Fin P.vertices.length := ⟨i.val - 1, by omega⟩
        let jv' : Fin P.vertices.length := ⟨i.val, by omega⟩
        have hidx : i.val = j.val + 1 := by dsimp [j]; omega
        have hsP := P.edge_step j
        have hgetD : (d :: P.darts).get i = P.darts.get j := by
          simp only [List.get_eq_getElem]
          simp [hidx]
        have hgetV : (s :: P.vertices).get ⟨i.val, by
            simp [List.length_cons, P.vertices_length]; omega⟩ =
            P.vertices.get jv := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv]
        have hgetV' : (s :: P.vertices).get ⟨i.val + 1, by
            simp [List.length_cons, P.vertices_length]; omega⟩ =
            P.vertices.get jv' := by
          simp only [List.get_eq_getElem]
          simp [hidx, jv']
        rw [hgetD, hgetV, hgetV']
        simpa [jv, jv', hidx] using hsP
  }


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite walk contains a simple directed path of no greater length. -/
private theorem closeSdp2Walk_simple (M : DirectedMapWithMissing D)
    (ds : List D) (s t : MapVertex M) (hw : closeSdp2Walk M ds s t) :
    ∃ n : ℕ, n ≤ ds.length ∧ Nonempty (SimpleDirectedDartPath M s t n) := by
  classical
  induction ds generalizing s with
  | nil =>
    have he : s = t := hw
    subst t
    exact ⟨0, le_rfl, ⟨{
      darts := []
      vertices := [s]
      darts_length := rfl
      vertices_length := rfl
      vertices_nodup := List.nodup_singleton s
      start_vertex := rfl
      end_vertex := rfl
      edge_step := fun i => Fin.elim0 i }⟩⟩
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := hw
    obtain ⟨n, hn, ⟨P⟩⟩ := ih _ hw
    by_cases hmem : s ∈ P.vertices
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
      let j : Fin (n + 1) := ⟨i.val, by
        have h := i.isLt
        have hl := P.vertices_length
        omega⟩
      have he : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = s := hi
      have Q := P.suffix j
      rw [he] at Q
      exact ⟨n - j.val, by simp only [List.length_cons]; omega, ⟨Q⟩⟩
    · exact ⟨n + 1, by simp only [List.length_cons]; omega,
        ⟨closeSdp2Prepend M d hm ht hs rfl P hmem⟩⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A simple directed path gives the corresponding finite directed walk. -/
private theorem closeSdp2Simple_walk (M : DirectedMapWithMissing D)
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    ∃ ds : List D, closeSdp2Walk M ds s t ∧ ds.length = n := by
  induction n generalizing s t with
  | zero => exact ⟨[], P.start_vertex.symm.trans P.end_vertex, rfl⟩
  | succ n ih =>
    let i : Fin P.darts.length := ⟨0, by rw [P.darts_length]; omega⟩
    let j : Fin (n + 1 + 1) := ⟨1, by omega⟩
    have hs := P.edge_step i
    obtain ⟨ds, hw, hl⟩ := ih (P.suffix j)
    refine ⟨P.darts.get i :: ds, ⟨hs.1, hs.2.1, ?_, ?_⟩, by simp [hl]⟩
    · exact hs.2.2.1.symm.trans P.start_vertex
    · rw [← hs.2.2.2]
      exact hw

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite simple SDP is the infimum over all finite directed walks. -/
private theorem closeSdp2Finite_inf (M : DirectedMapWithMissing D)
    (s t : MapVertex M) :
    (show ℕ∞ from simpleDirectedPathSDPLength M s t) =
      ⨅ ds : List D, ⨅ (_ : closeSdp2Walk M ds s t), (ds.length : ℕ∞) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro ds
    apply le_iInf
    intro hw
    obtain ⟨n, hn, ⟨P⟩⟩ := closeSdp2Walk_simple M ds s t hw
    exact (Finset.min_le ((mem_simpleDirectedPathLengthSet M s t n).2
      ⟨P, trivial⟩)).trans (ENat.natCast_le_natCast.mpr hn)
  · unfold simpleDirectedPathSDPLength
    apply Finset.le_min
    intro n hn
    obtain ⟨P, _⟩ := (mem_simpleDirectedPathLengthSet M s t n).1 hn
    obtain ⟨ds, hw, hl⟩ := closeSdp2Simple_walk M P
    exact iInf_le_of_le ds (iInf_le_of_le hw (by rw [hl]; exact le_rfl))


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite rotation quotient embeds in the ambient vertex quotient. -/
private noncomputable def closeSdp2Vertex (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) :
    MapVertex (rootedLocallyFiniteFramedBall M r hr).map →
      RootedLocallyFiniteVertex M.D M.rot := by
  classical
  exact Quotient.map Subtype.val (fun x y h =>
    (rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap r x y).1 h)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite-to-ambient quotient map preserves and reflects vertex identity. -/
private theorem closeSdp2Vertex_injective (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) : Function.Injective (closeSdp2Vertex M r hr) := by
  classical
  intro a b
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      intro he
      exact Quotient.sound
        ((rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap r a b).2
          (Quotient.exact he))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Directed walks in the finite ball are exactly retained ambient dart walks. -/
private theorem closeSdp2Walk_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (ds : List (rootedLocallyFiniteFramedBall M r hr).D)
    (s t : MapVertex (rootedLocallyFiniteFramedBall M r hr).map) :
    closeSdp2Walk (rootedLocallyFiniteFramedBall M r hr).map ds s t ↔
      incrementSdpDartWalk M.toRootedLocallyFiniteMap (ds.map Subtype.val)
        (closeSdp2Vertex M r hr s) (closeSdp2Vertex M r hr t) := by
  classical
  induction ds generalizing s with
  | nil => exact (closeSdp2Vertex_injective M r hr).eq_iff.symm
  | cons d ds ih =>
    change (_ ∧ _ ∧ _ ∧ closeSdp2Walk _ _ _ _) ↔
      (_ ∧ _ ∧ _ ∧ incrementSdpDartWalk _ _ _ _)
    rw [ih]
    have he : dartTailVertex (rootedLocallyFiniteFramedBall M r hr).map d = s ↔
        rootedLocallyFiniteVertexClass M.rot d.1 = closeSdp2Vertex M r hr s :=
      (closeSdp2Vertex_injective M r hr).eq_iff.symm
    rw [he]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A retained ambient list lifts to a finite-ball list with identical darts. -/
private theorem closeSdp2List_lift (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (ds : List M.D)
    (hd : ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r) :
    ∃ es : List (rootedLocallyFiniteFramedBall M r hr).D, es.map Subtype.val = ds := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons d ds ih =>
    obtain ⟨es, he⟩ := ih (fun x hx => hd x (List.mem_cons_of_mem d hx))
    refine ⟨⟨d, hd d (List.mem_cons_self)⟩ :: es, ?_⟩
    change (d :: es.map Subtype.val) = d :: ds
    rw [he]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite simple shortest distance equals restricted ambient SDP, including infinity. -/
theorem FiniteBallSdpDistanceIdentification_proved
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r) :
    FiniteBallSdpDistanceIdentification M r hr := by
  classical
  intro d e
  rw [closeSdp2Finite_inf]
  apply le_antisymm
  · apply le_iInf
    intro ds
    apply le_iInf
    intro hw
    apply le_iInf
    intro hd
    obtain ⟨es, he⟩ := closeSdp2List_lift M r hr ds hd
    have hw' : closeSdp2Walk (rootedLocallyFiniteFramedBall M r hr).map es
        (vertexClass _ d) (vertexClass _ e) := by
      apply (closeSdp2Walk_transport M r hr es (vertexClass _ d) (vertexClass _ e)).2
      change incrementSdpDartWalk M.toRootedLocallyFiniteMap (es.map Subtype.val)
        (rootedLocallyFiniteVertexClass M.rot d.1)
        (rootedLocallyFiniteVertexClass M.rot e.1)
      rw [he]
      exact hw
    have hl : es.length = ds.length := by
      have h := congrArg List.length he
      exact (List.length_map Subtype.val).symm.trans h
    exact iInf_le_of_le es (iInf_le_of_le hw' (by rw [hl]))
  · apply le_iInf
    intro es
    apply le_iInf
    intro hw
    have hw' := (closeSdp2Walk_transport M r hr es
      (vertexClass _ d) (vertexClass _ e)).1 hw
    have hd : ∀ x ∈ es.map Subtype.val,
        x ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact y.2
    apply iInf_le_of_le (es.map Subtype.val)
    apply iInf_le_of_le hw'
    apply iInf_le_of_le hd
    exact le_of_eq (congrArg (fun n : ℕ => (n : ℕ∞)) (List.length_map Subtype.val))


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
All future copies satisfy the full shortest-distance characterization. -/
private theorem closeSdp2_ae_future_data :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∃ h : BoundaryHitWitnesses (fun i => uibhbotFutureCode k W (i + 1)),
        IsBoundaryBusemannSDP (boundaryPresentVertex _ h)
          (busemannSDPMeasurableVersion (uibhbotFutureCode k W)) := by
  apply ae_all_iff.mpr
  intro k
  have h := iidCodes_ae_busemannSDPMeasurableVersion
  rw [← uibhbotFutureCode_law k] at h
  exact ae_of_ae_map (measurable_uibhbotFutureCode k).aemeasurable h

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Equal path-length sets have equal shortest distances. -/
private theorem closeSdp2_eq_of_pathLengths
    {α β : Type*} [Quiver α] [Quiver β] {a b : α}
    (F : Prefunctor α β)
    (h : pathLengths (F.obj a) (F.obj b) = pathLengths a b) :
    DirectedDistances.sdp (F.obj a) (F.obj b) = DirectedDistances.sdp a b := by
  change (⨅ p : Quiver.Path (F.obj a) (F.obj b), (p.length : ℕ∞)) = _
  apply le_antisymm
  · apply le_iInf
    intro p
    have hp : p.length ∈ pathLengths a b := ⟨p, rfl⟩
    rw [← h] at hp
    obtain ⟨q, hq⟩ := hp
    have hq' : q.length = p.length := hq
    exact (iInf_le _ q).trans (by exact_mod_cast hq'.le)
  · apply le_iInf
    intro q
    have hq : q.length ∈ pathLengths (F.obj a) (F.obj b) := ⟨q, rfl⟩
    rw [h] at hq
    obtain ⟨p, hp⟩ := hq
    have hp' : p.length = q.length := hp
    exact (iInf_le _ p).trans (by exact_mod_cast hp'.le)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every distinct common reachable sequence characterizes a future increment. -/
private theorem closeSdp2_ae_future_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ K k : ℤ, k ≤ K →
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSourceSdp k W) (z m) ∧
        Reachable (uibhbotBusemannSourceSdp (k - 1) W) (z m)) →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
        DirectedDistances.sdp (uibhbotBusemannSourceSdp k W) (z m) = (a : ℕ∞) ∧
        DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W) (z m) =
          (b : ℕ∞) ∧
        SDPMasterFromLaw.increment busemannSDPMeasurableVersion (k - K)
          (uibhbotFutureCode K W) = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [closeSdp2_ae_future_data,
    ae_uibhbotFutureBoundary_index, ae_uibhbotFuture_boundary_pathLengths,
    ae_uibhbotFuture_boundary_path_lift]
      with W hdata hi hpaths hl K k hk z hz hr
  obtain ⟨h, hX⟩ := hdata K
  let w := fun i => uibhbotFutureCode K W (i + 1)
  let x := boundaryPresentVertex w h
  let F := uibhbotFutureToGlobal K W
  let j := k - K
  have hj : j ≤ 0 := by dsimp [j]; omega
  have hj1 : j - 1 ≤ 0 := by omega
  have hs (i : ℤ) (hi' : i ≤ 0) : F.obj (x i) =
      uibhbotBusemannSourceSdp (K + i) W := by
    apply congrArg UIBHBOTPresentVertex.mk
    exact hi K h i hi'
  have hs0 : F.obj (x j) = uibhbotBusemannSourceSdp k W := by
    simpa only [j, add_sub_cancel] using hs j hj
  have hs1 : F.obj (x (j - 1)) = uibhbotBusemannSourceSdp (k - 1) W := by
    have he : K + (j - 1) = k - 1 := by dsimp [j]; omega
    simpa only [he] using hs (j - 1) hj1
  have hp : ∀ m, ∃ c : PresentVertex w, F.obj c = z m ∧ Reachable (x j) c := by
    intro m
    have hrm := (hr m).1
    rw [← hs0] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h j hj (z m) p
    exact ⟨c, hc, ⟨q⟩⟩
  choose y hy hy0 using hp
  have hy1 : ∀ m, Reachable (x (j - 1)) (y m) := by
    intro m
    have hrm := (hr m).2
    rw [← hs1] at hrm
    obtain ⟨p⟩ := hrm
    obtain ⟨c, q, hc, _, _⟩ := hl K h (j - 1) hj1 (z m) p
    have he : c = y m := uibhbotFutureToGlobal_obj_injective K W (hc.trans (hy m).symm)
    subst c
    exact ⟨q⟩
  have hiy : Function.Injective y := by
    intro a b hab
    apply hz
    rw [← hy a, ← hy b, hab]
  obtain ⟨N, hN⟩ := hX.2 (j - 1) j y hiy (fun m => ⟨hy1 m, hy0 m⟩)
  refine ⟨N, fun m hm => ?_⟩
  let a := (DirectedDistances.sdp (x j) (y m)).toNat
  let b := (DirectedDistances.sdp (x (j - 1)) (y m)).toNat
  have hp0 := hpaths K h j hj (y m)
  have hp1 := hpaths K h (j - 1) hj1 (y m)
  have hd0 : DirectedDistances.sdp (uibhbotBusemannSourceSdp k W) (z m) =
      (a : ℕ∞) := by
    have he := closeSdp2_eq_of_pathLengths F hp0
    change DirectedDistances.sdp (F.obj (x j)) (F.obj (y m)) =
      DirectedDistances.sdp (x j) (y m) at he
    rw [hs0, hy m] at he
    have hne : DirectedDistances.sdp (x j) (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy0 m)
    simpa [a] using he.trans (ENat.natCast_toNat hne).symm
  have hd1 : DirectedDistances.sdp (uibhbotBusemannSourceSdp (k - 1) W) (z m) =
      (b : ℕ∞) := by
    have he := closeSdp2_eq_of_pathLengths F hp1
    change DirectedDistances.sdp (F.obj (x (j - 1))) (F.obj (y m)) =
      DirectedDistances.sdp (x (j - 1)) (y m) at he
    rw [hs1, hy m] at he
    have hne : DirectedDistances.sdp (x (j - 1)) (y m) ≠ ⊤ :=
      fun hh => (DirectedDistances.sdp_eq_top_iff_not_reachable.mp hh) (hy1 m)
    simpa [b] using he.trans (ENat.natCast_toNat hne).symm
  exact ⟨a, b, hd0, hd1, hN m hm⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every distinct common reachable sequence characterizes the intrinsic code increment. -/
private theorem ae_closeSdp2_sequence_characterization :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ z : ℕ → UIBHBOTPresentVertex W, Function.Injective z →
      (∀ m, Reachable (uibhbotBusemannSourceSdp k W) (z m) ∧
        Reachable (uibhbotBusemannSourceSdp (k - 1) W) (z m)) →
      ∃ N : ℕ, ∀ m ≥ N, ∃ a b : ℕ,
        sdp (uibhbotBusemannSourceSdp k W) (z m) = (a : ℕ∞) ∧
        sdp (uibhbotBusemannSourceSdp (k - 1) W) (z m) = (b : ℕ∞) ∧
        uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ) := by
  filter_upwards [closeSdp2_ae_future_characterization] with W hW k z hz hr
  simpa only [sub_self, uibhbotMirrorSdpCodeIncrement] using hW k k le_rfl z hz hr

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
This upgrades sequential convergence to simultaneous consensus outside a finite set. -/
private theorem ae_closeSdp2_finite_exceptions :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      {t : UIBHBOTPresentVertex W |
        Reachable (uibhbotBusemannSourceSdp k W) t ∧
        Reachable (uibhbotBusemannSourceSdp (k - 1) W) t ∧
        ¬ ∃ a b : ℕ,
          sdp (uibhbotBusemannSourceSdp k W) t = (a : ℕ∞) ∧
          sdp (uibhbotBusemannSourceSdp (k - 1) W) t =
            (b : ℕ∞) ∧
          uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ)}.Finite := by
  classical
  filter_upwards [ae_closeSdp2_sequence_characterization] with W hW k
  by_contra hinf
  let S := {t : UIBHBOTPresentVertex W |
    Reachable (uibhbotBusemannSourceSdp k W) t ∧
    Reachable (uibhbotBusemannSourceSdp (k - 1) W) t ∧
    ¬ ∃ a b : ℕ,
      sdp (uibhbotBusemannSourceSdp k W) t = (a : ℕ∞) ∧
      sdp (uibhbotBusemannSourceSdp (k - 1) W) t =
        (b : ℕ∞) ∧
      uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ)}
  let e : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  let z : ℕ → UIBHBOTPresentVertex W := fun m => (e m).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.injective
  obtain ⟨N, hN⟩ := hW k z hz (fun m => ⟨(e m).property.1, (e m).property.2.1⟩)
  exact (e N).property.2.2 (hN N le_rfl)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every finite set of intrinsic vertices is captured by one geometric radius. -/
private theorem closeSdp2_vertexFinset_captured (M : RootedLocallyFiniteMap)
    (T : Finset (RootedLocallyFiniteVertex M.D M.rot)) (r₀ : ℕ) :
    ∃ R : ℕ, r₀ ≤ R ∧ ∀ t ∈ T, rootedLocallyFiniteWithinRadius M R t := by
  classical
  obtain ⟨R, hR, hd⟩ := incrementDartList_captured M r₀ (T.toList.map Quotient.out)
  refine ⟨R, hR, fun t ht => ?_⟩
  have hmem : Quotient.out t ∈ T.toList.map Quotient.out :=
    List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩
  have hr := ((mem_rootedLocallyFiniteBallDarts M R _).mp (hd _ hmem)).1
  have he : rootedLocallyFiniteVertexClassOf M (Quotient.out t) = t :=
    Quotient.out_eq' t
  rw [he] at hr
  exact (mem_rootedLocallyFiniteRadiusVertices M R t).mp hr

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
All common reachable intrinsic targets outside one radius have the same finite
distance difference. The radius is fixed before quantifying over targets. -/
private theorem ae_closeSdp2_intrinsic_uniform_consensus :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        ∃ N : ℕ,
          ∀ t : RootedLocallyFiniteVertex (WholePlaneDart W) (wholePlaneRotation W H),
            ¬ rootedLocallyFiniteWithinRadius
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) N t →
            (∃ ds, incrementSdpDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              ds (intrinsicSdpIncrementSource
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t) →
            (∃ ds, incrementSdpDartWalk (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
              ds (intrinsicSdpIncrementSource
                (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t) →
            ∃ a b : ℕ,
              intrinsicIncrementSdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
                  (intrinsicSdpIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) k) t =
                (a : ℕ∞) ∧
              intrinsicIncrementSdp (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C)
                  (intrinsicSdpIncrementSource
                    (uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C) (k - 1)) t =
                (b : ℕ∞) ∧
              uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ) := by
  classical
  filter_upwards [ae_closeSdp2_finite_exceptions,
    ae_intrinsicSdpIncrementSource_identification] with W hfinite hs H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  let S := {t : UIBHBOTPresentVertex W |
    Reachable (uibhbotBusemannSourceSdp k W) t ∧
    Reachable (uibhbotBusemannSourceSdp (k - 1) W) t ∧
    ¬ ∃ a b : ℕ,
      sdp (uibhbotBusemannSourceSdp k W) t = (a : ℕ∞) ∧
      sdp (uibhbotBusemannSourceSdp (k - 1) W) t =
        (b : ℕ∞) ∧
      uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ)}
  have hpre : ((incrementOrbitVertex W H) ⁻¹' S).Finite :=
    Set.Finite.preimage (incrementOrbitVertex_injective W H).injOn (hfinite k)
  obtain ⟨N, _, hN⟩ := closeSdp2_vertexFinset_captured M hpre.toFinset 0
  refine ⟨N, fun t ht h0 h1 => ?_⟩
  have hr0 : Reachable (uibhbotBusemannSourceSdp k W) (incrementOrbitVertex W H t) := by
    obtain ⟨ds, hd⟩ := h0
    obtain ⟨p, _⟩ := incrementSdpDartWalk_to_codePath W H hhit C ds _ t hd
    rw [hs H hhit C k] at p
    exact ⟨p⟩
  have hr1 : Reachable (uibhbotBusemannSourceSdp (k - 1) W)
      (incrementOrbitVertex W H t) := by
    obtain ⟨ds, hd⟩ := h1
    obtain ⟨p, _⟩ := incrementSdpDartWalk_to_codePath W H hhit C ds _ t hd
    rw [hs H hhit C (k - 1)] at p
    exact ⟨p⟩
  have hg : ∃ a b : ℕ,
      sdp (uibhbotBusemannSourceSdp k W) (incrementOrbitVertex W H t) =
          (a : ℕ∞) ∧
      sdp (uibhbotBusemannSourceSdp (k - 1) W) (incrementOrbitVertex W H t) =
          (b : ℕ∞) ∧
      uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ) := by
    by_contra hn
    exact ht (hN t (hpre.mem_toFinset.mpr ⟨hr0, hr1, hn⟩))
  obtain ⟨a, b, ha, hb, hi⟩ := hg
  refine ⟨a, b, ?_, ?_, hi⟩
  · have he := intrinsicIncrementSdp_eq_codeSdp W H hhit C
      (intrinsicSdpIncrementSource M k) t
    apply he.trans
    rw [hs H hhit C k]
    exact ha
  · have he := intrinsicIncrementSdp_eq_codeSdp W H hhit C
      (intrinsicSdpIncrementSource M (k - 1)) t
    apply he.trans
    rw [hs H hhit C (k - 1)]
    exact hb

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Each sufficiently distant intrinsic shell has uniform eventual restricted-SDP consensus.
The enclosing radius is chosen after the shell and before all targets in that shell. -/
private theorem ae_closeSdp2_intrinsic_shell_radius_consensus :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
        ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R,
          ∀ t : RootedLocallyFiniteVertex M.D M.rot,
            rootedLocallyFiniteWithinRadius M (m + 1) t →
            ¬ rootedLocallyFiniteWithinRadius M m t →
            (∃ ds, incrementSdpDartWalk M ds (intrinsicSdpIncrementSource M k) t) →
            (∃ ds, incrementSdpDartWalk M ds (intrinsicSdpIncrementSource M (k - 1)) t) →
            ∃ a b : ℕ,
              incrementCloseSdp_ballDistance M r (intrinsicSdpIncrementSource M k) t =
                  (a : ℕ∞) ∧
              incrementCloseSdp_ballDistance M r (intrinsicSdpIncrementSource M (k - 1)) t =
                  (b : ℕ∞) ∧
              uibhbotMirrorSdpCodeIncrement k W = (a : ℤ) - (b : ℤ) := by
  filter_upwards [ae_closeSdp2_intrinsic_uniform_consensus] with W hW H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  obtain ⟨N, hN⟩ := hW H hhit C k
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨R, _, hR⟩ := incrementCloseSdp_ballDistance_stabilizes_on_radius M
    (intrinsicSdpIncrementSource M k) (intrinsicSdpIncrementSource M (k - 1)) (m + 1) 0
  refine ⟨R, fun r hr t hnear hfar h0 h1 => ?_⟩
  have hfarN : ¬ rootedLocallyFiniteWithinRadius M N t := by
    intro hn
    apply hfar
    exact (mem_rootedLocallyFiniteRadiusVertices M m t).mp
      (rootedLocallyFiniteRadiusVertices_mono M hm
        ((mem_rootedLocallyFiniteRadiusVertices M N t).mpr hn))
  obtain ⟨a, b, ha, hb, hi⟩ := hN t hfarN h0 h1
  obtain ⟨he0, he1⟩ := hR r hr t
    ((mem_rootedLocallyFiniteRadiusVertices M (m + 1) t).mpr hnear)
  exact ⟨a, b, he0.trans ha, he1.trans hb, hi⟩


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The actual future boundary ID agrees with its witnessed boundary vertex. -/
private theorem closeSdp2_boundaryId_eq (ω : ℕ → Fin 3)
    (h : BoundaryHitWitnesses (fun i => ω (i + 1))) (j : ℤ) :
    busemannBoundaryIdTotal ω j = boundaryVertex (fun i => ω (i + 1)) h j := by
  unfold busemannBoundaryIdTotal
  rw [boundaryHitTimeTotal_eq_boundaryHitTime ω h j, ENat.toNat_natCast]
  rw [boundaryVertex_eq_edgeWest_hit]
  exact (edge_endpoints_eq _ (act_lt_nextEdge _ le_rfl)).1

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every explicit target reaches every later target in its future boundary sequence. -/
private theorem ae_closeSdp2_target_tail_reachable :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      ∀ a b : ℕ, a ≤ b →
        Reachable (uibhbotBusemannTargetSdp k W a) (uibhbotBusemannTargetSdp k W b) := by
  filter_upwards [ae_uibhbotFuture_boundaryHitWitnesses] with W hW k a b hab
  let w := fun i => uibhbotFutureCode k W (i + 1)
  let h := hW k
  let F := uibhbotFutureToGlobal k W
  have ht (m : ℕ) : uibhbotBusemannTargetSdp k W m =
      F.obj (boundaryPresentVertex w h (m : ℤ)) := by
    unfold uibhbotBusemannTargetSdp
    rw [closeSdp2_boundaryId_eq _ h]
    rfl
  rw [ht a, ht b]
  obtain ⟨p⟩ := boundaryVertex_nonneg_reachable w h
    (show (0 : ℤ) ≤ (a : ℤ) by omega) (show (a : ℤ) ≤ (b : ℤ) by omega)
  exact ⟨F.mapPath p⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite directed walk leaving a ball crosses its next geometric shell, with
common reachability from both sources preserved along its initial segment. -/
private theorem closeSdp2_walk_crosses_shell (M : RootedLocallyFiniteMap) (m : ℕ)
    (s0 s1 : RootedLocallyFiniteVertex M.D M.rot)
    (ds : List M.D) (v t : RootedLocallyFiniteVertex M.D M.rot)
    (hv : rootedLocallyFiniteWithinRadius M m v)
    (ht : ¬ rootedLocallyFiniteWithinRadius M m t)
    (h0 : ∃ es, incrementDartWalk M es s0 v)
    (h1 : ∃ es, incrementDartWalk M es s1 v)
    (hw : incrementDartWalk M ds v t) :
    ∃ u : RootedLocallyFiniteVertex M.D M.rot,
      rootedLocallyFiniteWithinRadius M (m + 1) u ∧
      ¬ rootedLocallyFiniteWithinRadius M m u ∧
      (∃ es, incrementDartWalk M es s0 u) ∧
      (∃ es, incrementDartWalk M es s1 u) := by
  induction ds generalizing v with
  | nil =>
    change v = t at hw
    exact (ht (hw ▸ hv)).elim
  | cons d ds ih =>
    obtain ⟨hd, htail, hs, hw⟩ := hw
    let u := rootedLocallyFiniteVertexClass M.rot (M.edgeInv d)
    have hedge : incrementDartWalk M [d] v u := ⟨hd, htail, hs, rfl⟩
    have hu0 : ∃ es, incrementDartWalk M es s0 u := by
      obtain ⟨es, he⟩ := h0
      exact ⟨es ++ [d], incrementDartWalk_append M es [d] s0 v u he hedge⟩
    have hu1 : ∃ es, incrementDartWalk M es s1 u := by
      obtain ⟨es, he⟩ := h1
      exact ⟨es ++ [d], incrementDartWalk_append M es [d] s1 v u he hedge⟩
    by_cases hu : rootedLocallyFiniteWithinRadius M m u
    · exact ih u hu hu0 hu1 hw
    · exact ⟨u, .edge hv ⟨d, hs, rfl⟩, hu, hu0, hu1⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Every sufficiently distant intrinsic geometric shell has a target reachable
from both boundary sources. No radius is allowed to depend on the shell target. -/
private theorem ae_closeSdp2_intrinsic_shell_nonempty :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0) (k : ℤ),
        let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
        ∃ N : ℕ, ∀ m ≥ N,
          ∃ t : RootedLocallyFiniteVertex M.D M.rot,
            rootedLocallyFiniteWithinRadius M (m + 1) t ∧
            ¬ rootedLocallyFiniteWithinRadius M m t ∧
            (∃ ds, incrementDartWalk M ds (intrinsicSdpIncrementSource M k) t) ∧
            (∃ ds, incrementDartWalk M ds (intrinsicSdpIncrementSource M (k - 1)) t) := by
  classical
  filter_upwards [ae_uibhbotBusemannIncrementSdp_distance_realization,
    ae_intrinsicSdpIncrementSource_identification,
    ae_closeSdp2_target_tail_reachable] with W hreal hs htail H hhit C k
  let M := uibhbotWholePlaneRootedLocallyFiniteMap W H hhit C
  obtain ⟨hinj, B, hB⟩ := hreal k
  let v := incrementCloseSdp_intrinsicTarget W H k B
  have hv : incrementOrbitVertex W H v = uibhbotBusemannTargetSdp k W B :=
    incrementCloseSdp_intrinsicTarget_image W H k B
  obtain ⟨p0⟩ := (hB B le_rfl).1
  obtain ⟨p1⟩ := (hB B le_rfl).2.1
  obtain ⟨ds0, hd0, _⟩ := codePath_to_incrementSdpDartWalk W H hhit C p0
    (intrinsicSdpIncrementSource M k) v (hs H hhit C k) hv
  obtain ⟨ds1, hd1, _⟩ := codePath_to_incrementSdpDartWalk W H hhit C p1
    (intrinsicSdpIncrementSource M (k - 1)) v (hs H hhit C (k - 1)) hv
  obtain ⟨N, _, hN⟩ := closeSdp2_vertexFinset_captured M {v} 0
  refine ⟨N, fun m hm => ?_⟩
  have hvm : rootedLocallyFiniteWithinRadius M m v :=
    (mem_rootedLocallyFiniteRadiusVertices M m v).mp
      (rootedLocallyFiniteRadiusVertices_mono M hm
        ((mem_rootedLocallyFiniteRadiusVertices M N v).mpr
          (hN v (Finset.mem_singleton_self _))))
  let f := fun j : ℕ => incrementCloseSdp_intrinsicTarget W H k (B + j)
  have hf : Function.Injective f := by
    intro a b hab
    have he := congrArg (incrementOrbitVertex W H) hab
    change incrementOrbitVertex W H (incrementCloseSdp_intrinsicTarget W H k (B + a)) =
      incrementOrbitVertex W H (incrementCloseSdp_intrinsicTarget W H k (B + b)) at he
    rw [incrementCloseSdp_intrinsicTarget_image, incrementCloseSdp_intrinsicTarget_image] at he
    have he' := hinj he
    omega
  have hout : ∃ j, ¬ rootedLocallyFiniteWithinRadius M m (f j) := by
    by_contra! hn
    have hfin := Set.Finite.preimage hf.injOn
      (rootedLocallyFiniteRadiusVertices M m).finite_toSet
    apply Set.infinite_univ (α := ℕ)
    exact hfin.subset (fun j _ =>
      (mem_rootedLocallyFiniteRadiusVertices M m (f j)).mpr (hn j))
  obtain ⟨j, hj⟩ := hout
  obtain ⟨p⟩ := htail k B (B + j) (by omega)
  obtain ⟨ds, hd, _⟩ := codePath_to_incrementSdpDartWalk W H hhit C p v (f j) hv
    (incrementCloseSdp_intrinsicTarget_image W H k (B + j))
  exact closeSdp2_walk_crosses_shell M m _ _ ds v (f j) hvm hj
    ⟨ds0, hd0⟩ ⟨ds1, hd1⟩ hd



/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The difference is formed only when both shortest distances are finite. -/
private def closeSdp2Difference (a b : ℕ∞) : Option ℤ :=
  match a, b with
  | some x, some y => some ((x : ℤ) - (y : ℤ))
  | _, _ => none

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite difference certifies reachability of both ambient sources. -/
private theorem closeSdp2Difference_reachable (M : RootedLocallyFiniteMap)
    (s0 s1 t : RootedLocallyFiniteVertex M.D M.rot)
    (h : (closeSdp2Difference (intrinsicIncrementSdp M s0 t)
      (intrinsicIncrementSdp M s1 t)).isSome) :
    (∃ ds, incrementSdpDartWalk M ds s0 t) ∧
      (∃ ds, incrementSdpDartWalk M ds s1 t) := by
  have ha : intrinsicIncrementSdp M s0 t ≠ ⊤ := by
    intro he
    rw [he] at h
    change (none : Option ℤ).isSome = true at h
    cases h
  have hb : intrinsicIncrementSdp M s1 t ≠ ⊤ := by
    intro he
    rw [he] at h
    cases hval : intrinsicIncrementSdp M s0 t <;>
      rw [hval] at h <;> change (none : Option ℤ).isSome = true at h <;> cases h
  exact ⟨not_not.mp (mt (intrinsicIncrementSdp_eq_top_iff M s0 t).2 ha),
    not_not.mp (mt (intrinsicIncrementSdp_eq_top_iff M s1 t).2 hb)⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Boundary-source identification transports the finite-ball difference exactly. -/
private theorem closeSdp2At_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (k : ℤ)
    (h0 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ k)
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
    (h1 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ (k - 1))
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
    (d : (rootedLocallyFiniteFramedBall M r hr).D) :
    finiteBallSdpIncrementAt (rootedLocallyFiniteFramedBall M r hr) k d =
      closeSdp2Difference
        (incrementCloseSdp_ballDistance M.toRootedLocallyFiniteMap r
          (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k)
          (rootedLocallyFiniteVertexClass M.rot d.1))
        (incrementCloseSdp_ballDistance M.toRootedLocallyFiniteMap r
          (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1))
          (rootedLocallyFiniteVertexClass M.rot d.1)) := by
  let B := rootedLocallyFiniteFramedBall M r hr
  have ha := FiniteBallSdpDistanceIdentification_proved M r hr
    (((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart) d
  have hb := FiniteBallSdpDistanceIdentification_proved M r hr
    (((B.map.rot * B.map.edgeInv) ^ (k - 1)) B.frameEdgeDart) d
  rw [h0] at ha
  rw [h1] at hb
  change closeSdp2Difference _ _ = _
  rw [← ha, ← hb]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Concrete finite faced balls have nonempty eventual shell consensus at every index.
The representative-class transport is separate from this concrete statement. -/
private theorem ae_closeSdp2_concrete_ball_shell_consensus :
    ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)),
      ∀ (H : WholePlaneRotationHypothesis W)
        (hhit : ∀ N, BoundaryHitWitnesses (shiftedStream W N))
        (C : UIBHBOTCertifiedRootCapture W 0)
        (hcap : ∀ r : ℕ, Nonempty (UIBHBOTCertifiedRootCapture W r)) (k : ℤ),
        let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
        ∃ N : ℕ, ∀ m ≥ N, ∃ R : ℕ, ∀ r ≥ R, ∀ hr : 0 < r,
          FiniteBallSdpIncrementConsensus (rootedLocallyFiniteFramedBall M r hr) k m
            (uibhbotMirrorSdpCodeIncrement k W) := by
  classical
  filter_upwards [ae_closeSdp2_intrinsic_uniform_consensus,
    ae_closeSdp2_intrinsic_shell_nonempty] with W hcons hnon H hhit C hcap k
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  let A := M.toRootedLocallyFiniteMap
  obtain ⟨N0, hN0⟩ := hcons H hhit C k
  obtain ⟨N1, hN1⟩ := hnon H hhit C k
  obtain ⟨S0, hS0⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M k
  obtain ⟨S1, hS1⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M (k - 1)
  refine ⟨max N0 N1, fun m hm => ?_⟩
  have hm0 : N0 ≤ m := (le_max_left _ _).trans hm
  have hm1 : N1 ≤ m := (le_max_right _ _).trans hm
  obtain ⟨t, htnear, htfar, ht0, ht1⟩ := hN1 m hm1
  obtain ⟨S2, hS2low, hS2⟩ := incrementCloseSdp_ballDistance_stabilizes_on_radius A
    (intrinsicSdpIncrementSource A k) (intrinsicSdpIncrementSource A (k - 1)) (m + 1)
    (max (max S0 S1) (m + 1))
  obtain ⟨R, hR, hcap⟩ := incrementSdpDartList_captured A S2 [Quotient.out t]
  refine ⟨R, fun r hr hpos => ?_⟩
  have hr2 : S2 ≤ r := hR.trans hr
  have hrlow : max (max S0 S1) (m + 1) ≤ r := hS2low.trans hr2
  have hs0 := hS0 r (by omega) hpos
  have hs1 := hS1 r (by omega) hpos
  let B := rootedLocallyFiniteFramedBall M r hpos
  have htarget (d : B.D)
      (hnear : rootedLocallyFiniteWithinRadius A (m + 1)
        (rootedLocallyFiniteVertexClass M.rot d.1))
      (hfar : ¬ rootedLocallyFiniteWithinRadius A m
        (rootedLocallyFiniteVertexClass M.rot d.1))
      (hreach0 : ∃ ds, incrementSdpDartWalk A ds (intrinsicSdpIncrementSource A k)
        (rootedLocallyFiniteVertexClass M.rot d.1))
      (hreach1 : ∃ ds, incrementSdpDartWalk A ds (intrinsicSdpIncrementSource A (k - 1))
        (rootedLocallyFiniteVertexClass M.rot d.1)) :
      finiteBallSdpIncrementAt B k d = some (uibhbotMirrorSdpCodeIncrement k W) := by
    have hfar0 : ¬ rootedLocallyFiniteWithinRadius A N0
        (rootedLocallyFiniteVertexClass M.rot d.1) := by
      intro hn
      apply hfar
      exact (mem_rootedLocallyFiniteRadiusVertices A m _).mp
        (rootedLocallyFiniteRadiusVertices_mono A hm0
          ((mem_rootedLocallyFiniteRadiusVertices A N0 _).mpr hn))
    obtain ⟨a, b, ha, hb, hi⟩ := hN0 _ hfar0 hreach0 hreach1
    obtain ⟨he0, he1⟩ := hS2 r hr2 _
      ((mem_rootedLocallyFiniteRadiusVertices A (m + 1) _).mpr hnear)
    apply (closeSdp2At_transport M r hpos k hs0 hs1 d).trans
    apply (congrArg₂ closeSdp2Difference he0 he1).trans
    apply (congrArg₂ closeSdp2Difference ha hb).trans
    rw [hi]
    rfl
  constructor
  · let d : B.D := ⟨Quotient.out t,
      rootedLocallyFiniteBallDarts_mono A hr (hcap _ (List.mem_singleton_self _))⟩
    have hd : rootedLocallyFiniteVertexClass M.rot d.1 = t := Quotient.out_eq' t
    have hv := htarget d (hd.symm ▸ htnear) (hd.symm ▸ htfar)
      (hd.symm ▸ ht0) (hd.symm ▸ ht1)
    refine ⟨d, ?_, ?_, ?_⟩
    · apply (rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d).2
      have hdn : rootedLocallyFiniteWithinRadius A (m + 1)
          (rootedLocallyFiniteVertexClass M.rot d.1) := hd.symm ▸ htnear
      exact hdn
    · intro h
      have hdf : rootedLocallyFiniteWithinRadius A m
          (rootedLocallyFiniteVertexClass M.rot d.1) :=
        (rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d).1 h
      exact htfar (hd ▸ hdf)
    · rw [hv]
      rfl
  · intro d hd
    have hnear := (rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d).1
      hd.1
    have hfar : ¬ rootedLocallyFiniteWithinRadius A m
        (rootedLocallyFiniteVertexClass M.rot d.1) :=
      fun h => hd.2.1
        ((rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d).2 h)
    obtain ⟨he0, he1⟩ := hS2 r hr2 _
      ((mem_rootedLocallyFiniteRadiusVertices A (m + 1) _).mpr hnear)
    have he := (closeSdp2At_transport M r hpos k hs0 hs1 d).trans
      (congrArg₂ closeSdp2Difference he0 he1)
    have hfinite := (congrArg Option.isSome he).symm.trans hd.2.2
    obtain ⟨h0, h1⟩ := closeSdp2Difference_reachable A _ _ _ hfinite
    exact htarget d hnear hfar h0 h1


/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The inverse framed vertex map cancels the forward map. -/
private theorem closeSdp2Iso_inverse {B C : FramedBall} (I : FramedBallIso B C)
    (v : MapVertex B.map) :
    framedBallVertexMap I.symm (framedBallVertexMap I v) = v := by
  induction v using Quotient.inductionOn with | h d =>
    change vertexClass _ (I.mapIso.toEquiv.symm (I.mapIso.toEquiv d)) = _
    rw [Equiv.symm_apply_apply]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite directed walks transport along framed isomorphisms. -/
private theorem closeSdp2Walk_iso {B C : FramedBall} (I : FramedBallIso B C)
    (ds : List B.D) (s t : MapVertex B.map) (h : closeSdp2Walk B.map ds s t) :
    closeSdp2Walk C.map (ds.map I.mapIso.toEquiv)
      (framedBallVertexMap I s) (framedBallVertexMap I t) := by
  induction ds generalizing s with
  | nil => exact congrArg (framedBallVertexMap I) h
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := h
    refine ⟨fun hc => hm ((I.mapIso.missing_iff d).1 hc),
      (I.mapIso.tail_iff d).2 ht, congrArg (framedBallVertexMap I) hs, ?_⟩
    have hi := ih _ hw
    have he : framedBallVertexMap I (dartHeadVertex B.map d) =
        dartHeadVertex C.map (I.mapIso.toEquiv d) := by
      change vertexClass _ (I.mapIso.toEquiv (B.map.edgeInv d)) = _
      rw [I.mapIso.edgeInv_comm]
      rfl
    rw [he] at hi
    exact hi

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Isomorphisms cannot increase finite simple shortest distance. -/
private theorem closeSdp2Distance_iso_le {B C : FramedBall} (I : FramedBallIso B C)
    (s t : MapVertex B.map) :
    (show ℕ∞ from simpleDirectedPathSDPLength C.map
      (framedBallVertexMap I s) (framedBallVertexMap I t)) ≤
      (show ℕ∞ from simpleDirectedPathSDPLength B.map s t) := by
  rw [closeSdp2Finite_inf, closeSdp2Finite_inf]
  apply le_iInf
  intro ds
  apply le_iInf
  intro hw
  exact iInf_le_of_le (ds.map I.mapIso.toEquiv)
    (iInf_le_of_le (closeSdp2Walk_iso I ds s t hw)
      (le_of_eq (congrArg (fun n : ℕ => (n : ℕ∞)) (List.length_map _))))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Framed isomorphisms preserve the complete finite SDP, including infinity. -/
private theorem closeSdp2Distance_iso {B C : FramedBall} (I : FramedBallIso B C)
    (s t : MapVertex B.map) :
    (show ℕ∞ from simpleDirectedPathSDPLength C.map
      (framedBallVertexMap I s) (framedBallVertexMap I t)) =
      (show ℕ∞ from simpleDirectedPathSDPLength B.map s t) := by
  apply le_antisymm (closeSdp2Distance_iso_le I s t)
  have h := closeSdp2Distance_iso_le I.symm (framedBallVertexMap I s)
    (framedBallVertexMap I t)
  simpa only [closeSdp2Iso_inverse] using h

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The ordered boundary sources transport at every integer index. -/
private theorem closeSdp2Source_iso {B C : FramedBall} (I : FramedBallIso B C) (k : ℤ) :
    framedBallVertexMap I (finiteBallSdpIncrementSource B k) =
      finiteBallSdpIncrementSource C k := by
  let e := I.mapIso.toEquiv
  let F := B.map.rot * B.map.edgeInv
  let G := C.map.rot * C.map.edgeInv
  have hg : G = e.permCongr F := by
    ext d
    change C.map.rot (C.map.edgeInv d) = e (B.map.rot (B.map.edgeInv (e.symm d)))
    rw [I.mapIso.rot_comm, I.mapIso.edgeInv_comm, Equiv.apply_symm_apply]
  have hp : e.permCongr (F ^ k) = (e.permCongr F) ^ k :=
    map_zpow e.permCongrHom F k
  change vertexClass _ (e ((F ^ k) B.frameEdgeDart)) =
    vertexClass _ ((G ^ k) C.frameEdgeDart)
  apply congrArg (vertexClass C.map.toCombinatorialMap)
  rw [hg, ← hp]
  change e ((F ^ k) B.frameEdgeDart) =
    e ((F ^ k) (e.symm C.frameEdgeDart))
  rw [← I.frameEdge_comm, Equiv.symm_apply_apply]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The integer difference at corresponding finite targets is isomorphism invariant. -/
private theorem closeSdp2At_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (d : B.D) :
    finiteBallSdpIncrementAt C k (I.mapIso.toEquiv d) = finiteBallSdpIncrementAt B k d := by
  have ha := closeSdp2Distance_iso I (finiteBallSdpIncrementSource B k) (vertexClass _ d)
  have hb := closeSdp2Distance_iso I (finiteBallSdpIncrementSource B (k - 1))
    (vertexClass _ d)
  rw [closeSdp2Source_iso] at ha hb
  change closeSdp2Difference _ _ = closeSdp2Difference _ _
  exact congrArg₂ closeSdp2Difference ha hb

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shell membership transports with the root vertex and every edge identity. -/
private theorem closeSdp2Shell_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (d : B.D) :
    finiteBallSdpIncrementShell B k m d ↔
      finiteBallSdpIncrementShell C k m (I.mapIso.toEquiv d) := by
  have hroot : framedBallVertexMap I (vertexClass _ B.rootDart) =
      vertexClass _ C.rootDart := Quotient.sound I.root_vertex
  have h0 := framedBallWithinRadius_iso_iff I m (vertexClass _ B.rootDart)
    (vertexClass _ d)
  have h1 := framedBallWithinRadius_iso_iff I (m + 1) (vertexClass _ B.rootDart)
    (vertexClass _ d)
  rw [hroot] at h0 h1
  change (_ ∧ ¬ _ ∧ _) ↔ (_ ∧ ¬ _ ∧ _)
  rw [h0, h1, closeSdp2At_iso I k d]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Nonempty shell consensus transports across arbitrary framed-ball isomorphisms. -/
private theorem closeSdp2Consensus_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (z : ℤ) (h : FiniteBallSdpIncrementConsensus B k m z) :
    FiniteBallSdpIncrementConsensus C k m z := by
  constructor
  · obtain ⟨d, hd⟩ := h.1
    exact ⟨I.mapIso.toEquiv d, (closeSdp2Shell_iso I k m d).1 hd⟩
  · intro c hc
    let d := I.mapIso.toEquiv.symm c
    have he : I.mapIso.toEquiv d = c := I.mapIso.toEquiv.apply_symm_apply c
    have hd : finiteBallSdpIncrementShell B k m d :=
      (closeSdp2Shell_iso I k m d).2 (he.symm ▸ hc)
    exact (he ▸ closeSdp2At_iso I k d).trans (h.2 d hd)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shell stabilization holds at every integer index in the faced-ball representative. -/
theorem uibhbotSdpIncrementBallShellStabilizationAt_proved (k : ℤ) :
    UIBHBOTSdpIncrementBallShellStabilizationAt k := by
  filter_upwards [ae_closeSdp2_concrete_ball_shell_consensus,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hW hgood
  obtain ⟨H, hhit, C, hcap, hM⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hgood).1
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  obtain ⟨N, hN⟩ := hW H hhit C hcap k
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨R, hR⟩ := hN m hm
  refine ⟨R, fun r hr => ?_⟩
  apply (finiteBallSdpIncrementKernel_eq_some_iff k m _ _).2
  rw [hM]
  let q := rootedLocallyFiniteFacedBallClass r M
  obtain ⟨J⟩ : Nonempty (FacedFramedBallIso q.out
      (rootedLocallyFiniteFacedBall M (r + 1) (Nat.succ_pos r))) :=
    Quotient.exact q.out_eq
  exact closeSdp2Consensus_iso J.toFramedBallIso.symm k m _
    (hR (r + 1) (by omega) (Nat.succ_pos r))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The existing faced-map law uses its Borel topology. -/
noncomputable local instance closeSdp2Topology : TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The existing faced-map law uses the corresponding Borel measurable structure. -/
noncomputable local instance closeSdp2Measurable : MeasurableSpace RootedLocallyFinitePlanarMap :=
  borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic characterization and unbounded common reachable targets for the observable. -/
@[expose] def closeSdp2ObservableData (M : RootedLocallyFinitePlanarMap) : Prop :=
  (∀ k : ℤ, ∃ N : ℕ, ∀ t : RootedLocallyFiniteVertex M.D M.rot,
    ¬ rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap N t →
    (∃ ds, incrementSdpDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k) t) →
    (∃ ds, incrementSdpDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t) →
    ∃ a b : ℕ,
      intrinsicIncrementSdp M.toRootedLocallyFiniteMap
        (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k) t = (a : ℕ∞) ∧
      intrinsicIncrementSdp M.toRootedLocallyFiniteMap
        (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t = (b : ℕ∞) ∧
      finiteBallSdpIncrementObservable k M = (a : ℤ) - (b : ℤ)) ∧
  (∀ k : ℤ, ∀ T : Finset (RootedLocallyFiniteVertex M.D M.rot),
    ∃ t, t ∉ T ∧
      (∃ ds, incrementSdpDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap k) t) ∧
      (∃ ds, incrementSdpDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicSdpIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t))




@[expose] def SdpIntrinsicObservableDataMeasurable : Prop :=
  MeasurableSet {M : RootedLocallyFinitePlanarMap | closeSdp2ObservableData M}

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conditional transport of the full characterization from code space to the faced-map law. -/
private theorem closeSdp2_ae_observableData
    (hmeas : SdpIntrinsicObservableDataMeasurable) :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      closeSdp2ObservableData M := by
  change ∀ᵐ M ∂((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode), closeSdp2ObservableData M
  apply (ae_map_iff measurable_uibhbotRootedPlanarMapOfCode.aemeasurable hmeas).2
  have hreal : ∀ᵐ W ∂(uibhbotCodeLawRel : Measure (ℤ → Fin 3)), ∀ k : ℤ,
      finiteBallSdpIncrementObservable k (uibhbotRootedPlanarMapOfCode W) =
        uibhbotMirrorSdpCodeIncrement k W := by
    apply ae_all_iff.mpr
    intro k
    exact finiteBallSdpIncrementObservable_realization_of_ballShellStabilization k
      (uibhbotSdpIncrementBallShellStabilizationAt_proved k)
  filter_upwards [ae_closeSdp2_intrinsic_uniform_consensus,
    ae_closeSdp2_intrinsic_shell_nonempty, hreal,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hc hn hv hgood
  obtain ⟨H, hhit, C, hcap, hM⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hgood).1
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  have hvM (k : ℤ) : finiteBallSdpIncrementObservable k M =
      uibhbotMirrorSdpCodeIncrement k W :=
    (congrArg (finiteBallSdpIncrementObservable k) hM).symm.trans (hv k)
  rw [hM]
  constructor
  · intro k
    obtain ⟨N, hN⟩ := hc H hhit C k
    refine ⟨N, fun t ht h0 h1 => ?_⟩
    obtain ⟨a, b, ha, hb, hi⟩ := hN t ht h0 h1
    exact ⟨a, b, ha, hb, (hvM k).trans hi⟩
  · intro k T
    obtain ⟨R, _, hR⟩ := closeSdp2_vertexFinset_captured M.toRootedLocallyFiniteMap T 0
    obtain ⟨N, hN⟩ := hn H hhit C k
    obtain ⟨t, _, ht, h0, h1⟩ := hN (max N R) (le_max_left _ _)
    refine ⟨t, fun hmem => ht ?_, h0, h1⟩
    exact (mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap _ t).1
      (rootedLocallyFiniteRadiusVertices_mono M.toRootedLocallyFiniteMap (le_max_right N R)
        ((mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap R t).2
          (hR t hmem)))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic characterization forces reflection with the ordered-root shift two. -/
private theorem closeSdp2_reflection_of_data (M : RootedLocallyFinitePlanarMap)
    (h : closeSdp2ObservableData M)
    (hm : closeSdp2ObservableData (mirrorRootedLocallyFinitePlanarMap M)) :
    finiteBallSdpIncrementObservable 0 (mirrorRootedLocallyFinitePlanarMap M) =
      -finiteBallSdpIncrementObservable 2 M := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let B := mirrorRootedLocallyFiniteMap A
  let e := incrementSdpMirrorVertexEquiv A
  obtain ⟨N, hN⟩ := h.1 2
  obtain ⟨R, hR⟩ := hm.1 0
  let T := rootedLocallyFiniteRadiusVertices A N ∪
    (rootedLocallyFiniteRadiusVertices B R).image e.symm
  obtain ⟨t, ht, h0, h1⟩ := h.2 2 T
  have htN : ¬ rootedLocallyFiniteWithinRadius A N t := by
    intro hn
    exact ht (Finset.mem_union_left _
      ((mem_rootedLocallyFiniteRadiusVertices A N t).2 hn))
  have htR : ¬ rootedLocallyFiniteWithinRadius B R (e t) := by
    intro hr
    apply ht
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨e t, (mem_rootedLocallyFiniteRadiusVertices B R (e t)).2 hr,
        e.symm_apply_apply t⟩
  obtain ⟨a, b, ha, hb, hi⟩ := hN t htN h0 h1
  have hm0 : ∃ ds, incrementSdpDartWalk B ds (intrinsicSdpIncrementSource B 0) (e t) := by
    obtain ⟨ds, hd⟩ := h1
    have hx := (incrementSdpDartWalk_mirror A ds
      (intrinsicSdpIncrementSource A (2 - 1)) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicSdpIncrementSource_mirror, sub_zero,
      show (2 : ℤ) - 1 = 1 from rfl, e, B] using hx
  have hm1 : ∃ ds, incrementSdpDartWalk B ds
      (intrinsicSdpIncrementSource B (0 - 1)) (e t) := by
    obtain ⟨ds, hd⟩ := h0
    have hx := (incrementSdpDartWalk_mirror A ds
      (intrinsicSdpIncrementSource A 2) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicSdpIncrementSource_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl, e, B] using hx
  obtain ⟨c, d, hc, hd, hj⟩ := hR (e t) htR hm0 hm1
  change intrinsicIncrementSdp B (intrinsicSdpIncrementSource B 0) (e t) = (c : ℕ∞) at hc
  change intrinsicIncrementSdp B (intrinsicSdpIncrementSource B (0 - 1)) (e t) =
    (d : ℕ∞) at hd
  have hc' : intrinsicIncrementSdp A (intrinsicSdpIncrementSource A (2 - 1)) t =
      (c : ℕ∞) := by
    simpa only [B, e, intrinsicSdpIncrementSource_mirror, intrinsicIncrementSdp_mirror,
      sub_zero, show (2 : ℤ) - 1 = 1 from rfl] using hc
  have hd' : intrinsicIncrementSdp A (intrinsicSdpIncrementSource A 2) t = (d : ℕ∞) := by
    simpa only [B, e, intrinsicSdpIncrementSource_mirror, intrinsicIncrementSdp_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl] using hd
  have hcb : c = b := by exact_mod_cast hc'.symm.trans hb
  have hda : d = a := by exact_mod_cast hd'.symm.trans ha
  rw [hcb, hda] at hj
  omega




theorem uibhbotSdpIncrementObservableReflection_of_dataMeasurable
    (hmeas : SdpIntrinsicObservableDataMeasurable) :
    UIBHBOTSdpIncrementObservableReflection finiteBallSdpIncrementObservable := by
  have hdata := closeSdp2_ae_observableData hmeas
  have hmap : ∀ᵐ M ∂((uibhbotRootedPlanarMapLaw :
      Measure RootedLocallyFinitePlanarMap).map mirrorRootedLocallyFinitePlanarMap),
      closeSdp2ObservableData M := by
    rw [uibhbotLaw_mirror_invariant
      DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed]
    exact hdata
  have : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  have hm := ae_of_ae_map
    continuous_mirrorRootedLocallyFinitePlanarMap.measurable.aemeasurable hmap
  filter_upwards [hdata, hm] with M hM hmirror
  exact closeSdp2_reflection_of_data M hM hmirror

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conditional SDP symmetry with exactly one remaining measurability proposition.
No unconditional reflection or symmetry is asserted. -/
theorem hsymSdp_proved (hmeas : SdpIntrinsicObservableDataMeasurable) :
    iidCodeMeasure.map (SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0) =
      iidCodeMeasure.map
        (fun ω => -SDPMasterFromLaw.increment busemannSDPMeasurableVersion 0 ω) := by
  exact hsymSdp_of_remaining_ballShell_and_reflection
    (uibhbotSdpIncrementBallShellStabilizationAt_proved 0)
    (uibhbotSdpIncrementBallShellStabilizationAt_proved 2)
    (uibhbotSdpIncrementObservableReflection_of_dataMeasurable hmeas)

end DirectedDistances.PaperProofs.Section5
