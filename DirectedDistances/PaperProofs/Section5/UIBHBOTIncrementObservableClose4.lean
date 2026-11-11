module

public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableClose3
public import DirectedDistances.PaperProofs.Section5.UIBHBOTIncrementObservableCloseSdp





public section
namespace DirectedDistances.PaperProofs.Section5

open MeasureTheory Filter Quiver
open DirectedDistances.RandomWalk DirectedDistances.Recursive DirectedDistances.PlanarMap
open DirectedDistances.KMSW DirectedMapWithMissing
open DirectedDistances.PaperProofs.Section3.RootedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite directed dart walks used only for the finite-distance comparison. -/
private def incrementClose4_Walk {D : Type*} [Fintype D] [DecidableEq D]
    (M : DirectedMapWithMissing D) : List D → MapVertex M → MapVertex M → Prop
  | [], s, t => s = t
  | d :: ds, s, t => ¬ M.missing d ∧ M.tail d ∧ dartTailVertex M d = s ∧
      incrementClose4_Walk M ds (dartHeadVertex M d) t

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Prepending outside the existing vertex list preserves simplicity. -/
private def incrementClose4_Prepend
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
A simple directed path gives the corresponding finite directed walk. -/
private theorem incrementClose4_Simple_walk (M : DirectedMapWithMissing D)
    {s t : MapVertex M} {n : ℕ} (P : SimpleDirectedDartPath M s t n) :
    ∃ ds : List D, incrementClose4_Walk M ds s t ∧ ds.length = n := by
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
Every finite directed walk gives geometric directed reachability. -/
private theorem incrementClose4_reaches (M : DirectedMapWithMissing D)
    (ds : List D) (s t : MapVertex M) (hw : incrementClose4_Walk M ds s t) :
    Relation.ReflTransGen M.directedStep s t := by
  induction ds generalizing s with
  | nil => exact hw ▸ Relation.ReflTransGen.refl
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := hw
    exact (ih _ hw).head ⟨d, hm, ht, hs, rfl⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Acyclicity preserves the exact length when a walk is made into a simple path. -/
private theorem incrementClose4_Walk_simple (M : DirectedMapWithMissing D)
    (ha : M.IsAcyclic) (ds : List D) (s t : MapVertex M)
    (hw : incrementClose4_Walk M ds s t) :
    Nonempty (SimpleDirectedDartPath M s t ds.length) := by
  classical
  induction ds generalizing s with
  | nil =>
    have he : s = t := hw
    subst t
    exact ⟨{
      darts := []
      vertices := [s]
      darts_length := rfl
      vertices_length := rfl
      vertices_nodup := List.nodup_singleton s
      start_vertex := rfl
      end_vertex := rfl
      edge_step := fun i => Fin.elim0 i }⟩
  | cons d ds ih =>
    obtain ⟨hm, ht, hs, hw⟩ := hw
    obtain ⟨P⟩ := ih _ hw
    have hnot : s ∉ P.vertices := by
      intro hmem
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
      let j : Fin (ds.length + 1) := ⟨i.val, by
        have := i.isLt
        have hl := P.vertices_length
        omega⟩
      obtain ⟨es, he, _⟩ := incrementClose4_Simple_walk M (P.prefix j)
      have hr := incrementClose4_reaches M es _ _ he
      have heq : P.vertices.get ⟨j.val, by rw [P.vertices_length]; exact j.isLt⟩ = s := hi
      rw [heq] at hr
      exact ha s (Relation.TransGen.head' ⟨d, hm, ht, hs, rfl⟩ hr)
    exact ⟨incrementClose4_Prepend M d hm ht hs rfl P hnot⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite simple LDP equals the supremum of all walk lengths on an acyclic map. -/
private theorem incrementClose4_Finite_sup (M : DirectedMapWithMissing D)
    (ha : M.IsAcyclic) (s t : MapVertex M) :
    (simpleDirectedPathLDPLength M s t).map (fun n : ℕ => (n : ℕ∞)) =
      ⨆ ds : List D, ⨆ (_ : incrementClose4_Walk M ds s t),
        ((ds.length : ℕ∞) : WithBot ℕ∞) := by
  classical
  apply le_antisymm
  · cases hm : simpleDirectedPathLDPLength M s t with
    | bot => exact bot_le
    | coe n =>
      obtain ⟨P, _⟩ := (mem_simpleDirectedPathLengthSet M s t n).1
        (Finset.mem_of_max hm)
      obtain ⟨ds, hw, hl⟩ := incrementClose4_Simple_walk M P
      exact le_iSup_of_le ds (le_iSup_of_le hw (by
        rw [hl]
        exact le_rfl))
  · apply iSup_le
    intro ds
    apply iSup_le
    intro hw
    have hm := Finset.le_max ((mem_simpleDirectedPathLengthSet M s t ds.length).2
      ⟨(incrementClose4_Walk_simple M ha ds s t hw).some, trivial⟩)
    exact (WithBot.map_le_iff (fun n : ℕ => (n : ℕ∞))
      (fun {_ _} => ENat.natCast_le_natCast)).2 hm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite rotation quotient embeds in the ambient vertex quotient. -/
private noncomputable def incrementClose4_Vertex (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) :
    MapVertex (rootedLocallyFiniteFramedBall M r hr).map →
      RootedLocallyFiniteVertex M.D M.rot := by
  classical
  exact Quotient.map Subtype.val (fun x y h =>
    (rootedLocallyFiniteBall_rot_sameCycle_iff M.toRootedLocallyFiniteMap r x y).1 h)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite-to-ambient quotient map preserves and reflects vertex identity. -/
private theorem incrementClose4_Vertex_injective (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) : Function.Injective (incrementClose4_Vertex M r hr) := by
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
private theorem incrementClose4_Walk_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (ds : List (rootedLocallyFiniteFramedBall M r hr).D)
    (s t : MapVertex (rootedLocallyFiniteFramedBall M r hr).map) :
    incrementClose4_Walk (rootedLocallyFiniteFramedBall M r hr).map ds s t ↔
      incrementDartWalk M.toRootedLocallyFiniteMap (ds.map Subtype.val)
        (incrementClose4_Vertex M r hr s) (incrementClose4_Vertex M r hr t) := by
  classical
  induction ds generalizing s with
  | nil => exact (incrementClose4_Vertex_injective M r hr).eq_iff.symm
  | cons d ds ih =>
    change (_ ∧ _ ∧ _ ∧ incrementClose4_Walk _ _ _ _) ↔
      (_ ∧ _ ∧ _ ∧ incrementDartWalk _ _ _ _)
    rw [ih]
    have he : dartTailVertex (rootedLocallyFiniteFramedBall M r hr).map d = s ↔
        rootedLocallyFiniteVertexClass M.rot d.1 = incrementClose4_Vertex M r hr s :=
      (incrementClose4_Vertex_injective M r hr).eq_iff.symm
    rw [he]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A retained ambient list lifts to a finite-ball list with identical darts. -/
private theorem incrementClose4_List_lift (M : RootedLocallyFinitePlanarMap)
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
The concrete finite ball inherits ambient acyclicity. -/
private theorem incrementClose4_ball_acyclic (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) : (rootedLocallyFiniteFramedBall M r hr).map.IsAcyclic := by
  intro v hv
  apply M.acyclic (incrementClose4_Vertex M r hr v)
  apply hv.lift (incrementClose4_Vertex M r hr)
  intro a b hab
  obtain ⟨d, hm, ht, hs, he⟩ := hab
  exact ⟨d.1, hm, ht, congrArg (incrementClose4_Vertex M r hr) hs,
    congrArg (incrementClose4_Vertex M r hr) he⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite simple LDP equals the restricted intrinsic LDP, including unreachable pairs. -/
theorem incrementClose4_distanceIdentification
    (M : RootedLocallyFinitePlanarMap) (r : ℕ) (hr : 0 < r)
    (d e : (rootedLocallyFiniteFramedBall M r hr).D) :
    (simpleDirectedPathLDPLength (rootedLocallyFiniteFramedBall M r hr).map
      (vertexClass _ d) (vertexClass _ e)).map (fun n : ℕ => (n : ℕ∞)) =
      incrementClose_ballLdp M.toRootedLocallyFiniteMap r
        (rootedLocallyFiniteVertexClass M.rot d.1)
        (rootedLocallyFiniteVertexClass M.rot e.1) := by
  classical
  rw [incrementClose4_Finite_sup _ (incrementClose4_ball_acyclic M r hr)]
  apply le_antisymm
  · apply iSup_le
    intro es
    apply iSup_le
    intro hw
    have hw' := (incrementClose4_Walk_transport M r hr es
      (vertexClass _ d) (vertexClass _ e)).1 hw
    have hd : ∀ x ∈ es.map Subtype.val,
        x ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact y.2
    exact le_iSup_of_le (es.map Subtype.val) (le_iSup_of_le hw'
      (le_iSup_of_le hd (le_of_eq (congrArg
        (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞)) (List.length_map Subtype.val)).symm)))
  · apply iSup_le
    intro ds
    apply iSup_le
    intro hw
    apply iSup_le
    intro hd
    obtain ⟨es, he⟩ := incrementClose4_List_lift M r hr ds hd
    have hw' : incrementClose4_Walk (rootedLocallyFiniteFramedBall M r hr).map es
        (vertexClass _ d) (vertexClass _ e) := by
      apply (incrementClose4_Walk_transport M r hr es (vertexClass _ d) (vertexClass _ e)).2
      change incrementDartWalk M.toRootedLocallyFiniteMap (es.map Subtype.val)
        (rootedLocallyFiniteVertexClass M.rot d.1)
        (rootedLocallyFiniteVertexClass M.rot e.1)
      rw [he]
      exact hw
    have hl : es.length = ds.length := by
      have h := congrArg List.length he
      exact (List.length_map Subtype.val).symm.trans h
    exact le_iSup_of_le es (le_iSup_of_le hw' (by rw [hl]))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite natural embedding reflects exact finite values. -/
private theorem incrementClose4_map_eq_iff (a : WithBot ℕ) (n : ℕ) :
    a.map (fun m : ℕ => (m : ℕ∞)) = ((n : ℕ∞) : WithBot ℕ∞) ↔ a = (n : WithBot ℕ) := by
  cases a with
  | bot =>
    constructor
    · intro h
      exact (WithBot.bot_ne_coe h).elim
    · intro h
      exact (WithBot.bot_ne_coe h).elim
  | coe m =>
    constructor
    · intro h
      have he : (m : ℕ∞) = (n : ℕ∞) := WithBot.coe_injective h
      exact congrArg (fun x : ℕ => (x : WithBot ℕ)) (ENat.natCast_inj.mp he)
    · intro h
      have he : m = n := WithBot.coe_injective h
      subst n
      rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Boundary traversal identifies the finite and restricted increment at every target. -/
private theorem incrementClose4_at_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (k : ℤ)
    (h0 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ k)
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicIncrementSource M.toRootedLocallyFiniteMap k)
    (h1 : rootedLocallyFiniteVertexClass M.rot
      ((((rootedLocallyFiniteFramedBall M r hr).map.rot *
        (rootedLocallyFiniteFramedBall M r hr).map.edgeInv) ^ (k - 1))
          (rootedLocallyFiniteFramedBall M r hr).frameEdgeDart).1 =
      intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1))
    (d : (rootedLocallyFiniteFramedBall M r hr).D) :
    finiteBallIncrementAt (rootedLocallyFiniteFramedBall M r hr) k d =
      incrementClose3_finiteDifference
        (incrementClose_ballLdp M.toRootedLocallyFiniteMap r
          (intrinsicIncrementSource M.toRootedLocallyFiniteMap k)
          (rootedLocallyFiniteVertexClass M.rot d.1))
        (incrementClose_ballLdp M.toRootedLocallyFiniteMap r
          (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1))
          (rootedLocallyFiniteVertexClass M.rot d.1)) := by
  let B := rootedLocallyFiniteFramedBall M r hr
  have ha := incrementClose4_distanceIdentification M r hr
    (((B.map.rot * B.map.edgeInv) ^ k) B.frameEdgeDart) d
  have hb := incrementClose4_distanceIdentification M r hr
    (((B.map.rot * B.map.edgeInv) ^ (k - 1)) B.frameEdgeDart) d
  rw [h0] at ha
  rw [h1] at hb
  apply Option.ext
  intro z
  rw [incrementClose3_finiteDifference_eq_some_iff, ← ha, ← hb]
  simp only [incrementClose4_map_eq_iff]
  change finiteBallIncrementAt B k d = some z ↔
    ∃ n m : ℕ,
      simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B k)
        (vertexClass _ d) = (n : WithBot ℕ) ∧
      simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B (k - 1))
        (vertexClass _ d) = (m : WithBot ℕ) ∧ z = (n : ℤ) - (m : ℤ)
  unfold finiteBallIncrementAt
  cases simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B k)
      (vertexClass _ d) with
  | bot =>
    cases simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B (k - 1))
      (vertexClass _ d) <;> simp
  | coe a =>
    cases simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B (k - 1))
        (vertexClass _ d) with
    | bot => simp
    | coe b =>
      constructor
      · intro he
        exact ⟨a, b, rfl, rfl, (Option.some.inj he).symm⟩
      · rintro ⟨n, m, hn, hm, hz⟩
        have hn' : a = n := WithBot.coe_injective hn
        have hm' : b = m := WithBot.coe_injective hm
        subst n
        subst m
        exact congrArg some hz.symm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The inverse framed vertex map cancels the forward map. -/
private theorem incrementClose4_iso_inverse {B C : FramedBall} (I : FramedBallIso B C)
    (v : MapVertex B.map) :
    framedBallVertexMap I.symm (framedBallVertexMap I v) = v := by
  induction v using Quotient.inductionOn with | h d =>
    change vertexClass _ (I.mapIso.toEquiv.symm (I.mapIso.toEquiv d)) = _
    rw [Equiv.symm_apply_apply]
    rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The induced framed vertex map is injective. -/
private theorem incrementClose4_iso_injective {B C : FramedBall} (I : FramedBallIso B C) :
    Function.Injective (framedBallVertexMap I) := by
  intro a b hab
  have h := congrArg (framedBallVertexMap I.symm) hab
  simpa only [incrementClose4_iso_inverse] using h

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Simple paths transport without losing their length or vertex distinctness. -/
private noncomputable def incrementClose4_path_iso {B C : FramedBall}
    (I : FramedBallIso B C) {s t : MapVertex B.map} {n : ℕ}
    (P : SimpleDirectedDartPath B.map s t n) :
    SimpleDirectedDartPath C.map (framedBallVertexMap I s) (framedBallVertexMap I t) n where
  darts := P.darts.map I.mapIso.toEquiv
  vertices := P.vertices.map (framedBallVertexMap I)
  darts_length := by simp [P.darts_length]
  vertices_length := by simp [P.vertices_length]
  vertices_nodup := P.vertices_nodup.map (incrementClose4_iso_injective I)
  start_vertex := by simpa using congrArg (framedBallVertexMap I) P.start_vertex
  end_vertex := by simpa using congrArg (framedBallVertexMap I) P.end_vertex
  edge_step := by
    intro i
    have hiMap := i.isLt
    simp only [List.length_map] at hiMap
    have hi : i.val < n := by simpa [P.darts_length] using hiMap
    let j : Fin P.darts.length := ⟨i.val, by rw [P.darts_length]; exact hi⟩
    let jv : Fin P.vertices.length := ⟨i.val, by
      rw [P.vertices_length]
      omega⟩
    let jv' : Fin P.vertices.length := ⟨i.val + 1, by
      rw [P.vertices_length]
      omega⟩
    have h := P.edge_step j
    have hget : (P.darts.map I.mapIso.toEquiv).get i = I.mapIso.toEquiv (P.darts.get j) := by
      simp [j]
    have hgetV : (P.vertices.map (framedBallVertexMap I)).get
        ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          (framedBallVertexMap I) (P.vertices.get jv) := by
      simp [jv]
    have hgetV' : (P.vertices.map (framedBallVertexMap I)).get
        ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
          (framedBallVertexMap I) (P.vertices.get jv') := by
      simp [jv']
    rw [hget]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hm
      exact h.1 ((I.mapIso.missing_iff _).mp hm)
    · exact (I.mapIso.tail_iff _).2 h.2.1
    · calc
        (P.vertices.map (framedBallVertexMap I)).get
            ⟨i.val, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
            (framedBallVertexMap I) (P.vertices.get jv) := hgetV
        _ = (framedBallVertexMap I) (dartTailVertex B.map (P.darts.get j)) :=
            congrArg (framedBallVertexMap I) h.2.2.1
        _ = dartTailVertex C.map (I.mapIso.toEquiv (P.darts.get j)) :=
            rfl
    · calc
        (P.vertices.map (framedBallVertexMap I)).get
            ⟨i.val + 1, by simp only [List.length_map]; rw [P.vertices_length]; omega⟩ =
              (framedBallVertexMap I) (P.vertices.get jv') := hgetV'
        _ = (framedBallVertexMap I) (dartHeadVertex B.map (P.darts.get j)) :=
            congrArg (framedBallVertexMap I) h.2.2.2
        _ = dartHeadVertex C.map (I.mapIso.toEquiv (P.darts.get j)) :=
            by
              change vertexClass _ (I.mapIso.toEquiv (B.map.edgeInv _)) = _
              rw [I.mapIso.edgeInv_comm]
              rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Framed isomorphisms preserve all simple path lengths and the unreachable value. -/
private theorem incrementClose4_distance_iso {B C : FramedBall} (I : FramedBallIso B C)
    (s t : MapVertex B.map) :
    simpleDirectedPathLDPLength C.map (framedBallVertexMap I s) (framedBallVertexMap I t) =
      simpleDirectedPathLDPLength B.map s t := by
  have hset : simpleDirectedPathLengthSet C.map
      (framedBallVertexMap I s) (framedBallVertexMap I t) =
      simpleDirectedPathLengthSet B.map s t := by
    ext n
    rw [mem_simpleDirectedPathLengthSet, mem_simpleDirectedPathLengthSet]
    constructor
    · rintro ⟨P, _⟩
      have Q := incrementClose4_path_iso I.symm P
      rw [incrementClose4_iso_inverse, incrementClose4_iso_inverse] at Q
      exact ⟨Q, trivial⟩
    · rintro ⟨P, _⟩
      exact ⟨incrementClose4_path_iso I P, trivial⟩
  exact congrArg Finset.max hset

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The ordered boundary sources transport at every integer index. -/
private theorem incrementClose4_Source_iso {B C : FramedBall} (I : FramedBallIso B C) (k : ℤ) :
    framedBallVertexMap I (finiteBallIncrementSource B k) =
      finiteBallIncrementSource C k := by
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
private theorem incrementClose4_At_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (d : B.D) :
    finiteBallIncrementAt C k (I.mapIso.toEquiv d) = finiteBallIncrementAt B k d := by
  have ha := incrementClose4_distance_iso I (finiteBallIncrementSource B k) (vertexClass _ d)
  have hb := incrementClose4_distance_iso I (finiteBallIncrementSource B (k - 1))
    (vertexClass _ d)
  rw [incrementClose4_Source_iso] at ha hb
  change simpleDirectedPathLDPLength C.map (finiteBallIncrementSource C k)
    (vertexClass _ (I.mapIso.toEquiv d)) = _ at ha
  change simpleDirectedPathLDPLength C.map (finiteBallIncrementSource C (k - 1))
    (vertexClass _ (I.mapIso.toEquiv d)) = _ at hb
  unfold finiteBallIncrementAt
  rw [ha, hb]

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Shell membership transports with the root vertex and every edge identity. -/
private theorem incrementClose4_Shell_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (d : B.D) :
    finiteBallIncrementShell B k m d ↔
      finiteBallIncrementShell C k m (I.mapIso.toEquiv d) := by
  have hroot : framedBallVertexMap I (vertexClass _ B.rootDart) =
      vertexClass _ C.rootDart := Quotient.sound I.root_vertex
  have h0 := framedBallWithinRadius_iso_iff I m (vertexClass _ B.rootDart)
    (vertexClass _ d)
  have h1 := framedBallWithinRadius_iso_iff I (m + 1) (vertexClass _ B.rootDart)
    (vertexClass _ d)
  rw [hroot] at h0 h1
  change (_ ∧ ¬ _ ∧ _) ↔ (_ ∧ ¬ _ ∧ _)
  rw [h0, h1, incrementClose4_At_iso I k d]
  rfl

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Nonempty shell consensus transports across arbitrary framed-ball isomorphisms. -/
private theorem incrementClose4_Consensus_iso {B C : FramedBall} (I : FramedBallIso B C)
    (k : ℤ) (m : ℕ) (z : ℤ) (h : FiniteBallIncrementConsensus B k m z) :
    FiniteBallIncrementConsensus C k m z := by
  constructor
  · obtain ⟨d, hd⟩ := h.1
    exact ⟨I.mapIso.toEquiv d, (incrementClose4_Shell_iso I k m d).1 hd⟩
  · intro c hc
    let d := I.mapIso.toEquiv.symm c
    have he : I.mapIso.toEquiv d = c := I.mapIso.toEquiv.apply_symm_apply c
    have hd : finiteBallIncrementShell B k m d :=
      (incrementClose4_Shell_iso I k m d).2 (he.symm ▸ hc)
    exact (he ▸ incrementClose4_At_iso I k d).trans (h.2 d hd)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Finite simple LDP is finite exactly when a directed walk exists. -/
private theorem incrementClose4_finite_reachable (M : DirectedMapWithMissing D)
    (ha : M.IsAcyclic) (s t : MapVertex M) :
    simpleDirectedPathLDPLength M s t ≠ ⊥ ↔ ∃ ds, incrementClose4_Walk M ds s t := by
  classical
  constructor
  · intro hn
    cases hm : simpleDirectedPathLDPLength M s t with
    | bot => exact (hn hm).elim
    | coe n =>
      obtain ⟨P, _⟩ := (mem_simpleDirectedPathLengthSet M s t n).1 (Finset.mem_of_max hm)
      obtain ⟨ds, hw, _⟩ := incrementClose4_Simple_walk M P
      exact ⟨ds, hw⟩
  · rintro ⟨ds, hw⟩ he
    have hm := Finset.le_max ((mem_simpleDirectedPathLengthSet M s t ds.length).2
      ⟨(incrementClose4_Walk_simple M ha ds s t hw).some, trivial⟩)
    change (ds.length : WithBot ℕ) ≤ simpleDirectedPathLDPLength M s t at hm
    rw [he] at hm
    exact WithBot.not_coe_le_bot _ hm

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The finite increment exists exactly when both sources have directed walks. -/
private theorem incrementClose4_at_reachable (B : FramedBall) (ha : B.map.IsAcyclic)
    (k : ℤ) (d : B.D) :
    (finiteBallIncrementAt B k d).isSome ↔
      (∃ ds, incrementClose4_Walk B.map ds (finiteBallIncrementSource B k)
        (vertexClass _ d)) ∧
      (∃ ds, incrementClose4_Walk B.map ds (finiteBallIncrementSource B (k - 1))
        (vertexClass _ d)) := by
  rw [← incrementClose4_finite_reachable B.map ha,
    ← incrementClose4_finite_reachable B.map ha]
  unfold finiteBallIncrementAt
  cases simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B k)
      (vertexClass _ d) <;>
    cases simpleDirectedPathLDPLength B.map (finiteBallIncrementSource B (k - 1))
      (vertexClass _ d) <;> simp

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Retained ambient walks are exactly finite-ball walks, including empty walks. -/
private theorem incrementClose4_reachable_transport (M : RootedLocallyFinitePlanarMap)
    (r : ℕ) (hr : 0 < r) (d e : (rootedLocallyFiniteFramedBall M r hr).D) :
    (∃ ds, incrementClose4_Walk (rootedLocallyFiniteFramedBall M r hr).map ds
      (vertexClass _ d) (vertexClass _ e)) ↔
    ∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
      (rootedLocallyFiniteVertexClass M.rot d.1)
      (rootedLocallyFiniteVertexClass M.rot e.1) ∧
      ∀ x ∈ ds, x ∈ rootedLocallyFiniteBallDarts M.toRootedLocallyFiniteMap r := by
  constructor
  · rintro ⟨es, hw⟩
    refine ⟨es.map Subtype.val,
      (incrementClose4_Walk_transport M r hr es (vertexClass _ d) (vertexClass _ e)).1 hw,
      ?_⟩
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.2
  · rintro ⟨ds, hw, hd⟩
    obtain ⟨es, he⟩ := incrementClose4_List_lift M r hr ds hd
    refine ⟨es, (incrementClose4_Walk_transport M r hr es
      (vertexClass _ d) (vertexClass _ e)).2 ?_⟩
    change incrementDartWalk M.toRootedLocallyFiniteMap (es.map Subtype.val)
      (rootedLocallyFiniteVertexClass M.rot d.1)
      (rootedLocallyFiniteVertexClass M.rot e.1)
    rw [he]
    exact hw

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
A finite set of eventual radius assertions has one shared eventual radius. -/
private theorem incrementClose4_uniform_radius {α : Type*} (T : Finset α)
    (P : α → ℕ → Prop) (hP : ∀ t ∈ T, ∃ R : ℕ, ∀ r ≥ R, P t r) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ t ∈ T, P t r := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ ht => (Finset.notMem_empty _ ht).elim⟩
  | @insert t T _ ih =>
    obtain ⟨R0, hR0⟩ := hP t (Finset.mem_insert_self _ _)
    obtain ⟨R1, hR1⟩ := ih (fun u hu => hP u (Finset.mem_insert_of_mem hu))
    refine ⟨max R0 R1, fun r hr u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hR0 r ((le_max_left _ _).trans hr)
    · exact hR1 r ((le_max_right _ _).trans hr) u hu

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
One radius captures common reachability for every target in a finite vertex set. -/
private theorem incrementClose4_capture_common (M : RootedLocallyFiniteMap)
    (s0 s1 : RootedLocallyFiniteVertex M.D M.rot)
    (T : Finset (RootedLocallyFiniteVertex M.D M.rot)) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ t ∈ T,
      (∃ ds, incrementDartWalk M ds s0 t) →
      (∃ ds, incrementDartWalk M ds s1 t) →
      (∃ ds, incrementDartWalk M ds s0 t ∧
        ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M r) ∧
      (∃ ds, incrementDartWalk M ds s1 t ∧
        ∀ d ∈ ds, d ∈ rootedLocallyFiniteBallDarts M r) := by
  classical
  apply incrementClose4_uniform_radius T
  intro t _ht
  by_cases h0 : ∃ ds, incrementDartWalk M ds s0 t
  · by_cases h1 : ∃ ds, incrementDartWalk M ds s1 t
    · obtain ⟨ds, hd⟩ := h0
      obtain ⟨es, he⟩ := h1
      obtain ⟨R, _, hR⟩ := incrementDartList_captured M 0 (ds ++ es)
      refine ⟨R, fun r hr _ _ => ⟨⟨ds, hd, ?_⟩, ⟨es, he, ?_⟩⟩⟩
      · intro d hds
        exact rootedLocallyFiniteBallDarts_mono M hr
          (hR d (List.mem_append_left es hds))
      · intro e hes
        exact rootedLocallyFiniteBallDarts_mono M hr
          (hR e (List.mem_append_right ds hes))
    · exact ⟨0, fun _ _ _ h => (h1 h).elim⟩
  · exact ⟨0, fun _ _ h _ => (h0 h).elim⟩

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Concrete finite shell consensus equals restricted intrinsic shell consensus eventually. -/
private theorem incrementClose4_concrete_transport
    (M : RootedLocallyFinitePlanarMap) (k : ℤ) (m : ℕ) :
    ∃ R : ℕ, ∀ r ≥ R, ∀ hr : 0 < r, ∀ z : ℤ,
      FiniteBallIncrementConsensus (rootedLocallyFiniteFramedBall M r hr) k m z ↔
        IncrementClose3IntrinsicShellConsensus M.toRootedLocallyFiniteMap k m r z := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let T := rootedLocallyFiniteRadiusVertices A (m + 1)
  obtain ⟨S0, hS0⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M k
  obtain ⟨S1, hS1⟩ := finiteBallSdpBoundarySourceIdentificationAt_proved M (k - 1)
  obtain ⟨S2, hS2⟩ := incrementClose4_capture_common A
    (intrinsicIncrementSource A k) (intrinsicIncrementSource A (k - 1)) T
  obtain ⟨R, hlow, hcap⟩ := incrementDartList_captured A
    (max (max S0 S1) (max S2 (m + 1))) (T.toList.map Quotient.out)
  refine ⟨R, fun r hr hpos z => ?_⟩
  have hrlow : max (max S0 S1) (max S2 (m + 1)) ≤ r := hlow.trans hr
  have hs0 := hS0 r (by omega) hpos
  have hs1 := hS1 r (by omega) hpos
  let B := rootedLocallyFiniteFramedBall M r hpos
  have hat := incrementClose4_at_transport M r hpos k hs0 hs1
  have hreach (d : B.D) :
      (finiteBallIncrementAt B k d).isSome ↔
      (∃ ds, incrementDartWalk A ds (intrinsicIncrementSource A k)
        (rootedLocallyFiniteVertexClass M.rot d.1) ∧
        ∀ x ∈ ds, x ∈ rootedLocallyFiniteBallDarts A r) ∧
      (∃ ds, incrementDartWalk A ds (intrinsicIncrementSource A (k - 1))
        (rootedLocallyFiniteVertexClass M.rot d.1) ∧
        ∀ x ∈ ds, x ∈ rootedLocallyFiniteBallDarts A r) := by
    have h := incrementClose4_at_reachable B (incrementClose4_ball_acyclic M r hpos) k d
    dsimp only [finiteBallIncrementSource] at h
    rw [incrementClose4_reachable_transport M r hpos,
      incrementClose4_reachable_transport M r hpos] at h
    rw [hs0, hs1] at h
    exact h
  have hshell (d : B.D) :
      finiteBallIncrementShell B k m d ↔
        rootedLocallyFiniteWithinRadius A (m + 1)
          (rootedLocallyFiniteVertexClass M.rot d.1) ∧
        ¬ rootedLocallyFiniteWithinRadius A m
          (rootedLocallyFiniteVertexClass M.rot d.1) ∧
        (∃ ds, incrementDartWalk A ds (intrinsicIncrementSource A k)
          (rootedLocallyFiniteVertexClass M.rot d.1)) ∧
        (∃ ds, incrementDartWalk A ds (intrinsicIncrementSource A (k - 1))
          (rootedLocallyFiniteVertexClass M.rot d.1)) := by
    change (_ ∧ ¬ _ ∧ _) ↔ _
    rw [rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d,
      rootedLocallyFiniteFramedBall_withinRadius_iff M hpos (by omega) d]
    constructor
    · rintro ⟨hn, hf, hd⟩
      obtain ⟨⟨ds, hd, _⟩, ⟨es, he, _⟩⟩ := (hreach d).1 hd
      exact ⟨hn, hf, ⟨ds, hd⟩, ⟨es, he⟩⟩
    · rintro ⟨hn, hf, h0, h1⟩
      exact ⟨hn, hf, (hreach d).2 (hS2 r (by omega) _
        ((mem_rootedLocallyFiniteRadiusVertices A (m + 1) _).2 hn) h0 h1)⟩
  have hrep (t : RootedLocallyFiniteVertex M.D M.rot)
      (ht : rootedLocallyFiniteWithinRadius A (m + 1) t) :
      ∃ d : B.D, rootedLocallyFiniteVertexClass M.rot d.1 = t := by
    have htT : t ∈ T := (mem_rootedLocallyFiniteRadiusVertices A (m + 1) t).2 ht
    have hd := hcap (Quotient.out t)
      (List.mem_map.mpr ⟨t, Finset.mem_toList.mpr htT, rfl⟩)
    exact ⟨⟨Quotient.out t, rootedLocallyFiniteBallDarts_mono A hr hd⟩,
      Quotient.out_eq' t⟩
  constructor
  · intro h
    constructor
    · obtain ⟨d, hd⟩ := h.1
      exact ⟨rootedLocallyFiniteVertexClass M.rot d.1, (hshell d).1 hd⟩
    · intro t hn hf h0 h1
      obtain ⟨d, hd⟩ := hrep t hn
      have hds : finiteBallIncrementShell B k m d :=
        (hshell d).2 (hd.symm ▸ ⟨hn, hf, h0, h1⟩)
      have he := (hat d).symm.trans (h.2 d hds)
      simpa only [hd] using he
  · intro h
    constructor
    · obtain ⟨t, hn, hf, h0, h1⟩ := h.1
      obtain ⟨d, hd⟩ := hrep t hn
      exact ⟨d, (hshell d).2 (hd.symm ▸ ⟨hn, hf, h0, h1⟩)⟩
    · intro d hd
      obtain ⟨hn, hf, h0, h1⟩ := (hshell d).1 hd
      exact (hat d).trans (h.2 _ hn hf h0 h1)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Transport to a faced-class representative retains the radius shift and boundary sources. -/
theorem incrementClose4_facedShellTransport : IncrementClose3FacedShellTransport := by
  intro M k m
  obtain ⟨R, hR⟩ := incrementClose4_concrete_transport M k m
  refine ⟨R, fun r hr z => ?_⟩
  let q := rootedLocallyFiniteFacedBallClass r M
  obtain ⟨J⟩ : Nonempty (FacedFramedBallIso q.out
      (rootedLocallyFiniteFacedBall M (r + 1) (Nat.succ_pos r))) :=
    Quotient.exact q.out_eq
  have hc : FiniteBallIncrementConsensus q.out.toFramedBall k m z ↔
      FiniteBallIncrementConsensus (rootedLocallyFiniteFramedBall M (r + 1)
        (Nat.succ_pos r)) k m z :=
    ⟨incrementClose4_Consensus_iso J.toFramedBallIso k m z,
      incrementClose4_Consensus_iso J.toFramedBallIso.symm k m z⟩
  exact hc.trans (hR (r + 1) (by omega) (Nat.succ_pos r) z)

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Uniform finite faced-ball shell stabilization follows without a transport premise. -/
theorem uibhbotIncrementBallShellStabilization_proved :
    UIBHBOTIncrementBallShellStabilization :=
  uibhbotIncrementBallShellStabilization_of_facedShellTransport
    incrementClose4_facedShellTransport

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The existing faced-map law uses its Borel topology. -/
noncomputable local instance incrementClose4_Topology :
    TopologicalSpace RootedLocallyFinitePlanarMap :=
  bsLocalDistanceTopologyGeneric rootedLocallyFiniteFacedBallSystem

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The existing faced-map law uses the corresponding Borel measurable structure. -/
noncomputable local instance incrementClose4_Measurable :
    MeasurableSpace RootedLocallyFinitePlanarMap :=
  borel RootedLocallyFinitePlanarMap

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Intrinsic characterization and unbounded common reachable targets for the observable. -/
@[expose] def incrementClose4_ObservableData (M : RootedLocallyFinitePlanarMap) : Prop :=
  (∀ k : ℤ, ∃ N : ℕ, ∀ t : RootedLocallyFiniteVertex M.D M.rot,
    ¬ rootedLocallyFiniteWithinRadius M.toRootedLocallyFiniteMap N t →
    (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t) →
    (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
      (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t) →
    ∃ a b : ℕ,
      intrinsicIncrementLdp M.toRootedLocallyFiniteMap
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t = ((a : ℕ∞) : WithBot ℕ∞) ∧
      intrinsicIncrementLdp M.toRootedLocallyFiniteMap
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t = ((b : ℕ∞) : WithBot ℕ∞) ∧
      finiteBallIncrementObservable k M = (a : ℤ) - (b : ℤ)) ∧
  (∀ k : ℤ, ∀ T : Finset (RootedLocallyFiniteVertex M.D M.rot),
    ∃ t, t ∉ T ∧
      (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap k) t) ∧
      (∃ ds, incrementDartWalk M.toRootedLocallyFiniteMap ds
        (intrinsicIncrementSource M.toRootedLocallyFiniteMap (k - 1)) t))




@[expose] def LdpIntrinsicObservableDataMeasurable : Prop :=
  MeasurableSet {M : RootedLocallyFinitePlanarMap | incrementClose4_ObservableData M}

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
Conditional transport of the full characterization from code space to the faced-map law. -/
private theorem incrementClose4_ae_observableData
    (hmeas : LdpIntrinsicObservableDataMeasurable) :
    ∀ᵐ M ∂(uibhbotRootedPlanarMapLaw : Measure RootedLocallyFinitePlanarMap),
      incrementClose4_ObservableData M := by
  change ∀ᵐ M ∂((uibhbotCodeLawRel : Measure (ℤ → Fin 3)).map
    uibhbotRootedPlanarMapOfCode), incrementClose4_ObservableData M
  apply (ae_map_iff measurable_uibhbotRootedPlanarMapOfCode.aemeasurable hmeas).2
  have hreal := finiteBallIncrementObservable_realization_of_ballShellStabilization
    uibhbotIncrementBallShellStabilization_proved
  filter_upwards [ae_incrementClose3_intrinsic_uniform_consensus,
    ae_incrementClose3_intrinsic_shell_nonempty, hreal,
    uibhbotRootedPlanarMapConullEvent_spec.2.1] with W hc hn hv hgood
  obtain ⟨H, hhit, C, hcap, hM⟩ :=
    (uibhbotRootedPlanarMapOfCode_on_event W hgood).1
  let M := uibhbotRootedLocallyFinitePlanarMap W H hhit C hcap
  have hvM (k : ℤ) : finiteBallIncrementObservable k M =
      uibhbotBusemannIncrement k W :=
    (congrArg (finiteBallIncrementObservable k) hM).symm.trans (hv k)
  rw [hM]
  constructor
  · intro k
    obtain ⟨N, hN⟩ := hc H hhit C k
    refine ⟨N, fun t ht h0 h1 => ?_⟩
    obtain ⟨a, b, ha, hb, hi⟩ := hN t ht h0 h1
    exact ⟨a, b, ha, hb, (hvM k).trans hi⟩
  · intro k T
    obtain ⟨R, _, hR⟩ := incrementClose3_vertexFinset_captured M.toRootedLocallyFiniteMap T 0
    obtain ⟨N, hN⟩ := hn H hhit C k
    obtain ⟨t, _, ht, h0, h1⟩ := hN (max N R) (le_max_left _ _)
    refine ⟨t, fun hmem => ht ?_, h0, h1⟩
    exact (mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap _ t).1
      (rootedLocallyFiniteRadiusVertices_mono M.toRootedLocallyFiniteMap (le_max_right N R)
        ((mem_rootedLocallyFiniteRadiusVertices M.toRootedLocallyFiniteMap R t).2
          (hR t hmem)))

/-- Helper toward Theorem 1.7(iv) (item-busemann-sym) via Propositions 5.9 and 5.11;
The intrinsic characterization forces reflection with the ordered-root shift two. -/
private theorem incrementClose4_reflection_of_data (M : RootedLocallyFinitePlanarMap)
    (h : incrementClose4_ObservableData M)
    (hm : incrementClose4_ObservableData (mirrorRootedLocallyFinitePlanarMap M)) :
    finiteBallIncrementObservable 0 (mirrorRootedLocallyFinitePlanarMap M) =
      -finiteBallIncrementObservable 2 M := by
  classical
  let A := M.toRootedLocallyFiniteMap
  let B := mirrorRootedLocallyFiniteMap A
  let e := incrementMirrorVertexEquiv A
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
  have hm0 : ∃ ds, incrementDartWalk B ds (intrinsicIncrementSource B 0) (e t) := by
    obtain ⟨ds, hd⟩ := h1
    have hx := (incrementDartWalk_mirror A ds
      (intrinsicIncrementSource A (2 - 1)) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicIncrementSource_mirror, sub_zero,
      show (2 : ℤ) - 1 = 1 from rfl, e, B] using hx
  have hm1 : ∃ ds, incrementDartWalk B ds
      (intrinsicIncrementSource B (0 - 1)) (e t) := by
    obtain ⟨ds, hd⟩ := h0
    have hx := (incrementDartWalk_mirror A ds
      (intrinsicIncrementSource A 2) t).2 hd
    refine ⟨ds, ?_⟩
    simpa only [intrinsicIncrementSource_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl, e, B] using hx
  obtain ⟨c, d, hc, hd, hj⟩ := hR (e t) htR hm0 hm1
  change intrinsicIncrementLdp B (intrinsicIncrementSource B 0) (e t) =
    ((c : ℕ∞) : WithBot ℕ∞) at hc
  change intrinsicIncrementLdp B (intrinsicIncrementSource B (0 - 1)) (e t) =
    ((d : ℕ∞) : WithBot ℕ∞) at hd
  have hc' : intrinsicIncrementLdp A (intrinsicIncrementSource A (2 - 1)) t =
      ((c : ℕ∞) : WithBot ℕ∞) := by
    simpa only [B, e, intrinsicIncrementSource_mirror, intrinsicIncrementLdp_mirror,
      sub_zero, show (2 : ℤ) - 1 = 1 from rfl] using hc
  have hd' : intrinsicIncrementLdp A (intrinsicIncrementSource A 2) t =
      ((d : ℕ∞) : WithBot ℕ∞) := by
    simpa only [B, e, intrinsicIncrementSource_mirror, intrinsicIncrementLdp_mirror,
      show (1 : ℤ) - (0 - 1) = 2 from rfl] using hd
  have hcb : c = b := by exact_mod_cast hc'.symm.trans hb
  have hda : d = a := by exact_mod_cast hd'.symm.trans ha
  rw [hcb, hda] at hj
  omega




theorem uibhbotLdpIncrementObservableReflection_of_dataMeasurable
    (hmeas : LdpIntrinsicObservableDataMeasurable) :
    UIBHBOTIncrementObservableReflection finiteBallIncrementObservable := by
  have hdata := incrementClose4_ae_observableData hmeas
  have hmap : ∀ᵐ M ∂((uibhbotRootedPlanarMapLaw :
      Measure RootedLocallyFinitePlanarMap).map mirrorRootedLocallyFinitePlanarMap),
      incrementClose4_ObservableData M := by
    rw [uibhbotLaw_mirror_invariant
      DirectedDistances.PaperProofs.Section3.rootedPlanarMapLaw_hasOuterApproxClosed]
    exact hdata
  have : BorelSpace RootedLocallyFinitePlanarMap := ⟨rfl⟩
  have hm := ae_of_ae_map
    continuous_mirrorRootedLocallyFinitePlanarMap.measurable.aemeasurable hmap
  filter_upwards [hdata, hm] with M hM hmirror
  exact incrementClose4_reflection_of_data M hM hmirror



theorem hsym_ldp_unconditional (hmeas : LdpIntrinsicObservableDataMeasurable) :
    iidCodeMeasure.map (ldpIncrement busemannLDPMeasurableVersion 0) =
      iidCodeMeasure.map (fun ω => -ldpIncrement busemannLDPMeasurableVersion 0 ω) := by
  exact hsym_ldp_proved uibhbotIncrementBallShellStabilization_proved
    (uibhbotLdpIncrementObservableReflection_of_dataMeasurable hmeas)

end DirectedDistances.PaperProofs.Section5
