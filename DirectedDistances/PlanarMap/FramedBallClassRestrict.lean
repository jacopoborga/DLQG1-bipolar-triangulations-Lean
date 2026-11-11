module

public import DirectedDistances.PaperProofs.Section5.DiskBSBallRestriction
public import DirectedDistances.PlanarMap.PlanarFaceCycleSpace

public section
namespace DirectedDistances.PlanarMap

open CombinatorialMap

/-- One all-geometric edge joins these two vertex orbits. Helper toward
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def framedBallGeometricStep (B : FramedBall)
    (v w : VertexQuotient B.map.toCombinatorialMap) : Prop :=
  ∃ d, vertexClass B.map.toCombinatorialMap d = v ∧
    vertexClass B.map.toCombinatorialMap (B.map.edgeInv d) = w

/-- A path using exactly `n` all-geometric edges. Helper toward Proposition
5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
inductive framedBallGeometricPath (B : FramedBall) :
    VertexQuotient B.map.toCombinatorialMap → ℕ →
      VertexQuotient B.map.toCombinatorialMap → Prop
  | /-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling);
    not a paper result. -/
    nil (v) : framedBallGeometricPath B v 0 v
  | /-- Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling);
    not a paper result. -/
    snoc {v w z n} : framedBallGeometricPath B v n w →
      framedBallGeometricStep B w z → framedBallGeometricPath B v (n + 1) z

/-- Reachability by an all-geometric path of length at most `r`. Helper toward
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def framedBallWithinRadius (B : FramedBall) (r : ℕ)
    (v w : VertexQuotient B.map.toCombinatorialMap) : Prop :=
  ∃ n, n ≤ r ∧ framedBallGeometricPath B v n w

/-- The radius-`r` darts have both endpoints within all-geometric distance
at most `r` of the root's first endpoint. Helper toward Proposition 5.16
(prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] noncomputable def framedBallRadiusDarts (B : FramedBall) (r : ℕ) :
    Finset B.D := by
  classical
  exact Finset.univ.filter fun d =>
    framedBallWithinRadius B r (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap d) ∧
    framedBallWithinRadius B r (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap (B.map.edgeInv d))

/-- Membership in the radius set is exactly the two endpoint distance bounds.
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem framedBallRadiusDarts_mem_iff (B : FramedBall) (r : ℕ) (d : B.D) :
    d ∈ framedBallRadiusDarts B r ↔
      framedBallWithinRadius B r (vertexClass B.map.toCombinatorialMap B.rootDart)
        (vertexClass B.map.toCombinatorialMap d) ∧
      framedBallWithinRadius B r (vertexClass B.map.toCombinatorialMap B.rootDart)
        (vertexClass B.map.toCombinatorialMap (B.map.edgeInv d)) := by
  classical
  simp [framedBallRadiusDarts]

/-- The radius dart set is closed under the geometric edge flip. Helper toward
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem framedBallRadiusDarts_edgeInv_mem (B : FramedBall) (r : ℕ) {d : B.D}
    (hd : d ∈ framedBallRadiusDarts B r) :
    B.map.edgeInv d ∈ framedBallRadiusDarts B r := by
  rw [framedBallRadiusDarts_mem_iff] at hd ⊢
  exact ⟨hd.2, by simpa only [B.map.edgeInv_invol] using hd.1⟩

/-- At positive radius both root incidences are retained. Helper toward
Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem framedBallRadiusDarts_frameEdge_mem (B : FramedBall) (r : ℕ)
    (hr : 0 < r) :
    B.frameEdgeDart ∈ framedBallRadiusDarts B r ∧
      B.map.edgeInv B.frameEdgeDart ∈ framedBallRadiusDarts B r := by
  have hcenter :
      vertexClass B.map.toCombinatorialMap B.rootDart =
        vertexClass B.map.toCombinatorialMap B.frameEdgeDart :=
    Quotient.sound B.frameEdge_at_root
  have hroot : framedBallWithinRadius B r
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap B.frameEdgeDart) := by
    rw [← hcenter]
    exact ⟨0, Nat.zero_le _, .nil _⟩
  have hother : framedBallWithinRadius B r
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap (B.map.edgeInv B.frameEdgeDart)) := by
    refine ⟨1, hr, .snoc (.nil _) ?_⟩
    exact ⟨B.frameEdgeDart, hcenter.symm, rfl⟩
  have hfirst := (framedBallRadiusDarts_mem_iff B r B.frameEdgeDart).2
    ⟨hroot, hother⟩
  exact ⟨hfirst, framedBallRadiusDarts_edgeInv_mem B r hfirst⟩

private def framedBallCombinatorialStep {D : Type} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (x y : D) : Prop :=
  y = M.rot x ∨ y = M.rot.symm x ∨
    y = M.edgeInv x ∨ y = M.edgeInv.symm x

private theorem framedBallSameCycle_reachable {D : Type} [Fintype D]
    [DecidableEq D] (M : CombinatorialMap D) {x y : D}
    (h : M.rot.SameCycle x y) :
    Relation.ReflTransGen (framedBallCombinatorialStep M) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ n, Relation.ReflTransGen (framedBallCombinatorialStep M)
      x ((M.rot ^ n) x) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.tail (Or.inl rfl)
  rw [← hn]
  exact hpow n

private theorem framedBallRadiusRoot_mem (B : FramedBall) (r : ℕ)
    (hr : 0 < r) : B.rootDart ∈ framedBallRadiusDarts B r := by
  have hroot : framedBallWithinRadius B r
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap B.rootDart) :=
    ⟨0, Nat.zero_le _, .nil _⟩
  have hother : framedBallWithinRadius B r
      (vertexClass B.map.toCombinatorialMap B.rootDart)
      (vertexClass B.map.toCombinatorialMap (B.map.edgeInv B.rootDart)) := by
    refine ⟨1, hr, .snoc (.nil _) ?_⟩
    exact ⟨B.rootDart, rfl, rfl⟩
  exact (framedBallRadiusDarts_mem_iff B r B.rootDart).2
    ⟨hroot, hother⟩

private theorem framedBallRadiusPath_reaches (B : FramedBall) (r : ℕ)
    (hr : 0 < r) {v : VertexQuotient B.map.toCombinatorialMap} {n : ℕ}
    (hp : framedBallGeometricPath B
      (vertexClass B.map.toCombinatorialMap B.rootDart) n v)
    (hn : n ≤ r) (d : B.D) (hd : d ∈ framedBallRadiusDarts B r)
    (hvertex : vertexClass B.map.toCombinatorialMap d = v) :
    Relation.ReflTransGen
      (framedBallCombinatorialStep
        (inducedCombinatorialMap B.map.toCombinatorialMap
          (framedBallRadiusDarts B r)
          (fun _d hd => framedBallRadiusDarts_edgeInv_mem B r hd)))
      ⟨B.rootDart, framedBallRadiusRoot_mem B r hr⟩ ⟨d, hd⟩ := by
  classical
  let S := framedBallRadiusDarts B r
  let hflip : ∀ d, d ∈ S → B.map.edgeInv d ∈ S :=
    fun d hd => framedBallRadiusDarts_edgeInv_mem B r hd
  let N := inducedCombinatorialMap B.map.toCombinatorialMap S hflip
  have hroot : B.rootDart ∈ S := framedBallRadiusRoot_mem B r hr
  revert hn d hd hvertex
  induction hp with
  | nil =>
      intro hn d hd hvertex
      have hcycle : B.map.rot.SameCycle B.rootDart d :=
        (Quotient.exact hvertex).symm
      have hcycleN : N.rot.SameCycle
          (⟨B.rootDart, hroot⟩ : {d : B.D // d ∈ S})
          ⟨d, hd⟩ :=
        (inducedCombinatorialMap_rot_sameCycle_iff
          B.map.toCombinatorialMap S hflip _ _).2 hcycle
      exact framedBallSameCycle_reachable N hcycleN
  | @snoc w z n hp hstep ih =>
      intro hn d hd hvertex
      rcases hstep with ⟨e, hev, hew⟩
      have hn' : n ≤ r := Nat.le_trans (Nat.le_succ n) hn
      have hw : framedBallWithinRadius B r
          (vertexClass B.map.toCombinatorialMap B.rootDart) w :=
        ⟨n, hn', hp⟩
      have hz : framedBallWithinRadius B r
          (vertexClass B.map.toCombinatorialMap B.rootDart) z :=
        ⟨n + 1, hn, .snoc hp ⟨e, hev, hew⟩⟩
      have heS : e ∈ S := by
        apply (framedBallRadiusDarts_mem_iff B r e).2
        exact ⟨by simpa [hev] using hw, by simpa [hew] using hz⟩
      have hreach := ih hn' e heS hev
      have hedge : N.edgeInv (⟨e, heS⟩ : {d : B.D // d ∈ S}) =
          ⟨B.map.edgeInv e, hflip e heS⟩ := by
        apply Subtype.ext
        rfl
      have hflipstep : Relation.ReflTransGen
          (framedBallCombinatorialStep N) (⟨e, heS⟩ : {d : B.D // d ∈ S})
          ⟨B.map.edgeInv e, hflip e heS⟩ :=
        Relation.ReflTransGen.single (Or.inr (Or.inr (Or.inl hedge)))
      have hcycle : B.map.rot.SameCycle (B.map.edgeInv e) d :=
        Quotient.exact (hew.trans hvertex.symm)
      have hcycleN : N.rot.SameCycle
          ⟨B.map.edgeInv e, hflip e heS⟩ ⟨d, hd⟩ :=
        (inducedCombinatorialMap_rot_sameCycle_iff
          B.map.toCombinatorialMap S hflip _ _).2 hcycle
      exact hreach.trans (hflipstep.trans
        (framedBallSameCycle_reachable N hcycleN))

/-- The induced radius ball is combinatorially connected at positive radius.
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper -/
theorem framedBallRadiusDarts_connected (B : FramedBall) (r : ℕ)
    (hr : 0 < r) :
    (inducedCombinatorialMap B.map.toCombinatorialMap
      (framedBallRadiusDarts B r)
        (fun _d hd => framedBallRadiusDarts_edgeInv_mem B r hd)).IsConnected := by
  classical
  let S := framedBallRadiusDarts B r
  let hflip : ∀ d, d ∈ S → B.map.edgeInv d ∈ S :=
    fun d hd => framedBallRadiusDarts_edgeInv_mem B r hd
  let N := inducedCombinatorialMap B.map.toCombinatorialMap S hflip
  have hsymmetric : Std.Symm (framedBallCombinatorialStep N) := ⟨by
    intro x y hxy
    rcases hxy with hxy | hxy | hxy | hxy
    · right; left; simp [hxy]
    · left; simp [hxy]
    · right; right; right; simp [hxy]
    · right; right; left; simp [hxy]⟩
  intro x y
  have hxmem := (framedBallRadiusDarts_mem_iff B r x.1).1 x.2
  have hymem := (framedBallRadiusDarts_mem_iff B r y.1).1 y.2
  rcases hxmem.1 with ⟨nx, hnx, hpx⟩
  rcases hymem.1 with ⟨ny, hny, hpy⟩
  have hreachx := framedBallRadiusPath_reaches B r hr hpx hnx x.1 x.2 rfl
  have hreachy := framedBallRadiusPath_reaches B r hr hpy hny y.1 y.2 rfl
  have hreverseSymm : Std.Symm
      (Relation.ReflTransGen (framedBallCombinatorialStep N)) :=
    @Relation.ReflTransGen.stdSymm _ _ hsymmetric
  exact (hreverseSymm.symm
    (⟨B.rootDart, framedBallRadiusRoot_mem B r hr⟩ : {d : B.D // d ∈ S}) x
    hreachx).trans hreachy

/-- Restrict a planar connected framed ball to its positive radius darts.
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper -/
@[expose] noncomputable def planarFramedBallRestrictRadius
    (B : DirectedDistances.PaperProofs.Section5.PlanarConnectedFramedBall)
    (r' : ℕ) (hr' : 0 < r') :
    DirectedDistances.PaperProofs.Section5.PlanarConnectedFramedBall := by
  classical
  unfold DirectedDistances.PaperProofs.Section5.PlanarConnectedFramedBall at B
  let S : Finset B.1.D := framedBallRadiusDarts B.1 r'
  let hflip : ∀ d, d ∈ S → B.1.map.edgeInv d ∈ S :=
    fun d hd => framedBallRadiusDarts_edgeInv_mem B.1 r' hd
  let hconn := framedBallRadiusDarts_connected B.1 r' hr'
  let hframe := framedBallRadiusDarts_frameEdge_mem B.1 r' hr'
  let root : {d : B.1.D // d ∈ S} := ⟨
    B.1.map.edgeInv B.1.frameEdgeDart, hframe.2⟩
  let outerD := if h : CombinatorialMap.IsOuter B.1.map.toCombinatorialMap
      B.1.map.outer B.1.frameEdgeDart then B.1.frameEdgeDart
    else B.1.map.edgeInv B.1.frameEdgeDart
  have houterD : CombinatorialMap.IsOuter B.1.map.toCombinatorialMap
      B.1.map.outer outerD := by
    by_cases h : CombinatorialMap.IsOuter B.1.map.toCombinatorialMap
        B.1.map.outer B.1.frameEdgeDart
    · simp [outerD, h]
    · simp only [outerD, dite_eq_right h]
      rcases B.1.map.missing_outer B.1.frameEdgeDart
          B.1.frameEdge_missing with hframe | hframe
      · exact (h hframe).elim
      · exact hframe
  have houterMem : outerD ∈ S := by
    by_cases h : CombinatorialMap.IsOuter B.1.map.toCombinatorialMap
        B.1.map.outer B.1.frameEdgeDart
    · simpa [outerD, h] using hframe.1
    · simpa [outerD, h] using hframe.2
  let outer : {d : B.1.D // d ∈ S} := ⟨outerD, houterMem⟩
  let houter := fun d (hd : d ∈ S)
      (ho : CombinatorialMap.IsOuter B.1.map.toCombinatorialMap
        B.1.map.outer d) =>
    have hocycle : B.1.map.toCombinatorialMap.faceSucc.SameCycle outerD d :=
      houterD.symm.trans ho
    inducedCombinatorialMap_face_sameCycle_of_connected_planar
      B.1.map.toCombinatorialMap B.2.1 S hflip hconn outer ⟨d, hd⟩ hocycle
  exact DirectedDistances.PaperProofs.Section5.framedBallRestrict
    B S hflip outer houter root
    ((B.1.map.missing_edgeInv B.1.frameEdgeDart).mp B.1.frameEdge_missing)
    hconn

/-- The quotient map on vertices induced by a framed-ball isomorphism. Helper
toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
@[expose] def framedBallVertexMap {B B' : FramedBall} (I : FramedBallIso B B')
    (v : VertexQuotient B.map.toCombinatorialMap) :
    VertexQuotient B'.map.toCombinatorialMap :=
  Quotient.map I.mapIso.toEquiv (fun _d _e h =>
    FramedBallIso.vertexRel_map I.mapIso h) v

private theorem framedBallVertexMap_apply_dart {B B' : FramedBall}
    (I : FramedBallIso B B') (d : B.D) :
    framedBallVertexMap I (vertexClass B.map.toCombinatorialMap d) =
      vertexClass B'.map.toCombinatorialMap (I.mapIso.toEquiv d) := rfl

private theorem framedBallVertexMap_symm_apply {B B' : FramedBall}
    (I : FramedBallIso B B') (v : VertexQuotient B.map.toCombinatorialMap) :
    framedBallVertexMap (FramedBallIso.symm I)
        (framedBallVertexMap I v) = v := by
  refine Quotient.inductionOn v ?_
  intro d
  simp [framedBallVertexMap, FramedBallIso.symm,
    DirectedMapWithMissingIso.symm]

private theorem framedBallGeometricStep_map {B B' : FramedBall}
    (I : FramedBallIso B B') {v w : VertexQuotient B.map.toCombinatorialMap}
    (h : framedBallGeometricStep B v w) :
    framedBallGeometricStep B' (framedBallVertexMap I v)
      (framedBallVertexMap I w) := by
  rcases h with ⟨d, hdv, hdw⟩
  refine ⟨I.mapIso.toEquiv d, ?_, ?_⟩
  · calc
      vertexClass B'.map.toCombinatorialMap (I.mapIso.toEquiv d) =
          framedBallVertexMap I (vertexClass B.map.toCombinatorialMap d) :=
        (framedBallVertexMap_apply_dart I d).symm
      _ = framedBallVertexMap I v := congrArg (framedBallVertexMap I) hdv
  · calc
      vertexClass B'.map.toCombinatorialMap (B'.map.edgeInv (I.mapIso.toEquiv d)) =
          vertexClass B'.map.toCombinatorialMap
            (I.mapIso.toEquiv (B.map.edgeInv d)) := by
              rw [← I.mapIso.edgeInv_comm]
      _ = framedBallVertexMap I
          (vertexClass B.map.toCombinatorialMap (B.map.edgeInv d)) :=
        (framedBallVertexMap_apply_dart I (B.map.edgeInv d)).symm
      _ = framedBallVertexMap I w := congrArg (framedBallVertexMap I) hdw

private theorem framedBallGeometricPath_map {B B' : FramedBall}
    (I : FramedBallIso B B') {v w : VertexQuotient B.map.toCombinatorialMap}
    {n : ℕ} (h : framedBallGeometricPath B v n w) :
    framedBallGeometricPath B' (framedBallVertexMap I v) n
      (framedBallVertexMap I w) := by
  induction h with
  | nil => exact .nil _
  | snoc hpath hstep ih =>
      exact .snoc ih (framedBallGeometricStep_map I hstep)

private theorem framedBallWithinRadius_map {B B' : FramedBall}
    (I : FramedBallIso B B') (r : ℕ)
    {v w : VertexQuotient B.map.toCombinatorialMap}
    (h : framedBallWithinRadius B r v w) :
    framedBallWithinRadius B' r (framedBallVertexMap I v)
      (framedBallVertexMap I w) := by
  rcases h with ⟨n, hn, hp⟩
  exact ⟨n, hn, framedBallGeometricPath_map I hp⟩

private theorem framedBallVertexMap_root {B B' : FramedBall}
    (I : FramedBallIso B B') :
    framedBallVertexMap I (vertexClass B.map.toCombinatorialMap B.rootDart) =
      vertexClass B'.map.toCombinatorialMap B'.rootDart := by
  rw [framedBallVertexMap_apply_dart]
  exact Quotient.sound I.root_vertex

/-- The all-geometric vertex radius is preserved by framed-ball isomorphisms.
Helper toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem framedBallWithinRadius_iso_iff {B B' : FramedBall}
    (I : FramedBallIso B B') (r : ℕ)
    (v w : VertexQuotient B.map.toCombinatorialMap) :
    framedBallWithinRadius B r v w ↔
      framedBallWithinRadius B' r (framedBallVertexMap I v)
        (framedBallVertexMap I w) := by
  constructor
  · exact framedBallWithinRadius_map I r
  · intro h
    have h' := framedBallWithinRadius_map (FramedBallIso.symm I) r h
    simpa only [framedBallVertexMap_symm_apply] using h'

/-- Framed-ball isomorphisms transport the radius dart set exactly. Helper
toward Proposition 5.16 (prop-disk-bs-conv; local topology ruling); not a paper result. -/
theorem framedBallRadiusDarts_mem_iso_iff {B B' : FramedBall}
    (I : FramedBallIso B B') (r : ℕ) (d : B.D) :
    I.mapIso.toEquiv d ∈ framedBallRadiusDarts B' r ↔
      d ∈ framedBallRadiusDarts B r := by
  rw [framedBallRadiusDarts_mem_iff, framedBallRadiusDarts_mem_iff]
  have hfirst := framedBallWithinRadius_iso_iff I r
    (vertexClass B.map.toCombinatorialMap B.rootDart)
    (vertexClass B.map.toCombinatorialMap d)
  have hsecond := framedBallWithinRadius_iso_iff I r
    (vertexClass B.map.toCombinatorialMap B.rootDart)
    (vertexClass B.map.toCombinatorialMap (B.map.edgeInv d))
  rw [framedBallVertexMap_root, framedBallVertexMap_apply_dart] at hfirst hsecond
  rw [I.mapIso.edgeInv_comm] at hsecond
  exact and_congr hfirst.symm hsecond.symm

end DirectedDistances.PlanarMap
end
