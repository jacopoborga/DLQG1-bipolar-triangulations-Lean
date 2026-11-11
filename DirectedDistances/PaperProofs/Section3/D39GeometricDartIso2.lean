/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDartIso

/-! # Further geometric dart isomorphism properties -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open Set
open DirectedDistances.PlanarMap
open scoped ENNReal Topology

universe uV uE uV' uE' uV'' uE''

namespace D39GeomBallIsoV2

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {r s : ℕ} {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: transport a geometric adjacency through a dart ball isomorphism. -/
private theorem adj_map (e : D39GeomBallIsoV2 r M rho M' rho')
    {v w : V} (hv : v ∈ d39GeomBallVertices M rho r)
    (hw : w ∈ d39GeomBallVertices M rho r)
    (hadj : (d39GeomGraph M).Adj v w) :
    (d39GeomGraph M').Adj (e.vertexEquiv ⟨v, hv⟩).1
      (e.vertexEquiv ⟨w, hw⟩).1 := by
  rcases hadj with ⟨hne, a, ha | ha⟩
  · let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a, by rw [ha.1]; exact hv⟩
    let y : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a, by rw [ha.2]; exact hw⟩
    let a0 : {e // e ∈ d39GeomBallEdges M rho r} := ⟨a, ⟨x.2, y.2⟩⟩
    have hx : (e.vertexEquiv x).1 = (e.vertexEquiv ⟨v, hv⟩).1 := by
      have h : x = ⟨v, hv⟩ := Subtype.ext ha.1
      exact congrArg (fun z => (e.vertexEquiv z).1) h
    have hy : (e.vertexEquiv y).1 = (e.vertexEquiv ⟨w, hw⟩).1 := by
      have h : y = ⟨w, hw⟩ := Subtype.ext ha.2
      exact congrArg (fun z => (e.vertexEquiv z).1) h
    have hs := e.src_map a0
    have ht := e.tgt_map a0
    have hne' : (e.vertexEquiv ⟨v, hv⟩).1 ≠ (e.vertexEquiv ⟨w, hw⟩).1 := by
      intro h
      apply hne
      exact congrArg Subtype.val (e.vertexEquiv.injective (Subtype.ext h))
    cases hf : e.edgeFlip a0
    · refine ⟨hne', (e.edgeEquiv a0).1, Or.inl ?_⟩
      constructor
      · simpa [a0, x, hx, hf] using hs.symm
      · simpa [a0, y, hy, hf] using ht.symm
    · refine ⟨hne', (e.edgeEquiv a0).1, Or.inr ?_⟩
      constructor
      · simpa [a0, y, hy, hf] using ht.symm
      · simpa [a0, x, hx, hf] using hs.symm

  · let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a, by rw [ha.1]; exact hw⟩
    let y : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a, by rw [ha.2]; exact hv⟩
    let a0 : {e // e ∈ d39GeomBallEdges M rho r} := ⟨a, ⟨x.2, y.2⟩⟩
    have hx : (e.vertexEquiv x).1 = (e.vertexEquiv ⟨w, hw⟩).1 := by
      have h : x = ⟨w, hw⟩ := Subtype.ext ha.1
      exact congrArg (fun z => (e.vertexEquiv z).1) h
    have hy : (e.vertexEquiv y).1 = (e.vertexEquiv ⟨v, hv⟩).1 := by
      have h : y = ⟨v, hv⟩ := Subtype.ext ha.2
      exact congrArg (fun z => (e.vertexEquiv z).1) h
    have hs := e.src_map a0
    have ht := e.tgt_map a0
    have hne' : (e.vertexEquiv ⟨v, hv⟩).1 ≠ (e.vertexEquiv ⟨w, hw⟩).1 := by
      intro h
      apply hne
      exact (congrArg Subtype.val (e.vertexEquiv.injective (Subtype.ext h.symm))).symm
    cases hf : e.edgeFlip a0
    · refine ⟨hne', (e.edgeEquiv a0).1, Or.inr ?_⟩
      constructor
      · simpa [a0, x, hx, hf] using hs.symm
      · simpa [a0, y, hy, hf] using ht.symm
    · refine ⟨hne', (e.edgeEquiv a0).1, Or.inl ?_⟩
      constructor
      · simpa [a0, y, hy, hf] using ht.symm
      · simpa [a0, x, hx, hf] using hs.symm

/-- Helper toward Definition 3.8: reflect adjacency through a dart ball isomorphism. -/
private theorem adj_map_symm (e : D39GeomBallIsoV2 r M rho M' rho')
    {v' w' : V'} (hv' : v' ∈ d39GeomBallVertices M' rho' r)
    (hw' : w' ∈ d39GeomBallVertices M' rho' r)
    (hadj : (d39GeomGraph M').Adj v' w') :
    (d39GeomGraph M).Adj (e.vertexEquiv.symm ⟨v', hv'⟩).1
      (e.vertexEquiv.symm ⟨w', hw'⟩).1 := by
  rcases hadj with ⟨hne, b, hb | hb⟩
  · let y : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src b, by rw [hb.1]; exact hv'⟩
    let z : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt b, by rw [hb.2]; exact hw'⟩
    let b0 : {e // e ∈ d39GeomBallEdges M' rho' r} := ⟨b, ⟨y.2, z.2⟩⟩
    let a0 := e.edgeEquiv.symm b0
    have hab : e.edgeEquiv a0 = b0 := Equiv.apply_symm_apply _ _
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a0.1, a0.2.1⟩
    let t : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a0.1, a0.2.2⟩
    have hs : (e.vertexEquiv x).1 =
        if e.edgeFlip a0 then M'.tgt b else M'.src b := by
      simpa [x, a0, b0, hab]
        using e.src_map a0
    have ht : (e.vertexEquiv t).1 =
        if e.edgeFlip a0 then M'.src b else M'.tgt b := by
      simpa [t, a0, b0, hab]
        using e.tgt_map a0
    have hne' : (e.vertexEquiv.symm ⟨v', hv'⟩).1 ≠
        (e.vertexEquiv.symm ⟨w', hw'⟩).1 := by
      intro h
      apply hne
      simpa using congrArg Subtype.val
        (congrArg e.vertexEquiv (Subtype.ext h))
    cases hf : e.edgeFlip a0
    · have hix : (e.vertexEquiv.symm ⟨v', hv'⟩).1 = x.1 := by
        have heq : e.vertexEquiv x = ⟨v', hv'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.1] using hs
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      have hit : (e.vertexEquiv.symm ⟨w', hw'⟩).1 = t.1 := by
        have heq : e.vertexEquiv t = ⟨w', hw'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.2] using ht
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      refine ⟨hne', a0.1, Or.inl ?_⟩
      exact ⟨by simpa [x] using hix.symm, by simpa [t] using hit.symm⟩
    · have hit : (e.vertexEquiv.symm ⟨v', hv'⟩).1 = t.1 := by
        have heq : e.vertexEquiv t = ⟨v', hv'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.1] using ht
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      have hix : (e.vertexEquiv.symm ⟨w', hw'⟩).1 = x.1 := by
        have heq : e.vertexEquiv x = ⟨w', hw'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.2] using hs
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      refine ⟨hne', a0.1, Or.inr ?_⟩
      exact ⟨by simpa [x] using hix.symm, by simpa [t] using hit.symm⟩
  · let y : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.src b, by rw [hb.1]; exact hw'⟩
    let z : {v // v ∈ d39GeomBallVertices M' rho' r} :=
      ⟨M'.toPlaneMapWithMissing.tgt b, by rw [hb.2]; exact hv'⟩
    let b0 : {e // e ∈ d39GeomBallEdges M' rho' r} := ⟨b, ⟨y.2, z.2⟩⟩
    let a0 := e.edgeEquiv.symm b0
    have hab : e.edgeEquiv a0 = b0 := Equiv.apply_symm_apply _ _
    let x : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.src a0.1, a0.2.1⟩
    let t : {v // v ∈ d39GeomBallVertices M rho r} :=
      ⟨M.toPlaneMapWithMissing.tgt a0.1, a0.2.2⟩
    have hs : (e.vertexEquiv x).1 =
        if e.edgeFlip a0 then M'.tgt b else M'.src b := by
      simpa [x, a0, b0, hab] using e.src_map a0
    have ht : (e.vertexEquiv t).1 =
        if e.edgeFlip a0 then M'.src b else M'.tgt b := by
      simpa [t, a0, b0, hab] using e.tgt_map a0
    have hne' : (e.vertexEquiv.symm ⟨v', hv'⟩).1 ≠
        (e.vertexEquiv.symm ⟨w', hw'⟩).1 := by
      intro h
      apply hne
      simpa using congrArg Subtype.val
        (congrArg e.vertexEquiv (Subtype.ext h))
    cases hf : e.edgeFlip a0
    · have hix : (e.vertexEquiv.symm ⟨w', hw'⟩).1 = x.1 := by
        have heq : e.vertexEquiv x = ⟨w', hw'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.1] using hs
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      have hit : (e.vertexEquiv.symm ⟨v', hv'⟩).1 = t.1 := by
        have heq : e.vertexEquiv t = ⟨v', hv'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.2] using ht
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      refine ⟨hne', a0.1, Or.inr ?_⟩
      exact ⟨by simpa [x] using hix.symm, by simpa [t] using hit.symm⟩
    · have hit : (e.vertexEquiv.symm ⟨w', hw'⟩).1 = t.1 := by
        have heq : e.vertexEquiv t = ⟨w', hw'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.1] using ht
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      have hix : (e.vertexEquiv.symm ⟨v', hv'⟩).1 = x.1 := by
        have heq : e.vertexEquiv x = ⟨v', hv'⟩ := by
          apply Subtype.ext
          simpa [hf, hb.2] using hs
        have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
        simpa using h.symm
      refine ⟨hne', a0.1, Or.inl ?_⟩
      exact ⟨by simpa [x] using hix.symm, by simpa [t] using hit.symm⟩

/-- Helper toward Definition 3.8: map a walk whose vertices lie in the ball. -/
private theorem mapWalk (e : D39GeomBallIsoV2 r M rho M' rho') {v w : V}
    (p : (d39GeomGraph M).Walk v w)
    (hpath : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M rho r) :
    ∃ q : (d39GeomGraph M').Walk
      (e.vertexEquiv ⟨v, by simpa using hpath 0 (Nat.zero_le _)⟩).1
      (e.vertexEquiv ⟨w, by simpa using hpath p.length le_rfl⟩).1,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @cons v x w hadj p ih =>
    have hx : x ∈ d39GeomBallVertices M rho r := by
      simpa using hpath 1 (by simp)
    have htail : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M rho r := by
      intro i hi
      have hi' : i + 1 ≤ (SimpleGraph.Walk.cons hadj p).length := by
        simpa using Nat.succ_le_succ hi
      simpa using hpath (i + 1) hi'
    obtain ⟨q, hq⟩ := ih htail
    have ha := adj_map e (by simpa using hpath 0 (Nat.zero_le _)) hx hadj
    exact ⟨SimpleGraph.Walk.cons ha q, by simp [hq]⟩

/-- Helper toward Definition 3.8: one-sided distance bound from a dart ball isomorphism. -/
private theorem distance_le (e : D39GeomBallIsoV2 r M rho M' rho')
    (v : V) (hv : v ∈ d39GeomBallVertices M rho r) :
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho')
        (e.vertexEquiv ⟨v, hv⟩).1 ≤
      d39GeomGraphDistance M (d39GeomRootVertex M rho) v := by
  let G := d39GeomGraph M
  let G' := d39GeomGraph M'
  let root := d39GeomRootVertex M rho
  have hfinite : G.edist root v ≠ ⊤ := by
    intro htop
    have hv' := hv
    simp [d39GeomBallVertices, d39GeomGraphDistance, G, root, htop] at hv'
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ r := by
    have : (p.length : ℕ∞) ≤ (r : ℕ∞) := by rw [hp]; exact hv
    exact_mod_cast this
  have hpath : ∀ i, i ≤ p.length →
      p.getVert i ∈ d39GeomBallVertices M rho r := by
    intro i hi
    have hdist := SimpleGraph.edist_le (p.take i)
    have hle : (p.take i).length ≤ r := by
      rw [SimpleGraph.Walk.take_length]
      omega
    change G.edist root (p.getVert i) ≤ (r : ℕ∞)
    exact le_trans hdist (by exact_mod_cast hle)
  obtain ⟨q, hq⟩ := mapWalk e p hpath
  have hstart : (e.vertexEquiv ⟨root, by simpa [root] using hpath 0 (Nat.zero_le _)⟩).1 =
      d39GeomRootVertex M' rho' := by
    simpa [root] using e.root_initial_map
  have hend : (e.vertexEquiv ⟨v, by simpa using hpath p.length le_rfl⟩).1 =
      (e.vertexEquiv ⟨v, hv⟩).1 := by congr 1
  change G'.edist _ _ ≤ _
  calc
    G'.edist (d39GeomRootVertex M' rho') (e.vertexEquiv ⟨v, hv⟩).1 ≤
        (q.copy hstart hend).length := SimpleGraph.edist_le _
    _ = p.length := by rw [SimpleGraph.Walk.length_copy, hq]
    _ = G.edist root v := hp


/-- Helper toward Definition 3.8: map walks back through the inverse vertex equivalence. -/
private theorem mapWalk_symm (e : D39GeomBallIsoV2 r M rho M' rho')
    {v' w' : V'} (p : (d39GeomGraph M').Walk v' w')
    (hpath : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M' rho' r) :
    ∃ q : (d39GeomGraph M).Walk
      (e.vertexEquiv.symm ⟨v', by simpa using hpath 0 (Nat.zero_le _)⟩).1
      (e.vertexEquiv.symm ⟨w', by simpa using hpath p.length le_rfl⟩).1,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @cons v x w hadj p ih =>
    have hx : x ∈ d39GeomBallVertices M' rho' r := by
      simpa using hpath 1 (by simp)
    have htail : ∀ i, i ≤ p.length → p.getVert i ∈ d39GeomBallVertices M' rho' r := by
      intro i hi
      have hi' : i + 1 ≤ (SimpleGraph.Walk.cons hadj p).length := by
        simpa using Nat.succ_le_succ hi
      simpa using hpath (i + 1) hi'
    obtain ⟨q, hq⟩ := ih htail
    have ha := adj_map_symm e (by simpa using hpath 0 (Nat.zero_le _)) hx hadj
    exact ⟨SimpleGraph.Walk.cons ha q, by simp [hq]⟩

/-- Helper toward Definition 3.8: a distance bound through inverse dart maps. -/
private theorem distance_back (e : D39GeomBallIsoV2 r M rho M' rho')
    (v' : V') (hv' : v' ∈ d39GeomBallVertices M' rho' r) :
      d39GeomGraphDistance M (d39GeomRootVertex M rho)
        (e.vertexEquiv.symm ⟨v', hv'⟩).1 ≤
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho') v' := by
  let G := d39GeomGraph M
  let G' := d39GeomGraph M'
  let root' := d39GeomRootVertex M' rho'
  have hfinite : G'.edist root' v' ≠ ⊤ := by
    intro htop
    have hv'' := hv'
    simp [d39GeomBallVertices, d39GeomGraphDistance, G', root', htop] at hv''
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ r := by
    have : (p.length : ℕ∞) ≤ (r : ℕ∞) := by rw [hp]; exact hv'
    exact_mod_cast this
  have hpath : ∀ i, i ≤ p.length →
      p.getVert i ∈ d39GeomBallVertices M' rho' r := by
    intro i hi
    have hdist := SimpleGraph.edist_le (p.take i)
    have hle : (p.take i).length ≤ r := by
      rw [SimpleGraph.Walk.take_length]
      omega
    change G'.edist root' (p.getVert i) ≤ (r : ℕ∞)
    exact le_trans hdist (by exact_mod_cast hle)
  obtain ⟨q, hq⟩ := mapWalk_symm e p hpath
  have hstart :
      (e.vertexEquiv.symm ⟨root', by simpa [root'] using hpath 0 (Nat.zero_le _)⟩).1 =
        d39GeomRootVertex M rho := by
    have heq : e.vertexEquiv
        ⟨d39GeomRootVertex M rho, by simp [d39GeomBallVertices,
          d39GeomGraphDistance]⟩ =
        ⟨root', by simpa [root'] using hpath 0 (Nat.zero_le _)⟩ := by
      apply Subtype.ext
      simpa [root'] using e.root_initial_map
    have h := congrArg (fun z => (e.vertexEquiv.symm z).1) heq
    simpa using h.symm
  have hend :
      (e.vertexEquiv.symm ⟨v', by simpa using hpath p.length le_rfl⟩).1 =
        (e.vertexEquiv.symm ⟨v', hv'⟩).1 := by congr 1
  change G.edist _ _ ≤ _
  calc
    G.edist (d39GeomRootVertex M rho) (e.vertexEquiv.symm ⟨v', hv'⟩).1 ≤
        (q.copy hstart hend).length := SimpleGraph.edist_le _
    _ = p.length := by rw [SimpleGraph.Walk.length_copy, hq]
    _ = G'.edist root' v' := hp

/-- Helper toward Definition 3.8: a dart ball isomorphism preserves distance from its ordered root. -/
theorem distance_preserving (e : D39GeomBallIsoV2 r M rho M' rho')
    (v : V) (hv : v ∈ d39GeomBallVertices M rho r) :
    d39GeomGraphDistance M (d39GeomRootVertex M rho) v =
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho')
        (e.vertexEquiv ⟨v, hv⟩).1 := by
  apply le_antisymm
  · have h := e.distance_back (e.vertexEquiv ⟨v, hv⟩).1
      (e.vertexEquiv ⟨v, hv⟩).2
    have hback :
        (e.vertexEquiv.symm
          ⟨(e.vertexEquiv ⟨v, hv⟩).1, (e.vertexEquiv ⟨v, hv⟩).2⟩).1 = v := by
      exact congrArg Subtype.val (Equiv.symm_apply_apply e.vertexEquiv ⟨v, hv⟩)
    rw [hback] at h
    exact h
  · exact e.distance_le v hv

/-- Helper toward Definition 3.8: a smaller geometric vertex ball lies in its enclosing ball. -/
theorem vertexBall_mono (hsr : s ≤ r) {v : V}
    (hv : v ∈ d39GeomBallVertices M rho s) :
    v ∈ d39GeomBallVertices M rho r := by
  change d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (s : ℕ∞) at hv
  change d39GeomGraphDistance M (d39GeomRootVertex M rho) v ≤ (r : ℕ∞)
  exact le_trans hv (by exact_mod_cast hsr)

/-- Helper toward Definition 3.8: restrict the vertex equivalence to smaller balls. -/
@[expose] def restrictVertices (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) :
    {v // v ∈ d39GeomBallVertices M rho s} ≃
      {v // v ∈ d39GeomBallVertices M' rho' s} := by
  let L := Equiv.subtypeSubtypeEquivSubtype
    (p := fun v : V => v ∈ d39GeomBallVertices M rho r)
    (q := fun v : V => v ∈ d39GeomBallVertices M rho s)
    (fun {_} h => vertexBall_mono hsr h)
  let R := Equiv.subtypeSubtypeEquivSubtype
    (p := fun v : V' => v ∈ d39GeomBallVertices M' rho' r)
    (q := fun v : V' => v ∈ d39GeomBallVertices M' rho' s)
    (fun {_} h => vertexBall_mono (M := M') (rho := rho') hsr h)
  let mid := e.vertexEquiv.subtypeEquiv
      (p := fun v : {v // v ∈ d39GeomBallVertices M rho r} =>
        v.1 ∈ d39GeomBallVertices M rho s)
      (q := fun v : {v // v ∈ d39GeomBallVertices M' rho' r} =>
        v.1 ∈ d39GeomBallVertices M' rho' s) fun v => by
    change v.1 ∈ d39GeomBallVertices M rho s ↔
      (e.vertexEquiv v).1 ∈ d39GeomBallVertices M' rho' s
    change d39GeomGraphDistance M (d39GeomRootVertex M rho) v.1 ≤ (s : ℕ∞) ↔
      d39GeomGraphDistance M' (d39GeomRootVertex M' rho')
        (e.vertexEquiv v).1 ≤ (s : ℕ∞)
    rw [e.distance_preserving v.1 v.2]
  exact L.symm.trans (mid.trans R)

/-- Helper toward Definition 3.8: the restricted vertex equivalence keeps the same vertex. -/
theorem restrictVertices_val (e : D39GeomBallIsoV2 r M rho M' rho')
    (hsr : s ≤ r) (v : {v // v ∈ d39GeomBallVertices M rho s}) :
    (restrictVertices e hsr v).1 =
      (e.vertexEquiv ⟨v.1, vertexBall_mono hsr v.2⟩).1 := by
  rfl









end D39GeomBallIsoV2

end DirectedDistances.PaperProofs.Section3

end
