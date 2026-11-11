/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section3.D39GeometricDomain
public import DirectedDistances.PlanarMap.GeneralPlaneMapEndpointSwap

/-! # Combinatorial transport for Definition 3.8 -/

public section

noncomputable section

namespace DirectedDistances.PaperProofs.Section3

open DirectedDistances.PlanarMap
open scoped ENNReal

universe uV uE uV' uE''

/-- Helper toward Definition 3.8: a rooted combinatorial dart isomorphism.
The edge flip records when the stored endpoint order is reversed. -/
structure D39CombDartIso {V : Type uV} {E : Type uE}
    {V' : Type uV'} {E' : Type uE''}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool)
    (M' : DirectedPlaneMapWithMissing V' E') (rho' : E' × Bool) where
  vertexEquiv : V ≃ V'
  edgeEquiv : E ≃ E'
  flip : E → Bool
  src_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.src e) =
    if flip e then M'.toPlaneMapWithMissing.tgt (edgeEquiv e)
    else M'.toPlaneMapWithMissing.src (edgeEquiv e)
  tgt_map : ∀ e, vertexEquiv (M.toPlaneMapWithMissing.tgt e) =
    if flip e then M'.toPlaneMapWithMissing.src (edgeEquiv e)
    else M'.toPlaneMapWithMissing.tgt (edgeEquiv e)
  missing_map : ∀ e,
    M'.toPlaneMapWithMissing.missing (edgeEquiv e) ↔
      M.toPlaneMapWithMissing.missing e
  forward_map : ∀ e (he : ¬ M.toPlaneMapWithMissing.missing e),
    M'.forward ⟨edgeEquiv e, by simpa [missing_map e] using he⟩ =
      Bool.xor (M.forward ⟨e, he⟩) (flip e)
  root_edge : edgeEquiv rho.1 = rho'.1
  root_bool : rho'.2 = Bool.xor rho.2 (flip rho.1)

namespace D39CombDartIso

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
  {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
  {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}

/-- Helper toward Definition 3.8: the identity combinatorial dart isomorphism. -/
@[expose] def refl (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) :
    D39CombDartIso M rho M rho where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  flip := fun _ => false
  src_map := by intro e; simp
  tgt_map := by intro e; simp
  missing_map := by intro e; rfl
  forward_map := by intro e he; simp
  root_edge := rfl
  root_bool := by simp

/-- Helper toward Definition 3.8: reverse a combinatorial dart isomorphism. -/
@[expose] def symm (e : D39CombDartIso M rho M' rho') :
    D39CombDartIso M' rho' M rho where
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  flip := fun f => e.flip (e.edgeEquiv.symm f)
  src_map := by
    intro f
    have hs := e.src_map (e.edgeEquiv.symm f)
    have ht := e.tgt_map (e.edgeEquiv.symm f)
    have heq : e.edgeEquiv (e.edgeEquiv.symm f) = f := e.edgeEquiv.apply_symm_apply f
    cases hb : e.flip (e.edgeEquiv.symm f)
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm hs).symm
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm ht).symm
  tgt_map := by
    intro f
    have hs := e.src_map (e.edgeEquiv.symm f)
    have ht := e.tgt_map (e.edgeEquiv.symm f)
    have heq : e.edgeEquiv (e.edgeEquiv.symm f) = f := e.edgeEquiv.apply_symm_apply f
    cases hb : e.flip (e.edgeEquiv.symm f)
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm ht).symm
    · simpa [hb, heq] using (congrArg e.vertexEquiv.symm hs).symm
  missing_map := by
    intro f
    simpa using (e.missing_map (e.edgeEquiv.symm f)).symm
  -- The transport of the marked root edge identifies the flip at the inverse image.
  -- (Used below to keep the root Boolean equation in the original indexing.)
  forward_map := by
    intro f hf
    have he : ¬ M.toPlaneMapWithMissing.missing (e.edgeEquiv.symm f) := by
      intro hm
      exact hf (by simpa using (e.missing_map (e.edgeEquiv.symm f)).mpr hm)
    have h := e.forward_map (e.edgeEquiv.symm f) he
    have hpresent : ¬ M'.toPlaneMapWithMissing.missing
        (e.edgeEquiv (e.edgeEquiv.symm f)) :=
      fun hm => he ((e.missing_map (e.edgeEquiv.symm f)).mp hm)
    have hsub : (⟨f, hf⟩ : {a : E' // ¬ M'.toPlaneMapWithMissing.missing a}) =
        ⟨e.edgeEquiv (e.edgeEquiv.symm f), hpresent⟩ := by
      apply Subtype.ext
      exact (e.edgeEquiv.apply_symm_apply f).symm
    rw [← hsub] at h
    cases hb : e.flip (e.edgeEquiv.symm f) <;>
      cases hm : M.forward ⟨e.edgeEquiv.symm f, he⟩ <;> simp [hb, hm] at h ⊢
    all_goals exact h
  root_edge := by
    apply e.edgeEquiv.injective
    simpa using e.root_edge.symm
  root_bool := by
    have h := e.root_bool
    have hflip : e.flip (e.edgeEquiv.symm rho'.1) = e.flip rho.1 := by
      have h' := congrArg (fun a => e.flip (e.edgeEquiv.symm a)) e.root_edge
      simpa using h'.symm
    rw [hflip]
    cases hb : rho.2 <;> cases hf : e.flip rho.1 <;> simp_all

/-- Helper toward Definition 3.8: compose combinatorial dart isomorphisms. -/
@[expose] def trans {V'' : Type*} {E'' : Type*}
    {M'' : DirectedPlaneMapWithMissing V'' E''} {rho'' : E'' × Bool}
    (e : D39CombDartIso M rho M' rho')
    (f : D39CombDartIso M' rho' M'' rho'') :
    D39CombDartIso M rho M'' rho'' where
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  flip := fun a => Bool.xor (e.flip a) (f.flip (e.edgeEquiv a))
  src_map := by
    intro a
    have hs := e.src_map a
    have hs' := f.src_map (e.edgeEquiv a)
    have ht' := f.tgt_map (e.edgeEquiv a)
    cases h1 : e.flip a <;> cases h2 : f.flip (e.edgeEquiv a)
    all_goals
      simp [h1] at hs
      simp [h2] at hs' ht'
      first
      | simpa [Equiv.trans_apply, h1, h2] using (congrArg f.vertexEquiv hs).trans hs'
      | simpa [Equiv.trans_apply, h1, h2] using (congrArg f.vertexEquiv hs).trans ht'
  tgt_map := by
    intro a
    have ht := e.tgt_map a
    have hs' := f.src_map (e.edgeEquiv a)
    have ht' := f.tgt_map (e.edgeEquiv a)
    cases h1 : e.flip a <;> cases h2 : f.flip (e.edgeEquiv a)
    all_goals
      simp [h1] at ht
      simp [h2] at hs' ht'
      first
      | simpa [Equiv.trans_apply, h1, h2] using (congrArg f.vertexEquiv ht).trans hs'
      | simpa [Equiv.trans_apply, h1, h2] using (congrArg f.vertexEquiv ht).trans ht'
  missing_map := by intro a; exact (f.missing_map _).trans (e.missing_map a)
  forward_map := by
    intro a ha
    have ha' : ¬ M'.toPlaneMapWithMissing.missing (e.edgeEquiv a) :=
      fun hm => ha ((e.missing_map a).mp hm)
    have h1 := e.forward_map a ha
    have h2 := f.forward_map (e.edgeEquiv a) ha'
    cases hflip1 : e.flip a <;> cases hflip2 : f.flip (e.edgeEquiv a) <;>
      simp [hflip1, hflip2, h1, h2]
  root_edge := by
    change f.edgeEquiv (e.edgeEquiv rho.1) = rho''.1
    rw [e.root_edge, f.root_edge]
  root_bool := by
    have h2 : rho''.2 = Bool.xor rho'.2 (f.flip (e.edgeEquiv rho.1)) := by
      simpa [e.root_edge] using f.root_bool
    rw [h2, e.root_bool]
    cases rho.2 <;> cases e.flip rho.1 <;>
      cases f.flip (e.edgeEquiv rho.1) <;> rfl

end D39CombDartIso

namespace D39CombDartIso

/-- Helper toward Definition 3.8: adjacency is preserved and reflected by the
vertex equivalence, while edge identities witness adjacency. -/
theorem adj_map {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    (e : D39CombDartIso M rho M' rho') {v w : V} :
    d39GeomAdj M v w ↔
      d39GeomAdj M' (e.vertexEquiv v) (e.vertexEquiv w) := by
  constructor
  · rintro ⟨hne, a, ha | ha⟩
    · have hne' : e.vertexEquiv v ≠ e.vertexEquiv w :=
        fun h => hne (e.vertexEquiv.injective h)
      cases hb : e.flip a
      · refine ⟨hne', e.edgeEquiv a, Or.inl ?_⟩
        have hs : M'.toPlaneMapWithMissing.src (e.edgeEquiv a) =
            e.vertexEquiv v := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.src a) := by
              simpa [hb] using (e.src_map a).symm
            _ = e.vertexEquiv v := congrArg e.vertexEquiv ha.1
        have ht : M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a) =
            e.vertexEquiv w := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) := by
              simpa [hb] using (e.tgt_map a).symm
            _ = e.vertexEquiv w := congrArg e.vertexEquiv ha.2
        exact ⟨hs, ht⟩
      · refine ⟨hne', e.edgeEquiv a, Or.inr ?_⟩
        have hs : M'.toPlaneMapWithMissing.src (e.edgeEquiv a) =
            e.vertexEquiv w := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) := by
              simpa [hb] using (e.tgt_map a).symm
            _ = e.vertexEquiv w := congrArg e.vertexEquiv ha.2
        have ht : M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a) =
            e.vertexEquiv v := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.src a) := by
              simpa [hb] using (e.src_map a).symm
            _ = e.vertexEquiv v := congrArg e.vertexEquiv ha.1
        exact ⟨hs, ht⟩
    · have hne' : e.vertexEquiv v ≠ e.vertexEquiv w :=
        fun h => hne (e.vertexEquiv.injective h)
      cases hb : e.flip a
      · refine ⟨hne', e.edgeEquiv a, Or.inr ?_⟩
        have hs : M'.toPlaneMapWithMissing.src (e.edgeEquiv a) =
            e.vertexEquiv w := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.src a) := by
              simpa [hb] using (e.src_map a).symm
            _ = e.vertexEquiv w := congrArg e.vertexEquiv ha.1
        have ht : M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a) =
            e.vertexEquiv v := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) := by
              simpa [hb] using (e.tgt_map a).symm
            _ = e.vertexEquiv v := congrArg e.vertexEquiv ha.2
        exact ⟨hs, ht⟩
      · refine ⟨hne', e.edgeEquiv a, Or.inl ?_⟩
        have hs : M'.toPlaneMapWithMissing.src (e.edgeEquiv a) =
            e.vertexEquiv v := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) := by
              simpa [hb] using (e.tgt_map a).symm
            _ = e.vertexEquiv v := congrArg e.vertexEquiv ha.2
        have ht : M'.toPlaneMapWithMissing.tgt (e.edgeEquiv a) =
            e.vertexEquiv w := by
          calc
            _ = e.vertexEquiv (M.toPlaneMapWithMissing.src a) := by
              simpa [hb] using (e.src_map a).symm
            _ = e.vertexEquiv w := congrArg e.vertexEquiv ha.1
        exact ⟨hs, ht⟩
  · rintro ⟨hne', b, hb | hb⟩
    · have hne : v ≠ w := fun h => hne' (congrArg e.vertexEquiv h)
      let a := e.edgeEquiv.symm b
      cases hf : e.flip a
      · refine ⟨hne, a, Or.inl ?_⟩
        have hs : e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
            M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.src_map a
        have ht : e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
            M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.tgt_map a
        constructor
        · apply e.vertexEquiv.injective
          exact hs.trans hb.1
        · apply e.vertexEquiv.injective
          exact ht.trans hb.2
      · refine ⟨hne, a, Or.inr ?_⟩
        have hs : e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
            M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.src_map a
        have ht : e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
            M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.tgt_map a
        constructor
        · apply e.vertexEquiv.injective
          exact hs.trans hb.2
        · apply e.vertexEquiv.injective
          exact ht.trans hb.1
    · have hne : v ≠ w := fun h => hne' (congrArg e.vertexEquiv h)
      let a := e.edgeEquiv.symm b
      cases hf : e.flip a
      · refine ⟨hne, a, Or.inr ?_⟩
        have hs : e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
            M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.src_map a
        have ht : e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
            M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.tgt_map a
        constructor
        · apply e.vertexEquiv.injective
          exact hs.trans hb.1
        · apply e.vertexEquiv.injective
          exact ht.trans hb.2
      · refine ⟨hne, a, Or.inl ?_⟩
        have hs : e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
            M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.src_map a
        have ht : e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
            M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.tgt_map a
        constructor
        · apply e.vertexEquiv.injective
          exact hs.trans hb.2
        · apply e.vertexEquiv.injective
          exact ht.trans hb.1

/-- Helper toward Definition 3.8: the combinatorial dart isomorphism induces
an isomorphism of the underlying undirected geometric graphs. -/
@[expose] def graphIso {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    (e : D39CombDartIso M rho M' rho') : d39GeomGraph M ≃g d39GeomGraph M' where
  toEquiv := e.vertexEquiv
  map_rel_iff' := by
    intro v w
    exact (e.adj_map).symm

/-- Helper toward Definition 3.8: extended geometric graph distance is
preserved. -/
theorem graphDistance_map {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    (e : D39CombDartIso M rho M' rho') (v w : V) :
    d39GeomGraphDistance M v w =
      d39GeomGraphDistance M' (e.vertexEquiv v) (e.vertexEquiv w) :=
  (e.graphIso.edist_eq v w).symm

/-- Helper toward Definition 3.8: the ordered root dart's initial vertex maps
to the target ordered root dart's initial vertex. -/
theorem rootVertex_map {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    (e : D39CombDartIso M rho M' rho') :
    e.vertexEquiv (d39GeomRootVertex M rho) =
      d39GeomRootVertex M' rho' := by
  cases hb : rho.2 <;> cases hf : e.flip rho.1 <;>
    simp [d39GeomRootVertex, hb, hf, e.root_edge, e.root_bool,
      e.src_map, e.tgt_map]

/-- Helper toward Definition 3.8: the source domain hypotheses transport to
the target rooted geometric map. -/
theorem domain_map {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE''}
    {M : DirectedPlaneMapWithMissing V E} {rho : E × Bool}
    {M' : DirectedPlaneMapWithMissing V' E'} {rho' : E' × Bool}
    (e : D39CombDartIso M rho M' rho') (hM : D39GeomDomain M rho) :
    D39GeomDomain M' rho' := by
  refine ⟨?_, ?_, ?_⟩
  · intro v' w'
    have h := hM.connected (e.vertexEquiv.symm v') (e.vertexEquiv.symm w')
    have hm := h.map e.graphIso.toHom
    simpa [graphIso] using hm
  · intro v'
    let I : Set E := {a | M.toPlaneMapWithMissing.src a = e.vertexEquiv.symm v' ∨
      M.toPlaneMapWithMissing.tgt a = e.vertexEquiv.symm v'}
    let I' : Set E' := {a | M'.toPlaneMapWithMissing.src a = v' ∨
      M'.toPlaneMapWithMissing.tgt a = v'}
    have hI : I.Finite := hM.locallyFinite (e.vertexEquiv.symm v')
    have hsub : I' ⊆ e.edgeEquiv '' I := by
      intro b hb
      let a := e.edgeEquiv.symm b
      have hsrc : M'.toPlaneMapWithMissing.src b = v' → a ∈ I := by
        intro heq
        cases hf : e.flip a
        · apply Or.inl
          apply e.vertexEquiv.injective
          calc
            e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
                M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.src_map a
            _ = v' := heq
            _ = e.vertexEquiv (e.vertexEquiv.symm v') :=
              (e.vertexEquiv.apply_symm_apply v').symm
        · apply Or.inr
          apply e.vertexEquiv.injective
          calc
            e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
                M'.toPlaneMapWithMissing.src b := by simpa [a, hf] using e.tgt_map a
            _ = v' := heq
            _ = e.vertexEquiv (e.vertexEquiv.symm v') :=
              (e.vertexEquiv.apply_symm_apply v').symm
      have htgt : M'.toPlaneMapWithMissing.tgt b = v' → a ∈ I := by
        intro heq
        cases hf : e.flip a
        · apply Or.inr
          apply e.vertexEquiv.injective
          calc
            e.vertexEquiv (M.toPlaneMapWithMissing.tgt a) =
                M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.tgt_map a
            _ = v' := heq
            _ = e.vertexEquiv (e.vertexEquiv.symm v') :=
              (e.vertexEquiv.apply_symm_apply v').symm
        · apply Or.inl
          apply e.vertexEquiv.injective
          calc
            e.vertexEquiv (M.toPlaneMapWithMissing.src a) =
                M'.toPlaneMapWithMissing.tgt b := by simpa [a, hf] using e.src_map a
            _ = v' := heq
            _ = e.vertexEquiv (e.vertexEquiv.symm v') :=
              (e.vertexEquiv.apply_symm_apply v').symm
      have hab : a ∈ {x | M.toPlaneMapWithMissing.src x = e.vertexEquiv.symm v' ∨
          M.toPlaneMapWithMissing.tgt x = e.vertexEquiv.symm v'} := by
        rcases hb with hs | ht
        · exact hsrc (by simpa [a] using hs)
        · exact htgt (by simpa [a] using ht)
      refine ⟨a, hab, ?_⟩
      simp [a]
    exact hI.image e.edgeEquiv |>.subset hsub
  · rcases hM.rootValid with hmiss | ⟨hpresent, hforward⟩
    · left
      rw [← e.root_edge]
      exact (e.missing_map rho.1).mpr hmiss
    · right
      have hpresent' : ¬ M'.toPlaneMapWithMissing.missing rho'.1 := by
        rw [← e.root_edge]
        exact fun hm => hpresent ((e.missing_map rho.1).mp hm)
      refine ⟨hpresent', ?_⟩
      calc
        M'.forward ⟨rho'.1, hpresent'⟩ =
            Bool.xor (M.forward ⟨rho.1, hpresent⟩) (e.flip rho.1) := by
              simpa [e.root_edge] using e.forward_map rho.1 hpresent
        _ = Bool.xor rho.2 (e.flip rho.1) := by rw [hforward]
        _ = rho'.2 := e.root_bool.symm

end D39CombDartIso

namespace D39CombDartIso

/-- Helper toward Definition 3.8: the Boolean encoding of membership in an
edge set, using classical decidability. -/
@[expose] noncomputable def membershipFlip {E : Type uE} (S : Set E) (e : E) : Bool :=
  @decide (e ∈ S) (Classical.propDecidable (e ∈ S))

/-- Helper toward Definition 3.8: reverse stored endpoints on the selected
edge set using the endpoint-storage operation, whose arc field uses
`Path.symm`, and adjust the ordered root Boolean by the same flip. Membership
in `S` is represented by its Boolean decider. -/
@[expose] noncomputable def storeFlip {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E) :
    D39CombDartIso M rho
      (M.endpointSwap (membershipFlip S))
      (rho.1, Bool.xor rho.2 (membershipFlip S rho.1)) := by
  classical
  refine {
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    flip := membershipFlip S
    src_map := ?_
    tgt_map := ?_
    missing_map := ?_
    forward_map := ?_
    root_edge := rfl
    root_bool := rfl }
  · intro e
    by_cases hs : membershipFlip S e = true <;>
      simp [DirectedPlaneMapWithMissing.endpointSwap,
        PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hs]
  · intro e
    by_cases hs : membershipFlip S e = true <;>
      simp [DirectedPlaneMapWithMissing.endpointSwap,
        PlaneMapWithMissing.endpointSwap, PlaneGraphDrawing.endpointSwap, hs]
  · intro e
    rfl
  · intro e he
    by_cases hs : membershipFlip S e = true <;>
      simp [DirectedPlaneMapWithMissing.endpointSwap, hs] <;> rfl

/-- Helper toward Definition 3.8: the rooted geometric domain is preserved by
the exact endpoint-storage reversal on an arbitrary selected edge set. -/
theorem domain_storeFlip {V : Type uV} {E : Type uE}
    (M : DirectedPlaneMapWithMissing V E) (rho : E × Bool) (S : Set E)
    (hM : D39GeomDomain M rho) :
    D39GeomDomain
      (M.endpointSwap (membershipFlip S))
      (rho.1, Bool.xor rho.2 (membershipFlip S rho.1)) := by
  classical
  exact (storeFlip M rho S).domain_map hM

end D39CombDartIso

end DirectedDistances.PaperProofs.Section3

end
