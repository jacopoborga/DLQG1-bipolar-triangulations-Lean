/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusSideMeasurable7

/-! # Dart transport for the nonpositive right-side code

Helpers toward Lemma 5.5 (`lem-geo-infty-ind`), -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open DirectedDistances.PaperProofs.Section4 DirectedDistances.Paper.Section4
open scoped Classical

local notation "Coherent" x =>
  selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime

/-- Helper toward Lemma 5.5. Transport a raw code dart representative by
fixing prefix darts and applying the hatted marked isomorphism, including its
edge-dependent endpoint-bit action. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_rawDartRepMap8
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N)
    (a : Sum {e : ℕ // e < F.nextEdge} M.edges) (s : Bool) :
    Sum {e : ℕ // e < F.nextEdge} N.edges × Bool :=
  match a with
  | .inl e => (.inl e, s)
  | .inr e =>
      let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(e.val, s), e.property⟩
      let d' := rMinus_rightSideMarkedIso_dartMap phi d
      (.inr ⟨d'.val.1, d'.property⟩, d'.val.2)

/-- Helper toward Lemma 5.5. Prefix dart representatives keep their endpoint
bit under the raw transport. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_snd_inl
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N)
    (a : {e : ℕ // e < F.nextEdge}) (s : Bool) :
    (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi (.inl a) s).2 = s := rfl

/-- Helper toward Lemma 5.5. A hatted dart representative transports its
endpoint bit by the marked isomorphism's full dart action. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_snd_inr
    (F : State) {M N : GeometricSideSubmap}
    (phi : GeometricSideMarkedIso M N) (a : M.edges) (s : Bool) :
    (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi (.inr a) s).2 =
      (rMinus_rightSideMarkedIso_dartMap phi ⟨(a.val, s), a.property⟩).val.2 := rfl

/-- Helper toward Lemma 5.5. At a shared boundary edge, the hatted dart
transport preserves the indexed endpoint bit, even when general edges may
reverse their orientation. -/
theorem rMinus_rightSideMarkedIso_dartMap_boundaryBit8
    (x : XDP) (q q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (i : ℕ) (s : Bool) :
    rMinus_rightSideMarkedIso_dartMap phi
      ⟨(((rMinusCoherentRightSide x q).boundary i).1, s),
        rMinus_hatted_boundary_mem x q i⟩ =
      ⟨(((rMinusCoherentRightSide x q').boundary i).1, s),
        rMinus_hatted_boundary_mem x q' i⟩ := by
  have hcell := rMinus_rightSideMarkedIso_dartMap_cell phi
    ⟨(((rMinusCoherentRightSide x q).boundary i).1, s),
      rMinus_hatted_boundary_mem x q i⟩
  have hboundary := rMinus_rightSideMarkedIso_boundaryDart_bit x q q' phi i s
  rw [hboundary] at hcell
  apply Subtype.ext
  exact (congrArg Subtype.val (Sum.inr.inj hcell)).symm

/-- Helper toward Lemma 5.5. The full raw dart transport sends every
indexed hatted boundary dart to the same target boundary dart with its bit
unchanged, so it agrees with the fixed prefix representative there. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_boundary
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (i : ℕ) (s : Bool) :
    rMinus_rightSideMarkedIso_rawDartRepMap8 F phi
      (.inr ⟨((rMinusCoherentRightSide x q).boundary i).1,
        rMinus_hatted_boundary_mem x q i⟩) s =
      (.inr ⟨((rMinusCoherentRightSide x q').boundary i).1,
        rMinus_hatted_boundary_mem x q' i⟩, s) := by
  have h := rMinus_rightSideMarkedIso_dartMap_boundaryBit8 x q q' phi i s
  unfold rMinus_rightSideMarkedIso_rawDartRepMap8
  apply Prod.ext
  · apply congrArg Sum.inr
    apply Subtype.ext
    exact congrArg (fun d => d.val.1) h
  · exact congrArg (fun d => d.val.2) h

/-- Helper toward Lemma 5.5. The raw dart transport carries each generating
shared-prefix/boundary edge identification to the corresponding target
identification and preserves its endpoint bit. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_gluing
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges) (s : Bool)
    (hab : rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).1
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi b s).1 ∧
    (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).2 =
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi b s).2 := by
  cases a with
  | inl a =>
      cases b with
      | inl b => simp [rMinusCodeEdgeGluing] at hab
      | inr b =>
          rcases hab with ⟨i, hi, hb⟩
          have hboundary : b = ⟨((rMinusCoherentRightSide x q).boundary i).1,
              rMinus_hatted_boundary_mem x q i⟩ := Subtype.ext hb.symm
          subst b
          have ha' : rMinus_rightSideMarkedIso_rawDartRepMap8 F phi (.inl a) s =
              (.inl a, s) := rfl
          have hb' := rMinus_rightSideMarkedIso_rawDartRepMap8_boundary
            x q q' phi F i s
          rw [ha', hb']
          exact ⟨⟨i, hi, rfl⟩, rfl⟩
  | inr a => cases b <;> simp [rMinusCodeEdgeGluing] at hab

/-- Helper toward Lemma 5.5. The raw dart transport respects the complete
edge-class relation at a fixed endpoint bit. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_setoid
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges) (s : Bool)
    (hab : rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeEdgeSetoid F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).1
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi b s).1 ∧
    (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).2 =
      (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi b s).2 := by
  change Relation.EqvGen
    (rMinusCodeEdgeGluing F (rMinusCoherentRightSide x q)) a b at hab
  induction hab with
  | rel a b hab =>
      obtain ⟨hglue, hbit⟩ :=
        rMinus_rightSideMarkedIso_rawDartRepMap8_gluing x q q' phi F a b s hab
      exact ⟨Relation.EqvGen.rel _ _ hglue, hbit⟩
  | refl a => exact ⟨Relation.EqvGen.refl _, rfl⟩
  | symm a b hab ih => exact ⟨Relation.EqvGen.symm _ _ ih.1, ih.2.symm⟩
  | trans a b c hab hbc ihab ihbc =>
      exact ⟨Relation.EqvGen.trans _ _ _ ihab.1 ihbc.1, ihab.2.trans ihbc.2⟩

/-- Helper toward Lemma 5.5. Lift raw dart transport through the edge
quotient, retaining the transported endpoint bit. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_rawDartQuotMap8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedDart F (rMinusCoherentRightSide x q) →
      RMinusCodeGluedDart F (rMinusCoherentRightSide x q') :=
  fun d => Quotient.lift
    (fun a =>
      (⟦(rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a d.2).1⟧,
        (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a d.2).2))
    (by
      intro a b hab
      obtain ⟨he, hs⟩ :=
        rMinus_rightSideMarkedIso_rawDartRepMap8_setoid x q q' phi F a b d.2 hab
      exact Prod.ext (Quotient.sound he) hs) d.1

/-- Helper toward Lemma 5.5. On a raw edge representative, the lifted dart
map agrees with the endpoint-bit-aware representative transport. -/
theorem rMinus_rightSideMarkedIso_rawDartQuotMap8_mk
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges) (s : Bool) :
    rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F
      (⟦a⟧, s) =
        (⟦(rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).1⟧,
          (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).2) := rfl

/-- Helper toward Lemma 5.5. The raw quotient dart maps induced by a marked
isomorphism and its inverse compose to the identity, including endpoint
bits that may flip on individual hatted edges. -/
theorem rMinus_rightSideMarkedIso_rawDartQuotMap8_symm_apply
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : RMinusCodeGluedDart F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_rawDartQuotMap8 x q' q
      (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F d) = d := by
  rcases d with ⟨e, s⟩
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a => rfl
  | inr a =>
      let d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q).edges} :=
        ⟨(a.val, s), a.property⟩
      let d' := rMinus_rightSideMarkedIso_dartMap phi d
      have hcanon :
          (⟨(d'.val.1, d'.val.2), d'.property⟩ :
            {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q').edges}) = d' := rfl
      have hinv := rMinus_rightSideMarkedIso_dartMap_symm_apply phi d
      have hinv' : rMinus_rightSideMarkedIso_dartMap
          (GeometricSideMarkedIso.symm phi)
          ⟨(d'.val.1, d'.val.2), d'.property⟩ = d := by
        rw [hcanon]
        exact hinv
      rw [rMinus_rightSideMarkedIso_rawDartQuotMap8_mk,
        rMinus_rightSideMarkedIso_rawDartQuotMap8_mk]
      have hraw :
          rMinus_rightSideMarkedIso_rawDartRepMap8 F
            (GeometricSideMarkedIso.symm phi)
            (.inr ⟨d'.val.1, d'.property⟩) d'.val.2 = (.inr a, s) := by
        unfold rMinus_rightSideMarkedIso_rawDartRepMap8
        apply Prod.ext
        · apply congrArg Sum.inr
          apply Subtype.ext
          exact congrArg (fun z => z.val.1) hinv'
        · exact congrArg (fun z => z.val.2) hinv'
      have hfirst :
          rMinus_rightSideMarkedIso_rawDartRepMap8 F phi (.inr a) s =
            (.inr ⟨d'.val.1, d'.property⟩, d'.val.2) := rfl
      rw [hfirst, hraw]

private theorem rMinus_rightSideMarkedIso_symm_symm8
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    GeometricSideMarkedIso.symm (GeometricSideMarkedIso.symm phi) = phi := by
  cases phi
  rfl

/-- Helper toward Lemma 5.5. The complete glued-dart carriers of the two
code blocks are equivalent, with endpoint bits transported by the hatted
marked isomorphism and fixed on the finite prefix. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_gluedDartEquiv8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) :
    RMinusCodeGluedDart F (rMinusCoherentRightSide x q) ≃
      RMinusCodeGluedDart F (rMinusCoherentRightSide x q') where
  toFun := rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F
  invFun := rMinus_rightSideMarkedIso_rawDartQuotMap8 x q' q
    (GeometricSideMarkedIso.symm phi) F
  left_inv := rMinus_rightSideMarkedIso_rawDartQuotMap8_symm_apply x q q' phi F
  right_inv := by
    intro d
    rw [← rMinus_rightSideMarkedIso_symm_symm8 phi]
    exact rMinus_rightSideMarkedIso_rawDartQuotMap8_symm_apply
      x q' q (GeometricSideMarkedIso.symm phi) F d

/-- Helper toward Lemma 5.5. For any finite state, the glued-dart action
fixes each prefix dart. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : StageDart F.nextEdge) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
      (rMinusCodePrefixDart F (rMinusCoherentRightSide x q) d) =
    rMinusCodePrefixDart F (rMinusCoherentRightSide x q') d := rfl

/-- Helper toward Lemma 5.5. For any finite state, the glued-dart action
on hatted darts is the marked isomorphism's full dart action. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State)
    (d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q).edges}) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
      (rMinusCodeHattedDart F (rMinusCoherentRightSide x q) d) =
    rMinusCodeHattedDart F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_dartMap phi d) := rfl

/-- Helper toward Lemma 5.5. The glued-dart equivalence fixes every
finite-prefix dart representative. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ) (d : StageDart (kmswStage w n).nextEdge) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusCodePrefixDart (kmswStage w n)
        (rMinusCoherentRightSide x q) d) =
      rMinusCodePrefixDart (kmswStage w n)
        (rMinusCoherentRightSide x q') d := rfl

/-- Helper toward Lemma 5.5. On hatted darts, the glued-dart equivalence
agrees with the full endpoint-bit-aware action of the marked isomorphism. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_hatted
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q).edges}) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusCodeHattedDart (kmswStage w n)
        (rMinusCoherentRightSide x q) d) =
      rMinusCodeHattedDart (kmswStage w n)
        (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_dartMap phi d) := rfl

/-- Helper toward Lemma 5.5. The induced equivalence of hatted dart carriers
preserves the first-return rotation recorded by each hatted geometric side. -/
theorem rMinus_rightSideMarkedIso_hattedRotation8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (d : {z : ℕ × Bool // z.1 ∈ (rMinusCoherentRightSide x q).edges}) :
    rMinus_rightSideMarkedIso_dartMap phi (rMinusHattedRotation x q d) =
      rMinusHattedRotation x q'
        (rMinus_rightSideMarkedIso_dartMap phi d) := by
  have h := (phi.relation_iff .rotation (.inr d)
      (.inr (rMinusHattedRotation x q d))).mp
    ((rMinusHattedRotation_iff x q d _).mpr rfl)
  simp only [rMinus_rightSideMarkedIso_dartMap_cell,
    geometricSideRelation] at h
  exact ((rMinusHattedRotation_iff x q'
    (rMinus_rightSideMarkedIso_dartMap phi d) _).mp h).symm

/-- Helper toward Lemma 5.5. The hatted dart map is a bijection, with the
inverse induced by the inverse marked isomorphism. -/
@[expose] noncomputable def rMinus_rightSideMarkedIso_dartEquiv8
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N) :
    {z : ℕ × Bool // z.1 ∈ M.edges} ≃ {z : ℕ × Bool // z.1 ∈ N.edges} where
  toFun := rMinus_rightSideMarkedIso_dartMap phi
  invFun := rMinus_rightSideMarkedIso_dartMap (GeometricSideMarkedIso.symm phi)
  left_inv := rMinus_rightSideMarkedIso_dartMap_symm_apply phi
  right_inv := by
    intro d
    rw [← rMinus_rightSideMarkedIso_symm_symm8 phi]
    exact rMinus_rightSideMarkedIso_dartMap_symm_apply
      (GeometricSideMarkedIso.symm phi) d

/-- Helper toward Lemma 5.5. Extending the hatted first-return rotation by
the identity outside the hatted block commutes with glued-dart transport. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedExtend
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : RMinusCodeGluedDart (kmswStage w n)
      (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      ((rMinusHattedRotation x q).extendDomain
        (Equiv.ofInjective _
          (rMinusCodeHattedDart_injective w n q)) d) =
    (rMinusHattedRotation x q').extendDomain
      (Equiv.ofInjective _ (rMinusCodeHattedDart_injective w n q'))
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi
        (kmswStage w n) d) := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
  let f := rMinusCodeHattedDart (kmswStage w n) (rMinusCoherentRightSide x q)
  let g := rMinusCodeHattedDart (kmswStage w n) (rMinusCoherentRightSide x q')
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image (rMinusHattedRotation x q)
      (Equiv.ofInjective f (rMinusCodeHattedDart_injective w n q)) a
    change (rMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective f (rMinusCodeHattedDart_injective w n q)) (f a) =
        f (rMinusHattedRotation x q a) at hs
    rw [hs]
    change T (f (rMinusHattedRotation x q a)) =
      (rMinusHattedRotation x q').extendDomain
        (Equiv.ofInjective g (rMinusCodeHattedDart_injective w n q')) (T (f a))
    rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_hatted,
      rMinus_rightSideMarkedIso_gluedDartEquiv8_hatted,
      rMinus_rightSideMarkedIso_hattedRotation8]
    exact (Equiv.Perm.extendDomain_apply_image (rMinusHattedRotation x q')
      (Equiv.ofInjective g (rMinusCodeHattedDart_injective w n q'))
      (rMinus_rightSideMarkedIso_dartMap phi a)).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := (rMinus_rightSideMarkedIso_dartEquiv8 phi).surjective b
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_hatted]
      change g (rMinus_rightSideMarkedIso_dartMap phi a) = T d
      rw [show rMinus_rightSideMarkedIso_dartMap phi a = b from ha]
      exact hb
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. The extended finite-prefix rotation commutes
with glued-dart transport, which fixes every prefix representative. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixExtend
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : RMinusCodeGluedDart (kmswStage w n)
      (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      ((stageRot w n).extendDomain
        (Equiv.ofInjective _
          (rMinusCodePrefixDart_injective w n q)) d) =
    (stageRot w n).extendDomain
      (Equiv.ofInjective _ (rMinusCodePrefixDart_injective w n q'))
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi
        (kmswStage w n) d) := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
  let f := rMinusCodePrefixDart (kmswStage w n) (rMinusCoherentRightSide x q)
  let g := rMinusCodePrefixDart (kmswStage w n) (rMinusCoherentRightSide x q')
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image (stageRot w n)
      (Equiv.ofInjective f (rMinusCodePrefixDart_injective w n q)) a
    change (stageRot w n).extendDomain
      (Equiv.ofInjective f (rMinusCodePrefixDart_injective w n q)) (f a) =
        f (stageRot w n a) at hs
    rw [hs]
    change T (f (stageRot w n a)) =
      (stageRot w n).extendDomain
        (Equiv.ofInjective g (rMinusCodePrefixDart_injective w n q')) (T (f a))
    rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix,
      rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix]
    exact (Equiv.Perm.extendDomain_apply_image (stageRot w n)
      (Equiv.ofInjective g (rMinusCodePrefixDart_injective w n q')) a).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨a, ha⟩
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix]
      exact ha
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. Every indexed finite-interface boundary port
is fixed as a dart representative by the glued-dart equivalence. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryPort
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : StageDart ((kmswStage w n).active :: (kmswStage w n).UR).length) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusCodeBoundaryDart w n (rMinusCoherentRightSide x q) d) =
    rMinusCodeBoundaryDart w n (rMinusCoherentRightSide x q') d := by
  rw [rMinusCodeBoundaryDart_eq_prefix,
    rMinusCodeBoundaryDart_eq_prefix]
  exact rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix x q q' phi w n _

/-- Helper toward Lemma 5.5. The finite-interface corner correction,
extended by the identity elsewhere, commutes with glued-dart transport. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryExtend
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : RMinusCodeGluedDart (kmswStage w n)
      (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      ((rMinusBoundaryCornerPerm
        ((kmswStage w n).active :: (kmswStage w n).UR).length).extendDomain
        (Equiv.ofInjective _ (rMinusCodeBoundaryDart_injective w n q)) d) =
    (rMinusBoundaryCornerPerm
      ((kmswStage w n).active :: (kmswStage w n).UR).length).extendDomain
      (Equiv.ofInjective _ (rMinusCodeBoundaryDart_injective w n q'))
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi
        (kmswStage w n) d) := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
  let f := rMinusCodeBoundaryDart w n (rMinusCoherentRightSide x q)
  let g := rMinusCodeBoundaryDart w n (rMinusCoherentRightSide x q')
  let C := rMinusBoundaryCornerPerm
    ((kmswStage w n).active :: (kmswStage w n).UR).length
  by_cases hd : d ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hd
    have hs := Equiv.Perm.extendDomain_apply_image C
      (Equiv.ofInjective f (rMinusCodeBoundaryDart_injective w n q)) a
    change C.extendDomain
      (Equiv.ofInjective f (rMinusCodeBoundaryDart_injective w n q)) (f a) =
        f (C a) at hs
    rw [hs]
    change T (f (C a)) =
      C.extendDomain
        (Equiv.ofInjective g (rMinusCodeBoundaryDart_injective w n q')) (T (f a))
    rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryPort,
      rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryPort]
    exact (Equiv.Perm.extendDomain_apply_image C
      (Equiv.ofInjective g (rMinusCodeBoundaryDart_injective w n q')) a).symm
  · have ht : T d ∉ Set.range g := by
      rintro ⟨a, ha⟩
      apply hd
      refine ⟨a, T.injective ?_⟩
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryPort]
      exact ha
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ ht]

/-- Helper toward Lemma 5.5. The three-factor code splice is conjugated by
the glued-dart equivalence. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_splice
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : RMinusCodeGluedDart (kmswStage w n)
      (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusCodeSpliceRotation w n q d) =
    rMinusCodeSpliceRotation w n q'
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi
        (kmswStage w n) d) := by
  simp only [rMinusCodeSpliceRotation, Equiv.Perm.mul_apply]
  rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedExtend,
    rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryExtend,
    rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixExtend]

/-- Helper toward Lemma 5.5. The local initial swap is natural under dart
transport, so the complete q-dependent adjusted rotations are conjugate. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_adjustedRotation
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n : ℕ)
    (d : RMinusCodeGluedDart (kmswStage w n)
      (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusCodeInitialAdjustedRotation w n q d) =
    rMinusCodeInitialAdjustedRotation w n q'
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi
        (kmswStage w n) d) := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  let i : Fin ((kmswStage w n).active :: (kmswStage w n).UR).length :=
    ⟨0, by simp only [List.length_cons]; omega⟩
  let c := rMinusCodeBoundaryDart w n M (i, false)
  let c' := rMinusCodeBoundaryDart w n N (i, false)
  let p := rMinusPrefixBoundaryDart w n (i, false)
  let b := rMinusCodePrefixDart (kmswStage w n) M (stageRot w n p)
  let b' := rMinusCodePrefixDart (kmswStage w n) N (stageRot w n p)
  have hc : T c = c' :=
    rMinus_rightSideMarkedIso_gluedDartEquiv8_boundaryPort x q q' phi w n (i, false)
  have hb : T b = b' :=
    rMinus_rightSideMarkedIso_gluedDartEquiv8_prefix x q q' phi w n _
  have hswap (e : RMinusCodeGluedDart (kmswStage w n) M) :
      T (Equiv.swap c b e) = Equiv.swap c' b' (T e) := by
    rw [T.injective.map_swap, hc, hb]
  change T (Equiv.swap c b
      (rMinusCodeSpliceRotation w n q (Equiv.swap c b d))) =
    Equiv.swap c' b'
      (rMinusCodeSpliceRotation w n q'
        (Equiv.swap c' b' (T d)))
  rw [hswap, rMinus_rightSideMarkedIso_gluedDartEquiv8_splice, hswap]

/-- Helper toward Lemma 5.5. The glued face-successor relation is preserved
on prefix and hatted representatives. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_faceNextForward
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : RMinusCodeGluedDart F (rMinusCoherentRightSide x q))
    (hab : rMinusCodeFaceNext F (rMinusCoherentRightSide x q) a b) :
    rMinusCodeFaceNext F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F a)
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F b) := by
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
  rcases hab with ⟨p, r, hpr, hpa, hrb⟩ | ⟨p, r, hpr, hpa, hrb⟩
  · apply Or.inl
    refine ⟨p, r, hpr, ?_, ?_⟩
    · calc
        rMinusCodePrefixDart F (rMinusCoherentRightSide x q') p =
            T (rMinusCodePrefixDart F (rMinusCoherentRightSide x q) p) :=
              (rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks
                x q q' phi F p).symm
        _ = T a := congrArg T hpa
    · calc
        rMinusCodePrefixDart F (rMinusCoherentRightSide x q') r =
            T (rMinusCodePrefixDart F (rMinusCoherentRightSide x q) r) :=
              (rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks
                x q q' phi F r).symm
        _ = T b := congrArg T hrb
  · let p' := rMinus_rightSideMarkedIso_dartMap phi p
    let r' := rMinus_rightSideMarkedIso_dartMap phi r
    have hface := (rMinus_rightSideMarkedIso_faceNext phi p r).mp hpr
    apply Or.inr
    refine ⟨p', r', hface, ?_, ?_⟩
    · calc
        rMinusCodeHattedDart F (rMinusCoherentRightSide x q') p' =
            T (rMinusCodeHattedDart F (rMinusCoherentRightSide x q) p) :=
              (rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks
                x q q' phi F p).symm
        _ = T a := congrArg T hpa
    · calc
        rMinusCodeHattedDart F (rMinusCoherentRightSide x q') r' =
            T (rMinusCodeHattedDart F (rMinusCoherentRightSide x q) r) :=
              (rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks
                x q q' phi F r).symm
        _ = T b := congrArg T hrb

/-- Helper toward Lemma 5.5. The glued face-successor relation is preserved
and reflected by the dart equivalence. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_faceNext
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a b : RMinusCodeGluedDart F (rMinusCoherentRightSide x q)) :
    rMinusCodeFaceNext F (rMinusCoherentRightSide x q) a b ↔
      rMinusCodeFaceNext F (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F a)
        (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F b) := by
  constructor
  · exact rMinus_rightSideMarkedIso_gluedDartEquiv8_faceNextForward
      x q q' phi F a b
  · intro h
    have hs := rMinus_rightSideMarkedIso_gluedDartEquiv8_faceNextForward
      x q' q (GeometricSideMarkedIso.symm phi) F
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F a)
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F b) h
    have hsa := rMinus_rightSideMarkedIso_rawDartQuotMap8_symm_apply
      x q q' phi F a
    have hsb := rMinus_rightSideMarkedIso_rawDartQuotMap8_symm_apply
      x q q' phi F b
    change rMinusCodeFaceNext F (rMinusCoherentRightSide x q)
      (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q' q
        (GeometricSideMarkedIso.symm phi) F
        (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F a))
      (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q' q
        (GeometricSideMarkedIso.symm phi) F
        (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F b)) at hs
    rw [hsa, hsb] at hs
    exact hs

/-- Helper toward Lemma 5.5. The hatted vertex action sends each endpoint
of a hatted edge to the endpoint selected by its transported dart bit. -/
theorem rMinus_rightSideMarkedIso_vertexIdMap_endpoint8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (e : (rMinusCoherentRightSide x q).edges) (s : Bool) :
    rMinus_rightSideMarkedIso_vertexIdMap phi
        (if s then (rMinusCoherentRightSide x q).east e.val
         else (rMinusCoherentRightSide x q).west e.val) =
      if (rMinus_rightSideMarkedIso_dartMap phi ⟨(e.val, s), e.property⟩).val.2
        then (rMinusCoherentRightSide x q').east
          (rMinus_rightSideMarkedIso_dartMap phi ⟨(e.val, s), e.property⟩).val.1
        else (rMinusCoherentRightSide x q').west
          (rMinus_rightSideMarkedIso_dartMap phi ⟨(e.val, s), e.property⟩).val.1 := by
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  have he := geometricSideSubmap_endpoints x renewalTime
    renewalTime_positiveSuccessTime .right q e.val e.property
  have hv : (if s then M.east e.val else M.west e.val) ∈ M.vertices := by
    cases s
    · exact he.1
    · exact he.2
  let v : M.vertices := ⟨if s then M.east e.val else M.west e.val, hv⟩
  let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(e.val, s), e.property⟩
  have h := (phi.relation_iff .incident (.inr d) (.inl v)).mp (by
    simp [geometricSideRelation, d, v, M])
  rw [rMinus_rightSideMarkedIso_dartMap_cell,
    rMinus_rightSideMarkedIso_vertexMap_cell] at h
  have hend :
      (if (rMinus_rightSideMarkedIso_dartMap phi d).val.2 then
        N.east (rMinus_rightSideMarkedIso_dartMap phi d).val.1
       else N.west (rMinus_rightSideMarkedIso_dartMap phi d).val.1) =
        (rMinus_rightSideMarkedIso_vertexMap phi v).val := by
    simpa [geometricSideRelation] using h
  rw [rMinus_rightSideMarkedIso_vertexIdMap_of_mem phi _ hv]
  simpa [v, M, N] using hend.symm

/-- Helper toward Lemma 5.5. The raw endpoint of a hatted dart commutes with
the glued vertex action when the target endpoint bit is transported. -/
theorem rMinus_rightSideMarkedIso_rawDartRepMap8_endpoint
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (a : Sum {e : ℕ // e < F.nextEdge}
      (rMinusCoherentRightSide x q).edges) (s : Bool) :
    rMinus_rightSideMarkedIso_vertexRepMap F phi
        (rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q) s a) =
      rMinusCodeRawEndpoint F (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).2
        (rMinus_rightSideMarkedIso_rawDartRepMap8 F phi a s).1 := by
  cases a with
  | inl a => rfl
  | inr a =>
      let d := rMinus_rightSideMarkedIso_dartMap phi ⟨(a.val, s), a.property⟩
      change Sum.inr (rMinus_rightSideMarkedIso_vertexIdMap phi
          (if s then (rMinusCoherentRightSide x q).east a.val
           else (rMinusCoherentRightSide x q).west a.val)) =
        Sum.inr (if d.val.2 then (rMinusCoherentRightSide x q').east d.val.1
          else (rMinusCoherentRightSide x q').west d.val.1)
      exact congrArg Sum.inr
        (rMinus_rightSideMarkedIso_vertexIdMap_endpoint8 x q q' phi a s)

/-- Helper toward Lemma 5.5. The quotient endpoint vertex of every glued
dart is transported by the induced allocated vertex equivalence. -/
theorem rMinus_rightSideMarkedIso_codeEndpoint8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : RMinusCodeGluedDart F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_rawVertexQuotMap7 x q q' phi F
        (rMinusCodeEndpoint F (rMinusCoherentRightSide x q) d.2 d.1) =
      rMinusCodeEndpoint F (rMinusCoherentRightSide x q')
        (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F d).2
        (rMinus_rightSideMarkedIso_rawDartQuotMap8 x q q' phi F d).1 := by
  rcases d with ⟨e, s⟩
  refine Quotient.inductionOn e ?_
  intro a
  rw [rMinus_rightSideMarkedIso_rawDartQuotMap8_mk]
  cases a with
  | inl a =>
      simp [rMinusCodeEndpoint, rMinusCodeRawEndpoint,
        rMinus_rightSideMarkedIso_rawVertexQuotMap7_inl,
        rMinus_rightSideMarkedIso_rawDartRepMap8]
      rfl
  | inr a =>
      let d' := rMinus_rightSideMarkedIso_dartMap phi ⟨(a.val, s), a.property⟩
      change (⟦Sum.inr (rMinus_rightSideMarkedIso_vertexIdMap phi
          (if s then (rMinusCoherentRightSide x q).east a.val
           else (rMinusCoherentRightSide x q).west a.val))⟧ :
          RMinusCodeRawVertex F (rMinusCoherentRightSide x q')) =
        ⟦Sum.inr (if d'.val.2 then (rMinusCoherentRightSide x q').east d'.val.1
          else (rMinusCoherentRightSide x q').west d'.val.1)⟧
      exact congrArg (fun v =>
        (⟦Sum.inr v⟧ : RMinusCodeRawVertex F (rMinusCoherentRightSide x q')))
        (rMinus_rightSideMarkedIso_vertexIdMap_endpoint8 x q q' phi a s)

/-- Helper toward Lemma 5.5. A present edge-class witness transports to a
present target edge class under the false-dart edge action. -/
theorem rMinus_rightSideMarkedIso_codeEdgePresent8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (e : RMinusCodeGluedEdge F (rMinusCoherentRightSide x q))
    (he : rMinusCodeEdgePresent F (rMinusCoherentRightSide x q) e) :
    rMinusCodeEdgePresent F (rMinusCoherentRightSide x q')
      (rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F (e, false)).1 := by
  let M := rMinusCoherentRightSide x q
  let N := rMinusCoherentRightSide x q'
  let T := rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
  revert he
  refine Quotient.inductionOn e ?_
  intro rep he
  rcases he with ⟨a, ha, hclass⟩ | ⟨a, ha, hclass⟩
  · refine Or.inl ⟨a, ha, ?_⟩
    let d : StageDart F.nextEdge := (⟨a.val, a.property⟩, false)
    have hrep : rMinusCodePrefixDart F M d = (⟦Sum.inl a⟧, false) := rfl
    have hp : (⟦Sum.inl a⟧, false) = (⟦rep⟧, false) := Prod.ext hclass rfl
    have hmap := congrArg T hp
    dsimp only [T] at hmap
    rw [← hrep] at hmap
    rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks] at hmap
    exact congrArg Prod.fst hmap
  · let d : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(a.val, false), a.property⟩
    let d' := rMinus_rightSideMarkedIso_dartMap phi d
    have hpres := (rMinus_rightSideMarkedIso_oriented phi d).mp ⟨ha, rfl⟩
    refine Or.inr ⟨⟨d'.val.1, d'.property⟩, hpres.1, ?_⟩
    have hrep : rMinusCodeHattedDart F M d = (⟦Sum.inr a⟧, false) := rfl
    have hp : (⟦Sum.inr a⟧, false) = (⟦rep⟧, false) := Prod.ext hclass rfl
    have hmap := congrArg T hp
    dsimp only [T] at hmap
    rw [← hrep] at hmap
    rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks] at hmap
    exact congrArg Prod.fst hmap

/-- Helper toward Lemma 5.5. The glued-dart equivalence preserves the full
decoded exterior boundary, including its finite-prefix/hatted-tail join. -/
theorem rMinus_rightSideMarkedIso_decodedBoundary8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n i : ℕ) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusDecodedBoundary w n q i) = rMinusDecodedBoundary w n q' i := by
  by_cases hi : i < ((kmswStage w n).LL ++ (kmswStage w n).LR).length
  · simp only [rMinusDecodedBoundary, dite_eq_left hi,
      rMinus_rightSideMarkedIso_gluedDartEquiv8_prefixOfBlocks]
  · simp only [rMinusDecodedBoundary, dite_eq_right hi,
      rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks]
    apply congrArg (rMinusCodeHattedDart (kmswStage w n)
      (rMinusCoherentRightSide x q'))
    apply Subtype.ext
    exact rMinus_rightSideMarkedIso_dartMap_boundary x q q' phi _

/-- Helper toward Lemma 5.5. The glued-dart equivalence preserves every
indexed decoded seam dart. -/
theorem rMinus_rightSideMarkedIso_decodedSeam8
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (w : ℕ → Fin 3) (n i : ℕ) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi (kmswStage w n)
      (rMinusDecodedSeam w n q i) = rMinusDecodedSeam w n q' i := by
  simp only [rMinusDecodedSeam,
    rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks]
  apply congrArg (rMinusCodeHattedDart (kmswStage w n)
    (rMinusCoherentRightSide x q'))
  apply Subtype.ext
  exact rMinus_rightSideMarkedIso_dartMap_seam x q q' phi i

/-- Helper toward Lemma 5.5. The hatted dart action commutes with reversal
of the endpoint bit. -/
theorem rMinus_rightSideMarkedIso_dartMap_reverse8
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (d : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    rMinus_rightSideMarkedIso_dartMap phi
        ⟨(d.val.1, !d.val.2), d.property⟩ =
      ⟨((rMinus_rightSideMarkedIso_dartMap phi d).val.1,
        !(rMinus_rightSideMarkedIso_dartMap phi d).val.2),
        (rMinus_rightSideMarkedIso_dartMap phi d).property⟩ := by
  have hrel : geometricSideRelation M .opposite
      (.inr ⟨(d.val.1, !d.val.2), d.property⟩) (.inr d) := by
    simp [geometricSideRelation]
  have h := (phi.relation_iff .opposite
    (.inr ⟨(d.val.1, !d.val.2), d.property⟩) (.inr d)).mp hrel
  rw [rMinus_rightSideMarkedIso_dartMap_cell,
    rMinus_rightSideMarkedIso_dartMap_cell] at h
  have hp : ((rMinus_rightSideMarkedIso_dartMap phi
      ⟨(d.val.1, !d.val.2), d.property⟩).val.1,
      !(rMinus_rightSideMarkedIso_dartMap phi
        ⟨(d.val.1, !d.val.2), d.property⟩).val.2) =
      (rMinus_rightSideMarkedIso_dartMap phi d).val := by
    simpa only [geometricSideRelation] using h
  apply Subtype.ext
  apply Prod.ext
  · exact (Prod.mk.inj hp).1
  · have hb := (Prod.mk.inj hp).2
    cases hm : (rMinus_rightSideMarkedIso_dartMap phi
        ⟨(d.val.1, !d.val.2), d.property⟩).val.2 <;>
      cases hs : (rMinus_rightSideMarkedIso_dartMap phi d).val.2 <;>
      simp_all

/-- Helper toward Lemma 5.5. The glued-dart equivalence commutes with
reversal of the endpoint bit, including on quotient representatives. -/
theorem rMinus_rightSideMarkedIso_gluedDartEquiv8_reverse
    (x : XDP) (q : Coherent x) (q' : Coherent x)
    (phi : GeometricSideMarkedIso
      (rMinusCoherentRightSide x q) (rMinusCoherentRightSide x q'))
    (F : State) (d : RMinusCodeGluedDart F (rMinusCoherentRightSide x q)) :
    rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F (d.1, !d.2) =
      ((rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).1,
        !(rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F d).2) := by
  rcases d with ⟨e, s⟩
  refine Quotient.inductionOn e ?_
  intro a
  cases a with
  | inl a => rfl
  | inr a =>
      let M := rMinusCoherentRightSide x q
      let N := rMinusCoherentRightSide x q'
      let d₀ : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(a.val, s), a.property⟩
      let d₁ : {z : ℕ × Bool // z.1 ∈ M.edges} := ⟨(a.val, !s), a.property⟩
      change rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
          (rMinusCodeHattedDart F M d₁) =
        ((rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
          (rMinusCodeHattedDart F M d₀)).1,
          !(rMinus_rightSideMarkedIso_gluedDartEquiv8 x q q' phi F
            (rMinusCodeHattedDart F M d₀)).2)
      rw [rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks,
        rMinus_rightSideMarkedIso_gluedDartEquiv8_hattedOfBlocks]
      have h := congrArg (rMinusCodeHattedDart F N)
        (rMinus_rightSideMarkedIso_dartMap_reverse8 phi d₀)
      simpa only [rMinusCodeHattedDart] using h

/-- Helper toward Lemma 5.5. A marked isomorphism sends its distinguished
root vertex to the distinguished root vertex. -/
theorem rMinus_rightSideMarkedIso_vertexMap_root8
    {M N : GeometricSideSubmap} (phi : GeometricSideMarkedIso M N)
    (v : M.vertices) (hv : v.val = M.root) :
    (rMinus_rightSideMarkedIso_vertexMap phi v).val = N.root := by
  have hsrc : geometricSideRelation M .root (.inl v) (.inl v) := by
    change v.val = M.root
    exact hv
  have h := (phi.relation_iff .root (.inl v) (.inl v)).mp hsrc
  rw [rMinus_rightSideMarkedIso_vertexMap_cell] at h
  exact h
























end DirectedDistances.PaperProofs.Section5
