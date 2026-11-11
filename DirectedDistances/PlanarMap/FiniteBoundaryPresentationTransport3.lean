/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PlanarMap.FiniteBoundaryPresentationTransport2
public import DirectedDistances.PlanarMap.Definition32OrientedSideTransport2

/-! # Oriented transport of finite boundary presentations

Helpers toward Definition 3.2. -/

public section

noncomputable section

namespace DirectedDistances.PlanarMap

variable {V E V' E' : Type*}
variable {M : DirectedPlaneMapWithMissing V E}
variable {M' : DirectedPlaneMapWithMissing V' E'}

/-- Helper toward Definition 3.2: the data carried by one upper-left dart. -/
private def ULBoundaryDartData (M : DirectedPlaneMapWithMissing V E)
    (d : E × Bool) : Prop :=
  ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
    d.2 = M.forward ⟨d.1, hp⟩ ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
        LeftOf M F ⟨d.1, hp⟩

/-- Helper toward Definition 3.2: upper-left dart data transports. -/
private theorem ulBoundaryDartData_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M') (d : E × Bool) :
    ULBoundaryDartData M' (e.toHomeoEquiv.mapDart d) ↔
      ULBoundaryDartData M d := by
  unfold ULBoundaryDartData
  constructor
  · rintro ⟨hp', hdir', F', hF', hleft'⟩
    have hp : ¬ M.toPlaneMapWithMissing.missing d.1 :=
      (e.toHomeoEquiv.drawing.missing_map d.1).not.mp (by
        simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hp')
    let dp : PresentEdge M := ⟨d.1, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hdp' : dp' = ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hf := e.toHomeoEquiv.forward_map dp
    change M'.forward dp' = M.forward dp at hf
    rw [hdp'] at hf
    have hdir : d.2 = M.forward dp := by
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using
        hdir'.trans hf
    have hUL' : dp' ∈ UL M' := by
      rw [hdp']
      exact ⟨F', hF', hleft'⟩
    have hUL : dp ∈ UL M := by
      exact (mem_UL_oriented_transport_iff e dp).mpr hUL'
    rcases hUL with ⟨F, hF, hleft⟩
    exact ⟨hp, hdir, F, hF, hleft⟩
  · rintro ⟨hp, hdir, F, hF, hleft⟩
    let dp : PresentEdge M := ⟨d.1, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hp' : ¬ M'.toPlaneMapWithMissing.missing (e.toHomeoEquiv.mapDart d).1 := by
      change ¬ M'.toPlaneMapWithMissing.missing
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
      exact dp'.2
    have hdp' : dp' = ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hUL : dp ∈ UL M := ⟨F, hF, hleft⟩
    have hUL' : dp' ∈ UL M' := (mem_UL_oriented_transport_iff e dp).mp hUL
    rcases hUL' with ⟨F', hF', hleft'⟩
    have hf := e.toHomeoEquiv.forward_map dp
    change M'.forward dp' = M.forward dp at hf
    have hdir' : (e.toHomeoEquiv.mapDart d).2 =
        M'.forward ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      have hdir₀ : d.2 = M'.forward dp' := by
        simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using
          hdir.trans hf.symm
      rw [hdp'] at hdir₀
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hdir₀
    have hleft'' : LeftOf M' F' ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      rw [hdp'] at hleft'
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hleft'
    exact ⟨hp', hdir', F', hF', hleft''⟩

/-- Helper toward Definition 3.2: the data carried by one lower-right dart. -/
private def LRBoundaryDartData (M : DirectedPlaneMapWithMissing V E)
    (d : E × Bool) : Prop :=
  ∃ hp : ¬ M.toPlaneMapWithMissing.missing d.1,
    d.2 = !(M.forward ⟨d.1, hp⟩) ∧
      ∃ F : PlaneGraphDrawing.Face (Drawing M), (Drawing M).IsExternal F ∧
        RightOf M F ⟨d.1, hp⟩

/-- Helper toward Definition 3.2: lower-right dart data transports. -/
private theorem lrBoundaryDartData_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M') (d : E × Bool) :
    LRBoundaryDartData M' (e.toHomeoEquiv.mapDart d) ↔
      LRBoundaryDartData M d := by
  unfold LRBoundaryDartData
  constructor
  · rintro ⟨hp', hdir', F', hF', hright'⟩
    have hp : ¬ M.toPlaneMapWithMissing.missing d.1 :=
      (e.toHomeoEquiv.drawing.missing_map d.1).not.mp (by
        simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hp')
    let dp : PresentEdge M := ⟨d.1, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hdp' : dp' = ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hf := e.toHomeoEquiv.forward_map dp
    change M'.forward dp' = M.forward dp at hf
    rw [hdp'] at hf
    have hdir : d.2 = !(M.forward dp) := by
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using
        hdir'.trans (congrArg (fun b : Bool => !b) hf)
    have hLR' : dp' ∈ LR M' := by
      rw [hdp']
      exact ⟨F', hF', hright'⟩
    have hLR : dp ∈ LR M :=
      (mem_LR_oriented_transport_iff e dp).mpr hLR'
    rcases hLR with ⟨F, hF, hright⟩
    exact ⟨hp, hdir, F, hF, hright⟩
  · rintro ⟨hp, hdir, F, hF, hright⟩
    let dp : PresentEdge M := ⟨d.1, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hp' : ¬ M'.toPlaneMapWithMissing.missing (e.toHomeoEquiv.mapDart d).1 := by
      change ¬ M'.toPlaneMapWithMissing.missing
        (e.toHomeoEquiv.drawing.drawing.σE d.1)
      exact dp'.2
    have hdp' : dp' = ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hLR : dp ∈ LR M := ⟨F, hF, hright⟩
    have hLR' : dp' ∈ LR M' := (mem_LR_oriented_transport_iff e dp).mp hLR
    rcases hLR' with ⟨F', hF', hright'⟩
    have hf := e.toHomeoEquiv.forward_map dp
    change M'.forward dp' = M.forward dp at hf
    have hdir' : (e.toHomeoEquiv.mapDart d).2 =
        !(M'.forward ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩) := by
      have hdir₀ : d.2 = !(M'.forward dp') := by
        exact hdir.trans (congrArg (fun b : Bool => !b) hf.symm)
      rw [hdp'] at hdir₀
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hdir₀
    have hright'' : RightOf M' F' ⟨(e.toHomeoEquiv.mapDart d).1, hp'⟩ := by
      rw [hdp'] at hright'
      simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.mapDart] using hright'
    exact ⟨hp', hdir', F', hF', hright''⟩

/-- Helper toward Definition 3.2: the upper-left boundary condition is
preserved in both directions by oriented transport. -/
theorem ULOk_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    ULOk (e.toHomeoEquiv.pushforward P) ↔ ULOk P := by
  rw [ULOk_iff (P := e.toHomeoEquiv.pushforward P),
    DirectedPlaneMapWithMissing.HomeoEquiv.ul_pushforward,
    ULOk_iff (P := P)]
  constructor
  · intro h d hd
    exact (ulBoundaryDartData_oriented_pushforward_iff e d).mp
      (h (e.toHomeoEquiv.mapDart d)
        (List.mem_map.mpr ⟨d, hd, rfl⟩))
  · intro h d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, hEq⟩
    subst d
    exact (ulBoundaryDartData_oriented_pushforward_iff e d₀).mpr (h d₀ hd₀)

/-- Helper toward Definition 3.2: the lower-right boundary condition is
preserved in both directions by oriented transport. -/
theorem LROk_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    LROk (e.toHomeoEquiv.pushforward P) ↔ LROk P := by
  rw [LROk_iff (P := e.toHomeoEquiv.pushforward P),
    DirectedPlaneMapWithMissing.HomeoEquiv.lr_pushforward,
    LROk_iff (P := P)]
  constructor
  · intro h d hd
    exact (lrBoundaryDartData_oriented_pushforward_iff e d).mp
      (h (e.toHomeoEquiv.mapDart d)
        (List.mem_map.mpr ⟨d, hd, rfl⟩))
  · intro h d hd
    rcases List.mem_map.mp hd with ⟨d₀, hd₀, hEq⟩
    subst d
    exact (lrBoundaryDartData_oriented_pushforward_iff e d₀).mpr (h d₀ hd₀)

/-- Helper toward Definition 3.2: an edge has external faces on both sides. -/
private def BothSidesBoundaryDart (M : DirectedPlaneMapWithMissing V E)
    (a : E) : Prop :=
  ∃ hp : ¬ M.toPlaneMapWithMissing.missing a,
    ∃ F G : PlaneGraphDrawing.Face (Drawing M),
      (Drawing M).IsExternal F ∧ (Drawing M).IsExternal G ∧
        LeftOf M F ⟨a, hp⟩ ∧ RightOf M G ⟨a, hp⟩

/-- Helper toward Definition 3.2: paired external-side data transports. -/
private theorem bothSidesBoundaryDart_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M') (a : E) :
    BothSidesBoundaryDart M' (e.toHomeoEquiv.drawing.drawing.σE a) ↔
      BothSidesBoundaryDart M a := by
  unfold BothSidesBoundaryDart
  constructor
  · rintro ⟨hp', F', G', hF', hG', hleft', hright'⟩
    have hp : ¬ M.toPlaneMapWithMissing.missing a :=
      (e.toHomeoEquiv.drawing.missing_map a).not.mp hp'
    let dp : PresentEdge M := ⟨a, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hdp' : dp' = ⟨e.toHomeoEquiv.drawing.drawing.σE a, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hUL' : dp' ∈ UL M' := by
      rw [hdp']
      exact ⟨F', hF', hleft'⟩
    have hLR' : dp' ∈ LR M' := by
      rw [hdp']
      exact ⟨G', hG', hright'⟩
    have hUL : dp ∈ UL M := (mem_UL_oriented_transport_iff e dp).mpr hUL'
    have hLR : dp ∈ LR M := (mem_LR_oriented_transport_iff e dp).mpr hLR'
    rcases hUL with ⟨F, hF, hleft⟩
    rcases hLR with ⟨G, hG, hright⟩
    exact ⟨hp, F, G, hF, hG, hleft, hright⟩
  · rintro ⟨hp, F, G, hF, hG, hleft, hright⟩
    let dp : PresentEdge M := ⟨a, hp⟩
    let dp' := e.toHomeoEquiv.presentEdgeMap dp
    have hp' : ¬ M'.toPlaneMapWithMissing.missing
        (e.toHomeoEquiv.drawing.drawing.σE a) := dp'.2
    have hdp' : dp' = ⟨e.toHomeoEquiv.drawing.drawing.σE a, hp'⟩ := by
      apply Subtype.ext
      rfl
    have hUL : dp ∈ UL M := ⟨F, hF, hleft⟩
    have hLR : dp ∈ LR M := ⟨G, hG, hright⟩
    have hUL' : dp' ∈ UL M' := (mem_UL_oriented_transport_iff e dp).mp hUL
    have hLR' : dp' ∈ LR M' := (mem_LR_oriented_transport_iff e dp).mp hLR
    rcases hUL' with ⟨F', hF', hleft'⟩
    rcases hLR' with ⟨G', hG', hright'⟩
    rw [hdp'] at hleft' hright'
    exact ⟨hp', F', G', hF', hG', hleft', hright'⟩

/-- Helper toward Definition 3.2: word coverage transports by the edge map. -/
private theorem boundaryWordListedEdge_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) (a : E) :
    (∃ b : Bool, (a, b) ∈ P.word) ↔
      (∃ b : Bool,
        (e.toHomeoEquiv.drawing.drawing.σE a, b)
          ∈ (e.toHomeoEquiv.pushforward P).word) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [DirectedPlaneMapWithMissing.HomeoEquiv.pushforward_word]
    exact List.mem_map.mpr ⟨(a, b), hb, rfl⟩
  · rintro ⟨b, hb⟩
    rw [DirectedPlaneMapWithMissing.HomeoEquiv.pushforward_word] at hb
    rcases List.mem_map.mp hb with ⟨d, hd, heq⟩
    refine ⟨d.2, ?_⟩
    have hedge : e.toHomeoEquiv.drawing.drawing.σE d.1 =
        e.toHomeoEquiv.drawing.drawing.σE a := congrArg Prod.fst heq
    have hEdge : d.1 = a := e.toHomeoEquiv.drawing.drawing.σE.injective hedge
    have hpair : d = (a, d.2) := by
      apply Prod.ext
      · exact hEdge
      · rfl
    rw [← hpair]
    exact hd

/-- Helper toward Definition 3.2: the multiplicity of an edge in a word. -/
private noncomputable def boundaryEdgeMultiplicity
    (word : List (E × Bool)) (a : E) : ℕ := by
  classical
  exact (word.filter (fun d => decide (d.1 = a))).length

/-- Helper toward Definition 3.2: edge multiplicities are preserved. -/
private theorem boundaryWordEdgeMultiplicity_oriented_pushforward_eq
    (e : OrientedMissingHomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) (a : E) :
    boundaryEdgeMultiplicity (e.toHomeoEquiv.pushforward P).word
      (e.toHomeoEquiv.drawing.drawing.σE a) =
      boundaryEdgeMultiplicity P.word a := by
  classical
  let f := e.toHomeoEquiv
  have hcount : ∀ l : List (E × Bool),
      ((l.map f.mapDart).filter
        (fun d => decide (d.1 = f.drawing.drawing.σE a))).length =
        ((l.filter (fun d => decide (d.1 = a))).length) := by
    intro l
    induction l with
    | nil => simp
    | cons d ds ih =>
        have heq : decide ((f.mapDart d).1 = f.drawing.drawing.σE a) =
            decide (d.1 = a) := by
          change decide (f.drawing.drawing.σE d.1 =
            f.drawing.drawing.σE a) = decide (d.1 = a)
          by_cases h : d.1 = a
          · simp [h]
          · have h' : f.drawing.drawing.σE d.1 ≠
                f.drawing.drawing.σE a := by
              intro he
              exact h (f.drawing.drawing.σE.injective he)
            simp [h, h']
        simp only [List.map_cons, List.filter_cons, heq]
        by_cases h : d.1 = a <;> simp [h, ih]
  simpa only [DirectedPlaneMapWithMissing.HomeoEquiv.pushforward_word,
    boundaryEdgeMultiplicity] using hcount P.word

/-- Helper toward Definition 3.2: the boundary-order predicate is preserved
in both directions by oriented transport. -/
theorem IsBoundaryOrderOf_oriented_pushforward_iff
    (e : OrientedMissingHomeoEquiv M M')
    (P : FiniteBoundaryPresentation M) :
    IsBoundaryOrderOf M' (e.toHomeoEquiv.pushforward P) ↔ IsBoundaryOrderOf M P := by
  classical
  rw [IsBoundaryOrderOf_iff M' (e.toHomeoEquiv.pushforward P),
    IsBoundaryOrderOf_iff M P]
  constructor
  · rintro ⟨hcover', hmult'⟩
    refine ⟨?_, ?_⟩
    · intro a
      exact (boundaryWordListedEdge_oriented_pushforward_iff e P a).trans
        ((hcover' (e.toHomeoEquiv.drawing.drawing.σE a)).trans
          (DirectedPlaneMapWithMissing.HomeoEquiv.externalFrontierEdge_pushforward_iff
            e.toHomeoEquiv a))
    · intro a
      rcases hmult' (e.toHomeoEquiv.drawing.drawing.σE a) with
        ⟨hbound', hdouble'⟩
      have hcount :
          ((e.toHomeoEquiv.pushforward P).word.filter
            (fun d => decide (d.1 = e.toHomeoEquiv.drawing.drawing.σE a))).length =
          (P.word.filter (fun d => decide (d.1 = a))).length := by
        simpa only [boundaryEdgeMultiplicity] using
          boundaryWordEdgeMultiplicity_oriented_pushforward_eq e P a
      constructor
      · rw [← hcount]
        exact hbound'
      · rcases hdouble' with hsmall' | hboth'
        · exact Or.inl (by rw [← hcount]; exact hsmall')
        · exact Or.inr
            ((bothSidesBoundaryDart_oriented_pushforward_iff e a).mp hboth')
  · rintro ⟨hcover, hmult⟩
    refine ⟨?_, ?_⟩
    · intro a'
      let a := e.toHomeoEquiv.drawing.drawing.σE.symm a'
      have ha : e.toHomeoEquiv.drawing.drawing.σE a = a' := by simp [a]
      rw [← ha]
      exact (boundaryWordListedEdge_oriented_pushforward_iff e P a).symm.trans
        ((hcover a).trans
          (DirectedPlaneMapWithMissing.HomeoEquiv.externalFrontierEdge_pushforward_iff
            e.toHomeoEquiv a).symm)
    · intro a'
      let a := e.toHomeoEquiv.drawing.drawing.σE.symm a'
      have ha : e.toHomeoEquiv.drawing.drawing.σE a = a' := by simp [a]
      rw [← ha]
      rcases hmult a with ⟨hbound, hdouble⟩
      have hcount :
          ((e.toHomeoEquiv.pushforward P).word.filter
            (fun d => decide (d.1 = e.toHomeoEquiv.drawing.drawing.σE a))).length =
          (P.word.filter (fun d => decide (d.1 = a))).length := by
        simpa only [boundaryEdgeMultiplicity] using
          boundaryWordEdgeMultiplicity_oriented_pushforward_eq e P a
      constructor
      · rw [hcount]
        exact hbound
      · rcases hdouble with hsmall | hboth
        · exact Or.inl (by rw [hcount]; exact hsmall)
        · exact Or.inr
            ((bothSidesBoundaryDart_oriented_pushforward_iff e a).mpr hboth)

end DirectedDistances.PlanarMap

end
