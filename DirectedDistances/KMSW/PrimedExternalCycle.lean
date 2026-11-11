/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.PrimedExteriorOrbit
import DirectedDistances.KMSW.GluingBoundaryOrder
import DirectedDistances.KMSW.RunInfDartPartition
import DirectedDistances.Recursive.HLRLdpFinal

/-! # The primed external cycle

Helpers toward Lemma 5.13, with C18 and initial triangle convention.
Missing boundary edges retain their geometric darts without an orientation. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap Set
open scoped Topology



private theorem external_LL_index_persists (u : ℕ → Fin 3) (a b i : ℕ)
    (hab : a ≤ b) (hi : i < (kmswStage u a).LL.reverse.length) :
    (kmswStage u b).LL.reverse[i]? = (kmswStage u a).LL.reverse[i]? := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hib : i < (kmswStage u b).LL.reverse.length := by
      have hs := List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      rw [← ih] at hs
      exact (List.getElem?_eq_some_iff.mp hs).1
    generalize hc : u b = c
    fin_cases c
    · cases hp : (kmswStage u b).UL.dropLast.reverse with
      | nil =>
        have hs : (kmswStage u (b + 1)).LL.reverse =
            (kmswStage u b).LL.reverse ++ [(kmswStage u b).nextEdge + 1] := by
          simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp, State.addEdge]
        rw [hs, List.getElem?_append_left hib, ih]
      | cons f fs =>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih
    · simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep,
        State.addEdge] using ih
    · cases hp : (kmswStage u b).UR <;>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih



private theorem external_UR_prefix_persists (u : ℕ → Fin 3) (a b i e : ℕ)
    (hab : a ≤ b) (hmissing : ¬ EdgePresent u e)
    (he : (kmswStage u a).UR.reverse[i]? = some e) :
    ∀ j ≤ i, (kmswStage u b).UR.reverse[j]? = (kmswStage u a).UR.reverse[j]? := by
  induction b, hab using Nat.le_induction with
  | base => intro j hj; rfl
  | succ b hab ih =>
    have hie : (kmswStage u b).UR.reverse[i]? = some e := (ih i le_rfl).trans he
    have hi : i < (kmswStage u b).UR.reverse.length :=
      (List.getElem?_eq_some_iff.mp hie).1
    intro j hj
    generalize hc : u b = c
    fin_cases c
    · cases hp : (kmswStage u b).UL.dropLast.reverse <;>
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hp,
          State.addEdge] using ih j hj
    · have hs : (kmswStage u (b + 1)).UR.reverse =
          (kmswStage u b).UR.reverse ++ [(kmswStage u b).nextEdge + 1] := by
        simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, State.addEdge]
      rw [hs, List.getElem?_append_left (by omega), ih j hj]
    · cases hur : (kmswStage u b).UR with
      | nil => rw [hur] at hie; simp only [List.reverse_nil, List.getElem?_nil] at hie
               contradiction
      | cons f fs =>
        have hi' : i < fs.length := by
          by_contra hn
          have hieq : i = fs.length := by
            rw [hur, List.length_reverse, List.length_cons] at hi
            omega
          have hef : e = f := by
            rw [hur, List.reverse_cons, hieq,
              List.getElem?_append_right (by simp), List.length_reverse,
              Nat.sub_self, List.getElem?_cons_zero] at hie
            exact Option.some.inj hie.symm
          apply hmissing
          subst e
          have ha := (kmswStage_boundary_ids_lt_nextEdge u b).2 f (by
            simp only [List.mem_append]
            exact Or.inl (Or.inl (Or.inr (hur ▸ List.mem_cons_self))))
          refine ⟨b + 1, ha.trans_le (kmswStage_nextEdge_mono u (Nat.le_succ b)), ?_⟩
          simp [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur]
        have hh := ih j hj
        rw [hur, List.reverse_cons,
          List.getElem?_append_left (by simp only [List.length_reverse]; omega)] at hh
        simpa [kmswStage, hc, kmswStep, kmswCodeStep, kmswStepOfStep, hur] using hh



private theorem external_word_step (u : ℕ → Fin 3) (n k : ℕ)
    (a b : ℕ × Bool)
    (ha : (stageOuterWordVal u n)[k]? = some a)
    (hb : (stageOuterWordVal u n)[k + 1]? = some b) :
    ∃ d d' : StageDart (kmswStage u n).nextEdge,
      (d.1.val, d.2) = a ∧ (d'.1.val, d'.2) = b ∧
        (kmswMap u n).faceSucc d = d' := by
  have hk := (List.getElem?_eq_some_iff.mp ha).1
  have hk' := (List.getElem?_eq_some_iff.mp hb).1
  obtain ⟨d, d', hd, hd', hf⟩ :=
    outer_faceSucc_exists u n (stageOuterWord_faceSucc u n) k hk
  rw [Nat.mod_eq_of_lt hk'] at hd'
  exact ⟨d, d', Option.some.inj (hd.symm.trans ha),
    Option.some.inj (hd'.symm.trans hb), hf⟩



private theorem external_word_LL (u : ℕ → Fin 3) (n i e : ℕ)
    (hlr : (kmswStage u n).LR = [0])
    (he : (0 :: (kmswStage u n).LL.reverse)[i]? = some e) :
    (stageOuterWordVal u n)[(kmswStage u n).UL.length +
      (kmswStage u n).UR.length + i]? = some (e, true) := by
  rw [stageOuterWordVal_eq_runs, hlr]
  simp only [List.reverse_singleton, List.map_cons, List.map_nil,
    List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  have hidx : (kmswStage u n).UL.length + (kmswStage u n).UR.length + i -
      (kmswStage u n).UL.length - (kmswStage u n).UR.length = i := by omega
  rw [hidx]
  change ((0 :: (kmswStage u n).LL.reverse).map (fun e => (e, true)))[i]? = _
  rw [List.getElem?_map, he]
  rfl



private theorem external_word_UR (u : ℕ → Fin 3) (n i e : ℕ)
    (he : (kmswStage u n).UR.reverse[i]? = some e) :
    (stageOuterWordVal u n)[(kmswStage u n).UL.length +
      ((kmswStage u n).UR.length - 1 - i)]? = some (e, false) := by
  have hi : i < (kmswStage u n).UR.length := by
    simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp he).1
  have he' : (kmswStage u n).UR[(kmswStage u n).UR.length - 1 - i]? = some e := by
    rw [List.getElem?_reverse hi] at he
    exact he
  have h1 : (kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1 - i) <
      (((kmswStage u n).UL.map fun e => (e, false)) ++
        ((kmswStage u n).UR.map fun e => (e, false))).length := by simp; omega
  have h2 : (kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1 - i) <
      ((((kmswStage u n).UL.map fun e => (e, false)) ++
        ((kmswStage u n).UR.map fun e => (e, false))) ++
          ((kmswStage u n).LR.reverse.map fun e => (e, true))).length := by
    simp; omega
  rw [stageOuterWordVal_eq_runs, List.getElem?_append_left h2,
    List.getElem?_append_left h1, List.getElem?_append_right (by simp),
    List.length_map]
  have hidx : (kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1 - i) -
      (kmswStage u n).UL.length = (kmswStage u n).UR.length - 1 - i := by omega
  rw [hidx, List.getElem?_map, he']
  rfl



private theorem external_LL_sameCycle (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (a i e : ℕ)
    (he : (0 :: (kmswStage (primedCode (primedSimInput w) h) a).LL.reverse)[i]? = some e) :
    (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart (e, true) := by
  let u := primedCode (primedSimInput w) h
  let hf := primedCode_finiteIncidence w h hfin
  have hstable (j n : ℕ) (hjn : j < (0 :: (kmswStage u a).LL.reverse).length)
      (hn : a ≤ n) :
      (0 :: (kmswStage u n).LL.reverse)[j]? =
        (0 :: (kmswStage u a).LL.reverse)[j]? := by
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.getElem?_cons_succ]
      exact external_LL_index_persists u a n j hn (by simpa using hjn)
  induction i generalizing e with
  | zero =>
    have he0 : 0 = e := Option.some.inj he
    rw [← he0]
    exact Equiv.Perm.SameCycle.refl _ _
  | succ i ih =>
    have hi : i + 1 < (0 :: (kmswStage u a).LL.reverse).length :=
      (List.getElem?_eq_some_iff.mp he).1
    have hi' : i < (0 :: (kmswStage u a).LL.reverse).length := by omega
    let p := (0 :: (kmswStage u a).LL.reverse)[i]
    have hp : (0 :: (kmswStage u a).LL.reverse)[i]? = some p :=
      List.getElem?_eq_some_iff.mpr ⟨hi', rfl⟩
    have hstep : kmswInfFaceSucc u hf (p, true) = (e, true) := by
      apply kmswInfFaceSucc_eq_of_stages
      refine ⟨a, fun n hn => ?_⟩
      have hp' := (hstable i n hi' hn).trans hp
      have he' := (hstable (i + 1) n hi hn).trans he
      exact external_word_step u n ((kmswStage u n).UL.length +
        (kmswStage u n).UR.length + i) _ _
        (external_word_LL u n i p (primedStage_LR_eq_root w h n) hp')
        (by simpa only [Nat.add_assoc] using
          external_word_LL u n (i + 1) e (primedStage_LR_eq_root w h n) he')
    exact (ih p hp).trans ⟨1, by simpa only [zpow_one] using hstep⟩



private theorem external_UR_sameCycle (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (a i e : ℕ)
    (hmissing : ¬ EdgePresent (primedCode (primedSimInput w) h) e)
    (he : (kmswStage (primedCode (primedSimInput w) h) a).UR.reverse[i]? = some e) :
    (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart (e, false) := by
  let u := primedCode (primedSimInput w) h
  let hf := primedCode_finiteIncidence w h hfin
  let f := kmswInfFaceSucc u hf
  have hstable := external_UR_prefix_persists u a
  have hchain : ∀ j ≤ i, ∀ p, (kmswStage u a).UR.reverse[j]? = some p →
      f.SameCycle futureMapOuterDart (p, false) := by
    intro j
    induction j with
    | zero =>
      intro hj p hp
      have hstep : f (p, false) = futureMapOuterDart := by
        apply kmswInfFaceSucc_eq_of_stages
        refine ⟨a, fun n hn => ?_⟩
        have hp' := (hstable n i e hn hmissing he 0 hj).trans hp
        have hlen : 0 < (kmswStage u n).UR.length := by
          simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hp').1
        refine external_word_step u n ((kmswStage u n).UL.length +
          ((kmswStage u n).UR.length - 1 - 0)) _ _
          (external_word_UR u n 0 p hp') ?_
        have hroot := external_word_LL u n 0 0 (primedStage_LR_eq_root w h n) rfl
        have hidx : (kmswStage u n).UL.length +
            ((kmswStage u n).UR.length - 1 - 0) + 1 =
            (kmswStage u n).UL.length + (kmswStage u n).UR.length + 0 := by omega
        rw [hidx]
        exact hroot
      exact (show f.SameCycle (p, false) futureMapOuterDart from
        ⟨1, by simpa only [zpow_one] using hstep⟩).symm
    | succ j ih =>
      intro hj p hp
      have hpbound := (List.getElem?_eq_some_iff.mp hp).1
      have hjbound : j < (kmswStage u a).UR.reverse.length := by omega
      let q := (kmswStage u a).UR.reverse[j]
      have hq : (kmswStage u a).UR.reverse[j]? = some q :=
        List.getElem?_eq_some_iff.mpr ⟨hjbound, rfl⟩
      have hstep : f (p, false) = (q, false) := by
        apply kmswInfFaceSucc_eq_of_stages
        refine ⟨a, fun n hn => ?_⟩
        have hp' := (hstable n i e hn hmissing he (j + 1) hj).trans hp
        have hq' := (hstable n i e hn hmissing he j (by omega)).trans hq
        have hlen : j + 1 < (kmswStage u n).UR.length := by
          simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hp').1
        refine external_word_step u n ((kmswStage u n).UL.length +
          ((kmswStage u n).UR.length - 1 - (j + 1))) _ _
          (external_word_UR u n (j + 1) p hp') ?_
        have hidx : (kmswStage u n).UL.length +
            ((kmswStage u n).UR.length - 1 - (j + 1)) + 1 =
            (kmswStage u n).UL.length + ((kmswStage u n).UR.length - 1 - j) := by omega
        rw [hidx]
        exact external_word_UR u n j q hq'
      exact (ih (by omega) q hq).trans
        (show f.SameCycle (p, false) (q, false) from
          ⟨1, by simpa only [zpow_one] using hstep⟩).symm
  exact hchain i le_rfl e he



private theorem external_L_unbounded (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hb : BoundaryHitWitnesses w) :
    ∀ a : ℤ, ∃ n, L (primedCode (primedSimInput w) h) n ≤ a := by
  intro a
  let u := primedCode (primedSimInput w) h
  let i := Int.toNat (-a)
  obtain ⟨n, hn⟩ :=
    (DirectedDistances.Recursive.primedEntryOuterLLVertexIdentification_proved w h hb i).exists
  obtain ⟨v, hv, _⟩ := hn
  have hi : i < (kmswStage u n).LL.length := by
    obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hv
    simpa only [List.length_map, List.length_reverse] using hh
  have hlen := kmswStage_LL_length u n
  obtain ⟨j, _, hj⟩ := runningMin_attained (L u) n
  refine ⟨j, ?_⟩
  change minL u n = L u j at hj
  have hai : -a ≤ (i : ℤ) := Int.self_le_toNat (-a)
  change L u j ≤ a
  omega




theorem primedExternalDart_sameCycle_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (d : ℕ × Bool) (hd : limitExternalDart (primedCode (primedSimInput w) h) d) :
    (kmswInfFaceSucc (primedCode (primedSimInput w) h)
      (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d := by
  classical
  let u := primedCode (primedSimInput w) h
  obtain ⟨N, hN⟩ := hd
  obtain ⟨M, hM⟩ := kmswRun_UL_eventually_absent u (external_L_unbounded w h hb) d.1
  have hboundaries (n : ℕ) (hn : max N M ≤ n) :
      (d.2 = false ∧ d.1 ∈ (kmswStage u n).UR) ∨
        (d.2 = true ∧ (d.1 ∈ (kmswStage u n).LL ∨ d.1 = 0)) := by
    obtain ⟨ha, ho⟩ := hN n ((le_max_left _ _).trans hn)
    have hout := (kmswStage_isOuter_iff_boundary u n (⟨d.1, ha⟩, d.2)).mp ho
    simp only [List.mem_append] at hout
    rcases hout with ⟨hs, hUL | hUR⟩ | ⟨hs, hLL | hLR⟩
    · exact (hM n ((le_max_right _ _).trans hn) hUL).elim
    · exact Or.inl ⟨hs, hUR⟩
    · exact Or.inr ⟨hs, Or.inl hLL⟩
    · rw [primedStage_LR_eq_root] at hLR
      exact Or.inr ⟨hs, Or.inr (List.mem_singleton.mp hLR)⟩
  rcases hboundaries (max N M) le_rfl with ⟨hs, hUR⟩ | ⟨hs, hLL | hz⟩
  · have hmissing : ¬ EdgePresent u d.1 := by
      intro hp
      obtain ⟨K, hK⟩ := hp.eventually_present
      let n := max (max N M) K
      obtain ⟨ha, hp⟩ := hK n (le_max_right _ _)
      rcases hboundaries n (le_max_left _ _) with ⟨_, he⟩ | ⟨_, he | he⟩
      · have hm := ((kmswStage_status u n).1 d.1 ha).mpr (Or.inl he)
        rw [hp] at hm
        contradiction
      · have hm := ((kmswStage_status u n).1 d.1 ha).mpr (Or.inr he)
        rw [hp] at hm
        contradiction
      · have hzero : (kmswStage u (max N M)).present 0 = true :=
          (kmswStage_status u (max N M)).2.2.1 0 (by
            rw [primedStage_LR_eq_root]; exact List.mem_singleton_self _)
        have ha0 := (kmswStage_boundary_ids_lt_nextEdge u (max N M)).2 d.1 (by
          simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr hUR)))
        have hm := ((kmswStage_status u (max N M)).1 d.1 ha0).mpr (Or.inl hUR)
        rw [he, hzero] at hm
        contradiction
    obtain ⟨i, hi, hei⟩ := List.getElem_of_mem (List.mem_reverse.mpr hUR)
    have he : (kmswStage u (max N M)).UR.reverse[i]? = some d.1 :=
      List.getElem?_eq_some_iff.mpr ⟨hi, hei⟩
    have hc := external_UR_sameCycle w h hfin (max N M) i d.1 hmissing he
    exact (show (d.1, false) = d from Prod.ext rfl hs.symm) ▸ hc
  · obtain ⟨i, hi, hei⟩ := List.getElem_of_mem (List.mem_reverse.mpr hLL)
    have he : (0 :: (kmswStage u (max N M)).LL.reverse)[i + 1]? = some d.1 := by
      simp only [List.getElem?_cons_succ]
      exact List.getElem?_eq_some_iff.mpr ⟨hi, hei⟩
    have hc := external_LL_sameCycle w h hfin (max N M) (i + 1) d.1 he
    exact (show (d.1, true) = d from Prod.ext rfl hs.symm) ▸ hc
  · have heq : d = futureMapOuterDart := Prod.ext hz hs
    rw [heq]

 
theorem primedExternalOrbitBordersGoal_holds (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) :
    primedExternalOrbitBordersGoal w h hfin hb :=
  (primedExternalOrbitBordersGoal_iff_externalRootCycle w h hfin hb hex).mpr
    (primedExternalDart_sameCycle_root w h hfin hb)



theorem primedExternalDart_iff_sameCycle_root (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    limitExternalDart (primedCode (primedSimInput w) h) d ↔
      (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle futureMapOuterDart d := by
  refine ⟨primedExternalDart_sameCycle_root w h hfin hb d, ?_⟩
  intro hd
  classical
  by_contra hn
  let f := kmswInfFaceSucc (primedCode (primedSimInput w) h)
    (primedCode_finiteIncidence w h hfin)
  have hfinite := (finiteFaceOrbit_iff_not_external _
    (primedCode_finiteIncidence w h hfin) d).mpr hn
  have hsub : {e | f.SameCycle futureMapOuterDart e} ⊆ {e | f.SameCycle d e} :=
    fun _ he => hd.symm.trans he
  exact ((finiteFaceOrbit_iff_not_external _
    (primedCode_finiteIncidence w h hfin) futureMapOuterDart).mp
      (hfinite.subset hsub)) (futureMapOuterDart_external _)



theorem primedDartFace_eq_iff_sameCycle (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) (d e : ℕ × Bool) :
    primedDartFace w h hfin hb d = primedDartFace w h hfin hb e ↔
      (kmswInfFaceSucc (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)).SameCycle d e := by
  refine ⟨?_, primedDartFace_eq_of_sameCycle w h hfin hb d e⟩
  intro heq
  let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
  let F := primedDartFace w h hfin hb d
  have hd : Q.dartBorders (primedGeometricDartEquiv w h hfin hb d) F :=
    (primedDartFace_eq_iff w h hfin hb d F).mp rfl
  have he : Q.dartBorders (primedGeometricDartEquiv w h hfin hb e) F :=
    (primedDartFace_eq_iff w h hfin hb e F).mp heq.symm
  by_cases hF : Q.IsUnbounded F
  · have hdc := primedExternalDart_sameCycle_root w h hfin hb d
      (primedUnboundedFace_border_external w h hfin hb hex F hF d hd)
    have hec := primedExternalDart_sameCycle_root w h hfin hb e
      (primedUnboundedFace_border_external w h hfin hb hex F hF e he)
    exact hdc.symm.trans hec
  · change ¬ ∀ R : ℝ, ∃ z ∈ F.val, R < ‖z‖ at hF
    push Not at hF
    obtain ⟨R, hR⟩ := hF
    have hbdd : Bornology.IsBounded F.val := by
      apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
      exact ⟨R, fun z hz => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hR z hz⟩
    obtain ⟨a, _, ha⟩ := primedBoundedFace_finiteOrbit_border_iff w h hfin hb hex ⟨F, hbdd⟩
    exact ((ha d).mp hd).symm.trans ((ha e).mp he)



@[expose] noncomputable def primedOrbitFace (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    PrimedFaceOrbit w h hfin → (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face :=
  Quotient.lift (primedDartFace w h hfin hb)
    (primedDartFace_eq_of_sameCycle w h hfin hb)



theorem primedOrbitFace_bijective (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) :
    Function.Bijective (primedOrbitFace w h hfin hb) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro d e heq
    exact Quotient.sound ((primedDartFace_eq_iff_sameCycle w h hfin hb hex d e).mp heq)
  · intro F
    obtain ⟨d, hd⟩ := primedRealizedFace_bordered w h hfin hb F
    exact ⟨Quotient.mk _ d, (primedDartFace_eq_iff w h hfin hb d F).mpr hd⟩



@[expose] noncomputable def primedFaceOrbitEquiv (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) :
    PrimedFaceOrbit w h hfin ≃ (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face :=
  Equiv.ofBijective (primedOrbitFace w h hfin hb)
    (primedOrbitFace_bijective w h hfin hb hex)



theorem primedFaceOrbitEquiv_eq_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) (d : ℕ × Bool)
    (F : (mhatPrimeDrawing w hfin hb (monotone_family_all w)).Face) :
    primedFaceOrbitEquiv w h hfin hb hex (Quotient.mk _ d) = F ↔
      (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
        (primedGeometricDartEquiv w h hfin hb d) F :=
  primedDartFace_eq_iff w h hfin hb d F



theorem dartBorders_primedFaceOrbitEquiv_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (d : ℕ × Bool) (q : PrimedFaceOrbit w h hfin) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d) (primedFaceOrbitEquiv w h hfin hb hex q) ↔
        Quotient.mk _ d = q := by
  rw [← primedFaceOrbitEquiv_eq_iff w h hfin hb hex]
  exact (primedFaceOrbitEquiv w h hfin hb hex).injective.eq_iff



theorem primedFaceOrbitEquiv_isUnbounded_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb)
    (q : PrimedFaceOrbit w h hfin) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).IsUnbounded
      (primedFaceOrbitEquiv w h hfin hb hex q) ↔ q = Quotient.mk _ futureMapOuterDart := by
  obtain ⟨U, hU, huniq, hborder⟩ := primedExternalOrbitBordersGoal_holds w h hfin hb hex
  have hr : primedFaceOrbitEquiv w h hfin hb hex (Quotient.mk _ futureMapOuterDart) = U :=
    (primedFaceOrbitEquiv_eq_iff w h hfin hb hex _ U).mpr
      ((hborder _).mpr (Equiv.Perm.SameCycle.refl _ _))
  constructor
  · intro hq
    exact (primedFaceOrbitEquiv w h hfin hb hex).injective ((huniq _ hq).trans hr.symm)
  · intro hq
    rw [hq, hr]
    exact hU



theorem primedFaceOrbitEquiv_exterior_border (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) (d : ℕ × Bool) :
    (mhatPrimeDrawing w hfin hb (monotone_family_all w)).dartBorders
      (primedGeometricDartEquiv w h hfin hb d)
      (primedFaceOrbitEquiv w h hfin hb hex (Quotient.mk _ futureMapOuterDart)) ↔
        limitExternalDart (primedCode (primedSimInput w) h) d := by
  exact (dartBorders_primedFaceOrbitEquiv_iff w h hfin hb hex d
    (Quotient.mk _ futureMapOuterDart)).trans
      ((primedFaceOrbit_mk_eq_iff w h hfin d futureMapOuterDart).trans
        ⟨fun hd => (primedExternalDart_iff_sameCycle_root w h hfin hb d).mpr hd.symm,
          fun hd => ((primedExternalDart_iff_sameCycle_root w h hfin hb d).mp hd).symm⟩)



theorem primedGeometricDartEquiv_vertex (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    kmswLimitDartVertex w (primedGeometricDartEquiv w h hfin hb d).val =
      primedLimitVertexMap w h
        (kmswLimitDartVertex (primedCode (primedSimInput w) h) d) := by
  obtain ⟨e, b⟩ := d
  rcases primedLimitEdgeMap_endpoint_sideflip w h e with ⟨hf, hw, he⟩ | ⟨hf, hw, he⟩
  · cases b <;>
      simp only [primedGeometricDartEquiv_apply, primedLimitDartMap, hf,
        Bool.xor_false, kmswLimitDartVertex, Bool.false_eq_true, ↓reduceIte]
    · exact hw
    · exact he
  · cases b <;>
      simp only [primedGeometricDartEquiv_apply, primedLimitDartMap, hf,
        Bool.false_xor, Bool.true_xor, Bool.not_true, kmswLimitDartVertex,
        Bool.false_eq_true, ↓reduceIte]
    · exact he
    · exact hw



@[expose] noncomputable def primedOrbitVertex (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    RootedLocallyFiniteVertex (ℕ × Bool)
      (kmswInfRot (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin)) →
      RestrictedVertex (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (primeDartSet w hfin hb) :=
  Quotient.lift (fun d => restrictedVertex
    (monotoneFamilyDrawing w hfin (monotone_family_all w))
    (primeDartSet w hfin hb) (primedGeometricDartEquiv w h hfin hb d)) (by
      intro d e hde
      apply Subtype.ext
      change kmswLimitDartVertex w (primedGeometricDartEquiv w h hfin hb d).val =
        kmswLimitDartVertex w (primedGeometricDartEquiv w h hfin hb e).val
      rw [primedGeometricDartEquiv_vertex, primedGeometricDartEquiv_vertex]
      exact congrArg (primedLimitVertexMap w h)
        ((futureMap_sameCycle_iff _ (primedCode_finiteIncidence w h hfin) d e).mp hde))



theorem primedOrbitVertex_bijective (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w) :
    Function.Bijective (primedOrbitVertex w h hfin hb) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro d e heq
    apply Quotient.sound
    apply (futureMap_sameCycle_iff _ (primedCode_finiteIncidence w h hfin) d e).mpr
    have he := congrArg Subtype.val heq
    change kmswLimitDartVertex w (primedGeometricDartEquiv w h hfin hb d).val =
      kmswLimitDartVertex w (primedGeometricDartEquiv w h hfin hb e).val at he
    rw [primedGeometricDartEquiv_vertex, primedGeometricDartEquiv_vertex] at he
    exact (primedLimit_maps_injective_on_allocated w h).2
      ((primedLocalIds_eventually_allocated w h).2 _)
      ((primedLocalIds_eventually_allocated w h).2 _) he
  · rintro ⟨v, d, hd, hv⟩
    let H := primedGeometricDartEquiv w h hfin hb
    let a : {d // d ∈ primeDartSet w hfin hb} := ⟨d, hd⟩
    refine ⟨Quotient.mk _ (H.symm a), ?_⟩
    apply Subtype.ext
    change kmswLimitDartVertex w (H (H.symm a)).val = v
    rw [H.apply_symm_apply]
    exact hv




@[expose] noncomputable def primedRealizedVertexEquiv (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) :
    RootedLocallyFiniteVertex (ℕ × Bool)
      (kmswInfRot (primedCode (primedSimInput w) h) (primedCode_finiteIncidence w h hfin)) ≃
      RestrictedVertex (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (primeDartSet w hfin hb) :=
  Equiv.ofBijective (primedOrbitVertex w h hfin hb) (primedOrbitVertex_bijective w h hfin hb)



theorem primedRealizedVertexEquiv_class (w : ℕ → Fin 3)
    (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
    (hb : BoundaryHitWitnesses w) (d : ℕ × Bool) :
    primedRealizedVertexEquiv w h hfin hb
      (rootedLocallyFiniteVertexClass (kmswInfRot (primedCode (primedSimInput w) h)
        (primedCode_finiteIncidence w h hfin)) d) =
      restrictedVertex (monotoneFamilyDrawing w hfin (monotone_family_all w))
        (primeDartSet w hfin hb) (primedGeometricDartEquiv w h hfin hb d) := rfl







theorem primedRootedMapIdentification (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfin : primedLimitFiniteIncidence w) (hb : BoundaryHitWitnesses w)
    (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb) :
    let u := primedCode (primedSimInput w) h
    let hf := primedCode_finiteIncidence w h hfin
    let ρ := kmswInfRot u hf
    let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
    let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
    let S := primeDartSet w hfin hb
    ∃ (H : (ℕ × Bool) ≃ {d // d ∈ S})
      (V : RootedLocallyFiniteVertex (ℕ × Bool) ρ ≃ RestrictedVertex P S)
      (F : PrimedFaceOrbit w h hfin ≃ Q.Face),
      (∀ d, (H d).val = primedLimitDartMap w h d) ∧
      (∀ d, V (rootedLocallyFiniteVertexClass ρ d) = restrictedVertex P S (H d)) ∧
      (H futureMapRootDart).val = (kmswLLCreatedEdge w (walkNL w h 0), false) ∧
      primeMissingEdge w hfin hb (H futureMapRootDart).val.1 ∧
      ¬ PrimedEdgePresent w h 0 ∧
      (∀ d, d.1 = 0 → ¬ ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
      (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
      (∀ d, ¬ PrimedEdgePresent w h d.1 ↔ primeMissingEdge w hfin hb (H d).val.1) ∧
      (∀ d, PrimedEdgePresent w h d.1 ↔ primePresentEdge w (H d).val.1) ∧
      (∀ d, (d.2 = false ∧ PrimedEdgePresent w h d.1) ↔
        ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
      (∀ d, kmswLimitDartVertex w (H d).val =
        primedLimitVertexMap w h (kmswLimitDartVertex u d)) ∧
      (∀ d, H (ρ d) = drawingFirstReturnPerm P S (H d)) ∧
      (∀ d, H (kmswInfFaceSucc u hf d) =
        (drawingFirstReturnPerm P S).symm
          (restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d))) ∧
      (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
      (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
      (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
        limitExternalDart u d) := by
  refine ⟨primedGeometricDartEquiv w h hfin hb,
    primedRealizedVertexEquiv w h hfin hb, primedFaceOrbitEquiv w h hfin hb hex,
    primedGeometricDartEquiv_apply w h hfin hb,
    primedRealizedVertexEquiv_class w h hfin hb, primedLimitDartMap_root w h,
    ?_, primedLimitRoot_not_primedPresent w h, ?_, primedLimitDartMap_edgeInv w h,
    ?_, ?_, primedLimitDartMap_tail w h, primedGeometricDartEquiv_vertex w h hfin hb,
    primedGeometricDartEquiv_rotation w h hfin hb,
    primedGeometricDartEquiv_faceSuccessor w h hfin hb,
    dartBorders_primedFaceOrbitEquiv_iff w h hfin hb hex,
    primedFaceOrbitEquiv_isUnbounded_iff w h hfin hb hex,
    primedFaceOrbitEquiv_exterior_border w h hfin hb hex⟩
  · exact primedLimitRoot_primeMissingEdge w h hfin hb
  · intro d hd ht
    have hp := ((primedLimitDartMap_tail w h d).mpr ht).2
    rw [hd] at hp
    exact primedLimitRoot_not_primedPresent w h hp
  · intro d
    exact primedLimitEdgeMap_missing w h hfin hb d.1
  · intro d
    exact primedLimitEdgeMap_present_iff w h d.1





theorem iidCodes_ae_primedRootedMapIdentification :
    ∀ᵐ ω ∂RandomWalk.iidCodeMeasure,
      let w := fun i => ω (i + 1)
      ∃ (h : HasFlowLineHits w) (hfin : primedLimitFiniteIncidence w)
        (hb : BoundaryHitWitnesses w),
        ∀ (hex : primedBoundedFace_deletedGeometryExclusionGoal w hfin hb),
        let u := primedCode (primedSimInput w) h
        let hf := primedCode_finiteIncidence w h hfin
        let ρ := kmswInfRot u hf
        let P := monotoneFamilyDrawing w hfin (monotone_family_all w)
        let Q := mhatPrimeDrawing w hfin hb (monotone_family_all w)
        let S := primeDartSet w hfin hb
        ∃ (H : (ℕ × Bool) ≃ {d // d ∈ S})
          (V : RootedLocallyFiniteVertex (ℕ × Bool) ρ ≃ RestrictedVertex P S)
          (F : PrimedFaceOrbit w h hfin ≃ Q.Face),
          (∀ d, (H d).val = primedLimitDartMap w h d) ∧
          (∀ d, V (rootedLocallyFiniteVertexClass ρ d) = restrictedVertex P S (H d)) ∧
          (H futureMapRootDart).val = (kmswLLCreatedEdge w (walkNL w h 0), false) ∧
          primeMissingEdge w hfin hb (H futureMapRootDart).val.1 ∧
          ¬ PrimedEdgePresent w h 0 ∧
          (∀ d, d.1 = 0 → ¬ ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
          (∀ d, (H (futureMapEdgeInv d)).val = futureMapEdgeInv (H d).val) ∧
          (∀ d, ¬ PrimedEdgePresent w h d.1 ↔ primeMissingEdge w hfin hb (H d).val.1) ∧
          (∀ d, PrimedEdgePresent w h d.1 ↔ primePresentEdge w (H d).val.1) ∧
          (∀ d, (d.2 = false ∧ PrimedEdgePresent w h d.1) ↔
            ((H d).val.2 = false ∧ primePresentEdge w (H d).val.1)) ∧
          (∀ d, kmswLimitDartVertex w (H d).val =
            primedLimitVertexMap w h (kmswLimitDartVertex u d)) ∧
          (∀ d, H (ρ d) = drawingFirstReturnPerm P S (H d)) ∧
          (∀ d, H (kmswInfFaceSucc u hf d) =
            (drawingFirstReturnPerm P S).symm
              (restrictedFlip P S (primeDartSet_flip_closed w hfin hb) (H d))) ∧
          (∀ d q, Q.dartBorders (H d) (F q) ↔ Quotient.mk _ d = q) ∧
          (∀ q, Q.IsUnbounded (F q) ↔ q = Quotient.mk _ futureMapOuterDart) ∧
          (∀ d, Q.dartBorders (H d) (F (Quotient.mk _ futureMapOuterDart)) ↔
            limitExternalDart u d) := by
  filter_upwards [iidCodes_ae_hasFlowLineHits_all_future_times,
    iidCodes_ae_finite_incident_edges, iidCodes_ae_boundaryHitWitnesses]
    with ω hflow hfin hb
  have h : HasFlowLineHits (fun i => ω (i + 1)) := by
    simpa only [Nat.zero_add] using hflow 0
  exact ⟨h, hfin, hb, fun hex => primedRootedMapIdentification _ h hfin hb hex⟩

end DirectedDistances.KMSW
