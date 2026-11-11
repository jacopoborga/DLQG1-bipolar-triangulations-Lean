/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.KMSW.StageBoundaryMap
public import DirectedDistances.KMSW.StageIncidenceChains
public import DirectedDistances.KMSW.BoundaryRecordsUL
public import DirectedDistances.KMSW.InfiniteGeodesic
public import DirectedDistances.RandomWalk.PitmanCodes
public import DirectedDistances.RandomWalk.SecondCoordinateUnbounded
public import DirectedDistances.RandomWalk.SDPIdentifyMax

/-! # Present upper-right boundary paths at an SDP hitting stage

The path in `eqn-sdp-identify-bdy` is formed by the active edge and the
upper-right boundary of the finite KMSW stage. The UR edges are missing and
unoriented at that stage; under an unbounded-below right coordinate, later
down-steps activate them, giving a path in the final present-edge map -/

public section
namespace DirectedDistances.KMSW

open Quiver MeasureTheory
open DirectedDistances.RandomWalk

private theorem R_succ_sdpIdentifyBdy (w : ℕ → Fin 3) (n : ℕ) :
    R w (n + 1) = R w n + (lazyTwoDimensionalStep (w n)).2 :=
  Finset.sum_range_succ _ _

private theorem R_step_lower_sdpIdentifyBdy (w : ℕ → Fin 3) (n : ℕ) :
    -1 ≤ (lazyTwoDimensionalStep (w n)).2 := by
  have hv := (w n).isLt
  have hcode : (w n).val = 0 ∨ (w n).val = 1 ∨ (w n).val = 2 := by omega
  rcases hcode with h | h | h
  · have hc : w n = 0 := Fin.ext h
    rw [hc, lazyTwoDimensionalStep_zero]
    norm_num
  · have hc : w n = 1 := Fin.ext h
    rw [hc, lazyTwoDimensionalStep_one]
    norm_num
  · have hc : w n = 2 := Fin.ext h
    rw [hc, lazyTwoDimensionalStep_two]

/-- The actual UR dart set and its ordered stage list both have at most `2a`
edges when every vertical coordinate through stage `n` has absolute value at
most `a`. The dart cardinality identity is the map-level boundary formula -/
theorem kmswStage_UR_boundary_card_le_two (w : ℕ → Fin 3) (n : ℕ) (a : ℤ)
    (hR : ∀ j ≤ n, |R w j| ≤ a) :
    ((Finset.card (kmswStageURDartsFinset w n) : ℤ) ≤ 2 * a) ∧
      ((kmswStage w n).UR.length : ℤ) ≤ 2 * a := by
  have hmin : -a ≤ minR w n := by
    induction n with
    | zero =>
      change -a ≤ R w 0
      exact (abs_le.mp (hR 0 (Nat.zero_le _))).1
    | succ n ih =>
      change -a ≤ min (minR w n) (R w (n + 1))
      exact le_min (ih (fun j hj => hR j (by omega)))
        (abs_le.mp (hR (n + 1) (Nat.le_refl _))).1
  have htop : R w n ≤ a := (abs_le.mp (hR n (Nat.le_refl _))).2
  have hcard := (kmswStage_boundary_dart_cardinalities w n).2.1
  have hlen := kmswStage_UR_length w n
  constructor
  · rw [hcard]
    omega
  · rw [hlen]
    omega

private theorem kmswStage_UR_length_real_le_two (w : ℕ → Fin 3) (n : ℕ) (b : ℝ)
    (hR : ∀ j ≤ n, |((R w j : ℤ) : ℝ)| ≤ b) :
    ((kmswStage w n).UR.length : ℝ) ≤ 2 * b := by
  have hmin : -b ≤ ((minR w n : ℤ) : ℝ) := by
    induction n with
    | zero =>
      change -b ≤ ((R w 0 : ℤ) : ℝ)
      exact (abs_le.mp (hR 0 (Nat.zero_le _))).1
    | succ n ih =>
      change -b ≤ ((min (minR w n) (R w (n + 1)) : ℤ) : ℝ)
      by_cases hmin : minR w n ≤ R w (n + 1)
      · rw [min_eq_left hmin]
        exact ih (fun j hj => hR j (by omega))
      · have hright : R w (n + 1) ≤ minR w n := le_of_lt (lt_of_not_ge hmin)
        rw [min_eq_right hright]
        exact (abs_le.mp (hR (n + 1) (Nat.le_refl _))).1
  have htop : ((R w n : ℤ) : ℝ) ≤ b :=
    (abs_le.mp (hR n (Nat.le_refl _))).2
  have hlen : ((kmswStage w n).UR.length : ℝ) =
      ((R w n : ℤ) : ℝ) - ((minR w n : ℤ) : ℝ) := by
    exact_mod_cast kmswStage_UR_length w n
  rw [hlen]
  linarith

private theorem ur_edge_transition_sdpIdentifyBdy (w : ℕ → Fin 3) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) :
    e ∈ (kmswStage w (n + 1)).UR ∨ (kmswStage w (n + 1)).present e = true := by
  have hcodes : w n = 0 ∨ w n = 1 ∨ w n = 2 := by
    have hv := (w n).isLt
    have hv' : (w n).val = 0 ∨ (w n).val = 1 ∨ (w n).val = 2 := by omega
    rcases hv' with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hcodes with hzero | hone | htwo
  · left
    cases hul : (kmswStage w n).UL.dropLast.reverse with
    | nil => simpa [kmswStage, kmswStep, kmswCodeStep, hzero, kmswStepOfStep,
        State.addEdge, hul] using he
    | cons f fs =>
        simpa [kmswStage, kmswStep, kmswCodeStep, hzero, kmswStepOfStep,
          State.addEdge, hul] using he
  · left
    simpa [kmswStage, kmswStep, kmswCodeStep, hone, kmswStepOfStep,
      State.addEdge, List.mem_cons] using
      List.mem_cons_of_mem ((kmswStage w n).nextEdge + 1) he
  · cases hur : (kmswStage w n).UR with
    | nil => simp [hur] at he
    | cons f fs =>
      have he' : e = f ∨ e ∈ fs := by simpa [hur] using he
      rcases he' with rfl | he'
      · right
        simp [kmswStage, kmswStep, kmswCodeStep, htwo, kmswStepOfStep, hur]
      · left
        simpa [kmswStage, kmswStep, kmswCodeStep, htwo, kmswStepOfStep, hur] using he'

private theorem ur_edge_remains_or_present_sdpIdentifyBdy (w : ℕ → Fin 3)
    {n e : ℕ} (he : e ∈ (kmswStage w n).UR) :
    ∀ m, n ≤ m → e ∈ (kmswStage w m).UR ∨ (kmswStage w m).present e = true := by
  have healloc : e < (kmswStage w n).nextEdge :=
    (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he)))
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact Or.inl he
  | succ m hmn ih =>
    rcases ih with hUR | hp
    · exact ur_edge_transition_sdpIdentifyBdy w m e hUR
    · right
      have hebound : e < (kmswStage w m).nextEdge :=
        healloc.trans_le (kmswStage_nextEdge_mono w hmn)
      have hs := kmswStep_present_existing (kmswStage w m) (w m) hebound
      change (kmswStep (kmswStage w m) (w m)).present e = true
      rw [hs]
      split <;> simp_all

/-- Under the deterministic condition that `R` is unbounded below, every UR
edge present in the bookkeeping boundary at stage `n` eventually becomes a
present edge. At stage `n` it is missing and is not oriented; the proof only
uses it as an arrow after the activating down-step -/
theorem kmswStage_UR_edge_eventually_present_of_R_unbounded (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n e : ℕ)
    (he : e ∈ (kmswStage w n).UR) :
    ∃ m, n ≤ m ∧ (kmswStage w m).present e = true := by
  let q := minR w n
  obtain ⟨m₀, hm₀⟩ := hR (q - 1)
  have hm₀past : n < m₀ := by
    by_contra h
    have hle := runningMin_le (R w) n m₀ (by omega)
    change minR w n ≤ R w m₀ at hle
    dsimp [q] at hm₀ hle
    omega
  let p : ℕ → Prop := fun j => n < j ∧ R w j < q
  have hp : ∃ j, p j := ⟨m₀, hm₀past, by dsimp [q] at hm₀ ⊢; omega⟩
  let t := Nat.find hp
  have ht := Nat.find_spec hp
  have hbefore : ∀ j < t, q ≤ R w j := by
    intro j hj
    by_cases hjn : j ≤ n
    · have hmin := runningMin_le (R w) n j hjn
      change q ≤ R w j at hmin
      exact hmin
    · have hnot : ¬p j := Nat.find_min hp hj
      have hjq : ¬ R w j < q := by
        intro hjq
        exact hnot ⟨by omega, hjq⟩
      omega
  have htpos : n < t := ht.1
  have hprev : q ≤ R w (t - 1) := hbefore (t - 1) (by omega)
  have hstep : R w t = R w (t - 1) + (lazyTwoDimensionalStep (w (t - 1))).2 := by
    have heq : t - 1 + 1 = t := by omega
    rw [← heq]
    exact R_succ_sdpIdentifyBdy w (t - 1)
  have hRval : R w t = q - 1 := by
    change n < t ∧ R w t < q at ht
    have hstepLower := R_step_lower_sdpIdentifyBdy w (t - 1)
    dsimp [q] at hprev ⊢
    omega
  have hminEq : minR w t = R w t := by
    obtain ⟨i, hit, hmin⟩ := runningMin_attained (R w) t
    change minR w t = R w i at hmin
    have hle := runningMin_le (R w) t t (Nat.le_refl _)
    change minR w t ≤ R w t at hle
    by_cases hit' : i < t
    · have hprior := hbefore i hit'
      dsimp [q] at hprior
      rw [hmin] at hle
      omega
    · have hi : i = t := by omega
      simpa [hi] using hmin
  have hURempty : (kmswStage w t).UR = [] := by
    have hlen := kmswStage_UR_length w t
    rw [hminEq, hRval] at hlen
    have hzero : (kmswStage w t).UR.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hzero
  have hstate := ur_edge_remains_or_present_sdpIdentifyBdy w he t (by omega)
  rcases hstate with hUR | hpresent
  · rw [hURempty] at hUR
    simp at hUR
  · have hebound : e < (kmswStage w t).nextEdge := by
      exact ((kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr he)))).trans_le (kmswStage_nextEdge_mono w (by omega))
    exact ⟨t, by omega, hpresent⟩

private theorem present_path_of_cons_sdpIdentifyBdy (w : ℕ → Fin 3)
    {u : PresentVertex w} (e : ℕ) (es : List ℕ)
    (hu : edgeWest w e = u.id)
    (hc : List.IsChain (fun a b => edgeEast w a = edgeWest w b) (e :: es))
    (hp : ∀ f ∈ e :: es, EdgePresent w f) :
    ∃ z : PresentVertex w, ∃ p : Path u z,
      pathEdgeList p = e :: es ∧ p.length = es.length + 1 := by
  induction es generalizing u e with
  | nil =>
    let a : u ⟶ (⟨edgeEast w e⟩ : PresentVertex w) :=
      ⟨e, hp e (by simp), hu, rfl⟩
    refine ⟨⟨edgeEast w e⟩, a.toPath, ?_, ?_⟩
    · simp [pathEdgeList, Hom.toPath, a]
    · simp
  | cons f fs ih =>
    have hrel : edgeEast w e = edgeWest w f := by
      simpa using hc.rel_head? (by simp)
    have hct : List.IsChain (fun a b => edgeEast w a = edgeWest w b) (f :: fs) := hc.tail
    have hpt : ∀ g ∈ f :: fs, EdgePresent w g := by
      intro g hg
      exact hp g (List.mem_cons_of_mem e hg)
    obtain ⟨z, p, hlist, hlength⟩ := ih (e := f) (u := ⟨edgeWest w f⟩) rfl hct hpt
    let a : u ⟶ (⟨edgeWest w f⟩ : PresentVertex w) :=
      ⟨e, hp e (by simp), hu, hrel⟩
    refine ⟨z, a.toPath.comp p, ?_, ?_⟩
    · rw [pathEdgeList_comp, hlist]
      simp [pathEdgeList, Hom.toPath, a]
    · simp [hlength]
      omega

private theorem active_UR_edge_chain_sdpIdentifyBdy (w : ℕ → Fin 3) (n : ℕ) :
    List.IsChain (fun e f => edgeEast w e = edgeWest w f)
      (act w n :: (kmswStage w n).UR) := by
  let s := kmswStage w n
  obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
  have hULs : s.UL = xs ++ [s.active] := by simpa [s] using hUL
  have hupper := (kmswStage_boundary_chain_invariant w n).1
  have hshape : s.UL ++ s.UR = xs ++ (s.active :: s.UR) := by
    rw [hULs]
    simp [List.append_assoc]
  have hlocal : List.IsChain (fun e f => s.east e = s.west f)
      (s.active :: s.UR) := by
    have h := hshape ▸ hupper
    exact h.right_of_append
  have hlocal' : List.IsChain (fun e f => s.east e = s.west f)
      (act w n :: s.UR) := by simpa [act, s] using hlocal
  apply hlocal'.imp_of_mem_imp
  intro e f he hf hrel
  have hbound (g : ℕ) (hg : g ∈ act w n :: s.UR) : g < s.nextEdge := by
    have hmem : g ∈ s.UL ∨ g ∈ s.UR := by
      rcases List.mem_cons.mp (by simpa [act, s] using hg) with h | h
      · subst g
        have hact : s.active ∈ s.UL := by rw [hULs]; simp
        exact Or.inl hact
      · exact Or.inr h
    have hAll : g ∈ s.UL ++ s.UR ++ s.LL ++ s.LR := by
      simp only [List.mem_append]
      exact Or.inl (Or.inl hmem)
    exact (kmswStage_boundary_ids_lt_nextEdge w n).2 g (by simpa [s] using hAll)
  have hbe := hbound e he
  have hbf := hbound f hf
  have heends := edge_endpoints_eq w hbe
  have hfends := edge_endpoints_eq w hbf
  exact heends.2.symm.trans (hrel.trans hfends.1)





theorem kmswStage_eta_present_path_of_R_unbounded (w : ℕ → Fin 3)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ) :
    ∃ z : PresentVertex w, ∃ p : Path
      (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) z,
      pathEdgeList p = act w n :: (kmswStage w n).UR ∧
        p.length = (kmswStage w n).UR.length + 1 := by
  let s := kmswStage w n
  have hactiveUL : act w n ∈ s.UL := by
    obtain ⟨xs, hUL⟩ := kmswStage_UL_last w n
    rw [hUL]
    simp [act]
  have hactive : EdgePresent w (act w n) := by
    refine ⟨n, act_lt_nextEdge w (Nat.le_refl _), ?_⟩
    exact (kmswStage_status w n).2.1 _ hactiveUL
  have hpresent : ∀ e ∈ act w n :: s.UR, EdgePresent w e := by
    intro e he
    rcases List.mem_cons.mp he with rfl | heUR
    · exact hactive
    · obtain ⟨m, hnm, hp⟩ := kmswStage_UR_edge_eventually_present_of_R_unbounded
        w hR n e heUR
      have hebound := (kmswStage_boundary_ids_lt_nextEdge w n).2 e (by
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inr heUR)))
      exact ⟨m, hebound.trans_le (kmswStage_nextEdge_mono w hnm), hp⟩
  have hhead : edgeWest w (act w n) =
      (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w).id := by
    exact (edge_endpoints_eq w (act_lt_nextEdge w (Nat.le_refl _))).1.symm
  obtain ⟨z, p, hlist, hlen⟩ := present_path_of_cons_sdpIdentifyBdy w
    (act w n) s.UR hhead (active_UR_edge_chain_sdpIdentifyBdy w n) hpresent
  refine ⟨z, p, hlist, ?_⟩
  simpa only [List.length_cons] using hlen

/-- If all vertical coordinates through stage `n` have magnitude at most `b`,
the realized eta path has length at most `2b+1` (`eqn-kmsw-bdy`, -/
theorem kmswStage_eta_length_real_le (w : ℕ → Fin 3) (n : ℕ) (b : ℝ)
    (hR : ∀ j ≤ n, |((R w j : ℤ) : ℝ)| ≤ b)
    {z : PresentVertex w}
    {p : Path (⟨(kmswStage w n).west (act w n)⟩ : PresentVertex w) z}
    (hp : pathEdgeList p = act w n :: (kmswStage w n).UR) :
    (p.length : ℝ) ≤ 2 * b + 1 := by
  have hpathLen : p.length = (kmswStage w n).UR.length + 1 := by
    have := congrArg List.length hp
    simpa only [pathEdgeList_length, List.length_cons] using this
  have hpathLenReal : (p.length : ℝ) = ((kmswStage w n).UR.length : ℝ) + 1 := by
    exact_mod_cast hpathLen
  have hUR := kmswStage_UR_length_real_le_two w n b hR
  linarith

/-- For the iid source codes `ω`, `codeWalk ω` is exactly the integrated KMSW
walk of `fun i => ω (i+1)`. Thus the stopped maximum event of
`iidCodeWalk_sdpIdentifyMax` controls the UR boundary length at the first hit -/
theorem iidCodeWalk_sdpIdentifyBdy (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 1 ≤ k →
      iidCodeMeasure.real
        {ω | ∃ h : ∃ n : ℕ,
            L (fun i => ω (i + 1)) n = -(k : ℤ),
          ∃ z : PresentVertex (fun i => ω (i + 1)),
          ∃ p : Path
            (⟨(kmswStage (fun i => ω (i + 1)) (Nat.find h)).west
              (act (fun i => ω (i + 1)) (Nat.find h))⟩ :
                PresentVertex (fun i => ω (i + 1))) z,
            pathEdgeList p =
                act (fun i => ω (i + 1)) (Nat.find h) ::
                  (kmswStage (fun i => ω (i + 1)) (Nat.find h)).UR ∧
              (p.length : ℝ) ≤ 2 * A * k + 1} ≥ 1 - δ := by
  obtain ⟨A, _, hA, _, hmax⟩ := iidCodeWalk_sdpIdentifyMax δ hδ
  refine ⟨A, hA, ?_⟩
  intro k hk
  let S : Set (ℕ → Fin 3) := {ω | ∃ h : ∃ n : ℕ,
      (codeWalk ω n).1 = -(k : ℤ),
      ∀ j ≤ Nat.find h, |((codeWalk ω j).2 : ℝ)| ≤ A * k}
  let T : Set (ℕ → Fin 3) := {ω | ∃ h : ∃ n : ℕ,
      L (fun i => ω (i + 1)) n = -(k : ℤ),
      ∃ z : PresentVertex (fun i => ω (i + 1)),
      ∃ p : Path
        (⟨(kmswStage (fun i => ω (i + 1)) (Nat.find h)).west
          (act (fun i => ω (i + 1)) (Nat.find h))⟩ :
            PresentVertex (fun i => ω (i + 1))) z,
        pathEdgeList p =
            act (fun i => ω (i + 1)) (Nat.find h) ::
              (kmswStage (fun i => ω (i + 1)) (Nat.find h)).UR ∧
          (p.length : ℝ) ≤ 2 * A * k + 1}
  let H : Set (ℕ → Fin 3) := {ω | ∀ a : ℤ,
      ∃ n, R (fun i => ω (i + 1)) n ≤ a}
  have hHae : ∀ᵐ ω ∂iidCodeMeasure, ω ∈ H := by
    filter_upwards [ae_codeWalk_snd_unbounded_below] with ω hω
    intro a
    obtain ⟨n, hn⟩ := hω a
    refine ⟨n, ?_⟩
    rw [kmsw_R_eq, ← codeWalk_eq_integrateCodes]
    exact hn
  have hHnull : iidCodeMeasure.real Hᶜ = 0 := by
    apply (measureReal_eq_zero_iff).2
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [Set.mem_compl_iff, not_not] using hHae
  have hsubset : S ⊆ T ∪ Hᶜ := by
    intro ω hω
    rcases hω with ⟨hcode, hbound⟩
    by_cases hωH : ω ∈ H
    · left
      let w : ℕ → Fin 3 := fun i => ω (i + 1)
      have hcoordL (j : ℕ) : L w j = (codeWalk ω j).1 := by
        rw [kmsw_L_eq, ← codeWalk_eq_integrateCodes]
      have hcoordR (j : ℕ) : R w j = (codeWalk ω j).2 := by
        rw [kmsw_R_eq, ← codeWalk_eq_integrateCodes]
      have hLw : ∃ n, L w n = -(k : ℤ) := by
        refine ⟨Nat.find hcode, ?_⟩
        rw [hcoordL]
        exact Nat.find_spec hcode
      have hfind : Nat.find hLw = Nat.find hcode := by
        apply Nat.find_congr'
        intro j
        rw [hcoordL]
      have hboundR : ∀ j ≤ Nat.find hLw,
          |((R w j : ℤ) : ℝ)| ≤ A * k := by
        intro j hj
        have h := hbound j (by rw [hfind] at hj; exact hj)
        rw [hcoordR]
        exact h
      have hR : ∀ a : ℤ, ∃ n, R w n ≤ a := by
        change ∀ a : ℤ, ∃ n, R w n ≤ a at hωH
        intro a
        exact hωH a
      obtain ⟨z, p, hp, _⟩ := kmswStage_eta_present_path_of_R_unbounded
        w hR (Nat.find hLw)
      have hlen := kmswStage_eta_length_real_le w (Nat.find hLw) (A * k)
        hboundR hp
      refine ⟨hLw, z, p, hp, ?_⟩
      calc
        (p.length : ℝ) ≤ 2 * (A * k) + 1 := hlen
        _ = 2 * A * k + 1 := by ring
    · exact Or.inr hωH
  have hprobS : iidCodeMeasure.real S ≥ 1 - δ := by
    have h := hmax k hk
    change iidCodeMeasure.real {ω | ∃ h : ∃ n : ℕ,
      (codeWalk ω n).1 = -(k : ℤ),
      ∀ j ≤ Nat.find h, |((codeWalk ω j).2 : ℝ)| ≤ A * k} ≥ 1 - δ at h
    simpa only [S] using h
  calc
    1 - δ ≤ iidCodeMeasure.real S := hprobS
    _ ≤ iidCodeMeasure.real (T ∪ Hᶜ) := measureReal_mono hsubset
    _ ≤ iidCodeMeasure.real T + iidCodeMeasure.real Hᶜ := measureReal_union_le _ _
    _ = iidCodeMeasure.real T := by rw [hHnull, add_zero]

end DirectedDistances.KMSW
