module

public import DirectedDistances.KMSW.WholePlaneFreshness
public import DirectedDistances.RandomWalk.TwoSidedIIDCodeMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Helper toward F4c / the whole-plane KMSW carrier
not the paper result; the source identification Q-F4c is not treated. -/

public section
namespace DirectedDistances.KMSW
open MeasureTheory RandomWalk




theorem kmswStage_UR_eq_nil_iff_record (w : ℕ → Fin 3) (k : ℕ) :
    (kmswStage w k).UR = [] ↔ R w k = minR w k := by
  have hlen := kmswStage_UR_length w k
  rw [← List.length_eq_zero_iff]
  omega




theorem kmswStage_UL_dropLast_reverse_eq_nil_iff_record (w : ℕ → Fin 3) (k : ℕ) :
    (kmswStage w k).UL.dropLast.reverse = [] ↔ L w k = minL w k := by
  have hlen := kmswStage_UL_length w k
  have hmin : minL w k ≤ L w k := runningMin_le (L w) k k (Nat.le_refl k)
  rw [← List.length_eq_zero_iff, List.length_reverse, List.length_dropLast]
  omega




@[expose] def KMSWNonrecordVertex (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  2 ≤ v ∧ ∀ k, v = (kmswStage w k).nextVertex →
    (kmswCodeStep (w k) = .down → R w k ≠ minR w k) ∧
    (kmswCodeStep (w k) = .left → L w k ≠ minL w k)




theorem wholePlaneFresh_of_nonrecord (W : ℤ → Fin 3) (N M : ℕ) (hNM : N ≤ M)
    (v : ℕ) (hv : KMSWNonrecordVertex (shiftedStream W N) v) :
    wholePlaneFresh W N M hNM v := by
  by_contra hf
  rcases (wholePlaneFresh_iff_windowSeam W N M hNM v).mp hf with
    hsmall | ⟨k, _, hk, hdown | hleft⟩
  · exact (Nat.not_lt_of_ge hv.1) hsmall
  · exact ((hv.2 k hk).1 hdown.1)
      ((kmswStage_UR_eq_nil_iff_record _ k).mp hdown.2.1)
  · exact ((hv.2 k hk).2 hleft.1)
      ((kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mp hleft.2.1)




theorem wholePlaneCofinalFreshness_of_nonrecord (W : ℤ → Fin 3)
    (hP : ∀ N v, ∃ M, ∃ hNM : N ≤ M,
      KMSWNonrecordVertex (shiftedStream W M) (wholePlaneVertexTrans W N M hNM v)) :
    ∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
      wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v) := by
  intro N v
  obtain ⟨M, hNM, hv⟩ := hP N v
  exact ⟨M, hNM, fun M' hMM' => wholePlaneFresh_of_nonrecord W M M' hMM' _ hv⟩




theorem wholePlaneIID_ae_backward_coordinates_unbounded :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ t : ℤ, ∀ a : ℤ,
      (∃ n, a ≤ (codeWalk (shiftedCodePath (fun i => W (t - 1 - i)) 0) n).1) ∧
      (∃ n, a ≤ (codeWalk (shiftedCodePath (fun i => W (t - 1 - i)) 0) n).2) := by
  apply ae_all_iff.2
  intro t
  have hmap : wholePlaneIIDCodeMeasure.map (fun W i => W (t - 1 - i)) =
      wholePlaneIIDCodeMeasure := by
    exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℤ => uniformCodeMeasure)
      (show Function.Injective (fun i : ℤ => t - 1 - i) from by
        intro i j h
        change t - 1 - i = t - 1 - j at h
        omega)
  have hf : ∀ᵐ ω ∂iidCodeMeasure, ∀ a : ℤ,
      (∃ n, a ≤ (codeWalk ω n).1) ∧ (∃ n, a ≤ (codeWalk ω n).2) := by
    filter_upwards [ae_codeWalk_fst_unbounded_above, ae_codeWalk_snd_unbounded_above]
      with ω hL hR a using ⟨hL a, hR a⟩
  rw [← wholePlaneIIDCodeMeasure_map_shiftedPath 0] at hf
  have hf' := ae_of_ae_map (measurable_shiftedCodePath 0).aemeasurable hf
  rw [← hmap] at hf'
  have hm : Measurable (fun W : ℤ → Fin 3 => fun i : ℤ => W (t - 1 - i)) :=
    measurable_pi_iff.2 (fun i => measurable_pi_apply (t - 1 - i))
  exact ae_of_ae_map hm.aemeasurable hf'

private theorem reverse_prefix_sum (f : ℕ → ℤ) (k n : ℕ) (hn : n ≤ k) :
    (∑ i ∈ Finset.range n, f (k - 1 - i)) =
      (∑ i ∈ Finset.range k, f i) - ∑ i ∈ Finset.range (k - n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hk : k - n = k - (n + 1) + 1 := by omega
    have hi : k - 1 - n = k - (n + 1) := by omega
    rw [hk, Finset.sum_range_succ, hi]
    omega

private theorem backward_sum_eq_sub (f : ℤ → ℤ) (t : ℤ) (M n : ℕ)
    (hzero : 0 ≤ t + (M : ℤ)) (hn : n ≤ (t + (M : ℤ)).toNat) :
    (∑ i ∈ Finset.range n, f (t - 1 - (i : ℤ))) =
      (∑ i ∈ Finset.range (t + (M : ℤ)).toNat, f ((i : ℤ) - M)) -
        ∑ i ∈ Finset.range ((t + (M : ℤ)).toNat - n), f ((i : ℤ) - M) := by
  rw [← reverse_prefix_sum (fun i => f ((i : ℤ) - M)) _ n hn]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hk : ((t + (M : ℤ)).toNat : ℤ) = t + M := by omega
  congr 1
  omega




theorem wholePlaneIID_ae_fixed_time_nonrecord :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure, ∀ t : ℤ,
      ∃ M₀ : ℕ, ∀ M ≥ M₀,
        0 ≤ t + (M : ℤ) ∧
        (let k := (t + (M : ℤ)).toNat
         minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
         minL (shiftedStream W M) k < L (shiftedStream W M) k) := by
  filter_upwards [wholePlaneIID_ae_backward_coordinates_unbounded] with W hW t
  obtain ⟨⟨nL, hnL⟩, ⟨nR, hnR⟩⟩ := hW t 1
  refine ⟨(max (nL : ℤ) (nR : ℤ) - t).toNat, ?_⟩
  intro M hM
  have hML : (nL : ℤ) ≤ t + M := by omega
  have hMR : (nR : ℤ) ≤ t + M := by omega
  have hzero : 0 ≤ t + (M : ℤ) := by omega
  have hL : nL ≤ (t + (M : ℤ)).toNat := by omega
  have hR : nR ≤ (t + (M : ℤ)).toNat := by omega
  refine ⟨hzero, ?_⟩
  have heL := backward_sum_eq_sub
    (fun i => (lazyTwoDimensionalStep (W i)).1) t M nL hzero hL
  have heR := backward_sum_eq_sub
    (fun i => (lazyTwoDimensionalStep (W i)).2) t M nR hzero hR
  have hdiffL : (codeWalk (shiftedCodePath (fun i => W (t - 1 - i)) 0) nL).1 =
      L (shiftedStream W M) (t + (M : ℤ)).toNat -
        L (shiftedStream W M) ((t + (M : ℤ)).toNat - nL) := by
    simpa [codeWalk, shiftedCodePath, shiftedStream, L, Prod.fst_sum] using heL
  have hdiffR : (codeWalk (shiftedCodePath (fun i => W (t - 1 - i)) 0) nR).2 =
      R (shiftedStream W M) (t + (M : ℤ)).toNat -
        R (shiftedStream W M) ((t + (M : ℤ)).toNat - nR) := by
    simpa [codeWalk, shiftedCodePath, shiftedStream, R, Prod.snd_sum] using heR
  have hminL := runningMin_le (L (shiftedStream W M)) (t + (M : ℤ)).toNat
    ((t + (M : ℤ)).toNat - nL) (by omega)
  have hminR := runningMin_le (R (shiftedStream W M)) (t + (M : ℤ)).toNat
    ((t + (M : ℤ)).toNat - nR) (by omega)
  dsimp only
  change runningMin _ _ < _ ∧ runningMin _ _ < _
  omega

private theorem windowEdgeMapInf_act (w : ℕ → Fin 3) (s k : ℕ) :
    kmswWindowEdgeMapInf w s (act (fun i => w (s + i)) k) = act w (s + k) := by
  unfold act
  rw [kmswWindowEdgeMapInf_eq_stage w s k _
    (kmswStage_boundary_ids_lt_nextEdge (fun i => w (s + i)) k).1]
  exact (kmswWindowPatchData_rel w s k).active

private theorem wholePlaneEdgeTrans_act (W : ℤ → Fin 3) (N M : ℕ) (h : N ≤ M)
    (k : ℕ) :
    wholePlaneEdgeTrans W N M h (act (shiftedStream W N) k) =
      act (shiftedStream W M) (M - N + k) := by
  simpa only [wholePlaneEdgeTrans, shiftedStream_shift W N M h] using
    windowEdgeMapInf_act (shiftedStream W M) (M - N) k

private def absoluteActiveEdge (W : ℤ → Fin 3) (t : ℤ) : WholePlaneEdge W :=
  wholePlaneEdgeι W (-t).toNat
    (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat)

private theorem absoluteActiveEdge_eq (W : ℤ → Fin 3) (N k : ℕ) :
    absoluteActiveEdge W ((k : ℤ) - N) =
      wholePlaneEdgeι W N (act (shiftedStream W N) k) := by
  unfold absoluteActiveEdge
  apply Quotient.sound
  let A := (-((k : ℤ) - N)).toNat
  refine ⟨max A N, Nat.le_max_left _ _, Nat.le_max_right _ _, ?_⟩
  change wholePlaneEdgeTrans W A (max A N) _
      (act (shiftedStream W A) ((k : ℤ) - N + (A : ℤ)).toNat) =
    wholePlaneEdgeTrans W N (max A N) _ (act (shiftedStream W N) k)
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act]
  congr 1
  dsimp only [A]
  omega

private theorem absoluteActiveEdge_injective (W : ℤ → Fin 3) :
    Function.Injective (absoluteActiveEdge W) := by
  intro t u he
  obtain ⟨M, ht, hu, h⟩ := Quotient.exact he
  change wholePlaneEdgeTrans W (-t).toNat M ht
      (act (shiftedStream W (-t).toNat) (t + ((-t).toNat : ℤ)).toNat) =
    wholePlaneEdgeTrans W (-u).toNat M hu
      (act (shiftedStream W (-u).toNat) (u + ((-u).toNat : ℤ)).toNat) at h
  rw [wholePlaneEdgeTrans_act, wholePlaneEdgeTrans_act] at h
  have hk := CutConverse.act_injective (shiftedStream W M) h
  change (-t).toNat ≤ M at ht
  change (-u).toNat ≤ M at hu
  change M - (-t).toNat + (t + ((-t).toNat : ℤ)).toNat =
    M - (-u).toNat + (u + ((-u).toNat : ℤ)).toNat at hk
  omega

private theorem incident_active_time_lower_bound (W : ℤ → Fin 3)
    (V : WholePlaneVertex W)
    (hfin : {e : WholePlaneEdge W |
      wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V}.Finite) :
    ∃ b : ℤ, ∀ M k : ℕ,
      (wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).west
          (act (shiftedStream W M) k)) = V ∨
        wholePlaneVertexι W M ((kmswStage (shiftedStream W M) k).east
          (act (shiftedStream W M) k)) = V) → b ≤ (k : ℤ) - M := by
  have hf := hfin.preimage (absoluteActiveEdge_injective W).injOn
  obtain ⟨b, hb⟩ := hf.bddBelow
  refine ⟨b, ?_⟩
  intro M k hk
  apply hb
  change wholePlaneEdgeWest W (absoluteActiveEdge W ((k : ℤ) - M)) = V ∨
    wholePlaneEdgeEast W (absoluteActiveEdge W ((k : ℤ) - M)) = V
  rw [absoluteActiveEdge_eq, wholePlaneEdgeWest_ι, wholePlaneEdgeEast_ι]
  have he := edge_endpoints_eq (shiftedStream W M)
    (kmswStage_boundary_ids_lt_nextEdge (shiftedStream W M) k).1
  simpa only [act, he.1, he.2] using hk

private theorem cofinal_vertex_potential_step (F : State) (c : Fin 3) (n : ℕ)
    (h : n + F.UL.length + 2 * F.UR.length ≤ 4 * F.nextVertex) :
    n + 1 + (kmswStep F c).UL.length + 2 * (kmswStep F c).UR.length ≤
      4 * (kmswStep F c).nextVertex := by
  unfold kmswStep
  cases kmswCodeStep c with
  | down =>
    cases hUR : F.UR with
    | nil =>
      have hlen := congrArg List.length hUR
      simp only [List.length_nil] at hlen
      simp only [kmswStepOfStep, hUR, State.addEdge, List.length_append,
        List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUR
      simp only [List.length_cons] at hlen
      simp only [kmswStepOfStep, hUR, List.length_append,
        List.length_cons, List.length_nil]
      omega
  | left =>
    cases hUL : F.UL.dropLast.reverse with
    | nil =>
      simp only [kmswStepOfStep, hUL, State.addEdge, List.length_cons, List.length_nil]
      omega
    | cons e es =>
      have hlen := congrArg List.length hUL
      simp only [List.length_reverse, List.length_dropLast, List.length_cons] at hlen
      simp only [kmswStepOfStep, hUL, State.addEdge, List.length_append,
        List.length_reverse, List.length_cons, List.length_nil]
      omega
  | up =>
    simp only [kmswStepOfStep, State.addEdge, List.length_append,
      List.length_dropLast, List.length_cons, List.length_nil]
    omega

private theorem cofinal_vertex_allocated (w : ℕ → Fin 3) (v : ℕ) :
    v < (kmswStage w (4 * v + 1)).nextVertex := by
  have hpot (n : ℕ) : n + (kmswStage w n).UL.length +
      2 * (kmswStage w n).UR.length ≤ 4 * (kmswStage w n).nextVertex := by
    induction n with
    | zero => change 1 ≤ 8; decide
    | succ n ih => exact cofinal_vertex_potential_step _ _ _ ih
  have h := hpot (4 * v + 1)
  omega

private theorem cofinal_nonrecord_of_finite_incidence (W : ℤ → Fin 3)
    (hB : ∀ t : ℤ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      0 ≤ t + (M : ℤ) ∧
      (let k := (t + (M : ℤ)).toNat
       minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
       minL (shiftedStream W M) k < L (shiftedStream W M) k))
    (hfin : ∀ V : WholePlaneVertex W, {e : WholePlaneEdge W |
      wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V}.Finite) :
    ∀ N v, ∃ M, ∃ hNM : N ≤ M,
      KMSWNonrecordVertex (shiftedStream W M) (wholePlaneVertexTrans W N M hNM v) := by
  classical
  intro N v
  obtain ⟨b, hb⟩ := incident_active_time_lower_bound W (wholePlaneVertexι W N v)
    (hfin (wholePlaneVertexι W N v))
  let J := 4 * v + 1
  let s := Finset.Icc (b - 1) ((J : ℤ) - N)
  let f : ℤ → ℕ := fun t => Classical.choose (hB t)
  let M := max N (max (s.sup f) (-b + 1).toNat)
  have hNM : N ≤ M := by dsimp only [M]; omega
  have hsup : s.sup f ≤ M := by dsimp only [M]; omega
  have hMb : -b + 1 ≤ (M : ℤ) := by dsimp only [M]; omega
  let u := wholePlaneVertexTrans W N M hNM v
  have hι : wholePlaneVertexι W M u = wholePlaneVertexι W N v :=
    congrFun (wholePlaneVertexι_trans W N M hNM) v
  have huBound : u < (kmswStage (shiftedStream W M) (M - N + J)).nextVertex := by
    have hv : v < (kmswStage (fun i => shiftedStream W M (M - N + i)) J).nextVertex := by
      rw [shiftedStream_shift W N M hNM]
      exact cofinal_vertex_allocated _ v
    have hm := (kmswWindowPatchVertexMap_rel (shiftedStream W M) (M - N) J).vertex_bound
      v hv
    rw [← kmswWindowVertexMapInf_eq_stage _ _ _ _ hv] at hm
    exact hm
  refine ⟨M, hNM, ?_, ?_⟩
  · by_contra hsmall
    have hu : u = 0 ∨ u = 1 := by omega
    have ht : b ≤ (0 : ℤ) - M := by
      apply hb M 0
      rcases hu with hu | hu
      · left
        simpa only [kmswStage, kmswInit, ← hu] using hι
      · right
        simpa only [kmswStage, kmswInit, ← hu] using hι
    omega
  · intro k hk
    have hιk : wholePlaneVertexι W M (kmswStage (shiftedStream W M) k).nextVertex =
        wholePlaneVertexι W N v := by rw [← hk]; exact hι
    have hku : k < M - N + J := by
      by_contra hnot
      have hm := CutConverse.nextVertex_mono (shiftedStream W M)
        (show M - N + J ≤ k by omega)
      change u = _ at hk
      omega
    have escape (ht : b ≤ ((k + 1 : ℕ) : ℤ) - M) :
        minR (shiftedStream W M) k < R (shiftedStream W M) k ∧
        minL (shiftedStream W M) k < L (shiftedStream W M) k := by
      have hmem : (k : ℤ) - M ∈ s := by
        apply Finset.mem_Icc.mpr
        have hMN : M - N + N = M := Nat.sub_add_cancel hNM
        constructor <;> dsimp only [J] at * <;> omega
      have hle : f ((k : ℤ) - M) ≤ M := (Finset.le_sup hmem).trans hsup
      have htB := Classical.choose_spec (hB ((k : ℤ) - M)) M hle
      have hind : ((k : ℤ) - M + (M : ℤ)).toNat = k := by omega
      simpa only [hind] using htB.2
    constructor
    · intro hdown hrec
      have hUR := (kmswStage_UR_eq_nil_iff_record _ k).mpr hrec
      have he : (kmswStage (shiftedStream W M) (k + 1)).east
          (act (shiftedStream W M) (k + 1)) =
          (kmswStage (shiftedStream W M) k).nextVertex := by
        simp [act, kmswStage, kmswStep, hdown, kmswStepOfStep, hUR, State.addEdge]
      have ht := hb M (k + 1) (Or.inr (by rw [he]; exact hιk))
      exact (ne_of_lt (escape ht).1) hrec.symm
    · intro hleft hrec
      have hUL := (kmswStage_UL_dropLast_reverse_eq_nil_iff_record _ k).mpr hrec
      have he : (kmswStage (shiftedStream W M) (k + 1)).west
          (act (shiftedStream W M) (k + 1)) =
          (kmswStage (shiftedStream W M) k).nextVertex := by
        simp [act, kmswStage, kmswStep, hleft, kmswStepOfStep, hUL, State.addEdge]
      have ht := hb M (k + 1) (Or.inl (by rw [he]; exact hιk))
      exact (ne_of_lt (escape ht).2) hrec.symm



theorem wholePlaneIID_ae_cofinalFreshness_of_colimit_finite_incidence :
    ∀ᵐ W ∂wholePlaneIIDCodeMeasure,
      (∀ V : WholePlaneVertex W, {e : WholePlaneEdge W |
        wholePlaneEdgeWest W e = V ∨ wholePlaneEdgeEast W e = V}.Finite) →
      ∀ N v, ∃ M, ∃ hNM : N ≤ M, ∀ M' (hMM' : M ≤ M'),
        wholePlaneFresh W M M' hMM' (wholePlaneVertexTrans W N M hNM v) := by
  filter_upwards [wholePlaneIID_ae_fixed_time_nonrecord] with W hB hfin
  exact wholePlaneCofinalFreshness_of_nonrecord W
    (cofinal_nonrecord_of_finite_incidence W hB hfin)

end DirectedDistances.KMSW
