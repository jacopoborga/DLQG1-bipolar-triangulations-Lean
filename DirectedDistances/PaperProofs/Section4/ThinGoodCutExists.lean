module

public import DirectedDistances.PaperProofs.Section4.ThinIndependenceAssembly
import DirectedDistances.KMSW.CutVertexDisconnects

/-! Supporting lemmas for paper labels `prop-thin-ind` (see CORRESPONDENCE.md). -/

public section
namespace DirectedDistances.PaperProofs.Section4

open DirectedDistances.RandomWalk DirectedDistances.KMSW
open DirectedDistances.PlanarMap DirectedDistances.PaperProofs.Section3
open Filter
open scoped Classical ENNReal

local notation "Ω" => (ℕ → ℤ × ℤ)

private theorem goodCut_hit_value (p : Ω) (k t : ℕ)
    (ht : conditionedSecondCoordinateFirstHit k p = (t : ℕ∞)) :
    (p t).2 = -(k : ℤ) := by
  classical
  unfold conditionedSecondCoordinateFirstHit at ht
  split at ht
  next h =>
    have heq : Nat.find h = t := by exact_mod_cast ht
    rw [← heq]
    exact Nat.find_spec h
  next h => exact (ENat.top_ne_natCast t ht).elim

private theorem goodCut_hit_time_lower_bound (p : Ω) (h0 : (p 0).2 = 0)
    (hstep : ∀ j, (p j).2 - 1 ≤ (p (j + 1)).2) (k t : ℕ)
    (ht : conditionedSecondCoordinateFirstHit k p = (t : ℕ∞)) :
    k ≤ t := by
  have hlower : ∀ n : ℕ, -(n : ℤ) ≤ (p n).2 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
        have hs := hstep n
        push_cast
        omega
  have hvalue := goodCut_hit_value p k t ht
  have hcast : (k : ℤ) ≤ (t : ℤ) := by
    have h := hlower t
    rw [hvalue] at h
    omega
  exact Int.ofNat_le.mp hcast

private theorem goodCut_success_has_rank (T : ℕ → Ω → ℕ∞) (p : Ω)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (n : ℕ) (hn : 0 < n) (hs : literalSuccessGraph p n) :
    ∃ m, 0 < m ∧ T m p = (n : ℕ∞) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let m := positiveSuccessCount (literalSuccessGraph p) (j + 1)
  have hm : 0 < m := by
    dsimp [m]
    rw [positiveSuccessCount_succ, ite_eq_left hs]
    omega
  have hg : IsPositiveSuccessTime (literalSuccessGraph p) m
      ((j + 1 : ℕ) : ℕ∞) :=
    (isPositiveSuccessTime_natCast_iff _ hm _).mpr ⟨by omega, hs, rfl⟩
  obtain ⟨u, _, hu⟩ := existsUnique_positiveSuccessTime (literalSuccessGraph p) m
  exact ⟨m, hm, (hu _ (hT m)).trans (hu _ hg).symm⟩

private theorem goodCut_selectedTime_nat_characterization
    (T : ℕ → Ω → ℕ∞) (p : Ω) (k : ℕ)
    (hT : ∀ m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (hfinite : conditionedSecondCoordinateFirstHit k p < ⊤) :
    (selectedCutTime T k p).toNat ≤
        (conditionedSecondCoordinateFirstHit k p).toNat ∧
      ((selectedCutTime T k p).toNat ≠ 0 →
        literalSuccessGraph p (selectedCutTime T k p).toNat) ∧
      (∀ n, n ≤ (conditionedSecondCoordinateFirstHit k p).toNat →
        literalSuccessGraph p n → n ≤ (selectedCutTime T k p).toNat) := by
  classical
  let K := (conditionedSecondCoordinateFirstHit k p).toNat
  let rank := selectedCutRank T k p
  have hτK : conditionedSecondCoordinateFirstHit k p = (K : ℕ∞) :=
    (ENat.natCast_toNat hfinite.ne).symm
  have hzero : T 0 p = 0 := (isPositiveSuccessTime_zero_iff _ _).mp (hT 0)
  have hrank : T rank p ≤ conditionedSecondCoordinateFirstHit k p := by
    dsimp [rank, selectedCutRank]
    apply Nat.findGreatest_spec (m := 0)
      (P := fun m => T m p ≤ conditionedSecondCoordinateFirstHit k p)
    · exact Nat.zero_le _
    · rw [hzero]
      exact bot_le
  have hsel : selectedCutTime T k p = T rank p := by
    rw [selectedCutTime, dite_eq_left hfinite]
  have hsle : selectedCutTime T k p ≤ conditionedSecondCoordinateFirstHit k p :=
    hsel ▸ hrank
  have hsfin : selectedCutTime T k p < ⊤ := hsle.trans_lt hfinite
  have hscast : selectedCutTime T k p =
      ((selectedCutTime T k p).toNat : ℕ∞) :=
    (ENat.natCast_toNat hsfin.ne).symm
  refine ⟨ENat.toNat_le_toNat hsle hfinite.ne, ?_, ?_⟩
  · intro hnonzero
    have hrpos : 0 < rank := by
      by_contra h
      have hr0 : rank = 0 := by omega
      have hs0 : selectedCutTime T k p = 0 := by rw [hsel, hr0, hzero]
      exact hnonzero (by rw [hs0]; rfl)
    have hg : IsPositiveSuccessTime (literalSuccessGraph p) rank
        ((selectedCutTime T k p).toNat : ℕ∞) := by
      rw [← hscast, hsel]
      exact hT rank
    exact ((isPositiveSuccessTime_natCast_iff _ hrpos _).mp hg).2.1
  · intro n hn hs
    by_cases hn0 : n = 0
    · subst n
      exact Nat.zero_le _
    obtain ⟨m, hm, hmn⟩ := goodCut_success_has_rank T p hT n (by omega) hs
    have hmK : m ≤ K := positiveSuccessTime_le_index T p hT m K (by
      rw [hmn]
      exact ENat.natCast_le_natCast.mpr hn)
    have hmrank : m ≤ rank := by
      dsimp [rank, selectedCutRank]
      apply Nat.le_findGreatest hmK
      rw [hmn, hτK]
      exact ENat.natCast_le_natCast.mpr hn
    have hord : T m p ≤ T rank p := by
      rcases hmrank.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (positiveSuccessTime_strictMono_of_finite T p hT hlt
          (by rw [hmn]; exact ENat.natCast_ne_top n)
          (ne_of_lt (hrank.trans_lt hfinite))).le
    have hns : (n : ℕ∞) ≤ selectedCutTime T k p := by
      rw [← hmn, hsel]
      exact hord
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hns hsfin.ne

private theorem goodCut_step (p : Ω)
    (hlegal : ∀ n, p (n + 1) - p n ∈ Set.range lazyTwoDimensionalStep) :
    ∀ n, (p n).2 - 1 ≤ (p (n + 1)).2 := by
  intro n
  obtain ⟨c, hc⟩ := hlegal n
  change lazyTwoDimensionalStep c = p (n + 1) - p n at hc
  have hs := congrArg Prod.snd hc
  fin_cases c <;>
    norm_num [lazyTwoDimensionalStep, Prod.snd_sub] at hs <;> omega

private theorem selectedCut_min_tendsto_atTop
    (x : DirectedDistances.PlanarMap.XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (q : selectedCutCoherentDomain x T hT) :
    Tendsto (fun k => min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
      (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2)) atTop atTop := by
  obtain ⟨_, hlegal, hhits, _, hwp, hfin, htrans, hR, hL, hinf, hchar⟩ :=
    selectedCutCoherentDomain_spec x T hT q
  let p := q.1
  let w := boltzmannKMSWStream (pathCode p)
  have h0 : (p 0).2 = 0 := congrArg Prod.snd hlegal.1
  have hstep := goodCut_step p hlegal.2
  have hLn : ∀ j, L w j = (p j).1 := by
    intro j
    rw [kmsw_L_eq, hwp]
  have hRn : ∀ j, R w j = (p j).2 := by
    intro j
    rw [kmsw_R_eq, hwp]
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp htrans b
  let r := b.toNat + 1
  have hrτ : conditionedSecondCoordinateFirstHit r p < ⊤ := hhits r
  obtain ⟨t₀, ht₀⟩ := ENat.ne_top_iff_exists.mp hrτ.ne
  have hτ₀ : conditionedSecondCoordinateFirstHit r p = (t₀ : ℕ∞) := ht₀.symm
  have hR₀ := goodCut_hit_value p r t₀ hτ₀
  let G : Set ℕ := {n | mapCutVertex w hfin (activeInitial w n) ∧
    ∀ i < n, activeInitial w i ≠ activeInitial w n}
  have hcutImage : {v : ℕ | mapCutVertex w hfin v} ⊆ activeInitial w '' G := by
    intro v hv
    obtain ⟨n, hnv, hfirst, _, _, _⟩ :=
      mapCutVertex_firstVisit_records w hfin htrans hR hL hv
    refine ⟨n, ?_, hnv.symm⟩
    exact ⟨by rw [← hnv]; exact hv, hfirst⟩
  have himage : (activeInitial w '' G).Infinite := hinf.mono hcutImage
  have hlarge : ∃ n, t₀ < n ∧ N ≤ n ∧ n ∈ G := by
    by_contra h
    have hbound : ∀ n ∈ G, n ≤ max t₀ N := by
      intro n hn
      by_contra hgt
      have hnlarge : t₀ < n ∧ N ≤ n := by omega
      exact h ⟨n, hnlarge.1, hnlarge.2, hn⟩
    have hGfinite : G.Finite := (Set.finite_Iic (max t₀ N)).subset hbound
    exact himage (hGfinite.image (activeInitial w))
  obtain ⟨n, htn, hNn, hnG⟩ := hlarge
  have hsuccess : literalSuccessGraph p n := by
    apply (hchar n).mp
    exact hnG
  have hnpositive : 0 < n := by omega
  have hnew : ∀ i < n, (p n).2 ≤ (p i).2 - 1 := hsuccess.1
  have hfuture : ∀ i ≥ n, (p n).1 ≤ (p i).1 := hsuccess.2
  refine ⟨n, fun k hk => ?_⟩
  have hτk : conditionedSecondCoordinateFirstHit (k + 1) p < ⊤ := hhits (k + 1)
  obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.mp hτk.ne
  have hτK : conditionedSecondCoordinateFirstHit (k + 1) p = (K : ℕ∞) := hK.symm
  have hKlower := goodCut_hit_time_lower_bound p h0 hstep (k + 1) K hτK
  have hnτ : (n : ℕ∞) ≤ conditionedSecondCoordinateFirstHit (k + 1) p := by
    rw [hτK]
    exact ENat.natCast_le_natCast.mpr (by omega)
  obtain ⟨htle, hselected, hmax⟩ := goodCut_selectedTime_nat_characterization
    T p (k + 1) (hT p) hτk
  let t := (selectedCutTime T (k + 1) p).toNat
  have hnt : n ≤ t := hmax n (by simpa [hτK] using hnτ) hsuccess
  have htpos : 0 < t := by omega
  have hselectedGraph : literalSuccessGraph p t := hselected htpos.ne'
  have hleft : b ≤ (p t).1 := by
    rw [← hLn t]
    exact hN t (by omega)
  have hright : b ≤ -(p t).2 := by
    have hrecord := hselectedGraph.1 t₀ (by omega)
    rw [hR₀] at hrecord
    have hrInt : b ≤ (r : ℤ) + 1 := by
      dsimp [r]
      omega
    omega
  exact le_min hleft hright




theorem exists_selectedCut_goodEvent
    (x : DirectedDistances.PlanarMap.XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    ∃ k : ℕ, (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (k + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (k + 1) q.1).toNat).2) := by
  obtain ⟨k, hk⟩ :=
    (tendsto_atTop_atTop.mp (selectedCut_min_tendsto_atTop x T hT q)) ((s : ℤ) + 1)
  exact ⟨k, hk k le_rfl⟩



@[expose] noncomputable def leastGoodCut
    (x : DirectedDistances.PlanarMap.XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s : ℕ) (q : selectedCutCoherentDomain x T hT) : ℕ :=
  Nat.find (exists_selectedCut_goodEvent x T hT s q)




theorem leastGoodCut_spec
    (x : DirectedDistances.PlanarMap.XDP) (T : ℕ → Ω → ℕ∞)
    (hT : ∀ p m, IsPositiveSuccessTime (literalSuccessGraph p) m (T m p))
    (s : ℕ) (q : selectedCutCoherentDomain x T hT) :
    (s : ℤ) + 1 ≤
      min ((q.1 (selectedCutTime T (leastGoodCut x T hT s q + 1) q.1).toNat).1)
        (-(q.1 (selectedCutTime T (leastGoodCut x T hT s q + 1) q.1).toNat).2) := by
  exact Nat.find_spec (exists_selectedCut_goodEvent x T hT s q)

end DirectedDistances.PaperProofs.Section4
