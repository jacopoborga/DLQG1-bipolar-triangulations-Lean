module

public import DirectedDistances.KMSW.KMSWFutureMapCarrier
public import DirectedDistances.KMSW.LimitRotationVertex
public import DirectedDistances.KMSW.LeftmostGeodesicUIQBOT
public import DirectedDistances.KMSW.OutgoingIntervalFreshLeft
public import DirectedDistances.KMSW.WholePlaneRightmostOutgoingExists

/-! Supporting lemmas for paper labels `lem-uibot-bdy` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap




@[expose] def kmswRunRightmostOutAt (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (v e : ℕ) : Prop :=
  EdgePresent w e ∧ edgeWest w e = v ∧
    ∃ k : ℕ, 0 < k ∧
      ¬ futureMapTail w (((kmswInfRot w hfin).symm ^ k) (e, false)) ∧
      ∀ j : ℕ, 0 < j → j < k →
        ¬ EdgePresent w (((kmswInfRot w hfin).symm ^ j) (e, false)).1




private theorem runRightmost_inverse_suffix {α : Type*} (σ : Equiv.Perm α)
    (x : α) {i j : ℕ} (hji : j ≤ i) :
    (σ.symm ^ j) ((σ ^ i) x) = (σ ^ (i - j)) x := by
  have hc (k : ℕ) (y : α) : (σ.symm ^ k) ((σ ^ k) y) = y := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        Equiv.symm_apply_apply, ih]
  have he : (σ ^ i) x = (σ ^ j) ((σ ^ (i - j)) x) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hji]
  rw [he]
  exact hc j _




private theorem runRightmost_arc_eq (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (e f k : ℕ)
    (hn : ¬ futureMapTail w (((kmswInfRot w hfin).symm ^ k) (f, false)))
    (hgap : ∀ j : ℕ, 0 < j → j < k →
      ¬ EdgePresent w (((kmswInfRot w hfin).symm ^ j) (f, false)).1)
    (h : RotationArc (kmswInfRot w hfin) (futureMapTail w)
      (e, false) (f, false)) : e = f := by
  obtain ⟨r, hr, hout⟩ := h
  by_cases hr0 : r = 0
  · subst r
    exact congrArg Prod.fst hr
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hsuffix (j : ℕ) (hjr : j ≤ r) :
        ((kmswInfRot w hfin).symm ^ j) (f, false) =
          ((kmswInfRot w hfin) ^ (r - j)) (e, false) := by
      have := runRightmost_inverse_suffix (kmswInfRot w hfin) (e, false) hjr
      rw [hr] at this
      exact this
    have htail (j : ℕ) (hjr : j ≤ r) :
        futureMapTail w (((kmswInfRot w hfin).symm ^ j) (f, false)) := by
      rw [hsuffix j hjr]
      exact hout (r - j) (by omega)
    by_cases hkr : k ≤ r
    · exact (hn (htail k hkr)).elim
    · have hlt : r < k := by omega
      have hp := hgap r hrpos hlt
      exact (hp (htail r le_rfl).2).elim




theorem kmswRunRightmostOutAt_unique (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (v : ℕ) {e f : ℕ}
    (he : kmswRunRightmostOutAt w hfin v e)
    (hf : kmswRunRightmostOutAt w hfin v f) : e = f := by
  have hout : EdgePresent w e := he.1
  have houtf : EdgePresent w f := hf.1
  rcases kmswInfRot_outgoing_interval_all w hfin e f
      (he.2.1.trans hf.2.1.symm) hout houtf with harc | harc
  · obtain ⟨_, _, k, _, hn, hgap⟩ := hf
    exact runRightmost_arc_eq w hfin e f k hn hgap harc
  · obtain ⟨_, _, k, _, hn, hgap⟩ := he
    exact (runRightmost_arc_eq w hfin f e k hn hgap harc).symm





theorem kmswRunRightmostOutAt_exists (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) (v : ℕ)
    (hout : ∃ e, EdgePresent w e ∧ edgeWest w e = v)
    (hstop : ∃ d, kmswLimitDartVertex w d = v ∧ ¬ futureMapTail w d) :
    ∃ e, kmswRunRightmostOutAt w hfin v e := by
  classical
  obtain ⟨e₀, he₀, hv₀⟩ := hout
  obtain ⟨a, haV, haN⟩ := hstop
  let σ := kmswInfRot w hfin
  let x : ℕ × Bool := (e₀, false)
  have hvertex : kmswLimitDartVertex w x = kmswLimitDartVertex w a := by
    change edgeWest w e₀ = _
    rw [hv₀, haV]
  have hEnd : (if a.2 then edgeEast w a.1 else edgeWest w a.1) =
      edgeWest w e₀ := by
    simpa [kmswLimitDartVertex, x] using hvertex.symm
  obtain ⟨m, hpow⟩ :=
    (kmswInfRot_exists_pow_iff_endpoint w hfin a x).2 hEnd
  have hfind : ∃ i : ℕ, futureMapTail w ((σ ^ i) a) := by
    refine ⟨m, ?_⟩
    rw [hpow]
    exact ⟨rfl, he₀⟩
  let i := Nat.find hfind
  have hi : futureMapTail w ((σ ^ i) a) := Nat.find_spec hfind
  have hipos : 0 < i := by
    by_contra hz
    have : i = 0 := by omega
    rw [this] at hi
    exact haN hi
  have hrotVertex (n : ℕ) : kmswLimitDartVertex w ((σ ^ n) a) =
      kmswLimitDartVertex w a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change kmswLimitDartVertex w
        (kmswInfRot w hfin ((σ ^ n) a)) = kmswLimitDartVertex w a
      exact (kmswLimitDartVertex_rot w hfin ((σ ^ n) a)).trans ih
  let d := (σ ^ i) a
  have hwest : edgeWest w d.1 = v := by
    have hdv : kmswLimitDartVertex w d = v := (hrotVertex i).trans haV
    simpa [d, kmswLimitDartVertex, hi.1] using hdv
  have hcan : (σ.symm ^ i) d = a := by
    change (σ.symm ^ i) ((σ ^ i) a) = a
    simpa [Nat.sub_self] using
      (runRightmost_inverse_suffix σ a (i := i) (j := i) le_rfl)
  have hback : ∃ k : ℕ, 0 < k ∧
      (EdgePresent w (((σ.symm ^ k) d).1) ∨ (σ.symm ^ k) d = a) := by
    exact ⟨i, hipos, Or.inr hcan⟩
  let k := Nat.find hback
  have hk := Nat.find_spec hback
  have hkpos : 0 < k := hk.1
  have hkle : k ≤ i := Nat.find_min' hback ⟨hipos, Or.inr hcan⟩
  have hend : ¬ futureMapTail w ((σ.symm ^ k) d) := by
    rcases hk.2 with _ | hEq
    · by_contra ht
      have hpow' : (σ.symm ^ k) d = ((σ ^ (i-k)) a) := by
        change (σ.symm ^ k) ((σ ^ i) a) = _
        exact runRightmost_inverse_suffix σ a hkle
      have htail : futureMapTail w ((σ ^ (i-k)) a) := by
        simpa only [futureMapTail, hpow'] using ht
      exact Nat.find_min hfind (by omega) htail
    · rw [hEq]
      exact haN
  have hgap' : ∀ j : ℕ, 0 < j → j < k →
      ¬ EdgePresent w (((σ.symm ^ j) d).1) := by
    intro j hj hjk hp
    exact Nat.find_min hback (by omega) ⟨hj, Or.inl hp⟩
  have hd : (d.1, false) = d := Prod.ext rfl hi.1.symm
  have hend' : ¬ futureMapTail w ((σ.symm ^ k) (d.1, false)) := by
    rw [hd]
    exact hend
  have hgapFinal : ∀ j : ℕ, 0 < j → j < k →
      ¬ EdgePresent w (((σ.symm ^ j) (d.1, false)).1) := by
    intro j hj hjk
    rw [hd]
    exact hgap' j hj hjk
  refine ⟨d.1, ?_⟩
  refine ⟨?_, hwest, k, hkpos, hend', hgapFinal⟩
  · exact hi.2




structure KMSWRunRightmostRay (w : ℕ → Fin 3)
    (hfin : KMSWFiniteIncidence w) where
  

  vertex : ℕ → ℕ
  


  edge : ℕ → ℕ
  

  rightmost : ∀ i, kmswRunRightmostOutAt w hfin (vertex i) (edge i)
  


  target : ∀ i, edgeEast w (edge i) = vertex (i + 1)




theorem kmswRunRightmostRays_coalesce_of_common_vertex
    {w : ℕ → Fin 3} {hfin : KMSWFiniteIncidence w}
    (P Q : KMSWRunRightmostRay w hfin) (i j : ℕ)
    (h : P.vertex i = Q.vertex j) :
    ∀ t, P.vertex (i + t) = Q.vertex (j + t) := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih =>
    have he : P.edge (i + t) = Q.edge (j + t) := by
      apply kmswRunRightmostOutAt_unique w hfin (P.vertex (i + t))
        (P.rightmost (i + t))
      rw [ih]
      exact Q.rightmost (j + t)
    exact (P.target (i + t)).symm.trans
      ((congrArg (edgeEast w) he).trans (Q.target (j + t)))

end DirectedDistances.KMSW
