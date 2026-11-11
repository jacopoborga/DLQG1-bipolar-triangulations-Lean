module

public import DirectedDistances.KMSW.HatInducedFirstReturn

/-! Supporting lemmas for paper labels `lem-geo-infty` (see CORRESPONDENCE.md). -/









public section
namespace DirectedDistances.KMSW

private theorem induced_rotation_scan {α β : Type*} (σ : α → α) (τ : β → β)
    (I : α → β)
    (hret : ∀ x, ∃ k : ℕ, 0 < k ∧ τ^[k] (I x) = I (σ x) ∧
      ∀ j : ℕ, 0 < j → j < k → τ^[j] (I x) ∉ Set.range I)
    (d : α) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧
      (∀ n, τ^[N n] (I d) = I (σ^[n] d)) ∧
      (∀ n j, j < N n →
        (τ^[j] (I d) ∈ Set.range I ↔ ∃ i < n, j = N i)) := by
  classical
  let r (n : ℕ) := (hret (σ^[n] d)).choose
  have hr (n : ℕ) : 0 < r n ∧
      τ^[r n] (I (σ^[n] d)) = I (σ (σ^[n] d)) ∧
      ∀ j : ℕ, 0 < j → j < r n →
        τ^[j] (I (σ^[n] d)) ∉ Set.range I :=
    (hret (σ^[n] d)).choose_spec
  let N : ℕ → ℕ := fun n => Nat.rec 0 (fun i acc => acc + r i) n
  have hN0 : N 0 = 0 := rfl
  have hNs (n : ℕ) : N (n + 1) = N n + r n := rfl
  have hmono : StrictMono N := strictMono_nat_of_lt_succ fun n => by
    rw [hNs]
    have := (hr n).1
    omega
  have hmap (n : ℕ) : τ^[N n] (I d) = I (σ^[n] d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hNs, Nat.add_comm, Function.iterate_add_apply, ih,
        (hr n).2.1, Function.iterate_succ_apply']
  refine ⟨N, hmono, hN0, hmap, ?_⟩
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    constructor
    · intro hm
      rcases Nat.lt_trichotomy j (N n) with hlt | heq | hgt
      · obtain ⟨i, hi, he⟩ := (ih j hlt).1 hm
        exact ⟨i, by omega, he⟩
      · exact ⟨n, by omega, heq⟩
      · have hpos : 0 < j - N n := by omega
        have hbound : j - N n < r n := by rw [hNs] at hj; omega
        apply False.elim
        apply (hr n).2.2 (j - N n) hpos hbound
        have he : τ^[j - N n] (I (σ^[n] d)) = τ^[j] (I d) := by
          rw [← hmap, ← Function.iterate_add_apply,
            Nat.sub_add_cancel hgt.le]
        rw [he]
        exact hm
    · rintro ⟨i, _, rfl⟩
      rw [hmap]
      exact ⟨σ^[i] d, rfl⟩






theorem hatInfRot_orderedImageScan (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d : ℕ × Bool) :
    let I : (ℕ × Bool) → ℕ × Bool := fun x => (hatLimitEdgeMap w h x.1, x.2)
    let ρu := kmswInfRot (hatCodes w h) (hatCodes_inducedFiniteIncidence w h hfinW)
    let ρw := kmswInfRot w hfinW
    ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧
      (∀ n, (ρw : _ → _)^[N n] (I d) = I ((ρu : _ → _)^[n] d)) ∧
      (∀ n j, j < N n →
        ((ρw : _ → _)^[j] (I d) ∈ Set.range I ↔ ∃ i < n, j = N i)) := by
  exact induced_rotation_scan _ _ _ (hatInfRot_firstReturn w h hfinW) d





theorem hatInfRot_cyclicOrder_iff (w : ℕ → Fin 3) (h : HasFlowLineHits w)
    (hfinW : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (d e f : ℕ × Bool) :
    let I : (ℕ × Bool) → ℕ × Bool := fun x => (hatLimitEdgeMap w h x.1, x.2)
    let ρu := kmswInfRot (hatCodes w h) (hatCodes_inducedFiniteIncidence w h hfinW)
    let ρw := kmswInfRot w hfinW
    (∃ i j : ℕ, 0 < i ∧ i < j ∧
      (ρu : _ → _)^[i] d = e ∧ (ρu : _ → _)^[j] d = f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → (ρu : _ → _)^[k] d ≠ d) ↔
    (∃ i j : ℕ, 0 < i ∧ i < j ∧
      (ρw : _ → _)^[i] (I d) = I e ∧ (ρw : _ → _)^[j] (I d) = I f ∧
      ∀ k : ℕ, 0 < k → k ≤ j → (ρw : _ → _)^[k] (I d) ≠ I d) := by
  let I : (ℕ × Bool) → ℕ × Bool := fun x => (hatLimitEdgeMap w h x.1, x.2)
  let ρu := kmswInfRot (hatCodes w h) (hatCodes_inducedFiniteIncidence w h hfinW)
  let ρw := kmswInfRot w hfinW
  obtain ⟨N, hmono, hzero, hmap, hhits⟩ := hatInfRot_orderedImageScan w h hfinW d
  have hinj : Function.Injective I := hatLimitDart_injective w h
  have hpos {i : ℕ} : 0 < N i ↔ 0 < i := by
    calc
      0 < N i ↔ N 0 < N i := by rw [hzero]
      _ ↔ 0 < i := hmono.lt_iff_lt
  have hlower (n : ℕ) : n ≤ N n := by
    induction n with
    | zero => omega
    | succ n ih =>
      have hlt : N n < N (n + 1) := hmono (Nat.lt_succ_self n)
      omega
  constructor
  · rintro ⟨i, j, hi, hij, hei, hfj, hno⟩
    refine ⟨N i, N j, hpos.mpr hi, hmono hij, ?_, ?_, ?_⟩
    · exact (hmap i).trans (congrArg I hei)
    · exact (hmap j).trans (congrArg I hfj)
    · intro k hk hkj heq
      have hbound : k < N (j + 1) :=
        hkj.trans_lt (hmono (Nat.lt_succ_self j))
      obtain ⟨q, _, hkq⟩ := (hhits (j + 1) k hbound).1 ⟨d, heq.symm⟩
      have hqpos : 0 < q := hpos.mp (hkq ▸ hk)
      have hqj : q ≤ j := hmono.le_iff_le.mp (hkq ▸ hkj)
      apply hno q hqpos hqj
      apply hinj
      rw [hkq, hmap] at heq
      exact heq
  · rintro ⟨i, j, hi, hij, hei, hfj, hno⟩
    have hjbound : j < N (j + 1) := by have := hlower (j + 1); omega
    obtain ⟨a, _, hia⟩ := (hhits (j + 1) i (hij.trans hjbound)).1 ⟨e, hei.symm⟩
    obtain ⟨b, _, hjb⟩ := (hhits (j + 1) j hjbound).1 ⟨f, hfj.symm⟩
    refine ⟨a, b, hpos.mp (hia ▸ hi), hmono.lt_iff_lt.mp ?_, ?_, ?_, ?_⟩
    · exact hia ▸ hjb ▸ hij
    · apply hinj
      rw [hia, hmap] at hei
      exact hei
    · apply hinj
      rw [hjb, hmap] at hfj
      exact hfj
    · intro k hk hkb heq
      apply hno (N k) (hpos.mpr hk)
      · rw [hjb]
        exact hmono.monotone hkb
      · rw [hmap, heq]

end DirectedDistances.KMSW
