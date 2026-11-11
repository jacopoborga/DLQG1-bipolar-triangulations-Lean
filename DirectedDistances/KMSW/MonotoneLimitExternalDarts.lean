module

public import DirectedDistances.KMSW.LimitExternalFace
public import DirectedDistances.KMSW.MonotoneStageFaces
public import DirectedDistances.KMSW.MonotoneLayoutData





public section
namespace DirectedDistances.KMSW

 
@[expose] def limitUpperExternalDart (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n → d.2 = false ∧
    ∃ _h : d.1 < (kmswStage w n).nextEdge,
      d.1 ∈ (kmswStage w n).UL ++ (kmswStage w n).UR

 
@[expose] def limitLowerExternalDart (w : ℕ → Fin 3) (d : ℕ × Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n → d.2 = true ∧
    ∃ _h : d.1 < (kmswStage w n).nextEdge,
      d.1 ∈ (kmswStage w n).LL ++ (kmswStage w n).LR

 
theorem limitExternalDart_iff_upper_or_lower (w : ℕ → Fin 3) (d : ℕ × Bool) :
    limitExternalDart w d ↔
      limitUpperExternalDart w d ∨ limitLowerExternalDart w d := by
  constructor
  · rintro ⟨N, hN⟩
    rcases d with ⟨e, b⟩
    cases b with
    | false =>
      left
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨h, ho⟩ := hN n hn
      have hb := (kmswStage_isOuter_iff_boundary w n
        (⟨⟨e, h⟩, false⟩)).mp ho
      rcases hb with hupper | hlower
      · exact ⟨rfl, h, hupper.2⟩
      · exact (Bool.noConfusion hlower.1)
    | true =>
      right
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨h, ho⟩ := hN n hn
      have hb := (kmswStage_isOuter_iff_boundary w n
        (⟨⟨e, h⟩, true⟩)).mp ho
      rcases hb with hupper | hlower
      · exact (Bool.noConfusion hupper.1)
      · exact ⟨rfl, h, hlower.2⟩
  · rintro (hupper | hlower)
    · rcases d with ⟨e, b⟩
      obtain ⟨N, hN⟩ := hupper
      cases b with
      | false =>
        refine ⟨N, fun n hn => ?_⟩
        obtain ⟨hb, h, he⟩ := hN n hn
        exact ⟨h, (kmswStage_isOuter_iff_boundary w n
          (⟨⟨e, h⟩, false⟩)).mpr (Or.inl ⟨hb, he⟩)⟩
      | true => exact (Bool.noConfusion (hN N le_rfl).1)
    · rcases d with ⟨e, b⟩
      obtain ⟨N, hN⟩ := hlower
      cases b with
      | false => exact (Bool.noConfusion (hN N le_rfl).1)
      | true =>
        refine ⟨N, fun n hn => ?_⟩
        obtain ⟨hb, h, he⟩ := hN n hn
        exact ⟨h, (kmswStage_isOuter_iff_boundary w n
          (⟨⟨e, h⟩, true⟩)).mpr (Or.inr ⟨hb, he⟩)⟩

 
@[expose] def InfinitelyManyFreshLeft (w : ℕ → Fin 3) : Prop :=
  {n | w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = []}.Infinite

 
theorem not_InfinitelyManyFreshLeft_iff_eventually_noFreshLeft (w : ℕ → Fin 3) :
    ¬ InfinitelyManyFreshLeft w ↔
      ∃ N, ∀ n, N ≤ n →
        w n ≠ 0 ∨ (kmswStage w n).UL.dropLast.reverse ≠ [] := by
  rw [InfinitelyManyFreshLeft, Set.infinite_iff_exists_gt]
  constructor
  · intro h
    push Not at h
    obtain ⟨N, hN⟩ := h
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra hnot
    rcases not_or.mp hnot with ⟨hleft, hright⟩
    have hnFresh : w n = 0 ∧ (kmswStage w n).UL.dropLast.reverse = [] := by
      constructor
      · by_contra h
        exact hleft h
      · by_contra h
        exact hright h
    have hnBound := hN n hnFresh
    omega
  · rintro ⟨N, hN⟩ hInf
    obtain ⟨n, hnFresh, hn⟩ := hInf N
    rcases hN n (le_of_lt hn) with hnLeft | hnRight
    · exact hnLeft hnFresh.1
    · exact hnRight hnFresh.2

end DirectedDistances.KMSW
