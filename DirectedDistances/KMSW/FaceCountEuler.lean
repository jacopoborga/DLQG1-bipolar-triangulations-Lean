module

public import DirectedDistances.KMSW.StageTriangleFaces
public import DirectedDistances.KMSW.StageEdgesConnected
public import DirectedDistances.KMSW.StageOuterWord
public import Mathlib.GroupTheory.Perm.List

/-! # Face partitions and Euler bookkeeping

The final assembly is conditional on the geometric face partition; it does
not assert that the KMSW boundary words already satisfy that partition. -/

public section
namespace DirectedDistances.KMSW
open DirectedDistances.PlanarMap

/-- The outer word (`none`) and indexed triangle words (`some i`) used to -/
@[expose] def faceWords {D : Type*} (B : List D) (Ts : List (D × D × D)) :
    Option (Fin Ts.length) → List D
  | none => B
  | some i => [Ts[i].1, Ts[i].2.1, Ts[i].2.2]

private theorem orbit_mem {D : Type*} [Fintype D] [DecidableEq D]
    (f : Equiv.Perm D) (L : List D)
    (hs : ∀ d ∈ L, f d = L.formPerm d) {x y : D}
    (hx : x ∈ L) (hxy : f.SameCycle x y) : y ∈ L := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    simpa only [pow_succ', Equiv.Perm.mul_apply, hs _ ih] using
      L.formPerm_apply_mem_of_mem ih

private theorem word_sameCycle {D : Type*} [Fintype D] [DecidableEq D]
    (f : Equiv.Perm D) (L : List D) (hn : L.Nodup)
    (hs : ∀ d ∈ L, f d = L.formPerm d) {x y : D}
    (hx : x ∈ L) (hy : y ∈ L) : f.SameCycle x y := by
  cases L with
  | nil => simp only [List.not_mem_nil] at hx
  | cons a l =>
    have hp : ∀ k, (f ^ k) a = ((a :: l).formPerm ^ k) a := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih,
          hs _ ((by
            rw [List.formPerm_pow_apply_head _ _ hn]
            exact List.getElem_mem _)),
          pow_succ', Equiv.Perm.mul_apply]
    have ha : ∀ z ∈ a :: l, f.SameCycle a z := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
      have he : (f ^ i) a = (a :: l)[i] := by
        rw [hp, List.formPerm_pow_apply_head _ _ hn]
        simp only [Nat.mod_eq_of_lt hi]
      rw [← he]
      exact Equiv.Perm.SameCycle.rfl.pow_right
    exact (ha x hx).symm.trans (ha y hy)

/-- Disjoint, nonempty face words on which the successor is the cyclic list
permutation give one face per word (`sec-kmsw`, -/
noncomputable def faceQuotientEquivWords
    {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I]
    (M : CombinatorialMap D) (L : I → List D)
    (hn : ∀ i, (L i).Nodup) (hne : ∀ i, L i ≠ [])
    (hs : ∀ i d, d ∈ L i → M.faceSucc d = (L i).formPerm d)
    (hd : ∀ i j, i ≠ j → List.Disjoint (L i) (L j))
    (hc : ∀ d, ∃ i, d ∈ L i) : M.FaceQuotient ≃ I := by
  classical
  let r : I → D := fun i => (L i).head (hne i)
  have hr : ∀ i, r i ∈ L i := fun i => List.head_mem (hne i)
  let q : I → M.FaceQuotient := fun i => Quotient.mk _ (r i)
  apply Equiv.symm
  apply Equiv.ofBijective q
  constructor
  · intro i j hij
    by_contra hneij
    have hm := orbit_mem M.faceSucc (L i) (hs i) (hr i) (Quotient.exact hij)
    exact List.disjoint_left.mp (hd i j hneij) hm (hr j)
  · intro x
    refine Quotient.inductionOn x ?_
    intro d
    obtain ⟨i, hi⟩ := hc d
    exact ⟨i, Quotient.sound (word_sameCycle M.faceSucc (L i) (hn i) (hs i) (hr i) hi)⟩

/-- An outer cycle and disjoint triangle three-cycles covering all darts
have exactly one more face than triangles (`def-kmsw`,
triangle entries are excluded as well as overlaps with the outer word. -/
theorem numFaces_of_outer_and_triangles {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (B : List D) (Ts : List (D × D × D))
    (hB : B.Nodup) (hne : B ≠ [])
    (hBs : ∀ d ∈ B, M.faceSucc d = B.formPerm d)
    (hTs : ∀ i : Fin Ts.length,
      FaceSucc3Cycle M.faceSucc Ts[i].1 Ts[i].2.1 Ts[i].2.2)
    (hd : ∀ i j, i ≠ j → List.Disjoint (faceWords B Ts i) (faceWords B Ts j))
    (hc : ∀ d, ∃ i, d ∈ faceWords B Ts i) : M.numFaces = Ts.length + 1 := by
  classical
  have hn : ∀ i, (faceWords B Ts i).Nodup := by
    intro i
    cases i with
    | none => exact hB
    | some i =>
      obtain ⟨_, _, _, h12, h23, h31⟩ := hTs i
      simpa only [faceWords, List.nodup_cons, List.mem_cons, List.mem_singleton,
        not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] using
        And.intro (And.intro h12 h31.symm) h23
  have hnon : ∀ i, faceWords B Ts i ≠ [] := by
    intro i
    cases i with
    | none => exact hne
    | some i => simp only [faceWords, ne_eq, List.cons_ne_nil, not_false_eq_true]
  have hs : ∀ i d, d ∈ faceWords B Ts i →
      M.faceSucc d = (faceWords B Ts i).formPerm d := by
    intro i d hd'
    cases i with
    | none => exact hBs d hd'
    | some i =>
      obtain ⟨h12, h23, h31, _, _, _⟩ := hTs i
      have hn' := hn (some i)
      simp only [faceWords, List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with rfl | rfl | rfl
      · simpa only [faceWords, List.formPerm_apply_head _ _ _ hn'] using h12
      · have he := List.formPerm_apply_getElem (faceWords B Ts (some i)) hn' 1
          (by simp [faceWords])
        simpa only [faceWords, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceMod, List.getElem_cons_succ, List.getElem_cons_zero]
          using h23.trans he.symm
      · have he := List.formPerm_cons_concat_apply_last Ts[i].1 Ts[i].2.2 [Ts[i].2.1]
        simpa only [faceWords, List.cons_append, List.nil_append] using h31.trans he.symm
  unfold CombinatorialMap.numFaces
  simpa using Fintype.card_congr
    (faceQuotientEquivWords M (faceWords B Ts) hn hnon hs hd hc)

/-- Creation-order Euler bookkeeping, checked through all five branches of -/
theorem kmswStage_euler_bookkeeping (w : ℕ → Fin 3) (n : ℕ) :
    (kmswStage w n).nextVertex + (kmswStage w n).triangles.length + 1 =
      (kmswStage w n).nextEdge + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).nextVertex +
      (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).triangles.length + 1 =
      (kmswStepOfStep (kmswStage w n) (kmswCodeStep (w n))).nextEdge + 2
    cases kmswCodeStep (w n) with
    | down =>
      cases hr : (kmswStage w n).UR <;>
        simp only [kmswStepOfStep, hr, State.addEdge] <;> omega
    | left =>
      cases hl : (kmswStage w n).UL.dropLast.reverse <;>
        simp only [kmswStepOfStep, hl, State.addEdge, List.length_append,
          List.length_cons, List.length_nil] <;> omega
    | up =>
      simp only [kmswStepOfStep, State.addEdge, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- Intermediate Euler assembly for `def-kmsw`,
triangle face partition are hypotheses here, not asserted geometric results.
There is one supplied dart triple for each bookkeeping triangle. -/
theorem kmswMap_eulerChar_of_face_partition (w : ℕ → Fin 3) (n : ℕ)
    (T : Fin (kmswStage w n).triangles.length →
      StageDart (kmswStage w n).nextEdge ×
        StageDart (kmswStage w n).nextEdge × StageDart (kmswStage w n).nextEdge)
    (hB : ∀ d ∈ stageOuterWord w n,
      (kmswMap w n).faceSucc d = (stageOuterWord w n).formPerm d)
    (hT : ∀ i, FaceSucc3Cycle (kmswMap w n).faceSucc
      (T i).1 (T i).2.1 (T i).2.2)
    (hd : ∀ i j, i ≠ j → List.Disjoint
      (faceWords (stageOuterWord w n) (List.ofFn T) i)
      (faceWords (stageOuterWord w n) (List.ofFn T) j))
    (hc : ∀ d, ∃ i, d ∈ faceWords (stageOuterWord w n) (List.ofFn T) i) :
    (kmswMap w n).eulerChar = 2 := by
  have hfaces := numFaces_of_outer_and_triangles (kmswMap w n)
    (stageOuterWord w n) (List.ofFn T) (stageOuterWord_nodup w n)
    (stageOuterWord_nonempty w n) hB (by
      intro i
      simpa only [Fin.getElem_fin, List.getElem_ofFn] using
        hT ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩) hd hc
  simp only [List.length_ofFn] at hfaces
  have hb := kmswStage_euler_bookkeeping w n
  unfold CombinatorialMap.eulerChar
  rw [kmswMap_numVertices, kmswMap_numEdges, hfaces]
  omega

end DirectedDistances.KMSW
