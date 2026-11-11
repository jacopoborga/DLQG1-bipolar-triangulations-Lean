/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516RootAlignment
public import DirectedDistances.KMSW.KMSWDiskRootOrderedFrame

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap
open MeasureTheory

private def finReverseEquiv (m : ℕ) : Fin m ≃ Fin m where
  toFun i := ⟨m - 1 - i.val, by omega⟩
  invFun i := ⟨m - 1 - i.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    simp
    omega
  right_inv i := by
    apply Fin.ext
    simp
    omega

private def finCastEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv i := by
    apply Fin.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl








@[expose] noncomputable def diskSampleLowerLeftEdgeId {ell n : ℕ}
    (c : KMSWLeftWalkClass (ell + 1) n) (k : Fin ell) :
    {e : ℕ // e ∈
      (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL} := by
  classical
  let k' : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k')
  let p : Fin S.LL.length :=
    ⟨S.LL.length - 1 - k'.val, by
      have hlen : S.LL.length = ell := by
        simpa only [Nat.add_sub_cancel] using
          (kmswDiskFiniteSample_index_bound c k').1
      rw [hlen]
      have hk := k'.isLt
      omega⟩
  have hposition := kmswDiskRootEdge_ll_position c k'
  dsimp only [u, S, e, p] at hposition
  have hselected : S.LL.get p = e := hposition.2.2.2
  refine ⟨(kmswDiskRootDart c k').1.val, ?_⟩
  change e ∈ S.LL
  rw [← hselected]
  exact List.get_mem _ _

private theorem diskSampleLowerLeftEdgeId_eq_llGet {ell n : ℕ}
    (c : KMSWLeftWalkClass (ell + 1) n) (k : Fin ell) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let S := kmswStage u n
    let k' : Fin ((ell + 1) - 1) :=
      Fin.cast (by omega : ell = (ell + 1) - 1) k
    (diskSampleLowerLeftEdgeId c k).val =
      S.LL.get ⟨S.LL.length - 1 - k'.val, by
        have hlen : S.LL.length = ell := by
          simpa only [Nat.add_sub_cancel] using
            (kmswDiskFiniteSample_index_bound c k').1
        rw [hlen]
        have hk := k'.isLt
        omega⟩ := by
  classical
  dsimp only [diskSampleLowerLeftEdgeId]
  let k' : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) k
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  let e := kmswLLCreatedEdge u (kmswDiskFirstHit c k')
  let p : Fin S.LL.length :=
    ⟨S.LL.length - 1 - k'.val, by
      have hlen : S.LL.length = ell := by
        simpa only [Nat.add_sub_cancel] using
          (kmswDiskFiniteSample_index_bound c k').1
      rw [hlen]
      have hk := k'.isLt
      omega⟩
  have hposition := kmswDiskRootEdge_ll_position c k'
  dsimp only [u, S, e, p] at hposition
  have hselected : S.LL.get p = e := hposition.2.2.2
  change e = S.LL.get p
  exact hselected.symm









theorem diskSampleLowerLeftEdgeId_bijective {ell n : ℕ}
    (hell : 0 < ell) (c : KMSWLeftWalkClass (ell + 1) n) :
    Function.Bijective (diskSampleLowerLeftEdgeId c) := by
  classical
  let u := finiteCodeExtend (n := n + 1) c.val
  let S := kmswStage u n
  let k₀ : Fin ell := ⟨0, hell⟩
  let k₀' : Fin ((ell + 1) - 1) :=
    Fin.cast (by omega : ell = (ell + 1) - 1) k₀
  have hlen : ell = S.LL.length := by
    simpa only [Nat.add_sub_cancel] using
      (kmswDiskFiniteSample_index_bound c k₀').1.symm
  have hnd : S.LL.Nodup := by
    simpa only [u, S] using (kmswStageFrontierChain_all u n).LL_nodup
  let hget := List.Nodup.getEquiv S.LL hnd
  let hrev := finReverseEquiv S.LL.length
  let hcast := finCastEquiv hlen
  let hcomp : Fin ell ≃
      {e : ℕ // e ∈ S.LL} := hcast.trans (hrev.trans hget)
  have hfun : diskSampleLowerLeftEdgeId c =
      fun k : Fin ell => hget (hrev (hcast k)) := by
    funext k
    apply Subtype.ext
    have hroot := diskSampleLowerLeftEdgeId_eq_llGet c k
    have hp : (⟨S.LL.length - 1 -
        (Fin.cast (by omega : ell = (ell + 1) - 1) k).val, by
        have hlen' : S.LL.length = ell := by
          simpa only [Nat.add_sub_cancel] using
            (kmswDiskFiniteSample_index_bound c
              (Fin.cast (by omega : ell = (ell + 1) - 1) k)).1
        rw [hlen']
        have hk := (Fin.cast (by omega : ell = (ell + 1) - 1) k).isLt
        omega⟩ : Fin S.LL.length) = hrev (hcast k) := by
      apply Fin.ext
      simp [hrev, finReverseEquiv, hcast, finCastEquiv]
    have hroot' : (diskSampleLowerLeftEdgeId c k).val =
        S.LL.get ⟨S.LL.length - 1 -
          (Fin.cast (by omega : ell = (ell + 1) - 1) k).val, by
          have hlen' : S.LL.length = ell := by
            simpa only [Nat.add_sub_cancel] using
              (kmswDiskFiniteSample_index_bound c
                (Fin.cast (by omega : ell = (ell + 1) - 1) k)).1
          rw [hlen']
          have hk := (Fin.cast (by omega : ell = (ell + 1) - 1) k).isLt
          omega⟩ := by
      simpa only [u, S] using hroot
    change (diskSampleLowerLeftEdgeId c k).val =
      (hget (hrev (hcast k))).val
    rw [hroot']
    change S.LL.get ⟨S.LL.length - 1 -
      (Fin.cast (by omega : ell = (ell + 1) - 1) k).val, _⟩ =
      S.LL.get (hrev (hcast k))
    exact congrArg S.LL.get hp
  rw [hfun]
  exact hcomp.bijective





theorem diskSampleLowerLeftEdgeId_isMissing {ell n : ℕ}
    (c : KMSWLeftWalkClass (ell + 1) n)
    (e : {e : ℕ // e ∈
      (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL}) :
    (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).present e.val = false := by
  classical
  let u := finiteCodeExtend (n := n + 1) c.val
  have h := (kmswStageFrontierChain_all u n).LL_missing_bounded e.val e.property
  simpa only [u] using h.1

/-- Helper toward Proposition 5.16. Under the uniform index mark on `Fin ell`,
the sampled edge ID has the uniform counting measure on the finite set of
distinct lower-left missing geometric edge IDs of the sampled KMSW map. The
bijective identification is `diskSampleLowerLeftEdgeId_bijective`, consistent -/
theorem diskSampleLowerLeftEdgeId_uniform {ell n : ℕ}
    (hell : 0 < ell) (c : KMSWLeftWalkClass (ell + 1) n) :
    letI : MeasurableSpace (Fin ell) := ⊤
    letI : MeasurableSpace
      {e : ℕ // e ∈
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL} := ⊤
    Measure.map (diskSampleLowerLeftEdgeId c) (uniformCountingMeasure (Fin ell)) =
      uniformCountingMeasure
        {e : ℕ // e ∈
          (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL} := by
  classical
  letI : MeasurableSpace (Fin ell) := ⊤
  letI : MeasurableSpace
      {e : ℕ // e ∈
        (kmswStage (finiteCodeExtend (n := n + 1) c.val) n).LL} := ⊤
  exact uniformCountingMeasure_map_of_bijective _
    (diskSampleLowerLeftEdgeId_bijective hell c)

end DirectedDistances.PaperProofs.Section5
