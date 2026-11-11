/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.GeoInftyNonposRightSideWhole8
public import DirectedDistances.PaperProofs.Section5.GeoInftyRMinusFiniteRotationCast

/-! Factorwise transport of the adjusted finite-prefix rotation across equal
stopped prefixes. -/

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap DirectedDistances.RandomWalk
open DirectedDistances.PaperProofs.Section3 DirectedDistances.PaperProofs.Section4
open DirectedDistances.Paper.Section4
open scoped Classical

private theorem rMinusCodePrefixDart_transport
    {F G : State} (M : GeometricSideSubmap) (h : F = G)
    (z : StageDart F.nextEdge) :
    transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) h)
      (rMinusCodePrefixDart F M z) =
    rMinusCodePrefixDart G M
      (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) h) z) := by
  cases h
  rfl

private theorem rMinusCodeHattedDart_transport
    {F G : State} (M : GeometricSideSubmap) (h : F = G)
    (z : {z : ℕ × Bool // z.1 ∈ M.edges}) :
    transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) h)
      (rMinusCodeHattedDart F M z) = rMinusCodeHattedDart G M z := by
  cases h
  rfl

private theorem rMinusBoundaryCornerPerm_cast
    {m n : ℕ} (h : m = n) (d : StageDart m) :
    Eq.mp (congrArg StageDart h) (rMinusBoundaryCornerPerm m d) =
      rMinusBoundaryCornerPerm n (Eq.mp (congrArg StageDart h) d) := by
  cases h
  rfl

private theorem stageDart_cast_apply {m n : ℕ} (h : m = n)
    (d : StageDart m) :
    Eq.mp (congrArg StageDart h) d = (Fin.cast h d.1, d.2) := by
  cases h
  rfl

private theorem rMinusPrefixBoundaryDart_transport
    (u v : ℕ → Fin 3) (n : ℕ)
    (hstate : kmswStage u n = kmswStage v n)
    (z : StageDart ((kmswStage u n).active :: (kmswStage u n).UR).length) :
    let hlist := congrArg (fun F : State => F.active :: F.UR) hstate
    let hlen := congrArg List.length hlist
    Eq.mp (congrArg StageDart (congrArg (fun F : State => F.nextEdge) hstate))
        (rMinusPrefixBoundaryDart u n z) =
      rMinusPrefixBoundaryDart v n (Eq.mp (congrArg StageDart hlen) z) := by
  dsimp only
  let hlist := congrArg (fun F : State => F.active :: F.UR) hstate
  let hlen := congrArg List.length hlist
  rw [stageDart_cast_apply (congrArg (fun F : State => F.nextEdge) hstate),
    stageDart_cast_apply hlen]
  apply Prod.ext
  · apply Fin.ext
    simp only [rMinusPrefixBoundaryDart]
    change ((kmswStage u n).active :: (kmswStage u n).UR)[z.1.val] =
      ((kmswStage v n).active :: (kmswStage v n).UR)[z.1.val]
    have hvalidV : z.1.val < ((kmswStage v n).active :: (kmswStage v n).UR).length := by
      rw [← hlen]
      exact z.1.isLt
    have hget := congrArg (fun L : List ℕ => L[z.1.val]?) hlist
    rw [List.getElem?_eq_getElem z.1.isLt,
      List.getElem?_eq_getElem hvalidV] at hget
    exact Option.some.inj hget
  · rfl

/-- Helper toward Lemma 5.5: the quotient-dart transport commutes with the
extended finite boundary-corner factor across a shared prefix. -/
theorem rMinusCodeBoundaryCornerFactor_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
    let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
    let NU := ((kmswStage u n).active :: (kmswStage u n).UR).length
    let NV := ((kmswStage v n).active :: (kmswStage v n).UR).length
    let CU := (rMinusBoundaryCornerPerm NU).extendDomain
      (Equiv.ofInjective (rMinusCodeBoundaryDart u n M)
        (rMinusCodeBoundaryDart_injective u n q))
    let CV := (rMinusBoundaryCornerPerm NV).extendDomain
      (Equiv.ofInjective (rMinusCodeBoundaryDart v n M)
        (rMinusCodeBoundaryDart_injective v n q))
    e (CU d) = CV (e d) := by
  dsimp only
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let hstate := kmswStage_eq_of_prefix u v n hp
  let hnext := congrArg (fun F : State => F.nextEdge) hstate
  let hlist := congrArg (fun F : State => F.active :: F.UR) hstate
  let hlen := congrArg List.length hlist
  let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
  let bU := rMinusCodeBoundaryDart u n M
  let bV := rMinusCodeBoundaryDart v n M
  let NU := ((kmswStage u n).active :: (kmswStage u n).UR).length
  let NV := ((kmswStage v n).active :: (kmswStage v n).UR).length
  let CU := (rMinusBoundaryCornerPerm NU).extendDomain
    (Equiv.ofInjective bU (rMinusCodeBoundaryDart_injective u n q))
  let CV := (rMinusBoundaryCornerPerm NV).extendDomain
    (Equiv.ofInjective bV (rMinusCodeBoundaryDart_injective v n q))
  have hboundary (z : StageDart NU) : e (bU z) = bV (Eq.mp (congrArg StageDart hlen) z) := by
    dsimp only [bU, bV]
    rw [rMinusCodeBoundaryDart_eq_prefix, rMinusCodeBoundaryDart_eq_prefix]
    have hpref := rMinusCodePrefixDart_transport M hstate (rMinusPrefixBoundaryDart u n z)
    rw [rMinusPrefixBoundaryDart_transport u v n hstate z] at hpref
    exact hpref
  by_cases hd : d ∈ Set.range bU
  · rcases hd with ⟨z, rfl⟩
    have hCU : CU (bU z) = bU (rMinusBoundaryCornerPerm NU z) :=
      (rMinusBoundaryCornerPerm NU).extendDomain_apply_image
        (Equiv.ofInjective bU (rMinusCodeBoundaryDart_injective u n q)) z
    have hCV : CV (bV (Eq.mp (congrArg StageDart hlen) z)) =
        bV (rMinusBoundaryCornerPerm NV (Eq.mp (congrArg StageDart hlen) z)) :=
      (rMinusBoundaryCornerPerm NV).extendDomain_apply_image
        (Equiv.ofInjective bV (rMinusCodeBoundaryDart_injective v n q)) _
    have hcorner := rMinusBoundaryCornerPerm_cast hlen z
    calc
      e (CU (bU z)) = e (bU (rMinusBoundaryCornerPerm NU z)) := congrArg e hCU
      _ = bV (Eq.mp (congrArg StageDart hlen) (rMinusBoundaryCornerPerm NU z)) := hboundary _
      _ = bV (rMinusBoundaryCornerPerm NV (Eq.mp (congrArg StageDart hlen) z)) := congrArg bV hcorner
      _ = CV (bV (Eq.mp (congrArg StageDart hlen) z)) := hCV.symm
      _ = CV (e (bU z)) := congrArg CV (hboundary z).symm
  · have hnot : e d ∉ Set.range bV := by
      rintro ⟨zV, hzV⟩
      let zU : StageDart NU := Eq.mpr (congrArg StageDart hlen) zV
      have hz : e (bU zU) = bV zV := by
        simpa [zU] using hboundary zU
      have hdu : d = bU zU := e.injective (hzV.symm.trans hz.symm)
      exact hd ⟨zU, hdu.symm⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective bU (rMinusCodeBoundaryDart_injective u n q)) hd,
        Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective bV (rMinusCodeBoundaryDart_injective v n q)) hnot]

/-- Helper toward Lemma 5.5: the quotient-dart transport commutes with the
extended prefix-rotation factor across a shared prefix. -/
theorem rMinusCodePrefixRotationFactor_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
    let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
    let PU := (stageRot u n).extendDomain
      (Equiv.ofInjective (rMinusCodePrefixDart (kmswStage u n) M)
        (rMinusCodePrefixDart_injective u n q))
    let PV := (stageRot v n).extendDomain
      (Equiv.ofInjective (rMinusCodePrefixDart (kmswStage v n) M)
        (rMinusCodePrefixDart_injective v n q))
    e (PU d) = PV (e d) := by
  dsimp only
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let hstate := kmswStage_eq_of_prefix u v n hp
  let hnext := congrArg (fun F : State => F.nextEdge) hstate
  let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
  let fU := rMinusCodePrefixDart (kmswStage u n) M
  let fV := rMinusCodePrefixDart (kmswStage v n) M
  let PU := (stageRot u n).extendDomain
    (Equiv.ofInjective fU (rMinusCodePrefixDart_injective u n q))
  let PV := (stageRot v n).extendDomain
    (Equiv.ofInjective fV (rMinusCodePrefixDart_injective v n q))
  by_cases hd : d ∈ Set.range fU
  · rcases hd with ⟨z, rfl⟩
    have hPU : PU (fU z) = fU (stageRot u n z) := by
      exact (stageRot u n).extendDomain_apply_image
        (Equiv.ofInjective fU (rMinusCodePrefixDart_injective u n q)) z
    have hV : e (fU z) = fV (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge)
        hstate) z) := by
      exact rMinusCodePrefixDart_transport M hstate z
    have hrot : Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate)
        (stageRot u n z) = stageRot v n
          (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate) z) := by
      exact stageRot_cast_conj_of_prefix n hp z
    have hPV : PV (fV (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge)
        hstate) z)) = fV (stageRot v n
          (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate) z)) := by
      exact (stageRot v n).extendDomain_apply_image
        (Equiv.ofInjective fV (rMinusCodePrefixDart_injective v n q)) _
    calc
      e (PU (fU z)) = e (fU (stageRot u n z)) := congrArg e hPU
      _ = fV (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate)
          (stageRot u n z)) := rMinusCodePrefixDart_transport M hstate _
      _ = fV (stageRot v n
          (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate) z)) :=
        congrArg fV hrot
      _ = PV (fV (Eq.mp (congrArg (fun s : State => StageDart s.nextEdge) hstate) z)) := hPV.symm
      _ = PV (e (fU z)) := congrArg PV hV.symm
  · have hnot : e d ∉ Set.range fV := by
      rintro ⟨zV, hzV⟩
      let hnext := congrArg (fun F : State => F.nextEdge) hstate
      let zU : StageDart (kmswStage u n).nextEdge := Eq.mpr (congrArg StageDart hnext) zV
      have hz : e (fU zU) = fV zV := by
        change transportEquivOfTypeEq
          (congrArg (fun s : State => RMinusCodeGluedDart s M) hstate) (fU zU) = fV zV
        simpa [zU] using rMinusCodePrefixDart_transport M hstate zU
      have hdu : d = fU zU := e.injective (hzV.symm.trans hz.symm)
      exact hd ⟨zU, hdu.symm⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective fU (rMinusCodePrefixDart_injective u n q)) hd,
        Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective fV (rMinusCodePrefixDart_injective v n q)) hnot]

/-- Helper toward Lemma 5.5: the quotient-dart transport commutes with the
extended hatted-rotation factor, whose underlying rotation is shared. -/
theorem rMinusCodeHattedRotationFactor_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
    let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
    let HU := (rMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage u n) M)
        (rMinusCodeHattedDart_injective u n q))
    let HV := (rMinusHattedRotation x q).extendDomain
      (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage v n) M)
        (rMinusCodeHattedDart_injective v n q))
    e (HU d) = HV (e d) := by
  dsimp only
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let hstate := kmswStage_eq_of_prefix u v n hp
  let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
  let fU := rMinusCodeHattedDart (kmswStage u n) M
  let fV := rMinusCodeHattedDart (kmswStage v n) M
  let HU := (rMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective fU (rMinusCodeHattedDart_injective u n q))
  let HV := (rMinusHattedRotation x q).extendDomain
    (Equiv.ofInjective fV (rMinusCodeHattedDart_injective v n q))
  have htransport (z : {z : ℕ × Bool // z.1 ∈ M.edges}) : e (fU z) = fV z := by
    change transportEquivOfTypeEq
      (congrArg (fun s : State => RMinusCodeGluedDart s M) hstate) (fU z) = fV z
    exact rMinusCodeHattedDart_transport M hstate z
  by_cases hd : d ∈ Set.range fU
  · rcases hd with ⟨z, rfl⟩
    have hU : HU (fU z) = fU (rMinusHattedRotation x q z) :=
      (rMinusHattedRotation x q).extendDomain_apply_image
        (Equiv.ofInjective fU (rMinusCodeHattedDart_injective u n q)) z
    have hV : HV (fV z) = fV (rMinusHattedRotation x q z) :=
      (rMinusHattedRotation x q).extendDomain_apply_image
        (Equiv.ofInjective fV (rMinusCodeHattedDart_injective v n q)) z
    calc
      e (HU (fU z)) = e (fU (rMinusHattedRotation x q z)) := congrArg e hU
      _ = fV (rMinusHattedRotation x q z) := htransport _
      _ = HV (fV z) := hV.symm
      _ = HV (e (fU z)) := congrArg HV (htransport z).symm
  · have hnot : e d ∉ Set.range fV := by
      rintro ⟨z, hz⟩
      have hz' : e (fU z) = fV z := htransport z
      have hd' : d = fU z := e.injective (hz.symm.trans hz'.symm)
      exact hd ⟨z, hd'.symm⟩
    rw [Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective fU (rMinusCodeHattedDart_injective u n q)) hd,
        Equiv.Perm.extendDomain_apply_not_subtype _
          (Equiv.ofInjective fV (rMinusCodeHattedDart_injective v n q)) hnot]

/-- Helper toward Lemma 5.5: the boundary-corner permutation commutes with
transport of its finite stage-dart carrier. -/
theorem rMinusBoundaryCornerPerm_cast_conj_of_sharedPrefix
    (_x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (d : StageDart ((kmswStage u n).active :: (kmswStage u n).UR).length) :
    let hstate := kmswStage_eq_of_prefix u v n hp
    Eq.mp (congrArg StageDart
      (congrArg List.length (congrArg (fun F : State => F.active :: F.UR) hstate)))
      (rMinusBoundaryCornerPerm ((kmswStage u n).active :: (kmswStage u n).UR).length d) =
      rMinusBoundaryCornerPerm ((kmswStage v n).active :: (kmswStage v n).UR).length
        (Eq.mp (congrArg StageDart
          (congrArg List.length (congrArg (fun F : State => F.active :: F.UR) hstate))) d) := by
  let hstate := kmswStage_eq_of_prefix u v n hp
  let hlist := congrArg (fun F : State => F.active :: F.UR) hstate
  have hlen := congrArg List.length hlist
  exact rMinusBoundaryCornerPerm_cast hlen d

/-- Helper toward Lemma 5.5: the initial root-port adjustment commutes with
quotient-dart transport across a shared prefix. -/
theorem rMinusCodeInitialAdjustmentFactor_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
    rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
      (Equiv.swap
        (rMinusCodeBoundaryDart u n M
          (⟨0, by simp⟩, false))
        (rMinusCodePrefixDart (kmswStage u n) M
          (stageRot u n (rMinusPrefixBoundaryDart u n (⟨0, by simp⟩, false)))) d) =
      Equiv.swap
        (rMinusCodeBoundaryDart v n M
          (⟨0, by simp⟩, false))
        (rMinusCodePrefixDart (kmswStage v n) M
          (stageRot v n (rMinusPrefixBoundaryDart v n (⟨0, by simp⟩, false))))
        (rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp d) := by
  exact rMinusCodeInitialRootPortAdjustment_conj_of_sharedPrefix x u v n hp q d

/-- Helper toward Lemma 5.5: the adjusted rotation on the glued quotient
darts is conjugate across streams with a common stopped prefix. -/
theorem rMinusCodeInitialAdjustedRotation_conj_of_sharedPrefix
    (x : XDP) (u v : ℕ → Fin 3) (n : ℕ)
    (hp : ∀ i < n, u i = v i)
    (q : selectedCutCoherentDomain x renewalTime renewalTime_positiveSuccessTime)
    (d : RMinusCodeGluedDart (kmswStage u n)
      (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)) :
    rMinusCodeGluedDartEquiv_of_sharedPrefix
        (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
        u v n hp (rMinusCodeInitialAdjustedRotation u n q d) =
      rMinusCodeInitialAdjustedRotation v n q
        (rMinusCodeGluedDartEquiv_of_sharedPrefix
          (geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q)
          u v n hp d) := by
  let M := geometricSideSubmap x renewalTime renewalTime_positiveSuccessTime .right q
  let e := rMinusCodeGluedDartEquiv_of_sharedPrefix M u v n hp
  let iU : Fin ((kmswStage u n).active :: (kmswStage u n).UR).length := ⟨0, by simp⟩
  let iV : Fin ((kmswStage v n).active :: (kmswStage v n).UR).length := ⟨0, by simp⟩
  let aU := rMinusCodeBoundaryDart u n M (iU, false)
  let aV := rMinusCodeBoundaryDart v n M (iV, false)
  let bU := rMinusCodePrefixDart (kmswStage u n) M
    (stageRot u n (rMinusPrefixBoundaryDart u n (iU, false)))
  let bV := rMinusCodePrefixDart (kmswStage v n) M
    (stageRot v n (rMinusPrefixBoundaryDart v n (iV, false)))
  have hswap (z : RMinusCodeGluedDart (kmswStage u n) M) :
      e (Equiv.swap aU bU z) = Equiv.swap aV bV (e z) := by
    exact rMinusCodeInitialRootPortAdjustment_conj_of_sharedPrefix x u v n hp q z
  have hsplice (z : RMinusCodeGluedDart (kmswStage u n) M) :
      e (rMinusCodeSpliceRotation u n q z) =
        rMinusCodeSpliceRotation v n q (e z) := by
    change e
        ((rMinusHattedRotation x q).extendDomain
          (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage u n) M)
            (rMinusCodeHattedDart_injective u n q))
          ((rMinusBoundaryCornerPerm ((kmswStage u n).active :: (kmswStage u n).UR).length).extendDomain
            (Equiv.ofInjective (rMinusCodeBoundaryDart u n M)
              (rMinusCodeBoundaryDart_injective u n q))
            ((stageRot u n).extendDomain
              (Equiv.ofInjective (rMinusCodePrefixDart (kmswStage u n) M)
                (rMinusCodePrefixDart_injective u n q)) z))) = _
    calc
      _ = (rMinusHattedRotation x q).extendDomain
            (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage v n) M)
              (rMinusCodeHattedDart_injective v n q))
            (e ((rMinusBoundaryCornerPerm ((kmswStage u n).active :: (kmswStage u n).UR).length).extendDomain
              (Equiv.ofInjective (rMinusCodeBoundaryDart u n M)
                (rMinusCodeBoundaryDart_injective u n q))
              ((stageRot u n).extendDomain
                (Equiv.ofInjective (rMinusCodePrefixDart (kmswStage u n) M)
                  (rMinusCodePrefixDart_injective u n q)) z))) :=
          rMinusCodeHattedRotationFactor_conj_of_sharedPrefix x u v n hp q _
      _ = (rMinusHattedRotation x q).extendDomain
            (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage v n) M)
              (rMinusCodeHattedDart_injective v n q))
            ((rMinusBoundaryCornerPerm ((kmswStage v n).active :: (kmswStage v n).UR).length).extendDomain
              (Equiv.ofInjective (rMinusCodeBoundaryDart v n M)
                (rMinusCodeBoundaryDart_injective v n q))
              (e ((stageRot u n).extendDomain
                (Equiv.ofInjective (rMinusCodePrefixDart (kmswStage u n) M)
                  (rMinusCodePrefixDart_injective u n q)) z))) :=
          congrArg _ (rMinusCodeBoundaryCornerFactor_conj_of_sharedPrefix x u v n hp q _)
      _ = rMinusCodeSpliceRotation v n q (e z) :=
          congrArg (fun t => (rMinusHattedRotation x q).extendDomain
            (Equiv.ofInjective (rMinusCodeHattedDart (kmswStage v n) M)
              (rMinusCodeHattedDart_injective v n q))
            ((rMinusBoundaryCornerPerm ((kmswStage v n).active :: (kmswStage v n).UR).length).extendDomain
              (Equiv.ofInjective (rMinusCodeBoundaryDart v n M)
                (rMinusCodeBoundaryDart_injective v n q)) t))
            (rMinusCodePrefixRotationFactor_conj_of_sharedPrefix x u v n hp q z)
  change e (Equiv.swap aU bU
      (rMinusCodeSpliceRotation u n q (Equiv.swap aU bU d))) =
    Equiv.swap aV bV
      (rMinusCodeSpliceRotation v n q (Equiv.swap aV bV (e d)))
  calc
    e (Equiv.swap aU bU (rMinusCodeSpliceRotation u n q (Equiv.swap aU bU d))) =
        Equiv.swap aV bV (e (rMinusCodeSpliceRotation u n q (Equiv.swap aU bU d))) := hswap _
    _ = Equiv.swap aV bV (rMinusCodeSpliceRotation v n q (e (Equiv.swap aU bU d))) :=
      congrArg (Equiv.swap aV bV) (hsplice _)
    _ = Equiv.swap aV bV (rMinusCodeSpliceRotation v n q (Equiv.swap aV bV (e d))) :=
      congrArg (fun z => Equiv.swap aV bV (rMinusCodeSpliceRotation v n q z)) (hswap d)
































end DirectedDistances.PaperProofs.Section5
