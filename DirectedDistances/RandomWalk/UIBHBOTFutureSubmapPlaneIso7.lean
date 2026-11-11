module

public import DirectedDistances.RandomWalk.UIBHBOTFutureSubmapPlaneIso6
public import DirectedDistances.KMSW.WholePlaneStartIso




public section
namespace DirectedDistances.RandomWalk

open MeasureTheory DirectedDistances.KMSW DirectedDistances.PaperProofs.Section5

/-- Helper toward Lemma 5.10. Reindexing the excursion family by any integer
preserves the almost-sure whole-plane rotation hypothesis for its concatenated
code, by shift invariance of `uibhbotWordFamilyLaw`. -/
theorem uibhbotWordFamilyLaw_ae_rotationHypothesis_reindexed (k : ℤ) :
    ∀ᵐ w ∂uibhbotWordFamilyLaw,
      ∃ hw : ∀ j, IsStoppedExcursionWord (w (j - k)),
        WholePlaneRotationHypothesis
          (uibhbotCodeWord (fun j => w (j - k)) (fun j => (hw j).1)) := by
  let T : (ℤ → List (Fin 3)) → (ℤ → List (Fin 3)) := fun w j => w (j - k)
  have hT : Measurable T := by
    apply measurable_pi_iff.2
    intro j
    exact measurable_pi_apply (j - k)
  have hTfun : T = (fun w j => w (j + (-k))) := by
    funext w j
    congr 1
  have hTlaw : uibhbotWordFamilyLaw.map T = uibhbotWordFamilyLaw := by
    rw [hTfun]
    exact uibhbotWordFamilyLaw_map_shift (-k)
  have hmap :
      ∀ᵐ v ∂(uibhbotWordFamilyLaw.map T),
        ∃ hv : ∀ j, IsStoppedExcursionWord (v j),
          WholePlaneRotationHypothesis
            (uibhbotCodeWord v (fun j => (hv j).1)) := by
    rw [hTlaw]
    exact uibhbotWordFamilyLaw_ae_rotationHypothesis
  filter_upwards [ae_of_ae_map hT.aemeasurable hmap] with w hw
  exact hw

private theorem uibhbotBlockBoundary_shift (w : ℤ → List (Fin 3)) (t j : ℤ) :
    uibhbotBlockBoundary (fun a => w (a + t)) j =
      uibhbotBlockBoundary w (j + t) - uibhbotBlockBoundary w t := by
  induction j using Int.induction_on with
  | zero => simp only [uibhbotBlockBoundary_zero, zero_add, sub_self]
  | succ n ih =>
      have ha : (n : ℤ) + 1 + t = ((n : ℤ) + t) + 1 := by omega
      rw [uibhbotBlockBoundary_succ, ha, uibhbotBlockBoundary_succ, ih]
      omega
  | pred n ih =>
      have hs := uibhbotBlockBoundary_succ (fun a => w (a + t)) (-(n : ℤ) - 1)
      have ht := uibhbotBlockBoundary_succ w (-(n : ℤ) - 1 + t)
      have ha : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      have hb : -(n : ℤ) - 1 + t + 1 = -(n : ℤ) + t := by omega
      rw [ha, ih] at hs
      rw [hb] at ht
      omega

/-- Helper toward Lemma 5.10. Reindexing the excursion family by `k` shifts
its concatenated code by exactly the boundary time at level `-k`, including
negative code indices. -/
private theorem uibhbotCodeWordRel_boundary_shift_all (w : ℤ → List (Fin 3))
    (hw : ∀ j, IsStoppedExcursionWord (w j)) (k n : ℤ) :
    uibhbotCodeWordRel w (uibhbotBlockBoundary w (-k) + n) =
      uibhbotCodeWordRel (fun j => w (j - k)) n := by
  let v : ℤ → List (Fin 3) := fun j => w (j - k)
  have hv : ∀ j, IsStoppedExcursionWord (v j) := fun j => hw (j - k)
  obtain ⟨q, hlo, hhi⟩ := uibhbotConcatWalk_exists_block v hv n
  let i : ℕ := (n - uibhbotBlockBoundary v q).toNat
  have hi : (i : ℤ) = n - uibhbotBlockBoundary v q :=
    Int.toNat_of_nonneg (by omega)
  have hil : i < (v q).length := by
    rw [uibhbotBlockBoundary_succ] at hhi
    omega
  have hn : n = uibhbotBlockBoundary v q + (i : ℤ) := by omega
  have hboundary : uibhbotBlockBoundary v q =
      uibhbotBlockBoundary w (q - k) - uibhbotBlockBoundary w (-k) := by
    simpa only [v, sub_eq_add_neg] using uibhbotBlockBoundary_shift w (-k) q
  have htime : uibhbotBlockBoundary w (-k) + n =
      uibhbotBlockBoundary w (q - k) + (i : ℤ) := by
    rw [hn, hboundary]
    omega
  calc
    uibhbotCodeWordRel w (uibhbotBlockBoundary w (-k) + n) =
        uibhbotCodeWordRel w (uibhbotBlockBoundary w (q - k) + (i : ℤ)) := by
          rw [htime]
    _ = uibhbotCodeWordRel (fun j => w (j - (k - q))) i := by
          simpa only [show -(k - q) = q - k by omega] using
            uibhbotCodeWordRel_boundary_suffix w hw (k - q) i
    _ = uibhbotCodeWordRel v (uibhbotBlockBoundary v q + (i : ℤ)) := by
          rw [show (fun j => w (j - (k - q))) = (fun j => v (j + q)) by
            funext j
            simp only [v]
            congr 1
            omega]
          simpa only [Int.neg_neg, sub_neg_eq_add] using
            (uibhbotCodeWordRel_boundary_suffix v hv (-q) i).symm
    _ = uibhbotCodeWordRel v n := by rw [hn]

/-- Helper toward Lemma 5.10. Almost surely, shifting the UIBHBOT code to any
boundary hit gives the code of the correspondingly reindexed excursion family,
whose whole-plane rotation hypothesis follows from shift invariance of the
excursion-family law. -/
theorem uibhbotWordFamilyLaw_ae_boundaryShift_rotationHypothesis :
    ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ k : ℤ,
      WholePlaneRotationHypothesis
        (shiftWordInt (uibhbotCodeWordRel w)
          (uibhbotBoundaryHitTime k (uibhbotCodeWordRel w))) := by
  have hAll : ∀ᵐ w ∂uibhbotWordFamilyLaw, ∀ k : ℤ,
      ∃ hw : ∀ j, IsStoppedExcursionWord (w (j - k)),
        WholePlaneRotationHypothesis
          (uibhbotCodeWord (fun j => w (j - k)) (fun j => (hw j).1)) := by
    apply ae_all_iff.2
    intro k
    exact uibhbotWordFamilyLaw_ae_rotationHypothesis_reindexed k
  filter_upwards [hAll, ae_uibhbotWordFamily_all_stopped] with w hAll hw k
  obtain ⟨hv, hrot⟩ := hAll k
  let v : ℤ → List (Fin 3) := fun j => w (j - k)
  have hshift : shiftWordInt (uibhbotCodeWordRel w)
      (uibhbotBlockBoundary w (-k)) = uibhbotCodeWordRel v := by
    funext n
    change uibhbotCodeWordRel w
      (n + uibhbotBlockBoundary w (-k)) = uibhbotCodeWordRel v n
    rw [Int.add_comm n]
    exact uibhbotCodeWordRel_boundary_shift_all w hw k n
  rw [uibhbotBoundaryHitTime_codeWordRel k w hw, hshift,
    uibhbotCodeWordRel_eq v (fun j => (hv j).1)]
  exact hrot



























end DirectedDistances.RandomWalk
