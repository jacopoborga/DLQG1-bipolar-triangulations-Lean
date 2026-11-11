module

public import DirectedDistances.KMSW.KMSWDiskRootedLaw
public import DirectedDistances.KMSW.KMSWWindowPatchRotation
public import DirectedDistances.KMSW.KMSWWindowPatchVertex

/-! Helper toward prop-disk-bs-conv / Proposition 5.16
transport of the disk root edge frame through the KMSW window maps. Window edge
IDs use local allocation, so the exact edge correspondence is via the patch
map `φ`. The Boolean root-side convention is proposed, not adopted. No ball
this deterministic helper; this is not the paper result. -/

public section
namespace DirectedDistances.KMSW

open DirectedDistances.PlanarMap

private theorem diskRootEdge_window_map {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1)) (s : ℕ)
    (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    (kmswWindowPatchData u s m).φ (kmswLLCreatedEdge v (T - s)) =
      kmswLLCreatedEdge u T := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let m := n - s
  let v := fun i => u (s + i)
  have hspec := kmswDiskFirstHit_spec c k
  dsimp only [u, T] at hspec
  have hTn : T ≤ n := hspec.2.1
  have hτpos : 0 < T - s := by omega
  have hτle : T - s ≤ m := by omega
  let j := T - s - 1
  have hsj : s + j = T - 1 := by dsimp [j]; omega
  obtain ⟨j₀, hj₀T, _, hj₀code, hj₀drop, hj₀tr, _, _, _⟩ :=
    kmswDiskFirstHit_triangle c k
  have hrootId : kmswLLCreatedEdge u T =
      (kmswStage u (T - 1)).nextEdge + 1 := by
    have hfresh := stageTriangleDartTriple_left_fresh u j₀ hj₀code
      (by rw [hj₀drop]; rfl)
    rw [hfresh] at hj₀tr
    have hthird := congrArg (fun t => t.2.2.1) hj₀tr
    change (kmswStage u j₀.val).nextEdge + 1 = kmswLLCreatedEdge u T at hthird
    have hthird' : (kmswStage u (T - 1)).nextEdge + 1 =
        kmswLLCreatedEdge u T := by
      simpa only [hj₀T] using hthird
    exact hthird'.symm
  have hdropGlobal : (kmswStage u (s + j)).UL.dropLast = [] := by
    rw [hsj]
    simpa [hj₀T] using hj₀drop
  have hcode : v j = 0 := by
    dsimp [v, j]
    rw [hsj]
    simpa [hj₀T] using hj₀code
  let pre := kmswStage v j
  let globalPre := kmswStage u (s + j)
  let data := kmswWindowPatchData u s j
  have hrel := kmswWindowPatchData_rel u s j
  change KMSWWindowPatchRel (kmswStage u s) globalPre pre data.φ
    data.A data.B data.YL data.YR data.XL data.XR at hrel
  have hglobalULne : globalPre.UL ≠ [] := by
    exact (kmswStage_UL_nonempty_active_last u (s + j)).1
  have hpreULne : pre.UL ≠ [] := by
    exact (kmswStage_UL_nonempty_active_last v j).1
  have hglobalULlen : globalPre.UL.length = 1 := by
    have hdropGlobal' : globalPre.UL.dropLast = [] := by
      simpa only [globalPre] using hdropGlobal
    have hlen := congrArg List.length hdropGlobal'
    simp only [List.length_dropLast, List.length_nil] at hlen
    have hpos := List.length_pos_of_ne_nil hglobalULne
    omega
  have hA : data.A = [] := by
    apply List.length_eq_zero_iff.mp
    have hlen := congrArg List.length hrel.ul
    simp only [List.length_append, List.length_map] at hlen
    rw [hglobalULlen] at hlen
    have hprepos := List.length_pos_of_ne_nil hpreULne
    omega
  have hpreULlen : pre.UL.length = 1 := by
    have hlen : globalPre.UL.length = data.A.length + pre.UL.length := by
      simpa only [List.length_append, List.length_map] using
        congrArg List.length hrel.ul
    rw [hglobalULlen, hA] at hlen
    simpa only [List.length_nil, Nat.zero_add] using hlen.symm
  have hdropPre : pre.UL.dropLast = [] := by
    apply List.length_eq_zero_iff.mp
    rw [List.length_dropLast, hpreULlen]
  have hcode' : u (s + j) = 0 := by simpa [v] using hcode
  have hdropRev : pre.UL.dropLast.reverse = [] := by
    rw [hdropPre]
    rfl
  have hrootLocal : kmswLLCreatedEdge v (j + 1) = pre.nextEdge + 1 := by
    have hnext : (kmswStage v (j + 1)).nextEdge = pre.nextEdge + 2 := by
      change (kmswStep (kmswStage v j) (v j)).nextEdge = pre.nextEdge + 2
      rw [hcode]
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdropRev,
        State.addEdge, pre]
    change (kmswStage v (j + 1)).nextEdge - 1 = pre.nextEdge + 1
    rw [hnext]
    omega
  have hmapFresh :
      (kmswWindowPatchData u s (j + 1)).φ (pre.nextEdge + 1) =
        globalPre.nextEdge + 1 := by
    have hARev : data.A.reverse = [] := by rw [hA]; rfl
    have hfresh : kmswCodeStep (u (s + j)) = Step.left := by
      simp [kmswCodeStep, hcode']
    change (KMSWWindowPatchData.step globalPre pre
      (kmswCodeStep (u (s + j))) data).φ (pre.nextEdge + 1) =
        globalPre.nextEdge + 1
    rw [hfresh]
    simp [KMSWWindowPatchData.step, hdropRev, hARev]
  have hlocalBound : kmswLLCreatedEdge v (j + 1) <
      (kmswStage v (j + 1)).nextEdge := by
    rw [hrootLocal]
    have hnext : (kmswStage v (j + 1)).nextEdge = pre.nextEdge + 2 := by
      change (kmswStep (kmswStage v j) (v j)).nextEdge = pre.nextEdge + 2
      rw [hcode]
      simp [kmswStep, kmswStepOfStep, kmswCodeStep, hdropRev,
        State.addEdge, pre]
    rw [hnext]
    omega
  have hmapStable := kmswWindowPatchData_extends_le u s (j + 1) m
    (by dsimp [j, m]; omega) (kmswLLCreatedEdge v (j + 1)) hlocalBound
  calc
    (kmswWindowPatchData u s m).φ (kmswLLCreatedEdge v (T - s)) =
        (kmswWindowPatchData u s (j + 1)).φ (kmswLLCreatedEdge v (j + 1)) := by
          have hτ : T - s = j + 1 := by dsimp [j]; omega
          rw [hτ]
          exact hmapStable
    _ = globalPre.nextEdge + 1 := by rw [hrootLocal]; exact hmapFresh
    _ = kmswLLCreatedEdge u T := by
      change (kmswStage u (s + j)).nextEdge + 1 =
        kmswLLCreatedEdge u T
      rw [hsj]
      exact hrootId.symm

/-- Helper toward prop-disk-bs-conv / Proposition 5.16
transport of the disk root edge frame through the KMSW window maps. Window edge
IDs use local allocation, so the exact edge correspondence is via the patch
map `φ`. The Boolean root-side convention is proposed, not adopted. No ball
this deterministic helper; this is not the paper result. -/
theorem kmswDiskRootFrame_in_window {ℓ n : ℕ}
    (c : KMSWLeftWalkClass ℓ n) (k : Fin (ℓ - 1))
    (s : ℕ) (hs : s < kmswDiskFirstHit c k) :
    let u := finiteCodeExtend (n := n + 1) c.val
    let T := kmswDiskFirstHit c k
    let m := n - s
    let v := fun i => u (s + i)
    s + m = n ∧
    ∃ d : StageDart (kmswStage v m).nextEdge,
      (kmswWindowPatchData u s m).φ d.1.val = kmswLLCreatedEdge u T ∧
      d.2 = true ∧
      (kmswWindowDartMap u s m d).1.val = (kmswDiskRootDart c k).1.val ∧
      (kmswWindowDartMap u s m d).2 = (kmswDiskRootDart c k).2 ∧
      ∀ b : Bool, stageEndpoint (kmswStage u (s + m))
          (if b then kmswWindowDartMap u s m d
           else edgeFlip _ (kmswWindowDartMap u s m d)) =
        kmswWindowPatchVertexMap u s m
          (stageEndpoint (kmswStage v m) (if b then d else edgeFlip _ d)) := by
  dsimp only
  let u := finiteCodeExtend (n := n + 1) c.val
  let T := kmswDiskFirstHit c k
  let m := n - s
  let v := fun i => u (s + i)
  have hspec := kmswDiskFirstHit_spec c k
  dsimp only [u, T] at hspec
  have hTn : T ≤ n := hspec.2.1
  have hsT : s < T := hs
  have hsm : s + m = n := by dsimp [m]; omega
  have hτpos : 0 < T - s := by omega
  have hτle : T - s ≤ m := by omega
  let τ := T - s
  let e := kmswLLCreatedEdge v τ
  have heBound : e < (kmswStage v m).nextEdge := by
    have hpre := (kmswStage_boundary_ids_lt_nextEdge v τ).1
    have heτ : e < (kmswStage v τ).nextEdge := by
      dsimp [e, kmswLLCreatedEdge]
      omega
    exact heτ.trans_le (kmswStage_nextEdge_mono v hτle)
  have heMap := diskRootEdge_window_map c k s hs
  dsimp only [u, T, m, v] at heMap
  have heMap' : (kmswWindowPatchData u s m).φ e =
      kmswLLCreatedEdge u T := by
    simpa only [e, τ] using heMap
  let d : StageDart (kmswStage v m).nextEdge := (⟨e, heBound⟩, true)
  have hrootVal : (kmswDiskRootDart c k).1.val = kmswLLCreatedEdge u T := rfl
  refine ⟨hsm, d, ?_, rfl, ?_, ?_, ?_⟩
  · exact heMap'
  · change (kmswWindowDartMap u s m d).1.val =
      (kmswDiskRootDart c k).1.val
    calc
      (kmswWindowPatchData u s m).φ e = kmswLLCreatedEdge u T := heMap'
      _ = (kmswDiskRootDart c k).1.val := hrootVal.symm
  · change (kmswWindowDartMap u s m d).2 = (kmswDiskRootDart c k).2
    rfl
  · intro b
    cases b
    · simpa [stageEndpoint, kmswWindowDartMap_edgeFlip] using
        kmswWindowDartMap_vertex u s m (edgeFlip _ d)
    · simpa [stageEndpoint] using kmswWindowDartMap_vertex u s m d

end DirectedDistances.KMSW
