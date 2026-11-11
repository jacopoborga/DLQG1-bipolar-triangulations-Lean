module

public import DirectedDistances.KMSW.KMSWWindowPatchRotation








public section
namespace DirectedDistances.KMSW

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
edge-map cocycle; not the paper result and does not settle Q-F4c. -/
theorem kmswWindowPatchData_phi_comp_zero (w : ℕ → Fin 3) (s t e : ℕ)
    (he : e < (kmswStage (fun i => w (s + (t + i))) 0).nextEdge) :
    (kmswWindowPatchData w s t).φ
        ((kmswWindowPatchData (fun i => w (s + i)) t 0).φ e) =
      (kmswWindowPatchData w (s + t) 0).φ e := by
  have hrel := kmswWindowPatchData_rel w s t
  have he0 : e = 0 := by
    have he' : e < 1 := by simpa only [kmswStage, kmswInit] using he
    omega
  subst e
  simpa only [Nat.add_zero, kmswWindowPatchData] using hrel.active

/-- The active edge always satisfies nested-window composition. This checks the distinguished
edge only; it is not the full edge-map cocycle or the paper result. -/
theorem kmswWindowPatchData_phi_comp_active (w : ℕ → Fin 3) (s t m : ℕ) :
    (kmswWindowPatchData w s (t + m)).φ
        ((kmswWindowPatchData (fun i => w (s + i)) t m).φ
          (kmswStage (fun i => w (s + (t + i))) m).active) =
      (kmswWindowPatchData w (s + t) m).φ
        (kmswStage (fun i => w (s + (t + i))) m).active := by
  let u := fun i => w (s + i)
  let v := fun i => w (s + (t + i))
  let z := fun i => w ((s + t) + i)
  have hword : v = z := by
    funext i
    change w (s + (t + i)) = w ((s + t) + i)
    rw [Nat.add_assoc]
  have hsource : kmswStage v m = kmswStage z m := by rw [hword]
  have htarget : kmswStage w (s + (t + m)) = kmswStage w ((s + t) + m) := by
    rw [Nat.add_assoc]
  have hInner := (kmswWindowPatchData_rel u t m).active
  have hOuter := (kmswWindowPatchData_rel w s (t + m)).active
  have hDirect := (kmswWindowPatchData_rel w (s + t) m).active
  change (kmswWindowPatchData u t m).φ (kmswStage v m).active =
    (kmswStage u (t + m)).active at hInner
  change (kmswWindowPatchData w s (t + m)).φ
      (kmswStage u (t + m)).active = (kmswStage w (s + (t + m))).active at hOuter
  change (kmswWindowPatchData w (s + t) m).φ (kmswStage z m).active =
      (kmswStage w ((s + t) + m)).active at hDirect
  calc
    (kmswWindowPatchData w s (t + m)).φ
        ((kmswWindowPatchData u t m).φ (kmswStage v m).active) =
        (kmswWindowPatchData w s (t + m)).φ (kmswStage u (t + m)).active := by
          rw [hInner]
    _ = (kmswStage w (s + (t + m))).active := hOuter
    _ = (kmswWindowPatchData w (s + t) m).φ (kmswStage v m).active := by
      rw [hsource, htarget, ← hDirect]

/-- Side-preserving dart-map cocycle at zero depth, toward F4c; this is only a finite helper
for the whole-plane KMSW carrier and does not settle Q-F4c. -/
theorem kmswWindowDartMap_comp_zero (w : ℕ → Fin 3) (s t : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + (t + i))) 0).nextEdge) :
    kmswWindowDartMap w s t
        (kmswWindowDartMap (fun i => w (s + i)) t 0 d) =
      kmswWindowDartMap w (s + t) 0 d := by
  apply Prod.ext
  · apply Fin.ext
    exact kmswWindowPatchData_phi_comp_zero w s t d.1.val d.1.isLt
  · rfl

private theorem triangle_list_congr {u v : ℕ → Fin 3} (h : u = v) (j : ℕ)
    (hu : u j = 0 ∨ u j = 1) (hv : v j = 0 ∨ v j = 1) :
    stageTriangleDartList u ⟨j, hu⟩ = stageTriangleDartList v ⟨j, hv⟩ := by
  subst v
  rfl

private theorem triangle_comp_sum (w : ℕ → Fin 3) (s t m : ℕ)
    (hc : w (s + (t + m)) = 0 ∨ w (s + (t + m)) = 1) :
    ((stageTriangleDartList (fun i => w (s + (t + i))) ⟨m, hc⟩).map
      (fun p => (kmswWindowPatchData w s (t + (m + 1))).φ
        ((kmswWindowPatchData (fun i => w (s + i)) t (m + 1)).φ p.1))).sum =
    ((stageTriangleDartList (fun i => w (s + (t + i))) ⟨m, hc⟩).map
      (fun p => (kmswWindowPatchData w (s + t) (m + 1)).φ p.1)).sum := by
  have hi := kmswWindowPatchData_triangle_rotated (fun i => w (s + i)) t
    (m + 1) m (by omega) hc
  have ho := kmswWindowPatchData_triangle_rotated w s (t + (m + 1))
    (t + m) (by omega) hc
  have hd := kmswWindowPatchData_triangle_rotated w (s + t) (m + 1) m
    (by omega) (by simpa only [Nat.add_assoc] using hc)
  have hi' := hi.map (fun p => (kmswWindowPatchData w s (t + (m + 1))).φ p.1)
  have ho' := ho.map Prod.fst
  have hd' := hd.map Prod.fst
  simp only [List.map_map, Function.comp_def] at hi' ho' hd'
  have hh := (hi'.trans ho').perm.sum_eq
  have hh' := hd'.perm.sum_eq
  simp only [Nat.add_assoc] at hh'
  have hw : (fun i => w (s + t + i)) = (fun i => w (s + (t + i))) := by
    funext i
    rw [Nat.add_assoc]
  rw [triangle_list_congr hw m (by simpa only [Nat.add_assoc] using hc) hc] at hh'
  exact hh.trans hh'.symm

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
window patch maps; does not construct the whole-plane carrier, β_0^{L,R}, the cut or the
source identification (Q-F4c is an unanswered author question); not the paper result. -/
theorem kmswWindowPatchData_phi_comp (w : ℕ → Fin 3) (s t m e : ℕ)
    (he : e < (kmswStage (fun i => w (s + (t + i))) m).nextEdge) :
    (kmswWindowPatchData w s (t + m)).φ
        ((kmswWindowPatchData (fun i => w (s + i)) t m).φ e) =
      (kmswWindowPatchData w (s + t) m).φ e := by
  induction m generalizing e with
  | zero => exact kmswWindowPatchData_phi_comp_zero w s t e he
  | succ m ih =>
    let v := fun i => w (s + (t + i))
    have hOld (f : ℕ) (hf : f < (kmswStage v m).nextEdge) :
        (kmswWindowPatchData w s (t + (m + 1))).φ
            ((kmswWindowPatchData (fun i => w (s + i)) t (m + 1)).φ f) =
          (kmswWindowPatchData w (s + t) (m + 1)).φ f := by
      have hi := kmswWindowPatchData_extends (fun i => w (s + i)) t m f hf
      have ho := kmswWindowPatchData_extends w s (t + m)
        ((kmswWindowPatchData (fun i => w (s + i)) t m).φ f)
        ((kmswWindowPatchData_rel (fun i => w (s + i)) t m).edge_bound f hf)
      have hd := kmswWindowPatchData_extends w (s + t) m f
        (by simpa only [Nat.add_assoc] using hf)
      rw [hi]
      calc
        _ = (kmswWindowPatchData w s (t + m)).φ
            ((kmswWindowPatchData (fun i => w (s + i)) t m).φ f) := by
              simpa only [Nat.add_assoc] using ho
        _ = (kmswWindowPatchData w (s + t) m).φ f := ih f hf
        _ = _ := hd.symm
    by_cases heOld : e < (kmswStage v m).nextEdge
    · exact hOld e heOld
    have hNew := kmswWindowPatchData_phi_comp_active w s t (m + 1)
    have hActive := hOld (kmswStage v m).active
      (kmswStage_boundary_ids_lt_nextEdge v m).1
    dsimp only [v] at hActive
    by_cases h0 : v m = 0
    · cases hs : (kmswStage v m).UL.dropLast.reverse with
      | nil =>
        have hn : (kmswStage v (m + 1)).nextEdge =
            (kmswStage v m).nextEdge + 2 := by
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge]
        have ha : (kmswStage v (m + 1)).active = (kmswStage v m).nextEdge := by
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge]
        rw [show (kmswStage (fun i => w (s + (t + i)))) (m + 1) =
          kmswStage v (m + 1) from rfl, ha] at hNew
        dsimp only [v] at hNew
        have hsum := triangle_comp_sum w s t m (Or.inl h0)
        have h0' : w (s + (t + m)) = 0 := h0
        have hs' : (kmswStage (fun i => w (s + (t + i))) m).UL.dropLast.reverse =
            [] := hs
        simp only [stageTriangleDartList, stageTriangleDartTriple, h0', ite_true,
          hs', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero] at hsum
        have he' : e < (kmswStage v m).nextEdge + 2 := hn ▸ he
        have heq : e = (kmswStage v m).nextEdge ∨
            e = (kmswStage v m).nextEdge + 1 := by omega
        rcases heq with rfl | rfl
        · exact hNew
        · rw [hActive, hNew] at hsum
          exact Nat.add_left_cancel (Nat.add_left_cancel hsum)
      | cons q qs =>
        have hn : (kmswStage v (m + 1)).nextEdge =
            (kmswStage v m).nextEdge + 1 := by
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge]
        have ha : (kmswStage v (m + 1)).active = (kmswStage v m).nextEdge := by
          simp only [kmswStage, kmswStep, kmswCodeStep, h0, ite_true,
            kmswStepOfStep, hs, State.addEdge]
        have he' : e < (kmswStage v m).nextEdge + 1 := hn ▸ he
        have heq : e = (kmswStage v m).nextEdge := by omega
        subst e
        simpa only [show (fun i => w (s + (t + i))) = v from rfl, ha] using hNew
    · by_cases h1 : v m = 1
      · have hc1 : kmswCodeStep (v m) = .up := by
          rw [kmswCodeStep, ite_eq_right h0, ite_eq_left h1]
        have hn : (kmswStage v (m + 1)).nextEdge =
            (kmswStage v m).nextEdge + 2 := by
          simp only [kmswStage, kmswStep, hc1, kmswStepOfStep, State.addEdge]
        have ha : (kmswStage v (m + 1)).active = (kmswStage v m).nextEdge := by
          simp only [kmswStage, kmswStep, hc1, kmswStepOfStep, State.addEdge]
        rw [show (kmswStage (fun i => w (s + (t + i)))) (m + 1) =
          kmswStage v (m + 1) from rfl, ha] at hNew
        dsimp only [v] at hNew
        have hsum := triangle_comp_sum w s t m (Or.inr h1)
        have h0' : ¬w (s + (t + m)) = 0 := h0
        simp only [stageTriangleDartList, stageTriangleDartTriple, h0', ite_false,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
        have he' : e < (kmswStage v m).nextEdge + 2 := hn ▸ he
        have heq : e = (kmswStage v m).nextEdge ∨
            e = (kmswStage v m).nextEdge + 1 := by omega
        rcases heq with rfl | rfl
        · exact hNew
        · rw [hActive, hNew] at hsum
          exact Nat.add_right_cancel (Nat.add_left_cancel hsum)
      · cases hr : (kmswStage v m).UR with
        | nil =>
          have hn : (kmswStage v (m + 1)).nextEdge =
              (kmswStage v m).nextEdge + 1 := by
            simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
              kmswStepOfStep, hr, State.addEdge]
          have ha : (kmswStage v (m + 1)).active = (kmswStage v m).nextEdge := by
            simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
              kmswStepOfStep, hr, State.addEdge]
          have he' : e < (kmswStage v m).nextEdge + 1 := hn ▸ he
          have heq : e = (kmswStage v m).nextEdge := by omega
          subst e
          simpa only [show (fun i => w (s + (t + i))) = v from rfl, ha] using hNew
        | cons q qs =>
          have hn : (kmswStage v (m + 1)).nextEdge = (kmswStage v m).nextEdge := by
            simp only [kmswStage, kmswStep, kmswCodeStep, h0, h1, ite_false,
              kmswStepOfStep, hr]
          have he' : e < (kmswStage v m).nextEdge := hn ▸ he
          exact (heOld he').elim

/-- Helper toward F4c / the whole-plane KMSW carrier M_{−∞,∞}
with the allocation bounds transported across associativity of the window indices.
Does not construct the whole-plane carrier, β_0^{L,R}, the cut or the source identification
(Q-F4c is an unanswered author question); not the paper result. -/
theorem kmswWindowDartMap_comp (w : ℕ → Fin 3) (s t m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + (t + i))) m).nextEdge) :
    let d' : StageDart (kmswStage (fun i => w ((s + t) + i)) m).nextEdge :=
      (⟨d.1.val, by simpa only [Nat.add_assoc] using d.1.isLt⟩, d.2)
    let r := kmswWindowDartMap w (s + t) m d'
    kmswWindowDartMap w s (t + m)
        (kmswWindowDartMap (fun i => w (s + i)) t m d) =
      (⟨r.1.val, by simpa only [Nat.add_assoc] using r.1.isLt⟩, r.2) := by
  dsimp only
  apply Prod.ext
  · apply Fin.ext
    exact kmswWindowPatchData_phi_comp w s t m d.1.val d.1.isLt
  · rfl

end DirectedDistances.KMSW
