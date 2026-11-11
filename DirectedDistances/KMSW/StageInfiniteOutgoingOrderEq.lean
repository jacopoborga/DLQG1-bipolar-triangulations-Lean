module

public import DirectedDistances.KMSW.StageInfiniteOutgoingOrder
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Iterate








public section
namespace DirectedDistances.KMSW

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. Filtering a scan preserves first-return
successors. This abstract statement does not require a finite ambient type. -/
theorem firstReturn_filter_isChain {α : Type*} (σ τ : α → α) (S : α → Bool)
    (hreturn : ∀ a, S a = true → ∃ k : ℕ, 0 < k ∧ σ^[k] a = τ a ∧
      S (τ a) = true ∧ ∀ j : ℕ, 0 < j → j < k → S (σ^[j] a) = false)
    (xs : List α) (hxs : xs.IsChain (fun a b => σ a = b)) :
    (xs.filter S).IsChain (fun a b => τ a = b) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    have htail : xs.IsChain (fun a b => σ a = b) := hxs.tail
    have hi := ih htail
    by_cases ha : S a = true
    · simp only [List.filter_cons, ha, ↓reduceIte]
      cases heq : xs.filter S with
      | nil => exact .singleton a
      | cons b bs =>
        rw [heq] at hi
        apply List.IsChain.cons_cons ?_ hi
        obtain ⟨pre, post, hexs, hpre, hb, _⟩ := List.filter_eq_cons_iff.mp heq
        have hc : (a :: (pre ++ b :: post)).IsChain (fun x y => σ x = y) :=
          hexs ▸ hxs
        have hpow : σ^[pre.length + 1] a = b := by
          have hh := hc.iterate_eq_of_apply_eq (pre.length + 1) (by simp)
          simpa using hh
        have hgap (j : ℕ) (hj : 0 < j) (hjk : j < pre.length + 1) :
            S (σ^[j] a) = false := by
          have hidx : j - 1 < pre.length := by omega
          have hj' : j = (j - 1) + 1 := by omega
          have hv : σ^[j] a = pre[j - 1] := by
            calc
              σ^[j] a = σ^[j - 1 + 1] a := congrArg (fun i => σ^[i] a) hj'
              _ = pre[j - 1] := by
                have hh := hc.iterate_eq_of_apply_eq (j - 1 + 1) (by simp; omega)
                simpa only [List.getElem_cons_zero, List.getElem_cons_succ,
                  List.getElem_append_left hidx] using hh
          rw [hv]
          exact Bool.eq_false_iff.mpr (hpre _ (List.getElem_mem hidx))
        obtain ⟨k, hk, hret, hS, hbefore⟩ := hreturn a ha
        have hkeq : k = pre.length + 1 := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hf := hgap k hk hlt
            rw [hret, hS] at hf
            contradiction
          · have hf := hbefore (pre.length + 1) (by omega) hgt
            rw [hpow, hb] at hf
            contradiction
        rw [hkeq, hpow] at hret
        exact hret.symm
    · simpa only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte] using hi

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. A deterministic chain is its scan from
the first entry. -/
private theorem chain_eq_scan {α : Type*} (τ : α → α) (xs : List α)
    (hxs : xs.IsChain (fun a b => τ a = b)) :
    xs = match xs.head? with
      | none => []
      | some a => List.iterate τ a xs.length := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [List.head?_cons]
    apply List.ext_getElem
    · simp only [List.length_iterate]
    · intro i hi hi'
      simpa only [List.getElem_iterate, List.getElem_cons_zero] using
        (hxs.iterate_eq_of_apply_eq i hi).symm

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. Filter any finite scan from any cut by
membership in a return set, then by a predicate. The result is the return-map
scan from the first retained dart, filtered by that predicate. Empty scans are
included. Apply with an inverse permutation for the inverse-rotation scan. -/
theorem firstReturn_filter_scan {α : Type*} (σ τ : α → α) (S P : α → Bool)
    (hreturn : ∀ a, S a = true → ∃ k : ℕ, 0 < k ∧ σ^[k] a = τ a ∧
      S (τ a) = true ∧ ∀ j : ℕ, 0 < j → j < k → S (σ^[j] a) = false)
    (c : α) (N : ℕ) :
    let ys := (List.iterate σ c N).filter S
    ys.filter P = (match ys.head? with
      | none => []
      | some a => List.iterate τ a ys.length).filter P := by
  dsimp only
  have hc : (List.iterate σ c N).IsChain (fun a b => σ a = b) :=
    List.IsChain.iterate (fun _ => rfl)
  exact congrArg (List.filter P)
    (chain_eq_scan τ _ (firstReturn_filter_isChain σ τ S hreturn _ hc))

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. Removing repetitions commutes with
filtering, while preserving the first occurrence of every retained dart. -/
theorem eraseDups_filter_eq {α : Type*} [DecidableEq α] (P : α → Bool)
    (xs : List α) : (xs.filter P).eraseDups = xs.eraseDups.filter P := by
  classical
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      have hlt : (xs.filter (fun b => !(b == a))).length < n := by
        have := List.length_filter_le (fun b => !(b == a)) xs
        simp only [List.length_cons] at hn
        omega
      have he := ih _ hlt _ rfl
      have hcomm : (xs.filter (fun b => !(b == a))).filter P =
          (xs.filter P).filter (fun b => !(b == a)) := by
        simp only [List.filter_filter]
        congr 1
        funext b
        exact Bool.and_comm _ _
      rw [List.eraseDups_cons, List.filter_cons]
      cases ha : P a with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, ha]
        have hself : (xs.filter P).filter (fun b => !(b == a)) = xs.filter P := by
          apply List.filter_eq_self.mpr
          intro b hb
          have hp := (List.mem_filter.mp hb).2
          have hne : b ≠ a := by
            intro heq
            subst b
            rw [ha] at hp
            contradiction
          simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using hne
        rw [← he, hcomm, hself]
      | true =>
        simp only [↓reduceIte, List.eraseDups_cons, List.filter_cons, ha]
        rw [← he, hcomm]

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem nodup_eraseDups_self {α : Type*} [DecidableEq α] (xs : List α)
    (hxs : xs.Nodup) : xs.eraseDups = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hxs
    rw [List.eraseDups_cons]
    have hf : xs.filter (fun b => !(b == a)) = xs := by
      apply List.filter_eq_self.mpr
      intro b hb
      have hne : b ≠ a := by rintro rfl; exact ha hb
      simpa only [Bool.not_eq_true', beq_eq_false_iff_ne] using hne
    rw [hf, ih ht]

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. A repetition-free successor chain with
the correct members normalizes a periodic scan, including repeated full turns. -/
theorem scan_filter_eraseDups_eq_of_chain {α : Type*} [DecidableEq α]
    (τ : α → α) (a : α) (N : ℕ) (hN : 0 < N) (hperiod : τ^[N] a = a)
    (P : α → Bool) (ys : List α) (hnd : ys.Nodup)
    (hc : ys.IsChain (fun x y => τ x = y)) (hh : ys.head? = some a)
    (hm : ∀ x, x ∈ ys ↔ x ∈ List.iterate τ a N ∧ P x = true) :
    ((List.iterate τ a N).filter P).eraseDups = ys := by
  have hne : ys ≠ [] := by intro he; simp only [he, List.head?_nil] at hh; contradiction
  have hpos : 0 < ys.length := by cases ys <;> simp_all
  have hzero : ys[0] = a := by
    simpa only [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos,
      Option.some.injEq] using hh
  have hlen : ys.length ≤ N := by
    by_contra hn
    have hlt : N < ys.length := by omega
    have h := hc.iterate_eq_of_apply_eq N hlt
    rw [hzero, hperiod] at h
    have heq : ys[N] = ys[0] := h.symm.trans hzero.symm
    have := hnd.getElem_inj_iff.mp heq
    omega
  have hscan : ys = List.iterate τ a ys.length := by
    simpa only [hh] using chain_eq_scan τ ys hc
  let rest := List.iterate τ (τ^[ys.length] a) (N - ys.length)
  have hsplit : List.iterate τ a N = ys ++ rest := by
    conv_lhs => rw [← Nat.add_sub_of_le hlen]
    rw [List.iterate_add, ← hscan]
  have hfilter : ys.filter P = ys :=
    List.filter_eq_self.mpr (fun x hx => ((hm x).mp hx).2)
  have hrest : (rest.filter P).removeAll ys = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hx' : x ∈ ys := (hm x).mpr ⟨?_, (List.mem_filter.mp hx).2⟩
    · simp only [List.elem_eq_mem, hx', decide_true,
        Bool.not_true, Bool.false_eq_true, not_false_eq_true]
    · rw [hsplit]
      exact List.mem_append_right ys (List.mem_filter.mp hx).1
  rw [hsplit, List.filter_append, hfilter, List.eraseDups_append,
    nodup_eraseDups_self ys hnd, hrest, List.eraseDups_nil, List.append_nil]

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private def stageInverseReturn (w : ℕ → Fin 3) (n : ℕ)
    (d : ℕ × Bool) : ℕ × Bool :=
  if h : d.1 < (kmswStage w n).nextEdge then
    let e := (stageRot w n).symm (⟨d.1, h⟩, d.2)
    (e.1.val, e.2)
  else d

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem stageInverseReturn_spec (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) (a : ℕ × Bool) (ha : decide (a.1 < (kmswStage w n).nextEdge) = true) :
    ∃ k : ℕ, 0 < k ∧ ((kmswInfRot w hfin).symm : (ℕ × Bool) → ℕ × Bool)^[k] a =
      stageInverseReturn w n a ∧
      decide ((stageInverseReturn w n a).1 < (kmswStage w n).nextEdge) = true ∧
      ∀ j : ℕ, 0 < j → j < k →
        decide ((((kmswInfRot w hfin).symm : (ℕ × Bool) → ℕ × Bool)^[j] a).1 <
          (kmswStage w n).nextEdge) = false := by
  have hlt : a.1 < (kmswStage w n).nextEdge := of_decide_eq_true ha
  let d : StageDart (kmswStage w n).nextEdge := (⟨a.1, hlt⟩, a.2)
  obtain ⟨k, hk, heq, hgap⟩ := kmswInfRot_symm_firstReturn_stage w hfin n d
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · simpa only [Equiv.Perm.coe_pow, stageInverseReturn, dite_eq_left hlt, d] using heq
  · simp only [stageInverseReturn, dite_eq_left hlt, decide_eq_true_eq]
    exact ((stageRot w n).symm d).1.isLt
  · intro j hj hjk
    have hg := hgap j hj hjk
    simpa only [decide_eq_false_iff_not, not_lt, Equiv.Perm.coe_pow, d] using hg

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The allocated darts retained from any
inverse infinite rotation chain form an inverse stage rotation chain. -/
theorem stage_inverse_filter_isChain (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (n : ℕ) (xs : List (ℕ × Bool))
    (hxs : xs.IsChain (fun a b => (kmswInfRot w hfin).symm a = b)) :
    (xs.filter (fun d => decide (d.1 < (kmswStage w n).nextEdge))).IsChain
      (fun a b => ∃ da db : StageDart (kmswStage w n).nextEdge,
        (da.1.val, da.2) = a ∧ (db.1.val, db.2) = b ∧
          (stageRot w n).symm da = db) := by
  have hc := firstReturn_filter_isChain (kmswInfRot w hfin).symm
    (stageInverseReturn w n) (fun d => decide (d.1 < (kmswStage w n).nextEdge))
    (stageInverseReturn_spec w hfin n) xs hxs
  apply hc.imp_of_mem_imp
  intro a b ha hb hab
  have hal : a.1 < (kmswStage w n).nextEdge := of_decide_eq_true (List.mem_filter.mp ha).2
  let da : StageDart (kmswStage w n).nextEdge := (⟨a.1, hal⟩, a.2)
  refine ⟨da, (stageRot w n).symm da, rfl, ?_, rfl⟩
  simpa only [stageInverseReturn, dite_eq_left hal, da] using hab

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem infinite_outgoing_inverse_chain (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (v : ℕ)
    (hv : ∃ n, v < (kmswStage w n).nextVertex) :
    ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR v hv).map
      (fun e => (e, false))).IsChain (fun a b => (kmswInfRot w hfin).symm a = b) := by
  rw [List.isChain_map]
  unfold kmswOutgoingEdgesLeftToRight
  split
  · rw [List.isChain_reverse]
    have hc := (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.2.2.2.2
    exact hc.imp (fun a b hab => (kmswInfRot w hfin).symm_apply_eq.mpr hab.symm)
  · rename_i hn
    rw [List.isChain_reverse]
    have hen := kmsw_nonzero_outgoing_enumeration w hfin hL hR v hv hn
    have hc := hen.choose_spec.choose_spec.choose_spec.2.2.2.2.1
    exact hc.imp (fun a b hab => (kmswInfRot w hfin).symm_apply_eq.mpr hab.symm)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem incoming_cut_head (w : ℕ → Fin 3) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge)
    (hi : (stageRot w n corner).2 = true) (xs : List (ℕ × Bool))
    (hc : xs.IsChain (fun a b => ∃ da db : StageDart (kmswStage w n).nextEdge,
      (da.1.val, da.2) = a ∧ (db.1.val, db.2) = b ∧ (stageRot w n).symm da = db))
    (hb : ∀ a ∈ xs, a.2 = false) (hm : (corner.1.val, corner.2) ∈ xs) :
    xs.head? = some (corner.1.val, corner.2) := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hm
  | cons a xs ih =>
    by_cases ha : a = (corner.1.val, corner.2)
    · simp only [List.head?_cons, ha]
    · have hmt : (corner.1.val, corner.2) ∈ xs := (List.mem_cons.mp hm).resolve_left
        (fun h => ha h.symm)
      have hh := ih hc.tail (fun b h => hb b (List.mem_cons_of_mem a h)) hmt
      obtain ⟨da, db, hda, hdb, hrot⟩ := hc.rel_head? hh
      have heq : db = corner := Prod.ext
        (Fin.ext (congrArg (fun d : ℕ × Bool => d.1) hdb))
        (congrArg (fun d : ℕ × Bool => d.2) hdb)
      rw [heq] at hrot
      have hr : da = stageRot w n corner := (stageRot w n).symm_apply_eq.mp hrot
      have hf : da.2 = false :=
        (congrArg (fun d : ℕ × Bool => d.2) hda).trans (hb a List.mem_cons_self)
      rw [hr, hi] at hf
      contradiction

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. At an incoming-block cut, the first
allocated outgoing geometric edge in the infinite order is the stage corner.
Presence at the finite stage is deliberately not required in this assertion. -/
theorem infinite_outgoing_old_head_incomingCut (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge)
    (hd : corner.2 = false) (hi : (stageRot w n corner).2 = true) :
    ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
      (stageEndpoint (kmswStage w n) corner)
      ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
        (fun e => decide (e < (kmswStage w n).nextEdge))).head? = some corner.1.val := by
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
    (stageEndpoint (kmswStage w n) corner) ⟨n, stageEndpoint_lt_nextVertex w n corner⟩
  have hc := stage_inverse_filter_isChain w hfin n (es.map (fun e => (e, false)))
    (infinite_outgoing_inverse_chain w hfin hL htrans hR _ _)
  have hv : edgeWest w corner.1.val = stageEndpoint (kmswStage w n) corner := by
    simp only [stageEndpoint, hd, Bool.false_eq_true, ↓reduceIte,
      (edge_endpoints_eq w corner.1.isLt).1]
  have hem : corner.1.val ∈ es := (mem_kmswOutgoingEdgesLeftToRight w hfin hL
    htrans hR _ _ _).mpr ⟨edgePresent_of_nonneg_of_unbounded w hL hR _, hv⟩
  have hh := incoming_cut_head w n corner hi _ hc (by
    intro a ha
    obtain ⟨e, _, he⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
    exact congrArg (fun d : ℕ × Bool => d.2) he.symm) (by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_map.mpr ⟨corner.1.val, hem, Prod.ext rfl hd.symm⟩
    · simpa only [decide_eq_true_eq] using corner.1.isLt)
  rw [List.filter_map, List.head?_map] at hh
  change Option.map (fun e => (e, false))
    ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) =
      some (corner.1.val, corner.2) at hh
  change ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) = _
  cases he : (es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head? with
  | none => simp only [he, Option.map_none, reduceCtorEq] at hh
  | some e =>
    simp only [he, Option.map_some, Option.some.injEq] at hh
    exact congrArg some (congrArg (fun d : ℕ × Bool => d.1) hh)

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. -/
private theorem old_outgoing_stage_list (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge) (hd : corner.2 = false)
    (hh : ((kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
      (stageEndpoint (kmswStage w n) corner)
      ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
        (fun e => decide (e < (kmswStage w n).nextEdge))).head? = some corner.1.val) :
    ∃ ys : List (StageDart (kmswStage w n).nextEdge), ys.Nodup ∧
      ys.head? = some corner ∧ ys.IsChain (fun a b => (stageRot w n).symm a = b) ∧
      (∀ d, d ∈ ys ↔ d.2 = false ∧
        stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) corner) ∧
      ys.map (fun d => d.1.val) =
        (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
          (stageEndpoint (kmswStage w n) corner)
          ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
            (fun e => decide (e < (kmswStage w n).nextEdge)) := by
  classical
  let es := kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
    (stageEndpoint (kmswStage w n) corner) ⟨n, stageEndpoint_lt_nextVertex w n corner⟩
  let xs := (es.map (fun e => (e, false))).filter
    (fun d => decide (d.1 < (kmswStage w n).nextEdge))
  let C : (ℕ × Bool) → StageDart (kmswStage w n).nextEdge := fun d =>
    if h : d.1 < (kmswStage w n).nextEdge then (⟨d.1, h⟩, d.2) else corner
  have hC (d : StageDart (kmswStage w n).nextEdge) : C (d.1.val, d.2) = d := by
    simp only [C, dite_eq_left d.1.isLt]
  have hx (d : ℕ × Bool) (hm : d ∈ xs) : d.1 < (kmswStage w n).nextEdge :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  have hCx (d : ℕ × Bool) (hm : d ∈ xs) : ((C d).1.val, (C d).2) = d := by
    simp only [C, dite_eq_left (hx d hm)]
  have hnd : es.Nodup := by
    unfold es kmswOutgoingEdgesLeftToRight
    split
    · exact List.nodup_reverse.mpr
        (kmsw_source_outgoing_enumeration w hfin hL htrans hR).choose_spec.1
    · rename_i hn
      have hen := kmsw_nonzero_outgoing_enumeration w hfin hL hR _
        ⟨n, stageEndpoint_lt_nextVertex w n corner⟩ hn
      exact List.nodup_reverse.mpr
        hen.choose_spec.choose_spec.choose_spec.1
  have hnx : xs.Nodup := (hnd.map (by
    intro a b hab
    exact congrArg (fun d : ℕ × Bool => d.1) hab)).filter _
  have hc := stage_inverse_filter_isChain w hfin n (es.map (fun e => (e, false)))
    (infinite_outgoing_inverse_chain w hfin hL htrans hR _ _)
  refine ⟨xs.map C, ?_, ?_, ?_, ?_, ?_⟩
  · apply hnx.map_on
    intro a ha b hb heq
    exact (hCx a ha).symm.trans ((congrArg (fun d => (d.1.val, d.2)) heq).trans
      (hCx b hb))
  · rw [List.head?_map]
    have hhead : xs.head? = some (corner.1.val, corner.2) := by
      change ((es.map (fun e => (e, false))).filter
        (fun d => decide (d.1 < (kmswStage w n).nextEdge))).head? = _
      rw [List.filter_map, List.head?_map]
      change Option.map (fun e => (e, false))
        ((es.filter (fun e => decide (e < (kmswStage w n).nextEdge))).head?) = _
      rw [hh, Option.map_some, hd]
    rw [hhead, Option.map_some, hC]
  · rw [List.isChain_map]
    exact hc.imp (by
      rintro a b ⟨da, db, hda, hdb, hrot⟩
      rw [← hda, ← hdb, hC, hC]
      exact hrot)
  · intro d
    rw [List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_filter.mp ha).1
      have hav : edgeWest w a.1 = stageEndpoint (kmswStage w n) corner := by
        rw [← heq]
        exact ((mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ e).mp he).2
      have hab : a.2 = false := congrArg (fun d : ℕ × Bool => d.2) heq.symm
      have hb : (C a).2 = false :=
        (congrArg (fun d : ℕ × Bool => d.2) (hCx a ha)).trans hab
      have he : (C a).1.val = a.1 := congrArg (fun d : ℕ × Bool => d.1) (hCx a ha)
      refine ⟨hb, ?_⟩
      calc
        stageEndpoint (kmswStage w n) (C a) = edgeWest w a.1 := by
          simp only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte]
          rw [(edge_endpoints_eq w (C a).1.isLt).1, he]
        _ = _ := hav
    · rintro ⟨hb, hv⟩
      have hw : edgeWest w d.1.val = stageEndpoint (kmswStage w n) corner := by
        simpa only [stageEndpoint, hb, Bool.false_eq_true, ↓reduceIte,
          (edge_endpoints_eq w d.1.isLt).1] using hv
      refine ⟨(d.1.val, d.2), ?_, hC d⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨d.1.val, ?_, Prod.ext rfl hb.symm⟩, ?_⟩
      · exact (mem_kmswOutgoingEdgesLeftToRight w hfin hL htrans hR _ _ _).mpr
          ⟨edgePresent_of_nonneg_of_unbounded w hL hR _, hw⟩
      · simpa only [decide_eq_true_eq] using d.1.isLt
  · rw [List.map_map]
    change xs.map (fun d => (C d).1.val) = _
    have heq : xs.map (fun d => (C d).1.val) = xs.map Prod.fst := by
      apply List.map_congr_left
      intro d hd
      exact congrArg (fun a : ℕ × Bool => a.1) (hCx d hd)
    rw [heq]
    simp [xs, List.filter_map, List.map_map, Function.comp_def, es]

/-- infinite outgoing rotation order in the KMSW code realization; T_m, F4c and both-mode scope
are not treated; not the paper result. The incoming-block cut gives equality
of the stage and restricted infinite outgoing edge orders. -/
theorem stageOutgoingEdgeOrder_eq_infinite_filter_incomingCut (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ m, e < (kmswStage w m).nextEdge ∧
      ((kmswStage w m).west e = v ∨ (kmswStage w m).east e = v)}.Finite)
    (hL : ∀ j, 0 ≤ L w j) (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ a : ℤ, ∃ m, R w m ≤ a) (n : ℕ)
    (corner : StageDart (kmswStage w n).nextEdge)
    (hd : corner.2 = false) (hi : (stageRot w n corner).2 = true) :
    stageOutgoingEdgeOrder w n corner =
      (kmswOutgoingEdgesLeftToRight w hfin hL htrans hR
        (stageEndpoint (kmswStage w n) corner)
        ⟨n, stageEndpoint_lt_nextVertex w n corner⟩).filter
          (fun e => decide (e < (kmswStage w n).nextEdge ∧
            (kmswStage w n).present e = true)) := by
  classical
  obtain ⟨ys, hnd, hh, hc, hm, he⟩ := old_outgoing_stage_list w hfin hL htrans hR n
    corner hd (infinite_outgoing_old_head_incomingCut w hfin hL htrans hR n corner hd hi)
  let τ : Equiv.Perm (StageDart (kmswStage w n).nextEdge) := (stageRot w n).symm
  let N := orderOf τ
  let raw := List.iterate (τ : StageDart (kmswStage w n).nextEdge → _) corner N
  let P : StageDart (kmswStage w n).nextEdge → Bool := fun d =>
    decide (stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) corner ∧
      d.2 = false)
  let Q : StageDart (kmswStage w n).nextEdge → Bool := fun d =>
    decide ((kmswStage w n).present d.1.val = true)
  have hmem (d : StageDart (kmswStage w n).nextEdge) :
      d ∈ ys ↔ d ∈ raw ∧ P d = true := by
    rw [hm]
    constructor
    · rintro ⟨hb, hv⟩
      have hcycle := Equiv.Perm.sameCycle_inv.mpr
        ((stageRot_sameCycle_iff_endpoint_eq w n corner d).mpr hv.symm)
      obtain ⟨i, hi, hp⟩ := hcycle.exists_pow_eq'
      refine ⟨List.mem_iterate.mpr ⟨i, hi, ?_⟩, ?_⟩
      · simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_inv, τ] using hp.symm
      · exact decide_eq_true (And.intro hv hb)
    · rintro ⟨_, hp⟩
      exact ((of_decide_eq_true hp : _ ∧ _)).symm
  have hperiod : (τ : StageDart (kmswStage w n).nextEdge → _)^[N] corner = corner := by
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hnorm : (raw.filter P).eraseDups = ys :=
    scan_filter_eraseDups_eq_of_chain τ corner N (orderOf_pos τ) hperiod P ys hnd hc hh hmem
  have hraw : (List.ofFn fun i : Fin (orderOf (stageRot w n).symm) =>
      ((stageRot w n).symm ^ i.val) corner) = raw := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_iterate, raw, N, τ]
    · intro i hi hi'
      simp only [List.getElem_ofFn, List.getElem_iterate, raw, Equiv.Perm.coe_pow, τ]
  have hfilters : (raw.filter fun d =>
      decide (stageEndpoint (kmswStage w n) d = stageEndpoint (kmswStage w n) corner ∧
        (kmswStage w n).present d.1.val = true ∧ d.2 = false)) =
      (raw.filter P).filter Q := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro d _
    simp [P, Q, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  have hstage : stageOutgoingDartOrder w n corner = ys.filter Q := by
    unfold stageOutgoingDartOrder
    rw [hraw, hfilters, eraseDups_filter_eq, hnorm]
  unfold stageOutgoingEdgeOrder
  rw [hstage]
  have hefilter := congrArg
    (List.filter (fun e => decide ((kmswStage w n).present e = true))) he
  rw [List.filter_map, List.filter_filter] at hefilter
  simpa [Function.comp_def, Q, Bool.and_comm] using hefilter

end DirectedDistances.KMSW
