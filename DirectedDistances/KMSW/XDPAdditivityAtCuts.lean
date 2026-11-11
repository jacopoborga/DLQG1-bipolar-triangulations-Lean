module

public import DirectedDistances.KMSW.BusemannUIQBOT
public import DirectedDistances.KMSW.CutVertexDisconnects











public section
namespace DirectedDistances.KMSW

open Quiver

/-- additivity of the directed distance through a map cut vertex; the renewal times
An actual present path splits at a visited vertex, preserving length and arrows;
the concatenation has no repeated vertices by limit-graph acyclicity. -/
theorem presentPath_split_at_vertex {w : ℕ → Fin 3} {a b c : PresentVertex w}
    (r : Path a c) (hb : b ∈ r.vertices) :
    ∃ (p : Path a b) (q : Path b c),
      r = p.comp q ∧ r.length = p.length + q.length ∧
      (p.comp q).vertices.Nodup := by
  obtain ⟨p, q, rfl⟩ := r.exists_eq_comp_of_mem_vertices hb
  exact ⟨p, q, rfl, Path.length_comp p q,
    vertices_comp_nodup_of_acyclic (presentVertex_acyclic w) p q⟩

private theorem presentLdp_bot_of_unreachable {w : ℕ → Fin 3}
    {a c : PresentVertex w} (h : ¬ Reachable a c) : presentLdp a c = ⊥ := by
  let : IsEmpty (Path a c) := ⟨fun p => h ⟨p⟩⟩
  exact iSup_of_empty _

private theorem presentLdp_coe_iSup {w : ℕ → Fin 3}
    {a c : PresentVertex w} (h : Reachable a c) :
    presentLdp a c = (↑(⨆ p : Path a c, (p.length : ℕ∞)) : WithBot ℕ∞) := by
  let : Nonempty (Path a c) := h
  exact (WithBot.coe_iSup (f := fun p : Path a c => (p.length : ℕ∞))
    (OrderTop.bddAbove _)).symm

private theorem presentLdp_add_of_separator {w : ℕ → Fin 3}
    {a b c : PresentVertex w} (hb : ∀ r : Path a c, b ∈ r.vertices) :
    presentLdp a c = presentLdp a b + presentLdp b c := by
  by_cases hab : Reachable a b
  · by_cases hbc : Reachable b c
    · have hac : Reachable a c := by
        obtain ⟨p⟩ := hab
        obtain ⟨q⟩ := hbc
        exact ⟨p.comp q⟩
      let : Nonempty (Path a b) := hab
      let : Nonempty (Path b c) := hbc
      rw [presentLdp_coe_iSup hac, presentLdp_coe_iSup hab,
        presentLdp_coe_iSup hbc, ← WithBot.coe_add]
      apply congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      apply le_antisymm
      · apply iSup_le
        intro r
        obtain ⟨p, q, rfl, _, _⟩ := presentPath_split_at_vertex r (hb r)
        rw [Path.length_comp, ENat.natCast_add]
        exact add_le_add (le_iSup (fun p : Path a b => (p.length : ℕ∞)) p)
          (le_iSup (fun q : Path b c => (q.length : ℕ∞)) q)
      · apply ENat.iSup_add_iSup_le
        intro p q
        have h := le_iSup (fun r : Path a c => (r.length : ℕ∞)) (p.comp q)
        simpa only [Path.length_comp, ENat.natCast_add] using h
    · have hac : ¬ Reachable a c := by
        rintro ⟨r⟩
        obtain ⟨_, q, _, _, _⟩ := presentPath_split_at_vertex r (hb r)
        exact hbc ⟨q⟩
      rw [presentLdp_bot_of_unreachable hbc, presentLdp_bot_of_unreachable hac,
        WithBot.add_bot]
  · have hac : ¬ Reachable a c := by
      rintro ⟨r⟩
      obtain ⟨p, _, _, _, _⟩ := presentPath_split_at_vertex r (hb r)
      exact hab ⟨p⟩
    rw [presentLdp_bot_of_unreachable hab, presentLdp_bot_of_unreachable hac,
      WithBot.bot_add]

/-- additivity of the directed distance through a map cut vertex; the renewal times
Both limit-graph distances are additive at any compulsory vertex. Unreachable
LDP remains bottom, unreachable SDP remains top, and unbounded LDP is allowed. -/
theorem presentDistances_eq_add_of_forall_mem_vertices {w : ℕ → Fin 3}
    {a b c : PresentVertex w} (hb : ∀ r : Path a c, b ∈ r.vertices) :
    presentLdp a c = presentLdp a b + presentLdp b c ∧
      sdp a c = sdp a b + sdp b c :=
  ⟨presentLdp_add_of_separator hb, sdp_eq_add_of_forall_mem_vertices hb⟩

private theorem record_extremal_of_le (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    (hBn : ∀ j, n ≤ j → L w n ≤ L w j) :
    (∃ p : Path (recordVertex w m) (recordVertex w n), IsLongest p) ∧
      (∃ p : Path (recordVertex w m) (recordVertex w n), IsShortest p) := by
  rcases hmn.eq_or_lt with rfl | hmn
  · constructor
    · refine ⟨Path.nil, fun q => ?_⟩
      exact Nat.le_of_eq (presentVertex_acyclic w _ q)
    · exact ⟨Path.nil, fun _ => Nat.zero_le _⟩
  · exact recordVertex_exists_extremal w hmn hAm hAn hBn

/-- additivity of the directed distance through a map cut vertex; the renewal times
At ordered records both distances attain finite natural values. This includes
equal endpoints and supplies finiteness before any use of integer distances. -/
theorem recordVertex_distances_attained (w : ℕ → Fin 3) {m n : ℕ} (hmn : m ≤ n)
    (hAm : ∀ j < m, R w m ≤ R w j - 1)
    (hAn : ∀ j < n, R w n ≤ R w j - 1)
    (hBn : ∀ j, n ≤ j → L w n ≤ L w j) :
    ∃ p q : Path (recordVertex w m) (recordVertex w n),
      IsLongest p ∧ IsShortest q ∧
      presentLdp (recordVertex w m) (recordVertex w n) =
        ((p.length : ℕ∞) : WithBot ℕ∞) ∧
      sdp (recordVertex w m) (recordVertex w n) = (q.length : ℕ∞) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := record_extremal_of_le w hmn hAm hAn hBn
  exact ⟨p, q, hp, hq, presentLdp_eq_length hp,
    ((isShortest_iff_length_eq_sdp q).1 hq).symm⟩

/-- additivity of the directed distance through a map cut vertex; the renewal times
The finite cut-separation argument proves the compulsory visit for ordered
record times. Repeated endpoints, including the source at time zero, are allowed. -/
theorem recordVertex_distances_eq_add (w : ℕ → Fin 3) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hAb : ∀ j < b, R w b ≤ R w j - 1)
    (hBb : ∀ j, b ≤ j → L w b ≤ L w j)
    (hAc : ∀ j < c, R w c ≤ R w j - 1) :
    presentLdp (recordVertex w a) (recordVertex w c) =
      presentLdp (recordVertex w a) (recordVertex w b) +
        presentLdp (recordVertex w b) (recordVertex w c) ∧
    sdp (recordVertex w a) (recordVertex w c) =
      sdp (recordVertex w a) (recordVertex w b) +
        sdp (recordVertex w b) (recordVertex w c) := by
  apply presentDistances_eq_add_of_forall_mem_vertices
  intro p
  rcases hab.eq_or_lt with rfl | hab
  · exact p.start_mem_vertices
  · rcases hbc.eq_or_lt with rfl | hbc
    · exact p.end_mem_vertices
    · exact recordVertex_mem_path w hab hbc hAb hBb hAc p

/-- additivity of the directed distance through a map cut vertex; the renewal times
For an arbitrary map cut vertex, the source-to-cut distances are attained and
finite. Both extended distances to any endpoint split under the explicit finite
path separation hypothesis. No finiteness of the arbitrary suffix is asserted. -/
theorem mapCutVertex_distances_eq_add (w : ℕ → Fin 3)
    (hfin : ∀ u, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = u ∨ (kmswStage w n).east e = u)}.Finite)
    (htrans : Filter.Tendsto (L w) Filter.atTop Filter.atTop)
    (hR : ∀ x : ℤ, ∃ n, R w n ≤ x) (hL0 : ∀ j, 0 ≤ L w j)
    {v : ℕ} (hcut : mapCutVertex w hfin v) (z : PresentVertex w)
    (hsep : ∀ p : Path (⟨0⟩ : PresentVertex w) z, (⟨v⟩ : PresentVertex w) ∈ p.vertices) :
    (∃ p : Path (⟨0⟩ : PresentVertex w) ⟨v⟩, IsLongest p) ∧
    (∃ p : Path (⟨0⟩ : PresentVertex w) ⟨v⟩, IsShortest p) ∧
    presentLdp (⟨0⟩ : PresentVertex w) z =
      presentLdp (⟨0⟩ : PresentVertex w) ⟨v⟩ + presentLdp ⟨v⟩ z ∧
    sdp (⟨0⟩ : PresentVertex w) z =
      sdp (⟨0⟩ : PresentVertex w) ⟨v⟩ + sdp ⟨v⟩ z := by
  obtain ⟨n, hnv, _, hA, hB, _⟩ :=
    mapCutVertex_firstVisit_records w hfin htrans hR hL0 hcut
  have hv : (⟨v⟩ : PresentVertex w) = recordVertex w n := by
    cases hnv.trans (CutConverse.activeInitial_eq w n)
    rfl
  have hopt := record_extremal_of_le w (Nat.zero_le n) (by simp) hA hB
  change (∃ p : Path (⟨0⟩ : PresentVertex w) (recordVertex w n), IsLongest p) ∧
    (∃ p : Path (⟨0⟩ : PresentVertex w) (recordVertex w n), IsShortest p) at hopt
  rw [← hv] at hopt
  exact ⟨hopt.1, hopt.2, presentDistances_eq_add_of_forall_mem_vertices hsep⟩

private theorem presentLdp_self_zero (w : ℕ → Fin 3) (a : PresentVertex w) :
    presentLdp a a = 0 := by
  have hp : IsLongest (Path.nil : Path a a) :=
    fun q => Nat.le_of_eq (presentVertex_acyclic w a q)
  exact presentLdp_eq_length hp

/-- additivity of the directed distance through a map cut vertex; the renewal times
The source-to-record distance is the sum over consecutive record segments, for
both LDP and SDP, with the empty sum and repeated records included. -/
theorem recordSequence_distances_eq_sum (w : ℕ → Fin 3) (n : ℕ → ℕ)
    (hn : Monotone n) (hzero : n 0 = 0)
    (hA : ∀ k, ∀ j < n k, R w (n k) ≤ R w j - 1)
    (hB : ∀ k, ∀ j, n k ≤ j → L w (n k) ≤ L w j) (m : ℕ) :
    presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w (n m)) =
      ∑ j ∈ Finset.range m,
        presentLdp (recordVertex w (n j)) (recordVertex w (n (j + 1))) ∧
    sdp (⟨0⟩ : PresentVertex w) (recordVertex w (n m)) =
      ∑ j ∈ Finset.range m,
        sdp (recordVertex w (n j)) (recordVertex w (n (j + 1))) := by
  induction m with
  | zero =>
    have hz : recordVertex w (n 0) = (⟨0⟩ : PresentVertex w) := by
      rw [hzero]
      rfl
    rw [hz, presentLdp_self_zero, sdp_self, Finset.range_zero, Finset.sum_empty,
      Finset.sum_empty]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    have hsplit := recordVertex_distances_eq_add w (a := 0) (Nat.zero_le (n m))
      (hn (Nat.le_succ m)) (hA m) (hB m) (hA (m + 1))
    change presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w (n (m + 1))) =
        presentLdp (⟨0⟩ : PresentVertex w) (recordVertex w (n m)) +
          presentLdp (recordVertex w (n m)) (recordVertex w (n (m + 1))) ∧
      sdp (⟨0⟩ : PresentVertex w) (recordVertex w (n (m + 1))) =
        sdp (⟨0⟩ : PresentVertex w) (recordVertex w (n m)) +
          sdp (recordVertex w (n m)) (recordVertex w (n (m + 1))) at hsplit
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hsplit.1, hsplit.2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

end DirectedDistances.KMSW
