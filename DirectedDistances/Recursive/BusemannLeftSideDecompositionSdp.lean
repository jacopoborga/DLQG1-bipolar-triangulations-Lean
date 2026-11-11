module

public import DirectedDistances.DirectedPath.Distance
public import DirectedDistances.Recursive.BusemannLeftSideDecomposition
import DirectedDistances.DirectedPath.Extremal

public section
namespace DirectedDistances.Recursive

open DirectedDistances.KMSW Quiver

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The minimum of a set of natural path lengths, viewed in `ℕ∞`; the empty set has value -/
@[expose] noncomputable def leftLengthMin (s : Set ℕ) : ℕ∞ :=
  by
    classical
    exact if h : s.Nonempty then ((sInf s : ℕ) : ℕ∞) else ⊤

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
For a nonempty set, the minimum is its natural infimum. Source: -/
private theorem leftLengthMin_eq_sInf {s : Set ℕ} (hs : s.Nonempty) :
    leftLengthMin s = ((sInf s : ℕ) : ℕ∞) := by
  rw [leftLengthMin, dite_eq_left hs]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An empty set of lengths has minimum `⊤`. Source: -/
private theorem leftLengthMin_eq_top {s : Set ℕ} (hs : s = ∅) :
    leftLengthMin s = ⊤ := by
  rw [leftLengthMin, hs]
  simp

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The infimum of a nonempty natural length set is an attained least element. Source: -/
private theorem leftLengthMin_eq_of_isLeast {s : Set ℕ} {n : ℕ}
    (hn : IsLeast s n) : leftLengthMin s = (n : ℕ∞) := by
  rw [leftLengthMin_eq_sInf ⟨n, hn.1⟩]
  have hle : sInf s ≤ n := Nat.sInf_le hn.1
  have hge : n ≤ sInf s := hn.2 (Nat.sInf_mem ⟨n, hn.1⟩)
  exact congrArg (fun m : ℕ => (m : ℕ∞)) (Nat.le_antisymm hle hge)

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every nonempty set of natural lengths has its infimum as a least element. Source: -/
private theorem leftLengthMin_isLeast (s : Set ℕ) (hs : s.Nonempty) :
    IsLeast s (sInf s) :=
  ⟨Nat.sInf_mem hs, fun _ hn => Nat.sInf_le hn⟩

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
The shortest-distance first-entry decomposition, as an infimum over beta vertices of
the sum of the minimum primed-entry and hatted path lengths. Empty sets contribute
`⊤`, so unreachable pairs retain the SDP convention. Source: -/
theorem leftHat_sdp_beta (w : ℕ → Fin 3)
    (hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
      ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite)
    (hb : BoundaryHitWitnesses w) {x y : PresentVertex w}
    (hx : x ∉ leftHatVertices w) (hy : y ∈ leftHatVertices w) :
    sdp x y = ⨅ t : ℕ,
      leftLengthMin (leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩) +
      leftLengthMin (leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y) := by
  classical
  let aSet (t : ℕ) := leftPrimedEntryLengths w x ⟨kmswBeta0Vertices w hfin hb t⟩
  let bSet (t : ℕ) := leftHatPathLengths w ⟨kmswBeta0Vertices w hfin hb t⟩ y
  have hterm (t : ℕ) : sdp x y ≤ leftLengthMin (aSet t) + leftLengthMin (bSet t) := by
    by_cases ha : (aSet t).Nonempty
    · by_cases hbt : (bSet t).Nonempty
      · let m := sInf (aSet t)
        let n := sInf (bSet t)
        have hm : IsLeast (aSet t) m := by
          exact leftLengthMin_isLeast _ ha
        have hn : IsLeast (bSet t) n := by
          exact leftLengthMin_isLeast _ hbt
        obtain ⟨pa, hpa, _⟩ := hm.1
        obtain ⟨pb, hpb, _⟩ := hn.1
        have hsum : leftLengthMin (aSet t) + leftLengthMin (bSet t) =
            ((pa.length + pb.length : ℕ) : ℕ∞) := by
          rw [leftLengthMin_eq_of_isLeast hm, leftLengthMin_eq_of_isLeast hn]
          calc
            (m : ℕ∞) + (n : ℕ∞) = ((m + n : ℕ) : ℕ∞) := ENat.natCast_add _ _
            _ = ((pa.length + pb.length : ℕ) : ℕ∞) := by rw [← hpa, ← hpb]
        calc
          sdp x y ≤ (pa.comp pb).length := sdp_le_length _
          _ = ((pa.length + pb.length : ℕ) : ℕ∞) := by
            rw [Path.length_comp, ENat.natCast_add]
          _ = leftLengthMin (aSet t) + leftLengthMin (bSet t) := hsum.symm
      · rw [leftLengthMin_eq_top (Set.not_nonempty_iff_eq_empty.mp hbt)]
        simp
    · rw [leftLengthMin_eq_top (Set.not_nonempty_iff_eq_empty.mp ha)]
      simp
  by_cases hr : Reachable x y
  · obtain ⟨p, hp⟩ := exists_isShortest hr
    have hpmem : p.length ∈ pathLengths x y := ⟨p, rfl⟩
    have hdecomp := leftHat_pathLengths_beta w hfin hb hx hy
    rw [hdecomp] at hpmem
    obtain ⟨t, a, ha, b, hbt, hpab⟩ := hpmem
    obtain ⟨pa, hpa, haSide⟩ := ha
    obtain ⟨pb, hpb, hbSide⟩ := hbt
    have hAleast : IsLeast (aSet t) a := by
      refine ⟨⟨pa, hpa, haSide⟩, ?_⟩
      intro m hm
      obtain ⟨q, hq, _⟩ := hm
      have hshort := hp (q.comp pb)
      rw [Path.length_comp, hpab, hq, hpb] at hshort
      exact Nat.le_of_add_le_add_right hshort
    have hBleast : IsLeast (bSet t) b := by
      refine ⟨⟨pb, hpb, hbSide⟩, ?_⟩
      intro n hn
      obtain ⟨q, hq, _⟩ := hn
      have hshort := hp (pa.comp q)
      rw [Path.length_comp, hpab, hpa, hq] at hshort
      exact Nat.le_of_add_le_add_left hshort
    have hsum :
        leftLengthMin (aSet t) + leftLengthMin (bSet t) = (p.length : ℕ∞) := by
      rw [leftLengthMin_eq_of_isLeast hAleast, leftLengthMin_eq_of_isLeast hBleast]
      calc
        (a : ℕ∞) + (b : ℕ∞) = ((a + b : ℕ) : ℕ∞) := ENat.natCast_add _ _
        _ = (p.length : ℕ∞) := congrArg (fun n : ℕ => (n : ℕ∞)) hpab.symm
    have hpEq : (p.length : ℕ∞) = sdp x y :=
      (isShortest_iff_length_eq_sdp p).mp hp
    apply le_antisymm
    · exact le_iInf hterm
    · calc
        (⨅ k : ℕ, leftLengthMin (aSet k) + leftLengthMin (bSet k)) ≤
            leftLengthMin (aSet t) + leftLengthMin (bSet t) := iInf_le _ t
        _ = sdp x y := hsum.trans hpEq
  · rw [sdp_eq_top_iff_not_reachable.mpr hr]
    apply le_antisymm
    · apply le_iInf
      intro t
      have hempty : (aSet t) = ∅ ∨ (bSet t) = ∅ := by
        by_cases ha : (aSet t).Nonempty
        · by_cases hbt : (bSet t).Nonempty
          · obtain ⟨a, ⟨pa, _, _⟩⟩ := ha
            obtain ⟨b, ⟨pb, _, _⟩⟩ := hbt
            exact (hr ⟨pa.comp pb⟩).elim
          · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hbt)
        · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp ha)
      rcases hempty with ha | hbt
      · rw [leftLengthMin_eq_top ha]
        simp
      · rw [leftLengthMin_eq_top hbt]
        simp
    · exact le_top

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
An excursion between visits to a shortest geodesic can be replaced by its geodesic
segment with no change of optimal total length. `P` is the raw infinite path, with
shortest segments as for the leftmost SDP geodesic. Source: -/
theorem leftSdpGeodesic_replace_excursion {w : ℕ → Fin 3}
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments)
    (i j : ℕ) {x y : PresentVertex w}
    (a : Path x (P.initial i).1) (b : Path (P.initial i).1 (P.initial j).1)
    (c : Path (P.initial j).1 y) (hp : IsShortest ((a.comp b).comp c)) :
    ∃ s : Path (P.initial i).1 (P.initial j).1,
      i ≤ j ∧ s.length = j - i ∧
      pathEdgeList s = List.ofFn (fun k : Fin (j - i) => P.edge (i + k.val)) ∧
      s.length = b.length ∧ IsShortest ((a.comp s).comp c) := by
  have hij : i ≤ j := by
    by_contra hn
    have hji : j ≤ i := by omega
    have H := P.exists_shift_split j (i - j)
    rw [Nat.add_sub_of_le hji] at H
    obtain ⟨_, r, _, _, hr, _⟩ := H
    have hz := presentVertex_acyclic w _ (r.comp b)
    rw [Path.length_comp, hr] at hz
    omega
  have H := P.exists_shift_split i (j - i)
  rw [Nat.add_sub_of_le hij] at H
  obtain ⟨r, s, heq, _, hslen, hsedge⟩ := H
  have hshort := P.initial_isShortest w hP j
  rw [heq] at hshort
  have hle : s.length ≤ b.length := hshort.of_comp_right b
  have he : s.length = b.length := le_antisymm hle (hp.of_comp_middle s)
  refine ⟨s, hij, hslen, hsedge, he, ?_⟩
  apply hp.of_length_eq
  simp only [Path.length_comp, he]

/-- Helper toward Lemma 5.5 (lem-geo-infty-ind) and Theorem 1.7; not a paper result.
Every prefix of the raw shortest geodesic has attained root SDP equal to its index, -/
theorem leftSdpGeodesic_root_distance {w : ℕ → Fin 3}
    (P : InfinitePresentPath w ⟨0⟩) (hP : P.HasShortestSegments) (t : ℕ) :
    sdp (⟨0⟩ : PresentVertex w) (P.initial t).1 = (t : ℕ∞) := by
  rw [← (isShortest_iff_length_eq_sdp (P.initial t).2).mp
      (P.initial_isShortest w hP t), P.prefix_length]

end DirectedDistances.Recursive
