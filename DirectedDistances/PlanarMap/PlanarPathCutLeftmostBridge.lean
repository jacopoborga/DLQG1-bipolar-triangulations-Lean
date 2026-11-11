module

public import DirectedDistances.PlanarMap.PlanarPathCutNoStrictLeft

/-! # Geometric characterization of lex-leftmost XDP geodesics

Helpers toward the paper definition `def-geodesic` -/

public section
namespace DirectedDistances.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {ℓ r : ℕ}

/-- The paper's geometric leftmost condition, expressed as exclusion of every
geodesic dart from the strict-left region of the path cut. This records the
paper result. -/
@[expose] def IsGeometricLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) : Prop :=
  IsXDPGeodesicBase B x P ∧
    ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
      IsXDPGeodesicBase B x Q → ∀ d ∈ Q.darts,
        d ∉ pathCutLeftDarts B P \ pathCutSeamDarts B P

/-- The strict-left exclusion form of geometric leftmostness is equivalent to
requiring every competing geodesic dart to lie in the closed right half of the -/
theorem isGeometricLeftmost_iff_geodesics_in_rightHalf
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsGeometricLeftmostXDPGeodesic B x P ↔
      IsXDPGeodesicBase B x P ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
          IsXDPGeodesicBase B x Q → ∀ d ∈ Q.darts,
            d ∈ pathCutRightHalfDarts B P := by
  constructor
  · rintro ⟨hP, hleft⟩
    refine ⟨hP, ?_⟩
    intro m Q hQ d hd
    have hnotLeft := hleft Q hQ d hd
    rcases pathCut_halves_cover B P d with hleftHalf | hrightHalf
    · change d ∈ pathCutLeftDarts B P ∨ d ∈ pathCutSeamDarts B P at hleftHalf
      rcases hleftHalf with hleftDart | hseam
      · by_cases hseam : d ∈ pathCutSeamDarts B P
        · change d ∈ pathCutRightDarts B P ∨ d ∈ pathCutSeamDarts B P
          exact Or.inr hseam
        · exact False.elim (hnotLeft ⟨hleftDart, hseam⟩)
      · change d ∈ pathCutRightDarts B P ∨ d ∈ pathCutSeamDarts B P
        exact Or.inr hseam
    · exact hrightHalf
  · rintro ⟨hP, hright⟩
    refine ⟨hP, ?_⟩
    intro m Q hQ d hd hleft
    change d ∈ pathCutLeftDarts B P ∧ d ∉ pathCutSeamDarts B P at hleft
    have hleftHalf : d ∈ pathCutLeftHalfDarts B P := Or.inl hleft.1
    have hboth : d ∈ pathCutLeftHalfDarts B P ∩ pathCutRightHalfDarts B P :=
      ⟨hleftHalf, hright Q hQ d hd⟩
    have hseam : d ∈ pathCutSeamDarts B P := by
      rw [← pathCut_halves_inter_eq_seam B P]
      exact hboth
    exact hleft.2 hseam

/-- The order-theoretic lex-leftmost condition is equivalent to the paper's
geometric leftmost condition `def-geodesic` -/
theorem isLexLeftmost_iff_geometricLeftmost
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP)
    {n : ℕ} (P : SimpleDirectedDartPath B.map B.source B.sink n) :
    IsLexLeftmostXDPGeodesic B x P ↔ IsGeometricLeftmostXDPGeodesic B x P := by
  constructor
  · intro hP
    refine ⟨hP.1, ?_⟩
    intro m Q hQ d hd hleft
    exact lexLeftmost_no_strict_left_dart B x P hP Q hQ d hd hleft
  · intro hgeom
    obtain ⟨P₀, hP₀, _hP₀unique⟩ := existsUnique_lexLeftmostXDPGeodesic B x
    have hP := hgeom.1
    have hlen : n = xdpLengthBase B x := by
      cases x with
      | ldp => exact Nat.le_antisymm (hP₀.1 P) (hP P₀)
      | sdp => exact Nat.le_antisymm (hP P₀) (hP₀.1 P)
    by_cases hdarts : P.darts = P₀.darts
    · subst n
      have hpath : P = P₀ := SimpleDirectedDartPath.eq_of_darts_eq hdarts
      cases hpath
      exact hP₀
    · have hne : P₀.darts ≠ P.darts := by
        intro heq
        exact hdarts heq.symm
      obtain ⟨hnm, i, hdiff, hprefix, htail⟩ :=
        exists_firstDivergence B x P₀ P hP₀.1 hP hne
      subst n
      let d₀ := P₀.darts.get ⟨i.val, by rw [P₀.darts_length]; exact i.isLt⟩
      let d := P.darts.get ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
      have hdiff' : d₀ ≠ d := by simpa [d₀, d] using hdiff
      have hlistNe : P.darts ≠ P₀.darts := by
        intro heq
        exact hne heq.symm
      obtain ⟨hvs₀, horder⟩ :=
        hP₀.2 P hP hlistNe rfl i hprefix (by simpa [d₀, d] using hdiff)
      have hstepP₀ := P₀.edge_step ⟨i.val, by rw [P₀.darts_length]; exact i.isLt⟩
      have hstepP := P.edge_step ⟨i.val, by rw [P.darts_length]; exact i.isLt⟩
      have htailP : P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ =
          dartTailVertex B.map d := by
        simpa [d] using hstepP.2.2.1
      have htail₀P : dartTailVertex B.map d₀ =
          P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := by
        calc
          dartTailVertex B.map d₀ = dartTailVertex B.map d := by
            simpa [d₀, d] using htail
          _ = P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩ := htailP.symm
      have hleft : d₀ ∈ pathCutLeftDarts B P \ pathCutSeamDarts B P := by
        by_cases hi0 : i.val = 0
        ·
          have htail₀ : dartTailVertex B.map d₀ = B.source := by
            calc
              dartTailVertex B.map d₀ =
                  P₀.vertices.get ⟨0, by rw [P₀.vertices_length]; omega⟩ := by
                    simpa [d₀, hi0] using hstepP₀.2.2.1.symm
              _ = B.source := P₀.start_vertex
          let VertexNotSink := {v : MapVertex B.map // v ≠ B.sink}
          have hvertexOrder :
              (⟨dartTailVertex B.map d₀, hvs₀⟩ : VertexNotSink) =
                ⟨B.source, bipolar_source_ne_sink B⟩ := Subtype.ext htail₀
          have horderEq := congrArg
            (fun v : VertexNotSink => canonicalOutgoingOrder B v.1 v.2) hvertexOrder
          have hindex :
              (P.darts.get ⟨0, by rw [P.darts_length]; omega⟩) = d := by
            simp [d, hi0]
          have horderSource :
              (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).idxOf d₀ <
                (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).idxOf d := by
            have horderAtSource := congrArg
              (fun O : List D => O.idxOf d₀ < O.idxOf d) horderEq
            exact horderAtSource ▸ horder
          have hdiffSource : d₀ ≠
              P.darts.get ⟨0, by
                have hi : 0 < xdpLengthBase B x := by omega
                rw [P.darts_length]
                exact hi⟩ := by
            simpa only [hindex] using hdiff'
          have horderPathDart :
              (canonicalOutgoingOrder B B.source (bipolar_source_ne_sink B)).idxOf d₀ <
                (canonicalOutgoingOrder B B.source
                  (bipolar_source_ne_sink B)).idxOf
                  (P.darts.get ⟨0, by rw [P.darts_length]; omega⟩) := by
            rw [hindex]
            exact horderSource
          exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_source
            B P d₀ htail₀ hstepP₀.2.1 hdiffSource).mpr horderPathDart
        · have hi0' : 0 < i.val := by omega
          have hvsPath : P.vertices.get
              ⟨i.val, by rw [P.vertices_length]; omega⟩ ≠ B.sink :=
            simplePath_vertex_ne_end P i.val i.isLt
          have hvertexOrder :
              (⟨P.vertices.get ⟨i.val, by rw [P.vertices_length]; omega⟩,
                hvsPath⟩ : {v : MapVertex B.map // v ≠ B.sink}) =
                ⟨dartTailVertex B.map d₀, hvs₀⟩ := Subtype.ext htail₀P.symm
          have horderEq := congrArg
            (fun v : {v : MapVertex B.map // v ≠ B.sink} =>
              canonicalOutgoingOrder B v.1 v.2) hvertexOrder
          have horderPath := horder
          rw [horderEq.symm] at horderPath
          by_cases hleftBoundary : P.vertices.get
              ⟨i.val, by rw [P.vertices_length]; omega⟩ ∈ B.leftPath.vertices
          · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_leftBoundary
              B P i.val hi0' i.isLt hleftBoundary d₀ htail₀P hstepP₀.2.1 hdiff').mpr
                horderPath
          · by_cases hrightBoundary : P.vertices.get
                ⟨i.val, by rw [P.vertices_length]; omega⟩ ∈ B.rightPath.vertices
            · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_rightBoundary
                B P i.val hi0' i.isLt hrightBoundary d₀ htail₀P hstepP₀.2.1 hdiff').mpr
                  horderPath
            · exact (pathCutLeft_offSeam_iff_precedes_pathDart_of_interiorVertex
                B P i.val hi0' i.isLt hleftBoundary hrightBoundary d₀ htail₀P
                hstepP₀.2.1 hdiff').mpr horderPath
      have hd₀ : d₀ ∈ P₀.darts := List.get_mem _ _
      exact (hgeom.2 P₀ hP₀.1 d₀ hd₀ hleft).elim

/-- There exists a unique geometric leftmost XDP geodesic dart list. This
transfers the internal existence and uniqueness helper through the -/
theorem existsUnique_geometricLeftmostXDPGeodesic
    (B : BipolarTriangulationWithBoundaryBase D ℓ r) (x : XDP) :
    ∃ P : SimpleDirectedDartPath B.map B.source B.sink (xdpLengthBase B x),
      IsGeometricLeftmostXDPGeodesic B x P ∧
        ∀ {m : ℕ} (Q : SimpleDirectedDartPath B.map B.source B.sink m),
          IsGeometricLeftmostXDPGeodesic B x Q → Q.darts = P.darts := by
  obtain ⟨P, hP, hPunique⟩ := existsUnique_lexLeftmostXDPGeodesic B x
  refine ⟨P, (isLexLeftmost_iff_geometricLeftmost B x P).mp hP, ?_⟩
  intro m Q hQ
  exact hPunique Q ((isLexLeftmost_iff_geometricLeftmost B x Q).mpr hQ)

end DirectedDistances.PlanarMap
