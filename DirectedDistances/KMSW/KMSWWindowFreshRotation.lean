module

public import DirectedDistances.KMSW.KMSWWindowFreshVertexStar
public import DirectedDistances.KMSW.KMSWWindowFreshPresence

/-! rotation compatibility of the window dart map for fresh darts off the outer
word and for darts whose flip is off it. These are corollaries of existing
triangle-dart rotation results. The outer-word/boundary case is not treated
here; root-frame identification and local topology are not treated; not the
paper result. -/

public section
namespace DirectedDistances.KMSW

private theorem window_nonouter_mem_triangles (u : ℕ → Fin 3) (m : ℕ)
    (d : StageDart (kmswStage u m).nextEdge)
    (hout : d ∉ stageOuterWord u m) :
    (d.1.val, d.2) ∈ stageTriangleDartsVal u m := by
  rcases stage_dart_partition u m d with houter | ⟨j, ⟨hj, hmem⟩, _⟩
  · exact (hout houter).elim
  · exact List.mem_flatMap.mpr ⟨j, (mem_stageTriangleTimes u m j).mpr hj, hmem⟩

/-- the window dart map preserves rotation for every fresh dart off the outer
word. The outer-word (boundary) case and root-frame identification are not
treated. This is a helper, not the paper result. -/
theorem kmswWindowDartMap_rot_of_nonouter (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hout : d ∉ stageOuterWord (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).rot (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m
        ((kmswMap (fun i => w (s + i)) m).rot d) := by
  exact kmswWindowDartMap_rot w s m d
    (window_nonouter_mem_triangles (fun i => w (s + i)) m d hout)

/-- the inverse window rotation agrees for every fresh dart whose flip is off the
outer word. The outer-word (boundary) case and root-frame identification are
not treated. This is a helper, not the paper result. -/
theorem kmswWindowDartMap_rot_symm_of_nonouter (w : ℕ → Fin 3) (s m : ℕ)
    (d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge)
    (hout : edgeFlip _ d ∉ stageOuterWord (fun i => w (s + i)) m) :
    (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m d) =
      kmswWindowDartMap w s m
        ((kmswMap (fun i => w (s + i)) m).rot.symm d) := by
  exact kmswWindowDartMap_rot_symm w s m d
    (window_nonouter_mem_triangles (fun i => w (s + i)) m (edgeFlip _ d) hout)

end DirectedDistances.KMSW
