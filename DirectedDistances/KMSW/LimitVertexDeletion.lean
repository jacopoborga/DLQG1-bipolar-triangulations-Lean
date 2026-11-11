module

public import DirectedDistances.KMSW.CutVertexIff
public import Mathlib.Logic.Relation

public section
namespace DirectedDistances.KMSW

open MeasureTheory Filter
open DirectedDistances.RandomWalk

/-- Helper toward Definition 4.2 / Proposition 4.3
the map with `v` deleted, retaining its edge ID and allowing either direction.
Deletion transport, plan n287 item 2; not the paper result. -/
@[expose] def presentAdjAvoiding (w : ℕ → Fin 3) (v a b : ℕ) : Prop :=
  a ≠ v ∧ b ≠ v ∧ ∃ e, EdgePresent w e ∧ UndirectedEdgeStep w a e b

/-- Helper toward Definition 4.2 / Proposition 4.3
present geometric map when two vertex IDs other than `v` have no finite path
of present edges between them. The vertex set is all natural-number IDs, all
allocated under the carrier facts; loops and multiplicity are irrelevant to
connectivity. Deletion transport, plan n287 item 2; not the paper result. -/
@[expose] def DeletingDisconnects (w : ℕ → Fin 3) (v : ℕ) : Prop :=
  ∃ x y : ℕ, x ≠ v ∧ y ≠ v ∧
    ¬ Relation.ReflTransGen (presentAdjAvoiding w v) x y

private def appendUndirectedEdgePath {w : ℕ → Fin 3} {x y z e : ℕ}
    (p : FiniteUndirectedEdgePath w x y) (h : UndirectedEdgeStep w y e z) :
    FiniteUndirectedEdgePath w x z :=
  match p with
  | .nil _ => .cons e h (.nil z)
  | .cons e' h' tail => .cons e' h' (appendUndirectedEdgePath tail h)

private theorem finiteUndirectedPath_start_mem {w : ℕ → Fin 3} {x y : ℕ}
    (p : FiniteUndirectedEdgePath w x y) : x ∈ p.vertices := by
  induction p with
  | nil x => simp [FiniteUndirectedEdgePath.vertices]
  | cons e hstep tail ih => simp [FiniteUndirectedEdgePath.vertices]

private theorem finiteUndirectedPath_end_mem {w : ℕ → Fin 3} {x y : ℕ}
    (p : FiniteUndirectedEdgePath w x y) : y ∈ p.vertices := by
  induction p with
  | nil x => simp [FiniteUndirectedEdgePath.vertices]
  | cons e hstep tail ih =>
    simp only [FiniteUndirectedEdgePath.vertices, Set.mem_union]
    exact Or.inr ih

private theorem appendUndirectedEdgePath_avoids {w : ℕ → Fin 3} (v : ℕ)
    {x y z e : ℕ} (p : FiniteUndirectedEdgePath w x y)
    (h : UndirectedEdgeStep w y e z)
    (havoid : ∀ a ∈ p.vertices, a ≠ v) (hz : z ≠ v) :
    ∀ a ∈ (appendUndirectedEdgePath p h).vertices, a ≠ v := by
  revert havoid
  induction p with
  | nil x =>
    intro havoid a ha
    simp only [appendUndirectedEdgePath, FiniteUndirectedEdgePath.vertices,
      Set.mem_union, Set.mem_singleton_iff] at ha
    rcases ha with hax | haz
    · subst a
      exact havoid x (by simp [FiniteUndirectedEdgePath.vertices])
    · subst a
      exact hz
  | @cons x y y' e' h' tail ih =>
    intro havoid a ha
    simp only [appendUndirectedEdgePath, FiniteUndirectedEdgePath.vertices,
      Set.mem_union] at ha
    rcases ha with hax | hat
    · subst a
      exact havoid x (Or.inl rfl)
    · exact ih h (fun b hb => havoid b (Or.inr hb)) a hat

private theorem reflTransGen_prepend {α : Type} {r : α → α → Prop}
    {x y z : α} (hxy : r x y) (hyz : Relation.ReflTransGen r y z) :
    Relation.ReflTransGen r x z := by
  induction hyz with
  | refl => exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hxy
  | @tail b c hyb hbc ih => exact Relation.ReflTransGen.tail ih hbc

private theorem avoidingChain_to_edgePath (w : ℕ → Fin 3) (v : ℕ)
    {x y : ℕ} (hxy : Relation.ReflTransGen (presentAdjAvoiding w v) x y)
    (hx : x ≠ v) :
    ∃ p : FiniteUndirectedEdgePath w x y, ∀ a ∈ p.vertices, a ≠ v := by
  revert hx
  induction hxy with
  | refl =>
    intro hx
    refine ⟨.nil x, ?_⟩
    intro a ha
    simp [FiniteUndirectedEdgePath.vertices] at ha
    subst a
    exact hx
  | @tail b c hprev hbc ih =>
    intro hx
    obtain ⟨p, hp⟩ := ih hx
    rcases hbc with ⟨_, hc, e, he, hstep⟩
    exact ⟨appendUndirectedEdgePath p hstep,
      appendUndirectedEdgePath_avoids v p hstep hp hc⟩

private theorem edgePath_avoiding_to_chain (w : ℕ → Fin 3) (v : ℕ)
    (hall : ∀ e, EdgePresent w e) {x y : ℕ}
    (p : FiniteUndirectedEdgePath w x y)
    (havoid : ∀ a ∈ p.vertices, a ≠ v) :
    Relation.ReflTransGen (presentAdjAvoiding w v) x y := by
  revert havoid
  induction p with
  | nil x =>
    intro havoid
    exact Relation.ReflTransGen.refl
  | @cons x y z e hstep tail ih =>
    intro havoid
    have hx : x ≠ v := havoid x (Or.inl rfl)
    have hy : y ≠ v := havoid y (Or.inr (finiteUndirectedPath_start_mem tail))
    have hz : z ≠ v := havoid z (Or.inr (finiteUndirectedPath_end_mem tail))
    have hxy : presentAdjAvoiding w v x y := ⟨hx, hy, e, hall e, hstep⟩
    exact reflTransGen_prepend hxy
      (ih (fun a ha => havoid a (Or.inr ha)))

/-- Helper toward Definition 4.2 / Proposition 4.3
equivalent to disconnection after deleting the vertex, provided every edge ID
is present. Deletion transport, plan n287 item 2; not the paper result. -/
theorem deletingDisconnects_iff_removingDisconnects (w : ℕ → Fin 3)
    (v : ℕ) (hall : ∀ e, EdgePresent w e) :
    DeletingDisconnects w v ↔ RemovingDisconnects w v := by
  constructor
  · rintro ⟨x, y, hx, hy, hno⟩
    refine ⟨x, y, hx, hy, ?_⟩
    intro p
    by_contra hnot
    have havoid : ∀ a ∈ p.vertices, a ≠ v := by
      intro a ha hav
      exact hnot (hav ▸ ha)
    have hchain := edgePath_avoiding_to_chain w v hall p havoid
    exact hno hchain
  · rintro ⟨x, y, hx, hy, hsep⟩
    refine ⟨x, y, hx, hy, ?_⟩
    intro hchain
    obtain ⟨p, havoid⟩ := avoidingChain_to_edgePath w v hchain hx
    exact (havoid v (hsep p)) rfl

/-- Helper toward Definition 4.2 / Proposition 4.3
every integrating code has the source-or-deletion characterization, using the
root edge's initial vertex and the carrier's all-edge-presence clause.
Deletion transport, plan n287 item 2; not the paper result. -/
theorem conditionedVectorPathLaw_ae_mapCutVertex_iff_source_or_deletingDisconnects :
    ∀ᵐ p ∂conditionedVectorPathLaw 0 0,
      (∃ w : ℕ → Fin 3, integrateCodes w = p) ∧
        ∀ w : ℕ → Fin 3, integrateCodes w = p →
          ∃ hfin : ∀ v, {e : ℕ | ∃ n, e < (kmswStage w n).nextEdge ∧
              ((kmswStage w n).west e = v ∨ (kmswStage w n).east e = v)}.Finite,
            edgeWest w 0 = 0 ∧
              ∀ v, (mapCutVertex w hfin v ↔
                v = edgeWest w 0 ∨ DeletingDisconnects w v) := by
  filter_upwards [conditionedVectorPathLaw_ae_unique_carrier,
    conditionedVectorPathLaw_ae_infinite_mapCutVertices_first_visit] with p hcar hpath
  obtain ⟨w₀, hw₀, _⟩ := hcar
  have hwp₀ : integrateCodes w₀ = p := hw₀.1
  have hroot : edgeWest w₀ 0 = 0 := hw₀.2.1.1
  obtain ⟨_, hcarRest⟩ := hw₀.2.2.2
  rcases hcarRest with ⟨_, _, _, _, _, _, hpresent, _, _, _, _, _, _, _⟩
  have hall : ∀ e, EdgePresent w₀ e := by
    intro e
    obtain ⟨N, hN⟩ := hpresent e
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨w₁, hwp₁, hfin, htrans, hR, hL0, _, _⟩ := hpath
  have heq₁ : w₁ = w₀ := integrateCodes_injective (hwp₁.trans hwp₀.symm)
  subst w₁
  refine ⟨⟨w₀, hwp₀⟩, ?_⟩
  intro w hwp
  have heq : w = w₀ := integrateCodes_injective (hwp.trans hwp₀.symm)
  subst w
  refine ⟨hfin, hroot, ?_⟩
  intro v
  have hiff := mapCutVertex_iff_source_or_removingDisconnects
    w₀ hfin htrans hR hL0 v
  have hdequiv := deletingDisconnects_iff_removingDisconnects w₀ v hall
  constructor
  · intro hcut
    rcases hiff.mp hcut with hsource | hsep
    · exact Or.inl (by simpa [hroot] using hsource)
    · exact Or.inr (hdequiv.mpr hsep)
  · rintro (hsource | hdeleted)
    · exact hiff.mpr (Or.inl (by simpa [hroot] using hsource))
    · exact hiff.mpr (Or.inr (hdequiv.mp hdeleted))

end DirectedDistances.KMSW
