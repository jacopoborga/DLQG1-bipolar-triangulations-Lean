/-
Copyright (c) 2026 DirectedDistances contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DirectedDistances.PaperProofs.Section5.Prop516LeftSideHalfDisk2
public import DirectedDistances.PaperProofs.Section5.Prop516GeomToCombBallAssembly4
public import DirectedDistances.PaperProofs.Section5.Prop516HballForward

/-! # Removing pauses from the winding witness toward Proposition 5.16

The winding witness uses a paused edge subarc. Here an affine restriction
removes those pauses without changing winding or the return path. The
continuous simple-loop winding bound and the signed face identification -/

public section
noncomputable section

namespace DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk

open DirectedDistances.PlanarMap Set Metric unitInterval

/-- Helper toward Proposition 5.16: restrict a path to an interval by affine
rescaling, traversing it without the endpoint pauses in `edgeSubarc`. -/
@[expose]
def affineSubarc {x y : ℂ} (γ : Path x y) (a b : I) : Path (γ a) (γ b) where
  toFun t := γ (Set.Icc.convexComb a b t)
  continuous_toFun := γ.continuous.comp (Set.Icc.continuous_convexComb a b)
  source' := by simp only [Set.Icc.convexComb_zero]
  target' := by simp only [Set.Icc.convexComb_one]

private def normalizedClamp (a b : I) (hab : a < b) : C(I, I) where
  toFun t := ⟨(((min (max t a) b : I) : ℝ) - a) / ((b : ℝ) - a), by
    have hca : a ≤ min (max t a) b := le_min (le_max_right _ _) hab.le
    have hcb : min (max t a) b ≤ b := min_le_right _ _
    constructor
    · exact div_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr (show (a : ℝ) < b from hab))).mpr
        (sub_le_sub_right (show ((min (max t a) b : I) : ℝ) ≤ b from hcb) _)⟩
  continuous_toFun := by fun_prop

private theorem normalizedClamp_zero (a b : I) (hab : a < b) :
    normalizedClamp a b hab 0 = 0 := by
  apply Subtype.ext
  change (((min (max (0 : I) a) b : I) : ℝ) - a) / ((b : ℝ) - a) = 0
  rw [max_eq_right (show (0 : I) ≤ a from a.property.1),
    min_eq_left hab.le, sub_self, zero_div]

private theorem normalizedClamp_one (a b : I) (hab : a < b) :
    normalizedClamp a b hab 1 = 1 := by
  apply Subtype.ext
  change (((min (max (1 : I) a) b : I) : ℝ) - a) / ((b : ℝ) - a) = 1
  rw [max_eq_left (show a ≤ (1 : I) from a.property.2),
    min_eq_right (show b ≤ (1 : I) from b.property.2),
    div_self (sub_ne_zero.mpr (ne_of_gt (show (a : ℝ) < b from hab)))]

private theorem affineSubarc_normalizedClamp {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a < b) (t : I) :
    affineSubarc γ a b (normalizedClamp a b hab t) = edgeSubarc γ a b hab.le t := by
  rw [edgeSubarc_apply_clamp]
  change γ (Set.Icc.convexComb a b (normalizedClamp a b hab t)) = _
  congr 1
  apply Subtype.ext
  change (1 - ((((min (max t a) b : I) : ℝ) - a) / ((b : ℝ) - a))) * a +
    ((((min (max t a) b : I) : ℝ) - a) / ((b : ℝ) - a)) * b = _
  field_simp [sub_ne_zero.mpr (ne_of_gt (show (a : ℝ) < b from hab))]
  ring

private theorem hasLiftIncrement_edgeSubarc_of_affineSubarc
    {x y w c : ℂ} (γ : Path x y) (a b : I) (hab : a < b)
    (h : HasLiftIncrement (affineSubarc γ a b) w c) :
    HasLiftIncrement (edgeSubarc γ a b hab.le) w c := by
  obtain ⟨φ, hφ, hi⟩ := h
  refine ⟨φ.comp (normalizedClamp a b hab), ?_, ?_⟩
  · intro t
    exact (hφ _).trans (congrArg (fun z : ℂ => z - w)
      (affineSubarc_normalizedClamp γ a b hab t))
  · change φ (normalizedClamp a b hab 1) - φ (normalizedClamp a b hab 0) = c
    rw [normalizedClamp_one, normalizedClamp_zero]
    exact hi

/-- Helper toward Proposition 5.16: the affine subarc of an injective path
is injective whenever its chosen parameter endpoints are distinct and ordered. -/
theorem affineSubarc_injective {x y : ℂ} (γ : Path x y)
    (hγ : Function.Injective γ) (a b : I) (hab : a < b) :
    Function.Injective (affineSubarc γ a b) := by
  intro s t hst
  have heq := congrArg Subtype.val (hγ hst)
  change (1 - (s : ℝ)) * a + (s : ℝ) * b =
    (1 - (t : ℝ)) * a + (t : ℝ) * b at heq
  apply Subtype.ext
  have hab' : (a : ℝ) < b := hab
  nlinarith only [heq, hab']

/-- Helper toward Proposition 5.16: removing the pauses preserves exactly
the image of the selected edge subarc. -/
theorem affineSubarc_range_eq_edgeSubarc {x y : ℂ} (γ : Path x y)
    (a b : I) (hab : a < b) :
    Set.range (affineSubarc γ a b) = Set.range (edgeSubarc γ a b hab.le) := by
  apply Set.Subset.antisymm
  · rintro w ⟨t, rfl⟩
    refine ⟨Set.Icc.convexComb a b t, ?_⟩
    rw [edgeSubarc_apply_clamp,
      max_eq_left (Set.Icc.le_convexComb hab.le t),
      min_eq_left (Set.Icc.convexComb_le hab.le t)]
    rfl
  · rintro w ⟨t, rfl⟩
    exact ⟨normalizedClamp a b hab t, affineSubarc_normalizedClamp γ a b hab t⟩

/-- Helper toward Proposition 5.16: removing the pauses preserves every
logarithmic lift increment, in both directions and for every viewpoint. -/
theorem hasLiftIncrement_edgeSubarc_iff_affineSubarc
    {x y w c : ℂ} (γ : Path x y) (a b : I) (hab : a < b) :
    HasLiftIncrement (edgeSubarc γ a b hab.le) w c ↔
      HasLiftIncrement (affineSubarc γ a b) w c := by
  constructor
  · intro h
    have havoid : w ∉ Set.range (affineSubarc γ a b) := by
      rw [affineSubarc_range_eq_edgeSubarc γ a b hab]
      rintro ⟨t, ht⟩
      obtain ⟨φ, hφ, _⟩ := h
      exact Complex.exp_ne_zero (φ t) (by rw [hφ, ht, sub_self])
    obtain ⟨c', hc'⟩ := exists_hasLiftIncrement32 (affineSubarc γ a b) w havoid
    have heq := hasLiftIncrement_unique32
      (hasLiftIncrement_edgeSubarc_of_affineSubarc γ a b hab hc') h
    exact heq ▸ hc'
  · exact hasLiftIncrement_edgeSubarc_of_affineSubarc γ a b hab

/-- Helper toward Proposition 5.16: the actual return loop in a side
witness has unchanged signed winding after its edge traversal loses its
pauses. The return path itself is preserved. -/
theorem hasWinding_edgeSubarc_trans_iff_affineSubarc
    {x y : ℂ} (γ : Path x y) (a b : I) (hab : a < b)
    (q : Path (γ b) (γ a)) (w : ℂ) (n : ℤ) :
    HasWinding ((edgeSubarc γ a b hab.le).trans q) w n ↔
      HasWinding ((affineSubarc γ a b).trans q) w n := by
  change HasLiftIncrement ((edgeSubarc γ a b hab.le).trans q) w
      (2 * Real.pi * Complex.I * n) ↔
    HasLiftIncrement ((affineSubarc γ a b).trans q) w
      (2 * Real.pi * Complex.I * n)
  simp only [hasLiftIncrement_trans_iff,
    hasLiftIncrement_edgeSubarc_iff_affineSubarc γ a b hab]

/-- Helper toward Proposition 5.16: the original continuous return and the
unpaused edge subarc meet exactly at the two specified endpoints. No
polygonal replacement or local side choice is needed for this statement. -/
theorem affineSubarc_inter_returnPath
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (a b : I) (q : Path ((P.arc d).toPath b) ((P.arc d).toPath a))
    (hqF : ∀ t : I, t ∈ openParams → q t ∈ F.val) :
    Set.range (affineSubarc (P.arc d).toPath a b) ∩ Set.range q =
      {(P.arc d).toPath a, (P.arc d).toPath b} := by
  apply Set.Subset.antisymm
  · rintro w ⟨⟨t, rfl⟩, hwq⟩
    have hwimage : affineSubarc (P.arc d).toPath a b t ∈ P.image :=
      Or.inr ⟨d, (Polyline.range_toPath (P.arc d)) ▸
        Set.mem_range_self (Set.Icc.convexComb a b t)⟩
    have he : affineSubarc (P.arc d).toPath a b t ∈
        ({(P.arc d).toPath b, (P.arc d).toPath a} : Set ℂ) :=
      returnPath_inter_drawing P d F a b q hqF ▸ ⟨hwq, hwimage⟩
    exact he.elim Or.inr Or.inl
  · rintro w (hw | hw)
    · subst w
      exact ⟨⟨0, (affineSubarc (P.arc d).toPath a b).source⟩, ⟨1, q.target⟩⟩
    · subst w
      exact ⟨⟨1, (affineSubarc (P.arc d).toPath a b).target⟩, ⟨0, q.source⟩⟩

/-- Helper toward Proposition 5.16: every original winding-left witness
gives two injective continuous arcs meeting only at their endpoints, with
the same return path and winding-one accumulation. In particular the
endpoint pauses no longer obstruct a continuous Jordan winding bound. -/
theorem exists_leftAtOn_affineSubarc_return
    {D V : Type*} {flip : D → D} {rot : Equiv.Perm D} {vert : D → V}
    (P : PLDrawing D V flip rot vert) (d : D) (F : P.Face)
    (s : {t : I // t ∈ openParams})
    (hleft : LeftAtOn F.val (P.arc d).toPath s) :
    ∃ a b : I, ∃ (_ha : 0 < a) (_has : a < s.1) (_hsb : s.1 < b)
      (_hb : b < 1),
      ∃ q : Path ((P.arc d).toPath b) ((P.arc d).toPath a),
        Function.Injective (affineSubarc (P.arc d).toPath a b) ∧
        Function.Injective q ∧
        (∀ t : I, t ∈ openParams → q t ∈ F.val) ∧
        Set.range (affineSubarc (P.arc d).toPath a b) ∩ Set.range q =
          {(P.arc d).toPath a, (P.arc d).toPath b} ∧
        (P.arc d).toPath s.1 ∈ closure
          {w : ℂ | w ∈ F.val ∧ HasWinding
            ((affineSubarc (P.arc d).toPath a b).trans q) w 1} := by
  obtain ⟨a, b, ha, has, hsb, hb, q, hqi, hqF, hcl⟩ := hleft
  have hab : a < b := has.trans hsb
  refine ⟨a, b, ha, has, hsb, hb, q,
    affineSubarc_injective (P.arc d).toPath
      ((P.arc d).toPath_injective (P.arc_length d) (P.arc_simple d)) a b hab,
    hqi, hqF, affineSubarc_inter_returnPath P d F a b q hqF, ?_⟩
  apply closure_mono (s := {w : ℂ | w ∈ F.val ∧ HasWinding
    ((edgeSubarc (P.arc d).toPath a b hab.le).trans q) w 1}) ?_ hcl
  intro w hw
  exact ⟨hw.1,
    (hasWinding_edgeSubarc_trans_iff_affineSubarc (P.arc d).toPath a b hab q w 1).mp
      hw.2⟩















































































































end DirectedDistances.PaperProofs.Section5.LeftSideHalfDisk





































































































end
