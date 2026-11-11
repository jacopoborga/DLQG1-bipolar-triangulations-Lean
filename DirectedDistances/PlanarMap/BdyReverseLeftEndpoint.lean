module

public import DirectedDistances.PlanarMap.BdyReverseInverse

/-! Supporting lemmas for paper labels `lem-bdy-reverse` (see CORRESPONDENCE.md). -/







public section
namespace DirectedDistances.PlanarMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {a b l r : ℕ}

open BipolarTriangulationWithBoundary

/-- The restricted carrier of boundary-channeled maps with the indicated
left and right lengths, used in the reversal helpers for -/
abbrev BoundaryMbcClass (D : Type u) [Fintype D] [DecidableEq D]
    (a b : ℕ) :=
  {B : BipolarTriangulationWithBoundary D a b // InMbc a b B}

/-- Transport a restricted boundary class along equalities of its two -/
@[expose] def boundaryMbcClassEquiv {a b c d : ℕ}
    (ha : a = c) (hb : b = d) :
    BoundaryMbcClass D a b ≃ BoundaryMbcClass D c d := by
  cases ha
  cases hb
  exact Equiv.refl _

private theorem boundaryMbcClassEquiv_symm_apply {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b) :
    boundaryMbcClassEquiv (D := D) ha.symm hb.symm
      (boundaryMbcClassEquiv (D := D) ha hb B) = B := by
  cases ha
  cases hb
  rfl

private theorem boundaryMbcClassEquiv_val {a b c d : ℕ}
    (ha : a = c) (hb : b = d) (B : BoundaryMbcClass D a b) :
    (boundaryMbcClassEquiv (D := D) ha hb B).val =
      cast (by cases ha; cases hb; rfl) B.val := by
  cases ha
  cases hb
  rfl

private theorem boundaryMbcClassEquiv_comp_apply {a b c d e f : ℕ}
    (ha : a = c) (hc : c = e) (hb : b = d) (hd : d = f)
    (B : BoundaryMbcClass D a b) :
    boundaryMbcClassEquiv (D := D) hc hd
        (boundaryMbcClassEquiv (D := D) ha hb B) =
      boundaryMbcClassEquiv (D := D) (ha.trans hc) (hb.trans hd) B := by
  cases ha
  cases hc
  cases hb
  cases hd
  rfl

/-- Left-prefix reversal on the restricted simple-boundary carrier -/
@[expose] noncomputable def leftPrefixReversalMbc (k : ℕ)
    (hk : 1 ≤ k) (hka : k < a) :
    BoundaryMbcClass D a b → BoundaryMbcClass D (a - k) (b + k) :=
  fun B => ⟨leftPrefixReversal B.val k hk hka B.property,
    leftPrefixReversal_InMbc B.val k hk hka B.property⟩

private theorem cast_injective {α β : Sort u} (e : α = β) {x y : α}
    (h : cast e x = cast e y) : x = y := by
  cases e
  exact h

/-- Injectivity of restricted left-prefix reversal, using the supplied
right-after-left round trip (`lem-bdy-reverse` (left-interchanged), -/
theorem leftPrefixReversalMbc_injective (k : ℕ) (hk : 1 ≤ k) (hka : k < a) :
    Function.Injective (leftPrefixReversalMbc (D := D) (a := a) (b := b)
      k hk hka) := by
  intro B C h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change leftPrefixReversal B.val k hk hka B.property =
    leftPrefixReversal C.val k hk hka C.property at hval
  have hbB : 1 ≤ b := B.val.right_length_pos
  have hbk : k < b + k := by omega
  have hbcB := leftPrefixReversal_InMbc B.val k hk hka B.property
  have hbcC := leftPrefixReversal_InMbc C.val k hk hka C.property
  change (leftPrefixReversal B.val k hk hka B.property).IsBoundaryChanneled at hbcB
  change (leftPrefixReversal C.val k hk hka C.property).IsBoundaryChanneled at hbcC
  have hrev := congrArg Subtype.val
    (congrArg (rightPrefixReversalMbc (D := D) (ℓ := a - k) (r := b + k)
      k hk hbk) h)
  have hroundB := rightPrefixReversal_leftPrefixReversal B.val k hk hka B.property
  have hroundC := rightPrefixReversal_leftPrefixReversal C.val k hk hka C.property
  let e : BipolarTriangulationWithBoundary D a b =
      BipolarTriangulationWithBoundary D ((a - k) + k) ((b + k) - k) := by
    congr 1 <;> omega
  have hcast : cast e B.val = cast e C.val := by
    calc
      cast e B.val =
          rightPrefixReversal (leftPrefixReversal B.val k hk hka B.property)
            k hk hbk hbcB := hroundB.symm
      _ = rightPrefixReversal (leftPrefixReversal C.val k hk hka C.property)
            k hk hbk hbcC := by
        simpa only [rightPrefixReversalMbc, leftPrefixReversalMbc] using hrev
      _ = cast e C.val := hroundC
  exact cast_injective e hcast

private theorem leftPrefixReversalMbc_transport
    {a₁ b₁ a₂ b₂ : ℕ} (ha : a₁ = a₂) (hb : b₁ = b₂)
    (B : BoundaryMbcClass D a₁ b₁) (k : ℕ) (hk : 1 ≤ k)
    (hka₁ : k < a₁) (hka₂ : k < a₂) :
    leftPrefixReversalMbc (D := D) (a := a₂) (b := b₂) k hk hka₂
        (boundaryMbcClassEquiv (D := D) ha hb B) =
      boundaryMbcClassEquiv (D := D) (congrArg (fun n => n - k) ha)
        (congrArg (fun n => n + k) hb)
        (leftPrefixReversalMbc (D := D) (a := a₁) (b := b₁) k hk hka₁ B) := by
  cases ha
  cases hb
  rfl

/-- Surjectivity of restricted left-prefix reversal. Its inverse is right
reversal followed by explicit transport of the two natural-number lengths -/
theorem leftPrefixReversalMbc_surjective (k : ℕ) (hk : 1 ≤ k)
    (hka : k < a) (hb : 1 ≤ b) :
    Function.Surjective (leftPrefixReversalMbc (D := D) (a := a) (b := b)
      k hk hka) := by
  intro B'
  let hsa : (a - k) + k = a := by omega
  let hsb : (b + k) - k = b := by omega
  let htu₁ : a - k = ((a - k + k) - k) := by omega
  let htu₂ : b + k = ((b + k - k) + k) := by omega
  let R := rightPrefixReversalMbc (D := D) (ℓ := a - k) (r := b + k)
    k hk (by omega) B'
  let C := boundaryMbcClassEquiv (D := D) hsa hsb R
  refine ⟨C, ?_⟩
  have hka' : k < (a - k) + k := by omega
  have hround := leftPrefixReversal_rightPrefixReversal B'.val k hk
    (by omega) B'.property
  have hroundClass :
      leftPrefixReversalMbc (D := D) (a := (a - k) + k)
        (b := (b + k) - k) k hk hka' R =
      boundaryMbcClassEquiv (D := D) htu₁ htu₂ B' := by
    apply Subtype.ext
    dsimp [R, rightPrefixReversalMbc, leftPrefixReversalMbc]
    rw [boundaryMbcClassEquiv_val]
    exact hround
  calc
    leftPrefixReversalMbc (D := D) (a := a) (b := b) k hk hka C =
        boundaryMbcClassEquiv (D := D) (congrArg (fun n => n - k) hsa)
          (congrArg (fun n => n + k) hsb)
          (leftPrefixReversalMbc (D := D) (a := (a - k) + k)
            (b := (b + k) - k) k hk hka' R) := by
          exact leftPrefixReversalMbc_transport hsa hsb R k hk hka' hka
    _ = boundaryMbcClassEquiv (D := D) htu₁.symm htu₂.symm
          (boundaryMbcClassEquiv (D := D) htu₁ htu₂ B') := by
          rw [hroundClass]
    _ = B' := boundaryMbcClassEquiv_symm_apply htu₁ htu₂ B'

/-- Restricted left-prefix reversal is bijective for positive right length
used at `:432`). The boundary carrier itself supplies positive left length;
`hb` is needed for `k < b + k` in the inverse reversal. Helper, not counted; -/
theorem leftPrefixReversalMbc_bijective (k : ℕ) (hk : 1 ≤ k)
    (hka : k < a) (hb : 1 ≤ b) :
    Function.Bijective (leftPrefixReversalMbc (D := D) (a := a) (b := b)
      k hk hka) :=
  ⟨leftPrefixReversalMbc_injective k hk hka,
    leftPrefixReversalMbc_surjective k hk hka hb⟩

/-- The restricted left endpoint reversal on literal `(l,1)` and `(1,l)`
carriers (`lem-bdy-reverse` (left-interchanged), -/
@[expose] noncomputable def leftEndpointReversalEquiv (hl : 2 ≤ l) :
    BoundaryMbcClass D l 1 ≃ BoundaryMbcClass D 1 l :=
  (Equiv.ofBijective
    (leftPrefixReversalMbc (D := D) (a := l) (b := 1) (l - 1)
      (by omega) (by omega))
    (leftPrefixReversalMbc_bijective (D := D) (a := l) (b := 1)
      (l - 1) (by omega) (by omega) (by omega))).trans
    (boundaryMbcClassEquiv (D := D) (by omega) (by omega))

/-- The literal left endpoint map is bijective for `l ≥ 2` -/
theorem leftEndpointReversalEquiv_bijective (hl : 2 ≤ l) :
    Function.Bijective (leftEndpointReversalEquiv (D := D) (l := l) hl) :=
  (leftEndpointReversalEquiv (D := D) (l := l) hl).bijective

/-- The restricted right endpoint reversal transported to literal `(1,r)` -/
@[expose] noncomputable def rightEndpointReversalEquiv (hr : 2 ≤ r) :
    BoundaryMbcClass D 1 r ≃ BoundaryMbcClass D r 1 :=
  (Equiv.ofBijective
    (rightPrefixReversalMbc (D := D) (ℓ := 1) (r := r) (r - 1)
      (by omega) (by omega))
    (rightPrefixReversalMbc_endpoint_bijective (D := D) (r := r) hr)).trans
    (boundaryMbcClassEquiv (D := D) (by omega) (by omega))

/-- Source-index form of the literal right endpoint equivalence, with -/
@[expose] noncomputable def rightEndpointReversalEquiv_succ (l_n : ℕ) (hln : 1 ≤ l_n) :
    BoundaryMbcClass D 1 (l_n + 1) ≃ BoundaryMbcClass D (l_n + 1) 1 :=
  rightEndpointReversalEquiv (D := D) (r := l_n + 1) (by omega)

/-- At the degenerate endpoint `l = 1`, use the identity equivalence on the
literal `(1,1)` restricted class. This records the I3 source reading as -/
@[expose] def leftEndpointReversalEquiv_one :
    BoundaryMbcClass D 1 1 ≃ BoundaryMbcClass D 1 1 := Equiv.refl _

/-- Uniform restricted endpoint symmetry for every positive `l`: it is the
identity at `l = 1` and the left-prefix reversal for `l ≥ 2`. This is the I3 -/
@[expose] noncomputable def endpointSymmetryEquiv (l : ℕ) (hl : 1 ≤ l) :
    BoundaryMbcClass D l 1 ≃ BoundaryMbcClass D 1 l := by
  by_cases h : l = 1
  · subst l
    exact leftEndpointReversalEquiv_one (D := D)
  · exact leftEndpointReversalEquiv (D := D) (l := l) (by omega)

/-- The uniform symmetry reduces to the identity equivalence at `l = 1` -/
theorem endpointSymmetryEquiv_one :
    endpointSymmetryEquiv (D := D) 1 (by omega) =
      leftEndpointReversalEquiv_one (D := D) := by
  rfl

/-- For `l ≥ 2`, the uniform endpoint symmetry is the restricted left-prefix
reversal (`lem-bdy-reverse` (left-interchanged), -/
theorem endpointSymmetryEquiv_of_two (hl : 2 ≤ l) :
    endpointSymmetryEquiv (D := D) l (by omega) =
      leftEndpointReversalEquiv (D := D) hl := by
  unfold endpointSymmetryEquiv
  split
  · rename_i h
    omega
  · rfl

/-- On the restricted endpoint classes, left reversal is inverse to the -/
theorem leftEndpointReversalEquiv_comp_rightEndpointReversalEquiv
    (hl : 2 ≤ l) (B : BoundaryMbcClass D 1 l) :
    leftEndpointReversalEquiv (D := D) hl
      (rightEndpointReversalEquiv (D := D) (r := l) hl B) = B := by
  let k := l - 1
  have hk : 1 ≤ k := by omega
  have hkl : k < l := by omega
  have hsa : 1 + k = l := by omega
  have hsb : l - k = 1 := by omega
  have hkaS : k < 1 + k := by omega
  have hvu₁ : 1 = (1 + k) - k := by omega
  have hvu₂ : l = (l - k) + k := by omega
  have htv₁ : l - k = 1 := by omega
  have htv₂ : 1 + k = l := by omega
  let R := rightPrefixReversalMbc (D := D) (ℓ := 1) (r := l) k hk hkl B
  have hnat := leftPrefixReversalMbc_transport hsa hsb R k hk hkaS (by omega)
  have hround := leftPrefixReversal_rightPrefixReversal B.val k hk hkl B.property
  have hroundClass :
      leftPrefixReversalMbc (D := D) (a := 1 + k) (b := l - k)
        k hk hkaS R =
      boundaryMbcClassEquiv (D := D) hvu₁ hvu₂ B := by
    apply Subtype.ext
    dsimp [R, rightPrefixReversalMbc, leftPrefixReversalMbc]
    rw [boundaryMbcClassEquiv_val]
    exact hround
  simp only [leftEndpointReversalEquiv, rightEndpointReversalEquiv,
    Equiv.trans_apply, Equiv.ofBijective_apply]
  change boundaryMbcClassEquiv (D := D) htv₁ htv₂
      (leftPrefixReversalMbc (D := D) (a := l) (b := 1) k hk hkl
        (boundaryMbcClassEquiv (D := D) hsa hsb R)) = B
  calc
    boundaryMbcClassEquiv (D := D) htv₁ htv₂
        (leftPrefixReversalMbc (D := D) (a := l) (b := 1) k hk hkl
          (boundaryMbcClassEquiv (D := D) hsa hsb R)) =
      boundaryMbcClassEquiv (D := D) htv₁ htv₂
        (boundaryMbcClassEquiv (D := D)
          (congrArg (fun n => n - k) hsa) (congrArg (fun n => n + k) hsb)
          (leftPrefixReversalMbc (D := D) (a := 1 + k) (b := l - k)
            k hk hkaS R)) := by
              rw [leftPrefixReversalMbc_transport]
    _ = boundaryMbcClassEquiv (D := D) htv₁ htv₂
        (boundaryMbcClassEquiv (D := D)
          (congrArg (fun n => n - k) hsa) (congrArg (fun n => n + k) hsb)
          (boundaryMbcClassEquiv (D := D) hvu₁ hvu₂ B)) := by
              rw [hroundClass]
    _ = boundaryMbcClassEquiv (D := D)
          ((congrArg (fun n => n - k) hsa).trans htv₁)
          ((congrArg (fun n => n + k) hsb).trans htv₂)
          (boundaryMbcClassEquiv (D := D) hvu₁ hvu₂ B) := by
              exact boundaryMbcClassEquiv_comp_apply
                (congrArg (fun n => n - k) hsa) htv₁
                (congrArg (fun n => n + k) hsb) htv₂
                (boundaryMbcClassEquiv (D := D) hvu₁ hvu₂ B)
    _ = B := by
          exact boundaryMbcClassEquiv_symm_apply hvu₁ hvu₂ B

/-- The inverse of the literal left endpoint equivalence is exactly the -/
theorem leftEndpointReversalEquiv_symm
    (hl : 2 ≤ l) :
    (leftEndpointReversalEquiv (D := D) (l := l) hl).symm =
      rightEndpointReversalEquiv (D := D) (r := l) hl := by
  apply Equiv.ext
  intro B
  apply (leftEndpointReversalEquiv (D := D) (l := l) hl).injective
  rw [(leftEndpointReversalEquiv (D := D) (l := l) hl).apply_symm_apply]
  symm
  exact leftEndpointReversalEquiv_comp_rightEndpointReversalEquiv
    (D := D) (l := l) hl B

end DirectedDistances.PlanarMap
