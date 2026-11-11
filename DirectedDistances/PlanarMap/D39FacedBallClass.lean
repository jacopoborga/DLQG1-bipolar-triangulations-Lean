module

public import DirectedDistances.PlanarMap.D39Ball
public import DirectedDistances.PlanarMap.FacedFramedBall
public import DirectedDistances.PaperProofs.Section3.BSTopologyGeneric
import DirectedDistances.PaperProofs.Section3.BSTopologyConcreteSystem

noncomputable section

public section
namespace DirectedDistances.PlanarMap

open Equiv CombinatorialMap

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Provide decidable equality for each rooted map's darts. -/
local instance (M : D39RootedMap) : DecidableEq M.core.D := Classical.decEq _

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Finite retained data: geometric dart identities, plane rotation, ordered root,
present/missing tags, present orientations, and original face incidences. -/
structure D39FiniteBall where
  D : Type
  [instFintypeD : Fintype D]
  [instDecidableEqD : DecidableEq D]
  map : CombinatorialMap D
  missing : D → Prop
  tail : D → Prop
  rootDart : D
  original : Set D
  original_closed : ∀ d, map.faceSucc d ∈ original ↔ d ∈ original

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Expose the finite dart type stored in a finite ball. -/
instance (B : D39FiniteBall) : Fintype B.D := B.instFintypeD

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Expose decidable equality stored for the finite ball's darts. -/
instance (B : D39FiniteBall) : DecidableEq B.D := B.instDecidableEqD

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Isomorphisms preserve every retained dart datum. Rotation commutation preserves
the plane orientation; exact root-dart preservation retains the ordered mark. -/
structure D39BallIso (B C : D39FiniteBall) where
  toEquiv : B.D ≃ C.D
  rot_comm : ∀ d, toEquiv (B.map.rot d) = C.map.rot (toEquiv d)
  edgeInv_comm : ∀ d, toEquiv (B.map.edgeInv d) = C.map.edgeInv (toEquiv d)
  missing_iff : ∀ d, C.missing (toEquiv d) ↔ B.missing d
  tail_iff : ∀ d, C.tail (toEquiv d) ↔ B.tail d
  root_comm : toEquiv B.rootDart = C.rootDart
  original_iff : ∀ d, toEquiv d ∈ C.original ↔ d ∈ B.original

namespace D39BallIso

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Identity isomorphism. -/
@[expose] def refl (B : D39FiniteBall) : D39BallIso B B where
  toEquiv := Equiv.refl _
  rot_comm := fun _ => rfl
  edgeInv_comm := fun _ => rfl
  missing_iff := fun _ => Iff.rfl
  tail_iff := fun _ => Iff.rfl
  root_comm := rfl
  original_iff := fun _ => Iff.rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Inverse isomorphism. -/
@[expose] def symm {B C : D39FiniteBall} (I : D39BallIso B C) : D39BallIso C B where
  toEquiv := I.toEquiv.symm
  rot_comm := by
    intro d
    apply I.toEquiv.injective
    rw [Equiv.apply_symm_apply, I.rot_comm, Equiv.apply_symm_apply]
  edgeInv_comm := by
    intro d
    apply I.toEquiv.injective
    rw [Equiv.apply_symm_apply, I.edgeInv_comm, Equiv.apply_symm_apply]
  missing_iff := by
    intro d
    have h := I.missing_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  tail_iff := by
    intro d
    have h := I.tail_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  root_comm := by rw [← I.root_comm, Equiv.symm_apply_apply]
  original_iff := by
    intro d
    have h := I.original_iff (I.toEquiv.symm d)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Composition of isomorphisms. -/
@[expose] def trans {B C E : D39FiniteBall}
    (I : D39BallIso B C) (J : D39BallIso C E) : D39BallIso B E where
  toEquiv := I.toEquiv.trans J.toEquiv
  rot_comm := by intro d; exact (congrArg J.toEquiv (I.rot_comm d)).trans (J.rot_comm _)
  edgeInv_comm := by
    intro d
    exact (congrArg J.toEquiv (I.edgeInv_comm d)).trans (J.edgeInv_comm _)
  missing_iff := fun d => (J.missing_iff _).trans (I.missing_iff d)
  tail_iff := fun d => (J.tail_iff _).trans (I.tail_iff d)
  root_comm := (congrArg J.toEquiv I.root_comm).trans J.root_comm
  original_iff := fun d => (J.original_iff _).trans (I.original_iff d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Face successors commute, so retained original faces keep their incidences. -/
theorem face_comm {B C : D39FiniteBall} (I : D39BallIso B C) (d : B.D) :
    I.toEquiv (B.map.faceSucc d) = C.map.faceSucc (I.toEquiv d) := by
  change I.toEquiv (B.map.rot.symm (B.map.edgeInv d)) =
    C.map.rot.symm (C.map.edgeInv (I.toEquiv d))
  apply C.map.rot.injective
  rw [← I.rot_comm, B.map.rot.apply_symm_apply,
    C.map.rot.apply_symm_apply, I.edgeInv_comm]

end D39BallIso

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Equivalence relation given by isomorphisms of all retained data. -/
@[expose] def D39FiniteBall.setoid : Setoid D39FiniteBall where
  r B C := Nonempty (D39BallIso B C)
  iseqv := ⟨fun B => ⟨D39BallIso.refl B⟩,
    fun ⟨I⟩ => ⟨I.symm⟩, fun ⟨I⟩ ⟨J⟩ => ⟨I.trans J⟩⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Finite retained balls up to the full local topology isomorphism relation. -/
@[expose] def D39BallClass := Quotient D39FiniteBall.setoid

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
A finite ball relabelled to the canonical carrier Fin n. -/
private structure CanonicalD39Ball (n : ℕ) where
  map : CombinatorialMap (Fin n)
  missing : Fin n → Prop
  tail : Fin n → Prop
  rootDart : Fin n
  original : Set (Fin n)
  original_closed : ∀ d, map.faceSucc d ∈ original ↔ d ∈ original

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Encode the map and all retained tags by their data tuple. -/
private def canonicalCode {n : ℕ} (B : CanonicalD39Ball n) :=
  (B.map.rot, B.map.edgeInv, B.missing, B.tail, B.rootDart, B.original)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The retained-data code uniquely determines the canonical ball. -/
private theorem canonicalCode_injective {n : ℕ} :
    Function.Injective (@canonicalCode n) := by
  intro B C h
  cases B with
  | mk Bm Bmiss Bt Br Bo Bc =>
    cases C with
    | mk Cm Cmiss Ct Cr Co Cc =>
      cases Bm
      cases Cm
      simp_all [canonicalCode]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Each fixed-size canonical carrier has finitely many retained-data balls. -/
private instance (n : ℕ) : Finite (CanonicalD39Ball n) :=
  Finite.of_injective canonicalCode canonicalCode_injective

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
View a canonical representative as a finite ball. -/
private def CanonicalD39Ball.toBall {n : ℕ} (B : CanonicalD39Ball n) : D39FiniteBall where
  D := Fin n
  map := B.map
  missing := B.missing
  tail := B.tail
  rootDart := B.rootDart
  original := B.original
  original_closed := B.original_closed

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Transport edge involution and rotation along an equivalence of dart types. -/
private def relabelMap {D E : Type} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E) (M : CombinatorialMap D) :
    CombinatorialMap E where
  edgeInv := e.permCongr M.edgeInv
  edgeInv_invol := by intro d; simp [Equiv.permCongr_apply, M.edgeInv_invol]
  edgeInv_ne := by
    intro d hd
    apply M.edgeInv_ne (e.symm d)
    apply e.injective
    simpa [Equiv.permCongr_apply] using hd
  rot := e.permCongr M.rot

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Relabelling commutes with the face-successor permutation. -/
private theorem relabelFace {D E : Type} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E) (M : CombinatorialMap D) (d : E) :
    e.symm ((relabelMap e M).faceSucc d) = M.faceSucc (e.symm d) := by
  apply e.injective
  rw [e.apply_symm_apply]
  apply (e.permCongr M.rot).injective
  simp [CombinatorialMap.faceSucc, relabelMap, Equiv.permCongr_apply]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Relabel a finite ball onto Fin of its dart count. -/
private noncomputable def canonicalOf (B : D39FiniteBall) :
    CanonicalD39Ball (Fintype.card B.D) := by
  let e := Fintype.equivFin B.D
  exact {
    map := relabelMap e B.map
    missing := fun d => B.missing (e.symm d)
    tail := fun d => B.tail (e.symm d)
    rootDart := e B.rootDart
    original := {d | e.symm d ∈ B.original}
    original_closed := by
      intro d
      change e.symm ((relabelMap e B.map).faceSucc d) ∈ B.original ↔ _
      rw [relabelFace]
      exact B.original_closed _ }

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Map a canonical finite representative to its quotient class. -/
private noncomputable def canonicalClass (B : Σ n, CanonicalD39Ball n) : D39BallClass :=
  Quotient.mk D39FiniteBall.setoid B.2.toBall

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Every quotient class has a representative on Fin n. -/
private theorem canonicalClass_surjective : Function.Surjective canonicalClass := by
  intro q
  refine Quotient.inductionOn q ?_
  intro B
  let e := Fintype.equivFin B.D
  refine ⟨⟨Fintype.card B.D, canonicalOf B⟩, Quotient.sound ⟨?_⟩⟩
  apply D39BallIso.symm
  exact {
    toEquiv := e
    rot_comm := by
      intro d
      change e (B.map.rot d) = e (B.map.rot (e.symm (e d)))
      rw [e.symm_apply_apply]
    edgeInv_comm := by
      intro d
      change e (B.map.edgeInv d) = e (B.map.edgeInv (e.symm (e d)))
      rw [e.symm_apply_apply]
    missing_iff := by
      intro d
      change B.missing (e.symm (e d)) ↔ B.missing d
      rw [e.symm_apply_apply]
    tail_iff := by
      intro d
      change B.tail (e.symm (e d)) ↔ B.tail d
      rw [e.symm_apply_apply]
    root_comm := rfl
    original_iff := by
      intro d
      change e.symm (e d) ∈ B.original ↔ d ∈ B.original
      rw [e.symm_apply_apply] }


/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Canonical representatives on Fin n prove countability, without a countability
assumption on the space of maps. This is the same finite-representative method
used for faced framed balls. -/
instance instCountableD39BallClass : Countable D39BallClass :=
  Function.Surjective.countable canonicalClass_surjective

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The actual positive-radius retained ball. No genus-zero hypothesis is used;
the inherited plane rotation and the original-face selection are retained. -/
@[expose] noncomputable def d39FacedBall (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    D39FiniteBall := by
  classical
  exact {
  D := {d : M.core.D // d ∈ d39BallDarts M r}
  instFintypeD := inferInstance
  instDecidableEqD := inferInstance
  map := d39BallMap M r
  missing := d39BallMissing M r
  tail := d39BallTail M r
  rootDart := ⟨M.rootMark.dart, (d39BallDarts_root_mem M hr).1⟩
  original := {d | d39BallContainsOriginalFace M r d.1}
  original_closed := d39BallContainsOriginalFace_closed M r }

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The source-radius-r ball class, for strictly positive source radii. -/
@[expose] noncomputable def d39BallClass (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    D39BallClass := Quotient.mk D39FiniteBall.setoid (d39FacedBall M r hr)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Equality of classes is exactly existence of a full retained-data isomorphism. -/
theorem d39BallClass_eq_iff (M N : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    d39BallClass M r hr = d39BallClass N r hr ↔
      Nonempty (D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr)) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
All-geometric distance at most r from the ordered root, on a finite dart map. -/
inductive D39FiniteBallWithinRadius (B : D39FiniteBall) : ℕ → B.D → Prop
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
  Start from any dart in the root vertex's rotation cycle. -/
  | root {d} : B.map.rot.SameCycle B.rootDart d → D39FiniteBallWithinRadius B 0 d
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
  Carry reachability to the next radius. -/
  | stay {r d} : D39FiniteBallWithinRadius B r d → D39FiniteBallWithinRadius B (r + 1) d
  /-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
  Extend reachability across an edge and within its endpoint rotation cycle. -/
  | edge {r d e} : D39FiniteBallWithinRadius B r d → B.map.rot.SameCycle (B.map.edgeInv d) e →
      D39FiniteBallWithinRadius B (r + 1) e

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An isomorphism maps finite-ball radius reachability forward. -/
private theorem ballWithin_map {B C : D39FiniteBall} (I : D39BallIso B C)
    {r d} (h : D39FiniteBallWithinRadius B r d) : D39FiniteBallWithinRadius C r (I.toEquiv d) := by
  have hc := framedBall_sameCycle_iff_of_equiv I.toEquiv B.map.rot C.map.rot I.rot_comm
  induction h with
  | root h =>
    apply D39FiniteBallWithinRadius.root
    rw [← I.root_comm]
    exact (hc _ _).1 h
  | stay _ ih => exact .stay ih
  | edge _ h ih =>
    apply D39FiniteBallWithinRadius.edge ih
    rw [← I.edgeInv_comm]
    exact (hc _ _).1 h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Finite-ball radius reachability is invariant under ball isomorphism. -/
private theorem ballWithin_iso_iff {B C : D39FiniteBall} (I : D39BallIso B C)
    (r : ℕ) (d : B.D) :
    D39FiniteBallWithinRadius B r d ↔ D39FiniteBallWithinRadius C r (I.toEquiv d) := by
  refine ⟨ballWithin_map I, fun h => ?_⟩
  have h' := ballWithin_map I.symm h
  simpa only [D39BallIso.symm, Equiv.symm_apply_apply] using h'

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Ambient vertex reachability persists at larger radii. -/
private theorem ambient_mono (M : D39RootedMap) {r s : ℕ} (hrs : r ≤ s)
    {v} (h : D39WithinRadius M r v) : D39WithinRadius M s v :=
  (mem_d39BallVertices M s v).1
    (d39BallVertices_mono M hrs ((mem_d39BallVertices M r v).2 h))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Finite-ball reachability gives ambient vertex reachability. -/
private theorem within_toAmbient (M : D39RootedMap) (s : ℕ) (hs : 0 < s)
    {r d} (h : D39FiniteBallWithinRadius (d39FacedBall M s hs) r d) :
    D39WithinRadius M r (d39VertexClass M d.1) := by
  classical
  induction h with
  | @root d h =>
    have hc := (d39Ball_rot_sameCycle_iff M s _ _).1 h
    have heq : d39VertexClass M M.rootMark.dart = d39VertexClass M d.1 :=
      Quotient.sound hc
    rw [← heq]
    exact .root
  | stay _ ih => exact .stay ih
  | @edge r d e _ h ih =>
    have hc := (d39Ball_rot_sameCycle_iff M s _ _).1 h
    exact .edge ih ⟨d.1, rfl, Quotient.sound hc⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Ambient reachability of depth n lifts into an enclosing ball of radius s. -/
private theorem ambient_toWithin (M : D39RootedMap) (s : ℕ) (hs : 0 < s)
    {n v} (h : D39WithinRadius M n v) (hn : n ≤ s)
    (d : (d39FacedBall M s hs).D) (hd : d39VertexClass M d.1 = v) :
    D39FiniteBallWithinRadius (d39FacedBall M s hs) n d := by
  classical
  let B := d39FacedBall M s hs
  induction h generalizing d with
  | root =>
    apply D39FiniteBallWithinRadius.root
    exact (d39Ball_rot_sameCycle_iff M s _ _).2 (Quotient.exact hd).symm
  | stay hp ih => exact .stay (ih (by omega) d hd)
  | @edge n v w hp he ih =>
    obtain ⟨e, hev, hew⟩ := he
    have heS : e ∈ d39BallDarts M s := by
      apply (mem_d39BallDarts M s e).2
      constructor
      · exact (mem_d39BallVertices M s _).2
          (ambient_mono M (by omega) (hev.symm ▸ hp))
      · exact (mem_d39BallVertices M s _).2
          (ambient_mono M hn (D39WithinRadius.edge hp ⟨e, hev, rfl⟩))
    let e' : B.D := ⟨e, heS⟩
    apply D39FiniteBallWithinRadius.edge (ih (by omega) e' hev)
    exact (d39Ball_rot_sameCycle_iff M s _ _).2 (Quotient.exact (hew.trans hd.symm))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Finite-ball and ambient reachability agree up to the enclosing radius. -/
private theorem ballWithin_iff (M : D39RootedMap) {r s : ℕ} (hs : 0 < s)
    (hrs : r ≤ s) (d : (d39FacedBall M s hs).D) :
    D39FiniteBallWithinRadius (d39FacedBall M s hs) r d ↔
      D39WithinRadius M r (d39VertexClass M d.1) :=
  ⟨within_toAmbient M s hs, fun h => ambient_toWithin M s hs h hrs d rfl⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
A dart is in the smaller ball iff both endpoints lie within its radius. -/
private theorem small_mem_iff (M : D39RootedMap) {r s : ℕ} (hs : 0 < s)
    (hrs : r ≤ s) (d : (d39FacedBall M s hs).D) :
    d.1 ∈ d39BallDarts M r ↔
      D39FiniteBallWithinRadius (d39FacedBall M s hs) r d ∧
        D39FiniteBallWithinRadius (d39FacedBall M s hs) r
          ((d39FacedBall M s hs).map.edgeInv d) := by
  rw [mem_d39BallDarts, mem_d39BallVertices, mem_d39BallVertices]
  exact and_congr (ballWithin_iff M hs hrs d).symm
    (ballWithin_iff M hs hrs ((d39FacedBall M s hs).map.edgeInv d)).symm

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An enclosing-ball isomorphism preserves membership in its smaller dart ball. -/
private theorem small_mem_iso (M N : D39RootedMap) {r s : ℕ} (hs : 0 < s)
    (hrs : r ≤ s) (I : D39BallIso (d39FacedBall M s hs) (d39FacedBall N s hs))
    (d : (d39FacedBall M s hs).D) :
    d.1 ∈ d39BallDarts M r ↔ (I.toEquiv d).1 ∈ d39BallDarts N r := by
  rw [small_mem_iff M hs hrs, small_mem_iff N hs hrs]
  rw [← I.edgeInv_comm]
  exact and_congr (ballWithin_iso_iff I r d)
    (ballWithin_iso_iff I r ((d39FacedBall M s hs).map.edgeInv d))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An intertwining map commutes with every integer power of the two permutations. -/
private theorem commuting_zpow {A C : Type*} (f : A → C)
    (p : Equiv.Perm A) (q : Equiv.Perm C)
    (h : ∀ x, f (p x) = q (f x)) (i : ℤ) (x : A) :
    f ((p ^ i) x) = (q ^ i) (f x) := by
  have hnat (n : ℕ) : ∀ x, f ((p ^ n) x) = (q ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, h, ih]
  have hinv (x : A) : f (p.symm x) = q.symm (f x) := by
    apply q.injective
    rw [← h, p.apply_symm_apply, q.apply_symm_apply]
  have hneg (n : ℕ) : ∀ x, f ((p.symm ^ n) x) = (q.symm ^ n) (f x) := by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  cases i with
  | ofNat n => exact hnat n x
  | negSucc n =>
    simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using hneg (n + 1) x

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
On a retained original face, finite and ambient face cycles agree. -/
private theorem original_cycle (M : D39RootedMap) (s : ℕ) (hs : 0 < s)
    (d e : (d39FacedBall M s hs).D)
    (hd : d ∈ (d39FacedBall M s hs).original) :
    (d39FacedBall M s hs).map.faceSucc.SameCycle d e ↔
      Equiv.Perm.SameCycle (M.core.rot.symm * M.core.edgeInv) d.1 e.1 := by
  classical
  let B := d39FacedBall M s hs
  let p := B.map.faceSucc.subtypePerm B.original_closed
  let x : {d : B.D // d ∈ B.original} := ⟨d, hd⟩
  let f : {d : B.D // d ∈ B.original} → M.core.D := fun z => z.1.1
  have hc (z) : f (p z) = (M.core.rot.symm * M.core.edgeInv) (f z) :=
    d39Ball_faceSucc_of_contained M s z.1 z.2
  have hb (i : ℤ) : ((p ^ i) x).1 = (B.map.faceSucc ^ i) d := by
    simp only [p, Equiv.Perm.subtypePerm_zpow, Equiv.Perm.subtypePerm_apply, x]
  have ha (i : ℤ) : ((p ^ i) x).1.1 = ((M.core.rot.symm * M.core.edgeInv) ^ i) d.1 :=
    commuting_zpow f p (M.core.rot.symm * M.core.edgeInv) hc i x
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← ha i, hb i, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [← hb i, ha i, hi]

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Original-face selection matches full-face cycles contained in the smaller dart ball. -/
private theorem original_radius_iff (M : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s) (d : (d39FacedBall M s hs).D) :
    d39BallContainsOriginalFace M r d.1 ↔
      d ∈ (d39FacedBall M s hs).original ∧
        ∀ e, (d39FacedBall M s hs).map.faceSucc.SameCycle d e →
          e.1 ∈ d39BallDarts M r := by
  constructor
  · intro h
    have hlarge : d ∈ (d39FacedBall M s hs).original :=
      fun e he => d39BallDarts_mono M hrs (h e he)
    exact ⟨hlarge, fun e he => h e.1 ((original_cycle M s hs d e hlarge).1 he)⟩
  · rintro ⟨hlarge, hsmall⟩ e he
    let e' : (d39FacedBall M s hs).D := ⟨e, hlarge e he⟩
    exact hsmall e' ((original_cycle M s hs d e' hlarge).2 he)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An enclosing-ball isomorphism preserves the smaller original-face selection. -/
private theorem original_iso_radius_iff (M N : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s hs) (d39FacedBall N s hs))
    (d : (d39FacedBall M s hs).D) :
    d39BallContainsOriginalFace N r (I.toEquiv d).1 ↔
      d39BallContainsOriginalFace M r d.1 := by
  have hcycle := framedBall_sameCycle_iff_of_equiv I.toEquiv
    (d39FacedBall M s hs).map.faceSucc (d39FacedBall N s hs).map.faceSucc I.face_comm
  rw [original_radius_iff N hs hrs, original_radius_iff M hs hrs]
  constructor
  · rintro ⟨h, hall⟩
    refine ⟨(I.original_iff d).1 h, fun e he => (small_mem_iso M N hs hrs I e).2 ?_⟩
    exact hall (I.toEquiv e) ((hcycle d e).1 he)
  · rintro ⟨h, hall⟩
    refine ⟨(I.original_iff d).2 h, ?_⟩
    intro e he
    obtain ⟨e, rfl⟩ := I.toEquiv.surjective e
    exact (small_mem_iso M N hs hrs I e).1 (hall e ((hcycle d e).2 he))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Flatten the two subtype layers of a nested dart ball. -/
@[expose] noncomputable def d39NestedBallEquiv (M : D39RootedMap) {r s : ℕ} (hrs : r ≤ s) :
    {z // z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)} ≃
      {d : M.core.D // d ∈ d39BallDarts M r} := by
  classical
  exact {
    toFun := fun z => ⟨z.1.1, by simpa [firstReturnSubset] using z.2⟩
    invFun := fun z => ⟨⟨z.1, d39BallDarts_mono M hrs z.2⟩,
      by simp [firstReturnSubset, z.2]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Nested first return agrees with direct first return on every retained dart. -/
theorem d39NestedBallEquiv_rot (M : D39RootedMap) {r s : ℕ} (hs : 0 < s) (hrs : r ≤ s)
    (z : {z // z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)}) :
    d39NestedBallEquiv M hrs
        (cyclicFirstReturn (d39FacedBall M s hs).map.rot
          (firstReturnSubset (d39BallDarts M s) (d39BallDarts M r))
          (finitePermutationReturn _ _) z) =
      (d39BallMap M r).rot (d39NestedBallEquiv M hrs z) := by
  classical
  have hret (V : Finset M.core.D) : ∀ x : V,
      ∃ k : ℕ, 0 < k ∧ (M.core.rot ^ k) x.1 ∈ V := by
    intro x
    obtain ⟨k, hk, heq⟩ := d39RotationReturn M x.1
    exact ⟨k, hk, by rw [heq]; exact x.2⟩
  apply Subtype.ext
  exact firstReturn_nested' M.core.rot (d39BallDarts M s) (d39BallDarts M r)
    (hret _) (fun d hd => d39BallDarts_mono M hrs hd)
    (finitePermutationReturn _ _) (hret _) (d39NestedBallEquiv M hrs z)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An enclosing-ball isomorphism preserves membership in the nested dart subset. -/
private theorem nested_mem_iso (M N : D39RootedMap) {r s : ℕ} (hs : 0 < s)
    (hrs : r ≤ s) (I : D39BallIso (d39FacedBall M s hs) (d39FacedBall N s hs))
    (d : (d39FacedBall M s hs).D) :
    d ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r) ↔
      I.toEquiv d ∈ firstReturnSubset (d39BallDarts N s) (d39BallDarts N r) := by
  classical
  have hmem (A : D39RootedMap) (z : {d : A.core.D // d ∈ d39BallDarts A s}) :
      z ∈ firstReturnSubset (d39BallDarts A s) (d39BallDarts A r) ↔
        z.1 ∈ d39BallDarts A r := by
    simp only [firstReturnSubset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hmem M d).trans ((small_mem_iso M N hs hrs I d).trans
    (hmem N (I.toEquiv d)).symm)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The enclosing-ball isomorphism induces an equivalence on smaller dart sets. -/
private noncomputable def restrictEquiv (M N : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s hs) (d39FacedBall N s hs)) :
    {d : M.core.D // d ∈ d39BallDarts M r} ≃
      {d : N.core.D // d ∈ d39BallDarts N r} :=
  (d39NestedBallEquiv M hrs).symm.trans
    ((I.toEquiv.subtypeEquiv (nested_mem_iso M N hs hrs I)).trans (d39NestedBallEquiv N hrs))

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The restricted equivalence commutes with the induced dart rotations. -/
private theorem restrictEquiv_rot (M N : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s hs) (d39FacedBall N s hs))
    (d : {d : M.core.D // d ∈ d39BallDarts M r}) :
    restrictEquiv M N hs hrs I ((d39BallMap M r).rot d) =
      (d39BallMap N r).rot (restrictEquiv M N hs hrs I d) := by
  classical
  let B := d39FacedBall M s hs
  let C := d39FacedBall N s hs
  let U := firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)
  let V := firstReturnSubset (d39BallDarts N s) (d39BallDarts N r)
  let e := I.toEquiv.subtypeEquiv (nested_mem_iso M N hs hrs I)
  let R := cyclicFirstReturn B.map.rot U (finitePermutationReturn _ _)
  let T := cyclicFirstReturn C.map.rot V (finitePermutationReturn _ _)
  let z := (d39NestedBallEquiv M hrs).symm d
  have hcomm : e (R z) = T (e z) := by
    apply Subtype.ext
    exact DirectedDistances.PaperProofs.Section3.cyclicFirstReturn_map_of_equiv
      B.map.rot C.map.rot U V I.toEquiv
      (nested_mem_iso M N hs hrs I) I.rot_comm
      (finitePermutationReturn _ _) (finitePermutationReturn _ _) z
  have hback : (d39NestedBallEquiv M hrs).symm ((d39BallMap M r).rot d) = R z := by
    apply (d39NestedBallEquiv M hrs).injective
    rw [Equiv.apply_symm_apply]
    have h := d39NestedBallEquiv_rot M hs hrs z
    simpa only [z, Equiv.apply_symm_apply] using h.symm
  change d39NestedBallEquiv N hrs
      (e ((d39NestedBallEquiv M hrs).symm ((d39BallMap M r).rot d))) =
    (d39BallMap N r).rot (d39NestedBallEquiv N hrs (e z))
  rw [hback, hcomm]
  exact d39NestedBallEquiv_rot N hs hrs (e z)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
An enclosing-ball isomorphism restricts to every smaller positive radius,
including ordered root marks and retained original-face incidences. -/
private noncomputable def restrictCandidate
    (M N : D39RootedMap) {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s (hr.trans_le hrs))
      (d39FacedBall N s (hr.trans_le hrs))) :
    D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr) where
  toEquiv := restrictEquiv M N (hr.trans_le hrs) hrs I
  rot_comm := restrictEquiv_rot M N (hr.trans_le hrs) hrs I
  edgeInv_comm := by
    intro d
    apply Subtype.ext
    have h := congrArg (fun z : (d39FacedBall N s (hr.trans_le hrs)).D => z.1)
      (I.edgeInv_comm ⟨d.1, d39BallDarts_mono M hrs d.2⟩)
    exact h
  missing_iff := fun d => I.missing_iff ⟨d.1, d39BallDarts_mono M hrs d.2⟩
  tail_iff := fun d => I.tail_iff ⟨d.1, d39BallDarts_mono M hrs d.2⟩
  root_comm := by
    apply Subtype.ext
    have h := congrArg (fun z : (d39FacedBall N s (hr.trans_le hrs)).D => z.1) I.root_comm
    exact h
  original_iff := fun d => original_iso_radius_iff M N (hr.trans_le hrs) hrs I
    ⟨d.1, d39BallDarts_mono M hrs d.2⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Existence of the full restriction, with its exact action on ambient dart identities. -/
theorem d39BallIso_restrict_exists (M N : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s (hr.trans_le hrs))
      (d39FacedBall N s (hr.trans_le hrs))) :
    ∃ J : D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr),
      ∀ d, (J.toEquiv d).1 =
        (I.toEquiv ⟨d.1, d39BallDarts_mono M hrs d.2⟩).1 :=
  ⟨restrictCandidate M N hr hrs I, fun _ => rfl⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Select the proved full restriction isomorphism, without an additional premise. -/
@[expose] noncomputable def D39BallIso.restrict (M N : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s (hr.trans_le hrs))
      (d39FacedBall N s (hr.trans_le hrs))) :
    D39BallIso (d39FacedBall M r hr) (d39FacedBall N r hr) :=
  Classical.choose (d39BallIso_restrict_exists M N hr hrs I)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Restriction acts on ambient dart identities by the original isomorphism. -/
theorem D39BallIso.restrict_apply (M N : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s)
    (I : D39BallIso (d39FacedBall M s (hr.trans_le hrs))
      (d39FacedBall N s (hr.trans_le hrs))) (d : (d39FacedBall M r hr).D) :
    ((I.restrict M N hr hrs).toEquiv d).1 =
      (I.toEquiv ⟨d.1, d39BallDarts_mono M hrs d.2⟩).1 :=
  Classical.choose_spec (d39BallIso_restrict_exists M N hr hrs I) d

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Classes at source radius r+1 determine classes at source radius r. -/
theorem d39BallClass_restriction_compatible (M N : D39RootedMap)
    (r : ℕ) (hr : 0 < r)
    (h : d39BallClass M (r + 1) (by omega) =
      d39BallClass N (r + 1) (by omega)) :
    d39BallClass M r hr = d39BallClass N r hr := by
  obtain ⟨I⟩ := (d39BallClass_eq_iff M N (r + 1) (by omega)).1 h
  exact (d39BallClass_eq_iff M N r hr).2 ⟨I.restrict M N hr (Nat.le_succ r)⟩

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The generic index r uses source radius r+1. The object universe is unrestricted
by countability; only the finite-ball class space is countable. -/
@[expose] noncomputable def d39RootedBallSystem :
    DirectedDistances.PaperProofs.Section3.RootedBallSystem D39BallClass where
  Object := D39RootedMap
  ballClass := fun r M => d39BallClass M (r + 1) (Nat.succ_pos r)
  restriction_compatible := fun r M N h =>
    d39BallClass_restriction_compatible M N (r + 1) (Nat.succ_pos r) h

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The intrinsic all-geometric radius-r dart set of a finite rooted ball. -/
@[expose] noncomputable def d39FiniteBallRadiusDarts (B : D39FiniteBall) (r : ℕ) :
    Finset B.D := by
  classical
  exact Finset.univ.filter fun d => D39FiniteBallWithinRadius B r d ∧
    D39FiniteBallWithinRadius B r (B.map.edgeInv d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The intrinsic smaller ball has exactly the ambient smaller dart identities. -/
theorem d39FacedBall_radiusDarts (M : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s) :
    d39FiniteBallRadiusDarts (d39FacedBall M s hs) r =
      firstReturnSubset (d39BallDarts M s) (d39BallDarts M r) := by
  classical
  have hleft (B : D39FiniteBall) (d : B.D) :
      d ∈ d39FiniteBallRadiusDarts B r ↔
        D39FiniteBallWithinRadius B r d ∧
          D39FiniteBallWithinRadius B r (B.map.edgeInv d) := by
    simp only [d39FiniteBallRadiusDarts, Finset.mem_filter, Finset.mem_univ, true_and]
  have hright (z : {d : M.core.D // d ∈ d39BallDarts M s}) :
      z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r) ↔
        z.1 ∈ d39BallDarts M r := by
    simp only [firstReturnSubset, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Finset.ext
  intro d
  exact (hleft (d39FacedBall M s hs) d).trans
    ((small_mem_iff M hs hrs d).symm.trans (hright d).symm)


/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The nested induced map restricts the inherited plane rotation a second time. -/
@[expose] noncomputable def d39NestedBallMap (M : D39RootedMap) (r s : ℕ) :
    CombinatorialMap
      {z // z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)} :=
  inducedCombinatorialMap (d39BallMap M s)
    (firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)) (by
      intro d hd
      have hsmall : d.1 ∈ d39BallDarts M r := by
        simpa [firstReturnSubset] using hd
      have hflip := d39BallDarts_edgeInv_closed M r d.1 hsmall
      simpa [firstReturnSubset, d39BallMap_edgeInv] using hflip)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
Flattening the nested ball preserves its face incidence successor. -/
theorem d39NestedBallEquiv_face (M : D39RootedMap) {r s : ℕ}
    (hs : 0 < s) (hrs : r ≤ s)
    (d : {z // z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)}) :
    d39NestedBallEquiv M hrs ((d39NestedBallMap M r s).faceSucc d) =
      (d39BallMap M r).faceSucc (d39NestedBallEquiv M hrs d) := by
  let e := d39NestedBallEquiv M hrs
  let N := d39NestedBallMap M r s
  let K := d39BallMap M r
  have hrot (x) : e (N.rot x) = K.rot (e x) := d39NestedBallEquiv_rot M hs hrs x
  change e (N.rot.symm (N.edgeInv d)) = K.rot.symm (K.edgeInv (e d))
  apply K.rot.injective
  rw [← hrot, N.rot.apply_symm_apply, K.rot.apply_symm_apply]
  apply Subtype.ext
  rfl


/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The smaller intrinsic ball inside an enclosing ball, with the original faces
that remain wholly contained. The radius-set identity and original-face
characterization identify this construction with actual ball restriction. -/
@[expose] noncomputable def d39NestedFacedBall (M : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s) : D39FiniteBall where
  D := {z // z ∈ firstReturnSubset (d39BallDarts M s) (d39BallDarts M r)}
  map := d39NestedBallMap M r s
  missing := fun d => M.core.missing d.1.1
  tail := fun d => M.core.tail d.1.1
  rootDart := (d39NestedBallEquiv M hrs).symm (d39FacedBall M r hr).rootDart
  original := {d | d39BallContainsOriginalFace M r d.1.1}
  original_closed := by
    intro d
    change d39BallContainsOriginalFace M r
      (((d39NestedBallMap M r s).faceSucc d).1.1) ↔ _
    have h := congrArg Subtype.val (d39NestedBallEquiv_face M (hr.trans_le hrs) hrs d)
    change ((d39NestedBallMap M r s).faceSucc d).1.1 =
      ((d39BallMap M r).faceSucc (d39NestedBallEquiv M hrs d)).1 at h
    rw [h]
    exact d39BallContainsOriginalFace_closed M r (d39NestedBallEquiv M hrs d)

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The nested original-face selection is intrinsic to the enclosing faced ball. -/
theorem d39NestedFacedBall_original_iff (M : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s) (d : (d39NestedFacedBall M hr hrs).D) :
    d ∈ (d39NestedFacedBall M hr hrs).original ↔
      d.1 ∈ (d39FacedBall M s (hr.trans_le hrs)).original ∧
        ∀ e, (d39FacedBall M s (hr.trans_le hrs)).map.faceSucc.SameCycle d.1 e →
          e.1 ∈ d39BallDarts M r :=
  original_radius_iff M (hr.trans_le hrs) hrs d.1

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The radius-r ball of the enclosing radius-s ball is isomorphic to the
direct radius-r ball, preserving every retained datum; in particular s=r+1. -/
@[expose] noncomputable def d39NestedFacedBallIso (M : D39RootedMap) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s) :
    D39BallIso (d39NestedFacedBall M hr hrs) (d39FacedBall M r hr) where
  toEquiv := d39NestedBallEquiv M hrs
  rot_comm := d39NestedBallEquiv_rot M (hr.trans_le hrs) hrs
  edgeInv_comm := by intro d; apply Subtype.ext; rfl
  missing_iff := fun _ => Iff.rfl
  tail_iff := fun _ => Iff.rfl
  root_comm := Equiv.apply_symm_apply _ _
  original_iff := fun _ => Iff.rfl

/-- Helper toward Definition 3.8 (def-bs-topology, local topology v1+v2); not a paper result.
The root dart is exactly the dart of the retained present-or-missing root mark. -/
theorem d39FacedBall_rootMark (M : D39RootedMap) (r : ℕ) (hr : 0 < r) :
    (d39FacedBall M r hr).rootDart =
      match d39BallRootMark M r hr with
      | .present d _ _ => d
      | .missing d _ => d := by
  cases M with
  | mk c m => cases m <;> rfl

end DirectedDistances.PlanarMap
end
