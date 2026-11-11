module

public import DirectedDistances.KMSW.KMSWWindowFreshSetCapture
public import DirectedDistances.KMSW.KMSWWindowPatchVertex
public import DirectedDistances.KMSW.KMSWWindowPatchInjective

/-! Helper toward prop-disk-bs-conv / Proposition 5.16
ball capture through the KMSW window maps, parameterized by a transported
the Definition 3.8 distance (with or without missing edges;
ROOT convention, or local-topology definition is adopted; not the paper result.
For downstream users,
the source-ordered root (x₀, x₁) corresponds to
`(stageEndpoint (edgeFlip d), stageEndpoint d)` for the Lean disk root dart `d`,
so source centre x₀ is the endpoint of `edgeFlip d`. This file does not choose it. -/

public section
namespace DirectedDistances.KMSW

/-- A stage-dependent predicate on geometric edges from the ball construction -/
abbrev KMSWStageEdgePredicate :=
  (s : State) → Fin s.nextEdge → Prop

/-- One undirected step along an admissible geometric edge; the dart and its -/
@[expose] def kmswStageAdjacent (P : KMSWStageEdgePredicate)
    (s : State) (x y : ℕ) : Prop :=
  ∃ d : StageDart s.nextEdge,
    P s d.1 ∧ stageEndpoint s d = x ∧
      stageEndpoint s (edgeFlip _ d) = y

/-- A path records its natural number of undirected edge steps and all vertices -/
inductive KMSWStagePath (P : KMSWStageEdgePredicate) (s : State)
    (V : Set ℕ) (root : ℕ) : ℕ → ℕ → Prop where
  | nil (hv : root ∈ V) : KMSWStagePath P s V root 0 root
  | snoc {n y z} (hpath : KMSWStagePath P s V root n y)
      (hy : y ∈ V) (hz : z ∈ V)
      (hadj : kmswStageAdjacent P s y z) :
      KMSWStagePath P s V root (n + 1) z

/-- Reachability by at most `r` admissible undirected edge steps. This
Prop-valued relation avoids choosing arithmetic conventions for `ℕ∞` -/
@[expose] def kmswStageDistanceLe (P : KMSWStageEdgePredicate)
    (s : State) (r x y : ℕ) : Prop :=
  ∃ k, k ≤ r ∧
    KMSWStagePath P s Set.univ x k y

/-- Forget the vertex restriction on a path -/
theorem kmswStagePathForgetVertices (P : KMSWStageEdgePredicate)
    (s : State) (V : Set ℕ) {k x y : ℕ}
    (hpath : KMSWStagePath P s V x k y) :
    KMSWStagePath P s Set.univ x k y := by
  induction hpath with
  | nil _ => exact .nil (Set.mem_univ _)
  | @snoc n y z hpre _ _ hadj ih =>
      exact .snoc ih (Set.mem_univ _) (Set.mem_univ _) hadj

/-- Any path gives the corresponding bounded-distance witness -/
theorem kmswStageDistanceLe_of_path (P : KMSWStageEdgePredicate)
    (s : State) {r k x y : ℕ}
    (hpath : KMSWStagePath P s Set.univ x k y) (hk : k ≤ r) :
    kmswStageDistanceLe P s r x y :=
  ⟨k, hk, hpath⟩

/-- Source-side radius-ball closure makes every bounded path lie in the fresh -/
theorem kmswStagePathIn_of_distanceClosed
    (P : KMSWStageEdgePredicate) (s : State) (S : Set ℕ)
    (r c : ℕ)
    (hclosed : ∀ x, kmswStageDistanceLe P s r c x → x ∈ S)
    {k y : ℕ} (hpath : KMSWStagePath P s Set.univ c k y)
    (hk : k ≤ r) :
    KMSWStagePath P s S c k y := by
  induction hpath with
  | nil _ =>
      have hroot : kmswStageDistanceLe P s r c c := by
        exact ⟨0, Nat.zero_le _, .nil (Set.mem_univ _)⟩
      exact .nil (hclosed c hroot)
  | @snoc n y z hpre _ _ hadj ih =>
      have hn : n ≤ r := le_trans (Nat.le_succ _) hk
      have hyDist := kmswStageDistanceLe_of_path P s hpre hn
      have hzDist := kmswStageDistanceLe_of_path P s
        (KMSWStagePath.snoc hpre (Set.mem_univ _) (Set.mem_univ _) hadj) hk
      have ih' := ih hn
      exact .snoc ih' (hclosed y hyDist) (hclosed z hzDist) hadj

/-- Edge admissibility is transported when both edge endpoints are fresh -/
@[expose] def kmswWindowEdgePredicateTransport
    (P : KMSWStageEdgePredicate) (w : ℕ → Fin 3) (s m : ℕ)
    (S : Finset ℕ) : Prop :=
  ∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
    stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S →
    stageEndpoint (kmswStage (fun i => w (s + i)) m) (edgeFlip _ d) ∈ S →
    (P (kmswStage (fun i => w (s + i)) m) d.1 ↔
      P (kmswStage w (s + m))
        (kmswWindowFreshSetEdgeMap w s m d.1))

/-- All geometric edges are transported on any fresh vertex set -/
theorem kmswWindowAllEdgesTransport (w : ℕ → Fin 3) (s m : ℕ)
    (S : Finset ℕ) :
    kmswWindowEdgePredicateTransport (fun _ _ => True) w s m S := by
  intro d hd₁ hd₂
  simp

/-- Present-edge admissibility is transported using the fresh-set status -/
theorem kmswWindowPresentEdgesTransport (w : ℕ → Fin 3) (s m : ℕ)
    (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v) :
    kmswWindowEdgePredicateTransport
      (fun t e => t.present e.val = true) w s m S := by
  intro d hd₁ hd₂
  have hp := kmswWindowFreshSetPresentCapture w s m S hS d hd₁
  have hEdgeDart :
      (kmswWindowDartMap w s m d).1 =
        kmswWindowFreshSetEdgeMap w s m d.1 := by
    cases d with
    | mk e b => cases b <;> rfl
  have hstatus :
      (kmswStage (fun i => w (s + i)) m).present d.1.val =
        (kmswStage w (s + m)).present
          (kmswWindowFreshSetEdgeMap w s m d.1).val := by
    exact hp.trans (congrArg
      (fun e : Fin (kmswStage w (s + m)).nextEdge =>
        (kmswStage w (s + m)).present e.val) hEdgeDart)
  change (kmswStage (fun i => w (s + i)) m).present d.1.val = true ↔
    (kmswStage w (s + m)).present
      (kmswWindowFreshSetEdgeMap w s m d.1).val = true
  rw [hstatus]

/-- An admissible path whose vertices lie in the fresh set maps to the global
stage with the same length and mapped endpoints -/
theorem kmswWindowPathTransport (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    {root k y : ℕ}
    (hpath : KMSWStagePath P (kmswStage (fun i => w (s + i)) m)
      (S : Set ℕ) root k y) :
    KMSWStagePath P (kmswStage w (s + m))
      (Set.image (kmswWindowPatchVertexMap w s m) S)
      (kmswWindowPatchVertexMap w s m root) k
      (kmswWindowPatchVertexMap w s m y) := by
  induction hpath with
  | nil hx =>
      exact .nil (Set.mem_image_of_mem _ hx)
  | @snoc n y z hpre hy hz hadj ih =>
      obtain ⟨d, hpred, hstart, hend⟩ := hadj
      have hstartMem :
          stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈ S :=
        hstart ▸ hy
      have hendMem :
          stageEndpoint (kmswStage (fun i => w (s + i)) m)
            (edgeFlip _ d) ∈ S := hend ▸ hz
      have hpred' : P (kmswStage w (s + m))
          (kmswWindowFreshSetEdgeMap w s m d.1) :=
        (hP d hstartMem hendMem).mp hpred
      have hmapEndpoint := kmswWindowDartMap_vertex w s m d
      have hmapOpposite := kmswWindowDartMap_vertex w s m
        (edgeFlip _ d)
      rw [kmswWindowFreshSetEdgeFlipCapture] at hmapOpposite
      have hmapEndpoint' :
          stageEndpoint (kmswStage w (s + m))
            (kmswWindowDartMap w s m d) =
          kmswWindowPatchVertexMap w s m (stageEndpoint
            (kmswStage (fun i => w (s + i)) m) d) := by
        simpa [stageEndpoint] using hmapEndpoint
      have hmapOpposite' :
          stageEndpoint (kmswStage w (s + m))
            (edgeFlip _ (kmswWindowDartMap w s m d)) =
          kmswWindowPatchVertexMap w s m (stageEndpoint
            (kmswStage (fun i => w (s + i)) m) (edgeFlip _ d)) := by
        simpa [stageEndpoint] using hmapOpposite
      have hmap :
          kmswWindowDartMap w s m d =
            (kmswWindowFreshSetEdgeMap w s m d.1, d.2) := by
        cases d with
        | mk e b => cases b <;> rfl
      have hstart' :
          stageEndpoint (kmswStage w (s + m))
            (kmswWindowDartMap w s m d) =
          kmswWindowPatchVertexMap w s m y := by
        calc
          _ = kmswWindowPatchVertexMap w s m
              (stageEndpoint (kmswStage (fun i => w (s + i)) m) d) :=
            hmapEndpoint'
          _ = kmswWindowPatchVertexMap w s m y :=
            congrArg (kmswWindowPatchVertexMap w s m) hstart
      have hend' :
          stageEndpoint (kmswStage w (s + m))
            (edgeFlip _ (kmswWindowDartMap w s m d)) =
          kmswWindowPatchVertexMap w s m z := by
        calc
          _ = kmswWindowPatchVertexMap w s m
              (stageEndpoint (kmswStage (fun i => w (s + i)) m)
                (edgeFlip _ d)) := hmapOpposite'
          _ = kmswWindowPatchVertexMap w s m z :=
            congrArg (kmswWindowPatchVertexMap w s m) hend
      have hadj' : kmswStageAdjacent P (kmswStage w (s + m))
          (kmswWindowPatchVertexMap w s m y)
          (kmswWindowPatchVertexMap w s m z) := by
        refine ⟨kmswWindowDartMap w s m d, ?_, hstart', hend'⟩
        simpa [hmap] using hpred'
      have hy' : kmswWindowPatchVertexMap w s m y ∈
          Set.image (kmswWindowPatchVertexMap w s m) S :=
        Set.mem_image_of_mem _ hy
      have hz' : kmswWindowPatchVertexMap w s m z ∈
          Set.image (kmswWindowPatchVertexMap w s m) S :=
        Set.mem_image_of_mem _ hz
      exact .snoc ih hy' hz' hadj'

/-- Bounded-distance transport follows from path transport for a path whose -/
theorem kmswWindowDistanceLeTransport (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    {r k root y : ℕ} (hk : k ≤ r)
    (hpath : KMSWStagePath P (kmswStage (fun i => w (s + i)) m)
      (S : Set ℕ) root k y) :
    kmswStageDistanceLe P (kmswStage w (s + m)) r
      (kmswWindowPatchVertexMap w s m root)
      (kmswWindowPatchVertexMap w s m y) := by
  have hglobal := kmswWindowPathTransport P w s m S hP hpath
  exact ⟨k, hk, kmswStagePathForgetVertices P _ _ hglobal⟩

/-- An admissible global step between two image vertices lifts to the fresh
window, preserving dart identity and ordered endpoints -/
theorem kmswWindowAdjacentLift (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    {x y : ℕ}
    (hadj : kmswStageAdjacent P (kmswStage w (s + m)) x y)
    (hx : x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hy : y ∈ Set.image (kmswWindowPatchVertexMap w s m) S) :
    ∃ u v, u ∈ S ∧ v ∈ S ∧
      kmswWindowPatchVertexMap w s m u = x ∧
      kmswWindowPatchVertexMap w s m v = y ∧
      kmswStageAdjacent P (kmswStage (fun i => w (s + i)) m) u v := by
  obtain ⟨dG, hpredG, hstartG, hendG⟩ := hadj
  have hstartImage :
      stageEndpoint (kmswStage w (s + m)) dG ∈
        Set.image (kmswWindowPatchVertexMap w s m) (S : Set ℕ) := by
    rw [hstartG]
    exact hx
  obtain ⟨a, ha, hax⟩ :=
    (Set.mem_image _ (S : Set ℕ) _).mp hstartImage
  have hstartFin : stageEndpoint (kmswStage w (s + m)) dG ∈
      S.image (kmswWindowPatchVertexMap w s m) := by
    rw [← hax]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩
  obtain ⟨dF, hdF, hmap⟩ :=
    (kmswWindowFreshSetDartCapture w s m S hS).2.2.1 dG hstartFin
  let u := stageEndpoint (kmswStage (fun i => w (s + i)) m) dF
  let v := stageEndpoint (kmswStage (fun i => w (s + i)) m)
    (edgeFlip _ dF)
  have hmapStart := kmswWindowDartMap_vertex w s m dF
  have hmapEnd := kmswWindowDartMap_vertex w s m (edgeFlip _ dF)
  have hflip := kmswWindowFreshSetEdgeFlipCapture w s m dF
  have hstart :
      kmswWindowPatchVertexMap w s m u = x := by
    calc
      _ = stageEndpoint (kmswStage w (s + m))
          (kmswWindowDartMap w s m dF) := by
        simpa [u, stageEndpoint] using hmapStart.symm
      _ = stageEndpoint (kmswStage w (s + m)) dG := by rw [hmap]
      _ = x := hstartG
  have hend :
      kmswWindowPatchVertexMap w s m v = y := by
    calc
      _ = stageEndpoint (kmswStage w (s + m))
          (edgeFlip _ (kmswWindowDartMap w s m dF)) := by
        rw [← hflip]
        simpa [v, stageEndpoint] using hmapEnd.symm
      _ = stageEndpoint (kmswStage w (s + m))
          (edgeFlip _ dG) := by rw [hmap]
      _ = y := hendG
  have hendImage :
      stageEndpoint (kmswStage w (s + m)) (edgeFlip _ dG) ∈
        Set.image (kmswWindowPatchVertexMap w s m) (S : Set ℕ) := by
    rw [hendG]
    exact hy
  obtain ⟨z, hz, hzy⟩ :=
    (Set.mem_image _ (S : Set ℕ) _).mp hendImage
  have hzS : z ∈ S := Finset.mem_coe.mp hz
  have hvBound : v < (kmswStage (fun i => w (s + i)) m).nextVertex := by
    exact stageEndpoint_lt_nextVertex (fun i => w (s + i)) m (edgeFlip _ dF)
  obtain ⟨hzBound, _⟩ := hS z hzS
  have hvEq : v = z :=
    kmswWindowPatchVertexMap_injOn w s m hvBound hzBound
      (hend.trans (hzy.trans hendG).symm)
  have hvS : v ∈ S := hvEq ▸ hzS
  have htransport : P (kmswStage (fun i => w (s + i)) m) dF.1 ↔
      P (kmswStage w (s + m))
        (kmswWindowFreshSetEdgeMap w s m dF.1) :=
    hP dF hdF (by simpa [v] using hvS)
  have hEdgeDart :
      (kmswWindowDartMap w s m dF).1 =
        kmswWindowFreshSetEdgeMap w s m dF.1 := by
    cases dF with
    | mk e b => cases b <;> rfl
  have hEdgeMap : kmswWindowFreshSetEdgeMap w s m dF.1 = dG.1 := by
    calc
      kmswWindowFreshSetEdgeMap w s m dF.1 =
          (kmswWindowDartMap w s m dF).1 := hEdgeDart.symm
      _ = dG.1 := congrArg Prod.fst hmap
  have hpredF : P (kmswStage (fun i => w (s + i)) m) dF.1 := by
    apply htransport.mpr
    rw [hEdgeMap]
    exact hpredG
  refine ⟨u, v, hdF, hvS, hstart, hend, ?_⟩
  exact ⟨dF, hpredF, rfl, rfl⟩

/-- A global path of length at most `r` from the mapped center lifts through
the dart capture bijection when its radius-`r` ball lies in the image -/
theorem kmswWindowPathLift (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    (hBall : ∀ x,
      kmswStageDistanceLe P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hc : c ∈ S) {k x : ℕ} (hk : k ≤ r)
    (hpath : KMSWStagePath P (kmswStage w (s + m)) Set.univ
      (kmswWindowPatchVertexMap w s m c) k x) :
    ∃ y, y ∈ S ∧ kmswWindowPatchVertexMap w s m y = x ∧
      KMSWStagePath P (kmswStage (fun i => w (s + i)) m)
        (S : Set ℕ) c k y := by
  induction hpath with
  | nil _ =>
      exact ⟨c, hc, rfl, .nil hc⟩
  | @snoc n y z hpre _ _ hadj ih =>
      have hn : n ≤ r := by omega
      obtain ⟨u, hu, huy, hpreF⟩ := ih hn
      have hfull : KMSWStagePath P (kmswStage w (s + m))
          Set.univ (kmswWindowPatchVertexMap w s m c) (n + 1) z :=
        .snoc hpre (Set.mem_univ _) (Set.mem_univ _) hadj
      have hzBall := kmswStageDistanceLe_of_path P
        (kmswStage w (s + m)) hfull hk
      have hzImage := hBall z hzBall
      have hyImage :
          y ∈ Set.image (kmswWindowPatchVertexMap w s m) (S : Set ℕ) := by
        rw [← huy]
        exact Set.mem_image_of_mem _ (show u ∈ (S : Set ℕ) from hu)
      obtain ⟨u', v', hu', hv', huy', hvz, hadjF⟩ :=
        kmswWindowAdjacentLift P w s m S hS hP hadj
          hyImage hzImage
      have huBound := (hS u hu).1
      have hu'Bound := (hS u' hu').1
      have huEq : u' = u :=
        kmswWindowPatchVertexMap_injOn w s m hu'Bound huBound
          (huy'.trans huy.symm)
      have hadjF' : kmswStageAdjacent P
          (kmswStage (fun i => w (s + i)) m) u v' := by
        simpa [huEq] using hadjF
      refine ⟨v', hv', hvz, ?_⟩
      exact .snoc hpreF hu hv' hadjF'

/-- Bounded distances agree on the fresh set under radius-ball capture and
closure puts every path in the forward implication inside the domain where
edge admissibility is captured. -/
theorem kmswWindowDistanceLeCapture (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    (hBall : ∀ x,
      kmswStageDistanceLe P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ))
    (hc : c ∈ S) (v : ℕ) (hv : v ∈ S) {k : ℕ} (hk : k ≤ r) :
    kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) k c v ↔
      kmswStageDistanceLe P (kmswStage w (s + m)) k
        (kmswWindowPatchVertexMap w s m c)
        (kmswWindowPatchVertexMap w s m v) := by
  constructor
  · rintro ⟨n, hn, hpath⟩
    have hnr : n ≤ r := hn.trans hk
    have hpathIn := kmswStagePathIn_of_distanceClosed P
      (kmswStage (fun i => w (s + i)) m) (S : Set ℕ) r c hClosed
      hpath hnr
    have hpathGlobal := kmswWindowPathTransport P w s m S hP hpathIn
    exact ⟨n, hn, kmswStagePathForgetVertices P _ _ hpathGlobal⟩
  · rintro ⟨n, hn, hpath⟩
    have hnr : n ≤ r := hn.trans hk
    obtain ⟨u, hu, hψu, hpathIn⟩ := kmswWindowPathLift P w s m S r c
      hS hP hBall hc hnr hpath
    obtain ⟨huBound, _⟩ := hS u hu
    obtain ⟨hvBound, _⟩ := hS v hv
    have huv : u = v :=
      kmswWindowPatchVertexMap_injOn w s m huBound hvBound hψu
    subst u
    exact ⟨n, hn, kmswStagePathForgetVertices P _ _ hpathIn⟩

/-- The finite set of stage vertices at `P`-admissible graph distance at most
stage-vertex carrier `{x | x < s.nextVertex}`; a centre used as a stage vertex
must satisfy `c < s.nextVertex`. -/
@[expose] noncomputable def kmswStageBallVertices
    (P : KMSWStageEdgePredicate) (s : State) (r c : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range s.nextVertex).filter
    (fun v => kmswStageDistanceLe P s r c v)

/-- The fresh-set image of the source ball is exactly the target ball -/
theorem kmswWindowBallVerticesImageEq (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    (hBall : ∀ x,
      kmswStageDistanceLe P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ))
    (hc : c ∈ S) :
    (kmswStageBallVertices P
      (kmswStage (fun i => w (s + i)) m) r c).image
        (kmswWindowPatchVertexMap w s m) =
      kmswStageBallVertices P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨v, hvball, hvx⟩ := Finset.mem_image.mp hx
    obtain ⟨hvRange, hvdist⟩ := Finset.mem_filter.mp hvball
    have hvbound := Finset.mem_range.mp hvRange
    have hvS : v ∈ S := Finset.mem_coe.mp (hClosed v hvdist)
    have hcapture := kmswWindowDistanceLeCapture P w s m S r c
      hS hP hBall hClosed hc v hvS (le_rfl : r ≤ r)
    have hxbound : x < (kmswStage w (s + m)).nextVertex := by
      rw [← hvx]
      exact (kmswWindowPatchVertexMap_rel w s m).vertex_bound v hvbound
    rw [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range]
    refine ⟨hxbound, ?_⟩
    rw [← hvx]
    exact hcapture.mp hvdist
  · intro hx
    obtain ⟨hxbound, hxdist⟩ := Finset.mem_filter.mp hx
    have hxImage := hBall x hxdist
    obtain ⟨v, hvS, hvx⟩ :=
      (Set.mem_image _ (S : Set ℕ) _).mp hxImage
    have hvSFin : v ∈ S := Finset.mem_coe.mp hvS
    have hcapture := kmswWindowDistanceLeCapture P w s m S r c
      hS hP hBall hClosed hc v hvSFin (le_rfl : r ≤ r)
    have hvdist :
        kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c v := by
      apply hcapture.mpr
      simpa [hvx] using hxdist
    have hvbound := (hS v hvSFin).1
    have hvball : v ∈ kmswStageBallVertices P
        (kmswStage (fun i => w (s + i)) m) r c := by
      rw [kmswStageBallVertices, Finset.mem_filter, Finset.mem_range]
      exact ⟨hvbound, hvdist⟩
    exact Finset.mem_image.mpr ⟨v, hvball, hvx⟩

/-- The window vertex map is a bijection between the two radius-`r` balls -/
theorem kmswWindowBallVertexMapBijective (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    (hBall : ∀ x,
      kmswStageDistanceLe P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ))
    (hc : c ∈ S) :
    Function.Bijective
      (fun v : {x // x ∈ kmswStageBallVertices P
          (kmswStage (fun i => w (s + i)) m) r c} =>
        (⟨kmswWindowPatchVertexMap w s m v.1, by
          rw [← kmswWindowBallVerticesImageEq P w s m S r c hS hP
            hBall hClosed hc]
          exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
          {x // x ∈ kmswStageBallVertices P
            (kmswStage w (s + m)) r
            (kmswWindowPatchVertexMap w s m c)})) := by
  classical
  have himage := kmswWindowBallVerticesImageEq P w s m S r c
    hS hP hBall hClosed hc
  constructor
  · intro a b hab
    apply Subtype.ext
    have haS : a.1 ∈ S := Finset.mem_coe.mp
      (hClosed a.1 (Finset.mem_filter.mp a.2).2)
    have hbS : b.1 ∈ S := Finset.mem_coe.mp
      (hClosed b.1 (Finset.mem_filter.mp b.2).2)
    obtain ⟨haBound, _⟩ := hS a.1 haS
    obtain ⟨hbBound, _⟩ := hS b.1 hbS
    exact kmswWindowPatchVertexMap_injOn w s m haBound hbBound
      (congrArg Subtype.val hab)
  · intro b
    have hbImage : b.1 ∈
        (kmswStageBallVertices P
          (kmswStage (fun i => w (s + i)) m) r c).image
            (kmswWindowPatchVertexMap w s m) := by
      rw [himage]
      exact b.2
    obtain ⟨v, hv, hψv⟩ := Finset.mem_image.mp hbImage
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hψv

/-- Induced geometric edge IDs on the two balls correspond bijectively,
including parallel edges; target endpoints are the target ball by the image
dart theorem captures status, rotations and face successors. -/
theorem kmswWindowBallInducedEdgesBijective (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hP : kmswWindowEdgePredicateTransport P w s m S)
    (hBall : ∀ x,
      kmswStageDistanceLe P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) x →
      x ∈ Set.image (kmswWindowPatchVertexMap w s m) S)
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ))
    (hc : c ∈ S) :
    (kmswStageBallVertices P
      (kmswStage (fun i => w (s + i)) m) r c).image
        (kmswWindowPatchVertexMap w s m) =
      kmswStageBallVertices P (kmswStage w (s + m)) r
        (kmswWindowPatchVertexMap w s m c) ∧
    Function.Bijective (kmswWindowFreshSetEdgeMapOn w s m
      (kmswStageBallVertices P
        (kmswStage (fun i => w (s + i)) m) r c)) := by
  classical
  have hImage := kmswWindowBallVerticesImageEq P w s m S r c
    hS hP hBall hClosed hc
  have hFreshBall : ∀ v ∈ kmswStageBallVertices P
      (kmswStage (fun i => w (s + i)) m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    intro v hv
    have hvS := Finset.mem_coe.mp
      (hClosed v (Finset.mem_filter.mp hv).2)
    exact hS v hvS
  have hedge := kmswWindowFreshSetEdgeMap_bijective w s m
    (kmswStageBallVertices P
      (kmswStage (fun i => w (s + i)) m) r c) hFreshBall
  exact ⟨hImage, hedge⟩

/-- Present status, rotation and face successors are retained on the radius
ball under the captured dart and edge maps -/
theorem kmswWindowBallDartStructureCapture (P : KMSWStageEdgePredicate)
    (w : ℕ → Fin 3) (s m : ℕ) (S : Finset ℕ) (r c : ℕ)
    (hS : ∀ v ∈ S,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v)
    (hClosed : ∀ x,
      kmswStageDistanceLe P (kmswStage (fun i => w (s + i)) m) r c x →
      x ∈ (S : Set ℕ)) :
    (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈
          kmswStageBallVertices P
            (kmswStage (fun i => w (s + i)) m) r c →
      (kmswStage (fun i => w (s + i)) m).present d.1.val =
        (kmswStage w (s + m)).present
          (kmswWindowDartMap w s m d).1.val) ∧
    (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m) d ∈
          kmswStageBallVertices P
            (kmswStage (fun i => w (s + i)) m) r c →
      (kmswMap w (s + m)).rot (kmswWindowDartMap w s m d) =
        kmswWindowDartMap w s m
          ((kmswMap (fun i => w (s + i)) m).rot d) ∧
        (kmswMap w (s + m)).rot.symm (kmswWindowDartMap w s m d) =
          kmswWindowDartMap w s m
            ((kmswMap (fun i => w (s + i)) m).rot.symm d)) ∧
    (∀ d : StageDart (kmswStage (fun i => w (s + i)) m).nextEdge,
      stageEndpoint (kmswStage (fun i => w (s + i)) m)
        d ∈ kmswStageBallVertices P
          (kmswStage (fun i => w (s + i)) m) r c →
      stageEndpoint (kmswStage (fun i => w (s + i)) m)
        (edgeFlip _ d) ∈ kmswStageBallVertices P
          (kmswStage (fun i => w (s + i)) m) r c →
      (kmswMap w (s + m)).faceSucc (kmswWindowDartMap w s m d) =
        kmswWindowDartMap w s m
          ((kmswMap (fun i => w (s + i)) m).faceSucc d)) := by
  classical
  have hFreshBall : ∀ v ∈ kmswStageBallVertices P
      (kmswStage (fun i => w (s + i)) m) r c,
      v < (kmswStage (fun i => w (s + i)) m).nextVertex ∧
        (kmswStage w s).nextVertex ≤ kmswWindowPatchVertexMap w s m v := by
    intro v hv
    exact hS v (Finset.mem_coe.mp
      (hClosed v (Finset.mem_filter.mp hv).2))
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact kmswWindowFreshSetPresentCapture w s m _ hFreshBall d hd
  · intro d hd
    exact kmswWindowFreshSetRotationCapture w s m _ hFreshBall d hd
  · intro d _ hd
    exact kmswWindowFreshSetFaceSuccCapture w s m _ hFreshBall d hd

end DirectedDistances.KMSW
