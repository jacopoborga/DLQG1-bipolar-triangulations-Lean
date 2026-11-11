module

public import DirectedDistances.PaperProofs.Section5.Prop59FiniteReflectionGrade5
public import DirectedDistances.PaperProofs.Section5.Prop59CodeLawMirror
public import DirectedDistances.PaperProofs.Section5.Prop59ProviderMirror2

public section
namespace DirectedDistances.PaperProofs.Section5

open DirectedDistances.KMSW DirectedDistances.PlanarMap MeasureTheory




theorem diskRootedPlanarMapOfRightSample_eq_mirror
    (n ell : ℕ) (hell : 0 < ell)
    (p : Prop59LeftFiniteClass n ell × Fin ell) :
    diskRootedPlanarMapOfRightSample n ell hell
        (prop59FiniteReflectionClassEquiv n ell hell p.1, p.2.rev) =
      mirrorRootedLocallyFinitePlanarMap
        (diskRootedPlanarMapOfSample n ell hell p) := by
  simp [diskRootedPlanarMapOfRightSample, Fin.rev_rev]
































end DirectedDistances.PaperProofs.Section5
