import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveTorsorClassAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_torsor_class_additive : DescentSt → LowSt → AxOSt → AllAb fun _ _ A _ _ ↦ ∀ (c : HO1 A.hom) (a b d : HO1 (A ⊗ A).hom), IsPullO (wOver (fst A A * snd A A)) c a → IsPullO (wOver (fst A A)) c b → IsPullO (wOver (snd A A)) c d → a = b + d := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SmallLift.primitive_HO1_abelian
