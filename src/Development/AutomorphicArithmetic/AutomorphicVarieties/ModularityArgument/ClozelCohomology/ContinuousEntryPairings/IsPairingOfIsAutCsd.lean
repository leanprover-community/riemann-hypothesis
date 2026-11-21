import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu UpperTheory.V.Published GlobalTheory.MonoConj
open scoped Matrix






private noncomputable def dPerp {k : Type} [Field k] {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule k (Fin a → k) :=
  W.dualAnnihilator.comap (dotProductEquiv k (Fin a)).toLinearMap













