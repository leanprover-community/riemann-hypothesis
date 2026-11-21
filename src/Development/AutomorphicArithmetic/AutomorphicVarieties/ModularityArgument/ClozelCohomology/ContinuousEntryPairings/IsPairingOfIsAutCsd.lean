import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive

section
namespace GlobalTheory.ConjAut

open UpperTheory.V UpperTheory.V.Af

structure Tools : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  descU : UpperTheory.V.Published.DescentUnitary
  sol : SolDescent
  galU : GalUnitary
  csdOf : CsdOf
  bridge : AutBridge
  algCyc : AlgOfCyc
  twi : Twi
  exC : ExC
  compat : CompatCsd
  iso : IsoOfFrob
  satFrob : SatFrob
  satLoc : SatLoc
  locC : LocCompC
  locFixed : LocFixed
  wdAway : WDAway
  satK : SatK
  levelK : LevelK
  pureK : PureK
  intK : IntK
  cardK : CardK
  levelP : UpperTheory.V.Br.LevelP
  pureP : UpperTheory.V.Br.PureP
  intP : UpperTheory.V.Br.IntP
  cardP : UpperTheory.V.Br.CardP

end GlobalTheory.ConjAut
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu UpperTheory.V.Published GlobalTheory.MonoConj
open scoped Matrix






private noncomputable def dPerp {k : Type} [Field k] {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule k (Fin a → k) :=
  W.dualAnnihilator.comap (dotProductEquiv k (Fin a)).toLinearMap
end
