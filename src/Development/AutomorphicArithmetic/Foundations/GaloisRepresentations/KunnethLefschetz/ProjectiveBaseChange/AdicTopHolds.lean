module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateSurjectivePositiveDim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PCupEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PDualSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PGeomPb
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PIntFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PProjBC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumBC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumCl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumHl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PiBCHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PullbackComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CrystallineSemistableComparison

namespace UpperTheory.Gal.KunnethLefschetz

theorem adicTop_holds : AdicTop :=
  adicTop_of ringL_holds projBC_holds sumCl_holds sumBC_holds geomPb_holds sumHl_holds piBC_holds dualSum_holds perm_holds
    intFun_holds cupEx_holds

theorem etSide_sm (hI : In) (hQ : QDual) (hS : InSum) (hC : ModelComponents) (hG : GeometricGenericComponents) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] : EtSide (Model.Sm (l := l) (K := K)) :=
  adicTop_holds hI hQ hS l K _ (fun _ h => h.1) (hC l K).1 fun M h d hd => hG l K M h.1 d hd

theorem etFin_of (hI : In) (hQ : QDual) (hS : InSum) (hC : ModelComponents) (hG : GeometricGenericComponents) : CrystallineSemistableComparison.Onto.EtFin :=
  fun l _ K _ M hM n => (etSide_sm hI hQ hS hC hG l K).fin M hM n

end UpperTheory.Gal.KunnethLefschetz
