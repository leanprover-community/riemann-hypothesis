module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.SemistableModelSemistable
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CIn
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FinAllOf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiStepOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGeoSide
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace UpperTheory.Ru.crystallineComparison

theorem finAll : UpperTheory.Gal.crystallineComparison.Br.FinAll := finAll_of fun l _ K _ r f hf => cIn l K r f hf

theorem smoothModel_crystalline : CrystallineSemistableComparison.SmoothModelCrystalline := (CrystallineSemistableComparison.cstSmooth_of_side fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K).1

theorem phiStep : UpperTheory.Gal.Int.Geo.PhiStep := phiStep_of (UpperTheory.Gal.Int.Geo.geoSide_of finAll smoothModel_crystalline)

end UpperTheory.Ru.crystallineComparison
