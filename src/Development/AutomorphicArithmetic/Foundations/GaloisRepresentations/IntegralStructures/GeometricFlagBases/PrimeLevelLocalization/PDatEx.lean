module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.ExistsAuxiliaryPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.MemIffDvd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBarAdj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCjMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDiscInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSides
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

@[expose] public section

open UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1

namespace UpperTheory.Gal.Int.Geo.Pl

theorem datEx_holds : DatEx := datEx_of exists_auxiliary_prime ArithK_holds SetupEx_holds ScOf_holds PerfCof_holds

theorem sides_holds : Sides := pSides pCjMem (pBarAdj pDiscInt) (pKeyK pDiscInt) RootAt_holds

end UpperTheory.Gal.Int.Geo.Pl
