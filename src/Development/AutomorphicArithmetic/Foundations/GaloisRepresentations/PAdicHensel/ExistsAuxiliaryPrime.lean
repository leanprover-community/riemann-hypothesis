module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PArithK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAuxPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRootAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

theorem exists_auxiliary_prime : AuxiliaryInertOddPrime := exists_auxiliary_prime_cmDatum
theorem ArithK_holds : ArithK := pArithK BarEx_holds QuadEx_holds CEx_holds UnitMod_holds CodiffGen_holds CodiffUnit_holds IdemEx_holds RealGen_holds PosGen_holds DeltaEx_holds PerfOf_holds
theorem ScOf_holds : ScOf := pScOf SetupBasic_holds
theorem RootAt_holds : RootAt := pRootAt

end UpperTheory.Gal.G1
