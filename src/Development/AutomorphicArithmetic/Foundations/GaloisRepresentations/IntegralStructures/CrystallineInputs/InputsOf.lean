module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.OfInputs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.Crys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.FirstQuadraticSquareHolds
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
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

namespace UpperTheory.Gal.Int.Inp

theorem js : GlobalTheory.Published.JacquetShalikaRigidity := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
theorem gk : GlobalTheory.Published.GelfandKazhdanDual := UpperTheory.Gal.AbelianGaloisNormality.gk_holds
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := UpperTheory.Zero.LLC.Pr.adm
theorem len : GlobalTheory.Published.StandardFunctorsFiniteLength := PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := UpperTheory.Zero.LLC.Pr.exh
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing := UpperTheory.Zero.LLC.Pr.zel
theorem gen : GlobalTheory.Published.GenericUnitaryDualGL := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds
theorem ac : GlobalTheory.Published.ArthurClozelStrongTC := UpperTheory.Gal.AbelianGaloisNormality.strongTC_holds

theorem inp_holds : Inp := ⟨js, gk, adm, len, exh, zel, gen, ac, hk, alg, pst⟩

end UpperTheory.Gal.Int.Inp
