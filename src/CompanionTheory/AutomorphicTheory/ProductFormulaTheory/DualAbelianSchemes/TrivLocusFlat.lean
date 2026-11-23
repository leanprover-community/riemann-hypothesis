module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.AbelianDeRham.FreeAbelianDeRham.H1StructureDimLe
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.AddAcyclic
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.FewEqBridge
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.PointSurj
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocus
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplexStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPointOfIsAffine
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsIsoOfClosedImmersion
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KTrivModelOfTrivLocus
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PreDualOfIsPerfect
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpecMapAppFromSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem h1Le : H1StructureDimLe := MainStatements.Hodge.Free.h1Le

theorem trivLocus : TrivLocus := trivLocus_pf

theorem fewEquations : FewEquations := fewEquations_pf h1Le

theorem ciFlat : CIFlat := GlobalTheory.T.CechFlatComplex

theorem trivLocusFlat : TrivLocusFlat := @GlobalTheory.CompanionTheory.TrivFlat.trivLocusFlat fewEquations ciFlat

theorem pointSurj : PointSurj := pointSurj_pf addAcyclic_pf

theorem finDual : FinDual := @GlobalTheory.CompanionTheory.DualAb.finDual_of_univNoeth (@GlobalTheory.CompanionTheory.DualUniv.univNoeth trivLocus trivLocusFlat pointSurj)

theorem kTrivModel : KTrivModel := @GlobalTheory.CompanionTheory.KTrivSpread.kTrivModel_of_trivLocus trivLocus

theorem kTrivDual : KTrivDual := @GlobalTheory.CompanionTheory.DualScheme.ktrivDual kTrivModel finDual

end CompanionTheory.PfDual
