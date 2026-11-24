module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndepStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesianStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTestsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestCartOfSpecialFibreSurjectiveStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep C hI
  have hS := GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests C hT hF
  have hC : C.TestCart := GlobalTheory.T.testCart_of_specialFibre_surjective C hF hS
  have hL : C.FibLaw := GlobalTheory.T.fibreLaw_of_testCartesian C hC
  exact GlobalTheory.T.nonempty_law_abelianSchemeProperClosure C hS hC (GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw C hT hS hC hL) (GlobalTheory.T.exists_inverse_extension_properClosure C hT hS hC hL)

end GlobalTheory.ZJ
