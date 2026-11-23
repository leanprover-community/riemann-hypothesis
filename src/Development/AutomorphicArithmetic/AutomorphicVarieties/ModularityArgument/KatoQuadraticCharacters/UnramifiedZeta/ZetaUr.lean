module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishingStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.KatoGlobalUnitLawOfSmoothedClasses
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SmoothedZetaClasses.SmoothedZetaClassHodgeTateLaw
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormFactorLeOne
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.AdmissibleWeightedDataMonoCoef
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaElementsUnramifiedOrdinaryOfEulerSystemInert

@[expose] public section

namespace UpperTheory.V.Z.Kato.Final

theorem zetaUr : GlobalTheory.Ord2.ZetaUr := GlobalTheory.KZ.zetaUr_of_halves2 _
  (UpperTheory.V.Z.Kato.Joint.kato_global_unit_law_of_smoothed_classes UpperTheory.Kd.K4.kato_eulerSystem_integrality UpperTheory.V.Z.Kato.K5.smoothedZetaClass_hodgeTateLaw
    (fun {Ω} _ _ _ => GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing))
  UpperTheory.Kd.C7.pLocu

end UpperTheory.V.Z.Kato.Final
