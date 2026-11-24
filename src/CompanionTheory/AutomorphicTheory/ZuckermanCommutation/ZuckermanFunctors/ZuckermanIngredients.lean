module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSumStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLawsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTraceStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormulaStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadraticStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegralityStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategoryStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHomStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2Statement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferentialStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplexStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIsoStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesisStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps := by
  exact {
    infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
    decOfInj := decomposition_of_injective
    decOfTrace := GlobalTheory.T.DecompositionOfTrace
    homCat := GlobalTheory.T.HomCategory
    okTriv := trivial_rep_admissible
    okVr := vector_rep_admissible
    okWedge := GlobalTheory.T.ExteriorPowerIntegral
    okTens := GlobalTheory.T.TensorPowerIntegral
    matHom := GlobalTheory.T.MatrixHom
    uIso := GlobalTheory.T.UnitaryIso
    homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
    casSplit := GlobalTheory.T.CasimirSplitting
    casDS := GlobalTheory.T.CasimirDiagonalSum
    wedgeInt := GlobalTheory.T.ExteriorIntegrality
    wedgeQ := GlobalTheory.T.exterior_differential_sign_rule_quadratic GlobalTheory.T.StandardDifferential GlobalTheory.T.exterior_differential_matrix_unit_formula
    schur := CompanionTheory.D.gk.FinalFormK.schur'
    adj := adj_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom'
    multOne := multOne_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting GlobalTheory.T.StandardDifferential
      CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible GlobalTheory.T.TensorPowerIntegral
    inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
    occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
    zuckH := GlobalTheory.T.zuckerman_hypothesis
    decTens := GlobalTheory.T.decomposition_of_tensor_from_hom_laws GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
    toRaw := GlobalTheory.T.ToRawComplex
    count := GlobalTheory.T.CountingBound
  }

end CompanionTheory.Zuck
