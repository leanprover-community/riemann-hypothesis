module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOneOfSteps
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdm
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DDForm
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.BeBesselOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.SchurH
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.Lime.BM

open Formalism.FourierDecayAlt.P CompanionTheory.D.Upq

theorem shape (hU : UniqGap) : Shape := by
  exact shape_of hU PI.WBL.S5.psiConst PI.WBL.NIS.schurH BesselFunctionalConstruction.beConv BesselFunctionalConstruction.normIdSm BesselFunctionalConstruction.beBessel

theorem dDFormOne (hU : UniqGap) : DDFormOne := by
  exact Formalism.FourierDecayAlt.P.DDSmoothness.BM.discrete_form_one_side PI.WBL.S5.psiConst PI.WBL.NIS.schurH
    Formalism.FourierDecayAlt.P.norm_inverse_bound Formalism.FourierDecayAlt.P.growth_spherical_bound Formalism.FourierDecayAlt.P.growth_group_bound BesselFunctionalConstruction.decDD BesselFunctionalConstruction.beConv
    BesselFunctionalConstruction.normIdSm BesselFunctionalConstruction.beBessel (shape hU)

theorem atFormAdmOne (hU : UniqGap) : AtFormAdmOne := by
  exact Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.BM.smooth_admissible_form_one_side PI.WBL.NIS.schurH BesselFunctionalConstruction.beConv BesselFunctionalConstruction.normIdSm
    BesselFunctionalConstruction.beBessel (shape hU) BesselFunctionalConstruction.kFinForm BesselFunctionalConstruction.zeroCase BesselFunctionalConstruction.zeroCaseDD

end CompanionTheory.Lime.BM
