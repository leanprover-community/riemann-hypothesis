module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreAnnApply
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CycDense
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.GeneralizedVermaModulePolynomial
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.RhoSurj
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactFiniteAdelesAwayPBoundedDenominators
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsAdFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InNOfMem
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrthCycCycStable
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KsetSubset

@[expose] public section

namespace CompanionTheory.D.LK

theorem hGenCO : GenCO := genCO_of koszul_differential_sq_zero (cover2_of (acycAbs_of koszul_differential_sq_zero))

theorem hInj : Inj :=
  inj_of (vanK_of (cok_of hGenCO) GlobalTheory.CompanionTheory.LKWtProj.wtProj (GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of DSIC.hLowSpan)) GlobalTheory.CompanionTheory.LKWtProj.wtProj koszul_differential_sq_zero

theorem hMultAlg : MultAlg :=
  multAlg_of DSIC.hLowSpan DSIC.hHWMap GlobalTheory.CompanionTheory.LKDens.dens GlobalTheory.CompanionTheory.LKInvLift.invLift GlobalTheory.CompanionTheory.HCdecomp.hcdec hGenCO top_degree_cycle hInj

theorem hKModExists : KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs _root_.UpperTheory.Reformulated.B.Gc1.kFinStab DSIC.hStabLink DSIC.hHWofType
    DSIC.hTypeOfHW

theorem hOrthCyc : OrthCyc := GlobalTheory.CompanionTheory.LowKType.orthCyc

theorem low_K_type_multiplicity_one_unconditional : LowKMultOneP := lowKMultOneP_of hMultAlg hKModExists cyclic_vectors_dense _root_.GlobalTheory.CompanionTheory.LowKType.orthCyc

end CompanionTheory.D.LK
