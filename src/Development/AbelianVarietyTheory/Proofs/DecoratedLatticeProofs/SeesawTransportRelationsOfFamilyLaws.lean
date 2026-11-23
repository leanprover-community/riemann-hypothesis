module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RapidVal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
