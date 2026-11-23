module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistenceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniquenessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistenceStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.RgBcC

theorem wave_existence_speed_multiplicity : WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg := by
  have hL : LgFacts := GlobalTheory.T.length_function_facts_hold
  have hU : Unimod := GlobalTheory.T.general_linear_group_unimodular
  have hS : SobG := GlobalTheory.T.sobolev_inequality_on_group
  have hR : RCalc := GlobalTheory.T.right_derivative_calculus_holds
  have hKU : KerUniq := GlobalTheory.T.wave_kernel_uniqueness
  have hA : AlgEst := GlobalTheory.T.algebra_estimate_for_regularity
  have hsp : WaveSpeed := GlobalTheory.T.finite_propagation_speed_holds hL hU hR
  have hcpt : WaveCpt := Fc.asmCpt hL hU hR hS
  have hex : WaveEx := GlobalTheory.T.wave_solution_existence hL hR hsp hcpt
  have hk1 : KerOne := Fc.asmKerOne hL hU hR hS hA hsp
  exact ⟨hex, hsp, GlobalTheory.T.wave_kernel_existence hL hR hsp hex hKU hk1,
    GlobalTheory.CompanionTheory.WaveMult.asmMult_main hL hU hR hsp hex hKU hk1⟩

end PositivityTheory.RgBcC
