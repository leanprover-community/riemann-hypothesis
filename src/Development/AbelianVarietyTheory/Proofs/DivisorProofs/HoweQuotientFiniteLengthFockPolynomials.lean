module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommuteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvariStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  obtain ⟨hStab, hAdm⟩ := GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants P Q R S x
  refine ⟨⟨hLie, hWt, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne P Q R S x⟩

end GlobalTheory.HoweR
