module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := GlobalTheory.T.coeffHeckeUOperator_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
