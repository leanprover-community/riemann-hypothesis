module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dual_family_is_basis : ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ) (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V), IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) → LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | exact GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | (intros; apply GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit <;> assumption)
