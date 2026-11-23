module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuadraticCharactersInAdjoint
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.finite_quadratic_characters_in_adjoint' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k), Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  first | exact @GlobalTheory.finite_quadratic_characters_in_adjoint | exact GlobalTheory.finite_quadratic_characters_in_adjoint | (intros; apply GlobalTheory.finite_quadratic_characters_in_adjoint <;> assumption)
