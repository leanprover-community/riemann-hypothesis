module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetChangeOfBasis
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.gram_det_change_of_basis : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (n : ℕ)
    (β : Fin (n + 1) → V) (x : Fin n → V) (xe : V) (C : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (s : ℂ),
    (∀ j, x j = ∑ l, C j l • β l.castSucc) → xe = ∑ l, d l • β l.castSucc + s • β (Fin.last n) → s ≠ 0 →
    (Matrix.of fun a b => core.inner (x a) (x b)).det ≠ 0 → (Matrix.of fun a b => core.inner (β a) (β b)).det ≠ 0 →
    (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner ((Fin.snoc x xe : Fin (n + 1) → V) a)
        ((Fin.snoc x xe : Fin (n + 1) → V) b)).det‖ - Real.log ‖(Matrix.of fun a b => core.inner (x a) (x b)).det‖) =
      Real.log ‖s‖ + (1 / 2) * (Real.log ‖(Matrix.of fun a b => core.inner (β a) (β b)).det‖ -
        Real.log ‖(Matrix.of fun a b : Fin n => core.inner (β a.castSucc) (β b.castSucc)).det‖) := by
  exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot
