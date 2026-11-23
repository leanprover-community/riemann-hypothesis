module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
