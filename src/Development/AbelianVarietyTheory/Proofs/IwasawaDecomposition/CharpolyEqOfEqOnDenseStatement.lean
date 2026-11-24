module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
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
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  first | exact @GlobalTheory.charpoly_eq_of_eqOn_dense | exact GlobalTheory.charpoly_eq_of_eqOn_dense | (intros; apply GlobalTheory.charpoly_eq_of_eqOn_dense <;> assumption)
