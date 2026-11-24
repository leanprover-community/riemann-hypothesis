module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

theorem _root_.GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian → ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧ Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  first | exact @GlobalTheory.HSAmp.simultaneous_diagonalisation | exact GlobalTheory.HSAmp.simultaneous_diagonalisation | (intros; apply GlobalTheory.HSAmp.simultaneous_diagonalisation <;> assumption)
