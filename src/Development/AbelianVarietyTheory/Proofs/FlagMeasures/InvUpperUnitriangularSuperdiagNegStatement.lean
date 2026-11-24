module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUpperUnitriangularSuperdiagNeg
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inv_upperUnitriangular_superdiag_neg : ∀ (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, y < x → A x y = 0) → (∀ x, A x x = 1) → (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧ ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  first | exact @GlobalTheory.inv_upperUnitriangular | exact GlobalTheory.inv_upperUnitriangular | (intros; apply GlobalTheory.inv_upperUnitriangular <;> assumption)
