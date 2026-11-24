module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalProperties
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_basis_matrix_orthogonal_properties : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  first | exact @GlobalTheory.FockBasisMatrix.basis_matrix
