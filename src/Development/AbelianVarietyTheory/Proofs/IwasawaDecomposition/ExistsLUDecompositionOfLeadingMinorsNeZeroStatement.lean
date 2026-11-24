module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero : ∀ {n : ℕ} (B : GL (Fin n) ℂ), (∀ (k : ℕ) (hk : k ≤ n), (B.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → ∃ L U : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual ∧ U.val.BlockTriangular id ∧ B = L * U := by
  first | exact @GlobalTheory.LUDecomp.lu | exact GlobalTheory.LUDecomp.lu | (intros; apply GlobalTheory.LUDecomp.lu <;> assumption)
