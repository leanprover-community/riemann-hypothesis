module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
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

theorem _root_.GlobalTheory.T.lowerTriangular_GL_complex_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) → (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) → (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) → ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  first | exact @GlobalTheory.lowerTriangular_GL_induction | exact GlobalTheory.lowerTriangular_GL_induction | (intros; apply GlobalTheory.lowerTriangular_GL_induction <;> assumption)
