module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Coprime.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonal
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.matrix_induction_transvection_diagonal : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | exact GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | (intros; apply GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction <;> assumption)
