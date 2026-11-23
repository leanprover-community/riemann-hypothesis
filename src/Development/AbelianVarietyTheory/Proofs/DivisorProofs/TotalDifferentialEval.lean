module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialDoubleComplexDifferentials
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

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.total_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  first | (exact @GlobalTheory.EZ.ιTotal_tot_d) | (exact GlobalTheory.EZ.ιTotal_tot_d) | (intros; apply GlobalTheory.EZ.ιTotal_tot_d <;> assumption)
