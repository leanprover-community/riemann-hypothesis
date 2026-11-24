module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
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

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.bundle_degree_eq_sum_valuations : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ) (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L → (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧ deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula <;> assumption)
