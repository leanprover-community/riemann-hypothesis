module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneous
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

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.noether_normalization_homogeneous : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ → (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧ (∀ i, (y i).IsHomogeneous e) ∧ AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧ Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  first | exact @GlobalTheory.CompanionTheory.ConeNoether.main | exact GlobalTheory.CompanionTheory.ConeNoether.main | (intros; apply GlobalTheory.CompanionTheory.ConeNoether.main <;> assumption)
