module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquiv
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

theorem _root_.GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  first | (exact @GlobalTheory.EZ.awHomotopyEquiv) | (exact GlobalTheory.EZ.awHomotopyEquiv) | (intros; apply GlobalTheory.EZ.awHomotopyEquiv  <;> assumption)
