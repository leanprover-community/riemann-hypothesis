module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicAlgebraHilbertNinety
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.cyclic_algebra_hilbert_ninety : PositivityTheory.Rg.Tf.Loc.N1 → ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'), 0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) → (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) → (∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) → ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ, (∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R)) - (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (r : R) ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.FirstApprox.main | exact GlobalTheory.CompanionTheory.FirstApprox.main | (intros; apply GlobalTheory.CompanionTheory.FirstApprox.main <;> assumption)
