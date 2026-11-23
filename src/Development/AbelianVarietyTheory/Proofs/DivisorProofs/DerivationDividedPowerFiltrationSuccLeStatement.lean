module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDividedPowerFiltrationSuccLe
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

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.derivation_dividedPowerFiltration_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M) (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) → ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  first | exact @GlobalTheory.DerFil.deriv_fil_succ_le | exact GlobalTheory.DerFil.deriv_fil_succ_le | (intros; apply GlobalTheory.DerFil.deriv_fil_succ_le <;> assumption)
