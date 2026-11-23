module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPoint
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

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_algHom_quotient_pow_lifting_point : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ g : C →+* A, g.comp (algebraMap R C) = ρ →
    ∀ n : ℕ, ∃ f : C →ₐ[R] R ⧸ Ideal.span {t} ^ n, ∀ c : C,
      f c - Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c)) ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  first | (exact @GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (exact GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (intros; apply GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow <;> assumption)
