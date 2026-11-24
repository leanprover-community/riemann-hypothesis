module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLow
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

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  first | (exact @GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (exact GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (intros; apply GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow  <;> assumption)
