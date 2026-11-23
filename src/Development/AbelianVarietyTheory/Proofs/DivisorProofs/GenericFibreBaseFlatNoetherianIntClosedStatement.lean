module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseFlatNoetherianIntClosed
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

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    Module.Flat A (Localization.AtPrime QA) ∧ IsNoetherianRing (Localization.AtPrime QA) ∧
      algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X ∈ nonZeroDivisors (Localization.AtPrime QA) ∧
      ∀ f : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA), IsIntegral (Localization.AtPrime QA) f →
        ∃ r : Localization.AtPrime QA, algebraMap _ (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) r = f := by
  first | (exact @GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (exact GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed) | (intros; apply GlobalTheory.GoodEtaleBase.flat_noetherian_nzd_intClosed  <;> assumption)
