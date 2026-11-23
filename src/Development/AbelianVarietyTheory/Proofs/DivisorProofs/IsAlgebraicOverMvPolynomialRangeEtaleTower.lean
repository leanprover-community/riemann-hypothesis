module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem isAlgebraic_range_eval₂Hom_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  intro K L _ _ cK cL r R T ι ψ τ h hinj z
  classical
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let φL : A →+* L := T.subtype.comp φ
  have hφL : Function.Injective φL := Subtype.val_injective.comp hinj

  letI : Algebra A T := φ.toAlgebra
  letI : Algebra A L := φL.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale A T := h.etale

  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.top.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI : Algebra.FormallyUnramified T L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L

  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by
    change cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))
    rw [MvPolynomial.eval₂Hom_C]
    exact (h.const a).symm
  haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType
  haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L

  let F := FractionRing A
  letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hφL a).symm
  haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L
  haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L
  have hA : IsAlgebraic A z :=
    (IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)

  obtain ⟨p, hp, hpz⟩ := hA
  refine ⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff
    (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hpz

end GlobalTheory.FieldPair
