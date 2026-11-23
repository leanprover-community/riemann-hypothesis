module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
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
public import Mathlib.RingTheory.Trace.Quotient
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
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x]
  simp

end GlobalTheory
