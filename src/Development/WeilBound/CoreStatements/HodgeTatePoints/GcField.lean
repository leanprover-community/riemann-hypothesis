module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gc

theorem test_field : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 := by
  intro A _ _ _ _ _ p hp q hq h1 hpq
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R),
      IsLocalization.AtPrime R q ∧ IsDiscreteValuationRing R :=
    ⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance,
      dvr_of_height_one q h1⟩
  let K := FractionRing R
  have hAR : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R q.primeCompl_le_nonZeroDivisors
  haveI : CharZero R := charZero_of_injective_algebraMap hAR
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff R q (p : A)).2 hpq
    rwa [map_natCast] at this
  obtain ⟨C, _, _, _, _, _, _, hC⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing R K p hpR
  obtain ⟨φ, hφ, hφ'⟩ := GlobalTheory.exists_isLocalHom_normIntegers hC
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hO := GlobalTheory.normIntegers_integers C
  have key : ∀ a : A, a ∈ q ↔
      NormedField.valuation (K := C) (algebraMap (GlobalTheory.normIntegers C) C (φ (algebraMap A R a))) < 1 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R q a, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, ← isUnit_map_iff φ, hO.isUnit_iff_valuation_eq_one]
    exact (hO.map_le_one _).lt_iff_ne.symm
  have hv : NormedField.valuation (K := C) (p : C) < 1 := by
    simpa only [map_natCast] using (key p).1 hpq
  refine ⟨C, GlobalTheory.normIntegers C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, NormedField.valuation, φ.comp (algebraMap A R), hO, hv, ?_, ?_, key⟩
  · apply GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO
    exact_mod_cast hv
  · intro a b hab
    have : (φ (algebraMap A R a) : C) = (φ (algebraMap A R b) : C) := congrArg Subtype.val hab
    rw [hφ', hφ'] at this
    exact hAR (IsFractionRing.injective R K ((algebraMap K C).injective this))

end PositivityTheory.HtPt.Gc
