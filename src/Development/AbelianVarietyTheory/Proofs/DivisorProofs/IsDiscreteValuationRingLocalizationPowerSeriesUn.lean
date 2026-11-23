module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser
