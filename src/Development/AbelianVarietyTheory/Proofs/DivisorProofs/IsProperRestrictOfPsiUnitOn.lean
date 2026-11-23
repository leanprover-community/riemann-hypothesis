module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.PowerSeries.Inverse
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.UnifProperChar
section Inertia

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Inertia

section Reduction

open GlobalTheory.Published GlobalTheory.Published.AbVarRed

end Reduction

theorem exists_dvr_centre (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAlgClosed (ResidueField V) ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
  obtain ⟨V, _, _, _, φ, hφ, hc⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : R →+* V), Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · let K := FractionRing R
      let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
      have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
      refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ, hφ, ?_⟩
      refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
    · obtain ⟨V, _, _, hV, -, φ, h1, h2⟩ :=
        exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
      exact ⟨V, inferInstance, inferInstance, hV, φ, (RingHom.injective_iff_ker_eq_bot φ).2 h1, h2⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨V', _, _, _, _, h1, h2, -, h3⟩ := GlobalTheory.ClosedResidueExt.exists_unramified_ext V hπ
  refine ⟨V', inferInstance, inferInstance, inferInstance, (algebraMap V V').comp φ, h3, h1.comp hφ, ?_⟩
  rw [← Ideal.comap_comap, ← hc]
  congr 1
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (algebraMap_isIntegral_iff.mpr h2) (maximalIdeal V'))

end GlobalTheory.UnifProperChar
