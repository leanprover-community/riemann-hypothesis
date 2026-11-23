module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.HasFields

theorem cdv_powerSeries (k : Type) [Field k] [CharZero k] : CDV (PowerSeries k) := by
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have h0 : CharZero (PowerSeries k) := algebraRat.charZero _
  exact (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, h0⟩

theorem exists_lift (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic R K] [Field L] [IsAlgClosed L] (ψ : R →+* L)
    (hψ : Function.Injective ψ) : ∃ e : K →+* L, ∀ x, e (algebraMap R K x) = ψ x := by
  letI : Algebra R L := ψ.toAlgebra
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 hψ
  let e : K →ₐ[R] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨e, fun x => e.commutes x⟩

theorem exists_cdv_over_powerSeries : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : PowerSeries O' →+* W) (K₁ : Type) (_ : Field K₁) (_ : Algebra (FractionRing W) K₁) (_ : Algebra.IsAlgebraic (FractionRing W) K₁) (e : K →+* K₁), CDV W ∧ φ PowerSeries.X ∈ IsLocalRing.maximalIdeal W ∧ ∀ x, e (algebraMap (PowerSeries O') K x) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x)) := by
  intro O' _ _ _ K _ _ _ _
  let F := FractionRing O'
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing O'
  let W := PowerSeries F
  let φ : PowerSeries O' →+* W := PowerSeries.map (algebraMap O' F)
  have hφ : Function.Injective φ :=
    PowerSeries.map_injective _ (IsFractionRing.injective O' F)
  let K₁ := AlgebraicClosure (FractionRing W)
  let ψ : PowerSeries O' →+* K₁ :=
    (algebraMap (FractionRing W) K₁).comp ((algebraMap W (FractionRing W)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing W) K₁).injective.comp
      ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  have key : ∃ e : K →+* K₁, ∀ x, e (algebraMap (PowerSeries O') K x) = ψ x :=
    exists_lift _ K K₁ ψ hψ
  obtain ⟨e, he⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, φ, K₁, inferInstance, inferInstance,
    inferInstance, e, cdv_powerSeries F, ?_, he⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  rw [hX]
  exact Ideal.subset_span rfl

end GlobalTheory.HasFields
