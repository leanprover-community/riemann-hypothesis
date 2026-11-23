module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbGenericFibre

theorem baseChange_normal_generic : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  intro S G _ hG R _ _ _ _ χ
  set K := FractionRing R
  set T : Over S := Over.mk χ
  set TK : Over S := Over.mk (spMap (algebraMap R K) ≫ χ)
  set h : TK ⟶ T := Over.homMk (spMap (algebraMap R K)) rfl
  have hpb : IsPullback (h ▷ G).left (CartesianMonoidalCategory.fst TK G).left
      (CartesianMonoidalCategory.fst T G).left (spMap (algebraMap R K)) :=
    GlobalTheory.ThetaRuleCompare.isPullback_whisker h
  have hsm : Smooth G.hom := hG.smooth
  have h1 : IsPullback (CartesianMonoidalCategory.snd T G).left (CartesianMonoidalCategory.fst T G).left G.hom T.hom :=
    (IsPullback.of_hasPullback T.hom G.hom).flip
  have hsf : Smooth (CartesianMonoidalCategory.fst T G).left := MorphismProperty.of_isPullback h1 hsm
  have : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp R))
  have : IsLocallyNoetherian (T ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (CartesianMonoidalCategory.fst T G).left
  have : GlobalTheory.IsNormalScheme T.left := (inferInstance : GlobalTheory.IsNormalScheme (Sp R))
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  refine ⟨inferInstance, GlobalTheory.isNormalScheme_of_smooth (CartesianMonoidalCategory.fst T G).left,
    MorphismProperty.of_isPullback hpb.flip ‹_›, fun W => ?_⟩
  have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have : QuasiCompact (spMap (algebraMap R K)) := by
    set_option backward.isDefEq.respectTransparency.types false in
      exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr (by infer_instance)
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant (h ▷ G).left :=
    IsSchemeTheoreticallyDominant.of_isPullback hpb.flip
  have : QuasiCompact (h ▷ G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  exact (h ▷ G).left.app_injective W

end GlobalTheory.SemiAbGenericFibre
