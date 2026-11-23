module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimagStatement
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

namespace GlobalTheory.AbCoh

theorem isAffineOpen_preimage_of_isPullback (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X)
    (h : IsPullback φ s' s (spMap (algebraMap R R'))) (U : X.affineOpens) : IsAffineOpen (φ ⁻¹ᵁ U.1) := by
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact U.2.preimage φ

theorem exists_equiv_globForm_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R R' _ _ _ X X' s s' φ h hF hC hF' hC' hfl hsu
  have hb : Function.Bijective (liftSemi (pullForm h.w)) :=
    GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family R' _ _ (liftSemi (pullForm h.w)) X.affineOpens (fun U ↦ Sec s' (φ ⁻¹ᵁ U.1))
      (fun U ↦ GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme R' X' s' hfl ⟨_, isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U⟩)
      (GlobalTheory.T.exists_affineOpen_map_maximal_proper R' X X' s' φ hsu)
      (fun U ↦ GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective R R' X X' s s' φ h hF hC hF' hC' U
        (isAffineOpen_preimage_of_isPullback R R' X X' s s' φ h U))
  refine ⟨LinearEquiv.ofBijective _ hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, liftSemi_tmul, one_smul]

end GlobalTheory.AbCoh
