module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  first | exact @GlobalTheory.USepCov.exists_cover | exact GlobalTheory.USepCov.exists_cover | (intros; apply GlobalTheory.USepCov.exists_cover <;> assumption)
