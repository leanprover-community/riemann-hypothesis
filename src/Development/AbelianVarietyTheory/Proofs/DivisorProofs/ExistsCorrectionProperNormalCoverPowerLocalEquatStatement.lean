module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquat
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  first | exact @GlobalTheory.CorrCover.exists_corr | exact GlobalTheory.CorrCover.exists_corr | (intros; apply GlobalTheory.CorrCover.exists_corr <;> assumption)
