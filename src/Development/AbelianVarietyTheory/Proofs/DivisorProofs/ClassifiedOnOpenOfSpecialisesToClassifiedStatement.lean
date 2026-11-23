module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.classified_on_open_of_specialises_to_classified : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  first | exact @GlobalTheory.clsOpen | exact GlobalTheory.clsOpen | (intros; apply GlobalTheory.clsOpen <;> assumption)
