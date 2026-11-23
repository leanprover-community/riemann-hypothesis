module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitary
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
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_approximating_elements_normalCover_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  first | exact @GlobalTheory.USep.exists_elements_cover | exact GlobalTheory.USep.exists_elements_cover | (intros; apply GlobalTheory.USep.exists_elements_cover <;> assumption)
