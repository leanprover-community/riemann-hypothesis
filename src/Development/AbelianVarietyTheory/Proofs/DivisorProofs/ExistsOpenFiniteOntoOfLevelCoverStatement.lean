module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCover
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_open_finite_onto_of_levelCover : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  first | exact @GlobalTheory.SiegTh.exists_openAt_of_levAt | exact GlobalTheory.SiegTh.exists_openAt_of_levAt | (intros; apply GlobalTheory.SiegTh.exists_openAt_of_levAt <;> assumption)
