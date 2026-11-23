module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.degenerationData_eighthPower_via_characterMaps : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_characters | exact GlobalTheory.Mum.PowData.sharpRef_of_characters | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_characters <;> assumption)
