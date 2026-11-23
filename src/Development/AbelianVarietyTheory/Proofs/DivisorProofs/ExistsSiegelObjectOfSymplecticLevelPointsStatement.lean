module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPoints
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  first | exact @GlobalTheory.SiegelLevelPull.exists_siegPre_of_points | exact GlobalTheory.SiegelLevelPull.exists_siegPre_of_points | (intros; apply GlobalTheory.SiegelLevelPull.exists_siegPre_of_points <;> assumption)
