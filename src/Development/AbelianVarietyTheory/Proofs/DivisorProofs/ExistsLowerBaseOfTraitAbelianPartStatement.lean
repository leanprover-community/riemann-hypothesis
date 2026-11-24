module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lower_base_of_trait_abelian_part : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.TChart.exists_lowBase_of_trait | exact GlobalTheory.TChart.exists_lowBase_of_trait | (intros; apply GlobalTheory.TChart.exists_lowBase_of_trait <;> assumption)
