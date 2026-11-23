module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisation
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_local_thetaConstants_localisation : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  first | exact @GlobalTheory.UMin.ThLocal.exists_local | exact GlobalTheory.UMin.ThLocal.exists_local | (intros; apply GlobalTheory.UMin.ThLocal.exists_local <;> assumption)
