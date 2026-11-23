module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlowupChartIdealSheafEqSpanMonomial
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.blowup_chart_idealSheaf_eq_span_monomial : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∃ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) ∧ idlAlong (J.comap π) ξ = Ideal.span {∏ k, t k ^ b k} := by
  first | exact @GlobalTheory.SgZero.idlAlong_eq_span_monomial | exact GlobalTheory.SgZero.idlAlong_eq_span_monomial | (intros; apply GlobalTheory.SgZero.idlAlong_eq_span_monomial <;> assumption)
