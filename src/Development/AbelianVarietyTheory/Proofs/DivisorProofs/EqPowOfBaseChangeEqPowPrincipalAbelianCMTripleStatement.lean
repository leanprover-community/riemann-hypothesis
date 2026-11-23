module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.eq_pow_of_baseChange_eq_pow_principalAbelianCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  first | exact @GlobalTheory.eq_pow_of_baseChange_eq_pow | exact GlobalTheory.eq_pow_of_baseChange_eq_pow | (intros; apply GlobalTheory.eq_pow_of_baseChange_eq_pow <;> assumption)
