module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.WeilBound.CoreStatements.HodgeTatePoints.WeilfunCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Weilfun

theorem weil_fun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (n : ℕ), 1 ≤ n → ∃ (w : ∀ (T : Over S) (x z : T ⟶ t.G), x ^ n = 1 → z ^ n = 1 → Γ(T.left, ⊤)ˣ), (∀ (T T' : Over S) (f : T' ⟶ T) (x z : T ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (hx' : (f ≫ x) ^ n = 1) (hz' : (f ≫ z) ^ n = 1), (w T' (f ≫ x) (f ≫ z) hx' hz' : Γ(T'.left, ⊤)) = f.left.appTop.hom (w T x z hx hz)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S), IsProper (Limits.pullback.snd t.G.hom g) → ∀ (x z : Over.mk g ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (c : kˣ), Out.WeilIs t.G t.PP.L n x z (unitOn c) → w (Over.mk g) x z hx hz = unitOn c := by
  intro E _ _ _ H S _ t n _
  refine ⟨fun T x z hx hz => weilUnit t.cub n T x z hx hz, ?_, ?_⟩
  · intro T T' f x z hx hz hx' hz'
    exact weilUnit_comp t.cub n f hx hz hx' hz'
  · intro k _ _ g _ x z hx hz c hw
    haveI : Subsingleton ↥(Over.mk g).left := by
      show Subsingleton (PrimeSpectrum k)
      infer_instance
    exact weilUnit_eq_of_weilIs t.cub n hx hz _ hw

end PositivityTheory.HtPt.Weilfun
