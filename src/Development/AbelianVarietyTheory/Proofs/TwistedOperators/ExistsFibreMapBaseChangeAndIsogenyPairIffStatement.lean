module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  first | exact @GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | exact GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | (intros; apply GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff <;> assumption)
