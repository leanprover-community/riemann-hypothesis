module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
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

theorem _root_.GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (y z : FrPt Xo c K) (y' z' : FrPt Xo c L) (f : Fib Xo y.x ⟶ Fib Xo z.x) (f' : Fib Xo z.x ⟶ Fib Xo y.x) (g : Fib Xo y'.x ⟶ Fib Xo z'.x) (p : ℕ), 0 < p → FrMap φ y y' → FrMap φ z z' → IsPair (p ^ 2) f f' → IsBC φ.toRingHom f g → AllRat Xo y.x (p ^ 2) → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) ((p : ℤ) ^ 2) β) → (IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s ↔ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y'.x z'.x g.left) p y'.s z'.s) := by
  first | exact @GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | exact GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff | (intros; apply GlobalTheory.ThetaTraceBC.isThetaTrace_baseChange_iff <;> assumption)
