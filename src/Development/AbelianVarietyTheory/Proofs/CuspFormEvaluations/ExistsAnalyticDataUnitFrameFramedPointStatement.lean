module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_analyticData_unitFrame_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  first | exact @GlobalTheory.Dict.VSetup.exists_setup | exact GlobalTheory.Dict.VSetup.exists_setup | (intros; apply GlobalTheory.Dict.VSetup.exists_setup <;> assumption)
