module

public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.normalisedPullback_section_expands_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (α : 𝓞 E) (N k q : ℕ) (e : k * N = q), α * star α = (N : 𝓞 E) → 0 < N → (k = 1 ∨ 4 ≤ k) → ∀ (σ : P.U.toUnifPre.SecGF F k) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo xF))) (θ : Fam P.D.toPre F k) (σ₁ : P.U.toUnifPre.SecGF F q) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (θα : Fam P.D.toPre F (k * N)), SecTieF I P F xF k σ s → P.U.toUnifPre.ExpandsG F k σ θ → IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) (q : ℤ) (k : ℤ) s s₁ → SecTieF I P F xF q σ₁ s₁ → PullAl P.D F P.oD α k N θ θα → P.U.toUnifPre.ExpandsG F q σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) e θα) := by
  first | exact @GlobalTheory.NormPullExp.main | exact GlobalTheory.NormPullExp.main | (intros; apply GlobalTheory.NormPullExp.main <;> assumption)
