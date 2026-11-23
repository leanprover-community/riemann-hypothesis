module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ComposeLinearAction
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbert
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  first | exact @GlobalTheory.AnValEL.eL_appellHumbert | exact GlobalTheory.AnValEL.eL_appellHumbert | (intros; apply GlobalTheory.AnValEL.eL_appellHumbert <;> assumption)
