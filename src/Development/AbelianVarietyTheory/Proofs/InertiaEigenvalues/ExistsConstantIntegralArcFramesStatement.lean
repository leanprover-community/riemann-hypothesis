module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFrames
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.exists_constant_integral_arc_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  first | exact @GlobalTheory.ArcFrame.exists_arcFrame | exact GlobalTheory.ArcFrame.exists_arcFrame | (intros; apply GlobalTheory.ArcFrame.exists_arcFrame <;> assumption)
