module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodTorus_isTorusAt_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (T : I2.PT E) (ψ : (Fin Uw.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsTorusOf (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) (Uw.Pm k x) Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ (∀ th, T.ph th = I2.phiFD (U.X k) th x.1) ∧ ∀ m, (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ τ, T.dim τ ≤ m := by
  first | exact @GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | exact GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | (intros; apply GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf <;> assumption)
