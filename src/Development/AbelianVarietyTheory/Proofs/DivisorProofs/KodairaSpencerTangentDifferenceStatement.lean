module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.kodaira_spencer_tangent_difference : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  first | exact @GlobalTheory.FlagTan.eq_of_isKS_eq | exact GlobalTheory.FlagTan.eq_of_isKS_eq | (intros; apply GlobalTheory.FlagTan.eq_of_isKS_eq <;> assumption)
