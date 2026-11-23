module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  first | exact @GlobalTheory.CovInt.integral_smul_thLa | exact GlobalTheory.CovInt.integral_smul_thLa | (intros; apply GlobalTheory.CovInt.integral_smul_thLa <;> assumption)
