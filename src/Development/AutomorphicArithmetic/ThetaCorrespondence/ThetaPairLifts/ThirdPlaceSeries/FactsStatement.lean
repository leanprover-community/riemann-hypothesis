module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Facts
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.isChoice_of_start_of_over : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  first | exact @_root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | exact _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FirstFacts.facts_alt <;> assumption)
end
