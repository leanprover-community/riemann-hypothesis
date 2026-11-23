module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRows
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | exact GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | (intros; apply GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange <;> assumption)
