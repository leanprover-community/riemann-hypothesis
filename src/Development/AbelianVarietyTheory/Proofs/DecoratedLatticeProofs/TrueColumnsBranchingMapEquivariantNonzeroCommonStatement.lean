module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
