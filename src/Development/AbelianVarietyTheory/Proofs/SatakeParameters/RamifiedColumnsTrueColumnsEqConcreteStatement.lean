module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  first | exact @GlobalTheory.AtG.ramCols_true | exact GlobalTheory.AtG.ramCols_true | (intros; apply GlobalTheory.AtG.ramCols_true <;> assumption)
