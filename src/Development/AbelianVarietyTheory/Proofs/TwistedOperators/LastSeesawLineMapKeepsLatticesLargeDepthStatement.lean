module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLineMapKeepsLatticesLargeDepth
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastSeesawLineMap_keeps_lattices_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  first | exact @GlobalTheory.LastLineLat.kap_lastTau_latO | exact GlobalTheory.LastLineLat.kap_lastTau_latO | (intros; apply GlobalTheory.LastLineLat.kap_lastTau_latO <;> assumption)
