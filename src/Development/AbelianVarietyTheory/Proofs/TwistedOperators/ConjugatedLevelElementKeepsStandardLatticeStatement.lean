module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLattice
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  first | exact @GlobalTheory.RowVertexInv.moved_keeps_std | exact GlobalTheory.RowVertexInv.moved_keeps_std | (intros; apply GlobalTheory.RowVertexInv.moved_keeps_std <;> assumption)
