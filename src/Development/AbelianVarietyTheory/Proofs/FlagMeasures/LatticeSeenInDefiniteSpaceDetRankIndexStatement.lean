module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSeenInDefiniteSpaceDetRankIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeSeenInDefiniteSpace_det_rank_index : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  first | exact @GlobalTheory.LoopC.SeenIso.main | exact GlobalTheory.LoopC.SeenIso.main | (intros; apply GlobalTheory.LoopC.SeenIso.main <;> assumption)
