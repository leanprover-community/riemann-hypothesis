module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.autInst_degree_rootDiscriminant_rank : ∀ I : AutInst, Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, HasSig I p q → p + q = I.n := by
  first | exact @GlobalTheory.FlagMeas.instance_numbers | exact GlobalTheory.FlagMeas.instance_numbers | (intros; apply GlobalTheory.FlagMeas.instance_numbers <;> assumption)
