module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrime
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.standardFrames_match_completedLattices_at_prime : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.frames_match_lattices | exact GlobalTheory.LatMatch.frames_match_lattices | (intros; apply GlobalTheory.LatMatch.frames_match_lattices <;> assumption)
