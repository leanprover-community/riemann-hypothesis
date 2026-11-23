module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem _root_.GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  first | exact @GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | exact GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | (intros; apply GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves <;> assumption)
