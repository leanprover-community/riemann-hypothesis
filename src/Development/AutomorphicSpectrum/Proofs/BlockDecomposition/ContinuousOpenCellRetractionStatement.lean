module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOpenCellRetraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_open_cell_retraction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∃ Θ : Mir k ((i + 1) + t + 1) → GL (Fin (i + (t + 1) + 1)) k, Continuous Θ ∧ Θ 1 = 1 ∧
    ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) → ∀ (d : Fin (t + 1) → k) (m : Mir k (i + (t + 1)))
      (x : Mir k ((i + 1) + t + 1)), dEmb k i t d * wEl k i t * sO k i t m = h * wEl k i t * x →
      ∃ p ∈ parab k (ePG i (t + 1)), (m : GL (Fin (i + (t + 1) + 1)) k) = p * Θ x := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Proj.exists_parab_mul <;> assumption)
