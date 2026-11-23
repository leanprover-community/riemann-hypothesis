module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCartanDoubleCosetShellIntegrand
import Formalism.DoubleCosetMeasures.StatementZ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic


theorem _root_.GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  first | exact @GlobalTheory.ShellInt.integrableOn_shell | exact GlobalTheory.ShellInt.integrableOn_shell | (intros; apply GlobalTheory.ShellInt.integrableOn_shell <;> assumption)
