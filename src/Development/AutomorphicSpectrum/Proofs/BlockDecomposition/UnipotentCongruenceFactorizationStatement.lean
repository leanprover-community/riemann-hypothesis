module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCongruenceFactorization
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_congruence_factorization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (hs1 : ValuativeRel.valuation k (s : k) < 1)
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (κ : Mir k ((i + 1) + t + 1)) (hκ : κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1))
    (e : dEmb k i t d * sEmb k ((i + 1) + t) m = h * κ),
  ∃ a ∈ MirabolicParabolic k (i + 1) t, ∃ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t), m = a * x := by
  exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.Key1.mem_mirabolicParabolic_mul_cong
