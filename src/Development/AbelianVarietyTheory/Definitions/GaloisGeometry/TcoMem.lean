module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
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

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K] {F : Type} [Field F] [Algebra k F] [Algebra F K] [IsScalarTower k F K]
  {d : ℕ} (x : Fin (d + 1) → F)

theorem tco_mem (j : Fin d) : algebraMap F K (x j.succ / x 0) ∈ rB k K x {0} := by
  have hA : x j.succ / x 0 ∈ rA k x {0} := by
    unfold rA
    exact Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩
  unfold rB
  rw [Subalgebra.mem_restrictScalars]
  exact isIntegral_algebraMap (R := rA k x {0}) (A := K) (x := ⟨_, hA⟩)

def fib : Type := {e : rB k K x {0} →ₐ[k] k // ∀ j, e ⟨_, tco_mem k K x j⟩ = 0}

def locCoch (h : K) : Finset (Fin (d + 1)) → DR k K := fun s => if s = Finset.univ then h • vol0 k K x else 0

end GlobalTheory.PD
