module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}

def coinvSub (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨆ i, LinearMap.range (Y i - μ i • 1)

def jointEig (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, LinearMap.ker (Y i - μ i • 1)

abbrev Coinv (Y : ι → Module.End ℂ M) (μ : ι → ℂ) := M ⧸ coinvSub Y μ

theorem coinvSub_le_comap {Y : ι → Module.End ℂ M} (μ : ι → ℂ) {T : Module.End ℂ M}
    (hT : ∀ i, Commute T (Y i)) : coinvSub Y μ ≤ (coinvSub Y μ).comap T := by
  unfold coinvSub
  apply iSup_le
  intro i
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]
  apply Submodule.mem_iSup_of_mem i
  refine ⟨T y, ?_⟩
  have hc : T (Y i y) = Y i (T y) := by
    rw [← Module.End.mul_apply, (hT i).eq, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc]

def coinvOp {Y : ι → Module.End ℂ M} (μ : ι → ℂ) (T : Module.End ℂ M)
    (hT : ∀ i, Commute T (Y i)) : Module.End ℂ (Coinv Y μ) :=
  (coinvSub Y μ).mapQ (coinvSub Y μ) T (coinvSub_le_comap μ hT)

end ReciprocityTheory.ThetaSummability.Real
