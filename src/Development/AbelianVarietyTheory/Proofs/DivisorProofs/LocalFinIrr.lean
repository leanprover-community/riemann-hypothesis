module

public import Mathlib.Topology.Algebra.MulAction
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.LocFinIrr

def conjMA (H : Type*) [Group H] : MulAction H H where
  smul g y := g * y * g⁻¹
  one_smul y := by show 1 * y * 1⁻¹ = y; group
  mul_smul a b y := by show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹; group

theorem conjMA_cont (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    @ContinuousSMul H H (conjMA H).toSMul _ _ :=
  @ContinuousSMul.mk H H (conjMA H).toSMul _ _ (by
    show Continuous fun q : H × H => q.1 * q.2 * q.1⁻¹
    fun_prop)

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.OrbFinAf.LocFinIrr
