module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Formalism.PeriodIntegrals.UpqRep
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

section
noncomputable section
open Matrix Topology Filter
open scoped ContDiff
namespace GlobalTheory.BesselMapOne
section Smooth
open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end Smooth
section Frame
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k r : ℕ}
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
end Frame
section Dual
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Dual
section Main
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
end Main
end GlobalTheory.BesselMapOne
end
end
