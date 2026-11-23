module

public import Formalism.LocalToGlobal.KernelLattices.KerStd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm IsFrameH thetaH uniformGaussModelCondition)
open Formalism.L2.Th1.H (CmOK matH stdH stdLat pow4 imgLat relIdx StdData Th alphaQ kernel4 tens4)

def ThMMReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0) (B' : Base D cc δ),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ B'.IsCm a₀ b₀ ha hd ((g : ℂ) * δ) hl ∧
      B'.L.lattice = B.L.lattice ∧ B'.γ₀ = B.γ₀ ∧ B'.gC = B.gC ∧ B'.kappa = B.kappa ∧
      (B.ω₀ - B'.ω₀) / 2 ∈ B.L.lattice ∧ B'.IsThMM = B.IsThMM ∧ B'.thMM = B.thMM

end Formalism.L2.KerInert
