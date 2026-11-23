module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
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
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions
open Formalism.L2.Th1.H (cmL CmOK)

def CurveTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → Odd (Ideal.absNorm cc) → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ cc ≤ Ideal.span {(g : 𝓞 D.host.K)} ∧
      TaylorLogMetric.lamOf D cc δ = (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup

def CmReBase : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ D.host.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧
      (cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ ∧
      GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) (((g : ℂ) * δ) * a₀ / 2) ∧
      (B.ω₀ - ((g : ℂ) * δ) * a₀) / 2 ∈ TaylorLogMetric.lamOf D cc δ

end Formalism.L2.KerInert
