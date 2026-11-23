module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagStabMul

theorem latGroup_mul (I : AutInst) (xf : I.Gf) {x y : I.Ginf} (hx : x ∈ latGroup I xf)
    (hy : y ∈ latGroup I xf) : x * y ∈ latGroup I xf := by
  obtain ⟨γ, hγ, rfl, hk⟩ := hx
  obtain ⟨δ, hδ, rfl, hl⟩ := hy
  refine ⟨γ * δ, (GlobalTheory.RatDiscrete.ratSub I).mul_mem hγ hδ, rfl, ?_⟩
  have h : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
    rw [Prod.snd_mul]; group
  rw [h]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hk hl

theorem flagGroup_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  intro I xf a S x hx y hy
  refine ⟨latGroup_mul I xf hx.1 hy.1, fun v k z hz => ?_⟩
  have h : uMat ((x * y) v) = uMat (x v) * uMat (y v) := rfl
  rw [h, ← Matrix.mulVec_mulVec]
  exact hx.2 v k _ (hy.2 v k z hz)

end GlobalTheory.FlagStabMul
