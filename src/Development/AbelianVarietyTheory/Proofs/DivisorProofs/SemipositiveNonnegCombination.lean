module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess leviV)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace Weight

variable {A B : LB X}

theorem SemiPosReg.tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf)
    (hψ' : ψ.SemiPosReg D) (hφ' : φ.SemiPosReg D) : (ψ.tens φ).SemiPosReg D := fun i c y hy ξ => by
  have h1 := (mem_ptsIn_inf.1 hy.2).1
  have h2 := (mem_ptsIn_inf.1 hy.2).2
  have e := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add (hψ.contDiffAt c hy.1 h1)
    (hφ.contDiffAt c hy.1 h2) ξ
  have := add_nonneg (hψ' i.1 c y ⟨hy.1, h1⟩ ξ) (hφ' i.2 c y ⟨hy.1, h2⟩ ξ)
  rw [← Complex.add_re, ← e] at this
  exact this

theorem SemiPosReg.of_mul {E : LB X} (ψ : Weight p σ E) {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hφ' : φ.SemiPosReg D) (c : ℝ) (hc : 0 ≤ c) (j : E.ι → B.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (B.U (j i)))
    (he : ∀ i y, ψ.φ i y = c * φ.φ (j i) y) : ψ.SemiPosReg D := fun i c' y hy ξ => by
  have h1 := hj i y hy.2
  have hf : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =
      fun v => ((c * φ.φ (j i) (c'.e.symm v) : ℝ) : ℂ) := funext fun v => by rw [he]
  rw [hf, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul c (hφ.contDiffAt c' hy.1 h1) ξ,
    Complex.re_ofReal_mul]
  exact mul_nonneg hc (hφ' (j i) c' y ⟨hy.1, h1⟩ ξ)

end Weight

namespace HermLB

variable {L M : HermLB p}

theorem SemiPos.tens (hL : L.SemiPos D) (hM : M.SemiPos D) : (L.tens M).SemiPos D := fun σ =>
  Weight.SemiPosReg.tens (L.cInf σ) (M.cInf σ) (hL σ) (hM σ)

theorem SemiPos.pow (hL : L.SemiPos D) (m : ℕ) : (L.pow m).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
    (fun _ _ h => mem_pow_iff.1 h) fun j y => (L.φ σ).zpow_φ (m : ℤ) j y

end HermLB

namespace ArInt

variable {ι : Type} [Fintype ι]

end ArInt

end GlobalTheory
